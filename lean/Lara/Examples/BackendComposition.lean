/-
A worked heterogeneous witness for `Lara.BackendComposition` — B0's concrete
half.  `Lara/BackendComposition.lean` states the firewall and the accounting
laws abstractly; this file instantiates them at closed fixtures, so a
mistranscription of `usedBackends`, `prem_subterm_swap`, or `dis_subterm_swap`
cannot hide behind a theorem that only ever quantifies.

## The split witness, and why it is split

This module is deliberately built from **two** kinds of backend, and the reader
is owed the boundary up front.

* **Shipped identities carry the syntactic and resolution facts.**
  `mixed_usedBackends` and `mixed_registrations_distinct` are stated over the
  real `nd@1` and `ord@1` entries of `Lara.Examples.registryEx` — the same
  fixed triple `Lara.Driver.buildRegistry` builds.  Neither fact needs a
  certificate to be *accepted*: which identities a term names is readable from
  the term alone (design note D2 in `Lara/BackendComposition.lean`), and
  registration is a registry lookup.

* **A fixture core carries the typed facts.**  `mixed_swap` and
  `mixed_dis_swap` need a genuinely typed child term, and typing a certificate
  node requires its acceptance to hold *inside the Lean kernel*.  For `ord@1`
  that is currently unreachable: acceptance routes through
  `Lara.Cell.parseDecimal` → `parseUnsigned` → `String.splitOn` and through
  `parseCanonInt` → `String.startsWith`, and under Lean 4.32's Slice-based
  `String` API those two are kernel-opaque — `rfl`, `decide`, `simp`, and
  `grind` all fail on literal goals such as `"28".splitOn "." = ["28"]`, while
  unfolding `String.splitOnAux` diverges.  `native_decide` would close the gap
  and is forbidden here (the axiom gate admits only `propext`,
  `Classical.choice`, `Quot.sound`).  So the *child* of the mixed term is
  `fixCore`, a minimal `Strict.Backend` defined below whose acceptance is a
  list lookup.  Every one of its `Strict.Backend` fields is genuinely proved;
  none is `sorry`.

What sits *above* that child differs between the two swap theorems, and only
the premise half runs under a shipped parent.  For `mixed_swap` the *parent* is
the real `nd@1` (`ndParent`), whose acceptance is the already-worked
`Lara.Examples.registry_success_bridge`, and the swapped term names both
identities.  For `mixed_dis_swap` the parent is an *unassured defeasible*
`ruleMix` node — `strictNoQ` forces `D = []` on strict nodes, so a certified
node in a discharge position needs a defeasible ancestor above it — and `nd@1`
is the *replaced child* rather than the parent, which is what
`mixed_dis_swap_usedBackends` records by proving
`usedBackends disParent = [ndId]` and `usedBackends disSwapTerm = [fixId]`.

This is not a new concession.  Lean's `ord@1`/`ra@1` results have stopped at
the resolution layer for exactly this reason since before B0 — see the block
comment at `Lara/Examples.lean:368-376`, which says so in as many words.  The
worked mixed `nd@1`/`ord@1` acceptance vector lives in Haskell
(`test/StrictSpec.hs`, landed), which is where executable conformance evidence
belongs; the Lean side carries the metatheory.

## What is and is not claimed

The heterogeneity content is exactly two things: `OccurrenceConsequence`'s
binder structure (design note D3 — the formula type, theory, and consequence
relation are bound *inside* each occurrence's existential, so no binder in
scope relates two occurrences), plus the *registration* distinctness proved
below.  `mixed_registrations_distinct` is named for registrations and not for
`Form`s on purpose: Lean cannot state `nd@1`'s formula type ≠ `ord@1`'s
formula type as a proposition it could then refute, and record inequality does
not imply type inequality.  Nothing stronger is claimed.

In particular this module does **not** claim that Lean rejects a
backend-leakage program.  Such a program cannot be written: an `Assurance`
carries only `(β, hd, κ)`, and there is no syntax anywhere in the AST that
names another backend's `Form`.  Nor is any of this parametricity.
-/

import Lara.BackendComposition
import Lara.Examples

namespace Lara.Examples.BackendComposition

open Lara.Support Lara.BackendComposition

/-! ### The fixture child core

A `Strict.Backend` small enough to *replay in the kernel*.  Its formula type is
`Atom` itself, normalized: the encoder is `nf`, so `enc_iff` is `≡`-exactness
by definition rather than by an encoding argument.  Its certificate is opaque
and unread — acceptance says "the goal is the first entry of the consulted
context", which is the smallest rule that still makes `uses` a real report
(slot `0`) rather than an empty one.  That matters: an empty report would
discharge `uses_covers`/`uses_valid`/`uses_account` vacuously and the fixture
would prove nothing about the accounting laws it is meant to exercise.
-/

/-- The fixture core's consequence relation: the goal is one of the consulted
entries. -/
def fixModels (Γ : List Atom) (φ : Atom) : Prop := φ ∈ Γ

/-- The fixture core's acceptance: the goal is the consulted context's first
entry.  The certificate is not read — the fixture exists to be *decidable*, not
to be expressive. -/
def fixAccepts (_κ : CertRef) (Γ : List Atom) (φ : Atom) : Prop :=
  Γ[0]? = some φ

/-- Executable replay of `fixAccepts`.  A decidable equality on `Option Atom`,
which is what makes a `fix@1`-certified node typable inside the kernel. -/
def fixReplay (_κ : CertRef) (Γ : List Atom) (φ : Atom) : Bool :=
  decide (Γ[0]? = some φ)

/-- The fixture core's dependency report: slot `0`, the one entry acceptance
consults.  Deliberately non-empty, so obligation 4's three laws have content
here. -/
def fixUses (_κ : CertRef) : List Nat := [0]

/-- Replay is adequate: it is `decide` of the acceptance proposition. -/
theorem fixReplay_iff (κ : CertRef) (Γ : List Atom) (φ : Atom) :
    fixReplay κ Γ φ = true ↔ fixAccepts κ Γ φ := by
  simp [fixReplay, fixAccepts]

/-- Certificate soundness: the entry acceptance found is an entry of the
consulted context, which is precisely `fixModels`. -/
theorem fixSound (κ : CertRef) (Γ : List Atom) (φ : Atom)
    (h : fixAccepts κ Γ φ) : fixModels Γ φ := by
  have h' : Γ[0]? = some φ := h
  cases Γ with
  | nil => simp at h'
  | cons a rest =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h'
      subst h'
      simp [fixModels]

/-- Obligation 4, coverage: replay reads the consulted context only at slot
`0`, so two contexts agreeing there replay identically. -/
theorem fixUses_covers (κ : CertRef) (Γ Γ' : List Atom) (φ : Atom)
    (hag : ∀ i, i ∈ fixUses κ → Γ[i]? = Γ'[i]?) :
    fixReplay κ Γ φ = fixReplay κ Γ' φ := by
  simp only [fixReplay]
  rw [hag 0 (by simp [fixUses])]

/-- Obligation 4, validity: on acceptance the reported slot is in range —
`Γ[0]? = some φ` is itself the range evidence. -/
theorem fixUses_valid (κ : CertRef) (Γ : List Atom) (φ : Atom)
    (h : fixAccepts κ Γ φ) : ∀ i, i ∈ fixUses κ → i < Γ.length := by
  intro i hi
  simp only [fixUses, List.mem_singleton] at hi
  subst hi
  have h' : Γ[0]? = some φ := h
  exact lt_of_getElem?_some h'

/-- Obligation 4, accounting: the conclusion follows from the *reported* slots
alone.  `selectSlots Γ [0]` is the singleton `[φ]`, and `φ ∈ [φ]`. -/
theorem fixUses_account (κ : CertRef) (Γ : List Atom) (φ : Atom)
    (h : fixAccepts κ Γ φ) :
    fixModels (Lara.Strict.selectSlots Γ (fixUses κ)) φ := by
  have h' : Γ[0]? = some φ := h
  simp [fixModels, fixUses, Lara.Strict.selectSlots, h']

/-- The fixture backend core, every field discharged.  Its `Form` is `Atom`,
which is *not* `nd@1`'s `Lara.ND.Formula` — the two cores really do compute in
different formula types, even though (D3) no theorem here can or does assert
that inequality. -/
def fixCore : Lara.Strict.Backend id where
  Form := Atom
  enc := Lara.nf id
  enc_iff := fun p q => (Lara.equiv_iff_nf_eq id p q).symm
  modelsFull := fixModels
  acceptsFull := fixAccepts
  replayFull := fixReplay
  replayFull_iff := fixReplay_iff
  soundFull := fixSound
  uses := fixUses
  uses_covers := fixUses_covers
  uses_valid := fixUses_valid
  uses_account := fixUses_account

/-! ### A registry that extends `registryEx` rather than replacing it

`Lara.Examples.registryEx` is left untouched: `registryMix` adds the fixture
identity in front of it and delegates everything else, so it agrees with
`registryEx` on `nd@1`, `ra@1` and `ord@1` by construction.  That is what lets
the already-worked `nd@1` acceptance (`registry_success_bridge`) transport into
the mixed derivations below with a single lookup rewrite. -/

/-- The fixture identity.  A fourth `(name, version)` pair, distinct from the
three shipped ones. -/
def fixId : BackendId := ⟨"fix", 1⟩

/-- An opaque certificate reference for the fixture core, which never reads
it. -/
def fixCert : CertRef := ⟨.atom "fix-slot-0"⟩

/-- The fixture registration.  A known digest resolves to the EMPTY theory, on
the same discipline as the `ord@1` and `ra@1` entries: the consulted context is
then exactly the submitted premises. -/
def fixRegistered : RegisteredBackend id where
  core := fixCore
  resolveTheory := fun h => if h = digestA then some [] else none

/-- `registryEx` extended with the fixture identity. -/
def registryMix : BackendRegistry id := fun β =>
  if β = fixId then some fixRegistered else registryEx β

/-- The extension is conservative at `nd@1`: the shipped registration is
returned unchanged. -/
theorem registryMix_nd : registryMix ndId = registryEx ndId := by
  simp [registryMix, ndId, fixId]

/-- …and at `ord@1`. -/
theorem registryMix_ord : registryMix ordId = registryEx ordId := by
  simp [registryMix, ordId, fixId]

/-- The fixture identity is the only thing the extension adds. -/
theorem registryMix_fix : registryMix fixId = some fixRegistered := by
  simp [registryMix]

/-- Certificate acceptance depends on the registry *only* through the one
lookup at the certificate's own identity.  This is the transport lemma that
lets `Lara.Examples`' worked `nd@1` acceptance be reused verbatim under a
larger registry — and it is itself a small piece of the firewall: enlarging the
registry with an unrelated backend cannot change what an existing one
accepts. -/
theorem certOkOf_registry_congr {canon : String → String}
    {reg reg' : BackendRegistry canon} {β : BackendId}
    (hβ : reg β = reg' β) (hd : Digest) (κ : CertRef) (As : List Atom)
    (C : Atom) :
    certOkOf reg β hd κ As C = certOkOf reg' β hd κ As C := by
  simp only [certOkOf, hβ]

/-- The shipped `nd@1` acceptance, transported to `registryMix`.  This is
`Lara.Examples.registry_success_bridge` — a real ND proof term replayed by the
real ND adapter — not a fixture. -/
theorem nd_accepts_mix :
    certOkOf registryMix ndId digestA slot1Cert [pA] pB := by
  rw [certOkOf_registry_congr registryMix_nd digestA slot1Cert [pA] pB]
  exact registry_success_bridge

/-- The fixture core accepts `pA` from the single premise `pA`: slot `0` of the
consulted context `[enc pA] ++ []`. -/
theorem fix_certOkB_pA :
    certOkBOf registryMix fixId digestA fixCert [pA] pA = true := by decide

theorem fix_accepts_pA :
    certOkOf registryMix fixId digestA fixCert [pA] pA :=
  (certOkBOf_iff registryMix fixId digestA fixCert [pA] pA).mp fix_certOkB_pA

/-- The same at `pB`, needed for the discharge-position swap, whose question
pattern fixes the answer atom to `pB`. -/
theorem fix_certOkB_pB :
    certOkBOf registryMix fixId digestA fixCert [pB] pB = true := by decide

theorem fix_accepts_pB :
    certOkOf registryMix fixId digestA fixCert [pB] pB :=
  (certOkBOf_iff registryMix fixId digestA fixCert [pB] pB).mp fix_certOkB_pB

/-! ### Rules and context

`Lara.Examples.ruleCert` allowlists only `(nd@1, digestA)` and `Lara.Examples`'
`PiEx`/`PiCert` know nothing of the fixture identity, so the two fixture rules
and the rule context below are new.  `ruleCert`, `ruleMix`, `ΓEx`, `l1`, `l2`,
`q1`, `q2` are reused unchanged — the parent of the mixed term is meant to be
the *existing* worked `nd@1` node, not a new one. -/

def rFixAId : RuleId := ⟨"r-fix-a"⟩
def rFixBId : RuleId := ⟨"r-fix-b"⟩

/-- A strict `fix@1`-certified restatement of `p`.  Premise and conclusion
agree because the fixture core's acceptance is "the goal is slot 0". -/
def ruleFixA : Rule :=
  { mode := .strict, params := [], premises := [apA], concl := apA
  , questions := [], allowTrusted := false
  , certifiers := [(fixId, digestA)] }

/-- The same rule at `q`, for the discharge position. -/
def ruleFixB : Rule :=
  { mode := .strict, params := [], premises := [apB], concl := apB
  , questions := [], allowTrusted := false
  , certifiers := [(fixId, digestA)] }

/-- The rule context for the mixed derivations: the shipped `nd@1` certified
rule, the two fixture rules, and the defeasible question-bearing rule that
supplies a discharge position. -/
def PiMix : RuleId → Option Rule := fun rn =>
  if rn = rCertId then some ruleCert
  else if rn = rFixAId then some ruleFixA
  else if rn = rFixBId then some ruleFixB
  else if rn = rMixId then some ruleMix
  else none

/-! ### Step 2: a term naming two *shipped* identities

Nothing here is typed, and nothing needs to be: `usedBackends` reads the
identities off the assurance nodes (design note D2).  That is exactly why this
half of the witness can use the real `ord@1` — kernel-opaque acceptance is
irrelevant to a syntactic scan. -/

/-- A child node whose assurance names the shipped `ord@1`. -/
def shippedOrdChild : SupportTerm :=
  .inst rCertId [] [.leaf l1] [] [] (.cert ordId digestA slot0Cert)

/-- An `nd@1`-assured parent over an `ord@1`-assured child: one term, two
shipped backend identities. -/
def mixedTerm : SupportTerm :=
  .inst rCertId [] [shippedOrdChild] [] [] (.cert ndId digestA slot1Cert)

/-- **The term genuinely names two shipped identities.**  Not "at least two",
and not up to permutation: `usedBackends` returns the parent's identity then
the premise carrier's, in that order. -/
theorem mixed_usedBackends : usedBackends mixedTerm = [ndId, ordId] := by
  simp [mixedTerm, shippedOrdChild, usedBackends, usedBackendsList,
    usedBackendsDis]

/-! ### Step 3: the two shipped identities resolve to distinct registrations -/

/-- The length of the theory `digestA` resolves to, as a `RegisteredBackend`
invariant that is *not* dependent on the record's own formula type.  This is
the projection that makes registration distinctness provable: the theory data
itself has type `List r.core.Form` and so cannot be compared across records,
but its length is a plain `Nat`. -/
def digestATheoryLength (r : RegisteredBackend id) : Option Nat :=
  (r.resolveTheory digestA).map List.length

theorem ndRegistered_theory_length :
    digestATheoryLength ndRegistered = some 1 := by
  simp [digestATheoryLength, ndRegistered, slotTheory]
  rfl

theorem ordRegistered_theory_length :
    digestATheoryLength ordRegistered = some 0 := by
  simp [digestATheoryLength, ordRegistered]

/-- **The two shipped identities resolve to distinct registrations.**

Read the name literally.  This is *registration* distinctness — the registry
maps `nd@1` and `ord@1` to two records that are not the same record — and it is
deliberately **not** a claim that their `Form` types differ.  Lean cannot state
that: `registered.core.Form` is a `Type` bound inside the record, type
inequality is not expressible as a refutable proposition here, and record
inequality would not imply it anyway (a registry is an arbitrary function, and
nothing stops one mapping two identities to the same core — see design note D3
in `Lara/BackendComposition.lean`).

So the heterogeneity content of this module is exactly: D3's binder structure,
which is where the *absence of a relating binder* lives, plus this resolution
fact, which is what makes the absence non-vacuous at a concrete registry.
Nothing stronger is claimed anywhere below. -/
theorem mixed_registrations_distinct :
    registryEx ndId = some ndRegistered ∧
      registryEx ordId = some ordRegistered ∧
      ndRegistered ≠ ordRegistered := by
  refine ⟨by simp [registryEx, ndId], registry_ord_registered, ?_⟩
  intro h
  have hlen : digestATheoryLength ndRegistered
      = digestATheoryLength ordRegistered := by rw [h]
  rw [ndRegistered_theory_length, ordRegistered_theory_length] at hlen
  exact absurd hlen (by decide)

/-! ### Step 4: the firewall, instantiated

The parent is the shipped `nd@1` node from `Lara.Examples`: rule `ruleCert`,
one premise, certificate `slot1Cert`, acceptance `registry_success_bridge`.  Its
premise starts as the declared leaf `l1` and is then *replaced* by a
`fix@1`-certified term of the same conclusion.  `prem_subterm_swap` returns the
parent's typing at the same conclusion and the same obligations — and it does
so without the parent's side conditions ever mentioning either backend. -/

/-- The homogeneous starting point: a strict `nd@1`-certified instance over the
declared leaf `l1`. -/
def ndParent : SupportTerm :=
  .inst rCertId [] [.leaf l1] [] [] (.cert ndId digestA slot1Cert)

/-- The `fix@1`-certified replacement at conclusion `pA`. -/
def fixChildA : SupportTerm :=
  .inst rFixAId [] [.leaf l1] [] [] (.cert fixId digestA fixCert)

/-- The `fix@1`-certified replacement at conclusion `pB`, for the discharge
position. -/
def fixChildB : SupportTerm :=
  .inst rFixBId [] [.leaf l2] [] [] (.cert fixId digestA fixCert)

/-- The parent after the premise swap: an `nd@1` node whose premise is now
certified by `fix@1`. -/
def mixedSwapTerm : SupportTerm :=
  .inst rCertId [] [fixChildA] [] [] (.cert ndId digestA slot1Cert)

theorem sideNdParent :
    InstSide id PiMix (certOkOf registryMix) rCertId [] ruleCert
      [.leaf l1] [] [] (.cert ndId digestA slot1Cert)
      [pA] [pA] [[]] [] [] pB where
  rule := by simp [PiMix]
  θNodup := by simp
  θDom := by simp [ruleCert]
  prems := by decide
  concl := by decide
  lenAs := rfl
  lenCs := rfl
  lenOs := rfl
  premEq := by
    intro i A B hA hB
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hA hB
      subst hA; subst hB
      exact equiv_refl id pA
    | succ j => simp at hA
  lenDCs := rfl
  lenDOs := rfl
  ans := by intro j q w A hD _; simp at hD
  qNodup := by simp [questionNames, ruleCert]
  dNodup := by simp
  hNodup := by simp
  cover := by intro qd hqd; simp [ruleCert] at hqd
  disj := by intro n hn; simp at hn
  keysD := by intro n hn; simp at hn
  keysH := by intro n hn; simp at hn
  strictNoQ := by intro _; exact ⟨rfl, rfl⟩
  assur := .cert rfl (by simp [ruleCert]) nd_accepts_mix

/-- The unswapped premise obligation: slot `0` of `ndParent` is the declared
leaf `l1`. -/
theorem ndParent_prems :
    ∀ (i : Nat) (w : SupportTerm) (A : Atom) (O : List QuestionId),
      [SupportTerm.leaf l1][i]? = some w → [pA][i]? = some A →
      [([] : List QuestionId)][i]? = some O →
      HasSupport id PiMix ΓEx (certOkOf registryMix) w A O := by
  intro i w A O hw hA hO
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hA hO
    subst hw; subst hA; subst hO
    exact .leaf (by decide)
  | succ j => simp at hw

/-- The homogeneous parent types, on the real `nd@1` acceptance. -/
theorem ndParent_typed :
    HasSupport id PiMix ΓEx (certOkOf registryMix) ndParent pB [] :=
  (by decide : collectObligations [[]] [] ruleCert [] = []) ▸
    HasSupport.inst sideNdParent ndParent_prems no_dis

theorem sideFixA :
    InstSide id PiMix (certOkOf registryMix) rFixAId [] ruleFixA
      [.leaf l1] [] [] (.cert fixId digestA fixCert)
      [pA] [pA] [[]] [] [] pA where
  rule := by simp [PiMix, rCertId, rFixAId]
  θNodup := by simp
  θDom := by simp [ruleFixA]
  prems := by decide
  concl := by decide
  lenAs := rfl
  lenCs := rfl
  lenOs := rfl
  premEq := by
    intro i A B hA hB
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hA hB
      subst hA; subst hB
      exact equiv_refl id pA
    | succ j => simp at hA
  lenDCs := rfl
  lenDOs := rfl
  ans := by intro j q w A hD _; simp at hD
  qNodup := by simp [questionNames, ruleFixA]
  dNodup := by simp
  hNodup := by simp
  cover := by intro qd hqd; simp [ruleFixA] at hqd
  disj := by intro n hn; simp at hn
  keysD := by intro n hn; simp at hn
  keysH := by intro n hn; simp at hn
  strictNoQ := by intro _; exact ⟨rfl, rfl⟩
  assur := .cert rfl (by simp [ruleFixA]) fix_accepts_pA

/-- The fixture-certified child types, at the same conclusion and the same
(empty) obligations as the leaf it will replace. -/
theorem fixChildA_typed :
    HasSupport id PiMix ΓEx (certOkOf registryMix) fixChildA pA [] :=
  (by decide : collectObligations [[]] [] ruleFixA [] = []) ▸
    HasSupport.inst sideFixA ndParent_prems no_dis

/-- **The backend firewall, instantiated (premise half).**  The parent is the
real `nd@1` node — same rule, same substitution, same certificate, same
acceptance derivation — and its premise has been swapped from a declared leaf
to a term certified by a *different* registered identity, over a different
formula type, under a different theory.  The parent still types, at the same
conclusion `pB` and the same obligations `[]`.

The derivation is genuine on both sides: `sideNdParent` carries the real
`registry_success_bridge` acceptance (an ND proof term replayed by the ND
adapter), and `fixChildA_typed` carries the fixture core's own acceptance.  The
firewall is what makes them composable — and it composes them without any side
condition of the parent being able to see which backend the child used. -/
theorem mixed_swap :
    HasSupport id PiMix ΓEx (certOkOf registryMix) mixedSwapTerm pB [] :=
  (by decide : collectObligations [[]] [] ruleCert [] = []) ▸
    prem_subterm_swap (Gamma := ΓEx) sideNdParent ndParent_prems no_dis
      (i := 0) rfl rfl fixChildA_typed

/-- The swapped term names both identities, so `mixed_swap` really is a mixed
witness and not a homogeneous one in disguise. -/
theorem mixed_swap_usedBackends :
    usedBackends mixedSwapTerm = [ndId, fixId] := by
  simp [mixedSwapTerm, fixChildA, usedBackends, usedBackendsList,
    usedBackendsDis]

/-- **B0's headline at a concrete mixed term.**  `usedBackends_accounted`
applied to `mixed_swap`: each of the two identities the swapped term names is
registered, has an occurrence to point at, and discharges that occurrence in
its *own* logic — `nd@1` in `Lara.ND`, `fix@1` in `fixModels`.  The two
conjuncts are produced by two different cores and nothing in the statement
relates them. -/
theorem mixed_swap_accounted :
    ∀ β ∈ usedBackends mixedSwapTerm, ∃ o : CertOccurrence,
      OccursIn mixedSwapTerm o ∧ o.β = β ∧
        ∃ As Cn, certOkOf registryMix β o.hd o.κ As Cn ∧
          OccurrenceConsequence registryMix β o.hd o.κ As Cn :=
  usedBackends_accounted mixed_swap

/-! ### Step 4b: the discharge half

A discharge position only exists under a *defeasible* ancestor: `InstSide`'s
`strictNoQ` forces `D = []` on every strict node, so a certified node inside a
discharge subterm needs a defeasible parent above it.  `ruleMix` supplies one —
mandatory question `q1`, optional `q2` — and the certified node sits at `q1`.

This defeasible-ancestor shape is also what PW-T6 will need, which
is why it is built here rather than inline in a later milestone. -/

/-- Defeasible parent with the shipped `nd@1` node discharging `q1`. -/
def disParent : SupportTerm := .inst rMixId [] [] [(q1, ndParent)] [q2] .none

/-- The same parent after the discharge swap. -/
def disSwapTerm : SupportTerm := .inst rMixId [] [] [(q1, fixChildB)] [q2] .none

theorem sideFixB :
    InstSide id PiMix (certOkOf registryMix) rFixBId [] ruleFixB
      [.leaf l2] [] [] (.cert fixId digestA fixCert)
      [pB] [pB] [[]] [] [] pB where
  rule := by simp [PiMix, rCertId, rFixAId, rFixBId]
  θNodup := by simp
  θDom := by simp [ruleFixB]
  prems := by decide
  concl := by decide
  lenAs := rfl
  lenCs := rfl
  lenOs := rfl
  premEq := by
    intro i A B hA hB
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hA hB
      subst hA; subst hB
      exact equiv_refl id pB
    | succ j => simp at hA
  lenDCs := rfl
  lenDOs := rfl
  ans := by intro j q w A hD _; simp at hD
  qNodup := by simp [questionNames, ruleFixB]
  dNodup := by simp
  hNodup := by simp
  cover := by intro qd hqd; simp [ruleFixB] at hqd
  disj := by intro n hn; simp at hn
  keysD := by intro n hn; simp at hn
  keysH := by intro n hn; simp at hn
  strictNoQ := by intro _; exact ⟨rfl, rfl⟩
  assur := .cert rfl (by simp [ruleFixB]) fix_accepts_pB

/-- The fixture-certified discharge replacement types at `pB`, the answer atom
`q1`'s pattern fixes. -/
theorem fixChildB_typed :
    HasSupport id PiMix ΓEx (certOkOf registryMix) fixChildB pB [] :=
  (by decide : collectObligations [[]] [] ruleFixB [] = []) ▸
    HasSupport.inst sideFixB
      (by
        intro i w A O hw hA hO
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hw hA hO
          subst hw; subst hA; subst hO
          exact .leaf (by decide)
        | succ j => simp at hw)
      no_dis

theorem sideDisMix :
    InstSide id PiMix (certOkOf registryMix) rMixId [] ruleMix
      [] [(q1, ndParent)] [q2] .none [] [] [] [pB] [[]] pA where
  rule := by simp [PiMix, rCertId, rFixAId, rFixBId, rMixId]
  θNodup := by simp
  θDom := by simp [ruleMix]
  prems := rfl
  concl := by decide
  lenAs := rfl
  lenCs := rfl
  lenOs := rfl
  premEq := by intro i A B hA _; simp at hA
  lenDCs := rfl
  lenDOs := rfl
  ans := by
    intro j q w A hD hA
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hD hA
      injection hD with hq hw
      subst q; subst w; subst A
      exact ⟨⟨q1, apB, true⟩, by simp [ruleMix], rfl,
        pB, by decide, equiv_refl id pB⟩
    | succ j => simp at hD
  qNodup := by simp [questionNames, ruleMix, q1, q2]
  dNodup := by simp
  hNodup := by simp
  cover := by
    intro qd hqd
    simp only [ruleMix, List.mem_cons, List.not_mem_nil, or_false] at hqd
    rcases hqd with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  disj := by
    intro n hn hH
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hn hH
    rw [hn] at hH
    simp [q1, q2] at hH
  keysD := by
    intro n hn
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hn
    subst n
    simp [questionNames, ruleMix]
  keysH := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    subst n
    simp [questionNames, ruleMix]
  strictNoQ := by intro h; simp [ruleMix] at h
  assur := .defeasible rfl

/-- The unswapped discharge obligation: slot `0` of `disParent`'s map holds the
`nd@1` node. -/
theorem disParent_dis :
    ∀ (j : Nat) (q : QuestionId) (w : SupportTerm) (A : Atom)
      (O : List QuestionId),
      [(q1, ndParent)][j]? = some (q, w) → [pB][j]? = some A →
      [([] : List QuestionId)][j]? = some O →
      HasSupport id PiMix ΓEx (certOkOf registryMix) w A O := by
  intro j q w A O hD hA hO
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hD hA hO
    injection hD with hq hw
    subst hw; subst hA; subst hO
    exact ndParent_typed
  | succ j => simp at hD

/-- The defeasible parent types with the shipped `nd@1` node in its discharge
position. -/
theorem disParent_typed :
    HasSupport id PiMix ΓEx (certOkOf registryMix) disParent pA [] :=
  (by decide : collectObligations [] [[]] ruleMix [q2] = []) ▸
    HasSupport.inst sideDisMix no_prems disParent_dis

/-- **The backend firewall, instantiated (discharge half).**  The discharge
subterm answering `q1` is replaced by one certified under a different
registered identity, and the defeasible parent still types at the same
conclusion and the same obligations.

`dis_subterm_swap` is where more of `InstSide` has to survive than in the
premise case — `dNodup`, `cover`, `disj`, `keysD` all read `D`, and `ans`
constrains the answer atom — and the swap survives all of it because every one
of those reads `D` only through `D.map Prod.fst`, which the swap preserves.
None of them can see the replacement's assurance. -/
theorem mixed_dis_swap :
    HasSupport id PiMix ΓEx (certOkOf registryMix) disSwapTerm pA [] :=
  (by decide : collectObligations [] [[]] ruleMix [q2] = []) ▸
    dis_subterm_swap (Gamma := ΓEx) sideDisMix no_prems disParent_dis
      (j := 0) rfl rfl rfl fixChildB_typed

/-- The discharge-swapped term names `fix@1` where the original named `nd@1`,
so the swap really did cross a backend boundary. -/
theorem mixed_dis_swap_usedBackends :
    usedBackends disParent = [ndId] ∧ usedBackends disSwapTerm = [fixId] := by
  constructor <;>
    simp [disParent, disSwapTerm, ndParent, fixChildB, usedBackends,
      usedBackendsList, usedBackendsDis]

/-! ### Step 5: the cross-language `certDeps` golden

Everything above this point splits: the *typed* facts run on `fixCore` because
`ord@1` acceptance is kernel-opaque, and only the *syntactic* facts
(`mixed_usedBackends`) reach the shipped `ord@1`.  **This section does not
split.**  It is computed over the real shipped `nd@1` and `ord@1` cores —
`Lara.Strict.ndBackend` and `Lara.Ord.ordBackend`, the same two
`Lara.Driver.buildRegistry` registers — and it is the one artifact in B0 where
both languages compute the same thing over the same two shipped backends.

**Why the acceptance blocker does not touch it.**  `Lara.Support.stepDeps`
never calls `acceptsFull`.  It needs four things to resolve — the rule, the
premise instantiation `instAPats`, the registry entry `reg β`, and
`resolveTheory hd` — and then it maps `registered.core.uses κ` over the slots.
For `ord@1` that report is `Lara.Ord.ordUses`, which routes through
`Lara.Ord.decodeCert` → `Lara.Cell.decodeSlot` → `Lara.Cell.parseCanonNat` →
`String.toNat?`.  `String.toNat?` *is* provable per literal, via
`String.toNat?_eq_some_ofDigitChars` — the same treatment
`Lara.ND.decodeNat_leading_zero_01` already gives the ND decoder.  What is
kernel-opaque is `String.splitOn` and `String.startsWith`, reached only from
`Lara.Cell.parseDecimal`/`parseCanonInt`, i.e. only from *acceptance*.  So the
report resolves in the kernel even though the acceptance beside it does not,
and `depsMixedTerm_certDeps` below is a genuine two-shipped-backend fact with
no fixture anywhere in it.

The Haskell counterpart is `test/StrictSpec.hs`' `mixedTerm` /
`prop_mixedBackendDepsCollected`, whose term this one mirrors atom for atom:
same two backends, same rule shapes, same premise atoms, same certificate
payloads, same digests, same theory-entry index.  `scripts/check-backend-deps-golden.sh`
diffs the two through `test/backend-deps.golden`. -/

/-! #### The two mixed-backend terms, made to correspond

Every constant below is fixed by its Haskell twin in `test/StrictSpec.hs`, and
the correspondence is exact — no field of a `CertDep` is abstracted away to
make the diff pass.  In particular the digests are Haskell's `sha256:nd0` /
`sha256:ord0` rather than `Lara.Examples.digestA`, because a `CertDep.theoryEntry`
carries its digest and the encoded line would otherwise disagree on a field
that is genuinely part of the dependency. -/

/-- `nd@1`'s theory digest, spelled as `test/StrictSpec.hs`' `ndDigest`. -/
def depsNdDigest : Digest := ⟨"sha256:nd0"⟩

/-- `ord@1`'s theory digest, spelled as `test/StrictSpec.hs`' `ordDigest`. -/
def depsOrdDigest : Digest := ⟨"sha256:ord0"⟩

/-- `cell(ours, 28.4)` — `test/StrictSpec.hs`' `cellOurs`. -/
def depsCellOurs : Atom :=
  .atom "cell" (.cons (.con "ours" .nil) (.cons (.num "28.4") .nil))

/-- `cell(theirs, 31.6)` — `test/StrictSpec.hs`' `cellTheirs`. -/
def depsCellTheirs : Atom :=
  .atom "cell" (.cons (.con "theirs" .nil) (.cons (.num "31.6") .nil))

/-- `num_lt(28.4, 31.6)` — `test/StrictSpec.hs`' `comparison`. -/
def depsComparison : Atom :=
  .atom "num_lt" (.cons (.num "28.4") (.cons (.num "31.6") .nil))

/-- `within_compute_budget` — `test/StrictSpec.hs`' `budgetRespected`, and the
single entry of the `nd@1` theory `depsNdDigest` resolves to. -/
def depsBudget : Atom := .atom "within_compute_budget" .nil

/-- The ground pattern that instantiates to `depsCellOurs` under the empty
substitution (Haskell `patOf cellOurs`). -/
def depsCellOursPat : APat :=
  ⟨⟨"cell"⟩, .cons (.con ⟨"ours"⟩ .nil) (.cons (.num "28.4") .nil)⟩

def depsCellTheirsPat : APat :=
  ⟨⟨"cell"⟩, .cons (.con ⟨"theirs"⟩ .nil) (.cons (.num "31.6") .nil)⟩

def depsComparisonPat : APat :=
  ⟨⟨"num_lt"⟩, .cons (.num "28.4") (.cons (.num "31.6") .nil)⟩

def depsBudgetPat : APat := ⟨⟨"within_compute_budget"⟩, .nil⟩

/-- The `nd@1` registration for this section: the **shipped** ND core, with
`depsNdDigest` resolving to a one-entry theory.  One entry, not zero, is what
makes the root's report a `theoryEntry` — the only `CertDep` shape that carries
a backend identity. -/
def depsNdRegistered : RegisteredBackend id where
  core := Lara.Strict.ndBackend id
  resolveTheory := fun h =>
    if h = depsNdDigest then some (slotTheory id [depsBudget]) else none

/-- The `ord@1` registration for this section: the **shipped** `ord@1` core,
with `depsOrdDigest` resolving to the EMPTY theory — `Lara.Driver.buildRegistry`'s
discipline, and `test/StrictSpec.hs`' `depsTheories`.  The consulted context is
then exactly the submitted premises, so both reported slots resolve to premise
dependencies. -/
def depsOrdRegistered : RegisteredBackend id where
  core := Lara.Ord.ordBackend id
  resolveTheory := fun h => if h = depsOrdDigest then some [] else none

/-- The registry this section computes over: the two shipped identities and
nothing else.  `fixId` is deliberately absent — the point of this section is
that no fixture is involved. -/
def registryDeps : BackendRegistry id := fun β =>
  if β = ndId then some depsNdRegistered
  else if β = ordId then some depsOrdRegistered
  else none

def depsOrdRuleId : RuleId := ⟨"compare_cells"⟩
def depsNdRuleId : RuleId := ⟨"restate_budget"⟩

/-- The `ord@1` step: two measurement premises, a comparison conclusion
(`test/StrictSpec.hs`' `ordRule`). -/
def depsOrdRule : Rule :=
  { mode := .strict, params := []
  , premises := [depsCellOursPat, depsCellTheirsPat], concl := depsComparisonPat
  , questions := [], allowTrusted := false
  , certifiers := [(ordId, depsOrdDigest)] }

/-- The `nd@1` step sitting above it: one premise (the comparison), the budget
sentence as conclusion (`test/StrictSpec.hs`' `ndRule`). -/
def depsNdRule : Rule :=
  { mode := .strict, params := []
  , premises := [depsComparisonPat], concl := depsBudgetPat
  , questions := [], allowTrusted := false
  , certifiers := [(ndId, depsNdDigest)] }

/-- `cell(self, 7.5)` — `test/StrictSpec.hs`' `cellSelf`.  Same one-numeral
cell shape as `depsCellOurs`, so the shipped `ord@1` premise-cell convention
accepts it on the Haskell side. -/
def depsCellSelf : Atom :=
  .atom "cell" (.cons (.con "self" .nil) (.cons (.num "7.5") .nil))

/-- `num_le(7.5, 7.5)` — `test/StrictSpec.hs`' `numLeSelf`.  The reflexive
family member: a same-slot certificate compares a cell with itself, so the
goal must be one that holds. -/
def depsNumLeSelf : Atom :=
  .atom "num_le" (.cons (.num "7.5") (.cons (.num "7.5") .nil))

/-- `note(quote("say \"hi\"\\bye"), wrap(inner))` — `test/StrictSpec.hs`'s
`noteAtom`.  One atom carrying everything the first vector's atoms leave
untested: a `str` whose encoding must escape both `"` and `\`, and `con`s
with arguments nested two deep. -/
def depsNoteAtom : Atom :=
  .atom "note"
    (.cons (.con "quote" (.cons (.str "say \"hi\"\\bye") .nil))
      (.cons (.con "wrap" (.cons (.con "inner" .nil) .nil)) .nil))

def depsCellSelfPat : APat :=
  ⟨⟨"cell"⟩, .cons (.con ⟨"self"⟩ .nil) (.cons (.num "7.5") .nil)⟩

def depsNumLeSelfPat : APat :=
  ⟨⟨"num_le"⟩, .cons (.num "7.5") (.cons (.num "7.5") .nil)⟩

def depsNotePat : APat :=
  ⟨⟨"note"⟩,
    .cons (.con ⟨"quote"⟩ (.cons (.str "say \"hi\"\\bye") .nil))
      (.cons (.con ⟨"wrap"⟩ (.cons (.con ⟨"inner"⟩ .nil) .nil)) .nil)⟩

def depsDupOrdRuleId : RuleId := ⟨"compare_self"⟩
def depsDupNdRuleId : RuleId := ⟨"restate_note"⟩

/-- The `ord@1` self-comparison step: one measurement premise, the reflexive
comparison as conclusion (`test/StrictSpec.hs`' `dupOrdRule`). -/
def depsDupOrdRule : Rule :=
  { mode := .strict, params := []
  , premises := [depsCellSelfPat], concl := depsNumLeSelfPat
  , questions := [], allowTrusted := false
  , certifiers := [(ordId, depsOrdDigest)] }

/-- The `nd@1` step above it: two premises (the note atom and the
self-comparison), the note atom restated as conclusion
(`test/StrictSpec.hs`' `dupNdRule`).  Its certificate is `(hyp 0)`, so its
report names premise slot 0 — the note atom, not the comparison. -/
def depsDupNdRule : Rule :=
  { mode := .strict, params := []
  , premises := [depsNotePat, depsNumLeSelfPat], concl := depsNotePat
  , questions := [], allowTrusted := false
  , certifiers := [(ndId, depsNdDigest)] }

def PiDeps : RuleId → Option Rule := fun rn =>
  if rn = depsOrdRuleId then some depsOrdRule
  else if rn = depsNdRuleId then some depsNdRule
  else if rn = depsDupOrdRuleId then some depsDupOrdRule
  else if rn = depsDupNdRuleId then some depsDupNdRule
  else none

def depsOursLeaf : LeafId := ⟨"e_ours"⟩
def depsTheirsLeaf : LeafId := ⟨"e_theirs"⟩

/-- The shipped `ord@1` certificate payload `(ordcmp (prem 0) (prem 1))`,
spelled through the two backends' own keyword tables so the concrete wire words
stay defined in exactly one place — the discipline `test/StrictSpec.hs`'
`premSlot` already applies on the Haskell side. -/
def depsOrdCert : CertRef :=
  ⟨.list [.atom Lara.Ord.Tag.ordcmp.toString,
    .list [.atom Lara.Cell.Tag.prem.toString, .atom "0"],
    .list [.atom Lara.Cell.Tag.prem.toString, .atom "1"]]⟩

/-- The `ord@1`-certified premise node.  Unlike `shippedOrdChild` above — which
carries an ND-shaped payload because it only ever feeds a *syntactic* scan —
this node's payload is one `ord@1` actually decodes, which is what makes its
half of the golden non-empty. -/
def depsOrdNode : SupportTerm :=
  .inst depsOrdRuleId [] [.leaf depsOursLeaf, .leaf depsTheirsLeaf] [] []
    (.cert ordId depsOrdDigest depsOrdCert)

/-- The two-level heterogeneous term: a shipped `nd@1` root over a shipped
`ord@1` premise.  `slot1Cert` is `(hyp 1)`, exactly `certToSExpr (Hyp 1)` on
the Haskell side; the free context an ND certificate sees is
`premises ++ theory`, so slot 1 is theory entry 0. -/
def depsMixedTerm : SupportTerm :=
  .inst depsNdRuleId [] [depsOrdNode] [] [] (.cert ndId depsNdDigest slot1Cert)

/-! #### The two shipped `uses` reports, replayed in the kernel -/

/-- `Lara.Cell.parseCanonNat "0" = some 0`.  `String.toNat?` does not reduce by
`rfl`/`decide` under Lean 4.32's Slice-based `String`, but it is provable per
literal from `String.toNat?_eq_some_ofDigitChars` — the treatment
`Lara.ND.decodeNat_leading_zero_01` already uses. -/
theorem depsParseCanonNat0 : Lara.Cell.parseCanonNat "0" = some 0 := by
  unfold Lara.Cell.parseCanonNat
  rw [show "0".toNat? = some 0 from by
    rw [String.toNat?_eq_some_ofDigitChars (by
      apply String.isNat_of_isDigit
      · simp
      · intro c hc; simp at hc; subst hc; rfl)]
    rfl]
  rfl

/-- The same at `"1"`. -/
theorem depsParseCanonNat1 : Lara.Cell.parseCanonNat "1" = some 1 := by
  unfold Lara.Cell.parseCanonNat
  rw [show "1".toNat? = some 1 from by
    rw [String.toNat?_eq_some_ofDigitChars (by
      apply String.isNat_of_isDigit
      · simp
      · intro c hc; simp at hc; subst hc; rfl)]
    rfl]
  rfl

/-- **The shipped `ord@1` core reports both premise slots.**  No fixture: this
is `Lara.Ord.ordBackend`'s own `uses`, decoding the real wire payload. -/
theorem depsOrdUses : (Lara.Ord.ordBackend id).uses depsOrdCert = [0, 1] := by
  show Lara.Ord.ordUses depsOrdCert = [0, 1]
  simp [Lara.Ord.ordUses, depsOrdCert, Lara.Ord.decodeCert, Lara.Ord.Tag.parse,
    Lara.Ord.Tag.all, Lara.Ord.Tag.toString, Lara.Cell.decodeSlot,
    Lara.Cell.Tag.parse, Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
    depsParseCanonNat0, depsParseCanonNat1]

/-- **The shipped `nd@1` core reports slot 1.**  Again no fixture: this is
`Lara.Strict.ndBackend`'s `uses`, i.e. `Lara.ND.fv` of the decoded proof term. -/
theorem depsNdUses : (Lara.Strict.ndBackend id).uses slot1Cert = [1] := by
  show Lara.Strict.ndUses slot1Cert = [1]
  have h1 : Lara.ND.decodeNat "1" = some 1 := by
    change Lara.ND.decodeNat (Nat.repr 1) = some 1
    exact Lara.ND.decodeNat_repr 1
  simp [Lara.Strict.ndUses, slot1Cert, Lara.ND.decodeCert, Lara.ND.Tag.parse,
    h1, Lara.ND.fv]

/-! #### The reports, per node and unioned -/

/-- The `nd@1` root's own report: one theory entry, tagged with `nd@1` and its
digest.  `As = [depsComparison]` has length 1, so `resolveSlot` sends slot 1 to
theory entry `1 - 1 = 0`. -/
theorem depsMixedTerm_stepDeps :
    stepDeps PiDeps registryDeps depsMixedTerm =
      [.theoryEntry ndId depsNdDigest 0] := by
  simp [depsMixedTerm, stepDeps, PiDeps, depsNdRuleId, depsOrdRuleId,
    registryDeps, ndId, depsNdRegistered, depsNdRule, depsNdDigest,
    instAPats, instAPat, instPats, instPat, depsComparisonPat,
    depsNdUses, resolveSlot]

/-- The `ord@1` child's own report: both premise slots, each resolved to that
node's own instantiated premise atom.  The theory is empty, so both slots land
inside `As` and neither becomes a theory entry. -/
theorem depsOrdNode_stepDeps :
    stepDeps PiDeps registryDeps depsOrdNode =
      [.premise 0 depsCellOurs, .premise 1 depsCellTheirs] := by
  simp [depsOrdNode, stepDeps, PiDeps, depsOrdRuleId, registryDeps, ordId, ndId,
    depsOrdRegistered, depsOrdRule, depsOrdDigest, instAPats, instAPat,
    instPats, instPat, depsCellOursPat, depsCellTheirsPat, depsOrdUses,
    resolveSlot, depsCellOurs, depsCellTheirs]

/-- **Both shipped backends contribute, and neither contributes nothing.**

A golden in which one of the two identities reported an empty list would pass
byte-for-byte while proving nothing about heterogeneity, so the non-emptiness
of each half is asserted here rather than left to be read off the file. -/
theorem depsMixedTerm_both_halves_nonempty :
    stepDeps PiDeps registryDeps depsMixedTerm ≠ [] ∧
      stepDeps PiDeps registryDeps depsOrdNode ≠ [] := by
  constructor
  · rw [depsMixedTerm_stepDeps]; simp
  · rw [depsOrdNode_stepDeps]; simp

/-- **The union, over the shipped mixed term.**  Root first, then the premise
walk — `certDeps`' own traversal order.  This is the value the emitter encodes
into `test/backend-deps.golden`, and `test/StrictSpec.hs`'
`prop_mixedBackendDepsCollected` asserts the corresponding Haskell list. -/
theorem depsMixedTerm_certDeps :
    certDeps PiDeps registryDeps depsMixedTerm =
      [ .theoryEntry ndId depsNdDigest 0
      , .premise 0 depsCellOurs
      , .premise 1 depsCellTheirs ] := by
  show stepDeps PiDeps registryDeps depsMixedTerm ++
    certDepsList PiDeps registryDeps [depsOrdNode] ++
    certDepsDis PiDeps registryDeps [] = _
  rw [depsMixedTerm_stepDeps]
  show [CertDep.theoryEntry ndId depsNdDigest 0] ++
    (certDeps PiDeps registryDeps depsOrdNode ++ []) ++ [] = _
  show [CertDep.theoryEntry ndId depsNdDigest 0] ++
    ((stepDeps PiDeps registryDeps depsOrdNode ++
      certDepsList PiDeps registryDeps [SupportTerm.leaf depsOursLeaf,
        SupportTerm.leaf depsTheirsLeaf] ++
      certDepsDis PiDeps registryDeps []) ++ []) ++ [] = _
  rw [depsOrdNode_stepDeps]
  rfl

/-- The term really does name the two shipped identities, in root-then-premise
order.  Without this the golden could be a homogeneous term in disguise. -/
theorem depsMixedTerm_usedBackends :
    usedBackends depsMixedTerm = [ndId, ordId] := by
  simp [depsMixedTerm, depsOrdNode, usedBackends, usedBackendsList,
    usedBackendsDis]

/-! #### The second vector: escapes, nesting, and a repeated slot

`depsMixedTerm` leaves the interesting branches of *both* golden encoders dead:
no `TStr` and no escape character (so every `escapeCharGolden` branch is
unreached), no `con` with arguments (so `encodeTermsGolden` never recurses),
and no duplicate slot in any report (so the `insertGolden` / `nub` dedup path
never runs).  `depsDupTerm` — `test/StrictSpec.hs`' `dupTerm`, mirrored atom
for atom — exercises all three at once, again over the two shipped cores:

* its `nd@1` root reports premise slot 0, resolved to `depsNoteAtom`, whose
  term tree carries a `str` containing `"` and `\` and a `con` nested inside a
  `con`;
* its `ord@1` child carries `(ordcmp (prem 0) (prem 0))`, a certificate that
  names the same slot twice.

The repeated slot is the point of the vector.  Lean's `Backend.uses` is a
`List Nat` and carries the duplicate through, so `depsDupTerm_certDeps` below
pins a THREE-element pre-encoder list with `premise 0 cell(self, 7.5)` twice.
Haskell's adapters report a `Set Dependency`, so the duplicate collapses before
`resolve` ever runs and `test/StrictSpec.hs`' `prop_dupBackendDepsCollected`
pins a TWO-element list.  The two languages reach the encoder holding different
multiplicities and agree only because both encoders dedup — and the golden file
is what turns that agreement from an argument into an artifact.

The Haskell side must additionally *accept* the certificate (its collector
sees a report only through `CertAccepted`), which is why the self-comparison
goal is `num_le(7.5, 7.5)`: `7.5 ≤ 7.5` holds, where `num_lt` would reject.
Lean's `stepDeps` never calls acceptance, so only the goal's *shape* matters
here — but the term is kept acceptable anyway, so neither side carries a
vector the other cannot run.  The atoms, patterns, and rules live with the
other golden constants above `PiDeps`; what follows is the term and its
reports. -/

def depsSelfLeaf : LeafId := ⟨"e_self"⟩
def depsNoteLeaf : LeafId := ⟨"e_note"⟩

/-- The repeated-slot certificate `(ordcmp (prem 0) (prem 0))`, spelled through
the two backends' own keyword tables like `depsOrdCert`
(`test/StrictSpec.hs`' `dupOrdPayload`). -/
def depsDupOrdCert : CertRef :=
  ⟨.list [.atom Lara.Ord.Tag.ordcmp.toString,
    .list [.atom Lara.Cell.Tag.prem.toString, .atom "0"],
    .list [.atom Lara.Cell.Tag.prem.toString, .atom "0"]]⟩

/-- `(hyp 0)`, exactly `certToSExpr (Hyp 0)` on the Haskell side
(`test/StrictSpec.hs`' `dupNdPayload`). -/
def depsSlot0Cert : CertRef :=
  ⟨.list [.atom Lara.ND.Tag.hyp.toString, .atom "0"]⟩

/-- The repeated-slot `ord@1` node (`test/StrictSpec.hs`' `dupOrdNode`). -/
def depsDupOrdNode : SupportTerm :=
  .inst depsDupOrdRuleId [] [.leaf depsSelfLeaf] [] []
    (.cert ordId depsOrdDigest depsDupOrdCert)

/-- The second heterogeneous term: an `nd@1` root over a note leaf and the
repeated-slot `ord@1` node (`test/StrictSpec.hs`' `dupTerm`). -/
def depsDupTerm : SupportTerm :=
  .inst depsDupNdRuleId [] [.leaf depsNoteLeaf, depsDupOrdNode] [] []
    (.cert ndId depsNdDigest depsSlot0Cert)

/-- **The shipped `ord@1` core reports the same slot twice.**  No dedup happens
in `uses`: the `List Nat` report preserves the certificate's multiplicity,
which is exactly the multiplicity Haskell's `Set` report does not have. -/
theorem depsDupOrdUses : (Lara.Ord.ordBackend id).uses depsDupOrdCert = [0, 0] := by
  show Lara.Ord.ordUses depsDupOrdCert = [0, 0]
  simp [Lara.Ord.ordUses, depsDupOrdCert, Lara.Ord.decodeCert, Lara.Ord.Tag.parse,
    Lara.Ord.Tag.all, Lara.Ord.Tag.toString, Lara.Cell.decodeSlot,
    Lara.Cell.Tag.parse, Lara.Cell.Tag.all, Lara.Cell.Tag.toString,
    depsParseCanonNat0]

/-- **The shipped `nd@1` core reports slot 0.** -/
theorem depsDupNdUses : (Lara.Strict.ndBackend id).uses depsSlot0Cert = [0] := by
  show Lara.Strict.ndUses depsSlot0Cert = [0]
  have h0 : Lara.ND.decodeNat "0" = some 0 := by
    change Lara.ND.decodeNat (Nat.repr 0) = some 0
    exact Lara.ND.decodeNat_repr 0
  simp [Lara.Strict.ndUses, depsSlot0Cert, Lara.ND.decodeCert, Lara.ND.Tag.parse,
    Lara.ND.Tag.toString, h0, Lara.ND.fv]

/-- The `nd@1` root's own report: premise slot 0, resolved to the note atom.
`As = [depsNoteAtom, depsNumLeSelf]` has length 2, so slot 0 lands inside `As`. -/
theorem depsDupTerm_stepDeps :
    stepDeps PiDeps registryDeps depsDupTerm = [.premise 0 depsNoteAtom] := by
  simp [depsDupTerm, stepDeps, PiDeps, depsOrdRuleId, depsNdRuleId,
    depsDupOrdRuleId, depsDupNdRuleId, registryDeps, ndId,
    depsNdRegistered, depsDupNdRule, depsNdDigest, instAPats, instAPat,
    instPats, instPat, depsNotePat, depsNumLeSelfPat, depsDupNdUses,
    resolveSlot, depsNoteAtom]

/-- The `ord@1` child's own report: the same premise slot, TWICE — Lean's
pre-encoder multiplicity, pinned. -/
theorem depsDupOrdNode_stepDeps :
    stepDeps PiDeps registryDeps depsDupOrdNode =
      [.premise 0 depsCellSelf, .premise 0 depsCellSelf] := by
  simp [depsDupOrdNode, stepDeps, PiDeps, depsOrdRuleId, depsNdRuleId,
    depsDupOrdRuleId, registryDeps, ordId, ndId,
    depsOrdRegistered, depsDupOrdRule, depsOrdDigest, instAPats, instAPat,
    instPats, instPat, depsCellSelfPat, depsDupOrdUses, resolveSlot,
    depsCellSelf]

/-- **The union, over the second vector: three entries, the `ord@1` slot
repeated.**  This is the list the Lean encoder dedups, and the list Haskell
never has — `test/StrictSpec.hs`' `prop_dupBackendDepsCollected` pins the
two-entry counterpart.  The golden is where they meet. -/
theorem depsDupTerm_certDeps :
    certDeps PiDeps registryDeps depsDupTerm =
      [ .premise 0 depsNoteAtom
      , .premise 0 depsCellSelf
      , .premise 0 depsCellSelf ] := by
  show stepDeps PiDeps registryDeps depsDupTerm ++
    certDepsList PiDeps registryDeps [.leaf depsNoteLeaf, depsDupOrdNode] ++
    certDepsDis PiDeps registryDeps [] = _
  rw [depsDupTerm_stepDeps]
  show [CertDep.premise 0 depsNoteAtom] ++
    (certDeps PiDeps registryDeps (.leaf depsNoteLeaf) ++
      (certDeps PiDeps registryDeps depsDupOrdNode ++ [])) ++ [] = _
  show [CertDep.premise 0 depsNoteAtom] ++
    ([] ++ ((stepDeps PiDeps registryDeps depsDupOrdNode ++
      certDepsList PiDeps registryDeps [.leaf depsSelfLeaf] ++
      certDepsDis PiDeps registryDeps []) ++ [])) ++ [] = _
  rw [depsDupOrdNode_stepDeps]
  rfl

/-- The second vector also names the two shipped identities, root then
premise walk. -/
theorem depsDupTerm_usedBackends :
    usedBackends depsDupTerm = [ndId, ordId] := by
  simp [depsDupTerm, depsDupOrdNode, usedBackends, usedBackendsList,
    usedBackendsDis]

/-! #### The canonical textual encoding

The Lean and Haskell `certDeps` results are compared as *text*, through
`test/backend-deps.golden`.  The encoding is defined twice — here, and in
`test/StrictSpec.hs`' `encodeCertDepGolden` — and the two definitions must
agree byte for byte; `scripts/check-backend-deps-golden.sh` is what enforces
that they do.

**Grammar.**  One dependency per line.

```
  line   ::= "premise " nat " " atom
           | "theory " qstr " " nat " " qstr " " nat
  atom   ::= "(atom " qstr terms ")"
  terms  ::= { " " term }
  term   ::= "(num " qstr ")" | "(str " qstr ")" | "(con " qstr terms ")"
  qstr   ::= '"' { char | "\\\\" | "\\\"" | "\\n" | "\\t" } '"'
```

The `theory` line's two naturals are the backend *version* and the theory
*entry index*; its two quoted strings are the backend name and the theory
digest.  Nothing is dropped: every field of both `CertDep` constructors
appears, including the premise slot's resolved atom in full ground form.

**Sort order.**  Lines are emitted **sorted ascending by the encoded line
text**, compared as a sequence of Unicode code points (Lean `Char.val`,
Haskell `Char` — both are the code point, so the two orders coincide), and
**deduplicated**.  The order is on the *text*, not on the slot number: slot
`10` sorts before slot `2`.  That is deliberate — the order is a
canonicalization device, not a semantic ranking.

**Why deduplicated.**  Lean's per-node report is a `List Nat`
(`Backend.uses`); Haskell's is a `Set Dependency`.  A certificate naming the
same slot twice — `(ordcmp (prem 0) (prem 0))` — is a two-element list in Lean
and a one-element set in Haskell.  The two languages agree as *collections*,
which is what every accountability statement in `Lara/BackendComposition.lean`
is about, so multiplicity is deliberately not part of this contract and the
encoder canonicalizes it away on both sides.  This is not just an argument:
`depsDupTerm` carries exactly such a certificate, so `depsDupTerm_certDeps`
pins Lean's pre-dedup multiplicity while the golden pins the reconciled text
both sides emit. -/

/-- Code-point-lexicographic `<` on character lists.  Written out rather than
taken from `List.lt` so that the ordering the golden depends on is visibly the
same one `Data.List.sort` gives the Haskell encoder. -/
def charListLtGolden : List Char → List Char → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if x.val < y.val then true
      else if y.val < x.val then false
      else charListLtGolden xs ys

/-- Code-point-lexicographic `<` on strings. -/
def strLtGolden (a b : String) : Bool := charListLtGolden a.toList b.toList

/-- Insert into a sorted list, dropping an exact duplicate. -/
def insertGolden (x : String) : List String → List String
  | [] => [x]
  | y :: ys =>
      if x = y then y :: ys
      else if strLtGolden x y then x :: y :: ys
      else y :: insertGolden x ys

/-- Sort ascending and deduplicate. -/
def sortDedupGolden (xs : List String) : List String :=
  xs.foldl (fun acc x => insertGolden x acc) []

/-- Escape one character for a `qstr`. -/
def escapeCharGolden (c : Char) : String :=
  if c = '\\' then "\\\\"
  else if c = '"' then "\\\""
  else if c = '\n' then "\\n"
  else if c = '\t' then "\\t"
  else String.singleton c

/-- A quoted, escaped string literal. -/
def quoteGolden (s : String) : String :=
  "\"" ++ String.join (s.toList.map escapeCharGolden) ++ "\""

mutual
  /-- Encode a ground term. -/
  def encodeTermGolden : Term → String
    | .num s => "(num " ++ quoteGolden s ++ ")"
    | .str s => "(str " ++ quoteGolden s ++ ")"
    | .con k ts => "(con " ++ quoteGolden k ++ encodeTermsGolden ts ++ ")"
  /-- Encode an argument list, each element preceded by a single space. -/
  def encodeTermsGolden : Terms → String
    | .nil => ""
    | .cons t ts => " " ++ encodeTermGolden t ++ encodeTermsGolden ts
end

/-- Encode a ground atom. -/
def encodeAtomGolden : Atom → String
  | .atom p ts => "(atom " ++ quoteGolden p ++ encodeTermsGolden ts ++ ")"

/-- Encode one dependency as its golden line.  Mirrored by
`encodeCertDepGolden` in `test/StrictSpec.hs`. -/
def encodeCertDepGolden : CertDep → String
  | .premise i A => "premise " ++ toString i ++ " " ++ encodeAtomGolden A
  | .theoryEntry β hd t =>
      "theory " ++ quoteGolden β.name ++ " " ++ toString β.version ++ " " ++
        quoteGolden hd.hash ++ " " ++ toString t

/-- The canonical encoding of a whole dependency collection: sorted,
deduplicated, one line each. -/
def encodeCertDepsGolden (ds : List CertDep) : List String :=
  sortDedupGolden (ds.map encodeCertDepGolden)

/-- The golden body for the two shipped vectors — `depsMixedTerm` and
`depsDupTerm`, concatenated *before* encoding so the sort and dedup run over
the union — what `lean/BackendDepsGolden.lean` prints and
`test/backend-deps.golden` holds. -/
def backendDepsGolden : String :=
  String.intercalate "\n"
    (encodeCertDepsGolden
      (certDeps PiDeps registryDeps depsMixedTerm ++
        certDeps PiDeps registryDeps depsDupTerm))
end Lara.Examples.BackendComposition
