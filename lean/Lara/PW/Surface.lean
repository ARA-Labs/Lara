/-
# PW — surface syntax for the outer language (issue #307)

Before this module the outer language was Lean-side only: a bridge was a record
with three `Prop` fields, and a modal query was an intrinsically typed
`PW.Form`, which nothing outside Lean could author.
`docs/theory-pw-closeout.md` §3 recorded that as a boundary with no scheduling
condition; the condition it was really waiting on — M5's sorting machinery
(#188) — has since landed, so the `Query_κ` refinement (`Lara.PW.Sorted`) makes
a surface possible and this module supplies one.

**Two authoring forms.**

* `BridgeDecl` — declare a bridge: its symbol map, its evidence-leaf map, and
  the three structural clauses of T6's `StructuralBridge`.
* `SForm` / `Posed` — pose a modal query. The surface form is **untyped**:
  claims are raw `Atom`s and modal operators name a bridge by identifier.
  Elaboration is the typing pass that turns it into `PW.Form`, which is
  intrinsically typed by its context index.

**The M5 discipline, followed.** Like `Lara.Surface`, the theorem begins after
concrete parsing: the input is a structured AST, not source bytes, and the
environment is quantified (`Naming`, `BridgeEnv`) with its soundness premises
explicit. Each pass has an independent syntax-directed judgment, an executable
decider, and the `sound` / `complete` / `deterministic` trio; preservation and
reflection are stated separately and neither is defined as the other's
success. The judgments are independent of the *deciders* too, not only of the
elaborators: `ElaboratesBridge.rule_ok` is T6's clause verbatim rather than
`ruleOkB … = true`, and `Elaborates.status` says the typed query carries the
authored claim rather than `Sorted.pose … = .ok q`. `ruleOkB_iff` and
`Sorted.pose_ok_val` / `pose_val_self` are what bridge the two, so
sound/complete carry content on both sides.

**Joining the authoring forms.** `Lara.PW.Declared` builds a sorted frame and
its `Naming` from checked declarations. Its `elabPosed_declared` theorem links
every nested modal name to the original declaration and its symbol map (#313).
`Lara.PW.Wire` supplies concrete input and structured round trips (#314).

**What the elaborator can and cannot check.** T6's contract has three clauses,
and they are not alike:

* `rule_ok` **is decidable** from the two declared policies — a policy carries
  a finite `List RuleDecl` — so `ruleOkB` decides it and `ruleOkB_iff` proves
  the decider is the clause. This is the substantive gain from declaring the
  symbol map in the surface at all.
* `leaf_ok` and `cert_ok` **are not**: `Gamma` is a checker parameter (a
  function on all of `LeafId`) and `CertOk` is an arbitrary `Prop` over
  backends. They stay declared premises, named in `BridgeObligations` — the
  same shape as `Lara.Surface.Env`'s registry and identifier-classifier
  premises, and stated where they are used rather than assumed silently.

So `elabBridge_preserves` produces a real `PW.StructuralBridge`, and
`PW.support_transport` applies to a surface-authored bridge — but only against
the two premises the surface cannot discharge, which the type records.

No Mathlib; core Lean 4 only.
-/

import Lara.PW.Sorted
import Lara.PW.Structural

namespace Lara.PW.Surface

open Lara.Support
open Lara.Grounded (Status)

/-! ## 1. The surface AST

Symbolic, per the repository's core discipline: every domain identifier is its
own newtype, the clause vocabulary is a closed sum with one spelling table, and
no pass reads a bare `String` whose meaning depends on the concrete syntax. -/

/-- A scientific-context identifier in the outer surface. Distinct from every
core namespace: a context names a *checking environment*, not a rule, leaf or
claim. -/
structure CtxId where
  name : String
deriving DecidableEq

/-- A bridge identifier. -/
structure BridgeId where
  name : String
deriving DecidableEq

/-- One entry of a declared symbol map. Predicate and constructor namespaces
are declared separately because they are distinct symbol classes in the core
AST (`PredSym` vs `ConSym`), so one may be renamed while the other is out of
vocabulary — the same split `PW.SymMap` makes. -/
inductive SymEntry where
  | pred (source target : PredSym)
  | con (source target : ConSym)
deriving DecidableEq

/-- One entry of a declared evidence-leaf renaming. -/
structure LeafEntry where
  source : LeafId
  target : LeafId
deriving DecidableEq

/-- The three structural clauses a bridge declaration states. A closed sum, not
three string literals. -/
inductive Clause where
  /-- admitted evidence translates -/
  | leafOk
  /-- the target policy carries the translated rule at the same identifier -/
  | ruleOk
  /-- certificate acceptance survives translation -/
  | certOk
deriving DecidableEq, Repr

/-- The surface spelling of a clause — the one place the concrete names live,
following `Sigma.TermSort.text` and `Strict.ND.Tag`. -/
def Clause.text : Clause → String
  | .leafOk => "leaf-ok"
  | .ruleOk => "rule-ok"
  | .certOk => "cert-ok"

/-- The three clauses, in declaration order — the scan order of the
elaborator's completeness check, so a declaration missing two is reported
against the first. A declaration that omits one is rejected: the contract is
three clauses, and a bridge that states two of them is not a structural
bridge. -/
def Clause.all : List Clause := [.leafOk, .ruleOk, .certOk]

/-- `Clause.all` is the *type*, not a hand-maintained sample of it. Without
this the completeness check quantifies over a literal, and a fourth clause
added to `Clause` would silently stop being required — the one thing this type
exists to prevent. Adding a constructor breaks this `decide` at once. -/
theorem Clause.mem_all : ∀ c : Clause, c ∈ Clause.all
  | .leafOk => by decide
  | .ruleOk => by decide
  | .certOk => by decide

/-- **A bridge declaration.** -/
structure BridgeDecl where
  id : BridgeId
  source : CtxId
  target : CtxId
  /-- the declared symbol map, in declaration order -/
  symbols : List SymEntry
  /-- the declared evidence-leaf renaming, in declaration order -/
  leaves : List LeafEntry
  /-- the structural clauses this declaration states -/
  clauses : List Clause
deriving DecidableEq

/-- **A modal query, unelaborated.** Claims are raw `Atom`s and modalities name
a bridge by identifier; nothing here is typed by a context. Exactly PW0's
grammar and nothing more — no named-world operator, no dynamic operator, no
approximation syntax. -/
inductive SForm where
  | status (s : Status) (claim : Atom)
  | top
  | neg (form : SForm)
  | conj (left right : SForm)
  | box (bridge : BridgeId) (form : SForm)
  | dia (bridge : BridgeId) (form : SForm)
deriving DecidableEq

/-- A posed query: the context it is asked in, and the formula. -/
structure Posed where
  context : CtxId
  form : SForm
deriving DecidableEq

/-! ## 2. Assembling the declared maps

A declared entry list becomes a `PW.SymMap` and a `LeafId → LeafId`. Both are
first-match lookups over the declaration order, so the surface has a canonical
reading and the two runtimes would agree. -/

/-- The predicate half of a declared symbol map: first match wins, `none`
outside the declaration — which is the bridge's vocabulary boundary. -/
def predMapOf : List SymEntry → String → Option String
  | [], _ => none
  | .pred s t :: rest, p => if s.name = p then some t.name else predMapOf rest p
  | .con _ _ :: rest, p => predMapOf rest p

/-- The constructor half. -/
def conMapOf : List SymEntry → String → Option String
  | [], _ => none
  | .con s t :: rest, k => if s.name = k then some t.name else conMapOf rest k
  | .pred _ _ :: rest, k => conMapOf rest k

/-- The `PW.SymMap` a declaration denotes. -/
def symMapOf (entries : List SymEntry) : SymMap where
  predMap := predMapOf entries
  conMap := conMapOf entries

/-- The evidence-leaf renaming a declaration denotes. Total, because
`StructuralBridge.leafMap` is a total `LeafId → LeafId`; identity outside the
declaration is the only total extension under which the declaration order is
the sole determinant of the map, so no leaf is renamed by anything the author
did not write.

This does *not* make an empty declaration `StructuralBridge.refl`: `refl`'s
`sym` is `SymMap.id`, which is total, and no finite entry list is
(`predMapOf_eq_none`) — `refl` is not in this surface's image at all. -/
def leafMapOf : List LeafEntry → LeafId → LeafId
  | [], l => l
  | e :: rest, l => if e.source = l then e.target else leafMapOf rest l

/-- An empty declaration denotes the identity leaf map. -/
theorem leafMapOf_nil (l : LeafId) : leafMapOf [] l = l := rfl

/-- A declared leaf entry is honoured at its own source, provided no earlier
entry claims it. -/
theorem leafMapOf_cons_self (e : LeafEntry) (rest : List LeafEntry) :
    leafMapOf (e :: rest) e.source = e.target := by
  simp [leafMapOf]

/-- Declaration order decides: a later entry for an already-declared leaf is
shadowed, so the map is a function of the list and not of its order-forgetting
set. -/
theorem leafMapOf_cons_other (e : LeafEntry) (rest : List LeafEntry) (l : LeafId)
    (h : e.source ≠ l) : leafMapOf (e :: rest) l = leafMapOf rest l := by
  simp [leafMapOf, h]

/-! ## 3. The one clause the elaborator can check

`StructuralBridge.rule_ok` quantifies over `RuleId`, but a `Policy` carries its
rules as a finite list and `Policy.ruleLookup` reads exactly that list. So the
clause is decidable, and deciding it is what a declared symbol map buys. -/

/-- The executable `rule_ok` check: every rule the source policy resolves
translates, and the target policy carries the translation at the same
identifier. Scanning the declared identifiers rather than the declaration list
keeps the decider aligned with `ruleLookup`'s first-match reading, so a
shadowed duplicate is not held to a clause `ruleLookup` never consults. -/
def ruleOkB (m : SymMap) (ps pt : Lara.Policy.Policy) : Bool :=
  (ps.rules.map (·.id)).all fun rn =>
    match ps.ruleLookup rn with
    | none => true
    | some r =>
      match trRule m r with
      | none => false
      | some r' => pt.ruleLookup rn == some r'

/-- **The decider is the clause.** -/
theorem ruleOkB_iff (m : SymMap) (ps pt : Lara.Policy.Policy) :
    ruleOkB m ps pt = true ↔
      ∀ rn r, ps.ruleLookup rn = some r →
        ∃ r', trRule m r = some r' ∧ pt.ruleLookup rn = some r' := by
  constructor
  · intro h rn r hr
    obtain ⟨d, hd, hid, _⟩ := Lara.Policy.lookupRuleDecl_some_mem hr
    have hmem : rn ∈ ps.rules.map (·.id) :=
      List.mem_map.mpr ⟨d, hd, hid⟩
    have hall := List.all_eq_true.mp h rn hmem
    cases htr : trRule m r with
    | none => simp [hr, htr] at hall
    | some r' =>
      refine ⟨r', rfl, ?_⟩
      simpa [hr, htr] using hall
  · intro h
    refine List.all_eq_true.mpr ?_
    intro rn _
    cases hr : ps.ruleLookup rn with
    | none => simp
    | some r =>
      obtain ⟨r', htr, hpt⟩ := h rn r hr
      simp [htr, hpt]

/-! ## 4. Elaborating a bridge declaration

The output is the pair of maps the core wants; the judgment carries the
declaration's own well-formedness plus the one checked clause; and preservation
turns the two remaining premises into a `PW.StructuralBridge`. -/

/-- What a declaration elaborates to: exactly the data
`PW.StructuralBridge` carries. -/
structure Bridge where
  sym : SymMap
  leafMap : LeafId → LeafId

/-- The two clauses the elaborator cannot decide, named. `Gamma` is a checker
*parameter*, so `leaf_ok` quantifies over a function the surface never sees;
`CertOk` is an arbitrary `Prop` over backends. Declaring them here rather than
assuming them silently is the M5 discipline for `Env`'s soundness premises. -/
structure BridgeObligations (canon : String → String)
    (Gamma Gamma' : LeafId → Option Atom)
    (CertOk CertOk' : BackendId → Digest → CertRef → List Atom → Atom → Prop)
    (out : Bridge) : Prop where
  /-- the `leafOk` clause the declaration states -/
  leaf_ok : ∀ l p, Gamma l = some p →
    ∃ p', trAtom out.sym p = some p' ∧ Gamma' (out.leafMap l) = some p'
  /-- the `certOk` clause the declaration states -/
  cert_ok : ∀ β hd κ As C As' C', trAtoms out.sym As = some As' →
    trAtom out.sym C = some C' → CertOk β hd κ As C → CertOk' β hd κ As' C'

/-- Why a bridge declaration is not elaborable. The canonicalizer agreement is
not among them, because it is not a checkable condition (see
`BridgeEnv.canon_shared`); everything else the declaration writes down *is*
checked, and each error names what it found against what the environment
declares. -/
inductive BridgeError where
  /-- the declaration names a bridge other than the environment's -/
  | nameMismatch (declared expected : BridgeId)
  /-- the declaration's source context is not the environment's -/
  | sourceMismatch (declared expected : CtxId)
  /-- the declaration's target context is not the environment's -/
  | targetMismatch (declared expected : CtxId)
  /-- the declaration does not state all three clauses -/
  | missingClause (clause : Clause)
  /-- the declared symbol map does not carry the source policy's rules to the
  target policy — the one clause of T6's contract the elaborator decides -/
  | ruleClauseFails
deriving DecidableEq

/-- The environment a bridge declaration is elaborated against: the two
contexts it names, already resolved, *and their names*. Without the names the
declaration's own `id`, `source` and `target` would be read by nothing, and a
declaration reading `src → tgt` would elaborate identically against any
environment — so "T6 at a surface-authored bridge" would really be "T6 at
whatever environment the caller supplied".

Resolution itself is the caller's: this environment is what a resolver
*produced*, and the elaborator checks the declaration against it. The checked
loader in `Lara.PW.Declared` constructs this environment from resolved contexts
and derives `Naming.bridgeOf` from its registry of checked declarations.
Its `elabPosed_declared` theorem joins the two authoring forms at every modal
occurrence (#313). Low-level callers may still use `BridgeEnv` directly. -/
structure BridgeEnv where
  /-- the name this environment is the bridge for -/
  name : BridgeId
  /-- the name of the source context, as an author writes it -/
  sourceName : CtxId
  /-- the name of the target context -/
  targetName : CtxId
  source : Instance.Context
  target : Instance.Context
  /-- `PW.StructuralBridge` is stated over a *shared* source canonicalizer —
  the one thing two bridged environments must agree on for their conclusions to
  be comparable as claims (`docs/theory-pw-t6-structural-transport.md`). This
  is not a checkable condition: `canon` is a function, and function equality is
  undecidable. So it is a field of the declared environment rather than a
  clause the elaborator pretends to verify, and
  `elabBridge_support_transport` is where it becomes load-bearing. -/
  canon_shared : source.canon = target.canon

/-- The reported error, if any. Stated so negative fixtures can be closed by
`decide`: `Bridge` carries functions and therefore has no `DecidableEq`, while
`BridgeError` does. -/
def bridgeError? : Except BridgeError Bridge → Option BridgeError
  | .error e => some e
  | .ok _ => none

theorem bridgeError?_eq_none_iff (r : Except BridgeError Bridge) :
    bridgeError? r = none ↔ ∃ out, r = .ok out := by
  cases r with
  | error e => simp [bridgeError?]
  | ok out => simp [bridgeError?]

/-- **The independent judgment.** Syntax-directed and defined without reference
to `elabBridge` — and, in the substantive clause, without reference to the
*decider* either: `rule_ok` states `StructuralBridge.rule_ok` verbatim, and
`ruleOkB_iff` is what connects it to `ruleOkB`. A declaration elaborates to
`out` when it names the environment's bridge and contexts, states all three
clauses, satisfies the checkable clause, and `out` is the maps it denotes. -/
structure ElaboratesBridge (E : BridgeEnv) (d : BridgeDecl) (out : Bridge) :
    Prop where
  /-- the declaration is *this* bridge's, between *these* contexts -/
  name_eq : d.id = E.name
  source_eq : d.source = E.sourceName
  target_eq : d.target = E.targetName
  /-- all three clauses of the contract are stated — quantified over the
  `Clause` type, not over `Clause.all` -/
  clauses_complete : ∀ c : Clause, c ∈ d.clauses
  /-- the checkable clause, stated as T6 states it -/
  rule_ok : ∀ rn r, E.source.policy.ruleLookup rn = some r →
    ∃ r', trRule out.sym r = some r' ∧ E.target.policy.ruleLookup rn = some r'
  /-- the output is what the declaration denotes -/
  sym_eq : out.sym = symMapOf d.symbols
  leafMap_eq : out.leafMap = leafMapOf d.leaves

/-- **The executable elaborator.** -/
def elabBridge (E : BridgeEnv) (d : BridgeDecl) : Except BridgeError Bridge :=
  if d.id ≠ E.name then .error (.nameMismatch d.id E.name)
  else if d.source ≠ E.sourceName then .error (.sourceMismatch d.source E.sourceName)
  else if d.target ≠ E.targetName then .error (.targetMismatch d.target E.targetName)
  else
    match Clause.all.find? (fun c => !d.clauses.contains c) with
    | some c => .error (.missingClause c)
    | none =>
      let out : Bridge := ⟨symMapOf d.symbols, leafMapOf d.leaves⟩
      if ruleOkB out.sym E.source.policy E.target.policy then .ok out
      else .error .ruleClauseFails

/-- Every clause is stated exactly when the scan finds no missing one. Stated
over the `Clause` *type* on the right, via `Clause.mem_all`: the scan is
complete for the contract, not merely for a list someone maintains. -/
theorem find?_missing_none_iff (d : BridgeDecl) :
    Clause.all.find? (fun c => !d.clauses.contains c) = none ↔
      ∀ c : Clause, c ∈ d.clauses := by
  rw [List.find?_eq_none]
  constructor
  · intro h c
    have := h c (Clause.mem_all c)
    simpa using this
  · intro h c _
    simpa using h c

theorem elabBridge_sound (E : BridgeEnv) (d : BridgeDecl) (out : Bridge)
    (h : elabBridge E d = .ok out) : ElaboratesBridge E d out := by
  unfold elabBridge at h
  by_cases hn : d.id ≠ E.name
  · rw [if_pos hn] at h; exact absurd h (by simp)
  rw [if_neg hn] at h
  by_cases hs : d.source ≠ E.sourceName
  · rw [if_pos hs] at h; exact absurd h (by simp)
  rw [if_neg hs] at h
  by_cases ht : d.target ≠ E.targetName
  · rw [if_pos ht] at h; exact absurd h (by simp)
  rw [if_neg ht] at h
  cases hfind : Clause.all.find? (fun c => !d.clauses.contains c) with
  | some c => rw [hfind] at h; exact absurd h (by simp)
  | none =>
    rw [hfind] at h
    by_cases hrule :
        ruleOkB (symMapOf d.symbols) E.source.policy E.target.policy = true
    · simp only [hrule, if_pos] at h
      have hout : out = ⟨symMapOf d.symbols, leafMapOf d.leaves⟩ :=
        (Except.ok.inj h).symm
      subst hout
      exact
        { name_eq := by simpa using hn
        , source_eq := by simpa using hs
        , target_eq := by simpa using ht
        , clauses_complete := (find?_missing_none_iff d).mp hfind
        , rule_ok :=
            (ruleOkB_iff (symMapOf d.symbols) E.source.policy E.target.policy).mp hrule
        , sym_eq := rfl
        , leafMap_eq := rfl }
    · simp only [hrule, Bool.false_eq_true] at h
      exact absurd h (by simp)

theorem elabBridge_complete (E : BridgeEnv) (d : BridgeDecl) (out : Bridge)
    (h : ElaboratesBridge E d out) : elabBridge E d = .ok out := by
  have hout : out = ⟨symMapOf d.symbols, leafMapOf d.leaves⟩ := by
    cases out with
    | mk sym leafMap =>
      simp only [Bridge.mk.injEq]
      exact ⟨h.sym_eq, h.leafMap_eq⟩
  have hrule : ruleOkB (symMapOf d.symbols) E.source.policy E.target.policy = true := by
    refine (ruleOkB_iff (symMapOf d.symbols) E.source.policy E.target.policy).mpr ?_
    intro rn r hr
    have := h.rule_ok rn r hr
    rwa [h.sym_eq] at this
  subst hout
  unfold elabBridge
  rw [if_neg (not_not_intro h.name_eq), if_neg (not_not_intro h.source_eq),
    if_neg (not_not_intro h.target_eq),
    (find?_missing_none_iff d).mpr h.clauses_complete]
  simp only [hrule, if_pos]

/-- Elaboration is a function of the declaration. -/
theorem elaboratesBridge_deterministic (E : BridgeEnv) (d : BridgeDecl)
    {out₁ out₂ : Bridge} (h₁ : ElaboratesBridge E d out₁)
    (h₂ : ElaboratesBridge E d out₂) : out₁ = out₂ := by
  cases out₁ with
  | mk s₁ l₁ =>
    cases out₂ with
    | mk s₂ l₂ =>
      simp only [Bridge.mk.injEq]
      exact ⟨h₁.sym_eq.trans h₂.sym_eq.symm,
        h₁.leafMap_eq.trans h₂.leafMap_eq.symm⟩

/-! ### Preservation — a surface bridge is a `StructuralBridge`

The point of the whole pass. With the two premises the surface cannot decide,
a derivable declaration yields T6's contract at the two declared contexts, so
`PW.support_transport` applies to a surface-authored bridge. -/

/-- The `PW.StructuralBridge` a derivable declaration denotes. The two
undecidable clauses come in as `hobl`; the third is the judgment's own
`rule_ok`, which is T6's clause verbatim (the elaborator reaches it through
`ruleOkB_iff`, but the contract does not go through the decider). -/
def structuralBridgeOf (E : BridgeEnv) (d : BridgeDecl) (out : Bridge)
    (helab : ElaboratesBridge E d out)
    (hobl : BridgeObligations E.source.canon E.source.Gamma E.target.Gamma
      E.source.CertOk E.target.CertOk out) :
    StructuralBridge E.source.canon
      E.source.policy.ruleLookup E.target.policy.ruleLookup
      E.source.Gamma E.target.Gamma E.source.CertOk E.target.CertOk where
  sym := out.sym
  leafMap := out.leafMap
  leaf_ok := hobl.leaf_ok
  rule_ok := helab.rule_ok
  cert_ok := hobl.cert_ok

/-- **Preservation.** A derivable bridge declaration lowers successfully, and
the object it lowers to *is* T6's contract with the elaborated maps — not some
other pair.

The substantive conjunct is the first, `elabBridge_complete`; the two map
equations hold definitionally, because `structuralBridgeOf` is *built* from
`out`. They are stated anyway so that a later change to that construction —
one that normalized or re-derived the maps — would break here rather than
silently. The thing carrying "a derivable declaration is T6's contract" is the
*type* of `structuralBridgeOf`, and `Examples.PWSurface.bridge_declOK`
instantiates it at a concrete declaration with `BridgeObligations` discharged,
so the type is exercised and not merely written. -/
theorem elabBridge_preserves (E : BridgeEnv) (d : BridgeDecl) (out : Bridge)
    (helab : ElaboratesBridge E d out)
    (hobl : BridgeObligations E.source.canon E.source.Gamma E.target.Gamma
      E.source.CertOk E.target.CertOk out) :
    elabBridge E d = .ok out ∧
      (structuralBridgeOf E d out helab hobl).sym = out.sym ∧
      (structuralBridgeOf E d out helab hobl).leafMap = out.leafMap :=
  ⟨elabBridge_complete E d out helab, rfl, rfl⟩

/-- **T6 at a surface-authored bridge.** The transport theorem applies to the
declaration, and its conclusion is a judgment of the *target context's own*
checking environment — which is exactly what `BridgeEnv.canon_shared` buys:
without it the conclusion would be stated at `E.source.canon`, which is not the
target's judgment. -/
theorem elabBridge_support_transport (E : BridgeEnv) (d : BridgeDecl)
    (out : Bridge) (helab : ElaboratesBridge E d out)
    (hobl : BridgeObligations E.source.canon E.source.Gamma E.target.Gamma
      E.source.CertOk E.target.CertOk out)
    {w w' : SupportTerm} {C : Atom} {O : List QuestionId}
    (hs : HasSupport E.source.canon E.source.policy.ruleLookup E.source.Gamma
      E.source.CertOk w C O)
    (htr : trSupport out.sym out.leafMap w = some w') :
    ∃ C', trAtom out.sym C = some C' ∧
      HasSupport E.target.canon E.target.policy.ruleLookup E.target.Gamma
        E.target.CertOk w' C' O := by
  rw [← E.canon_shared]
  exact support_transport (structuralBridgeOf E d out helab hobl) hs htr

/-- **Reflection.** From a successful lowering back to the independent
judgment. It quantifies over the lowering a caller who ran the elaborator
actually has, not over arbitrary `Bridge` values. -/
theorem elabBridge_reflects (E : BridgeEnv) (d : BridgeDecl) (out : Bridge)
    (helab : elabBridge E d = .ok out) :
    ElaboratesBridge E d out :=
  elabBridge_sound E d out helab

/-- **The bridge's vocabulary is exactly what the surface writes down**: the
declared symbol map is undefined outside its declaration. A consequence worth
stating, because it bounds what the surface can express: `SymMap.id` is total
and no finite entry list is, so `StructuralBridge.refl` — the identity
endobridge T6 uses — is *not* in the image of this surface. That is a boundary
of the authoring form, not of the model; a surface-declared bridge always
carries a finite, explicitly written vocabulary. -/
theorem predMapOf_eq_none (entries : List SymEntry) (p : String)
    (h : ∀ s t, SymEntry.pred s t ∈ entries → s.name ≠ p) :
    predMapOf entries p = none := by
  induction entries with
  | nil => rfl
  | cons e rest ih =>
    cases e with
    | pred s t =>
      have hne : s.name ≠ p := h s t (by simp)
      simp only [predMapOf, hne, reduceIte]
      exact ih (fun s' t' hmem => h s' t' (by simp [hmem]))
    | con s t =>
      simp only [predMapOf]
      exact ih (fun s' t' hmem => h s' t' (by simp [hmem]))

/-- A well-named, clause-complete declaration elaborates whenever the source
policy declares no rules: the one checked clause is vacuous there, so the
surface's only obstruction is the vocabulary it writes. -/
theorem elabBridge_of_no_rules (E : BridgeEnv) (d : BridgeDecl)
    (hname : d.id = E.name) (hsrc : d.source = E.sourceName)
    (htgt : d.target = E.targetName)
    (hclauses : ∀ c : Clause, c ∈ d.clauses)
    (hrules : E.source.policy.rules = []) :
    elabBridge E d = .ok ⟨symMapOf d.symbols, leafMapOf d.leaves⟩ := by
  unfold elabBridge
  rw [if_neg (not_not_intro hname), if_neg (not_not_intro hsrc),
    if_neg (not_not_intro htgt), (find?_missing_none_iff d).mpr hclauses]
  have hrule :
      ruleOkB (symMapOf d.symbols) E.source.policy E.target.policy = true := by
    unfold ruleOkB
    rw [hrules]
    simp
  simp only [hrule, if_pos]


/-! ## 5. Elaborating a posed modal query

`SForm` is untyped: its claims are raw `Atom`s and its modalities name a bridge
by identifier. `PW.Form` is intrinsically typed by its context index, and its
status atoms carry `Sorted.Query`s. Elaboration is therefore a genuine typing
pass, and it is where the two halves of #307 meet: **posing a status atom is
`Sorted.pose`**, so a surface query whose claim is out of vocabulary or
ill-sorted is an elaboration error naming the fault, not a `gap` at some world.

The environment is a naming of an existing sorted frame — the M5 discipline of
quantifying the environment with explicit soundness premises. `Naming` supplies
both directions of the correspondence, which is what lets the elaborator decide
context equality by comparing *names* (decidable) instead of frame indices
(which carry no `DecidableEq`). -/

/-- A naming of a sorted frame's contexts and bridges. The premises make
`ctxOf`/`ctxName` and `bridgeOf`/`bridgeName` a partial bijection, which is all
the elaborator needs and strictly less than assuming decidable equality on the
frame's index types. -/
structure Naming (D : Sorted.SortedBridgeData) where
  ctxName : D.K → CtxId
  bridgeName : D.B → BridgeId
  ctxOf : CtxId → Option D.K
  bridgeOf : BridgeId → Option D.B
  ctxOf_ctxName : ∀ κ, ctxOf (ctxName κ) = some κ
  bridgeOf_bridgeName : ∀ b, bridgeOf (bridgeName b) = some b
  /-- Resolution is single-valued in the other direction too: a bridge has one
  declared name. Needed for preservation — without it two names could resolve
  to one bridge and the round trip would rename the authored query. -/
  bridgeName_of_bridgeOf : ∀ n b, bridgeOf n = some b → bridgeName b = n
  /-- The same for contexts, and for the same reason one level down: error
  location. `elabForm` reports `notAQuery (ctxName κ) …` and
  `bridgeSourceMismatch _ (ctxName κ) …`, so without this a report could name a
  context spelling the author never wrote, while the bridge names in the same
  reports are guaranteed to echo the source. -/
  ctxName_of_ctxOf : ∀ n κ, ctxOf n = some κ → ctxName κ = n

namespace Naming

variable {D : Sorted.SortedBridgeData}

/-- Names identify contexts: the naming's two directions force it. This is the
lemma that lets the elaborator compare `CtxId`s where the frame offers no
`DecidableEq`. -/
theorem ctxName_inj (E : Naming D) {κ₁ κ₂ : D.K} (h : E.ctxName κ₁ = E.ctxName κ₂) :
    κ₁ = κ₂ := by
  have h₁ := E.ctxOf_ctxName κ₁
  have h₂ := E.ctxOf_ctxName κ₂
  rw [h] at h₁
  rw [h₂] at h₁
  exact (Option.some.inj h₁).symm

theorem bridgeName_inj (E : Naming D) {b₁ b₂ : D.B}
    (h : E.bridgeName b₁ = E.bridgeName b₂) : b₁ = b₂ := by
  have h₁ := E.bridgeOf_bridgeName b₁
  have h₂ := E.bridgeOf_bridgeName b₂
  rw [h] at h₁
  rw [h₂] at h₁
  exact (Option.some.inj h₁).symm

end Naming

/-- Why a posed query does not elaborate. -/
inductive FormError where
  /-- the query is posed in an undeclared context -/
  | unknownContext (context : CtxId)
  /-- the formula names an undeclared bridge -/
  | unknownBridge (bridge : BridgeId)
  /-- the named bridge does not start at the context the query is posed in -/
  | bridgeSourceMismatch (bridge : BridgeId) (expected found : CtxId)
  /-- a status atom's claim is not a query of its context — half 1's fault,
  surfaced at authoring time instead of as a `gap` at some world -/
  | notAQuery (context : CtxId) (fault : Sorted.QueryFault)
deriving DecidableEq

section Elaborate

variable {D : Sorted.SortedBridgeData}

/-- The reported error, if any — the `FormError` counterpart of
`bridgeError?`, and for the same reason: `PW.Form` has no `DecidableEq`. -/
def formError? {κ : D.frame.K} : Except FormError (Form D.frame κ) →
    Option FormError
  | .error e => some e
  | .ok _ => none

theorem formError?_eq_none_iff {κ : D.frame.K}
    (r : Except FormError (Form D.frame κ)) :
    formError? r = none ↔ ∃ Φ, r = .ok Φ := by
  cases r with
  | error e => simp [formError?]
  | ok Φ => simp [formError?]

/-- **The independent judgment.** Syntax-directed, with no reference to
`elabForm` and none to `Sorted.pose` either: no constructor calls the
elaborator, and none is defined by another procedure's success. The status
case says what elaborating a status atom *means* — the typed query carries the
authored claim — and `Sorted.pose_ok_val` / `pose_val_self` are what connect
that to the decider. The `box`/`dia` constructors are stated *at the bridge's
own source context*, which is why the judgment needs no transport.

The well-sortedness side condition needs no field: `Sorted.Query` is a
subtype, so `q` already carries a proof that `q.val` is a query of its
context's signature, and `q.val = c` transfers it to the authored claim. -/
inductive Elaborates (E : Naming D) :
    {κ : D.frame.K} → SForm → Form D.frame κ → Prop where
  | status {κ : D.frame.K} (s : Status) (c : Atom)
      (q : Sorted.Query (D.ctx κ).sigma) :
      q.val = c →
      Elaborates E (.status s c) (.status s q)
  | top {κ : D.frame.K} : Elaborates E (κ := κ) .top .top
  | neg {κ : D.frame.K} {φ : SForm} {Φ : Form D.frame κ} :
      Elaborates E φ Φ → Elaborates E (.neg φ) (.neg Φ)
  | conj {κ : D.frame.K} {φ ψ : SForm} {Φ Ψ : Form D.frame κ} :
      Elaborates E φ Φ → Elaborates E ψ Ψ →
      Elaborates E (.conj φ ψ) (.conj Φ Ψ)
  | box {b : D.frame.B} {n : BridgeId} {φ : SForm}
      {Φ : Form D.frame (D.frame.tgt b)} :
      E.bridgeOf n = some b → Elaborates E φ Φ →
      Elaborates E (κ := D.frame.src b) (.box n φ) (.box b Φ)
  | dia {b : D.frame.B} {n : BridgeId} {φ : SForm}
      {Φ : Form D.frame (D.frame.tgt b)} :
      E.bridgeOf n = some b → Elaborates E φ Φ →
      Elaborates E (κ := D.frame.src b) (.dia n φ) (.dia b Φ)

/-- **The executable elaborator.** Its one dependent step is the modal case:
the operand elaborates at the bridge's target context, the result is a formula
at the bridge's *source* context, and the query's own context must be that one
— checked by name and transported by `Naming.ctxName_inj`. -/
def elabForm (E : Naming D) : (κ : D.frame.K) → SForm →
    Except FormError (Form D.frame κ)
  | κ, .status s c =>
    match Sorted.pose (D.ctx κ).sigma c with
    | .error f => .error (.notAQuery (E.ctxName κ) f)
    | .ok q => .ok (.status s q)
  | _, .top => .ok .top
  | κ, .neg φ =>
    match elabForm E κ φ with
    | .error e => .error e
    | .ok Φ => .ok (.neg Φ)
  | κ, .conj φ ψ =>
    match elabForm E κ φ, elabForm E κ ψ with
    | .ok Φ, .ok Ψ => .ok (.conj Φ Ψ)
    | .error e, _ => .error e
    | _, .error e => .error e
  | κ, .box n φ =>
    match E.bridgeOf n with
    | none => .error (.unknownBridge n)
    | some b =>
      if hk : E.ctxName (D.frame.src b) = E.ctxName κ then
        match elabForm E (D.frame.tgt b) φ with
        | .error e => .error e
        | .ok Φ => .ok (E.ctxName_inj hk ▸ Form.box (F := D.frame) b Φ)
      else .error (.bridgeSourceMismatch n (E.ctxName κ) (E.ctxName (D.frame.src b)))
  | κ, .dia n φ =>
    match E.bridgeOf n with
    | none => .error (.unknownBridge n)
    | some b =>
      if hk : E.ctxName (D.frame.src b) = E.ctxName κ then
        match elabForm E (D.frame.tgt b) φ with
        | .error e => .error e
        | .ok Φ => .ok (E.ctxName_inj hk ▸ Form.dia (F := D.frame) b Φ)
      else .error (.bridgeSourceMismatch n (E.ctxName κ) (E.ctxName (D.frame.src b)))

/-- **Soundness.** A successful elaboration is a derivation. -/
theorem elabForm_sound (E : Naming D) :
    ∀ {κ : D.frame.K} (φ : SForm) {Φ : Form D.frame κ},
      elabForm E κ φ = .ok Φ → Elaborates E φ Φ := by
  intro κ φ
  induction φ generalizing κ with
  | status s c =>
    intro Φ h
    unfold elabForm at h
    cases hp : Sorted.pose (D.ctx κ).sigma c with
    | error f => rw [hp] at h; exact absurd h (by simp)
    | ok q =>
      rw [hp] at h
      cases h
      exact .status s c q (Sorted.pose_ok_val hp)
  | top =>
    intro Φ h
    unfold elabForm at h
    cases h
    exact .top
  | neg φ ih =>
    intro Φ h
    unfold elabForm at h
    cases hφ : elabForm E κ φ with
    | error e => rw [hφ] at h; exact absurd h (by simp)
    | ok Φ' =>
      rw [hφ] at h
      cases h
      exact .neg (ih hφ)
  | conj φ ψ ihφ ihψ =>
    intro Φ h
    unfold elabForm at h
    cases hφ : elabForm E κ φ with
    | error e => rw [hφ] at h; simp at h
    | ok Φ' =>
      cases hψ : elabForm E κ ψ with
      | error e => rw [hφ, hψ] at h; simp at h
      | ok Ψ' =>
        rw [hφ, hψ] at h
        cases h
        exact .conj (ihφ hφ) (ihψ hψ)
  | box n φ ih =>
    intro Φ h
    unfold elabForm at h
    cases hb : E.bridgeOf n with
    | none => simp only [hb] at h; exact absurd h (by simp)
    | some b =>
      simp only [hb] at h
      by_cases hk : E.ctxName (D.frame.src b) = E.ctxName κ
      · rw [dif_pos hk] at h
        have hsrc : D.frame.src b = κ := E.ctxName_inj hk
        subst hsrc
        cases hφ : elabForm E (D.frame.tgt b) φ with
        | error e => rw [hφ] at h; exact absurd h (by simp)
        | ok Φ' =>
          rw [hφ] at h
          simp only [Except.ok.injEq] at h
          subst h
          exact .box hb (ih hφ)
      · rw [dif_neg hk] at h; exact absurd h (by simp)
  | dia n φ ih =>
    intro Φ h
    unfold elabForm at h
    cases hb : E.bridgeOf n with
    | none => simp only [hb] at h; exact absurd h (by simp)
    | some b =>
      simp only [hb] at h
      by_cases hk : E.ctxName (D.frame.src b) = E.ctxName κ
      · rw [dif_pos hk] at h
        have hsrc : D.frame.src b = κ := E.ctxName_inj hk
        subst hsrc
        cases hφ : elabForm E (D.frame.tgt b) φ with
        | error e => rw [hφ] at h; exact absurd h (by simp)
        | ok Φ' =>
          rw [hφ] at h
          simp only [Except.ok.injEq] at h
          subst h
          exact .dia hb (ih hφ)
      · rw [dif_neg hk] at h; exact absurd h (by simp)

/-- **Completeness.** A derivation is realized by the elaborator, at the same
output. -/
theorem elabForm_complete (E : Naming D) :
    ∀ {κ : D.frame.K} {φ : SForm} {Φ : Form D.frame κ},
      Elaborates E φ Φ → elabForm E κ φ = .ok Φ := by
  intro κ φ Φ h
  induction h with
  | @status κ' s c q hq =>
    have hp : Sorted.pose (D.ctx κ').sigma c = .ok q := hq ▸ Sorted.pose_val_self q
    simp [elabForm, hp]
  | top => rfl
  | neg _ ih => simp [elabForm, ih]
  | conj _ _ ihφ ihψ => simp [elabForm, ihφ, ihψ]
  | @box b n φ Φ hb _ ih =>
    have hk : E.ctxName (D.frame.src b) = E.ctxName (D.frame.src b) := rfl
    simp only [elabForm, hb, ih]
    congr 1
  | @dia b n φ Φ hb _ ih =>
    have hk : E.ctxName (D.frame.src b) = E.ctxName (D.frame.src b) := rfl
    simp only [elabForm, hb, ih]
    congr 1

/-- Elaboration is a function of the surface query and its context. -/
theorem elaborates_deterministic (E : Naming D) {κ : D.frame.K} {φ : SForm}
    {Φ₁ Φ₂ : Form D.frame κ} (h₁ : Elaborates E φ Φ₁) (h₂ : Elaborates E φ Φ₂) :
    Φ₁ = Φ₂ :=
  Except.ok.inj ((elabForm_complete E h₁).symm.trans (elabForm_complete E h₂))

/-! ### Preservation and reflection

`unelab` forgets the typing: status atoms drop to their claims, modalities drop
to their bridges' names. Preservation is the round trip — the elaborator does
not rewrite the authored query — and reflection recovers the derivation from a
formula that erases to the surface one. -/

/-- Forget the elaboration of a formula. -/
def unelab (E : Naming D) : {κ : D.frame.K} → Form D.frame κ → SForm
  | _, .status s q => .status s q.val
  | _, .top => .top
  | _, .neg Φ => .neg (unelab E Φ)
  | _, .conj Φ Ψ => .conj (unelab E Φ) (unelab E Ψ)
  | _, .box b Φ => .box (E.bridgeName b) (unelab E Φ)
  | _, .dia b Φ => .dia (E.bridgeName b) (unelab E Φ)

/-- **Preservation.** A derivable query elaborates, and the elaborated formula
erases back to exactly the query that was authored: nothing is renamed,
reassociated, or dropped. -/
theorem elaborates_preserves (E : Naming D) :
    ∀ {κ : D.frame.K} {φ : SForm} {Φ : Form D.frame κ},
      Elaborates E φ Φ → elabForm E κ φ = .ok Φ ∧ unelab E Φ = φ := by
  intro κ φ Φ h
  refine ⟨elabForm_complete E h, ?_⟩
  induction h with
  | status s c q hq =>
    show SForm.status s q.val = SForm.status s c
    rw [hq]
  | top => rfl
  | neg _ ih => exact congrArg SForm.neg ih
  | @conj κ' φ' ψ' Φ' Ψ' _ _ ihφ ihψ =>
    show SForm.conj (unelab E Φ') (unelab E Ψ') = SForm.conj φ' ψ'
    rw [ihφ, ihψ]
  | @box b n φ Φ hb _ ih =>
    show SForm.box (E.bridgeName b) (unelab E Φ) = SForm.box n φ
    rw [ih, E.bridgeName_of_bridgeOf n b hb]
  | @dia b n φ Φ hb _ ih =>
    show SForm.dia (E.bridgeName b) (unelab E Φ) = SForm.dia n φ
    rw [ih]
    rw [E.bridgeName_of_bridgeOf n b hb]

/-- **Reflection.** A core formula whose erasure is the authored query *is* its
elaboration — so the elaborator's output is determined by the surface, and no
other typed formula erases to the same query at the same context. Its
hypotheses are the ones a caller holding an already-lowered formula has. -/
theorem elaborates_reflects (E : Naming D) :
    ∀ {κ : D.frame.K} (Φ : Form D.frame κ), Elaborates E (unelab E Φ) Φ := by
  intro κ Φ
  induction Φ with
  | status s q => exact .status s q.val q rfl
  | top => exact .top
  | neg Φ ih => exact .neg ih
  | conj Φ Ψ ihΦ ihΨ => exact .conj ihΦ ihΨ
  | box b Φ ih => exact .box (E.bridgeOf_bridgeName b) ih
  | dia b Φ ih => exact .dia (E.bridgeOf_bridgeName b) ih

/-- The round trip closes in the other direction too: elaborating the erasure
of a formula returns that formula. -/
theorem elabForm_unelab (E : Naming D) {κ : D.frame.K} (Φ : Form D.frame κ) :
    elabForm E κ (unelab E Φ) = .ok Φ :=
  elabForm_complete E (elaborates_reflects E Φ)

/-! ### Posing a query in a named context

The top-level authoring form. Resolution of the context name is the one step
`elabForm` does not do, because `elabForm` is indexed by an already-resolved
context. -/

/-- Elaborate a whole posed query: resolve its context name, then type its
formula. The dependent pair is unavoidable and honest — which context the query
lives in is *determined by the surface*, not chosen by the caller. -/
def elabPosed (E : Naming D) (p : Posed) :
    Except FormError ((κ : D.frame.K) × Form D.frame κ) :=
  match E.ctxOf p.context with
  | none => .error (.unknownContext p.context)
  | some κ =>
    match elabForm E κ p.form with
    | .error e => .error e
    | .ok Φ => .ok ⟨κ, Φ⟩

/-- A posed query in a declared context elaborates exactly when its formula
does. -/
theorem elabPosed_ok_iff (E : Naming D) (p : Posed) (κ : D.frame.K)
    (hκ : E.ctxOf p.context = some κ) (Φ : Form D.frame κ) :
    elabPosed E p = .ok ⟨κ, Φ⟩ ↔ elabForm E κ p.form = .ok Φ := by
  constructor
  · intro h
    unfold elabPosed at h
    simp only [hκ] at h
    cases hf : elabForm E κ p.form with
    | error e => simp only [hf] at h; exact absurd h (by simp)
    | ok Φ' =>
      simp only [hf, Except.ok.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h
      exact congrArg Except.ok h
  · intro h
    unfold elabPosed
    simp only [hκ, h]

end Elaborate

end Lara.PW.Surface
