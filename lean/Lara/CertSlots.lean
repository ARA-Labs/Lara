/-
Named certificate premise slots (`lara-syntax@0.6`) — the Lean mirror of
the payload-rewrite math in the presentation-layer lowering pass
(`Lara.Elaborate.CertSlots.lowerCertPayload`, `src/Lara/Elaborate/CertSlots.hs`).

An `ord@1` or `ra@1` certificate may cite a premise by its source name —
`(prem e4)` instead of `(prem 0)` — and the elaborator rewrites exactly the
schema-declared reference positions to the byte-identical numeric payload the
backend already decodes. This module carries the mathematics of that rewrite
over an abstract source-identifier classifier
`startsSourceIdentifier : String → Bool` and resolver
`ρ : String → Option Nat`:

  * `lowerPayload startsSourceIdentifier ρ bname bver p` matches the unique
    declared `SlotSchema` on (backend name, version, head keyword, arity) and
    rewrites each declared reference position holding a symbolic `(prem s)` via
    `ρ`; canonical numeric references, non-`(prem …)` nodes at reference
    positions, and non-reference positions (e.g. `ra@1`'s witness fraction)
    pass through untouched. A schema-less backend's payload passes through
    byte-identical; a schema'd backend's payload that fails its schema match
    while containing a symbolic `(prem s)` anywhere is refused (the D6
    dead-wire rule: a symbolic name is never valid wire).
  * `none` uniformly models every failure KIND — never success-vs-failure.
    The explicit classifier is the Haskell presentation lexer's
    Unicode-aware first-character predicate. Lean's `Char.isAlpha` is
    ASCII-only, so attempting to reimplement that predicate here would silently
    narrow the source language. Parameterizing it keeps the rewrite theorem
    exact for the real lexical boundary, including non-ASCII identifiers and
    non-numeric invalid starts. Name resolution, classifier implementation, and
    the Haskell error taxonomy remain validated-not-verified elaborator logic
    (`test/CertSlotsSpec.hs`).

The two theorems are the mechanization targets: `lower_id_of_no_symbolic`
(the pass is byte-identical on payloads satisfying `NoSymbolicRef` — no
symbolic reference at a matched schema's reference positions, and none
anywhere under a failed match of a schema'd backend) and
`lower_eq_numeric_subst` (a successful lowering is exactly the declarative
positional substitution `SymNumericSubst`, stated independently of the pass's
control flow).

Spelling discipline: the `prem` keyword is taken from `Lara.Cell.Tag`, the
`ordcmp`/`radrop`/`frac` keywords from `Lara.Ord.Tag`/`Lara.RA.Tag`, and the
`app`/`hyp` keywords in the conformance vectors from `Lara.ND.Tag` — no wire
keyword is respelled here.
-/

import Lara.Ord
import Lara.RA

namespace Lara.CertSlots

open Lara.Support (SExpr)
open Lara.Cell (parseCanonNat)

/-! ### Slot-reference nodes -/

/-- The wire spelling of a slot-reference node `(prem s)` over a raw atom.
The keyword comes from `Lara.Cell.Tag` — the one home of the `prem`
spelling. -/
def premNode (s : String) : SExpr :=
  .list [.atom Lara.Cell.Tag.prem.toString, .atom s]

/-- The canonical numeric slot reference `(prem N)` a symbolic reference
lowers to (the Haskell `SAtom (show slot)`). -/
def premSlot (n : Nat) : SExpr := premNode (Nat.repr n)

/-- The symbolic name of a slot-reference node: `(prem s)` with `s` not a
canonical natural.  Canonical numeric references and every other node carry
no symbolic name (the Haskell `symbolicRefName`). -/
def symbolicRefName : SExpr → Option String
  | .list [.atom k, .atom s] =>
      match Lara.Cell.Tag.parse k with
      | some .prem =>
          match parseCanonNat s with
          | some _ => none
          | none => some s
      | _ => none
  | _ => none

/-- Whether a symbolic slot atom is unable to begin a source identifier.
The classifier is explicit because Haskell's `Data.Char.isAlpha` is
Unicode-aware while Lean's `Char.isAlpha` is ASCII-only. The Haskell
instantiation uses the presentation lexer's exact predicate; the finite
conformance classifier below pins every executable vector. -/
def numeralTypo (startsSourceIdentifier : String → Bool) (s : String) : Bool :=
  !startsSourceIdentifier s

mutual
  /-- Whether a symbolic `(prem s)` occurs anywhere in a payload: a generic
  sub-tree scan with no backend grammar knowledge, used only to enforce the
  dead-wire rule on schema-mismatched payloads (the Haskell
  `firstSymbolicRef`, with the offending name dropped — the Lean mirror
  models every failure uniformly as `none`). -/
  def hasSymbolicRef : SExpr → Bool
    | .atom _ => false
    | .list es => (symbolicRefName (.list es)).isSome || hasSymbolicRefList es

  def hasSymbolicRefList : List SExpr → Bool
    | [] => false
    | e :: es => hasSymbolicRef e || hasSymbolicRefList es
end

/-! ### The declared schemas -/

/-- A backend's declared flat premise-reference schema (the Haskell
`Lara.Strict.Cell.SlotSchema`): registered identity, payload head keyword,
arity, and the 0-based argument positions that are premise references. -/
structure SlotSchema where
  backendName : String
  backendVersion : Nat
  head : String
  arity : Nat
  refSlots : List Nat
deriving DecidableEq, Repr

/- Backend identity spellings.  The pass matches schemas on the backend's
registered name and version; the exact `ord@1` / `ra@1` identities are
already mechanized as `Lara.Driver.ordBackendId` / `raBackendId` (and the
`Lara.Examples` twins), but both of those modules sit downstream of this one
(the executable shim and the fixtures), so — like them — this module keeps
its own definition site for the names it presents. -/

/-- `ord@1`'s declared schema: `(ordcmp (prem N) (prem M))` — arity 2, both
positions premise references (the Haskell `Lara.Strict.Ord.slotSchema`). -/
def ordSlotSchema : SlotSchema :=
  { backendName := "ord"
  , backendVersion := 1
  , head := Lara.Ord.Tag.ordcmp.toString
  , arity := 2
  , refSlots := [0, 1] }

/-- `ra@1`'s declared schema: `(radrop (prem N) (prem M) (frac P Q))` — arity
3, the first two positions premise references, the witness fraction not a
reference position (the Haskell `Lara.Strict.RA.slotSchema`). -/
def raSlotSchema : SlotSchema :=
  { backendName := "ra"
  , backendVersion := 1
  , head := Lara.RA.Tag.radrop.toString
  , arity := 3
  , refSlots := [0, 1] }

/-- Every declared flat premise-reference schema — the closed table the pass
consults.  A backend@version absent here has no schema, and its payloads
pass through byte-identical. -/
def slotSchemas : List SlotSchema := [ordSlotSchema, raSlotSchema]

-- Table coherence (the Haskell `prop_schemaKeysDistinct` twin): `matchSchema`
-- requires a UNIQUE (backend, head, arity) match, so a duplicate key would
-- silently degrade to no-match instead of surfacing the table bug.
#guard
  ((slotSchemas.map fun s =>
      (s.backendName, s.backendVersion, s.head, s.arity)).eraseDups.length
    == slotSchemas.length)

/-- The schemas declared for a backend name at a version. -/
def schemasFor (bname : String) (bver : Nat) : List SlotSchema :=
  slotSchemas.filter fun s => s.backendName == bname && s.backendVersion == bver

/-- Whether a backend@version declares any schema at all.  Schema'd backends
get the dead-wire rule; schema-less ones always pass through. -/
def backendHasSchema (bname : String) (bver : Nat) : Bool :=
  !(schemasFor bname bver).isEmpty

/-- The unique schema matching the backend@version, head keyword, and arity,
with the payload split into head and arguments.  Anything less specific —
wrong head, wrong arity, not a list — is no match. -/
def matchSchema (bname : String) (bver : Nat) :
    SExpr → Option (SlotSchema × String × List SExpr)
  | .list (.atom h :: args) =>
      match (schemasFor bname bver).filter
          (fun s => s.head == h && s.arity == args.length) with
      | [schema] => some (schema, h, args)
      | _ => none
  | _ => none

/-! ### The lowering pass -/

/-- Lower one argument position. Only a symbolic `(prem s)` at a declared
reference position is touched: an `s` that the supplied source-identifier
classifier refuses fails before the resolver (the Haskell
`SlotNonCanonicalNumeral` route); every accepted spelling reaches `ρ`, with
`ρ s = none` as failure. Everything else passes through, the backend's to
accept or reject. -/
def lowerAt (startsSourceIdentifier : String → Bool)
    (ρ : String → Option Nat) (schema : SlotSchema) (i : Nat)
    (e : SExpr) : Option SExpr :=
  if i ∈ schema.refSlots then
    match symbolicRefName e with
    | some s =>
        if numeralTypo startsSourceIdentifier s then none
        else
          match ρ s with
          | some n => some (premSlot n)
          | none => none
    | none => some e
  else some e

/-- Lower an argument vector position-wise, the head sitting at argument
index `k` (the Haskell `zipWithM (lowerAt schema resolve) [0 ..]`, entered at
`k = 0`). -/
def lowerArgs (startsSourceIdentifier : String → Bool)
    (ρ : String → Option Nat) (schema : SlotSchema) :
    Nat → List SExpr → Option (List SExpr)
  | _, [] => some []
  | i, e :: es => do
      let e' ← lowerAt startsSourceIdentifier ρ schema i e
      let es' ← lowerArgs startsSourceIdentifier ρ schema (i + 1) es
      pure (e' :: es')

/-- Lower one certificate payload (the Haskell `lowerCertPayload` over an
abstract source-identifier classifier and resolver): on a schema match,
rewrite the declared reference positions; on no match, pass through
byte-identical — unless the backend is schema'd and a symbolic `(prem s)`
occurs anywhere, which is the D6 dead-wire refusal. -/
def lowerPayload (startsSourceIdentifier : String → Bool)
    (ρ : String → Option Nat) (bname : String) (bver : Nat)
    (p : SExpr) : Option SExpr :=
  match matchSchema bname bver p with
  | some (schema, h, args) =>
      (lowerArgs startsSourceIdentifier ρ schema 0 args).map
        fun args' => .list (.atom h :: args')
  | none =>
      if backendHasSchema bname bver && hasSymbolicRef p then none
      else some p

/-! ### The identity theorem -/

/-- No symbolic reference in the pass's scope, stated declaratively over the
payload: at a schema match, no declared reference position holds a symbolic
`(prem s)`; at a failed match of a schema'd backend (the dead-wire arm), no
symbolic `(prem s)` occurs anywhere. -/
def NoSymbolicRef (bname : String) (bver : Nat) (p : SExpr) : Prop :=
  (∀ schema hd args, matchSchema bname bver p = some (schema, hd, args) →
    ∀ i, i ∈ schema.refSlots → ∀ e, args[i]? = some e →
      symbolicRefName e = none) ∧
  (matchSchema bname bver p = none → backendHasSchema bname bver = true →
    hasSymbolicRef p = false)

/-- A schema match pins the payload's shape: the payload is exactly the
matched head over the matched argument vector. -/
theorem matchSchema_shape {bname : String} {bver : Nat} {p : SExpr}
    {schema : SlotSchema} {hd : String} {args : List SExpr} :
    matchSchema bname bver p = some (schema, hd, args) →
    p = .list (.atom hd :: args) := by
  unfold matchSchema
  split
  · split
    · intro h; cases h; rfl
    · intro h; cases h
  · intro h; cases h

/-- The position-wise engine lemma, generalized over the starting index `k`:
if a candidate output vector agrees position-by-position with what the
per-position contract demands, `lowerArgs` produces exactly it. Both
headline theorems instantiate this at `k = 0`. -/
theorem lowerArgs_pointwise (startsSourceIdentifier : String → Bool)
    (ρ : String → Option Nat) (schema : SlotSchema) (args : List SExpr) :
    ∀ (k : Nat) (args' : List SExpr),
      args'.length = args.length →
      (∀ i e e', args[i]? = some e → args'[i]? = some e' →
        (k + i ∉ schema.refSlots → e' = e) ∧
        (k + i ∈ schema.refSlots → symbolicRefName e = none → e' = e) ∧
        (k + i ∈ schema.refSlots → ∀ s, symbolicRefName e = some s →
          numeralTypo startsSourceIdentifier s = false ∧
            ∃ n, ρ s = some n ∧ e' = premSlot n)) →
      lowerArgs startsSourceIdentifier ρ schema k args = some args' := by
  induction args with
  | nil =>
      intro k args' hlen _
      cases args' with
      | nil => rfl
      | cons a as => simp at hlen
  | cons e es ih =>
      intro k args' hlen hpt
      cases args' with
      | nil => simp at hlen
      | cons e' es' =>
          have h0 := hpt 0 e e' (by simp) (by simp)
          simp only [Nat.add_zero] at h0
          have hAt : lowerAt startsSourceIdentifier ρ schema k e = some e' := by
            unfold lowerAt
            by_cases href : k ∈ schema.refSlots
            · rw [if_pos href]
              cases hsym : symbolicRefName e with
              | none => simp [h0.2.1 href hsym]
              | some s =>
                  obtain ⟨htypo, n, hn, he'⟩ := h0.2.2 href s hsym
                  simp [htypo, hn, he']
            · rw [if_neg href, h0.1 href]
          have hrec : lowerArgs startsSourceIdentifier ρ schema (k + 1) es = some es' := by
            refine ih (k + 1) es' (by simpa using hlen) ?_
            intro i a a' h1 h2
            have hstep := hpt (i + 1) a a' (by simpa using h1) (by simpa using h2)
            have hk : k + (i + 1) = k + 1 + i := by omega
            rw [hk] at hstep
            exact hstep
          simp [lowerArgs, hAt, hrec]

/-- **Identity.**  On a payload with no symbolic reference in scope the pass
is byte-identical, whatever the resolver: already-numeric payloads,
non-`(prem …)` nodes at reference positions, schema-less backends, and
symbolic-free schema mismatches all come back unchanged. -/
theorem lower_id_of_no_symbolic (startsSourceIdentifier : String → Bool)
    (ρ : String → Option Nat) (bname : String) (bver : Nat) (p : SExpr)
    (h : NoSymbolicRef bname bver p) :
    lowerPayload startsSourceIdentifier ρ bname bver p = some p := by
  obtain ⟨hmatched, hdead⟩ := h
  cases hm : matchSchema bname bver p with
  | none =>
      have hcond : (backendHasSchema bname bver && hasSymbolicRef p) = false := by
        cases hb : backendHasSchema bname bver with
        | false => simp
        | true => simp [hdead hm hb]
      simp [lowerPayload, hm, hcond]
  | some t =>
      obtain ⟨schema, hd, args⟩ := t
      have hargs : lowerArgs startsSourceIdentifier ρ schema 0 args = some args := by
        refine lowerArgs_pointwise startsSourceIdentifier ρ schema args 0 args rfl ?_
        intro i e e' h1 h2
        have hee : e' = e := by
          rw [h1] at h2
          exact (Option.some.inj h2).symm
        refine ⟨fun _ => hee, fun _ _ => hee, fun href s hs => ?_⟩
        rw [hmatched schema hd args hm i (by simpa using href) e h1] at hs
        cases hs
      have hshape := matchSchema_shape hm
      subst hshape
      simp [lowerPayload, hm, hargs]

/-! ### The substitution theorem -/

/-- The declarative positional description of a successful lowering — stated
independently of `lowerPayload`'s control flow (plan OV-4). For the schema
matched on (backend name, version, head, arity): `q` carries the same head
and argument count as `p`; every non-reference position is equal; every
declared reference position holding a symbolic `(prem s)` in `p` has an `s`
accepted by `startsSourceIdentifier` and holds the canonical `(prem N)` with
`ρ s = some N` in `q`; every other reference-position shape is equal. -/
def SymNumericSubst (startsSourceIdentifier : String → Bool)
    (ρ : String → Option Nat) (bname : String) (bver : Nat)
    (p q : SExpr) : Prop :=
  ∃ schema hd args args',
    matchSchema bname bver p = some (schema, hd, args) ∧
    q = .list (.atom hd :: args') ∧
    args'.length = args.length ∧
    ∀ i e e', args[i]? = some e → args'[i]? = some e' →
      (i ∉ schema.refSlots → e' = e) ∧
      (i ∈ schema.refSlots → symbolicRefName e = none → e' = e) ∧
      (i ∈ schema.refSlots → ∀ s, symbolicRefName e = some s →
        numeralTypo startsSourceIdentifier s = false ∧
          ∃ n, ρ s = some n ∧ e' = premSlot n)

/-- **Substitution.**  A payload related to `q` by the declarative positional
substitution lowers to exactly `q`: the pass computes `SymNumericSubst` and
nothing else. -/
theorem lower_eq_numeric_subst (startsSourceIdentifier : String → Bool)
    (ρ : String → Option Nat) (bname : String) (bver : Nat) (p q : SExpr)
    (h : SymNumericSubst startsSourceIdentifier ρ bname bver p q) :
    lowerPayload startsSourceIdentifier ρ bname bver p = some q := by
  obtain ⟨schema, hd, args, args', hm, hq, hlen, hpt⟩ := h
  have hargs : lowerArgs startsSourceIdentifier ρ schema 0 args = some args' := by
    refine lowerArgs_pointwise startsSourceIdentifier ρ schema args 0 args' hlen ?_
    intro i e e' h1 h2
    simpa using hpt i e e' h1 h2
  subst hq
  simp [lowerPayload, hm, hargs]

/-! ### Conformance vectors (Haskell ↔ Lean drift guard, plan Task 5 Step 2b)

Each `#guard` below has a named QuickCheck twin in `test/CertSlotsSpec.hs`
asserting the same expectation of `lowerCertPayload`. The Haskell side
additionally pins WHICH `SlotRefError` each failing vector reports, which the
Lean mirror collapses to `none`. The vector tags (V1–V11) are cross-referenced
in the Haskell test file. -/

/-- Finite model of Haskell's Unicode-aware source-identifier start predicate
for the executable vectors. It deliberately accepts the legal non-ASCII `é1`
and rejects both numeric and non-numeric invalid starts. -/
private def testStartsSourceIdentifier : String → Bool
  | "e1" => true
  | "e2" => true
  | "nope" => true
  | "é1" => true
  | _ => false

/-- The fixed vector resolver: `e1 ↦ 0`, `e2 ↦ 1`, everything else fails
(the Haskell fixture `res`, with every `Left` collapsed to `none`). -/
private def testResolver : String → Option Nat
  | "e1" => some 0
  | "e2" => some 1
  | _ => none


/-- `nd@1`'s registered name, used only by the pass-through vectors: it
declares no schema here by design — its recursive proof terms are
backend-owned (mechanized identity precedent: `Lara.Driver.ndBackendId`). -/
private def ndBackendName : String := "nd"

private def ordPayload (a b : SExpr) : SExpr := .list [.atom ordSlotSchema.head, a, b]

private def fracWitness : SExpr :=
  .list [.atom Lara.RA.Tag.frac.toString, .atom "119", .atom "500"]

private def raPayload (a b : SExpr) : SExpr :=
  .list [.atom raSlotSchema.head, a, b, fracWitness]

private def ndPayload : SExpr :=
  .list [.atom Lara.ND.Tag.app.toString,
    .list [.atom Lara.ND.Tag.hyp.toString, .atom "0"],
    .list [.atom Lara.ND.Tag.hyp.toString, .atom "1"]]

private def ordWrongArityNumeric : SExpr := .list [.atom ordSlotSchema.head, premSlot 0]

private def ordWrongAritySymbolic : SExpr :=
  .list [.atom ordSlotSchema.head, premNode "e1"]

-- V1 symbolic ord (Haskell `prop_lowersSymbolicOrdRefs`).
#guard lowerPayload testStartsSourceIdentifier testResolver ordSlotSchema.backendName
    ordSlotSchema.backendVersion (ordPayload (premNode "e1") (premNode "e2"))
  = some (ordPayload (premSlot 0) (premSlot 1))

-- V2 mixed symbolic/numeric (Haskell `prop_acceptsMixedPositions`).
#guard lowerPayload testStartsSourceIdentifier testResolver ordSlotSchema.backendName
    ordSlotSchema.backendVersion (ordPayload (premNode "e1") (premSlot 1))
  = some (ordPayload (premSlot 0) (premSlot 1))

-- V3 ra with frac witness (Haskell `prop_lowersRaRefsAroundWitness`).
#guard lowerPayload testStartsSourceIdentifier testResolver raSlotSchema.backendName
    raSlotSchema.backendVersion (raPayload (premNode "e1") (premNode "e2"))
  = some (raPayload (premSlot 0) (premSlot 1))

-- V4 nd@1 pass-through (Haskell `prop_passesMismatchesWithoutSymbolsThrough`).
#guard lowerPayload testStartsSourceIdentifier testResolver ndBackendName 1 ndPayload = some ndPayload

-- V5 wrong-arity pass-through, numeric slots only
-- (Haskell `prop_passesMismatchesWithoutSymbolsThrough`).
#guard lowerPayload testStartsSourceIdentifier testResolver ordSlotSchema.backendName
    ordSlotSchema.backendVersion ordWrongArityNumeric
  = some ordWrongArityNumeric

-- V6 numeric identity (Haskell `prop_leavesNumericPayloadsUntouched`).
#guard lowerPayload testStartsSourceIdentifier testResolver ordSlotSchema.backendName
    ordSlotSchema.backendVersion (ordPayload (premSlot 0) (premSlot 1))
  = some (ordPayload (premSlot 0) (premSlot 1))

-- V7 dead-wire: schema'd backend, wrong arity, symbolic reference present
-- (Haskell `prop_rejectsSymbolsInMismatchedPayloads`: Left SlotSchemaMismatch).
#guard lowerPayload testStartsSourceIdentifier testResolver ordSlotSchema.backendName
    ordSlotSchema.backendVersion ordWrongAritySymbolic
  = none

-- V8 resolver failure (Haskell `prop_reportsResolverFailures`:
-- Left SlotNameUnresolved on "nope").
#guard lowerPayload testStartsSourceIdentifier testResolver ordSlotSchema.backendName
    ordSlotSchema.backendVersion (ordPayload (premNode "nope") (premNode "e2"))
  = none

-- V9 non-canonical numeral: the `numeralTypo` early-out fires before the
-- resolver on both sides, whatever the resolver says (Haskell
-- `prop_rejectsNonCanonicalNumerals`: the dedicated SlotNonCanonicalNumeral).
#guard lowerPayload testStartsSourceIdentifier testResolver ordSlotSchema.backendName
    ordSlotSchema.backendVersion (ordPayload (premNode "007") (premNode "e2"))
  = none

-- V9b the early-out is resolver-independent: even a resolver that maps every
-- name to a slot cannot lower a malformed numeral — failure never flips to
-- success under any ρ. The Haskell twin pins the same fact through the error
-- identity: `prop_rejectsNonCanonicalNumerals` reports
-- SlotNonCanonicalNumeral, not the fixture resolver's SlotNameUnresolved, so
-- the resolver was provably never consulted.
#guard lowerPayload testStartsSourceIdentifier (fun _ => some 5) ordSlotSchema.backendName
    ordSlotSchema.backendVersion (ordPayload (premNode "007") (premSlot 1))
  = none

-- V9c signed and otherwise numeral-shaped atoms cannot be source names, so
-- they fail before even an all-resolving ρ is consulted (Haskell
-- `prop_rejectsNonCanonicalNumerals`).
#guard lowerPayload testStartsSourceIdentifier (fun _ => some 5) ordSlotSchema.backendName
    ordSlotSchema.backendVersion (ordPayload (premNode "-1") (premSlot 1))
  = none

-- V10 a non-ASCII source identifier must reach the resolver. Haskell's
-- Unicode-aware `Data.Char.isAlpha` accepts `é`, so the Lean model must not
-- mistake this legal name for a malformed numeral.
#guard lowerPayload testStartsSourceIdentifier
    (fun s => if s == "é1" then some 0 else none)
    ordSlotSchema.backendName ordSlotSchema.backendVersion
    (ordPayload (premNode "é1") (premSlot 1))
  = some (ordPayload (premSlot 0) (premSlot 1))

-- V11 non-numeric atoms that cannot begin source identifiers are also refused
-- before an all-resolving resolver. The classifier boundary is lexical, not
-- merely a malformed-number heuristic.
#guard lowerPayload testStartsSourceIdentifier (fun _ => some 5) ordSlotSchema.backendName
    ordSlotSchema.backendVersion (ordPayload (premNode "#x") (premSlot 1))
  = none
#guard lowerPayload testStartsSourceIdentifier (fun _ => some 5) ordSlotSchema.backendName
    ordSlotSchema.backendVersion (ordPayload (premNode ".x") (premSlot 1))
  = none

end Lara.CertSlots
