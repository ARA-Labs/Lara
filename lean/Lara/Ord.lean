/-
The ordered-comparison domain-checker backend `ord@1`
(`plans/2026-08-06-ord1-comparison-backend.md`).

The adapter certifies a closed two-predicate family — `num_lt(A, B)` and
`num_le(A, B)` over two numeric literals — by exact rational arithmetic.  The
shared cell machinery (exact decimals, the canonical numeral parsers, the
consulted-cell convention, the `(prem N)` slot sub-grammar, and the
cross-multiplied comparisons) lives in `Lara.Cell`; this module adds only the
`ord@1` goal family, its certificate tag, and its metatheory.  Like `Lara.RA`
the whole development stays in core Lean: no `Rat`, no Mathlib.

The `Backend` obligations are discharged the same way `Lara.RA` does it:

  * `enc` is `nf canon` itself — the identity encoding on normalized atoms —
    so `enc_iff` is exactly `equiv_iff_nf_eq`;
  * `replayFull` decodes the exact submitted certificate and runs the
    decidable arithmetic check (`checkB`); acceptance is the proposition-level
    mirror, and `replayFull_iff` is a case split;
  * `soundFull` extracts the mathematical consequence `ordModels`.  This is
    strictly simpler than the RA adapter: there is no witness value, so
    nothing has to be cancelled — `soundFull` just repackages the facts
    `checkB` pins down;
  * the certificate names its two consulted slots outright, so the
    obligation-4 laws (`uses_covers` / `uses_valid` / `uses_account`) follow
    from `checkB` touching the context only through those two lookups.

## Premise-only slots, and how they are modelled here

The Haskell adapter rejects any certificate slot `>= nPrem`, so a certificate
cannot cite a self-supplied theory entry as if it were measured evidence
(design §2.2).  The abstract `Backend` core, by contrast, is handed a single
context `Γ = Δ ++ T` and never learns `Δ.length`, so that guard is not
expressible at this layer.

It does not need to be.  `ord@1` is registered with a theory that is empty by
design: `Lara.Driver.buildRegistry` resolves any *known* `ord@1` digest to
`[]` (an unknown digest still fails to resolve, which is a rejection).  Hence
`Γ = Δ ++ [] = Δ`, and "slot names a premise" and "slot is in range of `Γ`"
coincide — the Lean model and the Haskell adapter accept exactly the same
certificates, including on units that declare a non-empty wire theory, since
the Haskell side rejects those slots outright.  The premise-only guard is
therefore an *acceptance-preserving* refinement on the Haskell side, and the
soundness statement below is about the premises it actually consulted.

## Intra-family consistency (design §3.2)

`num_lt` / `num_le` head no declared contrary pair, and that is a theorem
rather than a workaround: comparison goals are decidable against a shared
ground truth, so a sound backend can never accept two conflicting members of
the family over the same literals.  `ordModels_excl_of_lt` below is that
statement; the paper cites the lemma, not an observation.
-/

import Lara.Cell

namespace Lara.Ord

open Lara.Support (SExpr CertRef)
open Lara.Strict (selectSlots)

/- The cell machinery shared with `ra@1` lives in `Lara.Cell`.  `Lara.Cell.Tag`
is deliberately *not* opened: this module keeps its own closed tag table. -/
open Lara.Cell (Dec parseCanonNat parseDecimal premiseCell RatEq RatLt RatLe
  ratEqB ratLtB ratLeB ratEqB_iff ratLtB_iff ratLeB_iff decodeSlot
  lt_of_getElem?_eq_some)

/-! ### The closed goal family

Two predicates, and only two.  There is no `num_gt` / `num_ge` — "A > B" is
authored as `num_lt(B, A)` — and no `num_eq`, since canonical decimal form is
injective on representable rationals, so `num_eq(A, B)` could only ever hold
when `A` and `B` are the same numeral.  The concrete spellings live in exactly
one table (`Rel.pred`). -/

/-- The closed comparison family. -/
inductive Rel where
  | lt | le
deriving DecidableEq, Repr

/-- The goal predicate spelling of each family member. -/
def Rel.pred : Rel → String
  | .lt => "num_lt"
  | .le => "num_le"

def Rel.all : List Rel := [.lt, .le]

/-- Recognize a family predicate, inverse to `Rel.pred`. -/
def Rel.parse (s : String) : Option Rel := Rel.all.find? (fun r => r.pred = s)

/-- The relation each family member asserts of the two cells. -/
def RelHolds : Rel → Dec → Dec → Prop
  | .lt, a, b => RatLt a b
  | .le, a, b => RatLe a b

def relHoldsB : Rel → Dec → Dec → Bool
  | .lt, a, b => ratLtB a b
  | .le, a, b => ratLeB a b

theorem relHoldsB_iff (r : Rel) (a b : Dec) :
    relHoldsB r a b = true ↔ RelHolds r a b := by
  cases r
  · exact ratLtB_iff a b
  · exact ratLeB_iff a b

/-! ### The goal shape -/

/-- The parsed goal: a family member over two cells. -/
structure Goal where
  rel : Rel
  left : Dec
  right : Dec
deriving DecidableEq, Repr

def parseGoal : Lara.Atom → Option Goal
  | .atom p ts =>
      match Rel.parse p with
      | some r =>
          match Lara.Strict.sourceTermsToList ts with
          | [.num a, .num b] => do
              let A ← parseDecimal a
              let B ← parseDecimal b
              some ⟨r, A, B⟩
          | _ => none
      | none => none

/-! ### The certificate wire grammar (the closed decoder)

`cert := (ordcmp (prem N) (prem M))`

There is no witness value: a comparison over ground literals has nothing to
recompute, so the replay decides it directly.  The relation is read off the
goal predicate, not the certificate. -/

/-- The closed set of `ord@1`-specific wire keywords (`Lara.ND.Tag`
discipline).  The shared slot keyword `prem` lives in `Lara.Cell.Tag`. -/
inductive Tag where
  | ordcmp
deriving DecidableEq, Repr

def Tag.toString : Tag → String
  | .ordcmp => "ordcmp"

def Tag.all : List Tag := [.ordcmp]

def Tag.parse (s : String) : Option Tag :=
  Tag.all.find? (fun t => t.toString = s)

/-- A decoded certificate: the two consulted slots. -/
structure Cert where
  leftSlot : Nat
  rightSlot : Nat
deriving DecidableEq, Repr

def decodeCert : SExpr → Option Cert
  | .list [.atom k, sL, sR] =>
      match Tag.parse k with
      | some .ordcmp => do
          let nL ← decodeSlot sL
          let nR ← decodeSlot sR
          some ⟨nL, nR⟩
      | _ => none
  | _ => none

/-! ### The executable check -/

/-- The decidable comparison check, mirroring the Haskell adapter's `run`:
the goal parses, the two named slots resolve and carry cells matching the
goal's two numerals, and the goal's relation holds of them.  The context is
consulted **only** through the two named slots — the coverage law reads this
off the definition. -/
def checkB (c : Cert) (Γ : List Lara.Atom) (φ : Lara.Atom) : Bool :=
  match parseGoal φ, Γ[c.leftSlot]?, Γ[c.rightSlot]? with
  | some g, some pL, some pR =>
      match premiseCell pL, premiseCell pR with
      | some l, some r =>
          ratEqB l g.left && ratEqB r g.right &&
          relHoldsB g.rel g.left g.right
      | _, _ => false
  | _, _, _ => false

/-! ### The proposition layer -/

/-- Mathematical consequence for the `ord@1` backend: the goal parses as a
family member, some context entries carry the two cells, and the comparison
holds in exact rational arithmetic (cross-multiplied form).

Note what this does *and does not* say (the factivity firewall, design §3.1).
Since both numerals appear in the goal, the relation itself is decidable from
the goal alone; what the context adds is **provenance anchoring** — each cited
entry's unique numeric literal equals the corresponding goal numeral.  Nothing
here asserts that any cell is *true*; the measurement leaves stay defeasible. -/
def ordModels (Γ : List Lara.Atom) (φ : Lara.Atom) : Prop :=
  ∃ (g : Goal) (i j : Nat) (pL pR : Lara.Atom) (l r : Dec),
    parseGoal φ = some g ∧
    Γ[i]? = some pL ∧ Γ[j]? = some pR ∧
    premiseCell pL = some l ∧ premiseCell pR = some r ∧
    RatEq l g.left ∧ RatEq r g.right ∧
    RelHolds g.rel g.left g.right

/-- Acceptance of the exact submitted certificate. -/
def ordAccepts (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom) : Prop :=
  ∃ c, decodeCert κ.payload = some c ∧ checkB c Γ φ = true

/-- Decode and check the exact submitted certificate; no search occurs. -/
def ordReplay (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom) : Bool :=
  match decodeCert κ.payload with
  | none => false
  | some c => checkB c Γ φ

theorem ordReplay_iff (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom) :
    ordReplay κ Γ φ = true ↔ ordAccepts κ Γ φ := by
  cases hdec : decodeCert κ.payload with
  | none => simp [ordReplay, ordAccepts, hdec]
  | some c => simp [ordReplay, ordAccepts, hdec]

/-- Reported dependency slots: the two slots the certificate names.  A
function of the certificate alone; an undecodable certificate reports nothing
(it is never accepted).  A same-slot certificate reports that slot twice here;
`selectSlots` and the Haskell `Set` both collapse it to one dependency. -/
def ordUses (κ : CertRef) : List Nat :=
  match decodeCert κ.payload with
  | none => []
  | some c => [c.leftSlot, c.rightSlot]

/-- Everything a passing `checkB` pins down, in proposition form.  No witness
means no cancellation step: this is a direct repackaging. -/
theorem checkB_extract {c : Cert} {Γ : List Lara.Atom} {φ : Lara.Atom}
    (h : checkB c Γ φ = true) :
    ∃ (g : Goal) (pL pR : Lara.Atom) (l r : Dec),
      parseGoal φ = some g ∧
      Γ[c.leftSlot]? = some pL ∧ Γ[c.rightSlot]? = some pR ∧
      premiseCell pL = some l ∧ premiseCell pR = some r ∧
      RatEq l g.left ∧ RatEq r g.right ∧
      RelHolds g.rel g.left g.right := by
  unfold checkB at h
  split at h
  case _ g pL pR hgoal hL hR =>
    split at h
    case _ l r hl hr =>
      simp only [Bool.and_eq_true, ratEqB_iff, relHoldsB_iff] at h
      obtain ⟨⟨hlg, hrg⟩, hrel⟩ := h
      exact ⟨g, pL, pR, l, r, hgoal, hL, hR, hl, hr, hlg, hrg, hrel⟩
    case _ => exact absurd h (by simp)
  case _ => exact absurd h (by simp)

/-- Certificate soundness: an accepted certificate's conclusion is a
mathematical consequence of the consulted context. -/
theorem ordSound (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom)
    (hacc : ordAccepts κ Γ φ) : ordModels Γ φ := by
  obtain ⟨c, _, hchk⟩ := hacc
  obtain ⟨g, pL, pR, l, r, hgoal, hL, hR, hl, hr, hlg, hrg, hrel⟩ :=
    checkB_extract hchk
  exact ⟨g, c.leftSlot, c.rightSlot, pL, pR, l, r, hgoal, hL, hR, hl, hr,
    hlg, hrg, hrel⟩

/-- Obligation 4, coverage: replay consults the context only at the reported
slots — contexts agreeing there replay identically. -/
theorem ordUses_covers (κ : CertRef) (Γ Γ' : List Lara.Atom) (φ : Lara.Atom)
    (hag : ∀ i, i ∈ ordUses κ → Γ[i]? = Γ'[i]?) :
    ordReplay κ Γ φ = ordReplay κ Γ' φ := by
  cases hdec : decodeCert κ.payload with
  | none => simp [ordReplay, hdec]
  | some c =>
    have hL : Γ[c.leftSlot]? = Γ'[c.leftSlot]? :=
      hag c.leftSlot (by simp [ordUses, hdec])
    have hR : Γ[c.rightSlot]? = Γ'[c.rightSlot]? :=
      hag c.rightSlot (by simp [ordUses, hdec])
    simp only [ordReplay, hdec, checkB, hL, hR]

/-- Obligation 4, validity: on acceptance every reported slot names an entry
of the consulted context. -/
theorem ordUses_valid (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom)
    (hacc : ordAccepts κ Γ φ) : ∀ i, i ∈ ordUses κ → i < Γ.length := by
  obtain ⟨c, hdec, hchk⟩ := hacc
  obtain ⟨g, pL, pR, l, r, _, hL, hR, _⟩ := checkB_extract hchk
  intro i hi
  simp only [ordUses, hdec, List.mem_cons] at hi
  rcases hi with rfl | hi
  · exact lt_of_getElem?_eq_some hL
  · rcases hi with rfl | hfalse
    · exact lt_of_getElem?_eq_some hR
    · exact absurd hfalse (List.not_mem_nil)

/-- Obligation 4, semantic accounting: an accepted certificate's conclusion
follows from just the reported entries. -/
theorem ordUses_account (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom)
    (hacc : ordAccepts κ Γ φ) : ordModels (selectSlots Γ (ordUses κ)) φ := by
  obtain ⟨c, hdec, hchk⟩ := hacc
  obtain ⟨g, pL, pR, l, r, hgoal, hL, hR, hl, hr, hlg, hrg, hrel⟩ :=
    checkB_extract hchk
  have hsel : selectSlots Γ (ordUses κ) = [pL, pR] := by
    simp [selectSlots, ordUses, hdec, hL, hR]
  refine ⟨g, 0, 1, pL, pR, l, r, hgoal, ?_, ?_, hl, hr, hlg, hrg, hrel⟩
  · rw [hsel]; rfl
  · rw [hsel]; rfl

/-! ### Intra-family exclusivity (design §3.2)

Why `num_lt` / `num_le` head no declared contrary pair: over the *same* two
cells, a strict comparison in one direction rules out either comparison in the
other direction.  Each cross-multiplied relation is a statement about the same
two integer expressions, so these fall to `omega` with no positivity side
condition. -/

/-- `lt(A,B)` and `lt(B,A)` are jointly unsatisfiable. -/
theorem lt_excl_lt {a b : Dec} (h1 : RatLt a b) (h2 : RatLt b a) : False := by
  unfold RatLt at h1 h2; omega

/-- `lt(A,B)` and `le(B,A)` are jointly unsatisfiable. -/
theorem lt_excl_le {a b : Dec} (h1 : RatLt a b) (h2 : RatLe b a) : False := by
  unfold RatLt at h1; unfold RatLe at h2; omega

/-- `le(A,B)` and `le(B,A)` are jointly satisfiable — and exactly when the two
cells are equal.  This is why the family declares *no* contrary pair at all
rather than a partial one: the only reversed pair that can coexist pins down
equality, which is a consequence, not a conflict. -/
theorem le_le_iff_eq {a b : Dec} (h1 : RatLe a b) (h2 : RatLe b a) :
    RatEq a b := by
  unfold RatLe at h1 h2; unfold RatEq; omega

/-- The relation a `ordModels` witness asserts, extracted at a known goal. -/
theorem ordModels_relHolds {Γ : List Lara.Atom} {φ : Lara.Atom} {g : Goal}
    (hm : ordModels Γ φ) (hg : parseGoal φ = some g) :
    RelHolds g.rel g.left g.right := by
  obtain ⟨g', _, _, _, _, _, _, hgoal, _, _, _, _, _, _, hrel⟩ := hm
  have hgg : g' = g := Option.some.inj (hgoal.symm.trans hg)
  subst hgg
  exact hrel

/-- **Intra-family consistency.**  If the backend's consequence relation holds
for a *strict* goal over two numerals, it cannot also hold for either family
member over the same numerals reversed — whatever contexts the two are drawn
from.  So a sound backend never accepts two conflicting members of the family,
and declaring a contrary pair for `num_lt` / `num_le` would add nothing (and
would trip R12).  Intra-family consistency is enforced at acceptance time by
arithmetic, not by attack structure. -/
theorem ordModels_excl_of_lt {Γ Γ' : List Lara.Atom} {φ ψ : Lara.Atom}
    {g h : Goal}
    (hgm : ordModels Γ φ) (hhm : ordModels Γ' ψ)
    (hg : parseGoal φ = some g) (hh : parseGoal ψ = some h)
    (hL : h.left = g.right) (hR : h.right = g.left)
    (hstrict : g.rel = Rel.lt) : False := by
  have h1 := ordModels_relHolds hgm hg
  have h2 := ordModels_relHolds hhm hh
  rw [hstrict] at h1
  rw [hL, hR] at h2
  cases hrel : h.rel with
  | lt => rw [hrel] at h2; exact lt_excl_lt h1 h2
  | le => rw [hrel] at h2; exact lt_excl_le h1 h2

/-! ### The registered adapter -/

/-- The one fixed `ord@1` backend core.  `Form` is the normalized source atom
itself — the identity encoding — so `enc_iff` is `equiv_iff_nf_eq`.  A
registered digest resolves to the empty theory (design §2.2), so the consulted
context is exactly the submitted premises. -/
def ordBackend (canon : String → String) : Lara.Strict.Backend canon where
  Form := Lara.Atom
  enc := Lara.nf canon
  enc_iff := fun p q => (Lara.equiv_iff_nf_eq canon p q).symm
  modelsFull := ordModels
  acceptsFull := ordAccepts
  replayFull := ordReplay
  replayFull_iff := ordReplay_iff
  soundFull := ordSound
  uses := ordUses
  uses_covers := fun κ Γ Γ' φ hag => ordUses_covers κ Γ Γ' φ hag
  uses_valid := ordUses_valid
  uses_account := ordUses_account

end Lara.Ord
