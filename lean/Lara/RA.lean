/-
The rational-arithmetic domain-checker backend `ra@1`.

The adapter certifies one goal shape — the relative-drop inequality
`rel_drop_ge(F, A, C, T)` over numeric literals — by exact rational
arithmetic.  Rationals are represented as integer numerators over positive
denominators (parsed decimals carry a power-of-ten denominator), and every
comparison is a cross-multiplied integer identity, so the whole development
stays in core Lean: no `Rat`, no Mathlib.

The `Backend` obligations are discharged the same way the ND adapter does it:

  * `enc` is `nf canon` itself — the identity encoding on normalized atoms —
    so `enc_iff` is exactly `equiv_iff_nf_eq`;
  * `replayFull` decodes the exact submitted certificate and runs the
    decidable arithmetic check (`checkB`); acceptance is the proposition-level
    mirror, and `replayFull_iff` is a case split;
  * `soundFull` extracts the mathematical consequence `raModels`: the goal
    parses, the reported slots carry the two cells, and `(F − A)/F = C ≥ T`
    holds — the witness fraction is eliminated by integer cancellation;
  * the certificate names its two consulted slots outright, so the
    obligation-4 laws (`uses_covers` / `uses_valid` / `uses_account`) follow
    from `checkB` touching the context only through those two lookups.
-/

import Lara.Cell

namespace Lara.RA

open Lara.Support (SExpr CertRef)
open Lara.Strict (selectSlots)

/- The cell machinery shared with `ord@1` lives in `Lara.Cell` (exact
decimals, the canonical numeral parsers, the cross-multiplied comparisons, the
consulted-cell convention, and the `(prem N)` slot sub-grammar).  `Lara.Cell.Tag`
is deliberately *not* opened: this module keeps its own closed tag table. -/
open Lara.Cell (Dec parseCanonNat parseCanonInt parseFracDigits parseUnsigned
  parseDecimal RatEq RatGe ratEqB ratGeB ratEqB_iff ratGeB_iff premiseCell
  termNums termsNums decodeSlot lt_of_getElem?_eq_some)

/-! ### The goal shape -/

/-- The parsed goal `rel_drop_ge(F, A, C, T)`. -/
structure Goal where
  full : Dec
  ablated : Dec
  claimed : Dec
  threshold : Dec
deriving DecidableEq, Repr

/-- The single spelling of the goal predicate this backend recognizes. -/
def goalPred : String := "rel_drop_ge"

def parseGoal : Lara.Atom → Option Goal
  | .atom p ts =>
      if p = goalPred then
        match Lara.Strict.sourceTermsToList ts with
        | [.num f, .num a, .num c, .num t] => do
            let F ← parseDecimal f
            let A ← parseDecimal a
            let C ← parseDecimal c
            let T ← parseDecimal t
            some ⟨F, A, C, T⟩
        | _ => none
      else none

/-! ### The certificate wire grammar (the closed decoder)

`cert := (radrop (prem N) (prem M) (frac P Q))` -/

/-- The closed set of RA-specific wire keywords (`Lara.ND.Tag` discipline).
The shared slot keyword `prem` lives in `Lara.Cell.Tag`. -/
inductive Tag where
  | radrop | frac
deriving DecidableEq, Repr

def Tag.toString : Tag → String
  | .radrop => "radrop"
  | .frac => "frac"

def Tag.all : List Tag := [.radrop, .frac]

def Tag.parse (s : String) : Option Tag :=
  Tag.all.find? (fun t => t.toString = s)

/-- A decoded certificate: the two consulted premise slots and the claimed drop
as an exact fraction in lowest terms.  (Slots index the consulted context
`Γ = Δ ++ T`, but `Lara.Driver.buildRegistry` resolves a known `ra@1` digest to
the empty theory, so `Γ = Δ` and every in-range slot is a premise — the same
discipline `ord@1` uses; see `raBackend` below.) -/
structure Cert where
  fullSlot : Nat
  ablatedSlot : Nat
  witness : Dec
deriving DecidableEq, Repr

def decodeFrac : SExpr → Option Dec
  | .list [.atom k, .atom p, .atom q] =>
      match Tag.parse k with
      | some .frac =>
          match parseCanonInt p, parseCanonNat q with
          | some pn, some qn =>
              if qn = 0 then none
              else if Nat.gcd pn.natAbs qn = 1 then some ⟨pn, qn⟩ else none
          | _, _ => none
      | _ => none
  | _ => none

def decodeCert : SExpr → Option Cert
  | .list [.atom k, sF, sA, fr] =>
      match Tag.parse k with
      | some .radrop => do
          let nF ← decodeSlot sF
          let nA ← decodeSlot sA
          let w ← decodeFrac fr
          some ⟨nF, nA, w⟩
      | _ => none
  | _ => none

theorem decodeFrac_den_pos {e : SExpr} {d : Dec}
    (h : decodeFrac e = some d) : 0 < d.den := by
  unfold decodeFrac at h
  split at h
  · split at h
    · split at h
      · split at h
        · exact absurd h (by simp)
        · split at h
          · rename_i qn_ne _
            cases h
            exact Nat.pos_of_ne_zero qn_ne
          · exact absurd h (by simp)
      · exact absurd h (by simp)
    all_goals exact absurd h (by simp)
  · exact absurd h (by simp)

theorem decodeCert_witness_den_pos {e : SExpr} {c : Cert}
    (h : decodeCert e = some c) : 0 < c.witness.den := by
  unfold decodeCert at h
  split at h
  · split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨nF, _, nA, _, w, hw, hc⟩ := h
      cases hc
      exact decodeFrac_den_pos hw
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ### The arithmetic identities -/

/-- `(F − A) / F = w`, cross-multiplied: `(Fn·Ad − An·Fd)·Wd = Wn·(Ad·Fn)`.
Valid as the rational statement exactly when `Fn ≠ 0` and the denominators
are positive — both checked alongside. -/
def DropEqW (g : Goal) (w : Dec) : Prop :=
  (g.full.num * (g.ablated.den : Int) - g.ablated.num * (g.full.den : Int))
      * (w.den : Int)
    = w.num * ((g.ablated.den : Int) * g.full.num)

def dropEqWB (g : Goal) (w : Dec) : Bool :=
  (g.full.num * (g.ablated.den : Int) - g.ablated.num * (g.full.den : Int))
      * (w.den : Int)
    == w.num * ((g.ablated.den : Int) * g.full.num)

theorem dropEqWB_iff (g : Goal) (w : Dec) :
    dropEqWB g w = true ↔ DropEqW g w := by
  simp [dropEqWB, DropEqW]

/-- `(F − A) / F = C` directly against the goal's claimed drop. -/
def DropEq (g : Goal) : Prop := DropEqW g g.claimed

/-- Integer right-cancellation, proved in core. -/
theorem mul_right_cancel {a b c : Int} (hc : c ≠ 0) (h : a * c = b * c) :
    a = b := by
  have h2 : (a - b) * c = 0 := by rw [Int.sub_mul, h, Int.sub_self]
  rcases Int.mul_eq_zero.mp h2 with h3 | h3
  · omega
  · exact absurd h3 hc

/-- Eliminate the witness: if the recomputed drop equals the witness fraction
and the witness equals the claimed drop, the recomputed drop equals the
claimed drop.  Pure integer shuffling plus one cancellation of the witness
denominator. -/
theorem dropEq_of_witness {g : Goal} {w : Dec} (hden : 0 < w.den)
    (h1 : DropEqW g w) (h2 : RatEq w g.claimed) : DropEq g := by
  unfold DropEq
  unfold DropEqW at h1 ⊢
  unfold RatEq at h2
  have hWd : (w.den : Int) ≠ 0 := by
    simp only [ne_eq, Int.natCast_eq_zero]
    omega
  apply mul_right_cancel hWd
  calc (g.full.num * (g.ablated.den : Int) - g.ablated.num * (g.full.den : Int))
        * (g.claimed.den : Int) * (w.den : Int)
      = (g.full.num * (g.ablated.den : Int) - g.ablated.num * (g.full.den : Int))
          * (w.den : Int) * (g.claimed.den : Int) := by
        rw [Int.mul_assoc, Int.mul_comm (g.claimed.den : Int) (w.den : Int),
          ← Int.mul_assoc]
    _ = w.num * ((g.ablated.den : Int) * g.full.num) * (g.claimed.den : Int) := by
        rw [h1]
    _ = w.num * (g.claimed.den : Int) * ((g.ablated.den : Int) * g.full.num) := by
        rw [Int.mul_assoc, Int.mul_comm ((g.ablated.den : Int) * g.full.num)
          (g.claimed.den : Int), ← Int.mul_assoc]
    _ = g.claimed.num * (w.den : Int) * ((g.ablated.den : Int) * g.full.num) := by
        rw [h2]
    _ = g.claimed.num * ((g.ablated.den : Int) * g.full.num) * (w.den : Int) := by
        rw [Int.mul_assoc, Int.mul_comm (w.den : Int)
          ((g.ablated.den : Int) * g.full.num), ← Int.mul_assoc]

/-! ### The executable check -/

/-- The decidable arithmetic check, mirroring the Haskell adapter's `run`:
the goal parses, the two named slots resolve and carry cells matching the
goal's `F` and `A`, `F ≠ 0`, the witness equals the exact recomputation and
the claimed drop, and the claimed drop clears the threshold.  The context is
consulted **only** through the two named slots — the coverage law reads this
off the definition. -/
def checkB (c : Cert) (Γ : List Lara.Atom) (φ : Lara.Atom) : Bool :=
  match parseGoal φ, Γ[c.fullSlot]?, Γ[c.ablatedSlot]? with
  | some g, some pF, some pA =>
      match premiseCell pF, premiseCell pA with
      | some f, some a =>
          ratEqB f g.full && ratEqB a g.ablated &&
          (g.full.num != 0) &&
          dropEqWB g c.witness &&
          ratEqB c.witness g.claimed &&
          ratGeB g.claimed g.threshold
      | _, _ => false
  | _, _, _ => false

/-! ### The proposition layer -/

/-- Mathematical consequence for the RA backend: the goal parses as a
relative-drop inequality, some context entries carry the two cells, and the
arithmetic holds — `(F − A)/F = C` and `C ≥ T` in exact rational arithmetic
(cross-multiplied form). -/
def raModels (Γ : List Lara.Atom) (φ : Lara.Atom) : Prop :=
  ∃ (g : Goal) (i j : Nat) (pF pA : Lara.Atom) (f a : Dec),
    parseGoal φ = some g ∧
    Γ[i]? = some pF ∧ Γ[j]? = some pA ∧
    premiseCell pF = some f ∧ premiseCell pA = some a ∧
    RatEq f g.full ∧ RatEq a g.ablated ∧
    g.full.num ≠ 0 ∧
    DropEq g ∧
    RatGe g.claimed g.threshold

/-- Acceptance of the exact submitted certificate. -/
def raAccepts (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom) : Prop :=
  ∃ c, decodeCert κ.payload = some c ∧ checkB c Γ φ = true

/-- Decode and check the exact submitted certificate; no search occurs. -/
def raReplay (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom) : Bool :=
  match decodeCert κ.payload with
  | none => false
  | some c => checkB c Γ φ

theorem raReplay_iff (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom) :
    raReplay κ Γ φ = true ↔ raAccepts κ Γ φ := by
  cases hdec : decodeCert κ.payload with
  | none => simp [raReplay, raAccepts, hdec]
  | some c => simp [raReplay, raAccepts, hdec]

/-- Reported dependency slots: the two slots the certificate names.  A
function of the certificate alone; an undecodable certificate reports nothing
(it is never accepted). -/
def raUses (κ : CertRef) : List Nat :=
  match decodeCert κ.payload with
  | none => []
  | some c => [c.fullSlot, c.ablatedSlot]

/-- Everything a passing `checkB` pins down, in proposition form. -/
theorem checkB_extract {c : Cert} {Γ : List Lara.Atom} {φ : Lara.Atom}
    (hden : 0 < c.witness.den) (h : checkB c Γ φ = true) :
    ∃ (g : Goal) (pF pA : Lara.Atom) (f a : Dec),
      parseGoal φ = some g ∧
      Γ[c.fullSlot]? = some pF ∧ Γ[c.ablatedSlot]? = some pA ∧
      premiseCell pF = some f ∧ premiseCell pA = some a ∧
      RatEq f g.full ∧ RatEq a g.ablated ∧
      g.full.num ≠ 0 ∧
      DropEq g ∧
      RatGe g.claimed g.threshold := by
  unfold checkB at h
  split at h
  case _ g pF pA hgoal hF hA =>
    split at h
    case _ f a hf ha =>
      simp only [Bool.and_eq_true, ratEqB_iff, ratGeB_iff, dropEqWB_iff,
        bne_iff_ne, ne_eq] at h
      obtain ⟨⟨⟨⟨⟨hfg, hag⟩, hnz⟩, hdw⟩, hwc⟩, hge⟩ := h
      exact ⟨g, pF, pA, f, a, hgoal, hF, hA, hf, ha, hfg, hag, hnz,
        dropEq_of_witness hden hdw hwc, hge⟩
    case _ => exact absurd h (by simp)
  case _ => exact absurd h (by simp)

/-- Certificate soundness: an accepted certificate's conclusion is a
mathematical consequence of the consulted context. -/
theorem raSound (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom)
    (hacc : raAccepts κ Γ φ) : raModels Γ φ := by
  obtain ⟨c, hdec, hchk⟩ := hacc
  obtain ⟨g, pF, pA, f, a, hgoal, hF, hA, hf, ha, hfg, hag, hnz, hde, hge⟩ :=
    checkB_extract (decodeCert_witness_den_pos hdec) hchk
  exact ⟨g, c.fullSlot, c.ablatedSlot, pF, pA, f, a, hgoal, hF, hA, hf, ha,
    hfg, hag, hnz, hde, hge⟩

/-- Obligation 4, coverage: replay consults the context only at the reported
slots — contexts agreeing there replay identically. -/
theorem raUses_covers (κ : CertRef) (Γ Γ' : List Lara.Atom) (φ : Lara.Atom)
    (hag : ∀ i, i ∈ raUses κ → Γ[i]? = Γ'[i]?) :
    raReplay κ Γ φ = raReplay κ Γ' φ := by
  cases hdec : decodeCert κ.payload with
  | none => simp [raReplay, hdec]
  | some c =>
    have hF : Γ[c.fullSlot]? = Γ'[c.fullSlot]? :=
      hag c.fullSlot (by simp [raUses, hdec])
    have hA : Γ[c.ablatedSlot]? = Γ'[c.ablatedSlot]? :=
      hag c.ablatedSlot (by simp [raUses, hdec])
    simp only [raReplay, hdec, checkB, hF, hA]

/-- Obligation 4, validity: on acceptance every reported slot names an entry
of the consulted context. -/
theorem raUses_valid (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom)
    (hacc : raAccepts κ Γ φ) : ∀ i, i ∈ raUses κ → i < Γ.length := by
  obtain ⟨c, hdec, hchk⟩ := hacc
  obtain ⟨g, pF, pA, f, a, _, hF, hA, _⟩ :=
    checkB_extract (decodeCert_witness_den_pos hdec) hchk
  intro i hi
  simp only [raUses, hdec, List.mem_cons] at hi
  rcases hi with rfl | hi
  · exact lt_of_getElem?_eq_some hF
  · rcases hi with rfl | hfalse
    · exact lt_of_getElem?_eq_some hA
    · exact absurd hfalse (List.not_mem_nil)

/-- Obligation 4, semantic accounting: an accepted certificate's conclusion
follows from just the reported entries. -/
theorem raUses_account (κ : CertRef) (Γ : List Lara.Atom) (φ : Lara.Atom)
    (hacc : raAccepts κ Γ φ) : raModels (selectSlots Γ (raUses κ)) φ := by
  obtain ⟨c, hdec, hchk⟩ := hacc
  obtain ⟨g, pF, pA, f, a, hgoal, hF, hA, hf, ha, hfg, hag, hnz, hde, hge⟩ :=
    checkB_extract (decodeCert_witness_den_pos hdec) hchk
  have hsel : selectSlots Γ (raUses κ) = [pF, pA] := by
    simp [selectSlots, raUses, hdec, hF, hA]
  refine ⟨g, 0, 1, pF, pA, f, a, hgoal, ?_, ?_, hf, ha, hfg, hag, hnz,
    hde, hge⟩
  · rw [hsel]; rfl
  · rw [hsel]; rfl

/-! ### The registered adapter -/

/-- The one fixed RA backend core.  `Form` is the normalized source atom
itself — the identity encoding — so `enc_iff` is `equiv_iff_nf_eq`.  A
registered digest resolves to the **empty** theory (`Lara.Driver.buildRegistry`,
the seam-wide premise-only decision that extends `ord@1`'s premise-only slot
rule to `ra@1`), so the consulted context is exactly the submitted premises and every
certificate-named slot resolves to one.  The Haskell adapter reaches the same
acceptance set by rejecting any slot at or beyond the premise count; the
abstract core never learns `Δ.length`, and the empty resolution is what makes
"names a premise" and "is in range of `Γ`" the same condition. -/
def raBackend (canon : String → String) : Lara.Strict.Backend canon where
  Form := Lara.Atom
  enc := Lara.nf canon
  enc_iff := fun p q => (Lara.equiv_iff_nf_eq canon p q).symm
  modelsFull := raModels
  acceptsFull := raAccepts
  replayFull := raReplay
  replayFull_iff := raReplay_iff
  soundFull := raSound
  uses := raUses
  uses_covers := fun κ Γ Γ' φ hag => raUses_covers κ Γ Γ' φ hag
  uses_valid := raUses_valid
  uses_account := raUses_account

end Lara.RA
