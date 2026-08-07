/-
Shared cell machinery for the rational-arithmetic strict backends — the Lean
mirror of the Haskell `Lara.Strict.Cell` factoring.

`ra@1` (`Lara.RA`) and `ord@1` (`Lara.Ord`) certify goals over measured cells
and share the same three sub-problems: decoding a slot reference from the
opaque certificate, parsing canonical numerals (the `canon` image), and
extracting the one numeric literal a consulted context entry carries.  One
definition, two importers — each backend keeps its own closed top-level
certificate tag (`radrop` / `ordcmp`), while the slot-reference sub-grammar
has exactly one home: the `prem` spelling lives in this file's `Tag` table and
nowhere else.

Definitions travel with their lemmas, so the sibling theories stay symmetric
and there is no `Ord → RA` dependency.

Rationals are represented as integer numerators over positive denominators
(parsed decimals carry a power-of-ten denominator), and every comparison is a
cross-multiplied integer identity, so the whole development stays in core
Lean: no `Rat`, no Mathlib.
-/

import Lara.Strict

namespace Lara.Cell

open Lara.Support (SExpr)

/-! ### Exact decimals -/

/-- An exact rational as an integer numerator over a positive denominator.
Parsed decimals always carry a power-of-ten denominator; certificate witness
fractions carry an arbitrary positive denominator in lowest terms. -/
structure Dec where
  num : Int
  den : Nat
deriving DecidableEq, Repr

/-- Canonical natural: digits only, no sign, no leading zeros (the Haskell
`parseCanonicalNat`). -/
def parseCanonNat (s : String) : Option Nat :=
  match s.toNat? with
  | some n => if s = Nat.repr n then some n else none
  | none => none

/-- Canonical integer: an optional `-` on a nonzero canonical natural. -/
def parseCanonInt (s : String) : Option Int :=
  if s.startsWith "-" then
    match parseCanonNat (s.drop 1).toString with
    | some n => if n = 0 then none else some (-(n : Int))
    | none => none
  else (parseCanonNat s).map (fun n => (n : Int))

/-- Fraction digits: nonempty, digits only, no trailing zero (the value may
carry leading zeros — `05` in `0.05`). -/
def parseFracDigits (s : String) : Option Nat :=
  match s.toNat? with
  | some m => if s.endsWith "0" then none else some m
  | none => none

def parseUnsigned (s : String) : Option Dec :=
  match s.splitOn "." with
  | [intPart] => (parseCanonNat intPart).map (fun n => ⟨(n : Int), 1⟩)
  | [intPart, fracPart] =>
      match parseCanonNat intPart, parseFracDigits fracPart with
      | some n, some m =>
          let scale := 10 ^ fracPart.length
          some ⟨((n * scale + m : Nat) : Int), scale⟩
      | _, _ => none
  | _ => none

/-- Parse a canonical decimal numeral (the `canon` image: optional `-`, no
leading zeros, no trailing fraction zeros) into an exact rational — the
mirror of the Haskell adapters' `parseDecimal`. -/
def parseDecimal (s : String) : Option Dec :=
  if s.startsWith "-" then
    (parseUnsigned (s.drop 1).toString).map (fun d => ⟨-d.num, d.den⟩)
  else parseUnsigned s

/-! ### Cross-multiplied rational comparisons

Valid as rational equality/order exactly when the denominators are nonzero,
which the parsers and the decoders guarantee.

All four relations are stated over the *same* two integer expressions
`a.num * b.den` and `b.num * a.den`, which is what makes the `ord@1`
intra-family exclusivity lemmas fall to `omega`. -/

/-- `a = b` over ℚ, cross-multiplied. -/
def RatEq (a b : Dec) : Prop := a.num * (b.den : Int) = b.num * (a.den : Int)

/-- `a ≥ b` over ℚ, cross-multiplied (positive denominators). -/
def RatGe (a b : Dec) : Prop := b.num * (a.den : Int) ≤ a.num * (b.den : Int)

/-- `a < b` over ℚ, cross-multiplied (positive denominators). -/
def RatLt (a b : Dec) : Prop := a.num * (b.den : Int) < b.num * (a.den : Int)

/-- `a ≤ b` over ℚ, cross-multiplied (positive denominators). -/
def RatLe (a b : Dec) : Prop := a.num * (b.den : Int) ≤ b.num * (a.den : Int)

def ratEqB (a b : Dec) : Bool := a.num * (b.den : Int) == b.num * (a.den : Int)

def ratGeB (a b : Dec) : Bool :=
  decide (b.num * (a.den : Int) ≤ a.num * (b.den : Int))

def ratLtB (a b : Dec) : Bool :=
  decide (a.num * (b.den : Int) < b.num * (a.den : Int))

def ratLeB (a b : Dec) : Bool :=
  decide (a.num * (b.den : Int) ≤ b.num * (a.den : Int))

theorem ratEqB_iff (a b : Dec) : ratEqB a b = true ↔ RatEq a b := by
  simp [ratEqB, RatEq]

theorem ratGeB_iff (a b : Dec) : ratGeB a b = true ↔ RatGe a b := by
  simp [ratGeB, RatGe]

theorem ratLtB_iff (a b : Dec) : ratLtB a b = true ↔ RatLt a b := by
  simp [ratLtB, RatLt]

theorem ratLeB_iff (a b : Dec) : ratLeB a b = true ↔ RatLe a b := by
  simp [ratLeB, RatLe]

/-! ### Order facts

The trichotomy the `ord@1` family rests on.  Each is a statement about the two
integer expressions above, so `omega` closes it with no positivity side
condition. -/

/-- `≤` splits into `<` and `=`. -/
theorem ratLe_iff_lt_or_eq (a b : Dec) : RatLe a b ↔ (RatLt a b ∨ RatEq a b) := by
  unfold RatLe RatLt RatEq; omega

/-- Strict order is irreflexive: `a < a` is false. -/
theorem ratLt_irrefl (a : Dec) : ¬ RatLt a a := by
  unfold RatLt; omega

/-- Non-strict order is reflexive. -/
theorem ratLe_refl (a : Dec) : RatLe a a := by
  unfold RatLe; omega

/-! ### The consulted-cell convention -/

mutual
  def termNums : Lara.Term → List String
    | .num n => [n]
    | .str _ => []
    | .con _ ts => termsNums ts

  def termsNums : Lara.Terms → List String
    | .nil => []
    | .cons t ts => termNums t ++ termsNums ts
end

/-- A consulted context entry must carry exactly one numeric literal anywhere
in its argument terms; that literal is the cell.  Zero or several literals is
a rejection: the adapter refuses to guess which number the evidence reports. -/
def premiseCell : Lara.Atom → Option Dec
  | .atom _ ts =>
      match termsNums ts with
      | [n] => parseDecimal n
      | _ => none

/-! ### The slot-reference wire sub-grammar

`slot := (prem N)` with `N` a canonical natural.  Shared by both backends;
each backend's own top-level certificate tag lives in that backend's table. -/

/-- The closed set of shared wire keywords (`Lara.ND.Tag` discipline: the
concrete spellings live in exactly one table).  Only the slot-reference
keyword is shared. -/
inductive Tag where
  | prem
deriving DecidableEq, Repr

def Tag.toString : Tag → String
  | .prem => "prem"

def Tag.all : List Tag := [.prem]

def Tag.parse (s : String) : Option Tag :=
  Tag.all.find? (fun t => t.toString = s)

/-- Decode a slot reference `(prem N)`. -/
def decodeSlot : SExpr → Option Nat
  | .list [.atom k, .atom n] =>
      match Tag.parse k with
      | some .prem => parseCanonNat n
      | _ => none
  | _ => none

/-! ### Shared list lemma -/

/-- A successful indexed lookup bounds the index — the shape both adapters'
obligation-4 validity proofs need. -/
theorem lt_of_getElem?_eq_some {α : Type _} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : i < l.length := by
  rcases Nat.lt_or_ge i l.length with hlt | hge
  · exact hlt
  · rw [List.getElem?_eq_none hge] at h
    simp at h

end Lara.Cell
