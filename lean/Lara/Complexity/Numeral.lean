/-
Verified decimal round-trip and numeral injectivity for the M2b complexity
spine (issue #209). This is a local copy of the `Lara.ND.decodeNat` pattern
per decision D7 (module-ownership seam: no import of the ND backend).
-/
import Std.Data.String.ToNat

namespace Lara.Complexity.Numeral

/-- Local copy of the `Lara.ND.decodeNat` pattern (module-ownership seam; see D7). -/
def decodeNat (s : String) : Option Nat := do
  let n ← s.toNat?
  if s = Nat.repr n then some n else none

@[simp] theorem decodeNat_repr (n : Nat) : decodeNat (Nat.repr n) = some n := by
  simp [decodeNat]

theorem natRepr_inj {m n : Nat} (h : Nat.repr m = Nat.repr n) : m = n :=
  Option.some.inj ((decodeNat_repr m).symm.trans (h ▸ decodeNat_repr n))

theorem natRepr_toList_inj {m n : Nat}
    (h : (Nat.repr m).toList = (Nat.repr n).toList) : m = n :=
  natRepr_inj (String.toList_injective h)

/-- Every character of a decimal numeral is a digit, so `Nat.repr` never emits
the `'-'` separator character. -/
theorem repr_no_dash (n : Nat) : ¬ '-' ∈ (Nat.repr n).toList := by
  intro hmem
  rcases (String.isNat_iff.mp (Nat.isNat_repr n)).2.1 '-' hmem with hdigit | hunderscore
  · exact absurd hdigit (by decide)
  · exact absurd hunderscore (by decide)

end Lara.Complexity.Numeral
