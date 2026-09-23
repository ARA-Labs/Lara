/-
The Lean side of the cross-language presentation-shape parity guard: print the
normalized ordered TSV inventory that `scripts/check-presentation-parity.sh`
diffs against the Haskell one. See `Lara/PresentationParity.lean` for the
witnesses, shape tripwire, and named representation exemptions.
-/
import Lara.PresentationParity

def main : IO Unit :=
  IO.print Lara.PresentationParity.renderShape
