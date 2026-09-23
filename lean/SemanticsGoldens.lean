import Lara.Examples.Semantics

open Lara.Examples.Semantics

/-- Emit the Haskell golden block without the observation-table output produced
when the examples module itself is elaborated. Used by the cross-language parity
gate; it is not part of the library surface. -/
def main : IO Unit :=
  IO.println haskellGoldens
