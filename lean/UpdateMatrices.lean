import Lara.Examples.Update

open Lara.Examples.Update

/-- Emit the deterministic, theorem-backed grounded and five-valued public
update matrices. -/
def main : IO Unit := do
  IO.println groundedCoreMatrixReport
  IO.println ""
  IO.println fiveValuedPublicMatrixReport
