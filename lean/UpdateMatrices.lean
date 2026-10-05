import Lara.Examples.Update
import Lara.Examples.UpdateCompletion

open Lara.Examples.Update

/-- Emit the deterministic, theorem-backed grounded and five-valued public
update matrices, then the completion witnesses (atomic batches and in-place
discharge). -/
def main : IO Unit := do
  IO.println groundedCoreMatrixReport
  IO.println ""
  IO.println fiveValuedPublicMatrixReport
  IO.println ""
  IO.println Lara.Examples.UpdateCompletion.completionWitnessReport
