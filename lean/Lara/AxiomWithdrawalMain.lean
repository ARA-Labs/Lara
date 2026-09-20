/- Executable companion to the separately proved #350 structural witness. -/
import Lara.Examples.AxiomWithdrawal

open Lara.Examples.AxiomWithdrawal
open Lara.PW.Instance

def main : IO Unit := do
  IO.println "Axiom withdrawal: separate Lean structural-contract witness"
  for (name, action) in [("admit", Lara.Presentation.Admission.admit),
      ("quarantine", .quarantine), ("reject", .reject)] do
    let outcome := match admission action with
      | .accepted _ => "accepted"
      | .rejected _ => "rejected (R8)"
      | .invalid _ => "invalid"
    IO.println s!"source admission ({name}): {outcome}"
  IO.println s!"unit checker (admit): {(checked retained).isOk}"
  IO.println s!"unit checker (quarantine): {(checked withdrawn).isOk}"
  IO.println s!"local status (admit): {Lara.Driver.statusStr (cmpStatus source postulate)}"
  IO.println s!"local status (quarantine): {Lara.Driver.statusStr (cmpStatus target postulate)}"
  IO.println s!"identity leaf preservation (retained): {leafCheck (gamma retained)}"
  IO.println s!"identity leaf preservation (withdrawn): {leafCheck (gamma withdrawn)}"
  IO.println s!"ND replay (premise present): {Lara.Support.certOkBOf reg Lara.Driver.ndBackendId digest certificate [postulate] postulate}"
  IO.println s!"ND replay (premise absent): {Lara.Support.certOkBOf reg Lara.Driver.ndBackendId digest certificate [] postulate}"
