import Lara.Examples.ProcessSource
import Lara.Process.Source
import Lara.Process.SourceCoordinates

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace Lara.Examples.ProcessSourceCoordinates
open Lara Lara.Process.Source Lara.Examples.ProcessSource Lara.Examples.BHLBridge

def sourceInput (surface : Surface.Input) : SourceInput :=
  { surface := surface
    replay := { core := ⟨Driver.coreVersionText⟩, policy := surface.policy.id, backends := [], theories := [], artifact := surface.program.digest }
    capture := none }

def earlierLeaf : Presentation.Leaf :=
  { conflictingLeaf with id := ⟨"earlier-leaf"⟩, kind := .attested }

def beforeInput : SourceInput := sourceInput
  { ordinaryInput with program := { ordinaryInput.program with decls :=
      [.leaf earlierLeaf,
        .claim ⟨⟨"earlier-claim"⟩, "Other result", earlierLeaf.prop,
          ⟨"reader", "declared interpretation", .reviewed⟩⟩,
        .arg ⟨⟨"earlier"⟩, .supportsClaim ⟨"earlier-claim"⟩,
          .explicitTheta (.leaf earlierLeaf.id)⟩] ++ ordinaryInput.program.decls } }

def afterInput : SourceInput := sourceInput
  { beforeInput.surface with policy := { beforeInput.surface.policy with
      admission := [((.attested, .user), .quarantine)] } }

def accepted (input : SourceInput) (success : (checkSource input).isOk = true) :
    AcceptedObservation input :=
  (checkSource input).toOption.get (by
    cases equation : checkSource input with
    | error error => rw [equation] at success; contradiction
    | ok observation => rfl)

theorem before_accepted : (checkSource beforeInput).isOk = true := by decide +kernel
theorem after_accepted : (checkSource afterInput).isOk = true := by decide +kernel

def before := accepted beforeInput before_accepted
def after := accepted afterInput after_accepted

def carrier : List Presentation.ArgId := [⟨"earlier"⟩, ⟨"selected"⟩]

theorem pruning_shifts_checked_index :
    Coordinates.names before.run = [⟨"earlier"⟩, ⟨"selected"⟩] ∧
      Coordinates.names after.run = [⟨"selected"⟩] := by decide +kernel

theorem selected_identity_is_stable :
    Coordinates.identity before.run carrier 1 = 1 ∧
      Coordinates.identity after.run carrier 0 = 1 := by decide +kernel

theorem selected_support_is_exact :
    Coordinates.supports before.run evidenceAtom = [⟨"selected"⟩] ∧
      Coordinates.supports after.run evidenceAtom = [⟨"selected"⟩] := by decide +kernel

theorem deleted_argument_does_not_alias :
    0 ∉ (Coordinates.graph after.run carrier).args ∧
      1 ∈ (Coordinates.graph after.run carrier).args := by decide +kernel

end Lara.Examples.ProcessSourceCoordinates
