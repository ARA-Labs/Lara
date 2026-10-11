import Lara.Process.SourceKinds
import Lara.Examples.ProcessSource

namespace Lara.Examples.ProcessSourceKinds
open Lara Lara.Process Lara.Process.Source

def source : SourceInput :=
  { surface := ProcessSource.ordinaryInput
    replay :=
      { core := ⟨Driver.coreVersionText⟩
        policy := ProcessSource.ordinaryInput.policy.id
        backends := []
        theories := []
        artifact := ProcessSource.ordinaryInput.program.digest }
    capture := none }

def staleSource : SourceInput :=
  { source with surface := { source.surface with
      program := { source.surface.program with artifact := "different-source" } } }
def leaf : Presentation.LeafId := ⟨"leaf"⟩
def argument : Presentation.ArgId := ⟨"argument"⟩
def runEvent : Stamped := ⟨⟨0⟩, .run ⟨0⟩ ⟨0⟩ ⟨0⟩ [] ⟨0⟩⟩
def specs : List KindSpec :=
  [⟨source, .leaf leaf, .observed, some ⟨0⟩⟩,
    ⟨source, .argument argument, .observed, some ⟨1⟩⟩]
def assumptions : List CaptureAssumption :=
  [⟨⟨0⟩, source, .leaf leaf, runEvent, ⟨0⟩, .instrumentedLog⟩,
    ⟨⟨1⟩, source, .argument argument, runEvent, ⟨0⟩, .instrumentedLog⟩]

theorem explicit_admission :
    nodeKind source [runEvent] specs assumptions [.instrumentedLog] [] argument
      (.leaf ⟨leaf.val⟩) = (.observed, true) := by decide +kernel

theorem replay_label_is_not_admission :
    nodeKind source [runEvent] specs assumptions [] [] argument
      (.leaf ⟨leaf.val⟩) = (.conditional, true) := by decide +kernel

theorem stale_process_binding :
    nodeKind source [] specs assumptions [.instrumentedLog] [] argument
      (.leaf ⟨leaf.val⟩) = (.conditional, true) := by decide +kernel


theorem stale_source_binding :
    staleSource.surface.program.digest = source.surface.program.digest ∧
      staleSource.replay = source.replay ∧
      nodeKind source [runEvent] specs
        (assumptions.map fun assumption => { assumption with source := staleSource })
        [.instrumentedLog] [] argument (.leaf ⟨leaf.val⟩) =
        (.conditional, true) := by decide +kernel

theorem slot_overrides_observed_declaration :
    nodeKind source [runEvent] specs assumptions [.instrumentedLog] [.leaf leaf] argument
      (.leaf ⟨leaf.val⟩) = (.hypothetical, true) := by decide +kernel

theorem absent_node_metadata :
    nodeKind source [runEvent] [] assumptions [.instrumentedLog] [] argument
      (.leaf ⟨leaf.val⟩) = (.hypothetical, false) := by decide +kernel

def selectedKind : EvidenceKind × Bool :=
  nodeKind source [runEvent] specs assumptions [.instrumentedLog] [] argument (.leaf ⟨leaf.val⟩)

def otherKind : EvidenceKind × Bool :=
  nodeKind source [runEvent] specs assumptions [.instrumentedLog] [] ⟨"other"⟩ (.leaf ⟨leaf.val⟩)

theorem missing_non_witness_metadata :
    selectedKind = (.observed, true) ∧ otherKind = (.hypothetical, false) ∧
      (meetKinds [selectedKind, otherKind]).2 = false := by decide +kernel

theorem discharge_inputs_are_used :
    supportKeys (.inst ⟨"rule"⟩ [] [] [(⟨"discharge"⟩, .leaf ⟨leaf.val⟩)] [] .none) =
      [.method ⟨"rule"⟩, .leaf leaf] := by decide +kernel

end Lara.Examples.ProcessSourceKinds
