import Lara.Process.FamilyWire
import Lara.Examples.ProcessSource

namespace Lara.Examples.ProcessFamilyWire

open Lara.Process Lara.Process.Family Lara.Process.Family.Wire
open Lara.Process.InquiryProcessWire

private def names : Process.Wire.Names :=
  ⟨["commit", "run"], ["reader"], ["plan"], ["analysis"], [], [],
    ["selection", "test"], ["family"], []⟩

private def commit : Stamped := ⟨⟨0⟩, .commitPlan ⟨0⟩ ⟨0⟩ ⟨2⟩⟩
private def run : Stamped := ⟨⟨1⟩, .run ⟨0⟩ ⟨0⟩ ⟨2⟩ [(⟨1⟩, ⟨3⟩)] ⟨0⟩⟩
private def guard : Guard :=
  .and (.query (.conj (.atom (.runPrecommitted ⟨0⟩))
    (.disj (.atom (.splitSelection [⟨0⟩] [⟨1⟩]))
      (.neg (.atom (.familyCountAtMost ⟨0⟩ 2))))))
    (.or (.before commit run) (.not (.present run)))
private def fragment : SourceFragment :=
  [.leaf ProcessSource.ordinaryLeaf,
   .leaf { ProcessSource.ordinaryLeaf with id := ⟨"second-leaf"⟩ }]
private def choice : Choice := ⟨⟨3⟩, guard, fragment⟩
private def otherChoice : Choice := ⟨⟨8⟩, guard, fragment⟩
private def slot : Slot := ⟨⟨4⟩, [choice, otherChoice]⟩
private def completion : Completion :=
  ⟨[run, commit, run], [⟨⟨4⟩, choice⟩, ⟨⟨9⟩, otherChoice⟩]⟩

private theorem names_unique : UniqueNames names := by
  unfold UniqueNames names
  decide +kernel

private theorem guard_named : GuardWellNamed names guard := by
  simp [GuardWellNamed, QueryWellNamed, AtomWellNamed, StampedWellNamed,
    EventWellNamed, InputWellNamed, guard, commit, run, names]

theorem nested_guard_fragment_roundtrip :
    decodeChoice names (encodeChoice names choice) = some choice :=
  decode_encodeChoice names names_unique choice guard_named

theorem ordered_slot_roundtrip :
    decodeSlot names (encodeSlot names slot) = some slot :=
  decode_encodeSlot names names_unique slot (by
    simp [SlotWellNamed, slot, ChoiceWellNamed, choice, otherChoice, guard_named])

theorem ordered_completion_roundtrip :
    decodeCompletion names (encodeCompletion names completion) = some completion :=
  decode_encodeCompletion names names_unique completion (by
    constructor
    · simp [completion, StampedWellNamed, EventWellNamed, InputWellNamed, commit, run, names]
    · simp [completion, SelectionWellNamed, ChoiceWellNamed, choice, otherChoice, guard_named])

theorem equal_fragments_distinct_identities :
    choice.fragment = otherChoice.fragment ∧
      encodeChoice names choice ≠ encodeChoice names otherChoice ∧
      encodeSelection names ⟨⟨4⟩, choice⟩ ≠ encodeSelection names ⟨⟨9⟩, choice⟩ := by
  decide +kernel

theorem malformed_arity_rejected :
    decodeGuard names (.list [.atom Tag.before.text, Process.Wire.encodeStamped names commit]) = none ∧
      decodeChoice names (.list [.atom Tag.choice.text, encodeChoiceId ⟨3⟩,
        encodeGuard names guard]) = none := by
  decide +kernel

theorem noncanonical_indices_rejected :
    decodeChoiceId (.list [.atom Tag.choiceId.text, .atom "01"]) = none ∧
      decodeSlotId (.list [.atom Tag.slotId.text, .atom "01"]) = none := by
  have canonical : ∀ text, (Process.Wire.decodeNat (.atom text)).toOption = ND.decodeNat text := by
    intro text
    unfold Process.Wire.decodeNat ND.decodeNat
    cases parsed : text.toNat? with
    | none => simp [parsed, Process.Wire.bad, Except.toOption]
    | some n =>
        by_cases equal : text = Nat.repr n
        · simp [equal, Except.toOption, toString]
        · simp [parsed, equal, eq_comm, Except.toOption, Process.Wire.bad, toString]
  simp [decodeChoiceId, decodeSlotId, canonical, ND.decodeNat_leading_zero_01]

end Lara.Examples.ProcessFamilyWire
