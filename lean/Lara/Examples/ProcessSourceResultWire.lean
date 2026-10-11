import Lara.Process.SourceResultWire

namespace Lara.Examples.ProcessSourceResultWire
open Lara Lara.Process.Source Lara.Process.Source.ResultWire

def located : SourceRejection := .source (.core (.program (.rejection (.argument 12)
  (.R11 (.question (.premise .root 4) ⟨"why"⟩) [.prem 2, .ques ⟨"support"⟩]
    .undercut (.exceptionMismatch ⟨"rule"⟩ (.atom "expected" .nil) (.atom "actual" .nil))))))

def admission : SourceRejection := .source (.evidence
  ⟨.extraction, "leaf", some ⟨"object"⟩, "authored reason: not a tag"⟩)

theorem located_roundtrip : decodeRejection (encodeRejection located) = some located :=
  decode_encodeRejection _
theorem admission_roundtrip : decodeRejection (encodeRejection admission) = some admission :=
  decode_encodeRejection _
theorem group_roundtrip : decodeRejection (encodeRejection
    (.source (.source (.groupConflict ⟨"reports"⟩)))) =
    some (.source (.source (.groupConflict ⟨"reports"⟩))) := decode_encodeRejection _
theorem unselected_roundtrip : decodeRejection (encodeRejection
    (.unselectedCertificate 9 ⟨"argument"⟩ ⟨"backend", 3⟩)) =
    some (.unselectedCertificate 9 ⟨"argument"⟩ ⟨"backend", 3⟩) := decode_encodeRejection _

theorem blocked_labels_distinct :
    encodePublicStatus (.evidenceBlocked .justified) ≠
    encodePublicStatus (.evidenceBlocked .defeated) := by
  intro h
  have := encodePublicStatus_injective h
  cases this

theorem malformed_arity : decodeRejection (.list [.atom Tag.missingEvidence.text]) = none := by
  rfl

theorem noncanonical_number : decodeRejection
    (.list [.atom Tag.unselectedCertificate.text, .atom "01", .atom "argument",
      .list [.atom Tag.backend.text, .atom "backend", .atom "3"]]) = none := by
  simp [decodeRejection, Wire.canonical, decodeRejectionRaw, decodeNat,
    ND.decodeNat_leading_zero_01]

def structural : SourceRejection := .source (.source (.structural
  (.duplicateAdmissionKey .certified (.checker "checker-name" "version-text"))))

theorem structural_roundtrip : decodeRejection (encodeRejection structural) = some structural :=
  decode_encodeRejection _

def recursiveSupport : Support.SupportTerm := .inst ⟨"rule"⟩
  [(⟨"x"⟩, .con "f" (.cons (.str "payload") .nil))]
  [.leaf ⟨"premise"⟩] [(⟨"question"⟩, .leaf ⟨"answer"⟩)] [⟨"open"⟩]
  (.cert ⟨"backend", 2⟩ ⟨"digest"⟩ ⟨.list [.atom "authored", .list [.atom "proof"]]⟩)

def compound : SourceRejection := .source (.core (.program (.rejection (.attack 5)
  (.R1 (.premise (.question .root ⟨"q"⟩) 3) (.undeclaredAttackTarget recursiveSupport)))))

theorem compound_roundtrip : decodeRejection (encodeRejection compound) = some compound :=
  decode_encodeRejection _

theorem rejected_outcome_roundtrip :
    decodeQueryOutcome (encodeQueryOutcome (.rejected compound)) = some (.rejected compound) :=
  decode_encodeQueryOutcome _

theorem blocked_outcome_roundtrip :
    decodeQueryOutcome (encodeQueryOutcome (.accepted (.evidenceBlocked .contested))) =
      some (.accepted (.evidenceBlocked .contested)) := decode_encodeQueryOutcome _

theorem admission_optional_object_distinct :
    encodeRejection (.source (.evidence ⟨.binding, "leaf", none, "reason"⟩)) ≠
    encodeRejection (.source (.evidence ⟨.binding, "leaf", some ⟨"none"⟩, "reason"⟩)) := by
  intro h
  have := encodeRejection_injective h
  cases this

theorem unknown_outer_tag :
    decodeQueryOutcome (.list [.atom "future-outcome", encodeRejection located]) = none := by
  apply decodeQueryOutcome_unknown
  decide

end Lara.Examples.ProcessSourceResultWire
