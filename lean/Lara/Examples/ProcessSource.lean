import Lara.Examples.BHLBridge

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace Lara.Examples.ProcessSource

open Lara
open Lara.Examples.BHLBridge

/-- One ordinary declaration and its explicitly associated argument. -/
def ordinaryLeaf : Presentation.Leaf :=
  { csvLeaf with kind := .observed, provenance := .user, refs := [], extraction := none }

def ordinaryInput : Surface.Input :=
  { certifiedInput with program := { certifiedInput.program with
      decls := [.leaf ordinaryLeaf,
        .claim ⟨⟨"method"⟩, "Result", evidenceAtom,
          ⟨"reader", "declared interpretation", .reviewed⟩⟩,
        .arg ⟨⟨"selected"⟩, .supportsClaim ⟨"method"⟩,
          .explicitTheta (.leaf ordinaryLeaf.id)⟩] } }

def rejectedInput : Surface.Input :=
  { ordinaryInput with policy := { ordinaryInput.policy with
      admission := [((.observed, .user), .reject)] } }

def duplicateInput : Surface.Input :=
  { ordinaryInput with program := { ordinaryInput.program with
      decls := ordinaryInput.program.decls ++ [.leaf ordinaryLeaf] } }

def syntaxStructureInput : Surface.Input :=
  { duplicateInput with policy := { duplicateInput.policy with
      evidenceCheckers := [(.csvRow, ⟨1⟩), (.csvRow, ⟨1⟩)] } }

def rejectedEvidenceInput : Surface.Input :=
  { certifiedInput with policy := { certifiedPolicy with
      admission := [((.certified, .checker "csv-row" "1"), .reject)] } }

/-- Missing signature information reaches core checking, not source reconstruction. -/
def coreRejectedInput : Surface.Input :=
  { ordinaryInput with policy := { ordinaryInput.policy with sigma := ⟨[], [], []⟩ } }

def evidenceCoreInput : Surface.Input :=
  { certifiedInput with policy := { certifiedPolicy with sigma := ⟨[], [], []⟩ } }

def ordinaryError (input : Surface.Input) : Option Surface.SourceError :=
  match Surface.sourceWithoutEvidence certifiedEnv input with
  | .error error => some error
  | .ok _ => none

def evidenceError (input : Surface.Input) (snapshot : Evidence.Snapshot) :
    Option (Sum Surface.SourceError Evidence.AdmissionError) :=
  match Surface.sourceWithEvidence certifiedEnv input snapshot csvManifest Evidence.extract with
  | .error error => some error
  | .ok _ => none

theorem ordinary_accepted : ordinaryError ordinaryInput = none := by decide +kernel

theorem policy_rejection :
    ordinaryError rejectedInput = some (.structural (.admissionRejected ordinaryLeaf.id)) := by
  decide +kernel

theorem duplicate_rejection :
    ordinaryError duplicateInput = some (.structural (.duplicateLeafId ordinaryLeaf.id)) := by
  decide +kernel

theorem core_rejection : ordinaryError coreRejectedInput = some (.structural .unsupported) := by
  decide +kernel

theorem required_context :
    ordinaryError certifiedInput = some (.evidence csvLeaf.id) := by decide +kernel

theorem syntax_before_structure :
    evidenceError syntaxStructureInput [] = some (.inl .evidenceSyntax) := by decide +kernel

theorem admission_before_evidence :
    evidenceError rejectedEvidenceInput [] =
      some (.inl (.structural (.admissionRejected csvLeaf.id))) := by decide +kernel

/-- Both sources have the same missing capture; a later core error cannot mask it. -/
theorem evidence_before_core :
    evidenceError evidenceCoreInput [] = evidenceError certifiedInput [] ∧
      (evidenceError evidenceCoreInput []).isSome = true := by decide +kernel

def conflictingLeaf : Presentation.Leaf :=
  { ordinaryLeaf with id := ⟨"conflicting"⟩, prop := .atom "result" (.cons (.num "8") .nil) }

def groupInput : Surface.Input :=
  { ordinaryInput with program := { ordinaryInput.program with
      decls := ordinaryInput.program.decls ++ [.leaf conflictingLeaf,
        .group ⟨⟨"reports"⟩, [ordinaryLeaf.id, conflictingLeaf.id]⟩] } }

def escalatedInput : Surface.Input :=
  { groupInput with policy := { groupInput.policy with groupMode := .rejectOnConflict } }

theorem group_quarantine :
    (Surface.sourceWithoutEvidence certifiedEnv groupInput).toOption.map
      (fun output => output.unit.args) = some [] := by decide +kernel

theorem group_escalation :
    ordinaryError escalatedInput = some (.groupConflict ⟨"reports"⟩) := by decide +kernel

def mismatchedLeaf : Presentation.Leaf :=
  { csvLeaf with prop := conflictingLeaf.prop }

def mismatchedInput : Surface.Input :=
  { certifiedInput with program := { certifiedInput.program with
      decls := [.leaf mismatchedLeaf] } }

theorem evidence_mismatch :
    evidenceError mismatchedInput csvSnapshot =
      some (.inr ⟨.extraction, csvLeaf.id.val, none, "mismatch"⟩) := by decide +kernel

def groupEvidenceInput : Surface.Input :=
  { escalatedInput with program := { escalatedInput.program with
      decls := escalatedInput.program.decls ++ [.leaf { csvLeaf with id := ⟨"extraction"⟩ }] } }

theorem escalation_before_evidence :
    evidenceError groupEvidenceInput [] = some (.inl (.groupConflict ⟨"reports"⟩)) := by
  decide +kernel

def diagnosticError (input : Surface.Input) (snapshot : Evidence.Snapshot) :
    Option Surface.SourceDiagnostic :=
  match Surface.sourceWithEvidenceAudit certifiedEnv input snapshot csvManifest with
  | .error error => some error
  | .ok _ => none

theorem detailed_core_rejection :
    diagnosticError coreRejectedInput [] = some (.core (.signature .groundIllSorted)) := by
  decide +kernel

def mismatchCoreInput : Surface.Input :=
  { mismatchedInput with policy := { mismatchedInput.policy with sigma := ⟨[], [], []⟩ } }

def mismatchPolicyInput : Surface.Input :=
  { mismatchedInput with policy := { mismatchedInput.policy with
      admission := [((.certified, .checker "csv-row" "1"), .reject)] } }

theorem mismatch_before_core :
    diagnosticError mismatchCoreInput csvSnapshot =
      some (.evidence ⟨.extraction, csvLeaf.id.val, none, "mismatch"⟩) := by decide +kernel

theorem admission_before_mismatch :
    diagnosticError mismatchPolicyInput csvSnapshot =
      some (.source (.structural (.admissionRejected csvLeaf.id))) := by decide +kernel

end Lara.Examples.ProcessSource
