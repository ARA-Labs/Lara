import Lara.Process.SourceInput
import Lara.BHL.LaraBridge

namespace Lara.Process.Source

inductive SourceRejection where
  | replay : ReplayError → SourceRejection
  | source : Surface.SourceDiagnostic → SourceRejection
  | missingEvidence : Presentation.LeafId → SourceRejection
  | unselectedCertificate : Nat → Presentation.ArgId → Support.BackendId → SourceRejection
  deriving DecidableEq

def SourceInput.snapshot (input : SourceInput) : Evidence.Snapshot :=
  input.capture.map EvidenceCapture.snapshot |>.getD []

def SourceInput.manifest (input : SourceInput) : List Evidence.ObjectMeta :=
  input.capture.map EvidenceCapture.manifest |>.getD []

def selectedBackends (input : SourceInput) : List (String × String) :=
  input.replay.backends.map fun backend => (backend.name.val, backend.version.val)

/-- Inspect every authoritative reconstructed declaration, not just retained
AF arguments. The production traversal visits nested and discharge supports. -/
def firstUnselectedDeclared (selected : List (String × String)) :
    List Surface.ReconstructedArgument → Nat →
      Option (Nat × Presentation.ArgId × Support.BackendId)
  | [], _ => none
  | row :: rest, index =>
    match Driver.firstUnselectedCertificate selected row.core with
    | some backend => some (index, row.argument.id, backend)
    | none => firstUnselectedDeclared selected rest (index + 1)

theorem firstUnselectedDeclared_none_iff (selected : List (String × String)) :
    ∀ rows index, firstUnselectedDeclared selected rows index = none ↔
      ∀ row ∈ rows, Driver.CertificatesSelected selected row.core
  | [], _ => by simp [firstUnselectedDeclared]
  | row :: rest, index => by
    cases hfirst : Driver.firstUnselectedCertificate selected row.core with
    | none =>
      have selectedRow := (Driver.firstUnselectedCertificate_none_iff selected row.core).mp hfirst
      simp [firstUnselectedDeclared, hfirst, selectedRow,
        firstUnselectedDeclared_none_iff selected rest (index + 1)]
    | some backend =>
      have unselectedRow : ¬ Driver.CertificatesSelected selected row.core := by
        intro selectedRow
        have none := (Driver.firstUnselectedCertificate_none_iff selected row.core).mpr selectedRow
        rw [hfirst] at none
        cases none
      simp [firstUnselectedDeclared, hfirst, unselectedRow]

/-- Build the run from the checker value retained at the source boundary.
Only equality transports connect its context to the audit admission. -/
def retainedRun {input : SourceInput}
    (accepted : Surface.SourceWithEvidenceAudit (sourceEnv input) input.surface
      input.snapshot input.manifest) :
    Update.AcceptedRun (sourceEnv input).registry
      (BHL.sourceStateOfAudit input.surface accepted.audit) :=
  let alignment := Surface.elaborateWithAudit_alignment accepted.audit_eq
  let retained : { checked : Lara.Unit.CheckedUnit canonNum
      (Admission.buildGamma accepted.audit.declared.admission.prune.checkedLeaves)
      (Support.certOkOf (sourceEnv input).registry) //
      BHL.auditCoreResult (sourceEnv input) input.surface accepted.audit = .ok checked } := by
    unfold BHL.auditCoreResult
    rw [← alignment.outputGamma, ← alignment.outputUnit]
    exact ⟨accepted.checkedUnit, accepted.checkedUnit_eq⟩
  { declared :=
      { resolved := accepted.audit.declared.resolvedAttacks
        resolve_eq := alignment.rawResolution
        ids_nodup := alignment.idsNodup }
    admission := accepted.audit.declared.admission
    checked := retained.val
    admission_ok := alignment.admissionEvaluation
    check_ok := retained.property }

/-- Determinism identifies the retained checker value with the canonical
source bridge; the proof does not execute either checker at runtime. -/
theorem retainedRun_eq {input : SourceInput}
    (accepted : Surface.SourceWithEvidenceAudit (sourceEnv input) input.surface
      input.snapshot input.manifest) :
    retainedRun accepted = BHL.acceptedRunOfSource accepted.audit accepted.source_eq
      accepted.audit_eq rfl := by
  have same : (retainedRun accepted).checked =
      (BHL.acceptedRunOfSource accepted.audit accepted.source_eq accepted.audit_eq rfl).checked :=
    Except.ok.inj ((retainedRun accepted).check_ok.symm.trans
      (BHL.acceptedRunOfSource accepted.audit accepted.source_eq accepted.audit_eq rfl).check_ok)
  unfold retainedRun BHL.acceptedRunOfSource at same ⊢
  dsimp only at same ⊢
  simpa only [Update.AcceptedRun.mk.injEq, heq_eq_eq, true_and] using same

/-- A successful observation owns the exact authoritative source and audit
successes. Public graphs and statuses are derived from this record. -/
structure AcceptedObservation (input : SourceInput) where
  accepted : Surface.SourceWithEvidenceAudit (sourceEnv input) input.surface
    input.snapshot input.manifest
  replay_ok : replayCompatible input = .ok ()
  context_ok : input.capture.isSome = true ∨
    (Surface.leafRecords accepted.output.semanticProgram).find? Surface.needsEvidence = none
  selection_ok : firstUnselectedDeclared (selectedBackends input) accepted.audit.declared.pairs 0 = none
  run : Update.AcceptedRun (sourceEnv input).registry
    (BHL.sourceStateOfAudit input.surface accepted.audit)
  run_eq : run = BHL.acceptedRunOfSource accepted.audit accepted.source_eq accepted.audit_eq rfl

private def acceptedObservation {input : SourceInput}
    (accepted : Surface.SourceWithEvidenceAudit (sourceEnv input) input.surface
      input.snapshot input.manifest)
    (replay_ok : replayCompatible input = .ok ())
    (context_ok : input.capture.isSome = true ∨
      (Surface.leafRecords accepted.output.semanticProgram).find? Surface.needsEvidence = none)
    (selection_ok : firstUnselectedDeclared (selectedBackends input)
      accepted.audit.declared.pairs 0 = none) : AcceptedObservation input :=
  ⟨accepted, replay_ok, context_ok, selection_ok, retainedRun accepted, retainedRun_eq accepted⟩

abbrev SourceOutcome (input : SourceInput) := Except SourceRejection (AcceptedObservation input)

/-- Missing capture never supplies an observed fact. An empty immutable context
can discharge only declarations which do not require evidence. -/
def checkSource (input : SourceInput) : SourceOutcome input :=
  match hr : replayCompatible input with
  | .error error => .error (.replay error)
  | .ok _ =>
    match hs : Surface.sourceWithEvidenceAudit (sourceEnv input) input.surface
        input.snapshot input.manifest with
    | .error error => .error (.source error)
    | .ok accepted =>
      match hselected : firstUnselectedDeclared (selectedBackends input) accepted.audit.declared.pairs 0 with
      | some (index, argument, backend) => .error (.unselectedCertificate index argument backend)
      | none =>
        if hc : input.capture.isSome = true then
          .ok (acceptedObservation accepted hr (Or.inl hc) hselected)
        else
          match hn : (Surface.leafRecords accepted.output.semanticProgram).find?
              Surface.needsEvidence with
          | some leaf => .error (.missingEvidence leaf.id)
          | none => .ok (acceptedObservation accepted hr (Or.inr hn) hselected)

namespace AcceptedObservation

abbrev state {input : SourceInput} (observation : AcceptedObservation input) :=
  BHL.sourceStateOfAudit input.surface observation.accepted.audit

@[macro_inline]
def certified {input : SourceInput} (observation : AcceptedObservation input) :
    BHL.CertifiedSource Evidence.extract observation.run
      ⟨input.surface, input.snapshot, input.manifest, observation.accepted.output.ground⟩ :=
  observation.run_eq.symm ▸
    BHL.certifiedSourceOfSource observation.accepted.audit observation.accepted.source_eq
      observation.accepted.audit_eq rfl

def publicStatus {input : SourceInput} (observation : AcceptedObservation input) (query : Atom) :
    Driver.PublicStatus := BHL.ordinaryStatus observation.run query

def ordinary {input : SourceInput} (observation : AcceptedObservation input) (queries : List Atom) :=
  BHL.observeOrdinary observation.run queries

def holes {input : SourceInput} (observation : AcceptedObservation input) :=
  BHL.ordinaryHoleRows observation.run

theorem exact_source {input : SourceInput} (observation : AcceptedObservation input) :
    Surface.sourceWithEvidence (sourceEnv input) input.surface input.snapshot input.manifest
      Evidence.extract = .ok (observation.accepted.output, observation.accepted.judgments) :=
  observation.accepted.source_eq

theorem exact_audit {input : SourceInput} (observation : AcceptedObservation input) :
    Surface.elaborateWithAudit (sourceEnv input) input.surface = .ok observation.accepted.audit :=
  observation.accepted.audit_eq

theorem evidence_admitted {input : SourceInput} (observation : AcceptedObservation input) :
    Evidence.Admitted input.snapshot input.surface.policy.evidenceCheckers input.manifest
      Evidence.extract (Surface.leafRecords observation.accepted.audit.declared.semanticProgram)
      observation.accepted.judgments := observation.accepted.admitted

theorem certificates_selected {input : SourceInput} (observation : AcceptedObservation input)
    (row : Surface.ReconstructedArgument) (declared : row ∈ observation.accepted.audit.declared.pairs) :
    Driver.CertificatesSelected (selectedBackends input) row.core :=
  (firstUnselectedDeclared_none_iff (selectedBackends input)
    observation.accepted.audit.declared.pairs 0).mp observation.selection_ok row declared

end AcceptedObservation

inductive QueryOutcome where
  | rejected : SourceRejection → QueryOutcome
  | accepted : Driver.PublicStatus → QueryOutcome
  deriving DecidableEq

/-- Rejections remain observations, but never acquire a public status. -/
def observeSource (input : SourceInput) (queries : List Atom) :
    SourceOutcome input × List (Atom × QueryOutcome) :=
  let outcome := checkSource input
  (outcome, queries.map fun query => (query, match outcome with
    | .error rejection => .rejected rejection
    | .ok observation => .accepted (observation.publicStatus query)))

end Lara.Process.Source
