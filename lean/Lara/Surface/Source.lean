import Lara.Surface.Correctness
import Lara.Evidence.Admission
import Lara.Evidence.Extract

namespace Lara.Surface

/-- Evidence rejection is an outer source boundary, not a fabricated ordinary
policy-table rejection. Structural assembly is untrusted until the gate and
ordinary core continuation have both succeeded. -/
inductive SourceError where
  | structural : Error → SourceError
  | evidence : Presentation.LeafId → SourceError
  | evidenceSyntax : SourceError
  | groupConflict : Presentation.GroupId → SourceError
  deriving DecidableEq

def needsEvidence (leaf : Presentation.Leaf) : Bool :=
  leaf.kind == .certified || leaf.extraction.isSome

/-- Escalation is a source policy check on the complete semantic leaf table,
before evidence replay. Quarantine mode keeps the ordinary admission prune. -/
def checkSourceGroups (canon : String → String) (policy : Presentation.Policy)
    (semantic : Presentation.Program) : Except SourceError _root_.Unit :=
  match policy.groupMode with
  | .quarantineOnConflict => .ok ()
  | .rejectOnConflict =>
    match (admissionGroups semantic).find?
        (fun group => !Lara.Groups.consistentB canon (admissionLeafTable semantic) group) with
    | none => .ok ()
    | some group => .error (.groupConflict ⟨group.id⟩)

/-- The same ordinary core continuation as `check`, without re-expanding source. -/
def finishAssembled (env : Env canon) (output : Elaborated canon) : Except Error (Elaborated canon) :=
  match Check.Unit.checkUnit output.gamma env.registry output.ground output.unit with
  | .ok _ => .ok output
  | .error _ => .error .unsupported

theorem finishAssembled_eq_check {env : Env canon} {input output}
    (h : assemble env input = .ok output) : finishAssembled env output = check env input := by
  rw [check_eq_of_assemble env input output h]
  rfl

def elaborateSourceWithoutEvidence (env : Env canon) (input : Input) :
    Except SourceError (Elaborated canon) := do
  if !(decide input.policy.evidenceCheckers.Nodup) then .error .evidenceSyntax else do
    let lowered ← (assemble env input).mapError .structural
    checkSourceGroups canon input.policy lowered.semanticProgram
    match (leafRecords lowered.semanticProgram).find? needsEvidence with
    | some leaf => .error (.evidence leaf.id)
    | none => .ok lowered

def sourceWithoutEvidence (env : Env canon) (input : Input) :
    Except SourceError (Elaborated canon) := do
  let lowered ← elaborateSourceWithoutEvidence env input
  (finishAssembled env lowered).mapError .structural

theorem elaborateSourceWithoutEvidence_assembled {env : Env canon} {input output}
    (h : elaborateSourceWithoutEvidence env input = .ok output) : assemble env input = .ok output := by
  have hn : input.policy.evidenceCheckers.Nodup := by
    by_cases hp : input.policy.evidenceCheckers.Nodup
    · exact hp
    · simp [elaborateSourceWithoutEvidence, hp] at h
  unfold elaborateSourceWithoutEvidence at h
  simp [hn] at h
  cases hs : assemble env input with
  | error e => simp [hs, Except.mapError, Lara.Evidence.except_bind_error] at h
  | ok lowered =>
    simp only [hs, Except.mapError, Lara.Evidence.except_bind_ok] at h
    cases hg : checkSourceGroups canon input.policy lowered.semanticProgram with
    | error error => simp [hg, Lara.Evidence.except_bind_error] at h
    | ok ignored =>
      simp only [hg, Lara.Evidence.except_bind_ok] at h
      cases hf : (leafRecords lowered.semanticProgram).find? needsEvidence with
      | some leaf => simp [hf] at h
      | none =>
        simp only [hf] at h
        injection h with hlo
        subst hlo
        rfl

theorem sourceWithoutEvidence_core {env : Env canon} {input output}
    (h : sourceWithoutEvidence env input = .ok output) : check env input = .ok output := by
  unfold sourceWithoutEvidence at h
  cases hs : elaborateSourceWithoutEvidence env input with
  | error e => simp [hs, Except.mapError, Lara.Evidence.except_bind_error] at h
  | ok lowered =>
    have ha := elaborateSourceWithoutEvidence_assembled hs
    have hf : (finishAssembled env lowered).mapError SourceError.structural = .ok output := by
      simpa [hs, Lara.Evidence.except_bind_ok] using h
    rw [finishAssembled_eq_check ha] at hf
    cases hc : check env input with
    | error e => simp [hc, Except.mapError] at hf
    | ok checked =>
      simp only [hc, Except.mapError] at hf
      injection hf with hco
      subst hco
      rfl

theorem sourceWithoutEvidence_sound {env : Env canon} {input output}
    (h : sourceWithoutEvidence env input = .ok output) : Checks env input output :=
  check_sound env input output (sourceWithoutEvidence_core h)

theorem sourceWithoutEvidence_conservative {env : Env canon} {input output}
    (assembled : assemble env input = .ok output)
    (nodup : input.policy.evidenceCheckers.Nodup)
    (ordinary : (leafRecords output.semanticProgram).find? needsEvidence = none)
    (groups : checkSourceGroups canon input.policy output.semanticProgram = .ok ())
    (checked : check env input = .ok output) :
    sourceWithoutEvidence env input = .ok output := by
  have finish : finishAssembled env output = .ok output := by
    rw [finishAssembled_eq_check assembled]
    exact checked
  simp [sourceWithoutEvidence, elaborateSourceWithoutEvidence, nodup, assembled, ordinary,
    groups, finish, Except.mapError]

/-- Expand values/comparisons and perform ordinary structural/policy assembly
once. Replay ALL semantic declarations before the unchanged core continuation.
The full semanticProgram remains available even for pruned or unused leaves. -/
def sourceWithEvidence (env : Env canonNum) (input : Input)
    (snapshot : Evidence.Snapshot) (manifest : List Evidence.ObjectMeta)
    (registry : Evidence.Registry) :
    Except (Sum SourceError Evidence.AdmissionError) (Elaborated canonNum × List Evidence.Judgment) := do
  if !(decide input.policy.evidenceCheckers.Nodup) then
    .error (Sum.inl .evidenceSyntax) else do
    let lowered ← (assemble env input).mapError (Sum.inl ∘ SourceError.structural)
    (checkSourceGroups canonNum input.policy lowered.semanticProgram).mapError Sum.inl
    let judgments ← (Evidence.admit snapshot input.policy.evidenceCheckers manifest registry
      (leafRecords lowered.semanticProgram)).mapError Sum.inr
    let checked ← (finishAssembled env lowered).mapError (Sum.inl ∘ SourceError.structural)
    .ok (checked, judgments)

theorem sourceWithEvidence_core_and_semantic {env : Env canonNum}
    {input snapshot manifest registry output judgments}
    (h : sourceWithEvidence env input snapshot manifest registry = .ok (output, judgments)) :
    check env input = .ok output ∧
    Evidence.Admitted snapshot input.policy.evidenceCheckers manifest registry
      (leafRecords output.semanticProgram) judgments := by
  unfold sourceWithEvidence at h
  have hn : input.policy.evidenceCheckers.Nodup := by
    by_cases hp : input.policy.evidenceCheckers.Nodup
    · exact hp
    · simp [sourceWithEvidence, hp] at h
  simp [hn] at h
  cases hs : assemble env input with
  | error e => simp [hs, Except.mapError, Lara.Evidence.except_bind_error] at h
  | ok lowered =>
    simp only [hs, Except.mapError, Lara.Evidence.except_bind_ok] at h
    cases hg : checkSourceGroups canonNum input.policy lowered.semanticProgram with
    | error error => simp [hg, Except.mapError, Lara.Evidence.except_bind_error] at h
    | ok ignored =>
      simp only [hg, Except.mapError, Lara.Evidence.except_bind_ok] at h
      cases he : Evidence.admit snapshot input.policy.evidenceCheckers manifest registry
          (leafRecords lowered.semanticProgram) with
      | error e => simp [he, Except.mapError, Lara.Evidence.except_bind_error] at h
      | ok js =>
        simp only [he, Except.mapError, Lara.Evidence.except_bind_ok] at h
        cases hc : Check.Unit.checkUnit lowered.gamma env.registry lowered.ground lowered.unit with
        | error e => simp [finishAssembled, hc, Except.mapError, Lara.Evidence.except_bind_error] at h
        | ok checked =>
          simp only [finishAssembled, hc, Except.mapError, Lara.Evidence.except_bind_ok] at h
          injection h with hpair
          rcases hpair with ⟨rfl, rfl⟩
          exact ⟨by simp [check, hs, hc], Evidence.admit_iff.mp he⟩

theorem sourceWithEvidence_semantic {env : Env canonNum}
    {input snapshot manifest registry output judgments}
    (h : sourceWithEvidence env input snapshot manifest registry = .ok (output, judgments)) :
    Evidence.Admitted snapshot input.policy.evidenceCheckers manifest registry
      (leafRecords output.semanticProgram) judgments :=
  (sourceWithEvidence_core_and_semantic h).2

theorem sourceWithEvidence_sound {env : Env canonNum} {input snapshot manifest registry output judgments}
    (h : sourceWithEvidence env input snapshot manifest registry = .ok (output, judgments)) :
    Checks env input output ∧ ∃ lowered,
      elaborateWithAudit env input = .ok lowered ∧
      Evidence.Admitted snapshot input.policy.evidenceCheckers manifest registry
        (leafRecords lowered.declared.semanticProgram) judgments := by
  have core := sourceWithEvidence_core_and_semantic h
  have checks := check_sound env input output core.1
  have helab := elaborate_complete env input output checks
  cases hl : elaborateWithAudit env input with
  | error error => simp [elaborate, hl, Except.map] at helab
  | ok lowered =>
    have ho : lowered.output = output := by
      simpa [elaborate, hl, Except.map] using helab
    have hs : output.semanticProgram = lowered.declared.semanticProgram := by
      rw [← ho]
      exact (elaborateWithAudit_alignment hl).outputSemanticProgram
    exact ⟨checks, lowered, rfl, by simpa [hs] using core.2⟩

/-- The audit suffix starts after the shared expansion and reconstruction.
It is delayed until evidence and core acceptance, so its diagnostics cannot
preempt the existing source boundary. -/
private def auditAfterAssembly (canon : String → String) (input : Input)
    (semantic : Presentation.Program) (pairs : List ReconstructedArgument)
    (surfaceResolved : List Lara.Attack.Attack) : Except Error (ElaboratedWithAudit canon) := do
  let surfaceAttacks := surfaceAttacksOf semantic
  let rawAttacks ← match rawAttacksOfResolved surfaceAttacks surfaceResolved with
    | none =>
        let endpoints := (surfaceAttacks.head?.map attackEndpoints).getD (⟨""⟩, ⟨""⟩)
        .error (.invalidSurfaceAttack endpoints.1 endpoints.2)
    | some raw => .ok raw
  let argsRaw := admissionArgs pairs
  if hids : (argsRaw.map (·.1)).Nodup then
    match resolveAligned argsRaw rawAttacks hids with
    | .error _ =>
        let endpoints := (surfaceAttacks.head?.map attackEndpoints).getD (⟨""⟩, ⟨""⟩)
        .error (.invalidSurfaceAttack endpoints.1 endpoints.2)
    | .ok aligned =>
        match Lara.Admission.evaluateAdmission canon (admissionRows input.policy)
            (admissionLeafMetas semantic) (admissionLeafTable semantic) argsRaw
            rawAttacks (admissionGroups semantic) aligned with
        | .invalid (.duplicateAdmissionKey key) =>
            .error (.duplicateAdmissionKey key.1 key.2)
        | .invalid (.duplicateLeafId leaf) => .error (.duplicateLeafId ⟨leaf.name⟩)
        | .invalid .metadataLeafMisalignment => .error (.duplicateLeafId ⟨""⟩)
        | .rejected rejection => .error (.admissionRejected ⟨rejection.leaf.name⟩)
        | .accepted admission =>
            .ok
              { declared :=
                  { semanticProgram := semantic
                    pairs := pairs
                    rawAttacks := rawAttacks
                    resolvedAttacks := aligned.resolved
                    unit :=
                      { sigma := input.policy.sigma
                        policy := toCorePolicy input.policy
                        args := pairs.map (·.core)
                        atts := aligned.resolved }
                    admission := admission }
                output := outputFromAdmission input semantic pairs admission }
  else .error (.duplicateArgId ⟨""⟩)

/-- Assembly retains its already reconstructed rows through a delayed audit
continuation. Both equations are proofs and disappear from executable code. -/
private structure AssemblyWithAudit (env : Env canon) (input : Input) where
  output : Elaborated canon
  assembled : assemble env input = .ok output
  audit : _root_.Unit → Except Error (ElaboratedWithAudit canon)
  audit_eq : elaborateWithAudit env input = audit ()

/-- The ordinary assembly order, retaining the intermediate material rather
than running either source expansion or argument reconstruction again. -/
private def assembleRetainingAudit (env : Env canon) (input : Input) :
    Except Error (AssemblyWithAudit env input) :=
  match hp : elaborationPrologue input with
  | .error error => .error error
  | .ok _ =>
  match hv : expandValues input.policy input.program with
  | .error error => .error error
  | .ok valueExpanded =>
  match hc : expandComparisons input.policy valueExpanded with
  | .error error => .error error
  | .ok (semantic, _) =>
  match hi : semanticIdentifierChecks input.policy input.program with
  | .error error => .error error
  | .ok _ =>
  match hg : validateGroups semantic with
  | .error error => .error error
  | .ok _ =>
  match hr : reconstructArgs env semantic input.policy semantic.decls [] with
  | .error (.build id) => .error (.invalidInferredArgument id)
  | .error (.lower id) => .error (.invalidNamedCertificate id)
  | .error (.conclusionMismatch id claim) => .error (.conclusionMismatch id claim)
  | .error (.challengeTargetUndeclared id) => .error (.challengeTargetUndeclared id)
  | .ok pairs =>
  if hids : (pairs.map fun pair => pair.argument.id.val).Nodup then
  match ha : resolveSurfaceAttacks input.policy
      (pairs.map fun pair => (pair.argument.id, pair.core))
      (surfaceAttacksOf semantic) with
  | .error (source, target) => .error (.invalidSurfaceAttack source target)
  | .ok declaredResolved =>
  match hs : resolveStatuses semantic with
  | .error error => .error error
  | .ok _ =>
  match hguard : assembleGuards input with
  | .error error => .error error
  | .ok _ =>
      let keptIds :=
        (keptReconstructed canon input.policy semantic pairs).map (·.argument.id)
      let resolved :=
        selectResolvedAttacks keptIds (surfaceAttacksOf semantic) declaredResolved
      .ok
        { output :=
            { gamma := surfaceGamma canon input.policy semantic
              ground := surfaceGround canon input.policy semantic
              unit :=
                { sigma := input.policy.sigma
                  policy := toCorePolicy input.policy
                  args := (keptReconstructed canon input.policy semantic pairs).map (·.core)
                  atts := resolved }
              claimAlternatives :=
                claimAlternativesOf (keptReconstructed canon input.policy semantic pairs) semantic
              argIds := keptIds
              authoredObligations := authoredObligationsOf input.program
              openQuestions := openQuestionsOf (keptReconstructed canon input.policy semantic pairs)
              resolvedAttacks := resolved
              semanticProgram := semantic }
          assembled := by
            simp only [assemble, hp, hv, hc, hi, hg, hr, dif_pos hids, ha, hs, hguard]
            rfl
          audit := fun _ => auditAfterAssembly canon input semantic pairs declaredResolved
          audit_eq := by
            cases hraw : rawAttacksOfResolved (surfaceAttacksOf semantic) declaredResolved <;>
              simp [elaborateWithAudit, auditAfterAssembly, hp, hv, hc, hi, hg, hr, ha,
                hraw, hs, Lara.Evidence.except_bind_ok, Lara.Evidence.except_bind_error] <;> rfl }
  else .error (.duplicateArgId ⟨""⟩)

private theorem assembleRetainingAudit_erasure (env : Env canon) (input : Input) :
    (assembleRetainingAudit env input).map (·.output) = assemble env input := by
  unfold assembleRetainingAudit assemble
  repeat' (first
    | (simp_all [Except.map]; done)
    | split)

/-- Typed core rejection is retained before the legacy source boundary erases
it to `structural unsupported`. -/
inductive SourceDiagnostic where
  | source : SourceError → SourceDiagnostic
  | evidence : Evidence.AdmissionError → SourceDiagnostic
  | core : Check.Unit.UnitError → SourceDiagnostic
  deriving DecidableEq

def SourceDiagnostic.erase : SourceDiagnostic → Sum SourceError Evidence.AdmissionError
  | .source error => .inl error
  | .evidence error => .inr error
  | .core _ => .inl (.structural .unsupported)

/-- The exact accepted source result, with the audit from the same assembly. -/
structure SourceWithEvidenceAudit (env : Env canonNum) (input : Input)
    (snapshot : Evidence.Snapshot) (manifest : List Evidence.ObjectMeta) where
  audit : ElaboratedWithAudit canonNum
  judgments : List Evidence.Judgment
  source_eq : sourceWithEvidence env input snapshot manifest Evidence.extract =
    .ok (audit.output, judgments)
  audit_eq : elaborateWithAudit env input = .ok audit
  checkedUnit : Lara.Unit.CheckedUnit canonNum audit.output.gamma
    (Lara.Support.certOkOf env.registry)
  checkedUnit_eq : Check.Unit.checkUnit audit.output.gamma env.registry
    audit.output.ground audit.output.unit = .ok checkedUnit

/-- The output projection is the audited output, not a separately elaborated
or reconstructed carrier. -/
def SourceWithEvidenceAudit.output
    (result : SourceWithEvidenceAudit env input snapshot manifest) : Elaborated canonNum :=
  result.audit.output

theorem SourceWithEvidenceAudit.output_eq
    (result : SourceWithEvidenceAudit env input snapshot manifest) :
    result.output = result.audit.output := rfl

private theorem AssemblyWithAudit.audit_output {canon : String → String}
    {env : Env canon} {input : Input}
    (assembled : AssemblyWithAudit env input)
    {checked : Lara.Unit.CheckedUnit canon assembled.output.gamma
      (Lara.Support.certOkOf env.registry)}
    (core : Check.Unit.checkUnit assembled.output.gamma env.registry
      assembled.output.ground assembled.output.unit = .ok checked) :
    (assembled.audit ()).map (·.output) = .ok assembled.output := by
  rw [← assembled.audit_eq]
  have checkedSource : check env input = .ok assembled.output := by
    rw [check_eq_of_assemble env input assembled.output assembled.assembled]
    simp [core]
  exact elaborate_complete env input assembled.output
    (check_sound env input assembled.output checkedSource)

/-- The proof-retaining diagnostic door has the source priority: syntax,
ordinary assembly and group policy, all semantic evidence, then typed core
checking. Only the already assembled audit suffix is evaluated after acceptance. -/
def sourceWithEvidenceAudit (env : Env canonNum) (input : Input)
    (snapshot : Evidence.Snapshot) (manifest : List Evidence.ObjectMeta) :
    Except SourceDiagnostic (SourceWithEvidenceAudit env input snapshot manifest) :=
  if hn : input.policy.evidenceCheckers.Nodup then
    match assembleRetainingAudit env input with
    | .error error => .error (.source (.structural error))
    | .ok assembled =>
      match hg : checkSourceGroups canonNum input.policy assembled.output.semanticProgram with
      | .error error => .error (.source error)
      | .ok _ =>
        match he : Evidence.admit snapshot input.policy.evidenceCheckers manifest Evidence.extract
            (leafRecords assembled.output.semanticProgram) with
        | .error error => .error (.evidence error)
        | .ok judgments =>
          match hc : Check.Unit.checkUnit assembled.output.gamma env.registry
              assembled.output.ground assembled.output.unit with
          | .error error => .error (.core error)
          | .ok checked =>
            match hu : assembled.audit () with
            | .error error => False.elim (by
                have impossible := assembled.audit_output hc
                simp [hu, Except.map] at impossible)
            | .ok audit =>
              have outputEq : audit.output = assembled.output := by
                have same := assembled.audit_output hc
                simpa [hu, Except.map] using same
              let retained : { unit : Lara.Unit.CheckedUnit canonNum audit.output.gamma
                  (Lara.Support.certOkOf env.registry) //
                  Check.Unit.checkUnit audit.output.gamma env.registry audit.output.ground
                    audit.output.unit = .ok unit } :=
                outputEq.symm ▸ ⟨checked, hc⟩
              .ok
                { audit := audit
                  judgments := judgments
                  audit_eq := assembled.audit_eq.trans hu
                  source_eq := by
                    simp [sourceWithEvidence, hn, assembled.assembled, hg, he,
                      finishAssembled, hc, Except.mapError, outputEq,
                      Lara.Evidence.except_bind_ok]
                  checkedUnit := retained.val
                  checkedUnit_eq := retained.property }
  else .error (.source .evidenceSyntax)

/-- Erasing only diagnostics and the retained proofs recovers the existing
source entry point exactly, including every rejection priority. -/
theorem sourceWithEvidenceAudit_erasure (env : Env canonNum) (input : Input)
    (snapshot : Evidence.Snapshot) (manifest : List Evidence.ObjectMeta) :
    ((sourceWithEvidenceAudit env input snapshot manifest).map
      (fun result => (result.output, result.judgments))).mapError SourceDiagnostic.erase =
      sourceWithEvidence env input snapshot manifest Evidence.extract := by
  unfold sourceWithEvidenceAudit
  split
  next hn =>
    split
    next error ha =>
      have assembledError : assemble env input = .error error := by
        have erased := assembleRetainingAudit_erasure env input
        simpa [ha, Except.map] using erased.symm
      simp [hn, sourceWithEvidence, assembledError,
        Except.map, Except.mapError, SourceDiagnostic.erase, Lara.Evidence.except_bind_error]
    next assembled ha =>
      split
      next error hg =>
        simp [hn, hg, sourceWithEvidence, assembled.assembled,
          Except.map, Except.mapError, SourceDiagnostic.erase,
          Lara.Evidence.except_bind_ok, Lara.Evidence.except_bind_error]
      next ignored hg =>
        split
        next error he =>
          simp [hn, hg, he, sourceWithEvidence, assembled.assembled,
            Except.map, Except.mapError, SourceDiagnostic.erase,
            Lara.Evidence.except_bind_ok, Lara.Evidence.except_bind_error]
        next judgments he =>
          split
          next error hc =>
            simp [hn, hg, he, hc, sourceWithEvidence,
              assembled.assembled, finishAssembled, Except.map, Except.mapError,
              SourceDiagnostic.erase, Lara.Evidence.except_bind_ok, Lara.Evidence.except_bind_error]
          next checked hc =>
            split
            next error hu =>
              have impossible := assembled.audit_output hc
              simp [hu, Except.map] at impossible
            next audit hu =>
              have outputEq : audit.output = assembled.output := by
                have same := assembled.audit_output hc
                simpa [hu, Except.map] using same
              simp [hn, hg, he, hc, sourceWithEvidence,
                assembled.assembled, finishAssembled, Except.map, Except.mapError,
                SourceWithEvidenceAudit.output, outputEq, Lara.Evidence.except_bind_ok]
  next hn =>
    simp [hn, sourceWithEvidence, Except.map, Except.mapError, SourceDiagnostic.erase]

theorem SourceWithEvidenceAudit.admitted
    (result : SourceWithEvidenceAudit env input snapshot manifest) :
    Evidence.Admitted snapshot input.policy.evidenceCheckers manifest Evidence.extract
      (leafRecords result.audit.declared.semanticProgram) result.judgments := by
  have admitted := sourceWithEvidence_semantic result.source_eq
  have semantic := (elaborateWithAudit_alignment result.audit_eq).outputSemanticProgram
  simpa [semantic] using admitted

theorem SourceWithEvidenceAudit.checked
    (result : SourceWithEvidenceAudit env input snapshot manifest) :
    check env input = .ok result.output :=
  (sourceWithEvidence_core_and_semantic result.source_eq).1

end Lara.Surface
