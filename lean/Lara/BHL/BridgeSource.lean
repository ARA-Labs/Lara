import Lara.Update
import Lara.Evidence.Composition

namespace Lara.BHL

universe u v

open Lara Lara.Support

deriving instance DecidableEq for Lara.Update.SourceState
deriving instance DecidableEq for Except

/-- All decidable evidence input material, including presentation-only fields. -/
structure EvidenceMaterial where
  input : Surface.Input
  snapshot : Evidence.Snapshot
  manifest : List Evidence.ObjectMeta
  ground : List Atom
  deriving DecidableEq

/-- Alignment is on the declared source, not merely equal retained envelopes.
The two ground lists are retained separately: auxiliary signature atoms need
not coincide, whereas leaf contexts and checked argument/attack carriers do. -/
structure SourceAlignment {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state)
    (env : Surface.Env canonNum) (input : Surface.Input)
    (audit : Surface.ElaboratedWithAudit canonNum)
    (output : Surface.Elaborated canonNum) : Prop where
  output_exact : audit.output = output
  sigma : state.sigma = input.policy.sigma
  policy : state.policy = Surface.toCorePolicy input.policy
  table : state.table = Surface.admissionRows input.policy
  metas : state.metas = Surface.admissionLeafMetas audit.declared.semanticProgram
  leaves : state.leaves = Surface.admissionLeafTable audit.declared.semanticProgram
  args : state.argsRaw = Surface.admissionArgs audit.declared.pairs
  attacks : state.rawAtts = audit.declared.rawAttacks
  groups : state.groups = Surface.admissionGroups audit.declared.semanticProgram
  resolved : run.declared.resolved = audit.declared.resolvedAttacks
  checkedLeaves : run.admission.prune.checkedLeaves = audit.declared.admission.prune.checkedLeaves
  gamma : Admission.buildGamma run.admission.prune.checkedLeaves = output.gamma
  checkedSigma : run.checked.sigma = output.unit.sigma
  checkedPolicy : run.checked.policy = output.unit.policy
  unitArgs : run.admission.prune.keptArgs.map (·.2) = output.unit.args
  unitAttacks : run.admission.prune.keptAttacks = output.unit.atts
  /-- Explicit carrier transport across the two actual check contexts. -/
  checkedArgs : run.checked.program.args = Check.completeArgs output.unit.policy.ruleLookup
    output.gamma env.registry output.unit.args
  checkedHoles : run.checked.program.holes = Check.holeArgs output.unit.policy.ruleLookup
    output.gamma env.registry output.unit.args
  checkedAttacks : run.checked.program.atts =
    Check.liveAttacks run.checked.program.args output.unit.atts

/-- Function-valued evidence registries are bound by equality proofs. -/
structure CertifiedSource {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (expectedRegistry : Evidence.Registry)
    (run : Update.AcceptedRun reg state) (material : EvidenceMaterial) where
  env : Surface.Env canonNum
  actualRegistry : Evidence.Registry
  registry_exact : actualRegistry = expectedRegistry
  output : Surface.Elaborated canonNum
  judgments : List Evidence.Judgment
  audit : Surface.ElaboratedWithAudit canonNum
  source_ok : Surface.sourceWithEvidence env material.input material.snapshot
    material.manifest actualRegistry = .ok (output, judgments)
  audit_ok : Surface.elaborateWithAudit env material.input = .ok audit
  alignment : SourceAlignment run env material.input audit output
  ground_exact : material.ground = output.ground

/-- Ordinary declarations cannot silently omit certified evidence success. -/
inductive SourceEvidence {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (registry : Evidence.Registry)
    (run : Update.AcceptedRun reg state) : Option EvidenceMaterial → Type 1 where
  | ordinary (uncertified : ∀ m ∈ state.metas, m.kind ≠ .certified) :
      SourceEvidence registry run none
  | certified {material : EvidenceMaterial} (source : CertifiedSource registry run material) :
      SourceEvidence registry run (some material)

namespace CertifiedSource

theorem exact_source {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} {registry : Evidence.Registry}
    {run : Update.AcceptedRun reg state} {material : EvidenceMaterial}
    (source : CertifiedSource registry run material) :
    Surface.sourceWithEvidence source.env material.input material.snapshot material.manifest
      registry = .ok (source.output, source.judgments) := by
  have registryEquality := congrArg
    (fun current => Surface.sourceWithEvidence source.env material.input material.snapshot
      material.manifest current) source.registry_exact
  exact registryEquality.symm.trans source.source_ok

theorem admitted {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} {registry : Evidence.Registry}
    {run : Update.AcceptedRun reg state} {material : EvidenceMaterial}
    (source : CertifiedSource registry run material) :
    Evidence.Admitted material.snapshot material.input.policy.evidenceCheckers
      material.manifest registry (Surface.leafRecords source.output.semanticProgram)
      source.judgments :=
  Surface.sourceWithEvidence_semantic source.exact_source

theorem core {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} {registry : Evidence.Registry}
    {run : Update.AcceptedRun reg state} {material : EvidenceMaterial}
    (source : CertifiedSource registry run material) :
    Surface.check source.env material.input = .ok source.output :=
  (Surface.sourceWithEvidence_core_and_semantic source.exact_source).1

theorem alignment_from_audit {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} {registry : Evidence.Registry}
    {run : Update.AcceptedRun reg state} {material : EvidenceMaterial}
    (source : CertifiedSource registry run material) :
    Surface.ElaborationAlignment source.env material.input source.audit :=
  Surface.elaborateWithAudit_alignment source.audit_ok

theorem certified_witness {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} {registry : Evidence.Registry}
    {run : Update.AcceptedRun reg state} {material : EvidenceMaterial}
    (source : CertifiedSource registry run material) {leaf : Presentation.Leaf}
    (member : leaf ∈ Surface.leafRecords source.output.semanticProgram)
    (certified : leaf.kind = .certified) :
    ∃ request, Evidence.RequestBound material.input.policy.evidenceCheckers material.manifest
      leaf request ∧ ∃ judgment ∈ source.judgments,
      judgment.leaf = leaf.id.val ∧ judgment.request = request ∧
      ∃ result, Evidence.run material.snapshot registry request = .ok result ∧
        judgment.normalized = nf canonNum leaf.prop :=
  Evidence.package_same_source_witness source.exact_source member certified

theorem certified_dependencies {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} {registry : Evidence.Registry}
    {run : Update.AcceptedRun reg state} {material : EvidenceMaterial}
    (source : CertifiedSource registry run material) {leaf : Presentation.Leaf}
    (member : leaf ∈ Surface.leafRecords source.output.semanticProgram)
    (certified : leaf.kind = .certified) :
    ∃ request, Evidence.RequestBound material.input.policy.evidenceCheckers material.manifest
      leaf request ∧ ∃ judgment ∈ source.judgments,
      judgment.leaf = leaf.id.val ∧ judgment.request = request ∧
      ∃ result, Evidence.run material.snapshot registry request = .ok result ∧
        judgment.dependencies = result.dependencies ∧
        judgment.normalized = nf canonNum leaf.prop ∧
        nf canonNum result.proposition = nf canonNum leaf.prop ∧
        result.dependencies.map (·.id) = Evidence.requestObjects request ∧
        ∀ metadata ∈ result.dependencies, ∃ id ∈ Evidence.requestObjects request,
          ∃ object, Evidence.lookup material.snapshot id = .ok object ∧
            object.metadata = metadata :=
  Evidence.all_declared_certified_witness source.admitted member certified

end CertifiedSource

/-- The full declared source of an audit, with its actual surface ground. -/
def sourceStateOfAudit (input : Surface.Input) (audit : Surface.ElaboratedWithAudit canonNum) :
    Update.SourceState :=
  { sigma := input.policy.sigma
    policy := Surface.toCorePolicy input.policy
    table := Surface.admissionRows input.policy
    metas := Surface.admissionLeafMetas audit.declared.semanticProgram
    leaves := Surface.admissionLeafTable audit.declared.semanticProgram
    argsRaw := Surface.admissionArgs audit.declared.pairs
    rawAtts := audit.declared.rawAttacks
    groups := Surface.admissionGroups audit.declared.semanticProgram
    ground := audit.output.ground }

def auditCoreResult (env : Surface.Env canonNum) (input : Surface.Input)
    (audit : Surface.ElaboratedWithAudit canonNum) :=
  Check.Unit.checkUnit (Admission.buildGamma audit.declared.admission.prune.checkedLeaves)
    env.registry audit.output.ground
    { sigma := input.policy.sigma
      policy := Surface.toCorePolicy input.policy
      args := audit.declared.admission.prune.keptArgs.map (·.2)
      atts := audit.declared.admission.prune.keptAttacks }

theorem auditCoreResult_accepted {env : Surface.Env canonNum} {input snapshot manifest registry output judgments}
    (audit : Surface.ElaboratedWithAudit canonNum)
    (source : Surface.sourceWithEvidence env input snapshot manifest registry = .ok (output, judgments))
    (audited : Surface.elaborateWithAudit env input = .ok audit)
    (sameOutput : audit.output = output) :
    (auditCoreResult env input audit).isOk = true := by
  have alignment := Surface.elaborateWithAudit_alignment audited
  obtain ⟨checked, _, core, _⟩ := (Evidence.package_source_preserves source).2
  unfold auditCoreResult
  rw [← alignment.outputGamma, ← alignment.outputUnit, sameOutput, core]
  rfl

@[macro_inline]
def auditChecked (env : Surface.Env canonNum) (input : Surface.Input)
    (audit : Surface.ElaboratedWithAudit canonNum)
    (accepted : (auditCoreResult env input audit).isOk = true) :=
  (auditCoreResult env input audit).toOption.get (by
    cases equation : auditCoreResult env input audit with
    | error error => rw [equation] at accepted; contradiction
    | ok checked => exact rfl)

theorem except_toOption_get_exact {ε : Type u} {α : Type v}
    (result : Except ε α) (present : result.toOption.isSome = true) :
    result = .ok (result.toOption.get present) := by
  cases result with
  | error error => exact False.elim (Bool.noConfusion present)
  | ok value => rfl

theorem auditChecked_exact (env : Surface.Env canonNum) (input : Surface.Input)
    (audit : Surface.ElaboratedWithAudit canonNum)
    (accepted : (auditCoreResult env input audit).isOk = true) :
    auditCoreResult env input audit = .ok (auditChecked env input audit accepted) := by
  exact except_toOption_get_exact (auditCoreResult env input audit) (by
    cases equation : auditCoreResult env input audit with
    | error error => rw [equation] at accepted; contradiction
    | ok checked => rfl)

/-- No new admission/checking pipeline: the run retains the audit's actual
admission and the actual checker result, justified by sourceWithEvidence. -/
@[macro_inline]
def acceptedRunOfSource {env : Surface.Env canonNum} {input snapshot manifest registry output judgments}
    (audit : Surface.ElaboratedWithAudit canonNum)
    (source : Surface.sourceWithEvidence env input snapshot manifest registry = .ok (output, judgments))
    (audited : Surface.elaborateWithAudit env input = .ok audit)
    (sameOutput : audit.output = output) :
    Update.AcceptedRun env.registry (sourceStateOfAudit input audit) :=
  let alignment := Surface.elaborateWithAudit_alignment audited
  let accepted := auditCoreResult_accepted audit source audited sameOutput
  { declared :=
      { resolved := audit.declared.resolvedAttacks
        resolve_eq := alignment.rawResolution
        ids_nodup := alignment.idsNodup }
    admission := audit.declared.admission
    checked := auditChecked env input audit accepted
    admission_ok := alignment.admissionEvaluation
    check_ok := auditChecked_exact env input audit accepted }

theorem acceptedRunOfSource_alignment
    {env : Surface.Env canonNum} {input snapshot manifest registry output judgments}
    (audit : Surface.ElaboratedWithAudit canonNum)
    (source : Surface.sourceWithEvidence env input snapshot manifest registry = .ok (output, judgments))
    (audited : Surface.elaborateWithAudit env input = .ok audit)
    (sameOutput : audit.output = output) :
    SourceAlignment (acceptedRunOfSource audit source audited sameOutput) env input audit output := by
  have alignment := Surface.elaborateWithAudit_alignment audited
  have checked := Check.Unit.checkUnit_sound
    (acceptedRunOfSource audit source audited sameOutput).check_ok
  let unit : Lara.Unit :=
    { sigma := input.policy.sigma
      policy := Surface.toCorePolicy input.policy
      args := audit.declared.admission.prune.keptArgs.map (·.2)
      atts := audit.declared.admission.prune.keptAttacks }
  have outputGamma : output.gamma =
      Admission.buildGamma audit.declared.admission.prune.checkedLeaves :=
    (congrArg Surface.Elaborated.gamma sameOutput).symm.trans alignment.outputGamma
  have outputUnit : output.unit = unit :=
    (congrArg Surface.Elaborated.unit sameOutput).symm.trans alignment.outputUnit
  refine
    { output_exact := sameOutput
      sigma := rfl, policy := rfl, table := rfl, metas := rfl, leaves := rfl
      args := rfl, attacks := rfl, groups := rfl, resolved := rfl, checkedLeaves := rfl
      gamma := ?_, checkedSigma := ?_, checkedPolicy := ?_
      unitArgs := ?_, unitAttacks := ?_, checkedArgs := ?_
      checkedHoles := ?_, checkedAttacks := ?_ }
  · exact outputGamma.symm
  · exact checked.sigma_eq.trans (congrArg Lara.Unit.sigma outputUnit).symm
  · exact checked.policy_eq.trans (congrArg Lara.Unit.policy outputUnit).symm
  · exact (congrArg Lara.Unit.args outputUnit).symm
  · exact (congrArg Lara.Unit.atts outputUnit).symm
  · refine checked.args_eq.trans ?_
    change Check.completeArgs unit.policy.ruleLookup
      (Admission.buildGamma audit.declared.admission.prune.checkedLeaves) env.registry unit.args =
      Check.completeArgs output.unit.policy.ruleLookup output.gamma env.registry output.unit.args
    rw [outputUnit, outputGamma]
  · refine checked.holes_eq.trans ?_
    change Check.holeArgs unit.policy.ruleLookup
      (Admission.buildGamma audit.declared.admission.prune.checkedLeaves) env.registry unit.args =
      Check.holeArgs output.unit.policy.ruleLookup output.gamma env.registry output.unit.args
    rw [outputUnit, outputGamma]
  · exact checked.atts_eq.trans
      (congrArg (Check.liveAttacks
        (acceptedRunOfSource audit source audited sameOutput).checked.program.args)
        (congrArg Lara.Unit.atts outputUnit).symm)

@[macro_inline]
def certifiedSourceOfSource {env : Surface.Env canonNum} {input snapshot manifest registry output judgments}
    (audit : Surface.ElaboratedWithAudit canonNum)
    (source : Surface.sourceWithEvidence env input snapshot manifest registry = .ok (output, judgments))
    (audited : Surface.elaborateWithAudit env input = .ok audit)
    (sameOutput : audit.output = output) :
    CertifiedSource registry (acceptedRunOfSource audit source audited sameOutput)
      ⟨input, snapshot, manifest, output.ground⟩ :=
  { env := env, actualRegistry := registry, registry_exact := rfl
    output := output, judgments := judgments, audit := audit
    source_ok := source, audit_ok := audited
    alignment := acceptedRunOfSource_alignment audit source audited sameOutput
    ground_exact := rfl }

end Lara.BHL
