import Lara.Process.SourceAuditAssociation
import Lara.Process.SourceLedger
import Lara.Process.SourceKinds

namespace Lara.Process.Source

inductive GuaranteeBinding where
  | conditional : GuaranteeClass → ℚ → GuaranteeBinding
  | ledger : LedgerBinding → GuaranteeBinding
  deriving DecidableEq

inductive GuaranteeFault where
  | invalidConditionalLevel
  | ledger : LedgerFault → GuaranteeFault
  deriving DecidableEq

def GuaranteeHolds (history : ProcessHistory) : GuaranteeBinding → GuaranteeClass × ℚ → Prop
  | .conditional kind level, attained => attained = (kind, level) ∧ 0 ≤ level ∧ level ≤ 1
  | .ledger binding, attained => attained.1 = .fwer ∧ LedgerValid history binding attained.2

structure GuaranteeCertificate (history : ProcessHistory) (binding : GuaranteeBinding) where
  attained : GuaranteeClass × ℚ
  valid : GuaranteeHolds history binding attained

def checkGuarantee (history : ProcessHistory) :
    (binding : GuaranteeBinding) → Except GuaranteeFault (GuaranteeCertificate history binding)
  | .conditional kind level =>
    if lawful : 0 ≤ level ∧ level ≤ 1 then .ok ⟨(kind, level), rfl, lawful⟩
    else .error .invalidConditionalLevel
  | .ledger binding =>
    match checkLedger history binding with
    | .error error => .error (.ledger error)
    | .ok certificate => .ok ⟨(.fwer, certificate.level), rfl, certificate.sound⟩

theorem checkGuarantee_sound {history : ProcessHistory} {binding : GuaranteeBinding}
    {certificate : GuaranteeCertificate history binding}
    (_checked : checkGuarantee history binding = .ok certificate) :
    GuaranteeHolds history binding certificate.attained := certificate.valid

theorem checkGuarantee_complete {history : ProcessHistory} {binding : GuaranteeBinding}
    {attained : GuaranteeClass × ℚ} (valid : GuaranteeHolds history binding attained) :
    ∃ certificate, checkGuarantee history binding = .ok certificate ∧ certificate.attained = attained := by
  cases binding with
  | conditional kind level =>
    rcases valid with ⟨rfl, lawful⟩
    simp only [checkGuarantee, dif_pos lawful]
    exact ⟨_, rfl, rfl⟩
  | ledger binding =>
    obtain ⟨certificate, checked, level⟩ := checkLedger_complete valid.2
    simp only [checkGuarantee, checked]
    refine ⟨_, rfl, ?_⟩
    exact Prod.ext valid.1.symm level

structure WitnessSpec where
  witness : WitnessId
  claim : ClaimId
  source : SourceInput
  artifact : ArtifactSpec
  probed : List ErrorKind
  guarantee : GuaranteeBinding
  deriving DecidableEq

structure AuditConfig where
  claims : List ClaimBinding
  witnesses : List WitnessSpec
  kinds : List KindSpec
  assumptions : List CaptureAssumption
  deriving DecidableEq

def AuditConfig.WellFormed (config : AuditConfig) : Prop :=
  (config.claims.map ClaimBinding.claim).Nodup ∧
  (config.witnesses.map WitnessSpec.witness).Nodup ∧
  (config.kinds.map fun spec => (spec.source, spec.key)).Nodup ∧
  (config.assumptions.map CaptureAssumption.id).Nodup

def AuditConfig.wellFormed (config : AuditConfig) : Bool :=
  decide (config.claims.map ClaimBinding.claim).Nodup &&
  decide (config.witnesses.map WitnessSpec.witness).Nodup &&
  decide (config.kinds.map fun spec => (spec.source, spec.key)).Nodup &&
  decide (config.assumptions.map CaptureAssumption.id).Nodup

theorem AuditConfig.wellFormed_iff (config : AuditConfig) :
    config.wellFormed = true ↔ config.WellFormed := by
  simp [wellFormed, WellFormed, and_assoc]

/-- These are exactly the fidelity assumptions explicitly admitted by the reader.
The output reports them; their presence is not proof of physical observation. -/
def AuditConfig.admittedBases (config : AuditConfig) : List AdmissionBasis :=
  config.assumptions.map CaptureAssumption.basis

def WitnessSpec.conditional (spec : WitnessSpec) : Bool :=
  (match spec.guarantee with | .conditional .. => true | .ledger _ => false) ||
  match spec.artifact.interpretation with
  | .checkedMethod method => method.mode == .conditional
  | .declared _ => false

def AuditConfig.conditionalKeys (config : AuditConfig) (base : SourceInput) : List KindKey :=
  config.witnesses.filterMap fun spec =>
    if spec.source == base && spec.conditional then some (.argument spec.artifact.argument) else none

theorem AuditConfig.mem_conditionalKeys (config : AuditConfig) (base : SourceInput) (key : KindKey) :
    key ∈ config.conditionalKeys base ↔ ∃ spec ∈ config.witnesses,
      spec.source = base ∧ spec.conditional = true ∧ key = .argument spec.artifact.argument := by
  simp only [conditionalKeys, List.mem_filterMap]
  constructor
  · rintro ⟨spec, member, chosen⟩
    split at chosen
    · rename_i condition
      have conditions := Bool.and_eq_true_iff.mp condition
      exact ⟨spec, member, eq_of_beq conditions.1, conditions.2, (Option.some.inj chosen).symm⟩
    · cases chosen
  · rintro ⟨spec, member, source, conditional, rfl⟩
    exact ⟨spec, member, by simp [source, conditional]⟩

inductive WitnessFault where
  | missingClaim
  | missingWitness
  | ambiguousMetadata
  | wrongClaim
  | staleSource
  | artifact : ArtifactFault → WitnessFault
  | guarantee : GuaranteeFault → WitnessFault
  deriving DecidableEq

structure WitnessCertificate (base : SourceInput) {input : SourceInput}
    (observation : AcceptedObservation input) (history : ProcessHistory)
    (claim : ClaimBinding) (spec : WitnessSpec) where
  source_exact : spec.source = base
  claim_exact : spec.claim = claim.claim
  artifact : SourceArtifact observation claim spec.artifact
  guarantee : GuaranteeCertificate history spec.guarantee

def checkWitness (base : SourceInput) {input : SourceInput}
    (observation : AcceptedObservation input) (history : ProcessHistory)
    (claim : ClaimBinding) (spec : WitnessSpec) :
    Except WitnessFault (WitnessCertificate base observation history claim spec) :=
  if source : spec.source = base then
    if named : spec.claim = claim.claim then
      match checkArtifact observation claim spec.artifact with
      | .error error => .error (.artifact error)
      | .ok artifact =>
        match checkGuarantee history spec.guarantee with
        | .error error => .error (.guarantee error)
        | .ok guarantee => .ok ⟨source, named, artifact, guarantee⟩
    else .error .wrongClaim
  else .error .staleSource

structure WitnessFields where
  claim : ClaimId
  argument : Presentation.ArgId
  probed : List ErrorKind
  achieved : GuaranteeClass × ℚ
  deriving DecidableEq

def observeWitness (base : SourceInput) {input : SourceInput}
    (observation : AcceptedObservation input) (history : ProcessHistory)
    (claim : ClaimBinding) (spec : WitnessSpec) : Except WitnessFault WitnessFields :=
  (checkWitness base observation history claim spec).map fun certificate =>
    ⟨claim.claim, spec.artifact.argument, spec.probed, certificate.guarantee.attained⟩

theorem WitnessCertificate.source_claim_exact (base : SourceInput) {input : SourceInput}
    {observation : AcceptedObservation input} {history : ProcessHistory}
    {claim : ClaimBinding} {spec : WitnessSpec}
    (certificate : WitnessCertificate base observation history claim spec) :
    spec.source = base ∧ spec.claim = claim.claim ∧
      Surface.claimFormal? input.surface.program claim.declaration = some claim.query ∧
      Surface.claimFormal? observation.accepted.audit.declared.semanticProgram claim.declaration = some claim.query :=
  ⟨certificate.source_exact, certificate.claim_exact, certificate.artifact.association.inputClaim,
    certificate.artifact.association.semanticClaim⟩

theorem observeWitness_sound (base : SourceInput) {input : SourceInput}
    (observation : AcceptedObservation input) (history : ProcessHistory)
    (claim : ClaimBinding) (spec : WitnessSpec) (fields : WitnessFields)
    (observed : observeWitness base observation history claim spec = .ok fields) :
    ∃ certificate, checkWitness base observation history claim spec = .ok certificate ∧
      fields.claim = claim.claim ∧ fields.argument = spec.artifact.argument ∧
      fields.probed = spec.probed ∧ GuaranteeHolds history spec.guarantee fields.achieved := by
  unfold observeWitness at observed
  cases checked : checkWitness base observation history claim spec with
  | error error => simp [checked, Except.map] at observed
  | ok certificate =>
    simp only [checked, Except.map, Except.ok.injEq] at observed
    cases observed
    exact ⟨certificate, rfl, rfl, rfl, rfl, certificate.guarantee.valid⟩

def observeWitnesses (config : AuditConfig) (base : SourceInput) {input : SourceInput}
    (observation : AcceptedObservation input) (history : ProcessHistory) :
    List (WitnessId × Except WitnessFault WitnessFields) :=
  if config.wellFormed then
    config.witnesses.map fun spec =>
      (spec.witness, match config.claims.find? (fun claim => claim.claim == spec.claim) with
        | none => .error .missingClaim
        | some claim => observeWitness base observation history claim spec)
  else config.witnesses.map fun spec => (spec.witness, .error .ambiguousMetadata)

theorem observeWitnesses_ambiguous (config : AuditConfig) (base : SourceInput) {input : SourceInput}
    (observation : AcceptedObservation input) (history : ProcessHistory)
    (ambiguous : config.wellFormed = false)
    (row : WitnessId × Except WitnessFault WitnessFields)
    (member : row ∈ observeWitnesses config base observation history) :
    row.2 = .error .ambiguousMetadata := by
  simp only [observeWitnesses, ambiguous, Bool.false_eq_true, if_false, List.mem_map] at member
  obtain ⟨spec, _, rfl⟩ := member
  rfl

def ObservedWitness (config : AuditConfig) (base : SourceInput) {input : SourceInput}
    (observation : AcceptedObservation input) (history : ProcessHistory)
    (witness : WitnessId) (fields : WitnessFields) : Prop :=
  ∃ spec ∈ config.witnesses, ∃ claim ∈ config.claims, spec.witness = witness ∧
    ∃ certificate : WitnessCertificate base observation history claim spec,
      checkWitness base observation history claim spec = .ok certificate ∧
      fields = ⟨claim.claim, spec.artifact.argument, spec.probed, certificate.guarantee.attained⟩

theorem observeWitnesses_sound (config : AuditConfig) (base : SourceInput) {input : SourceInput}
    (observation : AcceptedObservation input) (history : ProcessHistory)
    (witness : WitnessId) (fields : WitnessFields)
    (member : (witness, .ok fields) ∈ observeWitnesses config base observation history) :
    ObservedWitness config base observation history witness fields := by
  unfold observeWitnesses at member
  split at member
  · obtain ⟨spec, declared, equal⟩ := List.mem_map.mp member
    have named : spec.witness = witness := congrArg Prod.fst equal
    cases found : config.claims.find? (fun claim => claim.claim == spec.claim) with
    | none => simp [found] at equal
    | some claim =>
      have success : observeWitness base observation history claim spec = .ok fields := by
        simpa [found] using congrArg Prod.snd equal
      refine ⟨spec, declared, claim, List.mem_of_find?_eq_some found, named, ?_⟩
      unfold observeWitness at success
      cases checked : checkWitness base observation history claim spec with
      | error error => simp [checked, Except.map] at success
      | ok certificate =>
        simp only [checked, Except.map, Except.ok.injEq] at success
        exact ⟨certificate, rfl, success.symm⟩
  · obtain ⟨spec, _, equal⟩ := List.mem_map.mp member
    cases (Prod.mk.inj equal).2

end Lara.Process.Source
