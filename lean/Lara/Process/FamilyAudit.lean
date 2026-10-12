import Lara.Process.SourceModel

namespace Lara.Process.Source

structure CheckedFamily (family : Family.FamilySpec) (config : AuditConfig)
    (completions : List Family.Completion) where
  snapshots : List Snapshot
  snapshots_eq : snapshots = completions.map (takeSnapshot family)
  context : ModelContext
  context_eq : context = modelContext family.base config (familyCarrier snapshots config)
  rows : List (Row context)
  rows_eq : rows = snapshots.map (prepareRow context)

def checkFamily (family : Family.FamilySpec) (config : AuditConfig)
    (completions : List Family.Completion) : CheckedFamily family config completions :=
  let snapshots := completions.map (takeSnapshot family)
  let context := modelContext family.base config (familyCarrier snapshots config)
  ⟨snapshots, rfl, context, rfl, snapshots.map (prepareRow context), rfl⟩

def pullbackModel {H X : Type} (model : WarrantModel H ClaimId WitnessId) (f : X → H) :
    WarrantModel X ClaimId WitnessId where
  af := fun x => model.af (f x)
  kind := fun x => model.kind (f x)
  argOf := model.argOf
  concludes := fun x => model.concludes (f x)
  probed := fun x => model.probed (f x)
  achieved := fun x => model.achieved (f x)
  artifact := fun x => model.artifact (f x)
  truth := fun x => model.truth (f x)

theorem warranted_pullback {H X : Type} (model : WarrantModel H ClaimId WitnessId)
    (f : X → H) (profile : Profile Empty) (x : X) (claim : ClaimId) (witness : WitnessId) :
    Warranted (pullbackModel model f) profile x claim witness ↔
      Warranted model profile (f x) claim witness := Iff.rfl

def completionModel (context : ModelContext) (family : Family.FamilySpec)
    (truth : Family.Completion → ClaimId → Prop) : WarrantModel Family.Completion ClaimId WitnessId :=
  pullbackModel (rowModel context (fun row => truth row.snapshot.completion))
    (fun completion => prepareRow context (takeSnapshot family completion))

def auditRows (context : ModelContext) (problem : Universe.Problem) (rows : List (Row context))
    (profile : Profile Empty) (claim : ClaimId) (witness : WitnessId) : Bool :=
  (Universe.admittedCoverage problem).all profile.acceptsCoverage &&
    !rows.isEmpty && rows.all (fun row => warranted context row profile claim witness)

def audit {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion} (checked : CheckedFamily family config completions)
    (profile : Profile Empty) (claim : ClaimId) (witness : WitnessId) : Bool :=
  auditRows checked.context family.problem checked.rows profile claim witness

def ProductAuditHolds (model : WarrantModel Family.Completion ClaimId WitnessId)
    (profile : Profile Empty) (problem : Universe.Problem) (completions : List Family.Completion)
    (claim : ClaimId) (witness : WitnessId) : Prop :=
  (∀ coverage ∈ Universe.admittedCoverage problem, profile.acceptsCoverage coverage = true) ∧
    ArgumentEntitledBy (· ∈ completions) (fun completion witness =>
      Warranted model profile completion claim witness) witness

theorem auditRows_iff (context : ModelContext) (problem : Universe.Problem)
    (rows : List (Row context)) (profile : Profile Empty) (claim : ClaimId) (witness : WitnessId)
    (truth : Row context → ClaimId → Prop) :
    auditRows context problem rows profile claim witness = true ↔
      (∀ coverage ∈ Universe.admittedCoverage problem, profile.acceptsCoverage coverage = true) ∧
        rows ≠ [] ∧ ∀ row ∈ rows, Warranted (rowModel context truth) profile row claim witness := by
  simp [auditRows, warranted, and_assoc]
  intro _ _
  rfl

theorem audit_iff {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion} (checked : CheckedFamily family config completions)
    (profile : Profile Empty) (claim : ClaimId) (witness : WitnessId)
    (truth : Family.Completion → ClaimId → Prop) :
    audit checked profile claim witness = true ↔
      ProductAuditHolds (completionModel checked.context family truth)
        profile family.problem completions claim witness := by
  rw [audit, auditRows_iff checked.context family.problem checked.rows profile claim witness
    (fun row => truth row.snapshot.completion)]
  rw [checked.rows_eq, checked.snapshots_eq]
  simp only [ProductAuditHolds, ArgumentEntitledBy, List.forall_mem_map]
  constructor
  · rintro ⟨coverage, nonempty, all⟩
    obtain ⟨row, member⟩ := List.exists_mem_of_ne_nil _ nonempty
    obtain ⟨snapshot, member, _⟩ := List.mem_map.mp member
    obtain ⟨completion, member, _⟩ := List.mem_map.mp member
    exact ⟨coverage, ⟨completion, member⟩, all⟩
  · rintro ⟨coverage, ⟨completion, member⟩, all⟩
    exact ⟨coverage, List.ne_nil_of_mem
      (List.mem_map_of_mem (f := prepareRow checked.context)
        (List.mem_map_of_mem (f := takeSnapshot family) member)), all⟩

theorem audit_rejection_fails {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion} (checked : CheckedFamily family config completions)
    (profile : Profile Empty) (claim : ClaimId) (witness : WitnessId)
    (row : Row checked.context) (member : row ∈ checked.rows)
    (error : SourceRejection) (rejected : row.view = .error error) :
    audit checked profile claim witness = false := by
  apply Bool.eq_false_iff.mpr
  intro positive
  have all := (auditRows_iff checked.context family.problem checked.rows profile claim witness
    (fun _ _ => False)).mp positive |>.2.2
  have failed := rejected_not_warranted checked.context row profile claim witness error rejected
  have passed := (warranted_iff checked.context row profile claim witness (fun _ _ => False)).mpr
    (all row member)
  rw [failed] at passed
  contradiction

theorem audit_empty_fails {family : Family.FamilySpec} {config : AuditConfig}
    (checked : CheckedFamily family config []) (profile : Profile Empty)
    (claim : ClaimId) (witness : WitnessId) : audit checked profile claim witness = false := by
  simp [audit, auditRows, checked.rows_eq, checked.snapshots_eq]

theorem checkedFamily_carrier_covers {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion} (checked : CheckedFamily family config completions)
    (row : Row checked.context) (member : row ∈ checked.rows)
    (observation : AcceptedObservation row.snapshot.input)
    (accepted : row.snapshot.outcome = .ok observation)
    (name : Presentation.ArgId) (named : name ∈ Coordinates.names observation.run) :
    name ∈ checked.context.carrier := by
  have names : row.snapshot.names = Coordinates.names observation.run := by
    simpa [accepted, outcomeNames] using row.snapshot.names_eq
  rw [checked.rows_eq] at member
  obtain ⟨snapshot, snapshotMember, rowEq⟩ := List.mem_map.mp member
  have same : snapshot = row.snapshot := congrArg Row.snapshot rowEq
  have rowNamed : name ∈ row.snapshot.names := names.symm ▸ named
  have snapshotNamed : name ∈ snapshot.names :=
    (congrArg Snapshot.names same).symm ▸ rowNamed
  have carrier := familyCarrier_covers (config := config) snapshotMember snapshotNamed
  simpa only [checked.context_eq, modelContext] using carrier

theorem no_slots_audit_iff (model : WarrantModel Family.Completion ClaimId WitnessId)
    (profile : Profile Empty) (problem : Universe.Problem) (base : SourceInput)
    (claim : ClaimId) (witness : WitnessId) :
    ProductAuditHolds model profile problem (Family.referenceFamily ⟨problem, base, []⟩) claim witness ↔
      Universe.AuditHolds (pullbackModel model (fun history => Family.Completion.mk history []))
        profile problem claim witness := by
  rw [Family.referenceFamily_no_slots]
  simp only [ProductAuditHolds, Universe.AuditHolds, ArgumentEntitledBy,
    List.forall_mem_map, warranted_pullback]
  constructor
  · rintro ⟨coverage, ⟨completion, member⟩, all⟩
    obtain ⟨history, member, _⟩ := List.mem_map.mp member
    exact ⟨coverage, ⟨history, member⟩, all⟩
  · rintro ⟨coverage, ⟨history, member⟩, all⟩
    exact ⟨coverage, ⟨⟨history, []⟩, List.mem_map_of_mem member⟩, all⟩

theorem checked_no_slots_audit_iff (problem : Universe.Problem) (base : SourceInput)
    (config : AuditConfig)
    (checked : CheckedFamily ⟨problem, base, []⟩ config (Family.referenceFamily ⟨problem, base, []⟩))
    (profile : Profile Empty) (claim : ClaimId) (witness : WitnessId)
    (truth : Family.Completion → ClaimId → Prop) :
    audit checked profile claim witness = true ↔
      Universe.AuditHolds
        (pullbackModel (completionModel checked.context ⟨problem, base, []⟩ truth)
          (fun history => Family.Completion.mk history [])) profile problem claim witness :=
  (audit_iff checked profile claim witness truth).trans
    (no_slots_audit_iff _ profile problem base claim witness)

end Lara.Process.Source
