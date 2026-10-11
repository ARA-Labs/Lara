import Lara.Process.Family
import Lara.Process.SourceAudit
import Lara.Process.SourceProvenance
import Lara.Process.SourceKindTable

namespace Lara.Process.Source

def outcomeNames {input : SourceInput} : SourceOutcome input → List Presentation.ArgId
  | .error _ => []
  | .ok observation => Coordinates.names observation.run

/-- The source result and raw coordinates are computed once per completion. -/
structure Snapshot where
  completion : Family.Completion
  input : SourceInput
  outcome : SourceOutcome input
  outcome_eq : outcome = checkSource input
  names : List Presentation.ArgId
  names_eq : names = outcomeNames outcome

def takeSnapshot (family : Family.FamilySpec) (completion : Family.Completion) : Snapshot :=
  let input := Family.materialize family completion
  let outcome := checkSource input
  let names := outcomeNames outcome
  ⟨completion, input, outcome, rfl, names, rfl⟩

theorem takeSnapshot_materialized (family : Family.FamilySpec) (completion : Family.Completion) :
    (takeSnapshot family completion).input = Family.materialize family completion := rfl

/-- The declared claim bindings are pinned to the family's base source by design:
a claim that only a materialized fragment declares fails this gate, and the
materialized formal is independently checked by the witness artifact
association (`WitnessCertificate.source_claim_exact`), so this is a conservative
gate rather than a soundness premise. -/
def fixedClaims (base : SourceInput) (config : AuditConfig) : Bool :=
  config.claims.all fun claim =>
    Surface.claimFormal? base.surface.program claim.declaration == some claim.query

theorem fixedClaims_iff (base : SourceInput) (config : AuditConfig) :
    fixedClaims base config = true ↔ ∀ claim ∈ config.claims,
      Surface.claimFormal? base.surface.program claim.declaration = some claim.query := by
  simp [fixedClaims]

/-- One raw-name carrier for the entire family, including fixed submitted witnesses. -/
def familyCarrier (snapshots : List Snapshot) (config : AuditConfig) : List Presentation.ArgId :=
  ((snapshots.flatMap Snapshot.names) ++ config.witnesses.map (·.artifact.argument)).dedup

theorem familyCarrier_covers {snapshots : List Snapshot} {config : AuditConfig}
    {snapshot : Snapshot} (member : snapshot ∈ snapshots) {name : Presentation.ArgId}
    (named : name ∈ snapshot.names) : name ∈ familyCarrier snapshots config := by
  simp only [familyCarrier, List.mem_dedup, List.mem_append]
  exact Or.inl (List.mem_flatMap.mpr ⟨snapshot, member, named⟩)

structure ModelContext where
  base : SourceInput
  config : AuditConfig
  carrier : List Presentation.ArgId
  valid : Bool
  valid_eq : valid = (config.wellFormed && fixedClaims base config)
  witnessCoordinates : List (WitnessId × Grounded.Arg)
  coordinates_eq : witnessCoordinates = config.witnesses.map
    (fun spec => (spec.witness, carrier.idxOf spec.artifact.argument))

def modelContext (base : SourceInput) (config : AuditConfig)
    (carrier : List Presentation.ArgId) : ModelContext :=
  ⟨base, config, carrier, config.wellFormed && fixedClaims base config, rfl,
    config.witnesses.map (fun spec => (spec.witness, carrier.idxOf spec.artifact.argument)), rfl⟩

structure NodeGrade where
  argument : Presentation.ArgId
  keys : Except Provenance.Error (List KindKey)
  value : EvidenceKind × Bool
  deriving DecidableEq

def gradeNode (kinds : KindTable.Table) (provenance : Except Provenance.Error Provenance.Table)
    (argument : Presentation.ArgId) : NodeGrade :=
  let keys := provenance.bind fun table => Provenance.lookup table argument
  let value := match keys with
    | .error _ => (.hypothetical, false)
    | .ok keys => Provenance.scalar (KindTable.lookup kinds) keys
  ⟨argument, keys, value⟩

structure QueryFields where
  claim : ClaimId
  query : Atom
  status : Driver.PublicStatus
  supports : List Presentation.ArgId
  deriving DecidableEq

structure Prepared where
  graph : Grounded.AF
  provenance : Except Provenance.Error Provenance.Table
  kinds : List NodeGrade
  complete : Bool
  witnesses : List (WitnessId × Except WitnessFault WitnessFields)
  queries : List QueryFields

def gradeTable (context : ModelContext) (snapshot : Snapshot) : KindTable.Table :=
  KindTable.build context.base snapshot.completion.history context.config.kinds
    context.config.assumptions context.config.admittedBases
    (Family.selectedKeys snapshot.completion) (context.config.conditionalKeys context.base)

/-- No graph or status is attached to a rejected source. `Row.graph` (and hence
`rowModel.af`) is only meaningful after `Row.view` is known to be `.ok`; the
placeholder it returns for a rejected row is unreachable through the verdict,
which `rejected_not_warranted` pins. -/
def prepare (context : ModelContext) (snapshot : Snapshot) : Except SourceRejection Prepared :=
  match snapshot.outcome with
  | .error error => .error error
  | .ok observation =>
    let names := snapshot.names.toArray
    let coordinates := (snapshot.names.map context.carrier.idxOf).toArray
    let graph := liftGraph (Compile.checkedAF observation.run.checked.program)
      (fun node => coordinates[node]?.getD context.carrier.length)
    let provenance := Provenance.ofObservation observation
    let kinds := gradeTable context snapshot
    let grades := snapshot.names.map (gradeNode kinds provenance)
    .ok
      { graph
        provenance
        kinds := grades
        complete := context.valid && provenance.isOk && grades.all (·.value.2)
        witnesses := observeWitnesses context.config context.base observation snapshot.completion.history
        queries := context.config.claims.map fun claim =>
          ⟨claim.claim, claim.query, observation.publicStatus claim.query,
            (Consistency.claimSupportFor observation.run.checked claim.query).filterMap
              (fun node => names[node]?)⟩ }

structure Row (context : ModelContext) where
  snapshot : Snapshot
  view : Except SourceRejection Prepared
  view_eq : view = prepare context snapshot

def prepareRow (context : ModelContext) (snapshot : Snapshot) : Row context :=
  ⟨snapshot, prepare context snapshot, rfl⟩

def ModelContext.argOf (context : ModelContext) (witness : WitnessId) : Grounded.Arg :=
  ((context.witnessCoordinates.find? (fun entry => entry.1 == witness)).map Prod.snd).getD
    context.carrier.length

def Row.witness {context : ModelContext} (row : Row context) (witness : WitnessId) :
    Option WitnessFields :=
  match row.view with
  | .error _ => none
  | .ok view =>
    match view.witnesses.find? (fun entry => entry.1 == witness) with
    | none => none
    | some entry =>
      match entry.2 with
      | .ok fields => some fields
      | .error _ => none

def Row.graph {context : ModelContext} (row : Row context) : Grounded.AF :=
  match row.view with
  | .error _ => ⟨[], fun _ _ => false⟩
  | .ok view => view.graph

def Row.kind {context : ModelContext} (row : Row context) (argument : Grounded.Arg) : EvidenceKind :=
  match row.view, context.carrier[argument]? with
  | .ok view, some name =>
    ((view.kinds.find? (fun entry => entry.argument == name)).map (·.value.1)).getD .hypothetical
  | _, _ => .hypothetical

def Row.artifact {context : ModelContext} (row : Row context) (witness : WitnessId) : Bool :=
  match row.view with
  | .error _ => false
  | .ok view => view.complete && (row.witness witness).isSome

def Row.concludes {context : ModelContext} (row : Row context)
    (witness : WitnessId) (claim : ClaimId) : Bool :=
  match row.witness witness with
  | none => false
  | some fields => fields.claim == claim &&
      context.config.witnesses.any (fun spec => spec.witness == witness &&
        spec.artifact.argument == fields.argument)

/-- Truth is an independent interpretation parameter, not inferred from warrant.
Default fields at failed lookups are inert: artifact and conclusion checks fail. -/
def rowModel (context : ModelContext) (truth : Row context → ClaimId → Prop) :
    WarrantModel (Row context) ClaimId WitnessId where
  af := Row.graph
  kind := Row.kind
  argOf := context.argOf
  concludes := fun row witness claim => row.concludes witness claim = true
  probed := fun row witness => ((row.witness witness).map (·.probed.toFinset)).getD ∅
  achieved := fun row witness => ((row.witness witness).map (·.achieved)).getD (.fwer, 1)
  artifact := fun row witness => row.artifact witness = true
  truth := truth

instance (context : ModelContext) (truth : Row context → ClaimId → Prop)
    (row : Row context) (witness : WitnessId) :
    Decidable ((rowModel context truth).artifact row witness) := inferInstanceAs (Decidable (_ = true))

instance (context : ModelContext) (truth : Row context → ClaimId → Prop)
    (row : Row context) (witness : WitnessId) (claim : ClaimId) :
    Decidable ((rowModel context truth).concludes row witness claim) := inferInstanceAs (Decidable (_ = true))

def warranted (context : ModelContext) (row : Row context) (profile : Profile Empty)
    (claim : ClaimId) (witness : WitnessId) : Bool :=
  decide (Warranted (rowModel context (fun _ _ => False)) profile row claim witness)

theorem warranted_iff (context : ModelContext) (row : Row context) (profile : Profile Empty)
    (claim : ClaimId) (witness : WitnessId) (truth : Row context → ClaimId → Prop) :
    warranted context row profile claim witness = true ↔
      Warranted (rowModel context truth) profile row claim witness := by
  simp only [warranted, decide_eq_true_eq]
  rfl

theorem rejected_not_warranted (context : ModelContext) (row : Row context)
    (profile : Profile Empty) (claim : ClaimId) (witness : WitnessId)
    (error : SourceRejection) (rejected : row.view = .error error) :
    warranted context row profile claim witness = false := by
  simp [warranted, Warranted, rowModel, Row.artifact, rejected]

theorem incomplete_not_warranted (context : ModelContext) (row : Row context)
    (profile : Profile Empty) (claim : ClaimId) (witness : WitnessId)
    (view : Prepared) (accepted : row.view = .ok view) (incomplete : view.complete = false) :
    warranted context row profile claim witness = false := by
  simp [warranted, Warranted, rowModel, Row.artifact, accepted, incomplete]

theorem prepare_kind_names (context : ModelContext) (snapshot : Snapshot) (view : Prepared)
    (accepted : prepare context snapshot = .ok view) :
    view.kinds.map NodeGrade.argument = snapshot.names := by
  unfold prepare at accepted
  split at accepted
  · cases accepted
  · cases Except.ok.inj accepted
    rw [List.map_map]
    change snapshot.names.map id = snapshot.names
    exact List.map_id snapshot.names

theorem prepare_graph (context : ModelContext) (snapshot : Snapshot) (view : Prepared)
    (accepted : prepare context snapshot = .ok view) :
    ∃ observation, snapshot.outcome = .ok observation ∧
      view.graph = Coordinates.graph observation.run context.carrier := by
  unfold prepare at accepted
  split at accepted
  · cases accepted
  · rename_i observation observed
    have names : snapshot.names = Coordinates.names observation.run := by
      simpa [observed, outcomeNames] using snapshot.names_eq
    cases Except.ok.inj accepted
    exact ⟨observation, observed, by simp only [Coordinates.graph, names]⟩

theorem prepare_queries_exact (context : ModelContext) (snapshot : Snapshot) (view : Prepared)
    (accepted : prepare context snapshot = .ok view) :
    ∃ observation, snapshot.outcome = .ok observation ∧
      view.queries = context.config.claims.map (fun claim =>
        ⟨claim.claim, claim.query, observation.publicStatus claim.query,
          Coordinates.supports observation.run claim.query⟩) := by
  unfold prepare at accepted
  split at accepted
  · cases accepted
  · rename_i observation observed
    have names : snapshot.names = Coordinates.names observation.run := by
      simpa [observed, outcomeNames] using snapshot.names_eq
    cases Except.ok.inj accepted
    exact ⟨observation, observed, by simp only [Coordinates.supports, names]⟩

theorem gradeNode_exact (kinds : KindTable.Table) (table : Provenance.Table)
    (argument : Presentation.ArgId) (keys : List KindKey)
    (found : Provenance.lookup table argument = .ok keys) :
    (gradeNode kinds (.ok table) argument).value =
      Provenance.scalar (KindTable.lookup kinds) keys := by
  simp [gradeNode, found, Except.bind]

theorem gradeNode_no_promotion (context : ModelContext) (snapshot : Snapshot)
    (table : Provenance.Table) (argument : Presentation.ArgId) (keys : List KindKey)
    (found : Provenance.lookup table argument = .ok keys) (key : KindKey)
    (used : key ∈ keys) (hypothetical : key ∈ Family.selectedKeys snapshot.completion) :
    (gradeNode (gradeTable context snapshot) (.ok table) argument).value.1 = .hypothetical := by
  rw [gradeNode_exact _ _ _ _ found]
  exact Provenance.scalar_no_promotion _ used
    (KindTable.lookup_build_no_promotion _ _ _ _ _ _ _ _ hypothetical)

theorem gradeNode_conditional_cap (context : ModelContext) (snapshot : Snapshot)
    (table : Provenance.Table) (argument : Presentation.ArgId) (keys : List KindKey)
    (found : Provenance.lookup table argument = .ok keys) (key : KindKey)
    (used : key ∈ keys) (conditional : key ∈ context.config.conditionalKeys context.base) :
    (gradeNode (gradeTable context snapshot) (.ok table) argument).value.1 ≤ .conditional := by
  rw [gradeNode_exact _ _ _ _ found]
  exact Provenance.scalar_conditional_cap _ used
    (KindTable.lookup_build_conditional_cap _ _ _ _ _ _ _ _ conditional)

theorem prepare_kinds_exact (context : ModelContext) (snapshot : Snapshot) (view : Prepared)
    (accepted : prepare context snapshot = .ok view) :
    ∃ observation, snapshot.outcome = .ok observation ∧
      view.provenance = Provenance.ofObservation observation ∧
      view.kinds = snapshot.names.map
        (gradeNode (gradeTable context snapshot) (Provenance.ofObservation observation)) ∧
      view.complete = (context.valid && view.provenance.isOk && view.kinds.all (·.value.2)) := by
  unfold prepare at accepted
  split at accepted
  · cases accepted
  · rename_i observation observed
    cases Except.ok.inj accepted
    exact ⟨observation, observed, rfl, rfl, rfl⟩

theorem prepare_complete_all_nodes (context : ModelContext) (snapshot : Snapshot) (view : Prepared)
    (accepted : prepare context snapshot = .ok view) (complete : view.complete = true) :
    context.valid = true ∧ view.provenance.isOk = true ∧
      ∀ node ∈ view.kinds, node.value.2 = true := by
  obtain ⟨_, _, _, _, equation⟩ := prepare_kinds_exact context snapshot view accepted
  rw [equation] at complete
  simpa only [Bool.and_eq_true, List.all_eq_true, and_assoc] using complete

theorem profile_graph_exact (context : ModelContext) (row : Row context)
    (profile : Profile Empty) (truth : Row context → ClaimId → Prop)
    (view : Prepared) (accepted : row.view = .ok view) :
    ∃ observation, row.snapshot.outcome = .ok observation ∧
      (rowModel context truth).underProfile profile row =
        ⟨(Coordinates.graph observation.run context.carrier).args.filter
          (fun argument => decide (row.kind argument ∈ profile.admissible)),
          (Coordinates.graph observation.run context.carrier).attack⟩ := by
  obtain ⟨observation, observed, graph⟩ :=
    prepare_graph context row.snapshot view (row.view_eq.symm.trans accepted)
  exact ⟨observation, observed, by
    simp only [WarrantModel.underProfile, rowModel, Row.graph, accepted, graph]
    rfl⟩

theorem prepare_witness_sound (context : ModelContext) (snapshot : Snapshot) (view : Prepared)
    (accepted : prepare context snapshot = .ok view) (witness : WitnessId) (fields : WitnessFields)
    (member : (witness, .ok fields) ∈ view.witnesses) :
    ∃ observation, snapshot.outcome = .ok observation ∧
      ObservedWitness context.config context.base observation snapshot.completion.history witness fields := by
  unfold prepare at accepted
  split at accepted
  · cases accepted
  · rename_i observation observed
    cases Except.ok.inj accepted
    exact ⟨observation, observed,
      observeWitnesses_sound _ _ _ _ _ _ member⟩

theorem Row.witness_member {context : ModelContext} (row : Row context)
    (witness : WitnessId) (fields : WitnessFields) (success : row.witness witness = some fields) :
    ∃ view, row.view = .ok view ∧ (witness, .ok fields) ∈ view.witnesses := by
  unfold Row.witness at success
  cases observed : row.view with
  | error error => simp [observed] at success
  | ok view =>
    cases found : view.witnesses.find? (fun entry => entry.1 == witness) with
    | none => simp [observed, found] at success
    | some entry =>
      have named : entry.1 = witness := eq_of_beq
        (List.find?_some (p := fun entry : WitnessId × Except WitnessFault WitnessFields =>
          entry.1 == witness) found)
      have outcome : entry.2 = .ok fields := by
        cases actual : entry.2 with
        | error error => simp [observed, found, actual] at success
        | ok value =>
          have equal : value = fields := by simpa [observed, found, actual] using success
          exact congrArg Except.ok equal
      have equal : entry = (witness, .ok fields) := Prod.ext named outcome
      exact ⟨view, rfl, equal ▸ List.mem_of_find?_eq_some found⟩

theorem warranted_source_witness (context : ModelContext) (row : Row context)
    (profile : Profile Empty) (claim : ClaimId) (witness : WitnessId)
    (positive : warranted context row profile claim witness = true) :
    ∃ fields, row.witness witness = some fields ∧ fields.claim = claim ∧
      ∃ observation, row.snapshot.outcome = .ok observation ∧
        ObservedWitness context.config context.base observation row.snapshot.completion.history witness fields := by
  have warrant := (warranted_iff context row profile claim witness (fun _ _ => False)).mp positive
  have artifact := warrant.1
  change row.artifact witness = true at artifact
  unfold Row.artifact at artifact
  cases observed : row.view with
  | error error => simp [observed] at artifact
  | ok view =>
    have both : view.complete = true ∧ (row.witness witness).isSome = true := by
      simpa only [observed, Bool.and_eq_true] using artifact
    obtain ⟨fields, found⟩ := Option.isSome_iff_exists.mp both.2
    have concludes := warrant.2.1
    change row.concludes witness claim = true at concludes
    simp only [Row.concludes, found, Bool.and_eq_true] at concludes
    have sameClaim : fields.claim = claim := eq_of_beq concludes.1
    obtain ⟨view, accepted, member⟩ := row.witness_member witness fields found
    exact ⟨fields, found, sameClaim,
      prepare_witness_sound context row.snapshot view (row.view_eq.symm.trans accepted)
        witness fields member⟩

end Lara.Process.Source
