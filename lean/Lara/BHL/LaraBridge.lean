import Lara.BHL.CheckedMethods
import Lara.BHL.BridgeSource
import Lara.BHL.AssertionLaws
import Lara.Driver

namespace Lara.BHL

open Lara Lara.Support

deriving instance DecidableEq for CheckedMethods.Request

inductive PayloadMode where
  | conditional | applied
  deriving DecidableEq, Repr

inductive ClaimInterpretation where
  | conditional (method : CheckedMethods.Method)
  | applied (method : CheckedMethods.Method)
  deriving DecidableEq, Repr

def ClaimInterpretation.ofMode (mode : PayloadMode) (method : CheckedMethods.Method) :
    ClaimInterpretation :=
  match mode with
  | .conditional => .conditional method
  | .applied => .applied method

inductive ResidualAssumption where
  | interpretationFidelity | physicalSampling | captureAdequacy | runtimeRefinement
  deriving DecidableEq, Repr

inductive HistoryCoverage where
  | completeModeled
  deriving DecidableEq, Repr

/-- A raw occurrence and its exact support material, not merely a stable name.
The checked index is a fresh compact index at this particular accepted run. -/
structure SupportRef where
  rawIndex : Nat
  row : String × SupportTerm
  conclusion : Atom
  query : Atom
  checkedIndex : Nat
  deriving DecidableEq

/-- Authored associations belong to the bridge, not a source declaration.
Declared associations name an actual source claim and its authored argument. -/
inductive ClaimOrigin where
  | authored
  | declared (argument : Presentation.ArgId)
  deriving DecidableEq

structure ArtifactBinding where
  source : Update.SourceState
  claim : Presentation.PropId
  origin : ClaimOrigin
  query : Atom
  interpretation : ClaimInterpretation
  selected : SupportRef
  dependencies : List SupportRef
  method : CheckedMethods.Method
  canonical : CheckedMethods.Binding
  request : CheckedMethods.Request
  residual : List ResidualAssumption
  coverage : HistoryCoverage
  mode : PayloadMode
  evidence : Option EvidenceMaterial
  deriving DecidableEq

def ArtifactBinding.supports (binding : ArtifactBinding) : List SupportRef :=
  binding.selected :: binding.dependencies

/-- Exact canonical execution, including the actual emitted event history. -/
def ArtifactBinding.run (binding : ArtifactBinding) : FiniteExecution.Outcome :=
  binding.method.run binding.request.parameter binding.request.first binding.request.second

/-- Independent declared typing, before admission or grounded evaluation. -/
structure RawSupport {canon : String → String} (reg : BackendRegistry canon)
    (state : Update.SourceState) (ref : SupportRef) : Prop where
  occurrence : state.argsRaw[ref.rawIndex]? = some ref.row
  typed : HasSupport canon state.policy.ruleLookup (Admission.buildGamma state.leaves)
    (certOkOf reg) ref.row.2 ref.conclusion []
  equivalent : equiv canon ref.conclusion ref.query

/-- Reference eligibility uses actual typing, retention, cache identity,
grounded membership and the production blocking computation independently. -/
structure SupportWarrant {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state)
    (ref : SupportRef) : Prop where
  raw : RawSupport reg state ref
  retained : ref.row ∈ run.admission.prune.keptArgs
  checked : HasSupport canon run.checked.policy.ruleLookup
    (Admission.buildGamma run.admission.prune.checkedLeaves) (certOkOf reg)
    ref.row.2 ref.conclusion []
  node : ∃ node, run.checked.nodes[ref.checkedIndex]? = some node ∧
    node.term = ref.row.2 ∧ node.conclusion = ref.conclusion
  carrier : ref.checkedIndex ∈ (Compile.checkedAF run.checked.program).args
  inLabel : Grounded.labelC (Compile.checkedAF run.checked.program) ref.checkedIndex = .inn
  unblocked : ref.query ∉ Update.blockedQueriesForRun run [ref.query]

def ArtifactWarrant {canon : String → String} {reg : BackendRegistry canon}
    (binding : ArtifactBinding) (run : Update.AcceptedRun reg binding.source) : Prop :=
  ∀ ref ∈ binding.supports, SupportWarrant run ref

def ConditionalMethod (binding : ArtifactBinding) : Prop :=
  ValidTriple binding.canonical.model.context binding.canonical.pre.assertion
    binding.canonical.program.program binding.canonical.post.assertion

/-- The precondition and execution are genuine mathematical premises. No Lara
support or applicability assertion is used as either premise. -/
structure ModeledApplication (binding : ArtifactBinding) : Prop where
  initial : satisfies binding.canonical.model.context.interpretation
    binding.canonical.model.context.model GhostEnv.empty
    (binding.request.before.world binding.request.parameter binding.request.first binding.request.second)
    binding.canonical.pre.assertion
  execution : executes binding.canonical.model.context binding.canonical.program.program
    (binding.request.before.world binding.request.parameter binding.request.first binding.request.second)
    (binding.request.after.world binding.request.parameter binding.request.first binding.request.second)

/-- Named claim correspondence is independent of grounded warrant and BHL
validity. Declared correspondence uses the actual full certified source/audit,
including the selected raw occurrence and its authored alternative ledger. -/
inductive ClaimAssociation {canon : String → String} {reg : BackendRegistry canon}
    (binding : ArtifactBinding) (run : Update.AcceptedRun reg binding.source) : Prop where
  | authored
      (origin : binding.origin = .authored)
      (occurrence : binding.source.argsRaw[binding.selected.rawIndex]? = some binding.selected.row)
      (query : binding.selected.query = binding.query) : ClaimAssociation binding run
  | declared {registry : Evidence.Registry} {material : EvidenceMaterial}
      (argument : Presentation.ArgId)
      (origin : binding.origin = .declared argument)
      (materialExact : binding.evidence = some material)
      (source : CertifiedSource registry run material)
      (occurrence : binding.source.argsRaw[binding.selected.rawIndex]? = some binding.selected.row)
      (inputClaim : Surface.claimFormal? material.input.program binding.claim = some binding.query)
      (semanticClaim : Surface.claimFormal? source.audit.declared.semanticProgram binding.claim =
        some binding.query)
      (selectedPair : ∃ pair,
        source.audit.declared.pairs[binding.selected.rawIndex]? = some pair ∧
        pair.argument.id = argument ∧ pair.core = binding.selected.row.2 ∧
        Surface.argSupportsClaim binding.claim pair.argument.concl = true)
      (rowName : binding.selected.row.1 = argument.val)
      (alternative : ∃ indices,
        (binding.claim, indices) ∈ Surface.claimAlternativesOf source.audit.declared.pairs
          source.audit.declared.semanticProgram ∧ binding.selected.rawIndex ∈ indices)
      (query : binding.selected.query = binding.query) : ClaimAssociation binding run

structure MathematicalAlignment (binding : ArtifactBinding) : Prop where
  canonical : binding.canonical = binding.method.binding
  request : binding.request = binding.method.request binding.request.parameter
    binding.request.first binding.request.second
  interpretation : binding.interpretation = ClaimInterpretation.ofMode binding.mode binding.method
  query : binding.selected.query = binding.query

/-- The three meanings stay distinct even in the combined artifact judgment. -/
structure ArtifactMeaning {canon : String → String} {reg : BackendRegistry canon}
    (binding : ArtifactBinding) (run : Update.AcceptedRun reg binding.source) : Prop where
  warrant : ArtifactWarrant binding run
  conditional : ConditionalMethod binding
  application : binding.mode = .applied → ModeledApplication binding
  alignment : MathematicalAlignment binding
  association : ClaimAssociation binding run

/-- Certificates retain independently proved raw typing and exact successful
source/evidence runs. They do not contain a desired warrant or postcondition. -/
structure BridgeCertificate {canon : String → String} (reg : BackendRegistry canon)
    (evidenceRegistry : Evidence.Registry) where
  binding : ArtifactBinding
  run : Update.AcceptedRun reg binding.source
  raw : ∀ ref ∈ binding.supports, RawSupport reg binding.source ref
  evidence : SourceEvidence evidenceRegistry run binding.evidence
  association : ClaimAssociation binding run

inductive BridgeError where
  | staleSnapshot | incompatibleInterpretation | incompatibleMethod
  | incompatibleClaim | incompatibleDependencies | incompatibleEvidence | incompatibleBinding
  | missingSupport | blockedSupport | defeatedSupport | failedDerivation | falsePrecondition
  | application (error : CheckedMethods.ApplicationError)
  deriving DecidableEq, Repr

structure SupportCertificate {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state) (ref : SupportRef) : Type where
  warrant : SupportWarrant run ref

/-- This checks actual retained material and public eligibility, not approval tags. -/
def checkSupport {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state) (ref : SupportRef)
    (raw : RawSupport reg state ref) : Except BridgeError (SupportCertificate run ref) := do
  if retained : ref.row ∈ run.admission.prune.keptArgs then
    match hn : run.checked.nodes[ref.checkedIndex]? with
    | none => .error .missingSupport
    | some node =>
      if ht : node.term = ref.row.2 then
        if hc : node.conclusion = ref.conclusion then
          if carrier : ref.checkedIndex ∈ (Compile.checkedAF run.checked.program).args then
            if blocked : ref.query ∈ Update.blockedQueriesForRun run [ref.query] then
              .error .blockedSupport
            else if label : Grounded.labelC (Compile.checkedAF run.checked.program)
                ref.checkedIndex = .inn then
              .ok ⟨⟨raw, retained, by simpa only [ht, hc] using node.valid,
                ⟨node, hn, ht, hc⟩, carrier, label, blocked⟩⟩
            else .error .defeatedSupport
          else .error .missingSupport
        else .error .missingSupport
      else .error .missingSupport
  else .error .missingSupport

structure SupportsCertificate {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state) (refs : List SupportRef) : Type where
  warrant : ∀ ref ∈ refs, SupportWarrant run ref

def checkSupports {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state) (refs : List SupportRef)
    (raw : ∀ ref ∈ refs, RawSupport reg state ref) :
    Except BridgeError (SupportsCertificate run refs) :=
  match refs with
  | [] => .ok ⟨by simp⟩
  | ref :: rest => do
    let head ← checkSupport run ref (raw ref (by simp))
    let tail ← checkSupports run rest (fun r hr => raw r (by simp [hr]))
    .ok ⟨by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact head.warrant
      · exact tail.warrant r hr⟩

inductive CheckedPayload (binding : ArtifactBinding) : PayloadMode → Type where
  | conditional : CheckedPayload binding .conditional
  | applied (application : CheckedMethods.ApplicationCertificate binding.method binding.request)
      (checked : CheckedMethods.checkApplication binding.method binding.request = .ok application) :
      CheckedPayload binding .applied

structure BoundCertificate {canon : String → String} {reg : BackendRegistry canon}
    {evidenceRegistry : Evidence.Registry} (certificate : BridgeCertificate reg evidenceRegistry) where
  meaning : ArtifactMeaning certificate.binding certificate.run
  payload : CheckedPayload certificate.binding certificate.binding.mode

/-- PR08's real proof checker and real application checker are composed here.
Conditional mode does not ask whether the artifact proves its precondition. -/
@[macro_inline]
def checkBound {canon : String → String} {reg : BackendRegistry canon}
    {evidenceRegistry : Evidence.Registry} (certificate : BridgeCertificate reg evidenceRegistry) :
    Except BridgeError (BoundCertificate certificate) := do
  let binding := certificate.binding
  if canonical : binding.canonical = binding.method.binding then
    if request : binding.request = binding.method.request binding.request.parameter
        binding.request.first binding.request.second then
      if interpretation : binding.interpretation = ClaimInterpretation.ofMode binding.mode binding.method then
        if query : binding.selected.query = binding.query then
          if derivation : (checkDerivation binding.method.evidence).isAccepted = true then
            let supports ← checkSupports certificate.run binding.supports certificate.raw
            let conditional : ConditionalMethod binding := by
              unfold ConditionalMethod
              rw [canonical]
              exact checkDerivation_sound binding.method.evidence derivation
            match mode : binding.mode with
            | .conditional =>
              .ok
                { meaning :=
                    { warrant := supports.warrant
                      conditional := conditional
                      application := by
                        intro applied
                        have impossible : PayloadMode.conditional = PayloadMode.applied :=
                          mode.symm.trans applied
                        cases impossible
                      alignment := ⟨canonical, request, interpretation, query⟩
                      association := certificate.association }
                  payload := by rw [mode]; exact .conditional }
            | .applied =>
              match ha : CheckedMethods.checkApplication binding.method binding.request with
              | .error .failedPrecondition => .error .falsePrecondition
              | .error error => .error (.application error)
              | .ok application =>
                .ok
                  { meaning :=
                      { warrant := supports.warrant
                        conditional := conditional
                        application := fun _ => by
                          change ModeledApplication binding
                          constructor
                          · rw [canonical]
                            exact application.initial
                          · rw [canonical]
                            exact application.execution
                        alignment := ⟨canonical, request, interpretation, query⟩
                        association := certificate.association }
                    payload := by rw [mode]; exact .applied application ha }
          else .error .failedDerivation
        else .error .incompatibleClaim
      else .error .incompatibleInterpretation
    else .error .incompatibleBinding
  else .error .incompatibleMethod

/-- Exact comparison includes every source and mathematical/evidence field. -/
def bindingError (expected actual : ArtifactBinding) : BridgeError :=
  if actual.interpretation ≠ expected.interpretation then .incompatibleInterpretation
  else if actual.method ≠ expected.method ∨ actual.canonical ≠ expected.canonical ∨
      actual.request ≠ expected.request then .incompatibleMethod
  else if actual.claim ≠ expected.claim ∨ actual.origin ≠ expected.origin ∨
      actual.query ≠ expected.query then .incompatibleClaim
  else if actual.selected ≠ expected.selected ∨ actual.dependencies ≠ expected.dependencies then
    .incompatibleDependencies
  else if actual.evidence ≠ expected.evidence then .incompatibleEvidence
  else .incompatibleBinding

structure BridgeResult {canon : String → String} {reg : BackendRegistry canon}
    {evidenceRegistry : Evidence.Registry} (expected : ArtifactBinding)
    (certificate : BridgeCertificate reg evidenceRegistry) where
  exact : certificate.binding = expected
  checked : BoundCertificate certificate

@[macro_inline]
def checkBridge {canon : String → String} {reg : BackendRegistry canon}
    {evidenceRegistry : Evidence.Registry} (expected : ArtifactBinding)
    (certificate : BridgeCertificate reg evidenceRegistry) :
    Except BridgeError (BridgeResult expected certificate) :=
  if snapshot : certificate.binding.source = expected.source then
    if exact : certificate.binding = expected then do
      let checked ← checkBound certificate
      .ok ⟨exact, checked⟩
    else .error (bindingError expected certificate.binding)
  else .error .staleSnapshot

/-- Expansion happens before ANF so proof-indexed mathematical contexts do not
become runtime lets. The result is a closed, executable diagnostic. -/
@[macro_inline]
def checkBridgeNative {canon : String → String} {reg : BackendRegistry canon}
    {evidenceRegistry : Evidence.Registry} (expected : ArtifactBinding)
    (certificate : BridgeCertificate reg evidenceRegistry) : Except BridgeError _root_.Unit :=
  (checkBridge expected certificate).map (fun _ => ())

theorem modeled_application_post (binding : ArtifactBinding)
    (method : ConditionalMethod binding) (application : ModeledApplication binding) :
    satisfies binding.canonical.model.context.interpretation binding.canonical.model.context.model
      GhostEnv.empty
      (binding.request.after.world binding.request.parameter binding.request.first binding.request.second)
      binding.canonical.post.assertion :=
  method GhostEnv.empty _ _ application.initial application.execution

theorem checkBridge_sound {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} {expected : ArtifactBinding}
    {certificate : BridgeCertificate reg registry} {result : BridgeResult expected certificate}
    (_checked : checkBridge expected certificate = .ok result) :
    ArtifactMeaning expected (result.exact ▸ certificate.run) := by
  cases result.exact
  exact result.checked.meaning

theorem checkBridge_binding_integrity {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} {expected : ArtifactBinding}
    {certificate : BridgeCertificate reg registry} {result : BridgeResult expected certificate}
    (_checked : checkBridge expected certificate = .ok result) :
    certificate.binding = expected := result.exact

theorem checkBridge_evidence {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} {expected : ArtifactBinding}
    {certificate : BridgeCertificate reg registry} {result : BridgeResult expected certificate}
    (_checked : checkBridge expected certificate = .ok result) :
    Nonempty (SourceEvidence registry certificate.run expected.evidence) := by
  rw [← result.exact]
  exact ⟨certificate.evidence⟩

theorem checkBridge_exact_fields {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} {expected : ArtifactBinding}
    {certificate : BridgeCertificate reg registry} {result : BridgeResult expected certificate}
    (_checked : checkBridge expected certificate = .ok result) :
    certificate.binding.source = expected.source ∧
    certificate.binding.claim = expected.claim ∧
    certificate.binding.origin = expected.origin ∧
    certificate.binding.query = expected.query ∧
    certificate.binding.interpretation = expected.interpretation ∧
    certificate.binding.method = expected.method ∧
    certificate.binding.canonical = expected.canonical ∧
    certificate.binding.request = expected.request ∧
    certificate.binding.selected = expected.selected ∧
    certificate.binding.dependencies = expected.dependencies ∧
    certificate.binding.evidence = expected.evidence ∧
    certificate.binding.residual = expected.residual ∧
    certificate.binding.coverage = expected.coverage ∧
    certificate.binding.mode = expected.mode := by
  rw [result.exact]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem checkBridge_stale {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} (expected : ArtifactBinding)
    (certificate : BridgeCertificate reg registry)
    (changed : certificate.binding.source ≠ expected.source) :
    checkBridge expected certificate = .error .staleSnapshot := by
  simp only [checkBridge, dif_neg changed]

theorem checkBridge_incompatible {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} (expected : ArtifactBinding)
    (certificate : BridgeCertificate reg registry)
    (sameSource : certificate.binding.source = expected.source)
    (changed : certificate.binding ≠ expected) :
    checkBridge expected certificate = .error (bindingError expected certificate.binding) := by
  simp only [checkBridge, dif_pos sameSource, dif_neg changed]

/-- Complete ordinary observations retain the conditional status even when
blocked; no five-valued projection is substituted for Driver.PublicStatus. -/
def ordinaryStatus {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state) (query : Atom) : Driver.PublicStatus :=
  let status := Grounded.statusC (Compile.checkedAF run.checked.program)
    (Consistency.completeClaimFor run.checked query)
  if query ∈ Update.blockedQueriesForRun run [query] then .evidenceBlocked status
  else .published status

structure OrdinaryObservation where
  source : Update.SourceState
  labels : List (Nat × Grounded.Label)
  edges : List (Nat × Nat)
  statuses : List (Atom × Driver.PublicStatus)
  arguments : List SupportTerm
  checkedHoles : List (Nat × SupportTerm × Atom × List QuestionId)
  attacks : List Attack.Attack
  retainedArguments : List ((String × SupportTerm) × Nat)
  rawArgumentMask : List Bool
  rawAttackMask : List Bool

/-- The full source and checked view, with actual raw retention coordinates.
Canonical located-hole rows, including sites, are derived by ordinaryHoleRows. -/
def observeOrdinary {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state)
    (queries : List Atom) : OrdinaryObservation :=
  let af := Compile.checkedAF run.checked.program
  { source := state
    labels := af.args.map (fun i => (i, Grounded.labelC af i))
    edges := af.args.flatMap (fun i => af.args.filterMap
      (fun j => if af.attack i j then some (i, j) else none))
    statuses := queries.map (fun p => (p, ordinaryStatus run p))
    arguments := run.checked.program.args
    checkedHoles := run.checked.holes.map (fun h => (h.index, h.term, h.conclusion, h.obligations))
    attacks := run.checked.program.atts
    retainedArguments := BlockedProgram.retainedView run.admission.prune.keep state.argsRaw
    rawArgumentMask := state.argsRaw.map run.admission.prune.keep
    rawAttackMask := state.rawAtts.map run.admission.prune.keepAttack }

def BridgeCertificate.ordinary {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} (certificate : BridgeCertificate reg registry)
    (queries : List Atom) : OrdinaryObservation := observeOrdinary certificate.run queries

theorem forgetting_metadata_preserves {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} (certificate : BridgeCertificate reg registry)
    (queries : List Atom) : certificate.ordinary queries = observeOrdinary certificate.run queries := rfl

theorem missing_metadata_preserves {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state) (queries : List Atom)
    (metadata : Option ArtifactBinding) :
    (match metadata with | none => observeOrdinary run queries | some _ => observeOrdinary run queries) =
      observeOrdinary run queries := by cases metadata <;> rfl

theorem ordinary_blocked_payload {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state) (query : Atom)
    (blocked : query ∈ Update.blockedQueriesForRun run [query]) :
    ordinaryStatus run query = .evidenceBlocked
      (Grounded.statusC (Compile.checkedAF run.checked.program)
        (Consistency.completeClaimFor run.checked query)) := by
  simp only [ordinaryStatus, if_pos blocked]


theorem SupportWarrant.published {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} {run : Update.AcceptedRun reg state}
    {ref : SupportRef} (warrant : SupportWarrant run ref) :
    ordinaryStatus run ref.query = .published .justified := by
  obtain ⟨node, nodeAt, term, conclusion⟩ := warrant.node
  have support : ref.checkedIndex ∈ Consistency.claimSupportFor run.checked ref.query :=
    Consistency.mem_claimSupportFor_iff.mpr
      ⟨node, nodeAt, by simpa only [conclusion] using warrant.raw.equivalent⟩
  have status := (Grounded.statusC_justified_iff
    (Compile.checkedAF run.checked.program)
    (Consistency.completeClaimFor run.checked ref.query)).mpr
      ⟨ref.checkedIndex, support, warrant.inLabel⟩
  simp only [ordinaryStatus, if_neg warrant.unblocked, status]

theorem artifact_warrant_selected_public {canon : String → String}
    {reg : BackendRegistry canon} {binding : ArtifactBinding}
    {run : Update.AcceptedRun reg binding.source} (warrant : ArtifactWarrant binding run) :
    ordinaryStatus run binding.selected.query = .published .justified :=
  (warrant binding.selected (by simp [ArtifactBinding.supports])).published

theorem checkSupport_complete {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state) (ref : SupportRef)
    (raw : RawSupport reg state ref) (warrant : SupportWarrant run ref) :
    (checkSupport run ref raw).isOk = true := by
  obtain ⟨node, nodeAt, term, conclusion⟩ := warrant.node
  unfold checkSupport
  rw [dif_pos warrant.retained]
  split
  · rename_i absent
    have impossible := absent.symm.trans nodeAt
    cases impossible
  · rename_i actualNode actualAt
    have sameNode : actualNode = node := Option.some.inj (actualAt.symm.trans nodeAt)
    subst actualNode
    simp only [dif_pos term, dif_pos conclusion, dif_pos warrant.carrier,
      dif_neg warrant.unblocked, dif_pos warrant.inLabel]
    rfl

theorem checkSupports_complete {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state) (refs : List SupportRef)
    (raw : ∀ ref ∈ refs, RawSupport reg state ref)
    (warrant : ∀ ref ∈ refs, SupportWarrant run ref) :
    (checkSupports run refs raw).isOk = true := by
  revert raw warrant
  induction refs with
  | nil => intro raw warrant; rfl
  | cons ref rest ih =>
    intro raw warrant
    have head := checkSupport_complete run ref (raw ref (by simp))
      (warrant ref (by simp))
    have tail := ih (fun r hr => raw r (by simp [hr]))
      (fun r hr => warrant r (by simp [hr]))
    unfold checkSupports
    cases hhead : checkSupport run ref (raw ref (by simp)) with
    | error error => rw [hhead] at head; contradiction
    | ok checked =>
      cases htail : checkSupports run rest (fun r hr => raw r (by simp [hr])) with
      | error error => rw [htail] at tail; contradiction
      | ok checked => rfl

/-- A missing actual context entry rules out every conclusion and obligation
set for this same term; this is not a metadata invalidation convention. -/
theorem no_support_of_missing_leaf {canon : String → String} {Pi Gamma CertOk}
    {term : SupportTerm} {leaf : LeafId}
    (used : leaf ∈ Support.leaves term) (missing : Gamma leaf = none) :
    ¬ ∃ conclusion obligations,
      HasSupport canon Pi Gamma CertOk term conclusion obligations := by
  rintro ⟨conclusion, obligations, typed⟩
  obtain ⟨proposition, declared⟩ := Support.leaves_declared typed leaf used
  rw [missing] at declared
  cases declared

/-- Follow a named source dependency through an actual tightening and the
canonical target prune. Other independent supports are not ruled out. -/
theorem tighten_dependency_loss {canon : String → String} {reg : BackendRegistry canon}
    {source target : Update.SourceState}
    (sourceRun : Update.AcceptedRun reg source) (targetRun : Update.AcceptedRun reg target)
    {key : Presentation.LeafKind × Presentation.Provenance}
    (update : Update.applyUpdate reg source (.tighten key) = .ok target)
    (ref : SupportRef) (raw : RawSupport reg source ref)
    (metadata : Admission.LeafMeta) (declared : metadata ∈ source.metas)
    (keyExact : (metadata.kind, metadata.provenance) = key)
    (used : metadata.id ∈ Support.leaves ref.row.2) :
    target.argsRaw[ref.rawIndex]? = some ref.row ∧
      ref.row ∉ targetRun.admission.prune.keptArgs ∧
      (¬ ∃ conclusion obligations, HasSupport canon targetRun.checked.policy.ruleLookup
        (Admission.buildGamma targetRun.admission.prune.checkedLeaves) (certOkOf reg)
        ref.row.2 conclusion obligations) ∧
      ¬ SupportWarrant targetRun ref := by
  obtain ⟨metas, leaves, args, policy, quarantine⟩ :=
    Update.applyUpdate_tighten_material update
  have targetMeta : metadata ∈ target.metas := by rw [metas]; exact declared
  have decision : Admission.decisionFor target.table metadata.kind metadata.provenance = .quarantine := by
    have sameDecision := congrArg
      (fun pair : Presentation.LeafKind × Presentation.Provenance =>
        Admission.decisionFor target.table pair.1 pair.2) keyExact
    exact sameDecision.trans quarantine
  have seeded : metadata.id ∈ Admission.policyQuarantineSeed target.table target.metas :=
    (Admission.mem_policyQuarantineSeed_iff target.table target.metas metadata.id).mpr
      ⟨metadata, targetMeta, rfl, decision⟩
  have uses := (Update.usesLeaf_true_iff
    (Admission.policyQuarantineSeed target.table target.metas) ref.row.2).mpr
      ⟨metadata.id, used, seeded⟩
  have excluded : ref.row ∉ targetRun.admission.prune.keptArgs := by
    rw [targetRun.prune_eq]
    exact Admission.policy_quarantined_arg_excluded canon target.table target.metas
      target.leaves target.argsRaw target.rawAtts target.groups targetRun.declared.resolved uses
  have absent := Admission.policy_quarantined_absent canon target.table target.metas
    target.leaves target.groups targetMeta decision
  have missing : Admission.buildGamma targetRun.admission.prune.checkedLeaves metadata.id = none := by
    cases gamma : Admission.buildGamma targetRun.admission.prune.checkedLeaves metadata.id with
    | none => rfl
    | some proposition =>
      have member := Admission.buildGamma_some_mem gamma
      rw [targetRun.prune_eq] at member
      have inChecked : metadata.id ∈ Admission.checkedAdmittedIds canon target.table target.metas
          target.leaves target.groups := by
        simpa only [Admission.buildPrune, Admission.checkedAdmittedIds] using member
      exact False.elim (absent inChecked)
  have lost := no_support_of_missing_leaf (canon := canon)
    (Pi := targetRun.checked.policy.ruleLookup) (CertOk := certOkOf reg) used missing
  refine ⟨?_, excluded, lost, ?_⟩
  · rw [args]
    exact raw.occurrence
  · intro warrant
    exact lost ⟨ref.conclusion, [], warrant.checked⟩

theorem tighten_artifact_warrant_loss {canon : String → String} {reg : BackendRegistry canon}
    {source target : Update.SourceState}
    (sourceRun : Update.AcceptedRun reg source) (targetRun : Update.AcceptedRun reg target)
    {key : Presentation.LeafKind × Presentation.Provenance}
    (update : Update.applyUpdate reg source (.tighten key) = .ok target)
    (binding : ArtifactBinding) (sameTarget : binding.source = target)
    (ref : SupportRef) (member : ref ∈ binding.supports) (raw : RawSupport reg source ref)
    (metadata : Admission.LeafMeta) (declared : metadata ∈ source.metas)
    (keyExact : (metadata.kind, metadata.provenance) = key)
    (used : metadata.id ∈ Support.leaves ref.row.2) :
    ¬ ArtifactWarrant binding (sameTarget.symm ▸ targetRun) := by
  have lost := (tighten_dependency_loss sourceRun targetRun update ref raw metadata declared keyExact used).2.2.2
  subst target
  intro warrant
  exact lost (warrant ref member)

/-- Rebinding changes occurrence indices only; exact material is retained. -/
def SupportRef.reindex (rawMap checkedMap : Nat → Nat) (ref : SupportRef) : SupportRef :=
  { ref with rawIndex := rawMap ref.rawIndex, checkedIndex := checkedMap ref.checkedIndex }

def reboundBinding (binding : ArtifactBinding) (target : Update.SourceState)
    (rawMap checkedMap : Nat → Nat) (evidence : Option EvidenceMaterial) : ArtifactBinding :=
  { binding with source := target
                 selected := binding.selected.reindex rawMap checkedMap
                 dependencies := binding.dependencies.map (SupportRef.reindex rawMap checkedMap)
                 evidence := evidence }

/-- Certified transport preserves actual objects, full metadata and exact
authored leaf request/reference records, while allowing unrelated additions. -/
def EvidenceTransport : Option EvidenceMaterial → Option EvidenceMaterial → Prop
  | none, none => True
  | some old, some fresh =>
      old.snapshot = fresh.snapshot ∧ old.manifest = fresh.manifest ∧
      old.input.policy = fresh.input.policy ∧
      ∀ leaf ∈ Surface.leafRecords old.input.program,
        leaf ∈ Surface.leafRecords fresh.input.program
  | _, _ => False

/-- Whole-carrier incoming attack/defense closure is the SinkEmbedding
contract. Fresh sinks cannot attack old nodes, so all old defense paths and
all three labels are preserved. Raw identities remain injective separately. -/
structure RebindConditions {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} (certificate : BridgeCertificate reg registry)
    {target : Update.SourceState} (targetRun : Update.AcceptedRun reg target)
    (rawMap checkedMap : Nat → Nat) (sinks : List Nat) (evidence : Option EvidenceMaterial) where
  rawInjective : Function.Injective rawMap
  checkedInjective : Function.Injective checkedMap
  policy : target.policy = certificate.binding.source.policy
  leafMaterial : ∀ ref ∈ certificate.binding.supports, ∀ leaf ∈ Support.leaves ref.row.2,
    Admission.buildGamma target.leaves leaf =
      Admission.buildGamma certificate.binding.source.leaves leaf
  occurrence : ∀ ref ∈ certificate.binding.supports,
    target.argsRaw[rawMap ref.rawIndex]? = some ref.row
  retained : ∀ ref ∈ certificate.binding.supports,
    ref.row ∈ targetRun.admission.prune.keptArgs
  node : ∀ ref ∈ certificate.binding.supports,
    ∃ node, targetRun.checked.nodes[checkedMap ref.checkedIndex]? = some node ∧
      node.term = ref.row.2 ∧ node.conclusion = ref.conclusion
  embedding : Grounded.SinkEmbedding
    (Compile.checkedAF certificate.run.checked.program)
    (Compile.checkedAF targetRun.checked.program) checkedMap sinks
  clean : Update.CleanBase targetRun
  evidenceSource : SourceEvidence registry targetRun evidence
  evidenceAlignment : EvidenceTransport certificate.binding.evidence evidence
  claimAssociation :
    ClaimAssociation (reboundBinding certificate.binding target rawMap checkedMap evidence) targetRun

theorem RebindConditions.raw {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} {certificate : BridgeCertificate reg registry}
    {target : Update.SourceState} {targetRun : Update.AcceptedRun reg target}
    {rawMap checkedMap : Nat → Nat} {sinks : List Nat} {evidence : Option EvidenceMaterial}
    (transport : RebindConditions certificate targetRun rawMap checkedMap sinks evidence)
    (ref : SupportRef) (member : ref ∈ certificate.binding.supports) :
    RawSupport reg target (ref.reindex rawMap checkedMap) := by
  have old := certificate.raw ref member
  refine ⟨transport.occurrence ref member, ?_, old.equivalent⟩
  change HasSupport canon target.policy.ruleLookup (Admission.buildGamma target.leaves)
    (certOkOf reg) ref.row.2 ref.conclusion []
  rw [transport.policy]
  exact Support.hasSupport_congr_gamma_on old.typed
    (fun leaf used => (transport.leafMaterial ref member leaf used).symm)

@[macro_inline]
def rebind {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} (certificate : BridgeCertificate reg registry)
    {target : Update.SourceState} (targetRun : Update.AcceptedRun reg target)
    (rawMap checkedMap : Nat → Nat) (sinks : List Nat) (evidence : Option EvidenceMaterial)
    (transport : RebindConditions certificate targetRun rawMap checkedMap sinks evidence) :
    BridgeCertificate reg registry :=
  { binding := reboundBinding certificate.binding target rawMap checkedMap evidence
    run := targetRun
    raw := by
      intro ref member
      have mapped : ref ∈ certificate.binding.supports.map (SupportRef.reindex rawMap checkedMap) := by
        simpa only [reboundBinding, ArtifactBinding.supports, List.map_cons] using member
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp mapped
      exact transport.raw old oldMember
    evidence := transport.evidenceSource
    association := transport.claimAssociation }

theorem rebind_labels {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} {certificate : BridgeCertificate reg registry}
    {target : Update.SourceState} {targetRun : Update.AcceptedRun reg target}
    {rawMap checkedMap : Nat → Nat} {sinks : List Nat} {evidence : Option EvidenceMaterial}
    (transport : RebindConditions certificate targetRun rawMap checkedMap sinks evidence)
    {index : Nat} (carrier : index ∈ (Compile.checkedAF certificate.run.checked.program).args) :
    Grounded.labelC (Compile.checkedAF targetRun.checked.program) (checkedMap index) =
      Grounded.labelC (Compile.checkedAF certificate.run.checked.program) index :=
  transport.embedding.label_old carrier

theorem rebind_warrant {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} (certificate : BridgeCertificate reg registry)
    {target : Update.SourceState} (targetRun : Update.AcceptedRun reg target)
    (rawMap checkedMap : Nat → Nat) (sinks : List Nat) (evidence : Option EvidenceMaterial)
    (transport : RebindConditions certificate targetRun rawMap checkedMap sinks evidence)
    (oldWarrant : ArtifactWarrant certificate.binding certificate.run) :
    ArtifactWarrant (reboundBinding certificate.binding target rawMap checkedMap evidence) targetRun := by
  intro ref member
  have mapped : ref ∈ certificate.binding.supports.map (SupportRef.reindex rawMap checkedMap) := by
    simpa only [reboundBinding, ArtifactBinding.supports, List.map_cons] using member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp mapped
  have oldEligible := oldWarrant old oldMember
  obtain ⟨node, nodeAt, term, conclusion⟩ := transport.node old oldMember
  refine
    { raw := transport.raw old oldMember
      retained := transport.retained old oldMember
      checked := by simpa only [SupportRef.reindex, term, conclusion] using node.valid
      node := ⟨node, nodeAt, term, conclusion⟩
      carrier := transport.embedding.map_mem old.checkedIndex oldEligible.carrier
      inLabel := (rebind_labels transport oldEligible.carrier).trans oldEligible.inLabel
      unblocked := ?_ }
  change old.query ∉ @Update.blockedQueriesForRun canon reg target targetRun [old.query]
  rw [Update.blockedQueriesForRun_eq_nil_of_clean targetRun transport.clean]
  simp

theorem rebind_mathematical_contract (binding : ArtifactBinding) (target : Update.SourceState)
    (rawMap checkedMap : Nat → Nat) (evidence : Option EvidenceMaterial) :
    (reboundBinding binding target rawMap checkedMap evidence).method = binding.method ∧
    (reboundBinding binding target rawMap checkedMap evidence).canonical = binding.canonical ∧
    (reboundBinding binding target rawMap checkedMap evidence).request = binding.request ∧
    (reboundBinding binding target rawMap checkedMap evidence).interpretation = binding.interpretation ∧
    (reboundBinding binding target rawMap checkedMap evidence).residual = binding.residual ∧
    (reboundBinding binding target rawMap checkedMap evidence).coverage = binding.coverage := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rebind_conditional (binding : ArtifactBinding) (target : Update.SourceState)
    (rawMap checkedMap : Nat → Nat) (evidence : Option EvidenceMaterial)
    (valid : ConditionalMethod binding) :
    ConditionalMethod (reboundBinding binding target rawMap checkedMap evidence) := valid

theorem rebind_application (binding : ArtifactBinding) (target : Update.SourceState)
    (rawMap checkedMap : Nat → Nat) (evidence : Option EvidenceMaterial)
    (application : ModeledApplication binding) :
    ModeledApplication (reboundBinding binding target rawMap checkedMap evidence) :=
  ⟨application.initial, application.execution⟩

theorem rebind_meaning {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} (certificate : BridgeCertificate reg registry)
    {target : Update.SourceState} (targetRun : Update.AcceptedRun reg target)
    (rawMap checkedMap : Nat → Nat) (sinks : List Nat) (evidence : Option EvidenceMaterial)
    (transport : RebindConditions certificate targetRun rawMap checkedMap sinks evidence)
    (oldMeaning : ArtifactMeaning certificate.binding certificate.run) :
    ArtifactMeaning (reboundBinding certificate.binding target rawMap checkedMap evidence) targetRun :=
  ⟨rebind_warrant certificate targetRun rawMap checkedMap sinks evidence transport oldMeaning.warrant,
    oldMeaning.conditional,
    fun applied => rebind_application certificate.binding target rawMap checkedMap evidence
      (oldMeaning.application applied),
    ⟨oldMeaning.alignment.canonical, oldMeaning.alignment.request,
      oldMeaning.alignment.interpretation, oldMeaning.alignment.query⟩,
    transport.claimAssociation⟩

theorem rebound_requires_fresh_certificate {canon : String → String}
    {reg : BackendRegistry canon} {registry : Evidence.Registry}
    (certificate : BridgeCertificate reg registry) (target : Update.SourceState)
    (rawMap checkedMap : Nat → Nat) (evidence : Option EvidenceMaterial)
    (changed : certificate.binding.source ≠ target) :
    checkBridge (reboundBinding certificate.binding target rawMap checkedMap evidence) certificate =
      .error .staleSnapshot :=
  checkBridge_stale _ certificate changed


theorem conditional_false_no_application (binding : ArtifactBinding)
    (canonical : binding.canonical = CheckedMethods.Method.conditionalFalse.binding) :
    ¬ ModeledApplication binding := by
  intro application
  have initial := application.initial
  rw [canonical] at initial
  exact CheckedMethods.conditional_false_not_applicable binding.request initial

theorem applicability_support_not_precondition {canon : String → String}
    {reg : BackendRegistry canon} (binding : ArtifactBinding)
    (run : Update.AcceptedRun reg binding.source)
    (_supported : ArtifactWarrant binding run)
    (canonical : binding.canonical = CheckedMethods.Method.conditionalFalse.binding) :
    ¬ ModeledApplication binding :=
  conditional_false_no_application binding canonical

/-- The real Driver located-hole projection from the exact accepted run;
neither callers nor BHL metadata supply hole rows. -/
def ordinaryHoleRows {reg : BackendRegistry Driver.dcanon} {state : Update.SourceState}
    (run : Update.AcceptedRun reg state) : List Driver.HoleRow :=
  Driver.holeRows run.admission.prune.keep state.argsRaw
    run.admission.prune.keepAttack state.rawAtts run.checked

/-- Actual Driver encoding, including derived located holes and the blocked
conditional section. -/
def observeOrdinaryWire {reg : BackendRegistry Driver.dcanon} {state : Update.SourceState}
    (run : Update.AcceptedRun reg state) (replay : Driver.ReplayId)
    (queries : List Atom) : Driver.Sx :=
  Driver.buildAccept replay run.checked queries (Update.blockedQueriesForRun run queries)
    (ordinaryHoleRows run)

theorem wire_metadata_preserves {reg : BackendRegistry Driver.dcanon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state)
    (replay : Driver.ReplayId) (queries : List Atom)
    (metadata : Option ArtifactBinding) :
    (match metadata with
      | none => observeOrdinaryWire run replay queries
      | some _ => observeOrdinaryWire run replay queries) =
      Driver.buildAccept replay run.checked queries (Update.blockedQueriesForRun run queries)
        (Driver.holeRows run.admission.prune.keep state.argsRaw
          run.admission.prune.keepAttack state.rawAtts run.checked) := by
  cases metadata <;> rfl

/-- Bridge-only metadata does not interpose a source/evidence rejection gate. -/
def sourceWithMetadata (env : Surface.Env canonNum) (input : Surface.Input)
    (snapshot : Evidence.Snapshot) (manifest : List Evidence.ObjectMeta)
    (registry : Evidence.Registry) (metadata : Option ArtifactBinding) :=
  (Surface.sourceWithEvidence env input snapshot manifest registry, metadata)

theorem source_metadata_preserves (env : Surface.Env canonNum) (input : Surface.Input)
    (snapshot : Evidence.Snapshot) (manifest : List Evidence.ObjectMeta)
    (registry : Evidence.Registry) (metadata : Option ArtifactBinding) :
    (sourceWithMetadata env input snapshot manifest registry metadata).1 =
      Surface.sourceWithEvidence env input snapshot manifest registry := rfl

def updateWithMetadata {canon : String → String} (reg : BackendRegistry canon)
    (source : Update.SourceState) (update : Update.SourceUpdate) (metadata : Option ArtifactBinding) :=
  (Update.applyUpdate reg source update, metadata)

theorem update_metadata_preserves {canon : String → String} (reg : BackendRegistry canon)
    (source : Update.SourceState) (update : Update.SourceUpdate) (metadata : Option ArtifactBinding) :
    (updateWithMetadata reg source update metadata).1 = Update.applyUpdate reg source update := rfl


theorem CheckedPayload.application_checked {binding : ArtifactBinding}
    (payload : CheckedPayload binding binding.mode) (applied : binding.mode = .applied) :
    (CheckedMethods.checkApplication binding.method binding.request).isOk = true := by
  rw [applied] at payload
  cases payload with
  | applied application checked => rw [checked]; rfl

theorem checkBound_complete {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} (certificate : BridgeCertificate reg registry)
    (alignment : MathematicalAlignment certificate.binding)
    (warrant : ArtifactWarrant certificate.binding certificate.run)
    (application : certificate.binding.mode = .applied →
      (CheckedMethods.checkApplication certificate.binding.method certificate.binding.request).isOk = true) :
    (checkBound certificate).isOk = true := by
  have supports := checkSupports_complete certificate.run certificate.binding.supports
    certificate.raw warrant
  unfold checkBound
  simp only [dif_pos alignment.canonical, dif_pos alignment.request,
    dif_pos alignment.interpretation, dif_pos alignment.query,
    dif_pos (CheckedMethods.method_checked certificate.binding.method)]
  cases hs : checkSupports certificate.run certificate.binding.supports certificate.raw with
  | error error => rw [hs] at supports; contradiction
  | ok checked =>
    simp only [hs, Bind.bind, Except.bind]
    split
    · rfl
    · rename_i mode
      have accepted := application mode
      split
      · simp_all [Except.isOk, Except.toBool]
      · simp_all [Except.isOk, Except.toBool]
      · rfl

theorem checkBridge_complete {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} (certificate : BridgeCertificate reg registry)
    (alignment : MathematicalAlignment certificate.binding)
    (warrant : ArtifactWarrant certificate.binding certificate.run)
    (application : certificate.binding.mode = .applied →
      (CheckedMethods.checkApplication certificate.binding.method certificate.binding.request).isOk = true) :
    (checkBridge certificate.binding certificate).isOk = true := by
  have accepted := checkBound_complete certificate alignment warrant application
  unfold checkBridge
  simp only [dif_pos rfl]
  cases checked : checkBound certificate with
  | error error => rw [checked] at accepted; contradiction
  | ok result => rfl

theorem rebind_checker_success {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} (certificate : BridgeCertificate reg registry)
    {target : Update.SourceState} (targetRun : Update.AcceptedRun reg target)
    (rawMap checkedMap : Nat → Nat) (sinks : List Nat) (evidence : Option EvidenceMaterial)
    (transport : RebindConditions certificate targetRun rawMap checkedMap sinks evidence)
    (oldChecked : BoundCertificate certificate) :
    (checkBridge (reboundBinding certificate.binding target rawMap checkedMap evidence)
      (rebind certificate targetRun rawMap checkedMap sinks evidence transport)).isOk = true := by
  apply checkBridge_complete
  · exact
      { canonical := oldChecked.meaning.alignment.canonical
        request := oldChecked.meaning.alignment.request
        interpretation := oldChecked.meaning.alignment.interpretation
        query := oldChecked.meaning.alignment.query }
  · exact rebind_warrant certificate targetRun rawMap checkedMap sinks evidence transport
      oldChecked.meaning.warrant
  · exact oldChecked.payload.application_checked

theorem rebind_run_exact (binding : ArtifactBinding) (target : Update.SourceState)
    (rawMap checkedMap : Nat → Nat) (evidence : Option EvidenceMaterial) :
    (reboundBinding binding target rawMap checkedMap evidence).run = binding.run := rfl

theorem checked_payload_run {binding : ArtifactBinding}
    (application : CheckedMethods.ApplicationCertificate binding.method binding.request) :
    application.computed = binding.run := application.computed_exact

theorem checkSupport_missing {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state) (ref : SupportRef)
    (raw : RawSupport reg state ref) (missing : ref.row ∉ run.admission.prune.keptArgs) :
    checkSupport run ref raw = .error .missingSupport := by
  simp only [checkSupport, dif_neg missing]


theorem sinkEmbedding_of_checked_agree {canon : String → String}
    {reg : BackendRegistry canon} {source target : Update.SourceState}
    (sourceRun : Update.AcceptedRun reg source) (targetRun : Update.AcceptedRun reg target)
    (arguments : sourceRun.checked.program.args = targetRun.checked.program.args)
    (attacks : sourceRun.checked.program.atts = targetRun.checked.program.atts) :
    Grounded.SinkEmbedding (Compile.checkedAF sourceRun.checked.program)
      (Compile.checkedAF targetRun.checked.program) id [] := by
  have same := Compile.checkedAF_eq_of_coverage sourceRun.checked.program targetRun.checked.program
    arguments (fun a _ b _ => by rw [attacks])
  rw [← same]
  exact
    { map_mem := fun a member => member
      mem_cases := fun b member => Or.inr ⟨b, member, rfl⟩
      old_attack := fun a _ b _ => rfl
      sink_no_out := by intro sink member; simp at member }


theorem conditional_false_precondition (binding : ArtifactBinding)
    (canonical : binding.canonical = CheckedMethods.Method.conditionalFalse.binding) :
    ¬ satisfies binding.canonical.model.context.interpretation binding.canonical.model.context.model
      GhostEnv.empty
      (binding.request.before.world binding.request.parameter binding.request.first binding.request.second)
      binding.canonical.pre.assertion := by
  rw [canonical]
  exact CheckedMethods.conditional_false_not_applicable binding.request

theorem supported_applicability_without_truth {canon : String → String}
    {reg : BackendRegistry canon} (binding : ArtifactBinding)
    (run : Update.AcceptedRun reg binding.source) (warrant : ArtifactWarrant binding run)
    (canonical : binding.canonical = CheckedMethods.Method.conditionalFalse.binding) :
    ordinaryStatus run binding.selected.query = .published .justified ∧
    ¬ satisfies binding.canonical.model.context.interpretation binding.canonical.model.context.model
      GhostEnv.empty
      (binding.request.before.world binding.request.parameter binding.request.first binding.request.second)
      binding.canonical.pre.assertion :=
  ⟨artifact_warrant_selected_public warrant, conditional_false_precondition binding canonical⟩

theorem supported_applicability_without_knowledge {canon : String → String}
    {reg : BackendRegistry canon} (binding : ArtifactBinding)
    (run : Update.AcceptedRun reg binding.source) (warrant : ArtifactWarrant binding run)
    (canonical : binding.canonical = CheckedMethods.Method.conditionalFalse.binding)
    (admitted : Admitted binding.canonical.model.context.model.dynamics
      (binding.request.before.world binding.request.parameter binding.request.first binding.request.second)) :
    ordinaryStatus run binding.selected.query = .published .justified ∧
    ¬ knows binding.canonical.model.context.model
      (binding.request.before.world binding.request.parameter binding.request.first binding.request.second)
      (fun world => satisfies binding.canonical.model.context.interpretation
        binding.canonical.model.context.model GhostEnv.empty world binding.canonical.pre.assertion) := by
  refine ⟨artifact_warrant_selected_public warrant, ?_⟩
  intro known
  exact conditional_false_precondition binding canonical
    (know_truth binding.canonical.model.context.model admitted known)

theorem tighten_raw_support_preserved {canon : String → String} {reg : BackendRegistry canon}
    {source target : Update.SourceState} {key : Presentation.LeafKind × Presentation.Provenance}
    (update : Update.applyUpdate reg source (.tighten key) = .ok target)
    {ref : SupportRef} (raw : RawSupport reg source ref) : RawSupport reg target ref := by
  obtain ⟨metas, leaves, arguments, policy, quarantine⟩ :=
    Update.applyUpdate_tighten_material update
  exact
    { occurrence := by rw [arguments]; exact raw.occurrence
      typed := by rw [policy, leaves]; exact raw.typed
      equivalent := raw.equivalent }

theorem tighten_support_rejected {canon : String → String} {reg : BackendRegistry canon}
    {source target : Update.SourceState}
    (sourceRun : Update.AcceptedRun reg source) (targetRun : Update.AcceptedRun reg target)
    {key : Presentation.LeafKind × Presentation.Provenance}
    (update : Update.applyUpdate reg source (.tighten key) = .ok target)
    (ref : SupportRef) (raw : RawSupport reg source ref)
    (metadata : Admission.LeafMeta) (declared : metadata ∈ source.metas)
    (keyExact : (metadata.kind, metadata.provenance) = key)
    (used : metadata.id ∈ Support.leaves ref.row.2) :
    checkSupport targetRun ref (tighten_raw_support_preserved update raw) = .error .missingSupport :=
  checkSupport_missing targetRun ref (tighten_raw_support_preserved update raw)
    (tighten_dependency_loss sourceRun targetRun update ref raw metadata declared keyExact used).2.1

theorem checkBridge_no_warrant {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} (expected : ArtifactBinding)
    (certificate : BridgeCertificate reg registry)
    (lost : ¬ ArtifactWarrant certificate.binding certificate.run) :
    (checkBridge expected certificate).isOk = false := by
  cases checked : checkBridge expected certificate with
  | error error => rfl
  | ok result => exact False.elim (lost result.checked.meaning.warrant)


theorem EvidenceTransport.certified_exact {old fresh : EvidenceMaterial}
    (transport : EvidenceTransport (some old) (some fresh)) :
    old.snapshot = fresh.snapshot ∧ old.manifest = fresh.manifest ∧
      old.input.policy = fresh.input.policy ∧
      ∀ leaf ∈ Surface.leafRecords old.input.program,
        leaf ∈ Surface.leafRecords fresh.input.program := transport

theorem EvidenceTransport.request_preserved {old fresh : EvidenceMaterial}
    (transport : EvidenceTransport (some old) (some fresh))
    {leaf : Presentation.Leaf} (member : leaf ∈ Surface.leafRecords old.input.program) :
    leaf ∈ Surface.leafRecords fresh.input.program := transport.2.2.2 leaf member

theorem quarantine_mathematical_contract (binding : ArtifactBinding) (target : Update.SourceState)
    (valid : ConditionalMethod binding) (application : ModeledApplication binding) :
    ConditionalMethod { binding with source := target } ∧
      ModeledApplication { binding with source := target } :=
  ⟨valid, ⟨application.initial, application.execution⟩⟩


theorem ClaimAssociation.raw_occurrence {canon : String → String}
    {reg : BackendRegistry canon} {binding : ArtifactBinding}
    {run : Update.AcceptedRun reg binding.source} (association : ClaimAssociation binding run) :
    binding.source.argsRaw[binding.selected.rawIndex]? = some binding.selected.row := by
  cases association <;> assumption

theorem ClaimAssociation.query_exact {canon : String → String}
    {reg : BackendRegistry canon} {binding : ArtifactBinding}
    {run : Update.AcceptedRun reg binding.source} (association : ClaimAssociation binding run) :
    binding.selected.query = binding.query := by
  cases association <;> assumption

theorem ClaimAssociation.declared_input_claim {canon : String → String}
    {reg : BackendRegistry canon} {binding : ArtifactBinding}
    {run : Update.AcceptedRun reg binding.source} (association : ClaimAssociation binding run)
    {argument : Presentation.ArgId} (declared : binding.origin = .declared argument) :
    ∃ material, binding.evidence = some material ∧
      Surface.claimFormal? material.input.program binding.claim = some binding.query := by
  cases association
  · rename_i origin occurrence query
    have impossible : ClaimOrigin.authored = ClaimOrigin.declared argument :=
      origin.symm.trans declared
    cases impossible
  · rename_i registry material actualArgument origin materialExact source occurrence
      inputClaim semanticClaim selectedPair rowName alternative query
    exact ⟨material, materialExact, inputClaim⟩

theorem ClaimAssociation.declared_source_alternative {canon : String → String}
    {reg : BackendRegistry canon} {binding : ArtifactBinding}
    {run : Update.AcceptedRun reg binding.source} (association : ClaimAssociation binding run)
    {argument : Presentation.ArgId} (declared : binding.origin = .declared argument) :
    ∃ registry material, ∃ source : CertifiedSource registry run material,
      binding.evidence = some material ∧
      Surface.claimFormal? source.audit.declared.semanticProgram binding.claim = some binding.query ∧
      binding.selected.row.1 = argument.val ∧
      (∃ pair, source.audit.declared.pairs[binding.selected.rawIndex]? = some pair ∧
        pair.argument.id = argument ∧ pair.core = binding.selected.row.2 ∧
        Surface.argSupportsClaim binding.claim pair.argument.concl = true) ∧
      ∃ indices, (binding.claim, indices) ∈ Surface.claimAlternativesOf source.audit.declared.pairs
        source.audit.declared.semanticProgram ∧ binding.selected.rawIndex ∈ indices := by
  cases association
  · rename_i origin occurrence query
    have impossible : ClaimOrigin.authored = ClaimOrigin.declared argument :=
      origin.symm.trans declared
    cases impossible
  · rename_i registry material actualArgument origin materialExact source occurrence
      inputClaim semanticClaim selectedPair rowName alternative query
    have argumentExact : actualArgument = argument :=
      ClaimOrigin.declared.inj (origin.symm.trans declared)
    rw [argumentExact] at selectedPair rowName
    exact ⟨registry, material, source, materialExact, semanticClaim, rowName, selectedPair, alternative⟩

theorem ClaimAssociation.no_declared_without_source {canon : String → String}
    {reg : BackendRegistry canon} {binding : ArtifactBinding}
    {run : Update.AcceptedRun reg binding.source}
    {argument : Presentation.ArgId} (declared : binding.origin = .declared argument)
    (ordinary : binding.evidence = none) : ¬ ClaimAssociation binding run := by
  intro association
  obtain ⟨material, present, formal⟩ := association.declared_input_claim declared
  have impossible : (none : Option EvidenceMaterial) = some material := ordinary.symm.trans present
  cases impossible

theorem checkBridge_claim_association {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} {expected : ArtifactBinding}
    {certificate : BridgeCertificate reg registry} {result : BridgeResult expected certificate}
    (checked : checkBridge expected certificate = .ok result) :
    ClaimAssociation expected (result.exact ▸ certificate.run) :=
  (checkBridge_sound checked).association

theorem checkBridge_origin_integrity {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} {expected : ArtifactBinding}
    {certificate : BridgeCertificate reg registry} {result : BridgeResult expected certificate}
    (_checked : checkBridge expected certificate = .ok result) :
    certificate.binding.origin = expected.origin :=
  congrArg ArtifactBinding.origin result.exact

theorem checkBridge_origin_copy_rejected {canon : String → String} {reg : BackendRegistry canon}
    {registry : Evidence.Registry} (expected : ArtifactBinding)
    (certificate : BridgeCertificate reg registry)
    (changed : certificate.binding.origin ≠ expected.origin) :
    (checkBridge expected certificate).isOk = false := by
  cases checked : checkBridge expected certificate with
  | error error => rfl
  | ok result => exact False.elim (changed (congrArg ArtifactBinding.origin result.exact))

theorem ordinary_retention_projection {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state) (queries : List Atom) :
    (observeOrdinary run queries).retainedArguments =
        BlockedProgram.retainedView run.admission.prune.keep state.argsRaw ∧
      (observeOrdinary run queries).rawArgumentMask = state.argsRaw.map run.admission.prune.keep ∧
      (observeOrdinary run queries).rawAttackMask = state.rawAtts.map run.admission.prune.keepAttack :=
  ⟨rfl, rfl, rfl⟩

theorem ordinary_checked_holes_projection {canon : String → String} {reg : BackendRegistry canon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state) (queries : List Atom) :
    (observeOrdinary run queries).checkedHoles =
      run.checked.holes.map (fun hole => (hole.index, hole.term, hole.conclusion, hole.obligations)) := rfl

theorem ordinaryHoleRows_exact {reg : BackendRegistry Driver.dcanon} {state : Update.SourceState}
    (run : Update.AcceptedRun reg state) :
    ordinaryHoleRows run = Driver.holeRows run.admission.prune.keep state.argsRaw
      run.admission.prune.keepAttack state.rawAtts run.checked := rfl

theorem ordinaryHoleRows_obligations {reg : BackendRegistry Driver.dcanon} {state : Update.SourceState}
    (run : Update.AcceptedRun reg state) :
    ∀ row ∈ ordinaryHoleRows run, ∃ hole ∈ run.checked.holes,
      row.obligations = Check.holeObligationSites hole :=
  Driver.holeRows_obligations run.admission.prune.keep state.argsRaw
    run.admission.prune.keepAttack state.rawAtts run.checked

theorem ordinaryWire_projection {reg : BackendRegistry Driver.dcanon}
    {state : Update.SourceState} (run : Update.AcceptedRun reg state)
    (replay : Driver.ReplayId) (queries : List Atom) :
    observeOrdinaryWire run replay queries =
      Driver.buildAccept replay run.checked queries (Update.blockedQueriesForRun run queries)
        (Driver.holeRows run.admission.prune.keep state.argsRaw
          run.admission.prune.keepAttack state.rawAtts run.checked) := rfl

end Lara.BHL
