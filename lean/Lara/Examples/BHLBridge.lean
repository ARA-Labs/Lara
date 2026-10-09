import Lara.Examples.Update
import Lara.Examples.Surface
import Lara.Surface.Source
import Lara.Evidence.Composition
import Lara.Evidence.Extract
import Lara.BHL.LaraBridge
import Lara.BHL.AssertionLaws
import Lara.Examples.BHLBelief

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace Lara.Examples.BHLBridge

open Lara Lara.Support Lara.Examples Lara.BHL


/-- Selected method and its named applicability argument are distinct raw occurrences. -/
def dependencySource : Lara.Update.SourceState :=
  { sigma := sigmaEx
    policy := { unitPolicyEx with defeat := ⟨[], []⟩ }
    table := []
    metas := [{ id := l1, kind := .attested, provenance := .user },
      { id := l2, kind := .observed, provenance := .user },
      { id := l3, kind := .observed, provenance := .user }]
    leaves := [(l1, pC), (l2, pA), (l3, pA)]
    argsRaw := [("selected", .leaf l2), ("applicability", .leaf l1),
      ("alternative", .leaf l3)]
    rawAtts := []
    groups := []
    ground := groundEx }

def applicabilityKey : Presentation.LeafKind × Presentation.Provenance :=
  (.attested, .user)

def dependencyTarget : Lara.Update.SourceState :=
  { dependencySource with table := [{ key := applicabilityKey, decision := .quarantine }] }

def dependencySourceRun : Examples.Update.AcceptedRun dependencySource :=
  Examples.Update.fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

def dependencyTargetRun : Examples.Update.AcceptedRun dependencyTarget :=
  Examples.Update.fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

theorem dependency_tighten :
    Lara.Update.applyUpdate registryEx dependencySource (.tighten applicabilityKey) =
      .ok dependencyTarget := by decide

theorem dependency_prune_exact :
    dependencyTargetRun.admission.prune.checkedLeaves = [(l2, pA), (l3, pA)] ∧
    dependencyTargetRun.admission.prune.keptArgs =
      [("selected", .leaf l2), ("alternative", .leaf l3)] := by decide

theorem dependency_named_pruned :
    ("applicability", SupportTerm.leaf l1) ∈ dependencyTarget.argsRaw ∧
    ("applicability", SupportTerm.leaf l1) ∉ dependencyTargetRun.admission.prune.keptArgs ∧
    Admission.buildGamma dependencyTargetRun.admission.prune.checkedLeaves l1 = none := by decide

theorem dependency_source_support :
    HasSupport id dependencySource.policy.ruleLookup
      (Admission.buildGamma dependencySource.leaves) (certOkOf registryEx)
      (.leaf l1) pC [] := .leaf (by rfl)

theorem dependency_target_no_support :
    ¬ ∃ conclusion obligations,
      HasSupport id dependencyTarget.policy.ruleLookup
        (Admission.buildGamma dependencyTargetRun.admission.prune.checkedLeaves)
        (certOkOf registryEx) (.leaf l1) conclusion obligations := by
  rintro ⟨conclusion, obligations, typed⟩
  have declared := Support.leaves_declared typed l1 (by simp [Support.leaves])
  rcases declared with ⟨proposition, present⟩
  have missing := dependency_named_pruned.2.2
  rw [missing] at present
  cases present

theorem dependency_alternative_support :
    HasSupport id dependencyTarget.policy.ruleLookup
      (Admission.buildGamma dependencyTargetRun.admission.prune.checkedLeaves)
      (certOkOf registryEx) (.leaf l3) pA [] := .leaf (by rfl)

theorem dependency_alternative_eligible :
    Grounded.labelC (Compile.checkedAF dependencyTargetRun.checked.program) 1 = .inn ∧
    2 ∉ Lara.Update.blockedSetForRun dependencyTargetRun ∧
    ordinaryStatus dependencyTargetRun pA = .published .justified := by decide

theorem dependency_source_published :
    ordinaryStatus dependencySourceRun pA = .published .justified := by decide

/-- Adding a fresh unrelated admitted leaf changes the complete source, not its graph. -/
def harmlessSource : Lara.Update.SourceState :=
  { sigma := sigmaEx
    policy := unitPolicyEx
    table := []
    metas := [{ id := l1, kind := .observed, provenance := .user },
      { id := l2, kind := .observed, provenance := .user }]
    leaves := [(l1, pA), (l2, pB)]
    argsRaw := [("selected", .leaf l1)]
    rawAtts := []
    groups := []
    ground := groundEx }

def harmlessMeta : Admission.LeafMeta :=
  { id := l3, kind := .observed, provenance := .user }

def harmlessTarget : Lara.Update.SourceState :=
  { harmlessSource with
    metas := harmlessSource.metas ++ [harmlessMeta]
    leaves := harmlessSource.leaves ++ [(l3, pC)] }

def harmlessSourceRun : Examples.Update.AcceptedRun harmlessSource :=
  Examples.Update.fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

def harmlessTargetRun : Examples.Update.AcceptedRun harmlessTarget :=
  Examples.Update.fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

theorem harmless_addLeaf :
    Lara.Update.applyUpdate registryEx harmlessSource (.addLeaf l3 pC harmlessMeta) =
      .ok harmlessTarget := by decide

theorem harmless_source_distinct : harmlessSource ≠ harmlessTarget := by
  intro equal
  have lengths := congrArg (fun state : Lara.Update.SourceState => state.leaves.length) equal
  change 2 = 3 at lengths
  exact absurd lengths (by decide)

theorem harmless_fresh_unrelated :
    l3 ∉ harmlessSource.leaves.map Prod.fst ∧
    l3 ∉ harmlessSource.metas.map Admission.LeafMeta.id ∧
    l3 ∉ Support.leaves (SupportTerm.leaf l1) ∧
    harmlessSource.groups = [] ∧ harmlessTarget.groups = [] ∧
    harmlessSource.rawAtts = [] ∧ harmlessTarget.rawAtts = [] := by decide

theorem harmless_carriers :
    harmlessSourceRun.admission.prune.keptArgs = harmlessTargetRun.admission.prune.keptArgs ∧
    harmlessSourceRun.checked.program.args = harmlessTargetRun.checked.program.args ∧
    harmlessSourceRun.checked.program.atts = harmlessTargetRun.checked.program.atts := by decide

theorem harmless_context_transport :
    ∀ leaf ∈ Support.leaves (SupportTerm.leaf l1),
      Admission.buildGamma harmlessSourceRun.admission.prune.checkedLeaves leaf =
        Admission.buildGamma harmlessTargetRun.admission.prune.checkedLeaves leaf := by
  intro leaf member
  have equal : leaf = l1 := by simpa [Support.leaves] using member
  subst leaf
  rfl

theorem harmless_statuses :
    ordinaryStatus harmlessSourceRun pA = .published .justified ∧
    ordinaryStatus harmlessTargetRun pA = .published .justified := by decide

theorem harmless_source_program_args :
    harmlessSourceRun.checked.program.args = [SupportTerm.leaf l1] := by
  have sound := Check.Unit.checkUnit_sound harmlessSourceRun.check_ok
  have complete : ∀ w ∈ [SupportTerm.leaf l1], ∃ C, HasSupport id unitPolicyEx.ruleLookup
      (Admission.buildGamma harmlessSourceRun.admission.prune.checkedLeaves)
      (certOkOf registryEx) w C [] := by
    intro w member
    have equal : w = SupportTerm.leaf l1 := by simpa using member
    subst w
    exact ⟨pA, .leaf (by decide)⟩
  rw [sound.args_eq_of_complete complete]
  rfl

theorem harmless_target_program_args :
    harmlessTargetRun.checked.program.args = [SupportTerm.leaf l1] := by
  have sound := Check.Unit.checkUnit_sound harmlessTargetRun.check_ok
  have complete : ∀ w ∈ [SupportTerm.leaf l1], ∃ C, HasSupport id unitPolicyEx.ruleLookup
      (Admission.buildGamma harmlessTargetRun.admission.prune.checkedLeaves)
      (certOkOf registryEx) w C [] := by
    intro w member
    have equal : w = SupportTerm.leaf l1 := by simpa using member
    subst w
    exact ⟨pA, .leaf (by decide)⟩
  rw [sound.args_eq_of_complete complete]
  rfl

theorem harmless_program_args :
    harmlessSourceRun.checked.program.args = harmlessTargetRun.checked.program.args := by
  rw [harmless_source_program_args, harmless_target_program_args]

theorem harmless_source_program_atts : harmlessSourceRun.checked.program.atts = [] := by
  have sound := Check.Unit.checkUnit_sound harmlessSourceRun.check_ok
  have complete : ∀ w ∈ [SupportTerm.leaf l1], ∃ C, HasSupport id unitPolicyEx.ruleLookup
      (Admission.buildGamma harmlessSourceRun.admission.prune.checkedLeaves)
      (certOkOf registryEx) w C [] := by
    intro w member
    have equal : w = SupportTerm.leaf l1 := by simpa using member
    subst w
    exact ⟨pA, .leaf (by decide)⟩
  rw [sound.atts_eq_of_complete complete]
  rfl

theorem harmless_target_program_atts : harmlessTargetRun.checked.program.atts = [] := by
  have sound := Check.Unit.checkUnit_sound harmlessTargetRun.check_ok
  have complete : ∀ w ∈ [SupportTerm.leaf l1], ∃ C, HasSupport id unitPolicyEx.ruleLookup
      (Admission.buildGamma harmlessTargetRun.admission.prune.checkedLeaves)
      (certOkOf registryEx) w C [] := by
    intro w member
    have equal : w = SupportTerm.leaf l1 := by simpa using member
    subst w
    exact ⟨pA, .leaf (by decide)⟩
  rw [sound.atts_eq_of_complete complete]
  rfl

theorem harmless_program_atts :
    harmlessSourceRun.checked.program.atts = harmlessTargetRun.checked.program.atts := by
  rw [harmless_source_program_atts, harmless_target_program_atts]

theorem harmless_sink_embedding :
    Grounded.SinkEmbedding (Compile.checkedAF harmlessSourceRun.checked.program)
      (Compile.checkedAF harmlessTargetRun.checked.program) id [] :=
  sinkEmbedding_of_checked_agree harmlessSourceRun harmlessTargetRun
    harmless_program_args harmless_program_atts

theorem harmless_all_labels_preserved (node : Nat)
    (member : node ∈ (Compile.checkedAF harmlessSourceRun.checked.program).args) :
    Grounded.labelC (Compile.checkedAF harmlessTargetRun.checked.program) node =
      Grounded.labelC (Compile.checkedAF harmlessSourceRun.checked.program) node :=
  harmless_sink_embedding.label_old member

/-- A defender is quarantined, exposing the surviving attacker of the method argument. -/
def defenseSource : Lara.Update.SourceState :=
  { sigma := sigmaEx
    policy := { unitPolicyEx with defeat := ⟨[(⟨⟨"q"⟩, .nil⟩, ⟨⟨"p"⟩, .nil⟩),
      (⟨⟨"s"⟩, .nil⟩, ⟨⟨"q"⟩, .nil⟩)], []⟩ }
    table := []
    metas := [{ id := l1, kind := .observed, provenance := .user },
      { id := l2, kind := .observed, provenance := .user },
      { id := l3, kind := .attested, provenance := .user }]
    leaves := [(l1, pA), (l2, pB), (l3, pC)]
    argsRaw := [("selected", .leaf l1), ("attacker", .leaf l2), ("defender", .leaf l3)]
    rawAtts := [.undermine "defender" "attacker" [], .undermine "attacker" "selected" []]
    groups := []
    ground := groundEx }

def defenseTarget : Lara.Update.SourceState :=
  { defenseSource with table := [{ key := applicabilityKey, decision := .quarantine }] }

def defenseSourceRun : Examples.Update.AcceptedRun defenseSource :=
  Examples.Update.fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

def defenseTargetRun : Examples.Update.AcceptedRun defenseTarget :=
  Examples.Update.fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

theorem defense_loss_update :
    Lara.Update.applyUpdate registryEx defenseSource (.tighten applicabilityKey) =
      .ok defenseTarget := by decide

theorem defense_loss_full_status :
    ordinaryStatus defenseSourceRun pA = .published .justified ∧
    ordinaryStatus defenseTargetRun pA = .evidenceBlocked .defeated := by decide

/-- A source can be accepted while the selected claim is defeated. -/
def defeatedSource : Lara.Update.SourceState :=
  { defenseSource with
    metas := [{ id := l1, kind := .observed, provenance := .user },
      { id := l2, kind := .observed, provenance := .user }]
    leaves := [(l1, pA), (l2, pB)]
    argsRaw := [("selected", .leaf l1), ("attacker", .leaf l2)]
    rawAtts := [.undermine "attacker" "selected" []] }

def defeatedSourceRun : Examples.Update.AcceptedRun defeatedSource :=
  Examples.Update.fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

theorem defeated_source_status :
    ordinaryStatus defeatedSourceRun pA = .published .defeated := by decide

theorem rejected_duplicate_leaf :
    Lara.Update.applyUpdate registryEx harmlessSource (.addLeaf l1 pC harmlessMeta) =
      .error (.leafNotFresh l1) := by rfl

def evidenceAtom : Atom := .atom "result" (.cons (.num "7") .nil)

def csvMetadata : Evidence.ObjectMeta :=
  ⟨⟨"data"⟩, ⟨"data.csv"⟩, 12,
    ⟨"sha256:0000000000000000000000000000000000000000000000000000000000000000"⟩⟩

def csvRequest : Evidence.ExtractionRequest :=
  .csvRowRequest ⟨1⟩ ⟨"data"⟩ ⟨"id"⟩ "one" [⟨⟨"value"⟩, .decimal⟩] "result"

def csvObject : Evidence.CapturedObject :=
  ⟨csvMetadata, .csv ⟨[⟨"id"⟩, ⟨"value"⟩], [["one", "7.00"]]⟩⟩

def csvSnapshot : Evidence.Snapshot := [(⟨"data"⟩, .ok csvObject)]

def csvManifest : List Evidence.ObjectMeta := [csvMetadata]

def csvLeaf : Presentation.Leaf :=
  ⟨⟨"measured"⟩, evidenceAtom, .certified, .checker "csv-row" "1",
    [⟨"data.csv"⟩], some csvRequest⟩

def certifiedPolicy : Presentation.Policy :=
  { id := ⟨"bridge-evidence"⟩
    sigma := ⟨[], [], [⟨⟨"result"⟩, [.num]⟩]⟩
    rules := []
    contraries := []
    exceptions := []
    admission := []
    theories := []
    groupMode := .quarantineOnConflict
    measurands := []
    comparisonSchemes := []
    evidenceCheckers := [(.csvRow, ⟨1⟩)] }

def certifiedInput : Surface.Input :=
  { program :=
      { artifact := "bridge-certified-csv"
        digest := ⟨"sha256:bridge-certified-csv"⟩
        policy := certifiedPolicy.id
        backends := []
        valueBindings := []
        decls := [.leaf csvLeaf,
          .claim ⟨⟨"method"⟩, "Captured result used by the conditional method artifact",
            evidenceAtom, ⟨"author", "explicit modeled interpretation", .reviewed⟩⟩,
          .arg ⟨⟨"selected"⟩, .supportsClaim ⟨"method"⟩,
            .explicitTheta (.leaf csvLeaf.id)⟩] }
    policy := certifiedPolicy }

theorem certified_declared_claim :
    Surface.claimFormal? certifiedInput.program ⟨"method"⟩ = some evidenceAtom := by decide

def certifiedEnv : Surface.Env canonNum :=
  { registry := fun _ => none
    startsIdent := fun _ => false
    startsIdent_nat_false := fun _ => rfl
    encodeProp := fun text =>
      (Surface.parseSurfaceProp text).map (fun proposition =>
        Strict.encodeAtomKey (nf canonNum proposition)) }

def certifiedResult :=
  Surface.sourceWithEvidence certifiedEnv certifiedInput csvSnapshot csvManifest Evidence.extract

theorem certified_result_success : certifiedResult.isOk = true := by decide +kernel

def certifiedPair : Surface.Elaborated canonNum × List Evidence.Judgment :=
  certifiedResult.toOption.get (by
    cases h : certifiedResult with
    | error error => exact Bool.noConfusion (h ▸ certified_result_success)
    | ok result => rfl)

theorem certified_source_success :
    Surface.sourceWithEvidence certifiedEnv certifiedInput csvSnapshot csvManifest Evidence.extract =
      .ok (certifiedPair.1, certifiedPair.2) := by
  change certifiedResult = .ok (certifiedPair.1, certifiedPair.2)
  cases h : certifiedResult with
  | error error =>
    exact Bool.noConfusion (h ▸ certified_result_success)
  | ok result =>
    have pair : certifiedPair = result := by
      unfold certifiedPair
      apply Option.get_of_eq_some
      exact congrArg Except.toOption h
    rw [pair]

theorem certified_extraction_exact :
    Evidence.run csvSnapshot Evidence.extract csvRequest =
      .ok ⟨evidenceAtom, [csvMetadata]⟩ := by decide

theorem certified_request_bound :
    Evidence.RequestBound certifiedPolicy.evidenceCheckers csvManifest csvLeaf csvRequest := by decide

theorem certified_semantic_admission :
    Evidence.Admitted csvSnapshot certifiedInput.policy.evidenceCheckers csvManifest Evidence.extract
      (Surface.leafRecords certifiedPair.1.semanticProgram) certifiedPair.2 :=
  Surface.sourceWithEvidence_semantic certified_source_success

theorem certified_same_declared_leaf :
    Surface.leafRecords certifiedPair.1.semanticProgram = [csvLeaf] := by decide +kernel

theorem certified_claim_carriers :
    Surface.claimFormal? certifiedPair.1.semanticProgram ⟨"method"⟩ = some evidenceAtom ∧
      certifiedPair.1.claimAlternatives = [(⟨"method"⟩, [0])] ∧
      certifiedPair.1.argIds = [⟨"selected"⟩] := by decide +kernel

theorem certified_same_source_witness :
    ∃ request, Evidence.RequestBound certifiedInput.policy.evidenceCheckers csvManifest csvLeaf request ∧
      ∃ judgment ∈ certifiedPair.2, judgment.leaf = csvLeaf.id.val ∧ judgment.request = request ∧
        ∃ result, Evidence.run csvSnapshot Evidence.extract request = .ok result ∧
          judgment.normalized = nf canonNum csvLeaf.prop := by
  apply Evidence.package_same_source_witness certified_source_success
  · rw [certified_same_declared_leaf]
    simp
  · rfl

/-- JSON replay is another real selector, not an oracle for the BHL postcondition. -/
def jsonMetadata : Evidence.ObjectMeta :=
  ⟨⟨"json"⟩, ⟨"data.json"⟩, 11,
    ⟨"sha256:0000000000000000000000000000000000000000000000000000000000000000"⟩⟩

def jsonRequest : Evidence.ExtractionRequest :=
  .jsonPointerRequest ⟨1⟩ ⟨"json"⟩ [⟨[⟨"value"⟩], .decimal⟩] "result"

def jsonObject : Evidence.CapturedObject :=
  ⟨jsonMetadata, .json (.object (.cons ⟨"value"⟩ (.number "7.00") .nil))⟩

theorem json_extraction_exact :
    Evidence.run [(⟨"json"⟩, .ok jsonObject)] Evidence.extract jsonRequest =
      .ok ⟨evidenceAtom, [jsonMetadata]⟩ := by decide

def quarantinedCertifiedInput : Surface.Input :=
  { certifiedInput with policy :=
    { certifiedPolicy with admission := [((.certified, .checker "csv-row" "1"), .quarantine)] } }

def quarantinedCertifiedResult :=
  Surface.sourceWithEvidence certifiedEnv quarantinedCertifiedInput csvSnapshot csvManifest Evidence.extract

theorem quarantined_certified_success : quarantinedCertifiedResult.isOk = true := by decide +kernel

def quarantinedCertifiedPair : Surface.Elaborated canonNum × List Evidence.Judgment :=
  quarantinedCertifiedResult.toOption.get (by
    cases h : quarantinedCertifiedResult with
    | error error => exact Bool.noConfusion (h ▸ quarantined_certified_success)
    | ok result => rfl)

theorem quarantined_certified_source_success :
    Surface.sourceWithEvidence certifiedEnv quarantinedCertifiedInput csvSnapshot csvManifest
      Evidence.extract = .ok (quarantinedCertifiedPair.1, quarantinedCertifiedPair.2) := by
  change quarantinedCertifiedResult = .ok (quarantinedCertifiedPair.1, quarantinedCertifiedPair.2)
  cases h : quarantinedCertifiedResult with
  | error error =>
    exact Bool.noConfusion (h ▸ quarantined_certified_success)
  | ok result =>
    have pair : quarantinedCertifiedPair = result := by
      unfold quarantinedCertifiedPair
      apply Option.get_of_eq_some
      exact congrArg Except.toOption h
    rw [pair]

theorem quarantined_evidence_admitted :
    Evidence.Admitted csvSnapshot quarantinedCertifiedInput.policy.evidenceCheckers csvManifest
      Evidence.extract (Surface.leafRecords quarantinedCertifiedPair.1.semanticProgram)
      quarantinedCertifiedPair.2 :=
  Surface.sourceWithEvidence_semantic quarantined_certified_source_success

theorem evidence_cannot_admit_quarantined :
    Surface.leafRecords quarantinedCertifiedPair.1.semanticProgram = [csvLeaf] ∧
    quarantinedCertifiedPair.1.gamma ⟨"measured"⟩ = none ∧
    quarantinedCertifiedPair.1.unit.args = [] ∧
    quarantinedCertifiedPair.1.unit.atts = [] := by decide +kernel

theorem evidence_independent_of_ordinary_quarantine :
    Evidence.Admitted csvSnapshot quarantinedCertifiedInput.policy.evidenceCheckers csvManifest
        Evidence.extract (Surface.leafRecords quarantinedCertifiedPair.1.semanticProgram)
        quarantinedCertifiedPair.2 ∧
      quarantinedCertifiedPair.1.gamma ⟨"measured"⟩ = none ∧
      quarantinedCertifiedPair.1.unit.args = [] :=
  ⟨quarantined_evidence_admitted, evidence_cannot_admit_quarantined.2.1,
    evidence_cannot_admit_quarantined.2.2.1⟩

def certifiedAudit : Lara.Surface.ElaboratedWithAudit canonNum :=
  (Lara.Surface.elaborateWithAudit certifiedEnv certifiedInput).toOption.get (by decide +kernel)

theorem certified_audit_success :
    Lara.Surface.elaborateWithAudit certifiedEnv certifiedInput = .ok certifiedAudit :=
  except_toOption_get_exact _ _

theorem certified_audit_output : certifiedAudit.output = certifiedPair.1 := by
  have core := Surface.sourceWithEvidence_core_and_semantic certified_source_success
  have checks := Surface.check_sound certifiedEnv certifiedInput certifiedPair.1 core.1
  have complete := Surface.elaborate_complete certifiedEnv certifiedInput certifiedPair.1 checks
  simpa [Surface.elaborate, certified_audit_success, Except.map] using complete

def certifiedState := sourceStateOfAudit certifiedInput certifiedAudit

@[macro_inline]
def certifiedRun : Lara.Update.AcceptedRun certifiedEnv.registry certifiedState :=
  acceptedRunOfSource certifiedAudit certified_source_success certified_audit_success certified_audit_output

def certifiedMaterial : EvidenceMaterial :=
  ⟨certifiedInput, csvSnapshot, csvManifest, certifiedPair.1.ground⟩

@[macro_inline]
def certifiedSource : CertifiedSource Evidence.extract certifiedRun certifiedMaterial :=
  certifiedSourceOfSource certifiedAudit certified_source_success certified_audit_success certified_audit_output

theorem certified_run_alignment :
    SourceAlignment certifiedRun certifiedEnv certifiedInput certifiedAudit certifiedPair.1 :=
  acceptedRunOfSource_alignment certifiedAudit certified_source_success
    certified_audit_success certified_audit_output

theorem certified_raw_exact :
    certifiedState.leaves = [(⟨"measured"⟩, evidenceAtom)] ∧
    certifiedState.metas = [⟨⟨"measured"⟩, .certified, .checker "csv-row" "1"⟩] ∧
    certifiedState.argsRaw = [("selected", .leaf ⟨"measured"⟩)] ∧
    certifiedState.rawAtts = [] ∧ certifiedState.groups = [] ∧
    certifiedState.ground = certifiedPair.1.ground := by decide +kernel

def harmlessSelected : SupportRef := ⟨0, ("selected", .leaf l1), pA, pA, 0⟩
def dependencySelected : SupportRef := ⟨0, ("selected", .leaf l2), pA, pA, 0⟩
def dependencyApplicability : SupportRef := ⟨1, ("applicability", .leaf l1), pC, pC, 1⟩
def dependencyAlternative : SupportRef := ⟨2, ("alternative", .leaf l3), pA, pA, 1⟩
def certifiedSelected : SupportRef :=
  ⟨0, ("selected", .leaf ⟨"measured"⟩), evidenceAtom, evidenceAtom, 0⟩

/-- Only closed mathematical codes are authored; eligibility is recomputed from each run. -/
def bindingFor (source : Lara.Update.SourceState) (selected : SupportRef)
    (dependencies : List SupportRef) (method : CheckedMethods.Method)
    (mode : PayloadMode) (evidence : Option EvidenceMaterial := none) : ArtifactBinding :=
  { source := source, claim := ⟨"method"⟩, origin := .authored, query := selected.query
    interpretation := ClaimInterpretation.ofMode mode method
    selected := selected, dependencies := dependencies
    method := method, canonical := method.binding
    request := method.request 0 true true
    residual := [.interpretationFidelity, .physicalSampling, .captureAdequacy, .runtimeRefinement]
    coverage := .completeModeled, mode := mode, evidence := evidence }

def harmlessBinding : ArtifactBinding :=
  bindingFor harmlessSource harmlessSelected [] .two .conditional

def harmlessTargetBinding : ArtifactBinding :=
  bindingFor harmlessTarget harmlessSelected [] .two .conditional

def appliedBinding : ArtifactBinding :=
  bindingFor harmlessSource harmlessSelected [] .two .applied

def falsePreconditionBinding : ArtifactBinding :=
  bindingFor harmlessSource harmlessSelected [] .conditionalFalse .conditional

def falsePreconditionAppliedBinding : ArtifactBinding :=
  bindingFor harmlessSource harmlessSelected [] .conditionalFalse .applied

@[macro_inline]
def harmlessCertificate : BridgeCertificate registryEx Evidence.extract :=
  { binding := harmlessBinding
    run := harmlessSourceRun
    association := .authored rfl rfl rfl
    raw := by
      intro ref member
      have equal : ref = harmlessSelected := by
        simpa [ArtifactBinding.supports, harmlessBinding, bindingFor] using member
      subst ref
      exact ⟨rfl, .leaf (by rfl), rfl⟩
    evidence := .ordinary (by
      intro metadata member
      change metadata ∈ harmlessSource.metas at member
      simp [harmlessSource] at member
      rcases member with rfl | rfl <;> decide) }

@[macro_inline]
def harmlessTargetCertificate : BridgeCertificate registryEx Evidence.extract :=
  { binding := harmlessTargetBinding
    run := harmlessTargetRun
    association := .authored rfl rfl rfl
    raw := by
      intro ref member
      have equal : ref = harmlessSelected := by
        simpa [ArtifactBinding.supports, harmlessTargetBinding, bindingFor] using member
      subst ref
      exact ⟨rfl, .leaf (by rfl), rfl⟩
    evidence := .ordinary (by
      intro metadata member
      change metadata ∈ harmlessTarget.metas at member
      simp [harmlessTarget, harmlessSource, harmlessMeta] at member
      rcases member with rfl | rfl | rfl <;> decide) }

@[macro_inline]
def appliedCertificate : BridgeCertificate registryEx Evidence.extract :=
  { binding := appliedBinding
    run := harmlessSourceRun
    association := .authored rfl rfl rfl
    raw := by
      intro ref member
      have equal : ref = harmlessSelected := by
        simpa [ArtifactBinding.supports, appliedBinding, bindingFor] using member
      subst ref
      exact ⟨rfl, .leaf (by rfl), rfl⟩
    evidence := harmlessCertificate.evidence }

@[macro_inline]
def falsePreconditionCertificate : BridgeCertificate registryEx Evidence.extract :=
  { binding := falsePreconditionBinding
    run := harmlessSourceRun
    association := .authored rfl rfl rfl
    raw := by
      intro ref member
      have equal : ref = harmlessSelected := by
        simpa [ArtifactBinding.supports, falsePreconditionBinding, bindingFor] using member
      subst ref
      exact ⟨rfl, .leaf (by rfl), rfl⟩
    evidence := harmlessCertificate.evidence }

@[macro_inline]
def falsePreconditionAppliedCertificate : BridgeCertificate registryEx Evidence.extract :=
  { binding := falsePreconditionAppliedBinding
    run := harmlessSourceRun
    association := .authored rfl rfl rfl
    raw := by
      intro ref member
      have equal : ref = harmlessSelected := by
        simpa [ArtifactBinding.supports, falsePreconditionAppliedBinding, bindingFor] using member
      subst ref
      exact ⟨rfl, .leaf (by rfl), rfl⟩
    evidence := harmlessCertificate.evidence }

theorem conditional_bridge_success :
    (checkBridge harmlessBinding harmlessCertificate).isOk = true := by decide

theorem applied_bridge_success :
    (checkBridge appliedBinding appliedCertificate).isOk = true := by decide

theorem harmless_stale_certificate :
    checkBridge harmlessTargetBinding harmlessCertificate = .error .staleSnapshot :=
  checkBridge_stale _ _ harmless_source_distinct

theorem harmless_fresh_certificate :
    (checkBridge harmlessTargetBinding harmlessTargetCertificate).isOk = true := by decide

theorem incompatible_method_copy :
    checkBridge { harmlessBinding with method := .low } harmlessCertificate =
      .error .incompatibleMethod := by rfl

theorem incompatible_interpretation_copy :
    checkBridge { harmlessBinding with interpretation := .conditional .low } harmlessCertificate =
      .error .incompatibleInterpretation := by rfl

theorem incompatible_dependency_copy :
    checkBridge { harmlessBinding with dependencies := [harmlessSelected] } harmlessCertificate =
      .error .incompatibleDependencies := by rfl

theorem incompatible_claim_copy :
    checkBridge { harmlessBinding with claim := ⟨"unknown-method"⟩ } harmlessCertificate =
      .error .incompatibleClaim := by rfl

theorem incompatible_origin_copy :
    checkBridge { harmlessBinding with origin := .declared ⟨"selected"⟩ } harmlessCertificate =
      .error .incompatibleClaim := by rfl

def dependencyBinding :=
  bindingFor dependencySource dependencySelected [dependencyApplicability] .two .conditional

def dependencyTargetBinding :=
  bindingFor dependencyTarget dependencySelected [dependencyApplicability] .two .conditional

@[macro_inline]
def dependencyCertificate : BridgeCertificate registryEx Evidence.extract :=
  { binding := dependencyBinding
    run := dependencySourceRun
    association := .authored rfl rfl rfl
    raw := by
      intro ref member
      simp only [ArtifactBinding.supports, dependencyBinding, bindingFor,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨rfl, .leaf (by rfl), rfl⟩
      · exact ⟨rfl, .leaf (by rfl), rfl⟩
    evidence := .ordinary (by
      intro metadata member
      change metadata ∈ dependencySource.metas at member
      simp [dependencySource] at member
      rcases member with rfl | rfl | rfl <;> decide) }

@[macro_inline]
def dependencyTargetCertificate : BridgeCertificate registryEx Evidence.extract :=
  { binding := dependencyTargetBinding
    run := dependencyTargetRun
    association := .authored rfl rfl rfl
    raw := by
      intro ref member
      exact tighten_raw_support_preserved dependency_tighten
        (dependencyCertificate.raw ref member)
    evidence := .ordinary (by
      intro metadata member
      change metadata ∈ dependencyTarget.metas at member
      simp [dependencyTarget, dependencySource] at member
      rcases member with rfl | rfl | rfl <;> decide) }

theorem dependency_bridge_source_success :
    (checkBridge dependencyBinding dependencyCertificate).isOk = true := by decide

theorem dependency_bridge_target_failure :
    checkBridge dependencyTargetBinding dependencyTargetCertificate = .error .missingSupport := by rfl

theorem dependency_conditional_unchanged :
    ConditionalMethod dependencyBinding ∧ ConditionalMethod dependencyTargetBinding :=
  ⟨CheckedMethods.method_valid .two, CheckedMethods.method_valid .two⟩

theorem dependency_target_no_warrant :
    ¬ ArtifactWarrant dependencyTargetBinding dependencyTargetRun := by
  intro warrant
  have dependency := warrant dependencyApplicability (by
    simp [ArtifactBinding.supports, dependencyTargetBinding, bindingFor])
  exact dependency_named_pruned.2.1 dependency.retained

def alternativeBinding :=
  bindingFor dependencyTarget dependencyAlternative [] .two .conditional

@[macro_inline]
def alternativeCertificate : BridgeCertificate registryEx Evidence.extract :=
  { binding := alternativeBinding
    run := dependencyTargetRun
    association := .authored rfl rfl rfl
    raw := by
      intro ref member
      have equal : ref = dependencyAlternative := by
        simpa [ArtifactBinding.supports, alternativeBinding, bindingFor] using member
      subst ref
      exact ⟨rfl, .leaf (by rfl), rfl⟩
    evidence := dependencyTargetCertificate.evidence }

theorem independent_alternative_bridge_success :
    (checkBridge alternativeBinding alternativeCertificate).isOk = true := by decide

def defenseBinding :=
  bindingFor defenseTarget harmlessSelected [] .two .conditional

@[macro_inline]
def defenseCertificate : BridgeCertificate registryEx Evidence.extract :=
  { binding := defenseBinding
    run := defenseTargetRun
    association := .authored rfl rfl rfl
    raw := by
      intro ref member
      have equal : ref = harmlessSelected := by
        simpa [ArtifactBinding.supports, defenseBinding, bindingFor] using member
      subst ref
      exact ⟨rfl, .leaf (by rfl), rfl⟩
    evidence := .ordinary (by
      intro metadata member
      change metadata ∈ defenseTarget.metas at member
      simp [defenseTarget, defenseSource] at member
      rcases member with rfl | rfl | rfl <;> decide) }

theorem blocked_bridge_failure :
    checkBridge defenseBinding defenseCertificate = .error .blockedSupport := by rfl

def defeatedBinding :=
  bindingFor defeatedSource harmlessSelected [] .two .conditional

@[macro_inline]
def defeatedCertificate : BridgeCertificate registryEx Evidence.extract :=
  { binding := defeatedBinding
    run := defeatedSourceRun
    association := .authored rfl rfl rfl
    raw := by
      intro ref member
      have equal : ref = harmlessSelected := by
        simpa [ArtifactBinding.supports, defeatedBinding, bindingFor] using member
      subst ref
      exact ⟨rfl, .leaf (by rfl), rfl⟩
    evidence := .ordinary (by
      intro metadata member
      change metadata ∈ defeatedSource.metas at member
      simp [defeatedSource] at member
      rcases member with rfl | rfl <;> decide) }

theorem defeated_bridge_failure :
    checkBridge defeatedBinding defeatedCertificate = .error .defeatedSupport := by rfl

def certifiedBinding :=
  { bindingFor certifiedState certifiedSelected [] .two .conditional (some certifiedMaterial) with
    origin := .declared ⟨"selected"⟩ }

private theorem sourceAuditProjection
    {env : Surface.Env canonNum} {input snapshot manifest registry output judgments}
    (audit : Surface.ElaboratedWithAudit canonNum)
    (source : Surface.sourceWithEvidence env input snapshot manifest registry = .ok (output, judgments))
    (audited : Surface.elaborateWithAudit env input = .ok audit)
    (sameOutput : audit.output = output) :
    (certifiedSourceOfSource audit source audited sameOutput).audit = audit := rfl

private theorem certifiedSourceAudit : certifiedSource.audit = certifiedAudit :=
  sourceAuditProjection certifiedAudit certified_source_success certified_audit_success certified_audit_output

@[macro_inline]
def certifiedCertificate : BridgeCertificate certifiedEnv.registry Evidence.extract :=
  { binding := certifiedBinding
    run := certifiedRun
    association := by
      refine ClaimAssociation.declared (binding := certifiedBinding) (run := certifiedRun)
        (registry := Evidence.extract) (material := certifiedMaterial)
        ⟨"selected"⟩ ?_ ?_ certifiedSource ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · decide +kernel
      · rw [certifiedSourceAudit]
        change ∃ pair, certifiedAudit.declared.pairs[0]? = some pair ∧
          pair.argument.id = ⟨"selected"⟩ ∧ pair.core = .leaf ⟨"measured"⟩ ∧
          Surface.argSupportsClaim ⟨"method"⟩ pair.argument.concl = true
        refine ⟨(certifiedAudit.declared.pairs[0]?).get (by decide +kernel), ?_, ?_, ?_, ?_⟩
        · exact (Option.some_get _).symm
        all_goals decide +kernel
      · decide +kernel
      · exact ⟨[0], by decide +kernel, by decide +kernel⟩
      · decide +kernel
    raw := by
      intro ref member
      change ref ∈ [certifiedSelected] at member
      have equal := List.mem_singleton.mp member
      subst ref
      exact ⟨by decide +kernel, .leaf (by decide +kernel), by decide +kernel⟩
    evidence := .certified certifiedSource }

theorem certified_bridge_success :
    (checkBridge certifiedBinding certifiedCertificate).isOk = true := by decide +kernel

theorem certified_declared_association : ClaimAssociation certifiedBinding certifiedRun :=
  certifiedCertificate.association

private theorem checkBridgeMismatch {canon : String → String} {reg : BackendRegistry canon}
    {evidenceRegistry : Evidence.Registry} (expected : ArtifactBinding)
    (certificate : BridgeCertificate reg evidenceRegistry)
    (sameSource : certificate.binding.source = expected.source)
    (different : certificate.binding ≠ expected)
    (error : bindingError expected certificate.binding = .incompatibleClaim) :
    checkBridge expected certificate = .error .incompatibleClaim := by
  unfold checkBridge
  rw [dif_pos sameSource, dif_neg different, error]

theorem certified_unknown_claim_copy :
    checkBridge { certifiedBinding with claim := ⟨"unknown-method"⟩ } certifiedCertificate =
      .error .incompatibleClaim :=
  checkBridgeMismatch { certifiedBinding with claim := ⟨"unknown-method"⟩ } certifiedCertificate
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def falsePreconditionBound : BoundCertificate falsePreconditionCertificate :=
  (checkBound falsePreconditionCertificate).toOption.get (by decide)

theorem supported_applicability_false_precondition :
    ordinaryStatus harmlessSourceRun pA = .published .justified ∧
    ¬ satisfies (falsePreconditionBinding).canonical.model.context.interpretation
      (falsePreconditionBinding).canonical.model.context.model GhostEnv.empty
      ((falsePreconditionBinding).request.before.world 0 true true)
      (falsePreconditionBinding).canonical.pre.assertion :=
  supported_applicability_without_truth falsePreconditionBinding harmlessSourceRun
    (falsePreconditionBound.meaning).warrant rfl

theorem false_precondition_conditional_success :
    (checkBridge falsePreconditionBinding falsePreconditionCertificate).isOk = true := by decide

theorem false_precondition_applied_failure :
    checkBridge falsePreconditionAppliedBinding falsePreconditionAppliedCertificate =
      .error .falsePrecondition := by rfl

theorem false_precondition_no_modeled_application :
    ¬ ModeledApplication falsePreconditionAppliedBinding := by
  intro application
  exact CheckedMethods.conditional_false_not_applicable
    falsePreconditionAppliedBinding.request application.initial

theorem complete_observation_projection :
    harmlessCertificate.ordinary [pA, pB] =
      observeOrdinary harmlessSourceRun [pA, pB] := rfl

def harmlessBound : BoundCertificate harmlessCertificate :=
  (checkBound harmlessCertificate).toOption.get (by decide)

theorem harmless_reference_warrant :
    ArtifactWarrant harmlessBinding harmlessSourceRun :=
  (harmlessBound.meaning).warrant

def harmlessTransport :
    RebindConditions harmlessCertificate harmlessTargetRun id id [] none :=
  { rawInjective := fun _ _ equal => equal
    checkedInjective := fun _ _ equal => equal
    policy := rfl
    leafMaterial := by
      intro ref member leaf used
      have equal : ref = harmlessSelected := by
        simpa [harmlessCertificate, ArtifactBinding.supports, harmlessBinding, bindingFor] using member
      subst ref
      have equal : leaf = l1 := by simpa [harmlessSelected, Support.leaves] using used
      subst leaf
      rfl
    occurrence := by
      intro ref member
      have equal : ref = harmlessSelected := by
        simpa [harmlessCertificate, ArtifactBinding.supports, harmlessBinding, bindingFor] using member
      subst ref
      rfl
    retained := by
      intro ref member
      have equal : ref = harmlessSelected := by
        simpa [harmlessCertificate, ArtifactBinding.supports, harmlessBinding, bindingFor] using member
      subst ref
      decide
    node := by
      intro ref member
      have equal : ref = harmlessSelected := by
        simpa [harmlessCertificate, ArtifactBinding.supports, harmlessBinding, bindingFor] using member
      subst ref
      exact ⟨_, rfl, rfl, rfl⟩
    embedding := harmless_sink_embedding
    clean := by
      change harmlessTargetRun.admission.prune.removedSeed = []
      rfl
    claimAssociation := .authored rfl rfl rfl
    evidenceSource := (harmlessTargetCertificate).evidence
    evidenceAlignment := by trivial }

@[macro_inline]
def harmlessReboundCertificate : BridgeCertificate registryEx Evidence.extract :=
  rebind (harmlessCertificate) harmlessTargetRun id id [] none harmlessTransport

theorem harmless_rebound_binding :
    harmlessReboundCertificate.binding = harmlessTargetBinding := by rfl

theorem harmless_rebound_warrant :
    ArtifactWarrant (harmlessTargetBinding) harmlessTargetRun :=
  rebind_warrant (harmlessCertificate) harmlessTargetRun id id [] none
    harmlessTransport harmless_reference_warrant

theorem harmless_rebind_success :
    (checkBridge (harmlessTargetBinding) harmlessReboundCertificate).isOk = true := by decide

theorem dependency_structural_loss :
    dependencyTarget.argsRaw[dependencyApplicability.rawIndex]? = some dependencyApplicability.row ∧
      dependencyApplicability.row ∉ dependencyTargetRun.admission.prune.keptArgs ∧
      (¬ ∃ conclusion obligations,
        HasSupport id dependencyTargetRun.checked.policy.ruleLookup
          (Admission.buildGamma dependencyTargetRun.admission.prune.checkedLeaves)
          (certOkOf registryEx) dependencyApplicability.row.2 conclusion obligations) ∧
      ¬ SupportWarrant dependencyTargetRun dependencyApplicability :=
  tighten_dependency_loss dependencySourceRun dependencyTargetRun dependency_tighten
    dependencyApplicability
    (dependencyCertificate.raw dependencyApplicability (by
      simp [dependencyCertificate, ArtifactBinding.supports, dependencyBinding, bindingFor]))
    ⟨l1, .attested, .user⟩ (by simp [dependencySource]) rfl (by
      simp [dependencyApplicability, Support.leaves])

theorem dependency_target_support_rejected :
    checkSupport dependencyTargetRun dependencyApplicability
      (tighten_raw_support_preserved dependency_tighten
        (dependencyCertificate.raw dependencyApplicability (by
          simp [dependencyCertificate, ArtifactBinding.supports, dependencyBinding, bindingFor]))) =
      .error .missingSupport :=
  tighten_support_rejected dependencySourceRun dependencyTargetRun dependency_tighten
    dependencyApplicability
    (dependencyCertificate.raw dependencyApplicability (by
      simp [dependencyCertificate, ArtifactBinding.supports, dependencyBinding, bindingFor]))
    ⟨l1, .attested, .user⟩ (by simp [dependencySource]) rfl (by
      simp [dependencyApplicability, Support.leaves])

theorem dependency_no_warrant_checker_failure :
    (checkBridge dependencyTargetBinding dependencyTargetCertificate).isOk = false :=
  checkBridge_no_warrant dependencyTargetBinding dependencyTargetCertificate
    dependency_target_no_warrant

theorem supported_applicability_no_knowledge
    (admitted : Admitted (falsePreconditionBinding).canonical.model.context.model.dynamics
      ((falsePreconditionBinding).request.before.world 0 true true)) :
    ordinaryStatus harmlessSourceRun pA = .published .justified ∧
    ¬ knows (falsePreconditionBinding).canonical.model.context.model
      ((falsePreconditionBinding).request.before.world 0 true true)
      (fun world => satisfies (falsePreconditionBinding).canonical.model.context.interpretation
        (falsePreconditionBinding).canonical.model.context.model GhostEnv.empty world
        (falsePreconditionBinding).canonical.pre.assertion) :=
  supported_applicability_without_knowledge falsePreconditionBinding harmlessSourceRun
    (falsePreconditionBound.meaning).warrant rfl admitted

theorem belief_without_truth_boundary :
    satisfies Lara.Examples.BHLBelief.interpretation Lara.Examples.BHLBelief.model GhostEnv.empty
      (Lara.Examples.BHLBelief.fixtureWorld false false false)
      (.modal (Lara.Examples.BHLBelief.belief false .equal 1)) ∧
    ¬ referenceModalSatisfaction Lara.Examples.BHLBelief.interpretation Lara.Examples.BHLBelief.model
      GhostEnv.empty (Lara.Examples.BHLBelief.fixtureWorld false false false)
      Lara.Examples.BHLBelief.alternative :=
  Lara.Examples.BHLBelief.exceptional_belief_false_alternative

theorem certified_leaf_prop_exact : csvLeaf.prop = evidenceAtom := rfl

theorem certified_registry_exact : certifiedSource.actualRegistry = Evidence.extract :=
  certifiedSource.registry_exact

theorem certified_source_equation :
    Surface.sourceWithEvidence certifiedEnv certifiedInput csvSnapshot csvManifest Evidence.extract =
      .ok (certifiedPair.1, certifiedPair.2) :=
  certified_source_success

theorem certified_full_witness :
    ∃ request, Evidence.RequestBound certifiedInput.policy.evidenceCheckers csvManifest csvLeaf request ∧
      ∃ judgment ∈ certifiedPair.2, judgment.leaf = csvLeaf.id.val ∧
        judgment.request = request ∧
        ∃ result, Evidence.run csvSnapshot Evidence.extract request = .ok result ∧
          judgment.dependencies = result.dependencies ∧
          judgment.normalized = nf canonNum csvLeaf.prop ∧
          nf canonNum result.proposition = nf canonNum csvLeaf.prop ∧
          result.dependencies.map (·.id) = Evidence.requestObjects request ∧
          ∀ metadata ∈ result.dependencies, ∃ id ∈ Evidence.requestObjects request,
            ∃ object, Evidence.lookup csvSnapshot id = .ok object ∧ object.metadata = metadata :=
  Evidence.all_declared_certified_witness certified_semantic_admission
    (by rw [certified_same_declared_leaf]; simp) rfl

theorem certified_declared_proposition_is_extraction :
    csvLeaf.prop = evidenceAtom ∧ Evidence.run csvSnapshot Evidence.extract csvRequest =
      .ok ⟨evidenceAtom, [csvMetadata]⟩ :=
  ⟨rfl, certified_extraction_exact⟩

def certifiedBound : BoundCertificate certifiedCertificate :=
  (checkBound certifiedCertificate).toOption.get (by decide +kernel)

theorem certified_bridge_meaning : ArtifactMeaning certifiedBinding certifiedRun :=
  certifiedBound.meaning

theorem certified_reference_warrant : ArtifactWarrant certifiedBinding certifiedRun :=
  certifiedBound.meaning.warrant

def dependencyBound : BoundCertificate dependencyCertificate :=
  (checkBound dependencyCertificate).toOption.get (by decide)

theorem dependency_reference_warrant :
    ArtifactWarrant dependencyBinding dependencySourceRun :=
  dependencyBound.meaning.warrant

def alternativeBound : BoundCertificate alternativeCertificate :=
  (checkBound alternativeCertificate).toOption.get (by decide)

theorem alternative_reference_warrant :
    ArtifactWarrant alternativeBinding dependencyTargetRun :=
  alternativeBound.meaning.warrant

theorem dependency_method_fields_preserved :
    (reboundBinding dependencyBinding dependencyTarget id id none).method =
        dependencyBinding.method ∧
      (reboundBinding dependencyBinding dependencyTarget id id none).canonical =
        dependencyBinding.canonical ∧
      (reboundBinding dependencyBinding dependencyTarget id id none).request =
        dependencyBinding.request ∧
      (reboundBinding dependencyBinding dependencyTarget id id none).query =
        dependencyBinding.query ∧
      (reboundBinding dependencyBinding dependencyTarget id id none).residual =
        dependencyBinding.residual ∧
      (reboundBinding dependencyBinding dependencyTarget id id none).coverage =
        dependencyBinding.coverage :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem dependency_source_bridge_success_and_alternative :
    (checkBridge dependencyBinding dependencyCertificate).isOk = true ∧
      (checkBridge alternativeBinding alternativeCertificate).isOk = true :=
  ⟨dependency_bridge_source_success, independent_alternative_bridge_success⟩

theorem conditional_bridge_native_success :
    checkBridgeNative harmlessBinding harmlessCertificate = .ok () := by decide

theorem dependency_target_native_failure :
    checkBridgeNative dependencyTargetBinding dependencyTargetCertificate =
      .error .missingSupport := by decide

theorem blocked_native_failure :
    checkBridgeNative defenseBinding defenseCertificate = .error .blockedSupport := by decide

theorem stale_native_failure :
    checkBridgeNative harmlessTargetBinding harmlessCertificate = .error .staleSnapshot := by decide

theorem incompatible_claim_native_failure :
    checkBridgeNative { harmlessBinding with claim := ⟨"unknown-method"⟩ } harmlessCertificate =
      .error .incompatibleClaim := by decide

theorem incompatible_origin_native_failure :
    checkBridgeNative { harmlessBinding with origin := .declared ⟨"selected"⟩ } harmlessCertificate =
      .error .incompatibleClaim := by decide

theorem certified_unknown_claim_native_failure :
    checkBridgeNative { certifiedBinding with claim := ⟨"unknown-method"⟩ } certifiedCertificate =
      .error .incompatibleClaim := by decide +kernel

end Lara.Examples.BHLBridge
