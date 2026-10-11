import Lara.Process.SourceAuditAssociation
import Lara.Examples.ProcessSource

set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

namespace Lara.Examples.ProcessSourceAudit

open Lara.Process.Source Lara.Examples.BHLBridge Lara.Examples.ProcessSource

def query : Atom := .atom "result" .nil

def auditSurface : Surface.Input :=
  { ordinaryInput with
    program := { ordinaryInput.program with decls := [
      .leaf ⟨ordinaryLeaf.id, query, .observed, .user, [], none⟩,
      .claim ⟨⟨"method"⟩, "Result", query,
        ⟨"reader", "declared interpretation", .reviewed⟩⟩,
      .arg ⟨⟨"selected"⟩, .supportsClaim ⟨"method"⟩,
        .explicitTheta (.leaf ordinaryLeaf.id)⟩] }
    policy := { ordinaryInput.policy with sigma := ⟨[], [], [⟨⟨"result"⟩, []⟩]⟩ } }

def input : SourceInput :=
  { surface := auditSurface
    replay :=
      { core := ⟨Driver.coreVersionText⟩
        policy := auditSurface.policy.id
        backends := []
        theories := []
        artifact := auditSurface.program.digest }
    capture := none }

theorem source_accepted : (checkSource input).isOk = true := by decide +kernel

def claim : ClaimBinding := ⟨⟨0⟩, ⟨"method"⟩, query⟩
def declared : ArtifactSpec := ⟨⟨"selected"⟩, [], .declared ⟨0⟩⟩

private def methodBinding (code : BHL.CheckedMethods.Method) (mode : BHL.PayloadMode) :
    MethodBinding :=
  ⟨code, mode, 0, true, true,
    [.interpretationFidelity, .physicalSampling, .captureAdequacy, .runtimeRefinement]⟩

def method (code : BHL.CheckedMethods.Method) (mode : BHL.PayloadMode) : ArtifactSpec :=
  { declared with interpretation := .checkedMethod (methodBinding code mode) }

def result (binding : ClaimBinding) (spec : ArtifactSpec) :
    Except SourceRejection (Except ArtifactFault _root_.Unit) :=
  (checkSource input).map fun observation =>
    (checkArtifact observation binding spec).map fun _ => ()

theorem actual_declared_association : result claim declared = .ok (.ok ()) := by decide +kernel

theorem unknown_claim_not_associated :
    result { claim with declaration := ⟨"unknown"⟩ } declared =
      .ok (.error (.association .inputClaim)) := by decide +kernel

theorem fixed_query_not_reinterpreted :
    result { claim with query := .atom "other" .nil } declared =
      .ok (.error (.support ⟨"selected"⟩ .differentConclusion)) := by decide +kernel

theorem missing_dependency_not_assumed :
    result claim { declared with dependencies := [⟨⟨"missing"⟩, query⟩] } =
      .ok (.error (.support ⟨"missing"⟩ .absent)) := by decide +kernel

private def observation : AcceptedObservation input :=
  Check.Unit.okValue (Check.Unit.exists_ok_of_isOk source_accepted)

private theorem observation_eq : checkSource input = .ok observation :=
  Check.Unit.okValue_eq (Check.Unit.exists_ok_of_isOk source_accepted)

private theorem unattacked_warrant {input : SourceInput}
    (observation : AcceptedObservation input) {binding : SupportBinding}
    (selected : ResolvedSupport observation binding)
    (noAttacks : observation.run.admission.prune.keptAttacks = []) :
    BHL.SupportWarrant observation.run selected.ref := by
  apply selected.warrant_of_label
  apply Grounded.labelC_inn_of_unattacked
  · obtain ⟨node, atNode, _, _⟩ := selected.node
    have bound := (List.getElem?_eq_some_iff.mp atNode).1
    have length : observation.run.checked.nodes.length =
        observation.run.checked.program.args.length := by
      simpa using congrArg List.length observation.run.checked.nodes_terms
    apply List.mem_range.mpr
    rw [← length]
    exact bound
  · intro attacker _
    have attacks := (Check.Unit.checkUnit_sound observation.run.check_ok).atts_eq
    simp only [noAttacks, Check.liveAttacks, List.filter_nil] at attacks
    change Compile.edgeB observation.run.checked.program attacker selected.ref.checkedIndex = false
    unfold Compile.edgeB
    rw [attacks]
    cases observation.run.checked.program.args[attacker]? <;>
      cases observation.run.checked.program.args[selected.ref.checkedIndex]? <;> rfl

private theorem selected_warrant
    (selected : ResolvedSupport observation ⟨declared.argument, claim.query⟩) :
    BHL.SupportWarrant observation.run selected.ref :=
  unattacked_warrant observation selected (by decide +kernel)

private theorem method_alignment
    {input : SourceInput} (observation : AcceptedObservation input)
    (selected : ResolvedSupport observation ⟨declared.argument, claim.query⟩)
    (dependencies : ResolvedSupports observation [])
    (binding : MethodBinding) :
    BHL.MathematicalAlignment
      (artifactBinding observation claim declared.argument selected dependencies binding) :=
  ⟨rfl, rfl, rfl, selected.query⟩

private theorem method_warrant
    {input : SourceInput} (observation : AcceptedObservation input)
    (selected : ResolvedSupport observation ⟨declared.argument, claim.query⟩)
    (dependencies : ResolvedSupports observation [])
    (binding : MethodBinding)
    (warrant : BHL.SupportWarrant observation.run selected.ref) :
    BHL.ArtifactWarrant
      (artifactBinding observation claim declared.argument selected dependencies binding)
      observation.run := by
  have empty : dependencies.refs = [] := List.map_eq_nil_iff.mp dependencies.exact
  intro ref member
  simp only [artifactBinding, BHL.ArtifactBinding.supports, empty,
    List.mem_cons, List.not_mem_nil, or_false] at member
  subst ref
  exact warrant

private theorem method_success
    {input : SourceInput} (observation : AcceptedObservation input)
    (selected : ResolvedSupport observation ⟨declared.argument, claim.query⟩)
    (association : SourceAssociation observation claim declared.argument selected)
    (dependencies : ResolvedSupports observation [])
    (binding : MethodBinding)
    (warrant : BHL.SupportWarrant observation.run selected.ref)
    (application : binding.mode = .applied →
      (BHL.CheckedMethods.checkApplication binding.method
        (binding.method.request binding.parameter binding.first binding.second)).isOk = true) :
    checkMethod observation claim declared.argument selected association dependencies binding = .ok () := by
  let certificate := bridgeCertificate observation claim declared.argument
    selected association dependencies binding
  have success := BHL.checkBridge_complete certificate
    (method_alignment observation selected dependencies binding)
    (method_warrant observation selected dependencies binding warrant) application
  obtain ⟨result, checked⟩ := Check.Unit.exists_ok_of_isOk success
  change (BHL.checkBridge certificate.binding certificate).map (fun _ => ()) = .ok ()
  rw [checked]
  rfl

private theorem two_application :
    (BHL.CheckedMethods.checkApplication .two
      (BHL.CheckedMethods.Method.two.request 0 true true)).isOk = true := by
  unfold BHL.CheckedMethods.checkApplication BHL.CheckedMethods.checkBinding
  simp only [BHL.CheckedMethods.Method.request]
  decide +kernel

private theorem false_application :
    BHL.CheckedMethods.checkApplication .conditionalFalse
      (BHL.CheckedMethods.Method.conditionalFalse.request 0 true true) =
      .error .failedPrecondition := by
  unfold BHL.CheckedMethods.checkApplication BHL.CheckedMethods.checkBinding
  simp only [BHL.CheckedMethods.Method.request]
  rfl

private theorem bridge_false_precondition {input : SourceInput}
    (certificate : BHL.BridgeCertificate (sourceEnv input).registry Evidence.extract)
    (alignment : BHL.MathematicalAlignment certificate.binding)
    (warrant : BHL.ArtifactWarrant certificate.binding certificate.run)
    (mode : certificate.binding.mode = .applied)
    (application : BHL.CheckedMethods.checkApplication certificate.binding.method
      certificate.binding.request = .error .failedPrecondition) :
    BHL.checkBridgeNative certificate.binding certificate = .error .falsePrecondition := by
  have supports := BHL.checkSupports_complete certificate.run certificate.binding.supports
    certificate.raw warrant
  have bound : BHL.checkBound certificate = .error .falsePrecondition := by
    unfold BHL.checkBound
    simp only [dif_pos alignment.canonical, dif_pos alignment.request,
      dif_pos alignment.interpretation, dif_pos alignment.query,
      dif_pos (BHL.CheckedMethods.method_checked certificate.binding.method)]
    cases hs : BHL.checkSupports certificate.run certificate.binding.supports certificate.raw with
    | error error => rw [hs] at supports; contradiction
    | ok checked =>
      simp only [Bind.bind, Except.bind]
      split
      · simp_all
      · split <;> simp_all
  unfold BHL.checkBridgeNative BHL.checkBridge
  simp only [↓reduceDIte, bound, Bind.bind, Except.bind, Except.map]

private theorem method_false_precondition
    {input : SourceInput} (observation : AcceptedObservation input)
    (selected : ResolvedSupport observation ⟨declared.argument, claim.query⟩)
    (association : SourceAssociation observation claim declared.argument selected)
    (dependencies : ResolvedSupports observation [])
    (warrant : BHL.SupportWarrant observation.run selected.ref) :
    checkMethod observation claim declared.argument selected association dependencies
      (methodBinding .conditionalFalse .applied) = .error .falsePrecondition := by
  let binding := methodBinding .conditionalFalse .applied
  let certificate := bridgeCertificate observation claim declared.argument
    selected association dependencies binding
  exact bridge_false_precondition certificate
    (method_alignment observation selected dependencies binding)
    (method_warrant observation selected dependencies binding warrant) rfl false_application

private theorem artifact_of_method_check {input : SourceInput}
    (observation : AcceptedObservation input)
    (code : BHL.CheckedMethods.Method) (mode : BHL.PayloadMode)
    (expected : Except BHL.BridgeError _root_.Unit)
    (base : (checkArtifact observation claim declared).map (fun _ => ()) = .ok ())
    (checked : ∀ (selected : ResolvedSupport observation ⟨declared.argument, claim.query⟩)
      (association : SourceAssociation observation claim declared.argument selected)
      (dependencies : ResolvedSupports observation []),
      checkMethod observation claim declared.argument selected association dependencies
        (methodBinding code mode) = expected) :
    (checkArtifact observation claim (method code mode)).map (fun _ => ()) =
      expected.mapError ArtifactFault.method := by
  cases hs : resolveSupport observation ⟨declared.argument, claim.query⟩ with
  | error error => simp [checkArtifact, hs, Except.map] at base
  | ok selected =>
    cases ha : associateSource observation claim declared.argument selected with
    | error error => simp [checkArtifact, hs, ha, Except.map] at base
    | ok association =>
      cases hd : resolveSupports observation declared.dependencies with
      | error error =>
        obtain ⟨argument, error⟩ := error
        simp [checkArtifact, hs, ha, hd, Except.map] at base
      | ok dependencies =>
        have hm := checked selected association dependencies
        cases expected with
        | error error =>
          simp only [checkArtifact, method, hs, ha, hd, Except.map, Except.mapError]
          split <;> rename_i branch
          all_goals
            split at branch <;> rename_i methodResult
            all_goals
              have same := hm.symm.trans methodResult
              cases same <;> cases branch <;> rfl
        | ok value =>
          cases value
          simp only [checkArtifact, method, hs, ha, hd, Except.map, Except.mapError]
          split <;> rename_i branch
          all_goals
            split at branch <;> rename_i methodResult
            all_goals
              have same := hm.symm.trans methodResult
              cases same <;> cases branch <;> rfl

private theorem result_of_method_check
    (code : BHL.CheckedMethods.Method) (mode : BHL.PayloadMode)
    (expected : Except BHL.BridgeError _root_.Unit)
    (checked : ∀ (selected : ResolvedSupport observation ⟨declared.argument, claim.query⟩)
      (association : SourceAssociation observation claim declared.argument selected)
      (dependencies : ResolvedSupports observation []),
      checkMethod observation claim declared.argument selected association dependencies
        (methodBinding code mode) = expected) :
    result claim (method code mode) = .ok (expected.mapError ArtifactFault.method) := by
  have base := actual_declared_association
  unfold result at base ⊢
  rw [observation_eq] at base ⊢
  exact congrArg Except.ok (artifact_of_method_check observation code mode expected
    (Except.ok.inj base) checked)

theorem checked_method_application : result claim (method .two .applied) = .ok (.ok ()) := by
  apply result_of_method_check .two .applied (.ok ())
  intro selected association dependencies
  exact method_success observation selected association dependencies _
    (selected_warrant selected) (fun _ => two_application)

theorem false_precondition_remains_conditional :
    result claim (method .conditionalFalse .conditional) = .ok (.ok ()) := by
  apply result_of_method_check .conditionalFalse .conditional (.ok ())
  intro selected association dependencies
  apply method_success observation selected association dependencies _
    (selected_warrant selected)
  intro impossible
  cases impossible

theorem false_precondition_cannot_be_applied :
    result claim (method .conditionalFalse .applied) =
      .ok (.error (.method .falsePrecondition)) := by
  apply result_of_method_check .conditionalFalse .applied (.error .falsePrecondition)
  intro selected association dependencies
  exact method_false_precondition observation selected association dependencies
    (selected_warrant selected)

end Lara.Examples.ProcessSourceAudit
