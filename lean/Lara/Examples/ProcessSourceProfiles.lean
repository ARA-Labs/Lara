import Lara.Process.FamilyAudit
import Lara.Examples.ProcessSource
import Lara.Examples.ProcessOrder

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 1024

namespace Lara.Examples.ProcessSourceProfiles

open Lara.Process Lara.Process.Source
namespace O
export Lara.Examples.ProcessOrder
  (commit read run success withoutSibling run0 family withSibling siblingRun failure accessScope)
end O

def atom (name : String) : Atom := .atom name .nil

def rule (name premise conclusion : String) : Presentation.Rule :=
  { id := ⟨name⟩, params := [], mode := .defeasible
    premises := [⟨premise, .nil⟩], premiseLabels := [], conclusion := ⟨conclusion, .nil⟩
    allowTrusted := false, certifiers := [], questions := [] }

def claimDecl : Presentation.Decl :=
  .claim ⟨⟨"claim"⟩, "Target", atom "t", ⟨"reader", "target interpretation", .reviewed⟩⟩

def argument (name method premise : String) (target : Presentation.ArgConcl) : Presentation.Decl :=
  .arg ⟨⟨name⟩, target, .inferTheta ⟨method⟩ [⟨premise⟩] [] [] .none⟩

def source (defender : Bool) : SourceInput :=
  let policy : Presentation.Policy :=
    { ProcessSource.ordinaryInput.policy with
      sigma := ⟨[], [], [⟨⟨"seed"⟩, []⟩, ⟨⟨"t"⟩, []⟩, ⟨⟨"s"⟩, []⟩,
        ⟨⟨"u"⟩, []⟩, ⟨⟨"v"⟩, []⟩]⟩
      rules := [rule "r-t" "seed" "t", rule "r-s" "seed" "s",
        rule "r-u" "seed" "u", rule "r-v" "t" "v"]
      contraries := [⟨⟨"s", .nil⟩, ⟨"t", .nil⟩⟩, ⟨⟨"u", .nil⟩, ⟨"s", .nil⟩⟩]
      theories := [] }
  let surface : Surface.Input :=
    { policy
      program := { ProcessSource.ordinaryInput.program with
        policy := policy.id, backends := []
        decls := [.leaf ⟨⟨"seed"⟩, atom "seed", .observed, .user, [], none⟩,
          claimDecl, argument "witness" "r-t" "seed" (.supportsClaim ⟨"claim"⟩),
          argument "attacker" "r-s" "seed" (.supportsDerived ⟨"attack-claim"⟩),
          .attack (.rebut ⟨"attacker"⟩ ⟨"witness"⟩)] ++
          (if defender then [argument "defender" "r-u" "seed" (.supportsDerived ⟨"defense-claim"⟩),
            .attack (.rebut ⟨"defender"⟩ ⟨"attacker"⟩)] else []) ++
          [argument "consumer" "r-v" "witness" (.supportsDerived ⟨"consumer-claim"⟩)] } }
  { surface, replay := ⟨⟨Driver.coreVersionText⟩, policy.id, [], [], surface.program.digest⟩
    capture := none }

def problem : Universe.Problem :=
  { record := ⟨O.withoutSibling.map (fun event => ⟨event, ⟨"fixture", "reported", none⟩⟩),
      [⟨O.commit.id, O.read.id, ⟨"fixture", "order", none⟩⟩,
       ⟨O.read.id, O.run.id, ⟨"fixture", "order", none⟩⟩,
       ⟨O.run.id, O.success.id, ⟨"fixture", "order", none⟩⟩],
      [⟨.complete O.accessScope, ⟨"fixture", "access coverage", none⟩, .instrumentedLog⟩], [], 10⟩
    unrecorded := [] }

def family (defender : Bool) : Family.FamilySpec := ⟨problem, source defender, []⟩
def completion : Family.Completion := ⟨O.withoutSibling, []⟩
def strict : Profile Empty := Profile.strict (1 / 20)
def claim : ClaimBinding := ⟨⟨0⟩, ⟨"claim"⟩, atom "t"⟩
def ledger : LedgerBinding :=
  ⟨O.run0, O.family, 1, ⟨some .pValue, some (1 / 40), some 1, some .fwer⟩⟩
def witness (base : SourceInput) : WitnessSpec :=
  ⟨⟨0⟩, claim.claim, base, ⟨⟨"witness"⟩, [], .declared ⟨0⟩⟩,
    [.sampling], .ledger ledger⟩

def keys (defender : Bool) : List KindKey :=
  [.leaf ⟨"seed"⟩, .method ⟨"r-t"⟩, .method ⟨"r-s"⟩, .method ⟨"r-v"⟩,
    .argument ⟨"witness"⟩, .argument ⟨"attacker"⟩, .argument ⟨"consumer"⟩] ++
    if defender then [.method ⟨"r-u"⟩, .argument ⟨"defender"⟩] else []

def configFor (base : SourceInput) (allKeys : List KindKey) (low : List KindKey) : AuditConfig :=
  { claims := [claim], witnesses := [witness base]
    kinds := allKeys.zipIdx |>.map (fun (key, i) =>
      ⟨base, key, if key ∈ low then .supported else .observed, some ⟨i⟩⟩)
    assumptions := allKeys.zipIdx |>.map (fun (key, i) =>
      ⟨⟨i⟩, base, key, O.success, O.run0, .instrumentedLog⟩) }

def config (defender : Bool) : AuditConfig :=
  configFor (source defender) (keys defender)
    [if defender then .argument ⟨"defender"⟩ else .argument ⟨"attacker"⟩]

def context (spec : Family.FamilySpec) (cfg : AuditConfig)
    (completions : List Family.Completion := [completion]) : ModelContext :=
  modelContext spec.base cfg (familyCarrier (completions.map (takeSnapshot spec)) cfg)

def row (defender : Bool) (cfg : AuditConfig) : Row (context (family defender) cfg) :=
  prepareRow _ (takeSnapshot (family defender) completion)

def gradeSummary (view : Prepared) : List (Presentation.ArgId × EvidenceKind × Bool) :=
  view.kinds.map fun node => (node.argument, node.value)

def statusSummary (view : Prepared) : List (Atom × Driver.PublicStatus) :=
  view.queries.map fun query => (query.query, query.status)

def passes (defender : Bool) (cfg : AuditConfig) : Bool :=
  warranted _ (row defender cfg) strict claim.claim ⟨0⟩

def audited (defender : Bool) (cfg : AuditConfig) : Bool :=
  audit (checkFamily (family defender) cfg [completion]) strict claim.claim ⟨0⟩

theorem real_family_singleton : Family.referenceFamily (family false) = [completion] ∧
    Family.referenceFamily (family true) = [completion] := by decide +kernel

theorem sources_checked : (checkSource (source false)).isOk = true ∧
    (checkSource (source true)).isOk = true := by decide +kernel

theorem attacker_checked_fields :
    (row false (config false)).view.map (fun view =>
      (view.complete, statusSummary view, gradeSummary view)) =
    .ok (true, [(atom "t", .published .defeated)],
      [(⟨"witness"⟩, .observed, true), (⟨"attacker"⟩, .supported, true),
       (⟨"consumer"⟩, .observed, true)]) := by decide +kernel

theorem inadmissible_attacker_reinstates :
    passes false (config false) = true ∧ audited false (config false) = true := by decide +kernel

theorem defender_checked_fields :
    (row true (config true)).view.map (fun view =>
      (view.complete, statusSummary view, gradeSummary view)) =
    .ok (true, [(atom "t", .published .justified)],
      [(⟨"witness"⟩, .observed, true), (⟨"attacker"⟩, .observed, true),
       (⟨"defender"⟩, .supported, true), (⟨"consumer"⟩, .observed, true)]) := by decide +kernel

theorem inadmissible_defender_removes_warrant :
    passes true (config true) = false ∧ audited true (config true) = false := by decide +kernel

def missingAttacker : AuditConfig :=
  { config false with kinds := (config false).kinds.filter (·.key != .argument ⟨"attacker"⟩) }

theorem missing_attacker_global_incomplete :
    (row false missingAttacker).view.map (fun view => (view.complete, gradeSummary view)) =
      .ok (false, [(⟨"witness"⟩, .observed, true), (⟨"attacker"⟩, .hypothetical, false),
        (⟨"consumer"⟩, .observed, true)]) ∧
    passes false missingAttacker = false ∧ audited false missingAttacker = false := by decide +kernel

def unadmitted : AuditConfig := { config false with assumptions := [] }

theorem observed_needs_admission :
    (row false unadmitted).view.map (fun view => (view.complete, gradeSummary view)) =
      .ok (true, [(⟨"witness"⟩, .conditional, true), (⟨"attacker"⟩, .conditional, true),
        (⟨"consumer"⟩, .conditional, true)]) ∧
    passes false unadmitted = false := by decide +kernel

def conditionalGuarantee : AuditConfig :=
  { config false with witnesses := [{ witness (source false) with guarantee := .conditional .fwer (1 / 40) }] }

def conditionalMethod : AuditConfig :=
  { config true with witnesses := [{ witness (source true) with artifact :=
      ⟨⟨"witness"⟩, [], .checkedMethod ⟨.conditionalFalse, .conditional, 0, true, true,
        [.interpretationFidelity, .physicalSampling, .captureAdequacy, .runtimeRefinement]⟩⟩ }] }

theorem conditional_guarantee_caps_transitive_use :
    (row false conditionalGuarantee).view.map gradeSummary =
      .ok [(⟨"witness"⟩, .conditional, true), (⟨"attacker"⟩, .supported, true),
        (⟨"consumer"⟩, .conditional, true)] ∧
    ((row false conditionalGuarantee).witness ⟨0⟩).isSome = true ∧
    passes false conditionalGuarantee = false := by decide +kernel

theorem conditional_method_caps_transitive_use :
    (row true conditionalMethod).view.map gradeSummary =
      .ok [(⟨"witness"⟩, .conditional, true), (⟨"attacker"⟩, .observed, true),
        (⟨"defender"⟩, .supported, true), (⟨"consumer"⟩, .conditional, true)] ∧
    ((row true conditionalMethod).witness ⟨0⟩).isSome = true ∧
    passes true conditionalMethod = false := by decide +kernel

def changedSource : SourceInput :=
  { source false with surface := { (source false).surface with program :=
    { (source false).surface.program with artifact := "different-full-source" } } }

def changedFamily : Family.FamilySpec := { family false with base := changedSource }
def changedRow := prepareRow (context changedFamily (config false)) (takeSnapshot changedFamily completion)

theorem same_digest_stale_pin :
    changedSource.surface.program.digest = (source false).surface.program.digest ∧
    changedSource ≠ source false ∧
    changedRow.view.map (fun view => view.witnesses.map (fun entry => entry.2.map (fun _ => ()))) =
      .ok [.error .staleSource] ∧
    warranted _ changedRow strict claim.claim ⟨0⟩ = false := by decide +kernel

def changedClaimSource : SourceInput :=
  { source false with surface := { (source false).surface with program :=
    { (source false).surface.program with decls := (source false).surface.program.decls.map fun decl =>
      match decl with
      | .claim c => .claim { c with formal := atom "u" }
      | .arg a => if a.id == ⟨"witness"⟩ then
          .arg { a with concl := .supportsDerived ⟨"original-target"⟩ } else .arg a
      | other => other } } }

def changedClaimFamily : Family.FamilySpec := { family false with base := changedClaimSource }
def changedClaimConfig : AuditConfig := configFor changedClaimSource (keys false) [.argument ⟨"attacker"⟩]
def changedClaimRow :=
  prepareRow (context changedClaimFamily changedClaimConfig) (takeSnapshot changedClaimFamily completion)

theorem changed_claim_keeps_fixed_query :
    changedClaimRow.view.map (fun view => (statusSummary view,
      view.witnesses.map (fun entry => entry.2.map (fun _ => ())))) =
      .ok ([(atom "t", .published .defeated)], [.error (.artifact (.association .inputClaim))]) ∧
    fixedClaims changedClaimSource changedClaimConfig = false ∧
    warranted _ changedClaimRow strict claim.claim ⟨0⟩ = false := by decide +kernel

def duplicateConfig : AuditConfig :=
  { config false with kinds := (config false).kinds ++ (config false).kinds }

theorem duplicate_metadata_fails_closed :
    duplicateConfig.wellFormed = false ∧
    (row false duplicateConfig).view.map (fun view => (view.complete,
      view.witnesses.map (fun entry => entry.2.map (fun _ => ())))) =
      .ok (false, [.error .ambiguousMetadata]) ∧
    audited false duplicateConfig = false := by decide +kernel

def duplicateConfigs : List AuditConfig :=
  [duplicateConfig,
    { config false with claims := (config false).claims ++ (config false).claims },
    { config false with witnesses := (config false).witnesses ++ (config false).witnesses },
    { config false with assumptions := (config false).assumptions ++ (config false).assumptions }]

theorem every_duplicate_metadata_class_fails :
    duplicateConfigs.all (fun cfg => !cfg.wellFormed && !audited false cfg) = true := by decide +kernel

def wrongCaptureSource : AuditConfig :=
  { config false with assumptions := (config false).assumptions.map fun assumption =>
      { assumption with source := changedSource } }

def wrongCaptureRun : AuditConfig :=
  { config false with assumptions := (config false).assumptions.map fun assumption =>
      { assumption with run := ⟨1⟩ } }

theorem observed_needs_exact_capture :
    (row false wrongCaptureSource).kind ((context (family false) wrongCaptureSource).argOf ⟨0⟩) = .conditional ∧
    (row false wrongCaptureRun).kind ((context (family false) wrongCaptureRun).argOf ⟨0⟩) = .conditional ∧
    passes false wrongCaptureSource = false ∧ passes false wrongCaptureRun = false := by decide +kernel

def siblingProblem : Universe.Problem :=
  { problem with unrecorded := [O.siblingRun, O.failure] }
def siblingFamily : Family.FamilySpec := { family false with problem := siblingProblem }
def siblingCompletion : Family.Completion := ⟨O.withSibling, []⟩
def siblingContext := context siblingFamily (config false) [completion, siblingCompletion]
def selectedRow := prepareRow siblingContext (takeSnapshot siblingFamily completion)
def siblingRow := prepareRow siblingContext (takeSnapshot siblingFamily siblingCompletion)

def siblingChecked :=
  checkFamily siblingFamily (config false) (Family.referenceFamily siblingFamily)

def graphSummary (view : Prepared) : List Nat × List (Nat × Nat) :=
  (view.graph.args, view.graph.args.flatMap fun attacker =>
    view.graph.args.filterMap fun target =>
      if view.graph.attack attacker target then some (attacker, target) else none)

theorem missing_metadata_filter_alone_reinstates :
    Grounded.labelC
      ((rowModel (context (family false) missingAttacker) (fun _ _ => False)).underProfile
        strict (row false missingAttacker)) ((context (family false) missingAttacker).argOf ⟨0⟩) = .inn ∧
    (row false missingAttacker).artifact ⟨0⟩ = false := by decide +kernel

theorem sibling_completions_real :
    completion ∈ Family.referenceFamily siblingFamily ∧
    siblingCompletion ∈ Family.referenceFamily siblingFamily := by decide +kernel

theorem sibling_full_family_preconditions :
    Family.referenceFamily siblingFamily ≠ [] ∧
    (Universe.admittedCoverage siblingFamily.problem).all strict.acceptsCoverage = true :=
  ⟨List.ne_nil_of_mem sibling_completions_real.1, rfl⟩

private theorem failed_sibling_full_audit :
    audit siblingChecked strict claim.claim ⟨0⟩ = false := by
  have absent :
      (prepareRow siblingChecked.context (takeSnapshot siblingFamily siblingCompletion)).witness ⟨0⟩ =
        none := by decide +kernel
  have invalid :
      (prepareRow siblingChecked.context (takeSnapshot siblingFamily siblingCompletion)).artifact ⟨0⟩ =
        false := by
    unfold Row.artifact
    split
    · rfl
    · simp only [absent, Option.isSome_none, Bool.and_false]
  apply Bool.eq_false_iff.mpr
  intro passed
  have valid := ((audit_iff siblingChecked strict claim.claim ⟨0⟩
    (fun _ _ => False)).mp passed).2.2 siblingCompletion sibling_completions_real.2
  have artifact := valid.1
  change (prepareRow siblingChecked.context
    (takeSnapshot siblingFamily siblingCompletion)).artifact ⟨0⟩ = true at artifact
  rw [invalid] at artifact
  exact Bool.false_ne_true artifact

theorem failed_sibling_same_graph_status :
    selectedRow.view.map (fun view => (graphSummary view, statusSummary view)) =
      siblingRow.view.map (fun view => (graphSummary view, statusSummary view)) ∧
    selectedRow.view.isOk = true ∧ siblingRow.view.isOk = true := by decide +kernel

theorem failed_sibling_changes_guarantee_warrant :
    selectedRow.view.map (fun view => view.witnesses.map (fun entry => entry.2.map (·.achieved))) =
      .ok [.ok (.fwer, 1 / 40)] ∧
    siblingRow.view.map (fun view => view.witnesses.map (fun entry => entry.2.map (·.achieved))) =
      .ok [.error (.guarantee (.ledger .exceededBound))] ∧
    warranted _ selectedRow strict claim.claim ⟨0⟩ = true ∧
    warranted _ siblingRow strict claim.claim ⟨0⟩ = false ∧
    audit siblingChecked strict claim.claim ⟨0⟩ = false := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, failed_sibling_full_audit⟩

def alternatingSource : SourceInput :=
  { source false with surface :=
    { (source false).surface with
      policy := { (source false).surface.policy with rules := [], contraries := [] }
      program := { (source false).surface.program with decls :=
        [.leaf ⟨⟨"first"⟩, atom "t", .observed, .user, [], none⟩,
         .leaf ⟨⟨"second"⟩, atom "t", .observed, .user, [], none⟩, claimDecl] } } }

def leftChoice : Family.Choice := ⟨⟨0⟩, .truth,
  [.arg ⟨⟨"witness"⟩, .supportsClaim ⟨"claim"⟩, .explicitTheta (.leaf ⟨"first"⟩)⟩]⟩
def rightChoice : Family.Choice := ⟨⟨1⟩, .truth,
  [.arg ⟨⟨"defender"⟩, .supportsClaim ⟨"claim"⟩, .explicitTheta (.leaf ⟨"second"⟩)⟩]⟩
def alternatingFamily : Family.FamilySpec :=
  ⟨problem, alternatingSource, [⟨⟨0⟩, [leftChoice, rightChoice]⟩]⟩
def leftCompletion : Family.Completion := ⟨O.withoutSibling, [⟨⟨0⟩, leftChoice⟩]⟩
def rightCompletion : Family.Completion := ⟨O.withoutSibling, [⟨⟨0⟩, rightChoice⟩]⟩
def alternatingCompletions := [leftCompletion, rightCompletion]
def alternatingConfig : AuditConfig :=
  let cfg := configFor alternatingSource
    [.leaf ⟨"first"⟩, .leaf ⟨"second"⟩,
      .argument ⟨"witness"⟩, .argument ⟨"defender"⟩] []
  { cfg with witnesses := [witness alternatingSource,
      ⟨⟨1⟩, claim.claim, alternatingSource, ⟨⟨"defender"⟩, [], .declared ⟨0⟩⟩,
        [.sampling], .ledger ledger⟩] }
def alternatingChecked := checkFamily alternatingFamily alternatingConfig alternatingCompletions

/-- Source-choice arguments remain hypothetical; this countermodel admits them
without changing the fixed-witness quantifier or any checker-produced result. -/
def alternatingProfile : Profile Empty :=
  { strict with admissible := {.hypothetical, .observed} }

theorem alternating_coverage_accepted :
    (Universe.admittedCoverage alternatingFamily.problem).all
      alternatingProfile.acceptsCoverage = true := rfl

theorem alternating_full_family :
    Family.referenceFamily alternatingFamily = alternatingCompletions ∧
    alternatingCompletions ≠ [] := by decide +kernel

theorem alternating_actual_checked_witnesses :
    alternatingChecked.rows.map (fun row => row.view.map (fun view =>
      (view.complete, statusSummary view, gradeSummary view))) =
      [.ok (true, [(atom "t", .published .justified)],
        [(⟨"witness"⟩, .hypothetical, true)]),
       .ok (true, [(atom "t", .published .justified)],
        [(⟨"defender"⟩, .hypothetical, true)])] ∧
    alternatingChecked.rows.map (fun row =>
      (warranted _ row alternatingProfile claim.claim ⟨0⟩,
       warranted _ row alternatingProfile claim.claim ⟨1⟩)) =
      [(true, false), (false, true)] := by decide +kernel

theorem alternating_fixed_witness_audits_fail :
    audit alternatingChecked alternatingProfile claim.claim ⟨0⟩ = false ∧
    audit alternatingChecked alternatingProfile claim.claim ⟨1⟩ = false := by decide +kernel

theorem alternating_fixed_witness_failure_nonvacuous :
    Family.referenceFamily alternatingFamily ≠ [] ∧
    (Universe.admittedCoverage alternatingFamily.problem).all
      alternatingProfile.acceptsCoverage = true ∧
    audit alternatingChecked alternatingProfile claim.claim ⟨0⟩ = false ∧
    audit alternatingChecked alternatingProfile claim.claim ⟨1⟩ = false := by
  refine ⟨?_, alternating_coverage_accepted, alternating_fixed_witness_audits_fail⟩
  rw [alternating_full_family.1]
  exact alternating_full_family.2

theorem alternating_existential_claim :
    ∀ row ∈ alternatingChecked.rows, ∃ witness ∈ ([⟨0⟩, ⟨1⟩] : List WitnessId),
      Warranted (rowModel alternatingChecked.context (fun _ _ => False))
        alternatingProfile row claim.claim witness := by
  have computed : alternatingChecked.rows.all (fun row =>
      ([⟨0⟩, ⟨1⟩] : List WitnessId).any (warranted _ row alternatingProfile claim.claim)) = true := by decide +kernel
  intro row member
  obtain ⟨witness, named, valid⟩ := List.any_eq_true.mp (List.all_eq_true.mp computed row member)
  exact ⟨witness, named, (warranted_iff _ _ _ _ _ _).mp valid⟩

end Lara.Examples.ProcessSourceProfiles
