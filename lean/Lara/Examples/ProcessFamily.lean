import Lara.Process.Family
import Lara.Examples.ProcessOrder
import Lara.Examples.ProcessSource

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-! Kernel-decidable fixtures for source-choice products. Guards constrain histories;
source material is appended even when declarations collide. -/

namespace Lara.Examples.ProcessFamily

open Lara.Process Lara.Process.Family Lara.Examples.ProcessOrder

private def base : Source.SourceInput :=
  let surface := ProcessSource.ordinaryInput
  { surface
    replay := {
      core := ⟨Driver.coreVersionText⟩
      policy := surface.policy.id
      backends := surface.program.backends.map fun pair => ⟨pair.1, ⟨pair.2⟩⟩
      theories := surface.policy.theories.map Prod.fst
      artifact := surface.program.digest }
    capture := none }

private def optional : Universe.Problem :=
  { record := ⟨[], [], [], [], 10⟩, unrecorded := [commit] }

private def absentChoice : Choice := ⟨⟨0⟩, .not (.present commit), []⟩
private def presentChoice : Choice := ⟨⟨1⟩, .present commit, []⟩
private def otherChoice : Choice := ⟨⟨2⟩, .truth, []⟩
private def guarded : FamilySpec :=
  ⟨optional, base, [⟨⟨0⟩, [absentChoice, presentChoice]⟩, ⟨⟨1⟩, [otherChoice]⟩]⟩

theorem guarded_product :
    wellFormed guarded = true ∧ referenceFamily guarded =
      [⟨[], [⟨⟨0⟩, absentChoice⟩, ⟨⟨1⟩, otherChoice⟩]⟩,
       ⟨[commit], [⟨⟨0⟩, presentChoice⟩, ⟨⟨1⟩, otherChoice⟩]⟩] := by decide +kernel

theorem no_slot_p0 :
    (referenceFamily ⟨optional, base, []⟩).map Completion.history = optional.completions :=
  referenceFamily_no_slots_projection optional base

private def failed : Universe.Problem :=
  { record := ⟨[⟨commit, ⟨"family", "commit", none⟩⟩,
      ⟨siblingRun, ⟨"family", "failed-run", none⟩⟩,
      ⟨failure, ⟨"family", "failed-result", none⟩⟩], [], [], [], 10⟩,
    unrecorded := [] }

private def failedFamily : FamilySpec := ⟨failed, base, [⟨⟨0⟩, [otherChoice]⟩]⟩

theorem failed_event_retained :
    (referenceFamily failedFamily).any (fun completion =>
      decide (siblingRun ∈ completion.history ∧ failure ∈ completion.history) &&
        decide ((materialize failedFamily completion).surface.program.decls =
          base.surface.program.decls)) = true := by decide +kernel

private def sameFragments : FamilySpec :=
  ⟨⟨⟨[], [], [], [], 10⟩, []⟩, base,
    [⟨⟨0⟩, [⟨⟨0⟩, .truth, []⟩, ⟨⟨1⟩, .truth, []⟩]⟩]⟩

theorem identical_fragments_distinct_choices :
    wellFormed sameFragments = true ∧ (referenceFamily sameFragments).length = 2 ∧
      (referenceFamily sameFragments).Nodup := by decide +kernel

private def firstChoice : Choice := ⟨⟨0⟩, .truth, []⟩
private def secondChoice : Choice := ⟨⟨1⟩, .truth, []⟩
private def twoByTwo : FamilySpec :=
  { sameFragments with slots :=
      [⟨⟨0⟩, [firstChoice, secondChoice]⟩, ⟨⟨1⟩, [firstChoice, secondChoice]⟩] }

theorem two_slot_product_order :
    referenceFamily twoByTwo =
      [⟨[], [⟨⟨0⟩, firstChoice⟩, ⟨⟨1⟩, firstChoice⟩]⟩,
       ⟨[], [⟨⟨0⟩, firstChoice⟩, ⟨⟨1⟩, secondChoice⟩]⟩,
       ⟨[], [⟨⟨0⟩, secondChoice⟩, ⟨⟨1⟩, firstChoice⟩]⟩,
       ⟨[], [⟨⟨0⟩, secondChoice⟩, ⟨⟨1⟩, secondChoice⟩]⟩] := by decide +kernel

private def duplicateChoice : Choice :=
  ⟨⟨0⟩, .truth, [.leaf ProcessSource.ordinaryLeaf]⟩

private def duplicateFamily : FamilySpec :=
  { sameFragments with slots := [⟨⟨0⟩, [duplicateChoice]⟩] }

private def duplicateCompletion : Completion :=
  ⟨[], [⟨⟨0⟩, duplicateChoice⟩]⟩

theorem duplicate_declaration_appended :
    duplicateCompletion ∈ referenceFamily duplicateFamily ∧
      (materialize duplicateFamily duplicateCompletion).surface.program.decls =
        base.surface.program.decls ++ [.leaf ProcessSource.ordinaryLeaf] := by decide +kernel

theorem duplicate_declaration_rejected :
    ProcessSource.ordinaryError (materialize duplicateFamily duplicateCompletion).surface =
      some (.structural (.duplicateLeafId ProcessSource.ordinaryLeaf.id)) := by decide +kernel

theorem guard_order_is_history_order :
    Guard.eval (.before commit read) [read, commit] = false ∧
      Guard.eval (.before commit read) [commit, read] = true ∧
      Guard.eval (.before commit commit) [commit] = false ∧
      Guard.eval (.before commit commit) [commit, commit] = true := by decide +kernel

private def selectedComparison : Presentation.Comparison :=
  { conclusion := ⟨"better", .nil⟩
    measurand := ⟨"quality"⟩
    dataset := ⟨"dataset"⟩
    relation := .strictlyBetter
    recheckArg := ⟨"comparison-recheck"⟩
    bridgeArg := ⟨"comparison-bridge"⟩
    result := ⟨"result"⟩
    baseline := ⟨"baseline"⟩
    binding := ⟨"binding"⟩
    claim := ⟨⟨"comparison-claim"⟩, "comparison", ⟨"reader", "interpretation", .reviewed⟩⟩
    supports := none }

private def comparisonChoice : Choice := ⟨⟨0⟩, .truth, [.comparison selectedComparison]⟩
private def comparisonFamily : FamilySpec :=
  { failedFamily with slots := [⟨⟨0⟩, [comparisonChoice]⟩] }
private def comparisonCompletion : Completion :=
  ⟨[commit, siblingRun, failure], [⟨⟨0⟩, comparisonChoice⟩]⟩

private def comparisonSource := materialize comparisonFamily comparisonCompletion
private def comparisonKeys : List Source.KindKey :=
  [.argument selectedComparison.recheckArg, .argument selectedComparison.bridgeArg,
    .leaf ⟨"support"⟩]
private def observedComparisonSpecs : List Source.KindSpec :=
  comparisonKeys.map fun key => ⟨comparisonSource, key, .observed, some ⟨0⟩⟩
private def comparisonAssumptions : List Source.CaptureAssumption :=
  comparisonKeys.map fun key =>
    ⟨⟨0⟩, comparisonSource, key, siblingRun, ⟨1⟩, .instrumentedLog⟩

private def comparisonKind (keys : List Source.KindKey) (argument : Presentation.ArgId) :=
  Source.nodeKind comparisonSource comparisonCompletion.history observedComparisonSpecs
    comparisonAssumptions [.instrumentedLog] keys argument (.leaf ⟨"support"⟩)

/-- Both generated arguments have complete, observed metadata and a matching
admitted capture. Only their source-choice provenance forces the hypothetical cap. -/
theorem comparison_observed_metadata_capped :
    comparisonCompletion ∈ referenceFamily comparisonFamily ∧
    comparisonKind [] selectedComparison.recheckArg = (.observed, true) ∧
    comparisonKind [] selectedComparison.bridgeArg = (.observed, true) ∧
    comparisonKind (selectedKeys comparisonCompletion) selectedComparison.recheckArg =
      (.hypothetical, true) ∧
    comparisonKind (selectedKeys comparisonCompletion) selectedComparison.bridgeArg =
      (.hypothetical, true) := by decide +kernel

end Lara.Examples.ProcessFamily
