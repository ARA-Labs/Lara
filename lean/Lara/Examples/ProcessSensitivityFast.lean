import Lara.Process.Analysis
import Lara.Examples.ProcessSource

/-! Small kernel-checked semantic fixtures for sparse slot sensitivity. The
large fixture evaluates only the sparse procedure; it never reduces the powerset
reference. These are implementation checks, not inquiry measurements. -/
namespace Lara.Examples.ProcessSensitivityFast

open Lara.Process Lara.Process.Source Lara.Process.Family Lara.Process.Analysis

private def base : SourceInput :=
  let surface := ProcessSource.ordinaryInput
  { surface
    replay := ⟨⟨Driver.coreVersionText⟩, surface.policy.id, [], [], surface.program.digest⟩
    capture := none }

private def spec (ids : List Nat) : FamilySpec :=
  ⟨⟨⟨[], [], [], [], 10⟩, []⟩, base, ids.map fun n => ⟨⟨n⟩, []⟩⟩

private def choice : Choice := ⟨⟨0⟩, .truth, []⟩
private def otherChoice : Choice := ⟨⟨1⟩, .truth, []⟩
private def completion (ids : List Nat) : Completion :=
  ⟨[], ids.map fun n => ⟨⟨n⟩, choice⟩⟩
private def reference : Completion := completion []
private def rejectedRead (c : Completion) : Except SourceRejection Bool :=
  if c = reference then .ok false else .error (.missingEvidence ⟨"missing"⟩)
private def event : Stamped := ⟨⟨0⟩, .retract ⟨0⟩⟩

/-- No differing observation means no minimal set. -/
theorem no_flips :
    minimalSlotSetsFast (spec [9, 2, 7]) [reference, completion [2]]
      (fun _ => .ok false) reference = [] ∧
    minimalSlotSets (spec [9, 2, 7]) [reference, completion [2]]
      (fun _ => .ok false) reference = [] := by
  simp only [minimalSlotSetsFast_eq_minimalSlotSets]
  decide +kernel

/-- A differing observation from another history cannot witness a slot flip. -/
theorem history_mismatch :
    minimalSlotSetsFast (spec [9]) [⟨[event], [⟨⟨9⟩, choice⟩]⟩]
      rejectedRead reference = [] ∧
    minimalSlotSets (spec [9]) [⟨[event], [⟨⟨9⟩, choice⟩]⟩]
      rejectedRead reference = [] := by
  simp only [minimalSlotSetsFast_eq_minimalSlotSets]
  decide +kernel

private def rows : List Completion :=
  [reference, completion [9], completion [2, 7, 100], completion [2, 7], completion [2, 7]]

/-- Last-occurrence dedup leaves [2,7,9]. The size-two and size-one minima are
incomparable, and colex puts the pair first despite numeric IDs and row order. -/
theorem incomparable_sizes_and_declaration_order :
    slotUniverse (spec [9, 2, 7, 9]) = [⟨2⟩, ⟨7⟩, ⟨9⟩] ∧
    minimalSlotSetsFast (spec [9, 2, 7, 9]) rows rejectedRead reference =
      [[⟨2⟩, ⟨7⟩], [⟨9⟩]] ∧
    minimalSlotSets (spec [9, 2, 7, 9]) rows rejectedRead reference =
      [[⟨2⟩, ⟨7⟩], [⟨9⟩]] := by
  simp only [minimalSlotSetsFast_eq_minimalSlotSets]
  decide +kernel

/-- Numeric SlotId sorting would reverse these singleton minima. -/
theorem nonnumeric_singleton_order :
    minimalSlotSetsFast (spec [9, 2, 7]) [completion [7], completion [9]]
      rejectedRead reference = [[⟨9⟩], [⟨7⟩]] ∧
    minimalSlotSets (spec [9, 2, 7]) [completion [7], completion [9]]
      rejectedRead reference = [[⟨9⟩], [⟨7⟩]] := by
  simp only [minimalSlotSetsFast_eq_minimalSlotSets]
  decide +kernel

/-- Rejections count as differing observations; duplicate rows survive, and
realization picks the first completion even when a later one has fewer fields. -/
theorem first_realizer_and_duplicate_rows :
    let result := sensitivityResultFast () (spec [9, 2, 7, 9]) rows rejectedRead reference
    result.total = 5 ∧ result.sensitive = 4 ∧
    result.differing.map SensitivityRow.completion =
      [completion [9], completion [2, 7, 100], completion [2, 7], completion [2, 7]] ∧
    result.realizing = [([⟨2⟩, ⟨7⟩], completion [2, 7, 100]), ([⟨9⟩], completion [9])] :=
  by
    simp only [sensitivityResultFast_eq_sensitivityResult]
    decide +kernel

/-- A changed completion outside the declared universe has an empty changed
set; every declared singleton is then minimal in declaration order. -/
theorem empty_changed_nonempty_universe :
    minimalSlotSetsFast (spec [9, 2, 9]) [completion [100]] rejectedRead reference =
      [[⟨2⟩], [⟨9⟩]] ∧
    minimalSlotSets (spec [9, 2, 9]) [completion [100]] rejectedRead reference =
      [[⟨2⟩], [⟨9⟩]] := by
  simp only [minimalSlotSetsFast_eq_minimalSlotSets]
  decide +kernel

/-- An empty universe still has no nonempty minimal set. -/
theorem empty_changed_empty_universe :
    minimalSlotSetsFast (spec []) [completion [100]] rejectedRead reference = [] ∧
    minimalSlotSets (spec []) [completion [100]] rejectedRead reference = [] := by
  simp only [minimalSlotSetsFast_eq_minimalSlotSets]
  decide +kernel

private def fragmentChoice : Choice :=
  ⟨⟨0⟩, .truth, [.claim ⟨⟨"c"⟩, "c", .atom "a" .nil, ⟨"r", "i", .reviewed⟩⟩]⟩
private def fragmentCompletion : Completion := ⟨[], [⟨⟨9⟩, fragmentChoice⟩]⟩
private def fragmentRead (c : Completion) : Except SourceRejection Bool :=
  .ok (decide (c = fragmentCompletion))

/-- Whole choices, including fragments, determine changes even if choice IDs
are identical. -/
theorem same_choice_id_changed_fragment :
    minimalSlotSetsFast (spec [9]) [completion [9], fragmentCompletion]
      fragmentRead (completion [9]) = [[⟨9⟩]] ∧
    minimalSlotSets (spec [9]) [completion [9], fragmentCompletion]
      fragmentRead (completion [9]) = [[⟨9⟩]] := by
  simp only [minimalSlotSetsFast_eq_minimalSlotSets]
  decide +kernel

/-- Independently execute fast and powerset computations on small cases. The
explicit output assertions also check canonical order and first realizers. -/
def smallSparseCheck : Bool :=
  let agrees := fun family cs read ref =>
    decide (minimalSlotSetsFast family cs read ref = minimalSlotSets family cs read ref)
  let result := sensitivityResultFast () (spec [9, 2, 7, 9]) rows rejectedRead reference
  agrees (spec [9, 2, 7]) [reference, completion [2]] (fun _ => .ok false) reference &&
  agrees (spec [9]) [⟨[event], [⟨⟨9⟩, choice⟩]⟩] rejectedRead reference &&
  agrees (spec [9, 2, 7, 9]) rows rejectedRead reference &&
  agrees (spec [9, 2, 7]) [completion [7], completion [9]] rejectedRead reference &&
  decide (minimalSlotSetsFast (spec [9, 2, 7]) [completion [7], completion [9]]
    rejectedRead reference = [[⟨9⟩], [⟨7⟩]]) &&
  agrees (spec [9, 2, 9]) [completion [100]] rejectedRead reference &&
  agrees (spec []) [completion [100]] rejectedRead reference &&
  agrees (spec [9]) [completion [9], fragmentCompletion] fragmentRead (completion [9]) &&
  decide (result.minimalSlotSets = [[⟨2⟩, ⟨7⟩], [⟨9⟩]] ∧ result.total = 5 ∧ result.sensitive = 4 ∧
    result.differing.map SensitivityRow.completion =
      [completion [9], completion [2, 7, 100], completion [2, 7], completion [2, 7]] ∧
    result.realizing = [([⟨2⟩, ⟨7⟩], completion [2, 7, 100]), ([⟨9⟩], completion [9])])

/-- Forty inert slots and two varying slots, with six completion rows. -/
private def largeSpec : FamilySpec := spec ([91, 3] ++ (List.range 40).map (· + 200))
private def largeRows : List Completion :=
  [reference, completion [91], completion [3], completion [91, 3],
   ⟨[], [⟨⟨91⟩, otherChoice⟩]⟩, ⟨[], [⟨⟨3⟩, otherChoice⟩]⟩]

/-- A compiled implementation check with an independently specified result. -/
def largeSparseCheck : Bool :=
  let result := sensitivityResultFast () largeSpec largeRows rejectedRead reference
  decide (result.total = 6 ∧ result.sensitive = 5 ∧
    result.differing.length = 5 ∧ result.minimalSlotSets = [[⟨91⟩], [⟨3⟩]] ∧
    result.realizing = [([⟨91⟩], completion [91]), ([⟨3⟩], completion [3])])

#eval do
  unless smallSparseCheck do
    throw (IO.userError "small sparse sensitivity conformance checks failed")
  IO.println "small sparse sensitivity conformance checks passed"
  unless largeSparseCheck do
    throw (IO.userError "42-slot sparse sensitivity implementation check failed")
  IO.println "42-slot sparse sensitivity implementation check passed (6 completions)"

end Lara.Examples.ProcessSensitivityFast
