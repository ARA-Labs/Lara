import Lara.Process.Order
import Lara.BHL.Trace

/-!
The process view of a BHL world and its test-event projection.

A BHL `World` keeps its ordered state trace; its ledger `History` is a multiset.
`testProjection` reads the test events off the trace as the consecutive ledger
increments and sums them. For every admitted world that sum is exactly the
final ledger (`admitted_testProjection`). `AnnotatedWorld` attaches a process
event and its test occurrences to each trace step, faithfully to the ledger
increments; `AnnotatedWorld.tests_sum` and `AnnotatedWorld.test_from_run` then
show the annotated tests are exactly the BHL `History` and that every test
occurrence comes from a run event of the valid process history.

`ArtifactBinding` still reads the multiset `History`; moving it to the ordered
view would touch every bridge theorem and is not done here.
-/

namespace Lara.Process

open Lara.BHL

variable {D Command : Type} [DecidableEq D]

/-- The ledger increment of each step of a state trace. -/
def ledgerDeltas : List (State D Command) → List (History D)
  | s :: t :: rest => (t.history - s.history) :: ledgerDeltas (t :: rest)
  | _ => []

/-- Along a trace whose ledgers only grow, the first ledger plus every increment
is the last ledger. -/
theorem ledgerDeltas_sum : ∀ (s : State D Command) (rest : List (State D Command)),
    List.IsChain (fun a b : State D Command => a.history ≤ b.history) (s :: rest) →
      s.history + (ledgerDeltas (s :: rest)).sum = ((s :: rest).getLast (by simp)).history
  | s, [], _ => by simp [ledgerDeltas]
  | s, t :: rest, chain => by
      rw [List.isChain_cons_cons] at chain
      have ih := ledgerDeltas_sum t rest chain.2
      simp only [ledgerDeltas, List.sum_cons, List.getLast_cons_cons]
      rw [← add_assoc, add_tsub_cancel_of_le chain.1, ih]

/-- The test events of a world, read off its ordered trace. -/
def testProjection (world : World D Command) : History D :=
  (ledgerDeltas world.trace).sum

/-- A world whose ledgers only grow along its trace projects to its final
ledger. -/
theorem testProjection_eq (world : World D Command)
    (mono : List.IsChain (fun a b : State D Command => a.history ≤ b.history) world.trace) :
    testProjection world = world.current.history := by
  have sum := ledgerDeltas_sum world.initial world.rest mono
  rw [world.initial_history_empty, zero_add] at sum
  exact sum

omit [DecidableEq D] in
/-- Locally allowed observation edges only grow the ledger. -/
theorem traceEdges_chain {dynamics : Dynamics D Command} {hidden : HiddenMemory} :
    ∀ {before : Observation D Command} {rest : List (Observation D Command)},
      TraceEdges dynamics hidden before rest →
        List.IsChain (fun a b : Observation D Command => a.history ≤ b.history) (before :: rest)
  | before, [], _ => List.IsChain.singleton before
  | before, after :: rest, ⟨edge, edges⟩ => by
      refine List.IsChain.cons_cons ?_ (traceEdges_chain edges)
      unfold AllowedEdge at edge
      split at edge
      · exact edge.elim
      · obtain ⟨delta, _, history⟩ := edge
        rw [history]
        exact le_add_right le_rfl
      · rw [edge.2]

/-- Every admitted world's test projection is its final ledger: the ordered
process view agrees with the multiset `History`. -/
theorem admitted_testProjection {dynamics : Dynamics D Command} {world : World D Command}
    (admitted : Admitted dynamics world) : testProjection world = world.current.history := by
  apply testProjection_eq
  have allowed := admitted.2
  simp only [observeWorld, World.trace, List.map_cons, TraceAllowed] at allowed
  have chain := traceEdges_chain allowed.2.2.2
  rw [← List.map_cons] at chain
  exact (List.isChain_map observeState).mp chain

/-- One ledger increment per non-initial trace step. -/
theorem ledgerDeltas_length : ∀ (s : State D Command) (rest : List (State D Command)),
    (ledgerDeltas (s :: rest)).length = rest.length
  | _, [] => rfl
  | _, t :: rest => by
      simp only [ledgerDeltas, List.length_cons]
      rw [ledgerDeltas_length t rest]

omit [DecidableEq D] in
/-- A test occurrence in a sum of ledgers occurs in one of them. -/
theorem mem_list_sum {t : D × TestId} : ∀ {l : List (History D)}, t ∈ l.sum → ∃ m ∈ l, t ∈ m
  | [], h => absurd h (by simp)
  | m :: l, h => by
      rw [List.sum_cons, Multiset.mem_add] at h
      rcases h with h | h
      · exact ⟨m, List.mem_cons_self, h⟩
      · obtain ⟨m', hm', ht⟩ := mem_list_sum h
        exact ⟨m', List.mem_cons_of_mem _ hm', ht⟩

/-- The process annotation of one trace step: the process event it realizes,
if any, and the test occurrences it adds to the ledger. -/
structure StepAnnotation (D : Type) where
  event : Option Stamped
  tests : History D

/-- A BHL world annotated step by step with process events. The annotation is
faithful to the trace: each step's tests are exactly that step's ledger
increment, tests occur only at run events, and the annotated events form a
valid process history in trace order. -/
structure AnnotatedWorld (D Command : Type) [DecidableEq D] where
  world : World D Command
  steps : List (StepAnnotation D)
  faithful : ledgerDeltas world.trace = steps.map StepAnnotation.tests
  testsOnRuns : ∀ s ∈ steps, s.tests ≠ 0 →
    ∃ e spec, s.event = some e ∧ e.event.runSpec? = some spec
  valid : ValidHistory (steps.filterMap StepAnnotation.event)

namespace AnnotatedWorld

/-- The process history of an annotated world, in trace order. -/
def process (a : AnnotatedWorld D Command) : ProcessHistory :=
  a.steps.filterMap StepAnnotation.event

/-- One annotation per non-initial trace step. -/
theorem steps_length (a : AnnotatedWorld D Command) : a.steps.length = a.world.rest.length := by
  have := congrArg List.length a.faithful
  rw [List.length_map] at this
  rw [← this]
  exact ledgerDeltas_length a.world.initial a.world.rest

/-- For an admitted world, the annotated tests sum to the BHL ledger. -/
theorem tests_sum {dynamics : Dynamics D Command} (a : AnnotatedWorld D Command)
    (admitted : Admitted dynamics a.world) :
    (a.steps.map StepAnnotation.tests).sum = a.world.current.history := by
  rw [← a.faithful]
  exact admitted_testProjection admitted

/-- Every test occurrence in the BHL ledger of an admitted world was added at a
step annotated with a run event of the process history. -/
theorem test_from_run {dynamics : Dynamics D Command} (a : AnnotatedWorld D Command)
    (admitted : Admitted dynamics a.world) {t : D × TestId}
    (mem : t ∈ a.world.current.history) :
    ∃ s ∈ a.steps, t ∈ s.tests ∧ ∃ e spec, s.event = some e ∧ e.event.runSpec? = some spec ∧
      e ∈ a.process := by
  rw [← a.tests_sum admitted] at mem
  obtain ⟨tests, hmem, ht⟩ := mem_list_sum mem
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hmem
  have nonzero : s.tests ≠ 0 := fun z => by rw [z] at ht; exact Multiset.notMem_zero _ ht
  obtain ⟨e, spec, he, hspec⟩ := a.testsOnRuns s hs nonzero
  exact ⟨s, hs, ht, e, spec, he, hspec, List.mem_filterMap.mpr ⟨s, hs, he⟩⟩

end AnnotatedWorld

end Lara.Process
