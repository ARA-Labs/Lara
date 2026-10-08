import Lara.BHL.Belief
import Lara.BHL.ModelLaws

namespace Lara.BHL

noncomputable section

variable {D Command : Type} [MeasurableSpace D] {context : List GhostSort}
variable (I : AssertionInterpretation D Command) (M : Model D Command)
  (env : GhostEnv D Command context)

theorem observationInvariant_ghost (term : GhostTerm context sort) :
    ObservationInvariantTerm I M env (.ghost term) := by
  intro left right _
  rfl

theorem observationInvariant_datasetRead (name : DatasetId) :
    ObservationInvariantTerm I M env (.datasetRead .ambient name) := by
  intro left right h
  change some (left.current.datasets name) = some (right.current.datasets name)
  exact congrArg some (accessible_dataset_eq h name)

theorem fixedRealTerm_ghost (term : GhostTerm context (.value .real)) :
    FixedRealTerm I M env (.ghost term) (term.eval I env) := by
  intro view
  rfl

theorem fixedRealTerm_rational (value : ℚ) :
    FixedRealTerm I M env (.rational value) (value : ℝ) := by
  intro view
  rfl

theorem observableTest_entries_invariant (test : TestExpression context)
    (hobs : ObservableTestExpression I M env test)
    {left right : World D Command} (h : Accessible left right) :
    evalTestEntries I M env (semanticView M.dynamics left) test =
      evalTestEntries I M env (semanticView M.dynamics right) test := by
  cases test with
  | leaf hypothesis data test population =>
      exact congrArg (fun result => result.map (fun d => [(d, test, population)]))
        (hobs left right h)
  | disj name a b =>
      simp only [evalTestEntries,
        observableTest_entries_invariant a hobs.1 h,
        observableTest_entries_invariant b hobs.2 h]
  | conj name a b =>
      simp only [evalTestEntries,
        observableTest_entries_invariant a hobs.1 h,
        observableTest_entries_invariant b hobs.2 h]
termination_by structural test

theorem observableTest_history_invariant (test : TestExpression context)
    (hobs : ObservableTestExpression I M env test)
    {left right : World D Command} (h : Accessible left right) :
    evalTestHistory I M env (semanticView M.dynamics left) test =
      evalTestHistory I M env (semanticView M.dynamics right) test := by
  unfold evalTestHistory
  rw [observableTest_entries_invariant I M env test hobs h]

theorem observableTest_event_invariant (test : TestExpression context)
    (hobs : ObservableTestExpression I M env test)
    {left right : World D Command} (h : Accessible left right) :
    evalNumericalEvent I M env (semanticView M.dynamics left) test =
      evalNumericalEvent I M env (semanticView M.dynamics right) test := by
  cases test with
  | leaf hypothesis data test population =>
      exact congrArg (fun result => result.map (fun d =>
        (⟨.real, NumericalEvent.tail (I.tests hypothesis test) d⟩ : PackedNumericalEvent)))
        (hobs left right h)
  | disj name a b =>
      simp only [evalNumericalEvent,
        observableTest_event_invariant a hobs.1 h,
        observableTest_event_invariant b hobs.2 h]
  | conj name a b =>
      simp only [evalNumericalEvent,
        observableTest_event_invariant a hobs.1 h,
        observableTest_event_invariant b hobs.2 h]
termination_by structural test

theorem observationInvariant_pvalue (test : TestExpression context)
    (hobs : ObservableTestExpression I M env test) :
    ObservationInvariantTerm I M env (.pvalue test) := by
  intro left right h
  unfold evalTerm
  rw [observableTest_event_invariant I M env test hobs h]

theorem evalTestHistory_leaf (view : SemanticView D) (hypothesis : HypothesisId)
    (data : AssertionTerm context .dataset) (test : TestId) (population : PopulationId) :
    evalTestHistory I M env view (.leaf hypothesis data test population) =
      (evalTerm I M env view data).map (fun d => {(d, test)}) := by
  cases h : evalTerm I M env view data <;>
    simp [evalTestHistory, evalTestEntries, h]

theorem evalTestHistory_disj (view : SemanticView D) (name : CouplingId)
    (left right : TestExpression context) :
    evalTestHistory I M env view (.disj name left right) =
      (do let a ← evalTestHistory I M env view left
          let b ← evalTestHistory I M env view right
          pure (a + b)) := by
  cases ha : evalTestEntries I M env view left <;>
    cases hb : evalTestEntries I M env view right <;>
    simp [evalTestHistory, evalTestEntries, ha, hb, List.map_append]

theorem evalTestHistory_conj (view : SemanticView D) (name : CouplingId)
    (left right : TestExpression context) :
    evalTestHistory I M env view (.conj name left right) =
      (do let a ← evalTestHistory I M env view left
          let b ← evalTestHistory I M env view right
          pure (a + b)) := by
  cases ha : evalTestEntries I M env view left <;>
    cases hb : evalTestEntries I M env view right <;>
    simp [evalTestHistory, evalTestEntries, ha, hb, List.map_append]

theorem eval_testHistoryTerm (view : SemanticView D) (test : TestExpression context) :
    evalTerm I M env view (testHistoryTerm test) = evalTestHistory I M env view test := by
  cases test with
  | leaf hypothesis data test population =>
      exact (evalTestHistory_leaf I M env view hypothesis data test population).symm
  | disj name left right =>
      rw [evalTestHistory_disj]
      simp only [testHistoryTerm, evalTerm,
        eval_testHistoryTerm view left, eval_testHistoryTerm view right]
  | conj name left right =>
      rw [evalTestHistory_conj]
      simp only [testHistoryTerm, evalTerm,
        eval_testHistoryTerm view left, eval_testHistoryTerm view right]
termination_by structural test

theorem exactHistory_iff_ledger (world : World D Command) (test : TestExpression context) :
    referenceModalSatisfaction I M env world (exactHistory test) ↔
      evalTestHistory I M env (semanticView M.dynamics world) test =
        some world.current.history := by
  change (∃ history, some world.current.history = some history ∧
    evalTerm I M env (semanticView M.dynamics world) (testHistoryTerm test) = some history) ↔ _
  rw [eval_testHistoryTerm]
  simp only [Option.some.injEq, exists_eq_left']

/-- Composite exact history accounts for all entries, including duplicate leaves. -/
theorem exactHistory_disj_iff (world : World D Command) (name : CouplingId)
    (left right : TestExpression context) :
    referenceModalSatisfaction I M env world (exactHistory (.disj name left right)) ↔
      ∃ a b, evalTestHistory I M env (semanticView M.dynamics world) left = some a ∧
        evalTestHistory I M env (semanticView M.dynamics world) right = some b ∧
        world.current.history = a + b := by
  rw [exactHistory_iff_ledger, evalTestHistory_disj]
  cases evalTestHistory I M env (semanticView M.dynamics world) left <;>
    cases evalTestHistory I M env (semanticView M.dynamics world) right <;>
    simp [eq_comm]

theorem exactHistory_conj_iff (world : World D Command) (name : CouplingId)
    (left right : TestExpression context) :
    referenceModalSatisfaction I M env world (exactHistory (.conj name left right)) ↔
      ∃ a b, evalTestHistory I M env (semanticView M.dynamics world) left = some a ∧
        evalTestHistory I M env (semanticView M.dynamics world) right = some b ∧
        world.current.history = a + b := by
  rw [exactHistory_iff_ledger, evalTestHistory_conj]
  cases evalTestHistory I M env (semanticView M.dynamics world) left <;>
    cases evalTestHistory I M env (semanticView M.dynamics world) right <;>
    simp [eq_comm]

theorem evalNumericalEvent_disj_of_coupling (view : SemanticView D) (name : CouplingId)
    (left right : TestExpression context) (a b : PackedNumericalEvent)
    (coupling : ProbabilityCoupling a.2.law b.2.law)
    (ha : evalNumericalEvent I M env view left = some a)
    (hb : evalNumericalEvent I M env view right = some b)
    (hc : I.couplings name a.1 b.1 a.2.law b.2.law = some coupling) :
    evalNumericalEvent I M env view (.disj name left right) =
      some ⟨.product a.1 b.1, NumericalEvent.union a.2 b.2 coupling⟩ := by
  simp [evalNumericalEvent, ha, hb, hc]

theorem evalNumericalEvent_conj_of_coupling (view : SemanticView D) (name : CouplingId)
    (left right : TestExpression context) (a b : PackedNumericalEvent)
    (coupling : ProbabilityCoupling a.2.law b.2.law)
    (ha : evalNumericalEvent I M env view left = some a)
    (hb : evalNumericalEvent I M env view right = some b)
    (hc : I.couplings name a.1 b.1 a.2.law b.2.law = some coupling) :
    evalNumericalEvent I M env view (.conj name left right) =
      some ⟨.product a.1 b.1, NumericalEvent.intersection a.2 b.2 coupling⟩ := by
  simp [evalNumericalEvent, ha, hb, hc]

theorem exactHistory_iff_entries (world : World D Command) (test : TestExpression context) :
    referenceModalSatisfaction I M env world (exactHistory test) ↔
      ∃ entries, evalTestEntries I M env (semanticView M.dynamics world) test = some entries ∧
        world.current.history =
          (entries.map (fun entry => (entry.1, entry.2.1)) : History D) := by
  rw [exactHistory_iff_ledger]
  cases he : evalTestEntries I M env (semanticView M.dynamics world) test <;>
    simp [evalTestHistory, he, eq_comm]

theorem evalTestHistory_repeated_disj (view : SemanticView D) (name : CouplingId)
    (test : TestExpression context) (history : History D)
    (h : evalTestHistory I M env view test = some history) :
    evalTestHistory I M env view (.disj name test test) = some (history + history) := by
  rw [evalTestHistory_disj, h]
  rfl

theorem evalTestHistory_repeated_conj (view : SemanticView D) (name : CouplingId)
    (test : TestExpression context) (history : History D)
    (h : evalTestHistory I M env view test = some history) :
    evalTestHistory I M env view (.conj name test test) = some (history + history) := by
  rw [evalTestHistory_conj, h]
  rfl

/-- Two occurrences of one leaf are two ledger entries, even if they alias. -/
theorem exactHistory_repeated_leaf_card (world : World D Command) (name : CouplingId)
    (hypothesis : HypothesisId) (data : AssertionTerm context .dataset)
    (test : TestId) (population : PopulationId) (d : D)
    (hdata : evalTerm I M env (semanticView M.dynamics world) data = some d)
    (hhistory : referenceModalSatisfaction I M env world
      (exactHistory (.disj name (.leaf hypothesis data test population)
        (.leaf hypothesis data test population)))) :
    Multiset.card world.current.history = 2 := by
  have hleaf : evalTestHistory I M env (semanticView M.dynamics world)
      (.leaf hypothesis data test population) = some {(d, test)} := by
    rw [evalTestHistory_leaf, hdata]
    rfl
  have hfull := (exactHistory_iff_ledger I M env world
    (.disj name (.leaf hypothesis data test population)
      (.leaf hypothesis data test population))).mp hhistory
  rw [evalTestHistory_repeated_disj I M env (semanticView M.dynamics world) name
    (.leaf hypothesis data test population) {(d, test)} hleaf] at hfull
  have hledger := Option.some.inj hfull
  rw [← hledger]
  simp

end
end Lara.BHL
