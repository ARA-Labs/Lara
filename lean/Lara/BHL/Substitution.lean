import Lara.BHL.AssertionLaws

namespace Lara.BHL

/-- Undefined primitive evaluation has no successor. A defined target is scoped
at its realized semantic view, including for nested knowledge and outer binders. -/
def liberalPreimage (target : AssertionTerm context .view) (post : Assertion context) :
    Assertion context :=
  Assertion.disj (.neg (.modal (.atom (.defined target)))) (.atView target post)

/-- The right-hand side is evaluated in the pre-state, not in the written view. -/
def assignmentView (x : Variable sort .observable)
    (rhs : AssertionTerm context (.value sort)) : AssertionTerm context .view :=
  .writeValue .ambient x rhs

def datasetAssignmentView (name : DatasetId) (rhs : AssertionTerm context .dataset) :
    AssertionTerm context .view := .writeDataset .ambient name rhs

/-- Each right-hand side refers to the original ambient view. Ordered writes
permit repeated targets; the last write wins, without reevaluating earlier RHSs. -/
structure SimultaneousWrite (context : List GhostSort) where
  sort : ValueSort
  target : Variable sort .observable
  rhs : AssertionTerm context (.value sort)

def simultaneousAssignmentView (writes : List (SimultaneousWrite context)) :
    AssertionTerm context .view :=
  writes.foldl (fun target write => .writeValue target write.target write.rhs) .ambient

/-- The numeric report and recorded dataset are both pre-state evaluations.
History is the complete ledger, incremented exactly once by this leaf test. -/
def testAssignmentView (result : Variable .real .observable)
    (hypothesis : HypothesisId) (data : AssertionTerm context .dataset)
    (test : TestId) (population : PopulationId) : AssertionTerm context .view :=
  .addHistory (.writeValue .ambient result (.pvalue (.leaf hypothesis data test population)))
    (.historySingleton data test)

def assignmentPreimage (x : Variable sort .observable)
    (rhs : AssertionTerm context (.value sort)) (post : Assertion context) : Assertion context :=
  liberalPreimage (assignmentView x rhs) post

def simultaneousAssignmentPreimage (writes : List (SimultaneousWrite context))
    (post : Assertion context) : Assertion context :=
  liberalPreimage (simultaneousAssignmentView writes) post

def testPreimage (result : Variable .real .observable) (hypothesis : HypothesisId)
    (data : AssertionTerm context .dataset) (test : TestId) (population : PopulationId)
    (post : Assertion context) : Assertion context :=
  liberalPreimage (testAssignmentView result hypothesis data test population) post

noncomputable section
variable {D Command : Type} [mD : MeasurableSpace D]

/-- The syntax describes the liberal preimage of the independent partial term
relation. Realizability is checked, not silently assumed for synthetic views. -/
theorem view_liberalPreimage_iff (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (view : SemanticView D)
    (target : AssertionTerm context .view) (post : Assertion context) :
    viewAssertionSatisfaction interpretation model env view (liberalPreimage target post) ↔
      ∀ after, evalTerm interpretation model env view target = some after →
        satisfiesView interpretation model env after post := by
  classical
  rw [liberalPreimage, viewAssertionSatisfaction_disj]
  change (¬ (∃ after, evalTerm interpretation model env view target = some after)) ∨
    (∃ after, evalTerm interpretation model env view target = some after ∧
      after ∈ model.views ∧ viewAssertionSatisfaction interpretation model env after post) ↔ _
  cases evalTerm interpretation model env view target with
  | none => simp
  | some after => simp [satisfiesView]

theorem reference_liberalPreimage_iff (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (world : World D Command)
    (target : AssertionTerm context .view) (post : Assertion context) :
    referenceAssertionSatisfaction interpretation model env world (liberalPreimage target post) ↔
      ∀ after, evalTerm interpretation model env (semanticView model.dynamics world) target = some after →
        satisfiesView interpretation model env after post := by
  rw [reference_view_assertion_correspondence, view_liberalPreimage_iff]

theorem liberalPreimage_undefined (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (world : World D Command)
    (target : AssertionTerm context .view) (post : Assertion context)
    (undefined : evalTerm interpretation model env (semanticView model.dynamics world) target = none) :
    referenceAssertionSatisfaction interpretation model env world (liberalPreimage target post) := by
  rw [reference_liberalPreimage_iff]
  intro after heval
  rw [undefined] at heval
  contradiction

/-- Any legal Assertion postcondition is allowed, including outer binders and
arbitrary modal depth; quantifiers beneath K remain excluded by the grammar. -/
theorem liberalPreimage_successor_iff (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context)
    (before after : World D Command) (hadmitted : Admitted model.dynamics after)
    (target : AssertionTerm context .view) (post : Assertion context)
    (effect : evalTerm interpretation model env (semanticView model.dynamics before) target =
      some (semanticView model.dynamics after)) :
    referenceAssertionSatisfaction interpretation model env before (liberalPreimage target post) ↔
      satisfies interpretation model env after post := by
  rw [reference_liberalPreimage_iff]
  simp only [effect, Option.some.injEq, forall_eq']
  exact (satisfies_view_iff interpretation model env after hadmitted post).symm

@[simp] theorem eval_assignmentView (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (view : SemanticView D)
    (x : Variable sort .observable) (rhs : AssertionTerm context (.value sort)) :
    evalTerm interpretation model env view (assignmentView x rhs) =
      (evalTerm interpretation model env view rhs).map (writeViewValue view x) := by
  simp only [assignmentView, evalTerm]
  cases evalTerm interpretation model env view rhs <;> rfl

@[simp] theorem eval_datasetAssignmentView (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (view : SemanticView D)
    (name : DatasetId) (rhs : AssertionTerm context .dataset) :
    evalTerm interpretation model env view (datasetAssignmentView name rhs) =
      (evalTerm interpretation model env view rhs).map (writeViewDataset view name) := by
  simp only [datasetAssignmentView, evalTerm]
  cases evalTerm interpretation model env view rhs <;> rfl

/-- Partial local view effects evaluate every RHS against one pre-state. -/
def evalSimultaneousWrites (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (before : SemanticView D) :
    SemanticView D → List (SimultaneousWrite context) → Option (SemanticView D)
  | after, [] => some after
  | after, write :: rest => do
      let value ← evalTerm interpretation model env before write.rhs
      evalSimultaneousWrites interpretation model env before
        (writeViewValue after write.target value) rest

theorem eval_simultaneous_fold (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (before : SemanticView D)
    (writes : List (SimultaneousWrite context)) (target : AssertionTerm context .view) :
    evalTerm interpretation model env before
      (writes.foldl (fun target write => .writeValue target write.target write.rhs) target) =
      (evalTerm interpretation model env before target).bind
        (fun after => evalSimultaneousWrites interpretation model env before after writes) := by
  induction writes generalizing target with
  | nil => simp [evalSimultaneousWrites]
  | cons write rest ih =>
      rw [List.foldl_cons, ih]
      simp only [evalTerm, evalSimultaneousWrites]
      cases ht : evalTerm interpretation model env before target <;>
        cases hr : evalTerm interpretation model env before write.rhs <;> rfl

@[simp] theorem eval_simultaneousAssignmentView
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (view : SemanticView D)
    (writes : List (SimultaneousWrite context)) :
    evalTerm interpretation model env view (simultaneousAssignmentView writes) =
      evalSimultaneousWrites interpretation model env view view writes := by
  rw [simultaneousAssignmentView, eval_simultaneous_fold]
  rfl

theorem simultaneous_writes_preserve_information
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (before : SemanticView D)
    (writes : List (SimultaneousWrite context)) (start after : SemanticView D)
    (evaluated : evalSimultaneousWrites interpretation model env before start writes = some after) :
    after.history = start.history ∧ after.hidden = start.hidden ∧
      after.compatible = start.compatible ∧ after.provenance = start.provenance ∧
      after.visible.datasets = start.visible.datasets := by
  induction writes generalizing start with
  | nil =>
      have h : start = after := Option.some.inj evaluated
      subst after
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons write rest ih =>
      simp only [evalSimultaneousWrites] at evaluated
      cases heval : evalTerm interpretation model env before write.rhs with
      | none => simp [heval] at evaluated
      | some value =>
          simp only [heval] at evaluated
          exact ih (writeViewValue start write.target value) evaluated


@[simp] theorem eval_testAssignmentView (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (view : SemanticView D)
    (result : Variable .real .observable) (hypothesis : HypothesisId)
    (data : AssertionTerm context .dataset) (test : TestId) (population : PopulationId) :
    evalTerm interpretation model env view
      (testAssignmentView result hypothesis data test population) =
      (evalTerm interpretation model env view data).map (fun d =>
        {(writeViewValue view result ((interpretation.tests hypothesis test).tailProbability d)) with
          history := view.history + {(d, test)}}) := by
  simp only [testAssignmentView, evalTerm, evalNumericalEvent]
  cases hd : evalTerm interpretation model env view data <;>
    simp [NumericalEvent.tail_probability, writeViewValue]

omit mD in
/-- The independent command effect and hidden preservation reconstruct a legal
full-world successor. No command relation is defined by a desired assertion. -/
theorem command_successor_admitted (model : Model D Command) {world : World D Command}
    (admitted : Admitted model.dynamics world) (after : State D Command) (command : Command)
    (action : after.action = .command command)
    (hidden : after.memory.hidden = world.current.memory.hidden)
    (effect : ∃ delta, model.dynamics.command command world.current.visible =
      some (after.visible, delta) ∧ after.history = world.current.history + delta) :
    Admitted model.dynamics (world.extend after) := by
  apply admitted_extend admitted after
  · exact hidden.trans (admitted_current_hidden admitted)
  · simp only [AllowedEdge, observeState, action]
    exact effect

omit mD in
theorem command_successor_view (model : Model D Command) (world : World D Command)
    (after : State D Command) (command : Command) (action : after.action = .command command)
    (hidden : after.memory.hidden = world.current.memory.hidden)
    (effect : ∃ delta, model.dynamics.command command world.current.visible =
      some (after.visible, delta) ∧ after.history = world.current.history + delta) :
    semanticView model.dynamics (world.extend after) =
      {semanticView model.dynamics world with visible := after.visible, history := after.history} := by
  simp only [semanticView, World.extend_current, hidden,
    compatibleHidden_extend_command model.dynamics world after command action effect,
    World.samplingProvenance_extend_command world after command action]

omit mD in
theorem hidden_observable_write (memory : Memory) (x : Variable sort .observable)
    (value : Value sort) : (memory.update x (some value)).hidden = memory.hidden := by
  funext s id
  exact Memory.read_update_invisible memory x (some value) ⟨id⟩

/-- Concrete single-cell command effects, separate from assertion interpretation. -/
def assignmentState (before : State D Command) (command : Command)
    (x : Variable sort .observable) (value : Value sort) : State D Command :=
  {before with memory := before.memory.update x (some value), action := .command command}

def testState (before : State D Command) (command : Command)
    (result : Variable .real .observable) (value : ℝ) (data : D) (test : TestId) :
    State D Command :=
  {before with
    memory := before.memory.update result (some value)
    history := before.history + {(data, test)}
    action := .command command}

omit mD in
theorem assignmentState_hidden (before : State D Command) (command : Command)
    (x : Variable sort .observable) (value : Value sort) :
    (assignmentState before command x value).memory.hidden = before.memory.hidden :=
  hidden_observable_write before.memory x value

omit mD in
theorem testState_hidden (before : State D Command) (command : Command)
    (result : Variable .real .observable) (value : ℝ) (data : D) (test : TestId) :
    (testState before command result value data test).memory.hidden = before.memory.hidden :=
  hidden_observable_write before.memory result value

omit mD in
theorem assignment_successor_view (model : Model D Command) (world : World D Command)
    (command : Command) (x : Variable sort .observable) (value : Value sort)
    (effect : model.dynamics.command command world.current.visible =
      some ((assignmentState world.current command x value).visible, 0)) :
    semanticView model.dynamics (world.extend (assignmentState world.current command x value)) =
      writeViewValue (semanticView model.dynamics world) x value := by
  rw [command_successor_view model world _ command rfl
    (assignmentState_hidden world.current command x value) ⟨0, effect, by simp [assignmentState]⟩]
  simp only [writeViewValue, semanticView, State.visible, assignmentState,
    Memory.assemble_projections]

omit mD in
theorem test_successor_view (model : Model D Command) (world : World D Command)
    (command : Command) (result : Variable .real .observable) (value : ℝ) (data : D) (test : TestId)
    (effect : model.dynamics.command command world.current.visible =
      some ((testState world.current command result value data test).visible, {(data, test)})) :
    semanticView model.dynamics
        (world.extend (testState world.current command result value data test)) =
      {(writeViewValue (semanticView model.dynamics world) result value) with
        history := world.current.history + {(data, test)}} := by
  rw [command_successor_view model world _ command rfl
    (testState_hidden world.current command result value data test) ⟨{(data, test)}, effect, rfl⟩]
  simp only [writeViewValue, semanticView, State.visible, testState,
    Memory.assemble_projections]

theorem assignment_preimage_iff (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (world : World D Command)
    (admitted : Admitted model.dynamics world) (command : Command)
    (x : Variable sort .observable) (rhs : AssertionTerm context (.value sort))
    (value : Value sort) (post : Assertion context)
    (evaluated : evalTerm interpretation model env (semanticView model.dynamics world) rhs = some value)
    (effect : model.dynamics.command command world.current.visible =
      some ((assignmentState world.current command x value).visible, 0)) :
    referenceAssertionSatisfaction interpretation model env world (assignmentPreimage x rhs post) ↔
      satisfies interpretation model env
        (world.extend (assignmentState world.current command x value)) post := by
  apply liberalPreimage_successor_iff
  · exact command_successor_admitted model admitted _ command rfl
      (assignmentState_hidden world.current command x value) ⟨0, effect, by simp [assignmentState]⟩
  · rw [eval_assignmentView, evaluated, Option.map_some,
      assignment_successor_view model world command x value effect]

theorem test_preimage_iff (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (world : World D Command)
    (admitted : Admitted model.dynamics world) (command : Command)
    (result : Variable .real .observable) (hypothesis : HypothesisId)
    (data : AssertionTerm context .dataset) (d : D) (test : TestId) (population : PopulationId)
    (post : Assertion context)
    (evaluated : evalTerm interpretation model env (semanticView model.dynamics world) data = some d)
    (effect : model.dynamics.command command world.current.visible =
      some ((testState world.current command result
        ((interpretation.tests hypothesis test).tailProbability d) d test).visible, {(d, test)})) :
    referenceAssertionSatisfaction interpretation model env world
        (testPreimage result hypothesis data test population post) ↔
      satisfies interpretation model env
        (world.extend (testState world.current command result
          ((interpretation.tests hypothesis test).tailProbability d) d test)) post := by
  apply liberalPreimage_successor_iff
  · exact command_successor_admitted model admitted _ command rfl
      (testState_hidden world.current command result _ d test) ⟨{(d, test)}, effect, rfl⟩
  · rw [eval_testAssignmentView, evaluated, Option.map_some,
      test_successor_view model world command result _ d test effect]
    rfl

/-- Materialize a visible command effect without changing ordinary hidden memory. -/
def commandState (before : State D Command) (command : Command)
    (visible : VisibleState D) (delta : History D) : State D Command :=
  ⟨Memory.assemble visible.memory before.memory.hidden, visible.datasets,
    before.history + delta, .command command⟩

omit mD in
@[simp] theorem commandState_visible (before : State D Command) (command : Command)
    (visible : VisibleState D) (delta : History D) :
    (commandState before command visible delta).visible = visible := by
  cases visible
  rfl

omit mD in
@[simp] theorem commandState_hidden (before : State D Command) (command : Command)
    (visible : VisibleState D) (delta : History D) :
    (commandState before command visible delta).memory.hidden = before.memory.hidden := rfl

theorem simultaneous_assignment_preimage_iff
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (world : World D Command)
    (admitted : Admitted model.dynamics world) (command : Command)
    (writes : List (SimultaneousWrite context)) (after : SemanticView D) (post : Assertion context)
    (evaluated : evalSimultaneousWrites interpretation model env
      (semanticView model.dynamics world) (semanticView model.dynamics world) writes = some after)
    (effect : model.dynamics.command command world.current.visible = some (after.visible, 0)) :
    referenceAssertionSatisfaction interpretation model env world
        (simultaneousAssignmentPreimage writes post) ↔
      satisfies interpretation model env
        (world.extend (commandState world.current command after.visible 0)) post := by
  have effect' : ∃ delta, model.dynamics.command command world.current.visible =
      some ((commandState world.current command after.visible 0).visible, delta) ∧
      (commandState world.current command after.visible 0).history = world.current.history + delta :=
    ⟨0, by simpa using effect, rfl⟩
  have hinfo := simultaneous_writes_preserve_information interpretation model env
    (semanticView model.dynamics world) writes (semanticView model.dynamics world) after evaluated
  have hview : semanticView model.dynamics
      (world.extend (commandState world.current command after.visible 0)) = after := by
    rw [command_successor_view model world _ command rfl (commandState_hidden _ _ _ _) effect']
    simp only [commandState, add_zero]
    cases after
    congr 1
    · exact hinfo.1.symm
    · exact hinfo.2.1.symm
    · exact hinfo.2.2.1.symm
    · exact hinfo.2.2.2.1.symm
  apply liberalPreimage_successor_iff
  · exact command_successor_admitted model admitted _ command rfl
      (commandState_hidden _ _ _ _) effect'
  · rw [eval_simultaneousAssignmentView, evaluated, hview]

end
end Lara.BHL
