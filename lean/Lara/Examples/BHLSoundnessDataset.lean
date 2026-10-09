import Lara.BHL.Soundness
import Lara.Examples.BHLExecution
import Lara.BHL.Numeric

namespace Lara.Examples.BHLSoundnessDataset

open Lara.BHL MeasureTheory
namespace E
export Lara.Examples.BHLExecution
  (aliasId dataId report oldReport initialSnapshot Source)
namespace Source
export Lara.Examples.BHLExecution.Source (quote)
end Source
namespace Snapshot
export Lara.Examples.BHLExecution.Snapshot (memory)
end Snapshot
namespace Science
export Lara.Examples.BHLExecution.Science
  (hypothesisId correctId populationId parameter hiddenMemory)
end Science
end E

/-- This finite encoding is only used for the two values in this fixture. -/
def initialData (name : DatasetId) : ℚ := if name = E.aliasId then 1 else 0

def aliasCommand : Primitive := .assignDataset E.aliasId (.read E.dataId)
def testCommand : Primitive :=
  .test E.report E.Science.hypothesisId (.read E.dataId)
    E.Science.correctId E.Science.populationId

def aliasSource : E.Source := .command (.alias E.aliasId E.dataId)

theorem alias_quote : aliasSource.quote = .command aliasCommand := rfl

noncomputable section

def interpretation : AssertionInterpretation ℝ Primitive where
  constants := fun sort _ => match sort with
    | .value sort => valueDefault sort
    | .dataset => 0
    | .world => World.start Memory.empty (fun _ => 0)
    | .trace => []
  functions := fun _ output _ _ => valueDefault output
  datasetFunctions := fun _ _ _ => 0
  predicates := fun _ _ _ => False
  tests := fun _ _ => realDiracTest
  hypotheses := fun hypothesis hidden => hypothesis = E.Science.hypothesisId ∧
    hidden .boolean E.Science.parameter.id = some true
  requirements := fun _ _ _ _ _ => False
  jointRequirements := fun _ _ _ => False
  couplings := fun _ _ _ _ _ => none
  commands := fun _ => .skip

def initialVisible : VisibleState ℝ :=
  ⟨E.initialSnapshot.memory, fun name => (initialData name : ℝ)⟩

def context : ProgramContext ℝ := ProgramContext.ofRelations interpretation
  (fun hidden visible => (∃ bit, hidden = E.Science.hiddenMemory bit) ∧
    visible = initialVisible)
  (fun _ _ _ _ _ => False)
  ⟨E.Science.hiddenMemory false, initialVisible, ⟨⟨false, rfl⟩, rfl⟩⟩

def startWorld (bit : Bool) : World ℝ Primitive := World.start
  (Memory.assemble initialVisible.memory (E.Science.hiddenMemory bit)) initialVisible.datasets

def testedVisible : VisibleState ℝ := (VisibleWrite.value E.report (1 : ℝ)).apply initialVisible

def testedState (world : World ℝ Primitive) : State ℝ Primitive :=
  commandState world.current testCommand testedVisible {(0, E.Science.correctId)}

def once (bit : Bool) := (startWorld bit).extend (testedState (startWorld bit))
def before (bit : Bool) := (once bit).extend (testedState (once bit))
def finalVisible : VisibleState ℝ :=
  (VisibleWrite.dataset E.aliasId 0).apply testedVisible

def after (bit : Bool) := (before bit).extend
  (commandState (before bit).current aliasCommand finalVisible 0)

theorem start_admitted (bit : Bool) : Admitted context.model.dynamics (startWorld bit) :=
  admitted_start context.model.dynamics initialVisible (E.Science.hiddenMemory bit)
    ⟨⟨bit, rfl⟩, rfl⟩

theorem test_effect_start (bit : Bool) :
    primitiveEffect interpretation testCommand (startWorld bit).current.visible =
      some (testedVisible, {(0, E.Science.correctId)}) := by
  simp [primitiveEffect, evalPrimitive, testCommand, evalDatasetExpr,
    interpretation, startWorld, initialVisible, initialData, E.dataId, E.aliasId,
    realDiracTest_tailProbability_zero, testedVisible, State.visible]

theorem test_effect_once (bit : Bool) :
    primitiveEffect interpretation testCommand (once bit).current.visible =
      some (testedVisible, {(0, E.Science.correctId)}) := by
  simp [once, testedState, primitiveEffect, evalPrimitive, testCommand,
    evalDatasetExpr, interpretation, testedVisible, initialVisible, initialData,
    E.dataId, E.aliasId, realDiracTest_tailProbability_zero, VisibleWrite.apply]
  funext sort name
  by_cases sameSort : ValueSort.real = sort <;>
    by_cases sameName : E.report.id = name <;>
    simp [Memory.observable, Memory.update, Memory.assemble, sameSort, sameName]

theorem alias_effect (bit : Bool) :
    primitiveEffect interpretation aliasCommand (before bit).current.visible =
      some (finalVisible, 0) := by
  simp [before, testedState, primitiveEffect, evalPrimitive, aliasCommand,
    evalDatasetExpr, testedVisible, initialVisible, initialData, finalVisible,
    E.dataId, E.aliasId, VisibleWrite.apply]

private theorem advance_admitted {world : World ℝ Primitive} {command : Primitive}
    {visible : VisibleState ℝ} {delta : History ℝ}
    (admitted : Admitted context.model.dynamics world)
    (effect : primitiveEffect interpretation command world.current.visible = some (visible, delta)) :
    Admitted context.model.dynamics
      (world.extend (commandState world.current command visible delta)) := by
  apply command_successor_admitted context.model admitted _ command rfl
    (commandState_hidden _ _ _ _)
  exact ⟨delta, effect, rfl⟩

theorem once_admitted (bit : Bool) : Admitted context.model.dynamics (once bit) :=
  advance_admitted (start_admitted bit) (test_effect_start bit)
theorem before_admitted (bit : Bool) : Admitted context.model.dynamics (before bit) :=
  advance_admitted (once_admitted bit) (test_effect_once bit)
theorem after_admitted (bit : Bool) : Admitted context.model.dynamics (after bit) :=
  advance_admitted (before_admitted bit) (alias_effect bit)

theorem first_test (bit : Bool) :
    Step context (some (.command testCommand)) (startWorld bit) none (once bit) :=
  .command (test_effect_start bit)
theorem second_test (bit : Bool) :
    Step context (some (.command testCommand)) (once bit) none (before bit) :=
  .command (test_effect_once bit)
theorem assignment_step (bit : Bool) :
    Step context (some (.command aliasCommand)) (before bit) none (after bit) :=
  .command (alias_effect bit)

abbrev Γ : List GhostSort := [.dataset]
def env : GhostEnv ℝ Primitive Γ := GhostEnv.push (sort := .dataset) (1 : ℝ) GhostEnv.empty
def zeroData : AssertionTerm Γ .dataset := .ghost (.constant (sort := GhostSort.dataset) ⟨0⟩)
def aliasData : AssertionTerm Γ .dataset := .datasetRead .ambient E.aliasId

def probability (data : AssertionTerm Γ .dataset) : AssertionTerm Γ (.value .real) :=
  .pvalue (.leaf E.Science.hypothesisId data E.Science.correctId E.Science.populationId)

def count (data : AssertionTerm Γ .dataset) : AssertionTerm Γ (.value .integer) :=
  .historyCount (.historyOf .ambient) data E.Science.correctId

def fullHistory : AssertionTerm Γ .history :=
  .historyAdd (.historySingleton zeroData E.Science.correctId)
    (.historySingleton zeroData E.Science.correctId)

def post : Assertion Γ := .conj
  (.modal (.atom (.equal aliasData zeroData)))
  (.conj (.modal (.atom (.equal (probability aliasData) (.rational 1))))
  (.conj (.modal (.atom (.equal (count aliasData) (.integer 2))))
  (.conj (.modal (.atom (.equal (.historyOf .ambient) fullHistory)))
    (.modal (.atom (.equal (.valueRead .ambient E.oldReport) (.rational (7 / 11))))))))

def pre : Assertion Γ := aliasCommand.preimage post

theorem derivation : Derivation context pre (.command aliasCommand) post :=
  .assign aliasCommand (by trivial) post

theorem complete_history (bit : Bool) :
    (before bit).current.history = {(0, E.Science.correctId)} + {(0, E.Science.correctId)} ∧
    (after bit).current.history = (before bit).current.history := by
  simp [before, once, after, testedState, commandState, startWorld]

theorem protected_output (bit : Bool) :
    (before bit).current.visible.memory .real E.oldReport.id = some (7 / 11 : ℝ) ∧
    (after bit).current.visible.memory .real E.oldReport.id = some (7 / 11 : ℝ) := by
  norm_num [before, after, testedState, testedVisible, finalVisible,
    VisibleWrite.apply, initialVisible, E.Snapshot.memory, E.initialSnapshot,
    Memory.observable, Memory.update, Memory.assemble, E.oldReport, E.report]

theorem probability_changes (bit : Bool) :
    realDiracTest.tailProbability ((before bit).current.datasets E.aliasId) = 0 ∧
    realDiracTest.tailProbability ((after bit).current.datasets E.aliasId) = 1 := by
  simp [before, after, testedState, commandState, testedVisible, finalVisible,
    VisibleWrite.apply, initialVisible, initialData, E.aliasId,
    realDiracTest_tailProbability_one, realDiracTest_tailProbability_zero]

theorem count_changes (bit : Bool) :
    History.count (before bit).current.history ((before bit).current.datasets E.aliasId)
      E.Science.correctId = 0 ∧
    History.count (after bit).current.history ((after bit).current.datasets E.aliasId)
      E.Science.correctId = 2 := by
  simp [before, once, after, testedState, commandState, startWorld,
    testedVisible, finalVisible, VisibleWrite.apply, initialVisible, initialData,
    E.aliasId, History.count]

theorem final_satisfaction (bit : Bool) :
    satisfies interpretation context.model env (after bit) post := by
  refine ⟨after_admitted bit, ?_⟩
  rcases protected_output bit with ⟨_, preservedReport⟩
  have dataset : (after bit).current.datasets E.aliasId = 0 := by
    simp [after, commandState, finalVisible, VisibleWrite.apply]
  have pvalue := (probability_changes bit).2
  have counter := (count_changes bit).2
  have history := (complete_history bit).2.trans (complete_history bit).1
  simp only [post, referenceAssertionSatisfaction, referenceModalSatisfaction, atomMeaning]
  refine ⟨⟨0, ?_, ?_⟩, ⟨⟨1, ?_, ?_⟩, ⟨⟨2, ?_, ?_⟩,
    ⟨⟨{(0, E.Science.correctId)} + {(0, E.Science.correctId)}, ?_, ?_⟩,
      ⟨7 / 11, ?_, ?_⟩⟩⟩⟩⟩
  · simpa only [evalTerm, aliasData, semanticView, Option.map_some, State.visible] using congrArg some dataset
  · rfl
  · simpa only [probability, evalTerm, evalNumericalEvent, aliasData, interpretation,
      Option.map_some, NumericalEvent.tail_probability, semanticView, State.visible] using congrArg some pvalue
  · simp [evalTerm]
  · change some (Int.ofNat (History.count (after bit).current.history
      ((after bit).current.datasets E.aliasId) E.Science.correctId)) = some 2
    exact congrArg (fun n : Nat => some (Int.ofNat n)) counter
  · rfl
  · simpa only [evalTerm, semanticView, Option.map_some] using congrArg some history
  · rfl
  · change (after bit).current.visible.memory .real E.oldReport.id = some (7 / 11)
    exact preservedReport
  · norm_num [evalTerm]

theorem initial_satisfaction (bit : Bool) :
    satisfies interpretation context.model env (before bit) pre := by
  refine ⟨before_admitted bit, ?_⟩
  apply (liberalPreimage_successor_iff interpretation context.model env
    (before bit) (after bit) (after_admitted bit)
    (aliasCommand.viewTerm Γ) post ?_).mpr (final_satisfaction bit)
  exact primitive_viewTerm_successor context env (assignment_step bit)

theorem initial_alias_ghost (bit : Bool) :
    evalTerm interpretation context.model env
      (semanticView context.model.dynamics (before bit)) aliasData =
    evalTerm interpretation context.model env
      (semanticView context.model.dynamics (before bit))
      (.ghost (.bound .here) : AssertionTerm Γ .dataset) := by
  simp [evalTerm, aliasData, env, GhostTerm.eval, ghostTermValue, GhostEnv.push,
    semanticView, before, testedState, commandState, testedVisible, State.visible,
    VisibleWrite.apply, initialVisible, initialData]
  rfl

end

/-- Finite observations use rationals, and never evaluate arbitrary real laws. -/
structure Observation where
  datasetValue : ℚ
  pvalue : ℚ
  aliasCount : Nat
  ledger : List (ℚ × TestId)
  protectedReport : ℚ
  deriving DecidableEq

def preObservation : Observation := ⟨1, 0, 0,
  [(0, E.Science.correctId), (0, E.Science.correctId)], 7 / 11⟩
def postObservation : Observation := ⟨0, 1, 2,
  [(0, E.Science.correctId), (0, E.Science.correctId)], 7 / 11⟩
def preEvaluator (observation : Observation) : Bool := decide (observation = preObservation)
def postEvaluator (observation : Observation) : Bool := decide (observation = postObservation)

def smokeRow : Observation × Observation := (preObservation, postObservation)
def smokeFlags : List Bool := [preEvaluator smokeRow.1, postEvaluator smokeRow.2,
  decide (smokeRow.1.ledger = smokeRow.2.ledger),
  decide (smokeRow.1.protectedReport = smokeRow.2.protectedReport),
  decide (smokeRow.1.pvalue ≠ smokeRow.2.pvalue),
  decide (smokeRow.1.aliasCount ≠ smokeRow.2.aliasCount)]

/-- The only executable dataset effect represented here is the quoted alias. -/
def assignmentEvaluator (observation : Observation) : Observation :=
  { observation with
    datasetValue := 0
    pvalue := 1
    aliasCount := observation.ledger.countP fun entry =>
      decide (entry.1 = 0 ∧ entry.2 = E.Science.correctId) }

theorem assignment_evaluates :
    assignmentEvaluator preObservation = postObservation := by rfl
theorem smoke_flags : smokeFlags = [true, true, true, true, true, true] := by
  norm_num [smokeFlags, smokeRow, preEvaluator, postEvaluator, preObservation, postObservation]

noncomputable section

def Represents (observation : Observation) (world : World ℝ Primitive) : Prop :=
  world.current.datasets E.aliasId = (observation.datasetValue : ℝ) ∧
  realDiracTest.tailProbability (world.current.datasets E.aliasId) = (observation.pvalue : ℝ) ∧
  History.count world.current.history (world.current.datasets E.aliasId) E.Science.correctId =
    observation.aliasCount ∧
  world.current.history = ((observation.ledger.map fun entry =>
    ((entry.1 : ℝ), entry.2)) : History ℝ) ∧
  world.current.visible.memory .real E.oldReport.id = some (observation.protectedReport : ℝ)

theorem pre_correspondence (bit : Bool) : Represents preObservation (before bit) := by
  rcases probability_changes bit with ⟨probability, _⟩
  rcases count_changes bit with ⟨count, _⟩
  rcases complete_history bit with ⟨history, _⟩
  rcases protected_output bit with ⟨preservedReport, _⟩
  simp only [Represents, preObservation, Rat.cast_zero, Rat.cast_one,
    List.map_cons, List.map_nil, ← Multiset.cons_coe, Multiset.coe_nil]
  refine ⟨?_, probability, count, ?_, ?_⟩
  · simp [before, testedState, commandState, testedVisible, VisibleWrite.apply,
      initialVisible, initialData]
  · simpa using history
  · simpa [preObservation] using preservedReport

theorem post_correspondence (bit : Bool) : Represents postObservation (after bit) := by
  rcases probability_changes bit with ⟨_, probability⟩
  rcases count_changes bit with ⟨_, count⟩
  rcases complete_history bit with ⟨history, preserved⟩
  rcases protected_output bit with ⟨_, preservedReport⟩
  simp only [Represents, postObservation, Rat.cast_zero, Rat.cast_one,
    List.map_cons, List.map_nil, ← Multiset.cons_coe, Multiset.coe_nil]
  refine ⟨?_, probability, count, ?_, ?_⟩
  · simp [after, commandState, finalVisible, VisibleWrite.apply]
  · simpa using preserved.trans history
  · simpa [postObservation] using preservedReport

theorem pre_evaluator_correspondence (bit : Bool) :
    preEvaluator preObservation = true ∧ Represents preObservation (before bit) ∧
      satisfies interpretation context.model env (before bit) pre :=
  ⟨by simp [preEvaluator], pre_correspondence bit, initial_satisfaction bit⟩

theorem post_evaluator_correspondence (bit : Bool) :
    postEvaluator postObservation = true ∧ Represents postObservation (after bit) ∧
      satisfies interpretation context.model env (after bit) post :=
  ⟨by simp [postEvaluator], post_correspondence bit, final_satisfaction bit⟩

theorem assignment_evaluator_correspondence (bit : Bool) :
    Represents (assignmentEvaluator preObservation) (after bit) ∧
      Step context (some aliasSource.quote) (before bit) none (after bit) := by
  rw [assignment_evaluates, alias_quote]
  exact ⟨post_correspondence bit, assignment_step bit⟩

end
end Lara.Examples.BHLSoundnessDataset
