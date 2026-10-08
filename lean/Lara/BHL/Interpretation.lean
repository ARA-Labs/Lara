import Lara.BHL.Syntax
import Lara.BHL.NumericalEvent

namespace Lara.BHL

open MeasureTheory

abbrev ValueTuple : List ValueSort → Type
  | [] => PUnit
  | sort :: rest => Value sort × ValueTuple rest

abbrev TermValue (D Command : Type) : TermSort → Type
  | .value sort => Value sort
  | .dataset => D
  | .world => World D Command
  | .trace => List (State D Command)
  | .state => State D Command
  | .view => SemanticView D
  | .visible => VisibleState D
  | .hidden => HiddenMemory
  | .history => History D
  | .provenance => Multiset (D × PopulationId)
  | .compatible => Set HiddenMemory

/-- Mathematical interpretations, not syntax fields. Ordinary user functions
and predicates consume explicit value arguments only. Requirement relations
are intended to express scientific population/null and joint-law conditions.
Their signatures take no assertions, executions or derivations as explicit
arguments; concrete interpretations must prove the intended binding separately. -/
structure AssertionInterpretation (D Command : Type) [MeasurableSpace D] where
  constants : (sort : GhostSort) → ConstantId sort → GhostValue D Command sort
  functions : (inputs : List ValueSort) → (output : ValueSort) →
    FunctionId inputs output → ValueTuple inputs → Value output
  datasetFunctions : (inputs : List ValueSort) → DatasetFunctionId inputs → ValueTuple inputs → D
  predicates : (inputs : List ValueSort) → PredicateId inputs → ValueTuple inputs → Prop
  tests : HypothesisId → TestId → NumericTest D ℝ
  hypotheses : HypothesisId → HiddenMemory → Prop
  requirements : HypothesisId → TestId → PopulationId → HiddenMemory → D → Prop
  jointRequirements : CouplingId → HiddenMemory → List (D × TestId × PopulationId) → Prop
  couplings : (name : CouplingId) → (left right : ValueSort) →
    (μ : ProbabilityMeasure (Value left)) → (ν : ProbabilityMeasure (Value right)) →
    Option (ProbabilityCoupling μ ν)
  commands : CommandId → Command

noncomputable section

variable {D Command : Type} [MeasurableSpace D]

def GhostTerm.eval (interpretation : AssertionInterpretation D Command)
    (env : GhostEnv D Command context) : GhostTerm context sort → GhostValue D Command sort
  | .bound index => env _ index
  | .constant name => interpretation.constants _ name

def ghostTermValue (sort : GhostSort) (value : GhostValue D Command sort) :
    TermValue D Command sort.termSort :=
  match sort with
  | .value _ => value
  | .dataset => value
  | .world => value
  | .trace => value

def writeViewValue (view : SemanticView D) (x : Variable sort .observable)
    (value : Value sort) : SemanticView D :=
  {view with visible := {view.visible with memory :=
    ((Memory.assemble view.visible.memory view.hidden).update x (some value)).observable}}

def writeViewDataset (view : SemanticView D) (name : DatasetId) (data : D) : SemanticView D :=
  {view with visible := {view.visible with datasets := Function.update view.visible.datasets name data}}

mutual
/-- Terms have explicit partiality. Missing operands, undefined reads, negative
or out-of-range trace indices, and unbound couplings yield none. -/
def evalTerm (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (view : SemanticView D) :
    AssertionTerm context sort → Option (TermValue D Command sort)
  | .ghost term => some (ghostTermValue _ (term.eval interpretation env))
  | .boolean value => some value
  | .integer value => some value
  | .rational value => some (value : ℝ)
  | .apply symbol args => (evalArguments interpretation model env view args).map
      (interpretation.functions _ _ symbol)
  | .datasetApply symbol args => (evalArguments interpretation model env view args).map
      (interpretation.datasetFunctions _ symbol)
  | .ambient => some view
  | .currentView world => (evalTerm interpretation model env view world).map (semanticView model.dynamics)
  | .currentState world => (evalTerm interpretation model env view world).map World.current
  | .worldTrace world => (evalTerm interpretation model env view world).map World.trace
  | .appendWorld world trace => do
      let w ← evalTerm interpretation model env view world
      let states ← evalTerm interpretation model env view trace
      pure ⟨w.initial, w.rest ++ states, w.initial_history_empty⟩
  | .traceEmpty => some []
  | .traceSingleton state => (evalTerm interpretation model env view state).map List.singleton
  | .traceAppend left right => do
      let a ← evalTerm interpretation model env view left
      let b ← evalTerm interpretation model env view right
      pure (a ++ b)
  | .traceLength trace => (evalTerm interpretation model env view trace).map (fun states => Int.ofNat states.length)
  | .traceTake trace index => do
      let states ← evalTerm interpretation model env view trace
      let n ← evalTerm interpretation model env view index
      if n < 0 then none else some (states.take n.toNat)
  | .traceIndex trace index => do
      let states ← evalTerm interpretation model env view trace
      let n ← evalTerm interpretation model env view index
      if n < 0 then none else states[n.toNat]?
  | .valueRead target x => do
      let v ← evalTerm interpretation model env view target
      (Memory.assemble v.visible.memory v.hidden).read x
  | .datasetRead target name => (evalTerm interpretation model env view target).map
      (fun v => v.visible.datasets name)
  | .visibleOf target => (evalTerm interpretation model env view target).map SemanticView.visible
  | .hiddenOf target => (evalTerm interpretation model env view target).map SemanticView.hidden
  | .historyOf target => (evalTerm interpretation model env view target).map SemanticView.history
  | .provenanceOf target => (evalTerm interpretation model env view target).map SemanticView.provenance
  | .compatibleOf target => (evalTerm interpretation model env view target).map SemanticView.compatible
  | .makeView visible history hidden compatible provenance => do
      let v ← evalTerm interpretation model env view visible
      let h ← evalTerm interpretation model env view history
      let ordinaryHidden ← evalTerm interpretation model env view hidden
      let alternatives ← evalTerm interpretation model env view compatible
      let samples ← evalTerm interpretation model env view provenance
      pure ⟨v, h, ordinaryHidden, alternatives, samples⟩
  | .writeValue target x value => do
      let v ← evalTerm interpretation model env view target
      let a ← evalTerm interpretation model env view value
      pure (writeViewValue v x a)
  | .writeDataset target name data => do
      let v ← evalTerm interpretation model env view target
      let d ← evalTerm interpretation model env view data
      pure (writeViewDataset v name d)
  | .addHistory target history => do
      let v ← evalTerm interpretation model env view target
      let h ← evalTerm interpretation model env view history
      pure {v with history := v.history + h}
  | .historyEmpty => some 0
  | .historySingleton data test => (evalTerm interpretation model env view data).map (fun d => {(d, test)})
  | .historyAdd left right => do
      let a ← evalTerm interpretation model env view left
      let b ← evalTerm interpretation model env view right
      pure (a + b)
  | .historyCount history data test => do
      let h ← evalTerm interpretation model env view history
      let d ← evalTerm interpretation model env view data
      pure (Int.ofNat (@History.count D (Classical.decEq D) h d test))
  | .provenanceEmpty => some 0
  | .provenanceSingleton data population => (evalTerm interpretation model env view data).map
      (fun d => {(d, population)})
  | .provenanceAdd left right => do
      let a ← evalTerm interpretation model env view left
      let b ← evalTerm interpretation model env view right
      pure (a + b)
  | .pvalue test => (evalNumericalEvent interpretation model env view test).map
      (fun event => event.2.probability)
  | .realAdd left right => do
      let a ← evalTerm interpretation model env view left
      let b ← evalTerm interpretation model env view right
      pure (a + b)
  | .realMin left right => do
      let a ← evalTerm interpretation model env view left
      let b ← evalTerm interpretation model env view right
      pure (min a b)
  | .intAdd left right => do
      let a ← evalTerm interpretation model env view left
      let b ← evalTerm interpretation model env view right
      pure (a + b)
  | .intSub left right => do
      let a ← evalTerm interpretation model env view left
      let b ← evalTerm interpretation model env view right
      pure (a - b)
  | .intLess left right => do
      let a ← evalTerm interpretation model env view left
      let b ← evalTerm interpretation model env view right
      pure (decide (a < b))
  | .booleanNot term => (evalTerm interpretation model env view term).map Bool.not

def evalArguments (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (view : SemanticView D) :
    ValueArguments context inputs → Option (ValueTuple inputs)
  | .nil => some PUnit.unit
  | .cons term rest => do
      let head ← evalTerm interpretation model env view term
      let tail ← evalArguments interpretation model env view rest
      pure (head, tail)

def evalNumericalEvent (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (view : SemanticView D) :
    TestExpression context → Option PackedNumericalEvent
  | .leaf hypothesis data test _ => (evalTerm interpretation model env view data).map
      (fun d => ⟨.real, NumericalEvent.tail (interpretation.tests hypothesis test) d⟩)
  | .disj name left right => do
      let a ← evalNumericalEvent interpretation model env view left
      let b ← evalNumericalEvent interpretation model env view right
      let coupling ← interpretation.couplings name a.1 b.1 a.2.law b.2.law
      pure ⟨.product a.1 b.1, NumericalEvent.union a.2 b.2 coupling⟩
  | .conj name left right => do
      let a ← evalNumericalEvent interpretation model env view left
      let b ← evalNumericalEvent interpretation model env view right
      let coupling ← interpretation.couplings name a.1 b.1 a.2.law b.2.law
      pure ⟨.product a.1 b.1, NumericalEvent.intersection a.2 b.2 coupling⟩
end

/-- Recorded dataset values, including repeats, are evaluated at the current node. -/
def evalTestEntries (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (view : SemanticView D) :
    TestExpression context → Option (List (D × TestId × PopulationId))
  | .leaf _ data test population => (evalTerm interpretation model env view data).map
      (fun d => [(d, test, population)])
  | .disj _ left right | .conj _ left right => do
      let a ← evalTestEntries interpretation model env view left
      let b ← evalTestEntries interpretation model env view right
      pure (a ++ b)

def evalTestHistory (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (view : SemanticView D) (test : TestExpression context) :
    Option (History D) :=
  (evalTestEntries interpretation model env view test).map
    (fun entries => ((entries.map (fun entry => (entry.1, entry.2.1))) : History D))

/-- Scientific requirements concern every successfully denoted dataset and its
modeled provenance. Unavailable inputs or numerical couplings are not evidence
of scientific model failure. Numerical definedness is a separate obligation. -/
def modelRequirements (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (view : SemanticView D) : TestExpression context → Prop
  | .leaf hypothesis data test population => ∀ d,
      evalTerm interpretation model env view data = some d →
      interpretation.requirements hypothesis test population view.hidden d ∧
      (d, population) ∈ view.provenance
  | expression@(.disj name left right) | expression@(.conj name left right) =>
      modelRequirements interpretation model env view left ∧
      modelRequirements interpretation model env view right ∧
      ∀ entries, evalTestEntries interpretation model env view expression = some entries →
        interpretation.jointRequirements name view.hidden entries

def compareReal : Comparison → ℝ → ℝ → Prop
  | .equal => Eq
  | .less => LT.lt
  | .lessEqual => LE.le
  | .greater => fun a b => b < a
  | .greaterEqual => fun a b => b ≤ a

def compareInt : Comparison → Int → Int → Prop
  | .equal => Eq
  | .less => LT.lt
  | .lessEqual => LE.le
  | .greater => fun a b => b < a
  | .greaterEqual => fun a b => b ≤ a

/-- Failed direct term/argument evaluation makes its consuming atom false.
Scientific requirements are conditional on successful dataset/entry evaluation;
they do not assert numerical definedness or invent missing values. -/
def atomMeaning (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (view : SemanticView D) : AssertionAtom context → Prop
  | .rigid predicate args => ∃ values, evalArguments interpretation model env view args = some values ∧
      interpretation.predicates _ predicate values
  | .equal left right => ∃ value,
      evalTerm interpretation model env view left = some value ∧
      evalTerm interpretation model env view right = some value
  | .defined term => ∃ value, evalTerm interpretation model env view term = some value
  | .realCompare comparison left right => ∃ a b,
      evalTerm interpretation model env view left = some a ∧
      evalTerm interpretation model env view right = some b ∧ compareReal comparison a b
  | .intCompare comparison left right => ∃ a b,
      evalTerm interpretation model env view left = some a ∧
      evalTerm interpretation model env view right = some b ∧ compareInt comparison a b
  | .hypothesis hypothesis target => ∃ hidden,
      evalTerm interpretation model env view target = some hidden ∧ interpretation.hypotheses hypothesis hidden
  | .sampling data population provenance => ∃ d samples,
      evalTerm interpretation model env view data = some d ∧
      evalTerm interpretation model env view provenance = some samples ∧ (d, population) ∈ samples
  | .requirements expression target => ∃ v,
      evalTerm interpretation model env view target = some v ∧ modelRequirements interpretation model env v expression
  | .admitted target => ∃ w,
      evalTerm interpretation model env view target = some w ∧ Admitted model.dynamics w
  | .action command target => ∃ state,
      evalTerm interpretation model env view target = some state ∧
      state.action = .command (interpretation.commands command)

end
end Lara.BHL
