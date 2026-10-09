import Lara.BHL.ExecutionLaws
import Lara.BHL.ProgramLaws
import Lara.Examples.BHLBelief
import Mathlib.Tactic

namespace Lara.Examples.BHLExecution

open Lara.BHL MeasureTheory

namespace Science
export Lara.Examples.BHLBelief (hypothesisId populationId correctId extraId testFor
  testFor_pvalue hiddenMemory hiddenMemory_false_ne_true parameter lawBinding populationLaw)
end Science

def x : Variable .integer .observable := ⟨⟨10⟩⟩
def y : Variable .integer .observable := ⟨⟨11⟩⟩
def report : Variable .real .observable := ⟨⟨12⟩⟩
def oldReport : Variable .real .observable := ⟨⟨13⟩⟩
def dataId : DatasetId := ⟨0⟩
def aliasId : DatasetId := ⟨1⟩

/-- Only integer arithmetic, dataset reads/aliases, and the named Dirac tests
are executable here. This is not an interpreter for arbitrary real laws. -/
inductive IntExpr where
  | literal : Int → IntExpr
  | read : Variable .integer .observable → IntExpr
  | add : IntExpr → IntExpr → IntExpr

inductive Guard where
  | literal : Bool → Guard
  | less : IntExpr → IntExpr → Guard

inductive Command where
  | skip
  | assign : Variable .integer .observable → IntExpr → Command
  | alias : DatasetId → DatasetId → Command
  | test : Variable .real .observable → DatasetId → TestId → Command
  | pvalue : Variable .real .observable → DatasetId → TestId → Command

inductive Source where
  | command : Command → Source
  | seq : Source → Source → Source
  | ite : Guard → Source → Source → Source
  | loop : Guard → Source → Source
  | par : Source → Source → Source

structure Snapshot where
  integers : VarId → Option Int
  rationals : VarId → Option ℚ
  datasets : DatasetId → Bool
  ledger : History Bool

/-- Source action codes are derived from actual emitted commands, not an expected
output string: skip=0, integer target=100+id, alias=200+id, test=300+id,
p-value-only assignment=400+id. -/
def Command.code : Command → Nat
  | .skip => 0
  | .assign target _ => 100 + target.id.index
  | .alias target _ => 200 + target.index
  | .test target _ _ => 300 + target.id.index
  | .pvalue target _ _ => 400 + target.id.index

def IntExpr.quote : IntExpr → ProgramExpr .integer
  | .literal value => .integer value
  | .read target => .read target
  | .add a b => .intAdd a.quote b.quote

def Guard.quote : Guard → ProgramExpr .boolean
  | .literal value => .boolean value
  | .less a b => .intLess a.quote b.quote

def Command.quote : Command → Primitive
  | .skip => .skip
  | .assign target expr => .assign target expr.quote
  | .alias target source => .assignDataset target (.read source)
  | .test target data testName =>
      .test target Science.hypothesisId (.read data) testName Science.populationId
  | .pvalue target data testName => .assign target
      (.pvalue Science.hypothesisId (.read data) testName Science.populationId)

def Source.quote : Source → Program
  | .command primitive => .command primitive.quote
  | .seq a b => .seq a.quote b.quote
  | .ite guard a b => .ite guard.quote a.quote b.quote
  | .loop guard body => .loop guard.quote body.quote
  | .par a b => .par a.quote b.quote

def IntExpr.eval (state : Snapshot) : IntExpr → Option Int
  | .literal value => some value
  | .read target => state.integers target.id
  | .add a b => do pure ((← a.eval state) + (← b.eval state))

def Guard.eval (state : Snapshot) : Guard → Option Bool
  | .literal value => some value
  | .less a b => do pure ((← a.eval state) < (← b.eval state))

def Command.eval (state : Snapshot) : Command → Option Snapshot
  | .skip => some state
  | .assign target expr => (expr.eval state).map fun value =>
      { state with integers := Function.update state.integers target.id (some value) }
  | .alias target source => some
      { state with datasets := Function.update state.datasets target (state.datasets source) }
  | .test target data testName => some
      { state with rationals := Function.update state.rationals target.id (some 1)
                   ledger := state.ledger + {(state.datasets data, testName)} }
  | .pvalue target _ _ => some
      { state with rationals := Function.update state.rationals target.id (some 1) }

/-- A source small step can be silent; only a command emission extends a world. -/
structure Event where
  emission : Option Command
  state : Snapshot

/-- The Boolean selects left/right at every encountered parallel node. A finite
list declares a schedule, not a fuel-based meaning of termination. -/
def next (leftFirst : Bool) : Source → Snapshot → Option (Option Source × Event)
  | .command command, state => (command.eval state).map fun after =>
      (none, ⟨some command, after⟩)
  | .seq a b, state => (next leftFirst a state).map fun out =>
      (some (match out.1 with | none => b | some a' => .seq a' b), out.2)
  | .ite guard a b, state => (guard.eval state).map fun value =>
      (some (if value then a else b), ⟨none, state⟩)
  | .loop guard body, state => (guard.eval state).map fun value =>
      (if value then some (.seq body (.loop guard body)) else none, ⟨none, state⟩)
  | .par a b, state =>
      if leftFirst then (next leftFirst a state).map fun out =>
        (some (match out.1 with | none => b | some a' => .par a' b), out.2)
      else (next leftFirst b state).map fun out =>
        (some (match out.1 with | none => a | some b' => .par a b'), out.2)

def scheduled : List Bool → Option Source → Snapshot →
    Option (Option Source × Snapshot × List Event)
  | [], source, state => some (source, state, [])
  | _ :: _, none, state => some (none, state, [])
  | choice :: rest, some source, state => do
      let out ← next choice source state
      let tail ← scheduled rest out.1 out.2.state
      pure (tail.1, tail.2.1, out.2 :: tail.2.2)

def initialSnapshot : Snapshot :=
  ⟨fun name => if name = x.id ∨ name = y.id then some 0 else none,
    fun name => if name = oldReport.id then some (7 / 11 : ℚ) else none,
    fun _ => false, 0⟩

def incrementX : Source := .command (.assign x (.add (.read x) (.literal 1)))
def incrementY : Source := .command (.assign y (.add (.read y) (.literal 2)))
def terminatingLoop : Source := .loop (.less (.read x) (.literal 3)) incrementX
def parallel : Source := .par incrementX incrementY
def badParallel : Source := .par incrementX
  (.command (.assign y (.add (.read x) (.literal 2))))
def testData : Source := .command (.test report dataId Science.correctId)
def testAlias : Source := .command (.test report aliasId Science.correctId)
def aliasData : Source := .command (.alias aliasId dataId)
def reportOnly : Source := .command (.pvalue report dataId Science.correctId)
def repeatedTests : Source := .seq testData (.seq aliasData testAlias)
def extraTest : Source := .command (.test report dataId Science.extraId)
def undefinedBranch : Source := .ite
  (.less (.read ⟨⟨99⟩⟩) (.literal 0)) incrementX incrementY

def loopSmoke := scheduled (List.replicate 7 true) (some terminatingLoop) initialSnapshot
def leftSmoke := scheduled [true, true] (some parallel) initialSnapshot
def rightSmoke := scheduled [false, true] (some parallel) initialSnapshot
def repeatedSmoke := scheduled [true, true, true] (some repeatedTests) initialSnapshot
def reportSmoke := scheduled [true] (some reportOnly) initialSnapshot

abbrev Summary := Option Int × Option Int × Option ℚ × Option ℚ × Bool × Bool ×
  Nat × Nat × Nat × List Nat

def summarize (result : Option (Option Source × Snapshot × List Event)) : Option Summary :=
  result.map fun out =>
    let state := out.2.1
    (state.integers x.id, state.integers y.id, state.rationals report.id,
      state.rationals oldReport.id, state.datasets dataId, state.datasets aliasId,
      History.count state.ledger false Science.correctId,
      History.count state.ledger false Science.extraId, out.2.2.length,
      out.2.2.filterMap fun event => event.emission.map Command.code)

def loopSummary := summarize loopSmoke
def leftSummary := summarize leftSmoke
def rightSummary := summarize rightSmoke
def repeatedSummary := summarize repeatedSmoke
def reportSummary := summarize reportSmoke
def goodNICheck := noninterferingCheck incrementX.quote incrementY.quote
def badNICheck := noninterferingCheck incrementX.quote
  (.command (.assign y (.intAdd (.read x) (.integer 2))))

theorem good_ni : Noninterfering incrementX.quote incrementY.quote := by
  simp [incrementX, incrementY, Noninterfering, Source.quote, Command.quote, IntExpr.quote,
    Program.writes, Program.used, Program.reads, Primitive.writes, Primitive.reads,
    ProgramExpr.reads, x, y]

theorem bad_ni : ¬ Noninterfering incrementX.quote
    (.command (.assign y (.intAdd (.read x) (.integer 2)))) := by
  simp [incrementX, Noninterfering, Source.quote, Command.quote, IntExpr.quote,
    Program.writes, Program.used, Program.reads, Primitive.writes, Primitive.reads,
    ProgramExpr.reads, x, y]

theorem good_ni_computes : goodNICheck = true := by decide
theorem bad_ni_computes : badNICheck = false := by decide

noncomputable section

/-- The real result is justified by the genuine measure-theoretic tail event. -/
theorem exact_dirac_pvalue (test : TestId) (data : Bool) :
    (Science.testFor test).tailProbability data = ((1 : ℚ) : ℝ) := by
  simp

def Snapshot.memory (state : Snapshot) : ObservableMemory
  | .integer, name => state.integers name
  | .real, name => (state.rationals name).map fun q => (q : ℝ)
  | _, _ => none

def Snapshot.visible (state : Snapshot) : VisibleState Bool :=
  ⟨state.memory, state.datasets⟩

/-- Independent science is reused, but the interpretation is constructed at
Primitive, not cast from the existing TestId-command model. -/
def interpretation : AssertionInterpretation Bool Primitive where
  constants := fun sort _ => match sort with
    | .value sort => valueDefault sort
    | .dataset => false
    | .world => World.start Memory.empty (fun _ => false)
    | .trace => []
  functions := fun _ output _ _ => valueDefault output
  datasetFunctions := fun _ _ _ => false
  predicates := fun _ _ _ => False
  tests := fun _ test => Science.testFor test
  hypotheses := fun hypothesis hidden =>
    hypothesis = Science.hypothesisId ∧ hidden .boolean Science.parameter.id = some true
  requirements := fun hypothesis test population hidden _ =>
    hypothesis = Science.hypothesisId ∧ population = Science.populationId ∧
      Science.lawBinding test hidden
  jointRequirements := fun _ _ _ => False
  couplings := fun _ _ _ _ _ => none
  commands := fun _ => .skip

def context : ProgramContext Bool := ProgramContext.ofRelations interpretation
  (fun hidden visible => (∃ bit : Bool, hidden = Science.hiddenMemory bit) ∧
    visible = initialSnapshot.visible)
  (fun hidden before after data population =>
    population = Science.populationId ∧ after = before ∧ before.datasets dataId = data ∧
      eventProbability (Science.populationLaw hidden) {data} = 1)
  ⟨Science.hiddenMemory false, initialSnapshot.visible, ⟨⟨false, rfl⟩, rfl⟩⟩

def startWorld (bit : Bool) : World Bool Primitive := World.start
  (Memory.assemble initialSnapshot.memory (Science.hiddenMemory bit)) initialSnapshot.datasets

theorem start_admitted (bit : Bool) : Admitted context.model.dynamics (startWorld bit) :=
  admitted_start context.model.dynamics initialSnapshot.visible (Science.hiddenMemory bit)
    ⟨⟨bit, rfl⟩, rfl⟩

def Reifies (world : World Bool Primitive) (state : Snapshot) : Prop :=
  world.current.visible = state.visible ∧ world.current.history = state.ledger

def eventWorld (world : World Bool Primitive) (event : Event) : World Bool Primitive :=
  match event.emission with
  | none => world
  | some command => world.extend
      ⟨Memory.assemble event.state.memory world.current.memory.hidden,
        event.state.datasets, event.state.ledger, .command command.quote⟩

def eventsWorld (world : World Bool Primitive) (events : List Event) : World Bool Primitive :=
  events.foldl eventWorld world

@[simp] theorem start_reifies (bit : Bool) : Reifies (startWorld bit) initialSnapshot :=
  ⟨rfl, rfl⟩

theorem integer_correspondence (state : Snapshot) (expr : IntExpr) :
    evalProgramExpr interpretation state.visible expr.quote = expr.eval state := by
  induction expr with
  | literal value => rfl
  | read target => rfl
  | add a b ha hb => simp [IntExpr.quote, evalProgramExpr, IntExpr.eval, ha, hb]

theorem guard_correspondence (state : Snapshot) (guard : Guard) :
    evalProgramExpr interpretation state.visible guard.quote = guard.eval state := by
  cases guard with
  | literal value => rfl
  | less a b => simp [Guard.quote, Guard.eval, evalProgramExpr, integer_correspondence]

private theorem integer_write (state : Snapshot) (target : Variable .integer .observable)
    (value : Int) :
    (VisibleWrite.value target value).apply state.visible =
      ({state with integers := Function.update state.integers target.id (some value)} : Snapshot).visible := by
  apply congrArg₂ VisibleState.mk
  · funext sort name
    by_cases sameName : name = target.id
    · rw [sameName]
      cases sort <;> simp [Snapshot.visible, Snapshot.memory,
        Memory.observable, Memory.update, Memory.assemble, Function.update]
    · cases sort <;> simp [Snapshot.visible, Snapshot.memory,
        Memory.observable, Memory.update, Memory.assemble, Function.update,
        sameName, Ne.symm sameName]
  · rfl

private theorem rational_write (state : Snapshot) (target : Variable .real .observable)
    (value : ℚ) :
    (VisibleWrite.value target (value : ℝ)).apply state.visible =
      ({state with rationals := Function.update state.rationals target.id (some value)} : Snapshot).visible := by
  apply congrArg₂ VisibleState.mk
  · funext sort name
    by_cases sameName : name = target.id
    · rw [sameName]
      cases sort <;> simp [Snapshot.visible, Snapshot.memory,
        Memory.observable, Memory.update, Memory.assemble, Function.update]
    · cases sort <;> simp [Snapshot.visible, Snapshot.memory,
        Memory.observable, Memory.update, Memory.assemble, Function.update,
        sameName, Ne.symm sameName]
  · rfl

/-- Every restricted effect equals the actual library primitive effect, including
its full ledger delta. Reporting a probability emits the assignment, but no test. -/
theorem command_correspondence (state after : Snapshot) (command : Command)
    (evaluated : command.eval state = some after) :
    ∃ delta, primitiveEffect interpretation command.quote state.visible =
      some (after.visible, delta) ∧ after.ledger = state.ledger + delta := by
  cases command with
  | skip =>
      simp [Command.eval] at evaluated
      subst after
      exact ⟨0, rfl, by simp⟩
  | assign target expr =>
      cases h : expr.eval state with
      | none => simp [Command.eval, h] at evaluated
      | some value =>
          simp [Command.eval, h] at evaluated
          subst after
          refine ⟨0, ?_, by simp⟩
          simp [primitiveEffect, evalPrimitive, Command.quote,
            integer_correspondence, h, integer_write]
  | «alias» target source =>
      simp [Command.eval] at evaluated
      subst after
      exact ⟨0, rfl, by simp⟩
  | test target data testName =>
      simp [Command.eval] at evaluated
      subst after
      refine ⟨{(state.datasets data, testName)}, ?_, rfl⟩
      simp [primitiveEffect, evalPrimitive, Command.quote, evalDatasetExpr, interpretation]
      constructor
      · trans ({ state with rationals := Function.update state.rationals target.id (some 1) } :
          Snapshot).visible
        · simpa using rational_write state target 1
        · apply congrArg₂ VisibleState.mk
          · funext sort name
            cases sort <;> rfl
          · rfl
      · rfl
  | pvalue target data testName =>
      simp [Command.eval] at evaluated
      subst after
      refine ⟨0, ?_, by simp⟩
      simp [primitiveEffect, evalPrimitive, Command.quote, evalProgramExpr,
        evalDatasetExpr, interpretation]
      simpa [Snapshot.visible, Snapshot.memory] using rational_write state target 1

private theorem command_step (world : World Bool Primitive) (state after : Snapshot)
    (command : Command) (represented : Reifies world state)
    (evaluated : command.eval state = some after) :
    Step context (some (.command command.quote)) world none
      (eventWorld world ⟨some command, after⟩) ∧
      Reifies (eventWorld world ⟨some command, after⟩) after := by
  obtain ⟨delta, effect, ledger⟩ := command_correspondence state after command evaluated
  have enabled : primitiveEffect context.interpretation command.quote world.current.visible =
      some (after.visible, delta) := by simpa only [context, ProgramContext.ofRelations,
        represented.1] using effect
  have equality : eventWorld world ⟨some command, after⟩ =
      world.extend (commandState world.current command.quote after.visible delta) := by
    simp [eventWorld, commandState, Snapshot.visible, ← ledger, represented.2]
  constructor
  · rw [equality]
    exact .command enabled
  · simp [Reifies, eventWorld, State.visible, Snapshot.visible]

/-- One computed source step is exactly one real Step, even inside seq/par;
finishing a child adds no administrative step. -/
theorem next_correspondence (choice : Bool) (source : Source) (state : Snapshot)
    (out : Option Source × Event) (world : World Bool Primitive)
    (represented : Reifies world state) (computed : next choice source state = some out) :
    Step context (some source.quote) world (out.1.map Source.quote)
      (eventWorld world out.2) ∧ Reifies (eventWorld world out.2) out.2.state := by
  induction source generalizing state out world with
  | command command =>
      cases evaluated : command.eval state with
      | none => simp [next, evaluated] at computed
      | some after =>
          simp [next, evaluated] at computed
          subst out
          exact command_step world state after command represented evaluated
  | seq a b ihA ihB =>
      cases h : next choice a state with
      | none => simp [next, h] at computed
      | some child =>
          simp [next, h] at computed
          subst out
          obtain ⟨step, reifies⟩ := ihA state child world represented h
          refine ⟨?_, reifies⟩
          cases residual : child.1 with
          | none =>
              simp only [residual, Option.map_none] at step
              simpa [Source.quote, residual] using Step.seqFinish step
          | some a' =>
              simp only [residual, Option.map_some] at step
              simpa [Source.quote, residual] using Step.seqContinue step
  | ite guard a b ihA ihB =>
      cases h : guard.eval state with
      | none => simp [next, h] at computed
      | some value =>
          simp [next, h] at computed
          subst out
          have enabled : evalProgramExpr context.interpretation world.current.visible guard.quote =
              some value := by simpa only [context, ProgramContext.ofRelations, represented.1,
                guard_correspondence] using h
          cases value
          · exact ⟨.ifFalse enabled, represented⟩
          · exact ⟨.ifTrue enabled, represented⟩
  | loop guard body ih =>
      cases h : guard.eval state with
      | none => simp [next, h] at computed
      | some value =>
          simp [next, h] at computed
          subst out
          have enabled : evalProgramExpr context.interpretation world.current.visible guard.quote =
              some value := by simpa only [context, ProgramContext.ofRelations, represented.1,
                guard_correspondence] using h
          cases value
          · exact ⟨.loopFalse enabled, represented⟩
          · exact ⟨.loopTrue enabled, represented⟩
  | par a b ihA ihB =>
      cases choice with
      | true =>
          cases h : next true a state with
          | none => simp [next, h] at computed
          | some child =>
              simp [next, h] at computed
              subst out
              obtain ⟨step, reifies⟩ := ihA state child world represented h
              refine ⟨?_, reifies⟩
              cases residual : child.1 with
              | none =>
                  simp only [residual, Option.map_none] at step
                  simpa [Source.quote, residual] using Step.parLeftFinish step
              | some a' =>
                  simp only [residual, Option.map_some] at step
                  simpa [Source.quote, residual] using Step.parLeftContinue step
      | false =>
          cases h : next false b state with
          | none => simp [next, h] at computed
          | some child =>
              simp [next, h] at computed
              subst out
              obtain ⟨step, reifies⟩ := ihB state child world represented h
              refine ⟨?_, reifies⟩
              cases residual : child.1 with
              | none =>
                  simp only [residual, Option.map_none] at step
                  simpa [Source.quote, residual] using Step.parRightFinish step
              | some b' =>
                  simp only [residual, Option.map_some] at step
                  simpa [Source.quote, residual] using Step.parRightContinue step

/-- The schedule length counts emitted and silent source steps alike. No claim
of totality or generic measure computation is made. -/
theorem scheduled_correspondence (schedule : List Bool) (source : Option Source)
    (state final : Snapshot) (residual : Option Source) (events : List Event)
    (world : World Bool Primitive) (represented : Reifies world state)
    (computed : scheduled schedule source state = some (residual, final, events)) :
    Steps context events.length (source.map Source.quote) world
      (residual.map Source.quote) (eventsWorld world events) ∧
      Reifies (eventsWorld world events) final := by
  induction schedule generalizing source state final residual events world with
  | nil =>
      simp [scheduled] at computed
      rcases computed with ⟨rfl, rfl, rfl⟩
      exact ⟨.refl _ _, represented⟩
  | cons choice rest ih =>
      cases source with
      | none =>
          simp [scheduled] at computed
          rcases computed with ⟨rfl, rfl, rfl⟩
          exact ⟨.refl _ _, represented⟩
      | some program =>
          cases hn : next choice program state with
          | none => simp [scheduled, hn] at computed
          | some out =>
              cases ht : scheduled rest out.1 out.2.state with
              | none => simp [scheduled, hn, ht] at computed
              | some tail =>
                  simp [scheduled, hn, ht] at computed
                  rcases computed with ⟨rfl, rfl, rfl⟩
                  obtain ⟨first, repr⟩ := next_correspondence choice program state out world represented hn
                  obtain ⟨steps, finalRepr⟩ := ih out.1 out.2.state tail.2.1 tail.1 tail.2.2
                    (eventWorld world out.2) repr ht
                  exact ⟨by simpa [eventsWorld] using Steps.cons first steps, finalRepr⟩

/-- Real sampling uses the independent population law; both Boolean hidden
parameters are admitted in the full relation-defined model. -/
def sampledWorld (bit : Bool) : World Bool Primitive :=
  (startWorld bit).extend
    ⟨(startWorld bit).current.memory, initialSnapshot.datasets, 0,
      .sample false Science.populationId⟩

theorem sampled_admitted (bit : Bool) :
    Admitted context.model.dynamics (sampledWorld bit) := by
  apply admitted_extend (start_admitted bit)
  · rfl
  · change (Science.populationId = Science.populationId ∧
      initialSnapshot.visible = initialSnapshot.visible ∧
      initialSnapshot.datasets dataId = false ∧
      eventProbability (Science.populationLaw (Science.hiddenMemory bit)) {false} = 1) ∧
      (0 : History Bool) = 0
    refine ⟨⟨rfl, rfl, rfl, ?_⟩, rfl⟩
    exact eventProbability_dirac_of_mem false (by simp)

theorem sampled_reifies (bit : Bool) : Reifies (sampledWorld bit) initialSnapshot := by
  simp [Reifies, sampledWorld, startWorld, initialSnapshot, State.visible, Snapshot.visible]

theorem sampled_hidden_distinct :
    (sampledWorld false).current.memory.hidden ≠
      (sampledWorld true).current.memory.hidden := by
  simpa [sampledWorld, startWorld] using Science.hiddenMemory_false_ne_true

theorem sampled_accessible (left right : Bool) :
    Accessible (sampledWorld left) (sampledWorld right) := by
  simp [Accessible, observeWorld, World.trace, World.extend, sampledWorld, startWorld,
    World.start, World.current, observeState, Memory.assemble]

end

def afterX (state : Snapshot) (n : Int) : Snapshot :=
  {state with integers := Function.update state.integers x.id (some n)}

def afterY (state : Snapshot) (n : Int) : Snapshot :=
  {state with integers := Function.update state.integers y.id (some n)}

def loopFinal := afterX (afterX (afterX initialSnapshot 1) 2) 3
def loopEvents : List Event :=
  [⟨none, initialSnapshot⟩,
   ⟨some (.assign x (.add (.read x) (.literal 1))), afterX initialSnapshot 1⟩,
   ⟨none, afterX initialSnapshot 1⟩,
   ⟨some (.assign x (.add (.read x) (.literal 1))), afterX (afterX initialSnapshot 1) 2⟩,
   ⟨none, afterX (afterX initialSnapshot 1) 2⟩,
   ⟨some (.assign x (.add (.read x) (.literal 1))), loopFinal⟩,
   ⟨none, loopFinal⟩]

theorem loop_computes : loopSmoke = some (none, loopFinal, loopEvents) := by rfl

theorem loop_seven_steps (bit : Bool) :
    Steps context 7 (some terminatingLoop.quote) (sampledWorld bit) none
      (eventsWorld (sampledWorld bit) loopEvents) := by
  exact (scheduled_correspondence _ _ _ _ _ _ _ (sampled_reifies bit) loop_computes).1

theorem loop_executes (bit : Bool) :
    executes context terminatingLoop.quote (sampledWorld bit)
      (eventsWorld (sampledWorld bit) loopEvents) := by
  exact ⟨trivial, sampled_admitted bit, 7, loop_seven_steps bit⟩

theorem loop_final_x (bit : Bool) :
    (eventsWorld (sampledWorld bit) loopEvents).current.memory.read x = some 3 := by
  have represented := (scheduled_correspondence _ _ _ _ _ _ _
    (sampled_reifies bit) loop_computes).2
  have memory := congrArg (fun visible : VisibleState Bool => visible.memory .integer x.id)
    represented.1
  simpa [State.visible, Memory.read, Memory.observable, loopFinal, afterX, Snapshot.visible, Snapshot.memory]
    using memory

theorem loop_three_command_states (bit : Bool) :
    (eventsWorld (sampledWorld bit) loopEvents).trace.length =
      (sampledWorld bit).trace.length + 3 := by
  simp [eventsWorld, loopEvents, eventWorld, World.extend_trace]

def leftFinal := afterY (afterX initialSnapshot 1) 2
def rightFinal := afterX (afterY initialSnapshot 2) 1
def leftEvents : List Event :=
  [⟨some (.assign x (.add (.read x) (.literal 1))), afterX initialSnapshot 1⟩,
   ⟨some (.assign y (.add (.read y) (.literal 2))), leftFinal⟩]
def rightEvents : List Event :=
  [⟨some (.assign y (.add (.read y) (.literal 2))), afterY initialSnapshot 2⟩,
   ⟨some (.assign x (.add (.read x) (.literal 1))), rightFinal⟩]

theorem left_computes : leftSmoke = some (none, leftFinal, leftEvents) := by rfl
theorem right_computes : rightSmoke = some (none, rightFinal, rightEvents) := by rfl

noncomputable def leftWorld (bit : Bool) := eventsWorld (sampledWorld bit) leftEvents
noncomputable def rightWorld (bit : Bool) := eventsWorld (sampledWorld bit) rightEvents

theorem left_steps (bit : Bool) :
    Steps context 2 (some parallel.quote) (sampledWorld bit) none (leftWorld bit) :=
  (scheduled_correspondence _ _ _ _ _ _ _ (sampled_reifies bit) left_computes).1

theorem right_steps (bit : Bool) :
    Steps context 2 (some parallel.quote) (sampledWorld bit) none (rightWorld bit) :=
  (scheduled_correspondence _ _ _ _ _ _ _ (sampled_reifies bit) right_computes).1

theorem left_executes (bit : Bool) :
    executes context parallel.quote (sampledWorld bit) (leftWorld bit) :=
  ⟨⟨trivial, trivial, good_ni⟩, sampled_admitted bit, 2, left_steps bit⟩

theorem right_executes (bit : Bool) :
    executes context parallel.quote (sampledWorld bit) (rightWorld bit) :=
  ⟨⟨trivial, trivial, good_ni⟩, sampled_admitted bit, 2, right_steps bit⟩

theorem parallel_visible : leftFinal.visible = rightFinal.visible := by
  apply congrArg₂ VisibleState.mk
  · funext sort name
    cases sort <;>
      simp [leftFinal, rightFinal, afterX, afterY, Snapshot.memory,
        Function.update, x, y]
    split_ifs <;> simp_all
  · rfl

/-- Full semantic views agree, not ordered action traces. The compatible-hidden
set and provenance equations are obtained from the actual seven/two-step runs. -/
theorem parallel_semantic_view (bit : Bool) :
    semanticView context.model.dynamics (leftWorld bit) =
      semanticView context.model.dynamics (rightWorld bit) := by
  have lr : Reifies (leftWorld bit) leftFinal := (scheduled_correspondence _ _ _ _ _ _ _
    (sampled_reifies bit) left_computes).2
  have rr : Reifies (rightWorld bit) rightFinal := (scheduled_correspondence _ _ _ _ _ _ _
    (sampled_reifies bit) right_computes).2
  have li := (show Run context _ _ _ _ from ⟨2, left_steps bit⟩).information
  have ri := (show Run context _ _ _ _ from ⟨2, right_steps bit⟩).information
  unfold semanticView
  rw [lr.1, rr.1, parallel_visible, lr.2, rr.2, li.1, ri.1,
    li.2.1, ri.2.1, li.2.2.1, ri.2.2.1]
  rfl

theorem parallel_order_differs :
    (leftEvents.filterMap fun event => event.emission.map Command.code) ≠
      (rightEvents.filterMap fun event => event.emission.map Command.code) := by decide

theorem parallel_complete_traces_differ (bit : Bool) :
    (leftWorld bit).trace ≠ (rightWorld bit).trace := by
  intro equality
  have first := congrArg (fun states : List (State Bool Primitive) =>
    (states[2]?).map fun state => state.memory.read x) equality
  simp [leftWorld, rightWorld, eventsWorld, eventWorld, leftEvents, rightEvents,
    sampledWorld, startWorld, World.trace, World.extend, World.start,
    Memory.read, Memory.assemble, Snapshot.memory, afterX, afterY, initialSnapshot,
    x, y] at first

def testedSnapshot : Snapshot :=
  { initialSnapshot with
    rationals := Function.update initialSnapshot.rationals report.id (some 1)
    ledger := {(false, Science.correctId)} }
def aliasedSnapshot : Snapshot :=
  {testedSnapshot with datasets := Function.update testedSnapshot.datasets aliasId false}
def repeatedFinal : Snapshot :=
  { aliasedSnapshot with
    rationals := Function.update aliasedSnapshot.rationals report.id (some 1)
    ledger := aliasedSnapshot.ledger + {(false, Science.correctId)} }
def repeatedEvents : List Event :=
  [⟨some (.test report dataId Science.correctId), testedSnapshot⟩,
   ⟨some (.alias aliasId dataId), aliasedSnapshot⟩,
   ⟨some (.test report aliasId Science.correctId), repeatedFinal⟩]

theorem repeated_computes : repeatedSmoke = some (none, repeatedFinal, repeatedEvents) := by rfl

noncomputable def repeatedWorld (bit : Bool) := eventsWorld (sampledWorld bit) repeatedEvents

theorem repeated_executes (bit : Bool) :
    executes context repeatedTests.quote (sampledWorld bit) (repeatedWorld bit) :=
  ⟨⟨trivial, trivial, trivial⟩, sampled_admitted bit, 3,
    (scheduled_correspondence _ _ _ _ _ _ _ (sampled_reifies bit) repeated_computes).1⟩

theorem alias_multiplicity (bit : Bool) :
    History.count (repeatedWorld bit).current.history false Science.correctId = 2 := by
  have represented : Reifies (repeatedWorld bit) repeatedFinal := (scheduled_correspondence _ _ _ _ _ _ _
    (sampled_reifies bit) repeated_computes).2
  rw [represented.2]
  simp [repeatedFinal, aliasedSnapshot, testedSnapshot, History.count]

def reportingFinal : Snapshot :=
  {initialSnapshot with rationals := Function.update initialSnapshot.rationals report.id (some 1)}
def reportingEvents : List Event := [⟨some (.pvalue report dataId Science.correctId), reportingFinal⟩]

theorem reporting_computes : reportSmoke = some (none, reportingFinal, reportingEvents) := by rfl

theorem report_adds_no_history (bit : Bool) :
    (eventsWorld (sampledWorld bit) reportingEvents).current.history = 0 :=
  (scheduled_correspondence _ _ _ _ _ _ _ (sampled_reifies bit) reporting_computes).2.2

theorem report_is_not_a_test :
    reportingFinal.visible = testedSnapshot.visible ∧
      reportingFinal.ledger ≠ testedSnapshot.ledger := by
  constructor
  · rfl
  · simp [reportingFinal, testedSnapshot, initialSnapshot]

theorem protected_old_result (bit : Bool) :
    (repeatedWorld bit).current.memory.read oldReport = some ((7 / 11 : ℚ) : ℝ) := by
  have represented : Reifies (repeatedWorld bit) repeatedFinal := (scheduled_correspondence _ _ _ _ _ _ _
    (sampled_reifies bit) repeated_computes).2
  have memory := congrArg (fun visible : VisibleState Bool => visible.memory .real oldReport.id)
    represented.1
  simpa [State.visible, Memory.read, Memory.observable, repeatedFinal, aliasedSnapshot, testedSnapshot,
    initialSnapshot, Snapshot.visible, Snapshot.memory, oldReport, report] using memory

theorem undefined_guard_computes :
    next true undefinedBranch initialSnapshot = none := by rfl

theorem undefined_guard_no_run (bit : Bool) (after : World Bool Primitive) :
    ¬ RawRun context undefinedBranch.quote (sampledWorld bit) after := by
  apply run_ite_undefined
  rfl

theorem source_skip_step (world : World Bool Primitive) :
    Step context (some Program.skip) world none
      (world.extend (commandState world.current .skip world.current.visible 0)) :=
  .command rfl

theorem false_loop_step (world : World Bool Primitive) :
    Step context (some (.loop (.boolean false) incrementX.quote)) world none world :=
  .loopFalse rfl

theorem branch_true_step (world : World Bool Primitive) :
    Step context (some (.ite (.boolean true) incrementX.quote incrementY.quote))
      world (some incrementX.quote) world := .ifTrue rfl

theorem branch_false_step (world : World Bool Primitive) :
    Step context (some (.ite (.boolean false) incrementX.quote incrementY.quote))
      world (some incrementY.quote) world := .ifFalse rfl

def extraFinal : Snapshot :=
  { repeatedFinal with
    rationals := Function.update repeatedFinal.rationals report.id (some 1)
    ledger := repeatedFinal.ledger + {(false, Science.extraId)} }
def extraEvents : List Event := [⟨some (.test report dataId Science.extraId), extraFinal⟩]
noncomputable def extraWorld (bit : Bool) := eventsWorld (repeatedWorld bit) extraEvents

theorem nonzero_ledger_computes :
    scheduled [true] (some extraTest) repeatedFinal = some (none, extraFinal, extraEvents) := by rfl

theorem nonzero_ledger_executes (bit : Bool) :
    executes context extraTest.quote (repeatedWorld bit) (extraWorld bit) := by
  have represented := (scheduled_correspondence _ _ _ _ _ _ _
    (sampled_reifies bit) repeated_computes).2
  exact ⟨trivial, exec_admitted (repeated_executes bit), 1,
    (scheduled_correspondence _ _ _ _ _ _ _ represented nonzero_ledger_computes).1⟩

theorem preserves_nonzero_ledger (bit : Bool) :
    (extraWorld bit).current.history =
      (repeatedWorld bit).current.history + {(false, Science.extraId)} := by
  have represented : Reifies (repeatedWorld bit) repeatedFinal := (scheduled_correspondence _ _ _ _ _ _ _
    (sampled_reifies bit) repeated_computes).2
  have finalRepr : Reifies (extraWorld bit) extraFinal := (scheduled_correspondence _ _ _ _ _ _ _
    represented nonzero_ledger_computes).2
  rw [finalRepr.2, represented.2]
  rfl

theorem same_memory_different_histories (bit : Bool) :
    (repeatedWorld bit).current.visible = (extraWorld bit).current.visible ∧
      (repeatedWorld bit).current.history ≠ (extraWorld bit).current.history ∧
      (repeatedWorld bit).trace ≠ (extraWorld bit).trace := by
  have represented : Reifies (repeatedWorld bit) repeatedFinal := (scheduled_correspondence _ _ _ _ _ _ _
    (sampled_reifies bit) repeated_computes).2
  have finalRepr : Reifies (extraWorld bit) extraFinal := (scheduled_correspondence _ _ _ _ _ _ _
    represented nonzero_ledger_computes).2
  refine ⟨?_, ?_, ?_⟩
  · rw [represented.1, finalRepr.1]
    apply congrArg₂ VisibleState.mk
    · funext sort name
      cases sort <;>
        simp [extraFinal, repeatedFinal, aliasedSnapshot, testedSnapshot,
          Snapshot.memory, Function.update]
    · rfl
  · rw [preserves_nonzero_ledger]
    intro equality
    have cardinality := congrArg Multiset.card equality
    simp at cardinality
  · intro equality
    have length := congrArg List.length equality
    simp [extraWorld, eventsWorld, extraEvents, eventWorld, World.extend_trace] at length

theorem parallel_all_assertions {Γ : List GhostSort}
    (env : GhostEnv Bool Primitive Γ) (assertion : Assertion Γ) (bit : Bool) :
    satisfiesView interpretation context.model env
      (semanticView context.model.dynamics (leftWorld bit)) assertion ↔
    satisfiesView interpretation context.model env
      (semanticView context.model.dynamics (rightWorld bit)) assertion := by
  rw [parallel_semantic_view bit]

def knowsXOne (Γ : List GhostSort) : ModalFormula Γ :=
  .knows (.knows (.atom (.equal (.valueRead .ambient x) (.integer 1))))

/-- Nested K ranges over every realized view in the actual model and keeps the
same arbitrary ghost environment. No finite table is used as a modal universe. -/
theorem parallel_nested_knowledge {Γ : List GhostSort}
    (env : GhostEnv Bool Primitive Γ) (bit : Bool) :
    satisfiesView interpretation context.model env
      (semanticView context.model.dynamics (leftWorld bit)) (.modal (knowsXOne Γ)) := by
  refine ⟨semanticView_mem_views context.model (exec_admitted (left_executes bit)), ?_⟩
  change ∀ first, first ∈ context.model.views →
    ViewAccessible (semanticView context.model.dynamics (leftWorld bit)) first →
    ∀ second, second ∈ context.model.views → ViewAccessible first second → _
  intro first _ firstAccess second _ secondAccess
  have represented := (scheduled_correspondence _ _ _ _ _ _ _
    (sampled_reifies bit) left_computes).2
  have visible : second.visible = leftFinal.visible :=
    secondAccess.1.symm.trans (firstAccess.1.symm.trans represented.1)
  change ∃ value, evalTerm interpretation context.model env second
      (.valueRead .ambient x) = some value ∧
    evalTerm interpretation context.model env second (.integer 1) = some value
  refine ⟨(1 : Int), ?_, rfl⟩
  simp [evalTerm, visible, leftFinal, afterX, afterY, Snapshot.visible, Snapshot.memory,
    Memory.read, Memory.assemble, initialSnapshot, x, y]

theorem sampled_both_hidden_compatible (source bit : Bool) :
    Science.hiddenMemory bit ∈ compatibleHidden context.model.dynamics (sampledWorld source) := by
  have member := admitted_hidden_mem_compatible (sampled_admitted bit)
  rw [compatibleHidden_eq_of_accessible (sampled_accessible bit source)] at member
  simpa [sampledWorld, startWorld] using member

theorem independently_correct_test (bit : Bool) :
    Science.lawBinding Science.correctId (Science.hiddenMemory bit) := by
  rw [Lara.Examples.BHLBelief.lawBinding_iff]
  decide

theorem false_loop_no_command_state (world : World Bool Primitive) :
    Steps context 1 (some (.loop (.boolean false) incrementX.quote)) world none world ∧
      world.trace.length = world.trace.length :=
  ⟨.cons (false_loop_step world) (.refl _ _), rfl⟩

theorem source_skip_one_command_state (world : World Bool Primitive) :
    (world.extend (commandState world.current .skip world.current.visible 0)).trace.length =
      world.trace.length + 1 := by
  simp [World.extend_trace]

theorem aliases_share_multiplicity (bit : Bool) :
    historyCount (repeatedWorld bit).current.datasets (repeatedWorld bit).current.history
      dataId Science.correctId = 2 ∧
    historyCount (repeatedWorld bit).current.datasets (repeatedWorld bit).current.history
      aliasId Science.correctId = 2 := by
  have represented := (scheduled_correspondence _ _ _ _ _ _ _
    (sampled_reifies bit) repeated_computes).2
  have datasets := congrArg VisibleState.datasets represented.1
  change (History.count _ _ _ = 2) ∧ (History.count _ _ _ = 2)
  rw [show (repeatedWorld bit).current.datasets = repeatedFinal.datasets from datasets]
  simpa [repeatedFinal, aliasedSnapshot, testedSnapshot, initialSnapshot] using
    And.intro (alias_multiplicity bit) (alias_multiplicity bit)

theorem bad_writes_are_disjoint :
    ∀ cell ∈ incrementX.quote.writes,
      cell ∉ (Program.command (.assign y (.intAdd (.read x) (.integer 2)))).writes := by
  simp [incrementX, Source.quote, Command.quote, Program.writes, Primitive.writes, x, y]

def trueBranchEvents : List Event :=
  [⟨none, initialSnapshot⟩,
    ⟨some (.assign x (.add (.read x) (.literal 1))), afterX initialSnapshot 1⟩]
def falseBranchEvents : List Event :=
  [⟨none, initialSnapshot⟩,
    ⟨some (.assign y (.add (.read y) (.literal 2))), afterY initialSnapshot 2⟩]

theorem true_branch_computes :
    scheduled [true, true] (some (.ite (.literal true) incrementX incrementY)) initialSnapshot =
      some (none, afterX initialSnapshot 1, trueBranchEvents) := by rfl
theorem false_branch_computes :
    scheduled [true, true] (some (.ite (.literal false) incrementX incrementY)) initialSnapshot =
      some (none, afterY initialSnapshot 2, falseBranchEvents) := by rfl

theorem true_branch_executes (bit : Bool) :
    executes context (.ite (.boolean true) incrementX.quote incrementY.quote)
      (sampledWorld bit) (eventsWorld (sampledWorld bit) trueBranchEvents) :=
  ⟨⟨trivial, trivial⟩, sampled_admitted bit, 2,
    (scheduled_correspondence _ _ _ _ _ _ _ (sampled_reifies bit) true_branch_computes).1⟩
theorem false_branch_executes (bit : Bool) :
    executes context (.ite (.boolean false) incrementX.quote incrementY.quote)
      (sampledWorld bit) (eventsWorld (sampledWorld bit) falseBranchEvents) :=
  ⟨⟨trivial, trivial⟩, sampled_admitted bit, 2,
    (scheduled_correspondence _ _ _ _ _ _ _ (sampled_reifies bit) false_branch_computes).1⟩


def branchTrueSummary := summarize (scheduled [true, true]
  (some (.ite (.literal true) incrementX incrementY)) initialSnapshot)
def branchFalseSummary := summarize (scheduled [true, true]
  (some (.ite (.literal false) incrementX incrementY)) initialSnapshot)
def skipSummary := summarize (scheduled [true] (some (.command .skip)) initialSnapshot)
def falseLoopSummary := summarize (scheduled [true]
  (some (.loop (.literal false) incrementX)) initialSnapshot)
def undefinedGuardRejected := (next true undefinedBranch initialSnapshot).isNone
def nonzeroLedgerSummary := summarize (scheduled [true] (some extraTest) repeatedFinal)

/-- Runtime flags inspect actual computed outputs. The permanent correspondence
and witness theorems above supply the semantic justification for these checks. -/
def loopChecks : Option Bool := loopSmoke.map fun out =>
  out.1.isNone && decide (out.2.1.integers x.id = some 3) &&
  decide (out.2.2.length = 7) &&
  decide ((out.2.2.filterMap fun event => event.emission).length = 3)

def parallelChecks : Option Bool := do
  let left ← leftSmoke
  let right ← rightSmoke
  pure (left.1.isNone && right.1.isNone &&
    decide (left.2.1.integers x.id = right.2.1.integers x.id) &&
    decide (left.2.1.integers y.id = right.2.1.integers y.id) &&
    decide (left.2.1.rationals oldReport.id = right.2.1.rationals oldReport.id) &&
    decide (left.2.1.datasets dataId = right.2.1.datasets dataId) &&
    decide (left.2.1.ledger = right.2.1.ledger) &&
    decide ((left.2.2.filterMap fun event => event.emission.map Command.code) ≠
      (right.2.2.filterMap fun event => event.emission.map Command.code)))

def historyChecks : Option Bool := do
  let repeated ← repeatedSmoke
  let reported ← reportSmoke
  let extra ← scheduled [true] (some extraTest) repeated.2.1
  pure (decide (History.count repeated.2.1.ledger false Science.correctId = 2) &&
    decide (reported.2.1.ledger = 0) &&
    decide (History.count extra.2.1.ledger false Science.correctId = 2) &&
    decide (History.count extra.2.1.ledger false Science.extraId = 1) &&
    decide (repeated.2.1.rationals report.id = extra.2.1.rationals report.id) &&
    decide (repeated.2.1.rationals oldReport.id = some (7 / 11 : ℚ)) &&
    decide (repeated.2.1.ledger ≠ extra.2.1.ledger))

theorem loop_checks_compute : loopChecks = some true := by decide
theorem parallel_checks_compute : parallelChecks = some true := by
  simp [parallelChecks, left_computes, right_computes, leftFinal, rightFinal,
    afterX, afterY, initialSnapshot, x, y, oldReport, Function.update,
    leftEvents, rightEvents, Command.code]
theorem history_checks_compute : historyChecks = some true := by
  simp only [historyChecks, repeated_computes, reporting_computes]
  dsimp only [Bind.bind, Option.bind]
  rw [nonzero_ledger_computes]
  simp [repeatedFinal, aliasedSnapshot, testedSnapshot, reportingFinal, extraFinal,
    initialSnapshot, History.count, report, oldReport, Science.correctId, Science.extraId,
    Function.update]
theorem undefined_check_computes : undefinedGuardRejected = true := by decide

def nestedParallelSummary := summarize (scheduled [true, true, true]
  (some (.par parallel (.command .skip))) initialSnapshot)

end Lara.Examples.BHLExecution
