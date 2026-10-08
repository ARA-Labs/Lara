import Lara.Examples.BHLBinaryScience

/-!
Exact rational computation for the informative finite instance and its actual
reference runs. This reuses the existing typed source commands, snapshots and
world-event reification; it does not call the PR04 Dirac-only evaluator. Tests
append the whole ledger delta. Merely reporting a p-value appends no test.
-/

namespace Lara.Examples.BHLBinaryRuns

open Lara.BHL
open Lara.Examples.BHLBinaryModel
open Lara.Examples.BHLSoundnessScience (Prior allowed secondReport)
open Lara.Examples.BHLExecution (Snapshot report oldReport dataId aliasId)

/-- Compute the finite null tail, then record this actual test occurrence. -/
def runTest (state : Snapshot) (target : Variable .real .observable)
    (data : DatasetId) (name : TestId) : Snapshot :=
  { state with
    rationals := Function.update state.rationals target.id
      (some (Tests.Binary.pvalue (state.datasets data)))
    ledger := state.ledger + {(state.datasets data, name)} }

/-- The same numeric computation without a test-history occurrence. -/
def runPvalue (state : Snapshot) (target : Variable .real .observable)
    (data : DatasetId) : Snapshot :=
  { state with
    rationals := Function.update state.rationals target.id
      (some (Tests.Binary.pvalue (state.datasets data))) }

noncomputable section

private theorem rational_write (state : Snapshot) (target : Variable .real .observable)
    (value : ℚ) :
    (VisibleWrite.value target (value : ℝ)).apply state.visible =
      ({state with rationals := Function.update state.rationals target.id (some value)} : Snapshot).visible := by
  apply congrArg₂ VisibleState.mk
  · funext sort name
    by_cases sameName : name = target.id
    · rw [sameName]
      cases sort <;> simp [Lara.Examples.BHLExecution.Snapshot.visible,
        Lara.Examples.BHLExecution.Snapshot.memory, Memory.observable, Memory.update,
        Memory.assemble, Function.update]
    · cases sort <;> simp [Lara.Examples.BHLExecution.Snapshot.visible,
        Lara.Examples.BHLExecution.Snapshot.memory, Memory.observable, Memory.update,
        Memory.assemble, Function.update, sameName, Ne.symm sameName]
  · rfl

 theorem test_effect (state : Snapshot) (target : Variable .real .observable)
    (data : DatasetId) (name : TestId) :
    primitiveEffect interpretation (Lara.Examples.BHLExecution.Command.quote (.test target data name)) state.visible =
      some ((runTest state target data name).visible, {(state.datasets data, name)}) := by
  simp [primitiveEffect, evalPrimitive, Lara.Examples.BHLExecution.Command.quote,
    evalDatasetExpr, interpretation]
  constructor
  · trans ({ state with rationals := Function.update state.rationals target.id (some (Tests.Binary.pvalue (state.datasets data))) } : Snapshot).visible
    · simpa only [Lara.Examples.BHLExecution.Snapshot.visible] using rational_write state target (Tests.Binary.pvalue (state.datasets data))
    · apply congrArg₂ VisibleState.mk
      · funext sort id
        cases sort <;> rfl
      · rfl
  · rfl

 theorem pvalue_effect (state : Snapshot) (target : Variable .real .observable)
    (data : DatasetId) (name : TestId) :
    primitiveEffect interpretation (Lara.Examples.BHLExecution.Command.quote (.pvalue target data name)) state.visible =
      some ((runPvalue state target data).visible, 0) := by
  simp [primitiveEffect, evalPrimitive, Lara.Examples.BHLExecution.Command.quote,
    evalProgramExpr, evalDatasetExpr, interpretation]
  simpa [runPvalue, Lara.Examples.BHLExecution.Snapshot.visible,
    Lara.Examples.BHLExecution.Snapshot.memory] using
      rational_write state target (Tests.Binary.pvalue (state.datasets data))

 theorem test_step (prior : Prior) (world : World Bool Primitive) (state : Snapshot)
    (target : Variable .real .observable) (data : DatasetId) (name : TestId)
    (represented : Lara.Examples.BHLExecution.Reifies world state) :
    Step (context prior)
      (some (.command (Lara.Examples.BHLExecution.Command.quote (.test target data name)))) world none
      (Lara.Examples.BHLExecution.eventWorld world
        ⟨some (.test target data name), runTest state target data name⟩) ∧
      Lara.Examples.BHLExecution.Reifies
        (Lara.Examples.BHLExecution.eventWorld world
          ⟨some (.test target data name), runTest state target data name⟩)
        (runTest state target data name) := by
  have enabled : primitiveEffect (context prior).interpretation
      (Lara.Examples.BHLExecution.Command.quote (.test target data name)) world.current.visible =
      some ((runTest state target data name).visible, {(state.datasets data, name)}) := by
    change primitiveEffect interpretation _ _ = _
    rw [represented.1]
    exact test_effect state target data name
  have equality : Lara.Examples.BHLExecution.eventWorld world
      ⟨some (.test target data name), runTest state target data name⟩ =
      world.extend (commandState world.current
        (Lara.Examples.BHLExecution.Command.quote (.test target data name))
        (runTest state target data name).visible {(state.datasets data, name)}) := by
    simp [Lara.Examples.BHLExecution.eventWorld, commandState,
      Lara.Examples.BHLExecution.Snapshot.visible, runTest, represented.2]
  constructor
  · rw [equality]
    exact .command enabled
  · simp [Lara.Examples.BHLExecution.Reifies, Lara.Examples.BHLExecution.eventWorld,
      State.visible, Lara.Examples.BHLExecution.Snapshot.visible]

 theorem sampled_reifies (n : Int) (first second : Bool) :
    Lara.Examples.BHLExecution.Reifies (sampledWorld n first second) (initialSnapshot first second) := by
  simp [Lara.Examples.BHLExecution.Reifies, sampledWorld, firstSample, startWorld,
    initialSnapshot, Lara.Examples.BHLExecution.initialSnapshot, State.visible,
    Lara.Examples.BHLExecution.Snapshot.visible]

def singleSource (name : TestId) : Lara.Examples.BHLExecution.Source :=
  .command (.test report dataId name)

def pairSource : Lara.Examples.BHLExecution.Source :=
  .seq (singleSource firstId) (.command (.test secondReport aliasId secondId))

def hiddenSource : Lara.Examples.BHLExecution.Source :=
  .seq (singleSource hiddenId) (singleSource firstId)

def singleFinal (first second : Bool) (name : TestId) : Snapshot :=
  runTest (initialSnapshot first second) report dataId name

def pairFinal (first second : Bool) : Snapshot :=
  runTest (singleFinal first second firstId) secondReport aliasId secondId

def hiddenFinal (first second : Bool) : Snapshot :=
  runTest (singleFinal first second hiddenId) report dataId firstId

def singleWorld (n : Int) (first second : Bool) (name : TestId) : World Bool Primitive :=
  Lara.Examples.BHLExecution.eventWorld (sampledWorld n first second)
    ⟨some (.test report dataId name), singleFinal first second name⟩

def pairWorld (n : Int) (first second : Bool) : World Bool Primitive :=
  Lara.Examples.BHLExecution.eventWorld (singleWorld n first second firstId)
    ⟨some (.test secondReport aliasId secondId), pairFinal first second⟩

def hiddenWorld (n : Int) (first second : Bool) : World Bool Primitive :=
  Lara.Examples.BHLExecution.eventWorld (singleWorld n first second hiddenId)
    ⟨some (.test report dataId firstId), hiddenFinal first second⟩

 theorem single_steps (prior : Prior) (n : Int) (first second : Bool) (name : TestId) :
    Steps (context prior) 1 (some (singleSource name).quote) (sampledWorld n first second) none
      (singleWorld n first second name) := by
  exact .cons (test_step prior _ _ report dataId name (sampled_reifies n first second)).1 (.refl _ _)

 theorem single_reifies (prior : Prior) (n : Int) (first second : Bool) (name : TestId) :
    Lara.Examples.BHLExecution.Reifies (singleWorld n first second name) (singleFinal first second name) :=
  (test_step prior _ _ report dataId name (sampled_reifies n first second)).2

 theorem single_executes (prior : Prior) (n : Int) (first second : Bool) (name : TestId)
    (hn : allowed prior n) :
    executes (context prior) (singleSource name).quote (sampledWorld n first second)
      (singleWorld n first second name) :=
  ⟨trivial, sampled_admitted prior n first second hn, 1, single_steps prior n first second name⟩

 theorem second_step (n : Int) (first second : Bool) :
    Step (context .two)
      (some (.command (Lara.Examples.BHLExecution.Command.quote (.test secondReport aliasId secondId))))
      (singleWorld n first second firstId) none (pairWorld n first second) :=
  (test_step .two _ _ secondReport aliasId secondId (single_reifies .two n first second firstId)).1

 theorem second_executes (n : Int) (first second : Bool) (hn : allowed .two n) :
    executes (context .two)
      (.command (Lara.Examples.BHLExecution.Command.quote (.test secondReport aliasId secondId)))
      (singleWorld n first second firstId) (pairWorld n first second) :=
  ⟨trivial, exec_admitted (single_executes .two n first second firstId hn),
    1, .cons (second_step n first second) (.refl _ _)⟩

 theorem pair_steps (n : Int) (first second : Bool) :
    Steps (context .two) 2 (some pairSource.quote) (sampledWorld n first second) none
      (pairWorld n first second) := by
  have h := (test_step .two _ _ report dataId firstId (sampled_reifies n first second)).1
  exact .cons (.seqFinish h) (.cons (second_step n first second) (.refl _ _))

 theorem pair_executes (n : Int) (first second : Bool) (hn : allowed .two n) :
    executes (context .two) pairSource.quote (sampledWorld n first second) (pairWorld n first second) :=
  ⟨⟨trivial, trivial⟩, sampled_admitted .two n first second hn, 2, pair_steps n first second⟩

 theorem hidden_steps (n : Int) (first second : Bool) :
    Steps (context .two) 2 (some hiddenSource.quote) (sampledWorld n first second) none
      (hiddenWorld n first second) := by
  have h := (test_step .two _ _ report dataId hiddenId (sampled_reifies n first second)).1
  have h₂ := (test_step .two _ _ report dataId firstId (single_reifies .two n first second hiddenId)).1
  exact .cons (.seqFinish h) (.cons h₂ (.refl _ _))

 theorem hidden_executes (n : Int) (first second : Bool) (hn : allowed .two n) :
    executes (context .two) hiddenSource.quote (sampledWorld n first second) (hiddenWorld n first second) :=
  ⟨⟨trivial, trivial⟩, sampled_admitted .two n first second hn, 2, hidden_steps n first second⟩

@[simp] theorem single_report (n : Int) (first second : Bool) (name : TestId) :
    (singleWorld n first second name).current.memory.read report =
      some (Tests.Binary.pvalue first : ℝ) := by
  simp [singleWorld, Lara.Examples.BHLExecution.eventWorld, singleFinal, runTest, initialSnapshot,
    Memory.read, Memory.assemble, Lara.Examples.BHLExecution.Snapshot.memory, dataId, aliasId,
    Lara.Examples.BHLExecution.report]

@[simp] theorem single_data (n : Int) (first second : Bool) (name : TestId) :
    (singleWorld n first second name).current.datasets dataId = first ∧
    (singleWorld n first second name).current.datasets aliasId = second := by
  simp [singleWorld, Lara.Examples.BHLExecution.eventWorld, singleFinal, runTest,
    initialSnapshot, dataId, aliasId]

 theorem pair_ledger (n : Int) (first second : Bool) :
    (pairWorld n first second).current.history = {(first, firstId)} + {(second, secondId)} := by
  simp [pairWorld, singleWorld, Lara.Examples.BHLExecution.eventWorld, pairFinal,
    singleFinal, runTest, initialSnapshot, Lara.Examples.BHLExecution.initialSnapshot, dataId, aliasId]

 theorem hidden_ledger (n : Int) (first second : Bool) :
    (hiddenWorld n first second).current.history = {(first, hiddenId)} + {(first, firstId)} := by
  simp [hiddenWorld, singleWorld, Lara.Examples.BHLExecution.eventWorld, hiddenFinal,
    singleFinal, runTest, initialSnapshot, Lara.Examples.BHLExecution.initialSnapshot, dataId, aliasId]

 theorem pair_reports (n : Int) (first second : Bool) :
    (pairWorld n first second).current.memory.read report = some (Tests.Binary.pvalue first : ℝ) ∧
    (pairWorld n first second).current.memory.read secondReport = some (Tests.Binary.pvalue second : ℝ) ∧
    (pairWorld n first second).current.memory.read oldReport = some ((7 / 11 : ℚ) : ℝ) := by
  simp [pairWorld, singleWorld, Lara.Examples.BHLExecution.eventWorld, pairFinal, singleFinal,
    runTest, initialSnapshot, Lara.Examples.BHLExecution.initialSnapshot,
    Lara.Examples.BHLExecution.Snapshot.memory, Memory.read, Memory.assemble,
    Lara.Examples.BHLExecution.report, secondReport, oldReport, dataId, aliasId]

 theorem hidden_report_unchanged (n : Int) (first second : Bool) :
    (hiddenWorld n first second).current.memory.read report =
      (singleWorld n first second firstId).current.memory.read report := by
  simp [hiddenWorld, singleWorld, Lara.Examples.BHLExecution.eventWorld, hiddenFinal, singleFinal,
    runTest, initialSnapshot, Lara.Examples.BHLExecution.Snapshot.memory, Memory.read,
    Memory.assemble, Lara.Examples.BHLExecution.report, dataId, aliasId]

end
end Lara.Examples.BHLBinaryRuns
