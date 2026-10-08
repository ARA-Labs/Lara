import Lara.BHL.Program

namespace Lara.BHL

variable {D : Type}

namespace ProgramCell

theorem Agrees.refl (cell : ProgramCell) (visible : VisibleState D) :
    cell.Agrees visible visible := by
  cases cell <;> rfl

theorem Agrees.symm {cell : ProgramCell} {left right : VisibleState D}
    (agreement : cell.Agrees left right) : cell.Agrees right left := by
  cases cell <;> exact Eq.symm agreement

theorem Agrees.trans {cell : ProgramCell} {left middle right : VisibleState D}
    (first : cell.Agrees left middle) (second : cell.Agrees middle right) :
    cell.Agrees left right := by
  cases cell <;> exact Eq.trans first second

end ProgramCell

namespace ProgramAgreement

theorem refl (support : List ProgramCell) (visible : VisibleState D) :
    ProgramAgreement support visible visible :=
  fun cell _ => ProgramCell.Agrees.refl cell visible

theorem symm {support : List ProgramCell} {left right : VisibleState D}
    (agreement : ProgramAgreement support left right) : ProgramAgreement support right left :=
  fun cell member => (agreement cell member).symm

theorem trans {support : List ProgramCell} {left middle right : VisibleState D}
    (first : ProgramAgreement support left middle) (second : ProgramAgreement support middle right) :
    ProgramAgreement support left right :=
  fun cell member => (first cell member).trans (second cell member)

@[simp] theorem nil (left right : VisibleState D) : ProgramAgreement [] left right := by
  simp [ProgramAgreement]

@[simp] theorem append_iff {first second : List ProgramCell} {left right : VisibleState D} :
    ProgramAgreement (first ++ second) left right ↔
      ProgramAgreement first left right ∧ ProgramAgreement second left right := by
  simp only [ProgramAgreement, List.mem_append, or_imp, forall_and]

theorem append_left {first second : List ProgramCell} {left right : VisibleState D}
    (agreement : ProgramAgreement (first ++ second) left right) :
    ProgramAgreement first left right := append_iff.mp agreement |>.1

theorem append_right {first second : List ProgramCell} {left right : VisibleState D}
    (agreement : ProgramAgreement (first ++ second) left right) :
    ProgramAgreement second left right := append_iff.mp agreement |>.2

theorem mono {small large : List ProgramCell} {left right : VisibleState D}
    (subset : ∀ cell ∈ small, cell ∈ large) (agreement : ProgramAgreement large left right) :
    ProgramAgreement small left right :=
  fun cell member => agreement cell (subset cell member)

theorem visible_eq {left right : VisibleState D}
    (agreement : ∀ cell : ProgramCell, cell.Agrees left right) : left = right := by
  have memory : left.memory = right.memory := by
    funext sort name
    exact agreement (.value sort name)
  have datasets : left.datasets = right.datasets := by
    funext name
    exact agreement (.dataset name)
  cases left
  cases right
  cases memory
  cases datasets
  rfl

end ProgramAgreement

namespace ProgramFrame

theorem refl (writes : List ProgramCell) (visible : VisibleState D) :
    ProgramFrame writes visible visible := fun cell _ => ProgramCell.Agrees.refl cell visible

theorem symm {writes : List ProgramCell} {left right : VisibleState D}
    (frame : ProgramFrame writes left right) : ProgramFrame writes right left :=
  fun cell outside => (frame cell outside).symm

theorem trans {writes : List ProgramCell} {left middle right : VisibleState D}
    (first : ProgramFrame writes left middle) (second : ProgramFrame writes middle right) :
    ProgramFrame writes left right :=
  fun cell outside => (first cell outside).trans (second cell outside)

theorem agreement {writes support : List ProgramCell} {before after : VisibleState D}
    (frame : ProgramFrame writes before after)
    (disjoint : ∀ cell ∈ support, cell ∉ writes) : ProgramAgreement support before after :=
  fun cell member => frame cell (disjoint cell member)

end ProgramFrame

noncomputable section
variable {Command : Type} [MeasurableSpace D]

mutual
theorem evalProgramExpr_congr (interpretation : AssertionInterpretation D Command)
    (left right : VisibleState D) : (expression : ProgramExpr sort) →
    ProgramAgreement expression.reads left right →
    evalProgramExpr interpretation left expression = evalProgramExpr interpretation right expression
  | .boolean _, _ => rfl
  | .integer _, _ => rfl
  | .rational _, _ => rfl
  | .constant _, _ => rfl
  | .read x, agreement => by
      exact agreement (.value _ x.id) (by simp [ProgramExpr.reads])
  | .apply symbol args, agreement => by
      simp only [evalProgramExpr,
        evalProgramArgs_congr interpretation left right args agreement]
  | .pvalue hypothesis data test population, agreement => by
      simp only [evalProgramExpr,
        evalDatasetExpr_congr interpretation left right data agreement]
  | .realAdd a b, agreement => by
      simp only [evalProgramExpr,
        evalProgramExpr_congr interpretation left right a agreement.append_left,
        evalProgramExpr_congr interpretation left right b agreement.append_right]
  | .realMin a b, agreement => by
      simp only [evalProgramExpr,
        evalProgramExpr_congr interpretation left right a agreement.append_left,
        evalProgramExpr_congr interpretation left right b agreement.append_right]
  | .intAdd a b, agreement => by
      simp only [evalProgramExpr,
        evalProgramExpr_congr interpretation left right a agreement.append_left,
        evalProgramExpr_congr interpretation left right b agreement.append_right]
  | .intSub a b, agreement => by
      simp only [evalProgramExpr,
        evalProgramExpr_congr interpretation left right a agreement.append_left,
        evalProgramExpr_congr interpretation left right b agreement.append_right]
  | .intLess a b, agreement => by
      simp only [evalProgramExpr,
        evalProgramExpr_congr interpretation left right a agreement.append_left,
        evalProgramExpr_congr interpretation left right b agreement.append_right]
  | .booleanNot value, agreement => by
      simp only [evalProgramExpr,
        evalProgramExpr_congr interpretation left right value agreement]

theorem evalProgramArgs_congr (interpretation : AssertionInterpretation D Command)
    (left right : VisibleState D) : (args : ProgramArgs inputs) →
    ProgramAgreement args.reads left right →
    evalProgramArgs interpretation left args = evalProgramArgs interpretation right args
  | .nil, _ => rfl
  | .cons value rest, agreement => by
      simp only [evalProgramArgs,
        evalProgramExpr_congr interpretation left right value agreement.append_left,
        evalProgramArgs_congr interpretation left right rest agreement.append_right]

theorem evalDatasetExpr_congr (interpretation : AssertionInterpretation D Command)
    (left right : VisibleState D) : (expression : DatasetExpr) →
    ProgramAgreement expression.reads left right →
    evalDatasetExpr interpretation left expression = evalDatasetExpr interpretation right expression
  | .constant _, _ => rfl
  | .read name, agreement => by
      exact congrArg some (agreement (.dataset name) (by simp [DatasetExpr.reads]))
  | .apply symbol args, agreement => by
      simp only [evalDatasetExpr,
        evalProgramArgs_congr interpretation left right args agreement]
end

mutual
theorem evalTerm_toProgramExpr (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (view : SemanticView D) :
    (expression : ProgramExpr sort) →
    evalTerm interpretation model env view (expression.toAssertionTerm context) =
      evalProgramExpr interpretation view.visible expression
  | .boolean _ => rfl
  | .integer _ => rfl
  | .rational _ => rfl
  | .constant _ => rfl
  | .read _ => rfl
  | .apply symbol args => by
      simp only [ProgramExpr.toAssertionTerm, evalTerm, evalProgramExpr,
        evalArguments_toProgramArgs interpretation model env view args]
  | .pvalue hypothesis data test population => by
      simp only [ProgramExpr.toAssertionTerm, evalTerm, evalNumericalEvent, evalProgramExpr,
        evalTerm_toDatasetExpr interpretation model env view data]
      cases evalDatasetExpr interpretation view.visible data <;>
        simp [NumericalEvent.tail_probability]
  | .realAdd a b => by
      simp only [ProgramExpr.toAssertionTerm, evalTerm, evalProgramExpr,
        evalTerm_toProgramExpr interpretation model env view a,
        evalTerm_toProgramExpr interpretation model env view b]
  | .realMin a b => by
      simp only [ProgramExpr.toAssertionTerm, evalTerm, evalProgramExpr,
        evalTerm_toProgramExpr interpretation model env view a,
        evalTerm_toProgramExpr interpretation model env view b]
  | .intAdd a b => by
      simp only [ProgramExpr.toAssertionTerm, evalTerm, evalProgramExpr,
        evalTerm_toProgramExpr interpretation model env view a,
        evalTerm_toProgramExpr interpretation model env view b]
  | .intSub a b => by
      simp only [ProgramExpr.toAssertionTerm, evalTerm, evalProgramExpr,
        evalTerm_toProgramExpr interpretation model env view a,
        evalTerm_toProgramExpr interpretation model env view b]
  | .intLess a b => by
      simp only [ProgramExpr.toAssertionTerm, evalTerm, evalProgramExpr,
        evalTerm_toProgramExpr interpretation model env view a,
        evalTerm_toProgramExpr interpretation model env view b]
  | .booleanNot value => by
      simp only [ProgramExpr.toAssertionTerm, evalTerm, evalProgramExpr,
        evalTerm_toProgramExpr interpretation model env view value]

theorem evalArguments_toProgramArgs (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (view : SemanticView D) :
    (args : ProgramArgs inputs) →
    evalArguments interpretation model env view (args.toAssertionArgs context) =
      evalProgramArgs interpretation view.visible args
  | .nil => rfl
  | .cons value rest => by
      simp only [ProgramArgs.toAssertionArgs, evalArguments, evalProgramArgs,
        evalTerm_toProgramExpr interpretation model env view value,
        evalArguments_toProgramArgs interpretation model env view rest]

theorem evalTerm_toDatasetExpr (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (view : SemanticView D) :
    (expression : DatasetExpr) →
    evalTerm interpretation model env view (expression.toAssertionTerm context) =
      evalDatasetExpr interpretation view.visible expression
  | .constant _ => rfl
  | .read _ => rfl
  | .apply symbol args => by
      simp only [DatasetExpr.toAssertionTerm, evalTerm, evalDatasetExpr,
        evalArguments_toProgramArgs interpretation model env view args]
end

/-- The observable projection of a typed observable write does not depend on
which actual hidden memory is used to assemble its input memory. -/
theorem observable_update_assemble_independent (memory : ObservableMemory)
    (hidden otherHidden : HiddenMemory) (x : Variable sort .observable)
    (value : Option (Value sort)) :
    ((Memory.assemble memory hidden).update x value).observable =
      ((Memory.assemble memory otherHidden).update x value).observable := by
  funext target name
  by_cases sameSort : sort = target
  · by_cases sameName : x.id = name
    · simp [Memory.observable, Memory.update, sameSort, sameName]
    · simp [Memory.observable, Memory.update, Memory.assemble, sameSort, sameName]
  · simp [Memory.observable, Memory.update, Memory.assemble, sameSort]

namespace VisibleWrite

omit [MeasurableSpace D] in
theorem apply_value_visible (view : SemanticView D) (x : Variable sort .observable)
    (value : Value sort) :
    (.value x value : VisibleWrite D).apply view.visible = (writeViewValue view x value).visible := by
  change
    ({ memory := ((Memory.assemble view.visible.memory (fun _ _ => none)).update x
        (some value)).observable, datasets := view.visible.datasets } : VisibleState D) =
      { memory := ((Memory.assemble view.visible.memory view.hidden).update x
        (some value)).observable, datasets := view.visible.datasets }
  rw [observable_update_assemble_independent view.visible.memory (fun _ _ => none) view.hidden]

omit [MeasurableSpace D] in
@[simp] theorem apply_value_self (visible : VisibleState D) (x : Variable sort .observable)
    (value : Value sort) :
    ((.value x value : VisibleWrite D).apply visible).memory sort x.id = some value := by
  exact Memory.read_update_self (Memory.assemble visible.memory (fun _ _ => none)) x (some value)

omit [MeasurableSpace D] in
@[simp] theorem apply_value_datasets (visible : VisibleState D) (x : Variable sort .observable)
    (value : Value sort) :
    ((.value x value : VisibleWrite D).apply visible).datasets = visible.datasets := rfl

omit [MeasurableSpace D] in
@[simp] theorem apply_dataset_memory (visible : VisibleState D) (name : DatasetId) (data : D) :
    ((.dataset name data : VisibleWrite D).apply visible).memory = visible.memory := rfl

omit [MeasurableSpace D] in
@[simp] theorem apply_dataset_self (visible : VisibleState D) (name : DatasetId) (data : D) :
    ((.dataset name data : VisibleWrite D).apply visible).datasets name = data := by
  simp [VisibleWrite.apply]

omit [MeasurableSpace D] in
theorem apply_frame (payload : VisibleWrite D) (visible : VisibleState D) :
    ProgramFrame payload.cells visible (payload.apply visible) := by
  intro cell outside
  cases payload with
  | unchanged => exact ProgramCell.Agrees.refl cell visible
  | @value sort x value =>
      cases cell with
      | value target name =>
          by_cases sameSort : sort = target
          · subst target
            have differentName : x.id ≠ name := by
              intro equal
              apply outside
              simp [VisibleWrite.cells, equal]
            exact (Memory.read_update_other
              (Memory.assemble visible.memory (fun _ _ => none)) x (some value)
              (⟨name⟩ : Variable sort .observable) (Or.inr (Or.inr differentName))).symm
          · exact (Memory.read_update_other
              (Memory.assemble visible.memory (fun _ _ => none)) x (some value)
              (⟨name⟩ : Variable target .observable) (Or.inl sameSort)).symm
      | dataset name => rfl
  | dataset name data =>
      cases cell with
      | value sort cellName => rfl
      | dataset other =>
          have differentName : other ≠ name := by
            intro equal
            apply outside
            simp [VisibleWrite.cells, equal]
          simp [ProgramCell.Agrees, VisibleWrite.apply, differentName]

omit [MeasurableSpace D] in
theorem apply_agrees (payload : VisibleWrite D) (cell : ProgramCell)
    {left right : VisibleState D} (agreement : cell.Agrees left right) :
    cell.Agrees (payload.apply left) (payload.apply right) := by
  cases payload with
  | unchanged => exact agreement
  | @value sort x value =>
      cases cell with
      | value target name =>
          by_cases sameSort : sort = target
          · by_cases sameName : x.id = name
            · simp [ProgramCell.Agrees, VisibleWrite.apply, Memory.observable,
                Memory.update, sameSort, sameName]
            · simpa [ProgramCell.Agrees, VisibleWrite.apply, Memory.observable,
                Memory.update, Memory.assemble, sameSort, sameName] using agreement
          · simpa [ProgramCell.Agrees, VisibleWrite.apply, Memory.observable,
              Memory.update, Memory.assemble, sameSort] using agreement
      | dataset name => exact agreement
  | dataset name data =>
      cases cell with
      | value sort cellName => exact agreement
      | dataset other =>
          by_cases sameName : other = name
          · simp [ProgramCell.Agrees, VisibleWrite.apply, sameName]
          · simpa [ProgramCell.Agrees, VisibleWrite.apply, sameName] using agreement

omit [MeasurableSpace D] in
theorem apply_agreement (payload : VisibleWrite D) {support : List ProgramCell}
    {left right : VisibleState D} (agreement : ProgramAgreement support left right) :
    ProgramAgreement support (payload.apply left) (payload.apply right) :=
  fun cell member => payload.apply_agrees cell (agreement cell member)

end VisibleWrite

/-- The complete optional semantic view, not just its visible endpoint, agrees
with the independent evaluator of an expanded primitive effect. -/
theorem evalPrimitive_viewTerm (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (view : SemanticView D)
    (primitive : Primitive) :
    evalTerm interpretation model env view (primitive.viewTerm context) =
      (primitiveEffect interpretation primitive view.visible).map (fun out =>
        {view with visible := out.1, history := view.history + out.2}) := by
  cases primitive with
  | skip => simp [Primitive.viewTerm, evalTerm, primitiveEffect, evalPrimitive, VisibleWrite.apply]
  | assign x rhs =>
      simp only [Primitive.viewTerm, eval_assignmentView,
        evalTerm_toProgramExpr, primitiveEffect, evalPrimitive]
      cases evalProgramExpr interpretation view.visible rhs with
      | none => rfl
      | some value =>
          simp only [Option.map_some, VisibleWrite.apply_value_visible, add_zero]
          rfl
  | assignDataset name rhs =>
      simp only [Primitive.viewTerm, eval_datasetAssignmentView,
        evalTerm_toDatasetExpr, primitiveEffect, evalPrimitive]
      cases evalDatasetExpr interpretation view.visible rhs <;>
        simp [VisibleWrite.apply, writeViewDataset]
  | test result hypothesis data test population =>
      simp only [Primitive.viewTerm, eval_testAssignmentView,
        evalTerm_toDatasetExpr, primitiveEffect, evalPrimitive]
      cases evalDatasetExpr interpretation view.visible data with
      | none => rfl
      | some d =>
          simp only [Option.map_some, VisibleWrite.apply_value_visible]
          rfl

theorem evalPrimitive_congr (interpretation : AssertionInterpretation D Command)
    (left right : VisibleState D) (primitive : Primitive)
    (agreement : ProgramAgreement primitive.reads left right) :
    evalPrimitive interpretation left primitive = evalPrimitive interpretation right primitive := by
  cases primitive with
  | skip => rfl
  | assign x rhs =>
      simp only [evalPrimitive, evalProgramExpr_congr interpretation left right rhs agreement]
  | assignDataset name rhs =>
      simp only [evalPrimitive, evalDatasetExpr_congr interpretation left right rhs agreement]
  | test result hypothesis data test population =>
      simp only [evalPrimitive, evalDatasetExpr_congr interpretation left right data agreement]

theorem evalPrimitive_cells (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) (primitive : Primitive) (payload : VisibleWrite D) (delta : History D)
    (enabled : evalPrimitive interpretation visible primitive = some (payload, delta)) :
    payload.cells = primitive.writes := by
  cases primitive with
  | skip =>
      have equal : (VisibleWrite.unchanged, (0 : History D)) = (payload, delta) :=
        Option.some.inj enabled
      cases equal
      rfl
  | assign x rhs =>
      cases evaluated : evalProgramExpr interpretation visible rhs with
      | none => simp [evalPrimitive, evaluated] at enabled
      | some value =>
          have equal : (VisibleWrite.value x value, (0 : History D)) = (payload, delta) := by
            simpa [evalPrimitive, evaluated] using enabled
          cases equal
          rfl
  | assignDataset name rhs =>
      cases evaluated : evalDatasetExpr interpretation visible rhs with
      | none => simp [evalPrimitive, evaluated] at enabled
      | some data =>
          have equal : (VisibleWrite.dataset name data, (0 : History D)) = (payload, delta) := by
            simpa [evalPrimitive, evaluated] using enabled
          cases equal
          rfl
  | test result hypothesis data test population =>
      cases evaluated : evalDatasetExpr interpretation visible data with
      | none => simp [evalPrimitive, evaluated] at enabled
      | some d =>
          have equal : (VisibleWrite.value result
              ((interpretation.tests hypothesis test).tailProbability d), ({(d, test)} : History D)) =
              (payload, delta) := by
            simpa [evalPrimitive, evaluated] using enabled
          cases equal
          rfl

theorem primitiveEffect_frame (interpretation : AssertionInterpretation D Command)
    (primitive : Primitive) (before after : VisibleState D) (delta : History D)
    (enabled : primitiveEffect interpretation primitive before = some (after, delta)) :
    ProgramFrame primitive.writes before after := by
  cases evaluated : evalPrimitive interpretation before primitive with
  | none => simp [primitiveEffect, evaluated] at enabled
  | some out =>
      rcases out with ⟨payload, history⟩
      have equal : (payload.apply before, history) = (after, delta) := by
        simpa [primitiveEffect, evaluated] using enabled
      have footprint := evalPrimitive_cells interpretation before primitive payload history evaluated
      rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
      rw [← footprint]
      exact payload.apply_frame before

@[simp] theorem evalPrimitive_skip (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) :
    evalPrimitive interpretation visible .skip = some (.unchanged, 0) := rfl

@[simp] theorem evalPrimitive_assign (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) (x : Variable sort .observable) (rhs : ProgramExpr sort) :
    evalPrimitive interpretation visible (.assign x rhs) =
      (evalProgramExpr interpretation visible rhs).map (fun value => (.value x value, 0)) := rfl

@[simp] theorem evalPrimitive_assignDataset (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) (name : DatasetId) (rhs : DatasetExpr) :
    evalPrimitive interpretation visible (.assignDataset name rhs) =
      (evalDatasetExpr interpretation visible rhs).map (fun data => (.dataset name data, 0)) := rfl

@[simp] theorem evalPrimitive_test (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) (result : Variable .real .observable) (hypothesis : HypothesisId)
    (data : DatasetExpr) (test : TestId) (population : PopulationId) :
    evalPrimitive interpretation visible (.test result hypothesis data test population) =
      (evalDatasetExpr interpretation visible data).map (fun d =>
        (.value result ((interpretation.tests hypothesis test).tailProbability d), {(d, test)})) := rfl

theorem evalPrimitive_assign_enabled (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) (x : Variable sort .observable) (rhs : ProgramExpr sort)
    (value : Value sort) (evaluated : evalProgramExpr interpretation visible rhs = some value) :
    evalPrimitive interpretation visible (.assign x rhs) = some (.value x value, 0) := by
  simp only [evalPrimitive_assign, evaluated, Option.map_some]

theorem evalPrimitive_assignDataset_enabled (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) (name : DatasetId) (rhs : DatasetExpr) (data : D)
    (evaluated : evalDatasetExpr interpretation visible rhs = some data) :
    evalPrimitive interpretation visible (.assignDataset name rhs) = some (.dataset name data, 0) := by
  simp only [evalPrimitive_assignDataset, evaluated, Option.map_some]

theorem evalPrimitive_test_enabled (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) (result : Variable .real .observable) (hypothesis : HypothesisId)
    (data : DatasetExpr) (test : TestId) (population : PopulationId) (d : D)
    (evaluated : evalDatasetExpr interpretation visible data = some d) :
    evalPrimitive interpretation visible (.test result hypothesis data test population) =
      some (.value result ((interpretation.tests hypothesis test).tailProbability d), {(d, test)}) := by
  simp only [evalPrimitive_test, evaluated, Option.map_some]

/-- A pure p-value assignment writes its report but does not record a test. -/
theorem evalPrimitive_assign_pvalue (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) (result : Variable .real .observable) (hypothesis : HypothesisId)
    (data : DatasetExpr) (test : TestId) (population : PopulationId) :
    evalPrimitive interpretation visible (.assign result (.pvalue hypothesis data test population)) =
      (evalDatasetExpr interpretation visible data).map (fun d =>
        (.value result ((interpretation.tests hypothesis test).tailProbability d), 0)) := by
  cases evaluated : evalDatasetExpr interpretation visible data <;>
    simp [evalPrimitive, evalProgramExpr, evaluated]

@[simp] theorem evalPrimitive_assign_none_iff (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) (x : Variable sort .observable) (rhs : ProgramExpr sort) :
    evalPrimitive interpretation visible (.assign x rhs) = none ↔
      evalProgramExpr interpretation visible rhs = none := by
  cases evaluated : evalProgramExpr interpretation visible rhs <;>
    simp [evalPrimitive, evaluated]

@[simp] theorem evalPrimitive_assignDataset_none_iff
    (interpretation : AssertionInterpretation D Command) (visible : VisibleState D)
    (name : DatasetId) (rhs : DatasetExpr) :
    evalPrimitive interpretation visible (.assignDataset name rhs) = none ↔
      evalDatasetExpr interpretation visible rhs = none := by
  cases evaluated : evalDatasetExpr interpretation visible rhs <;>
    simp [evalPrimitive, evaluated]

@[simp] theorem evalPrimitive_test_none_iff (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) (result : Variable .real .observable) (hypothesis : HypothesisId)
    (data : DatasetExpr) (test : TestId) (population : PopulationId) :
    evalPrimitive interpretation visible (.test result hypothesis data test population) = none ↔
      evalDatasetExpr interpretation visible data = none := by
  cases evaluated : evalDatasetExpr interpretation visible data <;>
    simp [evalPrimitive, evaluated]

@[simp] theorem primitiveEffect_skip (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) : primitiveEffect interpretation .skip visible = some (visible, 0) := rfl

@[simp] theorem primitiveEffect_assign (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) (x : Variable sort .observable) (rhs : ProgramExpr sort) :
    primitiveEffect interpretation (.assign x rhs) visible =
      (evalProgramExpr interpretation visible rhs).map (fun value =>
        ((VisibleWrite.value x value).apply visible, 0)) := by
  cases evaluated : evalProgramExpr interpretation visible rhs <;>
    simp [primitiveEffect, evalPrimitive, evaluated]

@[simp] theorem primitiveEffect_assignDataset (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) (name : DatasetId) (rhs : DatasetExpr) :
    primitiveEffect interpretation (.assignDataset name rhs) visible =
      (evalDatasetExpr interpretation visible rhs).map (fun data =>
        ((VisibleWrite.dataset name data).apply visible, 0)) := by
  cases evaluated : evalDatasetExpr interpretation visible rhs <;>
    simp [primitiveEffect, evalPrimitive, evaluated]

@[simp] theorem primitiveEffect_test (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) (result : Variable .real .observable) (hypothesis : HypothesisId)
    (data : DatasetExpr) (test : TestId) (population : PopulationId) :
    primitiveEffect interpretation (.test result hypothesis data test population) visible =
      (evalDatasetExpr interpretation visible data).map (fun d =>
        ((VisibleWrite.value result
          ((interpretation.tests hypothesis test).tailProbability d)).apply visible, {(d, test)})) := by
  cases evaluated : evalDatasetExpr interpretation visible data <;>
    simp [primitiveEffect, evalPrimitive, evaluated]

@[simp] theorem primitiveEffect_none_iff (interpretation : AssertionInterpretation D Command)
    (primitive : Primitive) (visible : VisibleState D) :
    primitiveEffect interpretation primitive visible = none ↔
      evalPrimitive interpretation visible primitive = none := by
  cases evaluated : evalPrimitive interpretation visible primitive <;>
    simp [primitiveEffect, evaluated]

theorem primitiveEffect_agreement (interpretation : AssertionInterpretation D Command)
    (primitive : Primitive) {left right leftAfter rightAfter : VisibleState D}
    {leftDelta rightDelta : History D} {support : List ProgramCell}
    (reads : ProgramAgreement primitive.reads left right)
    (agreement : ProgramAgreement support left right)
    (leftEnabled : primitiveEffect interpretation primitive left = some (leftAfter, leftDelta))
    (rightEnabled : primitiveEffect interpretation primitive right = some (rightAfter, rightDelta)) :
    ProgramAgreement support leftAfter rightAfter ∧ leftDelta = rightDelta := by
  have congruence := evalPrimitive_congr interpretation left right primitive reads
  cases evaluated : evalPrimitive interpretation left primitive with
  | none => simp [primitiveEffect, evaluated] at leftEnabled
  | some out =>
      rcases out with ⟨payload, delta⟩
      have evaluatedRight : evalPrimitive interpretation right primitive = some (payload, delta) :=
        congruence.symm.trans evaluated
      have equalLeft : (payload.apply left, delta) = (leftAfter, leftDelta) := by
        simpa [primitiveEffect, evaluated] using leftEnabled
      have equalRight : (payload.apply right, delta) = (rightAfter, rightDelta) := by
        simpa [primitiveEffect, evaluatedRight] using rightEnabled
      cases equalLeft
      cases equalRight
      exact ⟨payload.apply_agreement agreement, rfl⟩

theorem evalPrimitive_viewTerm_enabled (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (view : SemanticView D)
    (primitive : Primitive) (visible : VisibleState D) (delta : History D)
    (enabled : primitiveEffect interpretation primitive view.visible = some (visible, delta)) :
    evalTerm interpretation model env view (primitive.viewTerm context) =
      some {view with visible := visible, history := view.history + delta} := by
  rw [evalPrimitive_viewTerm, enabled]
  rfl

theorem primitive_viewTerm_preserves_information
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (before after : SemanticView D) (primitive : Primitive)
    (evaluated : evalTerm interpretation model env before (primitive.viewTerm context) = some after) :
    after.hidden = before.hidden ∧ after.compatible = before.compatible ∧
      after.provenance = before.provenance := by
  rw [evalPrimitive_viewTerm] at evaluated
  cases effect : primitiveEffect interpretation primitive before.visible with
  | none => simp [effect] at evaluated
  | some out =>
      have equal : {before with visible := out.1, history := before.history + out.2} = after := by
        simpa [effect] using evaluated
      cases equal
      exact ⟨rfl, rfl, rfl⟩

namespace ProgramContext

@[simp] theorem ofRelations_interpretation (interpretation : AssertionInterpretation D Primitive)
    (initial : HiddenMemory → VisibleState D → Prop)
    (sampling : HiddenMemory → VisibleState D → VisibleState D → D → PopulationId → Prop)
    (inhabited : ∃ hidden visible, initial hidden visible) :
    (ofRelations interpretation initial sampling inhabited).interpretation = interpretation := rfl

@[simp] theorem ofRelations_initial (interpretation : AssertionInterpretation D Primitive)
    (initial : HiddenMemory → VisibleState D → Prop)
    (sampling : HiddenMemory → VisibleState D → VisibleState D → D → PopulationId → Prop)
    (inhabited : ∃ hidden visible, initial hidden visible) :
    (ofRelations interpretation initial sampling inhabited).model.dynamics.initial = initial := rfl

@[simp] theorem ofRelations_sampling (interpretation : AssertionInterpretation D Primitive)
    (initial : HiddenMemory → VisibleState D → Prop)
    (sampling : HiddenMemory → VisibleState D → VisibleState D → D → PopulationId → Prop)
    (inhabited : ∃ hidden visible, initial hidden visible) :
    (ofRelations interpretation initial sampling inhabited).model.dynamics.sampling = sampling := rfl

@[simp] theorem ofRelations_command (interpretation : AssertionInterpretation D Primitive)
    (initial : HiddenMemory → VisibleState D → Prop)
    (sampling : HiddenMemory → VisibleState D → VisibleState D → D → PopulationId → Prop)
    (inhabited : ∃ hidden visible, initial hidden visible) (primitive : Primitive)
    (visible : VisibleState D) :
    (ofRelations interpretation initial sampling inhabited).model.dynamics.command primitive visible =
      primitiveEffect interpretation primitive visible := rfl

theorem ofRelations_binding (interpretation : AssertionInterpretation D Primitive)
    (initial : HiddenMemory → VisibleState D → Prop)
    (sampling : HiddenMemory → VisibleState D → VisibleState D → D → PopulationId → Prop)
    (inhabited : ∃ hidden visible, initial hidden visible) :
    ProgramModelBinding interpretation (ofRelations interpretation initial sampling inhabited).model :=
  fun _ _ => rfl

theorem ofRelations_has_world (interpretation : AssertionInterpretation D Primitive)
    (initial : HiddenMemory → VisibleState D → Prop)
    (sampling : HiddenMemory → VisibleState D → VisibleState D → D → PopulationId → Prop)
    (inhabited : ∃ hidden visible, initial hidden visible) :
    ∃ world, world ∈ (ofRelations interpretation initial sampling inhabited).model.worlds :=
  model_has_world _

theorem ofRelations_validWorld_nonempty (interpretation : AssertionInterpretation D Primitive)
    (initial : HiddenMemory → VisibleState D → Prop)
    (sampling : HiddenMemory → VisibleState D → VisibleState D → D → PopulationId → Prop)
    (inhabited : ∃ hidden visible, initial hidden visible) :
    Nonempty (ofRelations interpretation initial sampling inhabited).model.ValidWorld :=
  Model.validWorld_nonempty _

end ProgramContext

@[simp] theorem noninterferingCheck_iff (left right : Program) :
    noninterferingCheck left right = true ↔ Noninterfering left right := by
  simp only [noninterferingCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Noninterfering]

@[simp] theorem Program.wellFormedCheck_iff (program : Program) :
    program.wellFormedCheck = true ↔ program.WellFormed := by
  induction program with
  | command primitive => simp [Program.wellFormedCheck, Program.WellFormed]
  | seq left right leftIH rightIH =>
      simp [Program.wellFormedCheck, Program.WellFormed, leftIH, rightIH]
  | ite guard left right leftIH rightIH =>
      simp [Program.wellFormedCheck, Program.WellFormed, leftIH, rightIH]
  | loop guard body bodyIH =>
      simp [Program.wellFormedCheck, Program.WellFormed, bodyIH]
  | par left right leftIH rightIH =>
      simp [Program.wellFormedCheck, Program.WellFormed, leftIH, rightIH, and_assoc]

namespace Noninterfering

theorem symm {left right : Program} (noninterfering : Noninterfering left right) :
    Noninterfering right left := ⟨noninterfering.2, noninterfering.1⟩

theorem mono_left {small large right : Program} (noninterfering : Noninterfering large right)
    (writes : ∀ cell ∈ small.writes, cell ∈ large.writes)
    (used : ∀ cell ∈ small.used, cell ∈ large.used) : Noninterfering small right := by
  constructor
  · intro cell member
    exact noninterfering.1 cell (writes cell member)
  · intro cell member smallMember
    exact noninterfering.2 cell member (used cell smallMember)

theorem mono_right {left small large : Program} (noninterfering : Noninterfering left large)
    (writes : ∀ cell ∈ small.writes, cell ∈ large.writes)
    (used : ∀ cell ∈ small.used, cell ∈ large.used) : Noninterfering left small :=
  (noninterfering.symm.mono_left writes used).symm

theorem mono {smallLeft largeLeft smallRight largeRight : Program}
    (noninterfering : Noninterfering largeLeft largeRight)
    (leftWrites : ∀ cell ∈ smallLeft.writes, cell ∈ largeLeft.writes)
    (leftUsed : ∀ cell ∈ smallLeft.used, cell ∈ largeLeft.used)
    (rightWrites : ∀ cell ∈ smallRight.writes, cell ∈ largeRight.writes)
    (rightUsed : ∀ cell ∈ smallRight.used, cell ∈ largeRight.used) :
    Noninterfering smallLeft smallRight :=
  (noninterfering.mono_left leftWrites leftUsed).mono_right rightWrites rightUsed

theorem writes_not_reads {left right : Program} (noninterfering : Noninterfering left right)
    (cell : ProgramCell) (written : cell ∈ left.writes) : cell ∉ right.reads := by
  intro read
  exact noninterfering.1 cell written (List.mem_append_left right.writes read)

theorem writes_not_writes {left right : Program} (noninterfering : Noninterfering left right)
    (cell : ProgramCell) (written : cell ∈ left.writes) : cell ∉ right.writes := by
  intro otherWritten
  exact noninterfering.1 cell written (List.mem_append_right right.reads otherWritten)

theorem seq_left {left middle right : Program}
    (noninterfering : Noninterfering (.seq left middle) right) : Noninterfering left right := by
  apply noninterfering.mono_left
  · intro cell member
    exact List.mem_append_left middle.writes member
  · intro cell member
    rcases List.mem_append.mp member with read | written
    · exact List.mem_append_left _ (List.mem_append_left _ read)
    · exact List.mem_append_right _ (List.mem_append_left _ written)

theorem seq_right {left middle right : Program}
    (noninterfering : Noninterfering (.seq left middle) right) : Noninterfering middle right := by
  apply noninterfering.mono_left
  · intro cell member
    exact List.mem_append_right left.writes member
  · intro cell member
    rcases List.mem_append.mp member with read | written
    · exact List.mem_append_left _ (List.mem_append_right _ read)
    · exact List.mem_append_right _ (List.mem_append_right _ written)

theorem par_left {left middle right : Program}
    (noninterfering : Noninterfering (.par left middle) right) : Noninterfering left right := by
  apply noninterfering.mono_left
  · intro cell member
    exact List.mem_append_left middle.writes member
  · intro cell member
    rcases List.mem_append.mp member with read | written
    · exact List.mem_append_left _ (List.mem_append_left _ read)
    · exact List.mem_append_right _ (List.mem_append_left _ written)

theorem par_right {left middle right : Program}
    (noninterfering : Noninterfering (.par left middle) right) : Noninterfering middle right := by
  apply noninterfering.mono_left
  · intro cell member
    exact List.mem_append_right left.writes member
  · intro cell member
    rcases List.mem_append.mp member with read | written
    · exact List.mem_append_left _ (List.mem_append_right _ read)
    · exact List.mem_append_right _ (List.mem_append_right _ written)

theorem ite_left {guard : ProgramExpr .boolean} {left middle right : Program}
    (noninterfering : Noninterfering (.ite guard left middle) right) : Noninterfering left right := by
  apply noninterfering.mono_left
  · intro cell member
    exact List.mem_append_left middle.writes member
  · intro cell member
    rcases List.mem_append.mp member with read | written
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ read))
    · exact List.mem_append_right _ (List.mem_append_left _ written)

theorem ite_right {guard : ProgramExpr .boolean} {left middle right : Program}
    (noninterfering : Noninterfering (.ite guard left middle) right) : Noninterfering middle right := by
  apply noninterfering.mono_left
  · intro cell member
    exact List.mem_append_right left.writes member
  · intro cell member
    rcases List.mem_append.mp member with read | written
    · exact List.mem_append_left _ (List.mem_append_right _ read)
    · exact List.mem_append_right _ (List.mem_append_right _ written)

theorem loop_body {guard : ProgramExpr .boolean} {body right : Program}
    (noninterfering : Noninterfering (.loop guard body) right) : Noninterfering body right := by
  apply noninterfering.mono_left
  · exact fun _ member => member
  · intro cell member
    rcases List.mem_append.mp member with read | written
    · exact List.mem_append_left _ (List.mem_append_right _ read)
    · exact List.mem_append_right _ written

end Noninterfering

end
end Lara.BHL
