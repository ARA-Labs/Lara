import Lara.BHL.Dependencies
import Lara.BHL.ExecutionLaws
import Lara.BHL.ProgramLaws

namespace Lara.BHL

noncomputable section

variable {D Command : Type} [MeasurableSpace D]

/-- Delay the view-index constraint until after eliminating the term, so the
    computed index of a ghost constructor can be ruled out by its ghost sort. -/
private theorem viewTerm_cases {Γ : List GhostSort}
    (P : AssertionTerm Γ .view → Prop)
    (hAmbient : P .ambient)
    (hCurrentView : ∀ world, P (.currentView world))
    (hMakeView : ∀ visible history hidden compatible provenance,
      P (.makeView visible history hidden compatible provenance))
    (hWriteValue : ∀ {sort : ValueSort} target (x : Variable sort .observable) rhs,
      P (.writeValue target x rhs))
    (hWriteDataset : ∀ target name rhs, P (.writeDataset target name rhs))
    (hAddHistory : ∀ target history, P (.addHistory target history))
    (target : AssertionTerm Γ .view) : P target := by
  have general : ∀ (sort : TermSort) (term : AssertionTerm Γ sort)
      (equal : sort = .view), P (equal ▸ term) := by
    intro sort term equal
    cases term <;> try cases equal
    case ghost =>
      rename_i ghostSort ghost
      cases ghostSort <;> cases equal
    case ambient => exact hAmbient
    case currentView => exact hCurrentView _
    case makeView => exact hMakeView _ _ _ _ _
    case writeValue => exact hWriteValue _ _ _
    case writeDataset => exact hWriteDataset _ _ _
    case addHistory => exact hAddHistory _ _
  exact general .view target rfl

private theorem readSupport_valueRead_other (target : AssertionTerm Γ .view)
    (x : Variable sort visibility) (different : target ≠ .ambient) :
    (AssertionTerm.valueRead target x).readSupport = target.readSupport := by
  revert different
  refine viewTerm_cases
    (fun target => target ≠ .ambient →
      (AssertionTerm.valueRead target x).readSupport = target.readSupport)
    ?_ ?_ ?_ ?_ ?_ ?_ target
  · intro impossible
    exact (impossible rfl).elim
  all_goals intros; rfl

private theorem readSupport_datasetRead_other (target : AssertionTerm Γ .view)
    (name : DatasetId) (different : target ≠ .ambient) :
    (AssertionTerm.datasetRead target name).readSupport = target.readSupport := by
  revert different
  refine viewTerm_cases
    (fun target => target ≠ .ambient →
      (AssertionTerm.datasetRead target name).readSupport = target.readSupport)
    ?_ ?_ ?_ ?_ ?_ ?_ target
  · intro impossible
    exact (impossible rfl).elim
  all_goals intros; rfl

private theorem readSupport_visibleOf_other (target : AssertionTerm Γ .view)
    (different : target ≠ .ambient) :
    (AssertionTerm.visibleOf target).readSupport = target.readSupport := by
  revert different
  refine viewTerm_cases
    (fun target => target ≠ .ambient →
      (AssertionTerm.visibleOf target).readSupport = target.readSupport)
    ?_ ?_ ?_ ?_ ?_ ?_ target
  · intro impossible
    exact (impossible rfl).elim
  all_goals intros; rfl

private theorem readSupport_hiddenOf_other (target : AssertionTerm Γ .view)
    (different : target ≠ .ambient) :
    (AssertionTerm.hiddenOf target).readSupport = target.readSupport := by
  revert different
  refine viewTerm_cases
    (fun target => target ≠ .ambient →
      (AssertionTerm.hiddenOf target).readSupport = target.readSupport)
    ?_ ?_ ?_ ?_ ?_ ?_ target
  · intro impossible
    exact (impossible rfl).elim
  all_goals intros; rfl

private theorem readSupport_historyOf_other (target : AssertionTerm Γ .view)
    (different : target ≠ .ambient) :
    (AssertionTerm.historyOf target).readSupport = target.readSupport := by
  revert different
  refine viewTerm_cases
    (fun target => target ≠ .ambient →
      (AssertionTerm.historyOf target).readSupport = target.readSupport)
    ?_ ?_ ?_ ?_ ?_ ?_ target
  · intro impossible
    exact (impossible rfl).elim
  all_goals intros; rfl

private theorem readSupport_provenanceOf_other (target : AssertionTerm Γ .view)
    (different : target ≠ .ambient) :
    (AssertionTerm.provenanceOf target).readSupport = target.readSupport := by
  revert different
  refine viewTerm_cases
    (fun target => target ≠ .ambient →
      (AssertionTerm.provenanceOf target).readSupport = target.readSupport)
    ?_ ?_ ?_ ?_ ?_ ?_ target
  · intro impossible
    exact (impossible rfl).elim
  all_goals intros; rfl

private theorem readSupport_compatibleOf_other (target : AssertionTerm Γ .view)
    (different : target ≠ .ambient) :
    (AssertionTerm.compatibleOf target).readSupport = target.readSupport := by
  revert different
  refine viewTerm_cases
    (fun target => target ≠ .ambient →
      (AssertionTerm.compatibleOf target).readSupport = target.readSupport)
    ?_ ?_ ?_ ?_ ?_ ?_ target
  · intro impossible
    exact (impossible rfl).elim
  all_goals intros; rfl

mutual
/-- Full Option denotation congruence: no fragment restriction and no numerical
    definedness assumption. Coupling lookup sees exactly the same child laws. -/
theorem evalTerm_support_congr (I : AssertionInterpretation D Command)
    (M : Model D Command) (env : GhostEnv D Command Γ) {left right : SemanticView D} :
    (term : AssertionTerm Γ sort) → SupportAgreement term.readSupport left right →
    evalTerm I M env left term = evalTerm I M env right term
  | .ghost _, _ => rfl
  | .boolean _, _ => rfl
  | .integer _, _ => rfl
  | .rational _, _ => rfl
  | .apply f args, agreement => by
      simp only [evalTerm, evalArguments_support_congr I M env args agreement]
  | .datasetApply f args, agreement => by
      simp only [evalTerm, evalArguments_support_congr I M env args agreement]
  | .ambient, agreement => congrArg some agreement.view_eq
  | .currentView world, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env world agreement]
  | .currentState world, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env world agreement]
  | .worldTrace world, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env world agreement]
  | .appendWorld world trace, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env world agreement.append_left,
        evalTerm_support_congr I M env trace agreement.append_right]
  | .traceEmpty, _ => rfl
  | .traceSingleton state, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env state agreement]
  | .traceAppend a b, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env a agreement.append_left,
        evalTerm_support_congr I M env b agreement.append_right]
  | .traceLength trace, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env trace agreement]
  | .traceTake trace index, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env trace agreement.append_left,
        evalTerm_support_congr I M env index agreement.append_right]
  | .traceIndex trace index, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env trace agreement.append_left,
        evalTerm_support_congr I M env index agreement.append_right]
  | .valueRead target x, agreement => by
      by_cases equal : target = .ambient
      · subst target
        exact agreement (.variable _ _ x) (by simp [AssertionTerm.readSupport])
      · rw [readSupport_valueRead_other target x equal] at agreement
        simp only [evalTerm, evalTerm_support_congr I M env target agreement]
  | .datasetRead target name, agreement => by
      by_cases equal : target = .ambient
      · subst target
        exact congrArg some (agreement (.dataset name) (by simp [AssertionTerm.readSupport]))
      · rw [readSupport_datasetRead_other target name equal] at agreement
        simp only [evalTerm, evalTerm_support_congr I M env target agreement]
  | .visibleOf target, agreement => by
      by_cases equal : target = .ambient
      · subst target
        exact congrArg some agreement.visible_eq
      · rw [readSupport_visibleOf_other target equal] at agreement
        simp only [evalTerm, evalTerm_support_congr I M env target agreement]
  | .hiddenOf target, agreement => by
      by_cases equal : target = .ambient
      · subst target
        exact congrArg some (agreement .hiddenValues (by simp [AssertionTerm.readSupport]))
      · rw [readSupport_hiddenOf_other target equal] at agreement
        simp only [evalTerm, evalTerm_support_congr I M env target agreement]
  | .historyOf target, agreement => by
      by_cases equal : target = .ambient
      · subst target
        exact congrArg some (agreement .history (by simp [AssertionTerm.readSupport]))
      · rw [readSupport_historyOf_other target equal] at agreement
        simp only [evalTerm, evalTerm_support_congr I M env target agreement]
  | .provenanceOf target, agreement => by
      by_cases equal : target = .ambient
      · subst target
        exact congrArg some (agreement .provenance (by simp [AssertionTerm.readSupport]))
      · rw [readSupport_provenanceOf_other target equal] at agreement
        simp only [evalTerm, evalTerm_support_congr I M env target agreement]
  | .compatibleOf target, agreement => by
      by_cases equal : target = .ambient
      · subst target
        exact congrArg some (agreement .compatible (by simp [AssertionTerm.readSupport]))
      · rw [readSupport_compatibleOf_other target equal] at agreement
        simp only [evalTerm, evalTerm_support_congr I M env target agreement]
  | .makeView visible history hidden compatible provenance, agreement => by
      have h1 := agreement.append_left
      have h2 := h1.append_left
      have h3 := h2.append_left
      simp only [evalTerm, evalTerm_support_congr I M env visible h3.append_left,
        evalTerm_support_congr I M env history h3.append_right,
        evalTerm_support_congr I M env hidden h2.append_right,
        evalTerm_support_congr I M env compatible h1.append_right,
        evalTerm_support_congr I M env provenance agreement.append_right]
  | .writeValue target x rhs, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env target agreement.append_left,
        evalTerm_support_congr I M env rhs agreement.append_right]
  | .writeDataset target name rhs, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env target agreement.append_left,
        evalTerm_support_congr I M env rhs agreement.append_right]
  | .addHistory target history, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env target agreement.append_left,
        evalTerm_support_congr I M env history agreement.append_right]
  | .historyEmpty, _ => rfl
  | .historySingleton data test, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env data agreement]
  | .historyAdd a b, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env a agreement.append_left,
        evalTerm_support_congr I M env b agreement.append_right]
  | .historyCount history data test, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env history agreement.append_left,
        evalTerm_support_congr I M env data agreement.append_right]
  | .provenanceEmpty, _ => rfl
  | .provenanceSingleton data population, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env data agreement]
  | .provenanceAdd a b, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env a agreement.append_left,
        evalTerm_support_congr I M env b agreement.append_right]
  | .pvalue test, agreement => by
      simp only [evalTerm, evalNumericalEvent_support_congr I M env test agreement]
  | .realAdd a b, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env a agreement.append_left,
        evalTerm_support_congr I M env b agreement.append_right]
  | .realMin a b, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env a agreement.append_left,
        evalTerm_support_congr I M env b agreement.append_right]
  | .intAdd a b, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env a agreement.append_left,
        evalTerm_support_congr I M env b agreement.append_right]
  | .intSub a b, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env a agreement.append_left,
        evalTerm_support_congr I M env b agreement.append_right]
  | .intLess a b, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env a agreement.append_left,
        evalTerm_support_congr I M env b agreement.append_right]
  | .booleanNot term, agreement => by
      simp only [evalTerm, evalTerm_support_congr I M env term agreement]

theorem evalArguments_support_congr (I : AssertionInterpretation D Command)
    (M : Model D Command) (env : GhostEnv D Command Γ) {left right : SemanticView D} :
    (args : ValueArguments Γ inputs) → SupportAgreement args.readSupport left right →
    evalArguments I M env left args = evalArguments I M env right args
  | .nil, _ => rfl
  | .cons term rest, agreement => by
      simp only [evalArguments, evalTerm_support_congr I M env term agreement.append_left,
        evalArguments_support_congr I M env rest agreement.append_right]

theorem evalNumericalEvent_support_congr (I : AssertionInterpretation D Command)
    (M : Model D Command) (env : GhostEnv D Command Γ) {left right : SemanticView D} :
    (test : TestExpression Γ) → SupportAgreement test.readSupport left right →
    evalNumericalEvent I M env left test = evalNumericalEvent I M env right test
  | .leaf h data A pop, agreement => by
      simp only [evalNumericalEvent, evalTerm_support_congr I M env data agreement]
  | .disj name a b, agreement => by
      simp only [evalNumericalEvent,
        evalNumericalEvent_support_congr I M env a agreement.append_left,
        evalNumericalEvent_support_congr I M env b agreement.append_right]
  | .conj name a b, agreement => by
      simp only [evalNumericalEvent,
        evalNumericalEvent_support_congr I M env a agreement.append_left,
        evalNumericalEvent_support_congr I M env b agreement.append_right]
end

theorem evalTestEntries_support_congr (I : AssertionInterpretation D Command)
    (M : Model D Command) (env : GhostEnv D Command Γ) {left right : SemanticView D} :
    (test : TestExpression Γ) → SupportAgreement test.readSupport left right →
      evalTestEntries I M env left test = evalTestEntries I M env right test
  | .leaf h data A pop, agreement => by
      simp only [evalTestEntries, evalTerm_support_congr I M env data agreement]
  | .disj name a b, agreement => by
      simp only [evalTestEntries,
        evalTestEntries_support_congr I M env a agreement.append_left,
        evalTestEntries_support_congr I M env b agreement.append_right]
  | .conj name a b, agreement => by
      simp only [evalTestEntries,
        evalTestEntries_support_congr I M env a agreement.append_left,
        evalTestEntries_support_congr I M env b agreement.append_right]

theorem evalTestHistory_support_congr (I : AssertionInterpretation D Command)
    (M : Model D Command) (env : GhostEnv D Command Γ) {left right : SemanticView D}
    (test : TestExpression Γ) (agreement : SupportAgreement test.readSupport left right) :
    evalTestHistory I M env left test = evalTestHistory I M env right test := by
  simp only [evalTestHistory, evalTestEntries_support_congr I M env test agreement]

/-- Requirements consume hidden population state, modeled provenance, and the
    successful entry evaluations, not current p-values or the ambient ledger. -/
theorem modelRequirements_support_congr (I : AssertionInterpretation D Command)
    (M : Model D Command) (env : GhostEnv D Command Γ) {left right : SemanticView D}
    (hidden : left.hidden = right.hidden) (provenance : left.provenance = right.provenance) :
    (test : TestExpression Γ) → SupportAgreement test.readSupport left right →
      (modelRequirements I M env left test ↔ modelRequirements I M env right test)
  | .leaf h data A pop, agreement => by
      simp only [modelRequirements, evalTerm_support_congr I M env data agreement,
        hidden, provenance]
  | .disj name a b, agreement => by
      simp only [modelRequirements,
        modelRequirements_support_congr I M env hidden provenance a agreement.append_left,
        modelRequirements_support_congr I M env hidden provenance b agreement.append_right,
        evalTestEntries_support_congr I M env (.disj name a b) agreement, hidden]
  | .conj name a b, agreement => by
      simp only [modelRequirements,
        modelRequirements_support_congr I M env hidden provenance a agreement.append_left,
        modelRequirements_support_congr I M env hidden provenance b agreement.append_right,
        evalTestEntries_support_congr I M env (.conj name a b) agreement, hidden]

theorem atomMeaning_support_congr (I : AssertionInterpretation D Command)
    (M : Model D Command) (env : GhostEnv D Command Γ) {left right : SemanticView D}
    (atom : AssertionAtom Γ) (agreement : SupportAgreement atom.readSupport left right) :
    atomMeaning I M env left atom ↔ atomMeaning I M env right atom := by
  cases atom with
  | rigid predicate args =>
      simp only [atomMeaning, evalArguments_support_congr I M env args agreement]
  | equal a b =>
      simp only [atomMeaning, evalTerm_support_congr I M env a agreement.append_left,
        evalTerm_support_congr I M env b agreement.append_right]
  | defined term =>
      simp only [atomMeaning, evalTerm_support_congr I M env term agreement]
  | realCompare comparison a b =>
      simp only [atomMeaning, evalTerm_support_congr I M env a agreement.append_left,
        evalTerm_support_congr I M env b agreement.append_right]
  | intCompare comparison a b =>
      simp only [atomMeaning, evalTerm_support_congr I M env a agreement.append_left,
        evalTerm_support_congr I M env b agreement.append_right]
  | hypothesis h target =>
      simp only [atomMeaning, evalTerm_support_congr I M env target agreement]
  | sampling data pop provenance =>
      simp only [atomMeaning, evalTerm_support_congr I M env data agreement.append_left,
        evalTerm_support_congr I M env provenance agreement.append_right]
  | requirements test target =>
      simp only [atomMeaning, evalTerm_support_congr I M env target agreement.append_right]
  | admitted world =>
      simp only [atomMeaning, evalTerm_support_congr I M env world agreement]
  | action command state =>
      simp only [atomMeaning, evalTerm_support_congr I M env state agreement]

/-- A test writes exactly its observable real output. All other typed cells and
    scientific carriers are fresh; whole observable memory and history are not. -/
def TestFreshRegion (result : Variable .real .observable) : ReadRegion → Prop
  | .variable sort visibility x => visibility = .invisible ∨ sort ≠ .real ∨ x.id ≠ result.id
  | .dataset _ | .datasets | .hiddenValues | .compatible | .provenance => True
  | .observableValues | .history => False

inductive AtomTestFrame {Γ : List GhostSort} (result : Variable .real .observable) :
    AssertionAtom Γ → Prop where
  | fresh {atom} (fresh : ∀ region ∈ atom.readSupport, TestFreshRegion result region) :
      AtomTestFrame result atom
  | requirementsAmbient {test : TestExpression Γ}
      (fresh : ∀ region ∈ test.readSupport, TestFreshRegion result region) :
      AtomTestFrame result (.requirements test .ambient)

inductive ModalTestFrame {Γ : List GhostSort} (result : Variable .real .observable) :
    ModalFormula Γ → Prop where
  | atom {atom} : AtomTestFrame result atom → ModalTestFrame result (.atom atom)
  | neg {formula} : ModalTestFrame result formula → ModalTestFrame result (.neg formula)
  | conj {left right} : ModalTestFrame result left → ModalTestFrame result right →
      ModalTestFrame result (.conj left right)
  | knows {formula} : ModalTestFrame result formula → ModalTestFrame result (.knows formula)
  | atWorld {target : AssertionTerm Γ .world} {body : ModalFormula Γ}
      (fresh : ∀ region ∈ target.readSupport, TestFreshRegion result region) :
      ModalTestFrame result (.atWorld target body)
  | atView {target : AssertionTerm Γ .view} {body : ModalFormula Γ}
      (fresh : ∀ region ∈ target.readSupport, TestFreshRegion result region) :
      ModalTestFrame result (.atView target body)

inductive AssertionTestFrame (result : Variable .real .observable) :
    {Γ : List GhostSort} → Assertion Γ → Prop where
  | modal {formula : ModalFormula Γ} : ModalTestFrame result formula →
      AssertionTestFrame result (.modal formula)
  | neg {assertion : Assertion Γ} : AssertionTestFrame result assertion →
      AssertionTestFrame result (.neg assertion)
  | conj {left right : Assertion Γ} : AssertionTestFrame result left → AssertionTestFrame result right →
      AssertionTestFrame result (.conj left right)
  | all {sort : GhostSort} {body : Assertion (sort :: Γ)} : AssertionTestFrame result body →
      AssertionTestFrame result (.all sort body)
  | atWorld {target : AssertionTerm Γ .world} {body : Assertion Γ}
      (fresh : ∀ region ∈ target.readSupport, TestFreshRegion result region) :
      AssertionTestFrame result (.atWorld target body)
  | atView {target : AssertionTerm Γ .view} {body : Assertion Γ}
      (fresh : ∀ region ∈ target.readSupport, TestFreshRegion result region) :
      AssertionTestFrame result (.atView target body)

theorem ModalTestFrame.disj {φ ψ : ModalFormula Γ}
    (left : ModalTestFrame r φ) (right : ModalTestFrame r ψ) :
    ModalTestFrame r (φ.disj ψ) := .neg (.conj (.neg left) (.neg right))

theorem ModalTestFrame.implies {φ ψ : ModalFormula Γ}
    (left : ModalTestFrame r φ) (right : ModalTestFrame r ψ) :
    ModalTestFrame r (φ.implies ψ) := (ModalTestFrame.neg left).disj right

theorem ModalTestFrame.possible {φ : ModalFormula Γ}
    (body : ModalTestFrame r φ) : ModalTestFrame r φ.possible :=
  .neg (.knows (.neg body))

theorem AssertionTestFrame.disj {P Q : Assertion Γ}
    (left : AssertionTestFrame r P) (right : AssertionTestFrame r Q) :
    AssertionTestFrame r (P.disj Q) := .neg (.conj (.neg left) (.neg right))

theorem AssertionTestFrame.implies {P Q : Assertion Γ}
    (left : AssertionTestFrame r P) (right : AssertionTestFrame r Q) :
    AssertionTestFrame r (P.implies Q) := (AssertionTestFrame.neg left).disj right

theorem AssertionTestFrame.exists {P : Assertion (sort :: Γ)} (body : AssertionTestFrame r P) :
    AssertionTestFrame r (Assertion.exists sort P) := .neg (.all (.neg body))

variable {ctx : ProgramContext D} {r : Variable .real .observable}
    {h : HypothesisId} {y : DatasetExpr} {A : TestId} {pop : PopulationId}
    {before after : World D Primitive}

theorem test_step_datasets
    (step : Step ctx (some (.command (.test r h y A pop))) before none after) :
    after.current.datasets = before.current.datasets := by
  obtain ⟨data, evaluated, _, _⟩ := test_step_effect.mp step
  exact (test_step_report evaluated step).2.2.1

theorem test_step_program_frame
    (step : Step ctx (some (.command (.test r h y A pop))) before none after) :
    ProgramFrame [.value .real r.id] before.current.visible after.current.visible := by
  obtain ⟨data, _, _, rfl⟩ := test_step_effect.mp step
  simpa only [World.extend_current, commandState_visible, VisibleWrite.cells] using
    VisibleWrite.apply_frame
      (.value r ((ctx.interpretation.tests h A).tailProbability data))
      before.current.visible

theorem test_step_program_agreement {support : List ProgramCell}
    (fresh : ∀ cell ∈ support, cell ≠ .value .real r.id)
    (step : Step ctx (some (.command (.test r h y A pop))) before none after) :
    ProgramAgreement support before.current.visible after.current.visible :=
  (test_step_program_frame step).agreement
    (fun cell member => by simpa only [List.mem_singleton] using fresh cell member)

theorem evalProgramExpr_test_frame (expression : ProgramExpr sort)
    (fresh : ∀ cell ∈ expression.reads, cell ≠ .value .real r.id)
    (step : Step ctx (some (.command (.test r h y A pop))) before none after) :
    evalProgramExpr ctx.interpretation before.current.visible expression =
      evalProgramExpr ctx.interpretation after.current.visible expression :=
  evalProgramExpr_congr _ _ _ expression (test_step_program_agreement fresh step)

theorem evalDatasetExpr_test_frame (expression : DatasetExpr)
    (fresh : ∀ cell ∈ expression.reads, cell ≠ .value .real r.id)
    (step : Step ctx (some (.command (.test r h y A pop))) before none after) :
    evalDatasetExpr ctx.interpretation before.current.visible expression =
      evalDatasetExpr ctx.interpretation after.current.visible expression :=
  evalDatasetExpr_congr _ _ _ expression (test_step_program_agreement fresh step)

theorem test_step_read_other (x : Variable sort visibility)
    (fresh : TestFreshRegion r (.variable sort visibility x))
    (step : Step ctx (some (.command (.test r h y A pop))) before none after) :
    after.current.memory.read x = before.current.memory.read x := by
  obtain ⟨data, _, _, rfl⟩ := test_step_effect.mp step
  have other : ValueSort.real ≠ sort ∨ Visibility.observable ≠ visibility ∨ r.id ≠ x.id := by
    rcases fresh with invisible | differentSort | differentId
    · exact Or.inr (Or.inl (by simp [invisible]))
    · exact Or.inl (Ne.symm differentSort)
    · exact Or.inr (Or.inr (Ne.symm differentId))
  cases visibility with
  | observable =>
      simpa [commandState, VisibleWrite.apply, Memory.read, Memory.assemble,
        Memory.observable, State.visible] using
        Memory.read_update_other
          (Memory.assemble before.current.visible.memory (fun _ _ => none)) r
          (some ((ctx.interpretation.tests h A).tailProbability data)) x other
  | invisible =>
      simp [commandState, VisibleWrite.apply, Memory.read, Memory.assemble, Memory.hidden]

theorem test_step_fresh_support {support : ReadSupport}
    (fresh : ∀ region ∈ support, TestFreshRegion r region)
    (step : Step ctx (some (.command (.test r h y A pop))) before none after) :
    SupportAgreement support (semanticView ctx.model.dynamics before)
      (semanticView ctx.model.dynamics after) := by
  intro region member
  have valid := fresh region member
  cases region with
  | «variable» sort visibility x =>
      simpa only [ReadRegion.Agrees, semanticView, State.visible, Memory.assemble_projections]
        using (test_step_read_other x valid step).symm
  | dataset name =>
      exact congrArg (fun datasets => datasets name) (test_step_datasets step).symm
  | observableValues => exact False.elim valid
  | datasets => exact (test_step_datasets step).symm
  | hiddenValues => exact step.hidden.symm
  | history => exact False.elim valid
  | compatible => exact step.compatible_hidden.symm
  | provenance => exact step.sampling_provenance.symm

theorem evalTerm_test_frame (env : GhostEnv D Primitive Γ) (term : AssertionTerm Γ sort)
    (fresh : ∀ region ∈ term.readSupport, TestFreshRegion r region)
    (step : Step ctx (some (.command (.test r h y A pop))) before none after) :
    evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics before) term =
      evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics after) term :=
  evalTerm_support_congr _ _ env term (test_step_fresh_support fresh step)

theorem atom_test_frame {atom : AssertionAtom Γ} (cert : AtomTestFrame r atom)
    (env : GhostEnv D Primitive Γ)
    (step : Step ctx (some (.command (.test r h y A pop))) before none after) :
    atomMeaning ctx.interpretation ctx.model env (semanticView ctx.model.dynamics before) atom ↔
      atomMeaning ctx.interpretation ctx.model env (semanticView ctx.model.dynamics after) atom := by
  cases cert with
  | fresh fresh =>
      exact atomMeaning_support_congr _ _ env atom (test_step_fresh_support fresh step)
  | requirementsAmbient fresh =>
      simp only [atomMeaning, evalTerm, Option.some.injEq]
      have congruence := modelRequirements_support_congr
        ctx.interpretation ctx.model env step.hidden.symm
        step.sampling_provenance.symm _ (test_step_fresh_support fresh step)
      constructor
      · rintro ⟨view, equal, requirements⟩
        subst view
        exact ⟨_, rfl, congruence.mp requirements⟩
      · rintro ⟨view, equal, requirements⟩
        subst view
        exact ⟨_, rfl, congruence.mpr requirements⟩

/-- Exact reference frame under an actual admitted test transition, including
    arbitrary nested knowledge and arbitrary bodies at stable fixed targets. -/
theorem modal_test_frame {formula : ModalFormula Γ} (cert : ModalTestFrame r formula)
    (env : GhostEnv D Primitive Γ)
    (initial : Admitted ctx.model.dynamics before)
    (step : Step ctx (some (.command (.test r h y A pop))) before none after) :
    referenceModalSatisfaction ctx.interpretation ctx.model env before formula ↔
      referenceModalSatisfaction ctx.interpretation ctx.model env after formula := by
  induction cert generalizing before after with
  | atom atomCert => exact atom_test_frame atomCert env step
  | neg body ih => exact not_congr (ih initial step)
  | conj left right il ir => exact and_congr (il initial step) (ir initial step)
  | knows body ih =>
      constructor
      · intro known alternative admitted accessible
        obtain ⟨source, sourceAdmitted, sourceAccessible, sourceStep⟩ :=
          command_accessible_back initial step admitted accessible
        exact (ih sourceAdmitted sourceStep).mp (known source sourceAdmitted sourceAccessible)
      · intro known alternative admitted accessible
        obtain ⟨target, targetStep, targetAdmitted, targetAccessible⟩ :=
          command_accessible_forth step admitted accessible
        exact (ih admitted targetStep).mpr (known target targetAdmitted targetAccessible)
  | atWorld fresh =>
      simp only [referenceModalSatisfaction, evalTerm_test_frame env _ fresh step]
  | atView fresh =>
      simp only [referenceModalSatisfaction, evalTerm_test_frame env _ fresh step]

/-- Outer binders retain every mathematical ghost value; fixed scopes do not
    restrict the body grammar or its local reads. -/
theorem assertion_test_frame {P : Assertion Γ} (cert : AssertionTestFrame r P)
    (env : GhostEnv D Primitive Γ)
    (initial : Admitted ctx.model.dynamics before)
    (step : Step ctx (some (.command (.test r h y A pop))) before none after) :
    referenceAssertionSatisfaction ctx.interpretation ctx.model env before P ↔
      referenceAssertionSatisfaction ctx.interpretation ctx.model env after P := by
  induction cert with
  | modal modalCert => exact modal_test_frame modalCert env initial step
  | neg body ih => exact not_congr (ih env)
  | conj left right il ir => exact and_congr (il env) (ir env)
  | all body ih =>
      exact forall_congr' (fun value => ih (GhostEnv.push value env))
  | atWorld fresh =>
      simp only [referenceAssertionSatisfaction, evalTerm_test_frame env _ fresh step]
  | atView fresh =>
      simp only [referenceAssertionSatisfaction, evalTerm_test_frame env _ fresh step]

theorem satisfies_test_frame {P : Assertion Γ} (cert : AssertionTestFrame r P)
    (env : GhostEnv D Primitive Γ)
    (initial : Admitted ctx.model.dynamics before)
    (step : Step ctx (some (.command (.test r h y A pop))) before none after) :
    satisfies ctx.interpretation ctx.model env before P ↔
      satisfies ctx.interpretation ctx.model env after P := by
  simp only [satisfies, initial, step.admitted initial, true_and]
  exact assertion_test_frame cert env initial step

end
end Lara.BHL
