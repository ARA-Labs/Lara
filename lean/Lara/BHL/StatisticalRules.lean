import Lara.BHL.StatisticalFrame
import Lara.BHL.BeliefLaws
import Lara.BHL.Derivation
import Lara.BHL.Soundness

/-!
Derived statistical Hoare rules for the belief Hoare logic.

The five source-mapped rules (Two-HT, Low-HT, Up-HT and the two multiple-test
sum/min rules) are *derived* from the eight base constructors: a primitive test
with a proved bookkeeping preimage, followed by an assertion implication that
introduces belief from an actual observable exception (or from an actual coupled
union/intersection). No constructor asserts belief, an execution, or the derived
postcondition, and no premise contains the desired preimage or the whole triple.

Science is carried by explicit mathematical data: `LeafScientificBinding` binds
a real population-law family to the selected test's null law and binds the
declared null formula to the hypotheses relation; `PairScientificBinding`
selects an actual `I.couplings` coupling of the two *actual* child null laws and
supplies a genuine joint population law whose statistic pushforward is exactly
the selected joint law. Requirements, sampling provenance, numerical
availability, input definedness, freshness and output disjointness stay separate.
-/

namespace Lara.BHL
open MeasureTheory


noncomputable section

variable {D : Type} [MeasurableSpace D]

/-- Combined-null mode of the multiple-test rules. -/
inductive StatisticalMode where
  | disj
  | conj
  deriving DecidableEq

namespace StatisticalMode

/-- The combined test expression of the chosen mode. -/
abbrev combined {Γ : List GhostSort} (mode : StatisticalMode) (k : CouplingId)
    (left right : TestExpression Γ) : TestExpression Γ :=
  match mode with
  | .disj => TestExpression.disj k left right
  | .conj => TestExpression.conj k left right

/-- The alternative reported by the chosen mode: the disjunction of the two
child alternatives for the union rule, their conjunction for the intersection
rule. -/
abbrev alternative {Γ : List GhostSort} (mode : StatisticalMode) (φ1 φ2 : ModalFormula Γ) :
    ModalFormula Γ :=
  match mode with
  | .disj => ModalFormula.disj φ1 φ2
  | .conj => ModalFormula.conj φ1 φ2

/-- The genuine joint scientific hypothesis combination of the chosen mode.
A disjunction of null events corresponds to the conjunction of the individual
null hypotheses; a conjunction of null events to their disjunction. -/
def hypotheses (interpretation : AssertionInterpretation D Primitive) (h1 h2 : HypothesisId)
    (hidden : HiddenMemory) : StatisticalMode → Prop
  | .disj => interpretation.hypotheses h1 hidden ∧ interpretation.hypotheses h2 hidden
  | .conj => interpretation.hypotheses h1 hidden ∨ interpretation.hypotheses h2 hidden

end StatisticalMode

/-! ## Finite assertion builders -/

/-- A source leaf test: hypothesis, dataset expression, test and population. -/
abbrev leaf (context : List GhostSort) (h : HypothesisId) (y : DatasetExpr) (A : TestId)
    (pop : PopulationId) : TestExpression context :=
  TestExpression.leaf h (y.toAssertionTerm context) A pop

/-- The observable report cell read at the ambient view. -/
abbrev report (context : List GhostSort) (r : Variable .real .observable) :
    AssertionTerm context (.value .real) :=
  AssertionTerm.valueRead .ambient r

/-- The ambient ledger is exactly empty. -/
abbrev emptyHistory (context : List GhostSort) : Assertion context :=
  Assertion.modal (ModalFormula.atom (AssertionAtom.equal
    (AssertionTerm.historyOf AssertionTerm.ambient) AssertionTerm.historyEmpty))

/-- The ambient ledger is exactly the complete (multi)set of the test expression. -/
abbrev ledger {Γ : List GhostSort} (t : TestExpression Γ) : Assertion Γ :=
  Assertion.modal (exactHistory t)

/-- The stored report cell equals the current numerical event probability.
Equality demands successful evaluation of both sides, so an undefined event is
never silently read as zero. -/
abbrev stored {Γ : List GhostSort} (r : Variable .real .observable)
    (t : TestExpression Γ) : Assertion Γ :=
  Assertion.modal (ModalFormula.atom
    (AssertionAtom.equal (report Γ r) (AssertionTerm.pvalue t)))

/-- The stored report is an ordinary probability in the unit interval. -/
abbrev reportRange (context : List GhostSort) (r : Variable .real .observable) :
    Assertion context :=
  Assertion.modal (ModalFormula.conj
    (ModalFormula.atom (AssertionAtom.realCompare Comparison.lessEqual
      (AssertionTerm.rational (0 : ℚ)) (report context r)))
    (ModalFormula.atom (AssertionAtom.realCompare Comparison.lessEqual
      (report context r) (AssertionTerm.rational (1 : ℚ)))))

/-- A belief assertion for one test expression with an explicit real threshold. -/
abbrev belief {Γ : List GhostSort} (comparison : Comparison)
    (bound : AssertionTerm Γ (.value .real)) (t : TestExpression Γ)
    (alternative : ModalFormula Γ) : Assertion Γ :=
  Assertion.modal (statisticalBelief comparison bound t alternative)

/-- Explicit source falsehood used by the alternative-exclusivity premise. -/
abbrev falseAssertion {Γ : List GhostSort} : Assertion Γ :=
  Assertion.modal (ModalFormula.atom (AssertionAtom.equal (AssertionTerm.boolean true)
    (AssertionTerm.boolean false)))

/-- Precondition of the single-test rules: the shared assertion and an empty ledger. -/
abbrev singlePre {Γ : List GhostSort} (ψ : Assertion Γ) : Assertion Γ :=
  Assertion.conj ψ (emptyHistory Γ)

/-- Belief-free bookkeeping postcondition of a single test: the preserved shared
assertion, the exact complete ledger, the stored report equality and its range. -/
abbrev singleBook {Γ : List GhostSort} (ψ : Assertion Γ) (r : Variable .real .observable)
    (t : TestExpression Γ) : Assertion Γ :=
  Assertion.conj ψ (Assertion.conj (ledger t)
    (Assertion.conj (stored r t) (reportRange Γ r)))

/-- Postcondition of the single-test rules. -/
abbrev singlePost {Γ : List GhostSort} (ψ : Assertion Γ) (r : Variable .real .observable)
    (t : TestExpression Γ) (alternative : ModalFormula Γ) : Assertion Γ :=
  Assertion.conj ψ (Assertion.conj (ledger t)
    (belief Comparison.equal (report Γ r) t alternative))

/-- Precondition of the multiple-test rules: the shared assertion, the exact
first ledger, the first belief, the first stored report equality and its range. -/
abbrev multiPre {Γ : List GhostSort} (ψ : Assertion Γ) (r1 : Variable .real .observable)
    (t1 : TestExpression Γ) (φ1 : ModalFormula Γ) : Assertion Γ :=
  Assertion.conj ψ (Assertion.conj (ledger t1) (Assertion.conj
    (belief Comparison.equal (report Γ r1) t1 φ1)
    (Assertion.conj (stored r1 t1) (reportRange Γ r1))))

/-- Belief-free bookkeeping postcondition of the second test: the preserved
shared assertion, the exact complete combined ledger, both stored report
equalities (the first at its own, distinct, report cell) and both ranges. -/
abbrev multiBook {Γ : List GhostSort} (ψ : Assertion Γ) (r1 r2 : Variable .real .observable)
    (t1 t2 combined : TestExpression Γ) : Assertion Γ :=
  Assertion.conj ψ (Assertion.conj (ledger combined) (Assertion.conj (stored r1 t1)
    (Assertion.conj (stored r2 t2) (Assertion.conj (reportRange Γ r1) (reportRange Γ r2)))))

/-- Postcondition of the multiple-test disjunction rule. The sum is a real sum,
possibly greater than one; it is not clamped. -/
abbrev multiDisjPost {Γ : List GhostSort} (ψ : Assertion Γ) (r1 r2 : Variable .real .observable)
    (t1 t2 : TestExpression Γ) (k : CouplingId) (φ1 φ2 : ModalFormula Γ) : Assertion Γ :=
  Assertion.conj ψ (Assertion.conj (ledger (TestExpression.disj k t1 t2))
    (belief Comparison.lessEqual (AssertionTerm.realAdd (report Γ r1) (report Γ r2))
      (TestExpression.disj k t1 t2) (ModalFormula.disj φ1 φ2)))

/-- Postcondition of the multiple-test conjunction rule. The bound is the actual
minimum of the two stored reports. -/
abbrev multiConjPost {Γ : List GhostSort} (ψ : Assertion Γ) (r1 r2 : Variable .real .observable)
    (t1 t2 : TestExpression Γ) (k : CouplingId) (φ1 φ2 : ModalFormula Γ) : Assertion Γ :=
  Assertion.conj ψ (Assertion.conj (ledger (TestExpression.conj k t1 t2))
    (belief Comparison.lessEqual (AssertionTerm.realMin (report Γ r1) (report Γ r2))
      (TestExpression.conj k t1 t2) (ModalFormula.conj φ1 φ2)))

/-! ## Scientific carriers -/

/-- Actual scientific binding of one leaf test. `populationLaw` is a real family
of probability measures; `null_denotes` is the exact denotation of the declared
null formula on admitted worlds; `null_statistic_law` binds the population
pushforward of the selected statistic to the selected test's null law under the
modelled requirements and the null hypotheses. No field mentions belief,
execution, derivation or the derived postcondition. -/
structure LeafScientificBinding (ctx : ProgramContext D) (h : HypothesisId) (A : TestId)
    (pop : PopulationId) {Γ : List GhostSort} (nullFormula : ModalFormula Γ) where
  populationLaw : HiddenMemory → ProbabilityMeasure D
  null_denotes : ∀ (env : GhostEnv D Primitive Γ) (world : World D Primitive),
    Admitted ctx.model.dynamics world →
      (referenceModalSatisfaction ctx.interpretation ctx.model env world nullFormula ↔
        ctx.interpretation.hypotheses h (semanticView ctx.model.dynamics world).hidden)
  null_statistic_law : ∀ (hidden : HiddenMemory) (d : D),
    ctx.interpretation.requirements h A pop hidden d →
      ctx.interpretation.hypotheses h hidden →
      (populationLaw hidden).map
          (ctx.interpretation.tests h A).measurableStatistic.aemeasurable =
        (ctx.interpretation.tests h A).nullLaw

/-- The genuine joint real statistic of two leaf tests. -/
abbrev jointStatistic (ctx : ProgramContext D) (h1 : HypothesisId) (A1 : TestId)
    (h2 : HypothesisId) (A2 : TestId) : D × D → ℝ × ℝ :=
  fun pair => ((ctx.interpretation.tests h1 A1).statistic pair.1,
    (ctx.interpretation.tests h2 A2).statistic pair.2)

theorem measurable_jointStatistic (ctx : ProgramContext D) (h1 : HypothesisId) (A1 : TestId)
    (h2 : HypothesisId) (A2 : TestId) : Measurable (jointStatistic ctx h1 A1 h2 A2) :=
  ((ctx.interpretation.tests h1 A1).measurableStatistic.comp measurable_fst).prodMk
    ((ctx.interpretation.tests h2 A2).measurableStatistic.comp measurable_snd)

/-- Actual selected-coupling science for a multiple-test rule. The coupling is a
real `ProbabilityCoupling` of the two *actual* child null laws, selected by the
named coupling identifier; `jointPopulationLaw` is a genuine joint population
law whose joint-statistic pushforward equals the selected joint law under the
modelled joint requirement and the joint null hypothesis combination. Both
coupling marginals are proof evidence: neither independence nor coupling
availability is inferred from numerical availability. -/
structure PairScientificBinding (ctx : ProgramContext D) (h1 : HypothesisId) (A1 : TestId)
    (pop1 : PopulationId) (h2 : HypothesisId) (A2 : TestId) (pop2 : PopulationId)
    (k : CouplingId) {Γ : List GhostSort} (φ1 φ2 : ModalFormula Γ)
    (mode : StatisticalMode) where
  left : LeafScientificBinding ctx h1 A1 pop1 (.neg φ1)
  right : LeafScientificBinding ctx h2 A2 pop2 (.neg φ2)
  coupling : ProbabilityCoupling (ctx.interpretation.tests h1 A1).nullLaw
    (ctx.interpretation.tests h2 A2).nullLaw
  selected : ctx.interpretation.couplings k .real .real
    (ctx.interpretation.tests h1 A1).nullLaw (ctx.interpretation.tests h2 A2).nullLaw =
      some coupling
  jointPopulationLaw : HiddenMemory → ProbabilityMeasure (D × D)
  leftPopulationMarginal : ∀ (hidden : HiddenMemory) (d1 d2 : D),
    ctx.interpretation.jointRequirements k hidden [(d1, A1, pop1), (d2, A2, pop2)] →
      (jointPopulationLaw hidden).map measurable_fst.aemeasurable = left.populationLaw hidden
  rightPopulationMarginal : ∀ (hidden : HiddenMemory) (d1 d2 : D),
    ctx.interpretation.jointRequirements k hidden [(d1, A1, pop1), (d2, A2, pop2)] →
      (jointPopulationLaw hidden).map measurable_snd.aemeasurable = right.populationLaw hidden
  joint_null_law : ∀ (hidden : HiddenMemory) (d1 d2 : D),
    ctx.interpretation.jointRequirements k hidden [(d1, A1, pop1), (d2, A2, pop2)] →
      StatisticalMode.hypotheses ctx.interpretation h1 h2 hidden mode →
      (jointPopulationLaw hidden).map
        (measurable_jointStatistic ctx h1 A1 h2 A2).aemeasurable = coupling.joint

/-! ## Premise carriers -/

/-- Source-mapped explicit premises of the single-test rules. Each field is an
ordinary side condition; none contains a derivation, an execution, the desired
preimage or the desired postcondition. -/
structure SingleHTPremises (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (L U : ModalFormula Γ) (r : Variable .real .observable) (h : HypothesisId)
    (y : DatasetExpr) (A : TestId) (pop : PopulationId) (prior : ModalFormula Γ) where
  frameψ : AssertionTestFrame r ψ
  frameL : ModalTestFrame r L
  frameU : ModalTestFrame r U
  data_fresh : ProgramCell.value .real r.id ∉ y.reads
  inputs : AssertionEntails ctx ψ (.modal (.atom (.defined (y.toAssertionTerm Γ))))
  meaningful : AssertionEntails ctx ψ
    (.modal ((modelRequirementsFormula (leaf Γ h y A pop)).conj prior))
  exclusive : AssertionEntails ctx (.modal (L.conj U)) falseAssertion
  scientific : LeafScientificBinding ctx h A pop (nullAlternative U L)

/-- Source-mapped explicit premises of the multiple-test rules. -/
structure MultiHTPremises (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (φ1 φ2 : ModalFormula Γ) (r1 r2 : Variable .real .observable) (h1 h2 : HypothesisId)
    (y1 y2 : DatasetExpr) (A1 A2 : TestId) (pop1 pop2 : PopulationId) (k : CouplingId)
    (mode : StatisticalMode) where
  outputs_ne : r1.id ≠ r2.id
  dataset_fresh : ∀ r ∈ [r1, r2], ∀ y ∈ [y1, y2], ProgramCell.value .real r.id ∉ y.reads
  frameψ1 : AssertionTestFrame r1 ψ
  frameψ2 : AssertionTestFrame r2 ψ
  frameφ11 : ModalTestFrame r1 φ1
  frameφ12 : ModalTestFrame r2 φ1
  frameφ21 : ModalTestFrame r1 φ2
  frameφ22 : ModalTestFrame r2 φ2
  inputs : AssertionEntails ctx ψ (.modal ((ModalFormula.atom (.defined (y1.toAssertionTerm Γ))).conj
    (.atom (.defined (y2.toAssertionTerm Γ)))))
  meaningful : AssertionEntails ctx ψ (.modal
    ((modelRequirementsFormula (leaf Γ h2 y2 A2 pop2)).conj
      (ModalFormula.possible (StatisticalMode.alternative mode φ1 φ2))))
  pair_meaningful : AssertionEntails ctx ψ
    (.modal (modelRequirementsFormula (StatisticalMode.combined mode k
      (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2))))
  scientific : PairScientificBinding ctx h1 A1 pop1 h2 A2 pop2 k φ1 φ2 mode

/-! ## Elementary evaluation facts -/

/-- The report cell evaluates to the observable visible-memory read. -/
theorem evalTerm_report (ctx : ProgramContext D) {Γ : List GhostSort}
    (env : GhostEnv D Primitive Γ) (view : SemanticView D) (r : Variable .real .observable) :
    evalTerm ctx.interpretation ctx.model env view (report Γ r) = view.visible.memory .real r.id :=
  rfl

/-- Rational literals evaluate to their real coercion. -/
theorem evalTerm_rational (ctx : ProgramContext D) {Γ : List GhostSort}
    (env : GhostEnv D Primitive Γ) (view : SemanticView D) (q : ℚ) :
    evalTerm ctx.interpretation ctx.model env view (AssertionTerm.rational q) = some (q : ℝ) :=
  rfl

/-- A leaf numerical event is the actual null-law tail at the evaluated data. -/
theorem evalNumericalEvent_leaf (ctx : ProgramContext D) {Γ : List GhostSort}
    (env : GhostEnv D Primitive Γ) (view : SemanticView D) (h : HypothesisId)
    (y : DatasetExpr) (A : TestId) (pop : PopulationId) :
    evalNumericalEvent ctx.interpretation ctx.model env view (leaf Γ h y A pop) =
      (evalTerm ctx.interpretation ctx.model env view (y.toAssertionTerm Γ)).map
        (fun d => (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h A) d⟩ :
          PackedNumericalEvent)) :=
  rfl

/-- A leaf numerical event at a successful dataset value. -/
theorem evalNumericalEvent_leaf_some (ctx : ProgramContext D) {Γ : List GhostSort}
    (env : GhostEnv D Primitive Γ) (view : SemanticView D) (h : HypothesisId)
    (y : DatasetExpr) (A : TestId) (pop : PopulationId) (d : D)
    (hdata : evalTerm ctx.interpretation ctx.model env view (y.toAssertionTerm Γ) = some d) :
    evalNumericalEvent ctx.interpretation ctx.model env view (leaf Γ h y A pop) =
      some (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h A) d⟩ :
        PackedNumericalEvent) := by
  rw [evalNumericalEvent_leaf, hdata]
  rfl

/-- The p-value of a leaf test evaluated on a successful dataset value. -/
theorem evalTerm_pvalue_leaf_some (ctx : ProgramContext D) {Γ : List GhostSort}
    (env : GhostEnv D Primitive Γ) (view : SemanticView D) (h : HypothesisId)
    (y : DatasetExpr) (A : TestId) (pop : PopulationId) (d : D)
    (hdata : evalTerm ctx.interpretation ctx.model env view (y.toAssertionTerm Γ) = some d) :
    evalTerm ctx.interpretation ctx.model env view (.pvalue (leaf Γ h y A pop)) =
      some ((ctx.interpretation.tests h A).tailProbability d) := by
  change Option.map (fun event : PackedNumericalEvent => event.2.probability)
      (Option.map (fun data => (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h A) data⟩ :
        PackedNumericalEvent)) (evalTerm ctx.interpretation ctx.model env view
          (y.toAssertionTerm Γ))) =
    some ((ctx.interpretation.tests h A).tailProbability d)
  simp [hdata]

/-- A leaf p-value is defined exactly on a successfully evaluated dataset term. -/
theorem pvalue_leaf_some_iff (ctx : ProgramContext D) {Γ : List GhostSort}
    (env : GhostEnv D Primitive Γ) (view : SemanticView D) (h : HypothesisId)
    (y : DatasetExpr) (A : TestId) (pop : PopulationId) (value : ℝ) :
    evalTerm ctx.interpretation ctx.model env view (.pvalue (leaf Γ h y A pop)) = some value ↔
      ∃ d, evalTerm ctx.interpretation ctx.model env view (y.toAssertionTerm Γ) = some d ∧
        (ctx.interpretation.tests h A).tailProbability d = value := by
  change Option.map (fun event : PackedNumericalEvent => event.2.probability)
      (Option.map (fun data => (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h A) data⟩ :
        PackedNumericalEvent)) (evalTerm ctx.interpretation ctx.model env view
          (y.toAssertionTerm Γ))) = some value ↔
    ∃ d, evalTerm ctx.interpretation ctx.model env view (y.toAssertionTerm Γ) = some d ∧
      (ctx.interpretation.tests h A).tailProbability d = value
  cases hd : evalTerm ctx.interpretation ctx.model env view (y.toAssertionTerm Γ) <;>
    simp

/-- Exact meaning of the stored-report equality. -/
theorem stored_iff (ctx : ProgramContext D) {Γ : List GhostSort}
    (env : GhostEnv D Primitive Γ) (world : World D Primitive)
    (r : Variable .real .observable) (t : TestExpression Γ) :
    referenceAssertionSatisfaction ctx.interpretation ctx.model env world (stored r t) ↔
      ∃ value, evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics world)
          (report Γ r) = some value ∧
        evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics world)
          (.pvalue t) = some value :=
  Iff.rfl

/-- The report cell read is observation invariant. -/
theorem observationInvariant_report (ctx : ProgramContext D) {Γ : List GhostSort}
    (env : GhostEnv D Primitive Γ) (r : Variable .real .observable) :
    ObservationInvariantTerm ctx.interpretation ctx.model env (report Γ r) := by
  intro left right accessible
  rw [evalTerm_report, evalTerm_report]
  exact congrArg (fun visible : VisibleState D => visible.memory .real r.id)
    (accessible_current_visible accessible)

/-- Dataset-expression translation is observation invariant. -/
theorem observationInvariant_toDatasetExpr (ctx : ProgramContext D) {Γ : List GhostSort}
    (env : GhostEnv D Primitive Γ) (y : DatasetExpr) :
    ObservationInvariantTerm ctx.interpretation ctx.model env (y.toAssertionTerm Γ) := by
  intro left right accessible
  rw [evalTerm_toDatasetExpr, evalTerm_toDatasetExpr,
    show (semanticView ctx.model.dynamics left).visible = left.current.visible from rfl,
    show (semanticView ctx.model.dynamics right).visible = right.current.visible from rfl,
    accessible_current_visible accessible]

/-- Leaf tests are observable. -/
theorem observableTest_leaf (ctx : ProgramContext D) {Γ : List GhostSort}
    (env : GhostEnv D Primitive Γ) (h : HypothesisId) (y : DatasetExpr) (A : TestId)
    (pop : PopulationId) :
    ObservableTestExpression ctx.interpretation ctx.model env (leaf Γ h y A pop) :=
  observationInvariant_toDatasetExpr ctx env y

/-- The stored-report equation is observable, hence invariant across accessible
admitted alternatives. A first statistical belief alone is not a substitute. -/
theorem stored_at_accessible (ctx : ProgramContext D) {Γ : List GhostSort}
    (env : GhostEnv D Primitive Γ) (r : Variable .real .observable) (t : TestExpression Γ)
    (hobs : ObservableTestExpression ctx.interpretation ctx.model env t)
    {world other : World D Primitive} (accessible : Accessible world other)
    (h : referenceAssertionSatisfaction ctx.interpretation ctx.model env world (stored r t)) :
    referenceAssertionSatisfaction ctx.interpretation ctx.model env other (stored r t) := by
  obtain ⟨value, hreport, hpvalue⟩ := (stored_iff ctx env world r t).mp h
  refine (stored_iff ctx env other r t).mpr ⟨value, ?_, ?_⟩
  · exact (observationInvariant_report ctx env r world other accessible).symm.trans hreport
  · exact (observationInvariant_pvalue ctx.interpretation ctx.model env t hobs world other
      accessible).symm.trans hpvalue

/-- A stored report in the unit interval yields the range assertion. -/
theorem reportRange_of_eval (ctx : ProgramContext D) {Γ : List GhostSort}
    (env : GhostEnv D Primitive Γ) (world : World D Primitive)
    (r : Variable .real .observable) (p : ℝ)
    (hreport : evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics world)
      (report Γ r) = some p)
    (lower : 0 ≤ p) (upper : p ≤ 1) :
    referenceAssertionSatisfaction ctx.interpretation ctx.model env world (reportRange Γ r) := by
  refine ⟨⟨((0 : ℚ) : ℝ), p, ?_, hreport, ?_⟩, ⟨p, ((1 : ℚ) : ℝ), hreport, ?_, ?_⟩⟩
  · exact evalTerm_rational ctx env (semanticView ctx.model.dynamics world) 0
  · simpa only [compareReal, Rat.cast_zero] using lower
  · exact evalTerm_rational ctx env (semanticView ctx.model.dynamics world) 1
  · simpa only [compareReal, Rat.cast_one] using upper

/-! ## Test-step effects -/

/-- The visible writes of an actual test step. -/
theorem test_step_frame (ctx : ProgramContext D)
    {r : Variable .real .observable} {h : HypothesisId} {y : DatasetExpr} {A : TestId}
    {pop : PopulationId} {before after : World D Primitive}
    (step : Step ctx (some (.command (.test r h y A pop))) before none after) :
    ProgramFrame (Primitive.writes (.test r h y A pop)) before.current.visible
      after.current.visible := by
  obtain ⟨visible, delta, enabled, -, successor⟩ := Step.command_iff.mp step
  rw [successor]
  simp only [World.extend_current, commandState_visible]
  exact primitiveEffect_frame ctx.interpretation (.test r h y A pop) before.current.visible
    visible delta enabled

/-- An actual test step leaves every report cell but its own unchanged. -/
theorem test_step_read_ne (ctx : ProgramContext D)
    {r x : Variable .real .observable} {h : HypothesisId} {y : DatasetExpr} {A : TestId}
    {pop : PopulationId} {before after : World D Primitive} (distinct : x.id ≠ r.id)
    (step : Step ctx (some (.command (.test r h y A pop))) before none after) :
    after.current.visible.memory .real x.id = before.current.visible.memory .real x.id := by
  have agreement : ProgramCell.Agrees (.value .real x.id)
      before.current.visible after.current.visible := by
    apply test_step_frame ctx step
    intro member
    have same : x.id = r.id := by simpa [Primitive.writes] using member
    exact distinct same
  exact agreement.symm

/-- A dataset expression not reading the written report cell keeps its value. The
preserved expression `w` is independent of the tested expression `y`. -/
theorem test_step_dataset_value (ctx : ProgramContext D) {Γ : List GhostSort}
    (env : GhostEnv D Primitive Γ) {r : Variable .real .observable} {h : HypothesisId}
    {y : DatasetExpr} {A : TestId} {pop : PopulationId} {before after : World D Primitive}
    {d : D} {w : DatasetExpr}
    (step : Step ctx (some (.command (.test r h y A pop))) before none after)
    (fresh : ProgramCell.value .real r.id ∉ w.reads)
    (hdata : evalDatasetExpr ctx.interpretation before.current.visible w = some d) :
    evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics after)
      (w.toAssertionTerm Γ) = some d := by
  rw [evalTerm_toDatasetExpr]
  change evalDatasetExpr ctx.interpretation after.current.visible w = some d
  have agreement : ProgramAgreement w.reads before.current.visible after.current.visible :=
    ProgramFrame.agreement (test_step_frame ctx step) (fun cell member hmem => by
      have same : cell = ProgramCell.value .real r.id := by
        simpa [Primitive.writes] using hmem
      exact fresh (same ▸ member))
  exact (evalDatasetExpr_congr ctx.interpretation before.current.visible after.current.visible w
    agreement).symm.trans hdata

/-- The combined ledger of the chosen mode is the sum of the two leaf ledgers. -/
theorem evalTestHistory_combined (ctx : ProgramContext D) {Γ : List GhostSort}
    (env : GhostEnv D Primitive Γ) (view : SemanticView D) (mode : StatisticalMode)
    (k : CouplingId) (t1 t2 : TestExpression Γ) (hist1 hist2 : History D)
    (h1 : evalTestHistory ctx.interpretation ctx.model env view t1 = some hist1)
    (h2 : evalTestHistory ctx.interpretation ctx.model env view t2 = some hist2) :
    evalTestHistory ctx.interpretation ctx.model env view
      (StatisticalMode.combined mode k t1 t2) = some (hist1 + hist2) := by
  cases mode <;>
    simp [StatisticalMode.combined, evalTestHistory_disj, evalTestHistory_conj, h1, h2]

/-! ## Single-test bookkeeping and belief -/

/-- The single-test bookkeeping preimage, proved from the actual step effect.
The belief of the rule is never used here. -/
theorem single_pre_entails_book_preimage (ctx : ProgramContext D) {Γ : List GhostSort}
    (ψ : Assertion Γ) (r : Variable .real .observable) (h : HypothesisId) (y : DatasetExpr)
    (A : TestId) (pop : PopulationId) (frameψ : AssertionTestFrame r ψ)
    (data_fresh : ProgramCell.value .real r.id ∉ y.reads)
    (inputs : AssertionEntails ctx ψ (.modal (.atom (.defined (y.toAssertionTerm Γ))))) :
    AssertionEntails ctx (singlePre ψ)
      ((Primitive.test r h y A pop).preimage (singleBook ψ r (leaf Γ h y A pop))) := by
  intro env world pre
  have hψ : referenceAssertionSatisfaction ctx.interpretation ctx.model env world ψ := pre.2.1
  have defined : ∃ value, evalTerm ctx.interpretation ctx.model env
      (semanticView ctx.model.dynamics world) (y.toAssertionTerm Γ) = some value :=
    (inputs env world ⟨pre.1, hψ⟩).2
  obtain ⟨d0, hd0⟩ := defined
  have hdata : evalDatasetExpr ctx.interpretation world.current.visible y = some d0 :=
    (evalTerm_toDatasetExpr ctx.interpretation ctx.model env
      (semanticView ctx.model.dynamics world) y).symm.trans hd0
  have empty : world.current.history = (0 : History D) := by
    obtain ⟨value, firstPart, secondPart⟩ := pre.2.2
    simp only [evalTerm, Option.map_some, Option.some.injEq] at firstPart secondPart
    exact firstPart.trans secondPart.symm
  refine ⟨pre.1, ?_⟩
  have preimageForm : (Primitive.test r h y A pop).preimage (singleBook ψ r (leaf Γ h y A pop))
      = liberalPreimage ((Primitive.test r h y A pop).viewTerm Γ)
          (singleBook ψ r (leaf Γ h y A pop)) := rfl
  rw [preimageForm, reference_liberalPreimage_iff]
  intro terminal evaluated
  obtain ⟨after, step, admittedAfter, view⟩ :=
    primitive_viewTerm_realized ctx env pre.1 evaluated
  refine ⟨?_, ?_⟩
  · rw [← view]
    exact semanticView_mem_views ctx.model admittedAfter
  · rw [← view]
    refine (reference_view_assertion_correspondence ctx.interpretation ctx.model env after
      (singleBook ψ r (leaf Γ h y A pop))).mp ?_
    have hψAfter : referenceAssertionSatisfaction ctx.interpretation ctx.model env after ψ :=
      (assertion_test_frame frameψ env pre.1 step).mp hψ
    have hleaf : evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics after)
        (y.toAssertionTerm Γ) = some d0 :=
      test_step_dataset_value ctx env step data_fresh hdata
    have hreport : evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics after)
        (report Γ r) = some ((ctx.interpretation.tests h A).tailProbability d0) := by
      rw [evalTerm_report]
      exact (test_step_report hdata step).2.1
    have hpvalue : evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics after)
        (.pvalue (leaf Γ h y A pop)) =
          some ((ctx.interpretation.tests h A).tailProbability d0) :=
      evalTerm_pvalue_leaf_some ctx env (semanticView ctx.model.dynamics after) h y A pop d0 hleaf
    have ledgerSatisfied : referenceModalSatisfaction ctx.interpretation ctx.model env after
        (exactHistory (leaf Γ h y A pop)) := by
      refine (exactHistory_iff_ledger ctx.interpretation ctx.model env after
        (leaf Γ h y A pop)).mpr ?_
      have history : after.current.history = ({(d0, A)} : History D) := by
        rw [(test_step_report hdata step).2.2.2.1, empty]
        simp
      simp [evalTestHistory_leaf, hleaf, history]
    have storedSatisfied : referenceAssertionSatisfaction ctx.interpretation ctx.model env after
        (stored r (leaf Γ h y A pop)) :=
      (stored_iff ctx env after r (leaf Γ h y A pop)).mpr ⟨_, hreport, hpvalue⟩
    have rangeSatisfied : referenceAssertionSatisfaction ctx.interpretation ctx.model env after
        (reportRange Γ r) :=
      reportRange_of_eval ctx env after r _ hreport
        (NumericTest.tailProbability_nonneg (ctx.interpretation.tests h A) d0)
        (NumericTest.tailProbability_le_one (ctx.interpretation.tests h A) d0)
    exact ⟨hψAfter, ledgerSatisfied, storedSatisfied, rangeSatisfied⟩

/-- The single-test bookkeeping postcondition implies the belief postcondition:
the stored equality and range turn the actual exception into published belief. -/
theorem single_book_entails_post (ctx : ProgramContext D) {Γ : List GhostSort}
    (ψ : Assertion Γ) (r : Variable .real .observable) (h : HypothesisId) (y : DatasetExpr)
    (A : TestId) (pop : PopulationId) (alternative : ModalFormula Γ) :
    AssertionEntails ctx (singleBook ψ r (leaf Γ h y A pop))
      (singlePost ψ r (leaf Γ h y A pop) alternative) := by
  intro env world book
  obtain ⟨value, hreport, hpvalue⟩ :=
    (stored_iff ctx env world r (leaf Γ h y A pop)).mp book.2.2.2.1
  refine ⟨book.1, book.2.1, book.2.2.1, ?_⟩
  exact belief_from_observable_exception ctx.interpretation ctx.model env world Comparison.equal
    (report Γ r) (leaf Γ h y A pop) alternative (observableTest_leaf ctx env h y A pop)
    (observationInvariant_report ctx env r) ⟨value, value, hpvalue, hreport, rfl⟩ book.2.2.1

/-! ## The three single-test rules -/

/-- Two-sided two-HT rule, derived from `test` and `consequence`. -/
theorem twoHT_derivable (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (L U : ModalFormula Γ) (r : Variable .real .observable) (h : HypothesisId) (y : DatasetExpr)
    (AT : TestId) (pop : PopulationId)
    (conditions : SingleHTPremises ctx ψ L U r h y AT pop (L.possible.conj U.possible)) :
    Derivation ctx (singlePre ψ) (.command (.test r h y AT pop))
      (singlePost ψ r (leaf Γ h y AT pop) (L.disj U)) :=
  Derivation.consequence
    (single_pre_entails_book_preimage ctx ψ r h y AT pop conditions.frameψ conditions.data_fresh
      conditions.inputs)
    (Derivation.test r h y AT pop (singleBook ψ r (leaf Γ h y AT pop)))
    (single_book_entails_post ctx ψ r h y AT pop (L.disj U))

/-- Lower one-sided low-HT rule. -/
theorem lowHT_derivable (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (L U : ModalFormula Γ) (r : Variable .real .observable) (h : HypothesisId) (y : DatasetExpr)
    (AL : TestId) (pop : PopulationId)
    (conditions : SingleHTPremises ctx ψ L U r h y AL pop (L.possible.conj (.neg U.possible))) :
    Derivation ctx (singlePre ψ) (.command (.test r h y AL pop))
      (singlePost ψ r (leaf Γ h y AL pop) L) :=
  Derivation.consequence
    (single_pre_entails_book_preimage ctx ψ r h y AL pop conditions.frameψ conditions.data_fresh
      conditions.inputs)
    (Derivation.test r h y AL pop (singleBook ψ r (leaf Γ h y AL pop)))
    (single_book_entails_post ctx ψ r h y AL pop L)

/-- Upper one-sided up-HT rule. -/
theorem upHT_derivable (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (L U : ModalFormula Γ) (r : Variable .real .observable) (h : HypothesisId) (y : DatasetExpr)
    (AU : TestId) (pop : PopulationId)
    (conditions : SingleHTPremises ctx ψ L U r h y AU pop ((ModalFormula.neg L.possible).conj U.possible)) :
    Derivation ctx (singlePre ψ) (.command (.test r h y AU pop))
      (singlePost ψ r (leaf Γ h y AU pop) U) :=
  Derivation.consequence
    (single_pre_entails_book_preimage ctx ψ r h y AU pop conditions.frameψ conditions.data_fresh
      conditions.inputs)
    (Derivation.test r h y AU pop (singleBook ψ r (leaf Γ h y AU pop)))
    (single_book_entails_post ctx ψ r h y AU pop U)

theorem twoHT_sound (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (L U : ModalFormula Γ) (r : Variable .real .observable) (h : HypothesisId) (y : DatasetExpr)
    (AT : TestId) (pop : PopulationId)
    (conditions : SingleHTPremises ctx ψ L U r h y AT pop (L.possible.conj U.possible)) :
    ValidTriple ctx (singlePre ψ) (.command (.test r h y AT pop))
      (singlePost ψ r (leaf Γ h y AT pop) (L.disj U)) :=
  derivation_sound (twoHT_derivable ctx ψ L U r h y AT pop conditions)

theorem lowHT_sound (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (L U : ModalFormula Γ) (r : Variable .real .observable) (h : HypothesisId) (y : DatasetExpr)
    (AL : TestId) (pop : PopulationId)
    (conditions : SingleHTPremises ctx ψ L U r h y AL pop (L.possible.conj (.neg U.possible))) :
    ValidTriple ctx (singlePre ψ) (.command (.test r h y AL pop))
      (singlePost ψ r (leaf Γ h y AL pop) L) :=
  derivation_sound (lowHT_derivable ctx ψ L U r h y AL pop conditions)

theorem upHT_sound (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (L U : ModalFormula Γ) (r : Variable .real .observable) (h : HypothesisId) (y : DatasetExpr)
    (AU : TestId) (pop : PopulationId)
    (conditions : SingleHTPremises ctx ψ L U r h y AU pop ((ModalFormula.neg L.possible).conj U.possible)) :
    ValidTriple ctx (singlePre ψ) (.command (.test r h y AU pop))
      (singlePost ψ r (leaf Γ h y AU pop) U) :=
  derivation_sound (upHT_derivable ctx ψ L U r h y AU pop conditions)

/-- Source meaningfulness survives in the two-HT postcondition. -/
theorem twoHT_post_meaningful (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (L U : ModalFormula Γ) (r : Variable .real .observable) (h : HypothesisId) (y : DatasetExpr)
    (AT : TestId) (pop : PopulationId)
    (conditions : SingleHTPremises ctx ψ L U r h y AT pop (L.possible.conj U.possible)) :
    AssertionEntails ctx (singlePost ψ r (leaf Γ h y AT pop) (L.disj U))
      (.modal ((modelRequirementsFormula (leaf Γ h y AT pop)).conj
        (L.possible.conj U.possible))) :=
  AssertionEntails.trans (AssertionEntails.conj_left ctx ψ _) conditions.meaningful

/-- Source meaningfulness survives in the low-HT postcondition. -/
theorem lowHT_post_meaningful (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (L U : ModalFormula Γ) (r : Variable .real .observable) (h : HypothesisId) (y : DatasetExpr)
    (AL : TestId) (pop : PopulationId)
    (conditions : SingleHTPremises ctx ψ L U r h y AL pop (L.possible.conj (.neg U.possible))) :
    AssertionEntails ctx (singlePost ψ r (leaf Γ h y AL pop) L)
      (.modal ((modelRequirementsFormula (leaf Γ h y AL pop)).conj
        (L.possible.conj (.neg U.possible)))) :=
  AssertionEntails.trans (AssertionEntails.conj_left ctx ψ _) conditions.meaningful

/-- Source meaningfulness survives in the up-HT postcondition. -/
theorem upHT_post_meaningful (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (L U : ModalFormula Γ) (r : Variable .real .observable) (h : HypothesisId) (y : DatasetExpr)
    (AU : TestId) (pop : PopulationId)
    (conditions : SingleHTPremises ctx ψ L U r h y AU pop ((ModalFormula.neg L.possible).conj U.possible)) :
    AssertionEntails ctx (singlePost ψ r (leaf Γ h y AU pop) U)
      (.modal ((modelRequirementsFormula (leaf Γ h y AU pop)).conj
        ((ModalFormula.neg L.possible).conj U.possible))) :=
  AssertionEntails.trans (AssertionEntails.conj_left ctx ψ _) conditions.meaningful

/-! ## Multiple-test bookkeeping -/

/-- The second-test bookkeeping preimage, proved from the actual step effect.
The first belief and the first (now obsolete) singleton ledger are used only as
hypotheses about the source state; they are never framed through the write. -/
theorem multi_pre_entails_book_preimage (ctx : ProgramContext D) {Γ : List GhostSort}
    (ψ : Assertion Γ) (φ1 : ModalFormula Γ) (mode : StatisticalMode)
    (r1 r2 : Variable .real .observable) (h1 h2 : HypothesisId) (y1 y2 : DatasetExpr)
    (A1 A2 : TestId) (pop1 pop2 : PopulationId) (k : CouplingId)
    (frameψ2 : AssertionTestFrame r2 ψ) (outputs_ne : r1.id ≠ r2.id)
    (dataset_fresh : ∀ r ∈ [r1, r2], ∀ y ∈ [y1, y2], ProgramCell.value .real r.id ∉ y.reads)
    (inputs : AssertionEntails ctx ψ (.modal ((ModalFormula.atom (.defined (y1.toAssertionTerm Γ))).conj
      (.atom (.defined (y2.toAssertionTerm Γ)))))) :
    AssertionEntails ctx (multiPre ψ r1 (leaf Γ h1 y1 A1 pop1) φ1)
      ((Primitive.test r2 h2 y2 A2 pop2).preimage
        (multiBook ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2)
          (StatisticalMode.combined mode k (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2)))) := by
  intro env world pre
  have hψ : referenceAssertionSatisfaction ctx.interpretation ctx.model env world ψ := pre.2.1
  have hinputs := (inputs env world ⟨pre.1, hψ⟩).2
  have defined1 : ∃ value, evalTerm ctx.interpretation ctx.model env
      (semanticView ctx.model.dynamics world) (y1.toAssertionTerm Γ) = some value := hinputs.1
  have defined2 : ∃ value, evalTerm ctx.interpretation ctx.model env
      (semanticView ctx.model.dynamics world) (y2.toAssertionTerm Γ) = some value := hinputs.2
  obtain ⟨d1, hd1⟩ := defined1
  obtain ⟨d2, hd2⟩ := defined2
  have hdata1 : evalDatasetExpr ctx.interpretation world.current.visible y1 = some d1 :=
    (evalTerm_toDatasetExpr ctx.interpretation ctx.model env
      (semanticView ctx.model.dynamics world) y1).symm.trans hd1
  have hdata2 : evalDatasetExpr ctx.interpretation world.current.visible y2 = some d2 :=
    (evalTerm_toDatasetExpr ctx.interpretation ctx.model env
      (semanticView ctx.model.dynamics world) y2).symm.trans hd2
  have hhist1 : world.current.history = ({(d1, A1)} : History D) := by
    have h := (exactHistory_iff_ledger ctx.interpretation ctx.model env world
      (leaf Γ h1 y1 A1 pop1)).mp pre.2.2.1
    simp only [evalTestHistory_leaf, hd1, Option.map_some, Option.some.injEq] at h
    exact h.symm
  refine ⟨pre.1, ?_⟩
  have preimageForm : (Primitive.test r2 h2 y2 A2 pop2).preimage
        (multiBook ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2)
          (StatisticalMode.combined mode k (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2)))
      = liberalPreimage ((Primitive.test r2 h2 y2 A2 pop2).viewTerm Γ)
          (multiBook ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2)
            (StatisticalMode.combined mode k (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2))) := rfl
  rw [preimageForm, reference_liberalPreimage_iff]
  intro terminal evaluated
  obtain ⟨after, step, admittedAfter, view⟩ := primitive_viewTerm_realized ctx env pre.1 evaluated
  refine ⟨?_, ?_⟩
  · rw [← view]
    exact semanticView_mem_views ctx.model admittedAfter
  · rw [← view]
    refine (reference_view_assertion_correspondence ctx.interpretation ctx.model env after
      (multiBook ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2)
        (StatisticalMode.combined mode k (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2)))).mp ?_
    have hψAfter : referenceAssertionSatisfaction ctx.interpretation ctx.model env after ψ :=
      (assertion_test_frame frameψ2 env pre.1 step).mp hψ
    have hleaf1 : evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics after)
        (y1.toAssertionTerm Γ) = some d1 :=
      test_step_dataset_value ctx env step (dataset_fresh r2 (by simp) y1 (by simp)) hdata1
    have hleaf2 : evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics after)
        (y2.toAssertionTerm Γ) = some d2 :=
      test_step_dataset_value ctx env step (dataset_fresh r2 (by simp) y2 (by simp)) hdata2
    have hhistAfter : after.current.history = ({(d1, A1)} : History D) + {(d2, A2)} := by
      rw [(test_step_report hdata2 step).2.2.2.1, hhist1]
    have hledger : referenceModalSatisfaction ctx.interpretation ctx.model env after
        (exactHistory (StatisticalMode.combined mode k (leaf Γ h1 y1 A1 pop1)
          (leaf Γ h2 y2 A2 pop2))) := by
      refine (exactHistory_iff_ledger ctx.interpretation ctx.model env after _).mpr ?_
      have leaf1 : evalTestHistory ctx.interpretation ctx.model env
          (semanticView ctx.model.dynamics after) (leaf Γ h1 y1 A1 pop1) =
            some ({(d1, A1)} : History D) := by
        simp [evalTestHistory_leaf, hleaf1]
      have leaf2 : evalTestHistory ctx.interpretation ctx.model env
          (semanticView ctx.model.dynamics after) (leaf Γ h2 y2 A2 pop2) =
            some ({(d2, A2)} : History D) := by
        simp [evalTestHistory_leaf, hleaf2]
      rw [evalTestHistory_combined ctx env (semanticView ctx.model.dynamics after) mode k _ _ _ _
        leaf1 leaf2, hhistAfter]
    obtain ⟨v1, hreport1, hpvalue1⟩ :=
      (stored_iff ctx env world r1 (leaf Γ h1 y1 A1 pop1)).mp pre.2.2.2.2.1
    have hrelation1 : (ctx.interpretation.tests h1 A1).tailProbability d1 = v1 := by
      rw [evalTerm_pvalue_leaf_some ctx env (semanticView ctx.model.dynamics world) h1 y1 A1 pop1
        d1 hd1] at hpvalue1
      exact Option.some.inj hpvalue1
    have hbefore1 : world.current.visible.memory .real r1.id = some v1 := by
      simp only [evalTerm_report, semanticView] at hreport1
      exact hreport1
    have hreport1After : evalTerm ctx.interpretation ctx.model env
        (semanticView ctx.model.dynamics after) (report Γ r1) = some v1 := by
      rw [evalTerm_report]
      exact (test_step_read_ne ctx (r := r2) (x := r1) outputs_ne step).trans hbefore1
    have hpvalue1After : evalTerm ctx.interpretation ctx.model env
        (semanticView ctx.model.dynamics after) (.pvalue (leaf Γ h1 y1 A1 pop1)) = some v1 := by
      rw [evalTerm_pvalue_leaf_some ctx env (semanticView ctx.model.dynamics after) h1 y1 A1 pop1
        d1 hleaf1, hrelation1]
    have hstored1 : referenceAssertionSatisfaction ctx.interpretation ctx.model env after
        (stored r1 (leaf Γ h1 y1 A1 pop1)) :=
      (stored_iff ctx env after r1 (leaf Γ h1 y1 A1 pop1)).mpr ⟨v1, hreport1After, hpvalue1After⟩
    have hrange1 : referenceAssertionSatisfaction ctx.interpretation ctx.model env after
        (reportRange Γ r1) := by
      rw [← hrelation1] at hreport1After
      exact reportRange_of_eval ctx env after r1 _ hreport1After
        (NumericTest.tailProbability_nonneg (ctx.interpretation.tests h1 A1) d1)
        (NumericTest.tailProbability_le_one (ctx.interpretation.tests h1 A1) d1)
    have hreport2 : evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics after)
        (report Γ r2) = some ((ctx.interpretation.tests h2 A2).tailProbability d2) := by
      rw [evalTerm_report]
      exact (test_step_report hdata2 step).2.1
    have hpvalue2 : evalTerm ctx.interpretation ctx.model env
        (semanticView ctx.model.dynamics after) (.pvalue (leaf Γ h2 y2 A2 pop2)) =
          some ((ctx.interpretation.tests h2 A2).tailProbability d2) :=
      evalTerm_pvalue_leaf_some ctx env (semanticView ctx.model.dynamics after) h2 y2 A2 pop2
        d2 hleaf2
    have hstored2 : referenceAssertionSatisfaction ctx.interpretation ctx.model env after
        (stored r2 (leaf Γ h2 y2 A2 pop2)) :=
      (stored_iff ctx env after r2 (leaf Γ h2 y2 A2 pop2)).mpr ⟨_, hreport2, hpvalue2⟩
    have hrange2 : referenceAssertionSatisfaction ctx.interpretation ctx.model env after
        (reportRange Γ r2) :=
      reportRange_of_eval ctx env after r2 _ hreport2
        (NumericTest.tailProbability_nonneg (ctx.interpretation.tests h2 A2) d2)
        (NumericTest.tailProbability_le_one (ctx.interpretation.tests h2 A2) d2)
    exact ⟨hψAfter, hledger, hstored1, hstored2, hrange1, hrange2⟩

/-! ## Multiple-test belief -/

/-- The multiple-test disjunction bookkeeping postcondition implies its belief
postcondition: the actual coupled union bound is restated with the two stored
reports, validated on every admitted accessible alternative. -/
theorem multiDisj_book_entails_post (ctx : ProgramContext D) {Γ : List GhostSort}
    (ψ : Assertion Γ) (φ1 φ2 : ModalFormula Γ) (r1 r2 : Variable .real .observable)
    (h1 h2 : HypothesisId) (y1 y2 : DatasetExpr) (A1 A2 : TestId) (pop1 pop2 : PopulationId)
    (k : CouplingId)
    (conditions : MultiHTPremises ctx ψ φ1 φ2 r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k .disj) :
    AssertionEntails ctx
      (multiBook ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2)
        (TestExpression.disj k (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2)))
      (multiDisjPost ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2) k φ1 φ2) := by
  intro env world book
  have hobs1 : ObservableTestExpression ctx.interpretation ctx.model env (leaf Γ h1 y1 A1 pop1) :=
    observableTest_leaf ctx env h1 y1 A1 pop1
  have hobs2 : ObservableTestExpression ctx.interpretation ctx.model env (leaf Γ h2 y2 A2 pop2) :=
    observableTest_leaf ctx env h2 y2 A2 pop2
  have hleft : referenceAssertionSatisfaction ctx.interpretation ctx.model env world
      (stored r1 (leaf Γ h1 y1 A1 pop1)) := book.2.2.2.1
  have hright : referenceAssertionSatisfaction ctx.interpretation ctx.model env world
      (stored r2 (leaf Γ h2 y2 A2 pop2)) := book.2.2.2.2.1
  have hhistory : referenceModalSatisfaction ctx.interpretation ctx.model env world
      (exactHistory (TestExpression.disj k (leaf Γ h1 y1 A1 pop1)
        (leaf Γ h2 y2 A2 pop2))) := book.2.2.1
  obtain ⟨v1, hreport1, hpvalue1⟩ := (stored_iff ctx env world r1 (leaf Γ h1 y1 A1 pop1)).mp hleft
  obtain ⟨v2, hreport2, hpvalue2⟩ := (stored_iff ctx env world r2 (leaf Γ h2 y2 A2 pop2)).mp hright
  obtain ⟨d1, heval1, -⟩ := (pvalue_leaf_some_iff ctx env (semanticView ctx.model.dynamics world)
    h1 y1 A1 pop1 v1).mp hpvalue1
  obtain ⟨d2, heval2, -⟩ := (pvalue_leaf_some_iff ctx env (semanticView ctx.model.dynamics world)
    h2 y2 A2 pop2 v2).mp hpvalue2
  have ha : evalNumericalEvent ctx.interpretation ctx.model env
      (semanticView ctx.model.dynamics world) (leaf Γ h1 y1 A1 pop1) =
        some (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h1 A1) d1⟩ :
          PackedNumericalEvent) :=
    evalNumericalEvent_leaf_some ctx env (semanticView ctx.model.dynamics world) h1 y1 A1 pop1
      d1 heval1
  have hb : evalNumericalEvent ctx.interpretation ctx.model env
      (semanticView ctx.model.dynamics world) (leaf Γ h2 y2 A2 pop2) =
        some (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h2 A2) d2⟩ :
          PackedNumericalEvent) :=
    evalNumericalEvent_leaf_some ctx env (semanticView ctx.model.dynamics world) h2 y2 A2 pop2
      d2 heval2
  have hc : ctx.interpretation.couplings k
      (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h1 A1) d1⟩ : PackedNumericalEvent).1
      (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h2 A2) d2⟩ : PackedNumericalEvent).1
      (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h1 A1) d1⟩ : PackedNumericalEvent).2.law
      (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h2 A2) d2⟩ : PackedNumericalEvent).2.law =
        some conditions.scientific.coupling :=
    conditions.scientific.selected
  have coupled := belief_combined_disj ctx.interpretation ctx.model env world k
    (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2) (ModalFormula.disj φ1 φ2) hobs1 hobs2
    (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h1 A1) d1⟩ : PackedNumericalEvent)
    (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h2 A2) d2⟩ : PackedNumericalEvent)
    conditions.scientific.coupling ha hb hc hhistory
  have replacement : ∀ u, Admitted ctx.model.dynamics u → Accessible world u →
      referenceModalSatisfaction ctx.interpretation ctx.model env u
        (pvalueAtom Comparison.lessEqual
          (.realAdd (.pvalue (leaf Γ h1 y1 A1 pop1)) (.pvalue (leaf Γ h2 y2 A2 pop2)))
          (TestExpression.disj k (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2))) →
      referenceModalSatisfaction ctx.interpretation ctx.model env u
        (pvalueAtom Comparison.lessEqual (.realAdd (report Γ r1) (report Γ r2))
          (TestExpression.disj k (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2))) := by
    intro u admitted accessible hypothesis
    obtain ⟨w1, hreport1u, hpvalue1u⟩ := (stored_iff ctx env u r1 (leaf Γ h1 y1 A1 pop1)).mp
      (stored_at_accessible ctx env r1 (leaf Γ h1 y1 A1 pop1) hobs1 accessible hleft)
    obtain ⟨w2, hreport2u, hpvalue2u⟩ := (stored_iff ctx env u r2 (leaf Γ h2 y2 A2 pop2)).mp
      (stored_at_accessible ctx env r2 (leaf Γ h2 y2 A2 pop2) hobs2 accessible hright)
    obtain ⟨tested, bound, htested, hbound, comparison⟩ := hypothesis
    have sum : evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics u)
        (.realAdd (report Γ r1) (report Γ r2)) =
        evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics u)
          (.realAdd (.pvalue (leaf Γ h1 y1 A1 pop1)) (.pvalue (leaf Γ h2 y2 A2 pop2))) := by
      change (do
          let a ← evalTerm ctx.interpretation ctx.model env
            (semanticView ctx.model.dynamics u) (report Γ r1)
          let b ← evalTerm ctx.interpretation ctx.model env
            (semanticView ctx.model.dynamics u) (report Γ r2)
          pure (a + b)) = (do
          let a ← evalTerm ctx.interpretation ctx.model env
            (semanticView ctx.model.dynamics u) (.pvalue (leaf Γ h1 y1 A1 pop1))
          let b ← evalTerm ctx.interpretation ctx.model env
            (semanticView ctx.model.dynamics u) (.pvalue (leaf Γ h2 y2 A2 pop2))
          pure (a + b))
      simp [hreport1u, hpvalue1u, hreport2u, hpvalue2u]
    exact ⟨tested, bound, htested, sum.trans hbound, comparison⟩
  have belief := belief_of_pvalue_implication ctx.interpretation ctx.model env world
    Comparison.lessEqual Comparison.lessEqual
    (.realAdd (.pvalue (leaf Γ h1 y1 A1 pop1)) (.pvalue (leaf Γ h2 y2 A2 pop2)))
    (.realAdd (report Γ r1) (report Γ r2))
    (TestExpression.disj k (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2))
    (ModalFormula.disj φ1 φ2) replacement coupled
  exact ⟨book.1, book.2.1, book.2.2.1, belief⟩

/-- The multiple-test conjunction bookkeeping postcondition implies its belief
postcondition: the actual coupled intersection bound is restated with the two
stored reports as an actual minimum. -/
theorem multiConj_book_entails_post (ctx : ProgramContext D) {Γ : List GhostSort}
    (ψ : Assertion Γ) (φ1 φ2 : ModalFormula Γ) (r1 r2 : Variable .real .observable)
    (h1 h2 : HypothesisId) (y1 y2 : DatasetExpr) (A1 A2 : TestId) (pop1 pop2 : PopulationId)
    (k : CouplingId)
    (conditions : MultiHTPremises ctx ψ φ1 φ2 r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k .conj) :
    AssertionEntails ctx
      (multiBook ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2)
        (TestExpression.conj k (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2)))
      (multiConjPost ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2) k φ1 φ2) := by
  intro env world book
  have hobs1 : ObservableTestExpression ctx.interpretation ctx.model env (leaf Γ h1 y1 A1 pop1) :=
    observableTest_leaf ctx env h1 y1 A1 pop1
  have hobs2 : ObservableTestExpression ctx.interpretation ctx.model env (leaf Γ h2 y2 A2 pop2) :=
    observableTest_leaf ctx env h2 y2 A2 pop2
  have hleft : referenceAssertionSatisfaction ctx.interpretation ctx.model env world
      (stored r1 (leaf Γ h1 y1 A1 pop1)) := book.2.2.2.1
  have hright : referenceAssertionSatisfaction ctx.interpretation ctx.model env world
      (stored r2 (leaf Γ h2 y2 A2 pop2)) := book.2.2.2.2.1
  have hhistory : referenceModalSatisfaction ctx.interpretation ctx.model env world
      (exactHistory (TestExpression.conj k (leaf Γ h1 y1 A1 pop1)
        (leaf Γ h2 y2 A2 pop2))) := book.2.2.1
  obtain ⟨v1, hreport1, hpvalue1⟩ := (stored_iff ctx env world r1 (leaf Γ h1 y1 A1 pop1)).mp hleft
  obtain ⟨v2, hreport2, hpvalue2⟩ := (stored_iff ctx env world r2 (leaf Γ h2 y2 A2 pop2)).mp hright
  obtain ⟨d1, heval1, -⟩ := (pvalue_leaf_some_iff ctx env (semanticView ctx.model.dynamics world)
    h1 y1 A1 pop1 v1).mp hpvalue1
  obtain ⟨d2, heval2, -⟩ := (pvalue_leaf_some_iff ctx env (semanticView ctx.model.dynamics world)
    h2 y2 A2 pop2 v2).mp hpvalue2
  have ha : evalNumericalEvent ctx.interpretation ctx.model env
      (semanticView ctx.model.dynamics world) (leaf Γ h1 y1 A1 pop1) =
        some (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h1 A1) d1⟩ :
          PackedNumericalEvent) :=
    evalNumericalEvent_leaf_some ctx env (semanticView ctx.model.dynamics world) h1 y1 A1 pop1
      d1 heval1
  have hb : evalNumericalEvent ctx.interpretation ctx.model env
      (semanticView ctx.model.dynamics world) (leaf Γ h2 y2 A2 pop2) =
        some (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h2 A2) d2⟩ :
          PackedNumericalEvent) :=
    evalNumericalEvent_leaf_some ctx env (semanticView ctx.model.dynamics world) h2 y2 A2 pop2
      d2 heval2
  have hc : ctx.interpretation.couplings k
      (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h1 A1) d1⟩ : PackedNumericalEvent).1
      (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h2 A2) d2⟩ : PackedNumericalEvent).1
      (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h1 A1) d1⟩ : PackedNumericalEvent).2.law
      (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h2 A2) d2⟩ : PackedNumericalEvent).2.law =
        some conditions.scientific.coupling :=
    conditions.scientific.selected
  have coupled := belief_combined_conj ctx.interpretation ctx.model env world k
    (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2) (ModalFormula.conj φ1 φ2) hobs1 hobs2
    (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h1 A1) d1⟩ : PackedNumericalEvent)
    (⟨.real, NumericalEvent.tail (ctx.interpretation.tests h2 A2) d2⟩ : PackedNumericalEvent)
    conditions.scientific.coupling ha hb hc hhistory
  have replacement : ∀ u, Admitted ctx.model.dynamics u → Accessible world u →
      referenceModalSatisfaction ctx.interpretation ctx.model env u
        (pvalueAtom Comparison.lessEqual
          (.realMin (.pvalue (leaf Γ h1 y1 A1 pop1)) (.pvalue (leaf Γ h2 y2 A2 pop2)))
          (TestExpression.conj k (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2))) →
      referenceModalSatisfaction ctx.interpretation ctx.model env u
        (pvalueAtom Comparison.lessEqual (.realMin (report Γ r1) (report Γ r2))
          (TestExpression.conj k (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2))) := by
    intro u admitted accessible hypothesis
    obtain ⟨w1, hreport1u, hpvalue1u⟩ := (stored_iff ctx env u r1 (leaf Γ h1 y1 A1 pop1)).mp
      (stored_at_accessible ctx env r1 (leaf Γ h1 y1 A1 pop1) hobs1 accessible hleft)
    obtain ⟨w2, hreport2u, hpvalue2u⟩ := (stored_iff ctx env u r2 (leaf Γ h2 y2 A2 pop2)).mp
      (stored_at_accessible ctx env r2 (leaf Γ h2 y2 A2 pop2) hobs2 accessible hright)
    obtain ⟨tested, bound, htested, hbound, comparison⟩ := hypothesis
    have minimum : evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics u)
        (.realMin (report Γ r1) (report Γ r2)) =
        evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics u)
          (.realMin (.pvalue (leaf Γ h1 y1 A1 pop1)) (.pvalue (leaf Γ h2 y2 A2 pop2))) := by
      change (do
          let a ← evalTerm ctx.interpretation ctx.model env
            (semanticView ctx.model.dynamics u) (report Γ r1)
          let b ← evalTerm ctx.interpretation ctx.model env
            (semanticView ctx.model.dynamics u) (report Γ r2)
          pure (min a b)) = (do
          let a ← evalTerm ctx.interpretation ctx.model env
            (semanticView ctx.model.dynamics u) (.pvalue (leaf Γ h1 y1 A1 pop1))
          let b ← evalTerm ctx.interpretation ctx.model env
            (semanticView ctx.model.dynamics u) (.pvalue (leaf Γ h2 y2 A2 pop2))
          pure (min a b))
      simp [hreport1u, hpvalue1u, hreport2u, hpvalue2u]
    exact ⟨tested, bound, htested, minimum.trans hbound, comparison⟩
  have belief := belief_of_pvalue_implication ctx.interpretation ctx.model env world
    Comparison.lessEqual Comparison.lessEqual
    (.realMin (.pvalue (leaf Γ h1 y1 A1 pop1)) (.pvalue (leaf Γ h2 y2 A2 pop2)))
    (.realMin (report Γ r1) (report Γ r2))
    (TestExpression.conj k (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2))
    (ModalFormula.conj φ1 φ2) replacement coupled
  exact ⟨book.1, book.2.1, book.2.2.1, belief⟩

/-! ## The two multiple-test rules -/

/-- Multiple-test disjunction rule, derived from `test` and `consequence`. -/
theorem multDisj_derivable (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (φ1 φ2 : ModalFormula Γ) (r1 r2 : Variable .real .observable) (h1 h2 : HypothesisId)
    (y1 y2 : DatasetExpr) (A1 A2 : TestId) (pop1 pop2 : PopulationId) (k : CouplingId)
    (conditions : MultiHTPremises ctx ψ φ1 φ2 r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k .disj) :
    Derivation ctx (multiPre ψ r1 (leaf Γ h1 y1 A1 pop1) φ1)
      (.command (.test r2 h2 y2 A2 pop2))
      (multiDisjPost ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2) k φ1 φ2) :=
  Derivation.consequence
    (multi_pre_entails_book_preimage ctx ψ φ1 .disj r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k
      conditions.frameψ2 conditions.outputs_ne conditions.dataset_fresh conditions.inputs)
    (Derivation.test r2 h2 y2 A2 pop2 (multiBook ψ r1 r2 (leaf Γ h1 y1 A1 pop1)
      (leaf Γ h2 y2 A2 pop2) (TestExpression.disj k (leaf Γ h1 y1 A1 pop1)
        (leaf Γ h2 y2 A2 pop2))))
    (multiDisj_book_entails_post ctx ψ φ1 φ2 r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k conditions)

/-- Multiple-test conjunction rule, derived from `test` and `consequence`. -/
theorem multConj_derivable (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (φ1 φ2 : ModalFormula Γ) (r1 r2 : Variable .real .observable) (h1 h2 : HypothesisId)
    (y1 y2 : DatasetExpr) (A1 A2 : TestId) (pop1 pop2 : PopulationId) (k : CouplingId)
    (conditions : MultiHTPremises ctx ψ φ1 φ2 r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k .conj) :
    Derivation ctx (multiPre ψ r1 (leaf Γ h1 y1 A1 pop1) φ1)
      (.command (.test r2 h2 y2 A2 pop2))
      (multiConjPost ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2) k φ1 φ2) :=
  Derivation.consequence
    (multi_pre_entails_book_preimage ctx ψ φ1 .conj r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k
      conditions.frameψ2 conditions.outputs_ne conditions.dataset_fresh conditions.inputs)
    (Derivation.test r2 h2 y2 A2 pop2 (multiBook ψ r1 r2 (leaf Γ h1 y1 A1 pop1)
      (leaf Γ h2 y2 A2 pop2) (TestExpression.conj k (leaf Γ h1 y1 A1 pop1)
        (leaf Γ h2 y2 A2 pop2))))
    (multiConj_book_entails_post ctx ψ φ1 φ2 r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k conditions)

theorem multDisj_sound (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (φ1 φ2 : ModalFormula Γ) (r1 r2 : Variable .real .observable) (h1 h2 : HypothesisId)
    (y1 y2 : DatasetExpr) (A1 A2 : TestId) (pop1 pop2 : PopulationId) (k : CouplingId)
    (conditions : MultiHTPremises ctx ψ φ1 φ2 r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k .disj) :
    ValidTriple ctx (multiPre ψ r1 (leaf Γ h1 y1 A1 pop1) φ1)
      (.command (.test r2 h2 y2 A2 pop2))
      (multiDisjPost ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2) k φ1 φ2) :=
  derivation_sound (multDisj_derivable ctx ψ φ1 φ2 r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k
    conditions)

theorem multConj_sound (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (φ1 φ2 : ModalFormula Γ) (r1 r2 : Variable .real .observable) (h1 h2 : HypothesisId)
    (y1 y2 : DatasetExpr) (A1 A2 : TestId) (pop1 pop2 : PopulationId) (k : CouplingId)
    (conditions : MultiHTPremises ctx ψ φ1 φ2 r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k .conj) :
    ValidTriple ctx (multiPre ψ r1 (leaf Γ h1 y1 A1 pop1) φ1)
      (.command (.test r2 h2 y2 A2 pop2))
      (multiConjPost ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2) k φ1 φ2) :=
  derivation_sound (multConj_derivable ctx ψ φ1 φ2 r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k
    conditions)

/-- The printed second-test meaningfulness survives in the disjunction postcondition. -/
theorem multDisj_post_meaningful (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (φ1 φ2 : ModalFormula Γ) (r1 r2 : Variable .real .observable) (h1 h2 : HypothesisId)
    (y1 y2 : DatasetExpr) (A1 A2 : TestId) (pop1 pop2 : PopulationId) (k : CouplingId)
    (conditions : MultiHTPremises ctx ψ φ1 φ2 r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k .disj) :
    AssertionEntails ctx
      (multiDisjPost ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2) k φ1 φ2)
      (.modal ((modelRequirementsFormula (leaf Γ h2 y2 A2 pop2)).conj
        (ModalFormula.possible (ModalFormula.disj φ1 φ2)))) :=
  AssertionEntails.trans (AssertionEntails.conj_left ctx ψ _) conditions.meaningful

/-- The full joint scientific meaningfulness survives in the disjunction postcondition. -/
theorem multDisj_pair_meaningful (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (φ1 φ2 : ModalFormula Γ) (r1 r2 : Variable .real .observable) (h1 h2 : HypothesisId)
    (y1 y2 : DatasetExpr) (A1 A2 : TestId) (pop1 pop2 : PopulationId) (k : CouplingId)
    (conditions : MultiHTPremises ctx ψ φ1 φ2 r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k .disj) :
    AssertionEntails ctx
      (multiDisjPost ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2) k φ1 φ2)
      (.modal (modelRequirementsFormula (StatisticalMode.combined .disj k
        (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2)))) :=
  AssertionEntails.trans (AssertionEntails.conj_left ctx ψ _) conditions.pair_meaningful

/-- The printed second-test meaningfulness survives in the conjunction postcondition. -/
theorem multConj_post_meaningful (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (φ1 φ2 : ModalFormula Γ) (r1 r2 : Variable .real .observable) (h1 h2 : HypothesisId)
    (y1 y2 : DatasetExpr) (A1 A2 : TestId) (pop1 pop2 : PopulationId) (k : CouplingId)
    (conditions : MultiHTPremises ctx ψ φ1 φ2 r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k .conj) :
    AssertionEntails ctx
      (multiConjPost ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2) k φ1 φ2)
      (.modal ((modelRequirementsFormula (leaf Γ h2 y2 A2 pop2)).conj
        (ModalFormula.possible (ModalFormula.conj φ1 φ2)))) :=
  AssertionEntails.trans (AssertionEntails.conj_left ctx ψ _) conditions.meaningful

/-- The full joint scientific meaningfulness survives in the conjunction postcondition. -/
theorem multConj_pair_meaningful (ctx : ProgramContext D) {Γ : List GhostSort} (ψ : Assertion Γ)
    (φ1 φ2 : ModalFormula Γ) (r1 r2 : Variable .real .observable) (h1 h2 : HypothesisId)
    (y1 y2 : DatasetExpr) (A1 A2 : TestId) (pop1 pop2 : PopulationId) (k : CouplingId)
    (conditions : MultiHTPremises ctx ψ φ1 φ2 r1 r2 h1 h2 y1 y2 A1 A2 pop1 pop2 k .conj) :
    AssertionEntails ctx
      (multiConjPost ψ r1 r2 (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2) k φ1 φ2)
      (.modal (modelRequirementsFormula (StatisticalMode.combined .conj k
        (leaf Γ h1 y1 A1 pop1) (leaf Γ h2 y2 A2 pop2)))) :=
  AssertionEntails.trans (AssertionEntails.conj_left ctx ψ _) conditions.pair_meaningful

end

end Lara.BHL
