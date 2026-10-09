import Lara.Examples.BHLStatistical

/-!
Exact rational statistical-belief checking for the named binary endpoint family.
The checker compares the complete multiset ledger and a finite null event mass.
Its correspondence is with reference satisfaction, not general assertion validity:
the vocabulary consists of a single test at dataId and the accounted named pair.
-/

namespace Lara.Examples.BHLFiniteBelief

open Lara.BHL
open Lara.Examples.BHLBinaryModel
open Lara.Examples.BHLBinaryScience
open Lara.Examples.BHLBinaryRuns
open Lara.Examples.BHLSoundnessScience (allowed hiddenMemory theta alternative singleTest pairId sample)
open Lara.Examples.BHLExecution (Snapshot dataId aliasId report)
open Lara.Examples.BHLBelief (hypothesisId populationId)

/-- Actual run endpoints, including the hidden extra test. -/
inductive RunKind where
  | single (name : TestId)
  | pair
  | hidden
  deriving DecidableEq

/-- A closed test vocabulary; singles retain arbitrary kernel test identities. -/
inductive Bundle where
  | single (name : TestId)
  | disj
  | conj
  deriving DecidableEq

def endpointSnapshot (run : RunKind) (first second : Bool) : Snapshot :=
  match run with
  | .single name => singleFinal first second name
  | .pair => pairFinal first second
  | .hidden => hiddenFinal first second

def bundleHistory (bundle : Bundle) (first second : Bool) : History Bool :=
  match bundle with
  | .single name => {(first, name)}
  | .disj | .conj => {(first, firstId)} + {(second, secondId)}

/-- All masses are actual finite event sums, never hardcoded answer tables. -/
def eventMass (bundle : Bundle) (first second : Bool) : ℚ :=
  match bundle with
  | .single _ => Tests.Binary.pvalue first
  | .disj => FiniteProbability.eventMass Tests.Binary.nullJoint
      (fun p => (p.1 || !first) || (p.2 || !second))
  | .conj => FiniteProbability.eventMass Tests.Binary.nullJoint
      (fun p => (p.1 || !first) && (p.2 || !second))

def compareRational : Comparison → ℚ → ℚ → Prop
  | .equal => Eq
  | .less => LT.lt
  | .lessEqual => LE.le
  | .greater => fun a b => b < a
  | .greaterEqual => fun a b => b ≤ a

instance (comparison : Comparison) (a b : ℚ) : Decidable (compareRational comparison a b) := by
  cases comparison <;> unfold compareRational <;> infer_instance

/-- Full-ledger accounting AND the comparison with the measured null event. -/
def checkBelief (run : RunKind) (bundle : Bundle) (first second : Bool)
    (comparison : Comparison) (threshold : ℚ) : Bool :=
  decide ((endpointSnapshot run first second).ledger = bundleHistory bundle first second ∧
    compareRational comparison (eventMass bundle first second) threshold)

def checkSingle (name : TestId) (first second : Bool)
    (comparison : Comparison) (threshold : ℚ) : Bool :=
  checkBelief (.single name) (.single name) first second comparison threshold

def checkDisjunction (first second : Bool) (comparison : Comparison) (threshold : ℚ) : Bool :=
  checkBelief .pair .disj first second comparison threshold

def checkConjunction (first second : Bool) (comparison : Comparison) (threshold : ℚ) : Bool :=
  checkBelief .pair .conj first second comparison threshold

def checkHiddenSingle (first second : Bool) (comparison : Comparison) (threshold : ℚ) : Bool :=
  checkBelief .hidden (.single firstId) first second comparison threshold

noncomputable section

def endpointWorld (run : RunKind) (n : Int) (first second : Bool) : World Bool Primitive :=
  match run with
  | .single name => singleWorld n first second name
  | .pair => pairWorld n first second
  | .hidden => hiddenWorld n first second

def bundleTest (bundle : Bundle) : TestExpression Γ :=
  match bundle with
  | .single name => singleTest name
  | .disj => .disj pairId firstTest secondTest
  | .conj => .conj pairId firstTest secondTest

theorem eventMass_disj (first second : Bool) :
    eventMass .disj first second = Tests.Binary.pvalue first + Tests.Binary.pvalue second -
      Tests.Binary.pvalue first * Tests.Binary.pvalue second := by
  cases first <;> cases second <;>
    norm_num [eventMass, FiniteProbability.eventMass, Tests.Binary.nullJoint,
      FiniteProbability.product_mass, Tests.Binary.null, Fintype.sum_prod_type, Fintype.sum_bool]

theorem eventMass_conj (first second : Bool) :
    eventMass .conj first second = Tests.Binary.pvalue first * Tests.Binary.pvalue second := by
  cases first <;> cases second <;>
    norm_num [eventMass, FiniteProbability.eventMass, Tests.Binary.nullJoint,
      FiniteProbability.product_mass, Tests.Binary.null, Fintype.sum_prod_type, Fintype.sum_bool]

theorem eventMass_disj_correct (first second : Bool) :
    eventProbability (Tests.Binary.nullCoupling .two .two).joint
      (Tests.Binary.unionEvent .two .two first second) = (eventMass .disj first second : ℝ) := by
  rw [Tests.Binary.union_probability, eventMass_disj]

theorem eventMass_conj_correct (first second : Bool) :
    eventProbability (Tests.Binary.nullCoupling .two .two).joint
      (Tests.Binary.interEvent .two .two first second) = (eventMass .conj first second : ℝ) := by
  rw [Tests.Binary.inter_probability, eventMass_conj]

theorem eventMass_single_correct (name : TestId) (first second : Bool) :
    (testFor name).tailProbability first = (eventMass (.single name) first second : ℝ) :=
  testFor_pvalue name first

theorem eventMass_true_true :
    eventMass .disj true true = 7 / 16 ∧ eventMass .conj true true = 1 / 16 := by
  norm_num [eventMass_disj, eventMass_conj]

theorem compareRational_correct (comparison : Comparison) (a b : ℚ) :
    compareRational comparison a b ↔ compareReal comparison (a : ℝ) (b : ℝ) := by
  cases comparison <;> simp only [compareRational, compareReal] <;> norm_cast

theorem endpoint_admitted (run : RunKind) (n : Int) (first second : Bool)
    (hn : allowed .two n) :
    Admitted (context .two).model.dynamics (endpointWorld run n first second) := by
  cases run with
  | single name => exact exec_admitted (single_executes .two n first second name hn)
  | pair => exact exec_admitted (pair_executes n first second hn)
  | hidden => exact exec_admitted (hidden_executes n first second hn)

theorem endpoint_accessible (run : RunKind) (a b : Int) (first second : Bool) :
    Accessible (endpointWorld run a first second) (endpointWorld run b first second) := by
  cases run <;>
    simp [endpointWorld, singleWorld, pairWorld, hiddenWorld, Lara.Examples.BHLExecution.eventWorld,
      Accessible, observeWorld, World.trace, World.extend, sampledWorld, firstSample,
      startWorld, World.start, World.current, observeState, Memory.assemble]

theorem endpoint_data (run : RunKind) (n : Int) (first second : Bool) :
    (endpointWorld run n first second).current.datasets dataId = first ∧
      (endpointWorld run n first second).current.datasets aliasId = second := by
  cases run <;>
    simp [endpointWorld, singleWorld, pairWorld, hiddenWorld, Lara.Examples.BHLExecution.eventWorld,
      singleFinal, pairFinal, hiddenFinal, runTest, initialSnapshot, dataId, aliasId]

theorem endpoint_ledger (run : RunKind) (n : Int) (first second : Bool) :
    (endpointWorld run n first second).current.history =
      (endpointSnapshot run first second).ledger := by
  cases run <;> rfl

theorem endpoint_sample (run : RunKind) (env : GhostEnv Bool Primitive Γ)
    (n : Int) (first second : Bool) :
    referenceModalSatisfaction interpretation (context .two).model env
      (endpointWorld run n first second) (sample dataId) ∧
    referenceModalSatisfaction interpretation (context .two).model env
      (endpointWorld run n first second) (sample aliasId) := by
  cases run <;>
    simp [sample, referenceModalSatisfaction, atomMeaning, evalTerm, semanticView,
      endpointWorld, singleWorld, pairWorld, hiddenWorld, Lara.Examples.BHLExecution.eventWorld,
      singleFinal, pairFinal, hiddenFinal, runTest, sampledWorld, firstSample, startWorld,
      World.samplingProvenance, World.extend, World.current, World.trace, World.start,
      initialSnapshot, State.visible, dataId, aliasId]

theorem bundle_observable (bundle : Bundle) (env : GhostEnv Bool Primitive Γ) :
    ObservableTestExpression interpretation (context .two).model env (bundleTest bundle) := by
  have hd := observationInvariant_datasetRead interpretation (context .two).model env dataId
  have ha := observationInvariant_datasetRead interpretation (context .two).model env aliasId
  cases bundle with
  | single name => exact hd
  | disj => exact ⟨hd, ha⟩
  | conj => exact ⟨hd, ha⟩

theorem bundle_history_eval (bundle : Bundle) (env : GhostEnv Bool Primitive Γ)
    (w : World Bool Primitive) :
    evalTestHistory interpretation (context .two).model env
      (semanticView (context .two).model.dynamics w) (bundleTest bundle) =
        some (bundleHistory bundle (w.current.datasets dataId) (w.current.datasets aliasId)) := by
  cases bundle <;>
    simp [bundleTest, bundleHistory, evalTestHistory, evalTestEntries, firstTest, secondTest,
      singleTest, leaf, DatasetExpr.toAssertionTerm, evalTerm, semanticView, State.visible]
  all_goals rfl

theorem bundle_pvalue_eval (bundle : Bundle) (env : GhostEnv Bool Primitive Γ)
    (w : World Bool Primitive) :
    evalTerm interpretation (context .two).model env
      (semanticView (context .two).model.dynamics w) (.pvalue (bundleTest bundle)) =
        some (eventMass bundle (w.current.datasets dataId) (w.current.datasets aliasId) : ℝ) := by
  cases bundle with
  | single name =>
      simp [bundleTest, singleTest, leaf, DatasetExpr.toAssertionTerm, evalTerm,
        evalNumericalEvent, interpretation, semanticView, State.visible, eventMass]
  | disj =>
      simp only [bundleTest, firstTest, secondTest, singleTest, leaf,
        DatasetExpr.toAssertionTerm, evalTerm, evalNumericalEvent, interpretation,
        semanticView, State.visible, Option.map_some, bind, Option.bind_some, pure, NumericalEvent.tail]
      rw [couplingFor_selected]
      change some (eventProbability (Tests.Binary.nullCoupling .two .two).joint
        (Tests.Binary.unionEvent .two .two (w.current.datasets dataId)
          (w.current.datasets aliasId))) = _
      rw [eventMass_disj_correct]
  | conj =>
      simp only [bundleTest, firstTest, secondTest, singleTest, leaf,
        DatasetExpr.toAssertionTerm, evalTerm, evalNumericalEvent, interpretation,
        semanticView, State.visible, Option.map_some, bind, Option.bind_some, pure, NumericalEvent.tail]
      rw [couplingFor_selected]
      change some (eventProbability (Tests.Binary.nullCoupling .two .two).joint
        (Tests.Binary.interEvent .two .two (w.current.datasets dataId)
          (w.current.datasets aliasId))) = _
      rw [eventMass_conj_correct]

theorem bundle_requirements_of_samples (bundle : Bundle)
    (env : GhostEnv Bool Primitive Γ) (w : World Bool Primitive)
    (hs : referenceModalSatisfaction interpretation (context .two).model env w (sample dataId) ∧
      referenceModalSatisfaction interpretation (context .two).model env w (sample aliasId)) :
    referenceModalSatisfaction interpretation (context .two).model env w
      (modelRequirementsFormula (bundleTest bundle)) := by
  have h1 := requirements_of_sample .two env w dataId firstId hs.1
  have h2 := requirements_of_sample .two env w aliasId secondId hs.2
  cases bundle with
  | single name => exact requirements_of_sample .two env w dataId name hs.1
  | disj =>
      have hc : interpretation.jointRequirements pairId w.current.memory.hidden
          [(w.current.datasets dataId, firstId, populationId),
            (w.current.datasets aliasId, secondId, populationId)] :=
        ⟨rfl, ⟨_, _, rfl, joint_population_support _ _ _⟩⟩
      simpa [bundleTest, modelRequirementsFormula, referenceModalSatisfaction, atomMeaning,
        evalTerm, modelRequirements, evalTestEntries, firstTest, secondTest, singleTest,
        leaf, DatasetExpr.toAssertionTerm, semanticView, State.visible] using
        (show modelRequirements interpretation (context .two).model env
          (semanticView (context .two).model.dynamics w) firstTest ∧
          modelRequirements interpretation (context .two).model env
            (semanticView (context .two).model.dynamics w) secondTest ∧
          interpretation.jointRequirements pairId w.current.memory.hidden
            [(w.current.datasets dataId, firstId, populationId),
              (w.current.datasets aliasId, secondId, populationId)] from
          ⟨by simpa [modelRequirementsFormula, referenceModalSatisfaction, atomMeaning,
              evalTerm, firstTest, singleTest] using h1,
           by simpa [modelRequirementsFormula, referenceModalSatisfaction, atomMeaning,
              evalTerm, secondTest] using h2, hc⟩)
  | conj =>
      have hc : interpretation.jointRequirements pairId w.current.memory.hidden
          [(w.current.datasets dataId, firstId, populationId),
            (w.current.datasets aliasId, secondId, populationId)] :=
        ⟨rfl, ⟨_, _, rfl, joint_population_support _ _ _⟩⟩
      simpa [bundleTest, modelRequirementsFormula, referenceModalSatisfaction, atomMeaning,
        evalTerm, modelRequirements, evalTestEntries, firstTest, secondTest, singleTest,
        leaf, DatasetExpr.toAssertionTerm, semanticView, State.visible] using
        (show modelRequirements interpretation (context .two).model env
          (semanticView (context .two).model.dynamics w) firstTest ∧
          modelRequirements interpretation (context .two).model env
            (semanticView (context .two).model.dynamics w) secondTest ∧
          interpretation.jointRequirements pairId w.current.memory.hidden
            [(w.current.datasets dataId, firstId, populationId),
              (w.current.datasets aliasId, secondId, populationId)] from
          ⟨by simpa [modelRequirementsFormula, referenceModalSatisfaction, atomMeaning,
              evalTerm, firstTest, singleTest] using h1,
           by simpa [modelRequirementsFormula, referenceModalSatisfaction, atomMeaning,
              evalTerm, secondTest] using h2, hc⟩)

theorem endpoint_requirements (run : RunKind) (bundle : Bundle)
    (env : GhostEnv Bool Primitive Γ) (n : Int) (first second : Bool) :
    referenceModalSatisfaction interpretation (context .two).model env
      (endpointWorld run n first second) (modelRequirementsFormula (bundleTest bundle)) :=
  bundle_requirements_of_samples bundle env _ (endpoint_sample run env n first second)

/-- Provenance is transported by actual observational accessibility; source
support holds under every hidden population, including the non-null clones. -/
theorem accessible_endpoint_requirements (run : RunKind) (bundle : Bundle)
    (env : GhostEnv Bool Primitive Γ) (n : Int) (first second : Bool)
    (w : World Bool Primitive) (ha : Accessible (endpointWorld run n first second) w) :
    referenceModalSatisfaction interpretation (context .two).model env w
      (modelRequirementsFormula (bundleTest bundle)) := by
  apply bundle_requirements_of_samples bundle env w
  have hs := endpoint_sample run env n first second
  have hd := accessible_dataset_eq ha dataId
  have hd' := accessible_dataset_eq ha aliasId
  have hp := accessible_sampling_provenance ha
  simpa only [sample, referenceModalSatisfaction, atomMeaning, evalTerm, semanticView,
    State.visible, Option.map_some, Option.some.injEq, exists_eq_left', hd, hd', hp] using hs

theorem null_alternative_false (run : RunKind) (env : GhostEnv Bool Primitive Γ)
    (first second : Bool) :
    ¬ referenceModalSatisfaction interpretation (context .two).model env
      (endpointWorld run 0 first second) (alternative : ModalFormula Γ) := by
  cases run <;>
    simp [alternative, referenceModalSatisfaction_disj, lower_iff, upper_iff,
      endpointWorld, singleWorld, pairWorld, hiddenWorld, Lara.Examples.BHLExecution.eventWorld,
      sampledWorld, firstSample, startWorld, initialSnapshot,
      Lara.Examples.BHLSoundnessScience.theta_hiddenMemory]

theorem exception_iff_check (run : RunKind) (bundle : Bundle)
    (env : GhostEnv Bool Primitive Γ) (n : Int) (first second : Bool)
    (comparison : Comparison) (threshold : ℚ) :
    referenceModalSatisfaction interpretation (context .two).model env
      (endpointWorld run n first second)
      (exception comparison (.rational threshold) (bundleTest bundle)) ↔
        checkBelief run bundle first second comparison threshold = true := by
  have hd := endpoint_data run n first second
  rw [show referenceModalSatisfaction interpretation (context .two).model env
      (endpointWorld run n first second)
      (exception comparison (.rational threshold) (bundleTest bundle)) ↔
      referenceModalSatisfaction interpretation (context .two).model env
        (endpointWorld run n first second)
        (pvalueAtom comparison (.rational threshold) (bundleTest bundle)) ∧
      referenceModalSatisfaction interpretation (context .two).model env
        (endpointWorld run n first second) (exactHistory (bundleTest bundle)) from Iff.rfl]
  rw [exactHistory_iff_ledger, bundle_history_eval, hd.1, hd.2, endpoint_ledger]
  have hp : referenceModalSatisfaction interpretation (context .two).model env
      (endpointWorld run n first second)
      (pvalueAtom comparison (.rational threshold) (bundleTest bundle)) ↔
      compareRational comparison (eventMass bundle first second) threshold := by
    change (∃ a b, evalTerm interpretation (context .two).model env
        (semanticView (context .two).model.dynamics (endpointWorld run n first second))
        (.pvalue (bundleTest bundle)) = some a ∧
        some (threshold : ℝ) = some b ∧ compareReal comparison a b) ↔ _
    rw [bundle_pvalue_eval, hd.1, hd.2]
    simp only [Option.some.injEq]
    constructor
    · rintro ⟨a, b, ha, hb, hc⟩
      cases ha
      cases hb
      exact (compareRational_correct comparison _ threshold).mpr hc
    · intro hc
      exact ⟨_, _, rfl, rfl, (compareRational_correct comparison _ threshold).mp hc⟩
  rw [hp]
  simp only [Option.some.injEq, checkBelief, decide_eq_true_eq]
  exact ⟨fun ⟨hc, hh⟩ => ⟨hh.symm, hc⟩, fun ⟨hh, hc⟩ => ⟨hc, hh.symm⟩⟩

/-- Exact reference correspondence for every threshold, comparison, input pair
and run/bundle combination in this closed endpoint vocabulary. The null clone
is independently admitted by an actual execution, not postulated by the checker. -/
theorem checkBelief_correct (run : RunKind) (bundle : Bundle)
    (env : GhostEnv Bool Primitive Γ) (n : Int) (first second : Bool)
    (comparison : Comparison) (threshold : ℚ) :
    checkBelief run bundle first second comparison threshold = true ↔
      referenceModalSatisfaction interpretation (context .two).model env
        (endpointWorld run n first second)
        (statisticalBelief comparison (.rational threshold) (bundleTest bundle)
          (alternative : ModalFormula Γ)) := by
  constructor
  · intro checked
    have hex := (exception_iff_check run bundle env n first second comparison threshold).mpr checked
    exact belief_from_observable_exception interpretation (context .two).model env
      (endpointWorld run n first second) comparison (.rational threshold) (bundleTest bundle)
      alternative (bundle_observable bundle env) (by intro _ _ _; rfl) hex.1 hex.2
  · intro belief
    have null := (statisticalBelief_unfold interpretation (context .two).model env
      (endpointWorld run n first second) comparison (.rational threshold) (bundleTest bundle)
      alternative).mp belief (endpointWorld run 0 first second)
        (endpoint_admitted run 0 first second (by simp [allowed]))
        (endpoint_accessible run n 0 first second)
    rcases null with halt | hex | hfailed
    · exact False.elim (null_alternative_false run env first second halt)
    · exact (exception_iff_check run bundle env 0 first second comparison threshold).mp hex
    · exact False.elim (hfailed (endpoint_requirements run bundle env 0 first second))

/-- Outer assertion satisfaction also accounts for admission of the actual run. -/
theorem checkBelief_satisfies (run : RunKind) (bundle : Bundle)
    (env : GhostEnv Bool Primitive Γ) (n : Int) (first second : Bool)
    (hn : allowed .two n) (comparison : Comparison) (threshold : ℚ) :
    checkBelief run bundle first second comparison threshold = true ↔
      satisfies interpretation (context .two).model env (endpointWorld run n first second)
        (.modal (statisticalBelief comparison (.rational threshold) (bundleTest bundle)
          (alternative : ModalFormula Γ))) := by
  constructor
  · intro checked
    exact ⟨endpoint_admitted run n first second hn,
      (checkBelief_correct run bundle env n first second comparison threshold).mp checked⟩
  · intro sat
    exact (checkBelief_correct run bundle env n first second comparison threshold).mpr sat.2

theorem checkSingle_correct (name : TestId) (env : GhostEnv Bool Primitive Γ)
    (n : Int) (first second : Bool) (comparison : Comparison) (threshold : ℚ) :
    checkSingle name first second comparison threshold = true ↔
      referenceModalSatisfaction interpretation (context .two).model env
        (singleWorld n first second name)
        (statisticalBelief comparison (.rational threshold) (singleTest name)
          (alternative : ModalFormula Γ)) :=
  checkBelief_correct (.single name) (.single name) env n first second comparison threshold

theorem checkDisjunction_correct (env : GhostEnv Bool Primitive Γ)
    (n : Int) (first second : Bool) (comparison : Comparison) (threshold : ℚ) :
    checkDisjunction first second comparison threshold = true ↔
      referenceModalSatisfaction interpretation (context .two).model env (pairWorld n first second)
        (statisticalBelief comparison (.rational threshold) (.disj pairId firstTest secondTest)
          (alternative : ModalFormula Γ)) :=
  checkBelief_correct .pair .disj env n first second comparison threshold

theorem checkConjunction_correct (env : GhostEnv Bool Primitive Γ)
    (n : Int) (first second : Bool) (comparison : Comparison) (threshold : ℚ) :
    checkConjunction first second comparison threshold = true ↔
      referenceModalSatisfaction interpretation (context .two).model env (pairWorld n first second)
        (statisticalBelief comparison (.rational threshold) (.conj pairId firstTest secondTest)
          (alternative : ModalFormula Γ)) :=
  checkBelief_correct .pair .conj env n first second comparison threshold

theorem checkHiddenSingle_correct (env : GhostEnv Bool Primitive Γ)
    (n : Int) (first second : Bool) (comparison : Comparison) (threshold : ℚ) :
    checkHiddenSingle first second comparison threshold = true ↔
      referenceModalSatisfaction interpretation (context .two).model env (hiddenWorld n first second)
        (statisticalBelief comparison (.rational threshold) (singleTest firstId)
          (alternative : ModalFormula Γ)) :=
  checkBelief_correct .hidden (.single firstId) env n first second comparison threshold

/-- The actual accounted-disjunction conclusion uses the idempotent disjunction
of the two tests' common alternative, as in the scientific rule application. -/
theorem checkAccountedDisjunction_correct (env : GhostEnv Bool Primitive Γ)
    (n : Int) (first second : Bool) (comparison : Comparison) (threshold : ℚ) :
    checkDisjunction first second comparison threshold = true ↔
      referenceModalSatisfaction interpretation (context .two).model env (pairWorld n first second)
        (statisticalBelief comparison (.rational threshold) (.disj pairId firstTest secondTest)
          ((alternative : ModalFormula Γ).disj alternative)) := by
  simpa only [statisticalBelief_unfold, referenceModalSatisfaction_disj, or_self] using
    (checkDisjunction_correct env n first second comparison threshold)

theorem checkAccountedConjunction_correct (env : GhostEnv Bool Primitive Γ)
    (n : Int) (first second : Bool) (comparison : Comparison) (threshold : ℚ) :
    checkConjunction first second comparison threshold = true ↔
      referenceModalSatisfaction interpretation (context .two).model env (pairWorld n first second)
        (statisticalBelief comparison (.rational threshold) (.conj pairId firstTest secondTest)
          ((alternative : ModalFormula Γ).conj alternative)) := by
  simpa only [statisticalBelief_unfold, referenceModalSatisfaction_disj,
    referenceModalSatisfaction, and_self] using
    (checkConjunction_correct env n first second comparison threshold)

theorem checkHiddenSingle_false (first second : Bool) (comparison : Comparison) (threshold : ℚ) :
    checkHiddenSingle first second comparison threshold = false := by
  have mismatch : (endpointSnapshot .hidden first second).ledger ≠
      bundleHistory (.single firstId) first second := by
    intro equal
    have cards := congrArg Multiset.card equal
    norm_num [endpointSnapshot, hiddenFinal, singleFinal, runTest, initialSnapshot,
      Lara.Examples.BHLExecution.initialSnapshot, bundleHistory] at cards
  simp [checkHiddenSingle, checkBelief, mismatch]

theorem exceptional_single_checked : checkSingle firstId true true .equal (1 / 4) = true := by
  norm_num [checkSingle, checkBelief, endpointSnapshot, singleFinal, runTest,
    initialSnapshot, Lara.Examples.BHLExecution.initialSnapshot, bundleHistory, eventMass,
    compareRational, dataId, aliasId]

theorem accounted_pair_checked :
    checkDisjunction true true .lessEqual (1 / 2) = true ∧
      checkConjunction true true .lessEqual (1 / 4) = true := by
  norm_num [checkDisjunction, checkConjunction, checkBelief, endpointSnapshot,
    pairFinal, singleFinal, runTest, initialSnapshot, Lara.Examples.BHLExecution.initialSnapshot,
    bundleHistory, eventMass_disj, eventMass_conj, compareRational, dataId, aliasId]

theorem exceptional_checked_false_alternative :
    checkSingle firstId true true .equal (1 / 4) = true ∧
      ¬ referenceModalSatisfaction interpretation (context .two).model GhostEnv.empty
        (singleWorld 0 true true firstId) (alternative : ModalFormula []) :=
  ⟨exceptional_single_checked, BHLStatistical.single_alternative_false⟩

/-- The failed full-history check retains exactly the originally reported value. -/
theorem hidden_checked_report_unchanged (n : Int) (first second : Bool)
    (comparison : Comparison) (threshold : ℚ) :
    checkHiddenSingle first second comparison threshold = false ∧
      (hiddenWorld n first second).current.memory.read report =
        (singleWorld n first second firstId).current.memory.read report :=
  ⟨checkHiddenSingle_false first second comparison threshold,
    hidden_report_unchanged n first second⟩

end
end Lara.Examples.BHLFiniteBelief
