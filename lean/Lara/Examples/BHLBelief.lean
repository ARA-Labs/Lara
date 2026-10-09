import Lara.BHL.Belief
import Lara.BHL.AssertionLaws
import Lara.BHL.GhostSubstitution
import Mathlib.Tactic

namespace Lara.Examples.BHLBelief

open Lara.BHL MeasureTheory

/-- A nonidentifiable Boolean parameter; both populations have the same law. -/
def parameter : Variable .boolean .invisible := ⟨⟨0⟩⟩
def report : Variable .real .observable := ⟨⟨1⟩⟩
def dataId : DatasetId := ⟨0⟩
def populationId : PopulationId := ⟨0⟩
def hypothesisId : HypothesisId := ⟨0⟩
def correctId : TestId := ⟨0⟩
def wrongId : TestId := ⟨1⟩
def extraId : TestId := ⟨2⟩

def chosenId (wrong : Bool) : TestId := if wrong then wrongId else correctId

def hiddenMemory (b : Bool) : HiddenMemory :=
  (Memory.empty.update parameter (some b)).hidden

@[simp] theorem hiddenMemory_parameter (b : Bool) :
    hiddenMemory b .boolean parameter.id = some b := by
  simp [hiddenMemory, Memory.hidden, Memory.update, parameter]

theorem hiddenMemory_false_ne_true : hiddenMemory false ≠ hiddenMemory true := by
  intro h
  have read := congrArg (fun hidden : HiddenMemory => hidden .boolean parameter.id) h
  simp at read

noncomputable section

def populationLaw (_hidden : HiddenMemory) : ProbabilityMeasure Bool := diracProbability false

def constantTest (point : ℝ) : NumericTest Bool ℝ where
  statistic := fun _ => 0
  measurableStatistic := measurable_const
  nullLaw := diracProbability point
  tail := fun candidate observed => observed ≤ candidate
  measurableTail := fun _ => measurableSet_Ici

def testFor (test : TestId) : NumericTest Bool ℝ :=
  constantTest (if test = wrongId then 1 else 0)

@[simp] theorem constantTest_pvalue_zero (data : Bool) :
    (constantTest 0).tailProbability data = 1 := by
  apply eventProbability_dirac_of_mem
  exact (le_rfl : (0 : ℝ) ≤ 0)

@[simp] theorem constantTest_pvalue_one (data : Bool) :
    (constantTest 1).tailProbability data = 1 := by
  apply eventProbability_dirac_of_mem
  exact (zero_le_one : (0 : ℝ) ≤ 1)

@[simp] theorem testFor_pvalue (test : TestId) (data : Bool) :
    (testFor test).tailProbability data = 1 := by
  unfold testFor
  split <;> simp

/-- This is an equality of actual pushforward laws, not a permission to use B. -/
def lawBinding (test : TestId) (hidden : HiddenMemory) : Prop :=
  (populationLaw hidden).map (testFor test).measurableStatistic.aemeasurable =
    (testFor test).nullLaw

@[simp] theorem population_statistic_law (test : TestId) (hidden : HiddenMemory) :
    (populationLaw hidden).map (testFor test).measurableStatistic.aemeasurable =
      diracProbability (0 : ℝ) := by
  apply Subtype.ext
  change (Measure.dirac false).map (fun _ : Bool => (0 : ℝ)) = Measure.dirac 0
  exact Measure.map_dirac' measurable_const false

theorem dirac_zero_ne_one : diracProbability (0 : ℝ) ≠ diracProbability (1 : ℝ) := by
  intro h
  have mass := congrArg (fun law : ProbabilityMeasure ℝ =>
    eventProbability law ({0} : Set ℝ)) h
  have left : eventProbability (diracProbability (0 : ℝ)) ({0} : Set ℝ) = 1 :=
    eventProbability_dirac_of_mem 0 (by simp)
  have right : eventProbability (diracProbability (1 : ℝ)) ({0} : Set ℝ) = 0 :=
    eventProbability_dirac_of_notMem 1 (measurableSet_singleton 0) (by norm_num)
  rw [left, right] at mass
  norm_num at mass

@[simp] theorem lawBinding_iff (test : TestId) (hidden : HiddenMemory) :
    lawBinding test hidden ↔ test ≠ wrongId := by
  unfold lawBinding
  rw [population_statistic_law]
  by_cases h : test = wrongId
  · simp [testFor, constantTest, h, dirac_zero_ne_one]
  · simp [testFor, constantTest, h]

@[simp] theorem chosenId_wrong (wrong : Bool) :
    chosenId wrong = wrongId ↔ wrong = true := by
  cases wrong <;> simp [chosenId, correctId, wrongId]

def initialVisible : VisibleState Bool := ⟨Memory.empty.observable, fun _ => false⟩

/-- The primitive reads visible data, computes the genuine test probability, and
returns the complete one-test ledger delta. No hidden input reaches it. -/
def testEffect (test : TestId) (before : VisibleState Bool) : VisibleState Bool × History Bool :=
  (⟨((Memory.assemble before.memory Memory.empty.hidden).update report
      (some ((testFor test).tailProbability (before.datasets dataId)))).observable,
    before.datasets⟩, {(before.datasets dataId, test)})

def dynamics : Dynamics Bool TestId where
  initial := fun hidden visible => (∃ b : Bool, hidden = hiddenMemory b) ∧ visible = initialVisible
  command := fun test before => some (testEffect test before)
  sampling := fun hidden before after data population =>
    population = populationId ∧ after = before ∧ before.datasets dataId = data ∧
      eventProbability (populationLaw hidden) {data} = 1

def model : Model Bool TestId where
  dynamics := dynamics
  initial_nonempty := ⟨hiddenMemory false, initialVisible, ⟨⟨false, rfl⟩, rfl⟩⟩

def startWorld (b : Bool) : World Bool TestId :=
  World.start (Memory.assemble initialVisible.memory (hiddenMemory b)) initialVisible.datasets

def sampleState (b : Bool) : State Bool TestId :=
  ⟨Memory.assemble initialVisible.memory (hiddenMemory b), initialVisible.datasets, 0,
    .sample false populationId⟩

def sampledWorld (b : Bool) : World Bool TestId := (startWorld b).extend (sampleState b)

def testState (test : TestId) (world : World Bool TestId) : State Bool TestId :=
  let effect := testEffect test world.current.visible
  ⟨Memory.assemble effect.1.memory world.current.memory.hidden, effect.1.datasets,
    world.current.history + effect.2, .command test⟩

def testedWorld (wrong b : Bool) : World Bool TestId :=
  (sampledWorld b).extend (testState (chosenId wrong) (sampledWorld b))

/-- The extra audit test changes the full ledger but not the reported real result. -/
def fixtureWorld (wrong extra b : Bool) : World Bool TestId :=
  if extra then (testedWorld wrong b).extend (testState extraId (testedWorld wrong b))
  else testedWorld wrong b

theorem startWorld_admitted (b : Bool) : Admitted dynamics (startWorld b) :=
  admitted_start dynamics initialVisible (hiddenMemory b) ⟨⟨b, rfl⟩, rfl⟩

theorem sampledWorld_admitted (b : Bool) : Admitted dynamics (sampledWorld b) := by
  apply admitted_extend (startWorld_admitted b) (sampleState b) rfl
  change dynamics.sampling (hiddenMemory b) initialVisible initialVisible false populationId ∧
    (0 : History Bool) = 0 + 0
  refine ⟨⟨rfl, rfl, rfl, ?_⟩, by simp⟩
  exact eventProbability_dirac_of_mem false (by simp)

theorem testState_admitted {world : World Bool TestId} (h : Admitted dynamics world)
    (test : TestId) : Admitted dynamics (world.extend (testState test world)) := by
  apply admitted_extend h (testState test world)
  · simpa [testState] using admitted_current_hidden h
  · change ∃ delta, some (testEffect test world.current.visible) =
      some ((testState test world).visible, delta) ∧
      (testState test world).history = world.current.history + delta
    exact ⟨(testEffect test world.current.visible).2, rfl, rfl⟩

theorem testedWorld_admitted (wrong b : Bool) : Admitted dynamics (testedWorld wrong b) :=
  testState_admitted (sampledWorld_admitted b) (chosenId wrong)

theorem fixtureWorld_admitted (wrong extra b : Bool) :
    Admitted model.dynamics (fixtureWorld wrong extra b) := by
  cases extra
  · exact testedWorld_admitted wrong b
  · exact testState_admitted (testedWorld_admitted wrong b) extraId

@[simp] theorem fixtureWorld_hidden (wrong extra b : Bool) :
    (fixtureWorld wrong extra b).current.memory.hidden = hiddenMemory b := by
  cases extra <;> simp [fixtureWorld, testedWorld, sampledWorld, testState, sampleState]

@[simp] theorem fixtureWorld_data (wrong extra b : Bool) (name : DatasetId) :
    (fixtureWorld wrong extra b).current.datasets name = false := by
  cases extra <;> simp [fixtureWorld, testedWorld, sampledWorld, testState,
    testEffect, sampleState, initialVisible, State.visible]

@[simp] theorem fixtureWorld_history (wrong extra b : Bool) :
    (fixtureWorld wrong extra b).current.history =
      {(false, chosenId wrong)} + (if extra then {(false, extraId)} else 0) := by
  cases extra <;> simp [fixtureWorld, testedWorld, sampledWorld, testState,
    testEffect, sampleState, initialVisible, State.visible]

@[simp] theorem fixtureWorld_provenance (wrong extra b : Bool) :
    (fixtureWorld wrong extra b).samplingProvenance = {(false, populationId)} := by
  cases extra <;> simp [fixtureWorld, testedWorld, sampledWorld, startWorld,
    sampleState, testState, World.samplingProvenance, World.extend, World.start]

@[simp] theorem fixtureWorld_report (wrong extra b : Bool) :
    (fixtureWorld wrong extra b).current.memory.read report = some (1 : ℝ) := by
  cases extra <;> simp [fixtureWorld, testedWorld, sampledWorld, testState,
    testEffect, Memory.read, Memory.assemble, Memory.observable, report, Memory.update]

theorem fixtureWorld_accessible (wrong extra left right : Bool) :
    Accessible (fixtureWorld wrong extra left) (fixtureWorld wrong extra right) := by
  cases extra <;> simp [Accessible, observeWorld, World.trace, World.extend,
    fixtureWorld, testedWorld, sampledWorld, startWorld, World.start, sampleState,
    testState, testEffect, observeState, State.visible, World.current,
    Memory.observable, Memory.assemble]

/-- Enumeration is derived from the initial relation and every actual edge. The
model itself still contains all lawful worlds of arbitrary finite length. -/
theorem fixtureWorld_compatible (wrong extra : Bool) (hidden : HiddenMemory) :
    hidden ∈ compatibleHidden dynamics (fixtureWorld wrong extra false) ↔
      ∃ b : Bool, hidden = hiddenMemory b := by
  constructor
  · intro h
    cases extra <;>
      change _ = 0 ∧ _ = (Action.initial : Action Bool TestId) ∧
        dynamics.initial hidden initialVisible ∧ _ at h
    all_goals exact h.2.2.1.1
  · rintro ⟨b, rfl⟩
    have h := admitted_hidden_mem_compatible (fixtureWorld_admitted wrong extra b)
    rw [compatibleHidden_eq_of_accessible (fixtureWorld_accessible wrong extra b false)] at h
    simpa only [fixtureWorld_hidden, model] using h

theorem fixture_rebuild_closure (wrong extra : Bool) (hidden : HiddenMemory) :
    Admitted dynamics ((fixtureWorld wrong extra false).rebuildHidden hidden) ↔
      ∃ b : Bool, hidden = hiddenMemory b :=
  (admitted_rebuildHidden_iff dynamics (fixtureWorld wrong extra false) hidden).trans
    (fixtureWorld_compatible wrong extra hidden)

abbrev fixtureView (wrong extra b : Bool) : SemanticView Bool :=
  semanticView dynamics (fixtureWorld wrong extra b)

theorem fixtureView_mem (wrong extra b : Bool) : fixtureView wrong extra b ∈ model.views :=
  semanticView_mem_views model (fixtureWorld_admitted wrong extra b)

theorem fixtureView_accessible (wrong extra left right : Bool) :
    ViewAccessible (fixtureView wrong extra left) (fixtureView wrong extra right) :=
  view_accessible_forth dynamics (fixtureWorld_accessible wrong extra left right)

theorem fixtureView_false_ne_true (wrong extra : Bool) :
    fixtureView wrong extra false ≠ fixtureView wrong extra true := by
  intro h
  apply hiddenMemory_false_ne_true
  have hidden := congrArg SemanticView.hidden h
  simpa only [fixtureView, semanticView, fixtureWorld_hidden] using hidden

/-- No arbitrary two-world universe is selected: every realized accessible view
is one of these two, and both have independently admitted representatives. -/
theorem fixtureView_enumeration (wrong extra source : Bool) (view : SemanticView Bool)
    (member : view ∈ model.views) (accessible : ViewAccessible (fixtureView wrong extra source) view) :
    ∃ b : Bool, view = fixtureView wrong extra b := by
  rcases member with ⟨⟨world, admitted⟩, rfl⟩
  rcases (admitted_initial admitted).2.1 with ⟨b, hb⟩
  have hidden : world.current.memory.hidden = hiddenMemory b :=
    (admitted_current_hidden admitted).trans hb
  have target := view_accessible_trans (view_accessible_symm accessible)
    (fixtureView_accessible wrong extra source b)
  refine ⟨b, ?_⟩
  change world.current.visible = (fixtureWorld wrong extra b).current.visible ∧
    world.current.history = (fixtureWorld wrong extra b).current.history ∧
    compatibleHidden dynamics world = compatibleHidden dynamics (fixtureWorld wrong extra b) ∧
    world.samplingProvenance = (fixtureWorld wrong extra b).samplingProvenance at target
  change SemanticView.mk world.current.visible world.current.history world.current.memory.hidden
    (compatibleHidden dynamics world) world.samplingProvenance =
    SemanticView.mk (fixtureWorld wrong extra b).current.visible
      (fixtureWorld wrong extra b).current.history (fixtureWorld wrong extra b).current.memory.hidden
      (compatibleHidden dynamics (fixtureWorld wrong extra b))
      (fixtureWorld wrong extra b).samplingProvenance
  rw [target.1, target.2.1, target.2.2.1, target.2.2.2, hidden,
    fixtureWorld_hidden]

/-- A real scientific requirement combines the population/statistic law
identity with the declared hypothesis and population identities. Provenance is
additionally checked by the built-in modelRequirements interpretation. -/
def interpretation : AssertionInterpretation Bool TestId where
  constants := fun sort _ => match sort with
    | .value sort => valueDefault sort
    | .dataset => false
    | .world => startWorld false
    | .trace => []
  functions := fun _ output _ _ => valueDefault output
  datasetFunctions := fun _ _ _ => false
  predicates := fun _ _ _ => False
  tests := fun _ test => testFor test
  hypotheses := fun hypothesis hidden =>
    hypothesis = hypothesisId ∧ hidden .boolean parameter.id = some true
  requirements := fun hypothesis test population hidden _ =>
    hypothesis = hypothesisId ∧ population = populationId ∧ lawBinding test hidden
  jointRequirements := fun _ _ _ => False
  couplings := fun _ _ _ _ _ => none
  commands := fun command => ⟨command.index⟩

def datasetTerm : AssertionTerm [] .dataset := .datasetRead .ambient dataId

def testExpression (wrong : Bool) : TestExpression [] :=
  .leaf hypothesisId datasetTerm (chosenId wrong) populationId

def alternative : ModalFormula [] := .atom (.hypothesis hypothesisId (.hiddenOf .ambient))

def belief (wrong : Bool) (comparison : Comparison) (threshold : Nat) : ModalFormula [] :=
  statisticalBelief comparison (.rational threshold) (testExpression wrong) alternative

@[simp] theorem datasetTerm_evaluation (wrong extra b : Bool) :
    evalTerm interpretation model GhostEnv.empty (fixtureView wrong extra b) datasetTerm = some false := by
  simp [datasetTerm, evalTerm, fixtureView, semanticView, State.visible]

@[simp] theorem pvalue_evaluation (wrong extra b : Bool) :
    evalTerm interpretation model GhostEnv.empty (fixtureView wrong extra b)
      (.pvalue (testExpression wrong)) = some (1 : ℝ) := by
  simp only [evalTerm, evalNumericalEvent, testExpression, datasetTerm_evaluation,
    Option.map_some]
  change some ((NumericalEvent.tail (testFor (chosenId wrong)) false).probability) = some 1
  simp [NumericalEvent.tail_probability]

@[simp] theorem report_evaluation (wrong extra b : Bool) :
    evalTerm interpretation model GhostEnv.empty (fixtureView wrong extra b)
      (.valueRead .ambient report) = some (1 : ℝ) := by
  change (fixtureWorld wrong extra b).current.memory.read report = some (1 : ℝ)
  exact fixtureWorld_report wrong extra b

@[simp] theorem alternative_meaning (wrong extra b : Bool) :
    viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView wrong extra b) alternative ↔
      b = true := by
  simp [alternative, viewModalSatisfaction, atomMeaning, evalTerm, interpretation,
    fixtureView, semanticView]

@[simp] theorem requirements_meaning (wrong extra b : Bool) :
    viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView wrong extra b)
      (modelRequirementsFormula (testExpression wrong)) ↔ wrong = false := by
  cases wrong <;>
    simp [modelRequirementsFormula, viewModalSatisfaction, atomMeaning, evalTerm,
      modelRequirements, testExpression, datasetTerm, interpretation, fixtureView,
      semanticView, State.visible, lawBinding_iff, chosenId, correctId, wrongId]

theorem fixtureLedger_exact (wrong extra : Bool) :
    ({(false, chosenId wrong)} + (if extra then {(false, extraId)} else 0) : History Bool) =
      {(false, chosenId wrong)} ↔ extra = false := by
  cases extra
  · simp
  · constructor
    · intro h
      have cardinality := congrArg Multiset.card h
      simp at cardinality
    · intro h
      cases h

@[simp] theorem exactHistory_meaning (wrong extra b : Bool) :
    viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView wrong extra b)
      (exactHistory (testExpression wrong)) ↔ extra = false := by
  simpa [exactHistory, viewModalSatisfaction, atomMeaning, evalTerm,
    testHistoryTerm, testExpression, datasetTerm, fixtureView, semanticView, State.visible] using
    fixtureLedger_exact wrong extra

@[simp] theorem pvalue_meaning (wrong extra b : Bool) (comparison : Comparison) (n : Nat) :
    viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView wrong extra b)
      (pvalueAtom comparison (.rational n) (testExpression wrong)) ↔
      compareReal comparison 1 (n : ℝ) := by
  simp only [pvalueAtom, viewModalSatisfaction, atomMeaning, pvalue_evaluation]
  simp [evalTerm]

theorem view_conj_iff (view : SemanticView Bool) (left right : ModalFormula []) :
    viewModalSatisfaction interpretation model GhostEnv.empty view (.conj left right) ↔
      viewModalSatisfaction interpretation model GhostEnv.empty view left ∧
        viewModalSatisfaction interpretation model GhostEnv.empty view right := Iff.rfl

theorem view_neg_iff (view : SemanticView Bool) (formula : ModalFormula []) :
    viewModalSatisfaction interpretation model GhostEnv.empty view (.neg formula) ↔
      ¬ viewModalSatisfaction interpretation model GhostEnv.empty view formula := Iff.rfl

@[simp] theorem exception_meaning (wrong extra hidden : Bool) (comparison : Comparison) (n : Nat) :
    viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView wrong extra hidden)
      (exception comparison (.rational n) (testExpression wrong)) ↔
      compareReal comparison 1 (n : ℝ) ∧ extra = false := by
  simp only [exception, view_conj_iff, pvalue_meaning, exactHistory_meaning]

@[simp] theorem fixture_knows (wrong extra source : Bool) (formula : ModalFormula []) :
    viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView wrong extra source)
      (.knows formula) ↔
    ∀ b : Bool, viewModalSatisfaction interpretation model GhostEnv.empty
      (fixtureView wrong extra b) formula := by
  constructor
  · intro h b
    exact h (fixtureView wrong extra b) (fixtureView_mem wrong extra b)
      (fixtureView_accessible wrong extra source b)
  · intro h view member accessible
    rcases fixtureView_enumeration wrong extra source view member accessible with ⟨b, rfl⟩
    exact h b

/-- Exact evaluation of the published three-way B expression on this fixture. -/
theorem belief_meaning (wrong extra source : Bool) (comparison : Comparison) (n : Nat) :
    viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView wrong extra source)
      (belief wrong comparison n) ↔
      (compareReal comparison 1 (n : ℝ) ∧ extra = false) ∨ wrong = true := by
  classical
  simp only [belief, statisticalBelief, fixture_knows, viewModalSatisfaction_disj,
    alternative_meaning, exception, view_conj_iff, view_neg_iff, pvalue_meaning,
    exactHistory_meaning, requirements_meaning]
  constructor
  · intro h
    simpa using h false
  · intro h b
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by cases wrong <;> simp_all))

theorem exceptional_belief_false_alternative :
    satisfies interpretation model GhostEnv.empty (fixtureWorld false false false)
      (.modal (belief false .equal 1)) ∧
    ¬ referenceModalSatisfaction interpretation model GhostEnv.empty
      (fixtureWorld false false false) alternative := by
  constructor
  · refine ⟨fixtureWorld_admitted false false false, ?_⟩
    apply (reference_view_modal_correspondence interpretation model GhostEnv.empty _ _).2
    exact (belief_meaning false false false .equal 1).2 (Or.inl ⟨by norm_num [compareReal], rfl⟩)
  · rw [reference_view_modal_correspondence]
    simpa only [fixtureView, model] using (show
      ¬ viewModalSatisfaction interpretation model GhostEnv.empty
        (fixtureView false false false) alternative by simp)

/-- At zero the alternative and exceptional-sample branch are both false. B is
true only because the actual wrong Dirac law fails the population pushforward. -/
theorem model_failure_only_at_zero :
    satisfies interpretation model GhostEnv.empty (fixtureWorld true false false)
      (.modal (belief true .equal 0)) ∧
    ¬ viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView true false false) alternative ∧
    ¬ viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView true false false)
      (exception .equal (.rational 0) (testExpression true)) ∧
    viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView true false false)
      (exactHistory (testExpression true)) ∧
    ¬ viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView true false false)
      (modelRequirementsFormula (testExpression true)) := by
  refine ⟨⟨fixtureWorld_admitted true false false, ?_⟩, ?_, ?_, ?_, ?_⟩
  · apply (reference_view_modal_correspondence interpretation model GhostEnv.empty _ _).2
    exact (belief_meaning true false false .equal 0).2 (Or.inr rfl)
  · simp
  · intro h
    have impossible : (1 : ℝ) = 0 :=
      by simpa [compareReal] using ((exception_meaning true false false .equal 0).1 h).1
    norm_num at impossible
  · simp
  · simp

theorem exception_requirements_hold :
    viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView false false false)
      (modelRequirementsFormula (testExpression false)) := by simp

theorem exception_only_branch :
    viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView false false false)
      (exception .equal (.rational 1) (testExpression false)) ∧
    viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView false false false)
      (modelRequirementsFormula (testExpression false)) ∧
    ¬ viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView false false false)
      alternative := by
  exact ⟨(exception_meaning false false false .equal 1).2 ⟨by norm_num [compareReal], rfl⟩,
    exception_requirements_hold, by simp⟩

theorem equality_nonmonotone :
    (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 2 ∧
    viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView false false false)
      (belief false .equal 1) ∧
    ¬ viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView false false false)
      (belief false .equal 2) := by
  norm_num [belief_meaning, compareReal]

theorem unchanged_report_extra_ledger :
    (fixtureWorld false false false).current.memory.read report =
      (fixtureWorld false true false).current.memory.read report ∧
    ¬ viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView false true false)
      (exactHistory (testExpression false)) ∧
    ¬ viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView false true false)
      (belief false .equal 1) := by
  simp [belief_meaning, compareReal]

/-- Both hidden parameters are possible; the alternative is not known. -/
theorem hidden_alternative_nonidentifiable :
    ¬ viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView false false false)
      (.knows alternative) ∧
    viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView false false false)
      alternative.possible := by
  simp [ModalFormula.possible, view_neg_iff, fixture_knows, alternative_meaning]

end

/-- Only the atoms of this concrete typed fixture are executable. This is not a
decision procedure for arbitrary real measures or the complete BHL language. -/
inductive WitnessAtom where
  | alternative
  | pvalue : Comparison → Nat → WitnessAtom
  | exactHistory
  | requirements
  | reportedOne
  deriving Repr

inductive WitnessFormula where
  | atom : WitnessAtom → WitnessFormula
  | neg : WitnessFormula → WitnessFormula
  | conj : WitnessFormula → WitnessFormula → WitnessFormula
  | knows : WitnessFormula → WitnessFormula
  | atAmbient : WitnessFormula → WitnessFormula
  deriving Repr

def WitnessFormula.disj (left right : WitnessFormula) : WitnessFormula :=
  .neg (.conj (.neg left) (.neg right))

def compareRational : Comparison → ℚ → ℚ → Bool
  | .equal, a, b => decide (a = b)
  | .less, a, b => decide (a < b)
  | .lessEqual, a, b => decide (a ≤ b)
  | .greater, a, b => decide (b < a)
  | .greaterEqual, a, b => decide (b ≤ a)

/-- Exact finite Dirac integration: the inclusive event is tested at its sole
support point; the statistic evaluated on either Boolean sample is zero. -/
def finitePvalue (wrong : Bool) : ℚ :=
  if decide ((0 : ℚ) ≤ (if wrong then 1 else 0)) then 1 else 0

def finiteLedger (wrong extra : Bool) : List (Bool × TestId) :=
  [(false, chosenId wrong)] ++ if extra then [(false, extraId)] else []

def finiteProvenance : List (Bool × PopulationId) := [(false, populationId)]

def evaluateAtom (wrong extra hidden : Bool) : WitnessAtom → Bool
  | .alternative => hidden
  | .pvalue comparison n => compareRational comparison (finitePvalue wrong) n
  | .exactHistory => decide (finiteLedger wrong extra = [(false, chosenId wrong)])
  | .requirements => decide ((0 : ℚ) = (if wrong then 1 else 0)) &&
      decide ((false, populationId) ∈ finiteProvenance)
  | .reportedOne => decide (finitePvalue wrong = 1)

def evaluate (wrong extra hidden : Bool) : WitnessFormula → Bool
  | .atom atom => evaluateAtom wrong extra hidden atom
  | .neg formula => !(evaluate wrong extra hidden formula)
  | .conj left right => evaluate wrong extra hidden left && evaluate wrong extra hidden right
  | .knows formula => evaluate wrong extra false formula && evaluate wrong extra true formula
  | .atAmbient formula => evaluate wrong extra hidden formula

def witnessBelief (comparison : Comparison) (n : Nat) : WitnessFormula :=
  .knows (WitnessFormula.disj (.atom .alternative)
    (WitnessFormula.disj (.conj (.atom (.pvalue comparison n)) (.atom .exactHistory))
      (.neg (.atom .requirements))))

/-- Parent smoke runners can call these directly, without evaluating measures. -/
def exceptionalBeliefResult : Bool := evaluate false false false (witnessBelief .equal 1)
def exceptionalAlternativeResult : Bool := evaluate false false false (.atom .alternative)
def modelFailureBeliefAtZeroResult : Bool := evaluate true false false (witnessBelief .equal 0)
def modelFailureExceptionAtZeroResult : Bool :=
  evaluate true false false (.conj (.atom (.pvalue .equal 0)) (.atom .exactHistory))

noncomputable section

def quoteAtom (wrong : Bool) : WitnessAtom → ModalFormula []
  | .alternative => alternative
  | .pvalue comparison n => pvalueAtom comparison (.rational n) (testExpression wrong)
  | .exactHistory => exactHistory (testExpression wrong)
  | .requirements => modelRequirementsFormula (testExpression wrong)
  | .reportedOne => .atom (.equal (.valueRead .ambient report) (.rational 1))

def quote (wrong : Bool) : WitnessFormula → ModalFormula []
  | .atom atom => quoteAtom wrong atom
  | .neg formula => .neg (quote wrong formula)
  | .conj left right => .conj (quote wrong left) (quote wrong right)
  | .knows formula => .knows (quote wrong formula)
  | .atAmbient formula => .atView .ambient (quote wrong formula)

@[simp] theorem quote_witnessBelief (wrong : Bool) (comparison : Comparison) (n : Nat) :
    quote wrong (witnessBelief comparison n) = belief wrong comparison n := rfl

@[simp] theorem finitePvalue_one (wrong : Bool) : finitePvalue wrong = 1 := by
  cases wrong <;> norm_num [finitePvalue]

theorem compareRational_correspondence (comparison : Comparison) (n : Nat) :
    compareRational comparison 1 n = true ↔ compareReal comparison 1 (n : ℝ) := by
  cases comparison <;> simp only [compareRational, decide_eq_true_eq, compareReal]
  all_goals norm_cast

theorem evaluateAtom_correspondence (wrong extra hidden : Bool) (atom : WitnessAtom) :
    evaluateAtom wrong extra hidden atom = true ↔
      viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView wrong extra hidden)
        (quoteAtom wrong atom) := by
  cases atom with
  | alternative => simp [evaluateAtom, quoteAtom]
  | pvalue comparison n =>
      simpa [evaluateAtom, quoteAtom] using compareRational_correspondence comparison n
  | exactHistory => cases extra <;> simp [evaluateAtom, quoteAtom, finiteLedger]
  | requirements => cases wrong <;> norm_num [evaluateAtom, quoteAtom, finiteProvenance]
  | reportedOne =>
      simp only [evaluateAtom, quoteAtom, viewModalSatisfaction, atomMeaning, report_evaluation]
      simp [evalTerm]

/-- The finite modal evaluator corresponds to the actual realized-view meaning,
including nested K and targets reevaluated under K. -/
theorem evaluate_correspondence (wrong extra hidden : Bool) (formula : WitnessFormula) :
    evaluate wrong extra hidden formula = true ↔
      viewModalSatisfaction interpretation model GhostEnv.empty (fixtureView wrong extra hidden)
        (quote wrong formula) := by
  induction formula generalizing hidden with
  | atom atom => exact evaluateAtom_correspondence wrong extra hidden atom
  | neg formula ih => simp [evaluate, quote, viewModalSatisfaction, ← ih]
  | conj left right ihLeft ihRight =>
      simp [evaluate, quote, viewModalSatisfaction, ← ihLeft, ← ihRight]
  | knows formula ih =>
      simp only [evaluate, quote, Bool.and_eq_true, fixture_knows]
      constructor
      · rintro ⟨left, right⟩ b
        cases b
        · exact (ih false).1 left
        · exact (ih true).1 right
      · intro h
        exact ⟨(ih false).2 (h false), (ih true).2 (h true)⟩
  | atAmbient formula ih =>
      simp only [evaluate, quote, viewModalSatisfaction, evalTerm, Option.some.injEq,
        exists_eq_left', fixtureView_mem, true_and]
      exact ih hidden

/-- Executable correspondence is also to the public full-world satisfaction,
not merely to a separate canned Boolean semantics. -/
theorem evaluate_satisfies_correspondence (wrong extra hidden : Bool) (formula : WitnessFormula) :
    evaluate wrong extra hidden formula = true ↔
      satisfies interpretation model GhostEnv.empty (fixtureWorld wrong extra hidden)
        (.modal (quote wrong formula)) := by
  rw [evaluate_correspondence, satisfies]
  simp only [fixtureWorld_admitted, true_and]
  simp only [referenceAssertionSatisfaction, reference_view_modal_correspondence, fixtureView, model]

theorem executable_exception_certificate :
    exceptionalBeliefResult = true ∧ exceptionalAlternativeResult = false ∧
    satisfies interpretation model GhostEnv.empty (fixtureWorld false false false)
      (.modal (belief false .equal 1)) := by
  refine ⟨by decide, rfl, ?_⟩
  exact (evaluate_satisfies_correspondence false false false (witnessBelief .equal 1)).1
    (by decide)

theorem executable_failure_certificate :
    modelFailureBeliefAtZeroResult = true ∧ modelFailureExceptionAtZeroResult = false ∧
    satisfies interpretation model GhostEnv.empty (fixtureWorld true false false)
      (.modal (belief true .equal 0)) := by
  refine ⟨by decide, by decide, ?_⟩
  exact (evaluate_satisfies_correspondence true false false (witnessBelief .equal 0)).1
    (by decide)

/-- atAmbient is resolved separately at both hidden alternatives under each K. -/
theorem nested_knowledge_view_reevaluation :
    evaluate false false false
      (.knows (.atAmbient (.knows (.atom .reportedOne)))) = true ∧
    satisfies interpretation model GhostEnv.empty (fixtureWorld false false false)
      (.modal (quote false (.knows (.atAmbient (.knows (.atom .reportedOne)))))) := by
  exact ⟨by decide, (evaluate_satisfies_correspondence false false false _).1 (by decide)⟩

/-- Substitute a rigid false Boolean across a fresh Boolean binder. The fresh
value may be true; it must not capture the old index there here. -/
def captureSubstitution : GhostSubstitution [.value .boolean] []
  | _, .here => .constant ⟨0⟩
  | _, .there index => nomatch index

def scopedCaptureBody : Assertion [.value .boolean] :=
  .all (.value .boolean) (.modal (.knows (.atom (.equal
    (.ghost (.bound (.there .here))) (.boolean false)))))

def scopedCaptureExample : Assertion [] := scopedCaptureBody.substituteGhosts captureSubstitution

theorem captureSubstitution_environment :
    substitutionEnv interpretation captureSubstitution GhostEnv.empty =
      GhostEnv.push (sort := .value .boolean) false GhostEnv.empty := by
  apply GhostEnv.ext
  intro sort index
  cases index with
  | here => simp [substitutionEnv, captureSubstitution, GhostTerm.eval,
      interpretation, GhostEnv.lookup, GhostEnv.push, valueDefault]
  | there index => cases index

theorem scopedCaptureExample_correct :
    satisfies interpretation model GhostEnv.empty (fixtureWorld false false false) scopedCaptureExample := by
  apply (satisfies_substituteGhosts interpretation model captureSubstitution GhostEnv.empty
    (fixtureWorld false false false) scopedCaptureBody).2
  rw [captureSubstitution_environment]
  refine ⟨fixtureWorld_admitted false false false, ?_⟩
  change ∀ inner : Bool,
    referenceModalSatisfaction interpretation model
      (GhostEnv.push (sort := .value .boolean) inner
        (GhostEnv.push (sort := .value .boolean) false GhostEnv.empty))
      (fixtureWorld false false false) _
  intro inner world _ _
  exact ⟨false, rfl, rfl⟩

theorem scopedCapture_distinct_bindings :
    evalTerm interpretation model
      (GhostEnv.push (sort := .value .boolean) true
        (GhostEnv.push (sort := .value .boolean) false GhostEnv.empty))
      (fixtureView false false false)
      (.ghost (.bound (.here : BoundGhost [.value .boolean, .value .boolean] (.value .boolean)))) =
        some true ∧
    evalTerm interpretation model
      (GhostEnv.push (sort := .value .boolean) true
        (GhostEnv.push (sort := .value .boolean) false GhostEnv.empty))
      (fixtureView false false false)
      (.ghost (.bound (.there .here :
        BoundGhost [.value .boolean, .value .boolean] (.value .boolean)))) = some false :=
  ⟨rfl, rfl⟩

end
end Lara.Examples.BHLBelief
