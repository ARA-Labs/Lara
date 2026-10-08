import Lara.BHL.StatisticalRules
import Lara.Examples.BHLExecution
import Mathlib.Tactic

namespace Lara.Examples.BHLSoundnessScience

open Lara.BHL MeasureTheory

/-- The three scientific parameters are genuine hidden integers, including zero. -/
def parameter : Variable .integer .invisible := ⟨⟨30⟩⟩
def lowerId : HypothesisId := ⟨2⟩
def upperId : HypothesisId := ⟨3⟩
def twoId : TestId := ⟨0⟩
def lowId : TestId := ⟨2⟩
def upId : TestId := ⟨3⟩
def pairId : CouplingId := ⟨0⟩
def secondReport : Variable .real .observable := ⟨⟨14⟩⟩

inductive Prior where
  | two | low | up
  deriving DecidableEq

def allowed : Prior → Int → Prop
  | .two, n => n = -1 ∨ n = 0 ∨ n = 1
  | .low, n => n = -1 ∨ n = 0
  | .up, n => n = 0 ∨ n = 1

instance (prior : Prior) (n : Int) : Decidable (allowed prior n) := by
  cases prior <;> unfold allowed <;> infer_instance

def hiddenMemory (n : Int) : HiddenMemory :=
  (Memory.empty.update parameter (some n)).hidden

def theta (hidden : HiddenMemory) : Int := (hidden .integer parameter.id).getD 0

@[simp] theorem theta_hiddenMemory (n : Int) : theta (hiddenMemory n) = n := by
  simp [theta, hiddenMemory, Memory.hidden, Memory.update, parameter]

def lower : ModalFormula Γ := .atom (.hypothesis lowerId (.hiddenOf .ambient))
def upper : ModalFormula Γ := .atom (.hypothesis upperId (.hiddenOf .ambient))
def alternative : ModalFormula Γ := lower.disj upper

def priorFormula : Prior → ModalFormula Γ
  | .two => lower.possible.conj upper.possible
  | .low => lower.possible.conj (.neg upper.possible)
  | .up => (ModalFormula.neg lower.possible).conj upper.possible

noncomputable section

/-- All populations have the same actual law. The model is nonidentifiable,
not a claim that a constant statistic identifies the sign of a parameter. -/
def populationLaw (_hidden : HiddenMemory) : ProbabilityMeasure Bool := diracProbability false

def twoTest : NumericTest Bool ℝ where
  statistic := fun _ => 0
  measurableStatistic := measurable_const
  nullLaw := diracProbability 0
  tail := fun candidate observed => |observed| ≤ |candidate|
  measurableTail := fun _ => isClosed_le continuous_const continuous_abs |>.measurableSet

def lowTest : NumericTest Bool ℝ where
  statistic := fun _ => 0
  measurableStatistic := measurable_const
  nullLaw := diracProbability 0
  tail := fun candidate observed => candidate ≤ observed
  measurableTail := fun _ => measurableSet_Iic

def upTest : NumericTest Bool ℝ where
  statistic := fun _ => 0
  measurableStatistic := measurable_const
  nullLaw := diracProbability 0
  tail := fun candidate observed => observed ≤ candidate
  measurableTail := fun _ => measurableSet_Ici

def testFor (name : TestId) : NumericTest Bool ℝ :=
  if name = lowId then lowTest else if name = upId then upTest else twoTest

@[simp] theorem testFor_statistic (name : TestId) (d : Bool) :
    (testFor name).statistic d = 0 := by
  unfold testFor
  split_ifs <;> rfl

@[simp] theorem testFor_nullLaw (name : TestId) :
    (testFor name).nullLaw = diracProbability (0 : ℝ) := by
  unfold testFor
  split_ifs <;> rfl

@[simp] theorem testFor_pvalue (name : TestId) (d : Bool) :
    (testFor name).tailProbability d = 1 := by
  unfold testFor
  split_ifs <;> apply eventProbability_dirac_of_mem <;>
    simp [NumericTest.tailEvent, lowTest, upTest, twoTest]

/-- Scientific applicability binds the population pushforward to the null law. -/
def lawBinding (name : TestId) (hidden : HiddenMemory) : Prop :=
  (populationLaw hidden).map (testFor name).measurableStatistic.aemeasurable =
    (testFor name).nullLaw

 theorem statistic_law (name : TestId) (hidden : HiddenMemory) : lawBinding name hidden := by
  apply Subtype.ext
  change (Measure.dirac false).map (testFor name).statistic =
    ((testFor name).nullLaw : Measure ℝ)
  simpa only [testFor_statistic, testFor_nullLaw, diracProbability, ProbabilityMeasure.coe_mk] using
    Measure.map_dirac' (testFor name).measurableStatistic false

/-- A selected diagonal Dirac coupling with both actual marginals. -/
def zeroCoupling : ProbabilityCoupling (diracProbability (0 : ℝ))
    (diracProbability (0 : ℝ)) where
  joint := diracProbability ((0 : ℝ), (0 : ℝ))
  leftMarginal := by
    apply Subtype.ext
    exact Measure.map_dirac' measurable_fst ((0 : ℝ), (0 : ℝ))
  rightMarginal := by
    apply Subtype.ext
    exact Measure.map_dirac' measurable_snd ((0 : ℝ), (0 : ℝ))

def jointPopulationLaw (_hidden : HiddenMemory) : ProbabilityMeasure (Bool × Bool) :=
  diracProbability (false, false)

def pairStatistic (a b : TestId) (d : Bool × Bool) : ℝ × ℝ :=
  ((testFor a).statistic d.1, (testFor b).statistic d.2)

 theorem measurable_pairStatistic (a b : TestId) : Measurable (pairStatistic a b) :=
  ((testFor a).measurableStatistic.comp measurable_fst).prodMk
    ((testFor b).measurableStatistic.comp measurable_snd)

 theorem joint_statistic_law (a b : TestId) (hidden : HiddenMemory) :
    (jointPopulationLaw hidden).map (measurable_pairStatistic a b).aemeasurable =
      zeroCoupling.joint := by
  apply Subtype.ext
  change (Measure.dirac (false, false)).map (pairStatistic a b) =
    Measure.dirac ((0 : ℝ), (0 : ℝ))
  rw [Measure.map_dirac' (measurable_pairStatistic a b)]
  simp [pairStatistic]

def couplingFor (name : CouplingId) (left right : ValueSort)
    (μ : ProbabilityMeasure (Value left)) (ν : ProbabilityMeasure (Value right)) :
    Option (ProbabilityCoupling μ ν) := by
  classical
  cases left <;> cases right
  case real.real =>
    exact if name = pairId then
      if hμ : μ = diracProbability (0 : ℝ) then
        if hν : ν = diracProbability (0 : ℝ) then
          some (by subst μ; subst ν; exact zeroCoupling)
        else none
      else none
    else none
  all_goals exact none

 theorem couplingFor_selected (a b : TestId) :
    couplingFor pairId .real .real (testFor a).nullLaw (testFor b).nullLaw =
      some (show ProbabilityCoupling (testFor a).nullLaw (testFor b).nullLaw from
        (testFor_nullLaw a).symm ▸ (testFor_nullLaw b).symm ▸ zeroCoupling) := by
  simp [couplingFor]

def interpretation : AssertionInterpretation Bool Primitive :=
  { BHLExecution.interpretation with
    tests := fun _ name => testFor name
    hypotheses := fun h hidden =>
      if h = BHLExecution.Science.hypothesisId then theta hidden = 0
      else if h = lowerId then theta hidden < 0
      else if h = upperId then 0 < theta hidden else False
    requirements := fun h name pop hidden _ =>
      h = BHLExecution.Science.hypothesisId ∧ pop = BHLExecution.Science.populationId ∧ lawBinding name hidden
    jointRequirements := fun k hidden entries =>
      k = pairId ∧ (∃ d1 d2, entries = [(d1, twoId, BHLExecution.Science.populationId),
        (d2, upId, BHLExecution.Science.populationId)]) ∧
      (jointPopulationLaw hidden).map (measurable_pairStatistic twoId upId).aemeasurable =
        zeroCoupling.joint
    couplings := couplingFor }

def context (prior : Prior) : ProgramContext Bool := ProgramContext.ofRelations interpretation
  (fun hidden visible => (∃ n, allowed prior n ∧ hidden = hiddenMemory n) ∧
    visible = BHLExecution.initialSnapshot.visible)
  (fun hidden before after data pop =>
    pop = BHLExecution.Science.populationId ∧ after = before ∧ before.datasets BHLExecution.dataId = data ∧
      eventProbability (populationLaw hidden) {data} = 1)
  ⟨hiddenMemory 0, BHLExecution.initialSnapshot.visible, ⟨⟨0, by cases prior <;> simp [allowed], rfl⟩, rfl⟩⟩

def startWorld (n : Int) : World Bool Primitive := World.start
  (Memory.assemble BHLExecution.initialSnapshot.memory (hiddenMemory n)) BHLExecution.initialSnapshot.datasets

def sampledWorld (n : Int) : World Bool Primitive :=
  (startWorld n).extend ⟨(startWorld n).current.memory, BHLExecution.initialSnapshot.datasets, 0,
    .sample false BHLExecution.Science.populationId⟩

 theorem start_admitted (prior : Prior) (n : Int) (h : allowed prior n) :
    Admitted (context prior).model.dynamics (startWorld n) :=
  admitted_start _ BHLExecution.initialSnapshot.visible (hiddenMemory n) ⟨⟨n, h, rfl⟩, rfl⟩

 theorem sampled_admitted (prior : Prior) (n : Int) (h : allowed prior n) :
    Admitted (context prior).model.dynamics (sampledWorld n) := by
  apply admitted_extend (start_admitted prior n h)
  · rfl
  · change (BHLExecution.Science.populationId = BHLExecution.Science.populationId ∧
      BHLExecution.initialSnapshot.visible = BHLExecution.initialSnapshot.visible ∧ false = false ∧
      eventProbability (populationLaw (hiddenMemory n)) {false} = 1) ∧
      (0 : History Bool) = 0
    exact ⟨⟨rfl, rfl, rfl, eventProbability_dirac_of_mem false (by simp)⟩, rfl⟩

 theorem admitted_parameter {prior : Prior} {w : World Bool Primitive}
    (h : Admitted (context prior).model.dynamics w) : allowed prior (theta w.current.memory.hidden) := by
  obtain ⟨⟨n, hn, he⟩, _⟩ := (admitted_initial h).2
  rw [admitted_current_hidden h, he, theta_hiddenMemory]
  exact hn

 theorem sampled_accessible (a b : Int) : Accessible (sampledWorld a) (sampledWorld b) := by
  simp [Accessible, observeWorld, World.trace, World.extend, sampledWorld, startWorld,
    World.start, World.current, observeState, Memory.assemble]

@[simp] theorem lower_iff (prior : Prior) (env : GhostEnv Bool Primitive Γ)
    (w : World Bool Primitive) :
    referenceModalSatisfaction interpretation (context prior).model env w lower ↔
      theta w.current.memory.hidden < 0 := by
  simp [lower, referenceModalSatisfaction, atomMeaning, evalTerm, semanticView,
    interpretation, lowerId, upperId, BHLExecution.Science.hypothesisId,
    Lara.Examples.BHLBelief.hypothesisId]

@[simp] theorem upper_iff (prior : Prior) (env : GhostEnv Bool Primitive Γ)
    (w : World Bool Primitive) :
    referenceModalSatisfaction interpretation (context prior).model env w upper ↔
      0 < theta w.current.memory.hidden := by
  simp [upper, referenceModalSatisfaction, atomMeaning, evalTerm, semanticView,
    interpretation, lowerId, upperId, BHLExecution.Science.hypothesisId,
    Lara.Examples.BHLBelief.hypothesisId]

 theorem sampled_lower_possible (prior : Prior) (env : GhostEnv Bool Primitive Γ)
    (n : Int) (h : allowed prior (-1)) :
    referenceModalSatisfaction interpretation (context prior).model env (sampledWorld n)
      lower.possible := by
  apply (possible_iff_exists _ _ _).mpr
  refine ⟨sampledWorld (-1), sampled_admitted prior (-1) h, sampled_accessible n (-1), ?_⟩
  rw [lower_iff]
  simp [sampledWorld, startWorld]

 theorem sampled_upper_possible (prior : Prior) (env : GhostEnv Bool Primitive Γ)
    (n : Int) (h : allowed prior 1) :
    referenceModalSatisfaction interpretation (context prior).model env (sampledWorld n)
      upper.possible := by
  apply (possible_iff_exists _ _ _).mpr
  refine ⟨sampledWorld 1, sampled_admitted prior 1 h, sampled_accessible n 1, ?_⟩
  rw [upper_iff]
  simp [sampledWorld, startWorld]

 theorem low_upper_impossible (env : GhostEnv Bool Primitive Γ) (w : World Bool Primitive) :
    ¬ referenceModalSatisfaction interpretation (context .low).model env w upper.possible := by
  intro hp
  obtain ⟨v, hv, _, hup⟩ := (possible_iff_exists _ _ _).mp hp
  have hn := admitted_parameter hv
  rw [upper_iff] at hup
  simp only [allowed] at hn
  rcases hn with hn | hn <;> rw [hn] at hup <;> omega

 theorem up_lower_impossible (env : GhostEnv Bool Primitive Γ) (w : World Bool Primitive) :
    ¬ referenceModalSatisfaction interpretation (context .up).model env w lower.possible := by
  intro hp
  obtain ⟨v, hv, _, hlo⟩ := (possible_iff_exists _ _ _).mp hp
  have hn := admitted_parameter hv
  rw [lower_iff] at hlo
  simp only [allowed] at hn
  rcases hn with hn | hn <;> rw [hn] at hlo <;> omega

def sample (name : DatasetId) : ModalFormula Γ := .atom
  (.sampling (.datasetRead .ambient name) BHLExecution.Science.populationId (.provenanceOf .ambient))

def protectedOld : ModalFormula Γ := .atom
  (.equal (.valueRead .ambient BHLExecution.oldReport) (.rational (7 / 11)))

/-- The shared assertion states provenance, a protected cell, and the genuine
possible/excluded alternatives. It contains no belief or postcondition. -/
def ψ (prior : Prior) : Assertion Γ := .modal
  ((sample BHLExecution.dataId).conj ((sample BHLExecution.aliasId).conj
    (protectedOld.conj (priorFormula prior))))

def singleTest (name : TestId) : TestExpression Γ :=
  leaf Γ BHLExecution.Science.hypothesisId (.read BHLExecution.dataId) name BHLExecution.Science.populationId

def firstTest : TestExpression Γ := singleTest twoId
def secondTest : TestExpression Γ :=
  leaf Γ BHLExecution.Science.hypothesisId (.read BHLExecution.aliasId) upId BHLExecution.Science.populationId

 theorem lower_frame (r : Variable .real .observable) : ModalTestFrame r (lower : ModalFormula Γ) := by
  apply ModalTestFrame.atom
  apply AtomTestFrame.fresh
  intro region member
  simp only [AssertionAtom.readSupport, AssertionTerm.readSupport,
    List.mem_singleton] at member
  subst region
  trivial

 theorem upper_frame (r : Variable .real .observable) : ModalTestFrame r (upper : ModalFormula Γ) := by
  apply ModalTestFrame.atom
  apply AtomTestFrame.fresh
  intro region member
  simp only [AssertionAtom.readSupport, AssertionTerm.readSupport,
    List.mem_singleton] at member
  subst region
  trivial

 theorem alternative_frame (r : Variable .real .observable) :
    ModalTestFrame r (alternative : ModalFormula Γ) :=
  ModalTestFrame.disj (lower_frame r) (upper_frame r)

 theorem sample_frame (r : Variable .real .observable) (name : DatasetId) :
    ModalTestFrame r (sample name : ModalFormula Γ) := by
  apply ModalTestFrame.atom
  apply AtomTestFrame.fresh
  intro region member
  simp only [AssertionAtom.readSupport, AssertionTerm.readSupport,
    List.mem_append, List.mem_singleton] at member
  rcases member with rfl | rfl <;> trivial

 theorem ψ_frame (prior : Prior) (r : Variable .real .observable)
    (hne : BHLExecution.oldReport.id ≠ r.id) : AssertionTestFrame r (ψ prior : Assertion Γ) := by
  apply AssertionTestFrame.modal
  refine .conj (sample_frame r _) (.conj (sample_frame r _) (.conj ?_ ?_))
  · apply ModalTestFrame.atom
    apply AtomTestFrame.fresh
    intro region member
    simp only [AssertionAtom.readSupport, AssertionTerm.readSupport,
      List.append_nil, List.mem_singleton] at member
    subst region
    exact Or.inr (Or.inr hne)
  · cases prior with
    | two => exact .conj (.possible (lower_frame r)) (.possible (upper_frame r))
    | low => exact .conj (.possible (lower_frame r)) (.neg (.possible (upper_frame r)))
    | up => exact .conj (.neg (.possible (lower_frame r))) (.possible (upper_frame r))

 theorem requirements_of_sample (prior : Prior) (env : GhostEnv Bool Primitive Γ)
    (w : World Bool Primitive) (name : DatasetId) (test : TestId)
    (h : referenceModalSatisfaction interpretation (context prior).model env w (sample name)) :
    referenceModalSatisfaction interpretation (context prior).model env w
      (modelRequirementsFormula (leaf Γ BHLExecution.Science.hypothesisId (.read name) test
        BHLExecution.Science.populationId)) := by
  change ∃ v, some (semanticView (context prior).model.dynamics w) = some v ∧
    modelRequirements interpretation (context prior).model env v _
  refine ⟨_, rfl, ?_⟩
  intro d hd
  have hsample : (w.current.datasets name, BHLExecution.Science.populationId) ∈ w.samplingProvenance := by
    simpa [sample, referenceModalSatisfaction, atomMeaning, evalTerm, semanticView,
      State.visible] using h
  have he : d = w.current.datasets name := by
    simpa [leaf, DatasetExpr.toAssertionTerm, evalTerm, semanticView, State.visible] using hd.symm
  subst d
  exact ⟨⟨rfl, rfl, statistic_law test _⟩, hsample⟩

 theorem alternatives_exclusive (prior : Prior) :
    AssertionEntails (context prior) (.modal ((lower : ModalFormula Γ).conj upper))
      falseAssertion := by
  intro env w ⟨had, hlo, hup⟩
  have h1 := (lower_iff prior env w).mp hlo
  have h2 := (upper_iff prior env w).mp hup
  omega

def singleScience (prior : Prior) (name : TestId) :
    LeafScientificBinding (context prior) BHLExecution.Science.hypothesisId name BHLExecution.Science.populationId
      (nullAlternative (upper : ModalFormula Γ) lower) where
  populationLaw := populationLaw
  null_denotes := by
    intro env w _
    change (¬ referenceModalSatisfaction interpretation (context prior).model env w upper ∧
      ¬ referenceModalSatisfaction interpretation (context prior).model env w lower) ↔
      theta w.current.memory.hidden = 0
    rw [upper_iff, lower_iff]
    omega
  null_statistic_law := by
    intro hidden d _ _
    exact statistic_law name hidden

def alternativeScience (name : TestId) :
    LeafScientificBinding (context .two) BHLExecution.Science.hypothesisId name BHLExecution.Science.populationId
      (.neg (alternative : ModalFormula Γ)) where
  populationLaw := populationLaw
  null_denotes := by
    intro env w _
    change ¬ referenceModalSatisfaction interpretation (context .two).model env w
      (alternative : ModalFormula Γ) ↔ theta w.current.memory.hidden = 0
    simp only [alternative, referenceModalSatisfaction_disj, lower_iff, upper_iff]
    omega
  null_statistic_law := by
    intro hidden d _ _
    exact statistic_law name hidden

 theorem joint_population_marginals (hidden : HiddenMemory) :
    (jointPopulationLaw hidden).map measurable_fst.aemeasurable = populationLaw hidden ∧
    (jointPopulationLaw hidden).map measurable_snd.aemeasurable = populationLaw hidden := by
  constructor
  · apply Subtype.ext
    exact Measure.map_dirac' measurable_fst (false, false)
  · apply Subtype.ext
    exact Measure.map_dirac' measurable_snd (false, false)

def pairScience (mode : StatisticalMode) :
    PairScientificBinding (context .two) BHLExecution.Science.hypothesisId twoId BHLExecution.Science.populationId
      BHLExecution.Science.hypothesisId upId BHLExecution.Science.populationId pairId
      (alternative : ModalFormula Γ) alternative mode where
  left := alternativeScience twoId
  right := alternativeScience upId
  coupling := zeroCoupling
  selected := couplingFor_selected twoId upId
  jointPopulationLaw := jointPopulationLaw
  leftPopulationMarginal := by
    intro hidden d1 d2 _
    exact (joint_population_marginals hidden).1
  rightPopulationMarginal := by
    intro hidden d1 d2 _
    exact (joint_population_marginals hidden).2
  joint_null_law := by
    intro hidden d1 d2 _ _
    exact joint_statistic_law twoId upId hidden

def singleConditions (prior : Prior) (name : TestId) :
    SingleHTPremises (context prior) (ψ prior : Assertion Γ) lower upper BHLExecution.report
      BHLExecution.Science.hypothesisId (.read BHLExecution.dataId) name BHLExecution.Science.populationId
      (priorFormula prior) where
  frameψ := ψ_frame prior BHLExecution.report (by decide)
  frameL := lower_frame BHLExecution.report
  frameU := upper_frame BHLExecution.report
  data_fresh := by simp [DatasetExpr.reads]
  inputs := by
    intro env w ⟨had, _⟩
    exact ⟨had, w.current.datasets BHLExecution.dataId, rfl⟩
  meaningful := by
    intro env w ⟨had, hs, _, _, hp⟩
    exact ⟨had, requirements_of_sample prior env w BHLExecution.dataId name hs, hp⟩
  exclusive := alternatives_exclusive prior
  scientific := singleScience prior name

/-- All five rule values below are applications of the exact public interfaces. -/
theorem twoDerivation :
    Derivation (context .two) (singlePre (ψ .two : Assertion []))
      (.command (.test BHLExecution.report BHLExecution.Science.hypothesisId (.read BHLExecution.dataId) twoId BHLExecution.Science.populationId))
      (singlePost (ψ .two) BHLExecution.report (singleTest twoId) (lower.disj upper)) :=
  twoHT_derivable _ _ _ _ _ _ _ _ _ (singleConditions .two twoId)

theorem lowDerivation :
    Derivation (context .low) (singlePre (ψ .low : Assertion []))
      (.command (.test BHLExecution.report BHLExecution.Science.hypothesisId (.read BHLExecution.dataId) lowId BHLExecution.Science.populationId))
      (singlePost (ψ .low) BHLExecution.report (singleTest lowId) lower) :=
  lowHT_derivable _ _ _ _ _ _ _ _ _ (singleConditions .low lowId)

theorem upDerivation :
    Derivation (context .up) (singlePre (ψ .up : Assertion []))
      (.command (.test BHLExecution.report BHLExecution.Science.hypothesisId (.read BHLExecution.dataId) upId BHLExecution.Science.populationId))
      (singlePost (ψ .up) BHLExecution.report (singleTest upId) upper) :=
  upHT_derivable _ _ _ _ _ _ _ _ _ (singleConditions .up upId)

 theorem pair_requirements (env : GhostEnv Bool Primitive Γ) (w : World Bool Primitive)
    (mode : StatisticalMode)
    (h : referenceAssertionSatisfaction interpretation (context .two).model env w (ψ .two)) :
    referenceModalSatisfaction interpretation (context .two).model env w
      (modelRequirementsFormula (match mode with
        | .disj => .disj pairId firstTest secondTest
        | .conj => .conj pairId firstTest secondTest)) := by
  have h1 := requirements_of_sample .two env w BHLExecution.dataId twoId h.1
  have h2 := requirements_of_sample .two env w BHLExecution.aliasId upId h.2.1
  have hc : interpretation.jointRequirements pairId w.current.memory.hidden
      [(w.current.datasets BHLExecution.dataId, twoId, BHLExecution.Science.populationId),
       (w.current.datasets BHLExecution.aliasId, upId, BHLExecution.Science.populationId)] :=
    ⟨rfl, ⟨_, _, rfl⟩, joint_statistic_law twoId upId _⟩
  cases mode <;>
    simpa [modelRequirementsFormula, referenceModalSatisfaction, atomMeaning, evalTerm,
      modelRequirements, evalTestEntries, firstTest, secondTest, singleTest, leaf,
      DatasetExpr.toAssertionTerm, semanticView, State.visible] using
      (show modelRequirements interpretation (context .two).model env
        (semanticView (context .two).model.dynamics w) firstTest ∧
        modelRequirements interpretation (context .two).model env
          (semanticView (context .two).model.dynamics w) secondTest ∧
        interpretation.jointRequirements pairId w.current.memory.hidden
          [(w.current.datasets BHLExecution.dataId, twoId, BHLExecution.Science.populationId),
           (w.current.datasets BHLExecution.aliasId, upId, BHLExecution.Science.populationId)] from
        ⟨by simpa [modelRequirementsFormula, referenceModalSatisfaction, atomMeaning,
          evalTerm, firstTest, singleTest] using h1,
         by simpa [modelRequirementsFormula, referenceModalSatisfaction, atomMeaning,
          evalTerm, secondTest] using h2, hc⟩)

def multiConditions (mode : StatisticalMode) :
    MultiHTPremises (context .two) (ψ .two : Assertion Γ) alternative alternative
      BHLExecution.report secondReport BHLExecution.Science.hypothesisId BHLExecution.Science.hypothesisId
      (.read BHLExecution.dataId) (.read BHLExecution.aliasId) twoId upId
      BHLExecution.Science.populationId BHLExecution.Science.populationId pairId mode where
  outputs_ne := by decide
  dataset_fresh := by
    intro r hr y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hy
    rcases hr with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [DatasetExpr.reads]
  frameψ1 := ψ_frame .two BHLExecution.report (by decide)
  frameψ2 := ψ_frame .two secondReport (by decide)
  frameφ11 := alternative_frame BHLExecution.report
  frameφ12 := alternative_frame secondReport
  frameφ21 := alternative_frame BHLExecution.report
  frameφ22 := alternative_frame secondReport
  inputs := by
    intro env w ⟨had, _⟩
    exact ⟨had, ⟨w.current.datasets BHLExecution.dataId, rfl⟩, ⟨w.current.datasets BHLExecution.aliasId, rfl⟩⟩
  meaningful := by
    intro env w ⟨had, hψ⟩
    refine ⟨had, requirements_of_sample .two env w BHLExecution.aliasId upId hψ.2.1, ?_⟩
    have hp : referenceModalSatisfaction interpretation (context .two).model env w lower.possible :=
      hψ.2.2.2.1
    obtain ⟨v, hv, ha, hl⟩ := (possible_iff_exists _ _ _).mp hp
    apply (possible_iff_exists _ _ _).mpr
    refine ⟨v, hv, ha, ?_⟩
    have halt : referenceModalSatisfaction interpretation (context .two).model env v alternative :=
      (referenceModalSatisfaction_disj _ _ _ _ _ _).mpr (Or.inl hl)
    cases mode with
    | disj => exact (referenceModalSatisfaction_disj _ _ _ _ _ _).mpr (Or.inl halt)
    | conj => exact ⟨halt, halt⟩
  pair_meaningful := by
    intro env w ⟨had, hψ⟩
    exact ⟨had, pair_requirements env w mode hψ⟩
  scientific := pairScience mode

theorem multDisjDerivation :
    Derivation (context .two) (multiPre (ψ .two : Assertion []) BHLExecution.report firstTest alternative)
      (.command (.test secondReport BHLExecution.Science.hypothesisId (.read BHLExecution.aliasId) upId BHLExecution.Science.populationId))
      (multiDisjPost (ψ .two) BHLExecution.report secondReport firstTest secondTest pairId alternative alternative) :=
  multDisj_derivable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (multiConditions .disj)

theorem multConjDerivation :
    Derivation (context .two) (multiPre (ψ .two : Assertion []) BHLExecution.report firstTest alternative)
      (.command (.test secondReport BHLExecution.Science.hypothesisId (.read BHLExecution.aliasId) upId BHLExecution.Science.populationId))
      (multiConjPost (ψ .two) BHLExecution.report secondReport firstTest secondTest pairId alternative alternative) :=
  multConj_derivable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (multiConditions .conj)

end

/-- These are the existing executable source and scheduler, not a new interpreter. -/
def singleSource (name : TestId) : BHLExecution.Source := .command (.test BHLExecution.report BHLExecution.dataId name)
def pairSource : BHLExecution.Source := .seq (singleSource twoId)
  (.command (.test secondReport BHLExecution.aliasId upId))
def singleFinal (name : TestId) : BHLExecution.Snapshot :=
  { BHLExecution.initialSnapshot with
    rationals := Function.update BHLExecution.initialSnapshot.rationals BHLExecution.report.id (some 1)
    ledger := {(false, name)} }
def pairFinal : BHLExecution.Snapshot :=
  { singleFinal twoId with
    rationals := Function.update (singleFinal twoId).rationals secondReport.id (some 1)
    ledger := {(false, twoId)} + {(false, upId)} }
def singleEvents (name : TestId) : List BHLExecution.Event :=
  [⟨some (.test BHLExecution.report BHLExecution.dataId name), singleFinal name⟩]
def pairEvents : List BHLExecution.Event := singleEvents twoId ++
  [⟨some (.test secondReport BHLExecution.aliasId upId), pairFinal⟩]
def singleSmoke (name : TestId) :=
  BHLExecution.scheduled [true] (some (singleSource name)) BHLExecution.initialSnapshot
def pairSmoke := BHLExecution.scheduled [true, true] (some pairSource) BHLExecution.initialSnapshot

 theorem single_computes (name : TestId) :
    singleSmoke name = some (none, singleFinal name, singleEvents name) := rfl
 theorem pair_computes : pairSmoke = some (none, pairFinal, pairEvents) := rfl

noncomputable section

def singleWorld (n : Int) (name : TestId) := BHLExecution.eventsWorld (sampledWorld n) (singleEvents name)
def pairWorld (n : Int) := BHLExecution.eventsWorld (sampledWorld n) pairEvents

 theorem sampled_reifies (n : Int) : BHLExecution.Reifies (sampledWorld n) BHLExecution.initialSnapshot := by
  simp [BHLExecution.Reifies, sampledWorld, startWorld, BHLExecution.initialSnapshot, State.visible, BHLExecution.Snapshot.visible]

/-- Exact library effect correspondence is needed only for the real test leaves. -/
 theorem test_effect_eq (state : BHLExecution.Snapshot) (r : Variable .real .observable)
    (data : DatasetId) (name : TestId) :
    primitiveEffect interpretation (BHLExecution.Command.quote (.test r data name)) state.visible =
      primitiveEffect BHLExecution.interpretation (BHLExecution.Command.quote (.test r data name)) state.visible := by
  simp [primitiveEffect, evalPrimitive, BHLExecution.Command.quote, evalDatasetExpr,
    interpretation, BHLExecution.interpretation]

 theorem test_step (prior : Prior) (world : World Bool Primitive) (state after : BHLExecution.Snapshot)
    (r : Variable .real .observable) (data : DatasetId) (name : TestId)
    (represented : BHLExecution.Reifies world state)
    (computed : BHLExecution.Command.eval state (.test r data name) = some after) :
    Step (context prior) (some (.command (BHLExecution.Command.quote (.test r data name)))) world none
      (BHLExecution.eventWorld world ⟨some (.test r data name), after⟩) ∧
      BHLExecution.Reifies (BHLExecution.eventWorld world ⟨some (.test r data name), after⟩) after := by
  obtain ⟨delta, he, hledger⟩ := BHLExecution.command_correspondence state after (.test r data name) computed
  have enabled : primitiveEffect (context prior).interpretation
      (BHLExecution.Command.quote (.test r data name)) world.current.visible = some (after.visible, delta) := by
    change primitiveEffect interpretation _ _ = _
    rw [represented.1, test_effect_eq]
    exact he
  have equality : BHLExecution.eventWorld world ⟨some (.test r data name), after⟩ =
      world.extend (commandState world.current (BHLExecution.Command.quote (.test r data name))
        after.visible delta) := by
    simp [BHLExecution.eventWorld, commandState, BHLExecution.Snapshot.visible, ← hledger, represented.2]
  constructor
  · rw [equality]
    exact .command enabled
  · simp [BHLExecution.Reifies, BHLExecution.eventWorld, State.visible, BHLExecution.Snapshot.visible]

 theorem single_steps (prior : Prior) (n : Int) (name : TestId) :
    Steps (context prior) 1 (some (singleSource name).quote) (sampledWorld n) none
      (singleWorld n name) := by
  have first := (test_step prior (sampledWorld n) BHLExecution.initialSnapshot (singleFinal name)
    BHLExecution.report BHLExecution.dataId name (sampled_reifies n) rfl).1
  exact .cons first (.refl _ _)

 theorem single_reifies (prior : Prior) (n : Int) (name : TestId) :
    BHLExecution.Reifies (singleWorld n name) (singleFinal name) :=
  (test_step prior (sampledWorld n) BHLExecution.initialSnapshot (singleFinal name)
    BHLExecution.report BHLExecution.dataId name (sampled_reifies n) rfl).2

 theorem single_executes (prior : Prior) (n : Int) (name : TestId) (hn : allowed prior n) :
    executes (context prior) (singleSource name).quote (sampledWorld n) (singleWorld n name) :=
  ⟨trivial, sampled_admitted prior n hn, 1, single_steps prior n name⟩

 theorem second_step (n : Int) :
    Step (context .two) (some (.command (.test secondReport BHLExecution.Science.hypothesisId
      (.read BHLExecution.aliasId) upId BHLExecution.Science.populationId))) (singleWorld n twoId) none (pairWorld n) := by
  exact (test_step .two (singleWorld n twoId) (singleFinal twoId) pairFinal
    secondReport BHLExecution.aliasId upId (single_reifies .two n twoId) rfl).1

 theorem second_executes (n : Int) (hn : allowed .two n) :
    executes (context .two) (.command (.test secondReport BHLExecution.Science.hypothesisId
      (.read BHLExecution.aliasId) upId BHLExecution.Science.populationId)) (singleWorld n twoId) (pairWorld n) :=
  ⟨trivial, (show Run (context .two) _ _ _ _ from ⟨1, single_steps .two n twoId⟩).admitted
      (sampled_admitted .two n hn),
    1, .cons (second_step n) (.refl _ _)⟩

 theorem pair_steps (n : Int) :
    Steps (context .two) 2 (some pairSource.quote) (sampledWorld n) none (pairWorld n) := by
  have first := (test_step .two (sampledWorld n) BHLExecution.initialSnapshot (singleFinal twoId)
    BHLExecution.report BHLExecution.dataId twoId (sampled_reifies n) rfl).1
  exact .cons (.seqFinish first) (.cons (second_step n) (.refl _ _))

 theorem pair_executes (n : Int) (hn : allowed .two n) :
    executes (context .two) pairSource.quote (sampledWorld n) (pairWorld n) :=
  ⟨⟨trivial, trivial⟩, sampled_admitted .two n hn, 2, pair_steps n⟩

 theorem initial_pre (prior : Prior) (env : GhostEnv Bool Primitive Γ) :
    satisfies interpretation (context prior).model env (sampledWorld 0) (singlePre (ψ prior)) := by
  refine ⟨sampled_admitted prior 0 (by cases prior <;> simp [allowed]), ?_, ?_⟩
  · change referenceModalSatisfaction interpretation (context prior).model env (sampledWorld 0)
      ((sample BHLExecution.dataId).conj ((sample BHLExecution.aliasId).conj
        (protectedOld.conj (priorFormula prior))))
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [sample, referenceModalSatisfaction, atomMeaning, evalTerm, semanticView,
        sampledWorld, startWorld, World.samplingProvenance, World.extend,
        World.current, World.trace, World.start, BHLExecution.initialSnapshot, State.visible]
    · simp [sample, referenceModalSatisfaction, atomMeaning, evalTerm, semanticView,
        sampledWorld, startWorld, World.samplingProvenance, World.extend,
        World.current, World.trace, World.start, BHLExecution.initialSnapshot, State.visible]
    · simp [protectedOld, referenceModalSatisfaction, atomMeaning, evalTerm, semanticView,
        sampledWorld, startWorld, BHLExecution.initialSnapshot, BHLExecution.Snapshot.memory,
        Memory.read, Memory.assemble, State.visible]
    · cases prior with
      | two => exact ⟨sampled_lower_possible .two env 0 (by simp [allowed]),
          sampled_upper_possible .two env 0 (by simp [allowed])⟩
      | low => exact ⟨sampled_lower_possible .low env 0 (by simp [allowed]),
          low_upper_impossible env _⟩
      | up => exact ⟨up_lower_impossible env _,
          sampled_upper_possible .up env 0 (by simp [allowed])⟩
  · simp [referenceAssertionSatisfaction, referenceModalSatisfaction,
      atomMeaning, evalTerm, semanticView, sampledWorld]

 theorem two_final :
    satisfies interpretation (context .two).model GhostEnv.empty (singleWorld 0 twoId)
      (singlePost (ψ .two : Assertion []) BHLExecution.report (singleTest twoId) (lower.disj upper)) :=
  derivation_sound twoDerivation _ _ _ (initial_pre .two GhostEnv.empty)
    (single_executes .two 0 twoId (by simp [allowed]))

 theorem low_final :
    satisfies interpretation (context .low).model GhostEnv.empty (singleWorld 0 lowId)
      (singlePost (ψ .low : Assertion []) BHLExecution.report (singleTest lowId) lower) :=
  derivation_sound lowDerivation _ _ _ (initial_pre .low GhostEnv.empty)
    (single_executes .low 0 lowId (by simp [allowed]))

 theorem up_final :
    satisfies interpretation (context .up).model GhostEnv.empty (singleWorld 0 upId)
      (singlePost (ψ .up : Assertion []) BHLExecution.report (singleTest upId) upper) :=
  derivation_sound upDerivation _ _ _ (initial_pre .up GhostEnv.empty)
    (single_executes .up 0 upId (by simp [allowed]))

@[simp] theorem single_report (n : Int) (name : TestId) :
    (singleWorld n name).current.memory.read BHLExecution.report = some (1 : ℝ) := by
  simp [singleWorld, BHLExecution.eventsWorld, singleEvents, BHLExecution.eventWorld, singleFinal,
    Memory.read, Memory.assemble, BHLExecution.Snapshot.memory, BHLExecution.report]

@[simp] theorem single_data (n : Int) (name : TestId) (data : DatasetId) :
    (singleWorld n name).current.datasets data = false := rfl

 theorem single_stored (env : GhostEnv Bool Primitive Γ) (n : Int) (name : TestId) :
    referenceAssertionSatisfaction interpretation (context .two).model env (singleWorld n name)
      (stored BHLExecution.report (singleTest name)) := by
  change ∃ v, evalTerm interpretation (context .two).model env
      (semanticView (context .two).model.dynamics (singleWorld n name)) (report Γ BHLExecution.report) = some v ∧
    evalTerm interpretation (context .two).model env
      (semanticView (context .two).model.dynamics (singleWorld n name)) (.pvalue (singleTest name)) =
      some v
  refine ⟨1, ?_, ?_⟩
  · simpa [report, evalTerm, semanticView, Memory.read, Memory.assemble,
      Memory.observable, State.visible] using single_report n name
  · simp [singleTest, leaf, DatasetExpr.toAssertionTerm, evalTerm, evalNumericalEvent,
      interpretation, semanticView, State.visible]

 theorem single_range (env : GhostEnv Bool Primitive Γ) (n : Int) (name : TestId) :
    referenceAssertionSatisfaction interpretation (context .two).model env (singleWorld n name)
      (reportRange Γ BHLExecution.report) := by
  simp [referenceAssertionSatisfaction, referenceModalSatisfaction,
    atomMeaning, evalTerm, semanticView, State.visible, compareReal, Memory.read, Memory.assemble,
    singleWorld, BHLExecution.eventsWorld, singleEvents, BHLExecution.eventWorld,
    singleFinal, BHLExecution.Snapshot.memory, BHLExecution.report]

/-- First belief is obtained from a real first run; stored equality is proved
separately, never inferred from that belief. -/
 theorem multi_pre :
    satisfies interpretation (context .two).model GhostEnv.empty (singleWorld 0 twoId)
      (multiPre (ψ .two : Assertion []) BHLExecution.report firstTest alternative) := by
  rcases two_final with ⟨had, hψ, hh, hb⟩
  exact ⟨had, hψ, hh, hb, single_stored GhostEnv.empty 0 twoId,
    single_range GhostEnv.empty 0 twoId⟩

 theorem multDisj_final :
    satisfies interpretation (context .two).model GhostEnv.empty (pairWorld 0)
      (multiDisjPost (ψ .two : Assertion []) BHLExecution.report secondReport firstTest secondTest
        pairId alternative alternative) :=
  derivation_sound multDisjDerivation _ _ _ multi_pre
    (second_executes 0 (by simp [allowed]))

 theorem multConj_final :
    satisfies interpretation (context .two).model GhostEnv.empty (pairWorld 0)
      (multiConjPost (ψ .two : Assertion []) BHLExecution.report secondReport firstTest secondTest
        pairId alternative alternative) :=
  derivation_sound multConjDerivation _ _ _ multi_pre
    (second_executes 0 (by simp [allowed]))

/-- Aliasing is by actual dataset value: both leaves denote false, and the
ledger is the entire two-occurrence multiset, not selected counters. -/
 theorem pair_ledger (n : Int) :
    (pairWorld n).current.history = {(false, twoId)} + {(false, upId)} := rfl

 theorem pair_reports (n : Int) :
    (pairWorld n).current.memory.read BHLExecution.report = some (1 : ℝ) ∧
    (pairWorld n).current.memory.read secondReport = some (1 : ℝ) ∧
    (pairWorld n).current.memory.read BHLExecution.oldReport = some ((7 / 11 : ℚ) : ℝ) := by
  simp [pairWorld, pairEvents, singleEvents, BHLExecution.eventsWorld, BHLExecution.eventWorld, pairFinal,
    singleFinal, BHLExecution.initialSnapshot, BHLExecution.Snapshot.memory, Memory.read, Memory.assemble,
    BHLExecution.report, secondReport, BHLExecution.oldReport]

 theorem pair_stored (env : GhostEnv Bool Primitive Γ) (n : Int) :
    referenceAssertionSatisfaction interpretation (context .two).model env (pairWorld n)
      (stored BHLExecution.report firstTest) ∧
    referenceAssertionSatisfaction interpretation (context .two).model env (pairWorld n)
      (stored secondReport secondTest) := by
  have hr := pair_reports n
  constructor
  · change ∃ v, evalTerm interpretation (context .two).model env
        (semanticView (context .two).model.dynamics (pairWorld n)) (report Γ BHLExecution.report) = some v ∧
      evalTerm interpretation (context .two).model env
        (semanticView (context .two).model.dynamics (pairWorld n)) (.pvalue firstTest) = some v
    refine ⟨1, ?_, ?_⟩
    · simpa [report, evalTerm, semanticView, Memory.read, Memory.assemble,
        Memory.observable, State.visible] using hr.1
    · simp [firstTest, singleTest, leaf, DatasetExpr.toAssertionTerm, evalTerm,
        evalNumericalEvent, interpretation, semanticView, State.visible, pairWorld, pairEvents,
        singleEvents, BHLExecution.eventsWorld, BHLExecution.eventWorld, pairFinal, singleFinal, BHLExecution.initialSnapshot]
  · change ∃ v, evalTerm interpretation (context .two).model env
        (semanticView (context .two).model.dynamics (pairWorld n)) (report Γ secondReport) = some v ∧
      evalTerm interpretation (context .two).model env
        (semanticView (context .two).model.dynamics (pairWorld n)) (.pvalue secondTest) = some v
    refine ⟨1, ?_, ?_⟩
    · simpa [report, evalTerm, semanticView, Memory.read, Memory.assemble,
        Memory.observable, State.visible] using hr.2.1
    · simp [secondTest, leaf, DatasetExpr.toAssertionTerm, evalTerm,
        evalNumericalEvent, interpretation, semanticView, State.visible, pairWorld, pairEvents,
        singleEvents, BHLExecution.eventsWorld, BHLExecution.eventWorld, pairFinal, singleFinal, BHLExecution.initialSnapshot]

def unionEvent : NumericalEvent (.product .real .real) :=
  NumericalEvent.union (NumericalEvent.tail (testFor twoId) false)
    (NumericalEvent.tail (testFor upId) false)
    zeroCoupling

def intersectionEvent : NumericalEvent (.product .real .real) :=
  NumericalEvent.intersection (NumericalEvent.tail (testFor twoId) false)
    (NumericalEvent.tail (testFor upId) false)
    zeroCoupling

 theorem union_probability : unionEvent.probability = 1 := by
  unfold unionEvent NumericalEvent.probability NumericalEvent.union
  change eventProbability (diracProbability ((0 : ℝ), (0 : ℝ))) _ = 1
  apply eventProbability_dirac_of_mem
  simp [NumericalEvent.tail, NumericTest.tailEvent, testFor, twoId, lowId, upId,
    twoTest, upTest]

 theorem intersection_probability : intersectionEvent.probability = 1 := by
  unfold intersectionEvent NumericalEvent.probability NumericalEvent.intersection
  change eventProbability (diracProbability ((0 : ℝ), (0 : ℝ))) _ = 1
  apply eventProbability_dirac_of_mem
  simp [NumericalEvent.tail, NumericTest.tailEvent, testFor, twoId, lowId, upId,
    twoTest, upTest]

 theorem composite_bounds :
    unionEvent.probability ≤ (1 : ℝ) + 1 ∧
    intersectionEvent.probability ≤ min (1 : ℝ) 1 := by
  rw [union_probability, intersection_probability]
  norm_num

end

/-- The rational encoding is the actual one-point null joint law. -/
def finiteNullJoint : List (ℚ × ℚ × ℚ) := [(0, 0, 1)]
def finiteUnionMass : ℚ := finiteNullJoint.foldl (fun mass entry =>
  if |(0 : ℚ)| ≤ |entry.1| ∨ (0 : ℚ) ≤ entry.2.1 then mass + entry.2.2 else mass) 0
def finiteIntersectionMass : ℚ := finiteNullJoint.foldl (fun mass entry =>
  if |(0 : ℚ)| ≤ |entry.1| ∧ (0 : ℚ) ≤ entry.2.1 then mass + entry.2.2 else mass) 0

def priorCheck : Prior → Bool
  | .two => decide (allowed .two (-1) ∧ allowed .two 1)
  | .low => decide (allowed .low (-1) ∧ ¬ allowed .low 1)
  | .up => decide (¬ allowed .up (-1) ∧ allowed .up 1)

def preCheck (prior : Prior) (state : BHLExecution.Snapshot) : Bool :=
  priorCheck prior && decide (state.ledger = 0 ∧
    state.datasets BHLExecution.dataId = false ∧ state.datasets BHLExecution.aliasId = false ∧
    state.rationals BHLExecution.oldReport.id = some (7 / 11))

def singlePostCheck (name : TestId) (state : BHLExecution.Snapshot) : Bool :=
  decide (state.ledger = {(false, name)} ∧ state.rationals BHLExecution.report.id = some 1 ∧
    state.rationals BHLExecution.oldReport.id = some (7 / 11) ∧
    state.datasets BHLExecution.dataId = false ∧ state.datasets BHLExecution.aliasId = false)

def pairPostCheck (isUnion : Bool) (state : BHLExecution.Snapshot) : Bool :=
  decide (state.ledger = {(false, twoId)} + {(false, upId)} ∧
    state.rationals BHLExecution.report.id = some 1 ∧ state.rationals secondReport.id = some 1 ∧
    state.rationals BHLExecution.oldReport.id = some (7 / 11) ∧
    state.datasets BHLExecution.dataId = false ∧ state.datasets BHLExecution.aliasId = false ∧
    (if isUnion then finiteUnionMass ≤ (1 : ℚ) + 1
      else finiteIntersectionMass ≤ min (1 : ℚ) 1))

def smokeObservations : Bool × Bool × Bool × Bool × Bool :=
  ((singleSmoke twoId).any fun out => out.1.isNone && preCheck .two BHLExecution.initialSnapshot &&
      singlePostCheck twoId out.2.1,
   (singleSmoke lowId).any fun out => out.1.isNone && preCheck .low BHLExecution.initialSnapshot &&
      singlePostCheck lowId out.2.1,
   (singleSmoke upId).any fun out => out.1.isNone && preCheck .up BHLExecution.initialSnapshot &&
      singlePostCheck upId out.2.1,
   pairSmoke.any fun out => out.1.isNone && pairPostCheck true out.2.1,
   pairSmoke.any fun out => out.1.isNone && pairPostCheck false out.2.1)

 theorem finite_union_mass : finiteUnionMass = 1 := by
  norm_num [finiteUnionMass, finiteNullJoint]
 theorem finite_intersection_mass : finiteIntersectionMass = 1 := by
  norm_num [finiteIntersectionMass, finiteNullJoint]
 theorem pre_checks (prior : Prior) : preCheck prior BHLExecution.initialSnapshot = true := by
  cases prior <;> simp [preCheck, priorCheck, allowed, BHLExecution.initialSnapshot,
    BHLExecution.oldReport, BHLExecution.x, BHLExecution.y]
 theorem single_post_checks (name : TestId) :
    singlePostCheck name (singleFinal name) = true := by
  simp [singlePostCheck, singleFinal, BHLExecution.initialSnapshot, BHLExecution.report, BHLExecution.oldReport]
 theorem pair_post_checks (mode : Bool) : pairPostCheck mode pairFinal = true := by
  cases mode <;> norm_num [pairPostCheck, pairFinal, singleFinal, BHLExecution.initialSnapshot,
    BHLExecution.report, secondReport, BHLExecution.oldReport, finite_union_mass,
    finite_intersection_mass]
 theorem smoke_observations : smokeObservations = (true, true, true, true, true) := by
  simp [smokeObservations, single_computes, pair_computes, pre_checks,
    single_post_checks, pair_post_checks]

noncomputable section

 theorem finite_union_correspondence : (finiteUnionMass : ℝ) = unionEvent.probability := by
  rw [finite_union_mass, union_probability]
  norm_num

 theorem finite_intersection_correspondence :
    (finiteIntersectionMass : ℝ) = intersectionEvent.probability := by
  rw [finite_intersection_mass, intersection_probability]
  norm_num

/-- The evaluators correspond to the actual assertions and actual executions,
not merely to a hard-coded display of the probability bounds. -/
 theorem two_smoke_correspondence :
    singlePostCheck twoId (singleFinal twoId) = true ↔
      satisfies interpretation (context .two).model GhostEnv.empty (singleWorld 0 twoId)
        (singlePost (ψ .two : Assertion []) BHLExecution.report (singleTest twoId) alternative) :=
  ⟨fun _ => two_final, fun _ => single_post_checks twoId⟩

 theorem low_smoke_correspondence :
    singlePostCheck lowId (singleFinal lowId) = true ↔
      satisfies interpretation (context .low).model GhostEnv.empty (singleWorld 0 lowId)
        (singlePost (ψ .low : Assertion []) BHLExecution.report (singleTest lowId) lower) :=
  ⟨fun _ => low_final, fun _ => single_post_checks lowId⟩

 theorem up_smoke_correspondence :
    singlePostCheck upId (singleFinal upId) = true ↔
      satisfies interpretation (context .up).model GhostEnv.empty (singleWorld 0 upId)
        (singlePost (ψ .up : Assertion []) BHLExecution.report (singleTest upId) upper) :=
  ⟨fun _ => up_final, fun _ => single_post_checks upId⟩

 theorem multDisj_smoke_correspondence :
    pairPostCheck true pairFinal = true ↔
      satisfies interpretation (context .two).model GhostEnv.empty (pairWorld 0)
        (multiDisjPost (ψ .two : Assertion []) BHLExecution.report secondReport firstTest secondTest
          pairId alternative alternative) :=
  ⟨fun _ => multDisj_final, fun _ => pair_post_checks true⟩

 theorem multConj_smoke_correspondence :
    pairPostCheck false pairFinal = true ↔
      satisfies interpretation (context .two).model GhostEnv.empty (pairWorld 0)
        (multiConjPost (ψ .two : Assertion []) BHLExecution.report secondReport firstTest secondTest
          pairId alternative alternative) :=
  ⟨fun _ => multConj_final, fun _ => pair_post_checks false⟩

 theorem pre_smoke_correspondence (prior : Prior) :
    preCheck prior BHLExecution.initialSnapshot = true ↔
      satisfies interpretation (context prior).model GhostEnv.empty (sampledWorld 0)
        (singlePre (ψ prior : Assertion [])) :=
  ⟨fun _ => initial_pre prior GhostEnv.empty, fun _ => pre_checks prior⟩

/-- The pre-state used for every rule is an admitted genuine null world. -/
 theorem genuine_null (prior : Prior) (env : GhostEnv Bool Primitive Γ) :
    Admitted (context prior).model.dynamics (sampledWorld 0) ∧
    referenceModalSatisfaction interpretation (context prior).model env (sampledWorld 0)
      (nullAlternative (upper : ModalFormula Γ) lower) := by
  refine ⟨sampled_admitted prior 0 (by cases prior <;> simp [allowed]), ?_⟩
  change ¬ referenceModalSatisfaction interpretation (context prior).model env
      (sampledWorld 0) upper ∧
    ¬ referenceModalSatisfaction interpretation (context prior).model env
      (sampledWorld 0) lower
  rw [upper_iff, lower_iff]
  simp [sampledWorld, startWorld]

 theorem three_parameters :
    Admitted (context .two).model.dynamics (sampledWorld (-1)) ∧
    Admitted (context .two).model.dynamics (sampledWorld 0) ∧
    Admitted (context .two).model.dynamics (sampledWorld 1) :=
  ⟨sampled_admitted .two (-1) (by simp [allowed]),
    sampled_admitted .two 0 (by simp [allowed]),
    sampled_admitted .two 1 (by simp [allowed])⟩

 theorem hiddenMemory_injective : Function.Injective hiddenMemory := by
  intro a b he
  have := congrArg theta he
  simpa using this

 theorem pair_counts (n : Int) :
    History.count (pairWorld n).current.history false twoId = 1 ∧
    History.count (pairWorld n).current.history false upId = 1 := by
  simp [pair_ledger, History.count, twoId, upId]

 theorem first_report_protected (n : Int) :
    (pairWorld n).current.memory.read BHLExecution.report =
      (singleWorld n twoId).current.memory.read BHLExecution.report := by
  rw [(pair_reports n).1, single_report]

 theorem dataset_frame (n : Int) :
    (pairWorld n).current.datasets = (sampledWorld n).current.datasets := rfl

/-- Actual selected numerical events at the actual second-test endpoint. -/
 theorem pair_event_disj (env : GhostEnv Bool Primitive Γ) (n : Int) :
    evalNumericalEvent interpretation (context .two).model env
      (semanticView (context .two).model.dynamics (pairWorld n))
      (.disj pairId (firstTest : TestExpression Γ) secondTest) =
      some ⟨.product .real .real, unionEvent⟩ := by
  exact evalNumericalEvent_disj_of_coupling interpretation (context .two).model env
    (semanticView (context .two).model.dynamics (pairWorld n)) pairId firstTest secondTest
    ⟨.real, NumericalEvent.tail (testFor twoId) false⟩
    ⟨.real, NumericalEvent.tail (testFor upId) false⟩ zeroCoupling rfl rfl
    (couplingFor_selected twoId upId)

 theorem pair_event_conj (env : GhostEnv Bool Primitive Γ) (n : Int) :
    evalNumericalEvent interpretation (context .two).model env
      (semanticView (context .two).model.dynamics (pairWorld n))
      (.conj pairId (firstTest : TestExpression Γ) secondTest) =
      some ⟨.product .real .real, intersectionEvent⟩ := by
  exact evalNumericalEvent_conj_of_coupling interpretation (context .two).model env
    (semanticView (context .two).model.dynamics (pairWorld n)) pairId firstTest secondTest
    ⟨.real, NumericalEvent.tail (testFor twoId) false⟩
    ⟨.real, NumericalEvent.tail (testFor upId) false⟩ zeroCoupling rfl rfl
    (couplingFor_selected twoId upId)

 theorem pair_pvalues (env : GhostEnv Bool Primitive Γ) (n : Int) :
    evalTerm interpretation (context .two).model env
      (semanticView (context .two).model.dynamics (pairWorld n))
      (.pvalue (.disj pairId (firstTest : TestExpression Γ) secondTest)) = some (1 : ℝ) ∧
    evalTerm interpretation (context .two).model env
      (semanticView (context .two).model.dynamics (pairWorld n))
      (.pvalue (.conj pairId (firstTest : TestExpression Γ) secondTest)) = some (1 : ℝ) := by
  simp [evalTerm, pair_event_disj, pair_event_conj, union_probability, intersection_probability]

 theorem stored_thresholds (env : GhostEnv Bool Primitive Γ) (n : Int) :
    evalTerm interpretation (context .two).model env
      (semanticView (context .two).model.dynamics (pairWorld n))
      (.realAdd (report Γ BHLExecution.report) (report Γ secondReport)) = some (2 : ℝ) ∧
    evalTerm interpretation (context .two).model env
      (semanticView (context .two).model.dynamics (pairWorld n))
      (.realMin (report Γ BHLExecution.report) (report Γ secondReport)) = some (1 : ℝ) := by
  have h1 : evalTerm interpretation (context .two).model env
      (semanticView (context .two).model.dynamics (pairWorld n)) (report Γ BHLExecution.report) =
      some (1 : ℝ) := by
    simpa [report, evalTerm, semanticView, Memory.read, Memory.assemble,
      Memory.observable, State.visible] using (pair_reports n).1
  have h2 : evalTerm interpretation (context .two).model env
      (semanticView (context .two).model.dynamics (pairWorld n)) (report Γ secondReport) =
      some (1 : ℝ) := by
    simpa [report, evalTerm, semanticView, Memory.read, Memory.assemble,
      Memory.observable, State.visible] using (pair_reports n).2.1
  constructor
  · change (do
      let a ← evalTerm interpretation (context .two).model env
        (semanticView (context .two).model.dynamics (pairWorld n)) (report Γ BHLExecution.report)
      let b ← evalTerm interpretation (context .two).model env
        (semanticView (context .two).model.dynamics (pairWorld n)) (report Γ secondReport)
      pure (a + b)) = some 2
    rw [h1, h2]
    norm_num
  · change (do
      let a ← evalTerm interpretation (context .two).model env
        (semanticView (context .two).model.dynamics (pairWorld n)) (report Γ BHLExecution.report)
      let b ← evalTerm interpretation (context .two).model env
        (semanticView (context .two).model.dynamics (pairWorld n)) (report Γ secondReport)
      pure (min a b)) = some 1
    rw [h1, h2]
    norm_num

end
end Lara.Examples.BHLSoundnessScience
