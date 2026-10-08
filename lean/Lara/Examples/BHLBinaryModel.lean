import Lara.BHL.Tests.Binary
import Lara.Examples.BHLSoundnessScience

/-!
An informative finite population instance of the existing BHL model.

The null parameter is zero; lower and upper alternatives are the actual hidden
integers -1 and 1. Every Boolean sample has positive mass under both the null
and the alternative. The initial relation admits all two-draw observations,
not only the exceptional true/true witness used by the examples. The selected
joint population law is the independent product declared by this instance;
independence is not inferred from coincident observed values or alias names.
-/

namespace Lara.Examples.BHLBinaryModel

open Lara.BHL MeasureTheory
open Lara.Examples.BHLSoundnessScience
  (Prior allowed parameter theta hiddenMemory lowerId upperId lower upper alternative priorFormula pairId)
open Lara.Examples.BHLExecution (Snapshot report oldReport dataId aliasId)
open Lara.Examples.BHLBelief (hypothesisId populationId)

noncomputable section

/-- These are distinct kernel test identities, even when both observations agree. -/
def firstId : TestId := ⟨0⟩
def secondId : TestId := ⟨1⟩
def lowId : TestId := ⟨2⟩
def upId : TestId := ⟨3⟩
def hiddenId : TestId := ⟨4⟩

def modeFor (name : TestId) : Tests.Binary.Mode :=
  if name = lowId then .low else if name = upId then .up else .two

def testFor (name : TestId) : NumericTest Bool ℝ := Tests.Binary.test (modeFor name)

@[simp] theorem testFor_pvalue (name : TestId) (d : Bool) :
    (testFor name).tailProbability d = (Tests.Binary.pvalue d : ℝ) :=
  Tests.Binary.pvalue_correct (modeFor name) d

/-- This is a genuine nonconstant population law, not the PR05 Dirac witness. -/
def populationLaw (hidden : HiddenMemory) : ProbabilityMeasure Bool :=
  if theta hidden = 0 then FiniteProbability.probability Tests.Binary.null
  else FiniteProbability.probability Tests.Binary.alternative

def jointPopulationLaw (hidden : HiddenMemory) : ProbabilityMeasure (Bool × Bool) :=
  if theta hidden = 0 then FiniteProbability.probability Tests.Binary.nullJoint
  else FiniteProbability.probability Tests.Binary.alternativeJoint

 theorem population_support (hidden : HiddenMemory) (d : Bool) :
    0 < eventProbability (populationLaw hidden) {d} := by
  unfold populationLaw
  split_ifs
  · rw [FiniteProbability.eventProbability_probability_set]
    cases d <;> norm_num [Tests.Binary.null, Fintype.sum_bool]
  · rw [FiniteProbability.eventProbability_probability_set]
    cases d <;> norm_num [Tests.Binary.alternative, Fintype.sum_bool]

 theorem null_statistic_law (name : TestId) (hidden : HiddenMemory)
    (null : theta hidden = 0) :
    (populationLaw hidden).map (testFor name).measurableStatistic.aemeasurable =
      (testFor name).nullLaw := by
  simp [populationLaw, null, testFor, Tests.Binary.test]

 theorem joint_population_marginals (hidden : HiddenMemory) :
    (jointPopulationLaw hidden).map measurable_fst.aemeasurable = populationLaw hidden ∧
    (jointPopulationLaw hidden).map measurable_snd.aemeasurable = populationLaw hidden := by
  unfold jointPopulationLaw populationLaw
  split_ifs
  · exact ⟨Tests.Binary.null_population_left_marginal,
      Tests.Binary.null_population_right_marginal⟩
  · exact ⟨Tests.Binary.alternative_population_left_marginal,
      Tests.Binary.alternative_population_right_marginal⟩

/-- Only the named two-sided pair coupling is selected; incompatible laws reject. -/
def couplingFor (name : CouplingId) (left right : ValueSort)
    (μ : ProbabilityMeasure (Value left)) (ν : ProbabilityMeasure (Value right)) :
    Option (ProbabilityCoupling μ ν) := by
  classical
  cases left <;> cases right
  case real.real =>
    exact if name = pairId then
      if hμ : μ = (Tests.Binary.test .two).nullLaw then
        if hν : ν = (Tests.Binary.test .two).nullLaw then
          some (by subst μ; subst ν; exact Tests.Binary.nullCoupling .two .two)
        else none
      else none
    else none
  all_goals exact none

 theorem couplingFor_selected :
    couplingFor pairId .real .real (testFor firstId).nullLaw (testFor secondId).nullLaw =
      some (show ProbabilityCoupling (testFor firstId).nullLaw (testFor secondId).nullLaw from
        Tests.Binary.nullCoupling .two .two) := by
  simp [couplingFor, testFor, modeFor, firstId, secondId, lowId, upId]

/-- Applicability states identified population and positive source support;
conditional null-law agreement is proved separately, not supplied as a flag. -/
def interpretation : AssertionInterpretation Bool Primitive :=
  { Lara.Examples.BHLExecution.interpretation with
    tests := fun _ name => testFor name
    hypotheses := fun h hidden =>
      if h = hypothesisId then theta hidden = 0
      else if h = lowerId then theta hidden < 0
      else if h = upperId then 0 < theta hidden else False
    requirements := fun h _ pop hidden d =>
      h = hypothesisId ∧ pop = populationId ∧
        0 < eventProbability (populationLaw hidden) {d}
    jointRequirements := fun k hidden entries =>
      k = pairId ∧ (∃ d1 d2, entries = [(d1, firstId, populationId),
        (d2, secondId, populationId)] ∧
        0 < eventProbability (jointPopulationLaw hidden) {(d1, d2)})
    couplings := couplingFor }

/-- Both actual draws are public, with the old protected rational cell untouched. -/
def initialSnapshot (first second : Bool) : Snapshot :=
  { Lara.Examples.BHLExecution.initialSnapshot with
    datasets := fun name => if name = aliasId then second else first }

def context (prior : Prior) : ProgramContext Bool := ProgramContext.ofRelations interpretation
  (fun hidden visible => (∃ n, allowed prior n ∧ hidden = hiddenMemory n) ∧
    ∃ first second, visible = (initialSnapshot first second).visible)
  (fun hidden before after data pop =>
    pop = populationId ∧ after = before ∧
      (before.datasets dataId = data ∨ before.datasets aliasId = data) ∧
      0 < eventProbability (populationLaw hidden) {data})
  ⟨hiddenMemory 0, (initialSnapshot true true).visible,
    ⟨⟨0, by cases prior <;> simp [allowed], rfl⟩, true, true, rfl⟩⟩

def startWorld (n : Int) (first second : Bool) : World Bool Primitive := World.start
  (Memory.assemble (initialSnapshot first second).memory (hiddenMemory n))
    (initialSnapshot first second).datasets

def firstSample (n : Int) (first second : Bool) : World Bool Primitive :=
  (startWorld n first second).extend
    ⟨(startWorld n first second).current.memory, (initialSnapshot first second).datasets,
      0, .sample first populationId⟩

def sampledWorld (n : Int) (first second : Bool) : World Bool Primitive :=
  (firstSample n first second).extend
    ⟨(firstSample n first second).current.memory, (initialSnapshot first second).datasets,
      0, .sample second populationId⟩

 theorem start_admitted (prior : Prior) (n : Int) (first second : Bool) (h : allowed prior n) :
    Admitted (context prior).model.dynamics (startWorld n first second) :=
  admitted_start _ (initialSnapshot first second).visible (hiddenMemory n)
    ⟨⟨n, h, rfl⟩, first, second, rfl⟩

 theorem first_sample_admitted (prior : Prior) (n : Int) (first second : Bool)
    (h : allowed prior n) :
    Admitted (context prior).model.dynamics (firstSample n first second) := by
  apply admitted_extend (start_admitted prior n first second h)
  · rfl
  · change (populationId = populationId ∧
      (initialSnapshot first second).visible = (initialSnapshot first second).visible ∧
      ((initialSnapshot first second).datasets dataId = first ∨
        (initialSnapshot first second).datasets aliasId = first) ∧
      0 < eventProbability (populationLaw (hiddenMemory n)) {first}) ∧
      (0 : History Bool) = 0
    refine ⟨⟨rfl, rfl, Or.inl ?_, population_support _ _⟩, rfl⟩
    simp [initialSnapshot, dataId, aliasId]

 theorem sampled_admitted (prior : Prior) (n : Int) (first second : Bool)
    (h : allowed prior n) :
    Admitted (context prior).model.dynamics (sampledWorld n first second) := by
  apply admitted_extend (first_sample_admitted prior n first second h)
  · rfl
  · change (populationId = populationId ∧
      (initialSnapshot first second).visible = (initialSnapshot first second).visible ∧
      ((initialSnapshot first second).datasets dataId = second ∨
        (initialSnapshot first second).datasets aliasId = second) ∧
      0 < eventProbability (populationLaw (hiddenMemory n)) {second}) ∧
      (0 : History Bool) = 0
    exact ⟨⟨rfl, rfl, Or.inr (by simp [initialSnapshot]), population_support _ _⟩, rfl⟩

 theorem admitted_parameter {prior : Prior} {w : World Bool Primitive}
    (h : Admitted (context prior).model.dynamics w) : allowed prior (theta w.current.memory.hidden) := by
  obtain ⟨⟨n, hn, he⟩, _⟩ := (admitted_initial h).2
  rw [admitted_current_hidden h, he, Lara.Examples.BHLSoundnessScience.theta_hiddenMemory]
  exact hn

 theorem sampled_accessible (a b : Int) (first second : Bool) :
    Accessible (sampledWorld a first second) (sampledWorld b first second) := by
  simp [Accessible, observeWorld, World.trace, World.extend, sampledWorld, firstSample,
    startWorld, World.start, World.current, observeState, Memory.assemble]

@[simp] theorem lower_iff (prior : Prior) (env : GhostEnv Bool Primitive Γ)
    (w : World Bool Primitive) :
    referenceModalSatisfaction interpretation (context prior).model env w lower ↔
      theta w.current.memory.hidden < 0 := by
  simp [lower, referenceModalSatisfaction, atomMeaning, evalTerm, semanticView,
    interpretation, lowerId, upperId, hypothesisId]

@[simp] theorem upper_iff (prior : Prior) (env : GhostEnv Bool Primitive Γ)
    (w : World Bool Primitive) :
    referenceModalSatisfaction interpretation (context prior).model env w upper ↔
      0 < theta w.current.memory.hidden := by
  simp [upper, referenceModalSatisfaction, atomMeaning, evalTerm, semanticView,
    interpretation, lowerId, upperId, hypothesisId]

end
end Lara.Examples.BHLBinaryModel
