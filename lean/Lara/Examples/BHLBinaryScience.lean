import Lara.Examples.BHLBinaryModel

/-!
Concrete applications of the existing five scientific HT rules.

Applicability is positive population support plus actual sampling provenance.
Null statistic laws, product population marginals and the selected joint null
law are proved from the finite model. No applicability field certifies a
postcondition or supplies an assumed calibration inequality.
-/

namespace Lara.Examples.BHLBinaryScience

open Lara.BHL MeasureTheory
open Lara.Examples.BHLBinaryModel
open Lara.Examples.BHLSoundnessScience
  (Prior allowed theta hiddenMemory lower upper alternative priorFormula
    sample protectedOld ψ singleTest lower_frame upper_frame alternative_frame ψ_frame pairId secondReport)
open Lara.Examples.BHLExecution (report dataId aliasId)
open Lara.Examples.BHLBelief (hypothesisId populationId)

noncomputable section

def firstTest : TestExpression Γ := singleTest firstId
def secondTest : TestExpression Γ :=
  leaf Γ hypothesisId (.read aliasId) secondId populationId

 theorem sampled_lower_possible (prior : Prior) (env : GhostEnv Bool Primitive Γ)
    (n : Int) (first second : Bool) (h : allowed prior (-1)) :
    referenceModalSatisfaction interpretation (context prior).model env (sampledWorld n first second)
      lower.possible := by
  apply (possible_iff_exists _ _ _).mpr
  refine ⟨sampledWorld (-1) first second, sampled_admitted prior (-1) first second h,
    sampled_accessible n (-1) first second, ?_⟩
  rw [lower_iff]
  simp [sampledWorld, firstSample, startWorld, Lara.Examples.BHLSoundnessScience.theta_hiddenMemory]

 theorem sampled_upper_possible (prior : Prior) (env : GhostEnv Bool Primitive Γ)
    (n : Int) (first second : Bool) (h : allowed prior 1) :
    referenceModalSatisfaction interpretation (context prior).model env (sampledWorld n first second)
      upper.possible := by
  apply (possible_iff_exists _ _ _).mpr
  refine ⟨sampledWorld 1 first second, sampled_admitted prior 1 first second h,
    sampled_accessible n 1 first second, ?_⟩
  rw [upper_iff]
  simp [sampledWorld, firstSample, startWorld, Lara.Examples.BHLSoundnessScience.theta_hiddenMemory]

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

 theorem requirements_of_sample (prior : Prior) (env : GhostEnv Bool Primitive Γ)
    (w : World Bool Primitive) (name : DatasetId) (test : TestId)
    (h : referenceModalSatisfaction interpretation (context prior).model env w (sample name)) :
    referenceModalSatisfaction interpretation (context prior).model env w
      (modelRequirementsFormula (leaf Γ hypothesisId (.read name) test populationId)) := by
  change ∃ v, some (semanticView (context prior).model.dynamics w) = some v ∧
    modelRequirements interpretation (context prior).model env v _
  refine ⟨_, rfl, ?_⟩
  intro d hd
  have hsample : (w.current.datasets name, populationId) ∈ w.samplingProvenance := by
    simpa [sample, referenceModalSatisfaction, atomMeaning, evalTerm, semanticView,
      State.visible] using h
  have he : d = w.current.datasets name := by
    simpa [leaf, DatasetExpr.toAssertionTerm, evalTerm, semanticView, State.visible] using hd.symm
  subst d
  exact ⟨⟨rfl, rfl, population_support _ _⟩, hsample⟩

 theorem alternatives_exclusive (prior : Prior) :
    AssertionEntails (context prior) (.modal ((lower : ModalFormula Γ).conj upper))
      falseAssertion := by
  intro env w ⟨had, hlo, hup⟩
  have h1 := (lower_iff prior env w).mp hlo
  have h2 := (upper_iff prior env w).mp hup
  omega

/-- The conditional law is proved under the actual null hypothesis. -/
def singleScience (prior : Prior) (name : TestId) :
    LeafScientificBinding (context prior) hypothesisId name populationId
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
    intro hidden d _ null
    change theta hidden = 0 at null
    exact BHLBinaryModel.null_statistic_law name hidden null

 def alternativeScience (name : TestId) :
    LeafScientificBinding (context .two) hypothesisId name populationId
      (.neg (alternative : ModalFormula Γ)) where
  populationLaw := populationLaw
  null_denotes := by
    intro env w _
    change ¬ referenceModalSatisfaction interpretation (context .two).model env w
      (alternative : ModalFormula Γ) ↔ theta w.current.memory.hidden = 0
    simp only [alternative, referenceModalSatisfaction_disj, lower_iff, upper_iff]
    omega
  null_statistic_law := by
    intro hidden d _ null
    change theta hidden = 0 at null
    exact BHLBinaryModel.null_statistic_law name hidden null

 theorem joint_population_support (hidden : HiddenMemory) (first second : Bool) :
    0 < eventProbability (jointPopulationLaw hidden) {(first, second)} := by
  unfold jointPopulationLaw
  split_ifs
  · rw [FiniteProbability.eventProbability_probability_set]
    cases first <;> cases second <;>
      norm_num [Tests.Binary.nullJoint, FiniteProbability.product, Tests.Binary.null,
        Fintype.sum_prod_type, Fintype.sum_bool]
  · rw [FiniteProbability.eventProbability_probability_set]
    cases first <;> cases second <;>
      norm_num [Tests.Binary.alternativeJoint, FiniteProbability.product, Tests.Binary.alternative,
        Fintype.sum_prod_type, Fintype.sum_bool]

 theorem joint_null_statistic_law (hidden : HiddenMemory) (null : theta hidden = 0) :
    (jointPopulationLaw hidden).map (Tests.Binary.measurable_pairStatistic .two .two).aemeasurable =
      (Tests.Binary.nullCoupling .two .two).joint := by
  simp [jointPopulationLaw, null, Tests.Binary.nullCoupling]

 def pairScience (mode : StatisticalMode) :
    PairScientificBinding (context .two) hypothesisId firstId populationId
      hypothesisId secondId populationId pairId
      (alternative : ModalFormula Γ) alternative mode where
  left := alternativeScience firstId
  right := alternativeScience secondId
  coupling := Tests.Binary.nullCoupling .two .two
  selected := couplingFor_selected
  jointPopulationLaw := jointPopulationLaw
  leftPopulationMarginal := by
    intro hidden d1 d2 _
    exact (joint_population_marginals hidden).1
  rightPopulationMarginal := by
    intro hidden d1 d2 _
    exact (joint_population_marginals hidden).2
  joint_null_law := by
    intro hidden d1 d2 _ null
    change StatisticalMode.hypotheses interpretation hypothesisId hypothesisId hidden mode at null
    have hnull : theta hidden = 0 := by
      cases mode <;> simpa [StatisticalMode.hypotheses, interpretation] using null
    exact joint_null_statistic_law hidden hnull

 def singleConditions (prior : Prior) (name : TestId) :
    SingleHTPremises (context prior) (ψ prior : Assertion Γ) lower upper report
      hypothesisId (.read dataId) name populationId (priorFormula prior) where
  frameψ := ψ_frame prior report (by decide)
  frameL := lower_frame report
  frameU := upper_frame report
  data_fresh := by simp [DatasetExpr.reads]
  inputs := by
    intro env w ⟨had, _⟩
    exact ⟨had, w.current.datasets dataId, rfl⟩
  meaningful := by
    intro env w ⟨had, hs, _, _, hp⟩
    exact ⟨had, requirements_of_sample prior env w dataId name hs, hp⟩
  exclusive := alternatives_exclusive prior
  scientific := singleScience prior name

 theorem twoDerivation :
    Derivation (context .two) (singlePre (ψ .two : Assertion []))
      (.command (.test report hypothesisId (.read dataId) firstId populationId))
      (singlePost (ψ .two) report (singleTest firstId) (lower.disj upper)) :=
  twoHT_derivable _ _ _ _ _ _ _ _ _ (singleConditions .two firstId)

 theorem lowDerivation :
    Derivation (context .low) (singlePre (ψ .low : Assertion []))
      (.command (.test report hypothesisId (.read dataId) lowId populationId))
      (singlePost (ψ .low) report (singleTest lowId) lower) :=
  lowHT_derivable _ _ _ _ _ _ _ _ _ (singleConditions .low lowId)

 theorem upDerivation :
    Derivation (context .up) (singlePre (ψ .up : Assertion []))
      (.command (.test report hypothesisId (.read dataId) upId populationId))
      (singlePost (ψ .up) report (singleTest upId) upper) :=
  upHT_derivable _ _ _ _ _ _ _ _ _ (singleConditions .up upId)

 theorem pair_requirements (env : GhostEnv Bool Primitive Γ) (w : World Bool Primitive)
    (mode : StatisticalMode)
    (h : referenceAssertionSatisfaction interpretation (context .two).model env w (ψ .two)) :
    referenceModalSatisfaction interpretation (context .two).model env w
      (modelRequirementsFormula (match mode with
        | .disj => .disj pairId firstTest secondTest
        | .conj => .conj pairId firstTest secondTest)) := by
  have h1 := requirements_of_sample .two env w dataId firstId h.1
  have h2 := requirements_of_sample .two env w aliasId secondId h.2.1
  have hc : interpretation.jointRequirements pairId w.current.memory.hidden
      [(w.current.datasets dataId, firstId, populationId),
       (w.current.datasets aliasId, secondId, populationId)] :=
    ⟨rfl, ⟨_, _, rfl, joint_population_support _ _ _⟩⟩
  cases mode <;>
    simpa [modelRequirementsFormula, referenceModalSatisfaction, atomMeaning, evalTerm,
      modelRequirements, evalTestEntries, firstTest, secondTest, singleTest, leaf,
      DatasetExpr.toAssertionTerm, semanticView, State.visible] using
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

 def multiConditions (mode : StatisticalMode) :
    MultiHTPremises (context .two) (ψ .two : Assertion Γ) alternative alternative
      report secondReport hypothesisId hypothesisId (.read dataId) (.read aliasId) firstId secondId
      populationId populationId pairId mode where
  outputs_ne := by decide
  dataset_fresh := by
    intro r hr y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hy
    rcases hr with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [DatasetExpr.reads]
  frameψ1 := ψ_frame .two report (by decide)
  frameψ2 := ψ_frame .two secondReport (by decide)
  frameφ11 := alternative_frame report
  frameφ12 := alternative_frame secondReport
  frameφ21 := alternative_frame report
  frameφ22 := alternative_frame secondReport
  inputs := by
    intro env w ⟨had, _⟩
    exact ⟨had, ⟨w.current.datasets dataId, rfl⟩, ⟨w.current.datasets aliasId, rfl⟩⟩
  meaningful := by
    intro env w ⟨had, hψ⟩
    refine ⟨had, requirements_of_sample .two env w aliasId secondId hψ.2.1, ?_⟩
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
    Derivation (context .two) (multiPre (ψ .two : Assertion []) report firstTest alternative)
      (.command (.test secondReport hypothesisId (.read aliasId) secondId populationId))
      (multiDisjPost (ψ .two) report secondReport firstTest secondTest pairId alternative alternative) :=
  multDisj_derivable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (multiConditions .disj)

 theorem multConjDerivation :
    Derivation (context .two) (multiPre (ψ .two : Assertion []) report firstTest alternative)
      (.command (.test secondReport hypothesisId (.read aliasId) secondId populationId))
      (multiConjPost (ψ .two) report secondReport firstTest secondTest pairId alternative alternative) :=
  multConj_derivable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (multiConditions .conj)

end
end Lara.Examples.BHLBinaryScience
