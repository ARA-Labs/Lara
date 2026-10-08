import Lara.BHL.FiniteProbability
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Tactic

/-!
# Exact finite statistical instance for the Boolean two-draw population

The informative simple null puts mass `1/4` on the true Boolean observation and
`3/4` on false; the distinct nonzero alternative reverses the pair. Three
inclusive tail modes (`two`, `low`, `up`) act on the hidden integer statistic
value (`-1`, `0`, `1`), giving `test mode : NumericTest Bool ℝ` whose null law is
the genuine pushforward of `FiniteProbability.probability null`. The p-value is
computed by finite null-tail summation, agrees exactly with the real tail
probability, and is superuniform at every nonnegative threshold (inclusive
ties); the strict tails are not, with a zero-threshold counterexample. The
population joint is the independent product `nullJoint = product null null`; the
coupling is its pushforward under the pair statistic, with both population and
statistic marginals proved and all Boolean union/intersection event masses
computed as genuine measure events.
-/

namespace Lara.BHL.Tests.Binary

open MeasureTheory Set
open scoped BigOperators

/-- The three inclusive tail modes. -/
inductive Mode where
  | two
  | low
  | up
  deriving DecidableEq

/-- The informative simple null: the true observation has mass one quarter. -/
def null : FiniteProbability.Law Bool where
  mass d := if d then 1 / 4 else 3 / 4
  nonnegative := by intro d; cases d <;> norm_num
  normalized := by norm_num [Fintype.sum_bool]

/-- A nonzero alternative, distinct from the null at both observations. -/
def alternative : FiniteProbability.Law Bool where
  mass d := if d then 3 / 4 else 1 / 4
  nonnegative := by intro d; cases d <;> norm_num
  normalized := by norm_num [Fintype.sum_bool]

/-- The independent product joint population law of the two actual draws. -/
def nullJoint : FiniteProbability.Law (Bool × Bool) :=
  FiniteProbability.product null null

def alternativeJoint : FiniteProbability.Law (Bool × Bool) :=
  FiniteProbability.product alternative alternative

@[simp] theorem null_mass_true : null.mass true = 1 / 4 := rfl
@[simp] theorem null_mass_false : null.mass false = 3 / 4 := rfl
@[simp] theorem alternative_mass_true : alternative.mass true = 3 / 4 := rfl
@[simp] theorem alternative_mass_false : alternative.mass false = 1 / 4 := rfl

theorem null_ne_alternative : null ≠ alternative := by
  intro equal
  have h := congrArg (fun law : FiniteProbability.Law Bool => law.mass true) equal
  norm_num at h

/-- Source sampling support has positive mass on both outcomes. -/
theorem null_mass_positive (d : Bool) : 0 < null.mass d := by
  cases d <;> norm_num

theorem alternative_mass_positive (d : Bool) : 0 < alternative.mass d := by
  cases d <;> norm_num

/-- Genuine real singleton masses of the null population. -/
theorem null_probability_true :
    eventProbability (FiniteProbability.probability null) ({true} : Set Bool) = 1 / 4 := by
  rw [FiniteProbability.eventProbability_probability_set, Fintype.sum_bool]
  norm_num [null]

theorem null_probability_false :
    eventProbability (FiniteProbability.probability null) ({false} : Set Bool) = 3 / 4 := by
  rw [FiniteProbability.eventProbability_probability_set, Fintype.sum_bool]
  norm_num [null]

theorem alternative_probability_true :
    eventProbability (FiniteProbability.probability alternative)
      ({true} : Set Bool) = 3 / 4 := by
  rw [FiniteProbability.eventProbability_probability_set, Fintype.sum_bool]
  norm_num [alternative]

theorem alternative_probability_false :
    eventProbability (FiniteProbability.probability alternative)
      ({false} : Set Bool) = 1 / 4 := by
  rw [FiniteProbability.eventProbability_probability_set, Fintype.sum_bool]
  norm_num [alternative]

theorem null_probability_true_pos :
    0 < eventProbability (FiniteProbability.probability null) ({true} : Set Bool) := by
  rw [null_probability_true]; norm_num

theorem null_probability_false_pos :
    0 < eventProbability (FiniteProbability.probability null) ({false} : Set Bool) := by
  rw [null_probability_false]; norm_num

theorem alternative_probability_true_pos :
    0 < eventProbability (FiniteProbability.probability alternative) ({true} : Set Bool) := by
  rw [alternative_probability_true]; norm_num

theorem alternative_probability_false_pos :
    0 < eventProbability (FiniteProbability.probability alternative) ({false} : Set Bool) := by
  rw [alternative_probability_false]; norm_num

/-- Hidden integer statistic values; the tails select them. -/
def statistic : Mode → Bool → ℚ
  | .low, true => -1
  | .two, true => 1
  | .up, true => 1
  | _, false => 0

@[simp] theorem statistic_false (mode : Mode) : statistic mode false = 0 := by
  cases mode <;> rfl

@[simp] theorem statistic_low_true : statistic .low true = -1 := rfl
@[simp] theorem statistic_two_true : statistic .two true = 1 := rfl
@[simp] theorem statistic_up_true : statistic .up true = 1 := rfl

/-- Inclusive rational tail relations, ties included. -/
def rationalTail : Mode → ℚ → ℚ → Prop
  | .two, candidate, observed => |observed| ≤ |candidate|
  | .low, candidate, observed => candidate ≤ observed
  | .up, candidate, observed => observed ≤ candidate

instance (mode : Mode) (candidate observed : ℚ) :
    Decidable (rationalTail mode candidate observed) := by
  cases mode <;> unfold rationalTail <;> infer_instance

/-- The computed p-value: finite null-tail summation over the two-sided statistic. -/
def pvalue (d : Bool) : ℚ :=
  FiniteProbability.eventMass null
    (fun candidate => decide (rationalTail .two (statistic .two candidate) (statistic .two d)))

@[simp] theorem pvalue_true : pvalue true = 1 / 4 := by
  norm_num [pvalue, FiniteProbability.eventMass, Fintype.sum_bool, null, rationalTail,
    statistic]

@[simp] theorem pvalue_false : pvalue false = 1 := by
  norm_num [pvalue, FiniteProbability.eventMass, Fintype.sum_bool, null, rationalTail,
    statistic]

/-- Every inclusive mode's rational tail mass coincides with the computed p-value. -/
theorem rationalTail_probability (mode : Mode) (d : Bool) :
    FiniteProbability.eventMass null
      (fun candidate => decide (rationalTail mode (statistic mode candidate)
        (statistic mode d))) = pvalue d := by
  cases mode <;> cases d <;>
    norm_num [pvalue, FiniteProbability.eventMass, Fintype.sum_bool, null, rationalTail,
      statistic]

/-- Inclusive real tail relations on the statistic space. -/
def realTail : Mode → ℝ → ℝ → Prop
  | .two, candidate, observed => |observed| ≤ |candidate|
  | .low, candidate, observed => candidate ≤ observed
  | .up, candidate, observed => observed ≤ candidate

theorem measurable_statistic (mode : Mode) :
    Measurable (fun d : Bool => (statistic mode d : ℝ)) :=
  measurable_of_finite _

theorem measurable_realTail (mode : Mode) (observed : ℝ) :
    MeasurableSet {candidate | realTail mode candidate observed} := by
  cases mode
  · exact (isClosed_le continuous_const continuous_abs).measurableSet
  · exact measurableSet_Iic
  · exact measurableSet_Ici

/-- The actual pushed-forward test: null law is the real measure of `null`. -/
noncomputable def test (mode : Mode) : NumericTest Bool ℝ where
  statistic d := (statistic mode d : ℝ)
  measurableStatistic := measurable_statistic mode
  nullLaw := (FiniteProbability.probability null).map (measurable_statistic mode).aemeasurable
  tail := realTail mode
  measurableTail := measurable_realTail mode

theorem test_statistic_eq (mode : Mode) :
    (test mode).statistic = fun d : Bool => (statistic mode d : ℝ) := rfl

theorem test_tail_eq (mode : Mode) : (test mode).tail = realTail mode := rfl

theorem test_nullLaw_eq (mode : Mode) :
    (test mode).nullLaw =
      (FiniteProbability.probability null).map (measurable_statistic mode).aemeasurable := rfl

/-- On this two-point population all three inclusive modes select the same samples. -/
theorem tail_on_samples (mode : Mode) (candidate observed : Bool) :
    (test mode).tail ((test mode).statistic candidate) ((test mode).statistic observed) ↔
      candidate = true ∨ observed = false := by
  rw [test_tail_eq, test_statistic_eq]
  cases mode <;> cases candidate <;> cases observed <;>
    norm_num [realTail, statistic]

/-- The null tail event pulled back to the sample space is a computable Bool set. -/
theorem tail_event_preimage (mode : Mode) (d : Bool) :
    (test mode).statistic ⁻¹' (test mode).tailEvent ((test mode).statistic d) =
      {c : Bool | (c || !d) = true} := by
  ext c
  change (test mode).tail ((test mode).statistic c) ((test mode).statistic d) ↔
    (c || !d) = true
  rw [tail_on_samples mode c d]
  cases c <;> cases d <;> decide

theorem pvalue_correct (mode : Mode) (d : Bool) :
    (test mode).tailProbability d = (pvalue d : ℝ) := by
  unfold NumericTest.tailProbability
  rw [test_nullLaw_eq]
  rw [eventProbability_map _ (measurable_statistic mode) ((test mode).measurable_tailEvent _)]
  change eventProbability (FiniteProbability.probability null)
      ((test mode).statistic ⁻¹' (test mode).tailEvent ((test mode).statistic d)) =
    (pvalue d : ℝ)
  rw [tail_event_preimage mode d, FiniteProbability.eventProbability_probability_set,
    Fintype.sum_bool]
  simp only [Set.mem_setOf_eq]
  cases d <;> norm_num [FiniteProbability.eventMass, Fintype.sum_bool, null, pvalue,
    rationalTail, statistic]

@[simp] theorem tailProbability_true (mode : Mode) :
    (test mode).tailProbability true = 1 / 4 := by
  rw [pvalue_correct]
  norm_num

@[simp] theorem tailProbability_false (mode : Mode) :
    (test mode).tailProbability false = 1 := by
  rw [pvalue_correct]
  norm_num

/-- Exact null calibration distribution, ties included, for every real threshold. -/
theorem calibration_mass_real (mode : Mode) (α : ℝ) :
    eventProbability (FiniteProbability.probability null)
      {d | (test mode).tailProbability d ≤ α} =
      if 1 ≤ α then 1 else if (1 / 4 : ℝ) ≤ α then 1 / 4 else 0 := by
  classical
  have hset : {d : Bool | (test mode).tailProbability d ≤ α} =
      {b : Bool | decide ((test mode).tailProbability b ≤ α) = true} := by
    ext b
    simp
  rw [hset, FiniteProbability.eventProbability_probability_set, Fintype.sum_bool]
  simp only [Set.mem_setOf_eq, decide_eq_true_eq, tailProbability_true, tailProbability_false,
    null_mass_true, null_mass_false]
  by_cases hb : (1 : ℝ) ≤ α
  · have ha : (1 / 4 : ℝ) ≤ α := by linarith
    simp only [hb, ha, if_true]
    norm_num
  · by_cases ha : (1 / 4 : ℝ) ≤ α
    · simp only [hb, ha, if_true, if_false]
      norm_num
    · simp only [hb, ha, if_false]
      norm_num

/-- No calibration premise is assumed: the inclusive test is superuniform at
every nonnegative real threshold. -/
theorem superuniform (mode : Mode) (α : ℝ) (nonnegative : 0 ≤ α) :
    eventProbability (FiniteProbability.probability null)
      {d | (test mode).tailProbability d ≤ α} ≤ α := by
  rw [calibration_mass_real]
  by_cases hb : (1 : ℝ) ≤ α
  · rw [if_pos hb]
    exact hb
  · rw [if_neg hb]
    by_cases ha : (1 / 4 : ℝ) ≤ α
    · rw [if_pos ha]
      exact ha
    · rw [if_neg ha]
      exact nonnegative

/-- Exact rational calibration distribution of the computed p-value. -/
theorem calibration_mass_rational (α : ℚ) :
    FiniteProbability.eventMass null (fun d => decide (pvalue d ≤ α)) =
      if 1 ≤ α then 1 else if (1 / 4 : ℚ) ≤ α then 1 / 4 else 0 := by
  rw [FiniteProbability.eventMass, Fintype.sum_bool]
  simp only [decide_eq_true_eq, pvalue_true, pvalue_false, null_mass_true, null_mass_false]
  by_cases hb : (1 : ℚ) ≤ α
  · have ha : (1 / 4 : ℚ) ≤ α := by linarith
    simp only [hb, ha, if_true]
    norm_num
  · by_cases ha : (1 / 4 : ℚ) ≤ α
    · simp only [hb, ha, if_true, if_false]
      norm_num
    · simp only [hb, ha, if_false]
      norm_num

theorem superuniform_rational (mode : Mode) (α : ℚ) (nonnegative : 0 ≤ α) :
    eventProbability (FiniteProbability.probability null)
      {d | (test mode).tailProbability d ≤ (α : ℝ)} ≤ (α : ℝ) :=
  superuniform mode (α : ℝ) (by exact_mod_cast nonnegative)

/-- Rational specialization of superuniformity, phrased on the computable mass. -/
theorem calibration_rational_le (α : ℚ) (nonnegative : 0 ≤ α) :
    FiniteProbability.eventMass null (fun d => decide (pvalue d ≤ α)) ≤ α := by
  rw [calibration_mass_rational]
  by_cases hb : (1 : ℚ) ≤ α
  · rw [if_pos hb]
    exact hb
  · rw [if_neg hb]
    by_cases ha : (1 / 4 : ℚ) ≤ α
    · rw [if_pos ha]
      exact ha
    · rw [if_neg ha]
      exact nonnegative

/-- Informative size at the exact threshold: the null rejects with probability 1/4. -/
theorem null_rejection_at_quarter (mode : Mode) :
    eventProbability (FiniteProbability.probability null)
      {d | (test mode).tailProbability d ≤ 1 / 4} = 1 / 4 := by
  rw [calibration_mass_real]
  norm_num

/-- The nonzero alternative rejects with probability 3/4 at threshold 1/4. -/
theorem alternative_rejection_at_quarter (mode : Mode) :
    eventProbability (FiniteProbability.probability alternative)
      {d | (test mode).tailProbability d ≤ 1 / 4} = 3 / 4 := by
  classical
  have hset : {d : Bool | (test mode).tailProbability d ≤ 1 / 4} =
      {b : Bool | decide ((test mode).tailProbability b ≤ 1 / 4) = true} := by
    ext b
    simp
  rw [hset, FiniteProbability.eventProbability_probability_set, Fintype.sum_bool]
  simp only [Set.mem_setOf_eq, decide_eq_true_eq, tailProbability_true, tailProbability_false,
    alternative_mass_true, alternative_mass_false]
  norm_num

/-- Strict (tie-dropping) real tail relations, deliberately not calibrated. -/
def strictRealTail : Mode → ℝ → ℝ → Prop
  | .two, candidate, observed => |observed| < |candidate|
  | .low, candidate, observed => candidate < observed
  | .up, candidate, observed => observed < candidate

theorem measurable_strictRealTail (mode : Mode) (observed : ℝ) :
    MeasurableSet {candidate | strictRealTail mode candidate observed} := by
  cases mode
  · exact (isOpen_lt continuous_const continuous_abs).measurableSet
  · exact measurableSet_Iio
  · exact measurableSet_Ioi

noncomputable def strictTest (mode : Mode) : NumericTest Bool ℝ where
  statistic := (test mode).statistic
  measurableStatistic := (test mode).measurableStatistic
  nullLaw := (test mode).nullLaw
  tail := strictRealTail mode
  measurableTail := measurable_strictRealTail mode

theorem strictTest_statistic_eq (mode : Mode) :
    (strictTest mode).statistic = (test mode).statistic := rfl

theorem strictTest_tail_eq (mode : Mode) :
    (strictTest mode).tail = strictRealTail mode := rfl

theorem strictTest_nullLaw_eq (mode : Mode) :
    (strictTest mode).nullLaw = (test mode).nullLaw := rfl

theorem strictTail_on_samples (mode : Mode) (candidate observed : Bool) :
    (strictTest mode).tail ((strictTest mode).statistic candidate)
      ((strictTest mode).statistic observed) ↔ candidate = true ∧ observed = false := by
  rw [strictTest_tail_eq, strictTest_statistic_eq, test_statistic_eq]
  cases mode <;> cases candidate <;> cases observed <;>
    norm_num [strictRealTail, statistic]

theorem strict_tail_event_preimage (mode : Mode) (d : Bool) :
    (strictTest mode).statistic ⁻¹'
        (strictTest mode).tailEvent ((strictTest mode).statistic d) =
      {c : Bool | (c && !d) = true} := by
  ext c
  change (strictTest mode).tail ((strictTest mode).statistic c)
      ((strictTest mode).statistic d) ↔ (c && !d) = true
  rw [strictTail_on_samples mode c d]
  cases c <;> cases d <;> decide

@[simp] theorem strict_tailProbability_true (mode : Mode) :
    (strictTest mode).tailProbability true = 0 := by
  unfold NumericTest.tailProbability
  rw [strictTest_nullLaw_eq, test_nullLaw_eq]
  rw [eventProbability_map _ (measurable_statistic mode)
    ((strictTest mode).measurable_tailEvent _)]
  change eventProbability (FiniteProbability.probability null)
      ((strictTest mode).statistic ⁻¹'
        (strictTest mode).tailEvent ((strictTest mode).statistic true)) = 0
  rw [strict_tail_event_preimage mode true, FiniteProbability.eventProbability_probability_set,
    Fintype.sum_bool]
  simp only [Set.mem_setOf_eq]
  norm_num [null]

@[simp] theorem strict_tailProbability_false (mode : Mode) :
    (strictTest mode).tailProbability false = 1 / 4 := by
  unfold NumericTest.tailProbability
  rw [strictTest_nullLaw_eq, test_nullLaw_eq]
  rw [eventProbability_map _ (measurable_statistic mode)
    ((strictTest mode).measurable_tailEvent _)]
  change eventProbability (FiniteProbability.probability null)
      ((strictTest mode).statistic ⁻¹'
        (strictTest mode).tailEvent ((strictTest mode).statistic false)) = 1 / 4
  rw [strict_tail_event_preimage mode false, FiniteProbability.eventProbability_probability_set,
    Fintype.sum_bool]
  simp only [Set.mem_setOf_eq]
  norm_num [null]

/-- The strict tail leaves positive null mass at threshold zero, so it is not
superuniform there; inclusive ties are what make the calibrated tests work. -/
theorem strict_zero_mass (mode : Mode) :
    eventProbability (FiniteProbability.probability null)
      {d | (strictTest mode).tailProbability d ≤ 0} = 1 / 4 := by
  rw [show {d : Bool | (strictTest mode).tailProbability d ≤ 0} =
        {b : Bool | b = true} from by
      ext d
      cases d <;> norm_num [strict_tailProbability_true, strict_tailProbability_false],
    FiniteProbability.eventProbability_probability_set, Fintype.sum_bool]
  norm_num [null]

theorem strict_zero_not_superuniform (mode : Mode) :
    ¬ eventProbability (FiniteProbability.probability null)
        {d | (strictTest mode).tailProbability d ≤ 0} ≤ 0 := by
  rw [strict_zero_mass]
  norm_num

/-- The pair statistic of the two draws. -/
def pairStatistic (leftMode rightMode : Mode) (d : Bool × Bool) : ℝ × ℝ :=
  ((statistic leftMode d.1 : ℝ), (statistic rightMode d.2 : ℝ))

theorem measurable_pairStatistic (leftMode rightMode : Mode) :
    Measurable (pairStatistic leftMode rightMode) :=
  measurable_of_finite _

/-- Population marginals of the actual real product measure. -/
theorem null_population_left_marginal :
    (FiniteProbability.probability nullJoint).map measurable_fst.aemeasurable =
      FiniteProbability.probability null :=
  FiniteProbability.probability_product_fst null null

theorem null_population_right_marginal :
    (FiniteProbability.probability nullJoint).map measurable_snd.aemeasurable =
      FiniteProbability.probability null :=
  FiniteProbability.probability_product_snd null null

theorem alternative_population_left_marginal :
    (FiniteProbability.probability alternativeJoint).map measurable_fst.aemeasurable =
      FiniteProbability.probability alternative :=
  FiniteProbability.probability_product_fst alternative alternative

theorem alternative_population_right_marginal :
    (FiniteProbability.probability alternativeJoint).map measurable_snd.aemeasurable =
      FiniteProbability.probability alternative :=
  FiniteProbability.probability_product_snd alternative alternative

/-- Real event transfer along the actual left population marginal. -/
theorem null_joint_fst_event (A : Set Bool) (hA : MeasurableSet A) :
    eventProbability (FiniteProbability.probability nullJoint) (Prod.fst ⁻¹' A) =
      eventProbability (FiniteProbability.probability null) A := by
  have h := congrArg (fun ν : ProbabilityMeasure Bool => eventProbability ν A)
    null_population_left_marginal
  rwa [eventProbability_map _ measurable_fst hA] at h

/-- Real event transfer along the actual right population marginal. -/
theorem null_joint_snd_event (A : Set Bool) (hA : MeasurableSet A) :
    eventProbability (FiniteProbability.probability nullJoint) (Prod.snd ⁻¹' A) =
      eventProbability (FiniteProbability.probability null) A := by
  have h := congrArg (fun ν : ProbabilityMeasure Bool => eventProbability ν A)
    null_population_right_marginal
  rwa [eventProbability_map _ measurable_snd hA] at h

/-- Actual event independence of the two coordinates of the product population. -/
theorem null_population_independent (s t : Set Bool) :
    eventProbability (FiniteProbability.probability nullJoint)
      ((Prod.fst ⁻¹' s) ∩ (Prod.snd ⁻¹' t)) =
      eventProbability (FiniteProbability.probability null) s *
        eventProbability (FiniteProbability.probability null) t := by
  classical
  simp only [FiniteProbability.eventProbability_probability_set]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Set.mem_inter_iff, Set.mem_preimage]
  by_cases h₁ : (true : Bool) ∈ s <;> by_cases h₂ : (false : Bool) ∈ s <;>
    by_cases h₃ : (true : Bool) ∈ t <;> by_cases h₄ : (false : Bool) ∈ t <;>
    norm_num [h₁, h₂, h₃, h₄, nullJoint, FiniteProbability.product_mass, null]

/-- The coupling of the two tests: the pushforward of the real product measure
under the pair statistic. Independence is a property of this instance. -/
noncomputable def nullCoupling (leftMode rightMode : Mode) :
    ProbabilityCoupling (test leftMode).nullLaw (test rightMode).nullLaw where
  joint := (FiniteProbability.probability nullJoint).map
    (measurable_pairStatistic leftMode rightMode).aemeasurable
  leftMarginal := by
    apply ProbabilityMeasure.eq_of_forall_apply_eq
    intro s hs
    apply NNReal.coe_injective
    change eventProbability (((FiniteProbability.probability nullJoint).map
        (measurable_pairStatistic leftMode rightMode).aemeasurable).map
          measurable_fst.aemeasurable) s = eventProbability (test leftMode).nullLaw s
    rw [eventProbability_map _ measurable_fst hs]
    rw [eventProbability_map _ (measurable_pairStatistic leftMode rightMode)
      (hs.preimage measurable_fst), test_nullLaw_eq]
    rw [eventProbability_map _ (measurable_statistic leftMode) hs]
    rw [show pairStatistic leftMode rightMode ⁻¹' (Prod.fst ⁻¹' s) =
        Prod.fst ⁻¹' ((fun d : Bool => (statistic leftMode d : ℝ)) ⁻¹' s) from by
      ext p
      simp only [Set.mem_preimage, pairStatistic]]
    rw [null_joint_fst_event ((fun d : Bool => (statistic leftMode d : ℝ)) ⁻¹' s)
      (hs.preimage (measurable_statistic leftMode))]
  rightMarginal := by
    apply ProbabilityMeasure.eq_of_forall_apply_eq
    intro s hs
    apply NNReal.coe_injective
    change eventProbability (((FiniteProbability.probability nullJoint).map
        (measurable_pairStatistic leftMode rightMode).aemeasurable).map
          measurable_snd.aemeasurable) s = eventProbability (test rightMode).nullLaw s
    rw [eventProbability_map _ measurable_snd hs]
    rw [eventProbability_map _ (measurable_pairStatistic leftMode rightMode)
      (hs.preimage measurable_snd), test_nullLaw_eq]
    rw [eventProbability_map _ (measurable_statistic rightMode) hs]
    rw [show pairStatistic leftMode rightMode ⁻¹' (Prod.snd ⁻¹' s) =
        Prod.snd ⁻¹' ((fun d : Bool => (statistic rightMode d : ℝ)) ⁻¹' s) from by
      ext p
      simp only [Set.mem_preimage, pairStatistic]]
    rw [null_joint_snd_event ((fun d : Bool => (statistic rightMode d : ℝ)) ⁻¹' s)
      (hs.preimage (measurable_statistic rightMode))]

theorem nullCoupling_joint (leftMode rightMode : Mode) :
    (nullCoupling leftMode rightMode).joint =
      (FiniteProbability.probability nullJoint).map
        (measurable_pairStatistic leftMode rightMode).aemeasurable := rfl

/-- Both statistic marginals of the coupling are the two test null laws. -/
theorem null_statistic_left_marginal (leftMode rightMode : Mode) :
    (nullCoupling leftMode rightMode).joint.map measurable_fst.aemeasurable =
      (test leftMode).nullLaw :=
  (nullCoupling leftMode rightMode).leftMarginal

theorem null_statistic_right_marginal (leftMode rightMode : Mode) :
    (nullCoupling leftMode rightMode).joint.map measurable_snd.aemeasurable =
      (test rightMode).nullLaw :=
  (nullCoupling leftMode rightMode).rightMarginal

/-- Statistic-level independence derived from the concrete product population. -/
theorem null_statistic_independent (leftMode rightMode : Mode) (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    eventProbability (nullCoupling leftMode rightMode).joint
      ((Prod.fst ⁻¹' s) ∩ (Prod.snd ⁻¹' t)) =
      eventProbability (test leftMode).nullLaw s *
        eventProbability (test rightMode).nullLaw t := by
  rw [nullCoupling_joint]
  rw [eventProbability_map _ (measurable_pairStatistic leftMode rightMode)
    ((hs.preimage measurable_fst).inter (ht.preimage measurable_snd))]
  rw [show pairStatistic leftMode rightMode ⁻¹' ((Prod.fst ⁻¹' s) ∩ (Prod.snd ⁻¹' t)) =
      (Prod.fst ⁻¹' ((fun d : Bool => (statistic leftMode d : ℝ)) ⁻¹' s)) ∩
        (Prod.snd ⁻¹' ((fun d : Bool => (statistic rightMode d : ℝ)) ⁻¹' t)) from by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, pairStatistic]]
  rw [null_population_independent]
  rw [show eventProbability (FiniteProbability.probability null)
        ((fun d : Bool => (statistic leftMode d : ℝ)) ⁻¹' s) =
      eventProbability (test leftMode).nullLaw s from by
    rw [test_nullLaw_eq, eventProbability_map _ (measurable_statistic leftMode) hs],
    show eventProbability (FiniteProbability.probability null)
        ((fun d : Bool => (statistic rightMode d : ℝ)) ⁻¹' t) =
      eventProbability (test rightMode).nullLaw t from by
    rw [test_nullLaw_eq, eventProbability_map _ (measurable_statistic rightMode) ht]]

/-- Boolean union event of the two coupled tails at observations `x` and `y`. -/
def unionEvent (leftMode rightMode : Mode) (x y : Bool) : Set (ℝ × ℝ) :=
  (Prod.fst ⁻¹' (test leftMode).tailEvent ((test leftMode).statistic x)) ∪
    (Prod.snd ⁻¹' (test rightMode).tailEvent ((test rightMode).statistic y))

/-- Boolean intersection event of the two coupled tails. -/
def interEvent (leftMode rightMode : Mode) (x y : Bool) : Set (ℝ × ℝ) :=
  (Prod.fst ⁻¹' (test leftMode).tailEvent ((test leftMode).statistic x)) ∩
    (Prod.snd ⁻¹' (test rightMode).tailEvent ((test rightMode).statistic y))

theorem measurable_unionEvent (leftMode rightMode : Mode) (x y : Bool) :
    MeasurableSet (unionEvent leftMode rightMode x y) :=
  ((test leftMode).measurable_tailEvent _).preimage measurable_fst |>.union
    (((test rightMode).measurable_tailEvent _).preimage measurable_snd)

theorem measurable_interEvent (leftMode rightMode : Mode) (x y : Bool) :
    MeasurableSet (interEvent leftMode rightMode x y) :=
  ((test leftMode).measurable_tailEvent _).preimage measurable_fst |>.inter
    (((test rightMode).measurable_tailEvent _).preimage measurable_snd)

theorem unionEvent_preimage (leftMode rightMode : Mode) (x y : Bool) :
    pairStatistic leftMode rightMode ⁻¹' (unionEvent leftMode rightMode x y) =
      {p : Bool × Bool | ((p.1 || !x) || (p.2 || !y)) = true} := by
  ext p
  change ((test leftMode).tail ((test leftMode).statistic p.1)
      ((test leftMode).statistic x) ∨
      (test rightMode).tail ((test rightMode).statistic p.2)
        ((test rightMode).statistic y)) ↔
    ((p.1 || !x) || (p.2 || !y)) = true
  rw [tail_on_samples leftMode p.1 x, tail_on_samples rightMode p.2 y]
  cases p.1 <;> cases x <;> cases p.2 <;> cases y <;> decide

theorem interEvent_preimage (leftMode rightMode : Mode) (x y : Bool) :
    pairStatistic leftMode rightMode ⁻¹' (interEvent leftMode rightMode x y) =
      {p : Bool × Bool | ((p.1 || !x) && (p.2 || !y)) = true} := by
  ext p
  change ((test leftMode).tail ((test leftMode).statistic p.1)
      ((test leftMode).statistic x) ∧
      (test rightMode).tail ((test rightMode).statistic p.2)
        ((test rightMode).statistic y)) ↔
    ((p.1 || !x) && (p.2 || !y)) = true
  rw [tail_on_samples leftMode p.1 x, tail_on_samples rightMode p.2 y]
  cases p.1 <;> cases x <;> cases p.2 <;> cases y <;> decide

/-- All four Boolean input pairs, measured in the genuine statistic coupling. -/
theorem union_probability (leftMode rightMode : Mode) (x y : Bool) :
    eventProbability (nullCoupling leftMode rightMode).joint
      (unionEvent leftMode rightMode x y) =
      ((pvalue x + pvalue y - pvalue x * pvalue y : ℚ) : ℝ) := by
  rw [nullCoupling_joint]
  rw [eventProbability_map _ (measurable_pairStatistic leftMode rightMode)
    (measurable_unionEvent leftMode rightMode x y)]
  rw [unionEvent_preimage leftMode rightMode x y,
    FiniteProbability.eventProbability_probability_set]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Set.mem_setOf_eq]
  cases leftMode <;> cases rightMode <;> cases x <;> cases y <;>
    norm_num [FiniteProbability.eventMass, Fintype.sum_bool, nullJoint,
      FiniteProbability.product_mass, null, pvalue, rationalTail, statistic]

/-- The exact intersection is a product here, not an abstract independence premise. -/
theorem inter_probability (leftMode rightMode : Mode) (x y : Bool) :
    eventProbability (nullCoupling leftMode rightMode).joint
      (interEvent leftMode rightMode x y) = ((pvalue x * pvalue y : ℚ) : ℝ) := by
  rw [nullCoupling_joint]
  rw [eventProbability_map _ (measurable_pairStatistic leftMode rightMode)
    (measurable_interEvent leftMode rightMode x y)]
  rw [interEvent_preimage leftMode rightMode x y,
    FiniteProbability.eventProbability_probability_set]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Set.mem_setOf_eq]
  cases leftMode <;> cases rightMode <;> cases x <;> cases y <;>
    norm_num [FiniteProbability.eventMass, Fintype.sum_bool, nullJoint,
      FiniteProbability.product_mass, null, pvalue, rationalTail, statistic]

theorem union_true_true (leftMode rightMode : Mode) :
    eventProbability (nullCoupling leftMode rightMode).joint
      (unionEvent leftMode rightMode true true) = 7 / 16 := by
  rw [union_probability]
  norm_num

theorem inter_true_true (leftMode rightMode : Mode) :
    eventProbability (nullCoupling leftMode rightMode).joint
      (interEvent leftMode rightMode true true) = 1 / 16 := by
  rw [inter_probability]
  norm_num

theorem union_true_true_le_half (leftMode rightMode : Mode) :
    eventProbability (nullCoupling leftMode rightMode).joint
      (unionEvent leftMode rightMode true true) ≤ 1 / 2 := by
  rw [union_true_true]
  norm_num

theorem inter_true_true_le_quarter (leftMode rightMode : Mode) :
    eventProbability (nullCoupling leftMode rightMode).joint
      (interEvent leftMode rightMode true true) ≤ 1 / 4 := by
  rw [inter_true_true]
  norm_num

end Lara.BHL.Tests.Binary
