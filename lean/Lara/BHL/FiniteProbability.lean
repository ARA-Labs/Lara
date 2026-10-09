import Lara.BHL.Numeric
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.BigOperators

/-!
Normalized rational laws on finite carriers and their actual probability measures.
The rational event evaluator is computable; the measure embedding is a finite
sum of rationally weighted Dirac measures. Product laws retain their population
marginals after this embedding.
-/

namespace Lara.BHL.FiniteProbability

open MeasureTheory Set
open scoped BigOperators

/-- Exact finite probability data, with normalization proved rather than assumed
as a separate measure-valued field. -/
structure Law (α : Type*) [Fintype α] where
  mass : α → ℚ
  nonnegative : ∀ a, 0 ≤ mass a
  normalized : (∑ a, mass a) = 1

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Executable finite event summation. -/
def eventMass (law : Law α) (event : α → Bool) : ℚ :=
  ∑ a, if event a then law.mass a else 0

theorem eventMass_nonnegative (law : Law α) (event : α → Bool) :
    0 ≤ eventMass law event := by
  apply Finset.sum_nonneg
  intro a _
  split
  · exact law.nonnegative a
  · exact le_rfl

@[simp] theorem eventMass_false (law : Law α) :
    eventMass law (fun _ => false) = 0 := by
  simp [eventMass]

@[simp] theorem eventMass_true (law : Law α) :
    eventMass law (fun _ => true) = 1 := by
  simpa [eventMass] using law.normalized

theorem eventMass_le_one (law : Law α) (event : α → Bool) :
    eventMass law event ≤ 1 := by
  rw [← law.normalized]
  apply Finset.sum_le_sum
  intro a _
  split
  · exact le_rfl
  · exact law.nonnegative a

theorem eventMass_mono (law : Law α) {left right : α → Bool}
    (h : ∀ a, left a = true → right a = true) :
    eventMass law left ≤ eventMass law right := by
  apply Finset.sum_le_sum
  intro a _
  cases hl : left a with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      split
      · exact law.nonnegative a
      · exact le_rfl
  | true => simp [h a hl]

/-- The independent finite product, with exact rational normalization. -/
def product (left : Law α) (right : Law β) : Law (α × β) where
  mass p := left.mass p.1 * right.mass p.2
  nonnegative p := mul_nonneg (left.nonnegative p.1) (right.nonnegative p.2)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, right.normalized, mul_one]
    exact left.normalized

@[simp] theorem product_mass (left : Law α) (right : Law β) (p : α × β) :
    (product left right).mass p = left.mass p.1 * right.mass p.2 := rfl

@[simp] theorem eventMass_product_fst (left : Law α) (right : Law β)
    (event : α → Bool) :
    eventMass (product left right) (fun p => event p.1) = eventMass left event := by
  unfold eventMass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  cases h : event a <;>
    simp [h, ← Finset.mul_sum, right.normalized]

@[simp] theorem eventMass_product_snd (left : Law α) (right : Law β)
    (event : β → Bool) :
    eventMass (product left right) (fun p => event p.2) = eventMass right event := by
  unfold eventMass
  rw [Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro b _
  cases h : event b <;>
    simp [h, ← Finset.sum_mul, left.normalized]

section Measures

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The actual measure used by the embedding, not supplied by a caller. -/
noncomputable def measure (law : Law α) : Measure α :=
  ∑ a, ENNReal.ofReal (law.mass a : ℝ) • Measure.dirac a

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
private theorem mass_cast_nonnegative (law : Law α) (a : α) :
    0 ≤ (law.mass a : ℝ) := by
  exact_mod_cast law.nonnegative a

/-- Every set has the exact finite weighted-Dirac mass. Singleton
measurability makes all subsets of the finite carrier measurable. -/
theorem measure_apply (law : Law α) (s : Set α) [DecidablePred (· ∈ s)] :
    measure law s = ENNReal.ofReal (∑ a, if a ∈ s then (law.mass a : ℝ) else 0) := by
  classical
  rw [measure, Measure.finsetSum_apply]
  rw [ENNReal.ofReal_sum_of_nonneg
    (f := fun a => if a ∈ s then (law.mass a : ℝ) else 0) (fun a _ => by
      split
      · exact mass_cast_nonnegative law a
      · exact le_rfl)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : a ∈ s <;>
    simp [Measure.smul_apply, Measure.dirac_apply, Set.indicator, h]

@[simp] theorem measure_univ (law : Law α) : measure law univ = 1 := by
  rw [measure_apply]
  simp only [mem_univ, if_true]
  have h : (∑ a, (law.mass a : ℝ)) = 1 := by
    exact_mod_cast law.normalized
  rw [h, ENNReal.ofReal_one]

/-- The probability law canonically constructed from exact rational mass. -/
noncomputable def probability (law : Law α) : ProbabilityMeasure α :=
  ⟨measure law, ⟨measure_univ law⟩⟩

@[simp] theorem probability_toMeasure (law : Law α) :
    (probability law : Measure α) = measure law := rfl

/-- A set-level formula useful for pushforwards into arbitrary statistic spaces. -/
theorem eventProbability_probability_set (law : Law α) (s : Set α)
    [DecidablePred (· ∈ s)] :
    eventProbability (probability law) s =
      ∑ a, if a ∈ s then (law.mass a : ℝ) else 0 := by
  classical
  change (measure law s).toReal = _
  rw [measure_apply, ENNReal.toReal_ofReal]
  apply Finset.sum_nonneg
  intro a _
  split
  · exact mass_cast_nonnegative law a
  · exact le_rfl

/-- The existing real event semantics agrees exactly with computable rational
summation; there is no parallel numeric interpretation. -/
theorem eventProbability_probability (law : Law α) (event : α → Bool) :
    eventProbability (probability law) {a | event a = true} =
      (eventMass law event : ℝ) := by
  rw [eventProbability_probability_set, eventMass]
  push_cast
  simp only [Set.mem_setOf_eq]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : event a = true <;> simp [h]

/-- Pushforward events reduce to finite population summation, even when the
statistic carrier is not finite. -/
theorem eventProbability_map_probability {Ω : Type*} [MeasurableSpace Ω]
    (law : Law α) {f : α → Ω} (hf : Measurable f)
    {s : Set Ω} (hs : MeasurableSet s) [DecidablePred (fun a => f a ∈ s)] :
    eventProbability ((probability law).map hf.aemeasurable) s =
      ∑ a, if f a ∈ s then (law.mass a : ℝ) else 0 := by
  classical
  rw [eventProbability_map (probability law) hf hs,
    eventProbability_probability_set]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a ∈ s <;> simp [Set.mem_preimage, h]

variable [MeasurableSpace β] [MeasurableSingletonClass β]

/-- The actual weighted-Dirac product has the prescribed left population law. -/
theorem probability_product_fst (left : Law α) (right : Law β) :
    (probability (product left right)).map measurable_fst.aemeasurable =
      probability left := by
  classical
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s hs
  apply NNReal.coe_injective
  change eventProbability ((probability (product left right)).map
    measurable_fst.aemeasurable) s = eventProbability (probability left) s
  rw [eventProbability_map _ measurable_fst hs,
    eventProbability_probability_set, eventProbability_probability_set,
    Fintype.sum_prod_type]
  change (∑ a, ∑ b, if a ∈ s then
      ((left.mass a * right.mass b : ℚ) : ℝ) else 0) =
    ∑ a, if a ∈ s then (left.mass a : ℝ) else 0
  simp only [Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : a ∈ s
  · simp only [h, if_true]
    rw [← Finset.mul_sum]
    have hn : (∑ b, (right.mass b : ℝ)) = 1 := by
      exact_mod_cast right.normalized
    rw [hn, mul_one]
  · simp [h]

/-- The actual weighted-Dirac product has the prescribed right population law. -/
theorem probability_product_snd (left : Law α) (right : Law β) :
    (probability (product left right)).map measurable_snd.aemeasurable =
      probability right := by
  classical
  apply ProbabilityMeasure.eq_of_forall_apply_eq
  intro s hs
  apply NNReal.coe_injective
  change eventProbability ((probability (product left right)).map
    measurable_snd.aemeasurable) s = eventProbability (probability right) s
  rw [eventProbability_map _ measurable_snd hs,
    eventProbability_probability_set, eventProbability_probability_set,
    Fintype.sum_prod_type_right]
  change (∑ b, ∑ a, if b ∈ s then
      ((left.mass a * right.mass b : ℚ) : ℝ) else 0) =
    ∑ b, if b ∈ s then (right.mass b : ℝ) else 0
  simp only [Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : b ∈ s
  · simp only [h, if_true]
    rw [← Finset.sum_mul]
    have hn : (∑ a, (left.mass a : ℝ)) = 1 := by
      exact_mod_cast left.normalized
    rw [hn, one_mul]
  · simp [h]

end Measures

end Lara.BHL.FiniteProbability
