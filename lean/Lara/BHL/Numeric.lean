import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
Real-valued null-law event semantics, independent of the BHL syntax.

A test binds a measurable statistic to a probability law on its statistic space
and an explicit tail relation. Tail measurability is required separately for
every observation. No calibration, hypothesis truth, or global test soundness
is assumed. The relation determines the tie convention.

The event inequalities are measure-theoretic: coupling bounds require the
stated marginals, not independence. Their real-valued upper bounds may exceed
one, as required for an unclamped Bonferroni sum.
-/

namespace Lara.BHL

open MeasureTheory Set
open scoped NNReal

noncomputable section

/-- The actual real mass of an event under a normalized probability measure.
Mathlib also defines this on nonmeasurable sets via outer measure; statistical
tail events below are required to be measurable. -/
def eventProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (event : Set Ω) : ℝ :=
  (μ event : ℝ)

section Events

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

 theorem eventProbability_nonneg (μ : ProbabilityMeasure Ω) (event : Set Ω) :
    0 ≤ eventProbability μ event :=
  NNReal.coe_nonneg (μ event)

 theorem eventProbability_le_one (μ : ProbabilityMeasure Ω) (event : Set Ω) :
    eventProbability μ event ≤ 1 :=
  μ.apply_le_one event

@[simp] theorem eventProbability_empty (μ : ProbabilityMeasure Ω) :
    eventProbability μ ∅ = 0 := by
  simp [eventProbability]

@[simp] theorem eventProbability_univ (μ : ProbabilityMeasure Ω) :
    eventProbability μ univ = 1 := by
  simp [eventProbability]

 theorem eventProbability_mono (μ : ProbabilityMeasure Ω) {s t : Set Ω}
    (h : s ⊆ t) : eventProbability μ s ≤ eventProbability μ t :=
  μ.apply_mono h

 theorem eventProbability_union_le (μ : ProbabilityMeasure Ω) (s t : Set Ω) :
    eventProbability μ (s ∪ t) ≤ eventProbability μ s + eventProbability μ t :=
  μ.apply_union_le

 theorem eventProbability_inter_le_min (μ : ProbabilityMeasure Ω) (s t : Set Ω) :
    eventProbability μ (s ∩ t) ≤ min (eventProbability μ s) (eventProbability μ t) :=
  le_min (eventProbability_mono μ inter_subset_left)
    (eventProbability_mono μ inter_subset_right)

/-- Push-forward probabilities equal probabilities of measurable preimages. -/
 theorem eventProbability_map (μ : ProbabilityMeasure Ω) {f : Ω → Ω'}
    (hf : Measurable f) {s : Set Ω'} (hs : MeasurableSet s) :
    eventProbability (μ.map hf.aemeasurable) s = eventProbability μ (f ⁻¹' s) := by
  simp only [eventProbability, ProbabilityMeasure.map_apply μ hf.aemeasurable hs]

end Events

/-- A genuine statistical denotation. `nullLaw` is the law of the statistic
under the null, not a claimed p-value or a predicate asserting calibration.
`tail candidate observed` specifies the event, including discrete ties. -/
structure NumericTest (Sample Statistic : Type*)
    [MeasurableSpace Sample] [MeasurableSpace Statistic] where
  statistic : Sample → Statistic
  measurableStatistic : Measurable statistic
  nullLaw : ProbabilityMeasure Statistic
  tail : Statistic → Statistic → Prop
  measurableTail : ∀ observed, MeasurableSet {candidate | tail candidate observed}

namespace NumericTest

variable {Sample Statistic : Type*}
variable [MeasurableSpace Sample] [MeasurableSpace Statistic]

 def tailEvent (test : NumericTest Sample Statistic) (observed : Statistic) : Set Statistic :=
  {candidate | test.tail candidate observed}

 theorem measurable_tailEvent (test : NumericTest Sample Statistic) (observed : Statistic) :
    MeasurableSet (test.tailEvent observed) :=
  test.measurableTail observed

 def tailProbability (test : NumericTest Sample Statistic) (sample : Sample) : ℝ :=
  eventProbability test.nullLaw (test.tailEvent (test.statistic sample))

 theorem tailProbability_nonneg (test : NumericTest Sample Statistic) (sample : Sample) :
    0 ≤ test.tailProbability sample :=
  eventProbability_nonneg _ _

 theorem tailProbability_le_one (test : NumericTest Sample Statistic) (sample : Sample) :
    test.tailProbability sample ≤ 1 :=
  eventProbability_le_one _ _

/-- Monotonicity follows from inclusion of the specified tail events; it does
not assume that an arbitrary tail relation is ordered in its observation. -/
 theorem tailProbability_mono (test : NumericTest Sample Statistic) {x y : Sample}
    (h : test.tailEvent (test.statistic x) ⊆ test.tailEvent (test.statistic y)) :
    test.tailProbability x ≤ test.tailProbability y :=
  eventProbability_mono _ h

end NumericTest

/-- A joint null law with the exact given marginals. No independence condition
is present, and the existence of a coupling is not assumed for any chosen pair. -/
structure ProbabilityCoupling {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (leftLaw : ProbabilityMeasure Ω) (rightLaw : ProbabilityMeasure Ω') where
  joint : ProbabilityMeasure (Ω × Ω')
  leftMarginal : joint.map measurable_fst.aemeasurable = leftLaw
  rightMarginal : joint.map measurable_snd.aemeasurable = rightLaw

namespace ProbabilityCoupling

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {μ : ProbabilityMeasure Ω} {ν : ProbabilityMeasure Ω'}

 theorem left_event (coupling : ProbabilityCoupling μ ν) {s : Set Ω}
    (hs : MeasurableSet s) :
    eventProbability coupling.joint (Prod.fst ⁻¹' s) = eventProbability μ s := by
  calc
    _ = eventProbability (coupling.joint.map measurable_fst.aemeasurable) s :=
      (eventProbability_map coupling.joint measurable_fst hs).symm
    _ = _ := congrArg (fun law => eventProbability law s) coupling.leftMarginal

 theorem right_event (coupling : ProbabilityCoupling μ ν) {t : Set Ω'}
    (ht : MeasurableSet t) :
    eventProbability coupling.joint (Prod.snd ⁻¹' t) = eventProbability ν t := by
  calc
    _ = eventProbability (coupling.joint.map measurable_snd.aemeasurable) t :=
      (eventProbability_map coupling.joint measurable_snd ht).symm
    _ = _ := congrArg (fun law => eventProbability law t) coupling.rightMarginal

 theorem union_le (coupling : ProbabilityCoupling μ ν) {s : Set Ω} {t : Set Ω'}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    eventProbability coupling.joint ((Prod.fst ⁻¹' s) ∪ (Prod.snd ⁻¹' t)) ≤
      eventProbability μ s + eventProbability ν t := by
  calc
    _ ≤ eventProbability coupling.joint (Prod.fst ⁻¹' s) +
        eventProbability coupling.joint (Prod.snd ⁻¹' t) :=
      eventProbability_union_le _ _ _
    _ = _ := by rw [coupling.left_event hs, coupling.right_event ht]

 theorem inter_le_min (coupling : ProbabilityCoupling μ ν) {s : Set Ω} {t : Set Ω'}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    eventProbability coupling.joint ((Prod.fst ⁻¹' s) ∩ (Prod.snd ⁻¹' t)) ≤
      min (eventProbability μ s) (eventProbability ν t) := by
  calc
    _ ≤ min (eventProbability coupling.joint (Prod.fst ⁻¹' s))
        (eventProbability coupling.joint (Prod.snd ⁻¹' t)) :=
      eventProbability_inter_le_min _ _ _
    _ = _ := by rw [coupling.left_event hs, coupling.right_event ht]

end ProbabilityCoupling

namespace NumericTest

variable {Sample₁ Sample₂ Statistic₁ Statistic₂ : Type*}
variable [MeasurableSpace Sample₁] [MeasurableSpace Sample₂]
variable [MeasurableSpace Statistic₁] [MeasurableSpace Statistic₂]

 theorem coupled_tail_union_le (left : NumericTest Sample₁ Statistic₁)
    (right : NumericTest Sample₂ Statistic₂)
    (coupling : ProbabilityCoupling left.nullLaw right.nullLaw)
    (x : Sample₁) (y : Sample₂) :
    eventProbability coupling.joint
      ((Prod.fst ⁻¹' left.tailEvent (left.statistic x)) ∪
        (Prod.snd ⁻¹' right.tailEvent (right.statistic y))) ≤
      left.tailProbability x + right.tailProbability y :=
  coupling.union_le (left.measurable_tailEvent _) (right.measurable_tailEvent _)

 theorem coupled_tail_inter_le_min (left : NumericTest Sample₁ Statistic₁)
    (right : NumericTest Sample₂ Statistic₂)
    (coupling : ProbabilityCoupling left.nullLaw right.nullLaw)
    (x : Sample₁) (y : Sample₂) :
    eventProbability coupling.joint
      ((Prod.fst ⁻¹' left.tailEvent (left.statistic x)) ∩
        (Prod.snd ⁻¹' right.tailEvent (right.statistic y))) ≤
      min (left.tailProbability x) (right.tailProbability y) :=
  coupling.inter_le_min (left.measurable_tailEvent _) (right.measurable_tailEvent _)

end NumericTest

/-- A concrete normalized law, available on any measurable sample space. -/
def diracProbability {Ω : Type*} [MeasurableSpace Ω] (point : Ω) : ProbabilityMeasure Ω :=
  ⟨Measure.dirac point, Measure.dirac.isProbabilityMeasure⟩

 theorem eventProbability_dirac_of_mem {Ω : Type*} [MeasurableSpace Ω]
    (point : Ω) {s : Set Ω} (h : point ∈ s) :
    eventProbability (diracProbability point) s = 1 := by
  simp [eventProbability, diracProbability, ProbabilityMeasure.mk_apply,
    Measure.dirac_apply_of_mem h]

 theorem eventProbability_dirac_of_notMem {Ω : Type*} [MeasurableSpace Ω]
    (point : Ω) {s : Set Ω} (hs : MeasurableSet s) (h : point ∉ s) :
    eventProbability (diracProbability point) s = 0 := by
  simp [eventProbability, diracProbability, ProbabilityMeasure.mk_apply,
    Measure.dirac_apply' point hs, Set.indicator_of_notMem h]

/-- A nonempty actual-real realization: the identity statistic under a Dirac
null law at zero, with an inclusive upper tail. This witnesses the carrier; it
is not a calibrated binary test or a continuous-distribution approximation. -/
def realDiracTest : NumericTest ℝ ℝ where
  statistic := id
  measurableStatistic := measurable_id
  nullLaw := diracProbability 0
  tail := fun candidate observed => observed ≤ candidate
  measurableTail := fun _ => measurableSet_Ici

 theorem realDiracTest_inhabits : Nonempty (NumericTest ℝ ℝ) :=
  ⟨realDiracTest⟩

theorem realDiracTest_tailProbability_zero : realDiracTest.tailProbability 0 = 1 := by
  apply eventProbability_dirac_of_mem
  change (0 : ℝ) ≤ 0
  exact le_rfl

theorem realDiracTest_tailProbability_one : realDiracTest.tailProbability 1 = 0 := by
  apply eventProbability_dirac_of_notMem 0 (realDiracTest.measurable_tailEvent _)
  change ¬ (1 : ℝ) ≤ 0
  exact not_le.mpr zero_lt_one

end

end Lara.BHL
