import Lara.BHL.Value
import Lara.BHL.Numeric

/-!
Measured numerical events retain their actual normalized law and sample sort.
Composition uses a supplied joint law with proved marginals, without assuming
independence or existence of a coupling. Product sample sorts preserve nested
event compositions and the product sigma algebra of the value carriers.
-/

namespace Lara.BHL

open MeasureTheory Set

noncomputable section

/-- A measurable event on the actual carrier of a BHL sample sort. -/
structure NumericalEvent (sample : ValueSort) where
  law : ProbabilityMeasure (Value sample)
  event : Set (Value sample)
  measurableEvent : MeasurableSet event

/-- An event together with its sample sort, including recursively nested products. -/
abbrev PackedNumericalEvent := Σ sample : ValueSort, NumericalEvent sample

namespace NumericalEvent

variable {s t : ValueSort}

/-- Actual real-valued probability under the event's normalized law. -/
def probability (numerical : NumericalEvent s) : ℝ :=
  eventProbability numerical.law numerical.event

 theorem probability_nonneg (numerical : NumericalEvent s) :
    0 ≤ numerical.probability :=
  eventProbability_nonneg numerical.law numerical.event

 theorem probability_le_one (numerical : NumericalEvent s) :
    numerical.probability ≤ 1 :=
  eventProbability_le_one numerical.law numerical.event

 theorem probability_mem_Icc (numerical : NumericalEvent s) :
    numerical.probability ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨probability_nonneg numerical, probability_le_one numerical⟩

/-- The exact null-law tail at the statistic observed on the supplied data. -/
def tail {D : Type*} [MeasurableSpace D] (test : NumericTest D ℝ)
    (data : D) : NumericalEvent .real where
  law := test.nullLaw
  event := test.tailEvent (test.statistic data)
  measurableEvent := test.measurable_tailEvent (test.statistic data)

@[simp] theorem tail_law {D : Type*} [MeasurableSpace D]
    (test : NumericTest D ℝ) (data : D) :
    (tail test data).law = test.nullLaw := rfl

@[simp] theorem tail_event {D : Type*} [MeasurableSpace D]
    (test : NumericTest D ℝ) (data : D) :
    (tail test data).event = test.tailEvent (test.statistic data) := rfl

@[simp] theorem mem_tail_event {D : Type*} [MeasurableSpace D]
    (test : NumericTest D ℝ) (data : D) (candidate : ℝ) :
    candidate ∈ (tail test data).event ↔ test.tail candidate (test.statistic data) :=
  Iff.rfl

 theorem tail_measurableEvent {D : Type*} [MeasurableSpace D]
    (test : NumericTest D ℝ) (data : D) :
    MeasurableSet (tail test data).event :=
  (tail test data).measurableEvent

@[simp] theorem tail_probability {D : Type*} [MeasurableSpace D]
    (test : NumericTest D ℝ) (data : D) :
    (tail test data).probability = test.tailProbability data := rfl

/-- Lift each component event to the supplied joint space, then take their union. -/
def union (left : NumericalEvent s) (right : NumericalEvent t)
    (coupling : ProbabilityCoupling left.law right.law) : NumericalEvent (.product s t) where
  law := coupling.joint
  event := (Prod.fst ⁻¹' left.event) ∪ (Prod.snd ⁻¹' right.event)
  measurableEvent := (left.measurableEvent.preimage measurable_fst).union
    (right.measurableEvent.preimage measurable_snd)

/-- Lift each component event to the supplied joint space, then intersect them. -/
def intersection (left : NumericalEvent s) (right : NumericalEvent t)
    (coupling : ProbabilityCoupling left.law right.law) : NumericalEvent (.product s t) where
  law := coupling.joint
  event := (Prod.fst ⁻¹' left.event) ∩ (Prod.snd ⁻¹' right.event)
  measurableEvent := (left.measurableEvent.preimage measurable_fst).inter
    (right.measurableEvent.preimage measurable_snd)

@[simp] theorem union_law (left : NumericalEvent s) (right : NumericalEvent t)
    (coupling : ProbabilityCoupling left.law right.law) :
    (union left right coupling).law = coupling.joint := rfl

@[simp] theorem intersection_law (left : NumericalEvent s) (right : NumericalEvent t)
    (coupling : ProbabilityCoupling left.law right.law) :
    (intersection left right coupling).law = coupling.joint := rfl

@[simp] theorem union_event (left : NumericalEvent s) (right : NumericalEvent t)
    (coupling : ProbabilityCoupling left.law right.law) :
    (union left right coupling).event =
      (Prod.fst ⁻¹' left.event) ∪ (Prod.snd ⁻¹' right.event) := rfl

@[simp] theorem intersection_event (left : NumericalEvent s) (right : NumericalEvent t)
    (coupling : ProbabilityCoupling left.law right.law) :
    (intersection left right coupling).event =
      (Prod.fst ⁻¹' left.event) ∩ (Prod.snd ⁻¹' right.event) := rfl

@[simp] theorem mem_union_event (left : NumericalEvent s) (right : NumericalEvent t)
    (coupling : ProbabilityCoupling left.law right.law) (value : Value (.product s t)) :
    value ∈ (union left right coupling).event ↔
      value.1 ∈ left.event ∨ value.2 ∈ right.event := Iff.rfl

@[simp] theorem mem_intersection_event (left : NumericalEvent s) (right : NumericalEvent t)
    (coupling : ProbabilityCoupling left.law right.law) (value : Value (.product s t)) :
    value ∈ (intersection left right coupling).event ↔
      value.1 ∈ left.event ∧ value.2 ∈ right.event := Iff.rfl

 theorem union_measurableEvent (left : NumericalEvent s) (right : NumericalEvent t)
    (coupling : ProbabilityCoupling left.law right.law) :
    MeasurableSet (union left right coupling).event :=
  (union left right coupling).measurableEvent

 theorem intersection_measurableEvent (left : NumericalEvent s) (right : NumericalEvent t)
    (coupling : ProbabilityCoupling left.law right.law) :
    MeasurableSet (intersection left right coupling).event :=
  (intersection left right coupling).measurableEvent

/-- The left lifted event has exactly the left probability, by the marginal law. -/
 theorem left_lift_probability (left : NumericalEvent s) (right : NumericalEvent t)
    (coupling : ProbabilityCoupling left.law right.law) :
    eventProbability coupling.joint (Prod.fst ⁻¹' left.event) = left.probability :=
  coupling.left_event left.measurableEvent

/-- The right lifted event has exactly the right probability, by the marginal law. -/
 theorem right_lift_probability (left : NumericalEvent s) (right : NumericalEvent t)
    (coupling : ProbabilityCoupling left.law right.law) :
    eventProbability coupling.joint (Prod.snd ⁻¹' right.event) = right.probability :=
  coupling.right_event right.measurableEvent

/-- The unclamped union bound depends only on the supplied marginal equalities. -/
 theorem union_probability_le (left : NumericalEvent s) (right : NumericalEvent t)
    (coupling : ProbabilityCoupling left.law right.law) :
    (union left right coupling).probability ≤ left.probability + right.probability :=
  coupling.union_le left.measurableEvent right.measurableEvent

/-- The intersection bound needs no independence or calibration assumption. -/
 theorem intersection_probability_le_min (left : NumericalEvent s) (right : NumericalEvent t)
    (coupling : ProbabilityCoupling left.law right.law) :
    (intersection left right coupling).probability ≤ min left.probability right.probability :=
  coupling.inter_le_min left.measurableEvent right.measurableEvent

end NumericalEvent

end

end Lara.BHL
