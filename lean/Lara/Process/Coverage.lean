import Lara.Process.Verdict

/-!
Laws of scoped coverage assumptions.

Coverage constructors are compatibility predicates, not a strength ladder.
Strength is `Assumptions.Stronger`, inclusion of allowed pairs on one model.
Two laws hold for every scope: open-world coverage is implied by every other
assumption, and a smaller count bound is stronger than a larger one. No
further order between constructors is claimed;
`Lara.Examples.ProcessCore.coverage_incomparable` exhibits a complete and a
count-bounded assumption whose allowed sets are incomparable.
-/

namespace Lara.Process

universe u v

variable {H : Type u} {Rho : Type v} {Policy : Type}
  (policy : Policy → ProcessHistory → List Stamped → Prop)
  (trace : H → ProcessHistory) (exposed : H → Rho → List Stamped)

instance [∀ p h reported, Decidable (policy p h reported)] (c : RecordCoverage Policy)
    (h : H) (rho : Rho) : Decidable ((c.assumptions policy trace exposed).Allowed h rho) :=
  inferInstanceAs (Decidable (c.Allowed policy (trace h) (exposed h rho)))

/-- Every scoped assumption is at least as strong as open-world coverage. -/
theorem RecordCoverage.stronger_openWorld (c : RecordCoverage Policy) (scope : CoverageScope) :
    (c.assumptions policy trace exposed).Stronger
      ((RecordCoverage.openWorld scope).assumptions policy trace exposed) :=
  fun _ _ _ => True.intro

/-- A smaller count bound is stronger. -/
theorem RecordCoverage.countBounded_mono (scope : CoverageScope) {small large : Nat}
    (le : small ≤ large) :
    ((RecordCoverage.countBounded scope small : RecordCoverage Policy).assumptions
        policy trace exposed).Stronger
      ((RecordCoverage.countBounded scope large).assumptions policy trace exposed) :=
  fun _ _ allowed => Nat.le_trans allowed le

/-- Strength is a preorder. -/
theorem Assumptions.stronger_refl (A : Assumptions H Rho) : A.Stronger A :=
  fun _ _ h => h

theorem Assumptions.stronger_trans {A B C : Assumptions H Rho} (ab : A.Stronger B)
    (bc : B.Stronger C) : A.Stronger C :=
  fun h rho allowed => bc h rho (ab h rho allowed)

/-- Adding an assumption is stronger than either part. -/
theorem Assumptions.and_stronger_left (A B : Assumptions H Rho) : (A.and B).Stronger A :=
  fun _ _ h => h.1

theorem Assumptions.and_stronger_right (A B : Assumptions H Rho) : (A.and B).Stronger B :=
  fun _ _ h => h.2

/-- Under complete coverage of a scope, with reports that expose only in-scope
events of the history, every compatible history has exactly the record's events
in scope. -/
theorem complete_scope_events {S : ProcessModel H Rho (List Stamped)} (scope : CoverageScope)
    (report : ∀ h rho, S.Report h rho = exposed h rho)
    (inScope : ∀ h rho, S.Valid h → ∀ e ∈ exposed h rho, e ∈ scope.events (trace h))
    {r : List Stamped} {x : H × Rho}
    (hx : Compatible S ((RecordCoverage.complete scope : RecordCoverage Policy).assumptions
      policy trace exposed) r x) :
    ∀ e, e ∈ scope.events (trace x.1) ↔ e ∈ r := by
  obtain ⟨valid, allowed, reported⟩ := hx
  rw [report] at reported
  intro e
  constructor
  · intro mem
    exact reported ▸ allowed e mem
  · intro mem
    exact inScope x.1 x.2 valid e (reported ▸ mem)

/-- Complete coverage determines every property that reads only the in-scope
events: a realized record has exactly the verdict of its generating history.
A property reading anything outside the scope (data accesses outside a test
scope, for instance) is not covered by this theorem. -/
theorem complete_coverage_determines {S : ProcessModel H Rho (List Stamped)}
    (scope : CoverageScope) (report : ∀ h rho, S.Report h rho = exposed h rho)
    (inScope : ∀ h rho, S.Valid h → ∀ e ∈ exposed h rho, e ∈ scope.events (trace h))
    {φ : H × Rho → Prop}
    (reads : ∀ x y, (∀ e, e ∈ scope.events (trace x.1) ↔ e ∈ scope.events (trace y.1)) →
      (φ x ↔ φ y))
    {r : List Stamped} {x₀ : H × Rho}
    (realized : Compatible S ((RecordCoverage.complete scope : RecordCoverage Policy).assumptions
      policy trace exposed) r x₀) :
    (verdictOf (Compatible S ((RecordCoverage.complete scope).assumptions policy trace exposed) r)
        φ = .certainTrue ↔ φ x₀) ∧
      (verdictOf (Compatible S ((RecordCoverage.complete scope).assumptions policy trace exposed) r)
        φ = .certainFalse ↔ ¬ φ x₀) := by
  refine verdict_of_generator realized fun x hx => reads x x₀ fun e => ?_
  rw [complete_scope_events policy trace exposed scope report inScope hx,
    complete_scope_events policy trace exposed scope report inScope realized]

end Lara.Process
