import Lara.BHL.AssertionLaws
import Lara.BHL.BeliefEventLaws

namespace Lara.BHL

noncomputable section

variable {D Command : Type} [MeasurableSpace D] {context : List GhostSort}
variable (I : AssertionInterpretation D Command) (M : Model D Command)
  (env : GhostEnv D Command context)

local notation "Sat" => referenceModalSatisfaction I M env

theorem prior_total_alternative_or_null (world : World D Command)
    (upper lower : ModalFormula context) :
    Sat world ((upper.disj lower).disj (nullAlternative upper lower)) := by
  classical
  simp only [referenceModalSatisfaction_disj, nullAlternative, referenceModalSatisfaction]
  by_cases h : Sat world upper ∨ Sat world lower
  · exact Or.inl h
  · exact Or.inr ⟨fun hu => h (Or.inl hu), fun hl => h (Or.inr hl)⟩

/-- Exclusivity is global over admitted worlds, not merely actual-world truth. -/
theorem prior_exclude_lower_iff_upper_or_null (world : World D Command)
    (upper lower : ModalFormula context)
    (hexclusive : ∀ w, Admitted M.dynamics w → Sat w upper → ¬ Sat w lower) :
    Sat world (.knows (.neg lower)) ↔
      Sat world (.knows (upper.disj (nullAlternative upper lower))) := by
  classical
  apply knows_congr M
  intro w hw _
  simp only [referenceModalSatisfaction_disj, nullAlternative, referenceModalSatisfaction]
  constructor
  · intro h
    by_cases hu : Sat w upper
    · exact Or.inl hu
    · exact Or.inr ⟨hu, h⟩
  · rintro (hu | hnull)
    · exact hexclusive w hw hu
    · exact hnull.2

theorem prior_exclude_upper_iff_lower_or_null (world : World D Command)
    (upper lower : ModalFormula context)
    (hexclusive : ∀ w, Admitted M.dynamics w → Sat w upper → ¬ Sat w lower) :
    Sat world (.knows (.neg upper)) ↔
      Sat world (.knows (lower.disj (nullAlternative upper lower))) := by
  classical
  apply knows_congr M
  intro w hw _
  simp only [referenceModalSatisfaction_disj, nullAlternative, referenceModalSatisfaction]
  constructor
  · intro h
    by_cases hl : Sat w lower
    · exact Or.inl hl
    · exact Or.inr ⟨h, hl⟩
  · rintro (hl | hnull)
    · exact fun hu => hexclusive w hw hu hl
    · exact hnull.1

theorem statisticalBelief_unfold (world : World D Command) (comparison : Comparison)
    (threshold : AssertionTerm context (.value .real)) (test : TestExpression context)
    (alternative : ModalFormula context) :
    Sat world (statisticalBelief comparison threshold test alternative) ↔
      knows M world (fun w => Sat w alternative ∨
        (Sat w (pvalueAtom comparison threshold test) ∧ Sat w (exactHistory test)) ∨
        ¬ Sat w (modelRequirementsFormula test)) := by
  change knows M world _ ↔ knows M world _
  apply knows_congr M
  intro w _ _
  simp only [referenceModalSatisfaction_disj, exception, referenceModalSatisfaction]

theorem belief_invariant {left right : World D Command} (h : Accessible left right)
    (comparison : Comparison) (threshold : AssertionTerm context (.value .real))
    (test : TestExpression context) (alternative : ModalFormula context) :
    Sat left (statisticalBelief comparison threshold test alternative) ↔
      Sat right (statisticalBelief comparison threshold test alternative) :=
  knows_invariant M h _

theorem belief_positive_introspection (world : World D Command) (comparison : Comparison)
    (threshold : AssertionTerm context (.value .real)) (test : TestExpression context)
    (alternative : ModalFormula context)
    (h : Sat world (statisticalBelief comparison threshold test alternative)) :
    Sat world (.knows (statisticalBelief comparison threshold test alternative)) :=
  know_positive_introspection M h

theorem belief_negative_introspection (world : World D Command) (comparison : Comparison)
    (threshold : AssertionTerm context (.value .real)) (test : TestExpression context)
    (alternative : ModalFormula context)
    (h : Sat world (.neg (statisticalBelief comparison threshold test alternative))) :
    Sat world (.knows (.neg (statisticalBelief comparison threshold test alternative))) :=
  know_negative_introspection M h

theorem belief_possibility_known (world : World D Command) (comparison : Comparison)
    (threshold : AssertionTerm context (.value .real)) (test : TestExpression context)
    (alternative : ModalFormula context)
    (h : Sat world (statisticalPossibility comparison threshold test alternative)) :
    Sat world (.knows (statisticalPossibility comparison threshold test alternative)) :=
  know_negative_introspection M h

theorem belief_possibility_negative_introspection (world : World D Command)
    (comparison : Comparison) (threshold : AssertionTerm context (.value .real))
    (test : TestExpression context) (alternative : ModalFormula context)
    (h : Sat world (.neg (statisticalPossibility comparison threshold test alternative))) :
    Sat world (.knows (.neg (statisticalPossibility comparison threshold test alternative))) := by
  intro w _ hw hp
  exact h (fun hb => hp ((belief_invariant I M env hw comparison threshold test (.neg alternative)).mp hb))

theorem knowledge_implies_statistical_belief (world : World D Command)
    (comparison : Comparison) (threshold : AssertionTerm context (.value .real))
    (test : TestExpression context) (alternative : ModalFormula context)
    (h : Sat world (.knows alternative)) :
    Sat world (statisticalBelief comparison threshold test alternative) := by
  apply (statisticalBelief_unfold I M env world comparison threshold test alternative).mpr
  intro w hw ha
  exact Or.inl (h w hw ha)

theorem pvalue_atom_fixed_iff (world : World D Command) (comparison : Comparison)
    (threshold : AssertionTerm context (.value .real)) (test : TestExpression context)
    (value : ℝ) (hfixed : FixedRealTerm I M env threshold value) :
    Sat world (pvalueAtom comparison threshold test) ↔
      ∃ p, evalTerm I M env (semanticView M.dynamics world) (.pvalue test) = some p ∧
        compareReal comparison p value := by
  constructor
  · rintro ⟨a, b, ha, hb, hcompare⟩
    rw [hfixed (semanticView M.dynamics world)] at hb
    have hvalue : value = b := Option.some.inj hb
    exact ⟨a, ha, hvalue.symm ▸ hcompare⟩
  · rintro ⟨p, hp, hcompare⟩
    exact ⟨p, value, hp, hfixed (semanticView M.dynamics world), hcompare⟩

theorem pvalue_atom_undefined (world : World D Command) (comparison : Comparison)
    (threshold : AssertionTerm context (.value .real)) (test : TestExpression context)
    (h : evalTerm I M env (semanticView M.dynamics world) (.pvalue test) = none) :
    ¬ Sat world (pvalueAtom comparison threshold test) := by
  rintro ⟨a, b, ha, _, _⟩
  rw [h] at ha
  cases ha

theorem pvalue_atom_threshold_undefined (world : World D Command) (comparison : Comparison)
    (threshold : AssertionTerm context (.value .real)) (test : TestExpression context)
    (h : evalTerm I M env (semanticView M.dynamics world) threshold = none) :
    ¬ Sat world (pvalueAtom comparison threshold test) := by
  rintro ⟨a, b, _, hb, _⟩
  rw [h] at hb
  cases hb

/-- Only the exception comparison changes; history and model-failure stay intact. -/
theorem belief_of_pvalue_implication (world : World D Command)
    (first second : Comparison) (a b : AssertionTerm context (.value .real))
    (test : TestExpression context) (alternative : ModalFormula context)
    (himp : ∀ w, Admitted M.dynamics w → Accessible world w →
      Sat w (pvalueAtom first a test) → Sat w (pvalueAtom second b test))
    (h : Sat world (statisticalBelief first a test alternative)) :
    Sat world (statisticalBelief second b test alternative) := by
  rw [statisticalBelief_unfold] at h ⊢
  intro w hw ha
  rcases h w hw ha with halt | hex | hfail
  · exact Or.inl halt
  · exact Or.inr (Or.inl ⟨himp w hw ha hex.1, hex.2⟩)
  · exact Or.inr (Or.inr hfail)

theorem belief_le_mono (world : World D Command)
    (a b : AssertionTerm context (.value .real)) (test : TestExpression context)
    (alternative : ModalFormula context) (epsilon epsilon' : ℝ)
    (ha : FixedRealTerm I M env a epsilon) (hb : FixedRealTerm I M env b epsilon')
    (hle : epsilon ≤ epsilon')
    (h : Sat world (statisticalBelief .lessEqual a test alternative)) :
    Sat world (statisticalBelief .lessEqual b test alternative) := by
  apply belief_of_pvalue_implication I M env world .lessEqual .lessEqual a b test alternative _ h
  intro w _ _ hp
  rcases (pvalue_atom_fixed_iff I M env w .lessEqual a test epsilon ha).mp hp with ⟨p, he, hc⟩
  exact (pvalue_atom_fixed_iff I M env w .lessEqual b test epsilon' hb).mpr
    ⟨p, he, le_trans hc hle⟩

theorem belief_lt_mono (world : World D Command)
    (a b : AssertionTerm context (.value .real)) (test : TestExpression context)
    (alternative : ModalFormula context) (epsilon epsilon' : ℝ)
    (ha : FixedRealTerm I M env a epsilon) (hb : FixedRealTerm I M env b epsilon')
    (hle : epsilon ≤ epsilon')
    (h : Sat world (statisticalBelief .less a test alternative)) :
    Sat world (statisticalBelief .less b test alternative) := by
  apply belief_of_pvalue_implication I M env world .less .less a b test alternative _ h
  intro w _ _ hp
  rcases (pvalue_atom_fixed_iff I M env w .less a test epsilon ha).mp hp with ⟨p, he, hc⟩
  exact (pvalue_atom_fixed_iff I M env w .less b test epsilon' hb).mpr
    ⟨p, he, lt_of_lt_of_le hc hle⟩

theorem belief_eq_to_le (world : World D Command)
    (threshold : AssertionTerm context (.value .real)) (test : TestExpression context)
    (alternative : ModalFormula context)
    (h : Sat world (statisticalBelief .equal threshold test alternative)) :
    Sat world (statisticalBelief .lessEqual threshold test alternative) := by
  apply belief_of_pvalue_implication I M env world .equal .lessEqual threshold threshold test alternative _ h
  intro w _ _ hp
  rcases hp with ⟨a, b, ha, hb, heq⟩
  exact ⟨a, b, ha, hb, le_of_eq heq⟩

theorem belief_le_possibility_antitone (world : World D Command)
    (a b : AssertionTerm context (.value .real)) (test : TestExpression context)
    (alternative : ModalFormula context) (epsilon epsilon' : ℝ)
    (ha : FixedRealTerm I M env a epsilon) (hb : FixedRealTerm I M env b epsilon')
    (hle : epsilon ≤ epsilon')
    (h : Sat world (statisticalPossibility .lessEqual b test alternative)) :
    Sat world (statisticalPossibility .lessEqual a test alternative) := by
  intro hbelief
  exact h (belief_le_mono I M env world a b test (.neg alternative) epsilon epsilon' ha hb hle hbelief)

theorem belief_lt_possibility_antitone (world : World D Command)
    (a b : AssertionTerm context (.value .real)) (test : TestExpression context)
    (alternative : ModalFormula context) (epsilon epsilon' : ℝ)
    (ha : FixedRealTerm I M env a epsilon) (hb : FixedRealTerm I M env b epsilon')
    (hle : epsilon ≤ epsilon')
    (h : Sat world (statisticalPossibility .less b test alternative)) :
    Sat world (statisticalPossibility .less a test alternative) := by
  intro hbelief
  exact h (belief_lt_mono I M env world a b test (.neg alternative) epsilon epsilon' ha hb hle hbelief)

theorem belief_eq_possibility_of_le (world : World D Command)
    (threshold : AssertionTerm context (.value .real)) (test : TestExpression context)
    (alternative : ModalFormula context)
    (h : Sat world (statisticalPossibility .lessEqual threshold test alternative)) :
    Sat world (statisticalPossibility .equal threshold test alternative) := by
  intro hbelief
  exact h (belief_eq_to_le I M env world threshold test (.neg alternative) hbelief)

theorem exactHistory_invariant (test : TestExpression context)
    (hobs : ObservableTestExpression I M env test)
    {left right : World D Command} (h : Accessible left right) :
    Sat left (exactHistory test) ↔ Sat right (exactHistory test) := by
  rw [exactHistory_iff_ledger, exactHistory_iff_ledger,
    observableTest_history_invariant I M env test hobs h, accessible_history_eq h]

theorem exactHistory_known (world : World D Command) (test : TestExpression context)
    (hobs : ObservableTestExpression I M env test) (h : Sat world (exactHistory test)) :
    Sat world (.knows (exactHistory test)) := by
  intro w _ hw
  exact (exactHistory_invariant I M env test hobs hw).mp h

theorem exactHistory_known_iff (world : World D Command) (test : TestExpression context)
    (hadmitted : Admitted M.dynamics world) (hobs : ObservableTestExpression I M env test) :
    Sat world (.knows (exactHistory test)) ↔ Sat world (exactHistory test) :=
  ⟨know_truth M hadmitted, exactHistory_known I M env world test hobs⟩

theorem exactHistory_possible_iff (world : World D Command) (test : TestExpression context)
    (hadmitted : Admitted M.dynamics world) (hobs : ObservableTestExpression I M env test) :
    Sat world ((exactHistory test).possible) ↔ Sat world (exactHistory test) := by
  rw [referenceModalSatisfaction_possible, possible_iff_exists]
  constructor
  · rintro ⟨w, _, hw, hp⟩
    exact (exactHistory_invariant I M env test hobs hw).mpr hp
  · intro h
    exact ⟨world, hadmitted, accessible_refl world, h⟩

/-- Self-equality requires an actually defined event; undefined is not zero. -/
theorem pvalue_atom_self (world : World D Command) (test : TestExpression context)
    (hdefined : ∃ event, evalNumericalEvent I M env (semanticView M.dynamics world) test = some event) :
    Sat world (pvalueAtom .equal (.pvalue test) test) := by
  rcases hdefined with ⟨event, hevent⟩
  exact ⟨event.2.probability, event.2.probability,
    by simp [evalTerm, hevent], by simp [evalTerm, hevent], rfl⟩

/-- Exact current history and an observable defined event suffice through the
exception disjunct, without proving the alternative or model requirements. -/
theorem belief_from_exact_test_history (world : World D Command)
    (test : TestExpression context) (alternative : ModalFormula context)
    (hobs : ObservableTestExpression I M env test)
    (hdefined : ∃ event, evalNumericalEvent I M env (semanticView M.dynamics world) test = some event)
    (hhistory : Sat world (exactHistory test)) :
    Sat world (statisticalBelief .equal (.pvalue test) test alternative) := by
  apply (statisticalBelief_unfold I M env world .equal (.pvalue test) test alternative).mpr
  intro w _ hw
  refine Or.inr (Or.inl ⟨pvalue_atom_self I M env w test ?_,
    (exactHistory_invariant I M env test hobs hw).mp hhistory⟩)
  rcases hdefined with ⟨event, hevent⟩
  exact ⟨event, (observableTest_event_invariant I M env test hobs hw).symm.trans hevent⟩

/-- The frozen value may be an actual p-value stored in a rigid real ghost. -/
theorem belief_from_exact_history_fixed_bound (world : World D Command)
    (test : TestExpression context) (alternative : ModalFormula context)
    (comparison : Comparison) (threshold : AssertionTerm context (.value .real)) (value : ℝ)
    (hfixed : FixedRealTerm I M env threshold value)
    (hobs : ObservableTestExpression I M env test)
    (event : PackedNumericalEvent)
    (hevent : evalNumericalEvent I M env (semanticView M.dynamics world) test = some event)
    (hcompare : compareReal comparison event.2.probability value)
    (hhistory : Sat world (exactHistory test)) :
    Sat world (statisticalBelief comparison threshold test alternative) := by
  apply (statisticalBelief_unfold I M env world comparison threshold test alternative).mpr
  intro w _ hw
  refine Or.inr (Or.inl ⟨?_, (exactHistory_invariant I M env test hobs hw).mp hhistory⟩)
  apply (pvalue_atom_fixed_iff I M env w comparison threshold test value hfixed).mpr
  refine ⟨event.2.probability, ?_, hcompare⟩
  have he := (observableTest_event_invariant I M env test hobs hw).symm.trans hevent
  simp [evalTerm, he]

/-- Observable thresholds can be actual expression values; unlike threshold
monotonicity, this transport does not claim they are globally fixed constants. -/
theorem belief_from_observable_exception (world : World D Command)
    (comparison : Comparison) (threshold : AssertionTerm context (.value .real))
    (test : TestExpression context) (alternative : ModalFormula context)
    (hobs : ObservableTestExpression I M env test)
    (hthreshold : ObservationInvariantTerm I M env threshold)
    (hp : Sat world (pvalueAtom comparison threshold test))
    (hhistory : Sat world (exactHistory test)) :
    Sat world (statisticalBelief comparison threshold test alternative) := by
  apply (statisticalBelief_unfold I M env world comparison threshold test alternative).mpr
  intro w _ hw
  rcases hp with ⟨p, bound, heval, hbound, hcompare⟩
  refine Or.inr (Or.inl ⟨⟨p, bound, ?_, ?_, hcompare⟩,
    (exactHistory_invariant I M env test hobs hw).mp hhistory⟩)
  · exact (observationInvariant_pvalue I M env test hobs world w hw).symm.trans heval
  · exact (hthreshold world w hw).symm.trans hbound

/-- The union uses the actual named coupling and actual current child p-values.
Neither independence nor availability of a missing coupling is inferred. -/
theorem belief_combined_disj (world : World D Command) (name : CouplingId)
    (left right : TestExpression context) (alternative : ModalFormula context)
    (hleft : ObservableTestExpression I M env left)
    (hright : ObservableTestExpression I M env right)
    (a b : PackedNumericalEvent) (coupling : ProbabilityCoupling a.2.law b.2.law)
    (ha : evalNumericalEvent I M env (semanticView M.dynamics world) left = some a)
    (hb : evalNumericalEvent I M env (semanticView M.dynamics world) right = some b)
    (hc : I.couplings name a.1 b.1 a.2.law b.2.law = some coupling)
    (hhistory : Sat world (exactHistory (.disj name left right))) :
    Sat world (statisticalBelief .lessEqual
      (.realAdd (.pvalue left) (.pvalue right)) (.disj name left right) alternative) := by
  apply belief_from_observable_exception I M env world .lessEqual
    (.realAdd (.pvalue left) (.pvalue right)) (.disj name left right) alternative
    ⟨hleft, hright⟩ _ _ hhistory
  · intro w v hwv
    change (do let p ← evalTerm I M env (semanticView M.dynamics w) (.pvalue left)
               let q ← evalTerm I M env (semanticView M.dynamics w) (.pvalue right)
               pure (p + q)) = _
    rw [observationInvariant_pvalue I M env left hleft w v hwv,
      observationInvariant_pvalue I M env right hright w v hwv]
    rfl
  · have hevent := evalNumericalEvent_disj_of_coupling I M env
      (semanticView M.dynamics world) name left right a b coupling ha hb hc
    refine ⟨(NumericalEvent.union a.2 b.2 coupling).probability,
      a.2.probability + b.2.probability, ?_, ?_, NumericalEvent.union_probability_le a.2 b.2 coupling⟩
    · simp [evalTerm, hevent]
    · simp [evalTerm, ha, hb]

/-- Intersection's bound is the actual minimum, with both marginal laws checked. -/
theorem belief_combined_conj (world : World D Command) (name : CouplingId)
    (left right : TestExpression context) (alternative : ModalFormula context)
    (hleft : ObservableTestExpression I M env left)
    (hright : ObservableTestExpression I M env right)
    (a b : PackedNumericalEvent) (coupling : ProbabilityCoupling a.2.law b.2.law)
    (ha : evalNumericalEvent I M env (semanticView M.dynamics world) left = some a)
    (hb : evalNumericalEvent I M env (semanticView M.dynamics world) right = some b)
    (hc : I.couplings name a.1 b.1 a.2.law b.2.law = some coupling)
    (hhistory : Sat world (exactHistory (.conj name left right))) :
    Sat world (statisticalBelief .lessEqual
      (.realMin (.pvalue left) (.pvalue right)) (.conj name left right) alternative) := by
  apply belief_from_observable_exception I M env world .lessEqual
    (.realMin (.pvalue left) (.pvalue right)) (.conj name left right) alternative
    ⟨hleft, hright⟩ _ _ hhistory
  · intro w v hwv
    change (do let p ← evalTerm I M env (semanticView M.dynamics w) (.pvalue left)
               let q ← evalTerm I M env (semanticView M.dynamics w) (.pvalue right)
               pure (min p q)) = _
    rw [observationInvariant_pvalue I M env left hleft w v hwv,
      observationInvariant_pvalue I M env right hright w v hwv]
    rfl
  · have hevent := evalNumericalEvent_conj_of_coupling I M env
      (semanticView M.dynamics world) name left right a b coupling ha hb hc
    refine ⟨(NumericalEvent.intersection a.2 b.2 coupling).probability,
      min a.2.probability b.2.probability, ?_, ?_,
      NumericalEvent.intersection_probability_le_min a.2 b.2 coupling⟩
    · simp [evalTerm, hevent]
    · simp [evalTerm, ha, hb]

theorem belief_combined_disj_fixed (world : World D Command) (name : CouplingId)
    (left right : TestExpression context) (alternative : ModalFormula context)
    (hleft : ObservableTestExpression I M env left)
    (hright : ObservableTestExpression I M env right)
    (a b : PackedNumericalEvent) (coupling : ProbabilityCoupling a.2.law b.2.law)
    (ha : evalNumericalEvent I M env (semanticView M.dynamics world) left = some a)
    (hb : evalNumericalEvent I M env (semanticView M.dynamics world) right = some b)
    (hc : I.couplings name a.1 b.1 a.2.law b.2.law = some coupling)
    (threshold : AssertionTerm context (.value .real))
    (hfixed : FixedRealTerm I M env threshold (a.2.probability + b.2.probability))
    (hhistory : Sat world (exactHistory (.disj name left right))) :
    Sat world (statisticalBelief .lessEqual threshold (.disj name left right) alternative) :=
  belief_from_exact_history_fixed_bound I M env world (.disj name left right) alternative
    .lessEqual threshold (a.2.probability + b.2.probability) hfixed ⟨hleft, hright⟩
    ⟨.product a.1 b.1, NumericalEvent.union a.2 b.2 coupling⟩
    (evalNumericalEvent_disj_of_coupling I M env (semanticView M.dynamics world)
      name left right a b coupling ha hb hc)
    (NumericalEvent.union_probability_le a.2 b.2 coupling) hhistory

theorem belief_combined_conj_fixed (world : World D Command) (name : CouplingId)
    (left right : TestExpression context) (alternative : ModalFormula context)
    (hleft : ObservableTestExpression I M env left)
    (hright : ObservableTestExpression I M env right)
    (a b : PackedNumericalEvent) (coupling : ProbabilityCoupling a.2.law b.2.law)
    (ha : evalNumericalEvent I M env (semanticView M.dynamics world) left = some a)
    (hb : evalNumericalEvent I M env (semanticView M.dynamics world) right = some b)
    (hc : I.couplings name a.1 b.1 a.2.law b.2.law = some coupling)
    (threshold : AssertionTerm context (.value .real))
    (hfixed : FixedRealTerm I M env threshold (min a.2.probability b.2.probability))
    (hhistory : Sat world (exactHistory (.conj name left right))) :
    Sat world (statisticalBelief .lessEqual threshold (.conj name left right) alternative) :=
  belief_from_exact_history_fixed_bound I M env world (.conj name left right) alternative
    .lessEqual threshold (min a.2.probability b.2.probability) hfixed ⟨hleft, hright⟩
    ⟨.product a.1 b.1, NumericalEvent.intersection a.2 b.2 coupling⟩
    (evalNumericalEvent_conj_of_coupling I M env (semanticView M.dynamics world)
      name left right a b coupling ha hb hc)
    (NumericalEvent.intersection_probability_le_min a.2 b.2 coupling) hhistory

/-- For a single test, exact history itself supplies dataset definedness. -/
theorem belief_from_exact_leaf_history (world : World D Command)
    (hypothesis : HypothesisId) (data : AssertionTerm context .dataset)
    (test : TestId) (population : PopulationId) (alternative : ModalFormula context)
    (hobs : ObservationInvariantTerm I M env data)
    (hhistory : Sat world (exactHistory (.leaf hypothesis data test population))) :
    Sat world (statisticalBelief .equal (.pvalue (.leaf hypothesis data test population))
      (.leaf hypothesis data test population) alternative) := by
  have hledger := (exactHistory_iff_ledger I M env world
    (.leaf hypothesis data test population)).mp hhistory
  rw [evalTestHistory_leaf] at hledger
  cases hdata : evalTerm I M env (semanticView M.dynamics world) data with
  | none => simp [hdata] at hledger
  | some d =>
      apply belief_from_exact_test_history I M env world
        (.leaf hypothesis data test population) alternative hobs _ hhistory
      exact ⟨⟨.real, NumericalEvent.tail (I.tests hypothesis test) d⟩,
        by simp [evalNumericalEvent, hdata]⟩

/-- Undefined data do not establish scientific model failure. Evaluation
definedness remains an independent premise of a modeled test application. -/
theorem modelRequirements_leaf_undefined (view : SemanticView D) (hypothesis : HypothesisId)
    (data : AssertionTerm context .dataset) (test : TestId) (population : PopulationId)
    (undefined : evalTerm I M env view data = none) :
    modelRequirements I M env view (.leaf hypothesis data test population) := by
  intro d evaluated
  rw [undefined] at evaluated
  contradiction

theorem modelRequirements_leaf_defined_iff (view : SemanticView D) (hypothesis : HypothesisId)
    (data : AssertionTerm context .dataset) (test : TestId) (population : PopulationId) (d : D)
    (evaluated : evalTerm I M env view data = some d) :
    modelRequirements I M env view (.leaf hypothesis data test population) ↔
      I.requirements hypothesis test population view.hidden d ∧ (d, population) ∈ view.provenance := by
  simp [modelRequirements, evaluated]

/-- At an admitted world with true scientific requirements and a false
alternative, undefined numerical evaluation rules out belief. This includes
missing composite couplings, but does not exclude belief via another disjunct. -/
theorem undefined_numerical_binding_not_belief (world : World D Command)
    (admitted : Admitted M.dynamics world) (comparison : Comparison)
    (threshold : AssertionTerm context (.value .real)) (test : TestExpression context)
    (alternative : ModalFormula context)
    (undefined : evalNumericalEvent I M env (semanticView M.dynamics world) test = none)
    (scientific : modelRequirements I M env (semanticView M.dynamics world) test)
    (falseAlternative : ¬ Sat world alternative) :
    ¬ Sat world (statisticalBelief comparison threshold test alternative) := by
  intro belief
  have actual := know_truth M admitted
    ((statisticalBelief_unfold I M env world comparison threshold test alternative).mp belief)
  rcases actual with halt | hexception | hfailure
  · exact falseAlternative halt
  · exact (pvalue_atom_undefined I M env world comparison threshold test
      (by simp [evalTerm, undefined])) hexception.1
  · apply hfailure
    simpa [modelRequirementsFormula, referenceModalSatisfaction, atomMeaning, evalTerm] using scientific

end
end Lara.BHL
