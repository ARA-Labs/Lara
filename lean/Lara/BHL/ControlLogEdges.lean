import Lara.BHL.ControlLogTerms

namespace Lara.BHL.ControlLogSyntax

variable {D : Type} [MeasurableSpace D] {Γ : List GhostSort}

noncomputable section

private theorem trueFormula_satisfaction (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (view : SemanticView D) :
    viewModalSatisfaction ctx.interpretation ctx.model env view (trueFormula : ModalFormula Γ) := by
  exact ⟨0, rfl, rfl⟩

theorem conjunction_satisfaction (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (view : SemanticView D) (formulas : List (ModalFormula Γ)) :
    viewModalSatisfaction ctx.interpretation ctx.model env view (conjunction formulas) ↔
      ∀ formula ∈ formulas, viewModalSatisfaction ctx.interpretation ctx.model env view formula := by
  induction formulas with
  | nil =>
      simp only [conjunction, List.foldr_nil]
      exact ⟨fun _ _ h => False.elim (List.not_mem_nil h),
        fun _ => trueFormula_satisfaction ctx env view⟩
  | cons formula formulas ih =>
      change (viewModalSatisfaction ctx.interpretation ctx.model env view formula ∧
        viewModalSatisfaction ctx.interpretation ctx.model env view (conjunction formulas)) ↔ _
      rw [ih, List.forall_mem_cons]

theorem disjunction_satisfaction (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (view : SemanticView D) (formulas : List (ModalFormula Γ)) :
    viewModalSatisfaction ctx.interpretation ctx.model env view (disjunction formulas) ↔
      ∃ formula ∈ formulas, viewModalSatisfaction ctx.interpretation ctx.model env view formula := by
  classical
  induction formulas with
  | nil =>
      change (¬ viewModalSatisfaction ctx.interpretation ctx.model env view
        (trueFormula : ModalFormula Γ)) ↔ _
      simp [trueFormula_satisfaction ctx env view]
  | cons formula formulas ih =>
      change (¬ (¬ viewModalSatisfaction ctx.interpretation ctx.model env view formula ∧
        ¬ viewModalSatisfaction ctx.interpretation ctx.model env view (disjunction formulas))) ↔ _
      rw [ih]
      simp only [not_and_or, not_not]
      constructor
      · rintro (satisfied | ⟨member, belongs, satisfied⟩)
        · exact ⟨formula, List.mem_cons_self, satisfied⟩
        · exact ⟨member, List.mem_cons_of_mem _ belongs, satisfied⟩
      · rintro ⟨member, belongs, satisfied⟩
        rcases List.mem_cons.mp belongs with rfl | belongs
        · exact Or.inl satisfied
        · exact Or.inr ⟨member, belongs, satisfied⟩

private theorem equal_right_satisfaction (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (view : SemanticView D)
    (left right : AssertionTerm Γ sort) (value : TermValue D Primitive sort)
    (evaluated : evalTerm ctx.interpretation ctx.model env view right = some value) :
    viewModalSatisfaction ctx.interpretation ctx.model env view (.atom (.equal left right)) ↔
      evalTerm ctx.interpretation ctx.model env view left = some value := by
  change (∃ result, evalTerm ctx.interpretation ctx.model env view left = some result ∧
    evalTerm ctx.interpretation ctx.model env view right = some result) ↔ _
  rw [evaluated]
  simp only [Option.some.injEq, exists_eq_right']

private theorem equal_evaluated_satisfaction (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (view : SemanticView D)
    (left right : AssertionTerm Γ sort) (a b : TermValue D Primitive sort)
    (leftEvaluated : evalTerm ctx.interpretation ctx.model env view left = some a)
    (rightEvaluated : evalTerm ctx.interpretation ctx.model env view right = some b) :
    viewModalSatisfaction ctx.interpretation ctx.model env view (.atom (.equal left right)) ↔ a = b := by
  rw [equal_right_satisfaction ctx env view left right b rightEvaluated, leftEvaluated]
  simp only [Option.some.injEq]

private theorem boundedInteger_satisfaction (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (view : SemanticView D)
    (count length : AssertionTerm Γ (.value .integer)) (bound : Nat)
    (lengthEvaluated : evalTerm ctx.interpretation ctx.model env view length = some (bound : Int)) :
    (viewModalSatisfaction ctx.interpretation ctx.model env view
        (.atom (.intCompare .lessEqual (.integer 0) count)) ∧
      viewModalSatisfaction ctx.interpretation ctx.model env view
        (.atom (.intCompare .lessEqual count length))) ↔
      ∃ n : Nat, n ≤ bound ∧ evalTerm ctx.interpretation ctx.model env view count = some (n : Int) := by
  constructor
  · rintro ⟨⟨zero, value, hzero, evaluated, lower⟩, ⟨other, limit, hother, hlimit, upper⟩⟩
    have hz : zero = 0 := by simpa only [evalTerm, Option.some.injEq] using hzero.symm
    have ho : other = value := Option.some.inj (hother.symm.trans evaluated)
    have hl : limit = (bound : Int) := Option.some.inj (hlimit.symm.trans lengthEvaluated)
    subst zero
    subst other
    subst limit
    change (0 : Int) ≤ value at lower
    change value ≤ (bound : Int) at upper
    refine ⟨value.toNat, Int.toNat_le.mpr upper, ?_⟩
    simpa only [Int.toNat_of_nonneg lower] using evaluated
  · rintro ⟨n, bounded, evaluated⟩
    refine ⟨⟨0, (n : Int), rfl, evaluated, ?_⟩,
      ⟨(n : Int), (bound : Int), evaluated, lengthEvaluated, ?_⟩⟩
    · change (0 : Int) ≤ (n : Int)
      omega
    · change (n : Int) ≤ (bound : Int)
      exact Int.ofNat_le.mpr bounded

private theorem admitted_satisfaction (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (view : SemanticView D)
    (term : AssertionTerm Γ .world) (world : World D Primitive)
    (evaluated : evalTerm ctx.interpretation ctx.model env view term = some world) :
    viewModalSatisfaction ctx.interpretation ctx.model env view (.atom (.admitted term)) ↔
      Admitted ctx.model.dynamics world := by
  change (∃ result, evalTerm ctx.interpretation ctx.model env view term = some result ∧
    Admitted ctx.model.dynamics result) ↔ _
  rw [evaluated]
  simp only [Option.some.injEq, exists_eq_left']

private theorem atView_satisfaction (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (view : SemanticView D)
    (term : AssertionTerm Γ .view) (world : World D Primitive) (formula : ModalFormula Γ)
    (evaluated : evalTerm ctx.interpretation ctx.model env view term =
      some (semanticView ctx.model.dynamics world)) (admitted : Admitted ctx.model.dynamics world) :
    viewModalSatisfaction ctx.interpretation ctx.model env view (.atView term formula) ↔
      viewModalSatisfaction ctx.interpretation ctx.model env
        (semanticView ctx.model.dynamics world) formula := by
  change (∃ result, evalTerm ctx.interpretation ctx.model env view term = some result ∧
    result ∈ ctx.model.views ∧ viewModalSatisfaction ctx.interpretation ctx.model env result formula) ↔ _
  rw [evaluated]
  simp only [Option.some.injEq, exists_eq_left']
  exact and_iff_right (semanticView_mem_views ctx.model admitted)

private theorem primitive_viewEffect_satisfaction (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (primitive : Primitive) (before after : World D Primitive) :
    evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics before)
        (primitive.viewTerm Γ) = some (semanticView ctx.model.dynamics after) ↔
      (ControlLabel.command primitive).viewEffect ctx before after := by
  constructor
  · intro evaluated
    rw [evalPrimitive_viewTerm] at evaluated
    cases effect : primitiveEffect ctx.interpretation primitive before.current.visible with
    | none => simp only [semanticView, effect, Option.map_none] at evaluated; contradiction
    | some out =>
        rcases out with ⟨visible, delta⟩
        refine ⟨visible, delta, effect, ?_⟩
        exact (Option.some.inj (by simpa only [semanticView, effect, Option.map_some]
          using evaluated)).symm
  · rintro ⟨visible, delta, effect, fullView⟩
    rw [evalPrimitive_viewTerm]
    change (primitiveEffect ctx.interpretation primitive before.current.visible).map
      (fun out => {semanticView ctx.model.dynamics before with
        visible := out.1, history := before.current.history + out.2}) = _
    rw [effect, Option.map_some, fullView]

private theorem label_satisfaction (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (label : ControlLabel) (index : AssertionTerm Γ (.value .integer)) (j count nextCount : Nat)
    (indexDenotes : ∀ view, evalTerm ctx.interpretation ctx.model env view index = some (j : Int))
    (countEvaluated : log.readCell j .commands = some (count : Int))
    (nextEvaluated : log.readCell (j + 1) .commands = some (nextCount : Int))
    (admitted : Admitted ctx.model.dynamics (log.programPrefix count)) (view : SemanticView D) :
    viewModalSatisfaction ctx.interpretation ctx.model env view
      (match label with
      | .guard expression value =>
          .conj (.atom (.equal (terms.count (.intAdd index (.integer 1))) (terms.count index)))
            (.atView (terms.programView index)
              (.atom (.equal (expression.toAssertionTerm Γ) (.boolean value))))
      | .command primitive =>
          .conj (.atom (.equal (terms.count (.intAdd index (.integer 1)))
            (.intAdd (terms.count index) (.integer 1))))
            (.atView (terms.programView index)
              (.atom (.equal (primitive.viewTerm Γ)
                (terms.programView (.intAdd index (.integer 1))))))) ↔
      label.viewEffect ctx (log.programPrefix count) (log.programPrefix nextCount) ∧
        (match label with
        | .guard _ _ => nextCount = count
        | .command _ => nextCount = count + 1) := by
  have nextIndex : ∀ v, evalTerm ctx.interpretation ctx.model env v
      (.intAdd index (.integer 1)) = some ((j + 1 : Nat) : Int) :=
    fun v => eval_nextIndex ctx env v index j (indexDenotes v)
  have hc : ∀ v, evalTerm ctx.interpretation ctx.model env v (terms.count index) = some (count : Int) :=
    fun v => (Terms.eval_count terms ctx env log denotes v index j (indexDenotes v)).trans countEvaluated
  have hn : ∀ v, evalTerm ctx.interpretation ctx.model env v
      (terms.count (.intAdd index (.integer 1))) = some (nextCount : Int) :=
    fun v => (Terms.eval_count terms ctx env log denotes v _ (j + 1) (nextIndex v)).trans nextEvaluated
  have hv : ∀ v, evalTerm ctx.interpretation ctx.model env v (terms.programView index) =
      some (semanticView ctx.model.dynamics (log.programPrefix count)) :=
    fun v => Terms.eval_programView terms ctx env log denotes v index j count (indexDenotes v) countEvaluated
  have hnv : ∀ v, evalTerm ctx.interpretation ctx.model env v
      (terms.programView (.intAdd index (.integer 1))) =
      some (semanticView ctx.model.dynamics (log.programPrefix nextCount)) :=
    fun v => Terms.eval_programView terms ctx env log denotes v _ (j + 1) nextCount (nextIndex v) nextEvaluated
  cases label with
  | guard expression value =>
      rw [viewModalSatisfaction,
        equal_evaluated_satisfaction ctx env view _ _ (nextCount : Int) (count : Int) (hn view) (hc view),
        atView_satisfaction ctx env view _ (log.programPrefix count) _ (hv view) admitted,
        equal_right_satisfaction ctx env (semanticView ctx.model.dynamics (log.programPrefix count))
          _ (.boolean value) value rfl,
        evalTerm_toProgramExpr]
      change ((nextCount : Int) = (count : Int) ∧
        evalProgramExpr ctx.interpretation (log.programPrefix count).current.visible expression = some value) ↔
        (evalProgramExpr ctx.interpretation (log.programPrefix count).current.visible expression = some value ∧
          semanticView ctx.model.dynamics (log.programPrefix count) =
            semanticView ctx.model.dynamics (log.programPrefix nextCount)) ∧ nextCount = count
      constructor
      · rintro ⟨equal, enabled⟩
        have same : nextCount = count := by omega
        exact ⟨⟨enabled, by rw [same]⟩, same⟩
      · rintro ⟨⟨enabled, _⟩, same⟩
        exact ⟨by rw [same], enabled⟩
  | command primitive =>
      have addEvaluated : evalTerm ctx.interpretation ctx.model env view
          (.intAdd (terms.count index) (.integer 1)) = some (((count + 1 : Nat) : Int)) :=
        eval_nextIndex ctx env view (terms.count index) count (hc view)
      rw [viewModalSatisfaction,
        equal_evaluated_satisfaction ctx env view _ _ (nextCount : Int) ((count + 1 : Nat) : Int)
          (hn view) addEvaluated,
        atView_satisfaction ctx env view _ (log.programPrefix count) _ (hv view) admitted,
        equal_right_satisfaction ctx env (semanticView ctx.model.dynamics (log.programPrefix count))
          _ _ (semanticView ctx.model.dynamics (log.programPrefix nextCount))
          (hnv (semanticView ctx.model.dynamics (log.programPrefix count))),
        primitive_viewEffect_satisfaction]
      constructor
      · rintro ⟨equal, effect⟩
        exact ⟨effect, by
          change nextCount = count + 1
          have equalInt : (nextCount : Int) = ((count + 1 : Nat) : Int) := equal
          exact Int.ofNat.inj equalInt⟩
      · rintro ⟨effect, equal⟩
        exact ⟨by rw [equal], effect⟩

/-- Each expanded edge describes successful typed counters and the complete
local effect, with no requirement that ghost states are literal command states. -/
theorem edge_satisfaction (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (program current : Program) (target : Option Program) (label : ControlLabel)
    (index : AssertionTerm Γ (.value .integer)) (j : Nat)
    (indexDenotes : ∀ view, evalTerm ctx.interpretation ctx.model env view index = some (j : Int))
    (view : SemanticView D) :
    viewModalSatisfaction ctx.interpretation ctx.model env view (edge terms program current target label index) ↔
      log.readCell j .control = some (program.controlCode (some current)) ∧
      log.readCell (j + 1) .control = some (program.controlCode target) ∧
      ∃ count nextCount : Nat,
        count ≤ log.programStates.length ∧ nextCount ≤ log.programStates.length ∧
        log.readCell j .commands = some (count : Int) ∧
        log.readCell (j + 1) .commands = some (nextCount : Int) ∧
        Admitted ctx.model.dynamics (log.programPrefix count) ∧
        Admitted ctx.model.dynamics (log.programPrefix nextCount) ∧
        label.viewEffect ctx (log.programPrefix count) (log.programPrefix nextCount) ∧
        (match label with | .guard _ _ => nextCount = count | .command _ => nextCount = count + 1) := by
  have nextIndex : ∀ v, evalTerm ctx.interpretation ctx.model env v
      (.intAdd index (.integer 1)) = some ((j + 1 : Nat) : Int) :=
    fun v => eval_nextIndex ctx env v index j (indexDenotes v)
  simp only [edge, conjunction_satisfaction, List.forall_mem_cons]
  rw [equal_right_satisfaction ctx env view _ (.integer (program.controlCode (some current))) _ rfl,
    Terms.eval_cell terms ctx env log denotes view index j (indexDenotes view) .control,
    equal_right_satisfaction ctx env view _ (.integer (program.controlCode target)) _ rfl,
    Terms.eval_cell terms ctx env log denotes view _ (j + 1) (nextIndex view) .control]
  constructor
  · rintro ⟨sourceCode, targetCode, lower, upper, nextLower, nextUpper, beforeAdmitted, afterAdmitted, action⟩
    rcases (boundedInteger_satisfaction ctx env view (terms.count index) _ log.programStates.length
      (Terms.eval_programLength terms ctx env log denotes view)).mp ⟨lower, upper⟩ with ⟨count, bound, hc⟩
    rcases (boundedInteger_satisfaction ctx env view (terms.count (.intAdd index (.integer 1))) _
      log.programStates.length (Terms.eval_programLength terms ctx env log denotes view)).mp
        ⟨nextLower, nextUpper⟩ with ⟨nextCount, nextBound, hn⟩
    have countEvaluated : log.readCell j .commands = some (count : Int) :=
      (Terms.eval_count terms ctx env log denotes view index j (indexDenotes view)).symm.trans hc
    have nextEvaluated : log.readCell (j + 1) .commands = some (nextCount : Int) :=
      (Terms.eval_count terms ctx env log denotes view _ (j + 1) (nextIndex view)).symm.trans hn
    have admitted := (admitted_satisfaction ctx env view _ (log.programPrefix count)
      (Terms.eval_programWorld terms ctx env log denotes view index j count
        (indexDenotes view) countEvaluated)).mp beforeAdmitted
    have nextAdmitted := (admitted_satisfaction ctx env view _ (log.programPrefix nextCount)
      (Terms.eval_programWorld terms ctx env log denotes view _ (j + 1) nextCount
        (nextIndex view) nextEvaluated)).mp afterAdmitted
    exact ⟨sourceCode, targetCode, count, nextCount, bound, nextBound, countEvaluated,
      nextEvaluated, admitted, nextAdmitted,
      (label_satisfaction terms ctx env log denotes label index j count nextCount indexDenotes
        countEvaluated nextEvaluated admitted view).mp action.1⟩
  · rintro ⟨sourceCode, targetCode, count, nextCount, bound, nextBound,
      countEvaluated, nextEvaluated, admitted, nextAdmitted, effect, increment⟩
    have hc := (Terms.eval_count terms ctx env log denotes view index j (indexDenotes view)).trans countEvaluated
    have hn := (Terms.eval_count terms ctx env log denotes view _ (j + 1) (nextIndex view)).trans nextEvaluated
    have bounds := (boundedInteger_satisfaction ctx env view (terms.count index) _ log.programStates.length
      (Terms.eval_programLength terms ctx env log denotes view)).mpr ⟨count, bound, hc⟩
    have nextBounds := (boundedInteger_satisfaction ctx env view (terms.count (.intAdd index (.integer 1))) _
      log.programStates.length (Terms.eval_programLength terms ctx env log denotes view)).mpr
        ⟨nextCount, nextBound, hn⟩
    exact ⟨sourceCode, targetCode, bounds.1, bounds.2, nextBounds.1, nextBounds.2,
      (admitted_satisfaction ctx env view _ (log.programPrefix count)
        (Terms.eval_programWorld terms ctx env log denotes view index j count
          (indexDenotes view) countEvaluated)).mpr admitted,
      (admitted_satisfaction ctx env view _ (log.programPrefix nextCount)
        (Terms.eval_programWorld terms ctx env log denotes view _ (j + 1) nextCount
          (nextIndex view) nextEvaluated)).mpr nextAdmitted,
      (label_satisfaction terms ctx env log denotes label index j count nextCount indexDenotes
        countEvaluated nextEvaluated admitted view).mpr ⟨effect, increment⟩, by simp⟩

/-- The finite source/residual graph disjunction has exactly the local-edge
meaning, for arbitrary original ghost contexts and arbitrary ambient views. -/
theorem edges_satisfaction (terms : Terms Γ) (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (log : ControlLog D) (denotes : terms.Denotes ctx env log)
    (program : Program) (index : AssertionTerm Γ (.value .integer)) (j : Nat)
    (indexDenotes : ∀ view, evalTerm ctx.interpretation ctx.model env view index = some (j : Int))
    (view : SemanticView D) :
    viewModalSatisfaction ctx.interpretation ctx.model env view (edges terms program index) ↔
      log.edge ctx program j := by
  rw [edges, disjunction_satisfaction]
  constructor
  · rintro ⟨formula, member, satisfied⟩
    rcases List.mem_flatMap.mp member with ⟨current, residual, member⟩
    rcases List.mem_map.mp member with ⟨⟨target, label⟩, choice, equal⟩
    subst formula
    exact ⟨current, residual, target, label, choice,
      (edge_satisfaction terms ctx env log denotes program current target label index j indexDenotes view).mp satisfied⟩
  · rintro ⟨current, residual, target, label, choice, body⟩
    refine ⟨edge terms program current target label index,
      List.mem_flatMap.mpr ⟨current, residual, List.mem_map.mpr ⟨(target, label), choice, rfl⟩⟩, ?_⟩
    exact (edge_satisfaction terms ctx env log denotes program current target label index j indexDenotes view).mpr body

end
end Lara.BHL.ControlLogSyntax
