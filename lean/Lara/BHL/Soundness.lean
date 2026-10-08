import Lara.BHL.Derivation

namespace Lara.BHL

noncomputable section

variable {D : Type} [MeasurableSpace D] {Γ : List GhostSort}

/-- Successful primitive view evaluation is realized by an actual admitted step. -/
theorem primitive_viewTerm_realized (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) {before : World D Primitive} {primitive : Primitive}
    {view : SemanticView D} (initial : Admitted ctx.model.dynamics before)
    (evaluated : evalTerm ctx.interpretation ctx.model env
      (semanticView ctx.model.dynamics before) (primitive.viewTerm Γ) = some view) :
    ∃ after, Step ctx (some (.command primitive)) before none after ∧
      Admitted ctx.model.dynamics after ∧ semanticView ctx.model.dynamics after = view := by
  rw [evalPrimitive_viewTerm] at evaluated
  cases enabled : primitiveEffect ctx.interpretation primitive before.current.visible with
  | none => simp [semanticView, enabled] at evaluated
  | some output =>
      rcases output with ⟨visible, delta⟩
      have evaluated' :
          some {semanticView ctx.model.dynamics before with
            visible := visible, history := before.current.history + delta} = some view := by
        simpa only [semanticView, enabled, Option.map_some] using evaluated
      let after := before.extend (commandState before.current primitive visible delta)
      have step : Step ctx (some (.command primitive)) before none after := .command enabled
      refine ⟨after, step, step.admitted initial, ?_⟩
      have effect : ∃ d, ctx.model.dynamics.command primitive before.current.visible =
          some ((commandState before.current primitive visible delta).visible, d) ∧
          (commandState before.current primitive visible delta).history =
            before.current.history + d := by
        exact ⟨delta, by simpa only [commandState_visible] using
          (ctx.command_binding primitive before.current.visible).trans enabled, rfl⟩
      rw [command_successor_view ctx.model before _ primitive rfl
        (commandState_hidden _ _ _ _) effect]
      exact Option.some.inj evaluated'

/-- Full optional primitive preimage denotes the actual successor semantic view. -/
theorem primitive_viewTerm_successor (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) {before after : World D Primitive} {primitive : Primitive}
    (step : Step ctx (some (.command primitive)) before none after) :
    evalTerm ctx.interpretation ctx.model env (semanticView ctx.model.dynamics before)
      (primitive.viewTerm Γ) = some (semanticView ctx.model.dynamics after) := by
  cases step with
  | @command primitive world visible delta enabled =>
      have effect : ∃ d, ctx.model.dynamics.command primitive before.current.visible =
          some ((commandState before.current primitive visible delta).visible, d) ∧
          (commandState before.current primitive visible delta).history =
            before.current.history + d := by
        exact ⟨delta, by simpa only [commandState_visible] using
          (ctx.command_binding primitive before.current.visible).trans enabled, rfl⟩
      rw [evalPrimitive_viewTerm, command_successor_view ctx.model before _ primitive rfl
        (commandState_hidden _ _ _ _) effect]
      simp only [semanticView, enabled, Option.map_some, commandState_visible]
      rfl

/-- Public preimage satisfaction iff public post satisfaction on an actual step.
Both sides retain the original arbitrary ghost context and environment. -/
theorem primitive_preimage_successor_iff (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) {before after : World D Primitive} {primitive : Primitive}
    (initial : Admitted ctx.model.dynamics before)
    (step : Step ctx (some (.command primitive)) before none after) (post : Assertion Γ) :
    satisfies ctx.interpretation ctx.model env before (primitive.preimage post) ↔
      satisfies ctx.interpretation ctx.model env after post := by
  rw [satisfies, Primitive.preimage,
    liberalPreimage_successor_iff ctx.interpretation ctx.model env before after
      (step.admitted initial) (primitive.viewTerm Γ) post
      (primitive_viewTerm_successor ctx env step)]
  exact and_iff_right initial

/-- Local primitive correctness precedes the independently inductive proof system. -/
theorem primitive_preimage_valid (ctx : ProgramContext D) (primitive : Primitive)
    (post : Assertion Γ) :
    ValidTriple ctx (primitive.preimage post) (.command primitive) post := by
  intro env before after pre execution
  obtain ⟨visible, delta, enabled, rfl⟩ := run_command_iff.mp execution.2.2
  exact (primitive_preimage_successor_iff ctx env pre.1 (.command enabled) post).mp pre

@[simp] theorem reference_guardAssertion_iff (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (world : World D Primitive)
    (guard : ProgramExpr .boolean) (choice : Bool) :
    referenceAssertionSatisfaction ctx.interpretation ctx.model env world
      (guardAssertion guard choice) ↔
      evalProgramExpr ctx.interpretation world.current.visible guard = some choice := by
  change (∃ value, evalTerm ctx.interpretation ctx.model env
      (semanticView ctx.model.dynamics world) (guard.toAssertionTerm Γ) = some value ∧
      evalTerm ctx.interpretation ctx.model env
        (semanticView ctx.model.dynamics world) (.boolean choice) = some value) ↔ _
  rw [evalTerm_toProgramExpr]
  simp [evalTerm, semanticView]

@[simp] theorem satisfies_guardAssertion_iff (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (world : World D Primitive)
    (guard : ProgramExpr .boolean) (choice : Bool) :
    satisfies ctx.interpretation ctx.model env world (guardAssertion guard choice) ↔
      Admitted ctx.model.dynamics world ∧
        evalProgramExpr ctx.interpretation world.current.visible guard = some choice := by
  simp only [satisfies, reference_guardAssertion_iff]

/-- The printed negative guard agrees with the false branch only when defined. -/
theorem guard_false_defined_negation (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (world : World D Primitive) (guard : ProgramExpr .boolean) :
    referenceAssertionSatisfaction ctx.interpretation ctx.model env world
      (guardAssertion guard false) ↔
      (∃ choice, evalProgramExpr ctx.interpretation world.current.visible guard = some choice) ∧
        ¬ referenceAssertionSatisfaction ctx.interpretation ctx.model env world
          (guardAssertion guard true) := by
  rw [reference_guardAssertion_iff, reference_guardAssertion_iff]
  cases h : evalProgramExpr ctx.interpretation world.current.visible guard with
  | none => simp
  | some choice => cases choice <;> simp

/-- Undefined guards satisfy neither branch assertion. -/
theorem guardAssertion_undefined (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (world : World D Primitive)
    (guard : ProgramExpr .boolean)
    (undefined : evalProgramExpr ctx.interpretation world.current.visible guard = none)
    (choice : Bool) :
    ¬ referenceAssertionSatisfaction ctx.interpretation ctx.model env world
      (guardAssertion guard choice) := by
  rw [reference_guardAssertion_iff, undefined]
  simp

@[simp] theorem satisfies_conj (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (world : World D Primitive) (left right : Assertion Γ) :
    satisfies ctx.interpretation ctx.model env world (.conj left right) ↔
      satisfies ctx.interpretation ctx.model env world left ∧
        satisfies ctx.interpretation ctx.model env world right := by
  simp only [satisfies, referenceAssertionSatisfaction]
  tauto

theorem rule_skip_sound (ctx : ProgramContext D) (pre : Assertion Γ) :
    ValidTriple ctx pre Program.skip pre := by
  intro env before after initial execution
  obtain ⟨visible, delta, enabled, rfl⟩ := run_command_iff.mp execution.2.2
  have step : Step ctx (some Program.skip) before none
      (before.extend (commandState before.current .skip visible delta)) := .command enabled
  have viewed := primitive_viewTerm_successor ctx env step
  have sameView := Option.some.inj (by
    simpa only [Primitive.viewTerm, evalTerm] using viewed)
  exact (satisfies_congr ctx.interpretation ctx.model env initial.1
    (exec_admitted execution) sameView pre).mp initial

theorem rule_assign_sound (ctx : ProgramContext D) (primitive : Primitive)
    (_pure : primitive.IsPureAssignment) (post : Assertion Γ) :
    ValidTriple ctx (primitive.preimage post) (.command primitive) post :=
  primitive_preimage_valid ctx primitive post

theorem rule_test_sound (ctx : ProgramContext D) (result : Variable .real .observable)
    (hypothesis : HypothesisId) (data : DatasetExpr) (testName : TestId)
    (population : PopulationId) (post : Assertion Γ) :
    ValidTriple ctx ((Primitive.test result hypothesis data testName population).preimage post)
      (.command (.test result hypothesis data testName population)) post :=
  primitive_preimage_valid ctx (.test result hypothesis data testName population) post

theorem rule_seq_sound (ctx : ProgramContext D) {pre intermediate post : Assertion Γ}
    {left right : Program} (first : ValidTriple ctx pre left intermediate)
    (second : ValidTriple ctx intermediate right post) :
    ValidTriple ctx pre (.seq left right) post := by
  intro env before after initial execution
  obtain ⟨middle, leftRun, rightRun⟩ := exec_seq_iff.mp execution
  exact second env middle after (first env before middle initial leftRun) rightRun

theorem rule_if_sound (ctx : ProgramContext D) {pre post : Assertion Γ}
    {guard : ProgramExpr .boolean} {left right : Program}
    (yes : ValidTriple ctx (.conj pre (guardAssertion guard true)) left post)
    (no : ValidTriple ctx (.conj pre (guardAssertion guard false)) right post) :
    ValidTriple ctx pre (.ite guard left right) post := by
  intro env before after initial execution
  rcases (exec_ite_iff.mp execution).2.2 with ⟨enabled, run⟩ | ⟨enabled, run⟩
  · exact yes env before after ((satisfies_conj ctx env before _ _).mpr
      ⟨initial, (satisfies_guardAssertion_iff ctx env before guard true).mpr
        ⟨initial.1, enabled⟩⟩) run
  · exact no env before after ((satisfies_conj ctx env before _ _).mpr
      ⟨initial, (satisfies_guardAssertion_iff ctx env before guard false).mpr
        ⟨initial.1, enabled⟩⟩) run

theorem rule_loop_sound (ctx : ProgramContext D) {invariant : Assertion Γ}
    {guard : ProgramExpr .boolean} {body : Program}
    (preserves : ValidTriple ctx (.conj invariant (guardAssertion guard true)) body invariant) :
    ValidTriple ctx invariant (.loop guard body) (.conj invariant (guardAssertion guard false)) := by
  intro env before after initial execution
  obtain ⟨wellFormed, _, iterations⟩ := exec_loop_finite_iterations.mp execution
  have soundIterations : ∀ source target, FiniteLoopIterations ctx guard body source target →
      satisfies ctx.interpretation ctx.model env source invariant →
        satisfies ctx.interpretation ctx.model env target
          (.conj invariant (guardAssertion guard false)) := by
    intro source target finite
    induction finite with
    | done guardFalse =>
        intro satisfied
        exact (satisfies_conj ctx env _ _ _).mpr ⟨satisfied,
          (satisfies_guardAssertion_iff ctx env _ guard false).mpr
            ⟨satisfied.1, guardFalse⟩⟩
    | next guardTrue bodyRun remaining ih =>
        intro satisfied
        apply ih
        apply preserves env _ _ _ ⟨wellFormed, satisfied.1, bodyRun⟩
        exact (satisfies_conj ctx env _ _ _).mpr ⟨satisfied,
          (satisfies_guardAssertion_iff ctx env _ guard true).mpr
            ⟨satisfied.1, guardTrue⟩⟩
  exact soundIterations before after iterations initial

theorem rule_consequence_sound (ctx : ProgramContext D)
    {pre strengthened weakened post : Assertion Γ} {program : Program}
    (initial : AssertionEntails ctx pre strengthened)
    (valid : ValidTriple ctx strengthened program weakened)
    (final : AssertionEntails ctx weakened post) :
    ValidTriple ctx pre program post := by
  intro env before after satisfied execution
  exact final env after (valid env before after (initial env before satisfied) execution)

theorem rule_parallel_sound (ctx : ProgramContext D) {pre post : Assertion Γ}
    {left right : Program} (_noninterfering : Noninterfering left right)
    (sequential : ValidTriple ctx pre (.seq left right) post) :
    ValidTriple ctx pre (.par left right) post := by
  intro env before after initial execution
  obtain ⟨sequentialAfter, run, equivalent⟩ := parallel_assertion_correspondence execution env
  exact (equivalent post).mpr (sequential env before sequentialAfter initial run)

/-- Global partial-correctness soundness by induction on the eight actual rules. -/
theorem derivation_sound {ctx : ProgramContext D} {pre post : Assertion Γ} {program : Program}
    (derivation : Derivation ctx pre program post) : ValidTriple ctx pre program post := by
  induction derivation with
  | skip pre => exact rule_skip_sound ctx pre
  | assign primitive pure post => exact rule_assign_sound ctx primitive pure post
  | seq _ _ first second => exact rule_seq_sound ctx first second
  | ite _ _ yes no => exact rule_if_sound ctx yes no
  | loop _ preserves => exact rule_loop_sound ctx preserves
  | consequence initial _ final valid => exact rule_consequence_sound ctx initial valid final
  | test result hypothesis data testName population post =>
      exact rule_test_sound ctx result hypothesis data testName population post
  | parallel noninterfering _ sequential => exact rule_parallel_sound ctx noninterfering sequential

end
end Lara.BHL
