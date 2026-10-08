import Lara.BHL.Soundness

namespace Lara.BHL

variable {D : Type} [MeasurableSpace D] {Γ : List GhostSort}

noncomputable section

/-- Independent universal outcome meaning. There is no termination obligation
and no syntactic derivation occurs in this definition. -/
def weakestLiberalPrecondition (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (program : Program) (post : Assertion Γ) (before : World D Primitive) : Prop :=
  ∀ after, executes ctx program before after →
    satisfies ctx.interpretation ctx.model env after post

/-- Relative assertion implication concerns the exact fixed model and all rigid
valuations, not a finite truth-table check or an automatic proof-search promise. -/
theorem valid_iff_entails_wlp (ctx : ProgramContext D) (pre post : Assertion Γ)
    (program : Program) :
    ValidTriple ctx pre program post ↔
      ∀ env before, satisfies ctx.interpretation ctx.model env before pre →
        weakestLiberalPrecondition ctx env program post before := by
  constructor
  · intro valid env before satisfied after execution
    exact valid env before after satisfied execution
  · intro entails env before after satisfied execution
    exact entails env before satisfied after execution

theorem wlp_mono {ctx : ProgramContext D} {env : GhostEnv D Primitive Γ}
    {program : Program} {post stronger : Assertion Γ} {before : World D Primitive}
    (entails : AssertionEntails ctx post stronger)
    (outcomes : weakestLiberalPrecondition ctx env program post before) :
    weakestLiberalPrecondition ctx env program stronger before := by
  intro after execution
  exact entails env after (outcomes after execution)

/-- Successful preimages come from actual admitted command steps; undefined
primitive evaluation is liberal, rather than a fabricated successor. -/
theorem wlp_command_iff (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (before : World D Primitive) (initial : Admitted ctx.model.dynamics before)
    (primitive : Primitive) (post : Assertion Γ) :
    weakestLiberalPrecondition ctx env (.command primitive) post before ↔
      satisfies ctx.interpretation ctx.model env before (primitive.preimage post) := by
  constructor
  · intro outcomes
    cases evaluated : evalTerm ctx.interpretation ctx.model env
        (semanticView ctx.model.dynamics before) (primitive.viewTerm Γ) with
    | none =>
        exact ⟨initial, liberalPreimage_undefined ctx.interpretation ctx.model env before
          (primitive.viewTerm Γ) post evaluated⟩
    | some view =>
        obtain ⟨after, step, _, _⟩ := primitive_viewTerm_realized ctx env initial evaluated
        have execution : executes ctx (.command primitive) before after :=
          ⟨True.intro, initial, Run.single step⟩
        exact (primitive_preimage_successor_iff ctx env initial step post).mpr
          (outcomes after execution)
  · intro satisfied after execution
    exact primitive_preimage_valid ctx primitive post env before after satisfied execution

theorem wlp_skip_iff (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (before : World D Primitive) (initial : Admitted ctx.model.dynamics before)
    (post : Assertion Γ) :
    weakestLiberalPrecondition ctx env Program.skip post before ↔
      satisfies ctx.interpretation ctx.model env before post := by
  constructor
  · intro outcomes
    have pre := (wlp_command_iff ctx env before initial .skip post).mp outcomes
    have reference := pre.2
    change referenceAssertionSatisfaction ctx.interpretation ctx.model env before
      (liberalPreimage .ambient post) at reference
    exact (liberalPreimage_successor_iff ctx.interpretation ctx.model env before before
      initial .ambient post rfl).mp reference
  · intro satisfied after execution
    exact rule_skip_sound ctx post env before after satisfied execution

theorem wlp_seq_iff (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (before : World D Primitive) (left right : Program) (post : Assertion Γ) :
    weakestLiberalPrecondition ctx env (.seq left right) post before ↔
      ∀ middle, executes ctx left before middle →
        weakestLiberalPrecondition ctx env right post middle := by
  constructor
  · intro outcomes middle first after second
    exact outcomes after (exec_seq_iff.mpr ⟨middle, first, second⟩)
  · intro outcomes after execution
    obtain ⟨middle, first, second⟩ := exec_seq_iff.mp execution
    exact outcomes middle first after second

/-- Both branches remain defined-value obligations. A missing guard does not
become the false branch by taking a logical negation. -/
theorem wlp_ite_iff (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (before : World D Primitive) (guard : ProgramExpr .boolean) (left right : Program)
    (post : Assertion Γ) (leftLegal : left.WellFormed) (rightLegal : right.WellFormed) :
    weakestLiberalPrecondition ctx env (.ite guard left right) post before ↔
      (evalProgramExpr ctx.interpretation before.current.visible guard = some true →
        weakestLiberalPrecondition ctx env left post before) ∧
      (evalProgramExpr ctx.interpretation before.current.visible guard = some false →
        weakestLiberalPrecondition ctx env right post before) := by
  constructor
  · intro outcomes
    constructor
    · intro enabled after execution
      exact outcomes after (exec_ite_iff.mpr ⟨leftLegal, rightLegal, Or.inl ⟨enabled, execution⟩⟩)
    · intro enabled after execution
      exact outcomes after (exec_ite_iff.mpr ⟨leftLegal, rightLegal, Or.inr ⟨enabled, execution⟩⟩)
  · rintro ⟨yes, no⟩ after execution
    rcases (exec_ite_iff.mp execution).2.2 with ⟨enabled, chosen⟩ | ⟨enabled, chosen⟩
    · exact yes enabled after chosen
    · exact no enabled after chosen

theorem wlp_ite_undefined (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (before : World D Primitive) (guard : ProgramExpr .boolean) (left right : Program)
    (post : Assertion Γ)
    (undefined : evalProgramExpr ctx.interpretation before.current.visible guard = none) :
    weakestLiberalPrecondition ctx env (.ite guard left right) post before := by
  intro after execution
  rcases (exec_ite_iff.mp execution).2.2 with ⟨enabled, _⟩ | ⟨enabled, _⟩ <;>
    rw [undefined] at enabled <;> cases enabled

/-- The loop outcome transformer is a realizable invariant: a true guard and an
actual body run leave every terminating continuation subject to the same post. -/
theorem wlp_loop_body {ctx : ProgramContext D} {env : GhostEnv D Primitive Γ}
    {before : World D Primitive} {guard : ProgramExpr .boolean} {body : Program}
    {post : Assertion Γ}
    (enabled : evalProgramExpr ctx.interpretation before.current.visible guard = some true)
    (outcomes : weakestLiberalPrecondition ctx env (.loop guard body) post before) :
    ∀ middle, executes ctx body before middle →
      weakestLiberalPrecondition ctx env (.loop guard body) post middle := by
  intro middle first after continuation
  exact outcomes after (exec_loop_unfold_iff.mpr
    ⟨first.1, first.2.1, Or.inr ⟨enabled, middle, first, continuation⟩⟩)

theorem wlp_loop_exit (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (before : World D Primitive) (guard : ProgramExpr .boolean) (body : Program)
    (post : Assertion Γ) (legal : body.WellFormed)
    (initial : Admitted ctx.model.dynamics before)
    (enabled : evalProgramExpr ctx.interpretation before.current.visible guard = some false)
    (outcomes : weakestLiberalPrecondition ctx env (.loop guard body) post before) :
    satisfies ctx.interpretation ctx.model env before post :=
  outcomes before (exec_loop_unfold_iff.mpr ⟨legal, initial, Or.inl ⟨enabled, rfl⟩⟩)

theorem wlp_loop_undefined (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (before : World D Primitive) (guard : ProgramExpr .boolean) (body : Program)
    (post : Assertion Γ)
    (undefined : evalProgramExpr ctx.interpretation before.current.visible guard = none) :
    weakestLiberalPrecondition ctx env (.loop guard body) post before := by
  intro after execution
  rcases (exec_loop_unfold_iff.mp execution).2.2 with ⟨enabled, _⟩ | ⟨enabled, _⟩ <;>
    rw [undefined] at enabled <;> cases enabled

/-- Noninterference gives universal post-outcome equivalence, not only equality
of one selected schedule or of visible stores. Arbitrary legal postconditions
and their unchanged rigid environments are retained. -/
theorem wlp_parallel_iff (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (before : World D Primitive) (left right : Program) (post : Assertion Γ)
    (noninterfering : Noninterfering left right) :
    weakestLiberalPrecondition ctx env (.par left right) post before ↔
      weakestLiberalPrecondition ctx env (.seq left right) post before := by
  constructor
  · intro outcomes after execution
    exact outcomes after (exec_seq_to_parallel noninterfering execution)
  · intro outcomes after execution
    obtain ⟨sequentialAfter, sequential, equivalent⟩ :=
      parallel_assertion_correspondence execution env
    exact (equivalent post).mpr (outcomes sequentialAfter sequential)

/-- A perpetually true guard has no terminating iteration witness, regardless
of what its body does. Its liberal precondition therefore holds for any post. -/
theorem wlp_true_loop (ctx : ProgramContext D) (env : GhostEnv D Primitive Γ)
    (before : World D Primitive) (body : Program) (post : Assertion Γ) :
    weakestLiberalPrecondition ctx env (.loop (.boolean true) body) post before := by
  intro after execution
  have finite := (exec_loop_finite_iterations.mp execution).2.2
  clear execution
  induction finite with
  | done guardFalse => simp [evalProgramExpr] at guardFalse
  | next _ _ _ ih => exact ih

end
end Lara.BHL
