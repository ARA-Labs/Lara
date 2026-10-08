import Lara.BHL.Execution

namespace Lara.BHL

variable {D : Type} [MeasurableSpace D]

noncomputable section

/-- A terminating source run, without the public well-formedness or admission gates. -/
abbrev RawRun (context : ProgramContext D) (program : Program)
    (before after : World D Primitive) : Prop :=
  Run context (some program) before none after

namespace Step

theorem command_iff {context : ProgramContext D} {primitive target before after} :
    Step context (some (.command primitive)) before target after ↔
      ∃ visible delta, primitiveEffect context.interpretation primitive before.current.visible =
        some (visible, delta) ∧ target = none ∧
        after = before.extend (commandState before.current primitive visible delta) := by
  constructor
  · intro step
    cases step with
    | command enabled => exact ⟨_, _, enabled, rfl, rfl⟩
  · rintro ⟨visible, delta, enabled, rfl, rfl⟩
    exact .command enabled

theorem seq_iff {context : ProgramContext D} {left right target before after} :
    Step context (some (.seq left right)) before target after ↔
      (∃ next, Step context (some left) before (some next) after ∧
        target = some (.seq next right)) ∨
      (Step context (some left) before none after ∧ target = some right) := by
  constructor
  · intro step
    cases step with
    | seqContinue child => exact Or.inl ⟨_, child, rfl⟩
    | seqFinish child => exact Or.inr ⟨child, rfl⟩
  · rintro (⟨next, child, rfl⟩ | ⟨child, rfl⟩)
    · exact .seqContinue child
    · exact .seqFinish child

theorem ite_iff {context : ProgramContext D} {guard left right target before after} :
    Step context (some (.ite guard left right)) before target after ↔
      after = before ∧
      ((evalProgramExpr context.interpretation before.current.visible guard = some true ∧
        target = some left) ∨
       (evalProgramExpr context.interpretation before.current.visible guard = some false ∧
        target = some right)) := by
  constructor
  · intro step
    cases step with
    | ifTrue enabled => exact ⟨rfl, Or.inl ⟨enabled, rfl⟩⟩
    | ifFalse enabled => exact ⟨rfl, Or.inr ⟨enabled, rfl⟩⟩
  · rintro ⟨rfl, (⟨enabled, rfl⟩ | ⟨enabled, rfl⟩)⟩
    · exact .ifTrue enabled
    · exact .ifFalse enabled

theorem loop_iff {context : ProgramContext D} {guard body target before after} :
    Step context (some (.loop guard body)) before target after ↔
      after = before ∧
      ((evalProgramExpr context.interpretation before.current.visible guard = some true ∧
        target = some (.seq body (.loop guard body))) ∨
       (evalProgramExpr context.interpretation before.current.visible guard = some false ∧
        target = none)) := by
  constructor
  · intro step
    cases step with
    | loopTrue enabled => exact ⟨rfl, Or.inl ⟨enabled, rfl⟩⟩
    | loopFalse enabled => exact ⟨rfl, Or.inr ⟨enabled, rfl⟩⟩
  · rintro ⟨rfl, (⟨enabled, rfl⟩ | ⟨enabled, rfl⟩)⟩
    · exact .loopTrue enabled
    · exact .loopFalse enabled

theorem par_iff {context : ProgramContext D} {left right target before after} :
    Step context (some (.par left right)) before target after ↔
      (∃ next, Step context (some left) before (some next) after ∧
        target = some (.par next right)) ∨
      (Step context (some left) before none after ∧ target = some right) ∨
      (∃ next, Step context (some right) before (some next) after ∧
        target = some (.par left next)) ∨
      (Step context (some right) before none after ∧ target = some left) := by
  constructor
  · intro step
    cases step with
    | parLeftContinue child => exact Or.inl ⟨_, child, rfl⟩
    | parLeftFinish child => exact Or.inr (Or.inl ⟨child, rfl⟩)
    | parRightContinue child => exact Or.inr (Or.inr (Or.inl ⟨_, child, rfl⟩))
    | parRightFinish child => exact Or.inr (Or.inr (Or.inr ⟨child, rfl⟩))
  · rintro (⟨next, child, rfl⟩ | ⟨child, rfl⟩ | ⟨next, child, rfl⟩ | ⟨child, rfl⟩)
    · exact .parLeftContinue child
    · exact .parLeftFinish child
    · exact .parRightContinue child
    · exact .parRightFinish child

end Step

/-- A completed child disappears on its final step, leaving the other source. -/
def seqResidual (right : Program) : Option Program → Option Program
  | none => some right
  | some left => some (.seq left right)

def parLeftResidual (right : Program) : Option Program → Option Program
  | none => some right
  | some left => some (.par left right)

def parRightResidual (left : Program) : Option Program → Option Program
  | none => some left
  | some right => some (.par left right)

namespace Step

theorem seq_lift {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) (right : Program) :
    Step context (seqResidual right source) before (seqResidual right target) after := by
  obtain ⟨left, rfl⟩ := step.source_some
  cases target with
  | none => exact .seqFinish step
  | some next => exact .seqContinue step

theorem par_left_lift {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) (right : Program) :
    Step context (parLeftResidual right source) before (parLeftResidual right target) after := by
  obtain ⟨left, rfl⟩ := step.source_some
  cases target with
  | none => exact .parLeftFinish step
  | some next => exact .parLeftContinue step

theorem par_right_lift {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) (left : Program) :
    Step context (parRightResidual left source) before (parRightResidual left target) after := by
  obtain ⟨right, rfl⟩ := step.source_some
  cases target with
  | none => exact .parRightFinish step
  | some next => exact .parRightContinue step

end Step

namespace Steps

theorem trans {context : ProgramContext D} {m n source middle target before intermediate after}
    (first : Steps context m source before middle intermediate)
    (second : Steps context n middle intermediate target after) :
    Steps context (m + n) source before target after := by
  induction first generalizing n target after with
  | refl => simpa using second
  | cons step rest ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Steps.cons step (ih second)

theorem one_iff {context : ProgramContext D} {source target before after} :
    Steps context 1 source before target after ↔ Step context source before target after := by
  constructor
  · intro steps
    cases steps with
    | cons first rest =>
        cases rest
        exact first
  · intro step
    exact .cons step (.refl _ _)

theorem succ_iff {context : ProgramContext D} {n source target before after} :
    Steps context (n + 1) source before target after ↔
      ∃ middle intermediate, Step context source before middle intermediate ∧
        Steps context n middle intermediate target after := by
  constructor
  · intro steps
    cases steps with
    | cons first rest => exact ⟨_, _, first, rest⟩
  · rintro ⟨middle, intermediate, first, rest⟩
    exact .cons first rest

theorem seq_lift {context : ProgramContext D} {n source target before after}
    (steps : Steps context n source before target after) (right : Program) :
    Steps context n (seqResidual right source) before (seqResidual right target) after := by
  induction steps with
  | refl => exact .refl _ _
  | cons first rest ih => exact .cons (first.seq_lift right) ih

theorem par_left_lift {context : ProgramContext D} {n source target before after}
    (steps : Steps context n source before target after) (right : Program) :
    Steps context n (parLeftResidual right source) before (parLeftResidual right target) after := by
  induction steps with
  | refl => exact .refl _ _
  | cons first rest ih => exact .cons (first.par_left_lift right) ih

theorem par_right_lift {context : ProgramContext D} {n source target before after}
    (steps : Steps context n source before target after) (left : Program) :
    Steps context n (parRightResidual left source) before (parRightResidual left target) after := by
  induction steps with
  | refl => exact .refl _ _
  | cons first rest ih => exact .cons (first.par_right_lift left) ih

theorem command_iff {context : ProgramContext D} {n primitive before after} :
    Steps context n (some (.command primitive)) before none after ↔
      n = 1 ∧ ∃ visible delta,
        primitiveEffect context.interpretation primitive before.current.visible =
          some (visible, delta) ∧
        after = before.extend (commandState before.current primitive visible delta) := by
  constructor
  · intro steps
    cases steps with
    | cons first rest =>
        obtain ⟨visible, delta, enabled, rfl, rfl⟩ := Step.command_iff.mp first
        obtain ⟨rfl, _, rfl⟩ := Steps.terminal_iff.mp rest
        exact ⟨rfl, visible, delta, enabled, rfl⟩
  · rintro ⟨rfl, visible, delta, enabled, rfl⟩
    exact .cons (.command enabled) (.refl _ _)

theorem seq_iff {context : ProgramContext D} {n left right before after} :
    Steps context n (some (.seq left right)) before none after ↔
      ∃ m k intermediate, n = m + k ∧
        Steps context m (some left) before none intermediate ∧
        Steps context k (some right) intermediate none after := by
  induction n using Nat.strong_induction_on generalizing left before with
  | h n ih =>
      constructor
      · intro steps
        cases steps with
        | @cons count source middle target before intermediate after first rest =>
            rcases Step.seq_iff.mp first with ⟨next, child, rfl⟩ | ⟨child, rfl⟩
            · obtain ⟨m, k, boundary, hcount, leftRun, rightRun⟩ :=
                (ih count (by omega)).mp rest
              exact ⟨m + 1, k, boundary, by omega, .cons child leftRun, rightRun⟩
            · exact ⟨1, count, intermediate, by omega,
                .cons child (.refl _ _), rest⟩
      · rintro ⟨m, k, intermediate, rfl, leftRun, rightRun⟩
        exact (leftRun.seq_lift right).trans rightRun

theorem seq_to_parallel {context : ProgramContext D} {n left right before after}
    (steps : Steps context n (some (.seq left right)) before none after) :
    Steps context n (some (.par left right)) before none after := by
  obtain ⟨m, k, intermediate, rfl, leftRun, rightRun⟩ := seq_iff.mp steps
  exact (leftRun.par_left_lift right).trans rightRun

end Steps

namespace Run

theorem single {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) : Run context source before target after :=
  ⟨1, .cons step (.refl _ _)⟩

theorem trans {context : ProgramContext D} {source middle target before intermediate after}
    (first : Run context source before middle intermediate)
    (second : Run context middle intermediate target after) :
    Run context source before target after := by
  obtain ⟨m, first⟩ := first
  obtain ⟨n, second⟩ := second
  exact ⟨m + n, first.trans second⟩

theorem first_iff {context : ProgramContext D} {program before after} :
    RawRun context program before after ↔
      ∃ target intermediate, Step context (some program) before target intermediate ∧
        Run context target intermediate none after := by
  constructor
  · rintro ⟨n, steps⟩
    cases steps with
    | cons first rest => exact ⟨_, _, first, _, rest⟩
  · rintro ⟨target, intermediate, first, n, rest⟩
    exact ⟨n + 1, .cons first rest⟩

theorem seq_lift {context : ProgramContext D} {source target before after}
    (run : Run context source before target after) (right : Program) :
    Run context (seqResidual right source) before (seqResidual right target) after := by
  obtain ⟨n, steps⟩ := run
  exact ⟨n, steps.seq_lift right⟩

theorem par_left_lift {context : ProgramContext D} {source target before after}
    (run : Run context source before target after) (right : Program) :
    Run context (parLeftResidual right source) before (parLeftResidual right target) after := by
  obtain ⟨n, steps⟩ := run
  exact ⟨n, steps.par_left_lift right⟩

theorem par_right_lift {context : ProgramContext D} {source target before after}
    (run : Run context source before target after) (left : Program) :
    Run context (parRightResidual left source) before (parRightResidual left target) after := by
  obtain ⟨n, steps⟩ := run
  exact ⟨n, steps.par_right_lift left⟩

end Run

theorem step_command_iff {context : ProgramContext D} {primitive target before after} :
    Step context (some (.command primitive)) before target after ↔
      ∃ visible delta, primitiveEffect context.interpretation primitive before.current.visible =
        some (visible, delta) ∧ target = none ∧
        after = before.extend (commandState before.current primitive visible delta) :=
  Step.command_iff

theorem run_command_iff {context : ProgramContext D} {primitive before after} :
    RawRun context (.command primitive) before after ↔
      ∃ visible delta, primitiveEffect context.interpretation primitive before.current.visible =
        some (visible, delta) ∧
        after = before.extend (commandState before.current primitive visible delta) := by
  constructor
  · rintro ⟨n, steps⟩
    exact (Steps.command_iff.mp steps).2
  · rintro ⟨visible, delta, enabled, rfl⟩
    exact Run.single (.command enabled)

theorem steps_skip_iff {context : ProgramContext D} {n before after} :
    Steps context n (some Program.skip) before none after ↔
      n = 1 ∧ after = before.extend
        (commandState before.current .skip before.current.visible 0) := by
  simp [Program.skip, Steps.command_iff, primitiveEffect, evalPrimitive, VisibleWrite.apply]

theorem run_skip_iff {context : ProgramContext D} {before after} :
    RawRun context Program.skip before after ↔
      after = before.extend (commandState before.current .skip before.current.visible 0) := by
  simp [RawRun, Run, steps_skip_iff]

theorem exec_skip_iff {context : ProgramContext D} {before after} :
    executes context Program.skip before after ↔
      Program.skip.WellFormed ∧ Admitted context.model.dynamics before ∧
        after = before.extend (commandState before.current .skip before.current.visible 0) := by
  change _ ∧ _ ∧ RawRun context Program.skip before after ↔ _
  rw [run_skip_iff]

theorem run_seq_iff {context : ProgramContext D} {left right before after} :
    RawRun context (.seq left right) before after ↔
      ∃ intermediate, RawRun context left before intermediate ∧
        RawRun context right intermediate after := by
  constructor
  · rintro ⟨n, steps⟩
    obtain ⟨m, k, intermediate, _, leftRun, rightRun⟩ := Steps.seq_iff.mp steps
    exact ⟨intermediate, ⟨m, leftRun⟩, ⟨k, rightRun⟩⟩
  · rintro ⟨intermediate, leftRun, rightRun⟩
    exact (leftRun.seq_lift right).trans rightRun

theorem run_ite_iff {context : ProgramContext D} {guard left right before after} :
    RawRun context (.ite guard left right) before after ↔
      (evalProgramExpr context.interpretation before.current.visible guard = some true ∧
        RawRun context left before after) ∨
      (evalProgramExpr context.interpretation before.current.visible guard = some false ∧
        RawRun context right before after) := by
  rw [Run.first_iff]
  constructor
  · rintro ⟨target, intermediate, first, rest⟩
    obtain ⟨rfl, alternatives⟩ := Step.ite_iff.mp first
    rcases alternatives with ⟨enabled, rfl⟩ | ⟨enabled, rfl⟩
    · exact Or.inl ⟨enabled, rest⟩
    · exact Or.inr ⟨enabled, rest⟩
  · rintro (⟨enabled, rest⟩ | ⟨enabled, rest⟩)
    · exact ⟨_, _, .ifTrue enabled, rest⟩
    · exact ⟨_, _, .ifFalse enabled, rest⟩

theorem run_ite_undefined {context : ProgramContext D} {guard left right before after}
    (undefined : evalProgramExpr context.interpretation before.current.visible guard = none) :
    ¬ RawRun context (.ite guard left right) before after := by
  simp [run_ite_iff, undefined]

theorem run_loop_unfold_iff {context : ProgramContext D} {guard body before after} :
    RawRun context (.loop guard body) before after ↔
      (evalProgramExpr context.interpretation before.current.visible guard = some false ∧
        after = before) ∨
      (evalProgramExpr context.interpretation before.current.visible guard = some true ∧
        ∃ intermediate, RawRun context body before intermediate ∧
          RawRun context (.loop guard body) intermediate after) := by
  rw [Run.first_iff]
  constructor
  · rintro ⟨target, intermediate, first, rest⟩
    obtain ⟨rfl, alternatives⟩ := Step.loop_iff.mp first
    rcases alternatives with ⟨enabled, rfl⟩ | ⟨enabled, rfl⟩
    · exact Or.inr ⟨enabled, run_seq_iff.mp rest⟩
    · exact Or.inl ⟨enabled, (Run.terminal_iff.mp rest).2.symm⟩
  · rintro (⟨enabled, rfl⟩ | ⟨enabled, runs⟩)
    · exact ⟨none, _, .loopFalse enabled, Run.refl _ _ _⟩
    · exact ⟨_, before, .loopTrue enabled, run_seq_iff.mpr runs⟩

/-- Finitely many actual body runs, with every guard evaluated in its actual world.
A body run may contain arbitrary legal parallel interleavings. -/
inductive FiniteLoopIterations (context : ProgramContext D)
    (guard : ProgramExpr .boolean) (body : Program) :
    World D Primitive → World D Primitive → Prop where
  | done {world}
      (guardFalse : evalProgramExpr context.interpretation world.current.visible guard = some false) :
      FiniteLoopIterations context guard body world world
  | next {before intermediate after}
      (guardTrue : evalProgramExpr context.interpretation before.current.visible guard = some true)
      (bodyRun : RawRun context body before intermediate)
      (remaining : FiniteLoopIterations context guard body intermediate after) :
      FiniteLoopIterations context guard body before after

namespace Steps

theorem loop_finite_iterations {context : ProgramContext D} {n guard body before after}
    (steps : Steps context n (some (.loop guard body)) before none after) :
    FiniteLoopIterations context guard body before after := by
  induction n using Nat.strong_induction_on generalizing before with
  | h n ih =>
      cases steps with
      | @cons count source middle target before intermediate after first rest =>
          obtain ⟨rfl, alternatives⟩ := Step.loop_iff.mp first
          rcases alternatives with ⟨enabled, rfl⟩ | ⟨enabled, rfl⟩
          · obtain ⟨m, k, boundary, hcount, bodySteps, loopSteps⟩ := Steps.seq_iff.mp rest
            exact .next enabled ⟨m, bodySteps⟩ (ih k (by omega) loopSteps)
          · obtain ⟨_, _, rfl⟩ := Steps.terminal_iff.mp rest
            exact .done enabled

end Steps

namespace FiniteLoopIterations

theorem run {context : ProgramContext D} {guard body before after}
    (iterations : FiniteLoopIterations context guard body before after) :
    RawRun context (.loop guard body) before after := by
  induction iterations with
  | done guardFalse => exact Run.single (.loopFalse guardFalse)
  | next guardTrue bodyRun remaining ih =>
      exact (Run.single (.loopTrue guardTrue)).trans
        (run_seq_iff.mpr ⟨_, bodyRun, ih⟩)

end FiniteLoopIterations

theorem run_loop_finite_iterations_iff {context : ProgramContext D} {guard body before after} :
    RawRun context (.loop guard body) before after ↔
      FiniteLoopIterations context guard body before after := by
  constructor
  · rintro ⟨n, steps⟩
    exact steps.loop_finite_iterations
  · exact FiniteLoopIterations.run

theorem exec_loop_finite_iterations {context : ProgramContext D} {guard body before after} :
    executes context (.loop guard body) before after ↔
      body.WellFormed ∧ Admitted context.model.dynamics before ∧
        FiniteLoopIterations context guard body before after := by
  change body.WellFormed ∧ Admitted context.model.dynamics before ∧
      RawRun context (.loop guard body) before after ↔ _
  rw [run_loop_finite_iterations_iff]

theorem primitiveEffect_delta_shape {context : ProgramContext D} {primitive visible after delta}
    (enabled : primitiveEffect context.interpretation primitive visible = some (after, delta)) :
    delta = 0 ∨ ∃ data test, delta = {(data, test)} := by
  cases primitive with
  | skip =>
      simp only [primitiveEffect, evalPrimitive, Option.map_some, VisibleWrite.apply,
        Option.some.injEq, Prod.mk.injEq] at enabled
      exact Or.inl enabled.2.symm
  | assign x rhs =>
      cases evaluated : evalProgramExpr context.interpretation visible rhs with
      | none => simp [primitiveEffect, evalPrimitive, evaluated] at enabled
      | some value =>
          simp only [primitiveEffect, evalPrimitive, evaluated, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at enabled
          exact Or.inl enabled.2.symm
  | assignDataset name rhs =>
      cases evaluated : evalDatasetExpr context.interpretation visible rhs with
      | none => simp [primitiveEffect, evalPrimitive, evaluated] at enabled
      | some data =>
          simp only [primitiveEffect, evalPrimitive, evaluated, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at enabled
          exact Or.inl enabled.2.symm
  | test result hypothesis expression test population =>
      cases evaluated : evalDatasetExpr context.interpretation visible expression with
      | none => simp [primitiveEffect, evalPrimitive, evaluated] at enabled
      | some data =>
          simp only [primitiveEffect, evalPrimitive, evaluated, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at enabled
          exact Or.inr ⟨data, test, enabled.2.symm⟩

theorem primitiveEffect_pure_delta {context : ProgramContext D} {primitive visible after delta}
    (pure : ∀ result hypothesis data test population,
      primitive ≠ .test result hypothesis data test population)
    (enabled : primitiveEffect context.interpretation primitive visible = some (after, delta)) :
    delta = 0 := by
  cases primitive with
  | skip =>
      simp only [primitiveEffect, evalPrimitive, Option.map_some, VisibleWrite.apply,
        Option.some.injEq, Prod.mk.injEq] at enabled
      exact enabled.2.symm
  | assign x rhs =>
      cases evaluated : evalProgramExpr context.interpretation visible rhs with
      | none => simp [primitiveEffect, evalPrimitive, evaluated] at enabled
      | some value =>
          simp only [primitiveEffect, evalPrimitive, evaluated, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at enabled
          exact enabled.2.symm
  | assignDataset name rhs =>
      cases evaluated : evalDatasetExpr context.interpretation visible rhs with
      | none => simp [primitiveEffect, evalPrimitive, evaluated] at enabled
      | some data =>
          simp only [primitiveEffect, evalPrimitive, evaluated, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at enabled
          exact enabled.2.symm
  | test result hypothesis data test population =>
      exact False.elim (pure result hypothesis data test population rfl)

namespace Step

/-- Every source step is a silent identity or one actual visible command extension. -/
theorem actual_effect {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) :
    after = before ∨ ∃ primitive visible delta,
      primitiveEffect context.interpretation primitive before.current.visible =
        some (visible, delta) ∧
      after = before.extend (commandState before.current primitive visible delta) := by
  induction step with
  | command enabled => exact Or.inr ⟨_, _, _, enabled, rfl⟩
  | seqContinue child ih => exact ih
  | seqFinish child ih => exact ih
  | ifTrue enabled => exact Or.inl rfl
  | ifFalse enabled => exact Or.inl rfl
  | loopTrue enabled => exact Or.inl rfl
  | loopFalse enabled => exact Or.inl rfl
  | parLeftContinue child ih => exact ih
  | parLeftFinish child ih => exact ih
  | parRightContinue child ih => exact ih
  | parRightFinish child ih => exact ih

theorem admitted {context : ProgramContext D} {source target before after}
    (step : Step context source before target after)
    (initial : Admitted context.model.dynamics before) :
    Admitted context.model.dynamics after := by
  rcases step.actual_effect with rfl | ⟨primitive, visible, delta, enabled, rfl⟩
  · exact initial
  · apply command_successor_admitted context.model initial _ primitive rfl
      (commandState_hidden _ _ _ _)
    exact ⟨delta, by simpa only [commandState_visible] using
      (context.command_binding primitive before.current.visible).trans enabled, rfl⟩

theorem information {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) :
    after.current.memory.hidden = before.current.memory.hidden ∧
      compatibleHidden context.model.dynamics after =
        compatibleHidden context.model.dynamics before ∧
      after.samplingProvenance = before.samplingProvenance ∧
      before.trace <+: after.trace := by
  rcases step.actual_effect with rfl | ⟨primitive, visible, delta, enabled, rfl⟩
  · exact ⟨rfl, rfl, rfl, ⟨[], by simp⟩⟩
  · refine ⟨by simp, ?_, ?_, World.extend_prefix _ _⟩
    · apply compatibleHidden_extend_command context.model.dynamics _ _ primitive rfl
      exact ⟨delta, by simpa only [commandState_visible] using
        (context.command_binding primitive before.current.visible).trans enabled, rfl⟩
    · exact World.samplingProvenance_extend_command _ _ primitive rfl

theorem hidden {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) :
    after.current.memory.hidden = before.current.memory.hidden :=
  step.information.1

theorem compatible_hidden {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) :
    compatibleHidden context.model.dynamics after = compatibleHidden context.model.dynamics before :=
  step.information.2.1

theorem sampling_provenance {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) :
    after.samplingProvenance = before.samplingProvenance :=
  step.information.2.2.1

theorem trace_prefix {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) : before.trace <+: after.trace :=
  step.information.2.2.2

theorem ledger_delta {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) :
    ∃ delta : History D, after.current.history = before.current.history + delta ∧
      (delta = 0 ∨ ∃ data test, delta = {(data, test)}) := by
  rcases step.actual_effect with rfl | ⟨primitive, visible, delta, enabled, rfl⟩
  · exact ⟨0, by simp, Or.inl rfl⟩
  · exact ⟨delta, by simp [commandState], primitiveEffect_delta_shape enabled⟩

end Step

namespace Steps

theorem admitted {context : ProgramContext D} {n source target before after}
    (steps : Steps context n source before target after)
    (initial : Admitted context.model.dynamics before) :
    Admitted context.model.dynamics after := by
  revert initial
  induction steps with
  | refl => exact id
  | cons first rest ih =>
      intro initial
      exact ih (first.admitted initial)

theorem information {context : ProgramContext D} {n source target before after}
    (steps : Steps context n source before target after) :
    after.current.memory.hidden = before.current.memory.hidden ∧
      compatibleHidden context.model.dynamics after =
        compatibleHidden context.model.dynamics before ∧
      after.samplingProvenance = before.samplingProvenance ∧
      before.trace <+: after.trace := by
  induction steps with
  | refl => exact ⟨rfl, rfl, rfl, ⟨[], by simp⟩⟩
  | cons first rest ih =>
      exact ⟨ih.1.trans first.hidden, ih.2.1.trans first.compatible_hidden,
        ih.2.2.1.trans first.sampling_provenance, first.trace_prefix.trans ih.2.2.2⟩

theorem ledger_delta {context : ProgramContext D} {n source target before after}
    (steps : Steps context n source before target after) :
    ∃ delta : History D, after.current.history = before.current.history + delta := by
  induction steps with
  | refl => exact ⟨0, by simp⟩
  | cons first rest ih =>
      obtain ⟨firstDelta, firstHistory, _⟩ := first.ledger_delta
      obtain ⟨restDelta, restHistory⟩ := ih
      exact ⟨firstDelta + restDelta, by rw [restHistory, firstHistory, add_assoc]⟩

end Steps

namespace Run

theorem admitted {context : ProgramContext D} {source target before after}
    (run : Run context source before target after)
    (initial : Admitted context.model.dynamics before) :
    Admitted context.model.dynamics after := by
  obtain ⟨n, steps⟩ := run
  exact steps.admitted initial

theorem information {context : ProgramContext D} {source target before after}
    (run : Run context source before target after) :
    after.current.memory.hidden = before.current.memory.hidden ∧
      compatibleHidden context.model.dynamics after =
        compatibleHidden context.model.dynamics before ∧
      after.samplingProvenance = before.samplingProvenance ∧
      before.trace <+: after.trace := by
  obtain ⟨n, steps⟩ := run
  exact steps.information

theorem hidden {context : ProgramContext D} {source target before after}
    (run : Run context source before target after) :
    after.current.memory.hidden = before.current.memory.hidden :=
  run.information.1

theorem compatible_hidden {context : ProgramContext D} {source target before after}
    (run : Run context source before target after) :
    compatibleHidden context.model.dynamics after = compatibleHidden context.model.dynamics before :=
  run.information.2.1

theorem sampling_provenance {context : ProgramContext D} {source target before after}
    (run : Run context source before target after) :
    after.samplingProvenance = before.samplingProvenance :=
  run.information.2.2.1

theorem trace_prefix {context : ProgramContext D} {source target before after}
    (run : Run context source before target after) : before.trace <+: after.trace :=
  run.information.2.2.2

theorem ledger_delta {context : ProgramContext D} {source target before after}
    (run : Run context source before target after) :
    ∃ delta : History D, after.current.history = before.current.history + delta := by
  obtain ⟨n, steps⟩ := run
  exact steps.ledger_delta

end Run

theorem exec_admitted {context : ProgramContext D} {program before after}
    (execution : executes context program before after) :
    Admitted context.model.dynamics after :=
  execution.2.2.admitted execution.2.1

theorem exec_seq_iff {context : ProgramContext D} {left right before after} :
    executes context (.seq left right) before after ↔
      ∃ intermediate, executes context left before intermediate ∧
        executes context right intermediate after := by
  constructor
  · rintro ⟨⟨leftWellFormed, rightWellFormed⟩, initial, run⟩
    obtain ⟨intermediate, leftRun, rightRun⟩ := run_seq_iff.mp run
    exact ⟨intermediate, ⟨leftWellFormed, initial, leftRun⟩,
      ⟨rightWellFormed, leftRun.admitted initial, rightRun⟩⟩
  · rintro ⟨intermediate, leftExecution, rightExecution⟩
    exact ⟨⟨leftExecution.1, rightExecution.1⟩, leftExecution.2.1,
      run_seq_iff.mpr ⟨intermediate, leftExecution.2.2, rightExecution.2.2⟩⟩

theorem exec_ite_iff {context : ProgramContext D} {guard left right before after} :
    executes context (.ite guard left right) before after ↔
      left.WellFormed ∧ right.WellFormed ∧
      ((evalProgramExpr context.interpretation before.current.visible guard = some true ∧
        executes context left before after) ∨
       (evalProgramExpr context.interpretation before.current.visible guard = some false ∧
        executes context right before after)) := by
  constructor
  · rintro ⟨⟨leftWellFormed, rightWellFormed⟩, initial, run⟩
    refine ⟨leftWellFormed, rightWellFormed, ?_⟩
    rcases run_ite_iff.mp run with ⟨enabled, chosen⟩ | ⟨enabled, chosen⟩
    · exact Or.inl ⟨enabled, leftWellFormed, initial, chosen⟩
    · exact Or.inr ⟨enabled, rightWellFormed, initial, chosen⟩
  · rintro ⟨leftWellFormed, rightWellFormed, (⟨enabled, chosen⟩ | ⟨enabled, chosen⟩)⟩
    · exact ⟨⟨leftWellFormed, rightWellFormed⟩, chosen.2.1,
        run_ite_iff.mpr (Or.inl ⟨enabled, chosen.2.2⟩)⟩
    · exact ⟨⟨leftWellFormed, rightWellFormed⟩, chosen.2.1,
        run_ite_iff.mpr (Or.inr ⟨enabled, chosen.2.2⟩)⟩

theorem run_seq_to_parallel {context : ProgramContext D} {left right before after}
    (run : RawRun context (.seq left right) before after) :
    RawRun context (.par left right) before after := by
  obtain ⟨n, steps⟩ := run
  exact ⟨n, steps.seq_to_parallel⟩

theorem exec_seq_to_parallel {context : ProgramContext D} {left right before after}
    (noninterfering : Noninterfering left right)
    (execution : executes context (.seq left right) before after) :
    executes context (.par left right) before after :=
  ⟨⟨execution.1.1, execution.1.2, noninterfering⟩, execution.2.1,
    run_seq_to_parallel execution.2.2⟩

theorem primitiveEffect_test_iff {context : ProgramContext D}
    {result hypothesis expression test population visible after delta} :
    primitiveEffect context.interpretation (.test result hypothesis expression test population)
      visible = some (after, delta) ↔
      ∃ data, evalDatasetExpr context.interpretation visible expression = some data ∧
        after = (VisibleWrite.value result
          ((context.interpretation.tests hypothesis test).tailProbability data)).apply visible ∧
        delta = {(data, test)} := by
  constructor
  · intro enabled
    cases evaluated : evalDatasetExpr context.interpretation visible expression with
    | none => simp [primitiveEffect, evalPrimitive, evaluated] at enabled
    | some data =>
        simp only [primitiveEffect, evalPrimitive, evaluated, Option.map_some,
          Option.some.injEq, Prod.mk.injEq] at enabled
        exact ⟨data, rfl, enabled.1.symm, enabled.2.symm⟩
  · rintro ⟨data, evaluated, rfl, rfl⟩
    simp [primitiveEffect, evalPrimitive, evaluated]

theorem test_step_effect {context : ProgramContext D}
    {result hypothesis expression test population target before after} :
    Step context (some (.command (.test result hypothesis expression test population)))
      before target after ↔
      ∃ data, evalDatasetExpr context.interpretation before.current.visible expression =
        some data ∧ target = none ∧
        after = before.extend (commandState before.current
          (.test result hypothesis expression test population)
          ((VisibleWrite.value result
            ((context.interpretation.tests hypothesis test).tailProbability data)).apply
            before.current.visible) {(data, test)}) := by
  constructor
  · intro step
    obtain ⟨visible, delta, enabled, targetEq, afterEq⟩ := Step.command_iff.mp step
    obtain ⟨data, evaluated, rfl, rfl⟩ := primitiveEffect_test_iff.mp enabled
    exact ⟨data, evaluated, targetEq, afterEq⟩
  · rintro ⟨data, evaluated, rfl, rfl⟩
    apply Step.command
    exact primitiveEffect_test_iff.mpr ⟨data, evaluated, rfl, rfl⟩

theorem test_step_report {context : ProgramContext D}
    {result hypothesis expression test population target before after data}
    (evaluated : evalDatasetExpr context.interpretation before.current.visible expression = some data)
    (step : Step context (some (.command (.test result hypothesis expression test population)))
      before target after) :
    target = none ∧
      after.current.memory.read result =
        some ((context.interpretation.tests hypothesis test).tailProbability data) ∧
      after.current.datasets = before.current.datasets ∧
      after.current.history = before.current.history + {(data, test)} ∧
      after.current.action = .command (.test result hypothesis expression test population) := by
  obtain ⟨actualData, actualEval, rfl, rfl⟩ := test_step_effect.mp step
  have dataEq : actualData = data := Option.some.inj (actualEval.symm.trans evaluated)
  subst actualData
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp [commandState, VisibleWrite.apply, Memory.read, Memory.assemble,
      Memory.observable, Memory.update]
  · simp [commandState, VisibleWrite.apply, State.visible]
  · simp [commandState]
  · simp [commandState]

theorem test_step_multiplicity [DecidableEq D] {context : ProgramContext D}
    {result hypothesis expression test population target before after data}
    (evaluated : evalDatasetExpr context.interpretation before.current.visible expression = some data)
    (step : Step context (some (.command (.test result hypothesis expression test population)))
      before target after) :
    History.count after.current.history data test =
      History.count before.current.history data test + 1 := by
  rw [(test_step_report evaluated step).2.2.2.1]
  simp [History.count, Multiset.count_add]

theorem run_skip_not_identity {context : ProgramContext D} {before after}
    (run : RawRun context Program.skip before after) : after ≠ before := by
  rw [run_skip_iff.mp run]
  intro equality
  have lengthEq := congrArg (fun world : World D Primitive => world.trace.length) equality
  simp only [World.extend_trace, List.length_append, List.length_singleton] at lengthEq
  omega

omit [MeasurableSpace D] in
/-- Intrinsically sorted writes return exactly their target carrier and cannot
change a read of a different sort, visibility, or identifier. -/
theorem visibleWrite_value_typed (visible : VisibleState D)
    (x : Variable sort .observable) (value : Value sort) :
    (Memory.assemble ((VisibleWrite.value x value).apply visible).memory
      (fun _ _ => none)).read x = some value ∧
    ∀ (otherSort : ValueSort) (visibility : Visibility) (y : Variable otherSort visibility),
      (Memory.assemble ((VisibleWrite.value x value).apply visible).memory
        (fun _ _ => none)).read y ≠
        (Memory.assemble visible.memory (fun _ _ => none)).read y →
      sort = otherSort ∧ .observable = visibility ∧ x.id = y.id := by
  have updated := Memory.memory_update_typed
    (Memory.assemble visible.memory (fun _ _ => none)) x (some value)
  have hidden := hidden_observable_write
    (Memory.assemble visible.memory (fun _ _ => none)) x value
  have materialized :
      Memory.assemble ((VisibleWrite.value x value).apply visible).memory (fun _ _ => none) =
        (Memory.assemble visible.memory (fun _ _ => none)).update x (some value) := by
    change Memory.assemble
      ((Memory.assemble visible.memory (fun _ _ => none)).update x (some value)).observable
      (fun _ _ => none) = _
    calc
      _ = Memory.assemble
          ((Memory.assemble visible.memory (fun _ _ => none)).update x (some value)).observable
          ((Memory.assemble visible.memory (fun _ _ => none)).update x (some value)).hidden := by
            rw [hidden, Memory.hidden_assemble]
      _ = _ := Memory.assemble_projections _
  simpa only [materialized] using updated

omit [MeasurableSpace D] in
private theorem state_eq_of_observe_hidden {left right : State D Primitive}
    (observed : observeState left = observeState right)
    (hidden : left.memory.hidden = right.memory.hidden) : left = right := by
  have observable := congrArg Observation.memory observed
  have datasets := congrArg Observation.datasets observed
  have history := congrArg Observation.history observed
  have action := congrArg Observation.action observed
  have memory : left.memory = right.memory := by
    calc
      _ = Memory.assemble left.memory.observable left.memory.hidden :=
        (Memory.assemble_projections _).symm
      _ = Memory.assemble right.memory.observable right.memory.hidden :=
        congrArg₂ Memory.assemble observable hidden
      _ = _ := Memory.assemble_projections _
  cases left
  cases right
  cases memory
  cases datasets
  cases history
  cases action
  rfl

omit [MeasurableSpace D] in
private theorem states_eq_of_observe_hidden
    (hidden : HiddenMemory) (left right : List (State D Primitive))
    (observed : left.map observeState = right.map observeState)
    (leftHidden : ∀ state ∈ left, state.memory.hidden = hidden)
    (rightHidden : ∀ state ∈ right, state.memory.hidden = hidden) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head rest => simp at observed
  | cons head rest ih =>
      cases right with
      | nil => simp at observed
      | cons other tail =>
          obtain ⟨headObserved, restObserved⟩ := List.cons.inj observed
          have headEq := state_eq_of_observe_hidden headObserved
            ((leftHidden head (by simp)).trans (rightHidden other (by simp)).symm)
          have restEq := ih tail restObserved
            (fun state member => leftHidden state (List.mem_cons_of_mem _ member))
            (fun state member => rightHidden state (List.mem_cons_of_mem _ member))
          rw [headEq, restEq]

theorem admitted_eq_of_accessible_hidden {context : ProgramContext D}
    {left right : World D Primitive}
    (leftAdmitted : Admitted context.model.dynamics left)
    (rightAdmitted : Admitted context.model.dynamics right)
    (accessible : Accessible left right)
    (hidden : left.current.memory.hidden = right.current.memory.hidden) : left = right := by
  have traces : left.trace = right.trace := by
    apply states_eq_of_observe_hidden left.current.memory.hidden _ _ accessible
    · intro state member
      exact (leftAdmitted.1 state member).trans (admitted_current_hidden leftAdmitted).symm
    · intro state member
      exact (rightAdmitted.1 state member).trans
        ((admitted_current_hidden rightAdmitted).symm.trans hidden.symm)
  have initial : left.initial = right.initial := (List.cons.inj traces).1
  have rest : left.rest = right.rest := (List.cons.inj traces).2
  cases left
  cases right
  cases initial
  cases rest
  rfl

theorem command_accessible_forth {context : ProgramContext D}
    {primitive before after alternativeBefore}
    (step : Step context (some (.command primitive)) before none after)
    (alternativeAdmitted : Admitted context.model.dynamics alternativeBefore)
    (accessible : Accessible before alternativeBefore) :
    ∃ alternativeAfter,
      Step context (some (.command primitive)) alternativeBefore none alternativeAfter ∧
      Admitted context.model.dynamics alternativeAfter ∧ Accessible after alternativeAfter := by
  obtain ⟨visible, delta, enabled, _, rfl⟩ := Step.command_iff.mp step
  have alternativeEnabled :
      primitiveEffect context.interpretation primitive alternativeBefore.current.visible =
        some (visible, delta) := by
    rw [← accessible_current_visible accessible]
    exact enabled
  let alternativeAfter := alternativeBefore.extend
    (commandState alternativeBefore.current primitive visible delta)
  have alternativeStep : Step context (some (.command primitive))
      alternativeBefore none alternativeAfter := .command alternativeEnabled
  refine ⟨alternativeAfter, alternativeStep, alternativeStep.admitted alternativeAdmitted, ?_⟩
  apply (extend_accessible_iff _ _ _ _).mpr
  refine ⟨accessible, ?_⟩
  simp only [observeState, commandState, Memory.assemble]
  rw [accessible_history_eq accessible]

/-- Every admitted full-trace alternative of a command successor is itself an
actual successor of an admitted alternative of the source world. -/
theorem command_accessible_back {context : ProgramContext D}
    {primitive before after alternativeAfter}
    (_initial : Admitted context.model.dynamics before)
    (step : Step context (some (.command primitive)) before none after)
    (alternativeAdmitted : Admitted context.model.dynamics alternativeAfter)
    (accessible : Accessible after alternativeAfter) :
    ∃ alternativeBefore, Admitted context.model.dynamics alternativeBefore ∧
      Accessible before alternativeBefore ∧
      Step context (some (.command primitive)) alternativeBefore none alternativeAfter := by
  let alternativeBefore := before.rebuildHidden alternativeAfter.current.memory.hidden
  have beforeAccessible : Accessible before alternativeBefore :=
    rebuildHidden_accessible _ _
  have beforeAdmitted : Admitted context.model.dynamics alternativeBefore := by
    apply (admitted_rebuildHidden_iff context.model.dynamics before _).mpr
    have compatible := admitted_hidden_mem_compatible alternativeAdmitted
    rw [← compatibleHidden_eq_of_accessible accessible, step.compatible_hidden] at compatible
    exact compatible
  obtain ⟨reconstructed, reconstructedStep, reconstructedAdmitted, reconstructedAccessible⟩ :=
    command_accessible_forth step beforeAdmitted beforeAccessible
  have exactAlternative : alternativeAfter = reconstructed := by
    apply admitted_eq_of_accessible_hidden alternativeAdmitted reconstructedAdmitted
      (accessible.symm.trans reconstructedAccessible)
    rw [reconstructedStep.hidden]
    exact (World.rebuildHidden_current_hidden before _).symm
  exact ⟨alternativeBefore, beforeAdmitted, beforeAccessible,
    by simpa only [exactAlternative] using reconstructedStep⟩

namespace Steps

theorem terminating_pos {context : ProgramContext D} {n program before after}
    (steps : Steps context n (some program) before none after) : 0 < n := by
  cases steps with
  | cons first rest => omega

theorem ite_iff {context : ProgramContext D} {n guard left right before after} :
    Steps context n (some (.ite guard left right)) before none after ↔
      (∃ m, n = m + 1 ∧
        evalProgramExpr context.interpretation before.current.visible guard = some true ∧
        Steps context m (some left) before none after) ∨
      (∃ m, n = m + 1 ∧
        evalProgramExpr context.interpretation before.current.visible guard = some false ∧
        Steps context m (some right) before none after) := by
  constructor
  · intro steps
    cases steps with
    | @cons count source middle target before intermediate after first rest =>
        obtain ⟨rfl, alternatives⟩ := Step.ite_iff.mp first
        rcases alternatives with ⟨enabled, rfl⟩ | ⟨enabled, rfl⟩
        · exact Or.inl ⟨count, rfl, enabled, rest⟩
        · exact Or.inr ⟨count, rfl, enabled, rest⟩
  · rintro (⟨m, rfl, enabled, rest⟩ | ⟨m, rfl, enabled, rest⟩)
    · exact .cons (.ifTrue enabled) rest
    · exact .cons (.ifFalse enabled) rest

theorem loop_unfold_iff {context : ProgramContext D} {n guard body before after} :
    Steps context n (some (.loop guard body)) before none after ↔
      (n = 1 ∧
        evalProgramExpr context.interpretation before.current.visible guard = some false ∧
        after = before) ∨
      (∃ m k intermediate, n = m + k + 1 ∧
        evalProgramExpr context.interpretation before.current.visible guard = some true ∧
        Steps context m (some body) before none intermediate ∧
        Steps context k (some (.loop guard body)) intermediate none after) := by
  constructor
  · intro steps
    cases steps with
    | @cons count source middle target before intermediate after first rest =>
        obtain ⟨rfl, alternatives⟩ := Step.loop_iff.mp first
        rcases alternatives with ⟨enabled, rfl⟩ | ⟨enabled, rfl⟩
        · obtain ⟨m, k, boundary, hcount, bodySteps, loopSteps⟩ := Steps.seq_iff.mp rest
          exact Or.inr ⟨m, k, boundary, by omega, enabled, bodySteps, loopSteps⟩
        · obtain ⟨rfl, _, rfl⟩ := Steps.terminal_iff.mp rest
          exact Or.inl ⟨rfl, enabled, rfl⟩
  · rintro (⟨rfl, enabled, rfl⟩ |
      ⟨m, k, intermediate, rfl, enabled, bodySteps, loopSteps⟩)
    · exact .cons (.loopFalse enabled) (.refl _ _)
    · exact .cons (.loopTrue enabled)
        ((bodySteps.seq_lift (.loop guard body)).trans loopSteps)

end Steps

theorem exec_loop_unfold_iff {context : ProgramContext D} {guard body before after} :
    executes context (.loop guard body) before after ↔
      body.WellFormed ∧ Admitted context.model.dynamics before ∧
      ((evalProgramExpr context.interpretation before.current.visible guard = some false ∧
        after = before) ∨
       (evalProgramExpr context.interpretation before.current.visible guard = some true ∧
        ∃ intermediate, executes context body before intermediate ∧
          executes context (.loop guard body) intermediate after)) := by
  constructor
  · rintro ⟨wellFormed, initial, run⟩
    refine ⟨wellFormed, initial, ?_⟩
    rcases run_loop_unfold_iff.mp run with ⟨enabled, same⟩ |
      ⟨enabled, intermediate, bodyRun, loopRun⟩
    · exact Or.inl ⟨enabled, same⟩
    · exact Or.inr ⟨enabled, intermediate, ⟨wellFormed, initial, bodyRun⟩,
        ⟨wellFormed, bodyRun.admitted initial, loopRun⟩⟩
  · rintro ⟨wellFormed, initial, alternatives⟩
    refine ⟨wellFormed, initial, run_loop_unfold_iff.mpr ?_⟩
    rcases alternatives with ⟨enabled, same⟩ |
      ⟨enabled, intermediate, bodyExecution, loopExecution⟩
    · exact Or.inl ⟨enabled, same⟩
    · exact Or.inr ⟨enabled, intermediate, bodyExecution.2.2, loopExecution.2.2⟩

end
end Lara.BHL
