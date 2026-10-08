import Lara.BHL.Program

namespace Lara.BHL

variable {D : Type} [MeasurableSpace D]

/-- Source programs and terminal configurations are distinct. In particular,
source skip emits a command state; only terminal none has an empty run. -/
inductive Step (context : ProgramContext D) :
    Option Program → World D Primitive → Option Program → World D Primitive → Prop where
  | command {primitive world visible delta}
      (enabled : primitiveEffect context.interpretation primitive world.current.visible =
        some (visible, delta)) :
      Step context (some (.command primitive)) world none
        (world.extend (commandState world.current primitive visible delta))
  | seqContinue {left right next before after}
      (child : Step context (some left) before (some next) after) :
      Step context (some (.seq left right)) before (some (.seq next right)) after
  | seqFinish {left right before after}
      (child : Step context (some left) before none after) :
      Step context (some (.seq left right)) before (some right) after
  | ifTrue {guard : ProgramExpr .boolean} {left right world}
      (enabled : evalProgramExpr context.interpretation world.current.visible guard = some true) :
      Step context (some (.ite guard left right)) world (some left) world
  | ifFalse {guard : ProgramExpr .boolean} {left right world}
      (enabled : evalProgramExpr context.interpretation world.current.visible guard = some false) :
      Step context (some (.ite guard left right)) world (some right) world
  | loopTrue {guard : ProgramExpr .boolean} {body world}
      (enabled : evalProgramExpr context.interpretation world.current.visible guard = some true) :
      Step context (some (.loop guard body)) world (some (.seq body (.loop guard body))) world
  | loopFalse {guard : ProgramExpr .boolean} {body world}
      (enabled : evalProgramExpr context.interpretation world.current.visible guard = some false) :
      Step context (some (.loop guard body)) world none world
  | parLeftContinue {left right next before after}
      (child : Step context (some left) before (some next) after) :
      Step context (some (.par left right)) before (some (.par next right)) after
  | parLeftFinish {left right before after}
      (child : Step context (some left) before none after) :
      Step context (some (.par left right)) before (some right) after
  | parRightContinue {left right next before after}
      (child : Step context (some right) before (some next) after) :
      Step context (some (.par left right)) before (some (.par left next)) after
  | parRightFinish {left right before after}
      (child : Step context (some right) before none after) :
      Step context (some (.par left right)) before (some left) after

/-- The index counts actual source small steps, including silent guards and
lifting a child's final step. It is not a fuel bound or a termination claim. -/
inductive Steps (context : ProgramContext D) :
    Nat → Option Program → World D Primitive → Option Program → World D Primitive → Prop where
  | refl (program : Option Program) (world : World D Primitive) :
      Steps context 0 program world program world
  | cons {length source middle target before intermediate after}
      (first : Step context source before middle intermediate)
      (rest : Steps context length middle intermediate target after) :
      Steps context (length + 1) source before target after

def Run (context : ProgramContext D) (source : Option Program) (before : World D Primitive)
    (target : Option Program) (after : World D Primitive) : Prop :=
  ∃ length, Steps context length source before target after

/-- Public terminating execution retains its exact operational context and
literal worlds. Every parallel occurrence must satisfy source noninterference. -/
def executes (context : ProgramContext D) (program : Program)
    (before after : World D Primitive) : Prop :=
  program.WellFormed ∧ Admitted context.model.dynamics before ∧
    Run context (some program) before none after

namespace Step

theorem source_some {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) : ∃ program, source = some program := by
  cases step <;> exact ⟨_, rfl⟩

theorem terminal_impossible {context : ProgramContext D} {target before after} :
    ¬ Step context none before target after := by
  intro step
  obtain ⟨program, impossible⟩ := step.source_some
  cases impossible

end Step

namespace Steps

theorem zero_iff {context : ProgramContext D} {source target before after} :
    Steps context 0 source before target after ↔ source = target ∧ before = after := by
  constructor
  · intro steps
    cases steps
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .refl _ _

theorem terminal_iff {context : ProgramContext D} {length target before after} :
    Steps context length none before target after ↔
      length = 0 ∧ target = none ∧ before = after := by
  constructor
  · intro steps
    cases steps with
    | refl => exact ⟨rfl, rfl, rfl⟩
    | cons first rest => exact False.elim (Step.terminal_impossible first)
  · rintro ⟨rfl, rfl, rfl⟩
    exact .refl _ _

end Steps

namespace Run

theorem refl (context : ProgramContext D) (program : Option Program) (world : World D Primitive) :
    Run context program world program world := ⟨0, .refl _ _⟩

theorem terminal_iff {context : ProgramContext D} {target before after} :
    Run context none before target after ↔ target = none ∧ before = after := by
  simp [Run, Steps.terminal_iff]

end Run

end Lara.BHL
