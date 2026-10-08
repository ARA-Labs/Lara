import Lara.BHL.ControlCoding
import Lara.BHL.ControlMetadata
import Lara.BHL.Soundness

namespace Lara.BHL

/-- Four ordinary typed ghost carriers. Control metadata is disjoint from the
program's memory and retains neither an interpreter nor a run predicate. -/
structure ControlLog (D : Type) where
  source : World D Primitive
  programStates : List (State D Primitive)
  controlSeed : World D Primitive
  controlStates : List (State D Primitive)

namespace ControlLog

 def programPrefix (log : ControlLog D) (count : Nat) : World D Primitive :=
  log.source.appendStates (log.programStates.take count)

 def metadataPrefix (log : ControlLog D) (index : Nat) : World D Primitive :=
  log.controlSeed.appendStates (log.controlStates.take index)

 def readCell (log : ControlLog D) (index : Nat) (cell : LogCell) : Option Int :=
  (log.metadataPrefix index).current.memory.read cell.toVariable

 def terminal (log : ControlLog D) : World D Primitive :=
  log.source.appendStates log.programStates

end ControlLog

variable {D : Type} [MeasurableSpace D]

noncomputable section

/-- One local action's full-view relation. This is deliberately weaker than
literal equality with a command state, so rigid ghost logs may use any admitted
representative; decoding must replay literal transitions from the actual source. -/
def ControlLabel.viewEffect (ctx : ProgramContext D) (label : ControlLabel)
    (before after : World D Primitive) : Prop :=
  match label with
  | .command primitive => ∃ visible delta,
      primitiveEffect ctx.interpretation primitive before.current.visible = some (visible, delta) ∧
        semanticView ctx.model.dynamics after =
          {semanticView ctx.model.dynamics before with
            visible := visible, history := before.current.history + delta}
  | .guard expression value =>
      evalProgramExpr ctx.interpretation before.current.visible expression = some value ∧
        semanticView ctx.model.dynamics before = semanticView ctx.model.dynamics after

/-- Finite edge membership, successful local evaluation, typed counters and
admitted program prefixes. There is no `Run`, `executes`, Hoare validity or WLP
in this independently defined predicate. -/
def ControlLog.edge (ctx : ProgramContext D) (program : Program)
    (log : ControlLog D) (index : Nat) : Prop :=
  ∃ current ∈ program.residuals, ∃ target label,
    (target, label) ∈ current.controlEdges ∧
      log.readCell index .control = some (program.controlCode (some current)) ∧
      log.readCell (index + 1) .control = some (program.controlCode target) ∧
      ∃ count nextCount : Nat,
        count ≤ log.programStates.length ∧ nextCount ≤ log.programStates.length ∧
          log.readCell index .commands = some (count : Int) ∧
          log.readCell (index + 1) .commands = some (nextCount : Int) ∧
          Admitted ctx.model.dynamics (log.programPrefix count) ∧
          Admitted ctx.model.dynamics (log.programPrefix nextCount) ∧
          label.viewEffect ctx (log.programPrefix count) (log.programPrefix nextCount) ∧
          (match label with
            | .guard _ _ => nextCount = count
            | .command _ => nextCount = count + 1)

/-- Exactly the local checks expanded by the finite assertion formula. Metadata
worlds are rigid read-only carriers and are not required to be admitted. -/
def ControlLog.Valid (ctx : ProgramContext D) (program : Program)
    (log : ControlLog D) : Prop :=
  Admitted ctx.model.dynamics log.source ∧
    log.readCell 0 .control = some (program.controlCode (some program)) ∧
    log.readCell 0 .commands = some 0 ∧
    log.readCell log.controlStates.length .control = some 0 ∧
    log.readCell log.controlStates.length .commands = some (log.programStates.length : Int) ∧
    ∀ index, index < log.controlStates.length → log.edge ctx program index

end
end Lara.BHL
