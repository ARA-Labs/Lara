import Lara.BHL.State

namespace Lara.BHL

/-- The input and output of a program primitive exclude ordinary hidden memory. -/
structure VisibleState (D : Type) where
  memory : ObservableMemory
  datasets : DatasetId → D

def Observation.visible (observation : Observation D Command) : VisibleState D :=
  ⟨observation.memory, observation.datasets⟩

def State.visible (state : State D Command) : VisibleState D :=
  ⟨state.memory.observable, state.datasets⟩

/-- Independent local evidence and primitive effects. Sampling is not a program
command: its relation may depend on the hidden population law. The command
function cannot inspect hidden memory and returns the exact finite test delta. -/
structure Dynamics (D Command : Type) where
  initial : HiddenMemory → VisibleState D → Prop
  command : Command → VisibleState D → Option (VisibleState D × History D)
  sampling : HiddenMemory → VisibleState D → VisibleState D → D → PopulationId → Prop

/-- A locally checked adjacent observation edge, independent of BHL assertions. -/
def AllowedEdge (dynamics : Dynamics D Command) (hidden : HiddenMemory)
    (before after : Observation D Command) : Prop :=
  match after.action with
  | .initial => False
  | .command command => ∃ delta,
      dynamics.command command before.visible = some (after.visible, delta) ∧
      after.history = before.history + delta
  | .sample data population =>
      dynamics.sampling hidden before.visible after.visible data population ∧
      after.history = before.history

/-- Explicit finite adjacent-edge equations, not an opaque execution predicate. -/
def TraceEdges (dynamics : Dynamics D Command) (hidden : HiddenMemory)
    (before : Observation D Command) : List (Observation D Command) → Prop
  | [] => True
  | after :: rest => AllowedEdge dynamics hidden before after ∧
      TraceEdges dynamics hidden after rest

/-- Initial evidence and every adjacent edge are independently constrained. -/
def TraceAllowed (dynamics : Dynamics D Command) (hidden : HiddenMemory) :
    List (Observation D Command) → Prop
  | [] => False
  | first :: rest => first.history = 0 ∧ first.action = .initial ∧
      dynamics.initial hidden first.visible ∧ TraceEdges dynamics hidden first rest

def ConstantHidden (world : World D Command) : Prop :=
  ∀ state ∈ world.trace, state.memory.hidden = world.initial.memory.hidden

/-- Every and only locally lawful trace is admitted. There is no caller-selected
world universe or field asserting a modal, replay, or soundness conclusion. -/
def Admitted (dynamics : Dynamics D Command) (world : World D Command) : Prop :=
  ConstantHidden world ∧ TraceAllowed dynamics world.initial.memory.hidden (observeWorld world)

def World.prefix (world : World D Command) (length : Nat) : World D Command :=
  ⟨world.initial, world.rest.take length, world.initial_history_empty⟩

end Lara.BHL
