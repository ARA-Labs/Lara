import Lara.BHL.Value
import Lara.BHL.History
import Mathlib.Data.List.Basic

namespace Lara.BHL

/-- Commands remain symbolic and are supplied by the program language.
Sampling actions bind mathematical data values to a distinct population name. -/
inductive Action (D Command : Type) where
  | initial
  | command : Command → Action D Command
  | sample : D → PopulationId → Action D Command

/-- History counters are derived from `history` and `datasets`, never stored
as independently mutable cells. `D` is a mathematical dataset carrier. -/
structure State (D Command : Type) where
  memory : Memory
  datasets : DatasetId → D
  history : History D
  action : Action D Command

structure Observation (D Command : Type) where
  memory : ObservableMemory
  datasets : DatasetId → D
  history : History D
  action : Action D Command

def observeState (state : State D Command) : Observation D Command :=
  ⟨fun s id => state.memory s .observable id,
    state.datasets, state.history, state.action⟩

/-- A world retains its nonempty ordered state trace and empty initial ledger.
Operational admissibility is a separate model restriction, not endpoint equality. -/
structure World (D Command : Type) where
  initial : State D Command
  rest : List (State D Command)
  initial_history_empty : initial.history = 0

namespace World

def trace (world : World D Command) : List (State D Command) :=
  world.initial :: world.rest

def current (world : World D Command) : State D Command :=
  world.trace.getLast (by simp [trace])

def start (memory : Memory) (datasets : DatasetId → D) : World D Command :=
  ⟨⟨memory, datasets, 0, .initial⟩, [], rfl⟩

def extend (world : World D Command) (state : State D Command) : World D Command :=
  ⟨world.initial, world.rest ++ [state], world.initial_history_empty⟩

@[simp] theorem trace_nonempty (world : World D Command) : world.trace ≠ [] := by
  simp [trace]

@[simp] theorem start_current (memory : Memory) (datasets : DatasetId → D) :
    (start (Command := Command) memory datasets).current =
      ⟨memory, datasets, 0, .initial⟩ := rfl

@[simp] theorem extend_trace (world : World D Command) (state : State D Command) :
    (world.extend state).trace = world.trace ++ [state] := by
  simp [extend, trace]

@[simp] theorem extend_current (world : World D Command) (state : State D Command) :
    (world.extend state).current = state := by
  simp [current]

 theorem extend_prefix (world : World D Command) (state : State D Command) :
    world.trace <+: (world.extend state).trace := by
  rw [extend_trace]
  exact List.prefix_append _ _

@[simp] theorem initial_history (world : World D Command) :
    world.initial.history = 0 := world.initial_history_empty

/-- Sampling provenance is derived from the recorded actions, including repeats.
This is modeled provenance, not evidence of physical sampling fidelity. -/
def samplingProvenance (world : World D Command) : Multiset (D × PopulationId) :=
  ((world.rest.filterMap fun state => match state.action with
    | .sample data population => some (data, population)
    | _ => none) : Multiset (D × PopulationId))

 theorem samplingProvenance_extend_command (world : World D Command)
    (state : State D Command) (command : Command)
    (h : state.action = .command command) :
    (world.extend state).samplingProvenance = world.samplingProvenance := by
  simp [samplingProvenance, extend, h]

 theorem samplingProvenance_extend_sample (world : World D Command)
    (state : State D Command) (data : D) (population : PopulationId)
    (h : state.action = .sample data population) :
    (world.extend state).samplingProvenance =
      world.samplingProvenance + {(data, population)} := by
  simp [samplingProvenance, extend, h, ← Multiset.coe_add]

end World

def observeWorld (world : World D Command) : List (Observation D Command) :=
  world.trace.map observeState

/-- BHL accessibility observes the complete trace, not just the final memory.
This relation is independent of Lara's arbitrary accepted-context bridges. -/
def Accessible (left right : World D Command) : Prop :=
  observeWorld left = observeWorld right

 theorem accessible_refl (world : World D Command) : Accessible world world := rfl

 theorem accessible_symm {left right : World D Command} (h : Accessible left right) :
    Accessible right left := h.symm

 theorem accessible_trans {left middle right : World D Command}
    (h₁ : Accessible left middle) (h₂ : Accessible middle right) :
    Accessible left right := h₁.trans h₂

 theorem observe_current (world : World D Command) :
    (observeWorld world).getLast (by simp [observeWorld]) =
      observeState world.current := by
  simp [observeWorld, World.current]

 theorem accessible_current_observation {left right : World D Command}
    (h : Accessible left right) : observeState left.current = observeState right.current := by
  have hlast := congrArg List.getLast? h
  have hl : observeWorld left ≠ [] := by simp [observeWorld]
  have hr : observeWorld right ≠ [] := by simp [observeWorld]
  rw [List.getLast?_eq_some_getLast hl, List.getLast?_eq_some_getLast hr] at hlast
  exact Option.some.inj (by simpa only [observe_current] using hlast)

 theorem accessible_history_eq {left right : World D Command}
    (h : Accessible left right) : left.current.history = right.current.history :=
  congrArg Observation.history (accessible_current_observation h)

 theorem accessible_dataset_eq {left right : World D Command}
    (h : Accessible left right) (name : DatasetId) :
    left.current.datasets name = right.current.datasets name := by
  exact congrArg (fun observation => observation.datasets name)
    (accessible_current_observation h)

 theorem accessible_visible_eq {left right : World D Command}
    (h : Accessible left right) (x : Variable s .observable) :
    left.current.memory.read x = right.current.memory.read x := by
  exact congrArg (fun observation => observation.memory s x.id)
    (accessible_current_observation h)

 theorem observe_extend (world : World D Command) (state : State D Command) :
    observeWorld (world.extend state) = observeWorld world ++ [observeState state] := by
  simp [observeWorld]

 theorem extend_accessible_iff (left right : World D Command)
    (leftState rightState : State D Command) :
    Accessible (left.extend leftState) (right.extend rightState) ↔
      Accessible left right ∧ observeState leftState = observeState rightState := by
  simp [Accessible, observe_extend]

 theorem accessible_sampling_provenance {left right : World D Command}
    (h : Accessible left right) :
    left.samplingProvenance = right.samplingProvenance := by
  have hrest := congrArg List.tail h
  have hactions := congrArg (List.map Observation.action) hrest
  simpa [World.samplingProvenance, observeWorld, World.trace, observeState,
    List.filterMap_map] using
    congrArg (fun actions : List (Action D Command) =>
      ((actions.filterMap fun action => match action with
        | Action.sample data population => some (data, population)
        | _ => none) : Multiset (D × PopulationId))) hactions


end Lara.BHL
