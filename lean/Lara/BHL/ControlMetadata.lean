import Lara.BHL.Soundness
import Lara.BHL.GhostSubstitution

namespace Lara.BHL

namespace World

variable {D Command : Type}

/-- The exact world constructor used by `AssertionTerm.appendWorld`. -/
def appendStates (world : World D Command) (states : List (State D Command)) :
    World D Command :=
  ⟨world.initial, world.rest ++ states, world.initial_history_empty⟩

@[simp] theorem appendStates_initial (world : World D Command)
    (states : List (State D Command)) :
    (world.appendStates states).initial = world.initial := rfl

@[simp] theorem appendStates_rest (world : World D Command)
    (states : List (State D Command)) :
    (world.appendStates states).rest = world.rest ++ states := rfl

@[simp] theorem appendStates_nil (world : World D Command) :
    world.appendStates [] = world := by
  cases world
  simp [appendStates]

@[simp] theorem appendStates_singleton (world : World D Command)
    (state : State D Command) : world.appendStates [state] = world.extend state := rfl

 theorem appendStates_assoc (world : World D Command)
    (left right : List (State D Command)) :
    (world.appendStates left).appendStates right = world.appendStates (left ++ right) := by
  simp only [appendStates, List.append_assoc]

@[simp] theorem appendStates_trace (world : World D Command)
    (states : List (State D Command)) :
    (world.appendStates states).trace = world.trace ++ states := by
  simp [appendStates, trace]

 theorem appendStates_trace_length (world : World D Command)
    (states : List (State D Command)) :
    (world.appendStates states).trace.length = world.trace.length + states.length := by
  simp only [appendStates_trace, List.length_append]

 theorem appendStates_trace_prefix (world : World D Command)
    (states : List (State D Command)) :
    world.trace <+: (world.appendStates states).trace := by
  rw [appendStates_trace]
  exact List.prefix_append _ _

 theorem appendStates_take_trace_prefix (world : World D Command)
    (states : List (State D Command)) (j : Nat) :
    (world.appendStates (states.take j)).trace <+: (world.appendStates states).trace := by
  refine ⟨states.drop j, ?_⟩
  simp only [appendStates_trace, List.append_assoc, List.take_append_drop]

 theorem appendStates_current (world : World D Command)
    (states : List (State D Command)) (nonempty : states ≠ []) :
    (world.appendStates states).current = states.getLast nonempty := by
  simp only [current, appendStates_trace, List.getLast_append_of_ne_nil _ nonempty]

@[simp] theorem appendStates_take_zero (world : World D Command)
    (states : List (State D Command)) : world.appendStates (states.take 0) = world := by
  simp

 theorem appendStates_take_succ (world : World D Command)
    (states : List (State D Command)) (j : Nat) (bound : j < states.length) :
    world.appendStates (states.take (j + 1)) =
      (world.appendStates (states.take j)).extend (states[j]'bound) := by
  rw [List.take_succ_eq_append_getElem bound, ← appendStates_assoc,
    appendStates_singleton]

 theorem appendStates_take_succ_current (world : World D Command)
    (states : List (State D Command)) (j : Nat) (bound : j < states.length) :
    (world.appendStates (states.take (j + 1))).current = states[j]'bound := by
  rw [appendStates_take_succ world states j bound, extend_current]

 theorem appendStates_start_prefix (memory : Memory) (datasets : DatasetId → D)
    (states : List (State D Command)) (j : Nat) :
    ((start (Command := Command) memory datasets).appendStates states).prefix j =
      (start (Command := Command) memory datasets).appendStates (states.take j) := rfl

end World

/-- Two cells in a synthetic metadata world, not reserved program variables. -/
inductive LogCell where
  | control
  | commands
  deriving DecidableEq, Repr

namespace LogCell

 def toVariable : LogCell → Variable .integer .observable
  | .control => ⟨⟨0⟩⟩
  | .commands => ⟨⟨1⟩⟩

@[simp] theorem control_variable_id : control.toVariable.id = ⟨0⟩ := rfl

@[simp] theorem commands_variable_id : commands.toVariable.id = ⟨1⟩ := rfl

 theorem distinct_ids : control.toVariable.id ≠ commands.toVariable.id := by decide

 theorem variable_id_injective : Function.Injective (fun cell : LogCell => cell.toVariable.id) := by
  intro left right equal
  cases left <;> cases right <;> simp_all [toVariable]

 theorem variable_injective : Function.Injective toVariable := by
  intro left right equal
  exact variable_id_injective (congrArg Variable.id equal)

 theorem distinct_variables : control.toVariable ≠ commands.toVariable := by
  intro equal
  exact distinct_ids (congrArg Variable.id equal)

end LogCell

namespace ControlMetadata

noncomputable section

variable {D Command : Type}

/-- Only the two observable integer cells are defined; hidden carriers are reused. -/
def memory (basis : Memory) (code count : Int) : Memory :=
  Memory.assemble
    (fun sort id => match sort with
      | .integer =>
          if id = LogCell.control.toVariable.id then some code
          else if id = LogCell.commands.toVariable.id then some count else none
      | _ => none)
    basis.hidden

@[simp] theorem memory_read_control (basis : Memory) (code count : Int) :
    (memory basis code count).read LogCell.control.toVariable = some code := by
  simp [memory, Memory.read, Memory.assemble, LogCell.toVariable]

@[simp] theorem memory_read_commands (basis : Memory) (code count : Int) :
    (memory basis code count).read LogCell.commands.toVariable = some count := by
  simp [memory, Memory.read, Memory.assemble, LogCell.toVariable]

 theorem memory_read_other_integer (basis : Memory) (code count : Int)
    (x : Variable .integer .observable)
    (control : x.id ≠ LogCell.control.toVariable.id)
    (commands : x.id ≠ LogCell.commands.toVariable.id) :
    (memory basis code count).read x = none := by
  change x.id ≠ ⟨0⟩ at control
  change x.id ≠ ⟨1⟩ at commands
  simp [memory, Memory.read, Memory.assemble, control, commands]

 theorem memory_read_other_sort (basis : Memory) (code count : Int)
    (x : Variable sort .observable) (other : sort ≠ .integer) :
    (memory basis code count).read x = none := by
  cases sort <;> simp_all [memory, Memory.read, Memory.assemble]

@[simp] theorem memory_hidden (basis : Memory) (code count : Int) :
    (memory basis code count).hidden = basis.hidden := rfl

@[simp] theorem memory_read_invisible (basis : Memory) (code count : Int)
    (x : Variable sort .invisible) :
    (memory basis code count).read x = basis.read x := rfl

 theorem memory_eq_of_hidden_eq (left right : Memory) (code count : Int)
    (hidden : left.hidden = right.hidden) :
    memory left code count = memory right code count := by
  unfold memory
  rw [hidden]

@[simp] theorem memory_memory (basis : Memory) (firstCode firstCount code count : Int) :
    memory (memory basis firstCode firstCount) code count = memory basis code count := rfl

 def state (basis : State D Command) (code count : Int) : State D Command :=
  ⟨memory basis.memory code count, basis.datasets, 0, .initial⟩

@[simp] theorem state_memory (basis : State D Command) (code count : Int) :
    (state basis code count).memory = memory basis.memory code count := rfl

@[simp] theorem state_datasets (basis : State D Command) (code count : Int) :
    (state basis code count).datasets = basis.datasets := rfl

@[simp] theorem state_history (basis : State D Command) (code count : Int) :
    (state basis code count).history = 0 := rfl

@[simp] theorem state_action (basis : State D Command) (code count : Int) :
    (state basis code count).action = .initial := rfl

@[simp] theorem state_hidden (basis : State D Command) (code count : Int) :
    (state basis code count).memory.hidden = basis.memory.hidden := rfl

@[simp] theorem state_read_control (basis : State D Command) (code count : Int) :
    (state basis code count).memory.read LogCell.control.toVariable = some code := by
  exact memory_read_control basis.memory code count

@[simp] theorem state_read_commands (basis : State D Command) (code count : Int) :
    (state basis code count).memory.read LogCell.commands.toVariable = some count := by
  exact memory_read_commands basis.memory code count

 theorem state_read_invisible (basis : State D Command) (code count : Int)
    (x : Variable sort .invisible) :
    (state basis code count).memory.read x = basis.memory.read x := rfl

@[simp] theorem state_state (basis : State D Command)
    (firstCode firstCount code count : Int) :
    state (state basis firstCode firstCount) code count = state basis code count := rfl

 def seed (basis : State D Command) (code : Int) : World D Command :=
  World.start (memory basis.memory code 0) basis.datasets

@[simp] theorem seed_initial (basis : State D Command) (code : Int) :
    (seed basis code).initial = state basis code 0 := rfl

@[simp] theorem seed_rest (basis : State D Command) (code : Int) :
    (seed basis code).rest = [] := rfl

@[simp] theorem seed_current (basis : State D Command) (code : Int) :
    (seed basis code).current = state basis code 0 := rfl

@[simp] theorem seed_read_control (basis : State D Command) (code : Int) :
    (seed basis code).current.memory.read LogCell.control.toVariable = some code := by
  rw [seed_current, state_read_control]

@[simp] theorem seed_read_commands (basis : State D Command) (code : Int) :
    (seed basis code).current.memory.read LogCell.commands.toVariable = some 0 := by
  rw [seed_current, state_read_commands]

 def trace (basis : State D Command) (rows : List (Int × Nat)) :
    List (State D Command) :=
  rows.map (fun row => state basis row.1 (Int.ofNat row.2))

@[simp] theorem trace_nil (basis : State D Command) : trace basis [] = [] := rfl

@[simp] theorem trace_cons (basis : State D Command) (row : Int × Nat)
    (rows : List (Int × Nat)) :
    trace basis (row :: rows) = state basis row.1 (Int.ofNat row.2) :: trace basis rows := rfl

@[simp] theorem trace_singleton (basis : State D Command) (row : Int × Nat) :
    trace basis [row] = [state basis row.1 (Int.ofNat row.2)] := rfl

@[simp] theorem trace_length (basis : State D Command) (rows : List (Int × Nat)) :
    (trace basis rows).length = rows.length := by
  simp only [trace, List.length_map]

 theorem trace_append (basis : State D Command) (left right : List (Int × Nat)) :
    trace basis (left ++ right) = trace basis left ++ trace basis right := by
  simp only [trace, List.map_append]

 theorem trace_take (basis : State D Command) (rows : List (Int × Nat)) (j : Nat) :
    trace basis (rows.take j) = (trace basis rows).take j := by
  exact List.map_take

 theorem trace_getElem (basis : State D Command) (rows : List (Int × Nat))
    (j : Nat) (bound : j < rows.length) :
    (trace basis rows)[j]'(by simpa only [trace_length] using bound) =
      state basis (rows[j]'bound).1 (Int.ofNat (rows[j]'bound).2) := by
  simp only [trace, List.getElem_map]

 def world (basis : State D Command) (code : Int) (rows : List (Int × Nat)) :
    World D Command :=
  (seed basis code).appendStates (trace basis rows)

/-- `j` counts appended rows; zero denotes the real initial metadata state. -/
def prefixWorld (basis : State D Command) (code : Int) (rows : List (Int × Nat))
    (j : Nat) : World D Command :=
  (seed basis code).appendStates ((trace basis rows).take j)

@[simp] theorem world_initial (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) : (world basis code rows).initial = state basis code 0 := rfl

@[simp] theorem world_rest (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) : (world basis code rows).rest = trace basis rows := rfl

 theorem world_trace (basis : State D Command) (code : Int) (rows : List (Int × Nat)) :
    (world basis code rows).trace = state basis code 0 :: trace basis rows := rfl

@[simp] theorem world_nil (basis : State D Command) (code : Int) :
    world basis code [] = seed basis code := by
  simp only [world, trace_nil, World.appendStates_nil]

 theorem world_append (basis : State D Command) (code : Int)
    (left right : List (Int × Nat)) :
    world basis code (left ++ right) =
      (world basis code left).appendStates (trace basis right) := by
  simp only [world, trace_append, World.appendStates_assoc]

 theorem world_append_singleton (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) (row : Int × Nat) :
    world basis code (rows ++ [row]) =
      (world basis code rows).extend (state basis row.1 (Int.ofNat row.2)) := by
  rw [world_append, trace_singleton, World.appendStates_singleton]

 theorem world_current_getLast (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) (nonempty : rows ≠ []) :
    (world basis code rows).current =
      state basis (rows.getLast nonempty).1 (Int.ofNat (rows.getLast nonempty).2) := by
  have encodedNonempty : trace basis rows ≠ [] := by
    simpa [trace] using nonempty
  change ((seed basis code).appendStates (trace basis rows)).current = _
  rw [World.appendStates_current _ _ encodedNonempty]
  simp only [trace, List.getLast_map]

 theorem world_prefix (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) (j : Nat) :
    (world basis code rows).prefix j = prefixWorld basis code rows j := rfl

 theorem prefix_trace (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) (j : Nat) :
    (prefixWorld basis code rows j).trace =
      state basis code 0 :: (trace basis rows).take j := rfl

 theorem prefix_eq_world_take (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) (j : Nat) :
    prefixWorld basis code rows j = world basis code (rows.take j) := by
  simp only [prefixWorld, world, trace_take]

@[simp] theorem prefix_zero (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) : prefixWorld basis code rows 0 = seed basis code := by
  simp only [prefixWorld, World.appendStates_take_zero]

@[simp] theorem prefix_zero_current (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) :
    (prefixWorld basis code rows 0).current = state basis code 0 := by
  rw [prefix_zero, seed_current]

 theorem prefix_succ (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) (j : Nat) (bound : j < rows.length) :
    prefixWorld basis code rows (j + 1) =
      (prefixWorld basis code rows j).extend
        (state basis (rows[j]'bound).1 (Int.ofNat (rows[j]'bound).2)) := by
  have encodedBound : j < (trace basis rows).length := by
    simpa only [trace_length] using bound
  simpa only [prefixWorld, trace_getElem basis rows j bound] using
    World.appendStates_take_succ (seed basis code) (trace basis rows) j encodedBound

 theorem prefix_succ_current (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) (j : Nat) (bound : j < rows.length) :
    (prefixWorld basis code rows (j + 1)).current =
      state basis (rows[j]'bound).1 (Int.ofNat (rows[j]'bound).2) := by
  rw [prefix_succ basis code rows j bound, World.extend_current]

 theorem prefix_of_length_le (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) (j : Nat) (bound : rows.length ≤ j) :
    prefixWorld basis code rows j = world basis code rows := by
  rw [prefix_eq_world_take, List.take_of_length_le bound]

 theorem prefix_trace_prefix (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) (j : Nat) :
    (prefixWorld basis code rows j).trace <+: (world basis code rows).trace := by
  exact World.appendStates_take_trace_prefix (seed basis code) (trace basis rows) j

@[simp] theorem prefix_zero_read_control (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) :
    (prefixWorld basis code rows 0).current.memory.read LogCell.control.toVariable = some code := by
  rw [prefix_zero_current, state_read_control]

@[simp] theorem prefix_zero_read_commands (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) :
    (prefixWorld basis code rows 0).current.memory.read LogCell.commands.toVariable = some 0 := by
  rw [prefix_zero_current, state_read_commands]

 theorem prefix_succ_read_control (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) (j : Nat) (bound : j < rows.length) :
    (prefixWorld basis code rows (j + 1)).current.memory.read LogCell.control.toVariable =
      some (rows[j]'bound).1 := by
  rw [prefix_succ_current basis code rows j bound, state_read_control]

 theorem prefix_succ_read_commands (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) (j : Nat) (bound : j < rows.length) :
    (prefixWorld basis code rows (j + 1)).current.memory.read LogCell.commands.toVariable =
      some (Int.ofNat (rows[j]'bound).2) := by
  rw [prefix_succ_current basis code rows j bound, state_read_commands]

 theorem prefix_current_cases (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) (j : Nat) :
    (prefixWorld basis code rows j).current = state basis code 0 ∨
      ∃ row ∈ rows, (prefixWorld basis code rows j).current =
        state basis row.1 (Int.ofNat row.2) := by
  have member : (prefixWorld basis code rows j).current ∈
      (prefixWorld basis code rows j).trace := List.getLast_mem _
  rw [prefix_trace] at member
  rcases List.mem_cons.mp member with initial | appended
  · exact Or.inl initial
  · have encodedMember := List.mem_of_mem_take appended
    rcases List.mem_map.mp encodedMember with ⟨row, member, equal⟩
    exact Or.inr ⟨row, member, equal.symm⟩

 theorem prefix_current_invariants (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) (j : Nat) :
    (prefixWorld basis code rows j).current.memory.hidden = basis.memory.hidden ∧
      (prefixWorld basis code rows j).current.datasets = basis.datasets ∧
      (prefixWorld basis code rows j).current.history = 0 ∧
      (prefixWorld basis code rows j).current.action = .initial := by
  rcases prefix_current_cases basis code rows j with initial | ⟨row, _, appended⟩
  · rw [initial]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [appended]
    exact ⟨rfl, rfl, rfl, rfl⟩

 theorem prefix_current_read_invisible (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) (j : Nat) (x : Variable sort .invisible) :
    (prefixWorld basis code rows j).current.memory.read x = basis.memory.read x := by
  rcases prefix_current_cases basis code rows j with initial | ⟨row, _, appended⟩
  · rw [initial]
    rfl
  · rw [appended]
    rfl

 theorem world_constantHidden (basis : State D Command) (code : Int)
    (rows : List (Int × Nat)) : ConstantHidden (world basis code rows) := by
  intro metadata member
  rw [world_trace] at member
  rcases List.mem_cons.mp member with initial | appended
  · rw [initial]
    rfl
  · rcases List.mem_map.mp appended with ⟨row, _, equal⟩
    rw [← equal]
    rfl

section Evaluation

variable [MeasurableSpace D] {Γ : List GhostSort}

/-- Reading a successfully denoted ghost world needs no model-admission premise. -/
theorem evalTerm_valueRead_currentView (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command Γ) (view : SemanticView D)
    (term : AssertionTerm Γ .world) (world : World D Command)
    (evaluated : evalTerm interpretation model env view term = some world)
    (x : Variable sort visibility) :
    evalTerm interpretation model env view (.valueRead (.currentView term) x) =
      world.current.memory.read x := by
  simp only [evalTerm, evaluated, Option.map_some]
  change (Memory.assemble world.current.memory.observable world.current.memory.hidden).read x =
    world.current.memory.read x
  rw [Memory.assemble_projections]

 theorem evalTerm_appendWorld (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command Γ) (view : SemanticView D)
    (worldTerm : AssertionTerm Γ .world) (traceTerm : AssertionTerm Γ .trace)
    (world : World D Command) (states : List (State D Command))
    (worldEvaluated : evalTerm interpretation model env view worldTerm = some world)
    (traceEvaluated : evalTerm interpretation model env view traceTerm = some states) :
    evalTerm interpretation model env view (.appendWorld worldTerm traceTerm) =
      some (world.appendStates states) := by
  simp only [evalTerm, worldEvaluated, traceEvaluated, World.appendStates]
  rfl

 theorem evalTerm_traceTake_ofNat (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command Γ) (view : SemanticView D)
    (term : AssertionTerm Γ .trace) (states : List (State D Command)) (j : Nat)
    (evaluated : evalTerm interpretation model env view term = some states) :
    evalTerm interpretation model env view (.traceTake term (.integer (Int.ofNat j))) =
      some (states.take j) := by
  simp [evalTerm, evaluated]

 theorem evalTerm_appendWorld_traceTake (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command Γ) (view : SemanticView D)
    (worldTerm : AssertionTerm Γ .world) (traceTerm : AssertionTerm Γ .trace)
    (world : World D Command) (states : List (State D Command)) (j : Nat)
    (worldEvaluated : evalTerm interpretation model env view worldTerm = some world)
    (traceEvaluated : evalTerm interpretation model env view traceTerm = some states) :
    evalTerm interpretation model env view
      (.appendWorld worldTerm (.traceTake traceTerm (.integer (Int.ofNat j)))) =
      some (world.appendStates (states.take j)) := by
  exact evalTerm_appendWorld interpretation model env view worldTerm _ world _
    worldEvaluated (evalTerm_traceTake_ofNat interpretation model env view traceTerm states j
      traceEvaluated)

 theorem evalTerm_prefix_zero_control (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command Γ) (view : SemanticView D)
    (seedTerm : AssertionTerm Γ .world) (traceTerm : AssertionTerm Γ .trace)
    (basis : State D Command) (code : Int) (rows : List (Int × Nat))
    (seedEvaluated : evalTerm interpretation model env view seedTerm = some (seed basis code))
    (traceEvaluated : evalTerm interpretation model env view traceTerm = some (trace basis rows)) :
    evalTerm interpretation model env view
      (.valueRead (.currentView (.appendWorld seedTerm (.traceTake traceTerm (.integer 0))))
        LogCell.control.toVariable) = some code := by
  have evaluated := evalTerm_appendWorld_traceTake interpretation model env view seedTerm
    traceTerm (seed basis code) (trace basis rows) 0 seedEvaluated traceEvaluated
  simp only [show Int.ofNat 0 = 0 from rfl] at evaluated
  rw [evalTerm_valueRead_currentView interpretation model env view _ _ evaluated]
  exact prefix_zero_read_control basis code rows

 theorem evalTerm_prefix_zero_commands (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command Γ) (view : SemanticView D)
    (seedTerm : AssertionTerm Γ .world) (traceTerm : AssertionTerm Γ .trace)
    (basis : State D Command) (code : Int) (rows : List (Int × Nat))
    (seedEvaluated : evalTerm interpretation model env view seedTerm = some (seed basis code))
    (traceEvaluated : evalTerm interpretation model env view traceTerm = some (trace basis rows)) :
    evalTerm interpretation model env view
      (.valueRead (.currentView (.appendWorld seedTerm (.traceTake traceTerm (.integer 0))))
        LogCell.commands.toVariable) = some 0 := by
  have evaluated := evalTerm_appendWorld_traceTake interpretation model env view seedTerm
    traceTerm (seed basis code) (trace basis rows) 0 seedEvaluated traceEvaluated
  simp only [show Int.ofNat 0 = 0 from rfl] at evaluated
  rw [evalTerm_valueRead_currentView interpretation model env view _ _ evaluated]
  exact prefix_zero_read_commands basis code rows

 theorem evalTerm_prefix_succ_control (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command Γ) (view : SemanticView D)
    (seedTerm : AssertionTerm Γ .world) (traceTerm : AssertionTerm Γ .trace)
    (basis : State D Command) (code : Int) (rows : List (Int × Nat))
    (j : Nat) (bound : j < rows.length)
    (seedEvaluated : evalTerm interpretation model env view seedTerm = some (seed basis code))
    (traceEvaluated : evalTerm interpretation model env view traceTerm = some (trace basis rows)) :
    evalTerm interpretation model env view
      (.valueRead (.currentView (.appendWorld seedTerm
        (.traceTake traceTerm (.integer (Int.ofNat (j + 1))))))
        LogCell.control.toVariable) = some (rows[j]'bound).1 := by
  have evaluated := evalTerm_appendWorld_traceTake interpretation model env view seedTerm
    traceTerm (seed basis code) (trace basis rows) (j + 1) seedEvaluated traceEvaluated
  rw [evalTerm_valueRead_currentView interpretation model env view _ _ evaluated]
  exact prefix_succ_read_control basis code rows j bound

 theorem evalTerm_prefix_succ_commands (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command Γ) (view : SemanticView D)
    (seedTerm : AssertionTerm Γ .world) (traceTerm : AssertionTerm Γ .trace)
    (basis : State D Command) (code : Int) (rows : List (Int × Nat))
    (j : Nat) (bound : j < rows.length)
    (seedEvaluated : evalTerm interpretation model env view seedTerm = some (seed basis code))
    (traceEvaluated : evalTerm interpretation model env view traceTerm = some (trace basis rows)) :
    evalTerm interpretation model env view
      (.valueRead (.currentView (.appendWorld seedTerm
        (.traceTake traceTerm (.integer (Int.ofNat (j + 1))))))
        LogCell.commands.toVariable) = some (Int.ofNat (rows[j]'bound).2) := by
  have evaluated := evalTerm_appendWorld_traceTake interpretation model env view seedTerm
    traceTerm (seed basis code) (trace basis rows) (j + 1) seedEvaluated traceEvaluated
  rw [evalTerm_valueRead_currentView interpretation model env view _ _ evaluated]
  exact prefix_succ_read_commands basis code rows j bound

end Evaluation

end

end ControlMetadata

end Lara.BHL
