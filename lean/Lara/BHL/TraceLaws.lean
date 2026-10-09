import Lara.BHL.Trace

namespace Lara.BHL

 theorem traceEdges_append (dynamics : Dynamics D Command) (hidden : HiddenMemory)
    (before : Observation D Command) (front suffix : List (Observation D Command)) :
    TraceEdges dynamics hidden before (front ++ suffix) ↔
      TraceEdges dynamics hidden before front ∧
      TraceEdges dynamics hidden ((before :: front).getLast (by simp)) suffix := by
  induction front generalizing before with
  | nil => simp [TraceEdges]
  | cons first rest ih =>
      simp only [List.cons_append, TraceEdges]
      rw [ih]
      cases rest <;> simp [and_assoc]

 theorem traceEdges_take_drop (dynamics : Dynamics D Command) (hidden : HiddenMemory)
    (before : Observation D Command) (rest : List (Observation D Command)) (length : Nat) :
    TraceEdges dynamics hidden before rest ↔
      TraceEdges dynamics hidden before (rest.take length) ∧
      TraceEdges dynamics hidden
        ((before :: rest.take length).getLast (by simp)) (rest.drop length) := by
  have h := traceEdges_append dynamics hidden before (rest.take length) (rest.drop length)
  simpa only [List.take_append_drop] using h

 theorem traceEdges_prefix {dynamics : Dynamics D Command} {hidden : HiddenMemory}
    {before : Observation D Command} {front rest : List (Observation D Command)}
    (hp : front <+: rest) (h : TraceEdges dynamics hidden before rest) :
    TraceEdges dynamics hidden before front := by
  rcases hp with ⟨suffix, rfl⟩
  exact (traceEdges_append dynamics hidden before front suffix).mp h |>.1

 theorem traceEdges_take {dynamics : Dynamics D Command} {hidden : HiddenMemory}
    {before : Observation D Command} {rest : List (Observation D Command)}
    (h : TraceEdges dynamics hidden before rest) (length : Nat) :
    TraceEdges dynamics hidden before (rest.take length) :=
  (traceEdges_take_drop dynamics hidden before rest length).mp h |>.1

 theorem constantHidden_current {world : World D Command} (h : ConstantHidden world) :
    world.current.memory.hidden = world.initial.memory.hidden :=
  h world.current (List.getLast_mem (World.trace_nonempty world))

 theorem constantHidden_binding {world : World D Command} (h : ConstantHidden world)
    {state : State D Command} (hs : state ∈ world.trace)
    (x : Variable s .invisible) :
    state.memory.read x = world.initial.memory.read x :=
  congrArg (fun hidden : HiddenMemory => hidden s x.id) (h state hs)

 theorem admitted_start (dynamics : Dynamics D Command) (visible : VisibleState D)
    (hidden : HiddenMemory) (h : dynamics.initial hidden visible) :
    Admitted dynamics (World.start (Memory.assemble visible.memory hidden) visible.datasets) := by
  constructor
  · intro state hs
    simp only [World.start, World.trace, List.mem_singleton] at hs
    subst state
    rfl
  · simpa [TraceAllowed, TraceEdges, observeWorld, World.trace, World.start,
      observeState, Observation.visible, Memory.assemble] using h

 theorem admitted_current_hidden {dynamics : Dynamics D Command} {world : World D Command}
    (h : Admitted dynamics world) :
    world.current.memory.hidden = world.initial.memory.hidden :=
  constantHidden_current h.1

 theorem admitted_hidden {dynamics : Dynamics D Command} {world : World D Command}
    (h : Admitted dynamics world) {state : State D Command} (hs : state ∈ world.trace) :
    state.memory.hidden = world.initial.memory.hidden :=
  h.1 state hs

 theorem admitted_current_hidden_binding {dynamics : Dynamics D Command}
    {world : World D Command} (h : Admitted dynamics world) (x : Variable s .invisible) :
    world.current.memory.read x = world.initial.memory.read x :=
  congrArg (fun hidden : HiddenMemory => hidden s x.id) (admitted_current_hidden h)

 theorem admitted_initial {dynamics : Dynamics D Command} {world : World D Command}
    (h : Admitted dynamics world) :
    world.initial.action = .initial ∧
      dynamics.initial world.initial.memory.hidden world.initial.visible := by
  have ha := h.2
  change world.initial.history = 0 ∧ world.initial.action = .initial ∧
    dynamics.initial world.initial.memory.hidden world.initial.visible ∧
    TraceEdges dynamics world.initial.memory.hidden (observeState world.initial)
      (world.rest.map observeState) at ha
  exact ⟨ha.2.1, ha.2.2.1⟩

 theorem constantHidden_prefix {world : World D Command} (h : ConstantHidden world)
    (length : Nat) : ConstantHidden (world.prefix length) := by
  intro state hs
  apply h state
  change state ∈ world.initial :: world.rest.take length at hs
  change state ∈ world.initial :: world.rest
  rcases List.mem_cons.mp hs with hi | hr
  · exact List.mem_cons.mpr (Or.inl hi)
  · exact List.mem_cons.mpr (Or.inr (List.mem_of_mem_take hr))

 theorem admitted_prefix {dynamics : Dynamics D Command} {world : World D Command}
    (h : Admitted dynamics world) (length : Nat) :
    Admitted dynamics (world.prefix length) := by
  refine ⟨constantHidden_prefix h.1 length, ?_⟩
  have ha := h.2
  change world.initial.history = 0 ∧ world.initial.action = .initial ∧
    dynamics.initial world.initial.memory.hidden world.initial.visible ∧
    TraceEdges dynamics world.initial.memory.hidden (observeState world.initial)
      (world.rest.map observeState) at ha
  change world.initial.history = 0 ∧ world.initial.action = .initial ∧
    dynamics.initial world.initial.memory.hidden world.initial.visible ∧
    TraceEdges dynamics world.initial.memory.hidden (observeState world.initial)
      ((world.rest.take length).map observeState)
  refine ⟨ha.1, ha.2.1, ha.2.2.1, ?_⟩
  simpa only [List.map_take] using traceEdges_take ha.2.2.2 length

 theorem constantHidden_extend {world : World D Command} {after : State D Command}
    (h : ConstantHidden world)
    (hidden : after.memory.hidden = world.initial.memory.hidden) :
    ConstantHidden (world.extend after) := by
  intro state hs
  rw [World.extend_trace] at hs
  rcases List.mem_append.mp hs with hold | hnew
  · exact h state hold
  · have heq := List.mem_singleton.mp hnew
    subst state
    exact hidden

 theorem admitted_extend {dynamics : Dynamics D Command} {world : World D Command}
    (h : Admitted dynamics world) (after : State D Command)
    (hidden : after.memory.hidden = world.initial.memory.hidden)
    (edge : AllowedEdge dynamics world.initial.memory.hidden
      (observeState world.current) (observeState after)) :
    Admitted dynamics (world.extend after) := by
  refine ⟨constantHidden_extend h.1 hidden, ?_⟩
  have ha := h.2
  change world.initial.history = 0 ∧ world.initial.action = .initial ∧
    dynamics.initial world.initial.memory.hidden world.initial.visible ∧
    TraceEdges dynamics world.initial.memory.hidden (observeState world.initial)
      (world.rest.map observeState) at ha
  change world.initial.history = 0 ∧ world.initial.action = .initial ∧
    dynamics.initial world.initial.memory.hidden world.initial.visible ∧
    TraceEdges dynamics world.initial.memory.hidden (observeState world.initial)
      ((world.rest ++ [after]).map observeState)
  refine ⟨ha.1, ha.2.1, ha.2.2.1, ?_⟩
  rw [List.map_append]
  apply (traceEdges_append dynamics world.initial.memory.hidden
    (observeState world.initial) (world.rest.map observeState) [observeState after]).mpr
  refine ⟨ha.2.2.2, ?_⟩
  have last : ((observeState world.initial :: world.rest.map observeState).getLast
      (by simp)) = observeState world.current := observe_current world
  simpa only [last, TraceEdges, and_true] using edge

 theorem traceAllowed_extend (dynamics : Dynamics D Command) (hidden : HiddenMemory)
    (world : World D Command) (after : State D Command) :
    TraceAllowed dynamics hidden (observeWorld (world.extend after)) ↔
      TraceAllowed dynamics hidden (observeWorld world) ∧
        AllowedEdge dynamics hidden (observeState world.current) (observeState after) := by
  change (world.initial.history = 0 ∧ world.initial.action = .initial ∧
    dynamics.initial hidden world.initial.visible ∧
    TraceEdges dynamics hidden (observeState world.initial)
      ((world.rest ++ [after]).map observeState)) ↔
    (world.initial.history = 0 ∧ world.initial.action = .initial ∧
      dynamics.initial hidden world.initial.visible ∧
      TraceEdges dynamics hidden (observeState world.initial) (world.rest.map observeState)) ∧
      AllowedEdge dynamics hidden (observeState world.current) (observeState after)
  rw [List.map_append, traceEdges_append]
  have last : ((observeState world.initial :: world.rest.map observeState).getLast
      (by simp)) = observeState world.current := observe_current world
  simp only [last, List.map_singleton, TraceEdges, and_true, and_assoc]

 theorem traceEdges_sample {dynamics : Dynamics D Command} {hidden : HiddenMemory}
    {initial : State D Command} {rest : List (State D Command)}
    (h : TraceEdges dynamics hidden (observeState initial) (rest.map observeState))
    {after : State D Command} (ha : after ∈ rest) {data : D} {population : PopulationId}
    (action : after.action = .sample data population) :
    ∃ before ∈ initial :: rest,
      dynamics.sampling hidden before.visible after.visible data population ∧
      after.history = before.history := by
  revert h ha action
  induction rest generalizing initial with
  | nil =>
      intro h ha action
      simp at ha
  | cons first rest ih =>
      intro h ha action
      change AllowedEdge dynamics hidden (observeState initial) (observeState first) ∧
        TraceEdges dynamics hidden (observeState first) (rest.map observeState) at h
      rcases List.mem_cons.mp ha with heq | hrest
      · subst after
        refine ⟨initial, List.mem_cons_self, ?_⟩
        have edge := h.1
        simp only [AllowedEdge, observeState, action] at edge
        exact edge
      · obtain ⟨before, hb, sampling, history⟩ := ih h.2 hrest action
        refine ⟨before, ?_, sampling, history⟩
        rcases List.mem_cons.mp hb with heq | hbefore
        · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl heq)))
        · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr hbefore)))

 theorem admitted_sample_transition {dynamics : Dynamics D Command}
    {world : World D Command} (h : Admitted dynamics world)
    {after : State D Command} (ha : after ∈ world.rest) {data : D}
    {population : PopulationId} (action : after.action = .sample data population) :
    ∃ before ∈ world.trace,
      dynamics.sampling world.initial.memory.hidden before.visible after.visible data population ∧
      after.history = before.history := by
  have hedges := h.2
  change world.initial.history = 0 ∧ world.initial.action = .initial ∧
    dynamics.initial world.initial.memory.hidden world.initial.visible ∧
    TraceEdges dynamics world.initial.memory.hidden (observeState world.initial)
      (world.rest.map observeState) at hedges
  exact traceEdges_sample hedges.2.2.2 ha action

end Lara.BHL
