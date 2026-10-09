import Lara.BHL.Model
import Lara.BHL.TraceLaws

namespace Lara.BHL

@[simp] theorem observeState_withHidden (state : State D Command) (hidden : HiddenMemory) :
    observeState (state.withHidden hidden) = observeState state := rfl

@[simp] theorem State.withHidden_visible (state : State D Command) (hidden : HiddenMemory) :
    (state.withHidden hidden).visible = state.visible := rfl

@[simp] theorem State.withHidden_hidden (state : State D Command) (hidden : HiddenMemory) :
    (state.withHidden hidden).memory.hidden = hidden := rfl

@[simp] theorem State.withHidden_history (state : State D Command) (hidden : HiddenMemory) :
    (state.withHidden hidden).history = state.history := rfl

@[simp] theorem World.rebuildHidden_trace (world : World D Command) (hidden : HiddenMemory) :
    (world.rebuildHidden hidden).trace = world.trace.map (fun state => state.withHidden hidden) :=
  rfl

@[simp] theorem World.rebuildHidden_current (world : World D Command)
    (hidden : HiddenMemory) :
    (world.rebuildHidden hidden).current = world.current.withHidden hidden := by
  simp [World.current, World.rebuildHidden_trace]

@[simp] theorem World.rebuildHidden_initial_hidden (world : World D Command)
    (hidden : HiddenMemory) :
    (world.rebuildHidden hidden).initial.memory.hidden = hidden := rfl

@[simp] theorem World.rebuildHidden_current_hidden (world : World D Command)
    (hidden : HiddenMemory) :
    (world.rebuildHidden hidden).current.memory.hidden = hidden := by
  rw [World.rebuildHidden_current, State.withHidden_hidden]

@[simp] theorem observe_rebuildHidden (world : World D Command) (hidden : HiddenMemory) :
    observeWorld (world.rebuildHidden hidden) = observeWorld world := by
  simp [observeWorld, World.rebuildHidden_trace, List.map_map]

 theorem rebuildHidden_accessible (world : World D Command) (hidden : HiddenMemory) :
    Accessible world (world.rebuildHidden hidden) :=
  (observe_rebuildHidden world hidden).symm

@[simp] theorem World.rebuildHidden_samplingProvenance (world : World D Command)
    (hidden : HiddenMemory) :
    (world.rebuildHidden hidden).samplingProvenance = world.samplingProvenance :=
  accessible_sampling_provenance (accessible_symm (rebuildHidden_accessible world hidden))

 theorem constantHidden_rebuildHidden (world : World D Command) (hidden : HiddenMemory) :
    ConstantHidden (world.rebuildHidden hidden) := by
  intro state hstate
  rw [World.rebuildHidden_trace] at hstate
  rcases List.mem_map.mp hstate with ⟨original, _, rfl⟩
  rfl

 theorem admitted_rebuildHidden_iff (dynamics : Dynamics D Command)
    (world : World D Command) (hidden : HiddenMemory) :
    Admitted dynamics (world.rebuildHidden hidden) ↔ hidden ∈ compatibleHidden dynamics world := by
  change ConstantHidden (world.rebuildHidden hidden) ∧
      TraceAllowed dynamics (world.rebuildHidden hidden).initial.memory.hidden
        (observeWorld (world.rebuildHidden hidden)) ↔
    TraceAllowed dynamics hidden (observeWorld world)
  rw [World.rebuildHidden_initial_hidden, observe_rebuildHidden]
  exact ⟨And.right, fun h => ⟨constantHidden_rebuildHidden world hidden, h⟩⟩

 theorem admitted_initial_hidden_mem_compatible {dynamics : Dynamics D Command}
    {world : World D Command} (h : Admitted dynamics world) :
    world.initial.memory.hidden ∈ compatibleHidden dynamics world := h.2

 theorem admitted_hidden_mem_compatible {dynamics : Dynamics D Command}
    {world : World D Command} (h : Admitted dynamics world) :
    world.current.memory.hidden ∈ compatibleHidden dynamics world := by
  rw [admitted_current_hidden h]
  exact admitted_initial_hidden_mem_compatible h

 theorem model_has_world (model : Model D Command) :
    ∃ world, world ∈ model.worlds := by
  rcases model.initial_nonempty with ⟨hidden, visible, hinitial⟩
  exact ⟨World.start (Memory.assemble visible.memory hidden) visible.datasets,
    admitted_start model.dynamics visible hidden hinitial⟩

 theorem Model.validWorld_nonempty (model : Model D Command) : Nonempty model.ValidWorld := by
  rcases model_has_world model with ⟨world, hworld⟩
  exact ⟨⟨world, hworld⟩⟩

 theorem compatibleHidden_eq_of_accessible {dynamics : Dynamics D Command}
    {left right : World D Command} (h : Accessible left right) :
    compatibleHidden dynamics left = compatibleHidden dynamics right := by
  unfold compatibleHidden
  rw [show observeWorld left = observeWorld right from h]

@[simp] theorem compatibleHidden_rebuildHidden (dynamics : Dynamics D Command)
    (world : World D Command) (hidden : HiddenMemory) :
    compatibleHidden dynamics (world.rebuildHidden hidden) = compatibleHidden dynamics world :=
  compatibleHidden_eq_of_accessible (accessible_symm (rebuildHidden_accessible world hidden))

 theorem compatibleHidden_extend_command (dynamics : Dynamics D Command)
    (world : World D Command) (after : State D Command) (command : Command)
    (action : after.action = .command command)
    (effect : ∃ delta, dynamics.command command world.current.visible =
      some (after.visible, delta) ∧ after.history = world.current.history + delta) :
    compatibleHidden dynamics (world.extend after) = compatibleHidden dynamics world := by
  ext hidden
  change TraceAllowed dynamics hidden (observeWorld (world.extend after)) ↔
    TraceAllowed dynamics hidden (observeWorld world)
  rw [traceAllowed_extend]
  have edge : AllowedEdge dynamics hidden (observeState world.current) (observeState after) := by
    simp only [AllowedEdge, observeState, action]
    exact effect
  simp only [edge, and_true]

 theorem accessible_current_visible {left right : World D Command}
    (h : Accessible left right) : left.current.visible = right.current.visible :=
  congrArg Observation.visible (accessible_current_observation h)

 theorem view_accessible_forth (dynamics : Dynamics D Command)
    {left right : World D Command} (h : Accessible left right) :
    ViewAccessible (semanticView dynamics left) (semanticView dynamics right) :=
  ⟨accessible_current_visible h, accessible_history_eq h,
    compatibleHidden_eq_of_accessible h, accessible_sampling_provenance h⟩

@[simp] theorem semanticView_rebuildHidden (dynamics : Dynamics D Command)
    (world : World D Command) (hidden : HiddenMemory) :
    semanticView dynamics (world.rebuildHidden hidden) =
      {semanticView dynamics world with hidden := hidden} := by
  simp only [semanticView, World.rebuildHidden_current, State.withHidden_visible,
    State.withHidden_history, State.withHidden_hidden, compatibleHidden_rebuildHidden,
    World.rebuildHidden_samplingProvenance]

 theorem view_accessible_back {dynamics : Dynamics D Command}
    {source target : World D Command}
    (htarget : Admitted dynamics target)
    (hview : ViewAccessible (semanticView dynamics source) (semanticView dynamics target)) :
    ∃ rebuilt, Admitted dynamics rebuilt ∧ Accessible source rebuilt ∧
      semanticView dynamics rebuilt = semanticView dynamics target := by
  change source.current.visible = target.current.visible ∧
    source.current.history = target.current.history ∧
    compatibleHidden dynamics source = compatibleHidden dynamics target ∧
    source.samplingProvenance = target.samplingProvenance at hview
  rcases hview with ⟨hvisible, hhistory, hcompatible, hprovenance⟩
  refine ⟨source.rebuildHidden target.current.memory.hidden, ?_,
    rebuildHidden_accessible source target.current.memory.hidden, ?_⟩
  · apply (admitted_rebuildHidden_iff dynamics source target.current.memory.hidden).2
    rw [hcompatible]
    exact admitted_hidden_mem_compatible htarget
  · rw [semanticView_rebuildHidden]
    change SemanticView.mk source.current.visible source.current.history
        target.current.memory.hidden (compatibleHidden dynamics source) source.samplingProvenance =
      SemanticView.mk target.current.visible target.current.history
        target.current.memory.hidden (compatibleHidden dynamics target) target.samplingProvenance
    rw [hvisible, hhistory, hcompatible, hprovenance]

 theorem view_accessible_refl (view : SemanticView D) : ViewAccessible view view :=
  ⟨rfl, rfl, rfl, rfl⟩

 theorem view_accessible_symm {left right : SemanticView D} (h : ViewAccessible left right) :
    ViewAccessible right left :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

 theorem view_accessible_trans {left middle right : SemanticView D}
    (h₁ : ViewAccessible left middle) (h₂ : ViewAccessible middle right) :
    ViewAccessible left right :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
    h₁.2.2.2.trans h₂.2.2.2⟩

 theorem view_accessible_equivalence : Equivalence (ViewAccessible (D := D)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro view
    exact view_accessible_refl view
  · intro left right h
    exact view_accessible_symm h
  · intro left middle right h₁ h₂
    exact view_accessible_trans h₁ h₂

 theorem Model.accessible_refl (model : Model D Command) (world : model.ValidWorld) :
    Accessible world.val world.val :=
  Lara.BHL.accessible_refl world.val

 theorem Model.accessible_symm (model : Model D Command) {left right : model.ValidWorld}
    (h : Accessible left.val right.val) : Accessible right.val left.val :=
  Lara.BHL.accessible_symm h

 theorem Model.accessible_trans (model : Model D Command)
    {left middle right : model.ValidWorld}
    (h₁ : Accessible left.val middle.val) (h₂ : Accessible middle.val right.val) :
    Accessible left.val right.val :=
  Lara.BHL.accessible_trans h₁ h₂

 theorem Model.accessible_equivalence (model : Model D Command) :
    Equivalence (fun left right : model.ValidWorld => Accessible left.val right.val) := by
  refine ⟨?_, ?_, ?_⟩
  · intro world
    exact model.accessible_refl world
  · intro left right h
    exact model.accessible_symm h
  · intro left middle right h₁ h₂
    exact model.accessible_trans h₁ h₂

 theorem Model.view_accessible_forth (model : Model D Command)
    {left right : model.ValidWorld} (h : Accessible left.val right.val) :
    ViewAccessible (semanticView model.dynamics left.val)
      (semanticView model.dynamics right.val) :=
  Lara.BHL.view_accessible_forth model.dynamics h

 theorem Model.view_accessible_back (model : Model D Command)
    {source target : model.ValidWorld}
    (hview : ViewAccessible (semanticView model.dynamics source.val)
      (semanticView model.dynamics target.val)) :
    ∃ rebuilt : model.ValidWorld, Accessible source.val rebuilt.val ∧
      semanticView model.dynamics rebuilt.val = semanticView model.dynamics target.val := by
  rcases Lara.BHL.view_accessible_back target.property hview with
    ⟨rebuilt, hadmitted, haccessible, hsemantic⟩
  exact ⟨⟨rebuilt, hadmitted⟩, haccessible, hsemantic⟩

 theorem Model.viewOf_surjective (model : Model D Command) :
    Function.Surjective model.viewOf := by
  intro view
  rcases view.property with ⟨world, hworld⟩
  exact ⟨world, Subtype.ext hworld⟩

 theorem Model.validView_nonempty (model : Model D Command) : Nonempty model.ValidView := by
  rcases model.validWorld_nonempty with ⟨world⟩
  exact ⟨model.viewOf world⟩

 theorem Model.viewOf_forth (model : Model D Command)
    {left right : model.ValidWorld} (h : Accessible left.val right.val) :
    ViewAccessible (model.viewOf left).val (model.viewOf right).val :=
  model.view_accessible_forth h

 theorem Model.viewOf_back (model : Model D Command) (source : model.ValidWorld)
    (target : model.ValidView)
    (h : ViewAccessible (model.viewOf source).val target.val) :
    ∃ rebuilt : model.ValidWorld, Accessible source.val rebuilt.val ∧
      model.viewOf rebuilt = target := by
  rcases target.property with ⟨targetWorld, htarget⟩
  have hv : ViewAccessible (semanticView model.dynamics source.val)
      (semanticView model.dynamics targetWorld.val) := by
    simpa only [Model.viewOf, htarget] using h
  rcases model.view_accessible_back hv with ⟨rebuilt, hr, heq⟩
  exact ⟨rebuilt, hr, Subtype.ext (heq.trans htarget)⟩

end Lara.BHL
