import Lara.BHL.Trace

namespace Lara.BHL

/-- The model is a local dynamics plus independently inhabited initial evidence.
Its world class is derived from the complete local trace conditions. -/
structure Model (D Command : Type) where
  dynamics : Dynamics D Command
  initial_nonempty : ∃ hidden visible, dynamics.initial hidden visible

def Model.worlds (model : Model D Command) : Set (World D Command) :=
  {world | Admitted model.dynamics world}

abbrev Model.ValidWorld (model : Model D Command) := {world // world ∈ model.worlds}

def compatibleHidden (dynamics : Dynamics D Command) (world : World D Command) :
    Set HiddenMemory := {hidden | TraceAllowed dynamics hidden (observeWorld world)}

/-- Change only ordinary hidden bindings, preserving all actual observations. -/
def State.withHidden (state : State D Command) (hidden : HiddenMemory) : State D Command :=
  {state with memory := Memory.assemble state.memory.observable hidden}

def World.rebuildHidden (world : World D Command) (hidden : HiddenMemory) : World D Command :=
  ⟨world.initial.withHidden hidden, world.rest.map (fun state => state.withHidden hidden),
    world.initial_history_empty⟩

/-- Ambient assertions expose this semantic view, not raw trace order, actions,
or length. Ghost worlds retain their own traces. The hidden possibility set is
derived from the complete ordered reference observations. -/
structure SemanticView (D : Type) where
  visible : VisibleState D
  history : History D
  hidden : HiddenMemory
  compatible : Set HiddenMemory
  provenance : Multiset (D × PopulationId)

def semanticView (dynamics : Dynamics D Command) (world : World D Command) : SemanticView D :=
  ⟨world.current.visible, world.current.history, world.current.memory.hidden,
    compatibleHidden dynamics world, world.samplingProvenance⟩

/-- Only views realized by admitted worlds belong to the semantic carrier. -/
def Model.views (model : Model D Command) : Set (SemanticView D) :=
  {view | ∃ world : model.ValidWorld, semanticView model.dynamics world.val = view}

abbrev Model.ValidView (model : Model D Command) := {view // view ∈ model.views}

def Model.viewOf (model : Model D Command) (world : model.ValidWorld) : model.ValidView :=
  ⟨semanticView model.dynamics world.val, ⟨world, rfl⟩⟩

/-- Equality of observable view components; ordinary hidden memory can vary. -/
def ViewAccessible (left right : SemanticView D) : Prop :=
  left.visible = right.visible ∧ left.history = right.history ∧
    left.compatible = right.compatible ∧ left.provenance = right.provenance

end Lara.BHL
