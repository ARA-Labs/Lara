import Lara.Process.Order

/-!
An explicit W3C PROV projection of a process history.

`provGraph` keeps the PROV core relations a process history determines:
`used` (an activity used an entity), `wasAssociatedWith` (an activity and its
agent), `hadPlan` (a run and the plan version it followed), `wasGeneratedBy`
(a result and the run that produced it) and `wasInvalidatedBy` for
retractions. It deliberately omits the relative order of events, the purpose
of a data access, the dataset versions a run used, a run's statistical family,
claim assertions and dataset updates. Relations are kept as lists and compared as sets
(`ProvGraph.Equiv`), which is how a PROV graph is read.

This is one specified projection, used to show that it erases distinctions
entitlement depends on (`Lara.Examples.ProcessAdequacy.prov_separates`). It is
not a claim that every PROV encoding must erase them: qualified PROV with
timestamps and roles can retain them.
-/

namespace Lara.Process

/-- A PROV activity: a plan commitment, a data access or a run. -/
inductive ProvActivity where
  | commit (plan : PlanId) (version : VersionId)
  | access (event : EventId)
  | run (run : RunId)
  deriving DecidableEq, Repr

/-- A PROV entity: a dataset or a result. -/
inductive ProvEntity where
  | data (data : DataId)
  | result (run : RunId) (outcome : Nat)
  deriving DecidableEq, Repr

/-- The PROV relations of one event. -/
structure ProvFacts where
  used : List (ProvActivity × ProvEntity)
  associated : List (ProvActivity × ActorId)
  plans : List (RunId × PlanId × VersionId)
  generated : List (ProvEntity × ProvActivity)
  invalidated : List SourceId
  deriving DecidableEq, Repr

def Event.prov (id : EventId) : Event → ProvFacts
  | .commitPlan actor plan version => ⟨[], [(.commit plan version, actor)], [], [], []⟩
  | .access actor data _ => ⟨[(.access id, .data data)], [(.access id, actor)], [], [], []⟩
  | .run r p v ins _ => ⟨ins.map fun i => (.run r, .data i.1), [], [(r, p, v)], [], []⟩
  | .result r outcome => ⟨[], [], [], [(.result r outcome, .run r)], []⟩
  | .retract source => ⟨[], [], [], [], [source]⟩
  | _ => ⟨[], [], [], [], []⟩

/-- The PROV graph of a history, as relation sets. -/
structure ProvGraph where
  used : List (ProvActivity × ProvEntity)
  associated : List (ProvActivity × ActorId)
  plans : List (RunId × PlanId × VersionId)
  generated : List (ProvEntity × ProvActivity)
  invalidated : List SourceId
  deriving DecidableEq, Repr

/-- The projection keeps relation membership and forgets event order and access
purpose. Relations are compared as sets (`ProvGraph.Equiv`). -/
def provGraph (h : ProcessHistory) : ProvGraph :=
  let facts := h.map fun e => e.event.prov e.id
  ⟨facts.flatMap ProvFacts.used, facts.flatMap ProvFacts.associated,
    facts.flatMap ProvFacts.plans, facts.flatMap ProvFacts.generated,
    facts.flatMap ProvFacts.invalidated⟩

/-- Two PROV graphs are equivalent when every relation has the same members. -/
def ProvGraph.Equiv (g g' : ProvGraph) : Prop :=
  (∀ x, x ∈ g.used ↔ x ∈ g'.used) ∧ (∀ x, x ∈ g.associated ↔ x ∈ g'.associated) ∧
    (∀ x, x ∈ g.plans ↔ x ∈ g'.plans) ∧ (∀ x, x ∈ g.generated ↔ x ∈ g'.generated) ∧
    (∀ x, x ∈ g.invalidated ↔ x ∈ g'.invalidated)

/-- A permutation of a history has an equivalent PROV graph: the projection
forgets order. -/
theorem provGraph_perm {h h' : ProcessHistory} (perm : h.Perm h') :
    (provGraph h).Equiv (provGraph h') := by
  have facts := perm.map fun e : Stamped => e.event.prov e.id
  have mem : ∀ {β : Type} (f : ProvFacts → List β) (x : β),
      x ∈ (h.map fun e => e.event.prov e.id).flatMap f ↔
        x ∈ (h'.map fun e => e.event.prov e.id).flatMap f := by
    intro β f x
    simp only [List.mem_flatMap]
    exact ⟨fun ⟨a, ha, hx⟩ => ⟨a, facts.mem_iff.mp ha, hx⟩,
      fun ⟨a, ha, hx⟩ => ⟨a, facts.mem_iff.mpr ha, hx⟩⟩
  exact ⟨mem _, mem _, mem _, mem _, mem _⟩

end Lara.Process
