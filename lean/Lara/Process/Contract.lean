import Lara.Process.Vocabulary
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

/-!
The reference contract of the research-process layer: what a record means.

A record denotes the complete modeled histories it could have come from. The
carrier ranges over pairs of a history and a reporting choice, because a
semantics that ignores the reporting protocol answers conditioning questions
wrongly (Grünwald–Halpern's Monty Hall analysis). `compat` describes completions
of the unobserved *past* only; continuing a history into the *future* is the
separate `FutureSemantics.continues` relation.

Two verdict functions are defined. `verdictOf` is the classical reference over
an arbitrary carrier. `verdict` is the executable version over a declared
finite carrier with decidable predicates.

The witness quantifiers are frozen here as well. `EntitledBy` asks for *some*
warrant in every compatible history; `ArgumentEntitledBy` fixes *one* submitted
witness and asks for it in every compatible history. Both require a nonempty
compatible set. A finite carrier is a model
assumption with an explicit horizon, never something inferred from a short
record.
-/

namespace Lara.Process

universe u v w

/-! ### Record semantics -/

/-- A record semantics: which complete objects `X` a record `R` is compatible
with. Finiteness and decidability are supplied as instances where a verdict is
computed, not assumed by the structure. -/
structure RecordSemantics (X : Type u) (R : Type v) where
  compat : R → X → Prop

/-- Future continuation is a separate relation from past completion: `continues
h h'` says `h'` extends `h` with later events. -/
structure FutureSemantics (H : Type u) where
  continues : H → H → Prop

/-- A process model: which histories are valid executions, and the decoded record
each history yields under each reporting choice. -/
structure ProcessModel (H : Type u) (Rho : Type v) (R : Type w) where
  Valid : H → Prop
  Report : H → Rho → R

/-- Admitted omission/reporting assumptions over histories and reporting
choices. -/
structure Assumptions (H : Type u) (Rho : Type v) where
  Allowed : H → Rho → Prop

namespace Assumptions

variable {H : Type u} {Rho : Type v}

/-- No restriction at all. -/
def trivial : Assumptions H Rho := ⟨fun _ _ => True⟩

/-- Conjunction of two assumption sets. -/
def and (A B : Assumptions H Rho) : Assumptions H Rho :=
  ⟨fun h rho => A.Allowed h rho ∧ B.Allowed h rho⟩

/-- Assumption strength is inclusion of allowed pairs, not a constructor order. -/
def Stronger (A B : Assumptions H Rho) : Prop :=
  ∀ h rho, A.Allowed h rho → B.Allowed h rho

end Assumptions

variable {H : Type u} {Rho : Type v} {R : Type w}

/-- `Compatible M A r (h, rho)`: `h` is a valid history, the reporting choice is
allowed by the admitted assumptions, and that choice reports exactly `r`. -/
def Compatible (M : ProcessModel H Rho R) (A : Assumptions H Rho) (r : R)
    (x : H × Rho) : Prop :=
  M.Valid x.1 ∧ A.Allowed x.1 x.2 ∧ M.Report x.1 x.2 = r

/-- The compatible completions of a record, as a set. -/
def Completions (M : ProcessModel H Rho R) (A : Assumptions H Rho) (r : R) : Set (H × Rho) :=
  {x | Compatible M A r x}

/-- The record semantics a process model and its admitted assumptions induce. -/
def ProcessModel.semantics (M : ProcessModel H Rho R) (A : Assumptions H Rho) :
    RecordSemantics (H × Rho) R :=
  ⟨Compatible M A⟩

instance (M : ProcessModel H Rho R) (A : Assumptions H Rho) (r : R) (x : H × Rho)
    [DecidablePred M.Valid] [∀ h, DecidablePred (A.Allowed h)] [DecidableEq R] :
    Decidable (Compatible M A r x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ### Verdicts -/

section Verdict

variable {X : Type u}

/-- The classical reference verdict of a compatibility predicate on a property.
The empty-set check comes first, so an inconsistent record never receives a
positive answer. -/
noncomputable def verdictOf (compat : X → Prop) (φ : X → Prop) : Verdict := by
  classical
  exact
    if ¬ ∃ x, compat x then .inconsistent
    else if ∀ x, compat x → φ x then .certainTrue
    else if ∀ x, compat x → ¬ φ x then .certainFalse
    else .unknown

/-- The executable verdict over a declared finite carrier. -/
def verdict [Fintype X] (compat : X → Prop) [DecidablePred compat]
    (φ : X → Prop) [DecidablePred φ] : Verdict :=
  if ¬ ∃ x, compat x then .inconsistent
  else if ∀ x, compat x → φ x then .certainTrue
  else if ∀ x, compat x → ¬ φ x then .certainFalse
  else .unknown

end Verdict

/-! ### Witness quantifiers -/

section Witness

variable {X : Type u} {W : Type v}

/-- Claim-level entitlement: the compatible set is nonempty and each compatible
history has *some* warranting witness, possibly a different one in each. -/
def EntitledBy (compat : X → Prop) (warranted : X → W → Prop) : Prop :=
  (∃ x, compat x) ∧ ∀ x, compat x → ∃ w, warranted x w

/-- Submitted-argument entitlement: the compatible set is nonempty and the one
fixed witness `w` warrants in every compatible history. -/
def ArgumentEntitledBy (compat : X → Prop) (warranted : X → W → Prop) (w : W) : Prop :=
  (∃ x, compat x) ∧ ∀ x, compat x → warranted x w

end Witness

/-! ### Scoped coverage over process histories -/

/-- The family restriction of a scope: unrestricted, or the event is a run of
that family. -/
def CoverageScope.familyOk (scope : CoverageScope) (event : Event) : Bool :=
  match scope.family with
  | none => true
  | some family => event.family? == some family

/-- The actor restriction of a scope: unrestricted, or the event has an actor
in the list. An event without an actor is outside an actor-restricted scope. -/
def CoverageScope.actorOk (scope : CoverageScope) (event : Event) : Bool :=
  match scope.actors, event.actor? with
  | none, _ => true
  | some actors, some actor => actors.contains actor
  | some _, none => false

/-- The dataset restriction of a scope: unrestricted, or the event touches at
least one dataset and only datasets in the list. -/
def CoverageScope.dataOk (scope : CoverageScope) (event : Event) : Bool :=
  match scope.data with
  | none => true
  | some data => !event.data.isEmpty && event.data.all data.contains

/-- Whether the event at position `index` of a history lies in a coverage scope:
before the cutoff, of a listed kind, and within every restriction. -/
def CoverageScope.Contains (scope : CoverageScope) (index : Nat) (event : Stamped) : Prop :=
  index < scope.cutoff ∧ event.event.kind ∈ scope.kinds ∧ scope.familyOk event.event = true ∧
    scope.actorOk event.event = true ∧ scope.dataOk event.event = true

instance (scope : CoverageScope) (index : Nat) (event : Stamped) :
    Decidable (scope.Contains index event) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The in-scope events of a history, with their positions. -/
def CoverageScope.events (scope : CoverageScope) (h : ProcessHistory) : List Stamped :=
  ((List.range h.length).zip h).filterMap fun (index, event) =>
    if scope.Contains index event then some event else none

/-- The meaning of a scoped coverage assumption for a complete history `h` and
the events `reported` that its reporting choice exposes. A declared policy is
read through the model's interpretation `policy`. -/
def RecordCoverage.Allowed {Policy : Type}
    (policy : Policy → ProcessHistory → List Stamped → Prop) :
    RecordCoverage Policy → ProcessHistory → List Stamped → Prop
  | .complete scope, h, reported => ∀ event ∈ scope.events h, event ∈ reported
  | .countBounded scope bound, h, _ => (scope.events h).length ≤ bound
  | .declaredPolicy _ p, h, reported => policy p h reported
  | .openWorld _, _, _ => True

instance {Policy : Type} (policy : Policy → ProcessHistory → List Stamped → Prop)
    [∀ p h reported, Decidable (policy p h reported)]
    (c : RecordCoverage Policy) (h : ProcessHistory) (reported : List Stamped) :
    Decidable (c.Allowed policy h reported) := by
  cases c <;> unfold RecordCoverage.Allowed <;> infer_instance

/-- The assumption set a scoped coverage assertion induces on a model whose
histories have process traces and whose reporting choices expose events. -/
def RecordCoverage.assumptions {Policy : Type}
    (policy : Policy → ProcessHistory → List Stamped → Prop)
    (trace : H → ProcessHistory) (exposed : H → Rho → List Stamped)
    (c : RecordCoverage Policy) : Assumptions H Rho :=
  ⟨fun h rho => c.Allowed policy (trace h) (exposed h rho)⟩

end Lara.Process
