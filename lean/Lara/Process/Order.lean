import Lara.Process.Verdict

/-!
Ordered process histories and analysis-order predicates.

`Lara.BHL.History` is a multiset and stays one; BHL's ledger semantics depends
on that. Order lives in `ProcessHistory`, an ordered list of identified events,
and in the BHL trace (`Lara.Process.WorldView`). This module defines:

* the process transition relation `Step` and `Valid` histories: a run needs a
  committed plan version and a fresh run identity, a result needs its run, and
  event identities are fresh;
* the decidable analysis-order predicates `PlanCommittedBefore`,
  `RunPrecommitted`, `Predictable` and `SplitSelection` over complete ordered
  histories;
* partial-order records, whose compatible histories are every valid ordering
  consistent with the recorded precedence constraints.

`SplitSelection` is structural read separation only. It does not establish
statistical independence, which the statistical layer states as a separate
premise. `Predictable` is order evidence under the model's
complete account of relevant accesses, not a measurability proof.
-/

namespace Lara.Process

/-! ### Event projections -/

/-- The plan version, inputs and family a run event used. -/
structure RunSpec where
  run : RunId
  plan : PlanId
  version : VersionId
  inputs : List (DataId × VersionId)
  family : FamilyId
  deriving DecidableEq, Repr

def Event.runSpec? : Event → Option RunSpec
  | .run r p v ins f => some ⟨r, p, v, ins, f⟩
  | _ => none

/-- The plan version an event commits. -/
def Event.commits? : Event → Option (PlanId × VersionId)
  | .commitPlan _ plan version => some (plan, version)
  | _ => none

/-- The dataset and purpose of an access event. -/
def Event.access? : Event → Option (DataId × AccessPurpose)
  | .access _ data purpose => some (data, purpose)
  | _ => none

/-! ### Valid histories -/

/-- The modeled process state: committed plan versions, started runs, used
event identities, the current version of each updated dataset, and retracted
sources. A dataset never updated is at version `⟨0⟩`. -/
structure ProcessState where
  committed : List (PlanId × VersionId)
  runs : List RunId
  used : List EventId
  versions : List (DataId × VersionId)
  retracted : List SourceId
  deriving DecidableEq, Repr

def ProcessState.initial : ProcessState := ⟨[], [], [], [], []⟩

/-- The current version of a dataset: its latest update, or `⟨0⟩`. -/
def ProcessState.version (s : ProcessState) (d : DataId) : VersionId :=
  ((s.versions.find? (·.1 == d)).map Prod.snd).getD ⟨0⟩

/-- One transition. Every event identity is fresh. A run needs a committed plan
version, a fresh run identity and the current version of every input. A result
needs its run. A dataset update records the new current version; a retraction
records the source, once. -/
def ProcessState.step (s : ProcessState) (e : Stamped) : Option ProcessState :=
  if e.id ∈ s.used then none
  else
    let s := { s with used := e.id :: s.used }
    match e.event with
    | .commitPlan _ plan version => some { s with committed := (plan, version) :: s.committed }
    | .run run plan version inputs _ =>
        if run ∉ s.runs ∧ (plan, version) ∈ s.committed ∧ ∀ i ∈ inputs, s.version i.1 = i.2 then
          some { s with runs := run :: s.runs }
        else none
    | .result run _ => if run ∈ s.runs then some s else none
    | .updateData data version => some { s with versions := (data, version) :: s.versions }
    | .retract source =>
        if source ∈ s.retracted then none else some { s with retracted := source :: s.retracted }
    | _ => some s

/-- The labeled transition relation of the process model. -/
def Step (s : ProcessState) (e : Stamped) (s' : ProcessState) : Prop := s.step e = some s'

/-- Run a history from a state. -/
def ProcessState.run : ProcessState → ProcessHistory → Option ProcessState
  | s, [] => some s
  | s, e :: rest => (s.step e).bind fun s' => ProcessState.run s' rest

/-- A history is valid when it executes from the initial state. -/
def ValidHistory (h : ProcessHistory) : Prop := (ProcessState.initial.run h).isSome

instance (h : ProcessHistory) : Decidable (ValidHistory h) :=
  inferInstanceAs (Decidable (_ = true))

/-- A valid history through a declared submission cutoff: at most `cutoff`
events. Completions of a record never extend past its cutoff; later events are
future continuations. -/
def ValidThrough (cutoff : Nat) (h : ProcessHistory) : Prop := ValidHistory h ∧ h.length ≤ cutoff

instance (cutoff : Nat) (h : ProcessHistory) : Decidable (ValidThrough cutoff h) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Execution is a chain of `Step` transitions. -/
theorem run_some_iff_steps : ∀ (s : ProcessState) (h : ProcessHistory) (s' : ProcessState),
    s.run h = some s' ↔
      match h with
      | [] => s' = s
      | e :: rest => ∃ mid, Step s e mid ∧ mid.run rest = some s'
  | s, [], s' => by simp [ProcessState.run, eq_comm]
  | s, e :: rest, s' => by
      simp only [ProcessState.run, Option.bind_eq_some_iff, Step]

/-- A valid history's prefixes are valid: validity is about the past only. -/
theorem valid_prefix : ∀ (s : ProcessState) (h t : ProcessHistory),
    (s.run (h ++ t)).isSome → (s.run h).isSome
  | s, [], _, _ => rfl
  | s, e :: rest, t, valid => by
      simp only [List.cons_append, ProcessState.run] at valid ⊢
      cases hs : s.step e with
      | none => rw [hs] at valid; cases valid
      | some mid =>
          rw [hs] at valid
          exact valid_prefix mid rest t valid

/-! ### Analysis-order predicates -/

section Predicates

variable (h : ProcessHistory)

/-- The commitment to plan version `(plan, version)` precedes every evaluation
access to the datasets `data`: some commit position is earlier than every such
access position. Every evaluation access to those datasets counts, whichever
run or dataset version it served; this is the conservative reading. -/
def PlanCommittedBefore (plan : PlanId) (version : VersionId) (data : List DataId) : Prop :=
  ∃ i : Fin h.length, h[i].event.commits? = some (plan, version) ∧
    ∀ j : Fin h.length, ∀ a ∈ h[j].event.access?.toList,
      a.2 = .evaluation → a.1 ∈ data → i < j

instance (plan : PlanId) (version : VersionId) (data : List DataId) :
    Decidable (PlanCommittedBefore h plan version data) := by
  unfold PlanCommittedBefore; infer_instance

/-- Every run with identity `run` used a plan version committed before every
evaluation access to its inputs. It holds vacuously when the history has no
such run; record compatibility, which requires reported runs to be present, is
what rules that case out. -/
def RunPrecommitted (run : RunId) : Prop :=
  ∀ k : Fin h.length, ∀ spec ∈ h[k].event.runSpec?.toList, spec.run = run →
    PlanCommittedBefore h spec.plan spec.version (spec.inputs.map Prod.fst)

instance (run : RunId) : Decidable (RunPrecommitted h run) := by
  unfold RunPrecommitted; infer_instance

/-- Every run's analysis is fixed before its evaluation data is read. Reading
each run as one e-value factor, this is the predictability condition: it is
`RunPrecommitted` for every run of the history. -/
def Predictable : Prop :=
  ∀ k : Fin h.length, ∀ spec ∈ h[k].event.runSpec?.toList,
    PlanCommittedBefore h spec.plan spec.version (spec.inputs.map Prod.fst)

instance : Decidable (Predictable h) := by
  unfold Predictable; infer_instance

/-- Structural split selection: selection reads only `selection` datasets,
evaluation reads only `test` datasets, and the two identity lists are disjoint.
This is read separation; it is not statistical independence. -/
def SplitSelection (selection test : List DataId) : Prop :=
  (∀ d ∈ selection, d ∉ test) ∧
    ∀ j : Fin h.length, ∀ a ∈ h[j].event.access?.toList,
      (a.2 = .selection → a.1 ∈ selection) ∧ (a.2 = .evaluation → a.1 ∈ test)

instance (selection test : List DataId) : Decidable (SplitSelection h selection test) := by
  unfold SplitSelection; infer_instance

/-- The number of runs of a statistical family, failed trials included. -/
def familyCount (family : FamilyId) : Nat :=
  (h.filter fun e => (e.event.runSpec?.map RunSpec.family) == some family).length

/-- The runs with a successful (positive) result. Only these yield arguments for
the argumentation lowering; a failed run (result `0`, or none) yields none, so it
can neither support nor attack. -/
def successfulRuns : List RunId :=
  h.filterMap fun e => match e.event with
    | .result run outcome => if 0 < outcome then some run else none
    | _ => none

end Predicates

theorem predictable_runPrecommitted {h : ProcessHistory} (p : Predictable h) (run : RunId) :
    RunPrecommitted h run :=
  fun k spec mem _ => p k spec mem

/-- Every run in the family and in the history is counted, whatever its outcome:
an extra run raises the count. -/
theorem familyCount_append_run (h : ProcessHistory) (e : Stamped) (spec : RunSpec)
    (run : e.event.runSpec? = some spec) :
    familyCount (h ++ [e]) spec.family = familyCount h spec.family + 1 := by
  simp [familyCount, List.filter_append, run]

/-! ### Partial-order records -/

/-- A partial-order record: reported events, explicit precedence constraints
between event identities, and the submission cutoff. The order of `events` is
not temporal evidence. -/
structure OrderRecord where
  events : List Stamped
  before : List (EventId × EventId)
  cutoff : Nat
  deriving DecidableEq, Repr

/-- The position of an event identity in a history, if present. -/
def ProcessHistory.position (h : ProcessHistory) (id : EventId) : Option Nat :=
  h.findIdx? (·.id == id)

/-- Event `a` occurs at an earlier position than event `b`. -/
def ProcessHistory.Precedes (h : ProcessHistory) (a b : EventId) : Prop :=
  ∃ i ∈ (h.position a).toList, ∃ j ∈ (h.position b).toList, i < j

instance (h : ProcessHistory) (a b : EventId) : Decidable (h.Precedes a b) := by
  unfold ProcessHistory.Precedes; infer_instance

/-- A complete history is compatible with a partial-order record when it is
valid through the cutoff, contains every reported event, and respects every
precedence constraint. -/
def OrderCompatible (r : OrderRecord) (h : ProcessHistory) : Prop :=
  ValidThrough r.cutoff h ∧ (∀ e ∈ r.events, e ∈ h) ∧ ∀ c ∈ r.before, h.Precedes c.1 c.2

instance (r : OrderRecord) (h : ProcessHistory) : Decidable (OrderCompatible r h) := by
  unfold OrderCompatible; infer_instance

/-- Reordering the reported events changes no compatible history: file or
display order is not temporal evidence. -/
theorem orderCompatible_perm {r r' : OrderRecord} (perm : r.events.Perm r'.events)
    (same : r.before = r'.before) (cutoff : r.cutoff = r'.cutoff) (h : ProcessHistory) :
    OrderCompatible r h ↔ OrderCompatible r' h := by
  unfold OrderCompatible
  rw [same, cutoff]
  constructor
  · rintro ⟨v, mem, c⟩; exact ⟨v, fun e he => mem e (perm.mem_iff.mpr he), c⟩
  · rintro ⟨v, mem, c⟩; exact ⟨v, fun e he => mem e (perm.mem_iff.mp he), c⟩

/-- More evidence never adds completions: a record with more reported events and
more constraints, at an earlier or equal cutoff, has fewer compatible histories.
So a record that leaves an order unconstrained keeps every history the
constrained record keeps, including any that violates an order predicate. -/
theorem orderCompatible_mono {r r' : OrderRecord} (events : ∀ e ∈ r.events, e ∈ r'.events)
    (before : ∀ c ∈ r.before, c ∈ r'.before) (cutoff : r'.cutoff ≤ r.cutoff)
    {h : ProcessHistory} (compat : OrderCompatible r' h) : OrderCompatible r h :=
  ⟨⟨compat.1.1, compat.1.2.trans cutoff⟩, fun e he => compat.2.1 e (events e he),
    fun c hc => compat.2.2 c (before c hc)⟩

/-- Contradictory precedence constraints admit no history. -/
theorem contradictory_constraints {r : OrderRecord} {a b : EventId}
    (ab : (a, b) ∈ r.before) (ba : (b, a) ∈ r.before) (h : ProcessHistory) :
    ¬ OrderCompatible r h := by
  rintro ⟨_, _, c⟩
  obtain ⟨i, hi, j, hj, lt⟩ := c _ ab
  obtain ⟨j', hj', i', hi', lt'⟩ := c _ ba
  simp only [Option.mem_toList] at hi hj hj' hi'
  rw [hi] at hi'; rw [hj] at hj'
  cases hi'; cases hj'
  exact absurd (lt.trans lt') (lt_irrefl _)

/-- So their verdict is `inconsistent`, never a positive answer. -/
theorem contradictory_constraints_inconsistent {X : Type} {r : OrderRecord} {a b : EventId}
    (ab : (a, b) ∈ r.before) (ba : (b, a) ∈ r.before) (history : X → ProcessHistory)
    (φ : X → Prop) : verdictOf (fun x => OrderCompatible r (history x)) φ = .inconsistent :=
  (verdictOf_inconsistent_iff _ _).mpr fun ⟨_, hx⟩ => contradictory_constraints ab ba _ hx

end Lara.Process
