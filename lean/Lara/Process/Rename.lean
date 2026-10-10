import Lara.Process.Universe

/-!
Identifier renaming for the `process-input 1` contract.

The wire spells identifiers as names, and the decoder interns each name to its
position in its namespace's declared table. Positions are arbitrary, so this
module shows the choice cannot matter: an injective renaming of each identifier
namespace preserves validity, order compatibility, coverage, the completion set
and every query answer.

Versions are not renamed. `ProcessState.version` reads an unupdated dataset as
version `⟨0⟩`, so version `0` has a meaning of its own; the wire spells versions
as decimals and never interns them.

* `step_rename`, `validThrough_rename`: the transition relation commutes with
  renaming.
* `compatible_rename`: a renamed history is compatible with the renamed record
  iff the original is compatible with the original.
* `completions_rename`: the renamed problem's completions are the renamed
  completions.
* `answer_rename`: every answer keeps its verdict and count, and its witnesses
  are the renamed witnesses.
-/

namespace Lara.Process

open Lara.Process.Universe

/-- One injective renaming per identifier namespace. Versions are not renamed. -/
structure Renaming where
  event : Nat → Nat
  actor : Nat → Nat
  plan : Nat → Nat
  run : Nat → Nat
  claim : Nat → Nat
  source : Nat → Nat
  data : Nat → Nat
  family : Nat → Nat
  witness : Nat → Nat
  event_inj : Function.Injective event
  actor_inj : Function.Injective actor
  plan_inj : Function.Injective plan
  run_inj : Function.Injective run
  claim_inj : Function.Injective claim
  source_inj : Function.Injective source
  data_inj : Function.Injective data
  family_inj : Function.Injective family
  witness_inj : Function.Injective witness

variable (ρ : Renaming)

/-! ### Identifiers -/

def EventId.rename (i : EventId) : EventId := ⟨ρ.event i.index⟩
def ActorId.rename (i : ActorId) : ActorId := ⟨ρ.actor i.index⟩
def PlanId.rename (i : PlanId) : PlanId := ⟨ρ.plan i.index⟩
def RunId.rename (i : RunId) : RunId := ⟨ρ.run i.index⟩
def ClaimId.rename (i : ClaimId) : ClaimId := ⟨ρ.claim i.index⟩
def SourceId.rename (i : SourceId) : SourceId := ⟨ρ.source i.index⟩
def DataId.rename (i : DataId) : DataId := ⟨ρ.data i.index⟩
def FamilyId.rename (i : FamilyId) : FamilyId := ⟨ρ.family i.index⟩
def WitnessId.rename (i : WitnessId) : WitnessId := ⟨ρ.witness i.index⟩

theorem EventId.rename_inj : Function.Injective (EventId.rename ρ) := by
  rintro ⟨a⟩ ⟨b⟩ h; simp only [EventId.rename, EventId.mk.injEq] at h; rw [ρ.event_inj h]
theorem ActorId.rename_inj : Function.Injective (ActorId.rename ρ) := by
  rintro ⟨a⟩ ⟨b⟩ h; simp only [ActorId.rename, ActorId.mk.injEq] at h; rw [ρ.actor_inj h]
theorem PlanId.rename_inj : Function.Injective (PlanId.rename ρ) := by
  rintro ⟨a⟩ ⟨b⟩ h; simp only [PlanId.rename, PlanId.mk.injEq] at h; rw [ρ.plan_inj h]
theorem RunId.rename_inj : Function.Injective (RunId.rename ρ) := by
  rintro ⟨a⟩ ⟨b⟩ h; simp only [RunId.rename, RunId.mk.injEq] at h; rw [ρ.run_inj h]
theorem ClaimId.rename_inj : Function.Injective (ClaimId.rename ρ) := by
  rintro ⟨a⟩ ⟨b⟩ h; simp only [ClaimId.rename, ClaimId.mk.injEq] at h; rw [ρ.claim_inj h]
theorem SourceId.rename_inj : Function.Injective (SourceId.rename ρ) := by
  rintro ⟨a⟩ ⟨b⟩ h; simp only [SourceId.rename, SourceId.mk.injEq] at h; rw [ρ.source_inj h]
theorem DataId.rename_inj : Function.Injective (DataId.rename ρ) := by
  rintro ⟨a⟩ ⟨b⟩ h; simp only [DataId.rename, DataId.mk.injEq] at h; rw [ρ.data_inj h]
theorem FamilyId.rename_inj : Function.Injective (FamilyId.rename ρ) := by
  rintro ⟨a⟩ ⟨b⟩ h; simp only [FamilyId.rename, FamilyId.mk.injEq] at h; rw [ρ.family_inj h]
theorem WitnessId.rename_inj : Function.Injective (WitnessId.rename ρ) := by
  rintro ⟨a⟩ ⟨b⟩ h; simp only [WitnessId.rename, WitnessId.mk.injEq] at h; rw [ρ.witness_inj h]

@[simp] theorem EventId.rename_eq_iff {a b : EventId} : a.rename ρ = b.rename ρ ↔ a = b :=
  (EventId.rename_inj ρ).eq_iff
@[simp] theorem ActorId.rename_eq_iff {a b : ActorId} : a.rename ρ = b.rename ρ ↔ a = b :=
  (ActorId.rename_inj ρ).eq_iff
@[simp] theorem PlanId.rename_eq_iff {a b : PlanId} : a.rename ρ = b.rename ρ ↔ a = b :=
  (PlanId.rename_inj ρ).eq_iff
@[simp] theorem RunId.rename_eq_iff {a b : RunId} : a.rename ρ = b.rename ρ ↔ a = b :=
  (RunId.rename_inj ρ).eq_iff
@[simp] theorem ClaimId.rename_eq_iff {a b : ClaimId} : a.rename ρ = b.rename ρ ↔ a = b :=
  (ClaimId.rename_inj ρ).eq_iff
@[simp] theorem SourceId.rename_eq_iff {a b : SourceId} : a.rename ρ = b.rename ρ ↔ a = b :=
  (SourceId.rename_inj ρ).eq_iff
@[simp] theorem DataId.rename_eq_iff {a b : DataId} : a.rename ρ = b.rename ρ ↔ a = b :=
  (DataId.rename_inj ρ).eq_iff
@[simp] theorem FamilyId.rename_eq_iff {a b : FamilyId} : a.rename ρ = b.rename ρ ↔ a = b :=
  (FamilyId.rename_inj ρ).eq_iff
@[simp] theorem WitnessId.rename_eq_iff {a b : WitnessId} : a.rename ρ = b.rename ρ ↔ a = b :=
  (WitnessId.rename_inj ρ).eq_iff

/-- Membership in a list is preserved by an injective map. -/
theorem mem_map_inj {α β : Type} {f : α → β} (hf : Function.Injective f) {a : α} {l : List α} :
    f a ∈ l.map f ↔ a ∈ l := List.mem_map_of_injective hf

/-- A version-keyed pair keeps its version. -/
def keyRename {α : Type} (r : α → α) (x : α × VersionId) : α × VersionId := (r x.1, x.2)

theorem keyRename_inj {α : Type} {r : α → α} (hr : Function.Injective r) :
    Function.Injective (keyRename r) := by
  rintro ⟨a, v⟩ ⟨b, w⟩ h
  simp only [keyRename, Prod.mk.injEq] at h
  rw [hr h.1, h.2]

def accessRename (x : DataId × AccessPurpose) : DataId × AccessPurpose := (x.1.rename ρ, x.2)

theorem accessRename_inj : Function.Injective (accessRename ρ) := by
  rintro ⟨a, p⟩ ⟨b, q⟩ h
  simp only [accessRename, Prod.mk.injEq, DataId.rename_eq_iff] at h
  rw [h.1, h.2]

/-! ### Events and states -/

def Event.rename : Event → Event
  | .commitPlan actor plan version => .commitPlan (actor.rename ρ) (plan.rename ρ) version
  | .access actor data purpose => .access (actor.rename ρ) (data.rename ρ) purpose
  | .run r plan version inputs family =>
      .run (r.rename ρ) (plan.rename ρ) version (inputs.map (keyRename (DataId.rename ρ)))
        (family.rename ρ)
  | .result r outcome => .result (r.rename ρ) outcome
  | .assert claim witness => .assert (claim.rename ρ) (witness.rename ρ)
  | .retract source => .retract (source.rename ρ)
  | .updateData data version => .updateData (data.rename ρ) version

theorem Event.rename_inj : Function.Injective (Event.rename ρ) := by
  have inputs := List.map_injective_iff.2 (keyRename_inj (DataId.rename_inj ρ))
  intro a b h
  cases a <;> cases b <;> simp only [Event.rename, Event.commitPlan.injEq, Event.access.injEq,
    Event.run.injEq, Event.result.injEq, Event.assert.injEq, Event.retract.injEq,
    Event.updateData.injEq, reduceCtorEq, ActorId.rename_eq_iff, PlanId.rename_eq_iff,
    RunId.rename_eq_iff, ClaimId.rename_eq_iff, SourceId.rename_eq_iff, DataId.rename_eq_iff,
    FamilyId.rename_eq_iff, WitnessId.rename_eq_iff, inputs.eq_iff] at h ⊢ <;> exact h

def Stamped.rename (e : Stamped) : Stamped := ⟨e.id.rename ρ, e.event.rename ρ⟩

theorem Stamped.rename_inj : Function.Injective (Stamped.rename ρ) := by
  rintro ⟨a, e⟩ ⟨b, f⟩ h
  simp only [Stamped.rename, Stamped.mk.injEq, EventId.rename_eq_iff] at h
  rw [h.1, Event.rename_inj ρ h.2]

/-- Rename every event of a history. -/
abbrev hrename (h : ProcessHistory) : ProcessHistory := h.map (Stamped.rename ρ)

theorem hrename_inj : Function.Injective (hrename ρ) :=
  List.map_injective_iff.2 (Stamped.rename_inj ρ)

def ProcessState.rename (s : ProcessState) : ProcessState where
  committed := s.committed.map (keyRename (PlanId.rename ρ))
  runs := s.runs.map (RunId.rename ρ)
  used := s.used.map (EventId.rename ρ)
  versions := s.versions.map (keyRename (DataId.rename ρ))
  retracted := s.retracted.map (SourceId.rename ρ)

theorem version_rename (versions : List (DataId × VersionId)) (d : DataId) :
    ((versions.map (keyRename (DataId.rename ρ))).find? (·.1 == d.rename ρ)).map Prod.snd =
      (versions.find? (·.1 == d)).map Prod.snd := by
  rw [List.find?_map, Option.map_map]
  have : ((fun x : DataId × VersionId => x.1 == d.rename ρ) ∘ keyRename (DataId.rename ρ)) =
      fun x => x.1 == d := by
    funext x; simp [keyRename]
  rw [this]; rfl

theorem step_rename (s : ProcessState) (e : Stamped) :
    (s.rename ρ).step (e.rename ρ) = (s.step e).map (ProcessState.rename ρ) := by
  obtain ⟨id, ev⟩ := e
  have used : id.rename ρ ∈ (s.rename ρ).used ↔ id ∈ s.used := mem_map_inj (EventId.rename_inj ρ)
  simp only [ProcessState.step, Stamped.rename]
  by_cases hu : id ∈ s.used
  · rw [if_pos (used.2 hu), if_pos hu]; rfl
  rw [if_neg (fun h => hu (used.1 h)), if_neg hu]
  cases ev with
  | commitPlan a p v => rfl
  | access a d pur => rfl
  | run r p v ins f =>
      simp only [Event.rename]
      have runs : r.rename ρ ∈ (s.rename ρ).runs ↔ r ∈ s.runs := mem_map_inj (RunId.rename_inj ρ)
      have com : keyRename (PlanId.rename ρ) (p, v) ∈ (s.rename ρ).committed ↔ (p, v) ∈ s.committed :=
        mem_map_inj (keyRename_inj (PlanId.rename_inj ρ))
      have vers : (∀ i ∈ ins.map (keyRename (DataId.rename ρ)),
          ({ s.rename ρ with used := id.rename ρ :: (s.rename ρ).used } : ProcessState).version i.1 = i.2) ↔
          ∀ i ∈ ins, ({ s with used := id :: s.used } : ProcessState).version i.1 = i.2 := by
        simp only [List.forall_mem_map, ProcessState.version]
        refine forall₂_congr fun i _ => ?_
        simp only [keyRename, ProcessState.rename]
        rw [version_rename]
      by_cases c : r ∉ s.runs ∧ (p, v) ∈ s.committed ∧
          ∀ i ∈ ins, ({ s with used := id :: s.used } : ProcessState).version i.1 = i.2
      · rw [if_pos c]
        rw [if_pos ⟨fun h => c.1 (runs.1 h), com.2 c.2.1, vers.2 c.2.2⟩]
        rfl
      · rw [if_neg c, if_neg]
        · rfl
        rintro ⟨a, b, d⟩
        exact c ⟨fun h => a (runs.2 h), com.1 b, vers.1 d⟩
  | result r o =>
      have runs : r.rename ρ ∈ (s.rename ρ).runs ↔ r ∈ s.runs := mem_map_inj (RunId.rename_inj ρ)
      simp only [Event.rename]
      by_cases c : r ∈ s.runs
      · rw [if_pos (runs.2 c), if_pos c]; rfl
      · rw [if_neg (fun h => c (runs.1 h)), if_neg c]; rfl
  | assert c w => rfl
  | retract src =>
      have ret : src.rename ρ ∈ (s.rename ρ).retracted ↔ src ∈ s.retracted :=
        mem_map_inj (SourceId.rename_inj ρ)
      simp only [Event.rename]
      by_cases c : src ∈ s.retracted
      · rw [if_pos (ret.2 c), if_pos c]; rfl
      · rw [if_neg (fun h => c (ret.1 h)), if_neg c]; rfl
  | updateData d v => rfl

theorem run_rename : ∀ (s : ProcessState) (h : ProcessHistory),
    (s.rename ρ).run (hrename ρ h) = (s.run h).map (ProcessState.rename ρ)
  | s, [] => rfl
  | s, e :: rest => by
      simp only [hrename, List.map_cons, ProcessState.run, step_rename]
      cases s.step e with
      | none => rfl
      | some mid => exact run_rename mid rest

theorem validThrough_rename (cutoff : Nat) (h : ProcessHistory) :
    ValidThrough cutoff (hrename ρ h) ↔ ValidThrough cutoff h := by
  have := run_rename ρ ProcessState.initial h
  simp only [ValidThrough, ValidHistory, List.length_map]
  rw [show ProcessState.initial.rename ρ = ProcessState.initial from rfl] at this
  rw [this, Option.isSome_map]

theorem precedes_rename (h : ProcessHistory) (a b : EventId) :
    (hrename ρ h).Precedes (a.rename ρ) (b.rename ρ) ↔ h.Precedes a b := by
  have pos : ∀ x : EventId, (hrename ρ h).position (x.rename ρ) = h.position x := by
    intro x
    simp only [ProcessHistory.position, hrename, List.findIdx?_map]
    congr 1
    funext e
    simp [Stamped.rename]
  simp only [ProcessHistory.Precedes, pos]

/-! ### Coverage -/

def CoverageScope.rename (sc : CoverageScope) : CoverageScope where
  kinds := sc.kinds
  family := sc.family.map (FamilyId.rename ρ)
  actors := sc.actors.map (List.map (ActorId.rename ρ))
  data := sc.data.map (List.map (DataId.rename ρ))
  cutoff := sc.cutoff

def RecordCoverage.rename : RecordCoverage Empty → RecordCoverage Empty
  | .complete sc => .complete (sc.rename ρ)
  | .countBounded sc bound => .countBounded (sc.rename ρ) bound
  | .declaredPolicy _ p => p.elim
  | .openWorld sc => .openWorld (sc.rename ρ)

theorem Event.kind_rename (e : Event) : (e.rename ρ).kind = e.kind := by cases e <;> rfl

theorem contains_rename (sc : CoverageScope) (index : Nat) (e : Stamped) :
    (sc.rename ρ).Contains index (e.rename ρ) ↔ sc.Contains index e := by
  obtain ⟨id, ev⟩ := e
  simp only [CoverageScope.Contains, Stamped.rename, Event.kind_rename, CoverageScope.rename]
  have fam : CoverageScope.familyOk ⟨sc.kinds, sc.family.map (FamilyId.rename ρ),
      sc.actors.map (List.map (ActorId.rename ρ)), sc.data.map (List.map (DataId.rename ρ)),
      sc.cutoff⟩ (ev.rename ρ) = sc.familyOk ev := by
    unfold CoverageScope.familyOk
    cases sc.family <;> cases ev <;> simp [Event.rename, Event.family?]
  have act : CoverageScope.actorOk ⟨sc.kinds, sc.family.map (FamilyId.rename ρ),
      sc.actors.map (List.map (ActorId.rename ρ)), sc.data.map (List.map (DataId.rename ρ)),
      sc.cutoff⟩ (ev.rename ρ) = sc.actorOk ev := by
    unfold CoverageScope.actorOk
    cases sc.actors <;> cases ev <;>
      simp [Event.rename, Event.actor?]
  have dat : CoverageScope.dataOk ⟨sc.kinds, sc.family.map (FamilyId.rename ρ),
      sc.actors.map (List.map (ActorId.rename ρ)), sc.data.map (List.map (DataId.rename ρ)),
      sc.cutoff⟩ (ev.rename ρ) = sc.dataOk ev := by
    unfold CoverageScope.dataOk
    cases sc.data <;> cases ev <;>
      simp [Event.rename, Event.data, keyRename, List.all_map, Function.comp_def]
  rw [fam, act, dat]

theorem scopeEvents_rename (sc : CoverageScope) (h : ProcessHistory) :
    (sc.rename ρ).events (hrename ρ h) = (sc.events h).map (Stamped.rename ρ) := by
  simp only [CoverageScope.events, hrename, List.length_map, List.zip_map_right,
    List.filterMap_map, List.map_filterMap]
  congr 1
  funext x
  obtain ⟨i, e⟩ := x
  simp only [Function.comp_apply, Prod.map_apply, id_eq]
  by_cases c : sc.Contains i e
  · rw [if_pos ((contains_rename ρ sc i e).2 c), if_pos c]; rfl
  · rw [if_neg (fun h => c ((contains_rename ρ sc i e).1 h)), if_neg c]; rfl

theorem allowed_rename (c : RecordCoverage Empty) (h : ProcessHistory) (reported : List Stamped) :
    (c.rename ρ).Allowed noPolicy (hrename ρ h) (reported.map (Stamped.rename ρ)) ↔
      c.Allowed noPolicy h reported := by
  cases c with
  | complete sc =>
      simp only [RecordCoverage.rename, RecordCoverage.Allowed, scopeEvents_rename,
        List.forall_mem_map, mem_map_inj (Stamped.rename_inj ρ)]
  | countBounded sc bound =>
      simp only [RecordCoverage.rename, RecordCoverage.Allowed, scopeEvents_rename,
        List.length_map]
  | declaredPolicy _ p => exact p.elim
  | openWorld sc => simp only [RecordCoverage.rename, RecordCoverage.Allowed]

/-! ### Records and problems -/

def DecodedRecord.rename (d : DecodedRecord Empty) : DecodedRecord Empty where
  events := d.events.map fun e => ⟨e.event.rename ρ, e.source⟩
  order := d.order.map fun o => ⟨o.first.rename ρ, o.second.rename ρ, o.source⟩
  coverage := d.coverage.map fun c => ⟨c.coverage.rename ρ, c.evidence, c.basis⟩
  submitted := d.submitted.map fun s => (s.1.rename ρ, s.2.rename ρ)
  cutoff := d.cutoff

theorem reported_rename (d : DecodedRecord Empty) :
    (d.rename ρ).events.map DecodedEvent.event =
      (d.events.map DecodedEvent.event).map (Stamped.rename ρ) := by
  simp [DecodedRecord.rename, Function.comp_def]

theorem compatible_rename (d : DecodedRecord Empty) (h : ProcessHistory) :
    (d.rename ρ).Compatible noPolicy (hrename ρ h) ↔ d.Compatible noPolicy h := by
  simp only [DecodedRecord.Compatible, OrderCompatible, DecodedRecord.toOrderRecord]
  rw [reported_rename]
  have cut : (d.rename ρ).cutoff = d.cutoff := rfl
  rw [cut, validThrough_rename]
  simp only [List.forall_mem_map, hrename, mem_map_inj (Stamped.rename_inj ρ)]
  simp only [DecodedRecord.rename, List.map_map, List.forall_mem_map]
  have prec := precedes_rename ρ h
  have allowed := fun c r => allowed_rename ρ c h r
  try simp only [hrename] at prec allowed
  have rep : List.map (Stamped.rename ρ ∘ DecodedEvent.event) d.events =
      (d.events.map DecodedEvent.event).map (Stamped.rename ρ) := by rw [List.map_map]
  simp only [prec, rep, allowed]

namespace Universe

def Problem.rename (p : Problem) : Problem :=
  ⟨p.record.rename ρ, p.unrecorded.map (Stamped.rename ρ)⟩

theorem base_rename (p : Problem) : (p.rename ρ).base = p.base.map (Stamped.rename ρ) := by
  simp only [Problem.base, Problem.rename]
  rw [reported_rename, List.dedup_map_of_injective (Stamped.rename_inj ρ)]

theorem compat_rename (p : Problem) (h : ProcessHistory) :
    (p.rename ρ).Compat (hrename ρ h) ↔ p.Compat h := by
  simp only [Problem.Compat, hrename, List.nodup_map_iff (Stamped.rename_inj ρ)]
  have := compatible_rename ρ p.record h
  simp only [hrename] at this
  simp only [Problem.rename, this]

theorem candidates_rename (p : Problem) :
    (p.rename ρ).candidates = p.candidates.map (hrename ρ) := by
  simp only [Problem.candidates, base_rename]
  simp only [Problem.rename, List.dedup_map_of_injective (Stamped.rename_inj ρ),
    List.sublists_map, List.flatMap_map, List.map_flatMap]
  congr 1
  funext sub
  rw [← List.map_append, ← List.map_permutations]

theorem completions_rename (p : Problem) :
    (p.rename ρ).completions = p.completions.map (hrename ρ) := by
  simp only [Problem.completions, candidates_rename, List.filter_map]
  rw [← List.dedup_map_of_injective (hrename_inj ρ)]
  congr 1
  congr 1
  apply List.filter_congr
  intro h _
  simp only [Function.comp_apply, compat_rename]

/-! ### Queries -/

def Atom.rename : Atom → Atom
  | .runPrecommitted r => .runPrecommitted (r.rename ρ)
  | .predictable => .predictable
  | .splitSelection selection test =>
      .splitSelection (selection.map (DataId.rename ρ)) (test.map (DataId.rename ρ))
  | .familyCountAtMost family bound => .familyCountAtMost (family.rename ρ) bound

def RunSpec.rename (s : RunSpec) : RunSpec :=
  ⟨s.run.rename ρ, s.plan.rename ρ, s.version, s.inputs.map (keyRename (DataId.rename ρ)),
    s.family.rename ρ⟩

theorem runSpec?_rename (e : Event) : (e.rename ρ).runSpec? = e.runSpec?.map (RunSpec.rename ρ) := by
  cases e <;> rfl

theorem commits?_rename (e : Event) :
    (e.rename ρ).commits? = e.commits?.map (keyRename (PlanId.rename ρ)) := by
  cases e <;> rfl

theorem access?_rename (e : Event) : (e.rename ρ).access? = e.access?.map (accessRename ρ) := by
  cases e <;> rfl

theorem forall_toList_map {α β : Type} (o : Option α) (g : α → β) (P : β → Prop) :
    (∀ b ∈ (o.map g).toList, P b) ↔ ∀ a ∈ o.toList, P (g a) := by
  cases o <;> simp

theorem map_eq_some_inj {α β : Type} {f : α → β} (hf : Function.Injective f) (o : Option α) (a : α) :
    o.map f = some (f a) ↔ o = some a := by
  cases o <;> simp [hf.eq_iff]

theorem keyed_mem {r : DataId → DataId} (hr : Function.Injective r) (l : List DataId) (d : DataId) :
    r d ∈ l.map r ↔ d ∈ l := mem_map_inj hr

theorem planCommittedBefore_rename (h : ProcessHistory) (plan : PlanId) (version : VersionId)
    (data : List DataId) :
    PlanCommittedBefore (hrename ρ h) (plan.rename ρ) version (data.map (DataId.rename ρ)) ↔
      PlanCommittedBefore h plan version data := by
  unfold PlanCommittedBefore
  simp only [Fin.exists_iff, Fin.forall_iff, hrename, List.length_map, Fin.getElem_fin, List.getElem_map,
    Fin.mk_lt_mk, Stamped.rename, access?_rename, commits?_rename, forall_toList_map]
  have key : keyRename (PlanId.rename ρ) (plan, version) = (plan.rename ρ, version) := rfl
  rw [← key]
  simp only [map_eq_some_inj (keyRename_inj (PlanId.rename_inj ρ)), accessRename,
    keyed_mem (DataId.rename_inj ρ)]

theorem runPrecommitted_rename (h : ProcessHistory) (run : RunId) :
    RunPrecommitted (hrename ρ h) (run.rename ρ) ↔ RunPrecommitted h run := by
  unfold RunPrecommitted
  simp only [Fin.forall_iff, hrename, List.length_map, Fin.getElem_fin, List.getElem_map, Stamped.rename,
    runSpec?_rename, forall_toList_map]
  refine forall_congr' fun k => forall_congr' fun hk => forall₂_congr fun spec _ => ?_
  simp only [RunSpec.rename, RunId.rename_eq_iff]
  have := planCommittedBefore_rename ρ h spec.plan spec.version (spec.inputs.map Prod.fst)
  simp only [hrename, List.map_map] at this
  have eq : (Prod.fst ∘ keyRename (DataId.rename ρ)) = (DataId.rename ρ ∘ Prod.fst) := rfl
  rw [List.map_map]
  exact imp_congr_right fun _ => this

theorem predictable_rename (h : ProcessHistory) : Predictable (hrename ρ h) ↔ Predictable h := by
  unfold Predictable
  simp only [Fin.forall_iff, hrename, List.length_map, Fin.getElem_fin, List.getElem_map, Stamped.rename,
    runSpec?_rename, forall_toList_map]
  refine forall_congr' fun k => forall_congr' fun hk => forall₂_congr fun spec _ => ?_
  have := planCommittedBefore_rename ρ h spec.plan spec.version (spec.inputs.map Prod.fst)
  simp only [hrename, List.map_map] at this
  have eq : (Prod.fst ∘ keyRename (DataId.rename ρ)) = (DataId.rename ρ ∘ Prod.fst) := rfl
  simp only [RunSpec.rename]
  rw [List.map_map]
  exact this

theorem splitSelection_rename (h : ProcessHistory) (selection test : List DataId) :
    SplitSelection (hrename ρ h) (selection.map (DataId.rename ρ)) (test.map (DataId.rename ρ)) ↔
      SplitSelection h selection test := by
  unfold SplitSelection
  simp only [Fin.forall_iff, hrename, List.length_map, Fin.getElem_fin, List.getElem_map, Stamped.rename,
    access?_rename, forall_toList_map, accessRename, List.forall_mem_map,
    keyed_mem (DataId.rename_inj ρ)]

theorem familyCount_rename (h : ProcessHistory) (family : FamilyId) :
    familyCount (hrename ρ h) (family.rename ρ) = familyCount h family := by
  unfold familyCount
  simp only [hrename, List.filter_map, List.length_map]
  congr 2
  funext e
  simp only [Function.comp_apply, Stamped.rename, runSpec?_rename, Option.map_map]
  rw [Bool.eq_iff_iff]
  cases e.event.runSpec? <;> simp [RunSpec.rename]

theorem atom_rename (a : Atom) (h : ProcessHistory) :
    (a.rename ρ).holds (hrename ρ h) ↔ a.holds h := by
  cases a with
  | runPrecommitted r => exact runPrecommitted_rename ρ h r
  | predictable => exact predictable_rename ρ h
  | splitSelection s t => exact splitSelection_rename ρ h s t
  | familyCountAtMost f k =>
      simp only [Atom.rename, Atom.holds, familyCount_rename]

def Query.rename : Query → Query
  | .atom a => .atom (a.rename ρ)
  | .neg f => .neg (Query.rename f)
  | .conj f g => .conj (Query.rename f) (Query.rename g)
  | .disj f g => .disj (Query.rename f) (Query.rename g)

theorem query_rename (q : Query) (h : ProcessHistory) :
    (Query.rename ρ q).holds Atom.holds (hrename ρ h) ↔ q.holds Atom.holds h := by
  induction q with
  | atom a => exact atom_rename ρ a h
  | neg f ih => simp only [Query.rename, Formula.holds, ih]
  | conj f g ihf ihg => simp only [Query.rename, Formula.holds, ihf, ihg]
  | disj f g ihf ihg => simp only [Query.rename, Formula.holds, ihf, ihg]

/-- Renaming changes no answer: the verdict and count are equal, and the witness
histories are the renamed witnesses. -/
theorem answer_rename (p : Problem) (q : Query) :
    answer (p.rename ρ) (Query.rename ρ q) =
      { answer p q with
        holds := (answer p q).holds.map (hrename ρ)
        fails := (answer p q).fails.map (hrename ρ) } := by
  have pred : (fun x => decide ((Query.rename ρ q).holds Atom.holds x)) ∘ hrename ρ =
      fun x => decide (q.holds Atom.holds x) := by
    funext x; simp only [Function.comp_apply, query_rename]
  have npred : (fun x => decide ¬ (Query.rename ρ q).holds Atom.holds x) ∘ hrename ρ =
      fun x => decide ¬ q.holds Atom.holds x := by
    funext x; simp only [Function.comp_apply, query_rename]
  have v : listVerdict (p.completions.map (hrename ρ)) ((Query.rename ρ q).holds Atom.holds) =
      listVerdict p.completions (q.holds Atom.holds) := by
    simp only [listVerdict, List.map_eq_nil_iff, List.all_map, pred, npred]
  simp only [answer, answerOf, completions_rename, v, List.length_map, List.find?_map, pred, npred]
  split_ifs <;> rfl

end Universe

end Lara.Process
