import Lara.Process.FamilyAudit
import Lara.Process.Enumerate
import Lara.Process.Inquiry
import Lara.Process.Vocabulary

/-!
Exact finite inquiry analyses (issue #22, stage P3).

This module defines the *rejection-aware* analyses over the checked-source
family of P1/P2. Nothing here re-runs a checker or re-derives a proposition: a
family is a list of `Family.Completion`s, each observed through the *same*
`Source.prepareRow`/`takeSnapshot` pipeline the landed source observer already
uses, and a public value is a `Driver.PublicStatus` taken from the prepared
row's fixed query list (`Source.QueryFields.status`), never a re-derived
proposition and never `Update.PublicReport`.

The analyses project a *shared* observation pass. The generic entry points
(`wholeStableB`, `acceptedStableB`, `stabilityResult`, `sensitivityResult`,
`assumptionResult`) take a supplied `read`. Stability (`wholeStableB`,
`acceptedStableB`, `stabilityResult`) derives every field from a single
`cs.map read` projection. Sensitivity and assumption enumeration never perform a
pairwise re-read either: `sensitivityResult` reads once per candidate change set
and `assumptionResult` once per catalog subset. The observable-specific
builders take one landed `Source.CheckedFamily`, whose already-prepared
`rows` are projected once into a table (`statusObservations` /
`auditObservations`) and read back through `tableRead`; the observation table
and the slots therefore come from the same `family` index, and
`statusObservations_map_snd` / `auditObservations_map_snd` state that the table
equals the per-completion `rowAt` reads. `rowAt` remains as that reference
per-completion reading.

The analyses are:

* observation/stability — full-observation equality, nonempty whole-outcome
  stability, an explicitly labelled accepted-only domain with its rejection
  count, and the partition of the family by rejected reason or accepted value;
* reference and changed-slot sensitivity — a named reference completion is
  compared with every other row; each differing row's exact changed-slot set is
  computed, and the joint analysis returns *every* inclusion-minimal nonempty
  change set admitting a flip (not one minimum-cardinality set);
* minimal conditional assumptions — a finite user-declared literal catalog is
  enumerated by subset; each satisfying set is required to remain nonempty and
  to have the requested accepted status or positive submitted-witness audit on
  every surviving row, and *every* subset-minimal set is returned with its
  surviving family and an immediate-deletion countercompletion.

`Lara.Process.Analysis.AnalysisWire` carries the canonical codecs. This module
is proved against the landed `Inquiry` laws rather than re-deriving them.
-/

namespace Lara.Process.Source

/-- The status a prepared row carries for a claim, read from the row's *fixed*
query list. `none` only when the claim is not one of the family's fixed
bindings; a well-bound observable always finds its entry. -/
def Row.claimStatus {context : ModelContext} (row : Row context) (claim : ClaimId) :
    Option Driver.PublicStatus :=
  match row.view with
  | .error _ => none
  | .ok view => (view.queries.find? (fun q => q.claim == claim)).map QueryFields.status

end Lara.Process.Source

namespace Lara.Process.Analysis

open Lara.Process
open Lara.Process.Source
open Lara.Process.Family

universe u

/-- Boolean decidability as an equivalence. -/
theorem decide_eq_true_iff' {p : Prop} [Decidable p] : (decide p = true) ↔ p :=
  ⟨of_decide_eq_true, fun h => decide_eq_true_eq.mpr h⟩

variable {context : ModelContext}

/-! ### Observation of one completion -/

/-- The prepared row of a completion, through the landed checked-source
pipeline. Definitionally the corresponding member of a `CheckedFamily`'s rows
when the completion belongs to the family: the bridge below
(`statusObservations_map_snd`) states the equality. Kept as the reference
per-completion reading the projection is proved against. -/
def rowAt (family : Family.FamilySpec) (context : ModelContext) (c : Family.Completion) :
    Row context :=
  prepareRow context (takeSnapshot family c)

/-- The status observation of one *supplied* prepared row: the rejection
reason, or the public status at the claim's fixed atom. The public value is
`Driver.PublicStatus`, so an `evidenceBlocked` result keeps its conditional
label. This reads a row the caller already holds, never a family plus context,
so no checker is re-run. -/
def statusRead {context : ModelContext} (row : Row context) (claim : ClaimId) :
    Except SourceRejection (Option Driver.PublicStatus) :=
  match row.view with
  | .error reason => .error reason
  | .ok _ => .ok (row.claimStatus claim)

theorem statusRead_rejected {context : ModelContext} {row : Row context} {claim : ClaimId}
    {reason : SourceRejection} (rejected : row.view = .error reason) :
    statusRead row claim = .error reason := by
  simp [statusRead, rejected]

theorem statusRead_accepted {context : ModelContext} {row : Row context} {claim : ClaimId}
    {view : Prepared} (accepted : row.view = .ok view) :
    statusRead row claim = .ok (row.claimStatus claim) := by
  simp [statusRead, accepted]

/-- The audit observation of one *supplied* prepared row: the rejection reason,
or the fixed-witness warrant at the claim. Rejected rows are kept as
rejections, never folded into a negative warrant. -/
def auditRead (context : ModelContext) (row : Row context) (claim : ClaimId)
    (witness : WitnessId) (profile : Profile Empty) : Except SourceRejection Bool :=
  match row.view with
  | .error reason => .error reason
  | .ok _ => .ok (warranted context row profile claim witness)

theorem auditRead_rejected {context : ModelContext} {row : Row context} {claim : ClaimId}
    {witness : WitnessId} {profile : Profile Empty} {reason : SourceRejection}
    (rejected : row.view = .error reason) :
    auditRead context row claim witness profile = .error reason := by
  simp [auditRead, rejected]

theorem auditRead_accepted {context : ModelContext} {row : Row context} {claim : ClaimId}
    {witness : WitnessId} {profile : Profile Empty} {view : Prepared}
    (accepted : row.view = .ok view) :
    auditRead context row claim witness profile =
      .ok (warranted context row profile claim witness) := by
  simp [auditRead, accepted]

/-- A read function indexed by an already-computed observation table: the
completion's entry, or the observation default for a completion outside the
table. The default is unreachable for the table's own completions
(`statusObservations_keys`, `tableRead_find?`): every completion of the table
is present, so the analyses below never see the default. -/
def tableRead {β : Type} [DecidableEq Family.Completion] [Inhabited β]
    (table : List (Family.Completion × Except SourceRejection β)) :
    Family.Completion → Except SourceRejection β :=
  fun c => (table.find? (fun p => decide (p.1 = c))).elim (.ok default) Prod.snd

theorem tableRead_find? {β : Type} [DecidableEq Family.Completion] [Inhabited β]
    (table : List (Family.Completion × Except SourceRejection β)) {c : Family.Completion}
    {o : Except SourceRejection β} (h : table.find? (fun p => decide (p.1 = c)) = some (c, o)) :
    tableRead table c = o := by
  simp [tableRead, h]

/-- A table indexed by its own keys reads back the entry a completion was
mapped from. Every pair sharing a key carries the same value, since the value is
recomputed from the key alone, so the first `find?` hit is the mapped entry even
when the key list repeats. -/
theorem find?_map_self {β : Type} [DecidableEq Family.Completion]
    (cs : List Family.Completion) (g : Family.Completion → Except SourceRejection β) :
    ∀ {c : Family.Completion}, c ∈ cs →
      (cs.map fun c' => (c', g c')).find? (fun p => decide (p.1 = c)) = some (c, g c) := by
  induction cs with
  | nil => intro c mem; exact absurd mem List.not_mem_nil
  | cons a t ih =>
      intro c mem
      rw [List.map_cons]
      by_cases h : a = c
      · subst h
        rw [List.find?_cons_of_pos (by simp)]
      · rw [List.find?_cons_of_neg (by simp [h])]
        exact ih (by
          rcases List.mem_cons.mp mem with h' | h'
          · exact absurd h'.symm h
          · exact h')

/-- `tableRead` over a table indexed by its own keys recovers the mapped value
for every completion of that table. -/
theorem tableRead_map_self {β : Type} [DecidableEq Family.Completion] [Inhabited β]
    (cs : List Family.Completion) (g : Family.Completion → Except SourceRejection β)
    {c : Family.Completion} (mem : c ∈ cs) :
    tableRead (cs.map fun c' => (c', g c')) c = g c :=
  tableRead_find? (cs.map fun c' => (c', g c')) (find?_map_self cs g mem)

/-- The completions of a checked family, in the family's order: definitionally
the family its rows were prepared from. -/
def checkedCompletions {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) : List Family.Completion :=
  checked.snapshots.map Snapshot.completion

theorem checkedCompletions_eq {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) :
    checkedCompletions checked = completions := by
  simp [checkedCompletions, checked.snapshots_eq, List.map_map, Function.comp_def, takeSnapshot]

/-- The status observation table of a checked family: computed in one pass over
the rows the family was checked with, one entry per completion. -/
def statusObservations {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) (claim : ClaimId) :
    List (Family.Completion × Except SourceRejection (Option Driver.PublicStatus)) :=
  checked.rows.map fun row => (row.snapshot.completion, statusRead row claim)

/-- The audit observation table of a checked family. -/
def auditObservations {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) (claim : ClaimId)
    (witness : WitnessId) (profile : Profile Empty) :
    List (Family.Completion × Except SourceRejection Bool) :=
  checked.rows.map fun row =>
    (row.snapshot.completion, auditRead checked.context row claim witness profile)

theorem statusObservations_map_snd {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) (claim : ClaimId) :
    (statusObservations checked claim).map Prod.snd =
      completions.map (fun c => statusRead (rowAt family checked.context c) claim) := by
  simp [statusObservations, rowAt, checked.rows_eq, checked.snapshots_eq, List.map_map,
    Function.comp_def]

theorem auditObservations_map_snd {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) (claim : ClaimId)
    (witness : WitnessId) (profile : Profile Empty) :
    (auditObservations checked claim witness profile).map Prod.snd =
      completions.map
        (fun c => auditRead checked.context (rowAt family checked.context c) claim witness profile) := by
  simp [auditObservations, rowAt, checked.rows_eq, checked.snapshots_eq, List.map_map,
    Function.comp_def]

theorem statusObservations_keys {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) (claim : ClaimId) :
    (statusObservations checked claim).map Prod.fst = checkedCompletions checked := by
  simp [statusObservations, checkedCompletions, checked.rows_eq, checked.snapshots_eq,
    List.map_map, Function.comp_def, prepareRow]

theorem auditObservations_keys {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) (claim : ClaimId)
    (witness : WitnessId) (profile : Profile Empty) :
    (auditObservations checked claim witness profile).map Prod.fst = checkedCompletions checked := by
  simp [auditObservations, checkedCompletions, checked.rows_eq, checked.snapshots_eq,
    List.map_map, Function.comp_def, prepareRow]

/-- The snapshot of a completion carries that completion back. -/
theorem takeSnapshot_completion (family : Family.FamilySpec)
    (completion : Family.Completion) :
    (takeSnapshot family completion).completion = completion := rfl

/-- The status observation table equals the per-completion `rowAt` reading, so
the observable-specific builders that consume `tableRead (statusObservations …)`
agree with the reference reading `statusRead (rowAt …)` on every completion of
the checked family. Derived from the table's own completion-indexed construction
(`checked.rows_eq`, `checked.snapshots_eq`, `takeSnapshot_completion`) and
`tableRead_find?`/`tableRead_map_self`, not assumed. -/
theorem statusObservations_tableRead {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) (claim : ClaimId)
    {c : Family.Completion} (mem : c ∈ completions) :
    tableRead (statusObservations checked claim) c =
      statusRead (rowAt family checked.context c) claim := by
  have h : statusObservations checked claim =
      completions.map (fun c' => (c', statusRead (rowAt family checked.context c') claim)) := by
    simp [statusObservations, rowAt, checked.rows_eq, checked.snapshots_eq, List.map_map,
      Function.comp_def, prepareRow, takeSnapshot_completion]
  rw [h]
  exact tableRead_map_self completions _ mem

/-- The audit counterpart of `statusObservations_tableRead`: the audit
observation table agrees with the per-completion `rowAt` audit reading on every
completion of the checked family. -/
theorem auditObservations_tableRead {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) (claim : ClaimId)
    (witness : WitnessId) (profile : Profile Empty)
    {c : Family.Completion} (mem : c ∈ completions) :
    tableRead (auditObservations checked claim witness profile) c =
      auditRead checked.context (rowAt family checked.context c) claim witness profile := by
  have h : auditObservations checked claim witness profile =
      completions.map (fun c' =>
        (c', auditRead checked.context (rowAt family checked.context c') claim witness profile)) := by
    simp [auditObservations, rowAt, checked.rows_eq, checked.snapshots_eq, List.map_map,
      Function.comp_def, prepareRow, takeSnapshot_completion]
  rw [h]
  exact tableRead_map_self completions _ mem

/-- The observable of a stability or sensitivity request. A status observable
is fixed by a claim: its atom is the claim's fixed binding, resolved inside the
family context, never re-derived from the materialized source. -/
inductive Observable where
  | status (claim : ClaimId)
  | audit (claim : ClaimId) (witness : WitnessId) (profile : Profile Empty)

/-- The target of a minimal-assumptions request: an exact public status
(including a blocked result's conditional label), or a positive
submitted-witness audit. -/
inductive Target where
  | status (claim : ClaimId) (expected : Driver.PublicStatus)
  | audit (claim : ClaimId) (witness : WitnessId) (profile : Profile Empty)

/-! ### Observation equality, stability and their Boolean specializations -/

section Stability

variable {β : Type} [DecidableEq β]

/-- Full-observation equality. -/
def SameObs (read : Family.Completion → Except SourceRejection β)
    (c d : Family.Completion) : Prop :=
  read c = read d

/-- Boolean specialization of full-observation equality. -/
def sameObsB (read : Family.Completion → Except SourceRejection β)
    (c d : Family.Completion) : Bool :=
  decide (read c = read d)

theorem sameObsB_iff (read : Family.Completion → Except SourceRejection β)
    (c d : Family.Completion) : sameObsB read c d = true ↔ SameObs read c d :=
  decide_eq_true_iff'

omit [DecidableEq β] in
theorem sameObs_refl (read : Family.Completion → Except SourceRejection β)
    (c : Family.Completion) : SameObs read c c := rfl

omit [DecidableEq β] in
theorem sameObs_symm (read : Family.Completion → Except SourceRejection β)
    {c d : Family.Completion} (h : SameObs read c d) : SameObs read d c := h.symm

omit [DecidableEq β] in
theorem sameObs_trans (read : Family.Completion → Except SourceRejection β)
    {c d e : Family.Completion} (h₁ : SameObs read c d) (h₂ : SameObs read d e) :
    SameObs read c e := h₁.trans h₂

/-- Whole-outcome stability: the family is nonempty and every pair of
completions has equal full observations. -/
def WholeStable (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) : Prop :=
  cs ≠ [] ∧ ∀ c ∈ cs, ∀ d ∈ cs, read c = read d

/-- Whole-outcome stability from an already-computed observation list:
nonempty and every entry equal to the first. This performs a single pass, so
the report is derived from one projection rather than pairwise reads. -/
def wholeStableProj (obs : List (Except SourceRejection β)) : Bool :=
  match obs with
  | [] => false
  | o :: _ => obs.all fun o' => decide (o' = o)

theorem wholeStableProj_iff (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) :
    wholeStableProj (cs.map read) = true ↔ WholeStable cs read := by
  unfold WholeStable
  cases cs with
  | nil => simp [wholeStableProj]
  | cons c cs =>
      simp only [List.map_cons, wholeStableProj]
      rw [List.all_eq_true]
      constructor
      · intro all
        refine ⟨by simp, fun x hx y hy => ?_⟩
        have hx' : read x ∈ read c :: cs.map read := by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact List.mem_cons.mpr (Or.inl rfl)
          · exact List.mem_cons.mpr (Or.inr (List.mem_map_of_mem hx))
        have hy' : read y ∈ read c :: cs.map read := by
          rcases List.mem_cons.mp hy with rfl | hy
          · exact List.mem_cons.mpr (Or.inl rfl)
          · exact List.mem_cons.mpr (Or.inr (List.mem_map_of_mem hy))
        exact (of_decide_eq_true (all (read x) hx')).trans
          (of_decide_eq_true (all (read y) hy')).symm
      · intro h
        obtain ⟨-, agree⟩ := h
        intro o ho
        rw [decide_eq_true_eq]
        rcases List.mem_cons.mp ho with rfl | ho
        · rfl
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ho
          exact agree x (List.mem_cons.mpr (Or.inr hx)) c (List.mem_cons.mpr (Or.inl rfl))

/-- Boolean specialization of whole-outcome stability, read from a single
projection of the family. -/
def wholeStableB (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) : Bool :=
  wholeStableProj (cs.map read)

theorem wholeStableB_iff (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) :
    wholeStableB cs read = true ↔ WholeStable cs read :=
  wholeStableProj_iff cs read

omit [DecidableEq β] in
theorem not_wholeStable_nil (read : Family.Completion → Except SourceRejection β) :
    ¬ WholeStable ([] : List Family.Completion) read :=
  fun h => h.1 rfl

omit [DecidableEq β] in
/-- Under a permutation the report is unchanged. -/
theorem wholeStable_perm {cs ds : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} (p : cs.Perm ds) :
    WholeStable cs read ↔ WholeStable ds read := by
  have hne : cs ≠ [] ↔ ds ≠ [] := by
    rw [← List.length_pos_iff, ← List.length_pos_iff, p.length_eq]
  constructor
  · rintro ⟨ne, agree⟩
    exact ⟨hne.mp ne, fun c hc d hd => agree c (p.mem_iff.mpr hc) d (p.mem_iff.mpr hd)⟩
  · rintro ⟨ne, agree⟩
    exact ⟨hne.mpr ne, fun c hc d hd => agree c (p.mem_iff.mp hc) d (p.mem_iff.mp hd)⟩

theorem wholeStableB_perm {cs ds : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} (p : cs.Perm ds) :
    wholeStableB cs read = wholeStableB ds read := by
  rw [Bool.eq_iff_iff, wholeStableB_iff, wholeStableB_iff, wholeStable_perm p]

/-- The completions whose observation is accepted (no source rejection). -/
def acceptedRows (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) : List Family.Completion :=
  cs.filter (fun c => (read c).isOk)

/-- The completions whose observation is a source rejection. -/
def rejectedRows (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) : List Family.Completion :=
  cs.filter (fun c => !(read c).isOk)

omit [DecidableEq β] in
theorem mem_acceptedRows {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {c : Family.Completion} :
    c ∈ acceptedRows cs read ↔ c ∈ cs ∧ (read c).isOk = true := by
  simp [acceptedRows, List.mem_filter]

omit [DecidableEq β] in
theorem mem_rejectedRows {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {c : Family.Completion} :
    c ∈ rejectedRows cs read ↔ c ∈ cs ∧ (read c).isOk = false := by
  simp [rejectedRows, List.mem_filter]

omit [DecidableEq β] in
theorem acceptedRows_nodup {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} (unique : cs.Nodup) :
    (acceptedRows cs read).Nodup := unique.filter _

omit [DecidableEq β] in
theorem rejectedRows_nodup {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} (unique : cs.Nodup) :
    (rejectedRows cs read).Nodup := unique.filter _

/-- The explicit accepted-only domain: the accepted rows, with the rejection
count kept separately so no reader has to infer it. -/
structure AcceptedDomain (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) where
  rows : List Family.Completion
  rows_eq : rows = acceptedRows cs read
  rejections : Nat
  rejections_eq : rejections = (rejectedRows cs read).length

/-- Accepted-only stability, always reported on its labelled domain rather than
substituted for whole-family stability. -/
def AcceptedStable (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) : Prop :=
  acceptedRows cs read ≠ [] ∧
    ∀ c ∈ acceptedRows cs read, ∀ d ∈ acceptedRows cs read, read c = read d

/-- The accepted entries of an already-computed observation list. -/
def acceptedProj (obs : List (Except SourceRejection β)) : List (Except SourceRejection β) :=
  obs.filter fun o => o.isOk

/-- Accepted-only stability from an already-computed observation list: nonempty
accepted entries, all equal to the first. -/
def acceptedStableProj (obs : List (Except SourceRejection β)) : Bool :=
  match acceptedProj obs with
  | [] => false
  | o :: _ => (acceptedProj obs).all fun o' => decide (o' = o)

theorem acceptedStableProj_spec (obs : List (Except SourceRejection β)) :
    acceptedStableProj obs = true ↔
      acceptedProj obs ≠ [] ∧
        ∀ o ∈ acceptedProj obs, ∀ o' ∈ acceptedProj obs, o = o' := by
  unfold acceptedStableProj
  cases h : acceptedProj obs with
  | nil => simp
  | cons o os =>
      rw [List.all_eq_true]
      constructor
      · intro all
        refine ⟨by simp, fun x hx y hy => ?_⟩
        exact (of_decide_eq_true (all x hx)).trans (of_decide_eq_true (all y hy)).symm
      · intro h
        obtain ⟨-, pw⟩ := h
        intro x hx
        rw [decide_eq_true_eq]
        exact pw x hx o (List.mem_cons.mpr (Or.inl rfl))

omit [DecidableEq β] in
theorem map_filter_isOk (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) :
    (cs.map read).filter (fun o => o.isOk) =
      (cs.filter fun c => (read c).isOk).map read := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      by_cases h : (read c).isOk = true
      · simp [List.map_cons, ih, h]
      · simp [List.map_cons, ih, h]

/-- Boolean specialization of accepted-only stability, read from a single
projection of the family. -/
def acceptedStableB (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) : Bool :=
  acceptedStableProj (cs.map read)

theorem acceptedStableB_iff (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) :
    acceptedStableB cs read = true ↔ AcceptedStable cs read := by
  unfold acceptedStableB AcceptedStable acceptedRows
  rw [acceptedStableProj_spec]
  simp only [acceptedProj]
  rw [map_filter_isOk]
  constructor
  · rintro ⟨ne, pw⟩
    refine ⟨fun h => ne (by rw [h]; rfl), fun c hc d hd => ?_⟩
    exact pw (read c) (List.mem_map_of_mem hc) (read d) (List.mem_map_of_mem hd)
  · rintro ⟨ne, pw⟩
    refine ⟨fun h => ne (List.map_eq_nil_iff.mp h), fun o ho o' ho' => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ho
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ho'
    exact pw c hc d hd

/-- An all-rejected family has no accepted domain: it may still be
outcome-stable, but it carries no public status and no positive audit. -/
theorem acceptedStableB_of_all_rejected {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β}
    (all : ∀ c ∈ cs, (read c).isOk = false) : acceptedStableB cs read = false := by
  have empty : (cs.filter fun c => (read c).isOk) = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro c hc
    obtain ⟨hc', hok⟩ := List.mem_filter.mp hc
    rw [all c hc'] at hok
    exact Bool.false_ne_true hok
  unfold acceptedStableB acceptedStableProj acceptedProj
  rw [map_filter_isOk, empty, List.map_nil]

/-! ### Partition by rejected reason or accepted value -/

/-- The distinct full observations of the family, in first-occurrence order. -/
def obsValues (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) : List (Except SourceRejection β) :=
  (cs.map read).dedup

/-- The complete partition of the family by observation: each bucket is a
distinct rejected reason or accepted value together with exactly the completions
carrying it. The observations are computed in one pass (the family is mapped
once), and the partition is then read out of that projection, so `read` is
applied exactly once per completion rather than once per (value, completion)
pair. -/
def buckets (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) :
    List (Except SourceRejection β × List Family.Completion) :=
  let paired := cs.map fun c => (read c, c)
  ((paired.map Prod.fst).dedup).map fun v =>
    (v, (paired.filter fun p => decide (p.1 = v)).map Prod.snd)

theorem filter_map_snd_pair (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (v : Except SourceRejection β) :
    ((cs.map fun c => (read c, c)).filter (fun p => decide (p.1 = v))).map Prod.snd =
      cs.filter fun c => decide (read c = v) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.map_cons, List.filter_cons]
      by_cases h : read c = v
      · simp [h, ih]
      · simp [h, ih]

/-- The projection form of `buckets`: the same partition as the value-indexed
`filter` definition, but with `read` already evaluated. -/
theorem buckets_eq (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) :
    buckets cs read = (obsValues cs read).map
      (fun v => (v, cs.filter fun c => decide (read c = v))) := by
  unfold buckets obsValues
  dsimp only
  have hkey : (cs.map fun c => (read c, c)).map Prod.fst = cs.map read := by
    simp [List.map_map, Function.comp_def]
  rw [hkey]
  simp only [filter_map_snd_pair]

theorem buckets_keys (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) :
    (buckets cs read).map Prod.fst = obsValues cs read := by
  rw [buckets_eq]
  simp [List.map_map, Function.comp_def]

theorem buckets_keys_nodup (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) :
    ((buckets cs read).map Prod.fst).Nodup := by
  rw [buckets_keys]; exact List.nodup_dedup _

theorem mem_obsValues {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {v : Except SourceRejection β} :
    v ∈ obsValues cs read ↔ v ∈ cs.map read := List.mem_dedup

theorem buckets_closed {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β}
    {b : Except SourceRejection β × List Family.Completion} (member : b ∈ buckets cs read)
    {c : Family.Completion} (inside : c ∈ b.2) :
    c ∈ cs ∧ read c = b.1 := by
  rw [buckets_eq] at member
  obtain ⟨v, _, heq⟩ := List.mem_map.mp member
  cases heq
  exact ⟨(List.mem_filter.mp inside).1, of_decide_eq_true (List.mem_filter.mp inside).2⟩

theorem buckets_nonempty {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β}
    {b : Except SourceRejection β × List Family.Completion} (member : b ∈ buckets cs read) :
    b.2 ≠ [] := by
  rw [buckets_eq] at member
  obtain ⟨v, vmem, heq⟩ := List.mem_map.mp member
  cases heq
  have : v ∈ cs.map read := List.mem_dedup.mp vmem
  obtain ⟨c, hc, hcv⟩ := List.mem_map.mp this
  exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hc, by simp [hcv]⟩)

theorem buckets_covers {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {c : Family.Completion}
    (member : c ∈ cs) :
    ∃ b ∈ buckets cs read, c ∈ b.2 := by
  refine ⟨(read c, cs.filter fun d => decide (read d = read c)), ?_, ?_⟩
  · rw [buckets_eq]
    exact List.mem_map.mpr ⟨read c, List.mem_dedup.mpr (List.mem_map.mpr ⟨c, member, rfl⟩), rfl⟩
  · exact List.mem_filter.mpr ⟨member, decide_eq_true_eq.mpr rfl⟩

/-- Two distinct buckets are disjoint. -/
theorem buckets_disjoint {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β}
    {b d : Except SourceRejection β × List Family.Completion}
    (hb : b ∈ buckets cs read) (hd : d ∈ buckets cs read) (keys : b.1 ≠ d.1)
    {c : Family.Completion} (cb : c ∈ b.2) (cd : c ∈ d.2) : False := by
  have left := (buckets_closed hb cb).2
  have right := (buckets_closed hd cd).2
  exact keys (left.symm.trans right)

/-- A bucket's members are exactly the family completions with its observation. -/
theorem buckets_second {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β}
    {b : Except SourceRejection β × List Family.Completion} (member : b ∈ buckets cs read) :
    b.2 = cs.filter (fun c => decide (read c = b.1)) := by
  rw [buckets_eq] at member
  obtain ⟨v, _, heq⟩ := List.mem_map.mp member
  cases heq; rfl

/-- The partition is complete: every completion lies in a bucket whose key is
correct, and any bucket containing it shares that key. -/
theorem buckets_mem_key {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {c : Family.Completion}
    (member : c ∈ cs) :
    ∃ b ∈ buckets cs read, c ∈ b.2 ∧
      ∀ d ∈ buckets cs read, c ∈ d.2 → d.1 = b.1 := by
  obtain ⟨b, hb, cb⟩ := buckets_covers (read := read) member
  refine ⟨b, hb, cb, fun d hd cd => ?_⟩
  have h1 : read c = b.1 := (buckets_closed hb cb).2
  have h2 : read c = d.1 := (buckets_closed hd cd).2
  exact h2.symm.trans h1

end Stability

/-! ### Reference and changed-slot sensitivity -/

/-- The choice a completion makes at a slot, if any. -/
def selectionFor (c : Family.Completion) (slot : SlotId) : Option Choice :=
  (c.assignment.find? (fun s => s.slot == slot)).map Selection.choice

/-- Exactly the slots whose chosen alternatives differ from the reference. -/
def changedSlots (spec : Family.FamilySpec) (reference c : Family.Completion) : List SlotId :=
  (spec.slots.filter (fun slot =>
    decide (selectionFor reference slot.id ≠ selectionFor c slot.id))).map Slot.id

theorem mem_changedSlots {spec : Family.FamilySpec} {reference c : Family.Completion}
    {slot : SlotId} :
    slot ∈ changedSlots spec reference c ↔
      slot ∈ spec.slots.map Slot.id ∧
        selectionFor reference slot ≠ selectionFor c slot := by
  unfold changedSlots
  rw [List.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨List.mem_map.mpr ⟨s, (List.mem_filter.mp hs).1, rfl⟩,
      of_decide_eq_true (List.mem_filter.mp hs).2⟩
  · rintro ⟨hslot, diff⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hslot
    exact ⟨s, List.mem_filter.mpr ⟨hs, decide_eq_true_eq.mpr diff⟩, rfl⟩

/-- The universe of slot identities a joint change set may range over. -/
def slotUniverse (spec : Family.FamilySpec) : List SlotId := (spec.slots.map Slot.id).dedup

theorem mem_slotUniverse {spec : Family.FamilySpec} {slot : SlotId} :
    slot ∈ slotUniverse spec ↔ slot ∈ spec.slots.map Slot.id := List.mem_dedup

theorem changedSlots_subset_universe {spec : Family.FamilySpec}
    {reference c : Family.Completion} : ∀ s ∈ changedSlots spec reference c, s ∈ slotUniverse spec :=
  fun _ h => mem_slotUniverse.mpr (mem_changedSlots.mp h).1

variable {β : Type} [DecidableEq β]

/-- Reference sensitivity: the completions whose full observation differs from
the named reference's. -/
def Sensitivity (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (reference : Family.Completion) :
    List Family.Completion :=
  cs.filter (fun c => decide (read c ≠ read reference))

theorem mem_Sensitivity {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {reference c : Family.Completion} :
    c ∈ Sensitivity cs read reference ↔ c ∈ cs ∧ read c ≠ read reference := by
  simp [Sensitivity, List.mem_filter]

/-- Boolean specialization of reference sensitivity. -/
def referenceSensitiveB (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (reference : Family.Completion) : Bool :=
  cs.any (fun c => decide (read c ≠ read reference))

theorem referenceSensitiveB_iff (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (reference : Family.Completion) :
    referenceSensitiveB cs read reference = true ↔ Sensitivity cs read reference ≠ [] := by
  unfold referenceSensitiveB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, hc, diff⟩
    exact List.ne_nil_of_mem (mem_Sensitivity.mpr ⟨hc, of_decide_eq_true diff⟩)
  · intro hne
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨c, (mem_Sensitivity.mp hc).1, decide_eq_true_eq.mpr (mem_Sensitivity.mp hc).2⟩

theorem sensitivity_perm {cs ds : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {reference : Family.Completion}
    (p : cs.Perm ds) : (Sensitivity cs read reference).Perm (Sensitivity ds read reference) :=
  (p.filter _)

/-- With the reference among the family, no completion flips the observation
exactly when the family is outcome-stable. -/
theorem sensitivity_empty_iff_wholeStable (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) {reference : Family.Completion}
    (mem : reference ∈ cs) :
    Sensitivity cs read reference = [] ↔ WholeStable cs read := by
  unfold Sensitivity WholeStable
  rw [List.filter_eq_nil_iff]
  constructor
  · intro none
    refine ⟨List.ne_nil_of_mem mem, fun c hc d hd => ?_⟩
    have hc' : read c = read reference := by
      by_contra h
      exact absurd (decide_eq_true_eq.mpr h) (none c hc)
    have hd' : read d = read reference := by
      by_contra h
      exact absurd (decide_eq_true_eq.mpr h) (none d hd)
    exact hc'.trans hd'.symm
  · rintro ⟨_, agree⟩ c hc
    simp [agree c hc reference mem]

/-- The comparison inquiry: the positions of the family form a finite inquiry
whose carrier needs no `DecidableEq` on rows. -/
def positions (cs : List Family.Completion) : Inquiry (Fin cs.length) :=
  ⟨Finset.univ⟩

omit [DecidableEq β] in
/-- Compatibility with the landed `Inquiry` stability law: whole-outcome
stability is determinacy of the indexed observation. -/
theorem wholeStable_iff_positions (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (j : Fin cs.length) :
    WholeStable cs read ↔
      (positions cs).Stable (fun i => read (cs.get i) = read (cs.get j)) := by
  unfold WholeStable Inquiry.Stable positions
  constructor
  · rintro ⟨_, agree⟩
    refine ⟨⟨j, Finset.mem_univ j⟩, fun i _ k _ => ?_⟩
    have hik := agree (cs.get i) (List.get_mem cs i) (cs.get k) (List.get_mem cs k)
    exact ⟨fun h => hik.symm.trans h, fun h => hik.trans h⟩
  · rintro ⟨_, agree⟩
    refine ⟨?_, fun c hc d hd => ?_⟩
    · intro h
      rw [h] at j
      exact nomatch j
    · obtain ⟨i, hi⟩ := List.get_of_mem hc
      obtain ⟨k, hk⟩ := List.get_of_mem hd
      have h1 : read (cs.get i) = read (cs.get j) :=
        (agree i (Finset.mem_univ i) j (Finset.mem_univ j)).mpr rfl
      have h2 : read (cs.get k) = read (cs.get j) :=
        (agree k (Finset.mem_univ k) j (Finset.mem_univ j)).mpr rfl
      rw [← hi, ← hk]
      exact h1.trans h2.symm

/-- Compatibility with the landed `Inquiry.sensitivity_empty_iff_stable`:
emptiness of this module's list-level sensitivity is the landed emptiness of
the inquiry's finset-level sensitivity. -/
theorem sensitivity_empty_iff_inquiry (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (j : Fin cs.length) :
    Sensitivity cs read (cs.get j) = [] ↔
      (positions cs).sensitivity (fun i => read (cs.get i) = read (cs.get j)) j = ∅ :=
  (sensitivity_empty_iff_wholeStable cs read (List.get_mem cs j)).trans
    ((wholeStable_iff_positions cs read j).trans
      (Inquiry.sensitivity_empty_iff_stable (positions cs)
        (fun i => read (cs.get i) = read (cs.get j)) (reference := j) (Finset.mem_univ j)).symm)

/-! ### Changed slots, single-slot and joint sensitivity -/

/-- One differing row of a slot-sensitivity analysis: the completion and the
exact set of slots whose choices differ from the reference. -/
structure SensitivityRow where
  completion : Family.Completion
  changed : List SlotId
  deriving DecidableEq

/-- The differing rows: same history as the reference, different observation. -/
def differingRows (spec : Family.FamilySpec) (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (reference : Family.Completion) :
    List SensitivityRow :=
  (cs.filter (fun c =>
    decide (read c ≠ read reference) &&
      decide (c.history = reference.history))).map
    (fun c => ⟨c, changedSlots spec reference c⟩)

theorem mem_differingRows {spec : Family.FamilySpec} {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {reference : Family.Completion}
    {row : SensitivityRow} :
    row ∈ differingRows spec cs read reference ↔
      row.completion ∈ cs ∧ read row.completion ≠ read reference ∧
        row.completion.history = reference.history ∧
        row.changed = changedSlots spec reference row.completion := by
  unfold differingRows
  rw [List.mem_map]
  constructor
  · rintro ⟨c, hc, heq⟩
    rw [List.mem_filter, Bool.and_eq_true] at hc
    cases heq
    exact ⟨hc.1, of_decide_eq_true hc.2.1, of_decide_eq_true hc.2.2, rfl⟩
  · rintro ⟨hc, diff, hist, hch⟩
    refine ⟨row.completion, ?_, ?_⟩
    · exact List.mem_filter.mpr ⟨hc, by simp [diff, hist]⟩
    · cases row; simp_all

/-- A change set admits a flip when some completion with the reference's
history changes only slots inside it and lands on a different observation. -/
def AdmitsFlip (spec : Family.FamilySpec) (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (reference : Family.Completion)
    (S : List SlotId) : Prop :=
  ∃ c ∈ cs, c.history = reference.history ∧
    (∀ s ∈ changedSlots spec reference c, s ∈ S) ∧ read c ≠ read reference

/-- Boolean specialization of `AdmitsFlip`. -/
def admitsFlipB (spec : Family.FamilySpec) (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (reference : Family.Completion)
    (S : List SlotId) : Bool :=
  cs.any (fun c =>
    decide (c.history = reference.history) &&
      decide (∀ s ∈ changedSlots spec reference c, s ∈ S) &&
      decide (read c ≠ read reference))

theorem admitsFlipB_iff (spec : Family.FamilySpec) (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (reference : Family.Completion)
    (S : List SlotId) : admitsFlipB spec cs read reference S = true ↔
      AdmitsFlip spec cs read reference S := by
  unfold admitsFlipB AdmitsFlip
  rw [List.any_eq_true]
  constructor
  · rintro ⟨c, hc, h⟩
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    exact ⟨c, hc, of_decide_eq_true h.1.1, fun s hs => of_decide_eq_true h.1.2 s hs,
      of_decide_eq_true h.2⟩
  · rintro ⟨c, hc, hist, inside, diff⟩
    refine ⟨c, hc, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨decide_eq_true_eq.mpr hist, decide_eq_true_eq.mpr inside⟩, decide_eq_true_eq.mpr diff⟩

omit [DecidableEq β] in
theorem admitsFlip_perm {spec : Family.FamilySpec} {cs ds : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {reference : Family.Completion}
    (p : cs.Perm ds) {S : List SlotId} :
    AdmitsFlip spec cs read reference S ↔ AdmitsFlip spec ds read reference S := by
  unfold AdmitsFlip
  constructor
  · rintro ⟨c, hc, hist, inside, diff⟩
    exact ⟨c, p.mem_iff.mp hc, hist, inside, diff⟩
  · rintro ⟨c, hc, hist, inside, diff⟩
    exact ⟨c, p.mem_iff.mpr hc, hist, inside, diff⟩

theorem admitsFlipB_perm {spec : Family.FamilySpec} {cs ds : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {reference : Family.Completion}
    (p : cs.Perm ds) (S : List SlotId) :
    admitsFlipB spec cs read reference S = admitsFlipB spec ds read reference S := by
  rw [Bool.eq_iff_iff, admitsFlipB_iff, admitsFlipB_iff, admitsFlip_perm p]

omit [DecidableEq β] in
/-- Admitting a flip is monotone in the change set. -/
theorem admitsFlip_mono {spec : Family.FamilySpec} {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {reference : Family.Completion}
    {S T : List SlotId} (cover : ∀ s ∈ S, s ∈ T) (h : AdmitsFlip spec cs read reference S) :
    AdmitsFlip spec cs read reference T := by
  obtain ⟨c, hc, hist, inside, diff⟩ := h
  exact ⟨c, hc, hist, fun s hs => cover s (inside s hs), diff⟩

/-- Inclusion-minimality of a change set: nonempty, admits a flip, and no
nonempty proper sublist admits one. -/
def SlotMinimal (spec : Family.FamilySpec) (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (reference : Family.Completion)
    (S : List SlotId) : Prop :=
  S ≠ [] ∧ AdmitsFlip spec cs read reference S ∧
    ∀ T, T.Sublist S → T ≠ S → T ≠ [] → ¬ AdmitsFlip spec cs read reference T

/-- A proper sublist is contained in an immediate removal of the larger list:
drop a position the sublist does not use. -/
theorem sublist_exists_eraseIdx {α : Type} (s : List α) {t : List α}
    (sub : List.Sublist t s) (ne : t ≠ s) :
    ∃ i, i < s.length ∧ List.Sublist t (s.eraseIdx i) := by
  induction s generalizing t with
  | nil =>
      cases sub with
      | slnil => exact absurd rfl ne
  | cons a s ih =>
      cases sub with
      | cons _ h' => exact ⟨0, by simp, by simpa using h'⟩
      | cons_cons _ h' =>
          obtain ⟨i, hi, hsub⟩ := ih h' (fun he => ne (by rw [he]))
          exact ⟨i + 1, by simpa using Nat.succ_lt_succ hi,
            by simpa using List.Sublist.cons_cons a hsub⟩

/-- Boolean specialization of `SlotMinimal`. Testing the immediate removals of
`S` is sufficient and equivalent to testing every nonempty proper sublist:
`sublist_exists_eraseIdx` embeds any proper sublist in an immediate removal,
and `admitsFlip_mono` lifts a flip from the sublist to that removal. -/
def slotMinimalB (spec : Family.FamilySpec) (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (reference : Family.Completion)
    (S : List SlotId) : Bool :=
  decide (S ≠ []) && admitsFlipB spec cs read reference S &&
    (List.range S.length).all (fun i =>
      decide (S.eraseIdx i = []) || !admitsFlipB spec cs read reference (S.eraseIdx i))

theorem slotMinimalB_iff (spec : Family.FamilySpec) (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (reference : Family.Completion)
    (S : List SlotId) :
    slotMinimalB spec cs read reference S = true ↔ SlotMinimal spec cs read reference S := by
  unfold slotMinimalB SlotMinimal
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨⟨nonempty, flip⟩, min⟩
    refine ⟨of_decide_eq_true nonempty, (admitsFlipB_iff _ _ _ _ _).mp flip, ?_⟩
    intro T hsub hne hnil hflip
    obtain ⟨i, hi, hsubi⟩ := sublist_exists_eraseIdx S hsub hne
    have hnei : S.eraseIdx i ≠ [] := fun h => hnil (List.sublist_nil.mp (h ▸ hsubi))
    have hclause := min i (List.mem_range.mpr hi)
    rw [Bool.or_eq_true] at hclause
    rcases hclause with h | h
    · exact absurd (of_decide_eq_true h) hnei
    · rw [Bool.not_eq_true'] at h
      exact absurd ((admitsFlipB_iff _ _ _ _ _).mpr (admitsFlip_mono hsubi.subset hflip))
        (by rw [h]; decide)
  · rintro ⟨nonempty, flip, min⟩
    refine ⟨⟨decide_eq_true_eq.mpr nonempty, (admitsFlipB_iff _ _ _ _ _).mpr flip⟩, ?_⟩
    intro i hi
    rw [Bool.or_eq_true]
    by_cases he : S.eraseIdx i = []
    · exact Or.inl (decide_eq_true_eq.mpr he)
    · refine Or.inr ?_
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      intro hf
      have hsub : (S.eraseIdx i).Sublist S := List.eraseIdx_sublist S i
      have hneS : S.eraseIdx i ≠ S := fun h =>
        Nat.not_le_of_lt (List.mem_range.mp hi) (List.eraseIdx_eq_self.mp h)
      exact min (S.eraseIdx i) hsub hneS he ((admitsFlipB_iff _ _ _ _ _).mp hf)

omit [DecidableEq β] in
theorem slotMinimal_perm {spec : Family.FamilySpec} {cs ds : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {reference : Family.Completion}
    (p : cs.Perm ds) {S : List SlotId} :
    SlotMinimal spec cs read reference S ↔ SlotMinimal spec ds read reference S := by
  unfold SlotMinimal
  rw [admitsFlip_perm p]
  constructor
  · rintro ⟨ne, flip, min⟩
    exact ⟨ne, flip, fun T hsub hne' hnil => (min T hsub hne' hnil) ∘ (admitsFlip_perm p).mpr⟩
  · rintro ⟨ne, flip, min⟩
    exact ⟨ne, flip, fun T hsub hne' hnil => (min T hsub hne' hnil) ∘ (admitsFlip_perm p).mp⟩

/-- The inclusion-minimal nonempty change sets admitting a flip, in canonical
subset order. Every such set is returned, not one minimum-cardinality set. -/
def minimalSlotSets (spec : Family.FamilySpec) (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (reference : Family.Completion) :
    List (List SlotId) :=
  (slotUniverse spec).sublists.filter (slotMinimalB spec cs read reference)

theorem mem_minimalSlotSets {spec : Family.FamilySpec} {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {reference : Family.Completion}
    {S : List SlotId} :
    S ∈ minimalSlotSets spec cs read reference ↔
      S.Sublist (slotUniverse spec) ∧ SlotMinimal spec cs read reference S := by
  simp [minimalSlotSets, List.mem_filter, List.mem_sublists, slotMinimalB_iff]

theorem minimalSlotSets_sound {spec : Family.FamilySpec} {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {reference : Family.Completion}
    {S : List SlotId} (member : S ∈ minimalSlotSets spec cs read reference) :
    SlotMinimal spec cs read reference S :=
  (mem_minimalSlotSets.mp member).2

theorem minimalSlotSets_complete {spec : Family.FamilySpec} {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {reference : Family.Completion}
    {S : List SlotId} (sub : S.Sublist (slotUniverse spec))
    (min : SlotMinimal spec cs read reference S) :
    S ∈ minimalSlotSets spec cs read reference :=
  mem_minimalSlotSets.mpr ⟨sub, min⟩

theorem nil_sublist {α : Type} (l : List α) : ([] : List α).Sublist l := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a t ih => exact List.Sublist.cons a ih

theorem singleton_sublist {α : Type} {a : α} {l : List α} (h : a ∈ l) :
    [a].Sublist l := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact List.Sublist.cons_cons a (nil_sublist t)
      · exact List.Sublist.cons b (ih h)

theorem sublist_nil {α : Type} {T : List α} (h : T.Sublist []) : T = [] := by
  cases h with
  | slnil => rfl

theorem sublist_singleton {α : Type} {s : α} {T : List α} (h : T.Sublist [s]) :
    T = [] ∨ T = [s] := by
  cases h with
  | cons _ h => exact Or.inl (sublist_nil h)
  | cons_cons _ h => exact Or.inr (by rw [sublist_nil h])

/-- A realizing completion for a joint change set. -/
def realizing (spec : Family.FamilySpec) (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (reference : Family.Completion)
    (S : List SlotId) : Option Family.Completion :=
  cs.find? (fun c =>
    decide (c.history = reference.history) &&
      decide (∀ s ∈ changedSlots spec reference c, s ∈ S) &&
      decide (read c ≠ read reference))

theorem realizing_spec {spec : Family.FamilySpec} {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {reference : Family.Completion}
    {S : List SlotId} {c : Family.Completion} (found : realizing spec cs read reference S = some c) :
    c ∈ cs ∧ c.history = reference.history ∧
      (∀ s ∈ changedSlots spec reference c, s ∈ S) ∧ read c ≠ read reference := by
  have h := List.find?_some found
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨List.mem_of_find?_eq_some found, of_decide_eq_true h.1.1,
    fun s hs => of_decide_eq_true h.1.2 s hs, of_decide_eq_true h.2⟩

/-- Singleton equivalence: a singleton change set is minimal exactly when it
admits a flip, because its only nonempty sublist is itself. -/
theorem singleton_minimal_iff {spec : Family.FamilySpec} {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {reference : Family.Completion}
    {s : SlotId} (mem : s ∈ slotUniverse spec) :
    [s] ∈ minimalSlotSets spec cs read reference ↔ AdmitsFlip spec cs read reference [s] := by
  rw [mem_minimalSlotSets]
  constructor
  · rintro ⟨_, _, flip, _⟩
    exact flip
  · intro flip
    refine ⟨singleton_sublist mem, ⟨by simp, flip, ?_⟩⟩
    intro T hsub hne hnil hflip
    rcases sublist_singleton hsub with rfl | rfl
    · exact hnil rfl
    · exact hne rfl

/-! ### Minimal conditional assumptions over a literal catalog -/

section Assumptions

/-- The finite user-declared catalog of conditional literals: slot
equality/inequality, event presence/absence, event precedence, or an existing
process formula and its negation. -/
inductive Literal where
  | slotEq (slot : SlotId) (choice : ChoiceId)
  | slotNe (slot : SlotId) (choice : ChoiceId)
  | present (event : Stamped)
  | absent (event : Stamped)
  | before (first second : Stamped)
  | formula (query : Universe.Query)
  | notFormula (query : Universe.Query)
  deriving DecidableEq

/-- Propositional semantics of a literal at a completion. -/
def Literal.Holds (lit : Literal) (c : Family.Completion) : Prop :=
  match lit with
  | .slotEq slot choice => (selectionFor c slot).map Choice.id = some choice
  | .slotNe slot choice => (selectionFor c slot).map Choice.id ≠ some choice
  | .present event => (Guard.present event).Holds c.history
  | .absent event => ¬ (Guard.present event).Holds c.history
  | .before first second => (Guard.before first second).Holds c.history
  | .formula query => query.holds Universe.Atom.holds c.history
  | .notFormula query => ¬ query.holds Universe.Atom.holds c.history

/-- Boolean interpreter, independent of the propositional semantics. -/
def Literal.holdsB : Literal → Family.Completion → Bool
  | .slotEq slot choice, c => decide ((selectionFor c slot).map Choice.id = some choice)
  | .slotNe slot choice, c => decide ((selectionFor c slot).map Choice.id ≠ some choice)
  | .present event, c => (Guard.present event).eval c.history
  | .absent event, c => !(Guard.present event).eval c.history
  | .before first second, c => (Guard.before first second).eval c.history
  | .formula query, c => decide (query.holds Universe.Atom.holds c.history)
  | .notFormula query, c => decide (¬ query.holds Universe.Atom.holds c.history)

theorem Literal.holdsB_iff (lit : Literal) (c : Family.Completion) :
    lit.holdsB c = true ↔ lit.Holds c := by
  cases lit with
  | slotEq slot choice => exact decide_eq_true_iff'
  | slotNe slot choice => exact decide_eq_true_iff'
  | present event => exact Guard.eval_iff (.present event) c.history
  | absent event =>
      simp only [Literal.holdsB, Literal.Holds]
      rw [Bool.not_eq_true', Bool.eq_false_iff]
      exact not_congr (Guard.eval_iff (.present event) c.history)
  | before first second => exact Guard.eval_iff (.before first second) c.history
  | formula query => exact decide_eq_true_iff'
  | notFormula query => exact decide_eq_true_iff'

/-- Filter the original family by a literal set. -/
def restrict (cs : List Family.Completion) (L : List Literal) : List Family.Completion :=
  cs.filter (fun c => L.all (fun lit => lit.holdsB c))

theorem mem_restrict {cs : List Family.Completion} {L : List Literal}
    {c : Family.Completion} :
    c ∈ restrict cs L ↔ c ∈ cs ∧ ∀ lit ∈ L, lit.Holds c := by
  simp only [restrict, List.mem_filter, List.all_eq_true, Literal.holdsB_iff]

theorem restrict_perm {cs ds : List Family.Completion} {L : List Literal}
    (p : cs.Perm ds) : (restrict cs L).Perm (restrict ds L) := p.filter _

theorem restrict_mono {cs : List Family.Completion} {L T : List Literal}
    (sub : ∀ lit ∈ L, lit ∈ T) :
    ∀ c ∈ restrict cs T, c ∈ restrict cs L := by
  intro c hc
  obtain ⟨hcs, holds⟩ := mem_restrict.mp hc
  exact mem_restrict.mpr ⟨hcs, fun lit hl => holds lit (sub lit hl)⟩

/-- The requested target on every surviving row, with no rejections. -/
def Satisfies (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (target : β) (L : List Literal) : Prop :=
  restrict cs L ≠ [] ∧ ∀ c ∈ restrict cs L, read c = .ok target

/-- Boolean specialization of `Satisfies`. -/
def satisfiesB (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (target : β) (L : List Literal) : Bool :=
  decide (restrict cs L ≠ [] ∧ ∀ c ∈ restrict cs L, read c = .ok target)

theorem satisfiesB_iff (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (target : β) (L : List Literal) :
    satisfiesB cs read target L = true ↔ Satisfies cs read target L :=
  decide_eq_true_iff'

omit [DecidableEq β] in
/-- Every surviving row is accepted and carries exactly the target value. -/
theorem satisfied_no_rejection {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {target : β} {L : List Literal}
    (sat : Satisfies cs read target L) {c : Family.Completion} (hc : c ∈ restrict cs L) :
    (read c).isOk = true := by
  rw [sat.2 c hc]; rfl

omit [DecidableEq β] in
theorem satisfies_perm {cs ds : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {target : β} {L : List Literal}
    (p : cs.Perm ds) : Satisfies cs read target L ↔ Satisfies ds read target L := by
  have hp := restrict_perm p (L := L)
  have hne : restrict cs L ≠ [] ↔ restrict ds L ≠ [] := by
    rw [← List.length_pos_iff, ← List.length_pos_iff, hp.length_eq]
  unfold Satisfies
  rw [hne]
  constructor
  · rintro ⟨ne, all⟩
    exact ⟨ne, fun c hc => all c (hp.mem_iff.mpr hc)⟩
  · rintro ⟨ne, all⟩
    exact ⟨ne, fun c hc => all c (hp.mem_iff.mp hc)⟩

/-- Subset-minimality among the sublists of `L`. -/
def MinimalAssumption (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (target : β) (L : List Literal) : Prop :=
  Satisfies cs read target L ∧
    ∀ T, T.Sublist L → T ≠ L → ¬ Satisfies cs read target T

/-- Boolean specialization of `MinimalAssumption`. Testing the immediate
removals of `L` is sufficient and equivalent to testing every proper sublist:
`sublist_exists_eraseIdx` embeds any proper sublist in an immediate removal, and
`satisfies_mono` (upward persistence) lifts satisfaction from the sublist to
that removal, so only `remove`-by-position needs to fail. -/
def minimalAssumptionB (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (target : β) (L : List Literal) : Bool :=
  satisfiesB cs read target L &&
    (List.range L.length).all (fun i => !satisfiesB cs read target (L.eraseIdx i))

theorem minimalAssumptionB_iff (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (target : β) (L : List Literal) :
    minimalAssumptionB cs read target L = true ↔ MinimalAssumption cs read target L := by
  unfold minimalAssumptionB MinimalAssumption
  rw [Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨sat, min⟩
    refine ⟨(satisfiesB_iff _ _ _ _).mp sat, ?_⟩
    intro T hsub hne hsat
    obtain ⟨i, hi, hsubi⟩ := sublist_exists_eraseIdx L hsub hne
    have hsubL : ∀ c ∈ restrict cs L, c ∈ restrict cs (L.eraseIdx i) :=
      restrict_mono (fun lit hl => (List.eraseIdx_sublist L i).subset hl)
    have nonempty : restrict cs (L.eraseIdx i) ≠ [] := by
      intro hnil
      exact ((satisfiesB_iff _ _ _ _).mp sat).1
        (List.subset_nil.mp fun c hc => hnil ▸ hsubL c hc)
    have hsati : Satisfies cs read target (L.eraseIdx i) :=
      ⟨nonempty, fun c hc => hsat.2 c (restrict_mono (fun lit hl => hsubi.subset hl) c hc)⟩
    have hfalse := min i (List.mem_range.mpr hi)
    rw [Bool.not_eq_true'] at hfalse
    exact absurd ((satisfiesB_iff _ _ _ _).mpr hsati) (by rw [hfalse]; decide)
  · rintro ⟨sat, min⟩
    refine ⟨(satisfiesB_iff _ _ _ _).mpr sat, ?_⟩
    intro i hi
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro hsat
    have hsub : (L.eraseIdx i).Sublist L := List.eraseIdx_sublist L i
    have hne : L.eraseIdx i ≠ L := fun h =>
      Nat.not_le_of_lt (List.mem_range.mp hi) (List.eraseIdx_eq_self.mp h)
    exact min (L.eraseIdx i) hsub hne ((satisfiesB_iff _ _ _ _).mp hsat)

/-- Every subset-minimal satisfying literal set, in canonical subset order. -/
def minimalAssumptions (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (target : β)
    (catalog : List Literal) : List (List Literal) :=
  catalog.dedup.sublists.filter (minimalAssumptionB cs read target)

theorem mem_minimalAssumptions {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {target : β}
    {catalog : List Literal} {L : List Literal} :
    L ∈ minimalAssumptions cs read target catalog ↔
      L.Sublist catalog.dedup ∧ MinimalAssumption cs read target L := by
  simp [minimalAssumptions, List.mem_filter, List.mem_sublists, minimalAssumptionB_iff]

theorem minimalAssumptions_sound {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {target : β}
    {catalog : List Literal} {L : List Literal}
    (member : L ∈ minimalAssumptions cs read target catalog) :
    MinimalAssumption cs read target L :=
  (mem_minimalAssumptions.mp member).2

theorem minimalAssumptions_complete {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {target : β}
    {catalog : List Literal} {L : List Literal} (sub : L.Sublist catalog.dedup)
    (min : MinimalAssumption cs read target L) :
    L ∈ minimalAssumptions cs read target catalog :=
  mem_minimalAssumptions.mpr ⟨sub, min⟩

omit [DecidableEq β] in
/-- Upward persistence among consistent restrictions: a superset of a
satisfying set that stays nonempty still satisfies. -/
theorem satisfies_mono {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {target : β}
    {L T : List Literal} (sub : ∀ lit ∈ L, lit ∈ T)
    (sat : Satisfies cs read target L) (nonempty : restrict cs T ≠ []) :
    Satisfies cs read target T :=
  ⟨nonempty, fun c hc => sat.2 c (restrict_mono sub c hc)⟩

/-- The immediate deletion of a minimal literal: the smaller set fails. -/
def removeLit (L : List Literal) (lit : Literal) : List Literal :=
  L.filter (fun l => decide (l ≠ lit))

theorem removeLit_sublist (L : List Literal) (lit : Literal) :
    (removeLit L lit).Sublist L :=
  List.filter_sublist

theorem removeLit_ne {L : List Literal} {lit : Literal} (mem : lit ∈ L) :
    removeLit L lit ≠ L := by
  intro h
  have : lit ∈ removeLit L lit := h.symm ▸ mem
  simp only [removeLit, List.mem_filter, decide_eq_true_eq] at this
  exact this.2 rfl

omit [DecidableEq β] in
theorem deletion_fails {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {target : β}
    {L : List Literal} {lit : Literal} (min : MinimalAssumption cs read target L)
    (mem : lit ∈ L) : ¬ Satisfies cs read target (removeLit L lit) :=
  min.2 (removeLit L lit) (removeLit_sublist L lit) (removeLit_ne mem)

/-- The countercompletion found for a deleted literal: a surviving completion
whose observation is not the target, or `none` when the reduced restriction is
empty. -/
def deletionCounter (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (target : β)
    (L : List Literal) (lit : Literal) : Option Family.Completion :=
  (restrict cs (removeLit L lit)).find? (fun c => decide (read c ≠ .ok target))

theorem deletionCounter_spec {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {target : β}
    {L : List Literal} {lit : Literal} {c : Family.Completion}
    (found : deletionCounter cs read target L lit = some c) :
    c ∈ restrict cs (removeLit L lit) ∧ read c ≠ .ok target := by
  unfold deletionCounter at found
  refine ⟨List.mem_of_find?_eq_some found, of_decide_eq_true ?_⟩
  exact List.find?_some (p := fun c => decide (read c ≠ .ok target))
    (l := restrict cs (removeLit L lit)) (a := c) found

/-- For every literal of a minimal set the immediate deletion fails, and either
the reduced restriction is empty or a countercompletion is found in it. -/
theorem deletion_witness {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {target : β}
    {L : List Literal} {lit : Literal} (min : MinimalAssumption cs read target L)
    (mem : lit ∈ L) :
    restrict cs (removeLit L lit) = [] ∨
      ∃ c, deletionCounter cs read target L lit = some c ∧ c ∈ cs ∧ read c ≠ .ok target := by
  by_cases empty : restrict cs (removeLit L lit) = []
  · exact Or.inl empty
  · refine Or.inr ?_
    have bad : ∃ c ∈ restrict cs (removeLit L lit), read c ≠ .ok target := by
      by_contra h
      refine deletion_fails min mem ⟨empty, fun c hc => ?_⟩
      by_contra hne
      exact h ⟨c, hc, hne⟩
    obtain ⟨c, hc, hdiff⟩ := bad
    have hex : deletionCounter cs read target L lit ≠ none := by
      intro hnone
      unfold deletionCounter at hnone
      exact absurd (List.find?_eq_none.mp hnone c hc) (by simp [hdiff])
    cases found : deletionCounter cs read target L lit with
    | none => exact absurd found hex
    | some d =>
        unfold deletionCounter at found
        refine ⟨d, rfl, (mem_restrict.mp (List.mem_of_find?_eq_some found)).1, of_decide_eq_true ?_⟩
        exact List.find?_some (p := fun c => decide (read c ≠ .ok target))
          (l := restrict cs (removeLit L lit)) (a := d) found

omit [DecidableEq β] in
/-- The empty set satisfies exactly when the whole family is nonempty and every
row carries the target. -/
theorem satisfies_nil (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (target : β) :
    Satisfies cs read target [] ↔ cs ≠ [] ∧ ∀ c ∈ cs, read c = .ok target := by
  unfold Satisfies restrict
  simp

/-- If the whole family already satisfies, the empty set is the minimal
assumption set and it is returned. -/
theorem minimalAssumptions_empty_mem {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {target : β}
    {catalog : List Literal} (sat : Satisfies cs read target []) :
    [] ∈ minimalAssumptions cs read target catalog := by
  refine minimalAssumptions_complete (nil_sublist _) ⟨sat, ?_⟩
  intro T hsub hne _
  exact absurd (sublist_nil hsub) hne

end Assumptions

/-! ### Result records -/

/-- A stability result: the observable, exact counts, whole-outcome stability
and accepted-only stability on its labelled domain. -/
structure StabilityResult (Obs : Type) where
  observable : Obs
  total : Nat
  accepted : Nat
  rejected : Nat
  wholeStable : Bool
  acceptedDomainStable : Bool

/-- A sensitivity result: the observable, the named reference, counts, every
differing row with its exact changed-slot set, every inclusion-minimal joint
change set, and a realizing completion for each. -/
structure SensitivityResult (Obs : Type) where
  observable : Obs
  reference : Family.Completion
  total : Nat
  sensitive : Nat
  differing : List SensitivityRow
  minimalSlotSets : List (List SlotId)
  realizing : List (List SlotId × Family.Completion)

/-- One literal deleted from a minimal set, its surviving family, and its
immediate-deletion countercompletion. `deletionOf` is public and unguarded, so
the counter is `none` exactly when the reduced restriction is empty *or* when
every surviving row already carries the target; the guaranteed statement under
`MinimalAssumption` is `deletion_witness`. -/
structure Deletion where
  literal : Literal
  surviving : List Family.Completion
  counter : Option Family.Completion

/-- One minimal assumption set with its surviving family and deletions. -/
structure MinimalSet where
  literals : List Literal
  surviving : List Family.Completion
  deletions : List Deletion

/-- A minimal-assumptions result: the target, the declared catalog, counts and
every minimal literal set with its surviving family and deletions. -/
structure AssumptionResult (Tgt : Type) where
  target : Tgt
  catalog : List Literal
  total : Nat
  minimal : List MinimalSet

def stabilityResult {Obs : Type} (obs : Obs) {β : Type} [DecidableEq β]
    (cs : List Family.Completion) (read : Family.Completion → Except SourceRejection β) :
    StabilityResult Obs :=
  let proj := cs.map read
  { observable := obs
    total := proj.length
    accepted := (acceptedProj proj).length
    rejected := (proj.filter fun o => !o.isOk).length
    wholeStable := wholeStableProj proj
    acceptedDomainStable := acceptedStableProj proj }

def sensitivityResult {Obs : Type} (obs : Obs)
    (spec : Family.FamilySpec) {β : Type} [DecidableEq β]
    (cs : List Family.Completion) (read : Family.Completion → Except SourceRejection β)
    (reference : Family.Completion) : SensitivityResult Obs :=
  let sets := minimalSlotSets spec cs read reference
  { observable := obs
    reference := reference
    total := cs.length
    sensitive := (Sensitivity cs read reference).length
    differing := differingRows spec cs read reference
    minimalSlotSets := sets
    realizing := sets.filterMap fun S => (realizing spec cs read reference S).map fun c => (S, c) }

def deletionOf (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (target : β)
    (L : List Literal) (lit : Literal) : Deletion where
  literal := lit
  surviving := restrict cs (removeLit L lit)
  counter := deletionCounter cs read target L lit

def minimalSetOf (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (target : β)
    (L : List Literal) : MinimalSet where
  literals := L
  surviving := restrict cs L
  deletions := L.map (deletionOf cs read target L)

def assumptionResult {Tgt : Type} (tgt : Tgt)
    {β : Type} [DecidableEq β] (cs : List Family.Completion)
    (read : Family.Completion → Except SourceRejection β) (target : β)
    (catalog : List Literal) : AssumptionResult Tgt where
  target := tgt
  catalog := catalog
  total := cs.length
  minimal := (minimalAssumptions cs read target catalog).map (minimalSetOf cs read target)

/-- Soundness of the record's minimal sets: each surviving family is exactly
the returned set's restriction and each is subset-minimal. -/
theorem minimalSetOf_spec {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {target : β} {L : List Literal} :
    (minimalSetOf cs read target L).surviving = restrict cs L ∧
      (minimalSetOf cs read target L).literals = L := ⟨rfl, rfl⟩

theorem minimalSetOf_deletions {cs : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {target : β} {L : List Literal} :
    (minimalSetOf cs read target L).deletions.map Deletion.literal = L := by
  simp only [minimalSetOf, List.map_map, Function.comp_def]
  exact List.map_id L

/-! ### Observable-specific builders

Each builder takes a single landed `Source.CheckedFamily`: the observations come
from its already-prepared rows and the slots/choices from its `family` index, so
observations and slots always come from one source and no checker is re-run. The
`read` handed to the generic analyses is `tableRead` over the one-pass
observation table (`statusObservations` / `auditObservations`). -/

def statusStability {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) (claim : ClaimId) :
    StabilityResult Observable :=
  stabilityResult (.status claim) (checkedCompletions checked)
    (tableRead (statusObservations checked claim))

def auditStability {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) (claim : ClaimId)
    (witness : WitnessId) (profile : Profile Empty) : StabilityResult Observable :=
  stabilityResult (.audit claim witness profile) (checkedCompletions checked)
    (tableRead (auditObservations checked claim witness profile))

def statusSensitivity {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) (claim : ClaimId)
    (reference : Family.Completion) : SensitivityResult Observable :=
  sensitivityResult (.status claim) family (checkedCompletions checked)
    (tableRead (statusObservations checked claim)) reference

def auditSensitivity {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) (claim : ClaimId)
    (witness : WitnessId) (profile : Profile Empty) (reference : Family.Completion) :
    SensitivityResult Observable :=
  sensitivityResult (.audit claim witness profile) family (checkedCompletions checked)
    (tableRead (auditObservations checked claim witness profile)) reference

def statusAssumptions {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) (claim : ClaimId)
    (expected : Driver.PublicStatus) (catalog : List Literal) : AssumptionResult Target :=
  assumptionResult (.status claim expected) (checkedCompletions checked)
    (tableRead (statusObservations checked claim)) (some expected) catalog

def auditAssumptions {family : Family.FamilySpec} {config : AuditConfig}
    {completions : List Family.Completion}
    (checked : CheckedFamily family config completions) (claim : ClaimId)
    (witness : WitnessId) (profile : Profile Empty) (catalog : List Literal) :
    AssumptionResult Target :=
  assumptionResult (.audit claim witness profile) (checkedCompletions checked)
    (tableRead (auditObservations checked claim witness profile)) true catalog

/-! ### Reference-equal analysis over the landed enumerators -/

theorem minimalAssumptionB_perm {cs ds : List Family.Completion}
    {read : Family.Completion → Except SourceRejection β} {target : β}
    (p : cs.Perm ds) (L : List Literal) :
    minimalAssumptionB cs read target L = minimalAssumptionB ds read target L := by
  rw [Bool.eq_iff_iff, minimalAssumptionB_iff, minimalAssumptionB_iff]
  unfold MinimalAssumption
  rw [satisfies_perm p]
  constructor
  · rintro ⟨sat, min⟩
    exact ⟨sat, fun T hsub hne => (min T hsub hne) ∘ (satisfies_perm p).mpr⟩
  · rintro ⟨sat, min⟩
    exact ⟨sat, fun T hsub hne => (min T hsub hne) ∘ (satisfies_perm p).mp⟩

theorem minimalAssumptions_perm {cs ds : List Family.Completion}
    (p : cs.Perm ds) {read : Family.Completion → Except SourceRejection β} (target : β)
    (catalog : List Literal) :
    minimalAssumptions cs read target catalog = minimalAssumptions ds read target catalog := by
  unfold minimalAssumptions
  have : minimalAssumptionB cs read target = minimalAssumptionB ds read target := by
    funext L; exact minimalAssumptionB_perm p L
  rw [this]

/-- Running every P3 analysis over P2's exact generated family gives the same
report as over the reference family: all predicates are permutation
invariant, so the generated family is a faithful stand-in. -/
theorem reference_family_agrees (spec : Family.FamilySpec)
    (read : Family.Completion → Except SourceRejection β) (reference : Family.Completion)
    (S : List SlotId) (catalog : List Literal) (target : β) :
    wholeStableB (Family.referenceFamily spec) read =
        wholeStableB (Enumerate.searchFamily spec) read ∧
      admitsFlipB spec (Family.referenceFamily spec) read reference S =
        admitsFlipB spec (Enumerate.searchFamily spec) read reference S ∧
      minimalAssumptions (Family.referenceFamily spec) read target catalog =
        minimalAssumptions (Enumerate.searchFamily spec) read target catalog :=
  ⟨wholeStableB_perm (Enumerate.searchFamily_perm spec).symm,
   admitsFlipB_perm (Enumerate.searchFamily_perm spec).symm S,
   minimalAssumptions_perm (Enumerate.searchFamily_perm spec).symm target catalog⟩

end Lara.Process.Analysis
