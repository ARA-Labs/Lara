/-
Completion updates beyond the additive sequence: atomic batches (D14, issue
#11) and the pipeline-level metatheory of in-place discharge (D13, issue #14).
`docs/located-gap-decision.md` §6a records the design.

An atomic batch applies its raw edits in order, checking each edit's syntactic
side condition against the state the earlier edits produced, and then runs
admission and `checkUnit` exactly once on the final raw state
(`applyUpdate_atomic_ok_iff`).  It is all-or-nothing: a rejected batch returns
no state, so the caller keeps the source (`applyOrKeep`).  Its point is
completeness: every completion of an accepted source by fresh leaves, fresh
instances (or an in-place discharge) and the attacks they need is reached by
one batch whenever the completed program is accepted
(`atomic_completion_complete`, `atomic_discharge_completion_complete`), which
the individually rechecked `addInstance`/`addAttack` sequence does not
guarantee (`Examples.UpdateCompletion.sequential_completion_fails`).

An in-place discharge rewrites one raw argument row: the row keeps its name and
declaration index, raw attacks are untouched, and the leaf context and policy
are unchanged, so only the discharged argument can change its classification.
-/
import Lara.Update

namespace Lara.Update

open Lara Lara.Support
open Lara.Presentation (LeafKind Provenance Admission)

/-! ### All or nothing -/

/-- The source state after an attempted update: the update's result when it is
accepted, the unchanged source when it is rejected. -/
def applyOrKeep {canon : String → String} (reg : BackendRegistry canon)
    (σ : SourceState) (u : SourceUpdate) : SourceState :=
  match applyUpdate reg σ u with
  | .ok τ => τ
  | .error _ => σ

theorem applyOrKeep_of_error {canon : String → String}
    {reg : BackendRegistry canon} {σ : SourceState} {u : SourceUpdate}
    {reason : UpdateRejection} (h : applyUpdate reg σ u = .error reason) :
    applyOrKeep reg σ u = σ := by
  simp [applyOrKeep, h]

theorem applyOrKeep_of_ok {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState} {u : SourceUpdate}
    (h : applyUpdate reg σ u = .ok τ) :
    applyOrKeep reg σ u = τ := by
  simp [applyOrKeep, h]

/-- **A batch is rejected exactly when no accepted final state exists.** -/
theorem atomic_rejected_iff {canon : String → String}
    {reg : BackendRegistry canon} {σ : SourceState} {edits : List AtomicEdit} :
    (∃ reason, applyUpdate reg σ (.atomic edits) = .error reason) ↔
      ∀ τ, applyBatch σ edits = .ok τ → ¬ Accepted reg τ := by
  constructor
  · rintro ⟨reason, hreject⟩ τ hbatch haccepted
    have hok := applyUpdate_atomic_ok_iff.mpr ⟨hbatch, haccepted⟩
    rw [hreject] at hok
    cases hok
  · intro hnone
    cases h : applyUpdate reg σ (.atomic edits) with
    | error reason => exact ⟨reason, rfl⟩
    | ok τ =>
        obtain ⟨hbatch, haccepted⟩ := applyUpdate_atomic_ok_iff.mp h
        exact absurd haccepted (hnone τ hbatch)

/-- **Rejection of a partial batch leaves the source unchanged.** A batch whose
raw final state is not accepted — for example one that omits an attack the
completed program needs — is rejected, and the source is kept. -/
theorem atomic_partial_rejected {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState} {edits : List AtomicEdit}
    (hbatch : applyBatch σ edits = .ok τ) (hnot : ¬ Accepted reg τ) :
    (∃ reason, applyUpdate reg σ (.atomic edits) = .error reason) ∧
      applyOrKeep reg σ (.atomic edits) = σ := by
  have hrejected : ∃ reason, applyUpdate reg σ (.atomic edits) = .error reason :=
    atomic_rejected_iff.mpr fun τ' hbatch' => by
      rw [hbatch] at hbatch'
      cases hbatch'
      exact hnot
  obtain ⟨reason, hreason⟩ := hrejected
  exact ⟨⟨reason, hreason⟩, applyOrKeep_of_error hreason⟩

/-! ### Raw batch structure -/

theorem applyBatchFrom_append (σ : SourceState) (index : Nat)
    (first second : List AtomicEdit) :
    applyBatchFrom σ index (first ++ second) =
      match applyBatchFrom σ index first with
      | .error reason => .error reason
      | .ok τ => applyBatchFrom τ (index + first.length) second := by
  induction first generalizing σ index with
  | nil => simp [applyBatchFrom]
  | cons e rest ih =>
      simp only [List.cons_append, applyBatchFrom]
      cases e.applyRaw σ with
      | error reason => rfl
      | ok σ' =>
          simp only
          rw [ih σ' (index + 1)]
          simp only [List.length_cons]
          rw [show index + 1 + rest.length = index + (rest.length + 1) by omega]

/-- The leaf-adding prefix of a completion batch. -/
def leafEdits (leaves : List (LeafId × Atom × Admission.LeafMeta)) : List AtomicEdit :=
  leaves.map fun x => .addLeaf x.1 x.2.1 x.2.2

/-- The fresh-instance segment of a completion batch. -/
def instanceEdits (instances : List (String × SupportTerm)) : List AtomicEdit :=
  instances.map fun x => .addInstance x.1 x.2

/-- The attack segment of a completion batch. -/
def attackEdits (attacks : List RawAttack.RawAttack) : List AtomicEdit :=
  attacks.map .addAttack

/-- `σ` with fresh leaves and their metadata appended. -/
def withLeaves (σ : SourceState) (leaves : List (LeafId × Atom × Admission.LeafMeta)) :
    SourceState :=
  { σ with
    metas := σ.metas ++ leaves.map fun x => { x.2.2 with id := x.1 }
    leaves := σ.leaves ++ leaves.map fun x => (x.1, x.2.1) }

theorem applyBatchFrom_leafEdits :
    ∀ (leaves : List (LeafId × Atom × Admission.LeafMeta)) (σ : SourceState)
      (index : Nat),
      (∀ x ∈ leaves, AddLeafFresh σ x.1) → (leaves.map (·.1)).Nodup →
      applyBatchFrom σ index (leafEdits leaves) = .ok (withLeaves σ leaves) := by
  intro leaves
  induction leaves with
  | nil =>
      intro σ index _ _
      simp [leafEdits, applyBatchFrom, withLeaves]
  | cons x rest ih =>
      intro σ index hfresh hnodup
      rw [List.map_cons] at hnodup
      obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hnodup
      have hx := hfresh x (by simp)
      have hxB : addLeafFreshB σ x.1 = true := (addLeafFreshB_iff σ x.1).mpr hx
      simp only [leafEdits, List.map_cons, applyBatchFrom, AtomicEdit.applyRaw,
        hxB, if_true]
      have hrest : ∀ y ∈ rest,
          AddLeafFresh
            { σ with metas := σ.metas ++ [{ x.2.2 with id := x.1 }]
                     leaves := σ.leaves ++ [(x.1, x.2.1)] } y.1 := by
        intro y hy
        have hyfresh := hfresh y (by simp [hy])
        have hne : x.1 ≠ y.1 := by
          intro heq
          exact hhead (heq ▸ List.mem_map.mpr ⟨y, hy, rfl⟩)
        refine ⟨?_, ?_, ?_⟩
        · intro e he
          rcases List.mem_append.mp he with he | he
          · exact hyfresh.1 e he
          · simp only [List.mem_singleton] at he
            subst he
            exact hne
        · intro m hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hyfresh.2.1 m hm
          · simp only [List.mem_singleton] at hm
            subst hm
            exact hne
        · exact hyfresh.2.2
      have := ih _ (index + 1) hrest htail
      simp only [leafEdits] at this
      rw [this]
      simp [withLeaves, List.append_assoc]

theorem applyBatchFrom_instanceEdits :
    ∀ (instances : List (String × SupportTerm)) (σ : SourceState) (index : Nat),
      (∀ x ∈ instances, InstanceFresh σ x.1 x.2) →
      (instances.map (·.1)).Nodup → (instances.map (·.2)).Nodup →
      applyBatchFrom σ index (instanceEdits instances) =
        .ok { σ with argsRaw := σ.argsRaw ++ instances } := by
  intro instances
  induction instances with
  | nil =>
      intro σ index _ _ _
      simp [instanceEdits, applyBatchFrom]
  | cons x rest ih =>
      intro σ index hfresh hnames hterms
      rw [List.map_cons] at hnames hterms
      obtain ⟨hnameHead, hnameTail⟩ := List.nodup_cons.mp hnames
      obtain ⟨htermHead, htermTail⟩ := List.nodup_cons.mp hterms
      have hx := hfresh x (by simp)
      have hxB : instanceFreshB σ x.1 x.2 = true :=
        (instanceFreshB_iff σ x.1 x.2).mpr hx
      simp only [instanceEdits, List.map_cons, applyBatchFrom, AtomicEdit.applyRaw,
        hxB, if_true]
      have hrest : ∀ y ∈ rest,
          InstanceFresh { σ with argsRaw := σ.argsRaw ++ [(x.1, x.2)] } y.1 y.2 := by
        intro y hy
        have hyfresh := hfresh y (by simp [hy])
        refine ⟨?_, ?_⟩
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hyfresh.1 a ha
          · simp only [List.mem_singleton] at ha
            subst ha
            intro heq
            exact hnameHead (heq ▸ List.mem_map.mpr ⟨y, hy, rfl⟩)
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hyfresh.2 a ha
          · simp only [List.mem_singleton] at ha
            subst ha
            intro heq
            exact htermHead (heq ▸ List.mem_map.mpr ⟨y, hy, rfl⟩)
      have := ih _ (index + 1) hrest hnameTail htermTail
      simp only [instanceEdits] at this
      rw [this]
      simp [List.append_assoc]

theorem applyBatchFrom_attackEdits :
    ∀ (attacks : List RawAttack.RawAttack) (σ : SourceState) (index : Nat),
      (∀ k ∈ attacks, EndpointDeclared σ k) →
      applyBatchFrom σ index (attackEdits attacks) =
        .ok { σ with rawAtts := σ.rawAtts ++ attacks } := by
  intro attacks
  induction attacks with
  | nil =>
      intro σ index _
      simp [attackEdits, applyBatchFrom]
  | cons k rest ih =>
      intro σ index hdeclared
      have hk : endpointDeclaredB σ k = true :=
        (endpointDeclaredB_iff σ k).mpr (hdeclared k (by simp))
      simp only [attackEdits, List.map_cons, applyBatchFrom, AtomicEdit.applyRaw,
        hk, if_true]
      have hrest : ∀ k' ∈ rest,
          EndpointDeclared { σ with rawAtts := σ.rawAtts ++ [k] } k' :=
        fun k' hk' => hdeclared k' (by simp [hk'])
      have := ih _ (index + 1) hrest
      simp only [attackEdits] at this
      rw [this]
      simp [List.append_assoc]

/-! ### Completeness of atomic completion -/

/-- A completion batch: fresh leaves, then fresh instances, then attacks. -/
def completionEdits (leaves : List (LeafId × Atom × Admission.LeafMeta))
    (instances : List (String × SupportTerm))
    (attacks : List RawAttack.RawAttack) : List AtomicEdit :=
  leafEdits leaves ++ instanceEdits instances ++ attackEdits attacks

/-- The completed program a completion batch denotes. -/
def completionState (σ : SourceState)
    (leaves : List (LeafId × Atom × Admission.LeafMeta))
    (instances : List (String × SupportTerm))
    (attacks : List RawAttack.RawAttack) : SourceState :=
  { withLeaves σ leaves with
    argsRaw := σ.argsRaw ++ instances
    rawAtts := σ.rawAtts ++ attacks }

/-- **Completeness of atomic completion (additive form).** If the program
obtained from `σ` by adding fresh leaves, fresh instances and the attacks they
need is accepted, then the one atomic batch that performs exactly those edits
is accepted and yields exactly that program.  Nothing is assumed about the
intermediate states; in particular an attack may name an instance added earlier
in the same batch. -/
theorem atomic_completion_complete {canon : String → String}
    {reg : BackendRegistry canon} (σ : SourceState)
    (leaves : List (LeafId × Atom × Admission.LeafMeta))
    (instances : List (String × SupportTerm))
    (attacks : List RawAttack.RawAttack)
    (hleafFresh : ∀ x ∈ leaves, AddLeafFresh σ x.1)
    (hleafNodup : (leaves.map (·.1)).Nodup)
    (hinstanceFresh : ∀ x ∈ instances, InstanceFresh σ x.1 x.2)
    (hnames : (instances.map (·.1)).Nodup)
    (hterms : (instances.map (·.2)).Nodup)
    (hendpoints : ∀ k ∈ attacks,
      EndpointDeclared { σ with argsRaw := σ.argsRaw ++ instances } k)
    (haccepted : Accepted reg (completionState σ leaves instances attacks)) :
    applyUpdate reg σ (.atomic (completionEdits leaves instances attacks)) =
      .ok (completionState σ leaves instances attacks) := by
  apply applyUpdate_atomic_ok_iff.mpr
  refine ⟨?_, haccepted⟩
  unfold applyBatch completionEdits
  rw [applyBatchFrom_append, applyBatchFrom_append,
    applyBatchFrom_leafEdits leaves σ 0 hleafFresh hleafNodup]
  simp only
  rw [applyBatchFrom_instanceEdits instances (withLeaves σ leaves) _
    (fun x hx => hinstanceFresh x hx) hnames hterms]
  simp only
  rw [applyBatchFrom_attackEdits attacks _ _ (fun k hk => by
    have h := hendpoints k hk
    simpa [EndpointDeclared, withLeaves] using h)]
  rfl

theorem dischargeRows_map_fst (argsRaw : List (String × SupportTerm))
    (name : String) (π : Attack.Pos) (q : QuestionId) (v : SupportTerm) :
    (dischargeRows argsRaw name π q v).map (·.1) = argsRaw.map (·.1) := by
  unfold dischargeRows
  rw [List.map_map]
  apply List.map_congr_left
  intro row _
  by_cases h : row.1 = name <;> simp [h]

/-- A discharge completion batch: fresh leaves, one in-place discharge, then
attacks. -/
def dischargeCompletionEdits (leaves : List (LeafId × Atom × Admission.LeafMeta))
    (name : String) (π : Attack.Pos) (q : QuestionId) (v : SupportTerm)
    (attacks : List RawAttack.RawAttack) : List AtomicEdit :=
  leafEdits leaves ++ [.dischargeOpen name π q v] ++ attackEdits attacks

/-- The completed program a discharge completion batch denotes. -/
def dischargeCompletionState (σ : SourceState)
    (leaves : List (LeafId × Atom × Admission.LeafMeta))
    (name : String) (π : Attack.Pos) (q : QuestionId) (v : SupportTerm)
    (attacks : List RawAttack.RawAttack) : SourceState :=
  { withLeaves σ leaves with
    argsRaw := dischargeRows σ.argsRaw name π q v
    rawAtts := σ.rawAtts ++ attacks }

/-- **Completeness of atomic completion (in-place form).** If the program
obtained from `σ` by adding fresh leaves, discharging an open question in place
and adding the attacks it needs is accepted, the corresponding batch yields
exactly that program. -/
theorem atomic_discharge_completion_complete {canon : String → String}
    {reg : BackendRegistry canon} (σ : SourceState)
    (leaves : List (LeafId × Atom × Admission.LeafMeta))
    (name : String) (π : Attack.Pos) (q : QuestionId) (v : SupportTerm)
    (attacks : List RawAttack.RawAttack)
    (hleafFresh : ∀ x ∈ leaves, AddLeafFresh σ x.1)
    (hleafNodup : (leaves.map (·.1)).Nodup)
    (hsite : DischargeOpen σ name π q)
    (hendpoints : ∀ k ∈ attacks, EndpointDeclared σ k)
    (haccepted :
      Accepted reg (dischargeCompletionState σ leaves name π q v attacks)) :
    applyUpdate reg σ
        (.atomic (dischargeCompletionEdits leaves name π q v attacks)) =
      .ok (dischargeCompletionState σ leaves name π q v attacks) := by
  apply applyUpdate_atomic_ok_iff.mpr
  refine ⟨?_, haccepted⟩
  unfold applyBatch dischargeCompletionEdits
  rw [applyBatchFrom_append, applyBatchFrom_append,
    applyBatchFrom_leafEdits leaves σ 0 hleafFresh hleafNodup]
  have hsiteB : dischargeOpenB (withLeaves σ leaves) name π q = true :=
    (dischargeOpenB_iff _ _ _ _).mpr hsite
  simp only [applyBatchFrom, AtomicEdit.applyRaw, hsiteB, if_true]
  rw [applyBatchFrom_attackEdits attacks _ _ (fun k hk => by
    have h := hendpoints k hk
    unfold EndpointDeclared at h ⊢
    simp only [withLeaves] at h ⊢
    rw [dischargeRows_map_fst]
    exact h)]
  rfl

/-! ### Raw identities across a batch -/

/-- Every edit except in-place discharge only appends. -/
def AtomicEdit.Additive : AtomicEdit → Prop
  | .dischargeOpen .. => False
  | _ => True

/-- Raw carriers across one raw edit: raw attacks, leaf rows and metadata rows
only grow at the end, argument names keep their positions, and the remaining
carriers are untouched.  An additive edit also keeps every argument row. -/
theorem AtomicEdit.applyRaw_prefix {σ τ : SourceState} {e : AtomicEdit}
    (h : e.applyRaw σ = .ok τ) :
    σ.rawAtts <+: τ.rawAtts ∧ σ.leaves <+: τ.leaves ∧ σ.metas <+: τ.metas ∧
      σ.argsRaw.map (·.1) <+: τ.argsRaw.map (·.1) ∧
      (e.Additive → σ.argsRaw <+: τ.argsRaw) ∧
      τ.sigma = σ.sigma ∧ τ.policy = σ.policy ∧ τ.table = σ.table ∧
      τ.groups = σ.groups ∧ τ.ground = σ.ground := by
  cases e with
  | addLeaf id a m =>
      simp only [AtomicEdit.applyRaw] at h
      split at h
      · cases h
        exact ⟨List.prefix_refl _, List.prefix_append _ _, List.prefix_append _ _,
          List.prefix_refl _, fun _ => List.prefix_refl _,
          rfl, rfl, rfl, rfl, rfl⟩
      · cases h
  | addInstance name w =>
      simp only [AtomicEdit.applyRaw] at h
      split at h
      · cases h
        exact ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
          by simp only [List.map_append]; exact List.prefix_append _ _,
          fun _ => List.prefix_append _ _, rfl, rfl, rfl, rfl, rfl⟩
      · cases h
  | addAttack k =>
      simp only [AtomicEdit.applyRaw] at h
      split at h
      · cases h
        exact ⟨List.prefix_append _ _, List.prefix_refl _, List.prefix_refl _,
          List.prefix_refl _, fun _ => List.prefix_refl _, rfl, rfl, rfl, rfl, rfl⟩
      · cases h
  | dischargeOpen name π q v =>
      simp only [AtomicEdit.applyRaw] at h
      split at h
      · cases h
        refine ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
          ?_, fun hadd => hadd.elim, rfl, rfl, rfl, rfl, rfl⟩
        rw [dischargeRows_map_fst]
        exact List.prefix_refl _
      · cases h

/-- **Raw identities persist across a batch.** Every raw attack keeps its
declaration index and content, every leaf and metadata row stays, and every
argument name keeps its declaration index; with no in-place discharge every
argument row (name and term) also stays at its index. -/
theorem applyBatchFrom_prefix :
    ∀ (edits : List AtomicEdit) {σ τ : SourceState} {index : Nat},
      applyBatchFrom σ index edits = .ok τ →
      σ.rawAtts <+: τ.rawAtts ∧ σ.leaves <+: τ.leaves ∧ σ.metas <+: τ.metas ∧
        σ.argsRaw.map (·.1) <+: τ.argsRaw.map (·.1) ∧
        ((∀ e ∈ edits, e.Additive) → σ.argsRaw <+: τ.argsRaw) ∧
        τ.sigma = σ.sigma ∧ τ.policy = σ.policy ∧ τ.table = σ.table ∧
        τ.groups = σ.groups ∧ τ.ground = σ.ground := by
  intro edits
  induction edits with
  | nil =>
      intro σ τ index h
      simp only [applyBatchFrom, Except.ok.injEq] at h
      subst h
      exact ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
        List.prefix_refl _, fun _ => List.prefix_refl _, rfl, rfl, rfl, rfl, rfl⟩
  | cons e rest ih =>
      intro σ τ index h
      simp only [applyBatchFrom] at h
      cases hstep : e.applyRaw σ with
      | error reason => rw [hstep] at h; cases h
      | ok σ' =>
          rw [hstep] at h
          obtain ⟨a1, l1, m1, n1, r1, s1, p1, t1, g1, gr1⟩ :=
            AtomicEdit.applyRaw_prefix hstep
          obtain ⟨a2, l2, m2, n2, r2, s2, p2, t2, g2, gr2⟩ := ih h
          exact ⟨a1.trans a2, l1.trans l2, m1.trans m2, n1.trans n2,
            fun hadd => (r1 (hadd e (by simp))).trans
              (r2 fun e' he' => hadd e' (by simp [he'])),
            s2.trans s1, p2.trans p1, t2.trans t1, g2.trans g1, gr2.trans gr1⟩

/-- A successful batch keeps every raw attack and, when additive, every raw
argument row of the source, at its declaration index. -/
theorem applyUpdate_atomic_raw_prefix {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState} {edits : List AtomicEdit}
    (h : applyUpdate reg σ (.atomic edits) = .ok τ) :
    σ.rawAtts <+: τ.rawAtts ∧ σ.argsRaw.map (·.1) <+: τ.argsRaw.map (·.1) ∧
      ((∀ e ∈ edits, e.Additive) → σ.argsRaw <+: τ.argsRaw) := by
  obtain ⟨a, _, _, n, r, _⟩ := applyBatchFrom_prefix edits (applyUpdate_atomic_target h)
  exact ⟨a, n, r⟩

/-! ### Old holes and complete arguments persist across an additive batch -/

/-- An additive edit whose new metadata, if any, is admitted by `table` (the
batch analogue of `AdditiveUpdate.addLeaf`'s admission premise). -/
def AtomicEdit.AdmittedAdditive (table : List Admission.AdmissionRow) :
    AtomicEdit → Prop
  | .addLeaf _ _ m => Admission.decisionFor table m.kind m.provenance = .admit
  | .addInstance _ _ => True
  | .addAttack _ => True
  | .dischargeOpen .. => False

/-- How an additive batch relates its final raw state to its source. -/
private structure AdditiveExtension (σ τ : SourceState) : Prop where
  table_eq : τ.table = σ.table
  groups_eq : τ.groups = σ.groups
  policy_eq : τ.policy = σ.policy
  leaves_ext : ∃ L, τ.leaves = σ.leaves ++ L ∧ ∀ x ∈ L, AddLeafFresh σ x.1
  metas_ext : ∃ M, τ.metas = σ.metas ++ M ∧
    ∀ m ∈ M, Admission.decisionFor σ.table m.kind m.provenance = .admit
  args_ext : ∃ I, τ.argsRaw = σ.argsRaw ++ I

private theorem AdditiveExtension.refl (σ : SourceState) : AdditiveExtension σ σ :=
  { table_eq := rfl, groups_eq := rfl, policy_eq := rfl
  , leaves_ext := ⟨[], by simp, by simp⟩
  , metas_ext := ⟨[], by simp, by simp⟩
  , args_ext := ⟨[], by simp⟩ }

private theorem AdditiveExtension.step {σ₀ σ σ' : SourceState} {e : AtomicEdit}
    (hext : AdditiveExtension σ₀ σ) (hstep : e.applyRaw σ = .ok σ')
    (hadd : e.AdmittedAdditive σ₀.table) : AdditiveExtension σ₀ σ' := by
  obtain ⟨htable, hgroups, hpolicy, ⟨L, hL, hLfresh⟩, ⟨M, hM, hMadmit⟩, ⟨I, hI⟩⟩ :=
    hext
  cases e with
  | addLeaf id a m =>
      simp only [AtomicEdit.applyRaw] at hstep
      split at hstep
      · rename_i hfreshB
        cases hstep
        have hfresh := (addLeafFreshB_iff σ id).mp hfreshB
        have hfresh₀ : AddLeafFresh σ₀ id := by
          refine ⟨fun e he => hfresh.1 e (by rw [hL]; exact List.mem_append_left _ he),
            fun m' hm' => hfresh.2.1 m' (by rw [hM]; exact List.mem_append_left _ hm'),
            fun g hg => hfresh.2.2 g (by rw [hgroups]; exact hg)⟩
        exact
          { table_eq := htable, groups_eq := hgroups, policy_eq := hpolicy
          , leaves_ext := ⟨L ++ [(id, a)], by simp [hL],
              fun x hx => by
                rcases List.mem_append.mp hx with hx | hx
                · exact hLfresh x hx
                · simp only [List.mem_singleton] at hx; subst hx; exact hfresh₀⟩
          , metas_ext := ⟨M ++ [{ m with id := id }], by simp [hM],
              fun m' hm' => by
                rcases List.mem_append.mp hm' with hm' | hm'
                · exact hMadmit m' hm'
                · simp only [List.mem_singleton] at hm'; subst hm'; exact hadd⟩
          , args_ext := ⟨I, hI⟩ }
      · cases hstep
  | addInstance name w =>
      simp only [AtomicEdit.applyRaw] at hstep
      split at hstep
      · cases hstep
        exact
          { table_eq := htable, groups_eq := hgroups, policy_eq := hpolicy
          , leaves_ext := ⟨L, hL, hLfresh⟩, metas_ext := ⟨M, hM, hMadmit⟩
          , args_ext := ⟨I ++ [(name, w)], by simp [hI]⟩ }
      · cases hstep
  | addAttack k =>
      simp only [AtomicEdit.applyRaw] at hstep
      split at hstep
      · cases hstep
        exact
          { table_eq := htable, groups_eq := hgroups, policy_eq := hpolicy
          , leaves_ext := ⟨L, hL, hLfresh⟩, metas_ext := ⟨M, hM, hMadmit⟩
          , args_ext := ⟨I, hI⟩ }
      · cases hstep
  | dischargeOpen => exact hadd.elim

private theorem applyBatchFrom_additiveExtension (σ₀ : SourceState) :
    ∀ (edits : List AtomicEdit) {σ τ : SourceState} {index : Nat},
      AdditiveExtension σ₀ σ → applyBatchFrom σ index edits = .ok τ →
      (∀ e ∈ edits, e.AdmittedAdditive σ₀.table) → AdditiveExtension σ₀ τ := by
  intro edits
  induction edits with
  | nil =>
      intro σ τ index hext h _
      simp only [applyBatchFrom, Except.ok.injEq] at h
      subst h
      exact hext
  | cons e rest ih =>
      intro σ τ index hext h hadd
      simp only [applyBatchFrom] at h
      cases hstep : e.applyRaw σ with
      | error reason => rw [hstep] at h; cases h
      | ok σ' =>
          rw [hstep] at h
          exact ih (AdditiveExtension.step hext hstep (hadd e (by simp))) h
            (fun e' he' => hadd e' (by simp [he']))

private theorem leafProp_append_not_mem (leaves extra : List (LeafId × Atom))
    {l : LeafId} (hl : l ∉ extra.map (·.1)) :
    Groups.leafProp (leaves ++ extra) l = Groups.leafProp leaves l := by
  unfold Groups.leafProp
  rw [List.find?_append]
  cases hfind : leaves.find? (fun e => decide (e.1 = l)) with
  | some row => rfl
  | none =>
      simp only [Option.none_or]
      rw [List.find?_eq_none.mpr (by
        intro row hrow hdec
        exact hl (List.mem_map.mpr ⟨row, hrow, of_decide_eq_true hdec⟩))]

private theorem quarantined_append_not_member (canon : String → String)
    (leaves extra : List (LeafId × Atom)) (groups : List Groups.DupGroup)
    (hfresh : ∀ g ∈ groups, ∀ member ∈ g.members, member ∉ extra.map (·.1)) :
    Groups.quarantined canon (leaves ++ extra) groups =
      Groups.quarantined canon leaves groups := by
  unfold Groups.quarantined
  congr 1
  apply List.filter_congr
  intro g hg
  have hprops :
      Groups.memberProps (leaves ++ extra) g = Groups.memberProps leaves g := by
    unfold Groups.memberProps
    have go : ∀ members : List LeafId,
        (∀ member ∈ members, member ∉ extra.map (·.1)) →
        List.mapM (Groups.leafProp (leaves ++ extra)) members =
          List.mapM (Groups.leafProp leaves) members := by
      intro members
      induction members with
      | nil => intro _; rfl
      | cons member rest ih =>
          intro hmembers
          simp only [List.mapM_cons]
          rw [leafProp_append_not_mem leaves extra (hmembers member (by simp)),
            ih (fun x hx => hmembers x (by simp [hx]))]
    exact go g.members (hfresh g hg)
  unfold Groups.consistentB
  rw [hprops]

/-- **Old holes and complete arguments persist across an additive batch.** For
a successful batch of additive edits whose new leaves are admitted, the source's
complete arguments are a prefix of the target's, and so are its reported holes:
no old hole changes its identity or position or leaves the report, and no old
AF argument is lost.  Raw argument rows and raw attacks are prefixes too
(`applyUpdate_atomic_raw_prefix`). -/
theorem atomic_additive_checked_prefix {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState} {edits : List AtomicEdit}
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.atomic edits) = .ok τ)
    (hadd : ∀ e ∈ edits, e.AdmittedAdditive σ.table) :
    sourceRun.checked.program.args <+: targetRun.checked.program.args ∧
      sourceRun.checked.program.holes <+: targetRun.checked.program.holes := by
  obtain ⟨htable, hgroups, hpolicy, ⟨L, hL, hLfresh⟩, ⟨M, hM, hMadmit⟩, ⟨I, hI⟩⟩ :=
    applyBatchFrom_additiveExtension σ edits (AdditiveExtension.refl σ)
      (applyUpdate_atomic_target happly) hadd
  have hpolicySeed :
      Admission.policyQuarantineSeed τ.table τ.metas =
        Admission.policyQuarantineSeed σ.table σ.metas := by
    rw [htable, hM]
    unfold Admission.policyQuarantineSeed
    rw [List.filterMap_append]
    have hnil : M.filterMap (fun m =>
        if Admission.decisionFor σ.table m.kind m.provenance = .quarantine then
          some m.id else none) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro m hm
      simp [hMadmit m hm]
    rw [hnil, List.append_nil]
  have hgroupSeed :
      Groups.quarantined canon τ.leaves τ.groups =
        Groups.quarantined canon σ.leaves σ.groups := by
    rw [hL, hgroups]
    apply quarantined_append_not_member
    intro g hg member hmember hmem
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmem
    exact (hLfresh x hx).2.2 g hg _ hmember rfl
  have hsPrune := sourceRun.prune_eq
  have htPrune := targetRun.prune_eq
  let seed := Admission.policyQuarantineSeed σ.table σ.metas ++
    Groups.quarantined canon σ.leaves σ.groups
  have hkept :
      targetRun.admission.prune.keptArgs =
        sourceRun.admission.prune.keptArgs ++
          I.filter (fun row => !Groups.usesLeaf seed row.2) := by
    rw [htPrune, hsPrune]
    change
      τ.argsRaw.filter (fun row => !Groups.usesLeaf
        (Admission.policyQuarantineSeed τ.table τ.metas ++
          Groups.quarantined canon τ.leaves τ.groups) row.2) =
      σ.argsRaw.filter (fun row => !Groups.usesLeaf seed row.2) ++
        I.filter (fun row => !Groups.usesLeaf seed row.2)
    rw [hpolicySeed, hgroupSeed, hI, List.filter_append]
  have hchecked :
      targetRun.admission.prune.checkedLeaves =
        sourceRun.admission.prune.checkedLeaves ++
          Groups.quarantineLeaves seed L := by
    rw [htPrune, hsPrune]
    change
      Admission.checkedLeafTable canon τ.table τ.metas τ.leaves τ.groups =
        Admission.checkedLeafTable canon σ.table σ.metas σ.leaves σ.groups ++
          Groups.quarantineLeaves seed L
    unfold Admission.checkedLeafTable
    rw [hpolicySeed, hgroupSeed, hL]
    simp [Groups.quarantineLeaves, List.filter_append, seed]
  have hsSound := Check.Unit.checkUnit_sound sourceRun.check_ok
  have htSound := Check.Unit.checkUnit_sound targetRun.check_ok
  have hgammaOn : ∀ w ∈ sourceRun.admission.prune.keptArgs.map (·.2),
      ∀ l ∈ Support.leaves w,
        Admission.buildGamma sourceRun.admission.prune.checkedLeaves l =
          Admission.buildGamma targetRun.admission.prune.checkedLeaves l := by
    intro w hw l hl
    obtain ⟨C, O, hsupport⟩ := hsSound.raw_support w hw
    obtain ⟨p, hp⟩ := Support.leaves_declared hsupport l hl
    rw [hp, hchecked, Admission.buildGamma_append_of_some _ _ hp]
  have hsArgs := hsSound.args_eq
  have hsHoles := hsSound.holes_eq
  have htArgs := htSound.args_eq
  have htHoles := htSound.holes_eq
  dsimp only at hsArgs hsHoles htArgs htHoles
  rw [hpolicy] at htArgs htHoles
  refine ⟨?_, ?_⟩
  · rw [htArgs, hsArgs, hkept, List.map_append, Check.completeArgs_append]
    have hold :
        Check.completeArgs σ.policy.ruleLookup
            (Admission.buildGamma targetRun.admission.prune.checkedLeaves) reg
            (sourceRun.admission.prune.keptArgs.map (·.2)) =
          Check.completeArgs σ.policy.ruleLookup
            (Admission.buildGamma sourceRun.admission.prune.checkedLeaves) reg
            (sourceRun.admission.prune.keptArgs.map (·.2)) :=
      Check.completeArgs_congr fun w hw =>
        (Check.argComplete_congr_gamma_on (hgammaOn w hw)).symm
    rw [hold]
    exact List.prefix_append _ _
  · rw [htHoles, hsHoles, hkept, List.map_append, Check.holeArgs_append]
    have hold :
        Check.holeArgs σ.policy.ruleLookup
            (Admission.buildGamma targetRun.admission.prune.checkedLeaves) reg
            (sourceRun.admission.prune.keptArgs.map (·.2)) =
          Check.holeArgs σ.policy.ruleLookup
            (Admission.buildGamma sourceRun.admission.prune.checkedLeaves) reg
            (sourceRun.admission.prune.keptArgs.map (·.2)) :=
      List.filter_congr fun w hw =>
        (Check.argHole_congr_gamma_on (hgammaOn w hw)).symm
    rw [hold]
    exact List.prefix_append _ _

/-! ### In-place discharge through the pipeline -/

/-- The term an in-place discharge gives the row named `n`: the discharged
term for the named row, the old term for every other row. -/
def dischargeTerm (name : String) (π : Attack.Pos) (q : QuestionId)
    (v : SupportTerm) (n : String) (t : SupportTerm) : SupportTerm :=
  if n = name then (Discharge.dischargeAt q v π t).getD t else t

/-- **Endpoint lookup after discharge.** Every raw name resolves exactly when it
did before, to the same term except for the discharged argument. -/
theorem lookupArg_dischargeRows (argsRaw : List (String × SupportTerm))
    (name : String) (π : Attack.Pos) (q : QuestionId) (v : SupportTerm)
    (n : String) :
    RawAttack.lookupArg (dischargeRows argsRaw name π q v) n =
      (RawAttack.lookupArg argsRaw n).map (dischargeTerm name π q v n) := by
  induction argsRaw with
  | nil => rfl
  | cons row rest ih =>
      obtain ⟨r1, r2⟩ := row
      unfold RawAttack.lookupArg at ih ⊢
      unfold dischargeRows at ih ⊢
      rw [List.map_cons]
      by_cases hrow : r1 = n
      · subst hrow
        by_cases hname : r1 = name
        · simp [hname, dischargeTerm]
        · simp [hname, dischargeTerm]
      · have hb : (r1 == n) = false := beq_false_of_ne hrow
        by_cases hname : r1 = name
        · subst hname
          simp only [List.find?_cons, if_true, hb]
          exact ih
        · simp only [List.find?_cons, hname, if_false, hb]
          exact ih

/-- Replace the endpoint terms of a resolved attack, keeping its kind and
position. -/
def retarget (s t : SupportTerm) : Attack.Attack → Attack.Attack
  | .rebut _ _ => .rebut s t
  | .undercut _ _ pos => .undercut s t pos
  | .undermine _ _ pos => .undermine s t pos

/-- **Raw endpoint alignment survives discharge.** Every raw attack resolves
after the discharge exactly as before, at the same index, kind and position,
with the discharged argument's new term at the endpoints that name it. -/
theorem resolveAttacks_dischargeRows (argsRaw : List (String × SupportTerm))
    (name : String) (π : Attack.Pos) (q : QuestionId) (v : SupportTerm) :
    ∀ (raws : List RawAttack.RawAttack) (atts : List Attack.Attack),
      RawAttack.resolveAttacks argsRaw raws = .ok atts →
      RawAttack.resolveAttacks (dischargeRows argsRaw name π q v) raws =
        .ok (List.zipWith (fun ra k =>
          retarget (dischargeTerm name π q v ra.endpoints.1 k.source)
            (dischargeTerm name π q v ra.endpoints.2 k.target) k) raws atts) := by
  intro raws
  induction raws with
  | nil =>
      intro atts h
      simp only [RawAttack.resolveAttacks, Except.ok.injEq] at h
      subst h
      rfl
  | cons ra rest ih =>
      intro atts h
      have hlookup := lookupArg_dischargeRows argsRaw name π q v
      rcases ra with ⟨s, t⟩ | ⟨s, t, pos⟩ | ⟨s, t, pos⟩
      all_goals
        first
        | rw [RawAttack.resolveAttacks_rebut] at h
          rw [RawAttack.resolveAttacks_rebut]
        | rw [RawAttack.resolveAttacks_undercut] at h
          rw [RawAttack.resolveAttacks_undercut]
        | rw [RawAttack.resolveAttacks_undermine] at h
          rw [RawAttack.resolveAttacks_undermine]
        rw [hlookup s, hlookup t]
        cases hs : RawAttack.lookupArg argsRaw s with
        | none => rw [hs] at h; cases h
        | some sw =>
            cases ht : RawAttack.lookupArg argsRaw t with
            | none => rw [hs, ht] at h; cases h
            | some tw =>
                rw [hs, ht] at h
                cases hr : RawAttack.resolveAttacks argsRaw rest with
                | error e => rw [hr] at h; cases h
                | ok restAtts =>
                    rw [hr] at h
                    simp only [Except.bind, Except.ok.injEq] at h
                    subst h
                    simp only [Option.map_some]
                    rw [ih restAtts hr]
                    rfl

/-- **Raw identities across a discharge.** Raw attacks, leaves, metadata, the
admission table, groups and policy are untouched; every argument keeps its name
at its declaration index, and every row other than the discharged one keeps its
term. -/
theorem dischargeOpen_raw_identities {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState}
    {name : String} {π : Attack.Pos} {q : QuestionId} {v : SupportTerm}
    (happly : applyUpdate reg σ (.dischargeOpen name π q v) = .ok τ) :
    τ.rawAtts = σ.rawAtts ∧ τ.leaves = σ.leaves ∧ τ.metas = σ.metas ∧
      τ.table = σ.table ∧ τ.groups = σ.groups ∧ τ.policy = σ.policy ∧
      τ.argsRaw.map (·.1) = σ.argsRaw.map (·.1) ∧
      (∀ (i : Nat) (row : String × SupportTerm), σ.argsRaw[i]? = some row → row.1 ≠ name →
        τ.argsRaw[i]? = some row) := by
  have hτ := applyUpdate_dischargeOpen_target happly
  subst hτ
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, dischargeRows_map_fst _ _ _ _ _, ?_⟩
  intro i row hrow hne
  simp only [dischargeRows, List.getElem?_map, hrow, Option.map_some, hne, if_false]

/-- **Endpoint alignment across a discharge, at the run level.** The target's
resolved attacks are the source's, index for index, with the discharged
argument's new term substituted at the endpoints that name it. -/
theorem dischargeOpen_resolved {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState}
    {name : String} {π : Attack.Pos} {q : QuestionId} {v : SupportTerm}
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.dischargeOpen name π q v) = .ok τ) :
    targetRun.declared.resolved =
      List.zipWith (fun ra k =>
        retarget (dischargeTerm name π q v ra.endpoints.1 k.source)
          (dischargeTerm name π q v ra.endpoints.2 k.target) k)
        σ.rawAtts sourceRun.declared.resolved := by
  have hτ := applyUpdate_dischargeOpen_target happly
  have htarget := targetRun.declared.resolve_eq
  have hsource := resolveAttacks_dischargeRows σ.argsRaw name π q v σ.rawAtts
    sourceRun.declared.resolved sourceRun.declared.resolve_eq
  subst hτ
  exact Except.ok.inj (htarget.symm.trans hsource)

/-- The facts every pipeline-level discharge theorem uses: same checker
context, the target's kept rows are the discharged source rows under the
source's keep predicate, and the source's kept terms are duplicate-free. -/
private theorem dischargeOpen_runs {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState}
    {name : String} {π : Attack.Pos} {q : QuestionId} {v : SupportTerm}
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.dischargeOpen name π q v) = .ok τ) :
    τ = { σ with argsRaw := dischargeRows σ.argsRaw name π q v } ∧
      targetRun.admission.prune.checkedLeaves =
        sourceRun.admission.prune.checkedLeaves ∧
      targetRun.admission.prune.keptArgs =
        (dischargeRows σ.argsRaw name π q v).filter
          (fun row => !Groups.usesLeaf sourceRun.admission.prune.removedSeed row.2) ∧
      sourceRun.admission.prune.keptArgs =
        σ.argsRaw.filter
          (fun row => !Groups.usesLeaf sourceRun.admission.prune.removedSeed row.2) := by
  have hτ := applyUpdate_dischargeOpen_target happly
  have hsPrune := sourceRun.prune_eq
  have htPrune := targetRun.prune_eq
  subst hτ
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [htPrune, hsPrune]; rfl
  · rw [htPrune, hsPrune]; rfl
  · rw [hsPrune]; rfl

private theorem eq_of_mem_of_name {argsRaw : List (String × SupportTerm)}
    (hnodup : (argsRaw.map (·.1)).Nodup) {name : String} {w : SupportTerm}
    (hw : RawAttack.lookupArg argsRaw name = some w)
    {row : String × SupportTerm} (hrow : row ∈ argsRaw) (hname : row.1 = name) :
    row = (name, w) := by
  have h := RawAttack.lookupArg_of_mem_nodup hnodup hrow
  rw [hname, hw] at h
  cases row
  simp only at hname h
  subst hname
  cases h
  rfl

/-- The kept terms after a discharge: the discharged argument's new term if
its row is kept, and the unchanged term of every other kept row. -/
private theorem dischargeOpen_kept_terms {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState}
    {name : String} {π : Attack.Pos} {q : QuestionId} {v : SupportTerm}
    {w w' : SupportTerm}
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.dischargeOpen name π q v) = .ok τ)
    (hw : RawAttack.lookupArg σ.argsRaw name = some w)
    (hw' : Discharge.dischargeAt q v π w = some w') (u : SupportTerm) :
    (u ∈ targetRun.admission.prune.keptArgs.map (·.2) ↔
      (u = w' ∧ (name, w') ∈ targetRun.admission.prune.keptArgs) ∨
        ∃ row ∈ sourceRun.admission.prune.keptArgs, row.1 ≠ name ∧ row.2 = u) ∧
    (u ∈ sourceRun.admission.prune.keptArgs.map (·.2) ↔
      (u = w ∧ (name, w) ∈ sourceRun.admission.prune.keptArgs) ∨
        ∃ row ∈ sourceRun.admission.prune.keptArgs, row.1 ≠ name ∧ row.2 = u) := by
  obtain ⟨_, _, htKept, hsKept⟩ := dischargeOpen_runs sourceRun targetRun happly
  have hnodup := sourceRun.declared.ids_nodup
  constructor
  · constructor
    · intro hu
      obtain ⟨row', hrow', rfl⟩ := List.mem_map.mp hu
      have hrow'' := hrow'
      rw [htKept, List.mem_filter] at hrow''
      obtain ⟨hmem, hkeep⟩ := hrow''
      obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
      by_cases hname : row.1 = name
      · have hrowEq := eq_of_mem_of_name hnodup hw hrow hname
        subst hrowEq
        left
        have hrowEq' :
            (if (name, w).1 = name then
                ((name, w).1, (Discharge.dischargeAt q v π (name, w).2).getD (name, w).2)
              else (name, w)) = (name, w') := by
          simp [hw']
        rw [hrowEq'] at hrow' ⊢
        exact ⟨rfl, hrow'⟩
      · right
        simp only [hname, if_false] at hkeep hrow' ⊢
        refine ⟨row, ?_, hname, rfl⟩
        rw [hsKept, List.mem_filter]
        exact ⟨hrow, hkeep⟩
    · rintro (⟨rfl, hmem⟩ | ⟨row, hrow, hname, rfl⟩)
      · exact List.mem_map.mpr ⟨_, hmem, rfl⟩
      · rw [hsKept, List.mem_filter] at hrow
        refine List.mem_map.mpr ⟨row, ?_, rfl⟩
        rw [htKept, List.mem_filter]
        refine ⟨List.mem_map.mpr ⟨row, hrow.1, by simp [hname]⟩, hrow.2⟩
  · constructor
    · intro hu
      obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hu
      by_cases hname : row.1 = name
      · have hrow' := hrow
        rw [hsKept, List.mem_filter] at hrow'
        have hrowEq := eq_of_mem_of_name hnodup hw hrow'.1 hname
        subst hrowEq
        exact Or.inl ⟨rfl, hrow⟩
      · exact Or.inr ⟨row, hrow, hname, rfl⟩
    · rintro (⟨rfl, hmem⟩ | ⟨row, hrow, _, rfl⟩)
      · exact List.mem_map.mpr ⟨_, hmem, rfl⟩
      · exact List.mem_map.mpr ⟨row, hrow, rfl⟩

/-- **Every other hole and every other AF argument persists.** Across an
in-place discharge, a source hole or complete argument other than the
discharged argument's old term is still a target hole or complete argument,
and conversely every target hole or complete argument other than its new term
was one in the source. -/
theorem dischargeOpen_others_persist {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState}
    {name : String} {π : Attack.Pos} {q : QuestionId} {v : SupportTerm}
    {w w' : SupportTerm}
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.dischargeOpen name π q v) = .ok τ)
    (hw : RawAttack.lookupArg σ.argsRaw name = some w)
    (hw' : Discharge.dischargeAt q v π w = some w') :
    (∀ u ∈ sourceRun.checked.program.holes, u ≠ w →
        u ∈ targetRun.checked.program.holes) ∧
      (∀ u ∈ targetRun.checked.program.holes, u ≠ w' →
        u ∈ sourceRun.checked.program.holes) ∧
      (∀ u ∈ sourceRun.checked.program.args, u ≠ w →
        u ∈ targetRun.checked.program.args) ∧
      (∀ u ∈ targetRun.checked.program.args, u ≠ w' →
        u ∈ sourceRun.checked.program.args) := by
  obtain ⟨hτ, hchecked, _, _⟩ := dischargeOpen_runs sourceRun targetRun happly
  have hsSound := Check.Unit.checkUnit_sound sourceRun.check_ok
  have htSound := Check.Unit.checkUnit_sound targetRun.check_ok
  have hsArgs := hsSound.args_eq
  have hsHoles := hsSound.holes_eq
  have htArgs := htSound.args_eq
  have htHoles := htSound.holes_eq
  dsimp only at hsArgs hsHoles htArgs htHoles
  have hpolicy : τ.policy = σ.policy := by rw [hτ]
  rw [hpolicy] at htArgs htHoles
  replace htArgs := htArgs.trans (by rw [hchecked])
  replace htHoles := htHoles.trans (by rw [hchecked])
  have hterms := dischargeOpen_kept_terms sourceRun targetRun happly hw hw'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu hne
    rw [hsHoles, Check.mem_holeArgs_iff] at hu
    rw [htHoles, Check.mem_holeArgs_iff]
    refine ⟨?_, hu.2⟩
    rcases (hterms u).2.mp hu.1 with ⟨rfl, _⟩ | hrow
    · exact absurd rfl hne
    · exact (hterms u).1.mpr (Or.inr hrow)
  · intro u hu hne
    rw [htHoles, Check.mem_holeArgs_iff] at hu
    rw [hsHoles, Check.mem_holeArgs_iff]
    refine ⟨?_, hu.2⟩
    rcases (hterms u).1.mp hu.1 with ⟨rfl, _⟩ | hrow
    · exact absurd rfl hne
    · exact (hterms u).2.mpr (Or.inr hrow)
  · intro u hu hne
    rw [hsArgs, Check.mem_completeArgs_iff] at hu
    rw [htArgs, Check.mem_completeArgs_iff]
    refine ⟨?_, hu.2⟩
    rcases (hterms u).2.mp hu.1 with ⟨rfl, _⟩ | hrow
    · exact absurd rfl hne
    · exact (hterms u).1.mpr (Or.inr hrow)
  · intro u hu hne
    rw [htArgs, Check.mem_completeArgs_iff] at hu
    rw [hsArgs, Check.mem_completeArgs_iff]
    refine ⟨?_, hu.2⟩
    rcases (hterms u).1.mp hu.1 with ⟨rfl, _⟩ | hrow
    · exact absurd rfl hne
    · exact (hterms u).2.mpr (Or.inr hrow)

/-- The discharged row stays retained when its source row was retained and the
discharging term uses no quarantined leaf. -/
theorem dischargeOpen_row_kept {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState}
    {name : String} {π : Attack.Pos} {q : QuestionId} {v : SupportTerm}
    {w w' : SupportTerm}
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.dischargeOpen name π q v) = .ok τ)
    (hw' : Discharge.dischargeAt q v π w = some w')
    (hkept : (name, w) ∈ sourceRun.admission.prune.keptArgs)
    (hclean : Groups.usesLeaf sourceRun.admission.prune.removedSeed v = false) :
    (name, w') ∈ targetRun.admission.prune.keptArgs := by
  obtain ⟨_, _, htKept, hsKept⟩ := dischargeOpen_runs sourceRun targetRun happly
  rw [hsKept, List.mem_filter] at hkept
  rw [htKept, List.mem_filter]
  refine ⟨List.mem_map.mpr ⟨(name, w), hkept.1, by simp [hw']⟩, ?_⟩
  have hw'clean :
      Groups.usesLeaf sourceRun.admission.prune.removedSeed w' = false := by
    cases huse : Groups.usesLeaf sourceRun.admission.prune.removedSeed w' with
    | false => rfl
    | true =>
        exfalso
        obtain ⟨l, hl, hseed⟩ := (usesLeaf_true_iff _ w').mp huse
        rcases (Discharge.leaves_dischargeAt hw' l).mp hl with hlw | hlv
        · have : Groups.usesLeaf sourceRun.admission.prune.removedSeed w = true :=
            (usesLeaf_true_iff _ w).mpr ⟨l, hlw, hseed⟩
          simp [this] at hkept
        · have : Groups.usesLeaf sourceRun.admission.prune.removedSeed v = true :=
            (usesLeaf_true_iff _ v).mpr ⟨l, hlv, hseed⟩
          rw [this] at hclean
          cases hclean
  simp [hw'clean]

private theorem eq_of_mem_of_nodup_map {α β : Type _} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l →
      f x = f y → x = y := by
  intro l
  induction l with
  | nil => intro _ x y hx; simp at hx
  | cons a rest ih =>
      intro hnodup x y hx hy hxy
      rw [List.map_cons] at hnodup
      obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hx with hxa | hxr
      · rcases List.mem_cons.mp hy with hya | hyr
        · rw [hxa, hya]
        · subst hxa
          exact absurd (hxy ▸ List.mem_map.mpr ⟨y, hyr, rfl⟩) hhead
      · rcases List.mem_cons.mp hy with hya | hyr
        · subst hya
          exact absurd (hxy.symm ▸ List.mem_map.mpr ⟨x, hxr, rfl⟩) hhead
        · exact ih htail hxr hyr hxy

/-- A complete term among the checked arguments supports every claim
equivalent to its conclusion. -/
theorem claimSupportFor_ne_nil_of_arg {canon : String → String}
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {unit : Lara.Unit.CheckedUnit canon Gamma CertOk} {w : SupportTerm}
    {C p : Atom} (hw : w ∈ unit.program.args)
    (hC : HasSupport canon unit.policy.ruleLookup Gamma CertOk w C [])
    (hp : equiv canon C p) :
    Consistency.claimSupportFor unit p ≠ [] := by
  rw [← unit.nodes_terms] at hw
  obtain ⟨node, hnode, rfl⟩ := List.mem_map.mp hw
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hnode
  have hconcl : node.conclusion = C := (hasSupport_unique node.valid hC).1
  have hmem : i ∈ Consistency.claimSupportFor unit p :=
    Consistency.mem_claimSupportFor_iff.mpr ⟨node, hi, by rw [hconcl]; exact hp⟩
  intro hnil
  rw [hnil] at hmem
  cases hmem

/-- **A hole discharged to completion becomes an AF node.** If the discharged
argument was a retained hole, the discharging term uses no quarantined leaf,
and the rewritten term is complete, then the target reports the new term as a
complete argument and neither its old nor its new term as a hole; every other
hole and complete argument persists (`dischargeOpen_others_persist`), and
every claim equivalent to its conclusion leaves `gap` under every extension
semantics. -/
theorem dischargeOpen_hole_becomes_node {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState}
    {name : String} {π : Attack.Pos} {q : QuestionId} {v : SupportTerm}
    {w w' : SupportTerm} {C : Atom}
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.dischargeOpen name π q v) = .ok τ)
    (hw : RawAttack.lookupArg σ.argsRaw name = some w)
    (hw' : Discharge.dischargeAt q v π w = some w')
    (hkept : (name, w) ∈ sourceRun.admission.prune.keptArgs)
    (hclean : Groups.usesLeaf sourceRun.admission.prune.removedSeed v = false)
    (hcomplete : HasSupport canon σ.policy.ruleLookup
      (Admission.buildGamma sourceRun.admission.prune.checkedLeaves)
      (certOkOf reg) w' C []) :
    w' ∈ targetRun.checked.program.args ∧
      w' ∉ targetRun.checked.program.holes ∧
      w ∉ targetRun.checked.program.holes ∧
      ∀ (sem : Semantics.ExtensionSemantics) (p : Atom), equiv canon C p →
        coreObs sem targetRun.checked p ≠
          .observed Grounded.Status.gap := by
  obtain ⟨hτ, hchecked, _, hsKept⟩ := dischargeOpen_runs sourceRun targetRun happly
  have hsSound := Check.Unit.checkUnit_sound sourceRun.check_ok
  have htSound := Check.Unit.checkUnit_sound targetRun.check_ok
  have htArgs := htSound.args_eq
  have htHoles := htSound.holes_eq
  dsimp only at htArgs htHoles
  have hpolicy : τ.policy = σ.policy := by rw [hτ]
  rw [hpolicy] at htArgs htHoles
  replace htArgs := htArgs.trans (by rw [hchecked])
  replace htHoles := htHoles.trans (by rw [hchecked])
  have hterms := dischargeOpen_kept_terms sourceRun targetRun happly hw hw'
  have hkept' := dischargeOpen_row_kept sourceRun targetRun happly hw' hkept hclean
  have hw'mem : w' ∈ targetRun.checked.program.args := by
    rw [htArgs, Check.mem_completeArgs_iff]
    exact ⟨(hterms w').1.mpr (Or.inl ⟨rfl, hkept'⟩), C, hcomplete⟩
  refine ⟨hw'mem, ?_, ?_, ?_⟩
  · rw [htHoles]
    exact Check.completeArgs_holeArgs_disjoint (by
      rw [← htArgs]; exact hw'mem)
  · intro hwHole
    rw [htHoles, Check.mem_holeArgs_iff] at hwHole
    rcases (hterms w).1.mp hwHole.1 with ⟨hww', _⟩ | ⟨row, hrow, hname, hrowTerm⟩
    · exact Discharge.dischargeAt_ne hw' hww'.symm
    · -- another retained source row carries `w`: duplicate kept terms
      have hnodupTerms := hsSound.raw_nodup
      dsimp only at hnodupTerms
      have hinj := eq_of_mem_of_nodup_map hnodupTerms hrow hkept hrowTerm
      exact hname (by rw [hinj])
  · intro sem p hp
    unfold coreObs
    rw [Ne, Semantics.observe_gap_iff]
    have hpolicyChecked : targetRun.checked.policy = σ.policy := by
      rw [htSound.policy_eq]; exact hpolicy
    apply claimSupportFor_ne_nil_of_arg hw'mem _ hp
    rw [hpolicyChecked, hchecked]
    exact hcomplete

end Lara.Update
