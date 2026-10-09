/-
Status transitions of the completion updates (issues #11 and #14).
`docs/theory-core.md#holes-and-the-agm-probe` and §6a record the design and
`docs/theory-core.md#source-updates-and-status-dynamics` records the claim boundary.

Neither completion update has an unrestricted transition theorem.  An in-place
discharge of an optional question of a complete argument with an incomplete
term turns an AF node into a hole, and its claim can enter `gap`
(`Examples.UpdateCompletion.discharge_optional_enters_gap`); a raw attack
already sourced at the discharged argument starts to fire once the argument is
complete, so a justified claim can become refuted
(`Examples.UpdateCompletion.discharge_outgoing_defeats`).  The results here are
the restricted ones.

* A discharge that completes a retained hole inserts one AF node into the
  source framework.  The claim can leave `gap` only if it is equivalent to the
  completed conclusion, no claim enters `gap`, and when no raw attack names
  the discharged argument the new node is a sink, so the grounded guarantees
  of a fresh complete `addInstance` hold
  (`dischargeOpen_completion_sink_status_monotone`).
* An additive batch keeps every old AF argument, so no claim enters `gap`; a
  batch with no `addInstance` keeps the AF arguments, so no claim leaves `gap`;
  a batch with no `addAttack` appends only sinks, so the grounded guarantees of
  `addInstance` hold.  A batch with an `addAttack` gets nothing more, since one
  `addAttack` already reaches every non-`gap` transition.
* A completed argument that no compiled attack reaches is labelled `in`, so
  every claim equivalent to its conclusion is `justified`, and publicly so
  unless the claim is blocked (`dischargeOpen_completion_justified`,
  `atomic_completion_justified`).
-/
import Lara.Update.Completion

namespace Lara.Update

open Lara Lara.Support
open Lara.Presentation (Admission)

/-! ### Inserting arguments into a checked unit -/

/-- Where the source AF index `i` lands when `n` arguments are inserted after
the first `k`. -/
def insertShift (k n i : Nat) : Nat := if i < k then i else i + n

private theorem getElem?_insertShift {α : Type _} (S₁ N S₂ : List α) (i : Nat) :
    (S₁ ++ N ++ S₂)[insertShift S₁.length N.length i]? = (S₁ ++ S₂)[i]? := by
  unfold insertShift
  by_cases h : i < S₁.length
  · rw [if_pos h, List.append_assoc, List.getElem?_append_left h,
      List.getElem?_append_left h]
  · rw [if_neg h, List.getElem?_append_right (by simp; omega),
      List.getElem?_append_right (by omega)]
    simp only [List.length_append]
    congr 1
    omega

section Insert

variable {canon : String → String} {Gamma₁ Gamma₂ : LeafId → Option Atom}
  {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}

/-- A term at a position of the AF arguments is the term of the node there. -/
private theorem node_at_arg (unit : Lara.Unit.CheckedUnit canon Gamma₁ CertOk)
    {i : Nat} {w : SupportTerm} (h : unit.program.args[i]? = some w) :
    ∃ node, unit.nodes[i]? = some node ∧ node.term = w := by
  rw [← unit.nodes_terms, List.getElem?_map] at h
  cases hnode : unit.nodes[i]? with
  | none => rw [hnode] at h; cases h
  | some node =>
      rw [hnode] at h
      exact ⟨node, rfl, Option.some.inj h⟩

/-- The term of the node at a position is the AF argument there. -/
private theorem arg_at_node (unit : Lara.Unit.CheckedUnit canon Gamma₁ CertOk)
    {i : Nat} {node : Compile.CheckedNode canon unit.policy.ruleLookup Gamma₁ CertOk}
    (h : unit.nodes[i]? = some node) :
    unit.program.args[i]? = some node.term := by
  rw [← unit.nodes_terms, List.getElem?_map, h]
  rfl

/-- **Inserted arguments keep every old support index, renamed.** When the
target's AF arguments are the source's with `N` inserted after `S₁`, and the
source's complete supports transfer to the target context, every support index
of a claim in the source is a support index of the same claim in the target,
shifted past the insertion. -/
theorem claimSupportFor_insertShift
    (source : Lara.Unit.CheckedUnit canon Gamma₁ CertOk)
    (target : Lara.Unit.CheckedUnit canon Gamma₂ CertOk)
    (S₁ N S₂ : List SupportTerm)
    (hS : source.program.args = S₁ ++ S₂)
    (hT : target.program.args = S₁ ++ N ++ S₂)
    (hpolicy : target.policy = source.policy)
    (hsupport : ∀ {w C}, w ∈ source.program.args →
      HasSupport canon source.policy.ruleLookup Gamma₁ CertOk w C [] →
      HasSupport canon source.policy.ruleLookup Gamma₂ CertOk w C [])
    (p : Atom) {i : Nat} (hi : i ∈ Consistency.claimSupportFor source p) :
    insertShift S₁.length N.length i ∈ Consistency.claimSupportFor target p := by
  obtain ⟨node, hnode, hconcl⟩ := Consistency.mem_claimSupportFor_iff.mp hi
  have hsourceArg := arg_at_node source hnode
  have htargetArg :
      target.program.args[insertShift S₁.length N.length i]? = some node.term := by
    rw [hT, getElem?_insertShift S₁ N S₂ i, ← hS]
    exact hsourceArg
  obtain ⟨tnode, htnode, hterm⟩ := node_at_arg target htargetArg
  have hvalid :
      HasSupport canon target.policy.ruleLookup Gamma₂ CertOk
        node.term node.conclusion [] := by
    rw [hpolicy]
    exact hsupport (List.mem_of_getElem? hsourceArg) node.valid
  have hsame : tnode.conclusion = node.conclusion :=
    (hasSupport_unique (by rw [← hterm]; exact tnode.valid) hvalid).1
  exact Consistency.mem_claimSupportFor_iff.mpr ⟨tnode, htnode, by rw [hsame]; exact hconcl⟩

/-- **Inserted arguments without outgoing attacks form a sink embedding.** If
the target's AF arguments are the source's with `N` inserted after `S₁` and
the compiled attacks are unchanged, the target framework embeds the source
framework, shifting indices past the insertion, and the inserted arguments
attack nothing: every compiled attack is sourced at an old argument, and the
target's arguments are duplicate-free. -/
theorem sinkEmbedding_insertShift
    (source : Lara.Unit.CheckedUnit canon Gamma₁ CertOk)
    (target : Lara.Unit.CheckedUnit canon Gamma₂ CertOk)
    (S₁ N S₂ : List SupportTerm)
    (hS : source.program.args = S₁ ++ S₂)
    (hT : target.program.args = S₁ ++ N ++ S₂)
    (hatts : target.program.atts = source.program.atts) :
    Grounded.SinkEmbedding (Compile.checkedAF source.program)
      (Compile.checkedAF target.program) (insertShift S₁.length N.length)
      ((List.range N.length).map (S₁.length + ·)) := by
  have hSlen : source.program.args.length = S₁.length + S₂.length := by
    rw [hS, List.length_append]
  have hTlen : target.program.args.length = S₁.length + N.length + S₂.length := by
    rw [hT, List.length_append, List.length_append]
  refine { map_mem := ?_, mem_cases := ?_, old_attack := ?_, sink_no_out := ?_ }
  · intro (a : Nat) ha
    simp only [Compile.checkedAF, Compile.toAF, List.mem_range] at ha ⊢
    unfold insertShift
    split <;> omega
  · intro (b : Nat) hb
    simp only [Compile.checkedAF, Compile.toAF, List.mem_range] at hb ⊢
    by_cases h1 : b < S₁.length
    · exact Or.inr ⟨b, by omega, by simp [insertShift, h1]⟩
    · by_cases h2 : b < S₁.length + N.length
      · exact Or.inl (List.mem_map.mpr ⟨b - S₁.length,
          List.mem_range.mpr (by omega), by show S₁.length + (b - S₁.length) = b; omega⟩)
      · refine Or.inr ⟨b - N.length, by omega, ?_⟩
        simp only [insertShift]
        rw [if_neg (by omega)]
        show b - N.length + N.length = b
        omega
  · intro (a : Nat) ha (b : Nat) hb
    simp only [Compile.checkedAF, Compile.toAF, List.mem_range] at ha hb ⊢
    unfold Compile.edgeB
    rw [hT, getElem?_insertShift S₁ N S₂ a, getElem?_insertShift S₁ N S₂ b,
      ← hS, hatts]
  · intro s hs b
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hs
    rw [List.mem_range] at hj
    have hat : target.program.args[S₁.length + j]? = N[j]? := by
      rw [hT, List.append_assoc, List.getElem?_append_right (by omega),
        List.getElem?_append_left (by omega)]
      congr 1
      omega
    obtain ⟨u, hu⟩ := Support.getElem?_some_of_lt N j hj
    have huN : u ∈ N := List.mem_of_getElem? hu
    have hnodup := target.program.nodup
    rw [hT] at hnodup
    have huOld : u ∉ source.program.args := by
      intro hmem
      rw [hS] at hmem
      rw [List.nodup_append, List.nodup_append] at hnodup
      obtain ⟨⟨_, _, h1N⟩, _, h12⟩ := hnodup
      rcases List.mem_append.mp hmem with hm | hm
      · exact h1N u hm u huN rfl
      · exact h12 u (List.mem_append_right _ huN) u hm rfl
    simp only [Compile.checkedAF, Compile.toAF]
    unfold Compile.edgeB
    rw [hat, hu]
    split
    · rename_i src tgt hsrc _
      cases hsrc
      apply List.any_eq_false.mpr
      intro k hk hcov
      rw [Bool.and_eq_true] at hcov
      have hsource := of_decide_eq_true hcov.1
      rw [hatts] at hk
      exact huOld (hsource ▸ source.program.source_declared k hk)
    · rfl

/-- The compiled framework's carrier is duplicate-free. -/
private theorem checkedAF_nodup (unit : Lara.Unit.CheckedUnit canon Gamma₁ CertOk) :
    (Compile.checkedAF unit.program).args.Nodup := by
  change (List.range unit.program.args.length).Nodup
  exact List.nodup_range

/-- A support index is an argument of the compiled framework. -/
private theorem claimSupportFor_mem_checkedAF
    (unit : Lara.Unit.CheckedUnit canon Gamma₁ CertOk) {p : Atom} {i : Nat}
    (hi : i ∈ Consistency.claimSupportFor unit p) :
    i ∈ (Compile.checkedAF unit.program).args := by
  obtain ⟨node, hnode, _⟩ := Consistency.mem_claimSupportFor_iff.mp hi
  have hlt := Support.lt_of_getElem?_some (arg_at_node unit hnode)
  simpa [Compile.checkedAF, Compile.toAF] using hlt

/-- **Inserted arguments never move a claim into `gap`**, under every
extension semantics. -/
theorem coreObs_not_gap_of_insert (sem : Semantics.ExtensionSemantics)
    (source : Lara.Unit.CheckedUnit canon Gamma₁ CertOk)
    (target : Lara.Unit.CheckedUnit canon Gamma₂ CertOk)
    (S₁ N S₂ : List SupportTerm)
    (hS : source.program.args = S₁ ++ S₂)
    (hT : target.program.args = S₁ ++ N ++ S₂)
    (hpolicy : target.policy = source.policy)
    (hsupport : ∀ {w C}, w ∈ source.program.args →
      HasSupport canon source.policy.ruleLookup Gamma₁ CertOk w C [] →
      HasSupport canon source.policy.ruleLookup Gamma₂ CertOk w C [])
    (p : Atom) (hsource : coreObs sem source p ≠ .observed .gap) :
    coreObs sem target p ≠ .observed .gap := by
  unfold coreObs at hsource ⊢
  rw [Ne, Semantics.observe_gap_iff] at hsource ⊢
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hsource
  intro hempty
  have hmem := claimSupportFor_insertShift source target S₁ N S₂ hS hT hpolicy
    hsupport p hi
  change insertShift S₁.length N.length i ∈
    (Consistency.completeClaimFor target p).support at hmem
  rw [hempty] at hmem
  cases hmem

/-- **A claim stays in `gap` unless an inserted argument supports it**, under
every extension semantics. -/
theorem coreObs_gap_of_insert (sem : Semantics.ExtensionSemantics)
    (source : Lara.Unit.CheckedUnit canon Gamma₁ CertOk)
    (target : Lara.Unit.CheckedUnit canon Gamma₂ CertOk)
    (S₁ N S₂ : List SupportTerm)
    (hS : source.program.args = S₁ ++ S₂)
    (hT : target.program.args = S₁ ++ N ++ S₂)
    (hpolicy : target.policy = source.policy)
    (hsupportBack : ∀ {w C}, w ∈ source.program.args →
      HasSupport canon source.policy.ruleLookup Gamma₂ CertOk w C [] →
      HasSupport canon source.policy.ruleLookup Gamma₁ CertOk w C [])
    (p : Atom)
    (hnew : ∀ u ∈ N, ∀ C, HasSupport canon source.policy.ruleLookup Gamma₂ CertOk
      u C [] → ¬ equiv canon C p)
    (hsource : coreObs sem source p = .observed .gap) :
    coreObs sem target p = .observed .gap := by
  unfold coreObs at hsource ⊢
  rw [Semantics.observe_gap_iff] at hsource ⊢
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro j hj
  obtain ⟨tnode, htnode, hconcl⟩ := Consistency.mem_claimSupportFor_iff.mp hj
  have htargetArg := arg_at_node target htnode
  have hvalid :
      HasSupport canon source.policy.ruleLookup Gamma₂ CertOk
        tnode.term tnode.conclusion [] := by
    rw [← hpolicy]
    exact tnode.valid
  have hmem := List.mem_of_getElem? htargetArg
  rw [hT, List.mem_append, List.mem_append] at hmem
  have hold : tnode.term ∈ source.program.args := by
    rcases hmem with (h | h) | h
    · rw [hS]; exact List.mem_append_left _ h
    · exact absurd hconcl (hnew _ h _ hvalid)
    · rw [hS]; exact List.mem_append_right _ h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hold
  obtain ⟨node, hnode, hterm⟩ := node_at_arg source hi
  have hsame : node.conclusion = tnode.conclusion :=
    (hasSupport_unique (by rw [← hterm]; exact node.valid)
      (hsupportBack hold hvalid)).1
  have hiSupport : i ∈ Consistency.claimSupportFor source p :=
    Consistency.mem_claimSupportFor_iff.mpr ⟨node, hnode, by rw [hsame]; exact hconcl⟩
  change i ∈ (Consistency.completeClaimFor source p).support at hiSupport
  rw [hsource] at hiSupport
  cases hiSupport

/-- **Inserted sinks keep the grounded guarantees of a fresh instance.** With
the compiled attacks unchanged, a grounded `justified` claim stays
`justified`, and a grounded `contested` claim does not become `defeated`. -/
theorem grounded_sink_monotone_of_insert
    (source : Lara.Unit.CheckedUnit canon Gamma₁ CertOk)
    (target : Lara.Unit.CheckedUnit canon Gamma₂ CertOk)
    (S₁ N S₂ : List SupportTerm)
    (hS : source.program.args = S₁ ++ S₂)
    (hT : target.program.args = S₁ ++ N ++ S₂)
    (hpolicy : target.policy = source.policy)
    (hsupport : ∀ {w C}, w ∈ source.program.args →
      HasSupport canon source.policy.ruleLookup Gamma₁ CertOk w C [] →
      HasSupport canon source.policy.ruleLookup Gamma₂ CertOk w C [])
    (hatts : target.program.atts = source.program.atts) (p : Atom) :
    ((CoreTransition Semantics.groundedSem source target p).1 =
        .observed Grounded.Status.justified →
      (CoreTransition Semantics.groundedSem source target p).2 =
        .observed Grounded.Status.justified) ∧
    ((CoreTransition Semantics.groundedSem source target p).1 =
        .observed Grounded.Status.contested →
      (CoreTransition Semantics.groundedSem source target p).2 ≠
        .observed Grounded.Status.defeated) := by
  have hemb := sinkEmbedding_insertShift source target S₁ N S₂ hS hT hatts
  have hcarrier : ∀ i ∈ (Consistency.completeClaimFor source p).support,
      i ∈ (Compile.checkedAF source.program).args :=
    fun i hi => claimSupportFor_mem_checkedAF source hi
  have hmap : ∀ i ∈ (Consistency.completeClaimFor source p).support,
      insertShift S₁.length N.length i ∈
        (Consistency.completeClaimFor target p).support :=
    fun i hi => claimSupportFor_insertShift source target S₁ N S₂ hS hT hpolicy
      hsupport p hi
  simp only [CoreTransition, coreObs]
  rw [Semantics.observe_grounded (checkedAF_nodup source),
    Semantics.observe_grounded (checkedAF_nodup target)]
  refine ⟨fun h => ?_, fun h hdef => ?_⟩
  · exact congrArg Semantics.ClaimObservation.observed
      (hemb.justified_preserved hcarrier hmap
        (Semantics.ClaimObservation.observed.inj h))
  · exact hemb.contested_not_defeated hcarrier hmap
      (Semantics.ClaimObservation.observed.inj h)
      (Semantics.ClaimObservation.observed.inj hdef)

end Insert

/-! ### An unattacked complete argument is justified -/

section Unattacked

variable {canon : String → String} {Gamma : LeafId → Option Atom}
  {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}

/-- No compiled attack reaches `w`: no attacked occurrence of a compiled
attack is contained in `w`.  Every closure edge into `w` comes from such an
attack (`Compile.edge_iff`), so this is exactly "nothing attacks `w` in the
compiled framework". -/
def Unattacked (atts : List Attack.Attack) (w : SupportTerm) : Prop :=
  ∀ k ∈ atts, ∀ t, Compile.AttackOcc k t → ¬ Compile.Contains w t

/-- **An unattacked complete argument justifies its conclusion.** If a
complete AF argument concluding `C` is reached by no compiled attack, it is
labelled `in`, so every claim equivalent to `C` is grounded `justified`. -/
theorem statusC_justified_of_unattacked
    (unit : Lara.Unit.CheckedUnit canon Gamma CertOk) {w : SupportTerm}
    {C p : Atom} (hw : w ∈ unit.program.args)
    (hC : HasSupport canon unit.policy.ruleLookup Gamma CertOk w C [])
    (hp : equiv canon C p) (hfree : Unattacked unit.program.atts w) :
    Grounded.statusC (Compile.checkedAF unit.program)
      (Consistency.completeClaimFor unit p) = .justified := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
  obtain ⟨node, hnode, hterm⟩ := node_at_arg unit hi
  have hconcl : node.conclusion = C :=
    (hasSupport_unique (by rw [← hterm]; exact node.valid) hC).1
  have hmem : i ∈ (Consistency.completeClaimFor unit p).support :=
    Consistency.mem_claimSupportFor_iff.mpr ⟨node, hnode, by rw [hconcl]; exact hp⟩
  apply (Grounded.statusC_justified_iff _ _).mpr
  refine ⟨i, hmem, Grounded.labelC_inn_of_unattacked
    (claimSupportFor_mem_checkedAF unit hmem) ?_⟩
  intro b _
  change Compile.edgeB unit.program b i = false
  cases hedge : Compile.edgeB unit.program b i with
  | false => rfl
  | true =>
      exfalso
      have hrange := (Compile.edgeB_faithful unit.program).ranged _ _ hedge
      obtain ⟨src, hsrc⟩ := Support.getElem?_some_of_lt _ b hrange.1
      obtain ⟨_, _, k, hk, _, t, hocc, hcont⟩ := (Compile.edgeB_iff hsrc hi).mp hedge
      exact hfree k hk t hocc hcont

/-- The grounded observation form of `statusC_justified_of_unattacked`. -/
theorem coreObs_justified_of_unattacked
    (unit : Lara.Unit.CheckedUnit canon Gamma CertOk) {w : SupportTerm}
    {C p : Atom} (hw : w ∈ unit.program.args)
    (hC : HasSupport canon unit.policy.ruleLookup Gamma CertOk w C [])
    (hp : equiv canon C p) (hfree : Unattacked unit.program.atts w) :
    coreObs Semantics.groundedSem unit p = .observed .justified := by
  unfold coreObs
  rw [Semantics.observe_grounded (checkedAF_nodup unit)]
  exact congrArg _ (statusC_justified_of_unattacked unit hw hC hp hfree)

end Unattacked

/-- **The public report agrees when nothing blocks the claim.** An unattacked
complete argument of an accepted run publishes every claim equivalent to its
conclusion as `justified` unless the production blocking computation blocks
that claim; a clean run blocks nothing (`publicReport_eq_core_of_clean`). -/
theorem publicReport_justified_of_unattacked {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) {w : SupportTerm} {C p : Atom}
    (hw : w ∈ run.checked.program.args)
    (hC : HasSupport canon run.checked.policy.ruleLookup
      (Admission.buildGamma run.admission.prune.checkedLeaves) (certOkOf reg) w C [])
    (hp : equiv canon C p) (hfree : Unattacked run.checked.program.atts w)
    (hunblocked : p ∉ blockedQueriesForRun run [p]) :
    publicReport run p = .justified := by
  unfold publicReport
  rw [if_neg hunblocked, statusC_justified_of_unattacked run.checked hw hC hp hfree]
  rfl

/-! ### In-place discharge of a retained hole to completion -/

/-- The kept attacks of a run are the aligned selection of its resolved
attacks whose two endpoints name kept rows. -/
private theorem AcceptedRun.keptAttacks_select {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) :
    run.admission.prune.keptAttacks =
      RawAttack.selectAligned
        (fun ra => decide (ra.endpoints.1 ∈ run.admission.prune.keptArgs.map (·.1)) &&
          decide (ra.endpoints.2 ∈ run.admission.prune.keptArgs.map (·.1)))
        state.rawAtts run.declared.resolved := by
  rw [run.prune_eq]
  rfl

private theorem zipWith_eq_right {α β : Type _} (f : α → β → β) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (∀ x ∈ xs, ∀ y, f x y = y) → List.zipWith f xs ys = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hlen, hf => by
      rw [List.zipWith_cons_cons, hf x (by simp) y,
        zipWith_eq_right f xs ys (by simpa using hlen)
          (fun x' hx' => hf x' (by simp [hx']))]
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

private theorem retarget_self (k : Attack.Attack) : retarget k.source k.target k = k := by
  cases k <;> rfl

/-- The kept rows across a discharge of a retained row that stays retained:
the discharged row keeps its place among the same kept rows. -/
private theorem dischargeOpen_kept_split {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState}
    {name : String} {π : Attack.Pos} {q : QuestionId} {v : SupportTerm}
    {w w' : SupportTerm}
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.dischargeOpen name π q v) = .ok τ)
    (hw : RawAttack.lookupArg σ.argsRaw name = some w)
    (hw' : Discharge.dischargeAt q v π w = some w')
    (hkept : (name, w) ∈ sourceRun.admission.prune.keptArgs)
    (hclean : Groups.usesLeaf sourceRun.admission.prune.removedSeed v = false) :
    ∃ F₁ F₂, sourceRun.admission.prune.keptArgs = F₁ ++ (name, w) :: F₂ ∧
      targetRun.admission.prune.keptArgs = F₁ ++ (name, w') :: F₂ := by
  have hkept' := dischargeOpen_row_kept sourceRun targetRun happly hw' hkept hclean
  obtain ⟨_, _, htKept, hsKept⟩ := dischargeOpen_runs sourceRun targetRun happly
  obtain ⟨row, hrow, hrowName, hrowTerm⟩ := RawAttack.lookupArg_some_row _ hw
  have hrowEq : row = (name, w) := by
    cases row
    simp only at hrowName hrowTerm
    rw [hrowName, hrowTerm]
  rw [hrowEq] at hrow
  obtain ⟨A₁, A₂, hA⟩ := List.append_of_mem hrow
  have hnodup := sourceRun.declared.ids_nodup
  rw [hA, List.map_append, List.map_cons, List.nodup_append] at hnodup
  obtain ⟨_, hnodup₂, hdisj⟩ := hnodup
  have hA₁ : ∀ x ∈ A₁, x.1 ≠ name := fun x hx heq =>
    hdisj x.1 (List.mem_map.mpr ⟨x, hx, rfl⟩) name (by simp) heq
  have hA₂ : ∀ x ∈ A₂, x.1 ≠ name := fun x hx heq =>
    (List.nodup_cons.mp hnodup₂).1 (heq ▸ List.mem_map.mpr ⟨x, hx, rfl⟩)
  have hrows : dischargeRows σ.argsRaw name π q v = A₁ ++ (name, w') :: A₂ := by
    unfold dischargeRows
    rw [hA, List.map_append, List.map_cons]
    have hid : ∀ (xs : List (String × SupportTerm)), (∀ x ∈ xs, x.1 ≠ name) →
        xs.map (fun row => if row.1 = name then
          (row.1, (Discharge.dischargeAt q v π row.2).getD row.2) else row) = xs := by
      intro xs hxs
      conv => rhs; rw [← List.map_id xs]
      apply List.map_congr_left
      intro x hx
      simp [hxs x hx]
    rw [hid A₁ hA₁, hid A₂ hA₂]
    simp [hw']
  let keep := fun row : String × SupportTerm =>
    !Groups.usesLeaf sourceRun.admission.prune.removedSeed row.2
  have hkeepw : keep (name, w) = true := by
    have h := hkept
    rw [hsKept, List.mem_filter] at h
    exact h.2
  have hkeepw' : keep (name, w') = true := by
    have h := hkept'
    rw [htKept, List.mem_filter] at h
    exact h.2
  refine ⟨A₁.filter keep, A₂.filter keep, ?_, ?_⟩
  · rw [hsKept, hA, List.filter_append, List.filter_cons_of_pos hkeepw]
  · rw [htKept, hrows, List.filter_append, List.filter_cons_of_pos hkeepw']

/-- The AF arguments across a discharge that completes a retained hole: the
completed term is inserted where its row stands among the old AF arguments. -/
private theorem dischargeOpen_args_split {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState}
    {name : String} {π : Attack.Pos} {q : QuestionId} {v : SupportTerm}
    {w w' : SupportTerm} {C : Atom}
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.dischargeOpen name π q v) = .ok τ)
    (hw : RawAttack.lookupArg σ.argsRaw name = some w)
    (hw' : Discharge.dischargeAt q v π w = some w')
    (hkept : (name, w) ∈ sourceRun.admission.prune.keptArgs)
    (hclean : Groups.usesLeaf sourceRun.admission.prune.removedSeed v = false)
    (hhole : w ∈ sourceRun.checked.program.holes)
    (hcomplete : HasSupport canon σ.policy.ruleLookup
      (Admission.buildGamma sourceRun.admission.prune.checkedLeaves)
      (certOkOf reg) w' C []) :
    ∃ S₁ S₂, sourceRun.checked.program.args = S₁ ++ S₂ ∧
      targetRun.checked.program.args = S₁ ++ [w'] ++ S₂ := by
  obtain ⟨F₁, F₂, hsK, htK⟩ :=
    dischargeOpen_kept_split sourceRun targetRun happly hw hw' hkept hclean
  obtain ⟨hτ, hchecked, _, _⟩ := dischargeOpen_runs sourceRun targetRun happly
  have hsSound := Check.Unit.checkUnit_sound sourceRun.check_ok
  have htSound := Check.Unit.checkUnit_sound targetRun.check_ok
  have hsArgs := hsSound.args_eq
  have hsHoles := hsSound.holes_eq
  have htArgs := htSound.args_eq
  dsimp only at hsArgs hsHoles htArgs
  have hpolicy : τ.policy = σ.policy := by rw [hτ]
  rw [hpolicy] at htArgs
  replace htArgs := htArgs.trans (by rw [hchecked])
  have hwHole := hhole
  rw [hsHoles, Check.mem_holeArgs_iff] at hwHole
  obtain ⟨_, Cw, Ow, hCw, hOw⟩ := hwHole
  have hwNot : Check.argComplete σ.policy.ruleLookup
      (Admission.buildGamma sourceRun.admission.prune.checkedLeaves) reg w = false := by
    rw [Check.argComplete_of_hasSupport hCw]
    cases Ow with
    | nil => exact absurd rfl hOw
    | cons _ _ => rfl
  have hw'Yes : Check.argComplete σ.policy.ruleLookup
      (Admission.buildGamma sourceRun.admission.prune.checkedLeaves) reg w' = true :=
    Check.argComplete_iff.mpr ⟨C, hcomplete⟩
  refine ⟨Check.completeArgs σ.policy.ruleLookup
      (Admission.buildGamma sourceRun.admission.prune.checkedLeaves) reg (F₁.map (·.2)),
    Check.completeArgs σ.policy.ruleLookup
      (Admission.buildGamma sourceRun.admission.prune.checkedLeaves) reg (F₂.map (·.2)),
    ?_, ?_⟩
  · rw [hsArgs, hsK, List.map_append, List.map_cons, Check.completeArgs_append,
      ← List.singleton_append, Check.completeArgs_append]
    simp [Check.completeArgs, hwNot]
  · rw [htArgs, htK, List.map_append, List.map_cons, Check.completeArgs_append,
      ← List.singleton_append, Check.completeArgs_append]
    simp [Check.completeArgs, hw'Yes]

/-- The shared facts every completion-transition theorem for `dischargeOpen`
uses: the policies agree, and the checker contexts are equal. -/
private theorem dischargeOpen_policy_gamma {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState}
    {name : String} {π : Attack.Pos} {q : QuestionId} {v : SupportTerm}
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.dischargeOpen name π q v) = .ok τ) :
    targetRun.checked.policy = sourceRun.checked.policy ∧
      sourceRun.checked.policy = σ.policy ∧
      targetRun.admission.prune.checkedLeaves = sourceRun.admission.prune.checkedLeaves ∧
      targetRun.admission.prune.removedSeed = sourceRun.admission.prune.removedSeed := by
  obtain ⟨hτ, hchecked, _, _⟩ := dischargeOpen_runs sourceRun targetRun happly
  have hsSound := Check.Unit.checkUnit_sound sourceRun.check_ok
  have htSound := Check.Unit.checkUnit_sound targetRun.check_ok
  have hsPolicy : sourceRun.checked.policy = σ.policy := hsSound.policy_eq
  have htPolicy : targetRun.checked.policy = τ.policy := htSound.policy_eq
  refine ⟨?_, hsPolicy, hchecked, ?_⟩
  · rw [htPolicy, hsPolicy, hτ]
  · rw [targetRun.prune_eq, sourceRun.prune_eq]
    subst hτ
    rfl

/-- **Discharging a retained hole to completion never moves a claim into
`gap`**, under every extension semantics: every old AF argument survives with
its conclusion, and the completed term is added. -/
theorem dischargeOpen_completion_no_gap_entry {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState}
    {name : String} {π : Attack.Pos} {q : QuestionId} {v : SupportTerm}
    {w w' : SupportTerm} {C : Atom}
    (sem : Semantics.ExtensionSemantics)
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.dischargeOpen name π q v) = .ok τ)
    (hw : RawAttack.lookupArg σ.argsRaw name = some w)
    (hw' : Discharge.dischargeAt q v π w = some w')
    (hkept : (name, w) ∈ sourceRun.admission.prune.keptArgs)
    (hclean : Groups.usesLeaf sourceRun.admission.prune.removedSeed v = false)
    (hhole : w ∈ sourceRun.checked.program.holes)
    (hcomplete : HasSupport canon σ.policy.ruleLookup
      (Admission.buildGamma sourceRun.admission.prune.checkedLeaves)
      (certOkOf reg) w' C [])
    (p : Atom)
    (hsource : (CoreTransition sem sourceRun.checked targetRun.checked p).1 ≠
      .observed Grounded.Status.gap) :
    (CoreTransition sem sourceRun.checked targetRun.checked p).2 ≠
      .observed Grounded.Status.gap := by
  obtain ⟨S₁, S₂, hS, hT⟩ := dischargeOpen_args_split sourceRun targetRun happly
    hw hw' hkept hclean hhole hcomplete
  obtain ⟨hpolicy, _, hchecked, _⟩ := dischargeOpen_policy_gamma sourceRun targetRun happly
  exact coreObs_not_gap_of_insert sem sourceRun.checked targetRun.checked S₁ [w'] S₂
    hS hT hpolicy (fun _ h => by rw [hchecked]; exact h) p hsource

/-- **Only the completed conclusion leaves `gap`.** Across a discharge that
completes a retained hole with conclusion `C`, a claim not equivalent to `C`
that was in `gap` stays in `gap`, under every extension semantics;
`dischargeOpen_hole_becomes_node` moves every claim equivalent to `C` out of
`gap`. -/
theorem dischargeOpen_completion_gap_fixed {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState}
    {name : String} {π : Attack.Pos} {q : QuestionId} {v : SupportTerm}
    {w w' : SupportTerm} {C : Atom}
    (sem : Semantics.ExtensionSemantics)
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.dischargeOpen name π q v) = .ok τ)
    (hw : RawAttack.lookupArg σ.argsRaw name = some w)
    (hw' : Discharge.dischargeAt q v π w = some w')
    (hkept : (name, w) ∈ sourceRun.admission.prune.keptArgs)
    (hclean : Groups.usesLeaf sourceRun.admission.prune.removedSeed v = false)
    (hhole : w ∈ sourceRun.checked.program.holes)
    (hcomplete : HasSupport canon σ.policy.ruleLookup
      (Admission.buildGamma sourceRun.admission.prune.checkedLeaves)
      (certOkOf reg) w' C [])
    (p : Atom) (hp : ¬ equiv canon C p)
    (hsource : (CoreTransition sem sourceRun.checked targetRun.checked p).1 =
      .observed Grounded.Status.gap) :
    (CoreTransition sem sourceRun.checked targetRun.checked p).2 =
      .observed Grounded.Status.gap := by
  obtain ⟨S₁, S₂, hS, hT⟩ := dischargeOpen_args_split sourceRun targetRun happly
    hw hw' hkept hclean hhole hcomplete
  obtain ⟨hpolicy, hsPolicy, hchecked, _⟩ :=
    dischargeOpen_policy_gamma sourceRun targetRun happly
  refine coreObs_gap_of_insert sem sourceRun.checked targetRun.checked S₁ [w'] S₂
    hS hT hpolicy (fun _ h => by rw [hchecked] at h; exact h) p ?_ hsource
  intro u hu C' hC'
  rw [List.mem_singleton] at hu
  subst hu
  rw [hchecked, hsPolicy] at hC'
  rw [(hasSupport_unique hC' hcomplete).1]
  exact hp

/-- **A sink discharge keeps the grounded guarantees of a fresh instance.**
If the discharge completes a retained hole and no raw attack names the
discharged argument — the condition freshness gives `addInstance` — the
compiled attacks are unchanged and the completed argument is a sink inserted
into the old framework.  A grounded `justified` claim stays `justified`, and a
grounded `contested` claim does not become `defeated`
(`addInstance_sink_status_monotone`).  The attack condition cannot be dropped:
a raw attack sourced at the discharged argument fires once it is complete
(`Examples.UpdateCompletion.discharge_outgoing_defeats`). -/
theorem dischargeOpen_completion_sink_status_monotone {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState}
    {name : String} {π : Attack.Pos} {q : QuestionId} {v : SupportTerm}
    {w w' : SupportTerm} {C : Atom}
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.dischargeOpen name π q v) = .ok τ)
    (hw : RawAttack.lookupArg σ.argsRaw name = some w)
    (hw' : Discharge.dischargeAt q v π w = some w')
    (hkept : (name, w) ∈ sourceRun.admission.prune.keptArgs)
    (hclean : Groups.usesLeaf sourceRun.admission.prune.removedSeed v = false)
    (hhole : w ∈ sourceRun.checked.program.holes)
    (hcomplete : HasSupport canon σ.policy.ruleLookup
      (Admission.buildGamma sourceRun.admission.prune.checkedLeaves)
      (certOkOf reg) w' C [])
    (hunnamed : ∀ ra ∈ σ.rawAtts, ra.endpoints.1 ≠ name ∧ ra.endpoints.2 ≠ name)
    (p : Atom) :
    ((CoreTransition Semantics.groundedSem sourceRun.checked targetRun.checked p).1 =
        .observed Grounded.Status.justified →
      (CoreTransition Semantics.groundedSem sourceRun.checked targetRun.checked p).2 =
        .observed Grounded.Status.justified) ∧
    ((CoreTransition Semantics.groundedSem sourceRun.checked targetRun.checked p).1 =
        .observed Grounded.Status.contested →
      (CoreTransition Semantics.groundedSem sourceRun.checked targetRun.checked p).2 ≠
        .observed Grounded.Status.defeated) := by
  obtain ⟨F₁, F₂, hsK, htK⟩ :=
    dischargeOpen_kept_split sourceRun targetRun happly hw hw' hkept hclean
  obtain ⟨S₁, S₂, hS, hT⟩ := dischargeOpen_args_split sourceRun targetRun happly
    hw hw' hkept hclean hhole hcomplete
  obtain ⟨hpolicy, _, hchecked, _⟩ := dischargeOpen_policy_gamma sourceRun targetRun happly
  obtain ⟨hτ, _, _, _⟩ := dischargeOpen_runs sourceRun targetRun happly
  have hres : targetRun.declared.resolved = sourceRun.declared.resolved := by
    rw [dischargeOpen_resolved sourceRun targetRun happly]
    apply zipWith_eq_right _ _ _
      (RawAttack.resolveAttacks_length _ sourceRun.declared.resolve_eq)
    intro ra hra k
    simp only [dischargeTerm, if_neg (hunnamed ra hra).1, if_neg (hunnamed ra hra).2]
    exact retarget_self k
  have hrawAtts : τ.rawAtts = σ.rawAtts := by rw [hτ]
  have hkA : targetRun.admission.prune.keptAttacks =
      sourceRun.admission.prune.keptAttacks := by
    have hnames : (F₁ ++ (name, w') :: F₂).map (·.1) =
        (F₁ ++ (name, w) :: F₂).map (·.1) := by simp
    rw [targetRun.keptAttacks_select, sourceRun.keptAttacks_select, htK, hsK, hres,
      hrawAtts, hnames]
  have hsSound := Check.Unit.checkUnit_sound sourceRun.check_ok
  have htSound := Check.Unit.checkUnit_sound targetRun.check_ok
  have hsAtts := hsSound.atts_eq
  have htAtts := htSound.atts_eq
  dsimp only at hsAtts htAtts
  have hsSource : ∀ k ∈ sourceRun.admission.prune.keptAttacks,
      k.source ∈ sourceRun.admission.prune.keptArgs.map (·.2) := hsSound.raw_source
  have htNodup : (targetRun.admission.prune.keptArgs.map (·.2)).Nodup :=
    htSound.raw_nodup
  rw [htK, List.map_append, List.map_cons, List.nodup_append] at htNodup
  obtain ⟨_, htNodup₂, htDisj⟩ := htNodup
  have hatts : targetRun.checked.program.atts = sourceRun.checked.program.atts := by
    rw [htAtts, hsAtts, hkA, hT, hS]
    apply Check.liveAttacks_congr
    intro k hk
    have hne : k.source ≠ w' := by
      intro heq
      have hmem := hsSource k hk
      rw [hsK, List.map_append, List.map_cons, heq] at hmem
      rcases List.mem_append.mp hmem with h | h
      · exact htDisj w' h w' (List.mem_cons_self) rfl
      · rcases List.mem_cons.mp h with h | h
        · exact Discharge.dischargeAt_ne hw' h
        · exact (List.nodup_cons.mp htNodup₂).1 h
    simp [hne]
  exact grounded_sink_monotone_of_insert sourceRun.checked targetRun.checked S₁ [w'] S₂
    hS hT hpolicy (fun _ h => by rw [hchecked]; exact h) hatts p

/-- **An unattacked completion is justified.** If a discharge completes a
retained row (the `dischargeOpen_hole_becomes_node` premises) and no compiled
attack of the target reaches the completed argument, every claim equivalent to
its conclusion is grounded `justified` in the target, and publicly `justified`
unless the target's blocking computation blocks it. -/
theorem dischargeOpen_completion_justified {canon : String → String}
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
      (certOkOf reg) w' C [])
    (hfree : Unattacked targetRun.checked.program.atts w')
    (p : Atom) (hp : equiv canon C p) :
    coreObs Semantics.groundedSem targetRun.checked p = .observed .justified ∧
      (p ∉ blockedQueriesForRun targetRun [p] → publicReport targetRun p = .justified) := by
  have hnode := dischargeOpen_hole_becomes_node sourceRun targetRun happly hw hw'
    hkept hclean hcomplete
  obtain ⟨hpolicy, hsPolicy, hchecked, _⟩ :=
    dischargeOpen_policy_gamma sourceRun targetRun happly
  have hC : HasSupport canon targetRun.checked.policy.ruleLookup
      (Admission.buildGamma targetRun.admission.prune.checkedLeaves) (certOkOf reg)
      w' C [] := by
    rw [hpolicy, hsPolicy, hchecked]
    exact hcomplete
  exact ⟨coreObs_justified_of_unattacked targetRun.checked hnode.1 hC hp hfree,
    publicReport_justified_of_unattacked targetRun hnode.1 hC hp hfree⟩

/-- Under a clean source run the discharge blocks nothing, so the unattacked
completion is publicly `justified`. -/
theorem dischargeOpen_completion_public_justified {canon : String → String}
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
      (certOkOf reg) w' C [])
    (hfree : Unattacked targetRun.checked.program.atts w')
    (hbase : CleanBase sourceRun) (p : Atom) (hp : equiv canon C p) :
    publicReport targetRun p = .justified := by
  obtain ⟨_, _, _, hseed⟩ := dischargeOpen_policy_gamma sourceRun targetRun happly
  have hcleanT : CleanBase targetRun := by
    unfold CleanBase at hbase ⊢
    rw [hseed, hbase]
  apply (dischargeOpen_completion_justified sourceRun targetRun happly hw hw' hkept
    hclean hcomplete hfree p hp).2
  rw [blockedQueriesForRun_eq_nil_of_clean targetRun hcleanT [p]]
  simp

/-! ### Additive atomic batches

What the per-constructor results give for a composition of additive edits.
Every additive batch keeps the old AF arguments (`atomic_additive_checked_split`),
so `additive_no_gap_entry` composes.  A batch without `addInstance` keeps the
AF arguments exactly, so the `gap` row of `nonInstance_gap_fixed` composes.  A
batch without `addAttack` appends only sinks, so `addInstance_sink_status_monotone`
composes.  Nothing else does: a single `addAttack` already reaches every
transition between the three non-`gap` statuses, in both directions. -/

/-- An edit that adds no argument row. -/
def AtomicEdit.AddsNoInstance : AtomicEdit → Prop
  | .addLeaf .. => True
  | .addAttack _ => True
  | _ => False

/-- An edit that adds no raw attack. -/
def AtomicEdit.AddsNoAttack : AtomicEdit → Prop
  | .addLeaf .. => True
  | .addInstance .. => True
  | _ => False

private theorem AtomicEdit.additive_of_addsNoInstance {e : AtomicEdit}
    (h : e.AddsNoInstance) : e.Additive := by
  cases e <;> first | trivial | exact h.elim

private theorem AtomicEdit.additive_of_addsNoAttack {e : AtomicEdit}
    (h : e.AddsNoAttack) : e.Additive := by
  cases e <;> first | trivial | exact h.elim

private theorem applyBatchFrom_argsRaw_eq :
    ∀ (edits : List AtomicEdit) {σ τ : SourceState} {index : Nat},
      applyBatchFrom σ index edits = .ok τ → (∀ e ∈ edits, e.AddsNoInstance) →
      τ.argsRaw = σ.argsRaw := by
  intro edits
  induction edits with
  | nil =>
      intro σ τ index h _
      simp only [applyBatchFrom, Except.ok.injEq] at h
      rw [h]
  | cons e rest ih =>
      intro σ τ index h hno
      simp only [applyBatchFrom] at h
      cases hstep : e.applyRaw σ with
      | error reason => rw [hstep] at h; cases h
      | ok σ' =>
          rw [hstep] at h
          rw [ih h (fun e' he' => hno e' (by simp [he']))]
          have he := hno e (by simp)
          cases e with
          | addLeaf id a m =>
              simp only [AtomicEdit.applyRaw] at hstep
              split at hstep <;> cases hstep
              rfl
          | addAttack k =>
              simp only [AtomicEdit.applyRaw] at hstep
              split at hstep <;> cases hstep
              rfl
          | addInstance => exact he.elim
          | dischargeOpen => exact he.elim

private theorem applyBatchFrom_rawAtts_eq :
    ∀ (edits : List AtomicEdit) {σ τ : SourceState} {index : Nat},
      applyBatchFrom σ index edits = .ok τ → (∀ e ∈ edits, e.AddsNoAttack) →
      τ.rawAtts = σ.rawAtts := by
  intro edits
  induction edits with
  | nil =>
      intro σ τ index h _
      simp only [applyBatchFrom, Except.ok.injEq] at h
      rw [h]
  | cons e rest ih =>
      intro σ τ index h hno
      simp only [applyBatchFrom] at h
      cases hstep : e.applyRaw σ with
      | error reason => rw [hstep] at h; cases h
      | ok σ' =>
          rw [hstep] at h
          rw [ih h (fun e' he' => hno e' (by simp [he']))]
          have he := hno e (by simp)
          cases e with
          | addLeaf id a m =>
              simp only [AtomicEdit.applyRaw] at hstep
              split at hstep <;> cases hstep
              rfl
          | addInstance name w =>
              simp only [AtomicEdit.applyRaw] at hstep
              split at hstep <;> cases hstep
              rfl
          | addAttack => exact he.elim
          | dischargeOpen => exact he.elim

/-- The facts the atomic transition theorems share: the old AF arguments are
a prefix of the new ones, the policies agree, and the checker contexts agree
on every old AF argument. -/
private theorem atomic_additive_args {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState} {edits : List AtomicEdit}
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.atomic edits) = .ok τ)
    (hadd : ∀ e ∈ edits, e.Additive) :
    ∃ I, τ.argsRaw = σ.argsRaw ++ I ∧ (∀ x ∈ I, InstanceFresh σ x.1 x.2) ∧
      targetRun.checked.program.args = sourceRun.checked.program.args ++
        Check.completeArgs σ.policy.ruleLookup
          (Admission.buildGamma targetRun.admission.prune.checkedLeaves) reg
          ((I.filter targetRun.admission.prune.keep).map (·.2)) ∧
      targetRun.checked.policy = sourceRun.checked.policy ∧
      sourceRun.checked.policy = σ.policy ∧
      (∀ w ∈ sourceRun.checked.program.args, ∀ l ∈ Support.leaves w,
        Admission.buildGamma sourceRun.admission.prune.checkedLeaves l =
          Admission.buildGamma targetRun.admission.prune.checkedLeaves l) := by
  obtain ⟨I, hI, hIfresh, hargs, _⟩ :=
    atomic_additive_checked_split sourceRun targetRun happly hadd
  obtain ⟨_, _, _, _, _, _, _, hgammaOn⟩ :=
    atomic_additive_kept sourceRun targetRun happly hadd
  have hpolicy : τ.policy = σ.policy :=
    (applyBatchFrom_prefix edits (applyUpdate_atomic_target happly)).2.2.2.2.2.2.1
  have hsSound := Check.Unit.checkUnit_sound sourceRun.check_ok
  have htSound := Check.Unit.checkUnit_sound targetRun.check_ok
  have hsPolicy : sourceRun.checked.policy = σ.policy := hsSound.policy_eq
  have htPolicy : targetRun.checked.policy = τ.policy := htSound.policy_eq
  have hsArgs := hsSound.args_eq
  dsimp only at hsArgs
  refine ⟨I, hI, hIfresh, hargs, by rw [htPolicy, hsPolicy, hpolicy], hsPolicy, ?_⟩
  intro w hw
  rw [hsArgs] at hw
  exact hgammaOn w (Check.completeArgs_subset hw)

/-- **An additive batch never moves a claim into `gap`**, under every
extension semantics, whether or not its new leaves are admitted: the batch
analogue of `additive_no_gap_entry`. -/
theorem atomic_additive_no_gap_entry {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState} {edits : List AtomicEdit}
    (sem : Semantics.ExtensionSemantics)
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.atomic edits) = .ok τ)
    (hadd : ∀ e ∈ edits, e.Additive) (p : Atom)
    (hsource : (CoreTransition sem sourceRun.checked targetRun.checked p).1 ≠
      .observed Grounded.Status.gap) :
    (CoreTransition sem sourceRun.checked targetRun.checked p).2 ≠
      .observed Grounded.Status.gap := by
  obtain ⟨I, _, _, hargs, hpolicy, _, hgammaOn⟩ :=
    atomic_additive_args sourceRun targetRun happly hadd
  exact coreObs_not_gap_of_insert sem sourceRun.checked targetRun.checked
    sourceRun.checked.program.args (Check.completeArgs σ.policy.ruleLookup
      (Admission.buildGamma targetRun.admission.prune.checkedLeaves) reg
      ((I.filter targetRun.admission.prune.keep).map (·.2))) [] (by simp) (by rw [hargs]; simp) hpolicy
    (fun hw h => hasSupport_congr_gamma_on h (hgammaOn _ hw)) p hsource

/-- **A batch that adds no argument keeps every `gap` claim in `gap`**, under
every extension semantics: the batch analogue of the `addLeaf`/`addAttack`
cases of `nonInstance_gap_fixed`. -/
theorem atomic_instanceFree_gap_fixed {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState} {edits : List AtomicEdit}
    (sem : Semantics.ExtensionSemantics)
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.atomic edits) = .ok τ)
    (hno : ∀ e ∈ edits, e.AddsNoInstance) (p : Atom)
    (hsource : (CoreTransition sem sourceRun.checked targetRun.checked p).1 =
      .observed Grounded.Status.gap) :
    (CoreTransition sem sourceRun.checked targetRun.checked p).2 =
      .observed Grounded.Status.gap := by
  obtain ⟨I, hI, _, hargs, hpolicy, _, hgammaOn⟩ :=
    atomic_additive_args sourceRun targetRun happly
      (fun e he => AtomicEdit.additive_of_addsNoInstance (hno e he))
  have hraw := applyBatchFrom_argsRaw_eq edits (applyUpdate_atomic_target happly) hno
  have hInil : I = [] := by
    rw [hraw] at hI
    exact List.append_cancel_left (hI.symm.trans (List.append_nil _).symm)
  subst hInil
  exact coreObs_gap_of_insert sem sourceRun.checked targetRun.checked
    sourceRun.checked.program.args [] [] (by simp) (by rw [hargs]; simp [Check.completeArgs])
    hpolicy (fun hw h => hasSupport_congr_gamma_on h (fun l hl => (hgammaOn _ hw l hl).symm))
    p (by simp) hsource

/-- **A batch that adds no attack keeps the grounded guarantees of a fresh
instance**: its new arguments are fresh, so no old raw attack names them, and
the compiled attacks are unchanged.  A grounded `justified` claim stays
`justified`, and a grounded `contested` claim does not become `defeated` — the
batch analogue of `addInstance_sink_status_monotone`. -/
theorem atomic_attackFree_sink_status_monotone {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState} {edits : List AtomicEdit}
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.atomic edits) = .ok τ)
    (hno : ∀ e ∈ edits, e.AddsNoAttack) (p : Atom) :
    ((CoreTransition Semantics.groundedSem sourceRun.checked targetRun.checked p).1 =
        .observed Grounded.Status.justified →
      (CoreTransition Semantics.groundedSem sourceRun.checked targetRun.checked p).2 =
        .observed Grounded.Status.justified) ∧
    ((CoreTransition Semantics.groundedSem sourceRun.checked targetRun.checked p).1 =
        .observed Grounded.Status.contested →
      (CoreTransition Semantics.groundedSem sourceRun.checked targetRun.checked p).2 ≠
        .observed Grounded.Status.defeated) := by
  have hadd : ∀ e ∈ edits, e.Additive :=
    fun e he => AtomicEdit.additive_of_addsNoAttack (hno e he)
  obtain ⟨I, hI, hIfresh, hargs, hpolicy, _, hgammaOn⟩ :=
    atomic_additive_args sourceRun targetRun happly hadd
  obtain ⟨_, I', _, hI', _, _, hkept, _⟩ :=
    atomic_additive_kept sourceRun targetRun happly hadd
  have hII' : I' = I := by
    rw [hI] at hI'
    exact (List.append_cancel_left hI').symm
  subst hII'
  have hrawAtts := applyBatchFrom_rawAtts_eq edits (applyUpdate_atomic_target happly) hno
  have hres : targetRun.declared.resolved = sourceRun.declared.resolved := by
    have hext : RawAttack.resolveAttacks τ.argsRaw τ.rawAtts =
        .ok sourceRun.declared.resolved := by
      rw [hrawAtts, hI]
      exact RawAttack.resolveAttacks_mono_lookup σ.argsRaw (σ.argsRaw ++ I')
        (fun _ _ h => RawAttack.lookupArg_append_of_some σ.argsRaw I' h)
        sourceRun.declared.resolve_eq
    exact Except.ok.inj (targetRun.declared.resolve_eq.symm.trans hext)
  have hnewName : ∀ n ∈ σ.argsRaw.map (·.1),
      n ∉ (I'.filter targetRun.admission.prune.keep).map (·.1) := by
    intro n hn hnew
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hnew
    obtain ⟨r, hr, hrn⟩ := List.mem_map.mp hn
    exact (hIfresh x (List.mem_filter.mp hx).1).1 r hr hrn
  have hkA : targetRun.admission.prune.keptAttacks =
      sourceRun.admission.prune.keptAttacks := by
    rw [targetRun.keptAttacks_select, sourceRun.keptAttacks_select, hres, hrawAtts,
      hkept]
    apply RawAttack.selectAligned_congr_on
    intro ra hra
    have hends := RawAttack.resolveAttacks_endpoints_mem σ.argsRaw
      sourceRun.declared.resolve_eq ra hra
    simp only [List.map_append, List.mem_append]
    have h1 := hnewName _ hends.1
    have h2 := hnewName _ hends.2
    simp [h1, h2]
  have hsSound := Check.Unit.checkUnit_sound sourceRun.check_ok
  have htSound := Check.Unit.checkUnit_sound targetRun.check_ok
  have hsAtts := hsSound.atts_eq
  have htAtts := htSound.atts_eq
  dsimp only at hsAtts htAtts
  have hsSource : ∀ k ∈ sourceRun.admission.prune.keptAttacks,
      k.source ∈ sourceRun.admission.prune.keptArgs.map (·.2) := hsSound.raw_source
  have hsKeptRaw : ∀ r ∈ sourceRun.admission.prune.keptArgs, r ∈ σ.argsRaw := by
    intro r hr
    rw [sourceRun.prune_eq] at hr
    exact (List.mem_filter.mp hr).1
  have hatts : targetRun.checked.program.atts = sourceRun.checked.program.atts := by
    rw [htAtts, hsAtts, hkA, hargs]
    apply Check.liveAttacks_congr
    intro k hk
    have hnot : k.source ∉ Check.completeArgs σ.policy.ruleLookup
        (Admission.buildGamma targetRun.admission.prune.checkedLeaves) reg
        ((I'.filter targetRun.admission.prune.keep).map (·.2)) := by
      intro hmem
      obtain ⟨x, hx, hxs⟩ := List.mem_map.mp (Check.completeArgs_subset hmem)
      obtain ⟨r, hr, hrs⟩ := List.mem_map.mp (hsSource k hk)
      exact (hIfresh x (List.mem_filter.mp hx).1).2 r (hsKeptRaw r hr) (hrs.trans hxs.symm)
    simp [hnot]
  exact grounded_sink_monotone_of_insert sourceRun.checked targetRun.checked
    sourceRun.checked.program.args (Check.completeArgs σ.policy.ruleLookup
      (Admission.buildGamma targetRun.admission.prune.checkedLeaves) reg
      ((I'.filter targetRun.admission.prune.keep).map (·.2))) [] (by simp) (by rw [hargs]; simp) hpolicy
    (fun hw h => hasSupport_congr_gamma_on h (hgammaOn _ hw)) hatts p

/-! ### Justified completions in an accepted run -/

/-- **A retained, complete, unattacked row is justified.** In any accepted
run, a raw row the prune keeps whose term is complete under the run's checker
context and reached by no compiled attack justifies every claim equivalent to
its conclusion, and publicly so unless that claim is blocked.  This is the
target-side fact behind every completion: it does not depend on how the run's
source was reached. -/
theorem AcceptedRun.justified_of_unattacked_row {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) {row : String × SupportTerm} {C p : Atom}
    (hrow : row ∈ state.argsRaw) (hkeep : run.admission.prune.keep row = true)
    (hC : HasSupport canon state.policy.ruleLookup
      (Admission.buildGamma run.admission.prune.checkedLeaves) (certOkOf reg)
      row.2 C [])
    (hfree : Unattacked run.checked.program.atts row.2) (hp : equiv canon C p) :
    coreObs Semantics.groundedSem run.checked p = .observed .justified ∧
      (p ∉ blockedQueriesForRun run [p] → publicReport run p = .justified) := by
  have hsound := Check.Unit.checkUnit_sound run.check_ok
  have hargs := hsound.args_eq
  dsimp only at hargs
  have hpolicy : run.checked.policy = state.policy := hsound.policy_eq
  have hkept : row ∈ run.admission.prune.keptArgs := by
    have hK : run.admission.prune.keptArgs = state.argsRaw.filter run.admission.prune.keep := by
      rw [run.prune_eq]; rfl
    rw [hK]
    exact List.mem_filter.mpr ⟨hrow, hkeep⟩
  have hmem : row.2 ∈ run.checked.program.args := by
    rw [hargs, Check.mem_completeArgs_iff]
    exact ⟨List.mem_map.mpr ⟨row, hkept, rfl⟩, C, hC⟩
  have hC' : HasSupport canon run.checked.policy.ruleLookup
      (Admission.buildGamma run.admission.prune.checkedLeaves) (certOkOf reg)
      row.2 C [] := by
    rw [hpolicy]; exact hC
  exact ⟨coreObs_justified_of_unattacked run.checked hmem hC' hp hfree,
    publicReport_justified_of_unattacked run hmem hC' hp hfree⟩

/-- **An unattacked atomic completion is justified, publicly too.** After an
admitted additive batch from a clean source run, every argument row of the
final state — in particular each fresh instance the batch adds — whose term is
complete and reached by no compiled attack justifies every claim equivalent
to its conclusion, both in the grounded core and in the public report. -/
theorem atomic_completion_justified {canon : String → String}
    {reg : BackendRegistry canon} {σ τ : SourceState} {edits : List AtomicEdit}
    (sourceRun : AcceptedRun reg σ) (targetRun : AcceptedRun reg τ)
    (happly : applyUpdate reg σ (.atomic edits) = .ok τ)
    (hadd : ∀ e ∈ edits, e.AdmittedAdditive σ.table) (hbase : CleanBase sourceRun)
    {row : String × SupportTerm} {C p : Atom} (hrow : row ∈ τ.argsRaw)
    (hC : HasSupport canon σ.policy.ruleLookup
      (Admission.buildGamma targetRun.admission.prune.checkedLeaves) (certOkOf reg)
      row.2 C [])
    (hfree : Unattacked targetRun.checked.program.atts row.2) (hp : equiv canon C p) :
    coreObs Semantics.groundedSem targetRun.checked p = .observed .justified ∧
      publicReport targetRun p = .justified := by
  have hcleanT := atomic_additive_clean_target sourceRun targetRun happly hadd hbase
  have hpolicy : τ.policy = σ.policy :=
    (applyBatchFrom_prefix edits (applyUpdate_atomic_target happly)).2.2.2.2.2.2.1
  have hkeep : targetRun.admission.prune.keep row = true := by
    have hK : targetRun.admission.prune.keep row =
        !Groups.usesLeaf targetRun.admission.prune.removedSeed row.2 := by
      rw [targetRun.prune_eq]; rfl
    rw [hK, show targetRun.admission.prune.removedSeed = [] from hcleanT]
    cases huse : Groups.usesLeaf [] row.2 with
    | false => rfl
    | true =>
        obtain ⟨_, _, hl⟩ := (usesLeaf_true_iff _ _).mp huse
        cases hl
  have h := AcceptedRun.justified_of_unattacked_row targetRun hrow hkeep
    (by rw [hpolicy]; exact hC) hfree hp
  refine ⟨h.1, h.2 ?_⟩
  rw [blockedQueriesForRun_eq_nil_of_clean targetRun hcleanT [p]]
  simp

end Lara.Update
