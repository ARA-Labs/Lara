/-
Closed completion fixtures for the atomic batch (D14, issue #11) and in-place
discharge (D13, issue #14) updates.

* `sequential_completion_fails`: a fresh complete alternative that needs an
  outgoing attack.  `addInstance` alone rejects for the uncovered conflict,
  `addAttack` first rejects because its source is not declared, and the
  two-edit atomic batch is accepted.
* `partial_batch_rejected`, `batch_edits_checked_in_order`: a batch that omits
  the needed attack is rejected with `missing-conflict` and the source is kept;
  an attack listed before the instance it names fails its syntactic check
  against the intermediate state.
* `atomic_keeps_old_hole`: an additive batch keeps the old hole reported.
* `discharge_hole_becomes_node`: discharging the only open mandatory question
  of a lone hole turns it into an AF node and moves its claim from `gap` to
  `justified`.
* `discharge_needs_attack`: an in-place discharge that makes a hole complete
  and conflicting is rejected alone, accepted in a batch with its attack, and
  (unlike a fresh instance) also reachable attack-first, one update at a time.
* `discharge_optional_enters_gap`, `discharge_outgoing_defeats`: the two
  counterexamples that restrict the discharge transition theorems.  Answering
  an optional question of a complete argument with a hole turns the AF node
  into a hole and moves its claim from `justified` to `gap`; completing a hole
  that an existing raw attack already names as its source makes that attack
  fire and moves the attacked claim from `justified` to `refuted`.
* `atomic_quarantined_leaf_pruned`: an additive batch whose new leaf is
  quarantined prunes the new argument that uses it, keeps the old hole and the
  old AF argument, and reports neither the pruned term as a hole nor as an AF
  argument.

`completionWitnessReport` prints the executable outcomes these theorems pin;
`lean/UpdateMatrices.lean` appends it to the committed update golden.
-/

import Lara.Update.Transitions
import Lara.Examples.Update

namespace Lara.Examples.UpdateCompletion

open Lara Lara.Support Lara.Attack Lara.Check

/-! ### Shared carriers -/

private def metas0 : List Admission.LeafMeta :=
  [ { id := l1, kind := .observed, provenance := .user }
  , { id := l2, kind := .observed, provenance := .user } ]

/-- A source over the shared example signature, policy and two leaves
(`l1 : p`, `l2 : q`, with `q` contrary to `p`). -/
def stateWith (args : List (String × SupportTerm))
    (atts : List RawAttack.RawAttack) : Lara.Update.SourceState :=
  { sigma := sigmaEx, policy := unitPolicyEx, table := [], metas := metas0
  , leaves := [(l1, pA), (l2, pB)], argsRaw := args, rawAtts := atts
  , groups := [], ground := groundEx }

/-- The attack the completion needs: the new `q`-argument undermines the
`p`-leaf argument. -/
def coverAttack : RawAttack.RawAttack := .undermine "b" "a" []

/-- One complete `p` argument. -/
def baseState : Lara.Update.SourceState := stateWith [("a", .leaf l1)] []

/-- The completed program: the base, a complete `q` argument, and its cover. -/
def completedState : Lara.Update.SourceState :=
  stateWith [("a", .leaf l1), ("b", .leaf l2)] [coverAttack]

/-- An empty batch re-runs the pipeline on the unchanged source, so its success
witnesses acceptance. -/
private theorem accepted_of_empty_batch {σ : Lara.Update.SourceState}
    (h : Lara.Update.applyUpdate registryEx σ (.atomic []) = .ok σ) :
    Lara.Update.Accepted registryEx σ :=
  (Lara.Update.applyUpdate_atomic_ok_iff.mp h).2

/-! ### The sequential completion counterexample -/

/-- **Sequential completion can fail where the atomic batch succeeds.** The
accepted source declares one complete `p` argument.  The completed program —
plus a complete `q` argument `b` and the attack covering its conflict with `a`
— is accepted.  Neither single-update order reaches it: `addInstance` first is
rejected for the uncovered `q`-against-`p` conflict, and `addAttack` first is
rejected because its source `b` is not declared yet.  The two-edit atomic batch
is accepted and yields exactly the completed program. -/
theorem sequential_completion_fails :
    Lara.Update.Accepted registryEx baseState ∧
    Lara.Update.Accepted registryEx completedState ∧
    Lara.Update.applyUpdate registryEx baseState (.addInstance "b" (.leaf l2)) =
      .error (.unitRejected (.program (.missingConflict ⟨1, 0, pB, pA⟩))) ∧
    Lara.Update.applyUpdate registryEx baseState (.addAttack coverAttack) =
      .error (.endpointNotDeclared coverAttack) ∧
    Lara.Update.applyUpdate registryEx baseState
        (.atomic [.addInstance "b" (.leaf l2), .addAttack coverAttack]) =
      .ok completedState := by
  refine ⟨accepted_of_empty_batch rfl, accepted_of_empty_batch rfl, rfl, rfl, rfl⟩

/-- The general completeness theorem applies to the counterexample: its
hypotheses hold, so the batch it builds is the accepted one above. -/
theorem completion_theorem_applies :
    Lara.Update.applyUpdate registryEx baseState
        (.atomic (Lara.Update.completionEdits [] [("b", .leaf l2)] [coverAttack])) =
      .ok (Lara.Update.completionState baseState [] [("b", .leaf l2)] [coverAttack]) :=
  Lara.Update.atomic_completion_complete baseState [] [("b", .leaf l2)]
    [coverAttack] (by simp) (by simp)
    (by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      simp [Lara.Update.InstanceFresh, baseState, stateWith, l1, l2])
    (by simp) (by simp)
    (by
      intro k hk
      simp only [List.mem_singleton] at hk
      subst hk
      simp [Lara.Update.EndpointDeclared, coverAttack, RawAttack.RawAttack.endpoints,
        baseState, stateWith])
    (accepted_of_empty_batch rfl)

/-! ### Partial batches and edit order -/

/-- **A batch that omits a required attack is rejected, and the source is
kept.** -/
theorem partial_batch_rejected :
    Lara.Update.applyUpdate registryEx baseState
        (.atomic [.addInstance "b" (.leaf l2)]) =
      .error (.unitRejected (.program (.missingConflict ⟨1, 0, pB, pA⟩))) ∧
    Lara.Update.applyOrKeep registryEx baseState
        (.atomic [.addInstance "b" (.leaf l2)]) = baseState :=
  ⟨rfl, Lara.Update.applyOrKeep_of_error rfl⟩

/-- **Each edit is checked against the state the earlier edits produced.** An
attack listed before the instance it names is rejected as the batch's first
edit, before admission runs. -/
theorem batch_edits_checked_in_order :
    Lara.Update.applyUpdate registryEx baseState
        (.atomic [.addAttack coverAttack, .addInstance "b" (.leaf l2)]) =
      .error (.batchEdit 0 (.endpointNotDeclared coverAttack)) :=
  rfl

/-! ### Old holes persist across an additive batch -/

/-- One complete `p` argument and the hole `tMix` (open mandatory `q1`). -/
def holeState : Lara.Update.SourceState :=
  stateWith [("a", .leaf l1), ("h", tMix)] []

def holeCompletedState : Lara.Update.SourceState :=
  stateWith [("a", .leaf l1), ("h", tMix), ("b", .leaf l2)] [coverAttack]

private def holeBatch : List Lara.Update.AtomicEdit :=
  [.addInstance "b" (.leaf l2), .addAttack coverAttack]

/-- The checked unit an accepted state's pipeline produces. -/
private def checkedHoles (σ : Lara.Update.SourceState) : List SupportTerm :=
  match RawAttack.resolveAttacks σ.argsRaw σ.rawAtts with
  | .error _ => []
  | .ok resolved =>
      let prune := Admission.buildPrune id σ.table σ.metas σ.leaves σ.argsRaw
        σ.rawAtts σ.groups resolved
      Check.holeArgs σ.policy.ruleLookup (Admission.buildGamma prune.checkedLeaves)
        registryEx (prune.keptArgs.map (·.2))

private def checkedArgs (σ : Lara.Update.SourceState) : List SupportTerm :=
  match RawAttack.resolveAttacks σ.argsRaw σ.rawAtts with
  | .error _ => []
  | .ok resolved =>
      let prune := Admission.buildPrune id σ.table σ.metas σ.leaves σ.argsRaw
        σ.rawAtts σ.groups resolved
      Check.completeArgs σ.policy.ruleLookup
        (Admission.buildGamma prune.checkedLeaves) registryEx
        (prune.keptArgs.map (·.2))

/-- Read the reported holes of an exact accepted run. -/
private theorem run_holes {σ : Lara.Update.SourceState}
    (run : Lara.Update.AcceptedRun registryEx σ) :
    run.checked.program.holes = checkedHoles σ := by
  have hs := Check.Unit.checkUnit_sound run.check_ok
  rw [hs.holes_eq]
  unfold checkedHoles
  rw [run.declared.resolve_eq]
  simp only
  rw [run.prune_eq]

/-- Read the complete arguments of an exact accepted run. -/
private theorem run_args {σ : Lara.Update.SourceState}
    (run : Lara.Update.AcceptedRun registryEx σ) :
    run.checked.program.args = checkedArgs σ := by
  have hs := Check.Unit.checkUnit_sound run.check_ok
  rw [hs.args_eq]
  unfold checkedArgs
  rw [run.declared.resolve_eq]
  simp only
  rw [run.prune_eq]

/-- **An additive batch keeps the old hole.** Completing the claim `q` beside
an unrelated hole keeps that hole reported, with the same term, before the
new argument, as `atomic_additive_checked_prefix` guarantees for every
additive batch. -/
theorem atomic_keeps_old_hole :
    Lara.Update.applyUpdate registryEx holeState (.atomic holeBatch) =
      .ok holeCompletedState ∧
    checkedHoles holeState = [tMix] ∧
    checkedHoles holeCompletedState = [tMix] ∧
    ∀ (sourceRun : Lara.Update.AcceptedRun registryEx holeState)
      (targetRun : Lara.Update.AcceptedRun registryEx holeCompletedState),
      sourceRun.checked.program.holes <+: targetRun.checked.program.holes := by
  have happly :
      Lara.Update.applyUpdate registryEx holeState (.atomic holeBatch) =
        .ok holeCompletedState := rfl
  refine ⟨happly, by decide, by decide, ?_⟩
  intro sourceRun targetRun
  exact (Lara.Update.atomic_additive_checked_prefix sourceRun targetRun happly
    (by
      intro e he
      simp only [holeBatch, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl <;> trivial)).2

/-! ### In-place discharge turns a hole into an AF node -/

/-- A lone hole for `p`: `tMix` leaves mandatory `q1` open. -/
def gapState : Lara.Update.SourceState := stateWith [("h", tMix)] []

/-- `tMix` with `q1` discharged by the `q`-leaf `l2`; optional `q2` stays
open. -/
def tMixDischarged : SupportTerm :=
  .inst rMixId [] [] [(q1, .leaf l2)] [q2] .none

def gapDischargedState : Lara.Update.SourceState :=
  stateWith [("h", tMixDischarged)] []

/-- **A hole discharged to completion becomes an AF node.** The argument keeps
its name and declaration index; the hole report goes from `[tMix]` to empty,
the complete arguments from empty to the discharged term, and `p` moves from
`gap` to `justified`.  `dischargeOpen_hole_becomes_node` predicts the node
and the exit from `gap` for every extension semantics. -/
theorem discharge_hole_becomes_node :
    Lara.Update.applyUpdate registryEx gapState (.dischargeOpen "h" [] q1 (.leaf l2)) =
      .ok gapDischargedState ∧
    Lara.Update.Discharge.dischargeAt q1 (.leaf l2) [] tMix = some tMixDischarged ∧
    checkedHoles gapState = [tMix] ∧ checkedArgs gapState = [] ∧
    checkedHoles gapDischargedState = [] ∧
    checkedArgs gapDischargedState = [tMixDischarged] ∧
    (∀ (sourceRun : Lara.Update.AcceptedRun registryEx gapState)
      (targetRun : Lara.Update.AcceptedRun registryEx gapDischargedState)
      (sem : Semantics.ExtensionSemantics),
      Lara.Update.coreObs sem sourceRun.checked pA = .observed .gap ∧
      Lara.Update.coreObs sem targetRun.checked pA ≠ .observed .gap) := by
  have happly :
      Lara.Update.applyUpdate registryEx gapState
          (.dischargeOpen "h" [] q1 (.leaf l2)) = .ok gapDischargedState := rfl
  refine ⟨happly, rfl, by decide, by decide, by decide, by decide, ?_⟩
  intro sourceRun targetRun sem
  have hres : sourceRun.declared.resolved = [] :=
    Except.ok.inj (sourceRun.declared.resolve_eq.symm.trans rfl)
  have hprune : sourceRun.admission.prune =
      Admission.buildPrune id gapState.table gapState.metas gapState.leaves
        gapState.argsRaw gapState.rawAtts gapState.groups [] := by
    rw [sourceRun.prune_eq, hres]
  have hinfer :
      Check.inferSupport gapState.policy.ruleLookup
        (Admission.buildGamma
          (Admission.buildPrune id gapState.table gapState.metas gapState.leaves
            gapState.argsRaw gapState.rawAtts gapState.groups []).checkedLeaves)
        registryEx .root tMixDischarged = .ok ⟨pA, []⟩ := rfl
  have hcomplete :
      HasSupport id gapState.policy.ruleLookup
        (Admission.buildGamma sourceRun.admission.prune.checkedLeaves)
        (certOkOf registryEx) tMixDischarged pA [] := by
    rw [hprune]
    exact Check.inferSupport_sound hinfer
  have hnode := Lara.Update.dischargeOpen_hole_becomes_node sourceRun targetRun
    happly (w := tMix) rfl rfl (by rw [hprune]; decide) (by rw [hprune]; decide)
    hcomplete
  refine ⟨?_, hnode.2.2.2 sem pA (equiv_refl id pA)⟩
  unfold Lara.Update.coreObs
  apply (Semantics.observe_gap_iff _ _ _).mpr
  have hargs := run_args sourceRun
  have hnil : checkedArgs gapState = [] := by decide
  rw [hnil] at hargs
  unfold Consistency.completeClaimFor Consistency.claimSupportFor
  simp only
  have hnodes : sourceRun.checked.nodes = [] := by
    have h := sourceRun.checked.nodes_terms
    rw [hargs] at h
    exact List.map_eq_nil_iff.mp h
  rw [hnodes]
  rfl

/-- A run of a state with no raw attacks compiles no attack. -/
private theorem atts_nil_of_no_raw {σ : Lara.Update.SourceState}
    (run : Lara.Update.AcceptedRun registryEx σ) (hraw : σ.rawAtts = []) :
    run.checked.program.atts = [] := by
  have hs := Check.Unit.checkUnit_sound run.check_ok
  rw [hs.atts_eq]
  have hres : run.declared.resolved = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [← RawAttack.resolveAttacks_length _ run.declared.resolve_eq, hraw]
    rfl
  have hkept : run.admission.prune.keptAttacks = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro k hk
    rw [run.prune_eq] at hk
    have hmem := RawAttack.mem_of_mem_selectAligned hk
    rw [hres] at hmem
    cases hmem
  change Check.liveAttacks run.checked.program.args run.admission.prune.keptAttacks = []
  rw [hkept]
  rfl

private theorem unattacked_nil (w : SupportTerm) : Lara.Update.Unattacked [] w :=
  fun _ hk => by cases hk

/-- **The completed lone hole is publicly justified.** The completion above is
unattacked and its source is clean, so `dischargeOpen_completion_public_justified`
applies: `p` is publicly `justified` in every target run. -/
theorem discharge_completion_public_justified :
    ∀ (_ : Lara.Update.AcceptedRun registryEx gapState)
      (targetRun : Lara.Update.AcceptedRun registryEx gapDischargedState),
      Lara.Update.publicReport targetRun pA = .justified := by
  intro sourceRun targetRun
  have hres : sourceRun.declared.resolved = [] :=
    Except.ok.inj (sourceRun.declared.resolve_eq.symm.trans rfl)
  have hprune : sourceRun.admission.prune =
      Admission.buildPrune id gapState.table gapState.metas gapState.leaves
        gapState.argsRaw gapState.rawAtts gapState.groups [] := by
    rw [sourceRun.prune_eq, hres]
  have hinfer :
      Check.inferSupport gapState.policy.ruleLookup
        (Admission.buildGamma
          (Admission.buildPrune id gapState.table gapState.metas gapState.leaves
            gapState.argsRaw gapState.rawAtts gapState.groups []).checkedLeaves)
        registryEx .root tMixDischarged = .ok ⟨pA, []⟩ := rfl
  have hcomplete :
      HasSupport id gapState.policy.ruleLookup
        (Admission.buildGamma sourceRun.admission.prune.checkedLeaves)
        (certOkOf registryEx) tMixDischarged pA [] := by
    rw [hprune]
    exact Check.inferSupport_sound hinfer
  have hfree : Lara.Update.Unattacked targetRun.checked.program.atts tMixDischarged := by
    rw [atts_nil_of_no_raw targetRun rfl]
    exact unattacked_nil _
  have happly :
      Lara.Update.applyUpdate registryEx gapState
          (.dischargeOpen "h" [] q1 (.leaf l2)) = .ok gapDischargedState := rfl
  exact Lara.Update.dischargeOpen_completion_public_justified sourceRun targetRun happly
    (w := tMix) rfl rfl (by rw [hprune]; decide) (by rw [hprune]; decide) hcomplete hfree
    (by rw [Lara.Update.CleanBase, hprune]; rfl) pA (equiv_refl id pA)

/-- The lone hole beside a fresh complete `p` argument. -/
def gapBatchState : Lara.Update.SourceState :=
  stateWith [("h", tMix), ("b", .leaf l1)] []

/-- **An unattacked atomic completion is publicly justified.** A batch adds a
complete `p` argument beside the lone hole; the hole stays, `p` leaves `gap`,
and because the batch is admitted, the source clean and the new argument
unattacked, `atomic_completion_justified` makes `p` publicly `justified` in
every target run. -/
theorem atomic_completion_public_justified :
    Lara.Update.applyUpdate registryEx gapState (.atomic [.addInstance "b" (.leaf l1)]) =
      .ok gapBatchState ∧
    checkedHoles gapBatchState = [tMix] ∧
    ∀ (_ : Lara.Update.AcceptedRun registryEx gapState)
      (targetRun : Lara.Update.AcceptedRun registryEx gapBatchState),
      Lara.Update.publicReport targetRun pA = .justified := by
  have happly :
      Lara.Update.applyUpdate registryEx gapState (.atomic [.addInstance "b" (.leaf l1)]) =
        .ok gapBatchState := rfl
  refine ⟨happly, by decide, ?_⟩
  intro sourceRun targetRun
  have hres : targetRun.declared.resolved = [] :=
    Except.ok.inj (targetRun.declared.resolve_eq.symm.trans rfl)
  have hprune : targetRun.admission.prune =
      Admission.buildPrune id gapBatchState.table gapBatchState.metas
        gapBatchState.leaves gapBatchState.argsRaw gapBatchState.rawAtts
        gapBatchState.groups [] := by
    rw [targetRun.prune_eq, hres]
  have hinfer :
      Check.inferSupport gapState.policy.ruleLookup
        (Admission.buildGamma
          (Admission.buildPrune id gapBatchState.table gapBatchState.metas
            gapBatchState.leaves gapBatchState.argsRaw gapBatchState.rawAtts
            gapBatchState.groups []).checkedLeaves)
        registryEx .root (.leaf l1) = .ok ⟨pA, []⟩ := rfl
  have hC :
      HasSupport id gapState.policy.ruleLookup
        (Admission.buildGamma targetRun.admission.prune.checkedLeaves)
        (certOkOf registryEx) (.leaf l1) pA [] := by
    rw [hprune]
    exact Check.inferSupport_sound hinfer
  have hfree : Lara.Update.Unattacked targetRun.checked.program.atts (.leaf l1) := by
    rw [atts_nil_of_no_raw targetRun rfl]
    exact unattacked_nil _
  have hsclean : Lara.Update.CleanBase sourceRun := by
    unfold Lara.Update.CleanBase
    rw [sourceRun.prune_eq]
    rfl
  exact (Lara.Update.atomic_completion_justified sourceRun targetRun happly
    (by
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      trivial)
    hsclean (row := ("b", .leaf l1)) (by decide) hC hfree (equiv_refl id pA)).2

/-! ### In-place discharge that needs an attack -/

/-- A complete `p` argument and the hole `tUse`, a `q`-wrapper of `tMix`. -/
def useState : Lara.Update.SourceState :=
  stateWith [("a", .leaf l1), ("h", tUse)] []

/-- The attack the discharged wrapper needs against the `p` argument. -/
def useCover : RawAttack.RawAttack := .undermine "h" "a" []

def tUseDischarged : SupportTerm :=
  .inst rWrapId [] [tMixDischarged] [] [] .none

def useDischargedState : Lara.Update.SourceState :=
  stateWith [("a", .leaf l1), ("h", tUseDischarged)] [useCover]

/-- **In-place discharge with a required attack.** Discharging `q1` inside the
wrapper makes it a complete `q` argument that conflicts with `a`.  Alone the
discharge is rejected with `missing-conflict`; in a batch with its covering
attack it is accepted.  Because the discharged argument keeps its declared
name, the attack-first single-update order also succeeds — the sequential
failure is specific to fresh ids. -/
theorem discharge_needs_attack :
    Lara.Update.applyUpdate registryEx useState
        (.dischargeOpen "h" [.prem 0] q1 (.leaf l2)) =
      .error (.unitRejected (.program (.missingConflict ⟨1, 0, pB, pA⟩))) ∧
    Lara.Update.applyUpdate registryEx useState
        (.atomic [.dischargeOpen "h" [.prem 0] q1 (.leaf l2), .addAttack useCover]) =
      .ok useDischargedState ∧
    Lara.Update.applyUpdate registryEx useState (.addAttack useCover) =
      .ok (stateWith [("a", .leaf l1), ("h", tUse)] [useCover]) ∧
    Lara.Update.applyUpdate registryEx
        (stateWith [("a", .leaf l1), ("h", tUse)] [useCover])
        (.dischargeOpen "h" [.prem 0] q1 (.leaf l2)) =
      .ok useDischargedState ∧
    checkedHoles useState = [tUse] ∧ checkedHoles useDischargedState = [] :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩

/-! ### Counterexamples to unrestricted discharge transitions -/

/-- The complete `tMixDischarged` with its optional `q2` answered by the hole
`tUse`, which leaves `q1` open inside the discharge. -/
def tMixBoth : SupportTerm :=
  .inst rMixId [] [] [(q1, .leaf l2), (q2, tUse)] [] .none

def optionalDischargedState : Lara.Update.SourceState := stateWith [("h", tMixBoth)] []

private def gapDischargedRun : Lara.Examples.Update.AcceptedRun gapDischargedState :=
  Lara.Examples.Update.fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

private def optionalDischargedRun :
    Lara.Examples.Update.AcceptedRun optionalDischargedState :=
  Lara.Examples.Update.fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

/-- **An optional discharge can move a claim into `gap`.** The site
precondition only asks that the question be open, so it holds for the optional
`q2` of the complete argument `tMixDischarged`.  Answering it with the hole
`tUse` is accepted, but the rewritten term inherits `tUse`'s open mandatory
`q1`: the AF node becomes a hole and `p` moves from `justified` to `gap`.  This
refutes an unrestricted no-gap-entry theorem for `dischargeOpen`; the
restricted one requires the discharged argument to be a retained hole that
the discharge completes (`dischargeOpen_completion_no_gap_entry`). -/
theorem discharge_optional_enters_gap :
    Lara.Update.applyUpdate registryEx gapDischargedState
        (.dischargeOpen "h" [] q2 tUse) = .ok optionalDischargedState ∧
    checkedArgs gapDischargedState = [tMixDischarged] ∧
    checkedHoles gapDischargedState = [] ∧
    checkedArgs optionalDischargedState = [] ∧
    checkedHoles optionalDischargedState = [tMixBoth] ∧
    Lara.Examples.Update.SuccessfulCoreCell Semantics.groundedSem
      gapDischargedState optionalDischargedState (.dischargeOpen "h" [] q2 tUse)
      pA .justified .gap :=
  ⟨rfl, by decide, by decide, by decide, by decide,
    ⟨gapDischargedRun, optionalDischargedRun, rfl, by decide⟩⟩

/-- The wrapper hole `tUse` beside a complete `p` argument, with the attack its
completion will need already declared. -/
def useAttackedState : Lara.Update.SourceState :=
  stateWith [("a", .leaf l1), ("h", tUse)] [useCover]

private def useAttackedRun : Lara.Examples.Update.AcceptedRun useAttackedState :=
  Lara.Examples.Update.fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

private def useDischargedRun : Lara.Examples.Update.AcceptedRun useDischargedState :=
  Lara.Examples.Update.fixtureOf _ (by rfl) (by decide) (by rfl) (by decide)

/-- **Completing a hole can defeat an old claim.** The raw attack `h -> a` is
declared while `h` is a hole, so it compiles to no edge and `p` is
`justified`.  Discharging `q1` completes `h` in place: every premise of
`dischargeOpen_hole_becomes_node` holds, the attack now fires, and `p` moves
from `justified` to `refuted`.  A fresh `addInstance` cannot do this, since no
old raw attack can name a fresh id; this is why
`dischargeOpen_completion_sink_status_monotone` requires that no raw attack
name the discharged argument. -/
theorem discharge_outgoing_defeats :
    Lara.Update.applyUpdate registryEx useAttackedState
        (.dischargeOpen "h" [.prem 0] q1 (.leaf l2)) = .ok useDischargedState ∧
    checkedHoles useAttackedState = [tUse] ∧
    checkedArgs useAttackedState = [.leaf l1] ∧
    checkedArgs useDischargedState = [.leaf l1, tUseDischarged] ∧
    Lara.Examples.Update.SuccessfulCoreCell Semantics.groundedSem
      useAttackedState useDischargedState (.dischargeOpen "h" [.prem 0] q1 (.leaf l2))
      pA .justified .defeated :=
  ⟨rfl, by decide, by decide, by decide,
    ⟨useAttackedRun, useDischargedRun, rfl, by decide⟩⟩

/-! ### Quarantined new leaves in an additive batch -/

/-- An admission table that quarantines attested user leaves. -/
def quarantineRow : Admission.AdmissionRow :=
  { key := (.attested, .user), decision := .quarantine }

/-- `holeState` under the quarantining table. -/
def quarantineHoleState : Lara.Update.SourceState :=
  { holeState with table := [quarantineRow] }

/-- Metadata the table quarantines. -/
def quarantinedMeta : Admission.LeafMeta :=
  { id := l3, kind := .attested, provenance := .user }

/-- Add a quarantined leaf and an argument that uses it. -/
def quarantineBatch : List Lara.Update.AtomicEdit :=
  [.addLeaf l3 pC quarantinedMeta, .addInstance "c" (.leaf l3)]

def quarantineBatchState : Lara.Update.SourceState :=
  { quarantineHoleState with
    metas := metas0 ++ [quarantinedMeta]
    leaves := [(l1, pA), (l2, pB), (l3, pC)]
    argsRaw := [("a", .leaf l1), ("h", tMix), ("c", .leaf l3)] }

/-- **A quarantined new leaf prunes only the new argument.** The batch is
additive but not admitted, so it is outside `atomic_completion_justified`'s
clean case.  It is accepted; the new argument `c` uses the quarantined leaf and
is pruned, so it is neither an AF argument nor a reported hole, while the old
AF argument and the old hole `h` keep their places, as
`atomic_additive_checked_prefix` and `AcceptedRun.pruned_not_reported`
guarantee for every run. -/
theorem atomic_quarantined_leaf_pruned :
    Lara.Update.applyUpdate registryEx quarantineHoleState (.atomic quarantineBatch) =
      .ok quarantineBatchState ∧
    checkedArgs quarantineHoleState = [.leaf l1] ∧
    checkedHoles quarantineHoleState = [tMix] ∧
    checkedArgs quarantineBatchState = [.leaf l1] ∧
    checkedHoles quarantineBatchState = [tMix] ∧
    ∀ (sourceRun : Lara.Update.AcceptedRun registryEx quarantineHoleState)
      (targetRun : Lara.Update.AcceptedRun registryEx quarantineBatchState),
      sourceRun.checked.program.args <+: targetRun.checked.program.args ∧
      sourceRun.checked.program.holes <+: targetRun.checked.program.holes ∧
      .leaf l3 ∉ targetRun.checked.program.args ∧
      .leaf l3 ∉ targetRun.checked.program.holes := by
  have happly :
      Lara.Update.applyUpdate registryEx quarantineHoleState (.atomic quarantineBatch) =
        .ok quarantineBatchState := rfl
  refine ⟨happly, by decide, by decide, by decide, by decide, ?_⟩
  intro sourceRun targetRun
  have hprefix := Lara.Update.atomic_additive_checked_prefix sourceRun targetRun happly
    (by
      intro e he
      simp only [quarantineBatch, List.mem_cons, List.mem_nil_iff, or_false] at he
      rcases he with rfl | rfl <;> trivial)
  have hdrop : targetRun.admission.prune.keep ("c", .leaf l3) = false := by
    rw [targetRun.prune_eq]
    rfl
  have hpruned := targetRun.pruned_not_reported hdrop
  exact ⟨hprefix.1, hprefix.2, hpruned.1, hpruned.2⟩

/-! ### Emitted witness report -/

private def outcome :
    Except Lara.Update.UpdateRejection Lara.Update.SourceState → String
  | .ok _ => "accepted"
  | .error (.unitRejected (.program (.missingConflict _))) =>
      "rejected missing-conflict"
  | .error (.endpointNotDeclared _) => "rejected endpoint-not-declared"
  | .error (.batchEdit i (.endpointNotDeclared _)) =>
      s!"rejected at edit {i}: endpoint-not-declared"
  | .error _ => "rejected"

private def statusText : Grounded.Status → String
  | .justified => "justified"
  | .defeated => "refuted"
  | .contested => "both"
  | .gap => "gap"

private def claimStatus (σ : Lara.Update.SourceState) (p : Atom) : String :=
  match Lara.Update.applyUpdate registryEx σ (.atomic []) with
  | .error _ => "rejected"
  | .ok _ =>
      match RawAttack.resolveAttacks σ.argsRaw σ.rawAtts with
      | .error _ => "rejected"
      | .ok resolved =>
          let prune := Admission.buildPrune id σ.table σ.metas σ.leaves
            σ.argsRaw σ.rawAtts σ.groups resolved
          match Check.Unit.checkUnit (Admission.buildGamma prune.checkedLeaves)
              registryEx σ.ground
              { sigma := σ.sigma, policy := σ.policy
              , args := prune.keptArgs.map (·.2), atts := prune.keptAttacks } with
          | .error _ => "rejected"
          | .ok checked =>
              statusText (Grounded.statusC (Compile.checkedAF checked.program)
                (Consistency.completeClaimFor checked p))

private def row (label result witness : String) : String :=
  s!"{label} | {result} | {witness}"

/-- Deterministic report of the completion witnesses, computed by running the
same `applyUpdate` calls the theorems above pin. -/
def completionWitnessReport : String :=
  String.intercalate "\n"
    [ "completion witnesses (atomic batches and in-place discharge)"
    , row "addInstance b alone"
        (outcome (Lara.Update.applyUpdate registryEx baseState
          (.addInstance "b" (.leaf l2))))
        "sequential_completion_fails"
    , row "addAttack b->a alone"
        (outcome (Lara.Update.applyUpdate registryEx baseState
          (.addAttack coverAttack)))
        "sequential_completion_fails"
    , row "atomic [addInstance b, addAttack b->a]"
        (outcome (Lara.Update.applyUpdate registryEx baseState
          (.atomic [.addInstance "b" (.leaf l2), .addAttack coverAttack])))
        "sequential_completion_fails"
    , row "atomic [addInstance b]"
        (outcome (Lara.Update.applyUpdate registryEx baseState
          (.atomic [.addInstance "b" (.leaf l2)])) ++ "; source kept")
        "partial_batch_rejected"
    , row "atomic [addAttack b->a, addInstance b]"
        (outcome (Lara.Update.applyUpdate registryEx baseState
          (.atomic [.addAttack coverAttack, .addInstance "b" (.leaf l2)])))
        "batch_edits_checked_in_order"
    , row "atomic beside hole h"
        (outcome (Lara.Update.applyUpdate registryEx holeState (.atomic holeBatch)) ++
          s!"; holes {(checkedHoles holeState).length} -> {(checkedHoles holeCompletedState).length}, h kept")
        "atomic_keeps_old_hole"
    , row "dischargeOpen h eps q1"
        (outcome (Lara.Update.applyUpdate registryEx gapState
          (.dischargeOpen "h" [] q1 (.leaf l2))) ++
          s!"; holes {(checkedHoles gapState).length} -> {(checkedHoles gapDischargedState).length}; p {claimStatus gapState pA} -> {claimStatus gapDischargedState pA}")
        "discharge_hole_becomes_node"
    , row "dischargeOpen h 0 q1 alone"
        (outcome (Lara.Update.applyUpdate registryEx useState
          (.dischargeOpen "h" [.prem 0] q1 (.leaf l2))))
        "discharge_needs_attack"
    , row "atomic [dischargeOpen h 0 q1, addAttack h->a]"
        (outcome (Lara.Update.applyUpdate registryEx useState
          (.atomic [.dischargeOpen "h" [.prem 0] q1 (.leaf l2), .addAttack useCover])) ++
          s!"; holes {(checkedHoles useState).length} -> {(checkedHoles useDischargedState).length}; q {claimStatus useState pB} -> {claimStatus useDischargedState pB}")
        "discharge_needs_attack"
    , row "atomic [addInstance b] beside lone hole h"
        (outcome (Lara.Update.applyUpdate registryEx gapState
          (.atomic [.addInstance "b" (.leaf l1)])) ++
          s!"; holes {(checkedHoles gapState).length} -> {(checkedHoles gapBatchState).length}; p {claimStatus gapState pA} -> {claimStatus gapBatchState pA}")
        "atomic_completion_public_justified"
    , row "dischargeOpen h eps q2 by hole tUse"
        (outcome (Lara.Update.applyUpdate registryEx gapDischargedState
          (.dischargeOpen "h" [] q2 tUse)) ++
          s!"; holes {(checkedHoles gapDischargedState).length} -> {(checkedHoles optionalDischargedState).length}; p {claimStatus gapDischargedState pA} -> {claimStatus optionalDischargedState pA}")
        "discharge_optional_enters_gap"
    , row "dischargeOpen h 0 q1 after addAttack h->a"
        (outcome (Lara.Update.applyUpdate registryEx useAttackedState
          (.dischargeOpen "h" [.prem 0] q1 (.leaf l2))) ++
          s!"; holes {(checkedHoles useAttackedState).length} -> {(checkedHoles useDischargedState).length}; p {claimStatus useAttackedState pA} -> {claimStatus useDischargedState pA}")
        "discharge_outgoing_defeats"
    , row "atomic [addLeaf l3 quarantined, addInstance c] beside hole h"
        (outcome (Lara.Update.applyUpdate registryEx quarantineHoleState
          (.atomic quarantineBatch)) ++
          s!"; args {(checkedArgs quarantineHoleState).length} -> {(checkedArgs quarantineBatchState).length}; holes {(checkedHoles quarantineHoleState).length} -> {(checkedHoles quarantineBatchState).length}, c pruned")
        "atomic_quarantined_leaf_pruned" ]

end Lara.Examples.UpdateCompletion
