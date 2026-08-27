/-
M1 counterexample: the frozen two-field compiler invariant is necessary but not
sufficient for realizability under a fixed policy.  With no contrary or
exception declarations, typed attacks are impossible and every compiled
framework is edgeless, while the invariant's conflict-completeness field is
vacuous.  A one-node self-edge framework therefore satisfies the record but is
not in the compilation image, even up to the all-Nat structured isomorphism.
-/

import Lara.Realizability
import Lara.Examples
import Lara.Examples.PolicyAcceptance

namespace Lara.Examples.Realizability

open Lara.Support

/-- A defeat policy with neither contrary nor exception declarations. -/
def emptyDefeat : Attack.DefeatPolicy :=
  { contraries := [], exceptions := [] }

/-- The smallest carrier whose sole edge cannot be compiled under
`emptyDefeat`. -/
def oneSelfEdge (p : Atom) : Invariants.StructuredAF :=
  { nodes := [p]
  , attack := fun i j => decide (i = 0 ∧ j = 0) }

/-- Proposition-level inversion: an empty defeat policy licenses no typed
attack.  This proof does not appeal to the Boolean attack checker. -/
theorem noAttack_of_emptyDefeat :
    ¬ Attack.HasAttack canon Pi Gamma CertOk emptyDefeat k := by
  intro hattack
  cases hattack with
  | rebut _ _ _ _ hcontrary =>
      simp [Attack.ContraryMatch, emptyDefeat] at hcontrary
  | undercut _ _ _ _ hexception _ _ =>
      simp [emptyDefeat] at hexception
  | undermine _ _ _ hcontrary =>
      simp [Attack.ContraryMatch, emptyDefeat] at hcontrary

/-- Every compiled edge is false under `emptyDefeat`, including indices outside
the retained argument range. -/
theorem compiled_no_edges_of_emptyDefeat
    (unit : Unit.CheckedUnit canon Gamma CertOk)
    (hpolicy : unit.policy.defeat = emptyDefeat) :
    (Invariants.compileUnit unit).attack i j = false := by
  change Compile.edgeB unit.program i j = false
  apply Bool.eq_false_iff.mpr
  intro hedge
  cases hsource : unit.program.args[i]? with
  | none =>
      simp [Compile.edgeB, hsource] at hedge
  | some source =>
      cases htarget : unit.program.args[j]? with
      | none =>
          simp [Compile.edgeB, hsource, htarget] at hedge
      | some target =>
          have hEdge := (Compile.edgeB_iff hsource htarget).mp hedge
          obtain ⟨_, _, k, _, htyped, _, _⟩ :=
            (Compile.edge_iff unit.program source target).mp hEdge
          rw [hpolicy] at htyped
          exact noAttack_of_emptyDefeat htyped

/-- The frozen record accepts the self-edge carrier because conflict
completeness is vacuous when the defeat policy has no contraries. -/
theorem oneSelfEdge_invariant (p : Atom) :
    Invariants.CompilerInvariant canon emptyDefeat (oneSelfEdge p) := by
  constructor
  · intro i j hedge
    have hij : i = 0 ∧ j = 0 := of_decide_eq_true hedge
    rcases hij with ⟨rfl, rfl⟩
    simp [oneSelfEdge, Invariants.StructuredAF.size]
  · intro i j ci cj hi hj hcontrary
    simp [Attack.ContraryMatch, emptyDefeat] at hcontrary

/-- Despite satisfying the unchanged M0 record, the self-edge carrier is not
realizable under any fixed signature and registry paired with `emptyDefeat`.
The contradiction uses the total label and attack equations of the structured
isomorphism. -/
theorem oneSelfEdge_not_realizable
    (sigma : Sigma.Sigma) (policy : Policy.Policy)
    (reg : BackendRegistry canon)
    (hpolicy : policy.defeat = emptyDefeat) :
    ¬ Realizability.Realizable canon sigma policy reg (oneSelfEdge p) := by
  rintro ⟨R⟩
  have hacceptedPolicy : R.accepted.policy.defeat = emptyDefeat := by
    rw [R.policy_eq, hpolicy]
  have hedgeless :
      (Invariants.compileUnit R.accepted).attack 0 0 = false :=
    compiled_no_edges_of_emptyDefeat R.accepted hacceptedPolicy
  let e := R.compiled_iso.nodeEquiv
  have hpreLabel := R.compiled_iso.labels (e.symm 0)
  have hpreToZero : e (e.symm 0) = 0 := e.right_inv 0
  rw [hpreToZero] at hpreLabel
  have hpreSome :
      (Invariants.compileUnit R.accepted).nodes[e.symm 0]? = some p := by
    simpa [oneSelfEdge] using hpreLabel
  have hpreLt := Support.lt_of_getElem?_some hpreSome
  have hzeroLt : 0 < (Invariants.compileUnit R.accepted).nodes.length := by
    omega
  obtain ⟨c0, hc0⟩ := Support.getElem?_some_of_lt
    (Invariants.compileUnit R.accepted).nodes 0 hzeroLt
  have hlabel0 := R.compiled_iso.labels 0
  rw [hc0] at hlabel0
  have heLt : e 0 < (oneSelfEdge p).nodes.length :=
    Support.lt_of_getElem?_some hlabel0.symm
  have heZero : e 0 = 0 := by
    simpa [oneSelfEdge] using heLt
  have hattacks := R.compiled_iso.attacks 0 0
  rw [hedgeless, heZero] at hattacks
  simp [oneSelfEdge] at hattacks

/-- A concrete empty input under the same fixed empty-defeat policy. -/
def emptyRawUnit : Lara.Unit :=
  { sigma := Lara.Examples.sigmaEx
  , policy := Lara.Examples.PolicyAcceptance.emptyPolicy
  , args := []
  , atts := [] }

/-- The executable checker result for the concrete empty context. -/
def emptyUnitCheck :=
  Check.Unit.checkUnit Lara.Examples.ΓEx Lara.Examples.registryEx []
    emptyRawUnit

/-- The accepted checker witness extracted from the concrete successful
result. -/
def acceptedEmptyUnit :
    Lara.Unit.CheckedUnit id Lara.Examples.ΓEx
      (certOkOf Lara.Examples.registryEx) :=
  emptyUnitCheck.toOption.get (by decide)

/-- The fixed empty-defeat context is executable and accepted, so the
counterexample does not rely on an inconsistent checker context. -/
theorem emptyUnitCheck_ok :
    emptyUnitCheck = .ok acceptedEmptyUnit := by
  cases h : emptyUnitCheck with
  | error error =>
      have hs : emptyUnitCheck.isOk = true := by decide
      rw [h] at hs
      contradiction
  | ok accepted =>
      have hoption : emptyUnitCheck.toOption = some accepted :=
        congrArg Except.toOption h
      have haccepted : acceptedEmptyUnit = accepted := by
        unfold acceptedEmptyUnit
        apply Option.get_of_eq_some
        exact hoption
      rw [haccepted]

/-! ### Nonempty realizability integration fixture -/

/-- Swap positions zero and one while fixing every position outside the
two-node range. -/
def swapFirstTwo : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => n + 2

theorem swapFirstTwo_involutive (i : Nat) :
    swapFirstTwo (swapFirstTwo i) = i := by
  cases i with
  | zero => rfl
  | succ i =>
      cases i with
      | zero => rfl
      | succ i => rfl

/-- The two-node swap as an all-`Nat` equivalence. -/
def swapFirstTwoEquiv : Lara.Realizability.Equiv Nat Nat where
  toFun := swapFirstTwo
  invFun := swapFirstTwo
  left_inv := swapFirstTwo_involutive
  right_inv := swapFirstTwo_involutive

/-- The accepted nonempty fixture, reindexed by the two-node swap. -/
def nonemptySwappedAF : Invariants.StructuredAF :=
  { nodes := [Lara.Examples.pA, Lara.Examples.pB]
  , attack := fun i j =>
      (Invariants.compileUnit Lara.Examples.acceptedUnitEx).attack
        (swapFirstTwo i) (swapFirstTwo j) }

/-- Compilation of the accepted fixture is isomorphic to the swapped carrier
through a non-identity permutation that fixes all positions from two onward. -/
def nonemptySwapIso :
    Lara.Realizability.StructuredAFIso
      (Invariants.compileUnit Lara.Examples.acceptedUnitEx)
      nonemptySwappedAF where
  nodeEquiv := swapFirstTwoEquiv
  labels := by
    intro i
    have hnodes :
        (Invariants.compileUnit Lara.Examples.acceptedUnitEx).nodes =
          [Lara.Examples.pB, Lara.Examples.pA] :=
      Lara.Examples.checked_unit_retained_alignment.2.2.2
    rw [hnodes]
    cases i with
    | zero => rfl
    | succ i =>
        cases i with
        | zero => rfl
        | succ i => rfl
  attacks := by
    intro i j
    change _ =
      (Invariants.compileUnit Lara.Examples.acceptedUnitEx).attack
        (swapFirstTwo (swapFirstTwo i)) (swapFirstTwo (swapFirstTwo j))
    rw [swapFirstTwo_involutive, swapFirstTwo_involutive]

theorem nonempty_ground_covers :
    Lara.Realizability.GroundCoversUsedLeaves
      Lara.Examples.ΓEx Lara.Examples.groundEx
      Lara.Examples.rawUnitEx.args := by
  simp [Lara.Realizability.GroundCoversUsedLeaves,
    Lara.Examples.rawUnitEx, Support.leaves, Lara.Examples.ΓEx,
    Lara.Examples.groundEx, Lara.Examples.l1, Lara.Examples.l2]

/-- A successful nonempty checker run, explicit used-leaf coverage, and a
non-identity all-`Nat` isomorphism assembled into one realization witness. -/
def nonemptySwappedRealization :
    Lara.Realizability.Realization id Lara.Examples.sigmaEx
      Lara.Examples.unitPolicyEx Lara.Examples.registryEx
      nonemptySwappedAF where
  Gamma := Lara.Examples.ΓEx
  ground := Lara.Examples.groundEx
  raw := Lara.Examples.rawUnitEx
  accepted := Lara.Examples.acceptedUnitEx
  checked := Lara.Examples.rawUnitCheck_ok
  sigma_eq := (Check.Unit.checkUnit_sound
    Lara.Examples.rawUnitCheck_ok).1
  policy_eq := (Check.Unit.checkUnit_sound
    Lara.Examples.rawUnitCheck_ok).2.2.2.2.2.1
  ground_covers := nonempty_ground_covers
  compiled_iso := nonemptySwapIso

theorem nonempty_swapped_realizable :
    Lara.Realizability.Realizable id Lara.Examples.sigmaEx
      Lara.Examples.unitPolicyEx Lara.Examples.registryEx
      nonemptySwappedAF :=
  ⟨nonemptySwappedRealization⟩

theorem nonempty_accepted_nodes :
    Lara.Examples.acceptedUnitEx.nodes ≠ [] := by
  intro hempty
  have hconclusions :=
    Lara.Examples.checked_unit_retained_alignment.2.2.2
  rw [hempty] at hconclusions
  contradiction

def nonemptyRetainedNode :=
  Lara.Examples.acceptedUnitEx.nodes.head nonempty_accepted_nodes

theorem nonemptyRetainedNode_mem :
    nonemptyRetainedNode ∈ Lara.Examples.acceptedUnitEx.nodes :=
  List.head_mem nonempty_accepted_nodes

/-- The realization boundary proves sortedness for an actual retained node of
the nonempty checker result. -/
theorem nonempty_swapped_node_wellSorted :
    Sigma.WellSorted Lara.Examples.sigmaEx
      nonemptyRetainedNode.conclusion :=
  nonemptySwappedRealization.node_conclusion_wellSorted
    nonemptyRetainedNode_mem
end Lara.Examples.Realizability
