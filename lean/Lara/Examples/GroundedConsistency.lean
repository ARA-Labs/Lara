/-
Focused executable fixtures for generic grounded conflict-freedom, exact
complete-claim projection, accepted-unit result 7, and the self-conflict
end-to-end boundary.
-/

import Lara.Examples

namespace Lara.Examples.GroundedConsistency

open Lara.Support Lara.Compile Lara.Check Lara.Check.Unit

/-! ### Generic grounded conflict-freedom and status witnesses -/

def oneWayAF : Grounded.AF where
  args := [0, 1]
  attack := fun i j => decide (i = 0 ∧ j = 1)

theorem one_way_grounded :
    Grounded.grounded oneWayAF = [0] := by decide

theorem one_way_grounded_conflict_free :
    Grounded.ConflictFree oneWayAF (Grounded.grounded oneWayAF) :=
  Grounded.grounded_conflictFree

def cycleAF : Grounded.AF where
  args := [0, 1]
  attack := fun i j =>
    decide ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))

theorem cycle_grounded_empty :
    Grounded.grounded cycleAF = [] := by decide

theorem cycle_allowed_and_conflict_free :
    cycleAF.attack 0 1 = true ∧
      Grounded.ConflictFree cycleAF (Grounded.grounded cycleAF) := by
  exact ⟨by decide, Grounded.grounded_conflictFree⟩

theorem empty_support_not_justified :
    Grounded.statusC oneWayAF ⟨[], [9]⟩ ≠
      Grounded.Status.justified := by decide

theorem all_out_support_not_justified :
    Grounded.statusC oneWayAF ⟨[1], []⟩ ≠
      Grounded.Status.justified := by decide

/-- Representative default-heartbeat regression for the proof-oriented
reference evaluator. The twelve-node chain exercises repeated carrier,
attacker, and defender scans; cached adjacency remains deferred to M3. -/
def referenceStressAF : Grounded.AF where
  args := List.range 12
  attack := fun i j => decide (i + 1 = j)

theorem grounded_default_heartbeat_regression :
    Grounded.grounded referenceStressAF = [0, 2, 4, 6, 8, 10] := by
  decide

/-! ### Exact computed complete-claim support -/

def numericRegistry : BackendRegistry numericCanon := fun _ => none

def numericΓ : LeafId → Option Atom := fun leaf =>
  if leaf = l1 then some numericNoisy
  else if leaf = l2 then some pB
  else if leaf = l3 then some numericCanonical
  else none

/-- The numeric fixtures' own signature: one unary numeric predicate plus the
nullary atoms of the shared example vocabulary. -/
def numericSigma : Lara.Sigma.Sigma :=
  { sorts := []
  , cons := []
  , preds :=
      [ ⟨⟨"p"⟩, []⟩
      , ⟨⟨"q"⟩, []⟩
      , ⟨⟨"s"⟩, []⟩
      , ⟨⟨"n"⟩, [.num]⟩ ] }

def numericGround : List Atom := [numericNoisy, pB, numericCanonical]

def numericUnit : Lara.Unit :=
  { sigma := numericSigma
  , policy := { rules := [], defeat := ⟨[], []⟩ }
  , args := [.leaf l1, .leaf l2, .leaf l3]
  , atts := [] }

def numericUnitCheck :=
  checkUnit numericΓ numericRegistry numericGround numericUnit

theorem numeric_unit_accepted :
    numericUnitCheck.isOk = true := by decide

def acceptedNumericUnit :
    Lara.Unit.CheckedUnit numericCanon numericΓ
      (certOkOf numericRegistry) :=
  numericUnitCheck.toOption.get (by decide)

theorem claim_support_zero :
    Lara.Consistency.claimSupportFor acceptedNumericUnit pC = [] := by decide

theorem claim_support_one_with_decoy :
    Lara.Consistency.claimSupportFor acceptedNumericUnit pB = [1] := by decide

theorem claim_support_multiple_canonical_equivalent :
    Lara.Consistency.claimSupportFor acceptedNumericUnit numericCanonical =
      [0, 2] := by decide

theorem claim_support_noisy_equivalent_same_order :
    Lara.Consistency.claimSupportFor acceptedNumericUnit numericNoisy =
      [0, 2] := by decide

theorem complete_claim_projection_holes_empty :
    (Lara.Consistency.completeClaimFor
      acceptedNumericUnit numericCanonical).holes = [] := rfl

/-! ### Self-conflict end to end -/

def selfConflictPolicy : Policy.Policy :=
  { rules := []
  , defeat := ⟨[(apA, apA)], []⟩ }

def missingSelfEdgeUnit : Lara.Unit :=
  { sigma := sigmaEx
  , policy := selfConflictPolicy
  , args := [.leaf l1]
  , atts := [] }

theorem missing_self_edge_rejected :
    checkUnit ΓEx registryEx groundEx missingSelfEdgeUnit =
      .error (.program
        (.missingConflict ⟨0, 0, pA, pA⟩)) := by rfl

def selfAttack : Attack.Attack :=
  .undermine (.leaf l1) (.leaf l1) []

def coveredSelfEdgeUnit : Lara.Unit :=
  { sigma := sigmaEx
  , policy := selfConflictPolicy
  , args := [.leaf l1]
  , atts := [selfAttack] }

def coveredSelfEdgeCheck :=
  checkUnit ΓEx registryEx groundEx coveredSelfEdgeUnit

theorem typed_self_edge_accepted :
    coveredSelfEdgeCheck.isOk = true := by decide

def acceptedSelfEdgeUnit :
    Lara.Unit.CheckedUnit id ΓEx (certOkOf registryEx) :=
  coveredSelfEdgeCheck.toOption.get (by decide)

theorem covered_self_edge_check_ok :
    coveredSelfEdgeCheck = .ok acceptedSelfEdgeUnit := by
  cases h : coveredSelfEdgeCheck with
  | error error =>
      have hs := typed_self_edge_accepted
      rw [h] at hs
      contradiction
  | ok accepted =>
      have hoption : coveredSelfEdgeCheck.toOption = some accepted :=
        congrArg Except.toOption h
      have haccepted : acceptedSelfEdgeUnit = accepted := by
        unfold acceptedSelfEdgeUnit
        apply Option.get_of_eq_some
        exact hoption
      rw [haccepted]

theorem self_attacking_node_not_grounded :
    0 ∉ Grounded.grounded
      (Compile.checkedAF acceptedSelfEdgeUnit.program) := by decide

theorem self_claim_support_includes_node :
    Lara.Consistency.claimSupportFor acceptedSelfEdgeUnit pA = [0] := by decide

theorem computed_self_claim_not_justified :
    Grounded.statusC (Compile.checkedAF acceptedSelfEdgeUnit.program)
        (Lara.Consistency.completeClaimFor acceptedSelfEdgeUnit pA) ≠
      Grounded.Status.justified := by decide

theorem computed_self_claim_result7 :
    ¬ (Grounded.statusC (Compile.checkedAF acceptedSelfEdgeUnit.program)
          (Lara.Consistency.completeClaimFor acceptedSelfEdgeUnit pA) =
            Grounded.Status.justified ∧
       Grounded.statusC (Compile.checkedAF acceptedSelfEdgeUnit.program)
          (Lara.Consistency.completeClaimFor acceptedSelfEdgeUnit pA) =
            Grounded.Status.justified) := by
  apply Lara.Consistency.contrary_claims_not_both_justified
  have hpolicy :=
    (checkUnit_sound covered_self_edge_check_ok).2.2.2.2.2.1
  change acceptedSelfEdgeUnit.policy = selfConflictPolicy at hpolicy
  rw [hpolicy]
  exact ⟨(apA, apA), by simp [selfConflictPolicy], [], pA, pA,
    by decide, by decide, equiv_refl id pA, equiv_refl id pA⟩

end Lara.Examples.GroundedConsistency
