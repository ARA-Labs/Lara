/-
Executable orchestration of the public unit-acceptance boundary.

`checkUnit` is the canonical executable constructor of `Unit.CheckedUnit`.
Its public six-stage order is: duplicate rule identifiers, policy R12,
duplicate arguments, support, typed attacks, then missing conflict. The first
two stages run before program checking; the remaining four are the detailed
program checker's fixed order. Successful construction carries that checker's
exact retained-node cache, so it neither rechecks support terms nor asks
callers to provide alignment proofs. Manual proof-level construction of
`CheckedUnit` still requires every invariant.
-/

import Lara.Unit
import Lara.Check.Program

namespace Lara.Check.Unit

open Lara Lara.Support Lara.Attack

/-- Closed diagnostics for whole-unit acceptance. -/
inductive UnitError where
  | duplicateRule : Policy.DuplicateRule → UnitError
  | policyViolation : Policy.Violation → UnitError
  | program : ProgramError → UnitError
deriving DecidableEq

/-- Only policy R12 and wrapped frozen checker failures have rejection
classes.  Structural duplicate-rule errors preserve their typed payload
without inventing a frozen rejection class. -/
def UnitError.rejectClass : UnitError → Option RejectClass
  | .duplicateRule _ => none
  | .policyViolation _ => some .R12
  | .program error => error.rejectClass

/-- The canonical executable constructor for proof-bearing accepted units. -/
def checkUnit {canon : String → String}
    (Gamma : LeafId → Option Atom) (reg : BackendRegistry canon)
    (unit : Lara.Unit) :
    Except UnitError (Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)) :=
  match hduplicate : Policy.firstDuplicateRuleId? unit.policy.rules with
  | some duplicate => .error (.duplicateRule duplicate)
  | none =>
      match hviolation : Policy.firstViolation? canon unit.policy with
      | some violation => .error (.policyViolation violation)
      | none =>
          match checkProgramDetailed unit.policy.ruleLookup Gamma reg
              unit.policy.defeat unit.args unit.atts with
          | .error error => .error (.program error)
          | .ok accepted =>
              .ok
                { policy := unit.policy
                , ruleIds_nodup :=
                    (Policy.firstDuplicateRuleId?_none_iff
                      unit.policy.rules).mp hduplicate
                , policy_wf :=
                    (Policy.firstViolation_none_iff).mp hviolation
                , program := accepted.program
                , attack_complete := accepted.attack_complete
                , nodes := accepted.nodes
                , nodes_terms := accepted.nodes_terms }

/-- Successful executable acceptance exposes every field of `CheckedUnit` by
its public name, together with exact correspondence to the raw declaration
lists supplied to the checker. -/
theorem checkUnit_sound {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {unit : Lara.Unit}
    {accepted : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (h : checkUnit Gamma reg unit = .ok accepted) :
    accepted.policy = unit.policy ∧
    (accepted.policy.rules.map (·.id)).Nodup ∧
    Policy.WellFormed canon accepted.policy ∧
    accepted.program.args = unit.args ∧
    accepted.program.atts = unit.atts ∧
    Compile.AttackComplete canon accepted.policy.ruleLookup Gamma
      (certOkOf reg) accepted.policy.defeat
      accepted.program.args accepted.program.atts ∧
    accepted.nodes.map (·.term) = accepted.program.args := by
  unfold checkUnit at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · rename_i programAcceptance hprogram
        have haccepted :
            accepted =
              { policy := unit.policy
              , ruleIds_nodup :=
                  (Policy.firstDuplicateRuleId?_none_iff
                    unit.policy.rules).mp (by assumption)
              , policy_wf :=
                  (Policy.firstViolation_none_iff).mp (by assumption)
              , program := programAcceptance.program
              , attack_complete := programAcceptance.attack_complete
              , nodes := programAcceptance.nodes
              , nodes_terms := programAcceptance.nodes_terms } :=
          Except.ok.inj h |>.symm
        subst accepted
        refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact
            (Policy.firstDuplicateRuleId?_none_iff unit.policy.rules).mp
              (by assumption)
        · exact (Policy.firstViolation_none_iff).mp (by assumption)
        · exact programAcceptance.arguments_eq
        · exact programAcceptance.attacks_eq
        · exact programAcceptance.attack_complete
        · exact programAcceptance.nodes_terms

/-- Exact completeness of the unit checker.  The premises are precisely the
raw policy and detailed-program obligations checked in the public fixed
order. -/
theorem checkUnit_complete {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {unit : Lara.Unit}
    (hruleIds : (unit.policy.rules.map (·.id)).Nodup)
    (hpolicy : Policy.WellFormed canon unit.policy)
    (hargs : unit.args.Nodup)
    (hsupport : ∀ w ∈ unit.args, ∃ C,
      HasSupport canon unit.policy.ruleLookup Gamma (certOkOf reg) w C [])
    (htyped : ∀ k ∈ unit.atts,
      HasAttack canon unit.policy.ruleLookup Gamma (certOkOf reg)
        unit.policy.defeat k)
    (hsource : ∀ k ∈ unit.atts, k.source ∈ unit.args)
    (htarget : ∀ k ∈ unit.atts, k.target ∈ unit.args)
    (hattackComplete :
      Compile.AttackComplete canon unit.policy.ruleLookup Gamma
        (certOkOf reg) unit.policy.defeat unit.args unit.atts) :
    ∃ accepted, checkUnit Gamma reg unit = .ok accepted := by
  have hduplicate :
      Policy.firstDuplicateRuleId? unit.policy.rules = none :=
    (Policy.firstDuplicateRuleId?_none_iff unit.policy.rules).mpr hruleIds
  have hviolation : Policy.firstViolation? canon unit.policy = none :=
    (Policy.firstViolation_none_iff).mpr hpolicy
  obtain ⟨programAcceptance, hprogram⟩ :=
    checkProgramDetailed_complete hargs hsupport htyped hsource htarget
      hattackComplete
  unfold checkUnit
  split
  · rename_i duplicate hfound
    rw [hduplicate] at hfound
    contradiction
  · split
    · rename_i violation hfound
      rw [hviolation] at hfound
      contradiction
    · split
      · rename_i error hfound
        rw [hprogram] at hfound
        contradiction
      · rename_i found hfound
        have hfound_eq : found = programAcceptance :=
          Except.ok.inj (hfound.symm.trans hprogram)
        subst found
        exact ⟨_, rfl⟩

end Lara.Check.Unit
