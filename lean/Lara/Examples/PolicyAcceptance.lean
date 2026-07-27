/-
Closed fixtures for the accepted policy boundary. They pin the declaration
ordering of the duplicate and R12 diagnostics as well as the first-match
lookup behavior used after identifier uniqueness has been established.
-/

import Lara.Policy

namespace Lara.Examples.PolicyAcceptance

open Lara.Support
open Lara.Policy

def emptyPolicy : Policy :=
  { rules := []
    defeat := ⟨[], []⟩ }

def defeasibleFly : Rule :=
  { Policy.Regression.strictFly with mode := .defeasible }

def defeasibleOnlyPolicy : Policy :=
  { rules := [⟨⟨"defeasibleFly"⟩, defeasibleFly⟩]
    defeat := ⟨[(Policy.Regression.canFlyTweety,
      Policy.Regression.penguinTweety)], []⟩ }

def firstStrictPolicy : Policy :=
  { rules := [⟨⟨"strictFly"⟩, Policy.Regression.strictFly⟩]
    defeat := ⟨[(Policy.Regression.canFlyTweety,
      Policy.Regression.penguinTweety)], []⟩ }

def multipleViolationPolicy : Policy :=
  { rules := [⟨⟨"first"⟩, Policy.Regression.strictFly⟩,
      ⟨⟨"second"⟩, Policy.Regression.strictFly⟩]
    defeat := ⟨[(Policy.Regression.canFlyTweety,
      Policy.Regression.penguinTweety)], []⟩ }

def multiplePairViolationPolicy : Policy :=
  { rules := [⟨⟨"strict"⟩, Policy.Regression.strictFly⟩]
    defeat :=
      ⟨[(Policy.Regression.canFlyTweety,
          Policy.Regression.canFlyTweety),
        (Policy.Regression.canFlyTweety,
          Policy.Regression.penguinTweety)], []⟩ }

def duplicateRuleIdPolicy : Policy :=
  { rules := [⟨⟨"duplicate"⟩, Policy.Regression.strictFly⟩,
      ⟨⟨"duplicate"⟩, defeasibleFly⟩,
      ⟨⟨"other"⟩, Policy.Regression.strictFly⟩]
    defeat := ⟨[], []⟩ }

def validUniquePolicy : Policy :=
  { rules := [⟨⟨"valid"⟩, Policy.Regression.strictFly⟩]
    defeat := ⟨[], []⟩ }

theorem empty_policy_accepted :
    firstViolation? id emptyPolicy = none ∧
      firstDuplicateRuleId? emptyPolicy.rules = none := by decide

theorem defeasible_only_accepted :
    firstViolation? id defeasibleOnlyPolicy = none := by decide

theorem first_strict_violation_located :
    firstViolation? id firstStrictPolicy =
      some ⟨⟨"strictFly"⟩, Policy.Regression.canFlyX,
        (Policy.Regression.canFlyTweety, Policy.Regression.penguinTweety)⟩ := by
  decide

theorem multiple_violations_report_first_rule :
    firstViolation? id multipleViolationPolicy =
      some ⟨⟨"first"⟩, Policy.Regression.canFlyX,
        (Policy.Regression.canFlyTweety, Policy.Regression.penguinTweety)⟩ := by
  decide

theorem multiple_violations_report_first_contrary_pair :
    firstViolation? id multiplePairViolationPolicy =
      some ⟨⟨"strict"⟩, Policy.Regression.canFlyX,
        (Policy.Regression.canFlyTweety,
          Policy.Regression.canFlyTweety)⟩ := by
  decide

theorem duplicate_rule_identifier_has_first_two_indices :
    firstDuplicateRuleId? duplicateRuleIdPolicy.rules =
      some ⟨⟨"duplicate"⟩, 0, 1⟩ := by decide

theorem valid_unique_policy_accepted :
    firstViolation? id validUniquePolicy = none ∧
      firstDuplicateRuleId? validUniquePolicy.rules = none := by decide

theorem known_rule_lookup :
    validUniquePolicy.ruleLookup ⟨"valid"⟩ = some Policy.Regression.strictFly := by
  rfl

/-- Raw lookup is deliberately first-match even before the duplicate-id
acceptance check rejects this policy. -/
theorem duplicate_rule_lookup_returns_first_declaration :
    duplicateRuleIdPolicy.ruleLookup ⟨"duplicate"⟩ =
      some Policy.Regression.strictFly := by
  rfl

theorem unknown_rule_lookup_none :
    validUniquePolicy.ruleLookup ⟨"unknown"⟩ = none := by decide

end Lara.Examples.PolicyAcceptance
