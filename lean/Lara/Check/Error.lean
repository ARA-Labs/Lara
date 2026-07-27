/-
Closed symbolic diagnostics shared by the executable support and attack
checkers.  Rendering human prose belongs at the decoder/diagnostics boundary;
the kernel-facing payloads retain only typed context.
-/

import Lara.Attack

namespace Lara.Check

open Lara Lara.Support

inductive RejectClass where
  | R1 | R3 | R4 | R5 | R6 | R7 | R10 | R11 | R12 | R13
deriving DecidableEq

inductive CheckLoc where
  | root
  | premise : CheckLoc → Nat → CheckLoc
  | question : CheckLoc → QuestionId → CheckLoc
deriving DecidableEq

inductive ReferenceReason where
  | missingLeaf : LeafId → ReferenceReason
  | missingRule : RuleId → ReferenceReason
  | undeclaredAttackSource : SupportTerm → ReferenceReason
  | undeclaredAttackTarget : SupportTerm → ReferenceReason
deriving DecidableEq

inductive SubstitutionReason where
  | duplicateKeys : List VarId → SubstitutionReason
  | domainMismatch : List VarId → List VarId → SubstitutionReason
  | premiseInstantiation : List APat → SubstitutionReason
  | conclusionInstantiation : APat → SubstitutionReason
deriving DecidableEq

inductive PremiseReason where
  | count : Nat → Nat → PremiseReason
  | mismatch : Atom → Atom → PremiseReason
deriving DecidableEq

inductive QuestionReason where
  | duplicateDeclarations : List QuestionId → QuestionReason
  | duplicateDischarges : List QuestionId → QuestionReason
  | duplicateHoles : List QuestionId → QuestionReason
  | uncovered : List QuestionId → List QuestionId → List QuestionId →
      QuestionReason
  | overlap : List QuestionId → List QuestionId → QuestionReason
  | undeclaredDischarge : List QuestionId → List QuestionId → QuestionReason
  | undeclaredHole : List QuestionId → List QuestionId → QuestionReason
deriving DecidableEq

inductive DischargeReason where
  | answerInstantiation : QuestionId → APat → DischargeReason
  | conclusionMismatch : QuestionId → Atom → Atom → DischargeReason
deriving DecidableEq

inductive AssuranceReason where
  | questionsPresent : List QuestionId → List QuestionId → AssuranceReason
  | wrongMode : Mode → Assurance → AssuranceReason
  | trustedDisallowed : AssuranceReason
  | certifierUnallowlisted : BackendId → Digest → AssuranceReason
deriving DecidableEq

inductive BackendReason where
  | backendMissing : BackendId → BackendReason
  | digestMissing : BackendId → Digest → BackendReason
  | replayRejected : BackendId → Digest → CertRef → BackendReason
deriving DecidableEq

inductive AttackKind where
  | rebut
  | undercut
  | undermine
deriving DecidableEq

inductive AttackOccurrenceKind where
  | rule
  | leaf
deriving DecidableEq

inductive AttackPositionReason where
  | undefinedPosition
  | wrongOccurrenceKind :
      (expected actual : AttackOccurrenceKind) → AttackPositionReason
deriving DecidableEq

/- These constructors cover the target-side failures in the frozen Task 4
matrix.  A missing declaration is kept distinct from a declaration whose
pattern cannot instantiate or whose instantiated atom does not match. -/
inductive AttackRelationReason where
  | missingTargetRule : RuleId → AttackRelationReason
  | targetConclusionInstantiation :
      RuleId → APat → AttackRelationReason
  | missingTargetLeaf : LeafId → AttackRelationReason
  | strictTarget : RuleId → AttackRelationReason
  | missingContrary : Atom → Atom → AttackRelationReason
  | missingException : RuleId → AttackRelationReason
  | exceptionInstantiation : RuleId → APat → AttackRelationReason
  | exceptionMismatch :
      RuleId → Atom → Atom → AttackRelationReason
deriving DecidableEq

inductive CheckError where
  | R1 : CheckLoc → ReferenceReason → CheckError
  | R3 : CheckLoc → SubstitutionReason → CheckError
  | R4 : CheckLoc → PremiseReason → CheckError
  | R5 : CheckLoc → QuestionReason → CheckError
  | R6 : CheckLoc → DischargeReason → CheckError
  | R7 : CheckLoc → AssuranceReason → CheckError
  | R10 : CheckLoc → Lara.Attack.Pos → AttackKind →
      AttackPositionReason → CheckError
  | R11 : CheckLoc → Lara.Attack.Pos → AttackKind →
      AttackRelationReason → CheckError
  | R13 : CheckLoc → BackendReason → CheckError
deriving DecidableEq

def CheckError.rejectClass : CheckError → RejectClass
  | .R1 _ _ => .R1
  | .R3 _ _ => .R3
  | .R4 _ _ => .R4
  | .R5 _ _ => .R5
  | .R6 _ _ => .R6
  | .R7 _ _ => .R7
  | .R10 _ _ _ _ => .R10
  | .R11 _ _ _ _ => .R11
  | .R13 _ _ => .R13

end Lara.Check
