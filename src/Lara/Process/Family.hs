-- | Guarded source alternatives. Source acceptance is deliberately not a family gate.
module Lara.Process.Family
  ( guardHolds, guardsHold, familyWellFormed, assignmentWellFormed
  , resolveSlot, resolveAssignment, assignmentMember, completionMember
  , claimBindingValid, fixedClaims, selectedDecls, materialize
  , declarationKeys, hypotheticalKeys
  ) where

import Data.List (find)
import qualified Data.Set as Set
import qualified Lara.AST as A
import Lara.Process.Audit.Types
import qualified Lara.Process.History as History
import Lara.Process.Source.Types
import Lara.Process.Types (ProcessHistory, Problem (..))

-- | 'GuardBefore' compares complete stamped events and requires a strict suffix.
guardHolds :: Guard -> ProcessHistory -> Bool
guardHolds guard history = case guard of
  GuardTruth -> True
  GuardQuery query -> History.queryHolds query history
  GuardPresent event -> event `elem` history
  GuardBefore first second -> before history
    where
      before [] = False
      before (event : rest) = (event == first && second `elem` rest) || before rest
  GuardNot inner -> not (guardHolds inner history)
  GuardAnd left right -> guardHolds left history && guardHolds right history
  GuardOr left right -> guardHolds left history || guardHolds right history

guardsHold :: ProcessHistory -> [Selection] -> Bool
guardsHold history = all (\selection -> guardHolds (choiceGuard (selectionChoice selection)) history)

familyWellFormed :: FamilySpec -> Bool
familyWellFormed spec = distinctOn slotId (familySlots spec)
  && all (\slot -> not (null (slotChoices slot)) && distinctOn choiceId (slotChoices slot)) (familySlots spec)
  where
    distinctOn key = go Set.empty
      where
        go _ [] = True
        go seen (value : rest)
          | Set.member (key value) seen = False
          | otherwise = go (Set.insert (key value) seen) rest

-- | Exactly one of the actual declared choices per slot, in declaration order.
-- Identity alone is insufficient: a caller cannot replace a choice's guard or fragment.
assignmentWellFormed :: FamilySpec -> [Selection] -> Bool
assignmentWellFormed spec = chooses (familySlots spec)
  where
    chooses [] [] = True
    chooses (slot : slots) (selection : assignment) =
      selectionSlot selection == slotId slot
      && selectionChoice selection `elem` slotChoices slot
      && chooses slots assignment
    chooses _ _ = False

-- | Lookup retains first-match semantics; family well-formedness is a separate gate.
resolveSlot :: FamilySpec -> SlotId -> ChoiceId -> Maybe Selection
resolveSlot spec slot choice = do
  declared <- find ((== slot) . slotId) (familySlots spec)
  selected <- find ((== choice) . choiceId) (slotChoices declared)
  pure (Selection slot selected)

resolveAssignment :: FamilySpec -> [(SlotId, ChoiceId)] -> Maybe [Selection]
resolveAssignment spec = traverse (uncurry (resolveSlot spec))

assignmentMember :: FamilySpec -> ProcessHistory -> [Selection] -> Bool
assignmentMember spec history assignment =
  assignmentWellFormed spec assignment && guardsHold history assignment

-- | Membership in the declared event universe matters in addition to compatibility.
completionMember :: FamilySpec -> Completion -> Bool
completionMember spec completion =
  all (`Set.member` allowed) history
  && History.problemCompatible problem history
  && assignmentMember spec history (completionAssignment completion)
  where
    problem = familyProblem spec
    history = completionHistory completion
    allowed = Set.fromList (History.base problem ++ problemUnrecorded problem)

-- | A fragment-only claim does not alter the fixed binding to the base source.
claimBindingValid :: FamilySpec -> ClaimBinding -> Bool
claimBindingValid spec binding = formal (A.programDecls (sourceProgram (familyBase spec))) == Just (bindingQuery binding)
  where
    formal [] = Nothing
    formal (A.DeclClaim claim : rest)
      | A.claimId claim == bindingDeclaration binding = Just (A.claimFormal claim)
      | otherwise = formal rest
    formal (_ : rest) = formal rest

fixedClaims :: FamilySpec -> AuditConfig -> Bool
fixedClaims spec = all (claimBindingValid spec) . auditClaims

selectedDecls :: Completion -> [A.Decl]
selectedDecls = concatMap (fragmentDecls . choiceFragment . selectionChoice) . completionAssignment

-- | Append the opaque carriers, preserving all base metadata and payload coordinates.
-- No fragment is checked separately, reordered, repaired or discarded.
materialize :: FamilySpec -> Completion -> SourceInput
materialize spec = foldl' appendSelection (familyBase spec) . completionAssignment
  where
    appendSelection input = appendFragment input . choiceFragment . selectionChoice

declarationKeys :: A.Decl -> [KindKey]
declarationKeys declaration = case declaration of
  A.DeclLeaf leaf -> [LeafKey (A.leafId leaf)]
  A.DeclArg argument -> [ArgumentKey (A.argId argument)]
  A.DeclComparison comparison -> [ArgumentKey (A.cmpRecheckArg comparison), ArgumentKey (A.cmpBridgeArg comparison)]
  _ -> []

hypotheticalKeys :: Completion -> [KindKey]
hypotheticalKeys = concatMap declarationKeys . selectedDecls
