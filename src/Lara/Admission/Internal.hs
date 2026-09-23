-- | Policy admission at the trusted source boundary.
--
-- The source pipeline is deliberately linear:
--
-- @
-- declared leaves -> validate table -> first reject? -> quarantine seed
--                 -> union inconsistent groups -> one prune -> audit
-- @
--
-- The table index used below is private.  Public observations retain source
-- declaration order even though decisions and duplicate checks use 'Map' and
-- 'Set' internally.
module Lara.Admission.Internal
  ( AdmissionCause (..)
  , AdmissionAudit (..)
  , admissionAuditLeaves
  , admissionAuditArgs
  , admissionAuditAttacks
  , admissionAuditIsEmpty
  , admissionAuditHasPolicyQuarantine
  , AdmissionRejection (..)
  , admissionRejectionLeaf
  , admissionRejectionKind
  , admissionRejectionProvenance
  , admissionRejectionMatchedRow
  , decisionFor
  , validateAdmissionKeys
  , firstAdmissionRejection
  , policyQuarantineSeed
  , buildAdmissionAudit
  , renderAdmissionRejection
  , renderAdmissionAudit
  ) where

import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Lara.AST
  ( Admission (..)
  , ArgId (..)
  , Attack (..)
  , DupGroup (..)
  , GroupId (..)
  , Leaf (..)
  , LeafId (..)
  , LeafKind (..)
  , Provenance (..)
  , QuestionId (..)
  , Step (..)
  )
import Lara.Blocked
  ( Prune
  , pruneInconsistentGroups
  , prunePolicyLeaves
  , pruneRemovedArgs
  , pruneRemovedAttacks
  , pruneRemovedLeaves
  )

-- | Why a leaf was removed.  Cause order is canonical: policy first, followed
-- by every inconsistent containing group in group declaration order.
data AdmissionCause
  = PolicyQuarantine
  | GroupQuarantine GroupId
  deriving (Eq, Ord, Show)

-- | The source-ordered material removed by the single admission/group prune.
-- The constructor is hidden so a caller cannot invent an empty cause list.
data AdmissionAudit = AdmissionAudit
  [(LeafId, NonEmpty AdmissionCause)]
  [ArgId]
  [Attack]
  deriving (Eq, Show)

admissionAuditLeaves :: AdmissionAudit -> [(LeafId, NonEmpty AdmissionCause)]
admissionAuditLeaves (AdmissionAudit leaves _ _) = leaves

admissionAuditArgs :: AdmissionAudit -> [ArgId]
admissionAuditArgs (AdmissionAudit _ args _) = args

admissionAuditAttacks :: AdmissionAudit -> [Attack]
admissionAuditAttacks (AdmissionAudit _ _ attacks) = attacks

admissionAuditIsEmpty :: AdmissionAudit -> Bool
admissionAuditIsEmpty (AdmissionAudit leaves args attacks) =
  null leaves && null args && null attacks

-- | Whether policy admission, rather than only duplicate-group quarantine,
-- removed source material. The leaf audit is the canonical cause carrier:
-- every policy seed member is recorded on its declared leaf before dependent
-- arguments and attacks are projected.
admissionAuditHasPolicyQuarantine :: AdmissionAudit -> Bool
admissionAuditHasPolicyQuarantine (AdmissionAudit leaves _ _) =
  any (\(_, causes) -> PolicyQuarantine `elem` causes) leaves

-- | A located R8 decision.  The constructor is hidden: it can only arise from
-- an exact row match performed by 'firstAdmissionRejection'.
data AdmissionRejection = AdmissionRejection
  LeafId
  LeafKind
  Provenance
  ((LeafKind, Provenance), Admission)
  deriving (Eq, Show)

admissionRejectionLeaf :: AdmissionRejection -> LeafId
admissionRejectionLeaf (AdmissionRejection leaf _ _ _) = leaf

admissionRejectionKind :: AdmissionRejection -> LeafKind
admissionRejectionKind (AdmissionRejection _ kind _ _) = kind

admissionRejectionProvenance :: AdmissionRejection -> Provenance
admissionRejectionProvenance (AdmissionRejection _ _ provenance _) = provenance

admissionRejectionMatchedRow
  :: AdmissionRejection
  -> ((LeafKind, Provenance), Admission)
admissionRejectionMatchedRow (AdmissionRejection _ _ _ row) = row

-- | Total exact lookup.  Omitted and unmatched keys default to 'Admit'.
decisionFor
  :: [((LeafKind, Provenance), Admission)]
  -> LeafKind
  -> Provenance
  -> Admission
decisionFor table kind provenance =
  Map.findWithDefault Admit (kind, provenance) (admissionIndex table)

-- | Reject the first duplicate key in declaration order.
validateAdmissionKeys
  :: [((LeafKind, Provenance), Admission)]
  -> Either (LeafKind, Provenance) ()
validateAdmissionKeys = go Set.empty
  where
    go :: Set (LeafKind, Provenance) -> [((LeafKind, Provenance), Admission)] -> Either (LeafKind, Provenance) ()
    go _ [] = Right ()
    go seen ((key, _) : rows)
      | Set.member key seen = Left key
      | otherwise = go (Set.insert key seen) rows

-- | The first rejected leaf in source declaration order.
firstAdmissionRejection
  :: [((LeafKind, Provenance), Admission)]
  -> [Leaf]
  -> Maybe AdmissionRejection
firstAdmissionRejection table = go
  where
    decisions = admissionIndex table
    go [] = Nothing
    go (leaf : leaves) =
      let key = (leafKind leaf, leafProvenance leaf)
       in case Map.lookup key decisions of
            Just Reject ->
              Just
                ( AdmissionRejection
                    (leafId leaf)
                    (leafKind leaf)
                    (leafProvenance leaf)
                    (key, Reject)
                )
            _ -> go leaves

-- | Policy-quarantined leaf ids in source declaration order.
policyQuarantineSeed
  :: [((LeafKind, Provenance), Admission)]
  -> [Leaf]
  -> [LeafId]
policyQuarantineSeed table leaves =
  [ leafId leaf
  | leaf <- leaves
  , Map.findWithDefault Admit (leafKind leaf, leafProvenance leaf) decisions == Quarantine
  ]
  where
    decisions = admissionIndex table

-- | Project the canonical audit from the exact decisions stored by 'Prune'.
-- No support or endpoint removal decision is repeated here.
buildAdmissionAudit :: Prune -> AdmissionAudit
buildAdmissionAudit pruned =
  AdmissionAudit leafRows (pruneRemovedArgs pruned) (pruneRemovedAttacks pruned)
  where
    policySet = Set.fromList (prunePolicyLeaves pruned)
    inconsistent =
      [(group, Set.fromList (dgMembers group)) | group <- pruneInconsistentGroups pruned]
    causesFor leaf =
      [PolicyQuarantine | Set.member leaf policySet]
        ++ [GroupQuarantine (dgId group) | (group, members) <- inconsistent, Set.member leaf members]
    leafRows =
      [ (leaf, cause :| causes)
      | leaf <- pruneRemovedLeaves pruned
      , cause : causes <- [causesFor leaf]
      ]

renderAdmissionRejection :: AdmissionRejection -> String
renderAdmissionRejection rejection =
  "leaf '" ++ leafText (admissionRejectionLeaf rejection)
    ++ "': kind=" ++ kindText (admissionRejectionKind rejection)
    ++ ", provenance=" ++ provenanceText (admissionRejectionProvenance rejection)
    ++ " matched admission row ("
    ++ kindText kind ++ ", " ++ provenanceText provenance
    ++ ") = " ++ admissionText decision ++ " (R8)"
  where
    ((kind, provenance), decision) = admissionRejectionMatchedRow rejection

renderAdmissionAudit :: AdmissionAudit -> String
renderAdmissionAudit audit =
  "admission audit: leaves ["
    ++ intercalate "," (map renderLeaf (admissionAuditLeaves audit))
    ++ "]; arguments ["
    ++ intercalate "," [arg | ArgId arg <- admissionAuditArgs audit]
    ++ "]; attacks ["
    ++ intercalate "," (map renderAttack (admissionAuditAttacks audit))
    ++ "]"
  where
    renderLeaf (LeafId leaf, causes) =
      leaf ++ "{" ++ intercalate "," (map renderCause (nonEmptyToList causes)) ++ "}"

admissionIndex :: [((LeafKind, Provenance), Admission)] -> Map (LeafKind, Provenance) Admission
admissionIndex = Map.fromList

renderCause :: AdmissionCause -> String
renderCause PolicyQuarantine = "policy-quarantine"
renderCause (GroupQuarantine (GroupId groupId)) = "group-quarantine:" ++ groupId

renderAttack :: Attack -> String
renderAttack attack = case attack of
  Rebut (ArgId source) (ArgId target) -> "rebut(" ++ source ++ "," ++ target ++ ")"
  Undercut (ArgId source) (ArgId target) position ->
    "undercut(" ++ source ++ "," ++ target ++ "," ++ renderPosition position ++ ")"
  Undermine (ArgId source) (ArgId target) position ->
    "undermine(" ++ source ++ "," ++ target ++ "," ++ renderPosition position ++ ")"

renderPosition :: [Step] -> String
renderPosition steps = "[" ++ intercalate "," (map renderStep steps) ++ "]"
  where
    renderStep (StepPremise index) = "premise:" ++ show index
    renderStep (StepQuestion (QuestionId question)) = "question:" ++ question

nonEmptyToList :: NonEmpty a -> [a]
nonEmptyToList (x :| xs) = x : xs

leafText :: LeafId -> String
leafText (LeafId leaf) = leaf

kindText :: LeafKind -> String
kindText kind = case kind of
  Observed -> "observed"
  Attested -> "attested"
  Assumed -> "assumed"
  Certified -> "certified"

provenanceText :: Provenance -> String
provenanceText provenance = case provenance of
  User -> "user"
  AiExecuted -> "ai-executed"
  Checker name version -> "checker(" ++ name ++ ", " ++ version ++ ")"

admissionText :: Admission -> String
admissionText decision = case decision of
  Admit -> "admit"
  Quarantine -> "quarantine"
  Reject -> "reject"
