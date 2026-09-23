-- | Source-update vocabulary and constructor side-condition deciders.
--
-- This module mirrors the executable surface of @lean\/Lara\/Update.lean@ that
-- can be checked before source admission: the four 'SourceUpdate' constructors,
-- their four symbolic rejection cases, and the named Boolean deciders. The Lean
-- development owns 'Accepted', 'AcceptedRun', the adequacy theorems for these
-- deciders, preservation, and @applyUpdate@. They are intentionally absent here.
-- In particular, this module is not connected to "Lara.Driver" and does not add
-- a parser, wire section, or runtime update command.
--
-- 'SourceState' retains the raw source carriers rather than a checked unit. A
-- successful update in Lean reruns admission and whole-unit checking; no checked
-- carrier survives an edit. Haskell mirrors the carrier only so the syntactic
-- side conditions can be read and tested declaration by declaration.
module Lara.Update
  ( -- * Raw source carrier
    AdmissionRow
  , LeafMeta (..)
  , RawAttack (..)
  , rawAttackEndpoints
  , SourceState (..)
    -- * Closed update surface
  , SourceUpdate (..)
  , UpdateRejection (..)
  , updatePrecondition
    -- * Constructor side-condition deciders
  , addLeafFreshB
  , admittedAtB
  , endpointDeclaredB
  , instanceFreshB
  ) where

import Data.List (find)

import Lara.AST
  ( Admission (Admit)
  , ArgId
  , DupGroup (..)
  , LeafId
  , LeafKind
  , Policy
  , Position
  , Provenance
  , SupportTerm
  )
import Lara.Prop (Prop)
import Lara.Sigma (Sigma)

-- | One admission-table row. The existing Haskell policy surface represents the
-- Lean @AdmissionRow@ structure as a key/outcome pair, so the update mirror uses
-- that same representation rather than introducing a second table convention.
type AdmissionRow = ((LeafKind, Provenance), Admission)

-- | Admission metadata kept parallel to a semantic leaf row (Lean
-- @Lara.Admission.LeafMeta@).
data LeafMeta = LeafMeta
  { leafMetaId :: LeafId
  , leafMetaKind :: LeafKind
  , leafMetaProvenance :: Provenance
  }
  deriving (Eq, Show)

-- | An attack whose endpoints name argument rows (Lean
-- @Lara.RawAttack.RawAttack@). Positions already use the symbolic Haskell ADT.
data RawAttack
  = RawRebut ArgId ArgId
  | RawUndercut ArgId ArgId Position
  | RawUndermine ArgId ArgId Position
  deriving (Eq, Show)

-- | The source and target row names of a raw attack.
rawAttackEndpoints :: RawAttack -> (ArgId, ArgId)
rawAttackEndpoints raw = case raw of
  RawRebut source target -> (source, target)
  RawUndercut source target _ -> (source, target)
  RawUndermine source target _ -> (source, target)

-- | Raw source material from which admission and whole-unit acceptance are
-- derived. It deliberately contains no checked unit.
data SourceState = SourceState
  { sourceSigma :: Sigma
  , sourcePolicy :: Policy
  , sourceTable :: [AdmissionRow]
  , sourceMetas :: [LeafMeta]
  , sourceLeaves :: [(LeafId, Prop)]
  , sourceArgsRaw :: [(ArgId, SupportTerm)]
  , sourceRawAttacks :: [RawAttack]
  , sourceGroups :: [DupGroup]
  , sourceGround :: [Prop]
  }
  deriving (Eq, Show)

-- | A raw source edit. No constructor changes an admitted source into a rejected
-- source because Lean proves that source rejection has no checked-unit target.
data SourceUpdate
  = AddLeaf LeafId Prop LeafMeta
  | Tighten (LeafKind, Provenance)
  | AddAttack RawAttack
  | AddInstance ArgId SupportTerm
  deriving (Eq, Show)

-- | Closed constructor-side rejections mirrored for decider conformance. The
-- later admission, attack-resolution, and whole-unit rejection cases remain in
-- Lean because Haskell does not expose @applyUpdate@.
data UpdateRejection
  = LeafNotFresh LeafId
  | KeyNotAdmitted (LeafKind, Provenance)
  | EndpointNotDeclared RawAttack
  | InstanceNotFresh ArgId SupportTerm
  deriving (Eq, Show)

-- | Return the constructor-side rejection selected by the same deciders as
-- Lean's @applyUpdate@, or 'Nothing' when every constructor precondition holds.
updatePrecondition :: SourceState -> SourceUpdate -> Maybe UpdateRejection
updatePrecondition source update = case update of
  AddLeaf identifier _ _ ->
    if addLeafFreshB source identifier
      then Nothing
      else Just (LeafNotFresh identifier)
  Tighten key ->
    if admittedAtB source key
      then Nothing
      else Just (KeyNotAdmitted key)
  AddAttack raw ->
    if endpointDeclaredB source raw
      then Nothing
      else Just (EndpointNotDeclared raw)
  AddInstance name term ->
    if instanceFreshB source name term
      then Nothing
      else Just (InstanceNotFresh name term)

-- | Decide whether a leaf identifier is absent from semantic leaf rows,
-- metadata rows, and every duplicate-group member list.
addLeafFreshB :: SourceState -> LeafId -> Bool
addLeafFreshB source identifier =
  all ((/= identifier) . fst) (sourceLeaves source)
    && all ((/= identifier) . leafMetaId) (sourceMetas source)
    && all (all (/= identifier) . dgMembers) (sourceGroups source)

-- | Decide whether Lean's total admission lookup returns 'Admit' at a key.
-- The first matching row wins; duplicate keys are rejected before this lookup
-- on every accepted source, but fixing the total behavior keeps the standalone
-- Haskell mirror differential-exact on arbitrary raw carriers.
admittedAtB :: SourceState -> (LeafKind, Provenance) -> Bool
admittedAtB source key =
  case find ((== key) . fst) (sourceTable source) of
    Just (_, decision) -> decision == Admit
    Nothing -> True

-- | Decide whether both endpoints of a raw attack name declared argument rows.
endpointDeclaredB :: SourceState -> RawAttack -> Bool
endpointDeclaredB source raw =
  let (sourceName, targetName) = rawAttackEndpoints raw
      declared candidate = any ((== candidate) . fst) (sourceArgsRaw source)
   in declared sourceName && declared targetName

-- | Decide freshness in both components of a proposed raw argument row.
instanceFreshB :: SourceState -> ArgId -> SupportTerm -> Bool
instanceFreshB source name term =
  all ((/= name) . fst) (sourceArgsRaw source)
    && all ((/= term) . snd) (sourceArgsRaw source)
