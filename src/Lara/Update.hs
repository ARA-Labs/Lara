-- | Source-update vocabulary and constructor side-condition deciders.
--
-- This module mirrors the executable surface of @lean\/Lara\/Update.lean@ that
-- can be checked before source admission: the six 'SourceUpdate' constructors,
-- their symbolic rejection cases, the named Boolean deciders, the in-place
-- discharge rewrite (@lean\/Lara\/Update\/Discharge.lean@), and the raw stage
-- of an atomic batch ('applyBatch'). The Lean development owns 'Accepted',
-- 'AcceptedRun', the adequacy theorems for these deciders, preservation, and
-- @applyUpdate@. They are intentionally absent here. In particular, this module
-- is not connected to "Lara.Driver" and does not add a parser, wire section, or
-- runtime update command.
--
-- 'SourceState' retains the raw source carriers rather than a checked unit. A
-- successful update in Lean reruns admission and whole-unit checking; no checked
-- carrier survives an edit. Haskell mirrors the carrier only so the syntactic
-- side conditions, and the raw edits a batch performs, can be read and tested
-- declaration by declaration.
module Lara.Update
  ( -- * Raw source carrier
    AdmissionRow
  , LeafMeta (..)
  , RawAttack (..)
  , rawAttackEndpoints
  , SourceState (..)
    -- * Closed update surface
  , SourceUpdate (..)
  , AtomicEdit (..)
  , UpdateRejection (..)
  , updatePrecondition
    -- * Constructor side-condition deciders
  , addLeafFreshB
  , admittedAtB
  , endpointDeclaredB
  , instanceFreshB
  , openAtB
  , dischargeOpenB
    -- * In-place discharge and atomic batches (raw stage)
  , dischargeAt
  , dischargeRows
  , applyRawEdit
  , applyBatch
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
  , QuestionId
  , Step (..)
  , SupportTerm (..)
  )
import Lara.Attack (lookupDis, subterm)
import Lara.Prop (Prop)
import Lara.Sigma (Sigma)
import Lara.SupportTerm (holeNames)

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
  | -- | Answer the open question of the rule occurrence at the position inside
    -- the named argument, in place (Lean @dischargeOpen@, D13).
    DischargeOpen ArgId Position QuestionId SupportTerm
  | -- | Apply raw edits in order, then admit and check once (Lean @atomic@,
    -- D14).
    Atomic [AtomicEdit]
  deriving (Eq, Show)

-- | One raw edit of an atomic batch (Lean @AtomicEdit@): the additive
-- constructors plus in-place discharge. A batch cannot contain a batch.
data AtomicEdit
  = EditAddLeaf LeafId Prop LeafMeta
  | EditAddInstance ArgId SupportTerm
  | EditAddAttack RawAttack
  | EditDischargeOpen ArgId Position QuestionId SupportTerm
  deriving (Eq, Show)

-- | Closed constructor-side rejections mirrored for decider conformance. The
-- later admission, attack-resolution, and whole-unit rejection cases remain in
-- Lean because Haskell does not expose @applyUpdate@.
data UpdateRejection
  = LeafNotFresh LeafId
  | KeyNotAdmitted (LeafKind, Provenance)
  | EndpointNotDeclared RawAttack
  | InstanceNotFresh ArgId SupportTerm
  | NotDischargeable ArgId Position QuestionId
  | -- | The first failing raw edit of a batch, by its zero-based position.
    BatchEdit Int UpdateRejection
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
  DischargeOpen name pos question _ ->
    if dischargeOpenB source name pos question
      then Nothing
      else Just (NotDischargeable name pos question)
  Atomic edits -> either Just (const Nothing) (applyBatch source edits)

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

-- | Decide whether the occurrence at a position is a rule instance whose open
-- set contains the question (Lean @Discharge.openAtB@).
openAtB :: SupportTerm -> Position -> QuestionId -> Bool
openAtB term pos question = case subterm term pos of
  Just (SRule _ _ _ _ holes _) -> question `elem` holeNames holes
  _ -> False

-- | Decide the in-place discharge site precondition (Lean @dischargeOpenB@):
-- the argument row the name resolves to (first match, as raw endpoint
-- resolution reads it) has an open site at the position.
dischargeOpenB :: SourceState -> ArgId -> Position -> QuestionId -> Bool
dischargeOpenB source name pos question =
  case lookup name (sourceArgsRaw source) of
    Just term -> openAtB term pos question
    Nothing -> False

-- | Close the open question at the position with the discharge term (Lean
-- @Discharge.dischargeAt@): the question leaves the open set and the discharge
-- is appended to the discharge map, so every earlier discharge lookup is
-- unchanged.
dischargeAt :: QuestionId -> SupportTerm -> Position -> SupportTerm -> Maybe SupportTerm
dischargeAt question answer pos term = case (pos, term) of
  ([], SRule rule theta premises discharges holes assurance)
    | question `elem` holeNames holes ->
        Just
          ( SRule
              rule
              theta
              premises
              (discharges ++ [(question, answer)])
              (filter ((/= [question]) . holeNames . pure) holes)
              assurance
          )
    | otherwise -> Nothing
  ([], SLeaf _) -> Nothing
  (_ : _, SLeaf _) -> Nothing
  (StepPremise i : rest, SRule rule theta premises discharges holes assurance) ->
    case indexAt premises i of
      Just child ->
        fmap
          (\child' -> SRule rule theta (setAt i child' premises) discharges holes assurance)
          (dischargeAt question answer rest child)
      Nothing -> Nothing
  (StepQuestion q : rest, SRule rule theta premises discharges holes assurance) ->
    case lookupDis discharges q of
      Just child ->
        fmap
          (\child' -> SRule rule theta premises (replaceDis q child' discharges) holes assurance)
          (dischargeAt question answer rest child)
      Nothing -> Nothing

-- | Rewrite every argument row named by the discharge in place (Lean
-- @dischargeRows@): each keeps its name and position.
dischargeRows ::
  [(ArgId, SupportTerm)] -> ArgId -> Position -> QuestionId -> SupportTerm -> [(ArgId, SupportTerm)]
dischargeRows rows name pos question answer =
  [ if rowName == name
      then (rowName, maybe term id (dischargeAt question answer pos term))
      else (rowName, term)
  | (rowName, term) <- rows
  ]

-- | Apply one raw edit of a batch against the state the earlier edits produced
-- (Lean @AtomicEdit.applyRaw@). No admission or checking happens here.
applyRawEdit :: SourceState -> AtomicEdit -> Either UpdateRejection SourceState
applyRawEdit source edit = case edit of
  EditAddLeaf identifier proposition metadata
    | addLeafFreshB source identifier ->
        Right
          source
            { sourceMetas = sourceMetas source ++ [metadata {leafMetaId = identifier}]
            , sourceLeaves = sourceLeaves source ++ [(identifier, proposition)]
            }
    | otherwise -> Left (LeafNotFresh identifier)
  EditAddInstance name term
    | instanceFreshB source name term ->
        Right source {sourceArgsRaw = sourceArgsRaw source ++ [(name, term)]}
    | otherwise -> Left (InstanceNotFresh name term)
  EditAddAttack raw
    | endpointDeclaredB source raw ->
        Right source {sourceRawAttacks = sourceRawAttacks source ++ [raw]}
    | otherwise -> Left (EndpointNotDeclared raw)
  EditDischargeOpen name pos question answer
    | dischargeOpenB source name pos question ->
        Right
          source
            { sourceArgsRaw = dischargeRows (sourceArgsRaw source) name pos question answer
            }
    | otherwise -> Left (NotDischargeable name pos question)

-- | The raw final state of a batch, or its first edit rejection tagged with the
-- edit's zero-based position (Lean @applyBatch@).
applyBatch :: SourceState -> [AtomicEdit] -> Either UpdateRejection SourceState
applyBatch = go 0
  where
    go :: Int -> SourceState -> [AtomicEdit] -> Either UpdateRejection SourceState
    go _ source [] = Right source
    go index source (edit : rest) = case applyRawEdit source edit of
      Left reason -> Left (BatchEdit index reason)
      Right next -> go (index + 1) next rest

indexAt :: [a] -> Int -> Maybe a
indexAt xs i
  | i < 0 = Nothing
  | otherwise = case drop i xs of
      (x : _) -> Just x
      [] -> Nothing

setAt :: Int -> a -> [a] -> [a]
setAt i x xs = [if j == i then x else y | (j, y) <- zip [0 ..] xs]

-- | Replace the first discharge entry keyed by the question (Lean
-- @Discharge.replaceDis@).
replaceDis :: QuestionId -> SupportTerm -> [(QuestionId, SupportTerm)] -> [(QuestionId, SupportTerm)]
replaceDis _ _ [] = []
replaceDis q term ((key, old) : rest)
  | key == q = (key, term) : rest
  | otherwise = (key, old) : replaceDis q term rest
