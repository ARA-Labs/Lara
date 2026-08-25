-- | Located rejection diagnostics — the bridge from the checker's internal
-- result types ("Lara.Check", "Lara.SupportTerm") to the wire-level
-- 'Lara.AST.Rejection' the @lara@ driver prints, and to a located description
-- (which unit constituent, which of the seven stages).
--
-- 'rejectionOf' is the exact wire mapping the Lean driver performs
-- (@lean/Lara/Driver.lean@ @rejectString@): a 'UnitError' becomes the single
-- @REJECTION@ atom of "Lara.Wire". 'locate' additionally records the failing
-- stage and constituent for richer reporting; the wire payload is the class
-- only (located diagnostics live off the wire, plan D16).
module Lara.Diagnostics
  ( -- * The wire mapping (Lean @rejectString@)
    rejectionOf
    -- * Located description
  , Stage (..)
  , Constituent (..)
  , LocatedRejection (..)
  , locate
    -- * Manifest spelling of located constituents (element and list codecs)
  , constituentText
  , parseConstituent
  , constituentListText
  , parseConstituentList
    -- * Seeded ground truth (non-empty by construction)
  , SeededSites
  , seededSite
  , seededSitesNE
  , seededSites
  , seededSitesList
  , seededPrimary
  , seededSitesText
  ) where

import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE

import Lara.AST (GroupId (..), Rejection (..), RejectClass (R2, R12))
import Lara.Check
  ( DeclLoc (..)
  , ProgramError (..)
  , UnitError (..)
  , mcSourceIndex
  , mcTargetIndex
  )
import Lara.SupportTerm (checkErrorClass)

-- ---------------------------------------------------------------------------
-- The wire mapping (Lean @Driver.rejectString@)
-- ---------------------------------------------------------------------------

-- | Map a whole-unit rejection to the wire 'Rejection' atom (Lean
-- @rejectString@). Structural outcomes keep their dedicated constructors; frozen
-- checker failures carry their R-class.
rejectionOf :: UnitError -> Rejection
rejectionOf e = case e of
  UEDuplicateRule _ -> DuplicateRule
  UESignature _ -> RejectClass R2
  UEPolicyViolation _ -> RejectClass R12
  UEProgram pe -> case pe of
    PERejection _ ce -> RejectClass (checkErrorClass ce)
    PEDuplicateArgument _ _ -> DuplicateArgument
    PEIncompleteArgument _ _ -> IncompleteArgument
    PEMissingConflict _ -> MissingConflict

-- ---------------------------------------------------------------------------
-- Located description
-- ---------------------------------------------------------------------------

-- | Which stage produced the rejection: one of the seven 'checkUnit' stages, or
-- one of the two whole-unit boundary rejections that reject in
-- "Lara.Driver".'Lara.Driver.runCheck' /before/ 'checkUnit' and so never become
-- a 'Lara.Check.UnitError' — the replay preflight (R13) and the §4.3 group
-- check (R9). Only "Lara.Driver".'Lara.Driver.runCheckLocated' produces the two
-- boundary stages; 'locate' produces only the seven checker stages.
data Stage
  = StageDuplicateRule
  | StageSignature
  | StagePolicyWellFormedness
  | StageDuplicateArgument
  | StageSupport
  | StageTypedAttack
  | StageMissingConflict
  | StageReplayPreflight
  | StageGroupBoundary
  deriving (Eq, Show)

-- | Which unit constituent the rejection is about. The four checker-stage
-- arms are located by 'locate'; the two boundary arms — 'CReplayEnvelope' (the
-- replay-id backend-selection envelope, ground truth for the
-- @duplicate-backend@\/@unknown-backend@ mutation operators) and 'CGroup' (a
-- declared duplicate-report group, ground truth for @group-conflict@) — are
-- produced only by "Lara.Driver".'Lara.Driver.runCheckLocated'. This is the one
-- location vocabulary shared by seeded ground truth
-- ("Lara.Mutate".@mutantSites@, an ordered non-empty list of admissible
-- constituents — 'SeededSites')
-- and located diagnostics; in the measurement harness @location_match@ is
-- membership in that list and @location_primary@ is '==' with its head
-- (@docs\/localization-metric-decision.md@).
data Constituent
  = CPolicy
  | CArgument Int
  | CAttack Int
  | CConflictPair Int Int
  | CReplayEnvelope
  | CGroup GroupId
  deriving (Eq, Show)

-- | The one place the concrete spelling of a located constituent exists (the
-- @expected-location@ manifest column, spec "symbolic core" rule). Round-trips
-- with 'parseConstituent'. TSV-safe (no tabs); the manifest reserves @-@ for
-- "no seeded site", which this never produces.
constituentText :: Constituent -> String
constituentText c = case c of
  CPolicy -> "policy"
  CArgument i -> "arg:" ++ show i
  CAttack i -> "attack:" ++ show i
  CConflictPair i j -> "conflict:" ++ show i ++ "-" ++ show j
  CReplayEnvelope -> "replay"
  CGroup (GroupId g) -> "group:" ++ g

-- | Parse the @expected-location@ manifest spelling back to a 'Constituent'
-- (inverse of 'constituentText'). 'Nothing' on any spelling this table does not
-- produce.
parseConstituent :: String -> Maybe Constituent
parseConstituent s = case s of
  "policy" -> Just CPolicy
  "replay" -> Just CReplayEnvelope
  _ -> case break (== ':') s of
    ("arg", ':' : rest) -> CArgument <$> readInt rest
    ("attack", ':' : rest) -> CAttack <$> readInt rest
    ("group", ':' : rest) -> Just (CGroup (GroupId rest))
    ("conflict", ':' : rest) -> case break (== '-') rest of
      (a, '-' : b) -> CConflictPair <$> readInt a <*> readInt b
      _ -> Nothing
    _ -> Nothing
  where
    readInt t = case reads t of
      [(n, "")] -> Just n
      _ -> Nothing

-- | The @expected-location@ manifest spelling of an ordered ground-truth
-- list: @-@ for the empty list (no seeded site), else the 'constituentText'
-- spellings joined with @,@. A single-element list renders exactly as its
-- 'constituentText'. 'GroupId' is free-form, so a group id containing @,@
-- would make the rendering ambiguous; that is a generation-time 'error',
-- keeping 'parseConstituentList' a total inverse on everything this produces.
constituentListText :: [Constituent] -> String
constituentListText [] = "-"
constituentListText cs
  | any (elem ',') rendered =
      error
        ( "constituentListText: a group id contains ',', which would make the"
            ++ " expected-location column ambiguous — rename the group: "
            ++ show (filter (elem ',') rendered)
        )
  | otherwise = intercalate "," rendered
  where
    rendered = map constituentText cs

-- | Parse the @expected-location@ list spelling back to its constituents
-- (inverse of 'constituentListText'): @-@ is the empty list, and every
-- comma-separated segment must parse via 'parseConstituent' ('Nothing' on any
-- failure, including an empty segment).
parseConstituentList :: String -> Maybe [Constituent]
parseConstituentList "-" = Just []
parseConstituentList s = traverse parseConstituent (splitComma s)
  where
    splitComma t = case break (== ',') t of
      (seg, ',' : rest) -> seg : splitComma rest
      (seg, _) -> [seg]

-- | A mutant's seeded ground truth: the ordered, /non-empty/ list of
-- admissible manifestation sites, head first in the checker's spec-fixed
-- stage order. Wrapping 'NonEmpty' makes "seeded, but at nothing" — the one
-- shape the metric boundary cannot distinguish from "seeds no site" — a type
-- error rather than a silently-dropped row (#169).
--
-- The distinction the wrapper protects is @Maybe SeededSites@: 'Nothing' is
-- "this row seeds no site" (the codec, cycle, and accept families), which
-- renders @-@ and puts both location metrics off-domain by design. Before the
-- wrapper an enumerator returning @[]@ reached that same state through the
-- other door, leaving the row out of the @location-accuracy-rate@ denominator
-- instead of counting as a miss ("Lara.Measure".@withLocs@).
--
-- The constructor is hidden: build one with 'seededSite' (a single defect),
-- 'seededSitesNE' (a statically non-empty list), or 'seededSites' (from a
-- list that might be empty, hence 'Maybe').
newtype SeededSites = SeededSites (NonEmpty Constituent)
  deriving (Eq, Show)

-- | The ground truth of a single-defect mutant: the singleton of the
-- constituent it mutates, the degenerate case under which membership
-- (@location_match@) and head-equality (@location_primary@) coincide.
seededSite :: Constituent -> SeededSites
seededSite c = SeededSites (c :| [])

-- | Seeded ground truth from a statically non-empty list — for the composite
-- enumerators, whose element count is fixed by construction.
seededSitesNE :: NonEmpty Constituent -> SeededSites
seededSitesNE = SeededSites

-- | Seeded ground truth from a list that may be empty: 'Nothing' exactly on
-- @[]@, which is the manifest's @-@. This is the sanctioned way to turn a
-- comprehension's output (or a parsed manifest column) into ground truth —
-- the empty case must be handled, not dropped.
seededSites :: [Constituent] -> Maybe SeededSites
seededSites = fmap SeededSites . NE.nonEmpty

-- | The admissible sites, in order.
seededSitesList :: SeededSites -> [Constituent]
seededSitesList (SeededSites ne) = NE.toList ne

-- | The spec-order-first site — total, which is the point of the wrapper:
-- @location_primary@ needs a head and now cannot fail to have one.
seededPrimary :: SeededSites -> Constituent
seededPrimary (SeededSites ne) = NE.head ne

-- | The @expected-location@ manifest column of a row's ground truth: @-@ when
-- the row seeds no site, else 'constituentListText' of the list.
seededSitesText :: Maybe SeededSites -> String
seededSitesText = constituentListText . maybe [] seededSitesList

-- | A located rejection: the wire class plus the stage and constituent that
-- produced it.
data LocatedRejection = LocatedRejection
  { lrRejection :: Rejection
  , lrStage :: Stage
  , lrConstituent :: Constituent
  }
  deriving (Eq, Show)

-- | Locate a whole-unit rejection at its stage and constituent.
locate :: UnitError -> LocatedRejection
locate e = LocatedRejection (rejectionOf e) stage constituent
  where
    (stage, constituent) = case e of
      UEDuplicateRule _ -> (StageDuplicateRule, CPolicy)
      -- A sort failure is always a fact about the policy's declared signature
      -- or about material read under it, so it locates at the policy — the same
      -- constituent R12 uses, and for the same reason.
      UESignature _ -> (StageSignature, CPolicy)
      UEPolicyViolation _ -> (StagePolicyWellFormedness, CPolicy)
      UEProgram pe -> case pe of
        PEDuplicateArgument i _ -> (StageDuplicateArgument, CArgument i)
        PERejection (DLArgument i) _ -> (StageSupport, CArgument i)
        PERejection (DLAttack i) _ -> (StageTypedAttack, CAttack i)
        PEIncompleteArgument i _ -> (StageSupport, CArgument i)
        PEMissingConflict mc ->
          (StageMissingConflict, CConflictPair (mcSourceIndex mc) (mcTargetIndex mc))
