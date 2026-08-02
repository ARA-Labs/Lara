-- | Located rejection diagnostics — the bridge from the checker's internal
-- result types ("Lara.Check", "Lara.SupportTerm") to the wire-level
-- 'Lara.AST.Rejection' the @lara@ driver prints, and to a located description
-- (which unit constituent, which of the six stages).
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
    -- * Manifest spelling of a located constituent
  , constituentText
  , parseConstituent
  ) where

import Lara.AST (GroupId (..), Rejection (..), RejectClass (R12))
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
  UEPolicyViolation _ -> RejectClass R12
  UEProgram pe -> case pe of
    PERejection _ ce -> RejectClass (checkErrorClass ce)
    PEDuplicateArgument _ _ -> DuplicateArgument
    PEIncompleteArgument _ _ -> IncompleteArgument
    PEMissingConflict _ -> MissingConflict

-- ---------------------------------------------------------------------------
-- Located description
-- ---------------------------------------------------------------------------

-- | Which stage produced the rejection: one of the six 'checkUnit' stages, or
-- one of the two whole-unit boundary rejections that reject in
-- "Lara.Driver".'Lara.Driver.runCheck' /before/ 'checkUnit' and so never become
-- a 'Lara.Check.UnitError' — the replay preflight (R13) and the §4.3 group
-- check (R9). Only "Lara.Driver".'Lara.Driver.runCheckLocated' produces the two
-- boundary stages; 'locate' produces only the six checker stages.
data Stage
  = StageDuplicateRule
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
-- ("Lara.Mutate".@mutantSite@) and located diagnostics; 'location_match' in the
-- measurement harness is '==' on this type.
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
      UEPolicyViolation _ -> (StagePolicyWellFormedness, CPolicy)
      UEProgram pe -> case pe of
        PEDuplicateArgument i _ -> (StageDuplicateArgument, CArgument i)
        PERejection (DLArgument i) _ -> (StageSupport, CArgument i)
        PERejection (DLAttack i) _ -> (StageTypedAttack, CAttack i)
        PEIncompleteArgument i _ -> (StageSupport, CArgument i)
        PEMissingConflict mc ->
          (StageMissingConflict, CConflictPair (mcSourceIndex mc) (mcTargetIndex mc))
