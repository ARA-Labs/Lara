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
  ) where

import Lara.AST (Rejection (..), RejectClass (R12))
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

-- | Which of the six 'checkUnit' stages produced the rejection.
data Stage
  = StageDuplicateRule
  | StagePolicyWellFormedness
  | StageDuplicateArgument
  | StageSupport
  | StageTypedAttack
  | StageMissingConflict
  deriving (Eq, Show)

-- | Which unit constituent the rejection is about.
data Constituent
  = CPolicy
  | CArgument Int
  | CAttack Int
  | CConflictPair Int Int
  deriving (Eq, Show)

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
