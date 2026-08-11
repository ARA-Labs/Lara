-- | Internal, __unstable__ surface exposing the 'CheckedUnit' constructor.
--
-- 'CheckedUnit' is the checker's acceptance certificate: it exists only when
-- 'Lara.Check.checkUnit' has run all seven stages successfully (the Lean
-- @Unit.CheckedUnit@ it erases carries the acceptance proof). The public
-- "Lara.Check" keeps the constructor hidden so a client cannot fabricate an
-- accepted unit; 'Lara.Check.checkUnit' is its sole sanctioned producer. Tests
-- that need a 'CheckedUnit' obtain it by running 'Lara.Check.checkUnit', not by
-- forging one. __No stability guarantees.__
module Lara.Check.Internal
  ( CheckedUnit (..)
  ) where

import Lara.Compile (CheckedProgram)
import Lara.SupportTerm (CheckedNode)

-- | A unit accepted against its own policy-derived rule lookup (Lean
-- @Unit.CheckedUnit@). Retains the compiled program (arguments + typed attacks)
-- and the exact checked-node cache the checker produced; downstream compilation
-- and grounding need no support re-inference.
data CheckedUnit = CheckedUnit
  { cuProgram :: CheckedProgram
  , cuNodes :: [CheckedNode]
  }
  deriving (Eq, Show)
