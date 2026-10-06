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
import Lara.SupportTerm (CheckedHole, CheckedNode)

-- | A unit accepted against its own policy-derived rule lookup (Lean
-- @Unit.CheckedUnit@). Retains the compiled program (complete arguments, live
-- typed attacks, hole terms), the exact checked-node cache the checker
-- produced, the AF-to-checked-declaration map, and the located holes;
-- downstream compilation, grounding and reporting need no support
-- re-inference.
--
-- Under 'Lara.Check.fullConfig' the cache partition holds (Lean
-- @DeclPartition@): 'cuNodeDecls' and the 'Lara.SupportTerm.chIndex' of
-- 'cuHoles' are disjoint, ascending, and together cover every checked
-- declaration index exactly once.
data CheckedUnit = CheckedUnit
  { cuProgram :: CheckedProgram
  , cuNodes :: [CheckedNode]
  , cuNodeDecls :: [Int]
  -- ^ entry @n@ is the checked declaration index of AF node @n@ (Lean
  -- @CheckedUnit.nodeDecls@)
  , cuHoles :: [CheckedHole]
  -- ^ the located holes, in checked declaration order (Lean
  -- @CheckedUnit.holes@)
  }
  deriving (Eq, Show)
