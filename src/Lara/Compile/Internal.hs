-- | Internal, __unstable__ surface exposing the 'CheckedProgram' constructor.
--
-- 'CheckedProgram' carries the checker's postcondition as an invariant: its
-- arguments are a duplicate-free set of /complete/ checked terms and its attacks
-- are typed (the Lean @Compile.CheckedProgram@ structure carries the
-- @nodup@\/@complete@\/@typed@ proof fields, which erase here). The public
-- "Lara.Compile" keeps the constructor hidden so a client cannot forge a
-- \"checked\" program and compile it to a verdict with no checking behind it;
-- the sanctioned producers ("Lara.Check", "Lara.Reporting") mint them through
-- this hatch. __No stability guarantees.__
module Lara.Compile.Internal
  ( CheckedProgram (..)
  ) where

import Lara.AST (SupportTerm)
import Lara.Attack (RAttack)

-- | A checked program at the compile boundary (Lean @Compile.CheckedProgram@):
-- the declared complete arguments (a set — no duplicate terms) and the declared
-- typed attacks. The completeness\/typing evidence of the Lean structure erases
-- at this layer; "Lara.Check" establishes it before constructing this value.
data CheckedProgram = CheckedProgram
  { cpArgs :: [SupportTerm]
  , cpAtts :: [RAttack]
  }
  deriving (Eq, Show)
