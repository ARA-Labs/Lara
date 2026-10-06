-- | Internal, __unstable__ surface exposing the 'CheckedProgram' constructor.
--
-- 'CheckedProgram' carries the checker's postcondition as an invariant: its
-- arguments are a duplicate-free set of /complete/ checked terms, its attacks
-- are typed with a complete source, and its holes are the typed declarations
-- with a nonempty obligation set (the Lean @Compile.CheckedProgram@ structure
-- carries the @nodup@\/@complete@\/@typed@\/@source_declared@ proof fields,
-- which erase here). The public
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
-- the declared complete arguments @Args(P)@ (a set — no duplicate terms), the
-- compiled attacks (the typed declared attacks whose source is complete), and
-- the located holes @Holes(P)@ (spec §4.4) in checked declaration order. Only
-- 'cpArgs' are AF nodes; 'cpHoles' are kept because a compiled attack may name
-- one as its target, and because they are part of a checked program's identity
-- (the derived 'Eq' compares all three fields, which is what
-- "Lara.PW.Run" deduplicates worlds by — Lean @PW.Run.WorldState@). The
-- completeness\/typing evidence of the Lean structure erases at this layer;
-- "Lara.Check" establishes it before constructing this value.
data CheckedProgram = CheckedProgram
  { cpArgs :: [SupportTerm]
  , cpAtts :: [RAttack]
  , cpHoles :: [SupportTerm]
  }
  deriving (Eq, Show)
