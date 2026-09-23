-- | Internal, __unstable__ surface of the map's identifier namespaces.
--
-- This module holds the two newtypes "Lara.Map.Qualify" exports opaquely, and
-- exposes their constructors. It carries __no stability guarantees__ and may
-- change without notice.
--
-- __Why it exists.__ 'Lara.Map.Qualify.qualifyArgId' is the only sanctioned way
-- to obtain a 'QualifiedArgId', which is what makes the wrapper mean "this went
-- through qualification" rather than merely "this is an 'ArgId'". A public
-- @ArgId -> QualifiedArgId@ function would have contradicted that in the same
-- module that claims it. Tests that synthesize qualified members need to forge
-- one anyway — they assert on readable stand-in spellings like @one:x@ rather
-- than on the real length-framed 'Lara.Map.Types.qualifiedKey' — so the forging
-- lives here, behind the @.Internal@ convention CLAUDE.md prescribes, and out of
-- the public API.
--
-- Ordinary consumers import "Lara.Map.Qualify", where the ways in are
-- 'Lara.Map.Qualify.qualifyArgId' and 'Lara.Map.Qualify.asLocalArgId', and the
-- ways out are 'Lara.Map.Qualify.qualifiedArgId' and
-- 'Lara.Map.Qualify.localArgId'.
module Lara.Map.Qualify.Internal
  ( QualifiedArgId (..)
  , LocalArgId (..)
  ) where

import Lara.AST (ArgId)

-- | An 'ArgId' in the __map's__ namespace, not a member's.
--
-- Both names an argument carries are 'ArgId's, and "Lara.Map.Qualify"'s Haddock
-- is explicit that they are different kinds of thing: "the qualified name is not
-- a report, and the local name is not an identity." While both were spelled
-- 'ArgId', swapping them compiled. The two call sites are one line apart —
-- "Lara.Map.Link" builds the linked unit's identity from one and the verdict's
-- reporting handle from the other — and a swap is silent in both directions: it
-- puts a framed key like @7:paper_a2:a1@ where an author's local name belongs,
-- or an unqualified colliding name into the linked unit.
newtype QualifiedArgId = QualifiedArgId ArgId
  deriving (Eq, Ord, Show)

-- | An 'ArgId' as the member's own author wrote it — a __report__, not an
-- identity.
--
-- The other half of the pair. One newtype would only have caught a swap in one
-- direction, because unwrapping it yields an 'ArgId' that the other site
-- accepts. With both, "Lara.Map.Link" cannot put the qualified key where the
-- author's name belongs, /or/ the author's name where the linked unit's identity
-- belongs: each site names the type it wants and the other value does not have
-- it.
newtype LocalArgId = LocalArgId ArgId
  deriving (Eq, Ord, Show)
