-- | Internal, __unstable__ surface exposing the 'CheckedNode' and
-- 'CheckedHole' constructors.
--
-- Both carry a checker postcondition as an invariant: the conclusion (and, for
-- a hole, the obligation set) is exactly the 'Lara.SupportTerm.inferSupport'
-- result of the term, read off the checker's argument cache. A node's
-- obligation set is empty (only complete arguments become nodes); a hole's is
-- nonempty. The public "Lara.SupportTerm" keeps the constructors hidden so a
-- client cannot forge a \"checked\" node or hole and get a verdict with no
-- checking behind it; "Lara.Check" is the sanctioned producer and mints them
-- through this hatch. This module carries __no stability guarantees__ and may
-- change without notice.
module Lara.SupportTerm.Internal
  ( CheckedNode (..)
  , CheckedHole (..)
  ) where

import Lara.AST (QuestionId, SupportTerm)
import Lara.Prop (Prop)

-- | Exact checked metadata for one retained argument-cache entry (Lean
-- @Compile.CheckedNode@): the term and its conclusion. In Lean the validity
-- proof is a field of the structure; it erases at this layer, so the constructor
-- /is/ the checker's postcondition and stays hidden outside the sanctioned
-- producers. Its obligation set is @[]@ (only complete arguments become nodes).
data CheckedNode = CheckedNode
  { cnTerm :: SupportTerm
  , cnConclusion :: Prop
  }
  deriving (Eq, Show)

-- | Exact checked metadata for one located hole (Lean @Compile.CheckedHole@,
-- spec §4.4): a declared argument that type-checks with a nonempty mandatory
-- root obligation set. It is never an AF node. 'chIndex' is its position in
-- the /checked/ declaration list — the post-admission unit 'Lara.Check.checkUnit'
-- ran on — not an AF index and not an original declaration index; the driver
-- composes it with admission's retained-argument map to report the original
-- position. 'chObligations' is the core's deduplicated union, in
-- @collectObligations@ order.
data CheckedHole = CheckedHole
  { chIndex :: Int
  , chTerm :: SupportTerm
  , chConclusion :: Prop
  , chObligations :: [QuestionId]
  }
  deriving (Eq, Show)
