-- | Internal, __unstable__ surface exposing the 'CheckedNode' constructor.
--
-- 'CheckedNode' carries a checker postcondition as an invariant: its conclusion
-- is exactly the 'Lara.SupportTerm.inferSupport' result of its term, with an
-- empty obligation set (only complete arguments become nodes). The public
-- "Lara.SupportTerm" keeps the constructor hidden so a client cannot forge a
-- \"checked\" node and get a verdict with no checking behind it; the sanctioned
-- producers ("Lara.Check", "Lara.Reporting") mint them through this hatch. This
-- module carries __no stability guarantees__ and may change without notice.
module Lara.SupportTerm.Internal
  ( CheckedNode (..)
  ) where

import Lara.AST (SupportTerm)
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
