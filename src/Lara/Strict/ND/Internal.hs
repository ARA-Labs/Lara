-- | Internal, __unstable__ surface of the ND reference adapter.
--
-- This module exposes the raw 'AtomId' constructor so tests and power users can
-- mint atoms directly. It carries __no stability guarantees__ and may change
-- without notice. Ordinary consumers should import "Lara.Strict.ND", which
-- keeps 'AtomId' opaque so that every atom originates from 'Lara.Strict.ND.encodeND'
-- or the module's closed decoder — never fabricated by hand.
module Lara.Strict.ND.Internal
  ( AtomId (..)
  ) where

-- | A backend atom: the canonical, injective serialization of a normalized
-- source proposition (see 'Lara.Strict.ND.encodeND'). The constructor is hidden
-- from the public "Lara.Strict.ND" module so the "atom came from @nf@"
-- invariant cannot be violated by consumers.
newtype AtomId = AtomId String
  deriving (Eq, Ord, Show)
