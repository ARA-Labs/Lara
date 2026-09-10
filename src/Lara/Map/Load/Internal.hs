-- | Internal, __unstable__ surface of the map's loading stage.
--
-- This module holds the two data declarations "Lara.Map.Load" exports opaquely,
-- and exposes their constructors. It carries __no stability guarantees__ and may
-- change without notice; ordinary consumers import "Lara.Map.Load", where the
-- only way to obtain a 'CheckedMembers' is 'Lara.Map.Load.loadMap' and the
-- constructor is the promise that every member was rechecked and compared
-- against the manifest's shared contract.
--
-- __Why it exists.__ The linking stage has structural failure arms — the shared
-- sections disagreeing, two members declaring one leaf identity, two linked
-- arguments sharing one identity — that no fixture can reach, because leaf
-- qualification makes a cross-member collision unreachable through 'loadMap'
-- under every policy this repository ships. That makes them a missing tripwire
-- rather than a hidden bug, and a tripwire nothing can break is one nothing
-- would notice the day the saturation and the attack checker come apart. Tests
-- reach those arms by synthesizing members here.
--
-- This is the @.Internal@ test-escape-hatch convention CLAUDE.md prescribes, and
-- the shape "Lara.Strict.ND.Internal" already uses for 'Lara.Strict.ND.AtomId'.
module Lara.Map.Load.Internal
  ( CheckedMember (..)
  , CheckedMembers (..)
  ) where

import Data.List.NonEmpty (NonEmpty)

import Lara.AST (Digest, PropId, Unit)
import Lara.Map.Types (DeclaredPath, MapManifest, MemberAlias)
import Lara.Prop (Prop)
import Lara.Replay (ReplayId)

-- | One member of a map, after it has been read, rechecked on its own, and
-- agreed with the manifest's shared contract.
--
-- __Opaque in "Lara.Map.Load"__: the constructor is the promise that all three
-- happened. Only the fields the qualification, linking, and verdict stages need
-- are carried — deliberately not the whole 'Lara.Elaborate.SourceResult',
-- because a stage that could reach the member's prune, diagnostics, or
-- certificate report could reconstruct a decision that module already made.
data CheckedMember
  = CheckedMember MemberAlias DeclaredPath Digest Unit ReplayId [(PropId, Prop)]

-- | A whole map's members, in manifest order, beside the manifest they came
-- from.
--
-- __Opaque in "Lara.Map.Load"__, for the same reason 'CheckedMember' is: the
-- pairing is part of the promise. The manifest travels along because the stages
-- after loading need its alignments, questions, policy id, and backend list, and
-- re-reading it would let them read a manifest the loader never validated the
-- members against.
--
-- Nonempty by type, inherited from 'Lara.Map.Types.mapMembers': "a map with no
-- members" is not a state a later stage has to consider.
data CheckedMembers = CheckedMembers MapManifest (NonEmpty CheckedMember)
