-- | Cached grounded adjacency — the production evaluator (M3 plan Task 2, D5).
--
-- This module adds __no new labelling and no second fixpoint__. It reuses the
-- single "Lara.Grounded" characteristic-operator iteration verbatim; the only
-- thing it changes is /how the edge relation is realized/. The compiled edge
-- decider ("Lara.Compile.edgeB", surfaced as 'Lara.Compile.checkedAF') rescans
-- the declared attacks on every @afAttack@ query, and for @n = |args|@ the
-- grounded fixpoint's @afAttack@ query count lies between @n^2@ and
-- @n^3 * (1 + n)@ for every framework (Lean: @groundedC_cost_ge@,
-- @groundedC_cost_le@); the fixed-context realizable three-block family
-- attains quartic worst-case degree for both grounded evaluation and the
-- nonempty carrier-status query (@quartic_realizable@, @quartic_cost_ge@,
-- @carrierStatus_quartic_cost_ge@). Those counts are proved about the
-- instrumented Lean mirrors ("Lara.Complexity"); this production runtime is
-- not instrumented. The production backend evaluates that
-- decider __once__ over the argument-index space, materialises the result into
-- immutable @containers@ structures ('CachedAdj'), and hands "Lara.Grounded" an
-- 'AF' whose @afAttack@ is a single 'Data.Set.member' lookup.
--
-- __Correctness contract:__ 'cachedAF' is /extensionally equal/ to its input
-- 'AF' on @afAttack@ over the carrier (and both answer @False@ off it), so it
-- yields identical 'Lara.Grounded.grounded', 'Lara.Grounded.labelC', and
-- 'Lara.Grounded.statusC'. The random-AF equivalence property in
-- @test/RuntimeSpec.hs@ is the conformance evidence; 'Lara.Driver' builds its
-- accept verdict through 'runtimeAF', so the byte-identical N11 fixtures pin the
-- default path.
module Lara.Runtime
  ( -- * Immutable adjacency, computed once
    CachedAdj (..)
  , buildAdj
    -- * The cached framework and the production AF builder
  , cachedAF
  , runtimeAF
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

import Lara.Compile (CheckedProgram, checkedAF)
import Lara.Grounded (AF (..))

-- ---------------------------------------------------------------------------
-- Immutable adjacency, computed once
-- ---------------------------------------------------------------------------

-- | The materialised edge relation of an 'AF', computed by evaluating its
-- @afAttack@ decider exactly once over @afArgs × afArgs@. 'adjEdges' is the
-- membership oracle the cached 'AF' consults — the single shape the grounded
-- fixpoint needs. (Direction-indexed adjacency lists would only pay off for a
-- traversal-shaped consumer, of which there is none; adding them would cost a
-- per-check build with no reader, so they are intentionally omitted.)
data CachedAdj = CachedAdj
  { adjArgs :: [Int]
  -- ^ the carrier, unchanged from the source 'AF'
  , adjEdges :: Set (Int, Int)
  -- ^ @(b, a)@ ∈ set iff @b@ attacks @a@ — the cached @afAttack@ oracle
  }
  deriving (Eq, Show)

-- | Materialise an 'AF'\'s edge relation once. The @afAttack@ decider is
-- evaluated exactly @|afArgs|^2@ times here and never again: every downstream
-- grounded iteration reads 'adjEdges' instead of rescanning the source.
buildAdj :: AF -> CachedAdj
buildAdj f =
  CachedAdj
    { adjArgs = args
    , adjEdges = Set.fromList edges
    }
  where
    args = afArgs f
    -- Single left-to-right scan of the edge surface; ascending in (b, a).
    edges = [(b, a) | b <- args, a <- args, afAttack f b a]

-- ---------------------------------------------------------------------------
-- The cached framework and the production AF builder
-- ---------------------------------------------------------------------------

-- | The cached framework over a source 'AF': the same carrier, but an
-- @afAttack@ that is one immutable 'Set.member' lookup against the pre-computed
-- edge set. Extensionally equal to @f@ on @afAttack@ (both answer @False@ off
-- the carrier), hence plugging it into "Lara.Grounded" gives identical labels
-- and statuses — with the edge relation scanned once rather than per iteration.
cachedAF :: AF -> AF
cachedAF f =
  AF
    { afArgs = adjArgs adj
    , afAttack = \b a -> Set.member (b, a) (adjEdges adj)
    }
  where
    adj = buildAdj f

-- | The production default: compile a checked program to its Dung framework
-- ('checkedAF') and cache the adjacency ('cachedAF'). This is the 'AF'
-- "Lara.Driver" grounds accepted units over; it produces byte-identical
-- verdicts to the un-cached 'checkedAF' path (the N11 fixtures pin this).
runtimeAF :: CheckedProgram -> AF
runtimeAF = cachedAF . checkedAF
