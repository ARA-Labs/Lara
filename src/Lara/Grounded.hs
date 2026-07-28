-- | Least-fixpoint grounded labelling and four-state claim status (spec §8) —
-- the Haskell mirror of @lean/Lara/Grounded.lean@ (@grounded@ \/ @labelC@ \/
-- @statusC@) and the @completeClaimFor@ projection of
-- @lean/Lara/Consistency.lean@.
--
-- The framework 'AF' is the /edge-access interface/ the fixpoint is defined
-- over exactly once (plan D5): a finite carrier 'afArgs' and a decidable attack
-- oracle 'afAttack'. "Lara.Compile" plugs in the checker-built edge decider
-- ('Lara.Compile.checkedAF'); a future cached-adjacency backend (Task 2) plugs a
-- different 'afAttack' into the same fixpoint with no second copy.
--
-- 'grounded' is the least fixed point of Dung's characteristic operator computed
-- by bounded iteration from @[]@; a finite carrier makes the ascending chain
-- stabilize within @|args|@ steps (Lean @grounded_stable@ — the termination
-- content of spec §8 result 5), so it is total and deterministic.
--
-- Four-state 'statusC' aggregates 'labelC' over a 'Claim' record. It reads
-- /only/ 'claimSupport' and never 'claimHoles': it decides @gap@ on empty
-- complete support alone (Lean @statusC_gap_iff@), so a complete winning @in@
-- argument is never downgraded by a hole (N17 point 1). 'completeClaimFor'
-- therefore leaves 'claimHoles' @[]@ (Lean @completeClaimFor@ likewise); the
-- diagnostic hole population lives in "Lara.Reporting"
-- ('Lara.Reporting.reportClaimFor').
module Lara.Grounded
  ( -- * The compiled framework (the edge-access interface, plan D5)
    AF (..)
    -- * The characteristic operator and the grounded extension
  , defendedB
  , step
  , iter
  , grounded
    -- * Labels and four-state status
  , labelC
  , Claim (..)
  , statusC
    -- * Computed complete-claim projection (Lean @completeClaimFor@)
  , claimSupportFor
  , completeClaimFor
  ) where

import Lara.AST (Label (..), Status (..))
import Lara.Prop (Prop, equiv)
import Lara.SupportTerm (CheckedNode (..))

-- ---------------------------------------------------------------------------
-- The compiled framework
-- ---------------------------------------------------------------------------

-- | A compiled argumentation framework (Lean @Grounded.AF@): a finite carrier
-- of argument indices and a decidable attack relation. This record is the
-- edge-access interface the fixpoint below is parameterized over (plan D5):
-- 'afAttack' is the pluggable edge oracle.
data AF = AF
  { afArgs :: [Int]
  , afAttack :: Int -> Int -> Bool
  }

-- ---------------------------------------------------------------------------
-- The characteristic operator and the grounded extension
-- ---------------------------------------------------------------------------

-- | @a@ is defended by @S@: every attacker of @a@ in the framework is itself
-- attacked by some member of @S@ (Lean @defendedB@).
defendedB :: AF -> [Int] -> Int -> Bool
defendedB f s a =
  all (\b -> not (afAttack f b a) || any (\c -> afAttack f c b) s) (afArgs f)

-- | One round of the characteristic operator (Lean @step@).
step :: AF -> [Int] -> [Int]
step f s = filter (defendedB f s) (afArgs f)

-- | The reference iteration from @[]@ (Lean @iter@).
iter :: AF -> Int -> [Int]
iter _ 0 = []
iter f k = step f (iter f (k - 1))

-- | The grounded extension: iterate @|args|@ times. @grounded_stable@ proves
-- this is already the least fixed point (Lean @grounded@).
grounded :: AF -> [Int]
grounded f = iter f (length (afArgs f))

-- ---------------------------------------------------------------------------
-- Labels and four-state status
-- ---------------------------------------------------------------------------

-- | The compiled labelling read off @grounded@ (Lean @labelC@): @in@ if
-- grounded, else @out@ if some grounded argument attacks it, else @undec@.
labelC :: AF -> Int -> Label
labelC f a =
  let g = grounded f
   in if a `elem` g
        then LIn
        else
          if any (\c -> c `elem` g && afAttack f c a) (afArgs f)
            then LOut
            else LUndec

-- | A claim with its complete checked support arguments and its (incomplete)
-- hole-bearing supporting arguments (Lean @Grounded.Claim@, whose @support@ and
-- @holes@ are both @List Arg@).
--
-- __'statusC' never reads 'claimHoles'__ by design (Lean @statusC_gap_iff@, N17
-- point 1): the field is diagnostic-only, populated by
-- 'Lara.Reporting.reportClaimFor' and surfaced through
-- 'Lara.Reporting.incompleteAlternative', never by the status.
--
-- __Index-space caveat.__ 'claimSupport' holds complete-node (AF) indices;
-- 'claimHoles', when populated by "Lara.Reporting", holds raw-@unitArgs@
-- declaration indices ('Lara.Reporting.iaIndex'). The two are /different index
-- spaces/ sharing this @[Int]@ type (the Lean @Claim@ mirror keeps both as
-- @List Arg@). Only their (non)emptiness is ever consumed here and in the
-- diagnostic, so they never interact numerically; a consumer that needs to
-- resolve a hole back to its term must use the located
-- 'Lara.Reporting.IncompleteAlternative' values in
-- 'Lara.Reporting.crAlternatives', not do arithmetic on 'claimHoles'.
data Claim = Claim
  { claimSupport :: [Int]
  , claimHoles :: [Int]
  }
  deriving (Eq, Show)

-- | Four-state compiled claim status in spec §8 priority order (Lean
-- @statusC@): @gap@ on empty complete support; else @justified@ if some support
-- argument is @in@; else @contested@ if some is @undec@; else @defeated@.
statusC :: AF -> Claim -> Status
statusC f c
  | null (claimSupport c) = Gap
  | any (\a -> labelC f a == LIn) (claimSupport c) = Justified
  | any (\a -> labelC f a == LUndec) (claimSupport c) = Contested
  | otherwise = Defeated

-- ---------------------------------------------------------------------------
-- Computed complete-claim projection (Lean @Consistency.completeClaimFor@)
-- ---------------------------------------------------------------------------

-- | Declaration-order indices of retained complete checked nodes whose exact
-- conclusions are @≡ p@ (Lean @claimSupportFor@).
claimSupportFor :: [CheckedNode] -> Prop -> [Int]
claimSupportFor nodes p =
  [i | (node, i) <- zip nodes [0 ..], equiv (cnConclusion node) p]

-- | The complete-support projection for @p@ (Lean @completeClaimFor@). Its holes
-- are empty: the full @holes(P,p)@ computation is a later task (plan D7).
completeClaimFor :: [CheckedNode] -> Prop -> Claim
completeClaimFor nodes p =
  Claim {claimSupport = claimSupportFor nodes p, claimHoles = []}
