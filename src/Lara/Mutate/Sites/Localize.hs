-- | The localization site enumerators (#123): the discriminating families of
-- @docs\/localization-metric-decision.md@ — mutants whose ground truth is a
-- genuine prediction rather than an echo of the edit site.
--
-- Every other rejection enumerator publishes the constituent it edits, so its
-- @location_match@ holds by construction. The three families here are the ones
-- that make the metric falsifiable:
--
-- * 'retractRuleSites' is __off-site__: the edit removes a declared rule from
--   the policy, but the manifestation is at the checked argument(s) whose
--   support instantiates it — publishing 'Lara.Diagnostics.CPolicy' would
--   guarantee a miss and measure nothing. The published list is the full
--   manifestation set, ascending in checked index; its head is the argument
--   the support stage reaches first, which is the constituent a
--   spec-conformant checker reports.
--
-- * 'twinSupportDefectSites' is __multi-defect within one stage__: two
--   wrong-premise defects at two distinct arguments. Support checks arguments
--   in checked declaration order, so the head is the pair's lower checked
--   index — declaration-index order, not accident, chooses the report.
--
-- * 'crossStageDefectSites' is __multi-defect across stages__: a wrong-premise
--   defect (support, stage 5) composed with a bad-attack-position defect
--   (typed attacks, stage 6). The head is the argument constituent regardless
--   of the indices involved, because the stage order is fixed.
--
-- The composite enumerators reuse "Lara.Mutate.Sites"'s single-site
-- enumerators, so every tail element inherits the component's own checker
-- gate; @test\/MutationSpec.hs@'s @prop_localizationSites@ pins the composite
-- lists to the component outputs and the retraction manifestation set to the
-- mutated unit itself.
--
-- The enumerators keep the "Lara.Mutate.Sites" invariants: output order is
-- load-bearing, an inapplicable base yields @[]@, and published indices are in
-- checked space ("Lara.Mutate.Sites.Nav"). Like "Lara.Mutate.Sorts", this
-- module is not re-exported through "Lara.Mutate.Sites" —
-- 'Lara.Mutate.Suite' imports it directly — because it imports that module
-- for its components and a re-export would cycle.
module Lara.Mutate.Sites.Localize
  ( retractRuleSites
  , twinSupportDefectSites
  , crossStageDefectSites
  ) where

import Data.List (tails)
import Data.Maybe (isNothing)

import Lara.AST
import Lara.Blocked (prune)
import Lara.Diagnostics (Constituent (..))
import Lara.Policy (firstViolation)
import Lara.Sigma.WellSorted (unitSortError)

import Lara.Mutate (Expected (..))
import Lara.Mutate.Sites (badAttackPositionSites, wrongPremiseSites)
import Lara.Mutate.Sites.Nav (CheckedIx (..), ruleSites)

-- | R1, off the edit site: retract one declared rule that at least one
-- checked argument instantiates. The rewrite edits only the policy — policy
-- material survives quarantine untouched, so no index mapping arises — and
-- the ground truth is the manifestation set: every checked argument carrying
-- an instance of the retracted rule (nested occurrences included), ascending
-- in checked index. The support stage reaches the head first and fails its
-- rule lookup there; an undeclared rule id is R1's business by the spec §10.1
-- class boundary ("Lara.Sigma.WellSorted" skips unresolved instances, so the
-- defect cannot leak into stage 2).
--
-- Self-gates: a rule instantiated only by pruned arguments is skipped (its
-- retraction is an accepting no-op), and so is a rule whose removal breaks a
-- stage the support stage hides behind — the mutated unit must keep
-- 'unitSortError' and 'firstViolation' clean, or the mutant would reject
-- before support at 'CPolicy' and the prediction would be wrong.
retractRuleSites :: Unit -> [(Expected, [Constituent], Unit -> Unit)]
retractRuleSites u =
  [ ( ExpectClass R1
    , [CArgument (checkedIx ci) | ci <- affected]
    , dropRule rid
    )
  | r <- unitRules u
  , let rid = ruleId r
  , let affected =
          ascendingNub
            [ci | (ci, _, _, SRule rid' _ _ _ _ _) <- ruleSites pruned, rid' == rid]
  , not (null affected)
  , policyStaysClean (dropRule rid u)
  ]
  where
    pruned = prune u
    dropRule rid u' = u' {unitRules = [rl | rl <- unitRules u', ruleId rl /= rid]}
    policyStaysClean u' =
      isNothing (unitSortError u')
        && isNothing (firstViolation (unitRules u') (unitContraries u') (unitExceptions u'))

-- | R4 at the stage-order-first of two defective arguments: every ordered
-- pair of 'wrongPremiseSites' proposals at distinct constituents, composed
-- into one mutant. 'wrongPremiseSites' enumerates the checked arguments in
-- checked order, so the earlier component's constituent is the pair's lower
-- checked index and therefore the head — the support stage checks arguments
-- in that order and reports the first failure. The two rewrites edit distinct
-- declared arguments, so their composition is order-independent; they are
-- composed in the fixed pair order regardless. The component's @R4@ class is
-- bound in the pattern, so a component-class drift empties the enumerator —
-- caught by the anti-vacuity gate — instead of mislabeling the composite.
twinSupportDefectSites :: Unit -> [(Expected, [Constituent], Unit -> Unit)]
twinSupportDefectSites u =
  [ (ExpectClass R4, [ci, cj], mutJ . mutI)
  | (ExpectClass R4, ci, mutI) : later <- tails (wrongPremiseSites u)
  , (ExpectClass R4, cj, mutJ) <- later
  , ci /= cj
  ]

-- | R4 across a stage boundary: a wrong-premise defect composed with a
-- bad-attack-position defect. The head is the argument constituent no matter
-- how the indices compare — support (stage 5) precedes typed attacks
-- (stage 6), so the attack defect is unreachable while the premise defect
-- stands. The premise rewrite edits an argument term and the attack rewrite
-- an attack entry, so the composition is order-independent; the premise
-- rewrite is applied first regardless. The components' @R4@\/@R10@ classes are
-- bound in the patterns, so a component-class drift empties the enumerator —
-- caught by the anti-vacuity gate — instead of mislabeling the composite.
crossStageDefectSites :: Unit -> [(Expected, [Constituent], Unit -> Unit)]
crossStageDefectSites u =
  [ (ExpectClass R4, [cp, ca], mutA . mutP)
  | (ExpectClass R4, cp, mutP) <- wrongPremiseSites u
  , (ExpectClass R10, ca, mutA) <- badAttackPositionSites u
  ]

-- | Collapse adjacent duplicates. Sufficient here because 'ruleSites' is
-- checked-argument-major: equal checked indices are adjacent, so the result
-- is strictly ascending whenever the input is weakly ascending.
ascendingNub :: [CheckedIx] -> [CheckedIx]
ascendingNub (x : y : rest)
  | x == y = ascendingNub (y : rest)
  | otherwise = x : ascendingNub (y : rest)
ascendingNub xs = xs
