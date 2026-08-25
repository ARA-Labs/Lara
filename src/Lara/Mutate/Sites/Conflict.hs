-- | The attack-completeness site enumerator (#124): the one operator whose
-- specified outcome is @reject-MissingConflict@.
--
-- Every other attack-family operator corrupts a /declared/ attack and is caught
-- by the typed-attack stage. This one declares nothing wrong — it deletes an
-- attack the unit needs, so the unit is rejected only by the seventh stage's
-- completeness scan ('Lara.Check.firstMissingConflictInfo'). It is therefore the
-- only mutation operator that measures the scan, which is the executable witness
-- of the frozen attack-completeness theorem.
--
-- The enumerator mirrors the scan rather than approximating it: same conclusion
-- derivation, same attackability and coverage deciders, same source-major /
-- target-major search order. That is what lets it publish the /located/ ground
-- truth ('Lara.Diagnostics.CConflictPair') — the exact pair the checker will
-- report — instead of only the class.
--
-- __What the mirror reads.__ The checker does not run on the declared unit: it
-- runs on the §4.3 quarantine of it (@Lara.Driver.Internal@ checks
-- @pruneChecked pruned@, and 'Lara.Blocked.pruneWithPolicySeed' filters leaves,
-- arguments, /and/ attacks). This enumerator reads the declared
-- 'Lara.AST.unitArgs' \/ 'Lara.AST.unitAttacks' \/ 'Lara.AST.unitLeaves'
-- throughout, so the two agree only where the quarantine is the identity —
-- otherwise the published @si@\/@ti@ would be declared indices against a
-- verdict reported in checked indices, a silently wrong answer key rather than
-- a loud failure. Where they can disagree, the enumerator therefore yields no
-- sites at all ('quarantineIsIdentity'): fail closed, matching the choice
-- "Lara.Blocked" makes on the analogous uncertainty. No current mutation base
-- declares a @groups@ form, so the gate removes nothing today; issue #159
-- tracks lifting it by mapping the chosen attack back through the prune, which
-- is what would restore coverage on a quarantining base.
--
-- The enumerator keeps the ordering and self-gating invariants documented in
-- "Lara.Mutate.Sites".
module Lara.Mutate.Sites.Conflict
  ( dropCoveringAttackSites
  ) where

import Lara.AST
import Lara.Attack (contraryMatchB)
import Lara.Blocked (quarantineUnit)
import Lara.Check (resolveAttacks)
import Lara.Compile (conflictAttackableB, coveredB)
import Lara.Diagnostics (Constituent (..))
import Lara.Policy (lookupRule)
import Lara.Prop (Prop)
import Lara.SupportTerm (instAPat)

import Lara.Mutate (Expected (..))

-- | Missing conflict: delete one declared attack that is the sole cover of an
-- attackable contrary pair, leaving the completeness scan with an uncovered
-- pair.
--
-- Self-gating is two-sided. An attack is a site only if deleting it leaves an
-- uncovered pair (so the mutant really does reject at the scan), and only if the
-- base itself has none (so the reported pair is /caused by/ the deletion — the
-- ground truth would otherwise name a pair that was already uncovered). The
-- second condition holds for every mutation base by construction, since a base
-- with an uncovered pair would itself be rejected; it is asserted here so the
-- enumerator's contract is local rather than inherited.
--
-- The deletion cannot fail an earlier stage: stages 1–5 never read the attack
-- list, and the attacks that remain typed before still type. So the mutant's
-- outcome is exactly 'ExpectMissingConflict'.
dropCoveringAttackSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
dropCoveringAttackSites u
  | not (quarantineIsIdentity u) = [] -- mirror would read the wrong graph
  | Just _ <- firstUncovered (unitAttacks u) = [] -- base already incomplete
  | otherwise =
      [ ( ExpectMissingConflict
        , CConflictPair si ti
        , \u' -> u' {unitAttacks = dropIx i (unitAttacks u')}
        )
      | i <- [0 .. length (unitAttacks u) - 1]
      , Just (si, ti) <- [firstUncovered (dropIx i (unitAttacks u))]
      ]
  where
    pI = lookupRule (unitRules u)

    -- The scan's cache, in declaration order: index, term, conclusion. Empty
    -- (hence no sites) if any argument's conclusion is underivable — a unit the
    -- support stage would reject before the scan ever runs.
    nodes :: [(Int, SupportTerm, Prop)]
    nodes =
      maybe
        []
        id
        (traverse (\(i, (_, w)) -> (,,) i w <$> conclusionOf w) (zip [0 ..] (unitArgs u)))

    -- 'Lara.SupportTerm.inferSupport' derives exactly this conclusion for an
    -- accepted term: the leaf's proposition, or the rule's instantiated
    -- conclusion pattern.
    conclusionOf w = case w of
      SLeaf l -> lookup l (unitLeaves u)
      SRule rn theta _ _ _ _ -> pI rn >>= instAPat theta . ruleConclusion

    -- 'Lara.Check.firstMissingConflictInfo' over a candidate attack list, source
    -- major then target major, reporting the same first pair the checker would.
    firstUncovered atts =
      firstJust [firstJust [pairCheck resolved s t | t <- nodes] | s <- nodes]
      where
        resolved = resolveAttacks (unitArgs u) atts

    pairCheck atts (si, sw, sc) (ti, tw, tc)
      | contraryMatchB (unitContraries u) sc tc
      , conflictAttackableB pI tw
      , not (coveredB atts sw tw) =
          Just (si, ti)
      | otherwise = Nothing

    dropIx i xs = [x | (j, x) <- zip [0 :: Int ..] xs, j /= i]

    firstJust = foldr (\m acc -> maybe acc Just m) Nothing

-- | Does the §4.3 quarantine remove nothing from the three lists this
-- enumerator reads? When it does, the declared unit /is/ the checked one and
-- the published pair is the checker's; when it does not, indices would be drawn
-- from a different graph than the verdict names. Compares the two fields
-- 'Lara.Blocked.blockedQueries' compares for its own identity fast path, plus
-- 'unitLeaves' — which this enumerator reads directly in @conclusionOf@ and that
-- one does not. Deliberately not the whole 'Unit', so an unrelated field can
-- never spuriously close the gate; strictly stronger than the @blockedQueries@
-- test, which is the safe direction for a fail-closed guard.
quarantineIsIdentity :: Unit -> Bool
quarantineIsIdentity u =
  unitLeaves checked == unitLeaves u
    && unitArgs checked == unitArgs u
    && unitAttacks checked == unitAttacks u
  where
    checked = quarantineUnit u
