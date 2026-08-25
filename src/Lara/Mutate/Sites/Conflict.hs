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
-- arguments, /and/ attacks). So the mirror reads the checked unit too (#159):
-- the scan cache, the coverage decider, and the published @si@\/@ti@ are all in
-- checked index space, which is the space the verdict names. Only the
-- /deletion/ is mapped back through the prune
-- ('Lara.Blocked.retainedAttackIndices'), because the mutation edits the
-- declared attack list. That mapping is sound because attack deletion commutes
-- with the prune: 'Lara.Blocked.pruneWithPolicySeed' keeps or drops each attack
-- pointwise, by its endpoints against a kept-argument set no attack influences,
-- so deleting retained declared attack @d@ prunes to exactly the checked attack
-- list minus its entry @i@ — the candidate the mirror scanned. Deleting a
-- /pruned/ attack leaves the checked unit unchanged (an accepting no-op), which
-- is why only retained attacks are candidate sites.
--
-- Throughout, the prune in question is the group-only one
-- (@'Lara.Blocked.prune' = 'Lara.Blocked.pruneWithPolicySeed' []@), which is
-- the one the raw\/mutation path builds; a policy-seeded source prune
-- ('Lara.Elaborate.prepareSource') is out of scope, because mutation bases are
-- checked through 'Lara.Driver.runCheck'.
--
-- The enumerator keeps the ordering and self-gating invariants documented in
-- "Lara.Mutate.Sites".
module Lara.Mutate.Sites.Conflict
  ( dropCoveringAttackSites
  ) where

import Lara.AST
import Lara.Attack (contraryMatchB)
import Lara.Blocked (prune, pruneChecked)
import Lara.Check (resolveAttacks)
import Lara.Compile (conflictAttackableB, coveredB)
import Lara.Diagnostics (Constituent (..))
import Lara.Driver (groupConflictReject)
import Lara.Policy (lookupRule)
import Lara.Prop (Prop)
import Lara.SupportTerm (instAPat)

import Lara.Mutate (Expected (..))
import Lara.Mutate.Sites.Nav (CheckedIx (..), attackSites, dropAttackAt)

-- | Missing conflict: delete one declared attack that is the sole cover of an
-- attackable contrary pair, leaving the completeness scan with an uncovered
-- pair.
--
-- Self-gating is three-sided. An attack is a site only if the base does not
-- escalate a group conflict to R9 (the driver rejects before the scan ever
-- runs, so the mutant could not reject at the scan), only if deleting it leaves
-- the checked unit with an uncovered pair (so the mutant really does reject at
-- the scan), and only if the checked base itself has none (so the reported pair
-- is /caused by/ the deletion — the ground truth would otherwise name a pair
-- that was already uncovered).
--
-- The first and third gates hold for every accepted mutation base by
-- construction (an R9 base is rejected before the scan; a base with an
-- uncovered pair is rejected by it); they are asserted here so the
-- enumerator's contract is local rather than inherited. The second is the site
-- predicate itself — it is false for most attacks of an accepted base, and
-- dropping it would turn the enumerator into an unconditional generator.
--
-- The deletion cannot fail an earlier stage: stages 1–5 never read the attack
-- list, and the checked attacks that remain typed before still type. So the
-- mutant's outcome is exactly 'ExpectMissingConflict'.
dropCoveringAttackSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
dropCoveringAttackSites u
  | groupConflictReject u = [] -- base escalates to R9 before the scan
  | Just _ <- firstUncovered checkedAttacks = [] -- base already incomplete
  | otherwise =
      [ ( ExpectMissingConflict
        , CConflictPair si ti
        , dropAttackAt di
        )
      | (ci, di, _) <- attackSites pruned
      , Just (si, ti) <- [firstUncovered (dropIx (checkedIx ci) checkedAttacks)]
      ]
  where
    pruned = prune u
    checked = pruneChecked pruned
    checkedAttacks = unitAttacks checked

    pI = lookupRule (unitRules checked)

    -- The scan's cache, in checked declaration order: index, term, conclusion.
    -- Empty (hence no sites) if any argument's conclusion is underivable — a
    -- unit the support stage would reject before the scan ever runs.
    nodes :: [(Int, SupportTerm, Prop)]
    nodes =
      maybe
        []
        id
        (traverse (\(i, (_, w)) -> (,,) i w <$> conclusionOf w) (zip [0 ..] (unitArgs checked)))

    -- 'Lara.SupportTerm.inferSupport' derives exactly this conclusion for an
    -- accepted term: the leaf's proposition, or the rule's instantiated
    -- conclusion pattern.
    conclusionOf w = case w of
      SLeaf l -> lookup l (unitLeaves checked)
      SRule rn theta _ _ _ _ -> pI rn >>= instAPat theta . ruleConclusion

    -- 'Lara.Check.firstMissingConflictInfo' over a candidate checked attack
    -- list, source major then target major, reporting the same first pair the
    -- checker would.
    firstUncovered atts =
      firstJust [firstJust [pairCheck resolved s t | t <- nodes] | s <- nodes]
      where
        resolved = resolveAttacks (unitArgs checked) atts

    pairCheck atts (si, sw, sc) (ti, tw, tc)
      | contraryMatchB (unitContraries checked) sc tc
      , conflictAttackableB pI tw
      , not (coveredB atts sw tw) =
          Just (si, ti)
      | otherwise = Nothing

    dropIx i xs = [x | (j, x) <- zip [0 :: Int ..] xs, j /= i]

    firstJust = foldr (\m acc -> maybe acc Just m) Nothing
