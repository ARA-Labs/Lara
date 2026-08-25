-- | Conformance tests for conservative reporting of quarantine-affected claims
-- ("Lara.Blocked", spec §4.3, issue #76).
--
-- The metatheory is mechanized in @lean\/Lara\/Blocked.lean@ over an arbitrary
-- pair of finite frameworks. The random properties instantiate that abstract
-- theorem directly; the real-unit properties pin the drivers' seed obligations.
-- The compact checked-program reindexing/support bridge is mechanized by
-- @production_justified_nonpromotion_of_not_blocked@ (issue #80); the corpus
-- differential remains cross-implementation conformance evidence:
--
--   * __The safety property, executably.__ Over random frameworks with a random
--     subset of arguments deleted, every unblocked argument keeps its label —
--     Lean @labelC_agree@, and with it @justified_nonpromotion@. This is the
--     property whose absence was the bug: without blocking, deleting an
--     attacker silently promotes its target.
--   * __The closure contract.__ 'blockedSet' contains the seed and is closed
--     under declared attack edges — Lean @seed_subset_blocked@ and
--     @blocked_closed@, the two facts @blocking_of_seed@ needs.
--   * __The seed obligations.__ On real units, the seed really does cover every
--     removed argument and every retained argument that lost an incoming edge —
--     Lean @blocking_of_seed@'s @hmissing@ and @hedge@ hypotheses.
--   * __No quarantine, no cost.__ A unit with no @≢@ group blocks nothing, so
--     every frozen artifact keeps its pre-#76 verdict bytes exactly.
module BlockedSpec (blockedSpecProps) where

import qualified Data.Set as Set
import Test.QuickCheck

import Lara.AST
  ( ArgId (..)
  , GroupConflictMode (..)
  , LeafId (..)
  , SupportTerm (..)
  , Unit (..)
  )
import Lara.Blocked
  ( blockedQueries
  , blockedSeed
  , blockedSet
  , declaredEdge
  , prune
  , pruneWithPolicySeed
  , pruneChecked
  , pruneDeclared
  , retainedAttackIndices
  , retainedEdge
  , retainedIndices
  )
import Lara.Check (checkUnit, cuNodes)
import Lara.Driver (buildCertOk, buildGamma)
import Lara.Grounded (AF (..), claimSupportFor, labelC)
import Lara.Prop (Pred (..), Prop (..))

import CheckSpec (quarantineFixtures, unquarantinedFixtures)
import SigmaFixture (sigmaOf)

-- ---------------------------------------------------------------------------
-- Random frameworks: the safety property, executably
-- ---------------------------------------------------------------------------

-- | A small random framework plus a random retained subset of its arguments —
-- the shape of a §4.3 prune before any leaf or policy detail enters.
data Deletion = Deletion
  { delSize :: Int
  , delEdges :: [(Int, Int)]
  , delRetained :: [Int]
  }
  deriving (Show)

instance Arbitrary Deletion where
  arbitrary = do
    n <- choose (1, 7)
    let ixs = [0 .. n - 1]
    edges <- sublistOf [(i, j) | i <- ixs, j <- ixs]
    retained <- sublistOf ixs
    pure (Deletion n edges retained)

declaredOf :: Deletion -> AF
declaredOf d =
  AF
    { afArgs = [0 .. delSize d - 1]
    , afAttack = \i j -> (i, j) `elem` delEdges d
    }

-- | The checked framework: the same edge relation on the retained carrier —
-- the shape Lean's @Blocking.args_sub@ demands: a sub-carrier, not a
-- renumbering.
checkedOf :: Deletion -> AF
checkedOf d = (declaredOf d) {afArgs = delRetained d}

blockedOf :: Deletion -> Set.Set Int
blockedOf d =
  blockedSet
    (afArgs (declaredOf d))
    (afAttack (declaredOf d))
    [i | i <- afArgs (declaredOf d), i `notElem` delRetained d]

-- | __The safety property (Lean @labelC_agree@).__ Deleting arguments cannot
-- change the label of an unblocked argument — in either direction. Every way
-- the prune could have inflated (or deflated) a claim is therefore either
-- impossible or reported as @evidence-blocked@.
prop_unblockedLabelsAgree :: Deletion -> Property
prop_unblockedLabelsAgree d =
  conjoin
    [ counterexample
        ("argument " ++ show a ++ " is unblocked but its label moved")
        (labelC (checkedOf d) a === labelC (declaredOf d) a)
    | a <- delRetained d
    , not (Set.member a (blockedOf d))
    ]

-- | The hazard itself: whenever deletion /does/ move a label, that argument is
-- blocked. The contrapositive of 'prop_unblockedLabelsAgree', stated the way the
-- bug report reads.
prop_movedLabelsAreBlocked :: Deletion -> Property
prop_movedLabelsAreBlocked d =
  -- The coverage check keeps this honest: if generated deletions stopped moving
  -- any label, both this property and 'prop_unblockedLabelsAgree' would pass
  -- vacuously and the suite would no longer exercise the hazard at all.
  checkCoverage $
    cover 10 (not (null moved)) "a deletion moved some label" $
      conjoin
        [ counterexample
            ("argument " ++ show a ++ " changed label but was published")
            (Set.member a (blockedOf d))
        | a <- moved
        ]
  where
    moved =
      [ a
      | a <- delRetained d
      , labelC (checkedOf d) a /= labelC (declaredOf d) a
      ]

-- | __The closure contract (Lean @seed_subset_blocked@ + @blocked_closed@).__
prop_closureContract :: Deletion -> Property
prop_closureContract d =
  conjoin
    [ counterexample "seed ⊆ blocked" $
        conjoin
          [ counterexample (show x) (Set.member x blocked)
          | x <- afArgs g
          , x `notElem` delRetained d
          ]
    , counterexample "blocked is closed under declared attack edges" $
        conjoin
          [ counterexample (show (x, y)) (Set.member y blocked)
          | x <- Set.toList blocked
          , y <- afArgs g
          , afAttack g x y
          ]
    ]
  where
    g = declaredOf d
    blocked = blockedOf d

-- | Tightness of the directed rule, checked against an independent bounded
-- reachability specification. The closure-contract property above proves only
-- that the result is large enough; an accidental undirected-component closure
-- would still pass it. This equality also proves it is no larger than forward
-- reachability, and the coverage obligation ensures generated cases contain a
-- reverse-only node that such an overblocking mutation would incorrectly add.
prop_directedBlockingTight :: Deletion -> Property
prop_directedBlockingTight d =
  checkCoverage $
    cover 10 (not (null reverseOnly)) "reverse-only node must remain published" $
      counterexample
        ("directed=" ++ show (Set.toList expected) ++ ", got=" ++ show (Set.toList actual))
        (actual === expected)
  where
    g = declaredOf d
    seed = Set.fromList [i | i <- afArgs g, i `notElem` delRetained d]
    forwardStep reached =
      Set.union reached $
        Set.fromList
          [ y
          | x <- Set.toList reached
          , y <- afArgs g
          , afAttack g x y
          ]
    backwardStep reached =
      Set.union reached $
        Set.fromList
          [ x
          | x <- afArgs g
          , y <- Set.toList reached
          , afAttack g x y
          ]
    expected = iterate forwardStep seed !! delSize d
    backward = iterate backwardStep seed !! delSize d
    actual = blockedOf d
    reverseOnly = Set.toList (backward `Set.difference` expected)

-- ---------------------------------------------------------------------------
-- Real units: the seed obligations
-- ---------------------------------------------------------------------------

-- | 'Lara.Blocked.blockedSeed' discharges Lean @blocking_of_seed@'s hypotheses
-- on a real declared\/checked unit pair: the retained indices are declared
-- indices (@hargs@), every removed argument is seeded (@hmissing@), and every
-- retained argument that lost an incoming edge is seeded (@hedge@).
seedObligations :: String -> Unit -> Property
seedObligations name declared =
  conjoin
    [ counterexample (name ++ ": retained ⊆ declared (hargs)") $
        conjoin [counterexample (show i) (property (i < declaredCount)) | i <- retained]
    , counterexample (name ++ ": every removed argument is seeded (hmissing)") $
        conjoin
          [ counterexample (show i) (property (i `elem` seed))
          | i <- [0 .. declaredCount - 1]
          , i `notElem` retained
          ]
    , -- Lean's @hedge@ is an equality, so both directions are asserted: a lost
      -- edge must be seeded, and the prune must never /gain/ one.
      counterexample (name ++ ": unseeded retained arguments kept their edges (hedge)") $
        conjoin
          [ counterexample (show (i, j)) (declaredEdge p i j === retainedEdge p i j)
          | j <- retained
          , j `notElem` seed
          , i <- retained
          ]
    , counterexample (name ++ ": the prune never gains an edge") $
        conjoin
          [ counterexample (show (i, j)) (property (declaredEdge p i j))
          | j <- retained
          , i <- retained
          , retainedEdge p i j
          ]
    ]
  where
    p = prune declared
    declaredCount = length (unitArgs (pruneDeclared p))
    retained = retainedIndices p
    seed = blockedSeed p

-- | A unit with no @≢@ duplicate-report group prunes nothing, so nothing is
-- blocked and its verdict bytes are exactly the pre-#76 ones. Every frozen
-- artifact is in this case.
noQuarantineNothingBlocked :: String -> Unit -> Property
noQuarantineNothingBlocked name declared =
  counterexample (name ++ ": unquarantined unit blocks nothing") $
    case checkUnit (buildGamma (unitLeaves checked)) (buildCertOk (unitTheories checked)) checked of
      Left _ -> property True -- a rejected unit prints no statuses at all
      Right accepted ->
        blockedQueries p (cuNodes accepted) (unitQueries declared) === []
  where
    p = prune declared
    checked = pruneChecked p

-- | Blocking is support-driven: a blocked query always has a non-empty complete
-- support set, so blocking never fires on a @gap@ claim. That matters because
-- @gap@ is the intended §4.3 outcome when a claim's /own/ support is
-- quarantined — losing support cannot promote a claim, so those claims must
-- keep reporting @gap@ rather than being blocked.
blockedQueriesAreSupported :: String -> Unit -> Property
blockedQueriesAreSupported name declared =
  case checkUnit (buildGamma (unitLeaves checked)) (buildCertOk (unitTheories checked)) checked of
    Left _ -> property True
    Right accepted ->
      conjoin
        [ counterexample
            (name ++ ": blocked query " ++ show q ++ " has no complete support")
            (property (not (null (claimSupportFor (cuNodes accepted) q))))
        | q <- blockedQueries p (cuNodes accepted) queries
        ]
  where
    p = prune declared
    checked = pruneChecked p
    queries = unitQueries declared

blockedSpecProps :: [(String, IO Result)]
blockedSpecProps =
  [ ("blocked unblocked labels agree (Lean labelC_agree)", quickCheckResult prop_unblockedLabelsAgree)
  , ("blocked moved labels are blocked", quickCheckResult prop_movedLabelsAreBlocked)
  , ("blocked closure contains seed and is edge-closed", quickCheckResult prop_closureContract)
  , ("blocked closure is tight directed reachability", quickCheckResult prop_directedBlockingTight)
  , ("blocked seed obligations on real units", quickCheckResult prop_seedObligations)
  , ("blocked unquarantined units block nothing", quickCheckResult prop_noQuarantine)
  , ("blocked queries are support-driven", quickCheckResult prop_blockedSupported)
  , ("blocked prune accepts an explicit policy seed", quickCheckResult prop_explicitPolicySeed)
  , ("blocked retained attack indices project the checked attack list", quickCheckResult prop_retainedAttackIndices)
  ]

-- | 'retainedAttackIndices' is the attack counterpart of 'retainedIndices'
-- (#159): indexing the declared attack list by it reproduces the checked attack
-- list exactly, order and multiplicity included. This is the contract
-- "Lara.Mutate.Sites.Conflict" leans on to map a checked-space deletion back to
-- the declared attack it must remove.
--
-- The projection equation alone is satisfied by the wrong implementation
-- @[0 .. length (unitAttacks (pruneChecked p)) - 1]@ — checked-space indices,
-- the exact confusion #159 exists to prevent — on any fixture whose retained
-- list is @[]@ or @[0 .. n-1]@, which is every group fixture taken alone. The
-- discriminating case is 'CheckSpec.quarantiningConflictBase': two declared
-- attacks, the /pruned/ one first, so the retained list is @[1]@ — non-empty,
-- non-zero, and gapped. The seeded prune is covered too, since
-- 'pruneWithPolicySeed' is otherwise exercised only by 'prop_explicitPolicySeed'.
prop_retainedAttackIndices :: Property
prop_retainedAttackIndices =
  once $
    conjoin
      ( [ counterexample (name ++ ": projected declared attacks differ from checked attacks") $
            map (unitAttacks (pruneDeclared p) !!) (retainedAttackIndices p)
              === unitAttacks (pruneChecked p)
        | (name, p) <- prunesUnderTest
        ]
          ++ [ counterexample "no fixture has a gapped retained-attack list — the property is vacuous" $
                 any (\(_, p) -> isGapped (retainedAttackIndices p)) prunesUnderTest
             ]
      )
  where
    prunesUnderTest =
      [(name, prune unit) | (name, unit) <- quarantineFixtures ++ unquarantinedFixtures]
        ++ [("policy-seed", pruneWithPolicySeed [LeafId "policy"] policySeedUnit)]

    -- Anything other than [] or [0 .. n-1] — i.e. an index the checked-space
    -- misimplementation would get wrong.
    isGapped ix = ix /= [0 .. length ix - 1]

-- The unit-level properties run over the in-memory "CheckSpec" quarantine
-- fixtures. Separate corpus and generated-mutant fixtures exercise the shipped
-- differential and mutation paths.
prop_seedObligations :: Property
prop_seedObligations = once (conjoin [seedObligations n u | (n, u) <- quarantineFixtures])

prop_noQuarantine :: Property
prop_noQuarantine =
  once (conjoin [noQuarantineNothingBlocked n u | (n, u) <- unquarantinedFixtures])

prop_blockedSupported :: Property
prop_blockedSupported =
  once (conjoin [blockedQueriesAreSupported n u | (n, u) <- quarantineFixtures])

-- | Policy quarantine enters the same 'Prune' carrier as group quarantine.
-- With no groups at all, the explicit seed alone removes its leaf and every
-- dependent argument while retaining declaration order in both projections.
prop_explicitPolicySeed :: Property
prop_explicitPolicySeed =
  once $
    let checked = pruneChecked (pruneWithPolicySeed [LeafId "policy"] policySeedUnit)
     in conjoin
          [ unitLeaves checked === [(LeafId "kept", Prop (Pred "kept") [])]
          , unitArgs checked === [(ArgId "a_kept", SLeaf (LeafId "kept"))]
          ]

policySeedUnit :: Unit
policySeedUnit =
  Unit
    { unitSigma = sigmaOf [] [] [("policy", []), ("kept", [])]
    , unitRules = []
    , unitContraries = []
    , unitExceptions = []
    , unitTheories = []
    , unitLeaves =
        [ (LeafId "policy", Prop (Pred "policy") [])
        , (LeafId "kept", Prop (Pred "kept") [])
        ]
    , unitArgs =
        [ (ArgId "a_policy", SLeaf (LeafId "policy"))
        , (ArgId "a_kept", SLeaf (LeafId "kept"))
        ]
    , unitAttacks = []
    , unitQueries = []
    , unitGroups = []
    , unitGroupMode = QuarantineOnConflict
    }
