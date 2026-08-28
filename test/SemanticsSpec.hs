-- | Conformance tests for "Lara.Semantics", the Haskell mirror of the
-- enumeration half of @lean\/Lara\/Semantics.lean@.
--
-- __Lean is the oracle.__ Every expected value in 'leanGoldens' was computed by
-- Lean and emitted already formatted as the Haskell literal below. Verify the
-- checked-in block with
--
-- > make semantics-goldens
--
-- and regenerate it with
-- @cd lean && lake env lean --run SemanticsGoldens.lean@. The emitter is
-- @haskellGoldens@ in
-- @lean\/Lara\/Examples\/Semantics.lean@; it reads each cell through the same
-- @semanticsInstance@ \/ @frameworkAF@ tables the observation table uses, so a
-- golden row cannot name one instance and evaluate another.
--
-- __This is conformance evidence, not soundness.__ Per @CLAUDE.md@: \"Haskell
-- property tests are conformance evidence, not soundness; the Lean proofs carry
-- soundness.\" The golden table checks that the two implementations produce the
-- same ordered lists on six small frameworks. A separate generated property
-- checks the Haskell grounded enumerator against the pre-existing grounded
-- fixpoint on small arbitrary frameworks. The adequacy of the deciders — that
-- @completeB@ decides @Complete@, and so on — is proved only in Lean, and no
-- amount of agreement here substitutes for it. The goldens are transcribed, so
-- a stale paste is a real failure mode; the @semantics-goldens@ gate regenerates
-- them from Lean and diffs the block below, while 'prop_goldensCoverProduct'
-- catches a dropped or duplicated row inside the Haskell suite.
--
-- The frameworks below are hand-copies of the six observation-table @AF@
-- values in @lean\/Lara\/Examples\/Semantics.lean@ (@threeCycle@,
-- @threeCycleAttacked@, @twoCycle@, @twoCycleSink@, @rangeSplit@,
-- @reinstatementChain@). That file defines a seventh, @dupCarrier@, which is the
-- duplicate-carrier witness for representative uniqueness and is deliberately
-- not mirrored here. They are duplicated rather than derived because the Lean
-- definitions are not reachable from Haskell; a mistranscribed edge would show
-- up as a golden mismatch, since the goldens come from the Lean side of the
-- same pair.
module SemanticsSpec (semanticsSpecProps) where

import Data.List (sort)
import Test.QuickCheck

import Lara.Grounded (AF (..), grounded)
import Lara.Semantics
  ( admissibleB
  , boundedB
  , candidates
  , enumerateComplete
  , enumerateGrounded
  , enumeratePreferred
  , enumerateSemiStable
  , enumerateStable
  , stableB
  )
import TestAF (genAF, naiveAF)

-- ---------------------------------------------------------------------------
-- The six example frameworks (mirrors of lean/Lara/Examples/Semantics.lean)
-- ---------------------------------------------------------------------------

-- | The bare three-cycle @0 → 1 → 2 → 0@ (Lean @threeCycle@).
threeCycle :: AF
threeCycle =
  AF
    { afArgs = [0, 1, 2]
    , afAttack = \a b -> (a, b) `elem` [(0, 1), (1, 2), (2, 0)]
    }

-- | The three-cycle plus a fourth argument attacking all of @0,1,2@ (Lean
-- @threeCycleAttacked@).
threeCycleAttacked :: AF
threeCycleAttacked =
  AF
    { afArgs = [0, 1, 2, 3]
    , afAttack = \a b ->
        (a, b) `elem` [(0, 1), (1, 2), (2, 0), (3, 0), (3, 1), (3, 2)]
    }

-- | The two-cycle @0 ↔ 1@ (Lean @twoCycle@).
twoCycle :: AF
twoCycle =
  AF
    { afArgs = [0, 1]
    , afAttack = \a b -> (a, b) `elem` [(0, 1), (1, 0)]
    }

-- | The two-cycle plus a sink @2@ attacked by both (Lean @twoCycleSink@).
twoCycleSink :: AF
twoCycleSink =
  AF
    { afArgs = [0, 1, 2]
    , afAttack = \a b -> (a, b) `elem` [(0, 1), (1, 0), (0, 2), (1, 2)]
    }

-- | The two-cycle extended by a self-attacking @2@ that @1@ attacks (Lean
-- @rangeSplit@).
rangeSplit :: AF
rangeSplit =
  AF
    { afArgs = [0, 1, 2]
    , afAttack = \a b -> (a, b) `elem` [(0, 1), (1, 0), (1, 2), (2, 2)]
    }

-- | The reinstatement chain @0 → 1 → 2@ (Lean @reinstatementChain@). Its
-- two-element extension forces the deciders to include an argument defended by
-- another extension member.
reinstatementChain :: AF
reinstatementChain =
  AF
    { afArgs = [0, 1, 2]
    , afAttack = \a b -> (a, b) `elem` [(0, 1), (1, 2)]
    }

-- | Framework lookup by the label the Lean emitter prints (Lean
-- @frameworkLabel@ \/ @frameworkAF@).
frameworkByName :: String -> Maybe AF
frameworkByName name = lookup name frameworks

-- | The framework axis, in the Lean @allFrameworks@ order.
frameworks :: [(String, AF)]
frameworks =
  [ ("threeCycle", threeCycle)
  , ("threeCycleAttacked", threeCycleAttacked)
  , ("twoCycle", twoCycle)
  , ("twoCycleSink", twoCycleSink)
  , ("rangeSplit", rangeSplit)
  , ("reinstatementChain", reinstatementChain)
  ]

-- | The semantics axis, in the Lean @allSemantics@ order, under the labels
-- Lean's @semanticsLabel@ prints.
semantics :: [(String, AF -> [[Int]])]
semantics =
  [ ("grounded", enumerateGrounded)
  , ("complete", enumerateComplete)
  , ("preferred", enumeratePreferred)
  , ("stable", enumerateStable)
  , ("semiStable", enumerateSemiStable)
  ]

-- | Semantics lookup by the label the Lean emitter prints.
semanticsByName :: String -> Maybe (AF -> [[Int]])
semanticsByName name = lookup name semantics

-- ---------------------------------------------------------------------------
-- The Lean-derived goldens
--
-- Verify with: make semantics-goldens
-- Regenerate with: cd lean && lake env lean --run SemanticsGoldens.lean
-- ---------------------------------------------------------------------------

leanGoldens :: [(String, String, [[Int]])]
leanGoldens =
  [ ("threeCycle", "grounded", [[]])
  , ("threeCycle", "complete", [[]])
  , ("threeCycle", "preferred", [[]])
  , ("threeCycle", "stable", [])
  , ("threeCycle", "semiStable", [[]])
  , ("threeCycleAttacked", "grounded", [[3]])
  , ("threeCycleAttacked", "complete", [[3]])
  , ("threeCycleAttacked", "preferred", [[3]])
  , ("threeCycleAttacked", "stable", [[3]])
  , ("threeCycleAttacked", "semiStable", [[3]])
  , ("twoCycle", "grounded", [[]])
  , ("twoCycle", "complete", [[],[0],[1]])
  , ("twoCycle", "preferred", [[0],[1]])
  , ("twoCycle", "stable", [[0],[1]])
  , ("twoCycle", "semiStable", [[0],[1]])
  , ("twoCycleSink", "grounded", [[]])
  , ("twoCycleSink", "complete", [[],[0],[1]])
  , ("twoCycleSink", "preferred", [[0],[1]])
  , ("twoCycleSink", "stable", [[0],[1]])
  , ("twoCycleSink", "semiStable", [[0],[1]])
  , ("rangeSplit", "grounded", [[]])
  , ("rangeSplit", "complete", [[],[0],[1]])
  , ("rangeSplit", "preferred", [[0],[1]])
  , ("rangeSplit", "stable", [[1]])
  , ("rangeSplit", "semiStable", [[1]])
  , ("reinstatementChain", "grounded", [[0,2]])
  , ("reinstatementChain", "complete", [[0,2]])
  , ("reinstatementChain", "preferred", [[0,2]])
  , ("reinstatementChain", "stable", [[0,2]])
  , ("reinstatementChain", "semiStable", [[0,2]])
  ]

-- ---------------------------------------------------------------------------
-- Properties
-- ---------------------------------------------------------------------------

-- | Every golden row is reproduced exactly by the Haskell enumeration —
-- including the order of the entries and the order within each entry, not just
-- the sets they denote. Both sides derive their layout from the same
-- \"drop it \/ keep it\" recursion (Lean @subseqs@, Haskell 'Lara.Semantics.subseqs'),
-- so list equality is the sharper check and it is the one made here.
prop_goldensMatch :: Property
prop_goldensMatch =
  once $
    conjoin
      [ counterexample (label' fname sname) (check fname sname expected)
      | (fname, sname, expected) <- leanGoldens
      ]
  where
    label' fname sname = fname ++ " / " ++ sname
    check fname sname expected =
      case (frameworkByName fname, semanticsByName sname) of
        (Just f, Just enumerate) ->
          counterexample
            ("expected " ++ show expected ++ " but got " ++ show (enumerate f))
            (enumerate f == expected)
        _ -> counterexample "unknown framework or semantics label" False

-- | The golden table is exactly the product of the two axes, once each. A
-- transcription that drops, duplicates, or renames a row fails here rather than
-- passing vacuously in 'prop_goldensMatch', whose quantifier ranges over the
-- rows that are present.
prop_goldensCoverProduct :: Property
prop_goldensCoverProduct =
  once $
    property $
      sort [(fname, sname) | (fname, sname, _) <- leanGoldens]
        == sort [(fname, sname) | (fname, _) <- frameworks, (sname, _) <- semantics]

-- | The grounded enumeration is a one-element list whose entry has exactly the
-- members of 'Lara.Grounded.grounded'. This is the Haskell-side instance of Lean
-- @groundedSem_enumerate@ \/ @groundedSem_singleton@ over generated
-- duplicate-free carriers. Members are compared as sorted lists because the two
-- computations lay a set out differently: 'enumerateGrounded' returns a carrier
-- sublist, while 'grounded' returns the carrier filtered by the fixpoint. The
-- six-argument cap keeps the powerset scan at no more than 64 candidates.
prop_groundedSingleton :: Property
prop_groundedSingleton =
  checkCoverage $
    forAll (resize 6 genAF) $ \(n, edges) ->
      cover 20 (n >= 5) "5+ arguments" $
        let f = naiveAF n edges
         in counterexample (show (n, edges)) $
              case enumerateGrounded f of
                [e] -> property (sort e == sort (grounded f))
                other -> counterexample ("not a singleton: " ++ show other) (property False)

-- | Sets containing an argument outside the carrier fail the carrier bound and
-- every base decider that includes it. Generated frameworks choose the first
-- integer beyond @[0..n-1]@ as the outsider, an input shape 'candidates' cannot
-- produce and therefore cannot cover indirectly through enumeration goldens.
prop_carrierBoundRejectsOutsiders :: Property
prop_carrierBoundRejectsOutsiders =
  forAll (resize 6 genAF) $ \(n, edges) ->
    let f = naiveAF n edges
        outsider = [n]
     in counterexample (show (n, edges)) $
          conjoin
            [ boundedB f outsider === False
            , admissibleB f outsider === False
            , stableB f outsider === False
            ]

-- | @candidates@ is a full powerset scan: on a duplicate-free carrier it has
-- @2 ^ |args|@ entries. Guards 'Lara.Semantics.subseqs' independently of the
-- goldens, which only ever see the filtered output.
prop_candidatesPowerset :: Property
prop_candidatesPowerset =
  forAll (resize 10 genAF) $ \(n, edges) ->
    let f = naiveAF n edges
     in counterexample (show (n, edges)) $
          length (candidates f) === 2 ^ length (afArgs f)

semanticsSpecProps :: [(String, IO Result)]
semanticsSpecProps =
  [ ("semantics enumerations match the Lean goldens", quickCheckResult prop_goldensMatch)
  , ("semantics goldens cover the framework x semantics product", quickCheckResult prop_goldensCoverProduct)
  , ("grounded enumeration is the grounded singleton", quickCheckResult prop_groundedSingleton)
  , ("carrier-bound deciders reject outsiders", quickCheckResult prop_carrierBoundRejectsOutsiders)
  , ("candidates is a full powerset scan", quickCheckResult prop_candidatesPowerset)
  ]
