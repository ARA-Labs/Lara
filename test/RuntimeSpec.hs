-- | Conformance tests for the cached grounded adjacency ("Lara.Runtime", M3
-- plan Task 2, D5) — the production evaluator that reuses the single
-- "Lara.Grounded" fixpoint over a pre-materialised edge relation.
--
-- Four kinds of test:
--
--   * __Random-AF equivalence.__ Over arbitrary small frameworks (including
--     self-loops, cycles, and disconnected components), the cached backend and
--     a naive un-memoised backend over the /same/ edge relation agree on
--     @afAttack@ (on and off the carrier), 'grounded', every 'labelC', and
--     'statusC' — the correctness contract that the cache changes only /how/
--     edges are stored, never /what/ the fixpoint computes.
--   * __Adjacency consistency.__ 'buildAdj' reconstructs exactly the edge set.
--   * __Fixture differential.__ On the two committed wire 'CheckInput'
--     fixtures and a rebut program, the un-cached 'checkedAF' and cached
--     'runtimeAF' produce identical labels\/statuses, and
--     'Lara.Driver.runCheck' (now on the cached default) still prints the
--     byte-identical identity-bearing Lean-driver verdicts.
--   * __Perf guard (smoke).__ A 120-argument synthetic AF: the cached labels
--     must equal the naive labels (the real assertion), completing under a
--     loose wall-clock ceiling that catches a pathological per-iteration
--     re-scan without being a micro-benchmark.
module RuntimeSpec (runtimeSpecProps) where

import Control.Exception (evaluate)
import Data.List (nub, sort)
import qualified Data.Set as Set
import System.Timeout (timeout)
import Test.QuickCheck

import Lara.AST (Label, Unit (..))
import Lara.Check (checkUnit, cuNodes, cuProgram)
import Lara.Compile (checkedAF)
import Lara.Driver (buildCertOk, buildGamma, runCheck)
import Lara.Grounded
  ( AF (..)
  , Claim (..)
  , completeClaimFor
  , grounded
  , labelC
  , statusC
  )
import Lara.Replay (CheckInput, inputReplayId, inputUnit)
import Lara.Runtime (CachedAdj (..), buildAdj, cachedAF, runtimeAF)
import Lara.Wire
  ( decodeCheckInputFile
  , decodeUnit
  , encodeReplayId
  , encodeVerdict
  , parseSExpr
  , printSExpr
  )
import TestReplay (testCheckInput)

-- ---------------------------------------------------------------------------
-- Generators and helpers
-- ---------------------------------------------------------------------------

-- | A random small framework as an explicit edge relation over @[0..n-1]@.
-- Random pairs over the carrier naturally include self-loops (@i,i@), cycles
-- (@i→j@ and @j→i@), and isolated (disconnected) arguments. @n@ and the edge
-- count are bounded so the whole property runs in well under a second (the
-- sizing discipline of @test/WireSpec.hs@'s @smallListOf@).
genAF :: Gen (Int, [(Int, Int)])
genAF = do
  n <- choose (0, 12)
  edges <-
    if n == 0
      then pure []
      else do
        k <- choose (0, 20)
        vectorOf k ((,) <$> choose (0, n - 1) <*> choose (0, n - 1))
  pure (n, edges)

-- | The naive un-memoised backend: @afAttack@ is a direct membership test
-- against the edge relation, re-scanned on every query.
naiveAF :: Int -> [(Int, Int)] -> AF
naiveAF n edges = AF [0 .. n - 1] (\b a -> (b, a) `elem` edges)

sameSet :: [Int] -> [Int] -> Bool
sameSet a b = sort (nub a) == sort (nub b)

-- ---------------------------------------------------------------------------
-- Random-AF equivalence (the correctness contract)
-- ---------------------------------------------------------------------------

prop_cachedEquivNaive :: Property
prop_cachedEquivNaive =
  forAll genAF $ \(n, edges) ->
    let naive = naiveAF n edges
        cached = cachedAF naive
        args = [0 .. n - 1]
        -- probe the whole carrier square plus a border, to pin off-carrier
        -- agreement (both backends answer False off [0..n-1]).
        square = [(b, a) | b <- [-1 .. n], a <- [-1 .. n]]
        someClaims = Claim [] [] : Claim args [] : [Claim [a] [] | a <- args]
     in counterexample (show (n, edges)) $
          conjoin
            [ counterexample "afAttack disagrees" $
                property (and [afAttack naive b a == afAttack cached b a | (b, a) <- square])
            , counterexample "grounded disagrees" $
                property (sameSet (grounded naive) (grounded cached))
            , counterexample "labelC disagrees" $
                property (and [labelC naive a == labelC cached a | a <- args])
            , counterexample "statusC disagrees" $
                property (and [statusC naive c == statusC cached c | c <- someClaims])
            ]

-- ---------------------------------------------------------------------------
-- Adjacency consistency
-- ---------------------------------------------------------------------------

prop_adjConsistent :: Property
prop_adjConsistent =
  forAll genAF $ \(n, edges) ->
    let adj = buildAdj (naiveAF n edges)
        args = [0 .. n - 1]
        expected = Set.fromList [(b, a) | b <- args, a <- args, (b, a) `elem` edges]
     in counterexample (show (n, edges)) (adjEdges adj === expected)

-- ---------------------------------------------------------------------------
-- Fixture differential (cached vs un-cached, and byte-identical defaults)
-- ---------------------------------------------------------------------------

-- | A two-argument rebut program (matches @test/CheckSpec.hs@): compiles to the
-- edge 0→1, exercising a non-self, non-trivial AF through the differential.
rebutProgram :: String
rebutProgram =
  "(unit (sigma (sorts) (cons) (preds (pred q (args)) (pred not_q (args))))"
    ++ " (policy"
    ++ " (rules"
    ++ " (rule r1 (mode defeasible) (params) (premises) (conclusion (apat q))"
    ++ " (questions) (allow-trusted false) (certifiers))"
    ++ " (rule r2 (mode defeasible) (params) (premises) (conclusion (apat not_q))"
    ++ " (questions) (allow-trusted false) (certifiers)))"
    ++ " (contraries (contrary (apat q) (apat not_q))) (exceptions))"
    ++ " (args"
    ++ " (arg a1 (inst r1 (subst) (premises) (discharges) (holes) (assurance none)))"
    ++ " (arg a2 (inst r2 (subst) (premises) (discharges) (holes) (assurance none))))"
    ++ " (attacks (rebut a1 a2))"
    ++ " (queries (atom q) (atom not_q)))"

-- | Build the un-cached ('checkedAF') and cached ('runtimeAF') backends from an
-- accepted check input and assert they agree on the complete result.
differentialInput :: CheckInput -> Property
differentialInput input =
  let unit = inputUnit input
   in case checkUnit (buildGamma (unitLeaves unit)) (buildCertOk (unitTheories unit)) unit of
        Left err -> counterexample ("unexpected reject: " ++ show err) (property False)
        Right cu ->
          let naive = checkedAF (cuProgram cu)
              cached = runtimeAF (cuProgram cu)
              args = afArgs naive
              claims = [completeClaimFor (cuNodes cu) p | p <- unitQueries unit]
           in conjoin
                [ counterexample "carrier differs" (afArgs naive === afArgs cached)
                , counterexample "afAttack differs" $
                    property (and [afAttack naive b a == afAttack cached b a | b <- args, a <- args])
                , counterexample "grounded differs" $
                    property (sameSet (grounded naive) (grounded cached))
                , counterexample "labelC differs" $
                    property (and [labelC naive a == labelC cached a | a <- args])
                , counterexample "statusC differs" $
                    property (and [statusC naive c == statusC cached c | c <- claims])
                ]

verdictBytes :: CheckInput -> String
verdictBytes = printSExpr . encodeVerdict . runCheck

decodeUnitText :: String -> Either String Unit
decodeUnitText text =
  case parseSExpr text of
    Left err -> Left (show err)
    Right value -> either (Left . show) Right (decodeUnit value)

expectedVerdictText :: CheckInput -> String -> String
expectedVerdictText input outcomeTail =
  "(verdict "
    ++ printSExpr (encodeReplayId (inputReplayId input))
    ++ " "
    ++ outcomeTail
    ++ ")"

-- | The cached\/un-cached differential on the two committed fixtures (read from
-- disk) and the rebut program. The missing fixture rejects, so it carries no AF
-- to differentiate — it is pinned by 'prop_fixtureGoldenBytes' below.
prop_fixtureDifferential :: Property
prop_fixtureDifferential = once $ ioProperty $ do
  coveredBytes <- readFile "fixtures/covered-self-edge.sexp"
  pure $ case (decodeCheckInputFile coveredBytes, decodeUnitText rebutProgram) of
    (Right coveredInput, Right rebutUnit) ->
      conjoin [differentialInput coveredInput, differentialInput (testCheckInput rebutUnit)]
    values -> counterexample ("fixture codec: " ++ show values) False

-- | The Driver default now grounds accepted units over the cached backend; its
-- printed verdicts must still be the byte-identical Lean-driver goldens for the
-- two committed fixtures.
prop_fixtureGoldenBytes :: Property
prop_fixtureGoldenBytes = once $ ioProperty $ do
  coveredBytes <- readFile "fixtures/covered-self-edge.sexp"
  missingBytes <- readFile "fixtures/missing-self-edge.sexp"
  pure $ case (decodeCheckInputFile coveredBytes, decodeCheckInputFile missingBytes) of
    (Right coveredInput, Right missingInput) ->
      conjoin
        [ verdictBytes coveredInput
            === expectedVerdictText coveredInput
              "accept (labels (0 undec)) (edges (0 0)) (statuses (status (atom p) contested))"
        , verdictBytes missingInput
            === expectedVerdictText missingInput "reject missing-conflict"
        ]
    values -> counterexample ("fixture codec: " ++ show values) False

-- ---------------------------------------------------------------------------
-- Perf guard (smoke, not a benchmark)
-- ---------------------------------------------------------------------------

-- | A 120-argument synthetic framework mixing a rebut chain, self-loops (which
-- force @undec@ labels), and a small back-cycle — enough structure to make the
-- grounded iteration do real work.
perfPred :: Int -> Int -> Int -> Bool
perfPred n b a =
  (even b && a == b + 1)
    || (b == a && b `mod` 17 == 0)
    || ((b + 1) `mod` n == a && a < 3)

-- | The ceiling is deliberately loose. A full 120-argument 'labelC' sweep
-- measures ~0.6s compiled (-O1); two sweeps here are ~1.2s. The bound is a
-- smoke bound to catch a /pathological/ blowup (e.g. an accidental
-- per-iteration edge re-scan, which is ~120x slower and would take minutes),
-- not a micro-benchmark. Shared CI runners are several times slower than a dev
-- laptop with noisy neighbours, so the ceiling is set to 30s: ~25x headroom on
-- the expected ~1.2s, still decisively below a real O(n) regression.
perfCeilingMicros :: Int
perfCeilingMicros = 30 * 1000 * 1000

prop_perfGuard :: Property
prop_perfGuard = once $ ioProperty $ do
  let n = 120
      naive = AF [0 .. n - 1] (perfPred n)
      cached = cachedAF naive
      args = [0 .. n - 1]
  r <-
    timeout perfCeilingMicros $ do
      let lsN = [labelC naive a | a <- args] :: [Label]
          lsC = [labelC cached a | a <- args] :: [Label]
      -- (==) forces both label vectors fully; evaluate forces the Bool.
      evaluate (lsN == lsC && length lsN == n)
  pure $ case r of
    Nothing ->
      counterexample "perf guard: exceeded 30s wall-clock ceiling" (property False)
    Just ok ->
      counterexample "perf guard: cached labels /= naive labels" (property ok)

-- ---------------------------------------------------------------------------
-- Index
-- ---------------------------------------------------------------------------

runtimeSpecProps :: [(String, IO Result)]
runtimeSpecProps =
  [ ("runtime cached ≡ naive (random AFs)", quickCheckResult prop_cachedEquivNaive)
  , ("runtime adjacency consistency", quickCheckResult prop_adjConsistent)
  , ("runtime fixture differential", quickCheckResult prop_fixtureDifferential)
  , ("runtime fixture golden bytes", quickCheckResult prop_fixtureGoldenBytes)
  , ("runtime perf guard (120 args, ≤30s)", quickCheckResult prop_perfGuard)
  ]
