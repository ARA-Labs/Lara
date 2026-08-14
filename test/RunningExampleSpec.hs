-- | The paper's running example (fig:example) as a standing freshness test
-- (P6, issue #70): the committed golden
-- @measurements\/frozen\/running-example.txt@ must reproduce byte-for-byte
-- from re-checking the two run programs through the pure
-- "Lara.RunningExample" pipeline — the same module
-- @scripts\/render-running-example.hs@ uses, so the pasted paper excerpt and
-- the shipped checker cannot drift apart silently.
--
-- A second property pins the semantic shape the paper narrates: run 1
-- accepts with the empirical claim @gap@, the certified comparison
-- @justified@, and only the unattacked strict step @s1@ in the framework;
-- run 2 accepts with @a1@ labelled out, @d1@ in, one closure edge, the
-- empirical claim @defeated@, and the certified comparison still
-- @justified@.
module RunningExampleSpec (runningExampleSpecProps) where

import Data.List (isPrefixOf)
import Test.QuickCheck

import Lara.AST (Decl (..), Label (..), PropId (..), Status (..), claimId, claimNl, programDecls)
import Lara.Elaborate.Comparison (expandSurface)
import Lara.RunningExample (checkRun, goldenPath, loadRun, renderRuns, runPaths)
import qualified Lara.Syntax as Syntax
import Lara.Wire (Outcome (..), PublicStatus (..), Verdict (..), encodeVerdict, printSExpr)

runningExampleSpecProps :: [(String, IO Result)]
runningExampleSpecProps =
  [ ("running-example: rendered reports re-diff the committed frozen golden", quickCheckResult prop_frozenGolden)
  , ("running-example: run 1 is gap beside the justified strict step, run 2 is defeated via the undercut", quickCheckResult prop_shape)
  , ("running-example: c2's value-reference nl interpolates to the bound scores in both runs", quickCheckResult prop_nlInterpolation)
  , ("running-example: the README's quoted verdict block is run 2's verdict bytes", quickCheckResult prop_readmeVerdict)
  ]

checkedRuns :: IO [(FilePath, Verdict)]
checkedRuns = mapM checkOne runPaths
  where
    checkOne path = do
      (progText, polText) <- loadRun path
      case checkRun progText polText of
        Left err -> fail (path ++ ": " ++ err)
        Right verdict -> pure (path, verdict)

prop_frozenGolden :: Property
prop_frozenGolden = once $ ioProperty $ do
  runs <- checkedRuns
  frozen <- readFile goldenPath
  pure $ counterexample "frozen running-example.txt" (renderRuns runs === frozen)

prop_shape :: Property
prop_shape = once $ ioProperty $ do
  runs <- checkedRuns
  case map (verdictOutcome . snd) runs of
    [Accept ls1 es1 sts1, Accept ls2 es2 sts2] ->
      pure $
        conjoin
          [ counterexample "run 1 framework is the strict step alone, in" (map snd ls1 === [LIn] .&&. es1 === [])
          , counterexample "run 1 statuses are gap then justified" (map snd sts1 === [Published Gap, Published Justified])
          , counterexample "run 2 labels s1 in, a1 out, d1 in" (map snd ls2 === [LIn, LOut, LIn])
          , counterexample "run 2 has the one closure edge" (es2 === [(2, 1)])
          , counterexample "run 2 statuses are defeated then justified" (map snd sts2 === [Published Defeated, Published Justified])
          ]
    outcomes ->
      pure $ counterexample ("unexpected outcomes: " ++ show outcomes) (property False)

-- | The @0.4 value-reference interpolation in c2's @nl@ is the one surface
-- feature of this example no golden can observe: 'claimNl' never reaches
-- 'Unit', so it is absent from @example.core.sexp@, @expected.json@, and the
-- frozen report. Pin the expanded prose directly: both runs' c2 must read
-- with the bound scores substituted (the general mechanism is covered by
-- ValueBindingsSpec; this pins THIS example's use of it).
prop_nlInterpolation :: Property
prop_nlInterpolation = once $ ioProperty $ do
  nls <- mapM expandedC2 runPaths
  pure $
    counterexample
      "expanded c2 nl in both runs"
      (nls === replicate 2 "The baseline accuracy 0.71 is strictly below 0.74")
  where
    expandedC2 path = do
      (progText, polText) <- loadRun path
      either (fail . ((path ++ ": ") ++)) pure $ do
        prog <- either (Left . Syntax.peReason) Right (Syntax.parseProgram progText)
        pol <- either (Left . Syntax.peReason) Right (Syntax.parsePolicy polText)
        expanded <- either (Left . show) Right (expandSurface pol prog)
        case [claimNl c | DeclClaim c <- programDecls expanded, claimId c == PropId "c2"] of
          [nl] -> Right nl
          other -> Left ("expected exactly one c2 claim, got " ++ show (length other))

-- | The README's quoted verdict block is a third copy of run 2's verdict
-- bytes (after the frozen report and the DifferentialSpec golden), so pin it:
-- the front page cannot drift from the checker. The block is located by
-- content — the one @```text@ fence whose first line starts with
-- @(verdict@ — and unwrapped by whitespace normalization, because the README
-- wraps the single CLI output line for page width.
prop_readmeVerdict :: Property
prop_readmeVerdict = once $ ioProperty $ do
  runs <- checkedRuns
  readme <- readFile "README.md"
  let verdictBlocks =
        [ unwords (concatMap words blk)
        | blk@(firstLine : _) <- fencedTextBlocks (lines readme)
        , "(verdict" `isPrefixOf` firstLine
        ]
      run2 =
        [ printSExpr (encodeVerdict v)
        | (path, v) <- runs
        , path == "examples/running-example/run2/example.lara"
        ]
  pure $ counterexample "README verdict block vs run 2 verdict bytes" (verdictBlocks === run2)

-- | The bodies of the @```text@ fenced blocks of a markdown document, in order.
fencedTextBlocks :: [String] -> [[String]]
fencedTextBlocks [] = []
fencedTextBlocks (l : ls)
  | l == "```text" = let (blk, rest) = break (== "```") ls in blk : fencedTextBlocks (drop 1 rest)
  | otherwise = fencedTextBlocks ls
