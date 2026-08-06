-- | The paper's running example (fig:example) as a standing freshness test
-- (P6, issue #70): the committed golden
-- @measurements\/frozen\/running-example.txt@ must reproduce byte-for-byte
-- from re-checking the two run programs through the pure
-- "Lara.RunningExample" pipeline — the same module
-- @scripts\/render-running-example.hs@ uses, so the pasted paper excerpt and
-- the shipped checker cannot drift apart silently.
--
-- A second property pins the semantic shape the paper narrates: run 1
-- accepts with the claim @gap@ and an empty framework; run 2 accepts with
-- @a1@ labelled out, @d1@ in, one closure edge, and the claim @defeated@.
module RunningExampleSpec (runningExampleSpecProps) where

import Test.QuickCheck

import Lara.AST (Label (..), Status (..))
import Lara.RunningExample (checkRun, goldenPath, loadRun, renderRuns, runPaths)
import Lara.Wire (Outcome (..), PublicStatus (..), Verdict (..))

runningExampleSpecProps :: [(String, IO Result)]
runningExampleSpecProps =
  [ ("running-example: rendered reports re-diff the committed frozen golden", quickCheckResult prop_frozenGolden)
  , ("running-example: run 1 is gap over an empty framework, run 2 is defeated via the undercut", quickCheckResult prop_shape)
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
          [ counterexample "run 1 framework is empty" (ls1 === [] .&&. es1 === [])
          , counterexample "run 1 claim is gap" (map snd sts1 === [Published Gap])
          , counterexample "run 2 labels a1 out, d1 in" (map snd ls2 === [LOut, LIn])
          , counterexample "run 2 has the one closure edge" (es2 === [(1, 0)])
          , counterexample "run 2 claim is defeated" (map snd sts2 === [Published Defeated])
          ]
    outcomes ->
      pure $ counterexample ("unexpected outcomes: " ++ show outcomes) (property False)
