-- | Single corpus-unit validator (M5 tracker #48, T2 authoring aid).
--
-- Parses one @unit.lara@ against the shared corpus policy, elaborates it, and
-- prints the computed claim statuses and argument labels — the authoring
-- inner loop for @corpus-units/@, without touching the manifest or any
-- committed anchor (that is @scripts/gen-corpus-units.hs@'s job).
--
-- >  cabal exec -- runghc --ghc-arg=-package --ghc-arg=lara scripts/check-corpus-unit.hs corpus-units/<artifact>/<claim>/unit.lara
--
-- (the package flag keeps the lara library visible regardless of which
-- component cabal last built)
--
-- Exit 0 iff the unit parses, elaborates, validates replay metadata, and the
-- checker's verdict class is @accept@; the computed JSON verdict (statuses
-- included) is printed in both the accept and reject cases. A parse,
-- elaboration, or replay-metadata failure dies with a located message on
-- stderr and nothing on stdout.
module Main (main) where

import Lara.Elaborate (defeasibleSuiteSigma, elabErrorMessage, elaborate, registryOf)
import Lara.ExpectedJson (JValue (..), expectedJsonValue, renderJson)
import Lara.Replay (replayErrorMessage, sourceCheckInput)
import Lara.Syntax (parsePolicy, parseProgram)
import System.Environment (getArgs)
import System.Exit (die, exitFailure)

policyPath :: FilePath
policyPath = "corpus-units/corpus-v1.policy.lara"

main :: IO ()
main = do
  args <- getArgs
  unitPath <- case args of
    [p] -> pure p
    _ -> die "usage: check-corpus-unit.hs <unit.lara>"
  policyText <- readFile policyPath
  policy <- either (die . ((policyPath ++ ": parse: ") ++) . show) pure (parsePolicy policyText)
  progText <- readFile unitPath
  prog <- either (die . ((unitPath ++ ": parse: ") ++) . show) pure (parseProgram progText)
  input <- case elaborate defeasibleSuiteSigma (registryOf policy) prog policy of
    Left err -> die (unitPath ++ ": elaborate: " ++ elabErrorMessage err)
    Right unit ->
      either (die . ((unitPath ++ ": replay: ") ++) . replayErrorMessage) pure
        (sourceCheckInput prog policy unit)
  let value = expectedJsonValue input
  putStrLn (renderJson value)
  case value of
    JObject top
      | Just (JString "accept") <- lookup "verdict-class" top -> pure ()
    _ -> exitFailure
