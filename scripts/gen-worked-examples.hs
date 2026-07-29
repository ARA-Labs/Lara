-- | Worked-examples @.core.sexp@ generator (M4a Task A2).
--
-- For each per-example directory @examples/<NAME>/@, reads the committed
-- @example.lara@ artifact and its co-located policy, parses both with
-- "Lara.Syntax", lowers the pair to the checker anchor 'Unit' with the trusted
-- surface elaborator ("Lara.Elaborate".@elaborate@), and writes
-- @examples/<NAME>/example.core.sexp@ = @printSExpr (encodeUnit u)@ plus a single
-- trailing newline — the canonical wire text both drivers decode (the same
-- convention @scripts/gen-corpus.hs@ uses for @fixtures/corpus@).
--
-- This is the exact derivation path @app\/Main.hs@ takes for a @.lara@ file, so
-- the generated @.core.sexp@ is the differential anchor: the wire denotes exactly
-- the 'Unit' the surface elaborates to. @test/WorkedExamplesSpec.hs@ pins this as
-- a freshness assertion (re-deriving each @.core.sexp@ from its @.lara@ must
-- reproduce the committed bytes) and @scripts/differential.sh@ runs each through
-- both drivers.
--
-- Run with the built library on the path:
--
-- >  cabal exec -- runghc scripts/gen-worked-examples.hs
--
-- The reject examples (R1/R2/R3) still elaborate to a structurally-valid 'Unit';
-- the checker (not the elaborator) rejects them, so every example below produces
-- a @.core.sexp@. The suite carries no @num@ literals (constant atoms only), so
-- the Lean @canon = id@ caveat that @gen-corpus.hs@ documents does not bite here.
module Main (main) where

import Lara.Elaborate (defeasibleSuiteSigma, elabErrorMessage, elaborate, emptyRegistry)
import Lara.ExpectedJson (expectedJson)
import Lara.Syntax (parsePolicy, parseProgram)
import Lara.Wire (encodeUnit, printSExpr)

-- | (example directory, policy basename). The artifact is always
-- @<dir>/example.lara@; the policy is @<dir>/<basename>@ (co-located, matching the
-- @policy <name>@ header the artifact declares).
examples :: [(FilePath, FilePath)]
examples =
  [ ("examples/A", "empirical-v1.policy.lara")
  , ("examples/B", "empirical-v1.policy.lara")
  , ("examples/E1", "empirical-v1.policy.lara")
  , ("examples/E2", "empirical-v1.policy.lara")
  , ("examples/E3", "empirical-v1.policy.lara")
  , ("examples/R1", "empirical-v1.policy.lara")
  , ("examples/R2", "strict-bad-v1.policy.lara")
  , ("examples/R3", "empirical-v1.policy.lara")
  ]

main :: IO ()
main = mapM_ genOne examples
  where
    genOne (dir, policyBase) = do
      let artifactPath = dir ++ "/example.lara"
          policyPath = dir ++ "/" ++ policyBase
          corePath = dir ++ "/example.core.sexp"
          expectedPath = dir ++ "/expected.json"
      progText <- readFile artifactPath
      polText <- readFile policyPath
      prog <- either (fail . ((artifactPath ++ ": parse: ") ++) . show) pure (parseProgram progText)
      pol <- either (fail . ((policyPath ++ ": parse: ") ++) . show) pure (parsePolicy polText)
      case elaborate defeasibleSuiteSigma emptyRegistry prog pol of
        Left e -> fail (artifactPath ++ ": elaborate: " ++ elabErrorMessage e)
        Right u -> do
          writeFile corePath (printSExpr (encodeUnit u) ++ "\n")
          putStrLn ("wrote " ++ corePath)
          writeFile expectedPath (expectedJson u)
          putStrLn ("wrote " ++ expectedPath)
