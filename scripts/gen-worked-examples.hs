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
-- >  cabal exec -- runghc scripts/gen-worked-examples.hs --bundle bundles/walking-skeleton
--
-- With @--bundle DIR@, reads @DIR/emitted.lara@ and the policy named by its
-- header, then writes @DIR/emitted.core.sexp@ through the same derivation. This
-- is the minimal bundle-input mode used by the replay-bundle freezer.
--
-- The reject examples (R1/R2/R3) still elaborate to a structurally-valid 'Unit';
-- the checker (not the elaborator) rejects them, so every example below produces
-- a @.core.sexp@. The suite carries no @num@ literals (constant atoms only), so
-- the Lean @canon = id@ caveat that @gen-corpus.hs@ documents does not bite here.
module Main (main) where

import Lara.AST (PolicyId (..), Program (..), Unit)
import Lara.Elaborate (defeasibleSuiteSigma, elabErrorMessage, elaborate, registryOf)
import Lara.ExpectedJson (expectedJson)
import Lara.Syntax (parsePolicy, parseProgram)
import Lara.Wire (encodeUnit, printSExpr)
import System.Environment (getArgs)
import System.FilePath ((</>), (<.>))

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
  , ("examples/S1", "strict-v1.policy.lara")
  ]

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> mapM_ genExample examples
    ["--bundle", dir] -> genBundle dir
    _ -> fail "usage: gen-worked-examples.hs [--bundle BUNDLE_DIR]"

genExample :: (FilePath, FilePath) -> IO ()
genExample (dir, policyBase) = do
  let artifactPath = dir </> "example.lara"
      policyPath = dir </> policyBase
      corePath = dir </> "example.core.sexp"
      expectedPath = dir </> "expected.json"
  unit <- loadUnit artifactPath policyPath
  writeCore corePath unit
  writeFile expectedPath (expectedJson unit)
  putStrLn ("wrote " ++ expectedPath)

genBundle :: FilePath -> IO ()
genBundle dir = do
  let artifactPath = dir </> "emitted.lara"
      corePath = dir </> "emitted.core.sexp"
  progText <- readFile artifactPath
  prog <- either (fail . ((artifactPath ++ ": parse: ") ++) . show) pure (parseProgram progText)
  let PolicyId policyName = programPolicy prog
      policyPath = dir </> policyName <.> "policy" <.> "lara"
  unit <- loadPolicyAndElaborate artifactPath policyPath prog
  writeCore corePath unit

loadUnit :: FilePath -> FilePath -> IO Unit
loadUnit artifactPath policyPath = do
  progText <- readFile artifactPath
  prog <- either (fail . ((artifactPath ++ ": parse: ") ++) . show) pure (parseProgram progText)
  loadPolicyAndElaborate artifactPath policyPath prog

loadPolicyAndElaborate :: FilePath -> FilePath -> Program -> IO Unit
loadPolicyAndElaborate artifactPath policyPath prog = do
  polText <- readFile policyPath
  pol <- either (fail . ((policyPath ++ ": parse: ") ++) . show) pure (parsePolicy polText)
  case elaborate defeasibleSuiteSigma (registryOf pol) prog pol of
    Left e -> fail (artifactPath ++ ": elaborate: " ++ elabErrorMessage e)
    Right unit -> pure unit

writeCore :: FilePath -> Unit -> IO ()
writeCore corePath unit = do
  writeFile corePath (printSExpr (encodeUnit unit) ++ "\n")
  putStrLn ("wrote " ++ corePath)
