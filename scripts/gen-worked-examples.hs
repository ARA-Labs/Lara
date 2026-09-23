-- | Worked-examples @.core.sexp@ generator (M4a Task A2).
--
-- For each per-example directory @examples/<NAME>/@, reads the committed
-- @example.lara@ artifact and its co-located policy, parses both with
-- "Lara.Syntax", lowers the pair to a 'CheckInput' with the trusted surface
-- elaborator and validated source replay metadata, and writes its canonical
-- check-input envelope. This is the exact derivation path @app\/Main.hs@ takes
-- for a @.lara@ file, so each anchor carries the real artifact, policy,
-- backend, and theory identity alongside the unchanged checker 'Unit'.
-- @test/WorkedExamplesSpec.hs@ pins this as a freshness assertion
-- (re-deriving each @.core.sexp@ from its @.lara@ must reproduce the committed
-- bytes) and @scripts/differential.sh@ runs each through both drivers.
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
-- a @.core.sexp@. The suite happens to carry constant atoms only; numeric
-- literals are nevertheless safe because both production drivers share
-- @canonNum@.
module Main (main) where

import Lara.AST (PolicyId (..), Program (..))
import Lara.Admission (renderAdmissionAudit, renderAdmissionRejection)
import Lara.Elaborate
  ( PreparedSource (..)
  , prepareSource
  , renderSourceInvalid
  , runSourceCheck
  , sourceResultCheckInput
  )
import Lara.ExpectedJson (expectedJson)
import Lara.Replay (CheckInput)
import Lara.Syntax (parsePolicy, parseProgram)
import Lara.Wire (encodeCheckInput, printSExpr)
import Lara.WorkedExamples
  ( workedExampleArtifact
  , workedExampleCore
  , workedExampleExpected
  , workedExamplePolicy
  , workedExamples
  )
import System.Environment (getArgs)
import System.FilePath ((</>), (<.>))

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> mapM_ genExample workedExamples
    ["--bundle", dir] -> genBundle dir
    _ -> fail "usage: gen-worked-examples.hs [--bundle BUNDLE_DIR]"

-- | Derive and write both generated files of one registry entry. The paths come
-- from "Lara.WorkedExamples" so the generator and @test\/WorkedExamplesSpec.hs@
-- cannot disagree about which bytes belong to which example.
genExample :: (FilePath, FilePath) -> IO ()
genExample entry@(dir, _) = do
  let artifactPath = workedExampleArtifact dir
      policyPath = workedExamplePolicy entry
      corePath = workedExampleCore dir
      expectedPath = workedExampleExpected dir
  input <- loadCheckInput artifactPath policyPath
  writeCore corePath input
  writeFile expectedPath (expectedJson input)
  putStrLn ("wrote " ++ expectedPath)

genBundle :: FilePath -> IO ()
genBundle dir = do
  let artifactPath = dir </> "emitted.lara"
      corePath = dir </> "emitted.core.sexp"
  progText <- readFile artifactPath
  prog <- either (fail . ((artifactPath ++ ": parse: ") ++) . show) pure (parseProgram progText)
  let PolicyId policyName = programPolicy prog
      policyPath = dir </> policyName <.> "policy" <.> "lara"
  input <- loadPolicyAndElaborate artifactPath policyPath prog
  writeCore corePath input

loadCheckInput :: FilePath -> FilePath -> IO CheckInput
loadCheckInput artifactPath policyPath = do
  progText <- readFile artifactPath
  prog <- either (fail . ((artifactPath ++ ": parse: ") ++) . show) pure (parseProgram progText)
  loadPolicyAndElaborate artifactPath policyPath prog

loadPolicyAndElaborate :: FilePath -> FilePath -> Program -> IO CheckInput
loadPolicyAndElaborate artifactPath policyPath prog = do
  policyText <- readFile policyPath
  policy <- either (fail . ((policyPath ++ ": parse: ") ++) . show) pure (parsePolicy policyText)
  case prepareSource prog policy of
    Left invalid -> fail (artifactPath ++ ": source invalid: " ++ renderSourceInvalid invalid)
    Right (SourceRejected rejection) ->
      fail (artifactPath ++ ": admission rejection: " ++ renderAdmissionRejection rejection)
    Right (SourceAccepted source) ->
      case sourceResultCheckInput (runSourceCheck source) of
        Left audit ->
          fail
            ( artifactPath
                ++ ": legacy core artifacts cannot encode source admission: "
                ++ renderAdmissionAudit audit
            )
        Right input -> pure input

writeCore :: FilePath -> CheckInput -> IO ()
writeCore corePath input = do
  writeFile corePath (printSExpr (encodeCheckInput input) ++ "\n")
  putStrLn ("wrote " ++ corePath)
