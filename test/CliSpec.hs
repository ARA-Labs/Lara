-- | End-to-end tests for the @lara@ command-line driver ("app/Main.hs"), the
-- @cabal test@ half of the review's CLI-coverage gap (M3 review item 8).
--
-- @scripts/differential.sh@ exercises the binary against the Lean oracle, but it
-- is not part of @cabal test@; nothing here spawned the executable, so the
-- 0\/1\/2 exit-code contract, the usage path, and the unreadable-file path were
-- untested by the suite. These tests run the real built binary (put on @PATH@ by
-- the test-suite's @build-tool-depends: lara:lara@) over the committed fixtures
-- and assert exactly the stdout bytes and exit code for each outcome.
--
-- The suite runs from the package root (as @cabal test@ does), so the fixture
-- relative paths resolve — the same assumption "DifferentialSpec" relies on.
module CliSpec (cliSpecProps) where

import Control.Exception (bracket)
import System.Directory (getTemporaryDirectory, removeFile)
import System.Exit (ExitCode (..))
import System.IO (hClose, hPutStr, openTempFile)
import System.Process (readProcessWithExitCode)
import Test.QuickCheck

-- | The executable name; Cabal puts it on @PATH@ during @cabal test@ via the
-- test-suite's @build-tool-depends: lara:lara@.
laraBin :: String
laraBin = "lara"

runLara :: [String] -> IO (ExitCode, String, String)
runLara args = readProcessWithExitCode laraBin args ""

-- | Write @contents@ to a fresh temp @.sexp@ file, run the body, then delete it.
withTempSexp :: String -> (FilePath -> IO a) -> IO a
withTempSexp contents k = do
  tmp <- getTemporaryDirectory
  bracket
    ( do
        (path, h) <- openTempFile tmp "lara-cli.sexp"
        hPutStr h contents
        hClose h
        pure path
    )
    removeFile
    k

-- | accept: exit 0 and exactly the verdict bytes plus one trailing newline
-- ('putStrLn'), byte-identical to the pinned Lean-driver golden.
prop_cliAccept :: Property
prop_cliAccept = once $ ioProperty $ do
  (code, out, _) <- runLara ["check", "fixtures/covered-self-edge.sexp"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitSuccess)
      , counterexample "stdout" $
          out
            === "(verdict accept (labels (0 undec)) (edges (0 0))"
              ++ " (statuses (status (atom p) contested)))\n"
      ]

-- | checker rejection: exit 1 and the reject verdict bytes on stdout.
prop_cliReject :: Property
prop_cliReject = once $ ioProperty $ do
  (code, out, _) <- runLara ["check", "fixtures/missing-self-edge.sexp"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitFailure 1)
      , counterexample "stdout" (out === "(verdict reject missing-conflict)\n")
      ]

-- | codec error (a well-formed file with malformed wire text): exit 2, nothing
-- on stdout (the located message goes to stderr).
prop_cliCodecError :: Property
prop_cliCodecError = once $ ioProperty $
  withTempSexp "(unit (policy" $ \path -> do
    (code, out, _) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 2)
        , counterexample "stdout empty" (out === "")
        ]

-- | unreadable input file: exit 2, nothing on stdout.
prop_cliUnreadable :: Property
prop_cliUnreadable = once $ ioProperty $ do
  (code, out, _) <- runLara ["check", "fixtures/does-not-exist.sexp"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitFailure 2)
      , counterexample "stdout empty" (out === "")
      ]

-- | misuse (unrecognized arguments): exit 2, nothing on stdout (usage goes to
-- stderr).
prop_cliUsage :: Property
prop_cliUsage = once $ ioProperty $ do
  (code, out, _) <- runLara ["not-a-subcommand"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitFailure 2)
      , counterexample "stdout empty" (out === "")
      ]

cliSpecProps :: [(String, IO Result)]
cliSpecProps =
  [ ("cli accept exit 0 + bytes", quickCheckResult prop_cliAccept)
  , ("cli reject exit 1 + bytes", quickCheckResult prop_cliReject)
  , ("cli codec error exit 2", quickCheckResult prop_cliCodecError)
  , ("cli unreadable file exit 2", quickCheckResult prop_cliUnreadable)
  , ("cli usage exit 2", quickCheckResult prop_cliUsage)
  ]
