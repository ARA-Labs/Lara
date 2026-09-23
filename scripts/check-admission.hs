-- | The executable admission differential driver (metatheory plan Task 3):
-- the Haskell side of @scripts\/admission-differential.sh@.
--
-- Reads one test-only fixture under @fixtures\/admission\/@ and runs the
-- shared Haskell adapter over production admission/prune primitives via
-- "Lara.AdmissionFixture" (also used by @test\/DifferentialSpec.hs@).
-- It does not invoke @prepareSource@ or @runSourceCheck@. The fixture's
-- @expected@ section must reproduce the computed semantic outcome
-- byte-for-byte; a mismatch is exit 1, while a malformed fixture is a codec
-- error (exit 2, empty stdout), matching the Lean semantic twin.
--
-- The fixture schema is test-only: it is NOT a production wire format and
-- never enters @lara-core\@0.1@ or replay identity.
--
-- Run with the built library and the test directory on the path:
--
-- >  cabal exec -- runghc -itest scripts/check-admission.hs fixtures/admission/NAME.sexp
module Main (main) where

import System.Environment (getArgs)
import System.Exit (ExitCode (ExitFailure), exitSuccess, exitWith)
import System.IO (hPutStrLn, stderr)

import Lara.AdmissionFixture (admissionOutcome)

codecError :: String -> IO a
codecError msg = do
  hPutStrLn stderr ("check-admission: codec error at " ++ msg)
  exitWith (ExitFailure 2)

runOnContents :: String -> IO ()
runOnContents contents = do
  case admissionOutcome contents of
    Left msg -> codecError msg
    Right (computed, expected) ->
      if computed == expected
        then do
          putStrLn computed
          exitSuccess
        else do
          hPutStrLn stderr ("check-admission: computed outcome differs from the fixture's expected section"
            ++ "\ncomputed: " ++ computed
            ++ "\nexpected: " ++ expected)
          exitWith (ExitFailure 1)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      contents <- readFile path
      runOnContents contents
    _ -> do
      hPutStrLn stderr "usage: check-admission.hs <fixture.sexp>"
      exitWith (ExitFailure 2)
