-- | The corpus claim-support aggregation harness (#56): the IO around the pure
-- "Lara.ClaimSupport" metrics. One command that emits the four
-- corpus-descriptive numbers the paper's /Claim-support outcomes/ paragraph
-- (@\\msfive@ in the external paper repo's @evaluation.tex@; this repo ships no
-- @.tex@) cites, over the FROZEN 60 corpus units (@corpus-units\/MANIFEST.tsv@,
-- tag @m5-freeze-v1@, seed 20260801).
--
-- Discovery is manifest-driven (never a glob), reusing
-- 'Lara.Measure.parseCorpusManifest'. The per-unit decode + 'runCheck' + surface
-- parse (and the documented @strict_certifier@\/@strict-flavored@ header flag)
-- live in 'Lara.ClaimSupport.Load', shared with the regression test so the two
-- cannot drift. The shared policy ('parsePolicy' on @corpus-v1.policy.lara@)
-- supplies rule modes for the strict-step count. Haskell-only by construction:
-- no Lean subprocess, no timing — a deterministic reporting pass, not a
-- differential run.
--
-- Output: @measurements\/claim-support.json@ (aggregate + per-unit records +
-- environment) and @measurements\/claim-support.tsv@ (flat per-unit rows). The
-- committed deliverable is the copy under @measurements\/frozen\/@.
--
-- Run with the built library on the path:
--
-- >  cabal exec -- runghc scripts/claim-support.hs
module Main (main) where

import Control.Monad (when)
import Data.List (dropWhileEnd)
import Data.Char (isSpace)
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..), exitFailure)
import System.Info (arch, os)
import System.IO (hPutStrLn, stderr)
import System.Process (readProcessWithExitCode)

import Lara.ClaimSupport (aggregate, claimSupportJson, claimSupportTsv)
import Lara.ClaimSupport.Load (loadRuleModes, loadUnitRecord)
import Lara.Measure (EnvBlock (..), parseCorpusManifest)

manifestPath :: FilePath
manifestPath = "corpus-units/MANIFEST.tsv"

policyPath :: FilePath
policyPath = "corpus-units/corpus-v1.policy.lara"

main :: IO ()
main = do
  corpusManifest <- readFile manifestPath
  let inputs = parseCorpusManifest corpusManifest
  when (null inputs) (die ("no corpus units discovered from " ++ manifestPath))
  ruleModeOf <- loadRuleModes policyPath
  env <- gatherEnv
  records <- mapM (loadUnitRecord ruleModeOf) inputs
  let report = aggregate records
  createDirectoryIfMissing True "measurements"
  writeFile "measurements/claim-support.json" (claimSupportJson env report records)
  writeFile "measurements/claim-support.tsv" (claimSupportTsv records)
  putStrLn
    ( "wrote claim-support aggregation over " ++ show (length records)
        ++ " corpus units to measurements/claim-support.{json,tsv}"
    )

-- | The reproducibility environment block (git rev + dirty flag, GHC, OS, CPU);
-- best-effort. @envLean@ is empty — this harness runs no Lean driver.
gatherEnv :: IO EnvBlock
gatherEnv = do
  rev <- capture "git" ["rev-parse", "HEAD"]
  dirty <- capture "git" ["status", "--porcelain"]
  ghc <- capture "ghc" ["--numeric-version"]
  pure
    EnvBlock
      { envGitRev = rev
      , envGitDirty = not (null dirty)
      , envGhc = ghc
      , envLean = ""
      , envOs = os
      , envCpu = arch
      }

capture :: String -> [String] -> IO String
capture cmd args = do
  (code, out, _err) <- readProcessWithExitCode cmd args ""
  pure $ case code of
    ExitSuccess -> trim out
    ExitFailure _ -> ""

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace

die :: String -> IO a
die msg = hPutStrLn stderr ("claim-support: " ++ msg) >> exitFailure
