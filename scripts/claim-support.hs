-- | The corpus claim-support aggregation harness: the IO around the pure
-- "Lara.ClaimSupport" metrics. One command that emits the four
-- corpus-descriptive numbers the paper's /Claim-support outcomes/ paragraph
-- (@\\msfive@ in the external paper repo's @evaluation.tex@; this repo ships no
-- @.tex@) cites, over the frozen 60-unit corpus sample
-- (@corpus-units\/MANIFEST.tsv@, seed 20260801).
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
-- environment), @measurements\/claim-support.tsv@ (flat per-unit rows), and
-- @measurements\/binding-audit\/worklist.tsv@ (the binding-audit review rows).
-- The committed aggregate deliverable is the copy under @measurements\/frozen\/@.
--
-- Run with the built library on the path:
--
-- >  cabal exec -- runghc scripts/claim-support.hs
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (when)
import Data.Char (isSpace)
import Data.List (dropWhileEnd)
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..), exitFailure)
import System.FilePath (takeDirectory)
import System.Info (arch, os)
import System.IO (hPutStrLn, stderr)
import System.Process (readProcessWithExitCode)

import Lara.AtomicWrite (atomicWriteFile)
import Lara.ClaimSupport
  ( aggregate
  , bindingAuditPath
  , bindingAuditTsv
  , claimSupportJson
  , claimSupportTsv
  )
import Lara.ClaimSupport.Load (loadPolicy, loadUnitRecord)
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
  policy <- loadPolicy policyPath
  env <- gatherEnv
  records <- mapM (loadUnitRecord policy) inputs
  let report = aggregate records
      jsonBytes = claimSupportJson env report records
      aggregateTsvBytes = claimSupportTsv records
      worklistBytes = bindingAuditTsv records
  -- Force every pure rendering before the first write. Context or encoding
  -- drift is reported through lazy errors; forcing here prevents an earlier
  -- output from being replaced before such an error aborts the command.
  _ <- evaluate (length jsonBytes + length aggregateTsvBytes + length worklistBytes)
  createDirectoryIfMissing True "measurements"
  createDirectoryIfMissing True (takeDirectory bindingAuditPath)
  -- The aggregate pair is ignored, regenerable output. The committed human
  -- audit worklist is the only tracked destination and is replaced atomically.
  writeFile "measurements/claim-support.json" jsonBytes
  writeFile "measurements/claim-support.tsv" aggregateTsvBytes
  atomicWriteFile bindingAuditPath worklistBytes
  putStrLn
    ( "wrote claim-support aggregate pair and binding-audit worklist over "
        ++ show (length records)
        ++ " corpus units to measurements/claim-support.{json,tsv} and "
        ++ bindingAuditPath
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
