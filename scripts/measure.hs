-- | The axis-(c) measurement harness (M5 tracker #48, T3).
--
-- One command that emits the machine-readable evaluation report the paper's
-- tables are generated from: per mutant + per corpus unit, the rejection
-- outcome, defect location vs. seeded ground truth, cross-driver agreement,
-- replay success, certificate size, and checking time. Discovery is
-- manifest-driven (@fixtures\/mutants\/MANIFEST.tsv@ + @corpus-units\/MANIFEST.tsv@),
-- never a glob.
--
-- All metric logic is the pure "Lara.Measure" library; this script is the IO:
-- reading files, spawning the Lean driver (@lean\/.lake\/build\/bin\/lara-driver@)
-- for the @lean_wall@ timing and the @lean_agree@ comparison, and wall-clock
-- timing via 'getMonotonicTimeNSec'. The @hs_check@ timed section forces the
-- fully rendered verdict text (an unforced lazy @runCheck@ measures thunk
-- allocation, ~0ns — eng review D8\/5A) and excludes decode; @lean_wall@ is
-- subprocess wall time (startup + decode included). The two are DIFFERENT
-- protocols and not comparable — no cross-driver time ratio may be derived.
--
-- Output: @measurements\/report.json@ (full records + aggregate + environment)
-- and @measurements\/report.tsv@ (flat, the table-generator input), plus the
-- ablation-baseline report @measurements\/ablation.{json,tsv}@ (M5 T6): every
-- input re-checked under each ablated 'CheckConfig' from 'ablationConfigs' —
-- Haskell-only by construction, no Lean run, no timing.
-- @measurements\/@ is gitignored: pre-freeze numbers are development output;
-- committed records are T5's post-freeze deliverable, from this same harness.
--
-- Run with the built library on the path:
--
-- >  cabal exec -- runghc scripts/measure.hs
--
-- @--ablation-only@ skips the Lean preflight and the timing\/agreement sweep
-- and emits only @measurements\/ablation.{json,tsv}@ (a seconds-long smoke
-- loop instead of the full sampling run).
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (replicateM, unless, when)
import Data.List (dropWhileEnd)
import Data.Char (isSpace)
import GHC.Clock (getMonotonicTimeNSec)
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitFailure)
import System.Info (arch, os)
import System.IO (hPutStrLn, stderr)
import System.Process
  ( CreateProcess (cwd)
  , proc
  , readCreateProcessWithExitCode
  , readProcessWithExitCode
  )

import Lara.Check (CheckConfig)
import Lara.Driver (runCheck)
import Lara.Measure
import Lara.Mutate (Expected (..))
import Lara.Wire (decodeCheckInputFile, encodeCheckInput, encodeVerdict, printSExpr)

leanBin :: FilePath
leanBin = "lean/.lake/build/bin/lara-driver"

samples :: Int
samples = 5

main :: IO ()
main = do
  args <- getArgs
  ablationOnly <- case args of
    [] -> pure False
    ["--ablation-only"] -> pure True
    _ -> die ("unrecognized arguments: " ++ unwords args ++ " (only --ablation-only is accepted)")
  unless ablationOnly preflightLean
  mutantManifest <- readFile "fixtures/mutants/MANIFEST.tsv"
  corpusManifest <- readFile "corpus-units/MANIFEST.tsv"
  let inputs = parseMutantManifest mutantManifest ++ parseCorpusManifest corpusManifest
  when (null inputs) (die "no inputs discovered from the manifests")
  env <- gatherEnv
  createDirectoryIfMissing True "measurements"
  ablations <- mapM (runAblation inputs) ablationConfigs
  writeFile "measurements/ablation.json" (ablationJson env ablations)
  writeFile "measurements/ablation.tsv" (ablationTsv ablations)
  putStrLn
    ( "wrote " ++ show (length ablations) ++ " ablation runs over "
        ++ show (length inputs) ++ " inputs to measurements/ablation.{json,tsv}"
    )
  unless ablationOnly $ do
    records <- mapM measureInput inputs
    writeFile "measurements/report.json" (reportJson env records)
    writeFile "measurements/report.tsv" (reportTsv records)
    putStrLn ("wrote " ++ show (length records) ++ " records to measurements/")

-- | Build the Lean driver the way @scripts\/differential.sh@ does, failing
-- loudly with a build hint rather than a mid-run subprocess error.
preflightLean :: IO ()
preflightLean = do
  (code, _out, err) <- readCreateProcessWithExitCode (proc "lake" ["build"]) {cwd = Just "lean"} ""
  case code of
    ExitSuccess -> pure ()
    ExitFailure _ -> die ("lake build failed (run `cd lean && lake build`):\n" ++ err)
  present <- doesFileExist leanBin
  unless present (die ("Lean driver missing after lake build: " ++ leanBin))

-- | One named ablation pass over every input: 'computeAblation' re-runs the
-- checker under the ablated config against the full one. Haskell-only by
-- construction — no Lean subprocess, no timing samples.
runAblation :: [InputMeta] -> (String, CheckConfig, [AblationBucket]) -> IO AblationReport
runAblation inputs (name, cfg, _buckets) = do
  cells <- mapM cellFor inputs
  pure (AblationReport name cells)
  where
    -- Force the read so at most one file handle is open at a time.
    cellFor im = do
      bytes <- readFile (imPath im)
      length bytes `seq` pure (computeAblation cfg im bytes)

-- | Measure one input: the deterministic metrics (pure), the @hs_check@ timing
-- samples, and the Lean subprocess timing + agreement.
measureInput :: InputMeta -> IO Record
measureInput im = do
  bytes <- readFile (imPath im)
  let det = computeDeterministic im bytes
  hsNs <- replicateM samples (timeHsCheck im bytes)
  (leanNs, agree) <- measureLean im bytes
  pure (Record im det agree hsNs leanNs)

-- | The @hs_check@ timed section: for a verdict row, decode is forced OUTSIDE
-- timing and the timed work is @runCheck@ + rendering the verdict to text
-- (forced with @length@); for a codec row, the timed work is the decode failure
-- (its own protocol).
timeHsCheck :: InputMeta -> String -> IO Integer
timeHsCheck im bytes = case imExpected im of
  ExpectCodecReject -> timed (evaluate (decodeFailureLen bytes))
  _ -> case decodeCheckInputFile bytes of
    Left _ -> timed (evaluate (decodeFailureLen bytes))
    Right input -> do
      _ <- evaluate (length (printSExpr (encodeCheckInput input))) -- force decode, excluded
      timed (evaluate (length (printSExpr (encodeVerdict (runCheck input)))))
  where
    decodeFailureLen b = case decodeCheckInputFile b of
      Left err -> length (show err)
      Right _ -> 0

-- | Time an action in nanoseconds via the monotonic clock.
timed :: IO a -> IO Integer
timed act = do
  t0 <- getMonotonicTimeNSec
  _ <- act
  t1 <- getMonotonicTimeNSec
  pure (fromIntegral (t1 - t0))

-- | Run the Lean driver @samples@ times: the retained wall-time samples, and the
-- @lean_agree@ verdict computed from one run's stdout/exit/stderr.
measureLean :: InputMeta -> String -> IO ([Integer], Maybe Bool)
measureLean im bytes = do
  runs <- replicateM samples (timeLean (imPath im))
  let leanNs = [ns | (ns, _, _, _) <- runs]
      agree = case runs of
        [] -> Nothing -- samples >= 1, unreachable
        ((_, out, code, err) : _) ->
          Just $ case imExpected im of
            ExpectCodecReject -> leanAgreeCodec (imLeanDiag im) code out err
            _ -> case decodeCheckInputFile bytes of
              Right input -> leanAgreeVerdict (runCheck input) out code
              Left _ -> False
  pure (leanNs, agree)

-- | One timed Lean subprocess run: @(wall ns, stdout, exit code, stderr)@.
timeLean :: FilePath -> IO (Integer, String, Int, String)
timeLean path = do
  t0 <- getMonotonicTimeNSec
  (code, out, err) <- readProcessWithExitCode leanBin [path] ""
  t1 <- getMonotonicTimeNSec
  pure (fromIntegral (t1 - t0), out, exitInt code, err)

exitInt :: ExitCode -> Int
exitInt ExitSuccess = 0
exitInt (ExitFailure n) = n

-- | The reproducibility environment block (git rev + dirty flag, tool versions,
-- OS, CPU); best-effort — a missing tool yields an empty field, not a failure.
gatherEnv :: IO EnvBlock
gatherEnv = do
  rev <- capture "git" ["rev-parse", "HEAD"]
  dirty <- capture "git" ["status", "--porcelain"]
  ghc <- capture "ghc" ["--numeric-version"]
  leanVer <- capture "lean" ["--version"]
  pure
    EnvBlock
      { envGitRev = rev
      , envGitDirty = not (null dirty)
      , envGhc = ghc
      , envLean = leanVer
      , envOs = os
      , envCpu = arch
      }

-- | Run a command and return its trimmed stdout, or @""@ on any failure.
capture :: String -> [String] -> IO String
capture cmd args = do
  (code, out, _err) <- readProcessWithExitCode cmd args ""
  pure $ case code of
    ExitSuccess -> trim out
    ExitFailure _ -> ""

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace

die :: String -> IO a
die msg = hPutStrLn stderr ("measure: " ++ msg) >> exitFailure
