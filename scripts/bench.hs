-- | The checker-performance bench (E1, issue #69).
--
-- One command that measures the production checker on the frozen corpus
-- units and the manifest-discovered harness and emits the paper's performance
-- table (@tables\/performance.tex@) plus a raw JSON record
-- (@measurements\/bench.json@) — the table is generated, never hand-typed.
--
-- Protocols (deliberately aligned with @scripts\/measure.hs@):
--
-- * @hs@ sections are in-process and exclude decode: the timed work is
--   @runCheck@ plus forcing the rendered verdict text. Because one check runs
--   in single-digit microseconds (below timer noise), every timed section
--   here runs the work 'reps' times and divides; the reported value is the
--   median of 'samples' such sections.
-- * Phase sections time the pipeline's stages against their forced outputs:
--   parse (decode + forced re-encode), validate (replay preflight + group
--   boundary), check (the six-stage @checkUnitWith@, deep-forced), compile
--   (the cached-adjacency AF and its closure-edge list), evaluate (grounded
--   labels + per-query four-state statuses, over a pre-built AF). Earlier
--   phases' results are pre-forced before a later phase is timed, so phases
--   are attributable but need not sum exactly to the end-to-end section.
-- * @lean@ is full subprocess wall time of the reference driver (startup +
--   decode included) — a DIFFERENT protocol, reported only to justify why
--   the Lean driver stays a test oracle; no cross-driver ratio may be
--   derived.
-- * The harness sweep pre-reads every manifest input, then times one full
--   in-memory pass (decode + check + render, or the codec failure path).
--
-- Timing numbers are reproducible-but-unfrozen (the @measure.hs@
-- discipline): @measurements\/@ is gitignored, and the committed
-- @tables\/performance.tex@ is refreshed by re-running @make bench@.
--
-- Run with the built library on the path:
--
-- >  cabal exec -- runghc scripts/bench.hs
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM, forM_, replicateM, unless, when)
import Data.List (intercalate, maximumBy, nub, sortOn)
import Data.Ord (comparing)
import GHC.Clock (getMonotonicTimeNSec)
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.Exit (ExitCode (..), exitFailure)
import System.IO (hPutStrLn, stderr)
import System.Info (arch, os)
import System.Process
  ( CreateProcess (cwd)
  , proc
  , readCreateProcessWithExitCode
  , readProcessWithExitCode
  )

import Lara.AST (Unit (..))
import Lara.Check (checkUnitWith, cuNodes, cuProgram, fullConfig)
import Lara.Driver (buildCertOk, buildGamma, groupConflictReject, quarantineUnit, runCheck)
import Lara.Grounded (AF (..), completeClaimFor, labelC, statusC)
import Lara.Measure (InputMeta (..), median, parseCorpusManifest, parseMutantManifest)
import Lara.Mutate (Expected (..))
import Lara.Replay (inputUnit, runtimeReplayFailure)
import Lara.Runtime (runtimeAF)
import Lara.Wire
  ( Outcome (..)
  , Verdict (..)
  , decodeCheckInputFile
  , encodeCheckInput
  , encodeVerdict
  , printSExpr
  )

leanBin :: FilePath
leanBin = "lean/.lake/build/bin/lara-driver"

-- | Repetitions inside one timed section: one corpus check runs in
-- single-digit microseconds, below single-shot timer noise.
reps :: Int
reps = 100

-- | Timed sections per number; the median is reported.
samples :: Int
samples = 5

-- | Full harness-sweep passes; the median is reported.
sweepSamples :: Int
sweepSamples = 3

main :: IO ()
main = do
  preflightLean
  mutantManifest <- readFile "fixtures/mutants/MANIFEST.tsv"
  corpusManifest <- readFile "corpus-units/MANIFEST.tsv"
  let mutants = parseMutantManifest mutantManifest
      corpus = parseCorpusManifest corpusManifest
      inputs = mutants ++ corpus
      inputCount = length inputs
  validateManifest "mutant" (mutantManifestRowCount mutantManifest) mutants
  validateManifest "corpus" (corpusManifestRowCount corpusManifest) corpus
  env <- gatherEnv
  units <- mapM benchUnit corpus
  sweepNs <- benchSweep inputs
  createDirectoryIfMissing True "measurements"
  createDirectoryIfMissing True "tables"
  writeFile "measurements/bench.json" (benchJson env inputCount units sweepNs)
  writeFile "tables/performance.tex" (performanceTex env inputCount units sweepNs)
  putStrLn
    ( "wrote " ++ show (length units)
        ++ " unit benches and one " ++ show inputCount
        ++ "-record harness sweep to measurements/bench.json and tables/performance.tex"
    )

preflightLean :: IO ()
preflightLean = do
  (code, _out, err) <- readCreateProcessWithExitCode (proc "lake" ["build"]) {cwd = Just "lean"} ""
  case code of
    ExitSuccess -> pure ()
    ExitFailure _ -> die ("lake build failed (run `cd lean && lake build`):\n" ++ err)
  present <- doesFileExist leanBin
  unless present (die ("Lean driver missing after lake build: " ++ leanBin))

die :: String -> IO a
die msg = hPutStrLn stderr ("bench: " ++ msg) >> exitFailure

-- | Reject silent parser drops without pinning the suite to one frozen count.
-- The shared manifest parsers deliberately return lists, so the benchmark
-- cross-checks their output against the independently visible data-row count
-- before publishing timings.
validateManifest :: String -> Int -> [a] -> IO ()
validateManifest label rowCount parsed = do
  when (rowCount == 0) (die (label ++ " manifest contains no data rows"))
  unless (length parsed == rowCount) $
    die
      ( label ++ " manifest parsed " ++ show (length parsed)
          ++ " of " ++ show rowCount ++ " data rows"
      )

mutantManifestRowCount :: String -> Int
mutantManifestRowCount raw =
  length
    [ ()
    | ln <- lines raw
    , not (null ln)
    , take 1 ln /= "#"
    ]

corpusManifestRowCount :: String -> Int
corpusManifestRowCount =
  length . filter (not . null) . drop 1 . lines

-- | One corpus unit's measurements. All times in nanoseconds (already
-- divided by 'reps' where batched).
data UnitBench = UnitBench
  { ubBase :: String -- ^ @artifact.claim@
  , ubArtifact :: String
  , ubTotalNs :: Integer -- ^ end-to-end decode + check + render
  , ubKernelNs :: Integer -- ^ check + render over the pre-decoded input
  , ubParseNs :: Integer -- ^ derived: total minus kernel (marginal decode)
  , ubValidateNs :: Integer
  , ubCheckNs :: Integer
  , ubCompileNs :: Integer
  , ubEvaluateNs :: Integer
  , ubLeanNs :: Integer -- ^ subprocess wall (different protocol)
  , ubNodes :: Int
  , ubEdges :: Int
  }

benchUnit :: InputMeta -> IO UnitBench
benchUnit im = do
  bytes <- readFile (imPath im)
  _ <- evaluate (length bytes)
  input <- case decodeCheckInputFile bytes of
    Left err -> die (imPath im ++ ": decode failed: " ++ show err)
    Right i -> pure i
  _ <- evaluate (length (printSExpr (encodeCheckInput input))) -- pre-force decode
  let unit = inputUnit input
      qunit = quarantineUnit unit
      gamma = buildGamma (unitLeaves qunit)
      certOk = buildCertOk (unitTheories qunit)
  -- End-to-end section: what the CLI does minus file IO — decode, check,
  -- render the verdict.
  totalNs <- medianSection
    (\b -> case decodeCheckInputFile b of
      Left err -> evaluate (length (show err))
      Right i -> evaluate (length (printSExpr (encodeVerdict (runCheck i)))))
    bytes
  -- The measure.hs kernel protocol: check + render over the pre-decoded
  -- input. Parse is reported as the marginal decode cost inside the real
  -- pipeline: end-to-end minus this kernel section.
  kernelNs <- medianSection
    (\x -> evaluate (length (printSExpr (encodeVerdict (runCheck x)))))
    input
  let parseNs = max 0 (totalNs - kernelNs)
  validateNs <- medianSection
    (\x -> evaluate
      ( maybe (0 :: Int) (const 1) (runtimeReplayFailure x)
          + (if groupConflictReject (inputUnit x) then 1 else 0)
      ))
    input
  checkNs <- medianSection
    (\u -> evaluate (length (show (checkUnitWith fullConfig gamma certOk u))))
    qunit
  checked <- case checkUnitWith fullConfig gamma certOk qunit of
    Left err -> die (imPath im ++ ": corpus unit rejected: " ++ show err)
    Right cu -> do
      _ <- evaluate (length (show cu)) -- pre-force the checked unit
      pure cu
  compileNs <- medianSection
    (\cu ->
      let af = runtimeAF (cuProgram cu)
          n = length (afArgs af)
       in evaluate (n + length [(i, j) | i <- [0 .. n - 1], j <- [0 .. n - 1], afAttack af i j]))
    checked
  let af0 = runtimeAF (cuProgram checked)
      n0 = length (afArgs af0)
  _ <- evaluate (n0 + length [(i, j) | i <- [0 .. n0 - 1], j <- [0 .. n0 - 1], afAttack af0 i j])
  evaluateNs <- medianSection
    (\af -> evaluate (length (show
      ( [(i, labelC af i) | i <- [0 .. n0 - 1]]
      , [(p, statusC af (completeClaimFor (cuNodes checked) p)) | p <- unitQueries unit]
      ))))
    af0
  leanRuns <- replicateM samples (timeLean (imPath im))
  leanNs <- maybe (die (imPath im ++ ": no lean samples")) pure (median leanRuns)
  (nodes, edges) <- case runCheck input of
    Verdict _ Accept {verdictLabels = ls, verdictEdges = es} -> pure (length ls, length es)
    _ -> die (imPath im ++ ": corpus unit did not accept")
  pure
    UnitBench
      { ubBase = imBase im
      , ubArtifact = takeWhile (/= '.') (imBase im)
      , ubTotalNs = totalNs
      , ubKernelNs = kernelNs
      , ubParseNs = parseNs
      , ubValidateNs = validateNs
      , ubCheckNs = checkNs
      , ubCompileNs = compileNs
      , ubEvaluateNs = evaluateNs
      , ubLeanNs = leanNs
      , ubNodes = nodes
      , ubEdges = edges
      }

-- | Median over 'samples' timed sections; each section runs the action
-- 'reps' times over distinct copies of the argument and divides.
medianSection :: (a -> IO b) -> a -> IO Integer
medianSection act x = do
  ns <- replicateM samples $ do
    t0 <- getMonotonicTimeNSec
    mapM_ act (replicate reps x)
    t1 <- getMonotonicTimeNSec
    pure (toInteger (t1 - t0) `div` toInteger reps)
  maybe (die "no timing samples") pure (median ns)

timeLean :: FilePath -> IO Integer
timeLean path = do
  t0 <- getMonotonicTimeNSec
  _ <- readProcessWithExitCode leanBin [path] ""
  t1 <- getMonotonicTimeNSec
  pure (toInteger (t1 - t0))

-- | One full pass over every harness record, in memory: decode + check +
-- render (or the codec-failure path, its own protocol, as in measure.hs).
benchSweep :: [InputMeta] -> IO Integer
benchSweep inputs = do
  loaded <- forM inputs $ \im -> do
    bytes <- readFile (imPath im)
    _ <- evaluate (length bytes)
    pure (imExpected im, bytes)
  ns <- replicateM sweepSamples $ do
    t0 <- getMonotonicTimeNSec
    forM_ loaded $ \(expected, bytes) -> case expected of
      ExpectCodecReject -> evaluate (codecLen bytes)
      _ -> case decodeCheckInputFile bytes of
        Left _ -> evaluate (codecLen bytes)
        Right input -> evaluate (length (printSExpr (encodeVerdict (runCheck input))))
    t1 <- getMonotonicTimeNSec
    pure (toInteger (t1 - t0))
  maybe (die "no sweep samples") pure (median ns)
  where
    codecLen b = case decodeCheckInputFile b of
      Left err -> length (show err)
      Right _ -> 0

-- | Environment of record: hardware + toolchain, best-effort per platform.
data Env = Env
  { envCpuModel :: String
  , envRamBytes :: Maybe Integer
  , envOsArch :: String
  , envGhc :: String
  , envLean :: String
  , envGitRev :: String
  }

gatherEnv :: IO Env
gatherEnv = do
  rev <- capture "git" ["rev-parse", "--short", "HEAD"]
  ghc <- capture "ghc" ["--numeric-version"]
  leanVer <- capture "lean" ["--version"]
  cpuDarwin <- capture "sysctl" ["-n", "machdep.cpu.brand_string"]
  memDarwin <- capture "sysctl" ["-n", "hw.memsize"]
  pure
    Env
      { envCpuModel = if null cpuDarwin then arch else cpuDarwin
      , envRamBytes = if null memDarwin then Nothing else Just (read memDarwin)
      , envOsArch = os ++ "/" ++ arch
      , envGhc = ghc
      , envLean = case words leanVer of
          ("Lean" : "(version" : v : _) -> "Lean " ++ takeWhile (/= ',') v
          _ -> takeWhile (/= ',') leanVer
      , envGitRev = rev
      }

capture :: String -> [String] -> IO String
capture cmd args = do
  (code, out, _err) <- readProcessWithExitCode cmd args ""
  pure $ case code of
    ExitSuccess -> trim out
    ExitFailure _ -> ""
  where
    trim = f . f
    f = reverse . dropWhile (`elem` " \t\r\n")

-- Statistics helpers ---------------------------------------------------------

medianOf :: [Integer] -> Integer
medianOf xs = maybe 0 id (median xs)

worstOf :: [(String, Integer)] -> (String, Integer)
worstOf = maximumBy (comparing snd)

-- | Nanoseconds to microseconds with one decimal.
us1 :: Integer -> String
us1 ns = showFixed1 (fromIntegral ns / 1000 :: Double)

-- | Nanoseconds to milliseconds with one decimal.
ms1 :: Integer -> String
ms1 ns = showFixed1 (fromIntegral ns / 1e6 :: Double)

showFixed1 :: Double -> String
showFixed1 x =
  let r = fromIntegral (round (x * 10) :: Integer) / 10 :: Double
      (w, f) = properFraction r :: (Integer, Double)
   in show w ++ "." ++ show (round (f * 10) :: Integer)

-- Rendering ------------------------------------------------------------------

benchJson :: Env -> Int -> [UnitBench] -> Integer -> String
benchJson env inputCount units sweepNs =
  unlines $
    [ "{"
    , "  \"environment\": {"
    , "    \"cpu\": " ++ jstr (envCpuModel env) ++ ","
    , "    \"ram_bytes\": " ++ maybe "null" show (envRamBytes env) ++ ","
    , "    \"os_arch\": " ++ jstr (envOsArch env) ++ ","
    , "    \"ghc\": " ++ jstr (envGhc env) ++ ","
    , "    \"lean\": " ++ jstr (envLean env) ++ ","
    , "    \"git_rev\": " ++ jstr (envGitRev env) ++ ","
    , "    \"reps\": " ++ show reps ++ ","
    , "    \"samples\": " ++ show samples
    , "  },"
    , "  \"sweep_records\": " ++ show inputCount ++ ","
    , "  \"sweep_ns\": " ++ show sweepNs ++ ","
    , "  \"units\": ["
    ]
      ++ [ "    {\"base\": " ++ jstr (ubBase u)
             ++ ", \"total_ns\": " ++ show (ubTotalNs u)
             ++ ", \"kernel_ns\": " ++ show (ubKernelNs u)
             ++ ", \"parse_ns\": " ++ show (ubParseNs u)
             ++ ", \"validate_ns\": " ++ show (ubValidateNs u)
             ++ ", \"check_ns\": " ++ show (ubCheckNs u)
             ++ ", \"compile_ns\": " ++ show (ubCompileNs u)
             ++ ", \"evaluate_ns\": " ++ show (ubEvaluateNs u)
             ++ ", \"lean_wall_ns\": " ++ show (ubLeanNs u)
             ++ ", \"nodes\": " ++ show (ubNodes u)
             ++ ", \"edges\": " ++ show (ubEdges u)
             ++ "}" ++ (if ubBase u == ubBase (last units) then "" else ",")
         | u <- units
         ]
      ++ ["  ]", "}"]
  where
    jstr s = "\"" ++ concatMap esc s ++ "\""
    esc '"' = "\\\""
    esc '\\' = "\\\\"
    esc c = [c]

performanceTex :: Env -> Int -> [UnitBench] -> Integer -> String
performanceTex env inputCount units sweepNs =
  unlines
    [ "% Generated by scripts/bench.hs (make bench) at " ++ envGitRev env ++ " -- do not edit."
    , "% Setting (stated in prose in src/evaluation.tex; keep in sync): "
        ++ show inputCount ++ "-record harness; "
        ++ envCpuModel env ++ ", " ++ ramGb ++ " GB RAM, "
        ++ envOsArch env ++ ", GHC " ++ envGhc env ++ ", " ++ envLean env
        ++ "; medians over " ++ show samples ++ " sections of "
        ++ show reps ++ " batched runs each."
    , "\\begin{table}[t]"
    , "\\caption{Production-checker performance. End-to-end is"
    , "decode + check + verdict render; each phase is timed with earlier"
    , "stages pre-forced, so phases need not sum exactly.}"
    , "\\label{tab:performance}"
    , "\\centering"
    , "\\small"
    , "\\begin{tabular}{@{}lrr@{}}"
    , "\\toprule"
    , " & median & worst \\\\"
    , "\\midrule"
    , "Corpus unit, end-to-end (\\si{\\micro\\second}) & "
        ++ num (us1 (medianOf totals)) ++ " & " ++ num (us1 (snd worstTotal)) ++ " \\\\"
    , "\\quad parse (\\si{\\micro\\second}) & "
        ++ num (us1 (medianOf (map ubParseNs units))) ++ " & " ++ num (us1 (maximum (map ubParseNs units))) ++ " \\\\"
    , "\\quad check + render, pre-decoded (\\si{\\micro\\second}) & "
        ++ num (us1 (medianOf (map ubKernelNs units))) ++ " & " ++ num (us1 (maximum (map ubKernelNs units))) ++ " \\\\"
    , "\\quad validate (\\si{\\micro\\second}) & "
        ++ num (us1 (medianOf (map ubValidateNs units))) ++ " & " ++ num (us1 (maximum (map ubValidateNs units))) ++ " \\\\"
    , "\\quad check (\\si{\\micro\\second}) & "
        ++ num (us1 (medianOf (map ubCheckNs units))) ++ " & " ++ num (us1 (maximum (map ubCheckNs units))) ++ " \\\\"
    , "\\quad compile (\\si{\\micro\\second}) & "
        ++ num (us1 (medianOf (map ubCompileNs units))) ++ " & " ++ num (us1 (maximum (map ubCompileNs units))) ++ " \\\\"
    , "\\quad evaluate (\\si{\\micro\\second}) & "
        ++ num (us1 (medianOf (map ubEvaluateNs units))) ++ " & " ++ num (us1 (maximum (map ubEvaluateNs units))) ++ " \\\\"
    , "Per-artifact total (" ++ show (length artifacts) ++ " artifacts, \\si{\\micro\\second}) & "
        ++ num (us1 (medianOf (map snd artifactTotals))) ++ " & " ++ num (us1 (snd worstArtifact)) ++ " \\\\"
    , "Framework size (nodes / edges) & "
        ++ show (medianOf (map (toInteger . ubNodes) units)) ++ " / "
        ++ show (medianOf (map (toInteger . ubEdges) units)) ++ " & "
        ++ show (maximum (map ubNodes units)) ++ " / "
        ++ show (maximum (map ubEdges units)) ++ " \\\\"
    , "Lean reference driver, subprocess (\\si{\\milli\\second}) & "
        ++ num (ms1 (medianOf (map ubLeanNs units))) ++ " & " ++ num (ms1 (maximum (map ubLeanNs units))) ++ " \\\\"
    , "\\midrule"
    , show inputCount ++ "-record harness, one full pass (\\si{\\milli\\second}) & \\multicolumn{2}{r}{"
        ++ num (ms1 sweepNs) ++ "} \\\\"
    , "\\bottomrule"
    , "\\end{tabular}"
    , "\\end{table}"
    ]
  where
    totals = map ubTotalNs units
    worstTotal = worstOf [(ubBase u, ubTotalNs u) | u <- units]
    artifacts = nub (map ubArtifact units)
    artifactTotals =
      [ (a, sum [ubTotalNs u | u <- units, ubArtifact u == a])
      | a <- artifacts
      ]
    worstArtifact = worstOf artifactTotals
    num s = "\\num{" ++ s ++ "}"
    ramGb = maybe "?" (\b -> show (b `div` (1024 * 1024 * 1024))) (envRamBytes env)
