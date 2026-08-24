-- | The checker-performance bench (E1, issue #69).
--
-- One command that measures the production checker on the frozen corpus
-- units and the manifest-discovered harness, prints the performance table in
-- the requested format, and writes a raw JSON record
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
-- discipline): @measurements\/@ is gitignored and no rendered table is
-- committed to this repository. A table is machine state, not source — it is
-- valid only for the machine and commit that produced it — so it is printed
-- on demand and pasted into whichever document consumes it (the paper
-- repository owns its own @tables\/performance.tex@).
--
-- Run with the built library on the path:
--
-- >  cabal exec -- runghc scripts/bench.hs
-- >  cabal exec -- runghc scripts/bench.hs --format=latex --out ../paper/tables/performance.tex
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM, forM_, replicateM, unless, when)
import qualified Data.ByteString as B
import Data.List (intercalate, maximumBy, nub, stripPrefix)
import Data.Ord (comparing)
import GHC.Clock (getMonotonicTimeNSec)
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.Environment (getArgs, lookupEnv)
import System.Exit (ExitCode (..), exitFailure, exitSuccess)
import System.IO
  ( IOMode (WriteMode)
  , hPutStr
  , hPutStrLn
  , hSetEncoding
  , stderr
  , stdout
  , utf8
  , withFile
  )
import System.FilePath ((</>))
import System.Info (arch, os)
import System.Process
  ( CreateProcess (cwd)
  , proc
  , readCreateProcessWithExitCode
  , readProcessWithExitCode
  )
import Text.Read (readMaybe)

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
  , decodeCheckInputFileBS
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
  argv <- getArgs
  when ("--help" `elem` argv || "-h" `elem` argv) (putStrLn usage >> exitSuccess)
  opts <- either (\e -> die (e ++ "\n" ++ usage)) pure (parseOptions argv)
  preflightLean (optPrebuilt opts)
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
  let raw = benchJson env inputCount units sweepNs
      table fmt = renderTable fmt env inputCount units sweepNs
  rawPath <- case optOutputDir opts of
    Just dir -> do
      createDirectoryIfMissing True dir
      writeFile (dir </> "bench.json") raw
      emit (Just (dir </> "performance.txt")) (table FmtText)
      emit (Just (dir </> "performance.md")) (table FmtMarkdown)
      emit (Just (dir </> "performance.tex")) (table FmtLatex)
      pure (dir </> "bench.json")
    Nothing -> do
      createDirectoryIfMissing True "measurements"
      writeFile "measurements/bench.json" raw
      emit (optOut opts) (table (optFormat opts))
      pure "measurements/bench.json"
  -- Progress goes to stderr so the table itself stays pipeable on stdout.
  hPutStrLn
    stderr
    ( "bench: " ++ show (length units)
        ++ " unit benches and one " ++ show inputCount
        ++ "-record harness sweep; raw record in " ++ rawPath
        ++ maybe "" ("; table written to " ++) (optOut opts)
        ++ maybe "" ("; all formats written to " ++) (optOutputDir opts)
    )

preflightLean :: Bool -> IO ()
preflightLean prebuilt = do
  unless prebuilt $ do
    (code, _out, err) <- readCreateProcessWithExitCode (proc "lake" ["build"]) {cwd = Just "lean"} ""
    case code of
      ExitSuccess -> pure ()
      ExitFailure _ -> die ("lake build failed (run `cd lean && lake build`):\n" ++ err)
  present <- doesFileExist leanBin
  unless present $
    die
      ( if prebuilt
          then "Lean driver missing in --prebuilt mode: " ++ leanBin
          else "Lean driver missing after lake build: " ++ leanBin
      )

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
  bytes <- B.readFile (imPath im)
  _ <- evaluate (B.length bytes)
  input <- case decodeCheckInputFileBS bytes of
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
    (\b -> case decodeCheckInputFileBS b of
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
  (code, _out, err) <- readProcessWithExitCode leanBin [path] ""
  t1 <- getMonotonicTimeNSec
  case code of
    ExitSuccess -> pure (toInteger (t1 - t0))
    ExitFailure n ->
      die
        ( "Lean driver failed with exit " ++ show n ++ " for " ++ path
            ++ if null err then "" else ":\n" ++ err
        )

-- | One full pass over every harness record, in memory: decode + check +
-- render (or the codec-failure path, its own protocol, as in measure.hs).
benchSweep :: [InputMeta] -> IO Integer
benchSweep inputs = do
  loaded <- forM inputs $ \im -> do
    bytes <- B.readFile (imPath im)
    _ <- evaluate (B.length bytes)
    pure (imExpected im, bytes)
  ns <- replicateM sweepSamples $ do
    t0 <- getMonotonicTimeNSec
    forM_ loaded $ \(expected, bytes) -> case expected of
      ExpectCodecReject -> evaluate (codecLen bytes)
      _ -> case decodeCheckInputFileBS bytes of
        Left _ -> evaluate (codecLen bytes)
        Right input -> evaluate (length (printSExpr (encodeVerdict (runCheck input))))
    t1 <- getMonotonicTimeNSec
    pure (toInteger (t1 - t0))
  maybe (die "no sweep samples") pure (median ns)
  where
    codecLen b = case decodeCheckInputFileBS b of
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
  rev <- captureOverride "LARA_BENCH_GIT_REV" "git" ["rev-parse", "HEAD"]
  ghc <- captureOverride "LARA_BENCH_GHC_VERSION" "ghc" ["--numeric-version"]
  leanVer <- captureOverride "LARA_BENCH_LEAN_VERSION" "lean" ["--version"]
  cpu <- captureOverride "LARA_BENCH_HOST_CPU" "sysctl" ["-n", "machdep.cpu.brand_string"]
  memOverride <- lookupEnv "LARA_BENCH_HOST_RAM_BYTES"
  mem <- case memOverride of
    Nothing -> readMaybe <$> capture "sysctl" ["-n", "hw.memsize"]
    Just raw -> case readMaybe raw of
      Just bytes | bytes >= 0 -> pure (Just bytes)
      _ -> die ("invalid LARA_BENCH_HOST_RAM_BYTES " ++ show raw)
  pure
    Env
      { envCpuModel = if null cpu then arch else cpu
      , envRamBytes = mem
      , envOsArch = os ++ "/" ++ arch
      , envGhc = ghc
      , envLean = case words leanVer of
          ("Lean" : "(version" : v : _) -> "Lean " ++ takeWhile (/= ',') v
          _ -> takeWhile (/= ',') leanVer
      , envGitRev = rev
      }

captureOverride :: String -> String -> [String] -> IO String
captureOverride name cmd args = do
  override <- lookupEnv name
  case override of
    Nothing -> capture cmd args
    Just "" -> die ("empty " ++ name)
    Just value -> pure value

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

-- | The environment-of-record line the table header and the paper's prose
-- must agree on.
settingLine :: Env -> Int -> String
settingLine env inputCount =
  show inputCount ++ "-record harness; "
    ++ envCpuModel env ++ ", " ++ ramGb ++ " GB RAM, "
    ++ envOsArch env ++ ", GHC " ++ envGhc env ++ ", " ++ envLean env
    ++ "; medians over " ++ show samples ++ " sections of "
    ++ show reps ++ " batched runs each."
  where
    ramGb = maybe "?" (\b -> show (b `div` (1024 * 1024 * 1024))) (envRamBytes env)

-- | The table's content, independent of how it is spelled.
benchRows :: Int -> [UnitBench] -> Integer -> [Row]
benchRows inputCount units sweepNs =
  [ Row (plain 0 "Corpus unit, end-to-end" Micro)
      (usNum (medianOf totals))
      (usNum (snd worstTotal))
  , phase "parse" ubParseNs
  , phase "check + render, pre-decoded" ubKernelNs
  , phase "validate" ubValidateNs
  , phase "check" ubCheckNs
  , phase "compile" ubCompileNs
  , phase "evaluate" ubEvaluateNs
  , Row (Label 0 "Per-artifact total" (Just (show (length artifacts) ++ " artifacts")) Micro)
      (usNum (medianOf (map snd artifactTotals)))
      (usNum (snd worstArtifact))
  , Row (plain 0 "Framework size (nodes / edges)" Bare)
      (sizeCell medianOf)
      (sizeCell maximum)
  , Row (plain 0 "Lean reference driver, subprocess" Milli)
      (msNum (medianOf (map ubLeanNs units)))
      (msNum (maximum (map ubLeanNs units)))
  , RowRule
  , RowSpan
      (plain 0 (show inputCount ++ "-record harness, one full pass") Milli)
      (msNum sweepNs)
  ]
  where
    plain ind lbl = Label ind lbl Nothing
    usNum = Num . us1
    msNum = Num . ms1
    phase lbl field =
      Row
        (plain 1 lbl Micro)
        (usNum (medianOf (map field units)))
        (usNum (maximum (map field units)))
    sizeCell agg =
      Plain
        ( show (agg (map (toInteger . ubNodes) units))
            ++ " / "
            ++ show (agg (map (toInteger . ubEdges) units))
        )
    totals = map ubTotalNs units
    worstTotal = worstOf [(ubBase u, ubTotalNs u) | u <- units]
    artifacts = nub (map ubArtifact units)
    artifactTotals =
      [ (a, sum [ubTotalNs u | u <- units, ubArtifact u == a])
      | a <- artifacts
      ]
    worstArtifact = worstOf artifactTotals

renderTable :: Format -> Env -> Int -> [UnitBench] -> Integer -> String
renderTable fmt env inputCount units sweepNs = case fmt of
  FmtLatex -> latexTable env setting rows
  FmtMarkdown -> markdownTable setting rows
  FmtText -> textTable setting rows
  where
    rows = benchRows inputCount units sweepNs
    setting = settingLine env inputCount

-- LaTeX ----------------------------------------------------------------------

latexTable :: Env -> String -> [Row] -> String
latexTable env setting rows =
  unlines $
    [ "% Generated by scripts/bench.hs (make bench) at " ++ envGitRev env ++ " -- do not edit."
    , "% Setting (stated in prose in src/evaluation.tex; keep in sync): " ++ setting
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
    ]
      ++ map latexRow rows
      ++ [ "\\bottomrule"
         , "\\end{tabular}"
         , "\\end{table}"
         ]

latexRow :: Row -> String
latexRow RowRule = "\\midrule"
latexRow (Row l m w) =
  labelText FmtLatex l ++ " & " ++ cellText FmtLatex m ++ " & " ++ cellText FmtLatex w ++ " \\\\"
latexRow (RowSpan l v) =
  labelText FmtLatex l ++ " & \\multicolumn{2}{r}{" ++ cellText FmtLatex v ++ "} \\\\"

-- Markdown and plain text ----------------------------------------------------

-- | A row reduced to already-spelled strings, for the two column formats.
data PlainRow = PlainRule | PlainCells String String String

plainRow :: Format -> Row -> PlainRow
plainRow _ RowRule = PlainRule
plainRow fmt (Row l m w) = PlainCells (labelText fmt l) (cellText fmt m) (cellText fmt w)
plainRow fmt (RowSpan l v) = PlainCells (labelText fmt l) (cellText fmt v) ""

captionLines :: [String]
captionLines =
  [ "Production-checker performance. End-to-end is decode + check + verdict"
  , "render; each phase is timed with earlier stages pre-forced, so phases"
  , "need not sum exactly."
  ]

markdownTable :: String -> [Row] -> String
markdownTable setting rows =
  unlines $
    captionLines
      ++ [ ""
         , "_Setting: " ++ setting ++ "_"
         , ""
         , "| | median | worst |"
         , "| --- | ---: | ---: |"
         ]
      ++ map (markdownRow . plainRow FmtMarkdown) rows

markdownRow :: PlainRow -> String
markdownRow PlainRule = "| | | |"
markdownRow (PlainCells l m w) = "| " ++ l ++ " | " ++ m ++ " | " ++ w ++ " |"

textTable :: String -> [Row] -> String
textTable setting rows =
  unlines $
    captionLines
      ++ [ "Setting: " ++ setting
         , ""
         , line (PlainCells "" "median" "worst")
         ]
      ++ map line entries
  where
    entries = map (plainRow FmtText) rows
    labelW = maximum (0 : [length l | PlainCells l _ _ <- entries])
    numW = maximum (6 : [length c | PlainCells _ m w <- entries, c <- [m, w]])
    line PlainRule = replicate (labelW + 2 + numW + 2 + numW) '-'
    line (PlainCells l m w) = trimEnd (padR labelW l ++ "  " ++ padL numW m ++ "  " ++ padL numW w)
    padR n s = s ++ replicate (n - length s) ' '
    padL n s = replicate (n - length s) ' ' ++ s
    trimEnd = reverse . dropWhile (== ' ') . reverse

-- Table model ----------------------------------------------------------------

-- | The rendered table's output shapes. Each format's concrete spelling lives
-- in 'formatName' / 'parseFormat' and the per-format cases below, so no format
-- name is written as a bare string anywhere else.
data Format = FmtText | FmtMarkdown | FmtLatex
  deriving (Eq)

everyFormat :: [Format]
everyFormat = [FmtText, FmtMarkdown, FmtLatex]

formatName :: Format -> String
formatName FmtText = "text"
formatName FmtMarkdown = "markdown"
formatName FmtLatex = "latex"

parseFormat :: String -> Maybe Format
parseFormat s = lookup s [(formatName f, f) | f <- everyFormat]

-- | A measured quantity's unit, spelled per format.
data Scale = Micro | Milli | Bare

unitWord :: Format -> Scale -> Maybe String
unitWord _ Bare = Nothing
unitWord FmtLatex Micro = Just "\\si{\\micro\\second}"
unitWord FmtLatex Milli = Just "\\si{\\milli\\second}"
unitWord _ Micro = Just "µs"
unitWord _ Milli = Just "ms"

-- | A table cell. 'Num' is numeric and takes the format's number wrapper;
-- 'Plain' is passed through untouched.
data Cell = Num String | Plain String

cellText :: Format -> Cell -> String
cellText FmtLatex (Num s) = "\\num{" ++ s ++ "}"
cellText _ (Num s) = s
cellText _ (Plain s) = s

-- | A row's left column: indent depth, label, an optional parenthetical note,
-- and the unit. Rendered as @label (note, unit)@, dropping the absent parts.
data Label = Label Int String (Maybe String) Scale

labelText :: Format -> Label -> String
labelText fmt (Label ind lbl note sc) = indent ++ lbl ++ paren
  where
    -- Markdown collapses leading spaces inside a cell, so it indents with
    -- explicit non-breaking spaces instead.
    indent = concat (replicate ind (indentUnit fmt))
    paren = case (note, unitWord fmt sc) of
      (Nothing, Nothing) -> ""
      (Just n, Nothing) -> " (" ++ n ++ ")"
      (Nothing, Just u) -> " (" ++ u ++ ")"
      (Just n, Just u) -> " (" ++ n ++ ", " ++ u ++ ")"

indentUnit :: Format -> String
indentUnit FmtLatex = "\\quad "
indentUnit FmtMarkdown = "&nbsp;&nbsp;"
indentUnit FmtText = "  "

data Row
  = Row Label Cell Cell -- ^ label, median, worst
  | RowSpan Label Cell -- ^ label, one value covering both columns
  | RowRule -- ^ horizontal separator

-- Options --------------------------------------------------------------------

data Options = Options
  { optFormat :: Format
  , optOut :: Maybe FilePath -- ^ 'Nothing' prints to stdout
  , optPrebuilt :: Bool
  , optOutputDir :: Maybe FilePath
  }

parseOptions :: [String] -> Either String Options
parseOptions = go (Options FmtText Nothing False Nothing)
  where
    go acc [] = Right acc
    go acc (a : rest)
      | Just v <- stripPrefix "--format=" a = withFormat acc v rest
      | a == "--format", (v : rest') <- rest = withFormat acc v rest'
      | a == "--format" = Left "--format needs a value"
      | Just v <- stripPrefix "--out=" a = withOut acc v rest
      | a == "--out", (v : rest') <- rest = withOut acc v rest'
      | a == "--out" = Left "--out needs a path"
      | a == "--prebuilt" = go acc {optPrebuilt = True} rest
      | Just v <- stripPrefix "--output-dir=" a = withOutputDir acc v rest
      | a == "--output-dir", (v : rest') <- rest = withOutputDir acc v rest'
      | a == "--output-dir" = Left "--output-dir needs a path"
      | otherwise = Left ("unknown argument " ++ show a)
    withFormat acc v rest = case parseFormat v of
      Just f -> go acc {optFormat = f} rest
      Nothing ->
        Left
          ( "unknown format " ++ show v ++ " (expected "
              ++ intercalate ", " (map formatName everyFormat) ++ ")"
          )
    withOut acc v rest
      | null v = Left "--out needs a nonempty path"
      | Just _ <- optOutputDir acc = Left "cannot combine --out with --output-dir"
      | otherwise = go acc {optOut = Just v} rest
    withOutputDir acc v rest
      | null v = Left "--output-dir needs a nonempty path"
      | Just _ <- optOut acc = Left "cannot combine --out with --output-dir"
      | otherwise = go acc {optOutputDir = Just v} rest

usage :: String
usage =
  "usage: bench.hs [--format=" ++ intercalate "|" (map formatName everyFormat)
    ++ "] [--out PATH] [--prebuilt] [--output-dir DIR]\n"
    ++ "  the table goes to stdout unless --out names a file;\n"
    ++ "  --output-dir writes bench.json plus text, markdown, and LaTeX tables;\n"
    ++ "  --prebuilt requires the existing Lean driver and runs no build;\n"
    ++ "  the default raw record is measurements/bench.json (gitignored)."

-- | Write the rendered table, forcing UTF-8 so the micro sign survives a
-- non-UTF-8 locale.
emit :: Maybe FilePath -> String -> IO ()
emit Nothing s = hSetEncoding stdout utf8 >> putStr s
emit (Just path) s =
  withFile path WriteMode $ \h -> hSetEncoding h utf8 >> hPutStr h s
