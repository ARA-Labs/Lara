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
-- * @--map@ is a second protocol with its own table, never folded into the
--   rows above (issue #319). It measures every accepted @map.laramap@
--   conformance anchor: one untimed pass reads the manifest, its policy, every
--   member and every member's policy into a fresh source cache, then the timed
--   sections run everything @lara check \<map.laramap\>@ does after argument
--   parsing over that cache — load and recheck every member, link, check,
--   evaluate, render — and, separately, the pure link-and-check stage over
--   pre-loaded members. Member count is reported beside each figure, because a
--   map's cost scales with its members rather than with one unit.
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

import Control.Exception (IOException, evaluate, try)
import Control.Monad (forM, forM_, replicateM, unless, when)
import qualified Data.ByteString as B
import Data.List (intercalate, maximumBy, nub, sort, stripPrefix)
import Data.Ord (comparing)
import GHC.Clock (getMonotonicTimeNSec)
import System.Directory
  ( createDirectoryIfMissing
  , doesDirectoryExist
  , doesFileExist
  , listDirectory
  )
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
import System.FilePath (takeDirectory, (</>))
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
import Lara.Map.Driver (checkMap)
import Lara.Map.Load (checkedMembers, loadMapWith)
import Lara.Map.Types (MapError (..), MapVerdict (..), mapErrorExitCode, renderMapError)
import Lara.Map.Wire (encodeMapVerdict)
import Lara.Measure (InputMeta (..), median, parseCorpusManifest, parseMutantManifest)
import Lara.Mutate (Expected (..))
import Lara.Replay (inputUnit, runtimeReplayFailure)
import Lara.Runtime (runtimeAF)
import Lara.Source.Load (newSourceCache)
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
  case optMode opts of
    KernelMode fmt -> benchKernel fmt opts
    MapMode fmt -> benchMaps fmt opts

-- | The kernel bench: the frozen corpus units and the harness sweep.
benchKernel :: Format -> Options -> IO ()
benchKernel fmt opts = do
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
      table tableFmt = renderTable tableFmt env inputCount units sweepNs
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
      emit (optOut opts) (table fmt)
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
  ns <- timedSections act x
  maybe (die "no timing samples") pure (median ns)

-- | The 'samples' timed sections themselves, in nanoseconds per run: each
-- section runs the action 'reps' times and divides.
timedSections :: (a -> IO b) -> a -> IO [Integer]
timedSections act x =
  replicateM samples $ do
    t0 <- getMonotonicTimeNSec
    mapM_ act (replicate reps x)
    t1 <- getMonotonicTimeNSec
    pure (toInteger (t1 - t0) `div` toInteger reps)

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

-- | A probe's trimmed stdout, or @""@ when the probe fails __or is absent__. The
-- environment record is best-effort per platform, and @--map@ runs no Lean at
-- all, so a machine without @lean@ (or @sysctl@) on @PATH@ records an unknown
-- field rather than aborting the bench. A failed probe is named on stderr, so a
-- blank or fallback field in the setting line always has a stated cause.
capture :: String -> [String] -> IO String
capture cmd args = do
  result <- try (readProcessWithExitCode cmd args "") :: IO (Either IOException (ExitCode, String, String))
  case result of
    Right (ExitSuccess, out, _err) -> pure (trim out)
    Right (ExitFailure n, _, _) -> unknown ("exit " ++ show n)
    Left err -> unknown (show err)
  where
    unknown why = do
      hPutStrLn
        stderr
        ( "bench: environment probe `" ++ unwords (cmd : args) ++ "` failed ("
            ++ why ++ "), so the record carries a fallback for that field"
        )
      pure ""
    trim = f . f
    f = reverse . dropWhile (`elem` " \t\r\n")

-- Map mode (issue #319) ------------------------------------------------------

-- | The roots whose @map.laramap@ anchors the map mode measures: the two that
-- @scripts\/check-map-conformance.sh@ discovers anchors under, so a map is
-- benched exactly when it is a conformance anchor.
mapAnchorRoots :: [FilePath]
mapAnchorRoots = ["test/fixtures/map", "examples/agreement-map-multi"]

-- | The shipped map. It must be among the measured anchors: it is the one a
-- reader runs and the one @docs\/demos\/d3-agreement-map.md@ quotes.
shippedMap :: FilePath
shippedMap = "examples/agreement-map-multi/map.laramap"

-- | One accepted map's measurements. Both timing lists hold one value per timed
-- section, in nanoseconds per run (already divided by 'reps').
data MapBench = MapBench
  { mbPath :: FilePath
  , mbMembers :: Int
  , mbNodes :: Int -- ^ linked arguments: the verdict's @labels@
  , mbEdges :: Int
  , mbTotalNs :: [Integer] -- ^ load + member checks + link + check + evaluate + render
  , mbLinkNs :: [Integer] -- ^ the same over pre-loaded members: link onward
  }

benchMaps :: MapFormat -> Options -> IO ()
benchMaps fmt opts = do
  manifests <- concat <$> mapM findManifests mapAnchorRoots
  env <- gatherEnv
  measured <- forM manifests $ \path -> (,) path <$> benchMap path
  let maps = [m | (_, Right m) <- measured]
      skipped = [(path, err) | (path, Left err) <- measured]
  -- A map that refuses by design and one that no longer loads are both skipped,
  -- so each is named with the diagnostic and exit code `lara check` gives it.
  forM_ skipped $ \(path, err) ->
    hPutStrLn stderr ("bench --map: not measured, no full pass to time: " ++ skipReason path err)
  case lookup shippedMap skipped of
    Just err -> die (shippedMap ++ " was not measured: " ++ skipReason shippedMap err)
    Nothing ->
      unless (shippedMap `elem` map mbPath maps) $
        die (shippedMap ++ " was not measured: it is not among the discovered anchors")
  let raw = mapBenchJson env maps
      table mfmt = renderMapTable mfmt env maps
  rawPath <- case optOutputDir opts of
    Just dir -> do
      createDirectoryIfMissing True dir
      writeFile (dir </> "bench-map.json") raw
      emit (Just (dir </> "performance-map.txt")) (table MapText)
      emit (Just (dir </> "performance-map.md")) (table MapMarkdown)
      pure (dir </> "bench-map.json")
    Nothing -> do
      createDirectoryIfMissing True "measurements"
      writeFile "measurements/bench-map.json" raw
      emit (optOut opts) (table fmt)
      pure "measurements/bench-map.json"
  hPutStrLn
    stderr
    ( "bench --map: " ++ show (length maps) ++ " accepted map anchors measured"
        ++ ( if null skipped
               then ""
               else "; " ++ show (length skipped) ++ " not measured, each named above"
           )
        ++ "; raw record in " ++ rawPath
        ++ maybe "" ("; table written to " ++) (optOut opts)
        ++ maybe "" ("; all formats written to " ++) (optOutputDir opts)
    )

-- | Every @map.laramap@ under a directory, in sorted path order. A missing root
-- is an error rather than an empty result, so a renamed fixture tree cannot
-- quietly shrink the table.
findManifests :: FilePath -> IO [FilePath]
findManifests root = do
  present <- doesDirectoryExist root
  unless present (die ("map anchor root is not a directory: " ++ root))
  go root
  where
    go dir = do
      entries <- sort <$> listDirectory dir
      fmap concat . forM entries $ \entry -> do
        let path = dir </> entry
        isDir <- doesDirectoryExist path
        if isDir then go path else pure [path | entry == "map.laramap"]

-- | Measure one map, or return the 'MapError' it stops at when it does not
-- accept.
--
-- The pre-read is one untimed pass through a fresh source cache
-- ('Lara.Map.Load.loadMapWith'): it reads the manifest, its policy, every member
-- and every member's policy, and every timed pass reuses that cache, so no
-- timed pass reads a file's bytes. What a timed pass still asks of the
-- filesystem is to resolve each path, because the cache is keyed by
-- 'System.Directory.canonicalizePath' — which the table's setting line states
-- rather than hides. The link section runs over members the warm-up pass has
-- already loaded and forced, so it times the pure stage and nothing before it.
benchMap :: FilePath -> IO (Either MapError MapBench)
benchMap path = do
  cache <- newSourceCache
  warm <- loadMapWith cache path
  case warm of
    Left err -> pure (Left err)
    Right loaded -> case checkMap loaded of
      Left err -> pure (Left err)
      Right verdict -> do
        _ <- evaluate (length (renderVerdict verdict))
        total <- timedSections (\p -> loadMapWith cache p >>= evaluate . outcomeLength) path
        link <- timedSections (evaluate . outcomeLength . Right) loaded
        pure
          ( Right
              MapBench
                { mbPath = path
                , mbMembers = length (checkedMembers loaded)
                , mbNodes = length (mvLabels verdict)
                , mbEdges = length (mvEdges verdict)
                , mbTotalNs = total
                , mbLinkNs = link
                }
          )
  where
    renderVerdict = printSExpr . encodeMapVerdict
    outcomeLength loadedOrError =
      either (length . renderMapError) (length . renderVerdict) (loadedOrError >>= checkMap)

-- | Why a map was not measured, on one line: whether the checker refused it or
-- it stopped before the checker, the exit code @lara check@ gives it, and the
-- diagnostic it prints.
skipReason :: FilePath -> MapError -> String
skipReason path err =
  path ++ ": " ++ kind ++ " (exit " ++ show (mapErrorExitCode err) ++ "): " ++ renderMapError err
  where
    kind = case err of
      MapReject _ -> "the checker refuses it"
      MapBoundary _ -> "it stops before the checker"

mapCaptionLines :: [String]
mapCaptionLines =
  [ "Multi-artifact map performance: its own protocol, never comparable with the"
  , "kernel table. A map row is one full pass of what `lara check <map.laramap>`"
  , "does after argument parsing (load and recheck every member, link, check,"
  , "evaluate, render) over files already in the run's source cache; the indented"
  , "row is the link-and-check stage alone. Worst is the slowest timed section."
  ]

mapSettingLine :: Env -> [MapBench] -> String
mapSettingLine env maps =
  show (length maps) ++ " accepted map anchors; "
    ++ envCpuModel env ++ ", " ++ ramGb env ++ " GB RAM, "
    ++ envOsArch env ++ ", GHC " ++ envGhc env
    ++ "; every file pre-read by one untimed pass (paths are still resolved per"
    ++ " pass); medians over " ++ show samples ++ " sections of "
    ++ show reps ++ " batched runs each."

mapRows :: [MapBench] -> [Row]
mapRows = concatMap rowsFor
  where
    rowsFor m =
      [ Row (Label 0 (takeDirectory (mbPath m)) (Just (shape m)) Micro)
          (Num (us1 (medianOf (mbTotalNs m))))
          (Num (us1 (maximum (mbTotalNs m))))
      , Row (Label 1 "link + check + render, members pre-loaded" Nothing Micro)
          (Num (us1 (medianOf (mbLinkNs m))))
          (Num (us1 (maximum (mbLinkNs m))))
      ]
    shape m =
      show (mbMembers m) ++ " members, "
        ++ show (mbNodes m) ++ " nodes / " ++ show (mbEdges m) ++ " edges"

renderMapTable :: MapFormat -> Env -> [MapBench] -> String
renderMapTable fmt env maps = case fmt of
  MapMarkdown -> markdownTable mapCaptionLines setting rows
  MapText -> textTable mapCaptionLines setting rows
  where
    rows = mapRows maps
    setting = mapSettingLine env maps

mapBenchJson :: Env -> [MapBench] -> String
mapBenchJson env maps =
  unlines $
    ["{"]
      ++ envJsonLines env
      ++ ["  \"maps\": ["]
      ++ [ "    {\"path\": " ++ jsonString (mbPath m)
             ++ ", \"members\": " ++ show (mbMembers m)
             ++ ", \"nodes\": " ++ show (mbNodes m)
             ++ ", \"edges\": " ++ show (mbEdges m)
             ++ ", \"total_ns\": " ++ show (mbTotalNs m)
             ++ ", \"link_ns\": " ++ show (mbLinkNs m)
             ++ "}" ++ (if index == length maps then "" else ",")
         | (index, m) <- zip [1 :: Int ..] maps
         ]
      ++ ["  ]", "}"]

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
    ["{"]
      ++ envJsonLines env
      ++ [ "  \"sweep_records\": " ++ show inputCount ++ ","
         , "  \"sweep_ns\": " ++ show sweepNs ++ ","
         , "  \"units\": ["
         ]
      ++ [ "    {\"base\": " ++ jsonString (ubBase u)
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

-- | The raw record's @environment@ object, shared by both modes' records.
envJsonLines :: Env -> [String]
envJsonLines env =
  [ "  \"environment\": {"
  , "    \"cpu\": " ++ jsonString (envCpuModel env) ++ ","
  , "    \"ram_bytes\": " ++ maybe "null" show (envRamBytes env) ++ ","
  , "    \"os_arch\": " ++ jsonString (envOsArch env) ++ ","
  , "    \"ghc\": " ++ jsonString (envGhc env) ++ ","
  , "    \"lean\": " ++ jsonString (envLean env) ++ ","
  , "    \"git_rev\": " ++ jsonString (envGitRev env) ++ ","
  , "    \"reps\": " ++ show reps ++ ","
  , "    \"samples\": " ++ show samples
  , "  },"
  ]

jsonString :: String -> String
jsonString s = "\"" ++ concatMap esc s ++ "\""
  where
    esc '"' = "\\\""
    esc '\\' = "\\\\"
    esc c = [c]

-- | The environment-of-record line the table header and the paper's prose
-- must agree on.
settingLine :: Env -> Int -> String
settingLine env inputCount =
  show inputCount ++ "-record harness; "
    ++ envCpuModel env ++ ", " ++ ramGb env ++ " GB RAM, "
    ++ envOsArch env ++ ", GHC " ++ envGhc env ++ ", " ++ envLean env
    ++ "; medians over " ++ show samples ++ " sections of "
    ++ show reps ++ " batched runs each."

-- | Installed memory in whole GiB, or @?@ when the platform did not say.
ramGb :: Env -> String
ramGb env = maybe "?" (\b -> show (b `div` (1024 * 1024 * 1024))) (envRamBytes env)

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
  FmtMarkdown -> markdownTable captionLines setting rows
  FmtText -> textTable captionLines setting rows
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

markdownTable :: [String] -> String -> [Row] -> String
markdownTable caption setting rows =
  unlines $
    caption
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

textTable :: [String] -> String -> [Row] -> String
textTable caption setting rows =
  unlines $
    caption
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
  { optMode :: Mode
  , optOut :: Maybe FilePath -- ^ 'Nothing' prints to stdout
  , optPrebuilt :: Bool
  , optOutputDir :: Maybe FilePath
  }

-- | Which bench runs, in which format. The map bench has no LaTeX format, so
-- @--map --format=latex@ is refused while the arguments are parsed, and the map
-- renderer has no LaTeX case to reach.
data Mode
  = KernelMode Format
  | MapMode MapFormat -- ^ @--map@: the map anchors instead (issue #319)

-- | The formats the map table prints in: 'Format' less LaTeX.
data MapFormat = MapText | MapMarkdown

-- | The map format for a requested 'Format', or why there is none.
mapFormatOf :: Format -> Either String MapFormat
mapFormatOf FmtText = Right MapText
mapFormatOf FmtMarkdown = Right MapMarkdown
mapFormatOf FmtLatex =
  Left
    ( "--map prints text or markdown only: the paper typesets the kernel table, "
        ++ "and a map row must never be read as one of its rows"
    )

parseOptions :: [String] -> Either String Options
parseOptions = go (Options (KernelMode FmtText) Nothing False Nothing)
  where
    go acc [] = Right acc
    go acc (a : rest)
      | a == "--map" = withMap acc rest
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
    -- @--map@ and @--format@ may come in either order, so each rebuilds the mode
    -- from what the other has already set.
    withMap acc rest = case optMode acc of
      MapMode _ -> go acc rest
      KernelMode f -> mapFormatOf f >>= \m -> go acc {optMode = MapMode m} rest
    withFormat acc v rest = case parseFormat v of
      Just f -> case optMode acc of
        KernelMode _ -> go acc {optMode = KernelMode f} rest
        MapMode _ -> mapFormatOf f >>= \m -> go acc {optMode = MapMode m} rest
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
    ++ "] [--out PATH] [--prebuilt] [--output-dir DIR] [--map]\n"
    ++ "  the table goes to stdout unless --out names a file;\n"
    ++ "  --output-dir writes bench.json plus text, markdown, and LaTeX tables;\n"
    ++ "  --prebuilt requires the existing Lean driver and runs no build;\n"
    ++ "  the default raw record is measurements/bench.json (gitignored).\n"
    ++ "  --map measures the multi-artifact map anchors instead, under their own\n"
    ++ "  protocol and in their own table (text or markdown; no Lean driver runs);\n"
    ++ "  its raw record is measurements/bench-map.json."

-- | Write the rendered table, forcing UTF-8 so the micro sign survives a
-- non-UTF-8 locale.
emit :: Maybe FilePath -> String -> IO ()
emit Nothing s = hSetEncoding stdout utf8 >> putStr s
emit (Just path) s =
  withFile path WriteMode $ \h -> hSetEncoding h utf8 >> hPutStr h s
