-- | The measurement harness (M5 tracker #48, T3) as a standing test: the pure
-- "Lara.Measure" library over both manifests (no subprocess, no timing).
--
-- Timing and Lean-subprocess columns are exercised by a harness smoke run in
-- CI-adjacent usage (@scripts\/measure.hs@) and by @scripts\/differential.sh@
-- (the cross-driver gate, which runs in CI), not pinned here. This spec pins the
-- deterministic columns, the D4\/1A driver-refactor regression guard, the pure
-- @lean_agree@ comparators (both regimes, including mismatches), the timing
-- statistics helper, the report round-trips, and the location vocabulary.
module MeasureSpec (measureSpecProps) where

import qualified Data.Aeson as Aeson
import qualified Data.ByteString.Lazy.Char8 as BL

import Test.QuickCheck

import Lara.AST (GroupId (..))
import Lara.Diagnostics (Constituent (..), constituentText, parseConstituent)
import Lara.Driver (runCheck, runCheckLocated)
import Lara.Measure
import Lara.Wire (decodeCheckInputFile, encodeVerdict, printSExpr, verdictOutcome)

-- ---------------------------------------------------------------------------
-- Discovery (both manifests, exactly as scripts/measure.hs)
-- ---------------------------------------------------------------------------

allInputs :: IO [InputMeta]
allInputs = do
  mutants <- readFile "fixtures/mutants/MANIFEST.tsv"
  corpus <- readFile "corpus-units/MANIFEST.tsv"
  pure (parseMutantManifest mutants ++ parseCorpusManifest corpus)

-- | Manifest discovery must account for every visible data row. The parsers
-- return lists, so this independent row census prevents a malformed row from
-- being silently omitted by measurement or benchmark consumers.
prop_manifestParsersTotal :: Property
prop_manifestParsersTotal = once $ ioProperty $ do
  mutantRaw <- readFile "fixtures/mutants/MANIFEST.tsv"
  corpusRaw <- readFile "corpus-units/MANIFEST.tsv"
  let mutantRows =
        [ ln
        | ln <- lines mutantRaw
        , not (null ln)
        , take 1 ln /= "#"
        ]
      corpusRows = filter (not . null) (drop 1 (lines corpusRaw))
      mutants = parseMutantManifest mutantRaw
      corpus = parseCorpusManifest corpusRaw
  pure $
    conjoin
      [ counterexample "mutant manifest parser dropped a data row" (length mutants === length mutantRows)
      , counterexample "corpus manifest parser dropped a data row" (length corpus === length corpusRows)
      , counterexample "mutant manifest has no data rows" (not (null mutants))
      , counterexample "corpus manifest has no data rows" (not (null corpus))
      ]

-- ---------------------------------------------------------------------------
-- Deterministic-column properties
-- ---------------------------------------------------------------------------

-- | The iron invariant behind the located driver, over EVERY manifest-discovered
-- input (critical regression guard on the D4\/1A driver refactor). Codec rows do
-- not decode and are skipped (they never reach 'runCheckLocated').
prop_runCheckLocated :: Property
prop_runCheckLocated = once $ ioProperty $ do
  inputs <- allInputs
  checks <- mapM check inputs
  pure $ conjoin (counterexample "no inputs discovered" (not (null checks)) : checks)
  where
    check im = do
      bytes <- readFile (imPath im)
      pure $ counterexample (imPath im) $ case decodeCheckInputFile bytes of
        Left _ -> property True
        Right input -> fst (runCheckLocated input) === runCheck input

-- | Every input's actual outcome, computed through the MEASUREMENT path, equals
-- its specified one (@class_match@ holds for all rows) — the measurement harness
-- must not disagree with the mutation suite / corpus golden.
prop_classMatch :: Property
prop_classMatch = once $ ioProperty $ do
  inputs <- allInputs
  checks <- mapM check inputs
  pure $ conjoin (counterexample "no inputs discovered" (not (null checks)) : checks)
  where
    check im = do
      bytes <- readFile (imPath im)
      let det = computeDeterministic im bytes
      pure $
        counterexample
          (imPath im ++ ": expected " ++ imExpectedText im ++ ", actual " ++ detActual det)
          (detClassMatch det)

-- | Replay success is measured on corpus units only (@replay_ok@ = 'Just True');
-- mutant rows carry no pinned replay identity and render @-@ ('Nothing').
prop_replayOk :: Property
prop_replayOk = once $ ioProperty $ do
  inputs <- allInputs
  checks <- mapM check inputs
  pure $ conjoin (counterexample "no inputs discovered" (not (null checks)) : checks)
  where
    check im = do
      bytes <- readFile (imPath im)
      let det = computeDeterministic im bytes
      pure $ counterexample (imPath im) $ case imKind im of
        CorpusRow -> detReplayOk det === Just True
        MutantRow -> detReplayOk det === Nothing

-- | The report renders to valid JSON (an independent, established parser —
-- @aeson@, a test-suite dependency — is a stronger check on the house 'JValue'
-- renderer than a hand-rolled dual, eng review D12) and to a well-formed TSV
-- (every row has exactly the header's column count, parsed by an independent
-- splitter).
prop_reportRoundTrips :: Property
prop_reportRoundTrips = once $ ioProperty $ do
  inputs <- allInputs
  records <- mapM record inputs
  let env = EnvBlock "0000000" False "9.14.1" "lean4" "test-os" "test-cpu"
      json = reportJson env records
      tsv = reportTsv records
  pure $
    conjoin
      [ counterexample "report.json is not valid JSON (aeson rejected it)" (validJson json)
      , counterexample "report.tsv has ragged rows" (tsvWellFormed tsv)
      ]
  where
    record im = do
      bytes <- readFile (imPath im)
      -- Deterministic metrics are real; the IO columns get synthetic samples so
      -- the median/samples rendering is exercised without spawning a subprocess.
      pure (Record im (computeDeterministic im bytes) (Just True) [3, 1, 4, 1, 5] [10, 20, 30, 40, 50])
    validJson s = case Aeson.decode (BL.pack s) :: Maybe Aeson.Value of
      Just _ -> True
      Nothing -> False
    tsvWellFormed s = case filter (not . null) (lines s) of
      [] -> False
      rows@(header : _) ->
        let n = length (splitOn '\t' header)
         in n == length (splitOn '\t' tsvHeader) && all ((== n) . length . splitOn '\t') rows

-- ---------------------------------------------------------------------------
-- Pure helpers (no IO): lean_agree comparators, median, Constituent table
-- ---------------------------------------------------------------------------

-- | The @lean_agree@ comparators are pure; unit-tested against synthetic
-- stdout/exit/stderr for both regimes, including every mismatch mode (the spec
-- never spawns a subprocess, so without this the comparison logic ships
-- untested).
prop_leanAgree :: Property
prop_leanAgree = once $ ioProperty $ do
  bytes <- readFile "examples/A/example.core.sexp"
  pure $ case decodeCheckInputFile bytes of
    Left err -> counterexample ("could not decode fixture: " ++ show err) (property False)
    Right input ->
      let v = runCheck input
          good = printSExpr (encodeVerdict v) ++ "\n"
          okExit = outcomeExitCode (verdictOutcome v)
       in conjoin
            [ counterexample "verdict: matching stdout+exit should agree" (leanAgreeVerdict v good okExit)
            , counterexample "verdict: wrong stdout must disagree" (not (leanAgreeVerdict v "(verdict wrong)\n" okExit))
            , counterexample "verdict: missing trailing newline must disagree" (not (leanAgreeVerdict v (printSExpr (encodeVerdict v)) okExit))
            , counterexample "verdict: wrong exit must disagree" (not (leanAgreeVerdict v good 2))
            , counterexample "codec: exit 2 + empty stdout + pinned stderr should agree" (leanAgreeCodec "unclosed list" 2 "" "codec: unclosed list here")
            , counterexample "codec: wrong exit must disagree" (not (leanAgreeCodec "unclosed list" 0 "" "codec: unclosed list here"))
            , counterexample "codec: nonempty stdout must disagree" (not (leanAgreeCodec "unclosed list" 2 "junk" "codec: unclosed list here"))
            , counterexample "codec: absent pin must disagree" (not (leanAgreeCodec "unclosed list" 2 "" "some other error"))
            , counterexample "codec: empty pin must disagree" (not (leanAgreeCodec "" 2 "" "anything at all"))
            ]

-- | The median-of-samples helper: 'Nothing' on empty, the sorted middle
-- otherwise (odd and even lengths), independent of input order.
prop_median :: Property
prop_median =
  once $
    conjoin
      [ counterexample "empty" (median [] === Nothing)
      , counterexample "singleton" (median [10] === Just 10)
      , counterexample "odd, unsorted" (median [5, 1, 3, 2, 4] === Just 3)
      , counterexample "even, unsorted" (median [4, 2] === Just 4)
      , counterexample "order independence" (median [40, 10, 30, 50, 20] === median [10, 20, 30, 40, 50])
      ]

-- | The 'Constituent' render/parse manifest-spelling table round-trips for every
-- shape (the shared location vocabulary; @location_match@ is '==' on it).
prop_constituentRoundTrip :: Property
prop_constituentRoundTrip =
  once $
    conjoin
      [ counterexample (constituentText c) (parseConstituent (constituentText c) === Just c)
      | c <-
          [ CPolicy
          , CArgument 0
          , CArgument 12
          , CAttack 4
          , CConflictPair 1 2
          , CReplayEnvelope
          , CGroup (GroupId "mut_g")
          ]
      ]

-- ---------------------------------------------------------------------------
-- Small local utility
-- ---------------------------------------------------------------------------

splitOn :: Char -> String -> [String]
splitOn sep s = case break (== sep) s of
  (field, _ : rest) -> field : splitOn sep rest
  (field, "") -> [field]

measureSpecProps :: [(String, IO Result)]
measureSpecProps =
  [ ("measure: manifest parsers account for every data row", quickCheckResult prop_manifestParsersTotal)
  , ("measure: runCheck == fst . runCheckLocated over both manifests", quickCheckResult prop_runCheckLocated)
  , ("measure: class_match holds for every mutant and corpus unit", quickCheckResult prop_classMatch)
  , ("measure: replay_ok on corpus units, - on mutants", quickCheckResult prop_replayOk)
  , ("measure: report.json parses (aeson) and report.tsv is well-formed", quickCheckResult prop_reportRoundTrips)
  , ("measure: lean_agree comparators (both regimes, with mismatches)", quickCheckResult prop_leanAgree)
  , ("measure: median-of-samples helper", quickCheckResult prop_median)
  , ("measure: Constituent render/parse table round-trips", quickCheckResult prop_constituentRoundTrip)
  ]
