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
import qualified Data.Aeson.Key as AK
import qualified Data.Aeson.Types as AT
import qualified Data.ByteString.Lazy.Char8 as BL

import Control.Exception (SomeException, evaluate, try)
import Data.List (isInfixOf)

import Test.QuickCheck

import Lara.AST (GroupId (..))
import Lara.Diagnostics
  ( Constituent (..)
  , constituentListText
  , constituentText
  , parseConstituent
  , parseConstituentList
  )
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

-- | The report's column /identity/ and the two location cells' /values/
-- (#167 review).
--
-- 'prop_reportRoundTrips' checks that every row carries the header's column
-- count, which is invariant under reordering 'tsvHeader' or
-- 'Lara.Measure.recordTsv' independently: such a swap keeps the arity
-- identical while silently mislabelling every @cut -f@ consumer downstream
-- (@docs\/m5-freeze-checklist.md@'s @cut -f1-15@ deterministic projection among
-- them) and changing the bytes the freeze hashes. Pinning the header verbatim
-- also makes the checklist's field numbers executable rather than prose.
--
-- The second half pins the values apart. @location_primary@ is 'Just' 'True'
-- on every committed row — 'prop_siteMatchesChecker' forces the located
-- constituent to equal the published head everywhere — so rendering
-- 'detLocationMatch' into the primary cell, or the reverse, is byte-identical
-- over the entire corpus and invisible to every property that reads the
-- committed suite. One synthetic record on which the two metrics differ
-- separates them in both renderers, TSV and JSON.
prop_reportColumnOrder :: Property
prop_reportColumnOrder = once $ ioProperty $ do
  inputs <- allInputs
  case inputs of
    [] -> pure (counterexample "no inputs discovered" (property False))
    im : _ -> do
      bytes <- readFile (imPath im)
      let det =
            (computeDeterministic im bytes)
              { detLocationMatch = Just True
              , detLocationPrimary = Just False
              }
          synthetic = Record im det (Just True) [3, 1, 4, 1, 5] [10, 20, 30, 40, 50]
          env = EnvBlock "0000000" False "9.14.1" "lean4" "test-os" "test-cpu"
      pure $
        conjoin
          [ counterexample "tsvHeader names or order drifted" $
              splitOn '\t' tsvHeader
                === [ "input"
                    , "base"
                    , "family"
                    , "operator"
                    , "expected"
                    , "actual"
                    , "class_match"
                    , "location"
                    , "location_match"
                    , "location_primary"
                    , "lean_agree"
                    , "replay_ok"
                    , "total_bytes"
                    , "policy_bytes"
                    , "payload_bytes"
                    , "hs_check_ns"
                    , "lean_wall_ns"
                    ]
          , case filter (not . null) (lines (reportTsv [synthetic])) of
              [_, row] ->
                let cells = splitOn '\t' row
                 in conjoin
                      [ counterexample
                          ("field 9 (location_match) rendered " ++ show (cells `cellAt` 8))
                          (cells `cellAt` 8 === Just "true")
                      , counterexample
                          ("field 10 (location_primary) rendered " ++ show (cells `cellAt` 9))
                          (cells `cellAt` 9 === Just "false")
                      ]
              rows ->
                counterexample
                  ("reportTsv rendered " ++ show (length rows) ++ " lines, expected header + one row")
                  (property False)
          , counterexample "report.json location-match / location-primary" $
              jsonLocationCells (reportJson env [synthetic]) === Just (Just True, Just False)
          ]
  where
    cellAt xs i
      | i >= 0, i < length xs = Just (xs !! i)
      | otherwise = Nothing
    -- Read the two cells back through aeson rather than the house renderer, so
    -- a renderer defect cannot be masked by reusing it as its own oracle.
    jsonLocationCells s = do
      v <- Aeson.decode (BL.pack s) :: Maybe Aeson.Value
      AT.parseMaybe
        ( Aeson.withObject "report" $ \o -> do
            records <- o Aeson..: AK.fromString "records"
            case records of
              [r] ->
                (,)
                  <$> (r Aeson..: AK.fromString "location-match")
                  <*> (r Aeson..: AK.fromString "location-primary")
              _ -> fail "expected exactly one record"
        )
        v

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
-- shape (the shared location vocabulary; @location_match@ is membership in the
-- ground-truth list over it, @location_primary@ '==' with the list head).
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

-- | The ordered-list spelling of the @expected-location@ column
-- (docs\/localization-metric-decision.md): @-@ ↔ the empty list, singletons
-- spell as the bare constituent, multi-element lists round-trip in order, and
-- malformed spellings (empty segment, unknown segment) parse to 'Nothing'.
prop_constituentListRoundTrip :: Property
prop_constituentListRoundTrip =
  once $
    conjoin
      ( [ counterexample (constituentListText cs) (parseConstituentList (constituentListText cs) === Just cs)
        | cs <-
            [ []
            , [CArgument 0]
            , [CArgument 0, CAttack 2]
            , [CArgument 1, CArgument 3, CConflictPair 0 2]
            , [CGroup (GroupId "mut_g"), CPolicy]
            ]
        ]
          ++ [ counterexample "empty list spells -" (constituentListText [] === "-")
             , counterexample
                 "singleton spells as the bare constituent"
                 (constituentListText [CAttack 4] === constituentText (CAttack 4))
             , counterexample "empty segment rejected" (parseConstituentList "arg:0,,arg:1" === Nothing)
             , counterexample "unknown segment rejected" (parseConstituentList "arg:0,bogus" === Nothing)
             , counterexample "empty string rejected" (parseConstituentList "" === Nothing)
             ]
      )

-- | The @,@ guard in 'Lara.Diagnostics.constituentListText' (#167 review).
--
-- 'GroupId' is free-form, so a group id containing a comma would render an
-- @expected-location@ column that 'parseConstituentList' cannot invert;
-- generation fails loudly instead. No committed corpus group id contains a
-- comma and 'prop_constituentListRoundTrip' only uses @mut_g@, so nothing else
-- in the suite reaches this branch — deleting the guard as an unreachable
-- 'error' would be invisible today, and a later comma-bearing group id would
-- then silently corrupt that row's ground truth instead of failing generation.
--
-- The second arm is the ambiguity the guard exists to prevent, stated
-- directly: @group:a,b@ — what the render /would/ produce — does not parse
-- back, so the round-trip 'constituentListText' promises is unavailable for
-- such an id at any spelling.
prop_constituentListCommaGuard :: Property
prop_constituentListCommaGuard = once $ ioProperty $ do
  thrown <-
    try (evaluate (length (constituentListText [CGroup (GroupId "a,b")])))
      :: IO (Either SomeException Int)
  pure $
    conjoin
      [ counterexample "a comma-bearing group id must fail generation, not render" $
          case thrown of
            Right n ->
              counterexample
                ("rendered " ++ show n ++ " characters instead of failing")
                (property False)
            Left e ->
              counterexample
                ("threw, but not the guard's error: " ++ show e)
                ("constituentListText" `isInfixOf` show e)
      , counterexample "the render the guard suppresses does not parse back" $
          parseConstituentList "group:a,b" === Nothing
      ]

-- | The two location metrics over every discovered row: defined exactly
-- together (both 'Just' or both 'Nothing'), primary implies membership, and on
-- a singleton ground truth the two coincide — the decision doc's guarantee
-- that a single-defect row means the same thing under both metrics.
prop_locationMetricsDomain :: Property
prop_locationMetricsDomain = once $ ioProperty $ do
  inputs <- allInputs
  checks <- mapM check inputs
  pure $ conjoin (counterexample "no inputs discovered" (not (null checks)) : checks)
  where
    check im = do
      bytes <- readFile (imPath im)
      let det = computeDeterministic im bytes
      pure $
        counterexample (imPath im) $
          conjoin
            [ counterexample
                "location_match and location_primary must share a domain"
                ((detLocationMatch det == Nothing) === (detLocationPrimary det == Nothing))
            , counterexample
                "location_primary=true must imply location_match=true"
                (detLocationPrimary det /= Just True .||. detLocationMatch det === Just True)
            , counterexample
                "singleton ground truth: membership must equal head-equality"
                ( length (imExpectedLocation im) /= 1
                    .||. detLocationMatch det === detLocationPrimary det
                )
            ]

-- ---------------------------------------------------------------------------
-- Small local utility
-- ---------------------------------------------------------------------------

splitOn :: Char -> String -> [String]
splitOn sep s = case break (== sep) s of
  (field, _ : rest) -> field : splitOn sep rest
  (field, "") -> [field]

-- | Membership and head-equality are genuinely different metrics, witnessed on
-- real mutant bytes: take a discovered seeded-reject row whose located
-- constituent @c@ is known, and re-measure it under synthetic ground-truth
-- lists. @[other, c]@ separates the two (member, not primary); @[c, other]@
-- satisfies both; @[other, other']@ fails both; @[]@ puts both off-domain.
-- Without this, swapping the two metric definitions would leave the suite
-- green, since a singleton ground truth cannot tell them apart.
prop_locationMetricsDiscriminate :: Property
prop_locationMetricsDiscriminate = once $ ioProperty $ do
  inputs <- allInputs
  located <- firstLocated inputs
  pure $ case located of
    Nothing -> counterexample "no seeded-reject row with a located constituent" False
    Just (im, bytes, c) ->
      let det locs = computeDeterministic im {imExpectedLocation = locs} bytes
          -- Constituent shapes no unit-mutant rejection locates at here — the
          -- row's actual located constituent is c, and c is asserted distinct.
          other = CConflictPair 97 98
          other' = CGroup (GroupId "synthetic_g")
       in conjoin
            [ counterexample "picked constituent collides with the synthetic ones" (c /= other && c /= other')
            , counterexample "[other, c]: member but not primary" $
                let d = det [other, c]
                 in (detLocationMatch d, detLocationPrimary d) === (Just True, Just False)
            , counterexample "[c, other]: member and primary" $
                let d = det [c, other]
                 in (detLocationMatch d, detLocationPrimary d) === (Just True, Just True)
            , counterexample "[other, other']: neither" $
                let d = det [other, other']
                 in (detLocationMatch d, detLocationPrimary d) === (Just False, Just False)
            , counterexample "[]: both off-domain" $
                let d = det []
                 in (detLocationMatch d, detLocationPrimary d) === (Nothing, Nothing)
            ]
  where
    firstLocated [] = pure Nothing
    firstLocated (im : rest)
      | seededReject im = do
          bytes <- readFile (imPath im)
          let d = computeDeterministic im bytes
          case detLocation d of
            Just c -> pure (Just (im, bytes, c))
            Nothing -> firstLocated rest
      | otherwise = firstLocated rest
    seededReject im = not (null (imExpectedLocation im))

measureSpecProps :: [(String, IO Result)]
measureSpecProps =
  [ ("measure: manifest parsers account for every data row", quickCheckResult prop_manifestParsersTotal)
  , ("measure: runCheck == fst . runCheckLocated over both manifests", quickCheckResult prop_runCheckLocated)
  , ("measure: class_match holds for every mutant and corpus unit", quickCheckResult prop_classMatch)
  , ("measure: replay_ok on corpus units, - on mutants", quickCheckResult prop_replayOk)
  , ("measure: report.json parses (aeson) and report.tsv is well-formed", quickCheckResult prop_reportRoundTrips)
  , ("measure: tsvHeader is pinned and the two location cells render apart", quickCheckResult prop_reportColumnOrder)
  , ("measure: lean_agree comparators (both regimes, with mismatches)", quickCheckResult prop_leanAgree)
  , ("measure: median-of-samples helper", quickCheckResult prop_median)
  , ("measure: Constituent render/parse table round-trips", quickCheckResult prop_constituentRoundTrip)
  , ("measure: expected-location list spelling round-trips", quickCheckResult prop_constituentListRoundTrip)
  , ("measure: a comma-bearing group id fails generation loudly", quickCheckResult prop_constituentListCommaGuard)
  , ("measure: location metrics share a domain and singletons coincide", quickCheckResult prop_locationMetricsDomain)
  , ("measure: membership and head-equality are distinguishable metrics", quickCheckResult prop_locationMetricsDiscriminate)
  ]
