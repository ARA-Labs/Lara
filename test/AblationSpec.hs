-- | The M5 T6 ablation baselines (tracker #48) as a standing test: the pure
-- ablation pass of "Lara.Measure" over both manifests (no subprocess, no
-- timing).
--
-- The two deterministic ablations ('Lara.Check.noCQConfig',
-- 'Lara.Check.noTypedConfig') only ever REMOVE rejections, so
-- @accept(full) ⊆ accept(ablation)@ holds by construction; this spec pins the
-- strict converse expectations: each ablation flips exactly its partition
-- bucket ('ablationBucket') reject→accept and leaves every other row
-- unchanged (surgical), codec rows are unchanged by definition, the
-- 'AblationReport' aggregate matches the manifest partition, and the
-- @ablation.{json,tsv}@ renderers produce the declared shape.
module AblationSpec (ablationSpecProps) where

import qualified Data.Aeson as Aeson
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.List (find, isPrefixOf)

import Test.QuickCheck

import Lara.AST hiding (Reject)
import Lara.Check (CheckConfig, fullConfig, noCQConfig, noTypedConfig)
import Lara.Diagnostics (LocatedRejection (..))
import Lara.Driver (runCheckLocated, runCheckLocatedWith)
import Lara.Measure
import Lara.Mutate (Expected (..), parseExpected)
import Lara.Prop (Pred (..), Prop (..))
import Lara.Wire
  ( Outcome (..)
  , decodeCheckInputFile
  , encodeVerdict
  , printSExpr
  , verdictOutcome
  )
import CheckSpec (negMissingConflict)
import TestReplay (testCheckInput)

-- ---------------------------------------------------------------------------
-- Discovery (both manifests, exactly as scripts/measure.hs)
-- ---------------------------------------------------------------------------

allInputs :: IO [InputMeta]
allInputs = do
  mutants <- readFile "fixtures/mutants/MANIFEST.tsv"
  corpus <- readFile "corpus-units/MANIFEST.tsv"
  pure (parseMutantManifest mutants ++ parseCorpusManifest corpus)

cellsFor :: CheckConfig -> IO [AblationCell]
cellsFor cfg = do
  inputs <- allInputs
  mapM (\im -> computeAblation cfg im <$> readFile (imPath im)) inputs

-- ---------------------------------------------------------------------------
-- Full-path guard + monotonicity
-- ---------------------------------------------------------------------------

-- | @runCheckLocatedWith fullConfig ≡ runCheckLocated@ over every
-- manifest-discovered input — definitional today (the alias), a guard against
-- any future non-aliased divergence. Codec rows never reach the checker and
-- are skipped.
prop_fullPathGuard :: Property
prop_fullPathGuard = once $ ioProperty $ do
  inputs <- allInputs
  checks <- mapM check inputs
  pure $ conjoin (counterexample "no inputs discovered" (not (null checks)) : checks)
  where
    check im = do
      bytes <- readFile (imPath im)
      pure $ counterexample (imPath im) $ case decodeCheckInputFile bytes of
        Left _ -> property True
        Right input ->
          let (v1, l1) = runCheckLocatedWith fullConfig input
              (v2, l2) = runCheckLocated input
           in printSExpr (encodeVerdict v1) === printSExpr (encodeVerdict v2) .&&. l1 === l2

-- | Accept-set monotonicity, strict form: every input the full system accepts
-- is accepted by each ablation with the byte-identical verdict (the config
-- only removes rejection arms, so on full-accepts the paths coincide).
prop_monotonicity :: Property
prop_monotonicity = once $ ioProperty $ do
  inputs <- allInputs
  checks <- mapM check [(name, cfg, im) | (name, cfg, _) <- ablationConfigs, im <- inputs]
  pure $ conjoin (counterexample "no inputs discovered" (not (null checks)) : checks)
  where
    check (name, cfg, im) = do
      bytes <- readFile (imPath im)
      pure $ counterexample (name ++ ": " ++ imPath im) $ case decodeCheckInputFile bytes of
        Left _ -> property True
        Right input ->
          let (vFull, _) = runCheckLocatedWith fullConfig input
              (vAbl, lAbl) = runCheckLocatedWith cfg input
           in case verdictOutcome vFull of
                Reject{} -> property True
                Accept{} ->
                  printSExpr (encodeVerdict vAbl) === printSExpr (encodeVerdict vFull)
                    .&&. lAbl === Nothing

-- ---------------------------------------------------------------------------
-- Surgical flips (strict, per ablation)
-- ---------------------------------------------------------------------------

-- | Strict surgical expectation for one named ablation: every row in its flip
-- bucket flips reject→accept (a missed reject whose recorded ablation outcome
-- is an accept class), and EVERY other row — other rejects, accepts, codec —
-- keeps the identical outcome text.
surgical :: String -> CheckConfig -> AblationBucket -> Property
surgical name cfg bucket = once $ ioProperty $ do
  cells <- cellsFor cfg
  pure $
    conjoin
      ( counterexample "no inputs discovered" (not (null cells))
          : map check cells
      )
  where
    check c =
      counterexample (name ++ ": " ++ imPath (acMeta c) ++ diag c) $
        if ablationBucket (imExpected (acMeta c)) == bucket
          then
            conjoin
              [ counterexample "must be a missed reject" (acMissedReject c)
              , counterexample "full system must reject" ("reject-" `isPrefixOf` acFullActual c)
              , counterexample "ablation must accept" ("accept-" `isPrefixOf` acAblationActual c)
              ]
          else counterexample "must be unchanged" (acAblationActual c === acFullActual c)
    diag c = " (full " ++ acFullActual c ++ ", ablation " ++ acAblationActual c ++ ")"

prop_noCQSurgical :: Property
prop_noCQSurgical = surgical "no-cq" noCQConfig FlipUnderNoCQ

prop_noTypedSurgical :: Property
prop_noTypedSurgical = surgical "no-typed" noTypedConfig FlipUnderNoTyped

-- | Codec rows are unchanged under every config — the decode fails before any
-- config is consulted. Asserted explicitly (decode failure + the cell's
-- spelling + no miss), not implied by the surgical properties.
prop_codecRows :: Property
prop_codecRows = once $ ioProperty $ do
  inputs <- allInputs
  let codecRows = [im | im <- inputs, imExpected im == ExpectCodecReject]
  checks <- mapM check [(name, cfg, im) | (name, cfg, _) <- ablationConfigs, im <- codecRows]
  pure $ conjoin (counterexample "no codec rows discovered" (not (null checks)) : checks)
  where
    check (name, cfg, im) = do
      bytes <- readFile (imPath im)
      let cell = computeAblation cfg im bytes
      pure $
        counterexample (name ++ ": " ++ imPath im) $
          conjoin
            [ counterexample "bytes must fail to decode" $
                case decodeCheckInputFile bytes of
                  Left _ -> True
                  Right _ -> False
            , acFullActual cell === codecFailText
            , acAblationActual cell === codecFailText
            , counterexample "codec rows can never be a missed reject" (not (acMissedReject cell))
            ]

-- ---------------------------------------------------------------------------
-- Aggregate: non-triviality + partition agreement
-- ---------------------------------------------------------------------------

-- | Each ablation misses at least one reject, and the 'AblationReport'
-- aggregate ('classSummaries') matches the manifest partition exactly: in the
-- flip bucket every row is missed, outside it nothing is missed and nothing
-- changes (no silent gaps between the report and the partition).
prop_reportMatchesPartition :: Property
prop_reportMatchesPartition = once $ ioProperty $ do
  inputs <- allInputs
  checks <- mapM (check inputs) ablationConfigs
  pure (conjoin checks)
  where
    check inputs (name, cfg, bucket) = do
      cells <- cellsFor cfg
      let sums = classSummaries (abrCells (AblationReport name cells))
          missedTotal = sum (map csMissed sums)
          partitionTotal =
            length [im | im <- inputs, ablationBucket (imExpected im) == bucket]
      pure $
        counterexample name $
          conjoin
            [ counterexample "ablation must miss at least one reject" (missedTotal >= 1)
            , counterexample "missed total must equal the manifest partition" $
                missedTotal === partitionTotal
            , conjoin (map (perClass inputs bucket) sums)
            ]
    perClass inputs bucket s =
      counterexample (csExpected s) $
        case bucketOfSpelling inputs (csExpected s) of
          Just b
            | b == bucket ->
                csMissed s === csTotal s
                  .&&. counterexample
                    "accept-class breakdown must cover every miss"
                    (sum (map snd (csMissedAcceptClasses s)) === csMissed s)
          Just _ -> csMissed s === 0 .&&. csUnchanged s === csTotal s
          Nothing -> counterexample "summary class not in any manifest" (property False)
    bucketOfSpelling inputs cls =
      ablationBucket . imExpected <$> find ((== cls) . imExpectedText) inputs

-- | Partition totality: every typed 'Expected' present in either manifest
-- lands in exactly one bucket (the three buckets are a disjoint cover — a
-- function's image, counted), and the bucket assignment agrees with the
-- 'parseExpected' spelling table: @reject-IncompleteArgument@ is the No-CQ
-- bucket, @reject-R10@\/@reject-R11@ the No-typed bucket, everything else
-- unchanged.
prop_partitionTotality :: Property
prop_partitionTotality = once $ ioProperty $ do
  inputs <- allInputs
  let buckets = map (ablationBucket . imExpected) inputs
      countOf b = length (filter (== b) buckets)
  pure $
    conjoin
      [ counterexample "no inputs discovered" (not (null inputs))
      , counterexample "buckets must cover every row exactly once" $
          countOf FlipUnderNoCQ + countOf FlipUnderNoTyped + countOf UnchangedUnderAblations
            === length inputs
      , conjoin
          [ counterexample (imExpectedText im) $
              ablationBucket (imExpected im) === spellingBucket (imExpectedText im)
          | im <- inputs
          ]
      , counterexample "spelling table must parse its flip spellings" $
          conjoin
            [ fmap ablationBucket (parseExpected "reject-IncompleteArgument") === Just FlipUnderNoCQ
            , fmap ablationBucket (parseExpected "reject-R10") === Just FlipUnderNoTyped
            , fmap ablationBucket (parseExpected "reject-R11") === Just FlipUnderNoTyped
            ]
      ]
  where
    spellingBucket t
      | t == "reject-IncompleteArgument" = FlipUnderNoCQ
      | t `elem` ["reject-R10", "reject-R11"] = FlipUnderNoTyped
      | otherwise = UnchangedUnderAblations

-- ---------------------------------------------------------------------------
-- Renderers + accept-class recording
-- ---------------------------------------------------------------------------

-- | The @ablation.{json,tsv}@ renderers produce the declared shape over the
-- real runs: the JSON parses under an independent parser (aeson) and the TSV
-- is rectangular with the declared header and one row per (ablation × input).
prop_rendererShape :: Property
prop_rendererShape = once $ ioProperty $ do
  reports <- mapM (\(name, cfg, _) -> AblationReport name <$> cellsFor cfg) ablationConfigs
  let env = EnvBlock "0000000" False "9.14.1" "lean4" "test-os" "test-cpu"
      json = ablationJson env reports
      tsv = ablationTsv reports
      rows = filter (not . null) (lines tsv)
      header = splitOn '\t' ablationTsvHeader
  pure $
    conjoin
      [ counterexample "ablation.json is not valid JSON (aeson rejected it)" (validJson json)
      , counterexample "declared TSV columns" $
          header
            === [ "ablation"
                , "input"
                , "base"
                , "family"
                , "operator"
                , "expected"
                , "full_actual"
                , "ablation_actual"
                , "missed_reject"
                ]
      , counterexample "ablation.tsv must start with the header" $
          take 1 rows === [ablationTsvHeader]
      , counterexample "ablation.tsv has ragged rows" $
          all ((== length header) . length . splitOn '\t') rows
      , counterexample "one TSV row per (ablation × input)" $
          length rows === 1 + sum (map (length . abrCells) reports)
      ]
  where
    validJson s = case Aeson.decode (BL.pack s) :: Maybe Aeson.Value of
      Just _ -> True
      Nothing -> False

-- | A known hole-mutant flip records the expected accept class: the @E1@
-- base's query is justified, so its hole-obligation mutant — rejected
-- @IncompleteArgument@ by the full system — is recorded @accept-justified@
-- by the No-CQ ablation (the paper's alarming case).
prop_acceptClassRecording :: Property
prop_acceptClassRecording = once $ ioProperty $ do
  inputs <- allInputs
  let path = "fixtures/mutants/E1--hole-obligation-0.sexp"
  case find ((== path) . imPath) inputs of
    Nothing -> pure (counterexample (path ++ " not in the manifest") (property False))
    Just im -> do
      cell <- computeAblation noCQConfig im <$> readFile (imPath im)
      pure $
        conjoin
          [ counterexample "must be a missed reject" (acMissedReject cell)
          , acFullActual cell === "reject-IncompleteArgument"
          , acAblationActual cell === "accept-justified"
          ]

-- | A hand-written minimal unit with a declared hole (the 'CheckSpec'
-- incomplete-argument shape): a defeasible rule with one Mandatory question,
-- instantiated with the question left open as a hole. The full system rejects
-- @IncompleteArgument@; 'noCQConfig' accepts it with the query justified — a
-- fast witness independent of the generated manifest.
prop_handWrittenHole :: Property
prop_handWrittenHole =
  once $
    conjoin
      [ counterexample "full system must reject IncompleteArgument" $
          case (verdictOutcome vFull, lrRejection <$> lFull) of
            (Reject IncompleteArgument, Just IncompleteArgument) -> property True
            other -> counterexample (show other) (property False)
      , counterexample "no-CQ must accept with the query justified" $
          case (verdictOutcome vAbl, lAbl) of
            (Accept _ _ [(_, Justified)], Nothing) -> property True
            other -> counterexample (show other) (property False)
      ]
  where
    (vFull, lFull) = runCheckLocatedWith fullConfig input
    (vAbl, lAbl) = runCheckLocatedWith noCQConfig input
    input = testCheckInput holeUnit
    holeUnit =
      Unit
        { unitRules =
            [ Rule
                (RuleId "d")
                []
                Defeasible
                []
                (AtomPat (Pred "c") [])
                False
                []
                [Question (QuestionId "q1") (AtomPat (Pred "ans") []) Mandatory]
            ]
        , unitContraries = []
        , unitExceptions = []
        , unitTheories = []
        , unitLeaves = []
        , unitArgs = [(ArgId "a", SRule (RuleId "d") [] [] [] [ObligationId "q1"] AssuranceNone)]
        , unitAttacks = []
        , unitQueries = [Prop (Pred "c") []]
        , unitGroups = []
        , unitGroupMode = QuarantineOnConflict
        }

-- | The conflict scan's config branch pinned in BOTH directions, on the
-- 'CheckSpec' missing-conflict fixture (a self-contrary complete argument with
-- no declared attack). The scan lives under 'ccTypedAttacks', so 'noCQConfig'
-- must still reject @MissingConflict@ — no manifest row pins this (neither
-- manifest has a @MissingConflict@ expectation), so without this property the
-- guard could silently move to 'ccObligationGate' with the whole suite green —
-- and 'noTypedConfig' must flip the same unit to accept.
prop_conflictScanGating :: Property
prop_conflictScanGating =
  once $
    conjoin
      [ counterexample "full system must reject MissingConflict" $
          case (verdictOutcome vFull, lrRejection <$> lFull) of
            (Reject MissingConflict, Just MissingConflict) -> property True
            other -> counterexample (show other) (property False)
      , counterexample "no-CQ must still reject MissingConflict (scan is typed-attack-gated)" $
          case (verdictOutcome vNoCQ, lrRejection <$> lNoCQ) of
            (Reject MissingConflict, Just MissingConflict) -> property True
            other -> counterexample (show other) (property False)
      , counterexample "no-typed must flip missing-conflict to accept (query justified)" $
          case (verdictOutcome vNoTyped, lNoTyped) of
            (Accept _ _ [(_, Justified)], Nothing) -> property True
            other -> counterexample (show other) (property False)
      ]
  where
    (vFull, lFull) = runCheckLocatedWith fullConfig input
    (vNoCQ, lNoCQ) = runCheckLocatedWith noCQConfig input
    (vNoTyped, lNoTyped) = runCheckLocatedWith noTypedConfig input
    input = testCheckInput negMissingConflict

-- ---------------------------------------------------------------------------
-- Small local utility
-- ---------------------------------------------------------------------------

splitOn :: Char -> String -> [String]
splitOn sep s = case break (== sep) s of
  (field, _ : rest) -> field : splitOn sep rest
  (field, "") -> [field]

ablationSpecProps :: [(String, IO Result)]
ablationSpecProps =
  [ ("ablation: runCheckLocatedWith fullConfig == runCheckLocated over both manifests", quickCheckResult prop_fullPathGuard)
  , ("ablation: accept-set monotonicity (full accepts are byte-identical)", quickCheckResult prop_monotonicity)
  , ("ablation: no-cq flips exactly reject-IncompleteArgument (surgical)", quickCheckResult prop_noCQSurgical)
  , ("ablation: no-typed flips exactly reject-R10/R11 (surgical)", quickCheckResult prop_noTypedSurgical)
  , ("ablation: codec rows unchanged under every config", quickCheckResult prop_codecRows)
  , ("ablation: report counts match the manifest partition (non-trivial)", quickCheckResult prop_reportMatchesPartition)
  , ("ablation: partition totality over both manifests", quickCheckResult prop_partitionTotality)
  , ("ablation: ablation.{json,tsv} renderer shape", quickCheckResult prop_rendererShape)
  , ("ablation: hole-mutant flip records its accept class", quickCheckResult prop_acceptClassRecording)
  , ("ablation: hand-written hole unit (full rejects, no-cq accepts)", quickCheckResult prop_handWrittenHole)
  , ("ablation: conflict scan stays on under no-cq, off under no-typed", quickCheckResult prop_conflictScanGating)
  ]
