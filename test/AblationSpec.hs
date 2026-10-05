-- | The M5 T6 ablation baselines as a standing test: the pure
-- ablation pass of "Lara.Measure" over both manifests (no subprocess, no
-- timing).
--
-- Two of the three deterministic ablations ('Lara.Check.noTypedConfig',
-- 'Lara.Check.noConflictScanConfig') only ever REMOVE rejections, so
-- @accept(full) ⊆ accept(ablation)@ holds for them by construction. The third,
-- 'Lara.Check.noCQConfig', is different in kind: it promotes typed holes to AF
-- nodes ('Lara.Check.PromoteTypedHoles'), so it changes accepted verdicts and
-- is identity exactly on hole-free units. This spec pins the strict
-- expectations: each rejection-relaxing ablation flips exactly its partition
-- buckets ('ablationBucket') reject→accept, @no-cq@ changes exactly the
-- located-hole rows while both runs accept, every other row is unchanged
-- (surgical), codec rows are unchanged by definition, the 'AblationReport'
-- aggregate matches the manifest partition, and the @ablation.{json,tsv}@
-- renderers produce the declared shape.
module AblationSpec (ablationSpecProps) where

import qualified Data.Aeson as Aeson
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.List (find, isPrefixOf)

import Test.QuickCheck

import Lara.AST hiding (Reject)
import SigmaFixture (sigmaOf)
import Lara.Check (CheckConfig (..), NodeCompleteness (..), fullConfig, noCQConfig, noConflictScanConfig, noTypedConfig)
import Lara.Diagnostics (LocatedRejection (..))
import Lara.Driver (runCheckLocated, runCheckLocatedWith)
import Lara.Measure
import Lara.Mutate (Expected (..), parseExpected)
import Lara.Prop (Pred (..), Prop (..))
import Lara.Wire (PublicStatus (..))
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

-- | Read fixture bytes strictly so the 8×input property product never retains
-- semi-closed lazy handles inside its deferred 'Property' list.
readFixture :: FilePath -> IO String
readFixture path = BS.unpack <$> BS.readFile path

allInputs :: IO [InputMeta]
allInputs = do
  mutants <- readFixture "fixtures/mutants/MANIFEST.tsv"
  corpus <- readFixture "corpus-units/MANIFEST.tsv"
  pure (parseMutantManifest mutants ++ parseCorpusManifest corpus)

cellsFor :: CheckConfig -> IO [AblationCell]
cellsFor cfg = do
  inputs <- allInputs
  mapM (\im -> computeAblation cfg im <$> readFixture (imPath im)) inputs

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
      bytes <- readFixture (imPath im)
      pure $ counterexample (imPath im) $ case decodeCheckInputFile bytes of
        Left _ -> property True
        Right input ->
          let (v1, l1) = runCheckLocatedWith fullConfig input
              (v2, l2) = runCheckLocated input
           in printSExpr (encodeVerdict v1) === printSExpr (encodeVerdict v2) .&&. l1 === l2

-- | Every rejection-relaxing 'CheckConfig' inhabitant, not just the named
-- baselines in 'ablationConfigs'. 'Lara.Check.CheckConfig' documents the
-- inclusion @accept(fullConfig) ⊆ accept(cfg)@ for every setting of its two
-- rejection-relaxing flags, so the property that enforces it quantifies over
-- all 4 states — enumerating only the named list once left states unenforced
-- (including @ccTypedAttacks=False, ccConflictScan=True@). Node completeness
-- stays 'CompleteNodesOnly' here: 'PromoteTypedHoles' changes the graph and is
-- pinned separately ('prop_promotionIdentityWithoutHoles').
allConfigs :: [(String, CheckConfig)]
allConfigs =
  [ (name, CheckConfig{ccNodeCompleteness = CompleteNodesOnly, ccTypedAttacks = t, ccConflictScan = s})
  | t <- [True, False]
  , s <- [True, False]
  , let name = "typed=" ++ show t ++ ",scan=" ++ show s
  ]

-- | Accept-set monotonicity, strict form: every input the full system accepts
-- is accepted by each rejection-relaxing 'CheckConfig' with the byte-identical
-- verdict (the config only removes rejection arms, so on full-accepts the
-- paths coincide). Quantifies over all 4 inhabitants via 'allConfigs'.
prop_monotonicity :: Property
prop_monotonicity = once $ ioProperty $ do
  inputs <- allInputs
  checks <- mapM check [(name, cfg, im) | (name, cfg) <- allConfigs, im <- inputs]
  pure $ conjoin (counterexample "no inputs discovered" (not (null checks)) : checks)
  where
    check (name, cfg, im) = do
      bytes <- readFixture (imPath im)
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

-- | Promotion has nothing to promote on a unit without holes: wherever the
-- full system's verdict reports no hole, 'noCQConfig' (and every
-- rejection-relaxing setting combined with it) yields the byte-identical
-- verdict. This is the exact scope of the @no-cq@ ablation's effect.
prop_promotionIdentityWithoutHoles :: Property
prop_promotionIdentityWithoutHoles = once $ ioProperty $ do
  inputs <- allInputs
  checks <- mapM check inputs
  pure $ conjoin (counterexample "no inputs discovered" (not (null checks)) : checks)
  where
    check im = do
      bytes <- readFixture (imPath im)
      pure $ counterexample (imPath im) $ case decodeCheckInputFile bytes of
        Left _ -> property True
        Right input ->
          let (vFull, lFull) = runCheckLocatedWith fullConfig input
              (vAbl, lAbl) = runCheckLocatedWith noCQConfig input
           in case verdictOutcome vFull of
                Accept{verdictHoles = _ : _} -> property True
                _ ->
                  printSExpr (encodeVerdict vAbl) === printSExpr (encodeVerdict vFull)
                    .&&. lAbl === lFull

-- ---------------------------------------------------------------------------
-- Surgical flips (strict, per ablation)
-- ---------------------------------------------------------------------------

-- | Strict surgical expectation for one named ablation: every row in its flip
-- buckets flips reject→accept (a missed reject whose recorded ablation outcome
-- is an accept class), every row in the @no-cq@ shift bucket stays an accept
-- whose verdict changes, and EVERY other row — other rejects, accepts, codec —
-- keeps the identical verdict.
--
-- Buckets are a list because @no-typed@ drops the whole typed-attack bundle
-- (the paper's baseline), so it flips both the typing rows and the completeness
-- rows; the single-bucket ablations are the isolating cells.
surgical :: String -> CheckConfig -> [AblationBucket] -> Property
surgical name cfg buckets = once $ ioProperty $ do
  cells <- cellsFor cfg
  pure $
    conjoin
      ( counterexample "no inputs discovered" (not (null cells))
          : map check cells
      )
  where
    check c =
      counterexample (name ++ ": " ++ imPath (acMeta c) ++ diag c) $
        case ablationBucket (imExpected (acMeta c)) of
          b
            | b `notElem` buckets ->
                conjoin
                  [ counterexample "must be unchanged" (not (acChanged c))
                  , acAblationActual c === acFullActual c
                  ]
          ShiftUnderNoCQ ->
            conjoin
              [ counterexample "full system must accept" ("accept-" `isPrefixOf` acFullActual c)
              , counterexample "ablation must accept" ("accept-" `isPrefixOf` acAblationActual c)
              , counterexample "the verdict must change" (acChanged c)
              ]
          _ ->
            conjoin
              [ counterexample "must be a missed reject" (acMissedReject c)
              , counterexample "full system must reject" ("reject-" `isPrefixOf` acFullActual c)
              , counterexample "ablation must accept" ("accept-" `isPrefixOf` acAblationActual c)
              ]
    diag c =
      " (full " ++ acFullActual c ++ " " ++ show (acFullStatuses c)
        ++ ", ablation " ++ acAblationActual c ++ " " ++ show (acAblationStatuses c) ++ ")"

prop_noCQSurgical :: Property
prop_noCQSurgical = surgical "no-cq" noCQConfig [ShiftUnderNoCQ]

prop_noTypedSurgical :: Property
prop_noTypedSurgical =
  surgical "no-typed" noTypedConfig [FlipUnderNoTyped, FlipUnderNoConflictScan]

prop_noConflictScanSurgical :: Property
prop_noConflictScanSurgical =
  surgical "no-conflict-scan" noConflictScanConfig [FlipUnderNoConflictScan]

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
      bytes <- readFixture (imPath im)
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
            , counterexample "codec rows can never change" (not (acChanged cell))
            ]

-- ---------------------------------------------------------------------------
-- Aggregate: non-triviality + partition agreement
-- ---------------------------------------------------------------------------

-- | Each rejection-relaxing ablation misses at least one reject and @no-cq@
-- changes at least one accept, and the 'AblationReport' aggregate
-- ('classSummaries') matches the manifest partition exactly: in a flip bucket
-- every row is missed, in the shift bucket every row changes with no reject on
-- either side, outside them nothing is missed, nothing is newly rejected and
-- nothing changes (no silent gaps between the report and the partition).
prop_reportMatchesPartition :: Property
prop_reportMatchesPartition = once $ ioProperty $ do
  inputs <- allInputs
  checks <- mapM (check inputs) ablationConfigs
  pure (conjoin checks)
  where
    check inputs (name, cfg, buckets) = do
      cells <- cellsFor cfg
      let sums = classSummaries (abrCells (AblationReport name cells))
          missedTotal = sum (map csMissed sums)
          changedTotal = sum [csTotal s - csUnchanged s | s <- sums]
          partitionTotal =
            length [im | im <- inputs, ablationBucket (imExpected im) `elem` buckets]
          shifts = ShiftUnderNoCQ `elem` buckets
      pure $
        counterexample name $
          conjoin
            [ if shifts
                then
                  counterexample "no-cq must change at least one accept" (changedTotal >= 1)
                    .&&. counterexample "changed total must equal the manifest partition" (changedTotal === partitionTotal)
                else
                  counterexample "ablation must miss at least one reject" (missedTotal >= 1)
                    .&&. counterexample "missed total must equal the manifest partition" (missedTotal === partitionTotal)
            , conjoin (map (perClass inputs buckets) sums)
            ]
    perClass inputs buckets s =
      counterexample (csExpected s) $
        case bucketOfSpelling inputs (csExpected s) of
          Just ShiftUnderNoCQ
            | ShiftUnderNoCQ `elem` buckets ->
                csUnchanged s === 0 .&&. csMissed s === 0 .&&. csNewRejects s === 0
          Just b
            | b `elem` buckets ->
                csMissed s === csTotal s
                  .&&. counterexample
                    "accept-class breakdown must cover every miss"
                    (sum (map snd (csMissedAcceptClasses s)) === csMissed s)
          Just _ ->
            csMissed s === 0 .&&. csNewRejects s === 0 .&&. csUnchanged s === csTotal s
          Nothing -> counterexample "summary class not in any manifest" (property False)
    bucketOfSpelling inputs cls =
      ablationBucket . imExpected <$> find ((== cls) . imExpectedText) inputs

-- | Partition totality: every typed 'Expected' present in either manifest
-- lands in exactly one bucket (the four buckets are a disjoint cover — a
-- function's image, counted), and the bucket assignment agrees with the
-- 'parseExpected' spelling table: @accept-located-hole@ is the No-CQ
-- bucket, @reject-R10@\/@reject-R11@ the No-typed bucket,
-- @reject-MissingConflict@ the No-conflict-scan bucket, everything else
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
          countOf ShiftUnderNoCQ
            + countOf FlipUnderNoTyped
            + countOf FlipUnderNoConflictScan
            + countOf UnchangedUnderAblations
            === length inputs
      , conjoin
          [ counterexample (imExpectedText im) $
              ablationBucket (imExpected im) === spellingBucket (imExpectedText im)
          | im <- inputs
          ]
      , counterexample "spelling table must parse its flip spellings" $
          conjoin
            [ fmap ablationBucket (parseExpected "accept-located-hole") === Just ShiftUnderNoCQ
            , fmap ablationBucket (parseExpected "reject-R10") === Just FlipUnderNoTyped
            , fmap ablationBucket (parseExpected "reject-R11") === Just FlipUnderNoTyped
            , fmap ablationBucket (parseExpected "reject-MissingConflict")
                === Just FlipUnderNoConflictScan
            ]
      ]
  where
    spellingBucket t
      | t == "accept-located-hole" = ShiftUnderNoCQ
      | t == "reject-MissingConflict" = FlipUnderNoConflictScan
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
                , "full_statuses"
                , "ablation_statuses"
                , "missed_reject"
                , "new_reject"
                , "changed"
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

-- | A known hole mutant records the status shift: the @E1@ base's query is
-- justified by the argument the mutant opens, so the full system reports it
-- as a located hole with the claim @gap@, while the No-CQ ablation promotes
-- the hole back to a node and publishes @justified@ (the paper's alarming
-- case).
prop_acceptClassRecording :: Property
prop_acceptClassRecording = once $ ioProperty $ do
  inputs <- allInputs
  let path = "fixtures/mutants/E1--hole-obligation-0.sexp"
  case find ((== path) . imPath) inputs of
    Nothing -> pure (counterexample (path ++ " not in the manifest") (property False))
    Just im -> do
      cell <- computeAblation noCQConfig im <$> readFixture (imPath im)
      pure $
        conjoin
          [ counterexample "must change" (acChanged cell)
          , counterexample "is not a reject flip" (not (acMissedReject cell || acNewReject cell))
          , acFullActual cell === "accept-located-hole"
          , acFullStatuses cell === ["gap"]
          , acAblationStatuses cell === ["justified"]
          ]

-- | A hand-written minimal unit with a declared hole (the 'CheckSpec'
-- hole shape): a defeasible rule with one Mandatory question, instantiated
-- with the question left open. The full system accepts, reports the hole and
-- publishes @gap@; 'noCQConfig' promotes the hole and publishes @justified@ —
-- a fast witness independent of the generated manifest.
prop_handWrittenHole :: Property
prop_handWrittenHole =
  once $
    conjoin
      [ counterexample "full system must accept with the hole and the claim gap" $
          case (verdictOutcome vFull, lFull) of
            (Accept [] [] [(_, Published Gap)] [_], Nothing) -> property True
            other -> counterexample (show other) (property False)
      , counterexample "no-CQ must accept with the query justified" $
          case (verdictOutcome vAbl, lAbl) of
            (Accept _ _ [(_, Published Justified)] _, Nothing) -> property True
            other -> counterexample (show other) (property False)
      ]
  where
    (vFull, lFull) = runCheckLocatedWith fullConfig input
    (vAbl, lAbl) = runCheckLocatedWith noCQConfig input
    input = testCheckInput holeUnit
    holeUnit =
      Unit
        { unitSigma = sigmaOf [] [] [("c", []), ("ans", [])]
        , unitRules =
            [ Rule
                (RuleId "d")
                []
                Defeasible
                []
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

-- | The conflict scan's config branch pinned in every direction, on the
-- 'CheckSpec' missing-conflict fixture (a self-contrary complete argument with
-- no declared attack). The scan is its own flag ('ccConflictScan'), so
-- exactly one named ablation may switch it alone: 'noCQConfig' must still
-- reject @MissingConflict@, 'noConflictScanConfig' must flip it to accept, and
-- 'noTypedConfig' must flip it too — it drops the whole typed-attack bundle.
--
-- The manifest now carries @reject-MissingConflict@ rows, so the surgical
-- properties cover this as well; this hand-written witness stays because it
-- pins the three configs against a fixture that no generator step can silently
-- stop producing.
prop_conflictScanGating :: Property
prop_conflictScanGating =
  once $
    conjoin
      [ counterexample "full system must reject MissingConflict" $
          rejectsMissingConflict (runCheckLocatedWith fullConfig input)
      , counterexample "no-CQ must still reject MissingConflict (a different flag)" $
          rejectsMissingConflict (runCheckLocatedWith noCQConfig input)
      , counterexample "no-conflict-scan must flip it to accept (query justified)" $
          acceptsJustified (runCheckLocatedWith noConflictScanConfig input)
      , counterexample "no-typed must flip it too (it drops the whole bundle)" $
          acceptsJustified (runCheckLocatedWith noTypedConfig input)
      ]
  where
    rejectsMissingConflict (v, l) = case (verdictOutcome v, lrRejection <$> l) of
      (Reject MissingConflict, Just MissingConflict) -> property True
      other -> counterexample (show other) (property False)
    acceptsJustified (v, l) = case (verdictOutcome v, l) of
      (Accept _ _ [(_, Published Justified)] _, Nothing) -> property True
      other -> counterexample (show other) (property False)
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
  , ("ablation: no-cq is identity wherever the full verdict has no hole", quickCheckResult prop_promotionIdentityWithoutHoles)
  , ("ablation: no-cq changes exactly accept-located-hole (surgical)", quickCheckResult prop_noCQSurgical)
  , ("ablation: no-typed flips exactly reject-R10/R11 + reject-MissingConflict (surgical)", quickCheckResult prop_noTypedSurgical)
  , ("ablation: no-conflict-scan flips exactly reject-MissingConflict (surgical)", quickCheckResult prop_noConflictScanSurgical)
  , ("ablation: codec rows unchanged under every config", quickCheckResult prop_codecRows)
  , ("ablation: report counts match the manifest partition (non-trivial)", quickCheckResult prop_reportMatchesPartition)
  , ("ablation: partition totality over both manifests", quickCheckResult prop_partitionTotality)
  , ("ablation: ablation.{json,tsv} renderer shape", quickCheckResult prop_rendererShape)
  , ("ablation: hole mutant records its status shift", quickCheckResult prop_acceptClassRecording)
  , ("ablation: hand-written hole unit (full reports gap, no-cq justified)", quickCheckResult prop_handWrittenHole)
  , ("ablation: conflict scan is switched by its own flag, not by no-cq", quickCheckResult prop_conflictScanGating)
  ]
