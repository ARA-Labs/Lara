-- | The axis-(c) measurement library (M5, T3): the pure metrics
-- behind @scripts\/measure.hs@.
--
-- Everything deterministic lives here — manifest discovery, per-input rejection
-- outcome / defect location / certificate size, the cross-driver agreement
-- COMPARATORS (pure functions of the Lean subprocess's stdout\/exit\/stderr),
-- the median helper, and JSON\/TSV rendering (via "Lara.ExpectedJson"'s
-- 'JValue' — the house codec, no @aeson@ in @src\/@). @scripts\/measure.hs@ adds
-- only the IO: reading files, spawning the Lean driver, and wall-clock timing.
--
-- Every column is defined for BOTH manifest regimes — verdict-bearing rows
-- (mutants + corpus units) and codec\/malformed rows — with 'Nothing' (rendered
-- @-@) marking a column outside a row's domain (eng review D5\/2A, D13\/OV-3).
--
-- The M5 T6 ablation baselines (@measurements\/ablation.{json,tsv}@) are a
-- second projection of the same decode+check core: 'computeAblation' runs the
-- checker under an ablated 'CheckConfig' and records what changed — missed
-- rejects, new rejects, and shifted statuses ('AblationCell', aggregated per
-- expected class by 'classSummaries').
module Lara.Measure
  ( -- * Discovery
    InputKind (..)
  , InputMeta (..)
  , parseMutantManifest
  , parseCorpusManifest
    -- * Deterministic per-input metrics
  , Deterministic (..)
  , computeDeterministic
  , codecFailText
    -- * Ablation baselines (M5 T6)
  , AblationBucket (..)
  , ablationBucket
  , ablationConfigs
  , AblationCell (..)
  , computeAblation
  , ClassSummary (..)
  , classSummaries
  , AblationReport (..)
    -- * Cross-driver agreement comparators (pure; unit-tested)
  , leanAgreeVerdict
  , leanAgreeCodec
  , outcomeExitCode
    -- * Records + statistics
  , Record (..)
  , median
    -- * Rendering
  , EnvBlock (..)
  , reportJson
  , reportTsv
  , tsvHeader
  , ablationJson
  , ablationTsv
  , ablationTsvHeader
  ) where

import Data.Char (isDigit)
import Data.List (intercalate, isInfixOf, isPrefixOf, nub, sort)

import Lara.AST (Label (..), RejectClass (..), Rejection (..), Status (..))
import Lara.Check (CheckConfig, fullConfig, noCQConfig, noConflictScanConfig, noTypedConfig)
import Lara.Diagnostics
  ( Constituent (..)
  , LocatedRejection (..)
  , SeededSites
  , constituentText
  , parseConstituentList
  , seededPrimary
  , seededSites
  , seededSitesList
  )
import Lara.Driver (runCheck, runCheckLocatedWith)
import Lara.ExpectedJson (JValue (..), renderJson)
import Lara.Mutate (Expected (..), expectedText, parseExpected, parseFamily, statusText)
import Lara.Replay (CheckInput, inputReplayId)
import Lara.Strict (SExpr (..))
import Lara.Wire
  ( HoleRow (..)
  , Outcome (..)
  , PublicStatus (..)
  , isPublished
  , Verdict (..)
  , WireError (..)
  , decodeCheckInputFile
  , encodeVerdict
  , parseSExpr
  , printSExpr
  )

-- ---------------------------------------------------------------------------
-- Discovery (manifest-driven, never a glob)
-- ---------------------------------------------------------------------------

-- | Which manifest a row came from: a generated mutant or a T2 corpus unit.
data InputKind = MutantRow | CorpusRow
  deriving (Eq, Show)

-- | One measured input's identity, resolved from a manifest row.
data InputMeta = InputMeta
  { imPath :: FilePath -- ^ the @.sexp@ file to measure
  , imBase :: String
  , imFamily :: String
  , imOperator :: Maybe String -- ^ 'Nothing' for corpus units
  , imExpected :: Expected
  , imExpectedText :: String
  , imExpectedLocation :: Maybe SeededSites
  -- ^ ordered seeded ground truth (manifest column 8): every element is an
  -- admissible located report, the head is the spec-order-first one
  -- (@docs\/evaluation.md#metric-contracts-class-match-location-and-coverage@); 'Nothing' when the row seeds no
  -- site (@-@). Non-empty by construction, so a row cannot be seeded at
  -- nothing and thereby drop out of the location metrics' denominator
  -- unnoticed
  , imHsDiag :: String -- ^ codec deletion-sensitivity pin (empty otherwise)
  , imLeanDiag :: String
  , imKind :: InputKind
  }
  deriving (Eq, Show)

-- | Parse @fixtures\/mutants\/MANIFEST.tsv@ into input rows (8 columns).
--
-- Columns 3 and 5 are both gated against their vocabularies ('parseFamily',
-- 'parseExpected') and a row failing either is dropped, so a stale or
-- hand-edited manifest cannot carry an unrecognized family or expectation into
-- @measurements\/report.{json,tsv}@. Dropping is safe precisely because
-- it is loud: @prop_manifestParsersTotal@ requires this parser to account for
-- every data row, so a dropped row fails the suite rather than silently
-- shrinking the measured set. That coupling only fires when a row /is/
-- dropped, though, and says nothing about a gate that stops dropping — so the
-- guards are pinned negatively by @prop_manifestGatesRejectUnknownSpellings@,
-- over a synthetic manifest rather than the committed one, whose spellings are
-- all valid and so leave both guards inert.
--
-- 'imFamily' stays a 'String' on purpose. 'parseCorpusManifest' fills the same
-- field with corpus group names (@paperbench@, @rebench@), which are an open
-- vocabulary and deliberately not mutation families — so the gate belongs on
-- this path only, and the parsed value is used to validate rather than to
-- replace the raw spelling (the 'imExpected' \/ 'imExpectedText' shape).
parseMutantManifest :: String -> [InputMeta]
parseMutantManifest raw =
  [ InputMeta
      { imPath = "fixtures/mutants/" ++ file
      , imBase = base
      , imFamily = family
      , imOperator = Just op
      , imExpected = e
      , imExpectedText = expected
      , imExpectedLocation = seededSites locs
      , imHsDiag = hsDiag
      , imLeanDiag = leanDiag
      , imKind = MutantRow
      }
  | ln <- lines raw
  , not (null ln)
  , not ("#" `isPrefixOf` ln)
  , [file, base, family, op, expected, hsDiag, leanDiag, loc] <- [splitTab ln]
  , Just e <- [parseExpected expected]
  , Just _family <- [parseFamily family]
  , Just locs <- [parseConstituentList loc]
  ]

-- | Parse @corpus-units\/MANIFEST.tsv@ into input rows (7 columns). A unit
-- whose @located_holes@ column is positive is specified to carry a located
-- hole, so it is measured as @accept-located-hole@ — the class the full
-- system reports for it (spec §4.4) and the one @no-cq@ promotes — exactly
-- as the hole mutants are; its claim status stays pinned by
-- @test\/CorpusUnitsSpec.hs@. Any other unit's @expected_status@ column
-- becomes an @accept-\<status\>@ expectation.
parseCorpusManifest :: String -> [InputMeta]
parseCorpusManifest raw =
  [ InputMeta
      { imPath = "corpus-units/" ++ artifact ++ "/" ++ claimId ++ "/unit.core.sexp"
      , imBase = artifact ++ "." ++ claimId
      , imFamily = group
      , imOperator = Nothing
      , imExpected = e
      , imExpectedText = expectedText e
      , imExpectedLocation = Nothing
      , imHsDiag = ""
      , imLeanDiag = ""
      , imKind = CorpusRow
      }
  | ln <- drop 1 (lines raw)
  , not (null ln)
  , [group, artifact, claimId, _type, _dbl, status, holes] <- [splitTab ln]
  , Just e <- [corpusExpected status holes]
  ]
  where
    corpusExpected status holes
      | holes == "0" = parseExpected ("accept-" ++ status)
      | all isDigit holes && not (null holes) = Just ExpectLocatedHole
      | otherwise = Nothing

splitTab :: String -> [String]
splitTab s = case break (== '\t') s of
  (field, '\t' : rest) -> field : splitTab rest
  (field, "") -> [field]
  (field, _) -> [field]

-- ---------------------------------------------------------------------------
-- Deterministic per-input metrics (no subprocess, no timing)
-- ---------------------------------------------------------------------------

-- | The columns computable in-process from a row's bytes alone.
data Deterministic = Deterministic
  { detActual :: String -- ^ actual outcome text (@reject-Rn@ / @accept-\<status\>@ / @codec-fail@)
  , detClassMatch :: Bool -- ^ actual outcome matches the specified one
  , detLocation :: Maybe Constituent
  -- ^ the located report: a reject's defect constituent, or an accept's first
  -- located hole (its original argument index, spec §4.4); 'Nothing' otherwise
  , detLocationMatch :: Maybe Bool
  -- ^ located constituent ∈ the seeded ground-truth list — the faithfulness
  -- claim ('-' off the seeded expectations)
  , detLocationPrimary :: Maybe Bool
  -- ^ located constituent '==' the list head (the spec-order-first site) —
  -- the ordering claim, measured never gated ('-' off the seeded
  -- expectations)
  , detReplayOk :: Maybe Bool -- ^ replay identity carried + stable (corpus units only)
  , detTotalBytes :: Int
  , detPolicyBytes :: Int -- ^ rendered bytes of the @(policy …)@ subtree
  , detPayloadBytes :: Int -- ^ total − policy (the distribution-bearing size)
  }
  deriving (Eq, Show)

-- | The shared decode+check core of 'computeDeterministic' and
-- 'computeAblation' (eng review D6): the decode boundary, the
-- config-parameterized checker call, and the outcome spelling exist exactly
-- once. A codec row fails before any config is consulted, so it is identical
-- under every 'CheckConfig' by construction.
data RowOutcome
  = RowCodecFail String
    -- ^ the rendered @ctx: msg@ decode diagnostic (matched against the
    -- manifest's deletion-sensitivity pin)
  | RowChecked CheckInput Verdict (Maybe LocatedRejection)

-- | Decode one input's bytes and, on success, check it under the config.
rowOutcome :: CheckConfig -> String -> RowOutcome
rowOutcome cfg bytes = case decodeCheckInputFile bytes of
  Left (WireError ctx msg) -> RowCodecFail (ctx ++ ": " ++ msg)
  Right input ->
    let (verdict, located) = runCheckLocatedWith cfg input
     in RowChecked input verdict located

-- | The row's outcome in report spelling ('actualText', or 'codecFailText').
rowActual :: RowOutcome -> String
rowActual row = case row of
  RowCodecFail _ -> codecFailText
  RowChecked _ verdict _ -> actualText (verdictOutcome verdict)

-- | Whether the row is a checker reject. A codec failure is not one — it
-- happens before the checker (and before any config) is reached.
rowRejects :: RowOutcome -> Bool
rowRejects row = case row of
  RowCodecFail _ -> False
  RowChecked _ verdict _ -> case verdictOutcome verdict of
    Reject{} -> True
    Accept{} -> False

-- | The @actual@ spelling of a row whose bytes fail to decode.
codecFailText :: String
codecFailText = "codec-fail"

-- | Compute the deterministic metrics for one input from its file bytes — the
-- 'fullConfig' projection of the shared 'rowOutcome' core.
computeDeterministic :: InputMeta -> String -> Deterministic
computeDeterministic im bytes = case rowOutcome fullConfig bytes of
  RowCodecFail rendered ->
    let classMatch = case imExpected im of
          -- codec row: the decode must fail AND carry the operator's pinned
          -- diagnostic (any-failure is not enough — the deletion-sensitivity pin
          -- carries into the metric).
          ExpectCodecReject -> not (null (imHsDiag im)) && imHsDiag im `isInfixOf` rendered
          _ -> False -- a verdict row that fails to decode is a mismatch
     in base {detActual = codecFailText, detClassMatch = classMatch}
  RowChecked input verdict located ->
    let outcome = verdictOutcome verdict
        loc = case located of
          Just lr -> Just (lrConstituent lr)
          Nothing -> case outcome of
            Accept{verdictHoles = hole : _} -> Just (CArgument (hrIndex hole))
            _ -> Nothing
     in base
          { detActual = actualText outcome
          , detClassMatch = classMatches (imExpected im) outcome
          , detLocation = loc
          -- location metrics are defined on the seeded expectations only
          -- (the seeded rejects and the seeded located hole); both are
          -- measured, never gated (docs/evaluation.md#metric-contracts-class-match-location-and-coverage).
          , detLocationMatch = onSeeded (\_ locs -> maybe False (`elem` locs) loc)
          , detLocationPrimary = onSeeded (\primary _ -> maybe False (== primary) loc)
          , detReplayOk = case imKind im of
              CorpusRow -> Just (replayStable input verdict)
              MutantRow -> Nothing
          }
  where
    total = length bytes
    policy = policyBytes bytes
    -- The location metrics' shared domain guard: defined exactly on the
    -- seeded expectations with a non-empty ground-truth list, whose head (the
    -- spec-order-first constituent) is passed alongside the list.
    onSeeded f = case imExpected im of
      ExpectClass _ -> withLocs f
      ExpectLocatedHole -> withLocs f
      ExpectMissingConflict -> withLocs f
      _ -> Nothing
    withLocs f =
      fmap (\ss -> f (seededPrimary ss) (seededSitesList ss)) (imExpectedLocation im)
    base =
      Deterministic
        { detActual = "-"
        , detClassMatch = False
        , detLocation = Nothing
        , detLocationMatch = Nothing
        , detLocationPrimary = Nothing
        , detReplayOk = Nothing
        , detTotalBytes = total
        , detPolicyBytes = policy
        , detPayloadBytes = total - policy
        }

-- | Whether the actual verdict outcome matches the specified expectation. Typed
-- (not string) so accept-family and cycle accepts are distinguished even though
-- their verdicts can look alike.
classMatches :: Expected -> Outcome -> Bool
classMatches e outcome = case e of
  ExpectCodecReject -> False -- decoded cleanly; expected a codec failure
  ExpectClass c -> outcome == Reject (RejectClass c)
  ExpectLocatedHole -> locatedHole outcome
  ExpectMissingConflict -> outcome == Reject MissingConflict
  ExpectAllContested -> allContested outcome
  ExpectEvidenceBlocked -> evidenceBlocked outcome
  ExpectPrimaryStatus s -> primaryStatus outcome == Just s

-- | The actual outcome in manifest spelling (for the report's @actual@ column).
actualText :: Outcome -> String
actualText outcome = case outcome of
  Reject r -> "reject-" ++ rejectionText r
  -- An @evidence-blocked@ query has no four-state public status — spec §4.3 —
  -- so it is its own class and never matches an expected status.
  Accept _ _ statuses _
    | evidenceBlocked outcome -> "accept-evidence-blocked"
    -- A located hole is reported beside the statuses, never as one (spec
    -- §4.4), so it is its own class and the statuses go to their own column.
    | locatedHole outcome -> "accept-located-hole"
    | allContested outcome -> "accept-all-contested"
    | [(_, Published st)] <- statuses -> "accept-" ++ statusText st
    | otherwise -> "accept-other"

rejectionText :: Rejection -> String
rejectionText r = case r of
  RejectClass c -> show (c :: RejectClass)
  other -> show other

allContested :: Outcome -> Bool
allContested outcome = case outcome of
  Accept labels _ statuses _ ->
    not (null labels)
      && all ((== LUndec) . snd) labels
      && not (null statuses)
      && all ((== Published Contested) . snd) statuses
  _ -> False

-- | The verdict accepts and reports at least one located hole (spec §4.4).
locatedHole :: Outcome -> Bool
locatedHole outcome = case outcome of
  Accept{verdictHoles = holes} -> not (null holes)
  _ -> False

-- | The verdict accepts and some queried claim's public status is
-- @evidence-blocked@ (spec §4.3).
evidenceBlocked :: Outcome -> Bool
evidenceBlocked outcome = case outcome of
  Accept _ _ statuses _ -> any (not . isPublished . snd) statuses
  _ -> False

primaryStatus :: Outcome -> Maybe Status
primaryStatus outcome = case outcome of
  Accept _ _ [(_, Published st)] _ -> Just st
  _ -> Nothing

-- | The verdict carries the input's replay identity, and re-checking is
-- byte-stable (a regression guard on replay-carried identity + determinism).
replayStable :: CheckInput -> Verdict -> Bool
replayStable input verdict =
  verdictReplayId verdict == inputReplayId input
    && printSExpr (encodeVerdict verdict) == printSExpr (encodeVerdict (runCheck input))

-- | Rendered bytes of the unit's @(policy …)@ subtree (the fixed ~6-7KB
-- @corpus-v1@ image); 0 when the bytes do not parse (a codec row). The policy is
-- looked up INSIDE the @(unit …)@ section — the @(replay-id …)@ section also
-- carries a @(policy \<id\>)@ form (the policy identity), which must not be
-- mistaken for the policy body.
policyBytes :: String -> Int
policyBytes bytes = case parseSExpr bytes of
  Right top -> maybe 0 (length . printSExpr) (findSection "unit" top >>= findSection "policy")
  Left _ -> 0

findSection :: String -> SExpr -> Maybe SExpr
findSection tag = go
  where
    go e@(SList (SAtom t : _)) | t == tag = Just e
    go (SList kids) = firstJust (map go kids)
    go _ = Nothing
    firstJust = foldr (\x acc -> maybe acc Just x) Nothing

-- ---------------------------------------------------------------------------
-- Ablation baselines (M5 T6): per-input cells + per-class aggregate
-- ---------------------------------------------------------------------------

-- | The ablation partition over the typed 'Expected' vocabulary (not a prose
-- family list — hand lists drift; the spelling table is
-- 'Lara.Mutate.parseExpected'). Total by construction: every constructor is
-- handled, so a future class or spelling cannot silently fall outside the
-- partition. Drives the per-ablation table and the surgical assertions.
data AblationBucket
  = ShiftUnderNoCQ
    -- ^ node completeness is load-bearing (the located-hole mutants): the
    -- full system accepts and reports the hole beside the AF, and @no-cq@
    -- promotes it to a node, so the verdict changes while both accept — an
    -- added label at least, and a shifted status where the hole was the
    -- claim's only support (the paper's alarming case)
  | FlipUnderNoTyped
    -- ^ per-attack typing is load-bearing (R10\/R11 bad-attack-targets)
  | FlipUnderNoConflictScan
    -- ^ the completeness scan is load-bearing (the drop-covering-attack
    -- mutants) — the isolating evidence for attack completeness
  | UnchangedUnderAblations
    -- ^ identical under every ablation: rejects decided by rules behind no
    -- flag, codec rows (decode fails before any config), and hole-free
    -- accepts (the rejection-relaxing flags only remove rejections, and
    -- promotion has nothing to promote)
  deriving (Eq, Ord, Show)

-- | Which bucket an expected class belongs to.
ablationBucket :: Expected -> AblationBucket
ablationBucket e = case e of
  ExpectLocatedHole -> ShiftUnderNoCQ
  ExpectMissingConflict -> FlipUnderNoConflictScan
  ExpectClass R10 -> FlipUnderNoTyped
  ExpectClass R11 -> FlipUnderNoTyped
  ExpectClass _ -> UnchangedUnderAblations -- R1/R3/…: rules behind no flag
  ExpectCodecReject -> UnchangedUnderAblations
  ExpectAllContested -> UnchangedUnderAblations
  -- Blocking is decided at the driver boundary from the §4.3 prune, behind no
  -- ablation flag, and the mutant accepts either way.
  ExpectEvidenceBlocked -> UnchangedUnderAblations
  ExpectPrimaryStatus _ -> UnchangedUnderAblations

-- | The named ablation runs the script and tests iterate, each with the
-- partition buckets it must change (and must change nothing else).
--
-- @no-typed@ carries TWO buckets because it is the paper's \"nodes and
-- arbitrary attack edges\" baseline: it drops the whole typed-attack bundle,
-- so both the typing rows and the completeness rows flip under it. @no-cq@ and
-- @no-conflict-scan@ each carry one, and are therefore the isolating cells —
-- the second exists precisely because the first-generation partition had
-- no cell that separated the completeness scan from the typing it shipped with.
--
-- @no-cq@ is different in kind ('Lara.Check.PromoteTypedHoles'): it changes
-- which declarations are AF nodes rather than removing a rejection arm, so its
-- bucket shifts accepted verdicts instead of flipping rejects.
ablationConfigs :: [(String, CheckConfig, [AblationBucket])]
ablationConfigs =
  [ ("no-cq", noCQConfig, [ShiftUnderNoCQ])
  , ("no-typed", noTypedConfig, [FlipUnderNoTyped, FlipUnderNoConflictScan])
  , ("no-conflict-scan", noConflictScanConfig, [FlipUnderNoConflictScan])
  ]

-- | One (input × ablation-config) measurement, recording change in __both__
-- directions: a full-system reject the ablation accepts (the rejection-relaxing
-- flags), a full-system accept the ablation rejects (possible under
-- 'Lara.Check.PromoteTypedHoles', which can make a conflict required that the
-- full checker never asks for), and an accept whose verdict changed. The
-- per-query public statuses of both runs are kept, so a status that a promoted
-- hole moves (@gap@ → @justified@ is the alarming case) is visible even when
-- both outcome texts read @accept-located-hole@.
data AblationCell = AblationCell
  { acMeta :: InputMeta
  , acFullActual :: String -- ^ the full system's outcome text
  , acAblationActual :: String -- ^ the ablation's outcome text
  , acFullStatuses :: [String]
  -- ^ the full system's public statuses, in query order (empty off accepts)
  , acAblationStatuses :: [String] -- ^ the ablation's, likewise
  , acMissedReject :: Bool -- ^ the full system rejects, the ablation accepts
  , acNewReject :: Bool -- ^ the full system accepts, the ablation rejects
  , acChanged :: Bool -- ^ the two verdicts differ (never on a codec row)
  }
  deriving (Eq, Show)

-- | Measure one input under an ablation config: both projections of the shared
-- 'rowOutcome' core, plus the change flags.
computeAblation :: CheckConfig -> InputMeta -> String -> AblationCell
computeAblation cfg im bytes =
  AblationCell
    { acMeta = im
    , acFullActual = rowActual full
    , acAblationActual = rowActual ablated
    , acFullStatuses = rowStatuses full
    , acAblationStatuses = rowStatuses ablated
    , acMissedReject = rowRejects full && rowAccepts ablated
    , acNewReject = rowAccepts full && rowRejects ablated
    , acChanged = rowVerdict full /= rowVerdict ablated
    }
  where
    full = rowOutcome fullConfig bytes
    ablated = rowOutcome cfg bytes
    rowAccepts row = case row of
      RowChecked _ verdict _ -> case verdictOutcome verdict of
        Accept{} -> True
        Reject{} -> False
      RowCodecFail _ -> False
    rowVerdict row = case row of
      RowChecked _ verdict _ -> Just verdict
      RowCodecFail _ -> Nothing

-- | The public statuses of an accepted row in query order, in report spelling
-- (@evidence-blocked@ for a blocked query); empty for a reject or codec row.
rowStatuses :: RowOutcome -> [String]
rowStatuses row = case row of
  RowChecked _ verdict _ -> case verdictOutcome verdict of
    Accept{verdictStatuses = statuses} -> map (publicStatusText . snd) statuses
    Reject{} -> []
  RowCodecFail _ -> []
  where
    publicStatusText st = case st of
      Published status -> statusText status
      EvidenceBlocked _ -> "evidence-blocked"

-- | Per-expected-class aggregate of one ablation run (one paper-table cell):
-- how many full-system rejects the ablation misses (with the accept-class
-- breakdown of those misses), how many full-system accepts it newly rejects,
-- how many accepts shift a status (with the @full->ablation@ breakdown), and
-- how many rows are unchanged (the surgical check: outside the changed
-- buckets, @unchanged == total@).
data ClassSummary = ClassSummary
  { csExpected :: String -- ^ manifest expected spelling
  , csTotal :: Int
  , csMissed :: Int -- ^ full-system rejects the ablation accepts
  , csMissedAcceptClasses :: [(String, Int)]
    -- ^ ablation outcome text of the misses (sorted, counted)
  , csNewRejects :: Int -- ^ full-system accepts the ablation rejects
  , csStatusShifts :: Int -- ^ accepts under both whose statuses differ
  , csShiftedStatuses :: [(String, Int)]
    -- ^ @full->ablation@ per-query status pairs that differ (sorted, counted)
  , csUnchanged :: Int -- ^ rows whose verdict is identical under the ablation
  }
  deriving (Eq, Show)

-- | Summarize an ablation run's cells per expected class (sorted spelling).
classSummaries :: [AblationCell] -> [ClassSummary]
classSummaries cells =
  [ ClassSummary
      { csExpected = cls
      , csTotal = length inClass
      , csMissed = length missed
      , csMissedAcceptClasses = counted (map acAblationActual missed)
      , csNewRejects = length (filter acNewReject inClass)
      , csStatusShifts = length shifted
      , csShiftedStatuses =
          counted
            [ f ++ "->" ++ a
            | c <- shifted
            , (f, a) <- zip (acFullStatuses c) (acAblationStatuses c)
            , f /= a
            ]
      , csUnchanged = length [c | c <- inClass, not (acChanged c)]
      }
  | cls <- nub (sort (map expectedOf cells))
  , let inClass = [c | c <- cells, expectedOf c == cls]
        missed = filter acMissedReject inClass
        shifted = filter statusShift inClass
  ]
  where
    expectedOf = imExpectedText . acMeta
    counted xs = [(x, length [y | y <- xs, y == x]) | x <- nub (sort xs)]
    statusShift c =
      not (acMissedReject c)
        && not (acNewReject c)
        && acFullStatuses c /= acAblationStatuses c

-- | One ablation run over the manifests: the named config's cells. The
-- renderers derive the aggregate ('classSummaries') from the cells.
data AblationReport = AblationReport
  { abrAblation :: String -- ^ the 'ablationConfigs' name (@no-cq@, @no-typed@, @no-conflict-scan@)
  , abrCells :: [AblationCell]
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Cross-driver agreement (pure comparators; the Lean subprocess is IO)
-- ---------------------------------------------------------------------------

-- | The exit code the outcome implies (the @app\/Main.hs@ convention both
-- drivers follow): 0 accept, 1 reject.
outcomeExitCode :: Outcome -> Int
outcomeExitCode outcome = case outcome of
  Accept{} -> 0
  Reject{} -> 1

-- | Verdict-bearing regime: the Lean driver's stdout is byte-equal to the exact
-- @app\/Main.hs@ verdict rendering (reused from "Lara.Wire", not re-derived) and
-- its exit code equals the outcome-derived one.
leanAgreeVerdict :: Verdict -> String -> Int -> Bool
leanAgreeVerdict verdict leanStdout leanExit =
  leanStdout == printSExpr (encodeVerdict verdict) ++ "\n"
    && leanExit == outcomeExitCode (verdictOutcome verdict)

-- | Codec regime: the Lean driver exits 2 with empty stdout and stderr carrying
-- the manifest's pinned Lean diagnostic.
leanAgreeCodec :: String -> Int -> String -> String -> Bool
leanAgreeCodec leanPin leanExit leanStdout leanStderr =
  leanExit == 2 && null leanStdout && not (null leanPin) && leanPin `isInfixOf` leanStderr

-- ---------------------------------------------------------------------------
-- Records + statistics
-- ---------------------------------------------------------------------------

-- | One fully measured input: its identity + deterministic metrics + the
-- IO-derived columns (cross-driver agreement and the retained timing samples).
data Record = Record
  { recMeta :: InputMeta
  , recDet :: Deterministic
  , recLeanAgree :: Maybe Bool
  , recHsSamplesNs :: [Integer] -- ^ all retained @hs_check@ samples (median in the report)
  , recLeanSamplesNs :: [Integer] -- ^ all retained @lean_wall@ samples
  }

-- | Median of a sample list (of the retained runs). 'Nothing' on empty.
median :: [Integer] -> Maybe Integer
median [] = Nothing
median xs = Just (sort xs !! (length xs `div` 2))

-- ---------------------------------------------------------------------------
-- Rendering (JValue — house codec; and flat TSV)
-- ---------------------------------------------------------------------------

-- | The reproducibility environment block (spec: git rev + dirty, tool
-- versions, OS, CPU), gathered by @scripts\/measure.hs@.
data EnvBlock = EnvBlock
  { envGitRev :: String
  , envGitDirty :: Bool
  , envGhc :: String
  , envLean :: String
  , envOs :: String
  , envCpu :: String
  }
  deriving (Eq, Show)

-- | The full @report.json@ content: environment + aggregate + per-input records.
reportJson :: EnvBlock -> [Record] -> String
reportJson env records =
  renderJson $
    JObject
      [ ("environment", envJson env)
      , ("aggregate", aggregateJson records)
      , ("records", JArray (map recordJson records))
      ]

envJson :: EnvBlock -> JValue
envJson env =
  JObject
    [ ("git-rev", JString (envGitRev env))
    , ("git-dirty", JBool (envGitDirty env))
    , ("ghc", JString (envGhc env))
    , ("lean", JString (envLean env))
    , ("os", JString (envOs env))
    , ("cpu", JString (envCpu env))
    ]

recordJson :: Record -> JValue
recordJson (Record im det leanAgree hsNs leanNs) =
  JObject
    [ ("input", JString (imPath im))
    , ("base", JString (imBase im))
    , ("family", JString (imFamily im))
    , ("operator", maybe JNull JString (imOperator im))
    , ("expected", JString (imExpectedText im))
    , ("actual", JString (detActual det))
    , ("class-match", JBool (detClassMatch det))
    , ("location", maybe JNull (JString . constituentText) (detLocation det))
    , ("location-match", maybeBoolJson (detLocationMatch det))
    , ("location-primary", maybeBoolJson (detLocationPrimary det))
    , ("lean-agree", maybeBoolJson leanAgree)
    , ("replay-ok", maybeBoolJson (detReplayOk det))
    , ("total-bytes", JNumber (detTotalBytes det))
    , ("policy-bytes", JNumber (detPolicyBytes det))
    , ("payload-bytes", JNumber (detPayloadBytes det))
    , ("hs-check-ns", medianJson hsNs)
    , ("hs-check-samples-ns", JArray (map bigNum hsNs))
    , ("lean-wall-ns", medianJson leanNs)
    , ("lean-wall-samples-ns", JArray (map bigNum leanNs))
    ]

maybeBoolJson :: Maybe Bool -> JValue
maybeBoolJson = maybe JNull JBool

medianJson :: [Integer] -> JValue
medianJson = maybe JNull bigNum . median

-- | 'JNumber' is 'Int'; nanosecond samples fit a 64-bit 'Int' comfortably.
bigNum :: Integer -> JValue
bigNum = JNumber . fromIntegral

-- | Aggregate block: overall + per-expected-class accuracy, location-accuracy
-- (membership) and location-primary (head-equality) rates, replay-success
-- rate, cross-driver agreement rate, byte-size distributions over total +
-- payload, and checking-time distributions over @hs_check@ + @lean_wall@ (the
-- two are different protocols — not comparable).
aggregateJson :: [Record] -> JValue
aggregateJson records =
  JObject
    [ ("count", JNumber (length records))
    , ("class-match-rate", rateJson [detClassMatch (recDet r) | r <- records])
    , ("class-accuracy", JObject [(cls, classRate cls) | cls <- classes])
    , ( "location-accuracy-rate"
      , rateJson [b | r <- records, Just b <- [detLocationMatch (recDet r)]]
      )
    , ( "location-primary-rate"
      , rateJson [b | r <- records, Just b <- [detLocationPrimary (recDet r)]]
      )
    , ( "replay-success-rate"
      , rateJson [b | r <- records, Just b <- [detReplayOk (recDet r)]]
      )
    , ( "lean-agree-rate"
      , rateJson [b | r <- records, Just b <- [recLeanAgree r]]
      )
    , ("total-bytes", distJson [detTotalBytes (recDet r) | r <- records])
    , ("payload-bytes", distJson [detPayloadBytes (recDet r) | r <- records])
    , ("hs-check-ns", nsDistJson (recordMedians recHsSamplesNs))
    , ("lean-wall-ns", nsDistJson (recordMedians recLeanSamplesNs))
    ]
  where
    classes = nub (sort [imExpectedText (recMeta r) | r <- records])
    classRate cls = rateJson [detClassMatch (recDet r) | r <- records, imExpectedText (recMeta r) == cls]
    recordMedians samplesOf = [m | r <- records, Just m <- [median (samplesOf r)]]

-- | @{min, median, max, count}@ over a nanosecond sample (Integer to avoid any
-- 'Int' width concern; distinct from the byte 'distJson').
nsDistJson :: [Integer] -> JValue
nsDistJson [] = JObject [("count", JNumber 0)]
nsDistJson xs =
  JObject
    [ ("min", bigNum (minimum xs))
    , ("median", medianJson xs)
    , ("max", bigNum (maximum xs))
    , ("count", JNumber (length xs))
    ]

-- | @{matched, total}@ for a boolean sample (a rate the report consumer divides;
-- kept as counts to avoid floating point in the house codec).
rateJson :: [Bool] -> JValue
rateJson bs =
  JObject
    [ ("matched", JNumber (length (filter id bs)))
    , ("total", JNumber (length bs))
    ]

-- | @{min, median, max, count}@ for a byte-size sample (delegates to
-- 'nsDistJson' — same shape, over 'Integer').
distJson :: [Int] -> JValue
distJson = nsDistJson . map fromIntegral

-- | The flat TSV columns (the paper's table-generator input). @-@ marks a column
-- outside a row's domain.
tsvHeader :: String
tsvHeader =
  intercalate
    "\t"
    [ "input"
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

-- | The full @report.tsv@ content (header + one row per record).
reportTsv :: [Record] -> String
reportTsv records = unlines (tsvHeader : map recordTsv records)

recordTsv :: Record -> String
recordTsv (Record im det leanAgree hsNs leanNs) =
  intercalate
    "\t"
    [ imPath im
    , imBase im
    , imFamily im
    , maybe "-" id (imOperator im)
    , imExpectedText im
    , detActual det
    , boolCell (detClassMatch det)
    , maybe "-" constituentText (detLocation det)
    , maybeBoolCell (detLocationMatch det)
    , maybeBoolCell (detLocationPrimary det)
    , maybeBoolCell leanAgree
    , maybeBoolCell (detReplayOk det)
    , show (detTotalBytes det)
    , show (detPolicyBytes det)
    , show (detPayloadBytes det)
    , maybe "-" show (median hsNs)
    , maybe "-" show (median leanNs)
    ]

boolCell :: Bool -> String
boolCell b = if b then "true" else "false"

maybeBoolCell :: Maybe Bool -> String
maybeBoolCell = maybe "-" boolCell

-- ---------------------------------------------------------------------------
-- Ablation rendering (measurements/ablation.{json,tsv} — the paper's
-- ablation-table input; same house codec and env block as report.{json,tsv})
-- ---------------------------------------------------------------------------

-- | The full @ablation.json@ content: environment + one block per ablation
-- (per-expected-class aggregate + per-input records).
ablationJson :: EnvBlock -> [AblationReport] -> String
ablationJson env reports =
  renderJson $
    JObject
      [ ("environment", envJson env)
      , ("ablations", JArray (map ablationBlockJson reports))
      ]

ablationBlockJson :: AblationReport -> JValue
ablationBlockJson (AblationReport name cells) =
  JObject
    [ ("ablation", JString name)
    , ("aggregate", ablationAggregateJson cells)
    , ("records", JArray (map ablationCellJson cells))
    ]

ablationAggregateJson :: [AblationCell] -> JValue
ablationAggregateJson cells =
  JObject
    [ ("count", JNumber (length cells))
    , ("missed-rejects", JNumber (sum (map csMissed sums)))
    , ("new-rejects", JNumber (sum (map csNewRejects sums)))
    , ("status-shifts", JNumber (sum (map csStatusShifts sums)))
    , ("unchanged", JNumber (sum (map csUnchanged sums)))
    , ("by-expected", JObject [(csExpected s, classSummaryJson s) | s <- sums])
    ]
  where
    sums = classSummaries cells

classSummaryJson :: ClassSummary -> JValue
classSummaryJson s =
  JObject
    [ ("total", JNumber (csTotal s))
    , ("missed-rejects", JNumber (csMissed s))
    , ("missed-accept-classes", JObject [(cls, JNumber n) | (cls, n) <- csMissedAcceptClasses s])
    , ("new-rejects", JNumber (csNewRejects s))
    , ("status-shifts", JNumber (csStatusShifts s))
    , ("shifted-statuses", JObject [(pair, JNumber n) | (pair, n) <- csShiftedStatuses s])
    , ("unchanged", JNumber (csUnchanged s))
    ]

ablationCellJson :: AblationCell -> JValue
ablationCellJson c =
  JObject
    [ ("input", JString (imPath im))
    , ("base", JString (imBase im))
    , ("family", JString (imFamily im))
    , ("operator", maybe JNull JString (imOperator im))
    , ("expected", JString (imExpectedText im))
    , ("full-actual", JString (acFullActual c))
    , ("ablation-actual", JString (acAblationActual c))
    , ("full-statuses", JArray (map JString (acFullStatuses c)))
    , ("ablation-statuses", JArray (map JString (acAblationStatuses c)))
    , ("missed-reject", JBool (acMissedReject c))
    , ("new-reject", JBool (acNewReject c))
    , ("changed", JBool (acChanged c))
    ]
  where
    im = acMeta c

-- | The flat @ablation.tsv@ columns (one row per ablation × input).
ablationTsvHeader :: String
ablationTsvHeader =
  intercalate
    "\t"
    [ "ablation"
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

-- | The full @ablation.tsv@ content (header + every run's rows, in run order).
ablationTsv :: [AblationReport] -> String
ablationTsv reports =
  unlines
    ( ablationTsvHeader
        : [ablationCellTsv name c | AblationReport name cells <- reports, c <- cells]
    )

ablationCellTsv :: String -> AblationCell -> String
ablationCellTsv name c =
  intercalate
    "\t"
    [ name
    , imPath im
    , imBase im
    , imFamily im
    , maybe "-" id (imOperator im)
    , imExpectedText im
    , acFullActual c
    , acAblationActual c
    , statusesCell (acFullStatuses c)
    , statusesCell (acAblationStatuses c)
    , boolCell (acMissedReject c)
    , boolCell (acNewReject c)
    , boolCell (acChanged c)
    ]
  where
    im = acMeta c
    statusesCell [] = "-"
    statusesCell sts = intercalate "," sts
