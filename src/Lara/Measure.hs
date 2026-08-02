-- | The axis-(c) measurement library (M5 tracker #48, T3): the pure metrics
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
module Lara.Measure
  ( -- * Discovery
    InputKind (..)
  , InputMeta (..)
  , parseMutantManifest
  , parseCorpusManifest
    -- * Deterministic per-input metrics
  , Deterministic (..)
  , computeDeterministic
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
  ) where

import Data.List (intercalate, isInfixOf, isPrefixOf, nub, sort)

import Lara.AST (Label (..), RejectClass, Rejection (..), Status (..))
import Lara.Diagnostics
  ( Constituent
  , LocatedRejection (..)
  , constituentText
  , parseConstituent
  )
import Lara.Driver (runCheck, runCheckLocated)
import Lara.ExpectedJson (JValue (..), renderJson)
import Lara.Mutate (Expected (..), parseExpected, statusText)
import Lara.Replay (CheckInput, inputReplayId)
import Lara.Strict (SExpr (..))
import Lara.Wire
  ( Outcome (..)
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
  , imExpectedLocation :: Maybe Constituent -- ^ seeded ground truth (manifest column 8)
  , imHsDiag :: String -- ^ codec deletion-sensitivity pin (empty otherwise)
  , imLeanDiag :: String
  , imKind :: InputKind
  }
  deriving (Eq, Show)

-- | Parse @fixtures\/mutants\/MANIFEST.tsv@ into input rows (8 columns).
parseMutantManifest :: String -> [InputMeta]
parseMutantManifest raw =
  [ InputMeta
      { imPath = "fixtures/mutants/" ++ file
      , imBase = base
      , imFamily = family
      , imOperator = Just op
      , imExpected = e
      , imExpectedText = expected
      , imExpectedLocation = if loc == "-" then Nothing else parseConstituent loc
      , imHsDiag = hsDiag
      , imLeanDiag = leanDiag
      , imKind = MutantRow
      }
  | ln <- lines raw
  , not (null ln)
  , not ("#" `isPrefixOf` ln)
  , [file, base, family, op, expected, hsDiag, leanDiag, loc] <- [splitTab ln]
  , Just e <- [parseExpected expected]
  ]

-- | Parse @corpus-units\/MANIFEST.tsv@ into input rows (6 columns; the
-- @expected_status@ column becomes an @accept-\<status\>@ expectation).
parseCorpusManifest :: String -> [InputMeta]
parseCorpusManifest raw =
  [ InputMeta
      { imPath = "corpus-units/" ++ artifact ++ "/" ++ claimId ++ "/unit.core.sexp"
      , imBase = artifact ++ "." ++ claimId
      , imFamily = group
      , imOperator = Nothing
      , imExpected = e
      , imExpectedText = "accept-" ++ status
      , imExpectedLocation = Nothing
      , imHsDiag = ""
      , imLeanDiag = ""
      , imKind = CorpusRow
      }
  | ln <- drop 1 (lines raw)
  , not (null ln)
  , [group, artifact, claimId, _type, _dbl, status] <- [splitTab ln]
  , Just e <- [parseExpected ("accept-" ++ status)]
  ]

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
  , detLocation :: Maybe Constituent -- ^ located defect constituent (rejects only)
  , detLocationMatch :: Maybe Bool -- ^ located vs seeded ground truth ('-' off rejects)
  , detReplayOk :: Maybe Bool -- ^ #36 replay identity carried + stable (corpus units only)
  , detTotalBytes :: Int
  , detPolicyBytes :: Int -- ^ rendered bytes of the @(policy …)@ subtree
  , detPayloadBytes :: Int -- ^ total − policy (the distribution-bearing size)
  }
  deriving (Eq, Show)

-- | Compute the deterministic metrics for one input from its file bytes.
computeDeterministic :: InputMeta -> String -> Deterministic
computeDeterministic im bytes = case decodeCheckInputFile bytes of
  Left (WireError ctx msg) ->
    let rendered = ctx ++ ": " ++ msg
        classMatch = case imExpected im of
          -- codec row: the decode must fail AND carry the operator's pinned
          -- diagnostic (any-failure is not enough — the deletion-sensitivity pin
          -- carries into the metric).
          ExpectCodecReject -> not (null (imHsDiag im)) && imHsDiag im `isInfixOf` rendered
          _ -> False -- a verdict row that fails to decode is a mismatch
     in base {detActual = "codec-fail", detClassMatch = classMatch}
  Right input ->
    let (verdict, located) = runCheckLocated input
        outcome = verdictOutcome verdict
        loc = lrConstituent <$> located
     in base
          { detActual = actualText outcome
          , detClassMatch = classMatches (imExpected im) outcome
          , detLocation = loc
          , detLocationMatch = case imExpected im of
              -- single-defect rejects localize at the mutated constituent by
              -- construction; a deviation is an honest diagnostic-ordering data
              -- point, not a generation failure (measured, never gated).
              ExpectClass _ -> Just (loc == imExpectedLocation im)
              _ -> Nothing
          , detReplayOk = case imKind im of
              CorpusRow -> Just (replayStable input verdict)
              MutantRow -> Nothing
          }
  where
    total = length bytes
    policy = policyBytes bytes
    base =
      Deterministic
        { detActual = "-"
        , detClassMatch = False
        , detLocation = Nothing
        , detLocationMatch = Nothing
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
  ExpectAllContested -> allContested outcome
  ExpectPrimaryStatus s -> primaryStatus outcome == Just s

-- | The actual outcome in manifest spelling (for the report's @actual@ column).
actualText :: Outcome -> String
actualText outcome = case outcome of
  Reject r -> "reject-" ++ rejectionText r
  Accept _ _ statuses
    | allContested outcome -> "accept-all-contested"
    | [(_, st)] <- statuses -> "accept-" ++ statusText st
    | otherwise -> "accept-other"

rejectionText :: Rejection -> String
rejectionText r = case r of
  RejectClass c -> show (c :: RejectClass)
  other -> show other

allContested :: Outcome -> Bool
allContested outcome = case outcome of
  Accept labels _ statuses ->
    not (null labels)
      && all ((== LUndec) . snd) labels
      && not (null statuses)
      && all ((== Contested) . snd) statuses
  _ -> False

primaryStatus :: Outcome -> Maybe Status
primaryStatus outcome = case outcome of
  Accept _ _ [(_, st)] -> Just st
  _ -> Nothing

-- | #36: the verdict carries the input's replay identity, and re-checking is
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
-- rate, replay-success rate, cross-driver agreement rate, byte-size
-- distributions over total + payload, and checking-time distributions over
-- @hs_check@ + @lean_wall@ (the two are different protocols — not comparable).
aggregateJson :: [Record] -> JValue
aggregateJson records =
  JObject
    [ ("count", JNumber (length records))
    , ("class-match-rate", rateJson [detClassMatch (recDet r) | r <- records])
    , ("class-accuracy", JObject [(cls, classRate cls) | cls <- classes])
    , ( "location-accuracy-rate"
      , rateJson [b | r <- records, Just b <- [detLocationMatch (recDet r)]]
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
