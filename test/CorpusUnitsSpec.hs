-- | Golden discipline for the T2 corpus units (M5 tracker #48).
--
-- The corpus-unit suite lowers the frozen 60-claim M0 sample
-- (@m0\/sample.tsv@, seed-42 stratified draw) into @.lara@ units under
-- @corpus-units\/@, one per claim, all checked against the shared
-- @corpus-v1.policy.lara@ (conventions: @corpus-units\/LOWERING.md@). These
-- properties pin the suite the same way 'WorkedExamplesSpec' pins the worked
-- examples, plus the manifest discipline the mutant suite established
-- (PR #49): discovery is manifest-driven and the manifest, the sample, and
-- the filesystem must agree exactly.
--
--   * __manifest ↔ sample__: the manifest's @(group, artifact, claim_id,
--     claim_type, double_annotate)@ rows are exactly the 60 sample rows —
--     the corpus cannot silently shrink, grow, or drift from the frozen draw.
--   * __manifest ↔ filesystem__: every listed unit directory exists with a
--     @unit.lara@, and no unlisted unit directory is committed.
--   * __freshness__: re-deriving every @unit.core.sexp@ and @expected.json@
--     from its committed @unit.lara@ + the shared policy reproduces the
--     committed bytes (the anchors never drift from their surface sources).
--   * __expected status__: the manifest's @expected_status@ column equals the
--     status the checker actually computes for the unit's single queried
--     claim — the per-unit golden-oracle comment is cross-checked by
--     construction, never a matter of prose.
--   * __status distribution__: the @expected_status@ counts are exactly 9
--     justified / 48 gap / 3 defeated — the corpus's headline status mix and
--     the legal status value set are pinned as data, so a lowering rewrite
--     that regenerates anchors and the manifest column together cannot
--     silently shift the mix.
--   * __stratum coverage__: the by-type counts equal the adjudicated M0
--     stratum quotas (the T5 freeze anchor for the sample composition).
module CorpusUnitsSpec (corpusUnitsSpecProps) where

import Test.QuickCheck

import Data.List (group, sort)
import System.Directory (doesFileExist, listDirectory)

import Lara.Admission (renderAdmissionAudit, renderAdmissionRejection)
import Lara.Elaborate
  ( PreparedSource (..)
  , defeasibleSuiteSigma
  , prepareSource
  , renderSourceInvalid
  , runSourceCheck
  , sourceResultCheckInput
  )
import Lara.ExpectedJson (JValue (..), expectedJson, expectedJsonValue)
import Lara.Replay (CheckInput)
import Lara.Syntax (parsePolicy, parseProgram)
import Lara.Wire (encodeCheckInput, printSExpr)

-- ---------------------------------------------------------------------------
-- Manifest and sample loading
-- ---------------------------------------------------------------------------

manifestPath :: FilePath
manifestPath = "corpus-units/MANIFEST.tsv"

samplePath :: FilePath
samplePath = "m0/sample.tsv"

policyPath :: FilePath
policyPath = "corpus-units/corpus-v1.policy.lara"

-- | @(group, artifact, claim_id, claim_type, double_annotate, expected_status)@.
type ManifestRow = (String, String, String, String, String, String)

splitTabs :: String -> [String]
splitTabs s = case break (== '\t') s of
  (fld, []) -> [fld]
  (fld, _ : rest) -> fld : splitTabs rest

readManifest :: IO [ManifestRow]
readManifest = do
  raw <- readFile manifestPath
  traverse toRow [ln | ln <- drop 1 (lines raw), not (null ln)]
  where
    toRow ln = case splitTabs ln of
      [g, a, c, t, d, s] -> pure (g, a, c, t, d, s)
      _ -> fail (manifestPath ++ ": malformed row: " ++ ln)

-- | The sample's @(group, artifact, claim_id, claim_type, double_annotate)@
-- columns (the trailing @title@ column is display-only).
readSampleKeys :: IO [(String, String, String, String, String)]
readSampleKeys = do
  raw <- readFile samplePath
  pure
    [ (g, a, c, t, d)
    | ln <- drop 1 (lines raw)
    , not (null ln)
    , (g : a : c : t : d : _) <- [splitTabs ln]
    ]

unitDir :: ManifestRow -> FilePath
unitDir (_, artifact, claimId, _, _, _) = "corpus-units/" ++ artifact ++ "/" ++ claimId

-- ---------------------------------------------------------------------------
-- Shared derivation (the exact gen-corpus-units.hs derivation chain —
-- @app/Main.hs@ runs the same functions but resolves a policy co-located
-- with the artifact, so the CLI cannot be pointed at a unit directly: the
-- shared policy lives at @corpus-units/corpus-v1.policy.lara@)
-- ---------------------------------------------------------------------------

deriveInput :: FilePath -> IO (Either String CheckInput)
deriveInput dir = do
  policyText <- readFile policyPath
  progText <- readFile (dir ++ "/unit.lara")
  pure $ case (parseProgram progText, parsePolicy policyText) of
    (Right prog, Right pol) ->
      case prepareSource defeasibleSuiteSigma prog pol of
        Left invalid -> Left (dir ++ ": source invalid: " ++ renderSourceInvalid invalid)
        Right (SourceRejected rejection) ->
          Left (dir ++ ": admission rejection: " ++ renderAdmissionRejection rejection)
        Right (SourceAccepted input) ->
          case sourceResultCheckInput (runSourceCheck input) of
            Left audit ->
              Left
                ( dir
                    ++ ": legacy core artifacts cannot encode source admission: "
                    ++ renderAdmissionAudit audit
                )
            Right legacyInput -> Right legacyInput
    (pr, pp) -> Left (dir ++ ": parse failed: " ++ show pr ++ " / " ++ show pp)

-- ---------------------------------------------------------------------------
-- Properties
-- ---------------------------------------------------------------------------

-- | The manifest rows are exactly the frozen sample rows (set equality on the
-- five shared columns; the manifest adds only @expected_status@).
prop_corpusManifestMatchesSample :: Property
prop_corpusManifestMatchesSample = once $ ioProperty $ do
  manifest <- readManifest
  sample <- readSampleKeys
  let manifestKeys = sort [(g, a, c, t, d) | (g, a, c, t, d, _) <- manifest]
  pure $
    counterexample
      "corpus-units/MANIFEST.tsv rows must be exactly the m0/sample.tsv rows"
      (manifestKeys === sort sample)

-- | Every listed unit exists on disk, and no unlisted unit directory is
-- committed (the mutant-suite manifest discipline).
prop_corpusManifestMatchesFilesystem :: Property
prop_corpusManifestMatchesFilesystem = once $ ioProperty $ do
  manifest <- readManifest
  listed <- mapM (\r -> (,) (unitDir r) <$> doesFileExist (unitDir r ++ "/unit.lara")) manifest
  artifacts <- filter (`notElem` nonUnitEntries) <$> listDirectory "corpus-units"
  onDisk <-
    concat
      <$> mapM
        (\a -> map (("corpus-units/" ++ a ++ "/") ++) <$> listDirectory ("corpus-units/" ++ a))
        artifacts
  contents <- mapM (\(d, ok) -> if ok then (,) d . sort <$> listDirectory d else pure (d, [])) listed
  let missing = [d | (d, ok) <- listed, not ok]
      strays = sort onDisk `minus` sort (map unitDir manifest)
      strayFiles = [(d, fs `minus` unitFiles) | (d, fs) <- contents, not (null (fs `minus` unitFiles))]
  pure $
    counterexample ("units listed in the manifest but missing on disk: " ++ show missing) (null missing)
      .&&. counterexample ("unit directories on disk but not in the manifest: " ++ show strays) (null strays)
      .&&. counterexample
        ("files inside unit directories beyond the three committed anchors: " ++ show strayFiles)
        (null strayFiles)
  where
    nonUnitEntries = ["MANIFEST.tsv", "corpus-v1.policy.lara", "LOWERING.md"]
    unitFiles = ["expected.json", "unit.core.sexp", "unit.lara"]
    minus xs ys = [x | x <- xs, x `notElem` ys]

-- | Re-deriving every committed @unit.core.sexp@ and @expected.json@ from its
-- @unit.lara@ + shared policy reproduces the committed bytes.
prop_corpusUnitsFresh :: Property
prop_corpusUnitsFresh = once $ ioProperty $ do
  manifest <- readManifest
  checks <- mapM checkOne manifest
  pure $ counterexample "corpus manifest parsed to zero rows" (not (null manifest)) .&&. conjoin checks
  where
    checkOne row = do
      let dir = unitDir row
      derived <- deriveInput dir
      case derived of
        Left err -> pure (counterexample err False)
        Right input -> do
          committedCore <- readFile (dir ++ "/unit.core.sexp")
          committedJson <- readFile (dir ++ "/expected.json")
          pure $
            counterexample
              (dir ++ ": unit.core.sexp is stale — regenerate with scripts/gen-corpus-units.hs")
              ((printSExpr (encodeCheckInput input) ++ "\n") === committedCore)
              .&&. counterexample
                (dir ++ ": expected.json is stale — regenerate with scripts/gen-corpus-units.hs")
                (expectedJson input === committedJson)

-- | The manifest's @expected_status@ equals the computed status of the unit's
-- single queried claim, and every unit is an accept-verdict unit.
prop_corpusExpectedStatus :: Property
prop_corpusExpectedStatus = once $ ioProperty $ do
  manifest <- readManifest
  checks <- mapM checkOne manifest
  pure $ counterexample "corpus manifest parsed to zero rows" (not (null manifest)) .&&. conjoin checks
  where
    checkOne row@(_, _, _, _, _, expected) = do
      let dir = unitDir row
      derived <- deriveInput dir
      pure $ case derived of
        Left err -> counterexample err False
        Right input -> case computedStatuses (expectedJsonValue input) of
          Just [status] ->
            counterexample
              (dir ++ ": manifest expected_status " ++ show expected ++ " /= computed " ++ show status)
              (status === expected)
          other ->
            counterexample
              (dir ++ ": expected exactly one accept-verdict claim status, got " ++ show other)
              False
    computedStatuses v = do
      JObject top <- Just v
      JString "accept" <- lookup "verdict-class" top
      JObject diag <- lookup "located-diagnostic" top
      JArray sts <- lookup "statuses" diag
      mapM (\s -> do JObject o <- Just s; JString st <- lookup "status" o; pure st) sts

-- | The headline status distribution (9 justified / 48 gap / 3 defeated) is
-- pinned as data: grouping the manifest's @expected_status@ column must
-- reproduce it exactly, so a lowering rewrite that regenerates anchors and
-- the manifest column together cannot silently shift the corpus's status
-- mix. Grouping over the sorted statuses also pins the legal status value
-- set — any other value lands in the grouped counts and fails.
prop_corpusStatusDistribution :: Property
prop_corpusStatusDistribution = once $ ioProperty $ do
  manifest <- readManifest
  let got = [(s, length g) | g@(s : _) <- group (sort [st | (_, _, _, _, _, st) <- manifest])]
  pure $
    counterexample
      "corpus status distribution drifted (or an illegal status value appeared)"
      (got === expected)
  where
    expected = [("defeated", 3), ("gap", 48), ("justified", 9)]

-- | The by-type counts equal the adjudicated M0 stratum quotas
-- (m0/README.md §"Annotation pass": post-adjudication counts, sample not
-- redrawn) — the frozen composition the T5 freeze will seal.
prop_corpusStratumCoverage :: Property
prop_corpusStratumCoverage = once $ ioProperty $ do
  manifest <- readManifest
  let count ty = length [() | (_, _, _, t, _, _) <- manifest, t == ty]
      got = map (\ty -> (ty, count ty)) (map fst quotas)
  pure $ counterexample "corpus stratum counts drifted from the frozen M0 sample" (got === quotas)
  where
    quotas =
      [ ("comparative", 17)
      , ("causal", 13)
      , ("descriptive", 9)
      , ("negative-result", 9)
      , ("implementation-behavioral", 7)
      , ("generalization", 5)
      ]

-- ---------------------------------------------------------------------------
-- Registry
-- ---------------------------------------------------------------------------

corpusUnitsSpecProps :: [(String, IO Result)]
corpusUnitsSpecProps =
  [ ("corpus-unit manifest rows are exactly the frozen m0/sample.tsv rows", quickCheckResult prop_corpusManifestMatchesSample)
  , ("corpus-unit manifest and committed unit directories agree exactly", quickCheckResult prop_corpusManifestMatchesFilesystem)
  , ("corpus-unit anchors and goldens are fresh (re-derive == committed)", quickCheckResult prop_corpusUnitsFresh)
  , ("corpus-unit manifest expected_status equals the computed claim status", quickCheckResult prop_corpusExpectedStatus)
  , ("corpus-unit status distribution is exactly 9 justified / 48 gap / 3 defeated", quickCheckResult prop_corpusStatusDistribution)
  , ("corpus-unit stratum counts equal the adjudicated M0 quotas", quickCheckResult prop_corpusStratumCoverage)
  ]
