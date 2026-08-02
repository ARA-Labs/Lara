-- | The seeded mutation suite (M5 tracker #48, T1) as a standing test.
--
-- Three properties hold the committed @fixtures\/mutants\/@ suite:
--
--   * __specified outcomes__: every manifest row's mutant produces exactly its
--     specified outcome through the production pipeline — the pinned rejection
--     class via 'Lara.Driver.runCheck', an all-@undec@\/@contested@ accept for
--     the cycle family, or — for the @malformed\/@ negative half — a
--     codec-boundary decode failure carrying the operator's pinned diagnostic
--     substring (manifest column @hs-diagnostic@, from 'codecDiagnostics'):
--     any-failure would let a deleted codec check stay green via a different
--     downstream check.
--   * __seeded reproducibility__: re-deriving the whole suite from the
--     committed worked-example anchors with "Lara.Mutate" (same
--     'mutationSeed') reproduces the committed files and manifest
--     byte-for-byte. A drifted base anchor, seed, or operator fails here —
--     regenerate with @scripts\/gen-mutants.hs@.
--   * __coverage__: every executable rejection class
--     (R1\/R3\/R4\/R5\/R6\/R7\/R9\/R10\/R11\/R12\/R13) is exercised by at
--     least one generated mutant, plus the codec negatives and the
--     specified-status cycle family — the rejection-class half of the T1
--     exit criterion (tracker #48), measured from the manifest rather than
--     asserted in prose. The other half — generators over T2 corpus units,
--     and generated mutants exercising every status\/attack kind — stays
--     open until the corpus units exist.
--
-- The Lean half of the obligation (byte-identical verdicts) is
-- @scripts/differential.sh@, which walks @fixtures\/mutants\/*.sexp@ as
-- positive anchors and @fixtures\/mutants\/malformed\/*.sexp@ as negative
-- anchors through both drivers.
module MutationSpec (mutationSpecProps) where

import Test.QuickCheck

import Data.List (isInfixOf, sort)
import Data.Maybe (mapMaybe)

import Lara.AST (Label (..), RejectClass (..), Rejection (..), Status (..))
import Lara.Diagnostics (LocatedRejection (..), constituentText, parseConstituent)
import Lara.Driver (runCheck, runCheckLocated)
import Lara.Mutate
import Lara.Mutate.Accept (acceptMutants, acceptStructureOk)
import Lara.Replay (CheckInput)
import Lara.Wire (Outcome (..), Verdict (..), WireError (..), decodeCheckInputFile)

suiteRoot :: FilePath
suiteRoot = "fixtures/mutants"

-- | One parsed manifest row: path relative to the suite root, family,
-- expected outcome, and — for codec rows — the pinned Haskell diagnostic
-- substring (empty otherwise). 'prop_seededReproducibility' ties the
-- diagnostic column back to 'codecDiagnostics', so asserting the column here
-- asserts the one table.
data Row = Row
  { rowPath :: FilePath
  , rowBase :: String
  , rowFamily :: String
  , rowOp :: String
  , rowExpected :: Expected
  , rowHsDiag :: String
  , rowSite :: String -- ^ raw @expected-location@ column (column 8)
  }
  deriving (Eq, Show)

readManifest :: IO [Row]
readManifest = do
  raw <- readFile (suiteRoot ++ "/MANIFEST.tsv")
  pure (mapMaybe parseRow (lines raw))
  where
    parseRow line = case splitTab line of
      [path, base, family, op, expected, hsDiag, _leanDiag, site]
        | not ("#" `isPrefix` path) ->
            (\e -> Row path base family op e hsDiag site) <$> parseExpected expected
      _ -> Nothing
    isPrefix p s = take (length p) s == p

splitTab :: String -> [String]
splitTab s = case break (== '\t') s of
  (field, '\t' : rest) -> field : splitTab rest
  (field, "") -> [field]
  (field, _) -> [field]

-- | The corpus units as mutation bases, in @corpus-units/MANIFEST.tsv@ order,
-- each labelled @\<artifact\>.\<claim_id\>@ and decoded from its committed
-- @unit.core.sexp@ (the exact list @scripts/gen-mutants.hs@ passes to
-- 'corpusMutants', so the re-derived suite matches byte-for-byte).
readCorpusBases :: IO [(String, CheckInput)]
readCorpusBases = do
  raw <- readFile "corpus-units/MANIFEST.tsv"
  let rows =
        [ (artifact, claimId)
        | ln <- drop 1 (lines raw)
        , not (null ln)
        , (_group : artifact : claimId : _) <- [splitTab ln]
        ]
  concat
    <$> mapM
      ( \(artifact, claimId) -> do
          let anchor = "corpus-units/" ++ artifact ++ "/" ++ claimId ++ "/unit.core.sexp"
          bytes <- readFile anchor
          case decodeCheckInputFile bytes of
            -- Fail loudly (as scripts/gen-mutants.hs does) rather than dropping the
            -- base, so a broken anchor surfaces here and not as a misleading
            -- "manifest is stale" mismatch from a silently-shortened base list.
            Left err -> fail (anchor ++ ": decode: " ++ show err)
            Right input -> pure [(artifact ++ "." ++ claimId, input)]
      )
      rows

-- | The outcome a mutant file actually produces, in manifest spelling.
actualOutcome :: String -> String
actualOutcome bytes = case decodeCheckInputFile bytes of
  Left _ -> expectedText ExpectCodecReject
  Right input -> case verdictOutcome (runCheck input) of
    Reject (RejectClass c) -> expectedText (ExpectClass c)
    Reject other -> "reject-" ++ show other
    Accept labels _ statuses
      | not (null labels)
          && all ((== LUndec) . snd) labels
          && not (null statuses)
          && all ((== Contested) . snd) statuses ->
          expectedText ExpectAllContested
      | otherwise -> "accept-other"

-- | Every manifest row's mutant produces exactly its specified outcome. A
-- codec row must additionally fail with its operator's pinned diagnostic —
-- the check the operator targets, not just any decode failure.
prop_specifiedOutcomes :: Property
prop_specifiedOutcomes = once $ ioProperty $ do
  rows <- readManifest
  checks <- mapM checkRow rows
  pure $
    conjoin
      ( counterexample "mutant manifest is empty" (not (null rows))
          : checks
      )
  where
    checkRow row = do
      bytes <- readFile (suiteRoot ++ "/" ++ rowPath row)
      pure $ counterexample (rowPath row) $ case rowExpected row of
        ExpectCodecReject -> checkCodec row bytes
        -- An accept-family mutant's verdict can look all-undec/all-contested
        -- (a 2-cycle has both args undec), so check the single queried claim's
        -- status directly rather than through 'actualOutcome'.
        ExpectPrimaryStatus s -> primaryStatus bytes === Just s
        _ -> actualOutcome bytes === expectedText (rowExpected row)
    checkCodec row bytes = case decodeCheckInputFile bytes of
      Right _ ->
        counterexample "decoded cleanly instead of failing at the codec boundary" False
      Left (WireError ctx msg) ->
        let rendered = ctx ++ ": " ++ msg
         in conjoin
              [ counterexample
                  "manifest hs-diagnostic column is empty for a codec row"
                  (not (null (rowHsDiag row)))
              , counterexample
                  ( "failed the wrong codec check: expected a diagnostic containing "
                      ++ show (rowHsDiag row)
                      ++ ", got "
                      ++ show rendered
                  )
                  (rowHsDiag row `isInfixOf` rendered)
              ]

-- | Re-deriving the suite from the committed anchors reproduces the committed
-- files and manifest exactly (the seeded-reproducibility guard).
prop_seededReproducibility :: Property
prop_seededReproducibility = once $ ioProperty $ do
  derived <- concat <$> mapM deriveBase mutationBases
  corpusBases <- readCorpusBases
  let mutants =
        derived
          ++ cycleMutants
          ++ corpusMutants corpusBases
          ++ acceptMutants corpusBases
  committedManifest <- readFile (suiteRoot ++ "/MANIFEST.tsv")
  fileChecks <- mapM checkFile mutants
  pure $
    conjoin
      ( counterexample
          "MANIFEST.tsv is stale — regenerate with scripts/gen-mutants.hs"
          (manifestFor mutants === committedManifest)
          : fileChecks
      )
  where
    deriveBase base = do
      let anchor = "examples/" ++ base ++ "/example.core.sexp"
      bytes <- readFile anchor
      pure $ case decodeCheckInputFile bytes of
        Left _ -> []
        Right input -> mutantsForBase base input ++ codecMutantsForBase base bytes
    checkFile m = do
      committed <- readFile (suiteRoot ++ "/" ++ mutantPath m)
      pure $
        counterexample
          (mutantPath m ++ " is stale — regenerate with scripts/gen-mutants.hs")
          (mutantBytes m === committed)

-- | The rejection-class half of the T1 exit criterion, measured from the
-- manifest: every executable rejection class, the codec negatives, and the
-- cycle family are witnessed. The status\/attack-kind half of the criterion
-- needs T2 corpus units and is not asserted here.
prop_mutationCoverage :: Property
prop_mutationCoverage = once $ ioProperty $ do
  rows <- readManifest
  let witnessed = sort (nubOrd (map rowExpected rows))
      families = sort (nubOrd (map rowFamily rows))
      wanted =
        ExpectCodecReject
          : ExpectAllContested
          : map ExpectClass [minBound .. maxBound]
  pure $
    conjoin
      [ counterexample
          ("outcome coverage incomplete — witnessed " ++ show (map expectedText witnessed))
          (all (`elem` witnessed) wanted)
      , counterexample
          ("family coverage incomplete — witnessed " ++ show families)
          ( all
              (`elem` families)
              [ "wrong-formulas"
              , "undeclared-leaves"
              , "hidden-policy-extension"
              , "bad-attack-targets"
              , "open-obligations"
              , "cycles"
              , "codec-corruption"
              , "certificate-tampering"
              , "data-integrity"
              ]
          )
      ]

-- | The located driver's contract, over every verdict-bearing mutant (the codec
-- rows do not decode): (1) the iron invariant @runCheck ≡ fst . runCheckLocated@
-- — a future-proofing guard should @runCheck@ ever be re-derived independently;
-- and (2) the non-definitional pairing — a @Reject@ verdict pairs with a
-- 'Just' located rejection whose class equals the verdict's, and an @Accept@
-- pairs with 'Nothing'. The T3 harness (@test\/MeasureSpec.hs@) will extend the
-- iron invariant over both the mutant and corpus-unit manifests.
prop_runCheckLocatedConsistent :: Property
prop_runCheckLocatedConsistent = once $ ioProperty $ do
  rows <- readManifest
  checks <- mapM checkRow [r | r <- rows, rowExpected r /= ExpectCodecReject]
  pure $
    conjoin
      (counterexample "no verdict-bearing rows found" (not (null checks)) : checks)
  where
    checkRow row = do
      bytes <- readFile (suiteRoot ++ "/" ++ rowPath row)
      pure $ counterexample (rowPath row) $ case decodeCheckInputFile bytes of
        Left err -> counterexample ("unexpected decode failure: " ++ show err) (property False)
        Right input ->
          let (verdict, located) = runCheckLocated input
           in conjoin
                [ counterexample "fst . runCheckLocated /= runCheck" (verdict === runCheck input)
                , counterexample
                    ("located-rejection contract violated: " ++ show (verdictOutcome verdict, located))
                    (contractHolds (verdictOutcome verdict) located)
                ]
    contractHolds outcome located = case (outcome, located) of
      (Reject rej, Just lr) -> lrRejection lr == rej
      (Accept{}, Nothing) -> True
      _ -> False

-- | The @expected-location@ column (column 8) is present exactly on the
-- verdict-bearing single-site (rejection) rows and round-trips through the one
-- 'constituentText'\/'parseConstituent' table; the codec and cycle rows carry
-- @-@ (no single seeded site).
prop_expectedLocationColumn :: Property
prop_expectedLocationColumn = once $ ioProperty $ do
  rows <- readManifest
  pure $
    conjoin
      ( counterexample "mutant manifest is empty" (not (null rows))
          : [ counterexample
                (rowPath row ++ ": expected-location " ++ show (rowSite row))
                (wellFormed row)
            | row <- rows
            ]
      )
  where
    wellFormed row = case rowExpected row of
      ExpectClass _ -> rowSite row /= "-" && roundTrips (rowSite row)
      _ -> rowSite row == "-"
    roundTrips s = maybe False ((== s) . constituentText) (parseConstituent s)

-- | The corpus half of the T1 coverage criterion (tracker #48): every
-- executable rejection class is witnessed by ≥1 corpus-based mutant. All eleven
-- 'RejectClass' values have corpus sites, so all eleven are required (the "where
-- corpus sites exist" hedge is vacuous for this corpus).
prop_corpusCoverage :: Property
prop_corpusCoverage = once $ ioProperty $ do
  rows <- readManifest
  corpusBases <- readCorpusBases
  let corpusLabels = map fst corpusBases
      corpusRows = [r | r <- rows, rowBase r `elem` corpusLabels]
      witnessed = sort (nubOrd [c | Row {rowExpected = ExpectClass c} <- corpusRows])
  pure $
    conjoin
      [ counterexample "no corpus-based mutant rows found" (not (null corpusRows))
      , counterexample
          ("corpus rejection-class coverage incomplete — witnessed " ++ show witnessed)
          (all (`elem` witnessed) [minBound .. maxBound :: RejectClass])
      ]

-- | The corpus sweep budget is honoured with no silent caps: per operator, the
-- selected-base count equals @min(applicable, B = 12)@, and the manifest carries
-- exactly that many corpus rows for the operator. The regenerated README prints
-- the same 'corpusSweepReport', so this ties the manifest, the report, and the
-- budget rule together.
prop_corpusBudget :: Property
prop_corpusBudget = once $ ioProperty $ do
  rows <- readManifest
  corpusBases <- readCorpusBases
  let corpusLabels = map fst corpusBases
      corpusRows = [r | r <- rows, rowBase r `elem` corpusLabels]
      rowsForOp name = length [() | r <- corpusRows, rowOp r == name]
      report = corpusSweepReport corpusBases
  pure $
    conjoin
      [ counterexample
          ( opName op
              ++ ": selected "
              ++ show selected
              ++ " /= min(applicable="
              ++ show applicable
              ++ ", "
              ++ show corpusBudget
              ++ ")"
          )
          (selected === min applicable corpusBudget)
        .&&. counterexample
          ( opName op
              ++ ": manifest has "
              ++ show (rowsForOp (opName op))
              ++ " corpus rows, sweep selected "
              ++ show selected
          )
          (rowsForOp (opName op) === selected)
      | (op, applicable, selected) <- report
      ]

-- | The status of a single-query accept mutant's queried claim (the accept
-- family always constructs single-query units); 'Nothing' on a reject, a codec
-- failure, or a non-single-query accept.
primaryStatus :: String -> Maybe Status
primaryStatus bytes = case decodeCheckInputFile bytes of
  Right input -> case verdictOutcome (runCheck input) of
    Accept _ _ [(_, st)] -> Just st
    _ -> Nothing
  Left _ -> Nothing

-- | The status/attack-kind half of the T1 exit criterion (tracker #48): the
-- accept family witnesses every claim status {gap, justified, contested,
-- defeated} and every attack kind {rebut, undercut, undermine} over corpus
-- units. Statuses are read from the @accept-\<status\>@ rows; attack kinds are
-- implied by the accept operator (undercut for attach-undercut/attach-reinstate,
-- undermine for attach-undermine, rebut for attach-rebut-cycle).
prop_statusAttackCoverage :: Property
prop_statusAttackCoverage = once $ ioProperty $ do
  rows <- readManifest
  corpusBases <- readCorpusBases
  let corpusLabels = map fst corpusBases
      corpusRows = [r | r <- rows, rowBase r `elem` corpusLabels]
      statuses = nubOrd [s | Row {rowExpected = ExpectPrimaryStatus s} <- corpusRows]
      attackKinds = nubOrd (concatMap (opAttackKinds . rowOp) corpusRows)
  pure $
    conjoin
      [ counterexample
          ("corpus status coverage incomplete — witnessed " ++ show statuses)
          (all (`elem` statuses) [Gap, Justified, Contested, Defeated])
      , counterexample
          ("corpus attack-kind coverage incomplete — witnessed " ++ show attackKinds)
          (all (`elem` attackKinds) ["rebut", "undercut", "undermine"])
      ]
  where
    opAttackKinds op = case op of
      "attach-undercut" -> ["undercut"]
      "attach-reinstate" -> ["undercut"]
      "attach-undermine" -> ["undermine"]
      "attach-rebut-cycle" -> ["rebut"]
      _ -> []

-- | The 4A structural re-verification (eng review D7): re-deriving the accept
-- family, every mutant satisfies 'acceptStructureOk' — the verdict accepts with
-- the specified primary status AND the operator's constructed label shape (a
-- status-only check passes a no-op reinstate vacuously). This runs the same
-- structural predicate @scripts/gen-mutants.hs@ gates generation on.
prop_acceptStructure :: Property
prop_acceptStructure = once $ ioProperty $ do
  corpusBases <- readCorpusBases
  let mutants = acceptMutants corpusBases
  pure $
    conjoin
      ( counterexample "no accept-family mutants derived" (not (null mutants))
          : [counterexample (mutantName m) (checkOne m) | m <- mutants]
      )
  where
    checkOne m = case (mutantExpected m, decodeCheckInputFile (mutantBytes m)) of
      (ExpectPrimaryStatus s, Right input) ->
        property (acceptStructureOk (mutantOp m) s input (runCheck input))
      (_, Left err) ->
        counterexample ("failed to decode: " ++ show err) (property False)
      _ -> counterexample "not an accept-family mutant" (property False)

nubOrd :: Ord a => [a] -> [a]
nubOrd = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

mutationSpecProps :: [(String, IO Result)]
mutationSpecProps =
  [ ("mutation suite: every mutant produces its specified outcome", quickCheckResult prop_specifiedOutcomes)
  , ("mutation suite: seeded regeneration reproduces committed bytes", quickCheckResult prop_seededReproducibility)
  , ("mutation suite: every rejection class, codec negatives, and cycles witnessed", quickCheckResult prop_mutationCoverage)
  , ("mutation suite: every rejection class witnessed by a corpus-based mutant", quickCheckResult prop_corpusCoverage)
  , ("mutation suite: corpus sweep budget honoured with no silent caps", quickCheckResult prop_corpusBudget)
  , ("mutation suite: every status and attack kind witnessed by a corpus mutant", quickCheckResult prop_statusAttackCoverage)
  , ("mutation suite: accept family verified structurally (status + label shape)", quickCheckResult prop_acceptStructure)
  , ("mutation suite: runCheck == fst . runCheckLocated over every mutant", quickCheckResult prop_runCheckLocatedConsistent)
  , ("mutation suite: expected-location column round-trips and is present on reject rows", quickCheckResult prop_expectedLocationColumn)
  ]
