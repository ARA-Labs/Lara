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
import Lara.Driver (runCheck)
import Lara.Mutate
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
  , rowFamily :: String
  , rowExpected :: Expected
  , rowHsDiag :: String
  }
  deriving (Eq, Show)

readManifest :: IO [Row]
readManifest = do
  raw <- readFile (suiteRoot ++ "/MANIFEST.tsv")
  pure (mapMaybe parseRow (lines raw))
  where
    parseRow line = case splitTab line of
      [path, _base, family, _op, expected, hsDiag, _leanDiag]
        | not ("#" `isPrefix` path) ->
            (\e -> Row path family e hsDiag) <$> parseExpected expected
      _ -> Nothing
    isPrefix p s = take (length p) s == p
    splitTab s = case break (== '\t') s of
      (field, '\t' : rest) -> field : splitTab rest
      (field, "") -> [field]
      (field, _) -> [field]

parseExpected :: String -> Maybe Expected
parseExpected s = lookup s table
  where
    table =
      ("codec-reject", ExpectCodecReject)
        : ("accept-all-contested", ExpectAllContested)
        : [ (expectedText (ExpectClass c), ExpectClass c)
          | c <- [minBound .. maxBound]
          ]

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
  let mutants = derived ++ cycleMutants
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

nubOrd :: Ord a => [a] -> [a]
nubOrd = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

mutationSpecProps :: [(String, IO Result)]
mutationSpecProps =
  [ ("mutation suite: every mutant produces its specified outcome", quickCheckResult prop_specifiedOutcomes)
  , ("mutation suite: seeded regeneration reproduces committed bytes", quickCheckResult prop_seededReproducibility)
  , ("mutation suite: every rejection class, codec negatives, and cycles witnessed", quickCheckResult prop_mutationCoverage)
  ]
