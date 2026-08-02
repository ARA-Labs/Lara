-- | Seeded mutation-suite generator (M5 tracker #48, T1).
--
-- Reads the accept-verdict worked-example anchors @examples\/<NAME>\/example.core.sexp@,
-- derives every mutant "Lara.Mutate" proposes for them (plus the constructed
-- rebut-cycle family), __verifies each mutant against the production
-- checker__ — a rejection mutant must produce exactly its specified class
-- through 'Lara.Driver.runCheck', a cycle mutant must accept with all-@undec@
-- labels and all-@contested@ statuses, and a codec mutant must fail
-- 'Lara.Wire.decodeCheckInputFile' with its operator's pinned diagnostic
-- ('codecDiagnostics' — any-failure would let a deleted codec check stay
-- green via a different downstream check) — and only then writes the suite:
--
-- >  fixtures/mutants/<BASE>--<operator>-<k>.sexp   (verdict anchors)
-- >  fixtures/mutants/cycle-rebut-<n>.sexp          (specified-status anchors)
-- >  fixtures/mutants/malformed/<BASE>--codec-*.sexp (negative half, exit 2)
-- >  fixtures/mutants/MANIFEST.tsv                  (file, base, family, operator,
-- >                                                  expected, hs-diagnostic, lean-diagnostic,
-- >                                                  expected-location)
--
-- A mutant whose actual outcome differs from its specification aborts
-- generation: the committed suite is verified-by-construction on the Haskell
-- side. @test/MutationSpec.hs@ re-verifies it on every @cabal test@ run (plus
-- seeded-reproducibility freshness), and @scripts/differential.sh@ holds every
-- file byte-identical across the Haskell and Lean drivers.
--
-- Run with the built library on the path:
--
-- >  cabal exec -- runghc scripts/gen-mutants.hs
module Main (main) where

import Control.Monad (forM, forM_, when)
import Data.List (isInfixOf, sort)
import System.Directory
  ( createDirectoryIfMissing
  , doesDirectoryExist
  , removeDirectoryRecursive
  )
import System.FilePath ((</>))

import Lara.AST (Label (..), Rejection (..), Status (..))
import Lara.Driver (runCheck)
import Lara.Mutate
import Lara.Mutate.Accept (acceptMutants, acceptStructureOk)
import Lara.Replay (CheckInput)
import Lara.Wire (Outcome (..), Verdict (..), WireError (..), decodeCheckInputFile)

suiteRoot :: FilePath
suiteRoot = "fixtures/mutants"

main :: IO ()
main = do
  perBase <- forM mutationBases $ \base -> do
    let anchor = "examples" </> base </> "example.core.sexp"
    bytes <- readFile anchor
    input <- case decodeCheckInputFile bytes of
      Left err -> fail (anchor ++ ": decode: " ++ show err)
      Right input -> pure input
    pure (mutantsForBase base input ++ codecMutantsForBase base bytes)
  corpusBases <- readCorpusBases
  let mutants =
        concat perBase
          ++ cycleMutants
          ++ corpusMutants corpusBases
          ++ acceptMutants corpusBases
  forM_ mutants verify
  fresh <- doesDirectoryExist suiteRoot
  when fresh (removeDirectoryRecursive suiteRoot)
  createDirectoryIfMissing True (suiteRoot </> "malformed")
  forM_ mutants $ \m -> writeFile (suiteRoot </> mutantPath m) (mutantBytes m)
  writeFile (suiteRoot </> "MANIFEST.tsv") (manifestFor mutants)
  writeFile (suiteRoot </> "README.md") (readmeFor corpusBases mutants)
  putStrLn ("wrote " ++ show (length mutants) ++ " verified mutants to " ++ suiteRoot)

-- | The corpus units as mutation bases, in @corpus-units/MANIFEST.tsv@ order,
-- each labelled @\<artifact\>.\<claim_id\>@ and decoded from its committed
-- @unit.core.sexp@ anchor (the same discovery @test/CorpusUnitsSpec.hs@ uses;
-- never a glob). The @.@ base separator cannot collide with the @--@ operator
-- separator in a mutant filename.
readCorpusBases :: IO [(String, CheckInput)]
readCorpusBases = do
  raw <- readFile ("corpus-units" </> "MANIFEST.tsv")
  let rows =
        [ (artifact, claimId)
        | ln <- drop 1 (lines raw)
        , not (null ln)
        , (_group : artifact : claimId : _) <- [splitTabs ln]
        ]
  forM rows $ \(artifact, claimId) -> do
    let anchor = "corpus-units" </> artifact </> claimId </> "unit.core.sexp"
    bytes <- readFile anchor
    case decodeCheckInputFile bytes of
      Left err -> fail (anchor ++ ": decode: " ++ show err)
      Right input -> pure (artifact ++ "." ++ claimId, input)

splitTabs :: String -> [String]
splitTabs s = case break (== '\t') s of
  (field, []) -> [field]
  (field, _ : rest) -> field : splitTabs rest

-- | The suite README, regenerated with the suite (counts are measured, not
-- prose).
readmeFor :: [(String, CheckInput)] -> [Mutant] -> String
readmeFor corpusBases mutants =
  unlines $
    [ "# Generated mutation suite (M5 tracker #48, T1)"
    , ""
    , "GENERATED — do not edit. Regenerate with:"
    , ""
    , "    cabal exec -- runghc scripts/gen-mutants.hs"
    , ""
    , "Every file is derived from the committed worked-example anchors"
    , "(`examples/<NAME>/example.core.sexp`, bases: "
        ++ unwords mutationBases
        ++ ")"
    , "and the "
        ++ show (length corpusBases)
        ++ " committed corpus-unit anchors"
    , "(`corpus-units/<artifact>/<claim_id>/unit.core.sexp`, base label"
    , "`<artifact>.<claim_id>`), by the seeded operators of `Lara.Mutate` (seed "
        ++ show mutationSeed
        ++ "),"
    , "verified against the production checker at generation time, re-verified on"
    , "every `cabal test` run (`test/MutationSpec.hs`: specified outcomes, seeded"
    , "reproducibility, class coverage, corpus sweep budget), and held"
    , "byte-identical across the Haskell and Lean drivers by"
    , "`scripts/differential.sh` (`malformed/` is the negative half: both drivers"
    , "exit 2 with no verdict AND the per-operator stderr diagnostic pinned in the"
    , "manifest's hs-diagnostic and lean-diagnostic columns, so a deleted codec"
    , "check cannot stay green via a different downstream failure)."
    , ""
    , "Total mutants: " ++ show (length mutants)
    , ""
    , "| expected outcome | mutants |"
    , "| --- | --- |"
    ]
      ++ [ "| `" ++ outcome ++ "` | " ++ show n ++ " |"
         | (outcome, n) <- tally (expectedText . mutantExpected)
         ]
      ++ [ ""
         , "| mutation family | mutants |"
         , "| --- | --- |"
         ]
      ++ [ "| `" ++ family ++ "` | " ++ show n ++ " |"
         | (family, n) <- tally (opFamily . mutantOp)
         ]
      ++ [ ""
         , "## Corpus sweep (uniform derived-applicability, B = "
            ++ show corpusBudget
            ++ ")"
         , ""
         , "Per rejection operator over the corpus units: how many bases carry ≥1"
         , "site (applicable) and how many were selected (all when ≤ B, else B"
         , "picked by the operator-keyed stream). Cert operators find no corpus"
         , "site (corpus units carry no strict certificates), recorded as 0/0."
         , ""
         , "| corpus operator | applicable bases | selected |"
         , "| --- | --- | --- |"
         ]
      ++ [ "| `" ++ opName op ++ "` | " ++ show applicable ++ " | " ++ show selected ++ " |"
         | (op, applicable, selected) <- corpusSweepReport corpusBases
         ]
  where
    tally key =
      [ (k, length ks)
      | group@(k : _) <- groupSorted (sort (map key mutants))
      , let ks = group
      ]
    groupSorted [] = []
    groupSorted (x : xs) = (x : same) : groupSorted rest
      where
        (same, rest) = span (== x) xs

-- | Abort unless the mutant's actual outcome equals its specification. A
-- codec mutant must fail with its operator's pinned diagnostic — the check
-- the operator targets, not just any decode failure.
verify :: Mutant -> IO ()
verify m = case mutantExpected m of
  ExpectCodecReject ->
    case decodeCheckInputFile (mutantBytes m) of
      Left (WireError ctx msg) ->
        case codecDiagnostics (mutantOp m) of
          Just (hsDiag, _)
            | hsDiag `isInfixOf` (ctx ++ ": " ++ msg) -> pure ()
            | otherwise ->
                bad
                  ( "failed the wrong codec check: expected a diagnostic containing "
                      ++ show hsDiag
                      ++ ", got "
                      ++ show (ctx ++ ": " ++ msg)
                  )
          Nothing -> bad "codec-reject mutant from a non-codec operator"
      Right _ -> bad "decoded cleanly instead of failing at the codec boundary"
  ExpectClass c -> withDecoded $ \verdict ->
    case verdictOutcome verdict of
      Reject (RejectClass c') | c' == c -> pure ()
      outcome -> bad ("expected reject " ++ show c ++ ", got " ++ describe outcome)
  ExpectAllContested -> withDecoded $ \verdict ->
    case verdictOutcome verdict of
      Accept labels _ statuses
        | not (null labels)
            && all ((== LUndec) . snd) labels
            && not (null statuses)
            && all ((== Contested) . snd) statuses ->
            pure ()
      outcome -> bad ("expected all-undec/all-contested accept, got " ++ describe outcome)
  ExpectPrimaryStatus status -> withInputVerdict $ \input verdict ->
    if acceptStructureOk (mutantOp m) status input verdict
      then pure ()
      else
        bad
          ( "accept-family structural check failed: expected primary status "
              ++ show status
              ++ " and the operator's label shape, got "
              ++ describe (verdictOutcome verdict)
          )
  where
    withDecoded k = withInputVerdict (\_ verdict -> k verdict)
    withInputVerdict k = case decodeCheckInputFile (mutantBytes m) of
      Left err -> bad ("failed to decode its own bytes: " ++ show err)
      Right input -> k input (runCheck input)
    describe outcome = case outcome of
      Reject r -> "reject " ++ show r
      Accept labels _ statuses ->
        "accept labels=" ++ show labels ++ " statuses=" ++ show statuses
    bad why =
      fail
        ( "mutant "
            ++ mutantPath m
            ++ " ("
            ++ opName (mutantOp m)
            ++ " on "
            ++ mutantBase m
            ++ "): "
            ++ why
        )
