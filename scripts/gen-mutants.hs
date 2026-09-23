-- | Seeded mutation-suite generator (T1).
--
-- Reads the accept-verdict worked-example anchors @examples\/<NAME>\/example.core.sexp@,
-- derives every mutant the @Lara.Mutate.*@ generators propose for them
-- ("Lara.Mutate.Suite" and "Lara.Mutate.Codec" per base, plus the constructed
-- "Lara.Mutate.Cycle" and "Lara.Mutate.Accept" families), __verifies each
-- mutant against the production
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
-- >  cabal exec -- runghc scripts/gen-mutants.hs            -- write the suite
-- >  cabal exec -- runghc scripts/gen-mutants.hs --check    -- assert it is fresh
--
-- @--check@ regenerates to a scratch tree and diffs it against the committed
-- one, exiting non-zero on any difference. CI runs it beside
-- @scripts/differential.sh@, so a generated artifact can no longer drift from
-- its generator unnoticed — the failure that shipped a stale
-- @fixtures\/mutants\/README.md@.
module Main (main) where

import Control.Monad (forM, forM_, unless, when)
import Data.List (isInfixOf, sort, (\\))
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import System.Directory
  ( createDirectoryIfMissing
  , doesDirectoryExist
  , listDirectory
  , removeDirectoryRecursive
  )
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import System.FilePath ((</>))
import System.IO (hPutStrLn, stderr)

import Lara.AST (Label (..), Rejection (..), Status (..))
import Lara.Driver (runCheck)
import Lara.Mutate
  ( Expected (..)
  , Mutant (..)
  , codecDiagnostics
  , expectedText
  , familyText
  , mutationBases
  , mutationSeed
  , opFamily
  , opName
  )
import Lara.Mutate.Accept (acceptMutants, acceptStructureOk)
import Lara.Mutate.Codec (codecMutantsForBase)
import Lara.Mutate.Cycle (cycleMutants)
import Lara.Mutate.Manifest (manifestFor, mutantPath)
import Lara.Mutate.Suite
  ( corpusBudget
  , corpusMutants
  , corpusSweepReport
  , mutantsForBase
  )
import Lara.Replay (CheckInput)
import Lara.Wire
  ( Outcome (..)
  , PublicStatus (..)
  , Verdict (..)
  , WireError (..)
  , decodeCheckInputFile
  , isPublished
  )

suiteRoot :: FilePath
suiteRoot = "fixtures/mutants"

-- | Where @--check@ regenerates before diffing. Under @dist-newstyle@ (already
-- ignored) rather than the system temp dir, so a crashed run leaves the
-- evidence beside the build tree and never inside the committed suite.
checkRoot :: FilePath
checkRoot = "dist-newstyle" </> "gen-mutants-check"

main :: IO ()
main = do
  -- Pin UTF-8 rather than inheriting the locale: the README carries @≥@ and
  -- @§@, so a C-locale run would fail to write it (and @--check@ would fail to
  -- read the committed copy) for reasons unrelated to the suite. Byte-neutral
  -- wherever the locale was already UTF-8.
  setLocaleEncoding utf8
  args <- getArgs
  case args of
    [] -> do
      n <- generate suiteRoot
      putStrLn ("wrote " ++ show n ++ " verified mutants to " ++ suiteRoot)
    ["--check"] -> check
    _ -> do
      prog <- getProgName
      hPutStrLn stderr ("usage: " ++ prog ++ " [--check]")
      exitFailure

-- | Regenerate the whole suite into @root@; returns the mutant count. Every
-- mutant is verified against the production checker before anything is
-- written, so an unmet specification aborts before the tree is touched.
generate :: FilePath -> IO Int
generate root = do
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
  stale <- doesDirectoryExist root
  when stale (removeDirectoryRecursive root)
  createDirectoryIfMissing True (root </> "malformed")
  forM_ mutants $ \m -> writeFile (root </> mutantPath m) (mutantBytes m)
  writeFile (root </> "MANIFEST.tsv") (manifestFor mutants)
  writeFile (root </> "README.md") (readmeFor corpusBases mutants)
  pure (length mutants)

-- | @--check@: regenerate into a scratch tree and assert the
-- committed suite is byte-identical to it, naming every file that is missing,
-- unexpected, or differing.
--
-- This covers what @test\/MutationSpec.hs@ structurally cannot.
-- @prop_seededReproducibility@ re-derives the mutant bytes and @MANIFEST.tsv@
-- from the library, but @README.md@ is rendered by 'readmeFor' /in this
-- script/, so no test can import it — which is why it shipped stale.
-- Comparing whole trees additionally catches a file the generator has stopped
-- emitting, which no per-file property ever sees.
check :: IO ()
check = do
  n <- generate checkRoot
  expected <- treeFiles checkRoot
  actual <- treeFiles suiteRoot
  differing <- forM (filter (`elem` actual) expected) $ \rel -> do
    fresh <- readStrict (checkRoot </> rel)
    committed <- readStrict (suiteRoot </> rel)
    pure (if fresh == committed then Nothing else Just rel)
  let problems =
        [ ("missing from " ++ suiteRoot, expected \\ actual)
        , ("not emitted by the generator", actual \\ expected)
        , ("differing from the generator's output", [rel | Just rel <- differing])
        ]
  removeDirectoryRecursive checkRoot
  if all (null . snd) problems
    then
      putStrLn
        ("OK: " ++ suiteRoot ++ " matches its generator (" ++ show n ++ " mutants)")
    else do
      forM_ problems $ \(label, files) ->
        unless (null files) $ do
          hPutStrLn stderr ("FAIL: " ++ show (length files) ++ " file(s) " ++ label ++ ":")
          forM_ files $ \rel -> hPutStrLn stderr ("  " ++ rel)
      hPutStrLn stderr ""
      hPutStrLn stderr "Regenerate with: cabal exec -- runghc scripts/gen-mutants.hs"
      exitFailure

-- | Every regular file under @root@, relative to it, sorted.
treeFiles :: FilePath -> IO [FilePath]
treeFiles root = sort <$> go ""
  where
    go rel = do
      entries <- listDirectory (root </> rel)
      fmap concat $ forM entries $ \entry -> do
        let child = if null rel then entry else rel </> entry
        isDir <- doesDirectoryExist (root </> child)
        if isDir then go child else pure [child]

-- | 'readFile' is lazy, and a mismatch found early leaves its handle open —
-- with ~570 files per side that exhausts the handle limit precisely on the
-- failing runs this check exists to report. Force the contents instead.
readStrict :: FilePath -> IO String
readStrict path = do
  contents <- readFile path
  length contents `seq` pure contents

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
         | (family, n) <- tally (familyText . opFamily . mutantOp)
         ]
      ++ [ ""
         , "## Corpus sweep (uniform derived-applicability, B = "
            ++ show corpusBudget
            ++ ")"
         , ""
         , "Per rejection operator over the corpus units: how many bases carry ≥1"
         , "site (applicable) and how many were selected (all when ≤ B, else B"
         , "picked by the operator-keyed stream). Two operators find no corpus"
         , "site and are recorded as 0/0: `drop-covering-attack` (only three"
         , "corpus units declare an attack at all, and none of those attacks"
         , "covers a contrary pair, so deleting one leaves the completeness scan"
         , "with nothing to report) and `twin-support-defect` (no corpus unit"
         , "carries wrong-premise sites at two distinct arguments)."
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
  ExpectIncompleteArgument -> withDecoded $ \verdict ->
    case verdictOutcome verdict of
      Reject IncompleteArgument -> pure ()
      outcome ->
        bad ("expected reject " ++ show IncompleteArgument ++ ", got " ++ describe outcome)
  ExpectMissingConflict -> withDecoded $ \verdict ->
    case verdictOutcome verdict of
      Reject MissingConflict -> pure ()
      outcome ->
        bad ("expected reject " ++ show MissingConflict ++ ", got " ++ describe outcome)
  ExpectAllContested -> withDecoded $ \verdict ->
    case verdictOutcome verdict of
      Accept labels _ statuses
        | all (isPublished . snd) statuses
            && not (null labels)
            && all ((== LUndec) . snd) labels
            && not (null statuses)
            && all ((== Published Contested) . snd) statuses ->
            pure ()
      outcome -> bad ("expected all-undec/all-contested accept, got " ++ describe outcome)
  ExpectEvidenceBlocked -> withInputVerdict $ \input verdict ->
    if acceptStructureOk (mutantOp m) ExpectEvidenceBlocked input verdict
      then pure ()
      else
        bad
          ( "accept-family structural check failed: expected an accept whose "
              ++ "queried claim is evidence-blocked with conditional status "
              ++ "justified (spec §4.3), got "
              ++ describe (verdictOutcome verdict)
          )
  ExpectPrimaryStatus status -> withInputVerdict $ \input verdict ->
    if acceptStructureOk (mutantOp m) (ExpectPrimaryStatus status) input verdict
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
