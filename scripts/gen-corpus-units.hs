-- | Corpus-unit @.core.sexp@ generator (T2).
--
-- For each row of @corpus-units/MANIFEST.tsv@, reads the committed
-- @corpus-units/<artifact>/<claim_id>/unit.lara@ and the shared
-- @corpus-units/corpus-v1.policy.lara@, parses both with "Lara.Syntax", lowers
-- the pair to a 'CheckInput' with the trusted surface elaborator and validated
-- source replay metadata, and writes the unit's canonical check-input envelope
-- (@unit.core.sexp@) and its @expected.json@ golden. This is the exact
-- derivation chain @app\/Main.hs@ runs — but note the CLI resolves a policy
-- co-located with the artifact, so it cannot be pointed at a unit directly:
-- the shared policy lives two levels up at @corpus-units/corpus-v1.policy.lara@,
-- hardcoded here. The output shape is the exact one
-- @scripts/gen-worked-examples.hs@ pins for the worked examples.
--
-- Discovery is manifest-driven, never by globbing (the mutant-suite rule):
-- the manifest and the committed unit directories must agree exactly.
-- @test/CorpusUnitsSpec.hs@ pins freshness (re-deriving each committed
-- @unit.core.sexp@\/@expected.json@ reproduces the bytes), manifest ↔
-- @m0/sample.tsv@ agreement, and expected-status agreement; the differential
-- harness runs every anchor through both drivers.
--
-- Run with the built library on the path:
--
-- >  cabal exec -- runghc --ghc-arg=-package --ghc-arg=lara scripts/gen-corpus-units.hs
--
-- (the package flag keeps the lara library visible regardless of which
-- component cabal last built)
module Main (main) where

import Data.List (isPrefixOf)
import Lara.Admission (renderAdmissionAudit, renderAdmissionRejection)
import Lara.Elaborate
  ( PreparedSource (..)
  , prepareSource
  , renderSourceInvalid
  , runSourceCheck
  , sourceResultCheckInput
  )
import Lara.ExpectedJson (expectedJson)
import Lara.Replay (CheckInput)
import Lara.Syntax (parsePolicy, parseProgram)
import Lara.Wire (encodeCheckInput, printSExpr)
import System.FilePath ((</>))

manifestPath :: FilePath
manifestPath = "corpus-units/MANIFEST.tsv"

policyPath :: FilePath
policyPath = "corpus-units/corpus-v1.policy.lara"

-- | A manifest row: (group, artifact, claim id). The remaining columns
-- (claim_type, double_annotate, expected_status) are consumed by
-- @test/CorpusUnitsSpec.hs@, not by generation — but a row must still carry
-- exactly those six fields, so a malformed line fails here with the
-- offending text instead of being silently truncated.
type Row = (String, String, String)

main :: IO ()
main = do
  rows <- readManifest
  policyText <- readFile policyPath
  policy <- either (fail . ((policyPath ++ ": parse: ") ++) . show) pure (parsePolicy policyText)
  mapM_ (genUnit policy) rows
  putStrLn ("generated " ++ show (length rows) ++ " corpus units")
  where
    genUnit policy (_, artifact, claimId) = do
      let dir = "corpus-units" </> artifact </> claimId
          unitPath = dir </> "unit.lara"
          corePath = dir </> "unit.core.sexp"
          expectedPath = dir </> "expected.json"
      progText <- readFile unitPath
      prog <- either (fail . ((unitPath ++ ": parse: ") ++) . show) pure (parseProgram progText)
      input <- case prepareSource prog policy of
        Left invalid -> fail (unitPath ++ ": source invalid: " ++ renderSourceInvalid invalid)
        Right (SourceRejected rejection) ->
          fail (unitPath ++ ": admission rejection: " ++ renderAdmissionRejection rejection)
        Right (SourceAccepted source) ->
          case sourceResultCheckInput (runSourceCheck source) of
            Left audit ->
              fail
                ( unitPath
                    ++ ": legacy core artifacts cannot encode source admission: "
                    ++ renderAdmissionAudit audit
                )
            Right input -> pure input
      writeCore corePath input
      writeFile expectedPath (expectedJson input)
      putStrLn ("wrote " ++ expectedPath)

readManifest :: IO [Row]
readManifest = do
  raw <- readFile manifestPath
  case lines raw of
    [] -> fail (manifestPath ++ ": empty manifest")
    (header : body)
      | not ("group\tartifact\tclaim_id" `isPrefixOf` header) ->
          fail (manifestPath ++ ": unexpected header: " ++ header)
      | null body -> fail (manifestPath ++ ": no rows")
      | otherwise -> traverse toRow body
  where
    toRow ln = case splitTabs ln of
      [g, a, c, _, _, _] -> pure (g, a, c)
      _ -> fail (manifestPath ++ ": malformed row: " ++ ln)

splitTabs :: String -> [String]
splitTabs s = case break (== '\t') s of
  (fld, []) -> [fld]
  (fld, _ : rest) -> fld : splitTabs rest

writeCore :: FilePath -> CheckInput -> IO ()
writeCore corePath input = do
  writeFile corePath (printSExpr (encodeCheckInput input) ++ "\n")
  putStrLn ("wrote " ++ corePath)
