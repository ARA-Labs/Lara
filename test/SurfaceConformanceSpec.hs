-- | Executable Task-8 surface-conformance assertions.
--
-- A production change that drops/reorders a manifest case, accepts a named
-- structural negative, collapses either alpha pair, or stops exercising one of
-- the five M5 constructor families makes a property below fail.  Expected rows
-- are literal manifest/golden bytes; no emitter helper computes its own oracle.
module SurfaceConformanceSpec (surfaceConformanceSpecProps) where

import Data.List (find, isInfixOf)
import qualified Data.ByteString.Char8 as BC
import Control.Exception (bracket)
import Control.Monad (forM_)
import System.Directory (findExecutable, getTemporaryDirectory, removeFile)
import System.Environment (getEnvironment)
import System.Exit (ExitCode (..))
import System.FilePath (takeFileName)
import System.IO (hClose, openBinaryTempFile)
import System.IO.Unsafe (unsafePerformIO)
import System.Process (CreateProcess (..), proc, readCreateProcessWithExitCode,
  readProcessWithExitCode)
import Test.QuickCheck

import Lara.AST
import Lara.Syntax (parsePolicy, parseProgram)

data Row = Row
  { rowCase :: String
  , rowAst :: String
  , rowOutcome :: String
  , rowCore :: String
  , rowObligations :: String
  , rowAttacks :: String
  , rowObservations :: String
  }
  deriving (Eq, Show)

orderedCases :: [String]
orderedCases =
  [ "all-forms-accept"
  , "rule-alpha-left"
  , "rule-alpha-right"
  , "nd-alpha-left"
  , "nd-alpha-right"
  , "comparison-accept"
  , "cell-interpolation-accept"
  , "named-cert-premise-accept"
  , "named-formula-accept"
  , "capture-reject"
  , "ambiguous-premise-reject"
  , "comparison-polarity-reject"
  , "attack-path-reject"
  , "conclusion-mismatch-reject"
  , "challenge-target-reject"
  , "unknown-status-reject"
  , "duplicate-group-id-reject"
  , "group-repeated-member-reject"
  , "group-too-few-members-reject"
  , "group-member-undeclared-reject"
  , "admission-prune-accept"
  , "observation-gap"
  , "observation-defeated"
  , "observation-contested"
  , "observation-no-extension"
  ]

observationRows :: [(String, String, String)]
observationRows =
  [ ("observation-gap", "-",
      "grounded:claim-main:gap,complete:claim-main:gap,preferred:claim-main:gap,"
        ++ "stable:claim-main:gap,semi-stable:claim-main:gap")
  , ("observation-defeated", "rebut:arg-con:arg-pro",
      "grounded:claim-main:defeated,complete:claim-main:defeated,"
        ++ "preferred:claim-main:defeated,stable:claim-main:defeated,"
        ++ "semi-stable:claim-main:defeated")
  , ("observation-contested", "rebut:arg-pro:arg-con,rebut:arg-con:arg-pro",
      "grounded:claim-main:contested,complete:claim-main:contested,"
        ++ "preferred:claim-main:contested,stable:claim-main:contested,"
        ++ "semi-stable:claim-main:contested")
  , ("observation-no-extension", "rebut:arg-pro:arg-pro",
      "grounded:claim-main:contested,complete:claim-main:contested,"
        ++ "preferred:claim-main:contested,stable:claim-main:noExtension,"
        ++ "semi-stable:claim-main:contested")
  ]

negativeOutcomes :: [(String, String)]
negativeOutcomes =
  [ ("capture-reject", "reject:cert-binder-captures-premise")
  , ("ambiguous-premise-reject", "reject:ambiguous-premise")
  , ("comparison-polarity-reject", "reject:comparison-polarity")
  , ("attack-path-reject", "reject:attack-path")
  , ("conclusion-mismatch-reject", "reject:conclusion-mismatch")
  , ("challenge-target-reject", "reject:challenge-target")
  , ("unknown-status-reject", "reject:unknown-status")
  , ("duplicate-group-id-reject", "reject:duplicate-group-id")
  , ("group-repeated-member-reject", "reject:group-repeated-member")
  , ("group-too-few-members-reject", "reject:group-too-few-members")
  , ("group-member-undeclared-reject", "reject:group-member-undeclared")
  ]

splitTabs :: String -> [String]
splitTabs [] = [""]
splitTabs text =
  let (cell, rest) = break (== '\t') text
   in cell : case rest of
        [] -> []
        _ : suffix -> splitTabs suffix

parseRows :: String -> Either String [Row]
parseRows bytes = case lines bytes of
  [] -> Left "empty table"
  header : records
    | header /= "case_id\tast_fingerprint\toutcome\tcore_fingerprint\tobligations\tattacks\tobservations" ->
        Left ("bad header: " ++ header)
    | otherwise -> traverse parseRow records
  where
    parseRow line = case splitTabs line of
      [caseId, ast, outcome, core, obligations, attacks, observations] ->
        Right (Row caseId ast outcome core obligations attacks observations)
      cells -> Left ("row has " ++ show (length cells) ++ " cells: " ++ line)

loadRows :: IO (Either String [Row])
loadRows = parseRows . BC.unpack <$> BC.readFile "test/surface-conformance.golden"

rowNamed :: String -> [Row] -> Either String Row
rowNamed caseId rows = maybe (Left ("missing case " ++ caseId)) Right (find ((== caseId) . rowCase) rows)

prop_emitterMatchesGolden :: Property
prop_emitterMatchesGolden = once $ ioProperty $ do
  executable <- findExecutable "surface-conformance"
  case executable of
    Nothing -> pure (counterexample "surface-conformance executable is not registered" False)
    Just path -> do
      (code, stdoutText, stderrText) <-
        readProcessWithExitCode path ["--manifest", "fixtures/surface/MANIFEST.tsv"] ""
      golden <- BC.unpack <$> BC.readFile "test/surface-conformance.golden"
      pure $ counterexample stderrText (code == ExitSuccess .&&. stdoutText === golden)

prop_utf8CodecVector :: Property
prop_utf8CodecVector = once $ ioProperty $ do
  executable <- findExecutable "surface-conformance"
  case executable of
    Nothing -> pure (counterexample "surface-conformance executable is not registered" False)
    Just path -> do
      (code, stdoutText, stderrText) <-
        readProcessWithExitCode path ["--codec-vector", "é"] ""
      let expected =
            "utf8=c3a9\tlength=2\tframed=s2:é\tpercent=%c3%a9\t"
              ++ "fingerprint=c6dcf16454f9f0ca\n"
      pure $ counterexample stderrText (code == ExitSuccess .&&. stdoutText === expected)

prop_localeCEmitter :: Property
prop_localeCEmitter = once $ ioProperty $ do
  executable <- findExecutable "surface-conformance"
  case executable of
    Nothing -> pure (counterexample "surface-conformance executable is not registered" False)
    Just path -> do
      inherited <- getEnvironment
      let localeC = ("LC_ALL", "C") : ("LANG", "C") :
            filter (\entry -> fst entry `notElem` ["LC_ALL", "LANG"]) inherited
      (code, stdoutText, stderrText) <- readCreateProcessWithExitCode
        (proc path ["--manifest", "fixtures/surface/MANIFEST.tsv"]){env = Just localeC} ""
      golden <- BC.unpack <$> BC.readFile "test/surface-conformance.golden"
      pure $ counterexample stderrText (code == ExitSuccess .&&. stdoutText === golden)

withTempFiles :: [String] -> ([FilePath] -> IO a) -> IO a
withTempFiles names action = do
  directory <- getTemporaryDirectory
  bracket
    (mapM (\name -> do
      (path, handle) <- openBinaryTempFile directory name
      hClose handle
      pure path) names)
    (\paths -> forM_ paths (\path -> removeFile path))
    action

prop_invalidUtf8Rejected :: Property
prop_invalidUtf8Rejected = once $ ioProperty $ do
  executable <- findExecutable "surface-conformance"
  case executable of
    Nothing -> pure (counterexample "surface-conformance executable is not registered" False)
    Just path -> withTempFiles
      ["lara-surface-invalid-program.lara", "lara-surface-policy.lara",
       "lara-surface-manifest.tsv"] $ \paths -> case paths of
        [programPath, policyPath, manifestPath] -> do
          BC.writeFile programPath (BC.pack "\xff")
          BC.readFile "fixtures/surface/surface.policy.lara" >>= BC.writeFile policyPath
          let allFeatures =
                "labelled-premise,named-discharge,comparison,value-interpolation,"
                  ++ "cell-interpolation,named-cert-premise,named-formula,rule-binder,"
                  ++ "nd-binder,surface-attacks,capture-rejection,"
                  ++ "ambiguous-premise-rejection,comparison-polarity-rejection,"
                  ++ "attack-path-rejection,conclusion-mismatch-rejection,"
                  ++ "challenge-target-rejection,unknown-status-rejection,"
                  ++ "duplicate-group-id-rejection,group-repeated-member-rejection,"
                  ++ "group-too-few-members-rejection,"
                  ++ "group-member-undeclared-rejection,admission-prune,open-obligation"
              manifest = unlines
                [ "case_id\tprogram\tpolicy\texpected\tfeatures"
                , "utf8-invalid\t" ++ takeFileName programPath ++ "\t"
                    ++ takeFileName policyPath ++ "\taccept\t" ++ allFeatures ]
          BC.writeFile manifestPath (BC.pack manifest)
          (code, _, stderrText) <-
            readProcessWithExitCode path ["--manifest", manifestPath] ""
          let expected = "surface conformance: utf8-invalid: program file invalid UTF-8: "
                ++ programPath ++ "\n"
          pure $ counterexample stderrText
            (code == ExitFailure 1 .&&. stderrText === expected)
        _ -> pure (counterexample "temporary file allocation shape" False)

prop_goldenCasesExact :: Property
prop_goldenCasesExact = once $ ioProperty $ do
  parsed <- loadRows
  pure $ case parsed of
    Left err -> counterexample err False
    Right rows -> map rowCase rows === orderedCases

prop_alphaPairs :: Property
prop_alphaPairs = once $ ioProperty $ do
  parsed <- loadRows
  pure $ case parsed of
    Left err -> counterexample err False
    Right rows -> conjoin (map (checkPair rows) pairs)
  where
    pairs = [("rule-alpha-left", "rule-alpha-right"), ("nd-alpha-left", "nd-alpha-right")]
    checkPair rows (leftName, rightName) = case (rowNamed leftName rows, rowNamed rightName rows) of
      (Right left, Right right) ->
        counterexample (show (left, right)) $
          rowAst left =/= rowAst right .&&. rowCore left === rowCore right
      (Left err, _) -> counterexample err False
      (_, Left err) -> counterexample err False

prop_namedNegativeOutcomes :: Property
prop_namedNegativeOutcomes = once $ ioProperty $ do
  parsed <- loadRows
  pure $ case parsed of
    Left err -> counterexample err False
    Right rows -> conjoin
      [ case rowNamed caseId rows of
          Left err -> counterexample err False
          Right row -> rowOutcome row === expected
      | (caseId, expected) <- negativeOutcomes
      ]

prop_admissionPrunedOpenObligation :: Property
prop_admissionPrunedOpenObligation = once $ ioProperty $ do
  parsed <- loadRows
  pure $ case parsed >>= rowNamed "admission-prune-accept" of
    Left err -> counterexample err False
    Right row ->
      counterexample (show row) $
        rowObligations row === "arg-open:cq"

prop_observationBranches :: Property
prop_observationBranches = once $ ioProperty $ do
  parsed <- loadRows
  pure $ case parsed of
    Left err -> counterexample err False
    Right rows -> conjoin
      [ case rowNamed caseId rows of
          Left err -> counterexample err False
          Right row -> counterexample (show row) $
            rowAttacks row === expectedAttacks .&&.
              rowObservations row === expectedObservations
      | (caseId, expectedAttacks, expectedObservations) <- observationRows
      ]

allFormsFixture :: (String, String)
allFormsFixture = unsafePerformIO $ do
  programText <- BC.unpack <$> BC.readFile "fixtures/surface/all-forms.lara"
  policyText <- BC.unpack <$> BC.readFile "fixtures/surface/surface.policy.lara"
  pure (programText, policyText)
{-# NOINLINE allFormsFixture #-}

prop_m5ConstructorCoverage :: Property
prop_m5ConstructorCoverage = checkCoverage $
  let (programText, policyText) = allFormsFixture
   in case (parseProgram programText, parsePolicy policyText) of
    (Right program, Right policy) ->
      let declarations = programDecls program
          rules = policyRules policy
          hasLabels = any (any (/= Nothing) . rulePremiseLabels) rules
          hasNamedDischarge = any declNamedDischarge declarations
          hasComparison = any isComparison declarations
          hasInterpolation = not (null (programValueBindings program)) && any nlHasCell declarations
          hasNamedCertificate = any declHasNamedCertificate declarations
          hasSurfaceAttacks = any isSurfaceAttack declarations
       in cover 100 (hasLabels && hasNamedDischarge) "labelled premise + named discharge"
            . cover 100 hasComparison "comparison"
            . cover 100 hasInterpolation "value + cell interpolation"
            . cover 100 hasNamedCertificate "named certificate + formula"
            . cover 100 hasSurfaceAttacks "surface attacks"
            $ property True
    (Left err, _) -> counterexample (show err) False
    (_, Left err) -> counterexample (show err) False
  where
    declNamedDischarge (DeclArg Arg{argInstantiation = InferTheta _ _ discharges _ _}) = not (null discharges)
    declNamedDischarge _ = False
    isComparison (DeclComparison _) = True
    isComparison _ = False
    nlHasCell (DeclClaim Claim{claimNl = nl}) = "{cell " `isInfixOf` nl
    nlHasCell (DeclComparison Comparison{cmpClaim = ComparisonClaim{ccNlRaw = nl}}) = "{cell " `isInfixOf` nl
    nlHasCell _ = False
    declHasNamedCertificate (DeclArg Arg{argInstantiation = ExplicitTheta term}) = termHasCert term
    declHasNamedCertificate (DeclArg Arg{argInstantiation = InferTheta _ _ _ _ assurance}) = assuranceHasCert assurance
    declHasNamedCertificate _ = False
    termHasCert (SLeaf _) = False
    termHasCert (SRule _ _ premises discharges _ assurance) =
      assuranceHasCert assurance || any termHasCert premises || any (termHasCert . snd) discharges
    assuranceHasCert (AssuranceCert _) = True
    assuranceHasCert _ = False
    isSurfaceAttack (DeclAttack _) = True
    isSurfaceAttack _ = False

surfaceConformanceSpecProps :: [(String, IO Result)]
surfaceConformanceSpecProps =
  [ ("surface emitter matches the committed production-path golden", quickCheckResult prop_emitterMatchesGolden)
  , ("surface UTF-8 framing, escaping, and fingerprint vector", quickCheckResult prop_utf8CodecVector)
  , ("surface emitter is locale-independent under locale C", quickCheckResult prop_localeCEmitter)
  , ("surface emitter rejects invalid UTF-8 with stable context", quickCheckResult prop_invalidUtf8Rejected)
  , ("surface golden case IDs are exact and ordered", quickCheckResult prop_goldenCasesExact)
  , ("surface alpha pairs change AST bytes but preserve core bytes", quickCheckResult prop_alphaPairs)
  , ("surface negatives retain stable structural outcomes", quickCheckResult prop_namedNegativeOutcomes)
  , ("surface obligations report the retained admission-pruned open case",
      quickCheckResult prop_admissionPrunedOpenObligation)
  , ("surface observation branches have exact attack and semantic cells",
      quickCheckResult prop_observationBranches)
  , ("surface fixtures cover every M5 constructor family", quickCheckResult prop_m5ConstructorCoverage)
  ]
