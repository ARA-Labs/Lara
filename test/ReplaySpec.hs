module ReplaySpec (replaySpecProps) where

import Test.QuickCheck
import Data.List (sort)

import Lara.AST
import Lara.Elaborate (ElabError (..), SourceInvalid (..), prepareSource)
import Lara.Replay
import Lara.Strict (SExpr (..))
import Lara.Wire (decodeReplayId, encodeReplayId, parseSExpr, printSExpr)
import SigmaFixture (structuralSigma)

-- | A unit with nothing in it: no symbols, so the empty signature is the
-- correct one (@lara-core\@0.2@) rather than a placeholder.
emptyUnit :: Unit
emptyUnit = Unit structuralSigma [] [] [] [] [] [] [] [] [] QuarantineOnConflict

sourceProgram :: Program
sourceProgram =
  Program
    { programArtifact = "fixture"
    , programDigest = Digest "sha256:artifact-0"
    , programPolicy = PolicyId "empirical-v1"
    , programBackends = [(BackendId "nd", "1")]
    , programValueBindings = []
    , programDecls = []
    }

sourcePolicy :: Policy
sourcePolicy =
  Policy
    { policyId = PolicyId "empirical-v1"
    , policySigma = structuralSigma
    , policyRules = []
    , policyContraries = []
    , policyExceptions = []
    , policyAdmission = []
    , policyTheories =
        [ (TheoryDigest "sha256:z", [])
        , (TheoryDigest "sha256:a", [])
        ]
    , policyGroupMode = QuarantineOnConflict
    , policyMeasurands = []
    , policyComparisonSchemes = []
    }

sourceUnit :: Unit
sourceUnit = emptyUnit {unitTheories = policyTheories sourcePolicy}

mkIdentity :: [(BackendId, String)] -> [TheoryDigest] -> ReplayId
mkIdentity backends theories =
  case mkReplayId LaraCoreV02 (PolicyId "empirical-v1") backends theories (Digest "sha256:artifact-0") of
    Right replayId -> replayId
    Left err -> error (replayErrorMessage err)

certRule :: BackendId -> Int -> [SupportTerm] -> [(QuestionId, SupportTerm)] -> SupportTerm
certRule backend version premises discharges =
  SRule
    (RuleId "strict")
    []
    premises
    discharges
    []
    (AssuranceCert (Cert backend version (TheoryDigest "sha256:a") (SAtom "proof")))

plainRule :: [SupportTerm] -> [(QuestionId, SupportTerm)] -> SupportTerm
plainRule premises discharges =
  SRule (RuleId "outer-rule") [] premises discharges [] AssuranceNone

rawInputFor :: Program -> Policy -> Unit -> Either ReplayError CheckInput
rawInputFor program policy unit = do
  replayId <-
    mkReplayId
      LaraCoreV02
      (policyId policy)
      (programBackends program)
      (sort (map fst (policyTheories policy)))
      (programDigest program)
  mkCheckInput replayId unit

prop_sourceConstruction :: Property
prop_sourceConstruction =
  fmap
    (\i ->
      ( replayCore (inputReplayId i)
      , replayPolicy (inputReplayId i)
      , replayBackends (inputReplayId i)
      , replayTheories (inputReplayId i)
      , replayArtifact (inputReplayId i)
      ))
    (rawInputFor sourceProgram sourcePolicy sourceUnit)
    === Right
      ( LaraCoreV02
      , PolicyId "empirical-v1"
      , [(BackendId "nd", "1")]
      , [TheoryDigest "sha256:a", TheoryDigest "sha256:z"]
      , Digest "sha256:artifact-0"
      )

prop_checkInputPreservesUnitTheoryTable :: Property
prop_checkInputPreservesUnitTheoryTable =
  fmap inputUnit (rawInputFor sourceProgram sourcePolicy sourceUnit) === Right sourceUnit

prop_replayConstructionRequiresCanonicalTheories :: Property
prop_replayConstructionRequiresCanonicalTheories =
  conjoin
    [ mkReplayId LaraCoreV02 (PolicyId "p") [] [z, a] artifact
        === Left (NonCanonicalTheoryDigests [z, a])
    , mkReplayId LaraCoreV02 (PolicyId "p") [] [a, a] artifact
        === Left (NonCanonicalTheoryDigests [a, a])
    ]
  where
    a = TheoryDigest "sha256:a"
    z = TheoryDigest "sha256:z"
    artifact = Digest "sha256:artifact"

prop_sourcePolicyMismatch :: Property
prop_sourcePolicyMismatch =
  case prepareSource sourceProgram mismatched of
    Left (SourceElaborationError (PolicyIdMismatch expected actual)) ->
      (expected, actual) === (PolicyId "empirical-v1", PolicyId "other-v1")
    result -> counterexample ("expected source policy mismatch, got " ++ showResult result) False
  where
    mismatched = sourcePolicy {policyId = PolicyId "other-v1"}
    showResult (Left invalid) = show invalid
    showResult (Right _) = "prepared source"

prop_duplicateUnitTheoryRejected :: Property
prop_duplicateUnitTheoryRejected =
  mkCheckInput replayId duplicateUnit
    === Left (DuplicateUnitTheory a)
  where
    a = TheoryDigest "sha256:a"
    replayId = mkIdentity [] [a]
    duplicateUnit = emptyUnit {unitTheories = [(a, []), (a, [])]}

prop_unitTheoryIdentityMustMatchReplay :: Property
prop_unitTheoryIdentityMustMatchReplay =
  mkCheckInput replayId mismatchedUnit
    === Left (TheoryIdentityMismatch [a, z] [a])
  where
    a = TheoryDigest "sha256:a"
    z = TheoryDigest "sha256:z"
    replayId = mkIdentity [] [a, z]
    mismatchedUnit = emptyUnit {unitTheories = [(a, [])]}

prop_theoriesUseUnicodeScalarOrder :: Property
prop_theoriesUseUnicodeScalarOrder =
  conjoin
    [ fmap (replayTheories . inputReplayId) sourceResult === Right [bmp, supplementary]
    , mkReplayId LaraCoreV02 (PolicyId "p") [] [supplementary, bmp] artifact
        === Left (NonCanonicalTheoryDigests [supplementary, bmp])
    ]
  where
    bmp = TheoryDigest "\xE000"
    supplementary = TheoryDigest "\x10000"
    artifact = Digest "sha256:unicode-order"
    policy = sourcePolicy {policyTheories = [(supplementary, []), (bmp, [])]}
    unit = emptyUnit {unitTheories = policyTheories policy}
    sourceResult = rawInputFor sourceProgram policy unit

-- | Wire-level quoted-atom golden (PR #44 review C11): a replay-id whose
-- theories section carries QUOTED non-ASCII digests in canonical Unicode
-- code-point order (@é@ is U+00E9, @λ@ is U+03BB, both outside the bare-atom
-- set, and @sha256:é@ sorts before @sha256:λ@). The canonical text must
-- decode, re-encode to the exact original bytes, and the reversed-order
-- variant must be rejected as non-canonical.
prop_quotedNonAsciiTheoriesWireGolden :: Property
prop_quotedNonAsciiTheoriesWireGolden =
  conjoin
    [ counterexample "quoted non-ASCII theories decode" $
        decoded === Right expectedReplayId
    , counterexample "re-encoding reproduces the exact bytes" $
        fmap (printSExpr . encodeReplayId) decoded === Right canonicalText
    , counterexample "reversed order is rejected" $
        isLeft reversedDecoded === True
    ]
  where
    canonicalText =
      "(replay-id (core lara-core@0.2) (policy empirical-v1) "
        ++ "(backends (backend nd 1)) "
        ++ "(theories \"sha256:é\" \"sha256:λ\") "
        ++ "(artifact sha256:artifact-0))"
    reversedText =
      "(replay-id (core lara-core@0.2) (policy empirical-v1) "
        ++ "(backends (backend nd 1)) "
        ++ "(theories \"sha256:λ\" \"sha256:é\") "
        ++ "(artifact sha256:artifact-0))"
    expectedReplayId = mkIdentity [(BackendId "nd", "1")] [eAcute, lambda]
    eAcute = TheoryDigest "sha256:é"
    lambda = TheoryDigest "sha256:λ"
    decoded = decodeText canonicalText
    reversedDecoded = decodeText reversedText
    decodeText text = case parseSExpr text of
      Left err -> Left (show err)
      Right value -> either (Left . show) Right (decodeReplayId value)
    isLeft (Left _) = True
    isLeft _ = False

prop_runtimeAcceptsSupportedSelection :: Property
prop_runtimeAcceptsSupportedSelection =
  runtimeReplayFailure input === Nothing
  where
    term = certRule (BackendId "nd") 1 [] []
    unit = emptyUnit {unitArgs = [(ArgId "a", term)]}
    input = either (error . replayErrorMessage) id (mkCheckInput (mkIdentity [(BackendId "nd", "1")] []) unit)

prop_duplicateSelectionPrecedesOtherFailures :: Property
prop_duplicateSelectionPrecedesOtherFailures =
  runtimeReplayFailure input
    === Just (DuplicateSelectedBackend (BackendId "nd") "1")
  where
    selections =
      [ (BackendId "unknown", "9")
      , (BackendId "nd", "1")
      , (BackendId "nd", "1")
      ]
    term = certRule (BackendId "missing") 3 [] []
    unit = emptyUnit {unitArgs = [(ArgId "a", term)]}
    input = either (error . replayErrorMessage) id (mkCheckInput (mkIdentity selections []) unit)

prop_unknownSelectionPrecedesUnselectedCertificate :: Property
prop_unknownSelectionPrecedesUnselectedCertificate =
  runtimeReplayFailure input
    === Just (UnknownSelectedBackend (BackendId "nd") "2")
  where
    selections = [(BackendId "nd", "1"), (BackendId "nd", "2")]
    term = certRule (BackendId "missing") 3 [] []
    unit = emptyUnit {unitArgs = [(ArgId "a", term)]}
    input = either (error . replayErrorMessage) id (mkCheckInput (mkIdentity selections []) unit)

prop_nestedPremiseCertificateReportsOuterArgument :: Property
prop_nestedPremiseCertificateReportsOuterArgument =
  runtimeReplayFailure input
    === Just (CertificateBackendNotSelected 0 (ArgId "outer") (BackendId "nd") 1)
  where
    nestedCertificate = certRule (BackendId "nd") 1 [] []
    outer = plainRule [nestedCertificate] []
    unit = emptyUnit {unitArgs = [(ArgId "outer", outer)]}
    input = either (error . replayErrorMessage) id (mkCheckInput (mkIdentity [] []) unit)

prop_certificateTraversalIsDepthFirst :: Property
prop_certificateTraversalIsDepthFirst =
  conjoin
    [ runtimeReplayFailure (inputFor [(ArgId "outer", assuranceFirst)])
        === missing (BackendId "assurance") 1
    , runtimeReplayFailure (inputFor [(ArgId "outer", premisesBeforeDischarges)])
        === missing (BackendId "deep") 2
    , runtimeReplayFailure (inputFor [(ArgId "first", dischargeOrder), (ArgId "second", secondArgument)])
        === Just (CertificateBackendNotSelected 0 (ArgId "first") (BackendId "first-discharge") 4)
    ]
  where
    missing backend version =
      Just (CertificateBackendNotSelected 0 (ArgId "outer") backend version)
    assuranceFirst =
      SRule
        (RuleId "outer-rule")
        []
        [certRule (BackendId "premise") 2 [] []]
        []
        []
        (AssuranceCert (Cert (BackendId "assurance") 1 (TheoryDigest "sha256:a") (SAtom "proof")))
    premisesBeforeDischarges =
      plainRule
        [plainRule [] [(QuestionId "nested", certRule (BackendId "deep") 2 [] [])], certRule (BackendId "sibling") 3 [] []]
        [(QuestionId "outer", certRule (BackendId "discharge") 4 [] [])]
    dischargeOrder =
      plainRule
        []
        [ (QuestionId "first", certRule (BackendId "first-discharge") 4 [] [])
        , (QuestionId "second", certRule (BackendId "second-discharge") 5 [] [])
        ]
    secondArgument = certRule (BackendId "second-argument") 6 [] []
    inputFor args =
      either (error . replayErrorMessage) id $
        mkCheckInput (mkIdentity [] []) (emptyUnit {unitArgs = args})

replaySpecProps :: [(String, IO Result)]
replaySpecProps =
  [ ("replay source construction freezes identity", quickCheckResult prop_sourceConstruction)
  , ("replay input preserves the Unit theory table", quickCheckResult prop_checkInputPreservesUnitTheoryTable)
  , ("replay construction requires canonical theory digests", quickCheckResult prop_replayConstructionRequiresCanonicalTheories)
  , ("replay source construction rejects policy mismatch", quickCheckResult prop_sourcePolicyMismatch)
  , ("replay input rejects duplicate Unit theory", quickCheckResult prop_duplicateUnitTheoryRejected)
  , ("replay input rejects theory identity mismatch", quickCheckResult prop_unitTheoryIdentityMustMatchReplay)
  , ("replay theory order is Unicode-scalar lexicographic", quickCheckResult prop_theoriesUseUnicodeScalarOrder)
  , ("replay wire golden: quoted non-ASCII theories in code-point order", quickCheckResult prop_quotedNonAsciiTheoriesWireGolden)
  , ("replay preflight accepts supported selection", quickCheckResult prop_runtimeAcceptsSupportedSelection)
  , ("replay preflight duplicate selection has first precedence", quickCheckResult prop_duplicateSelectionPrecedesOtherFailures)
  , ("replay preflight unknown selection precedes certificate", quickCheckResult prop_unknownSelectionPrecedesUnselectedCertificate)
  , ("replay preflight locates nested premise certificate", quickCheckResult prop_nestedPremiseCertificateReportsOuterArgument)
  , ("replay preflight certificate traversal is depth-first", quickCheckResult prop_certificateTraversalIsDepthFirst)
  ]
