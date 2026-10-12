module InquirySpec (inquirySpecProps) where

import Data.Either (isLeft)
import Test.QuickCheck
import AuditRuntimeSpec (auditRuntimeSpecProps)
import qualified Lara.AST as A
import Lara.Attack (subterm)
import Lara.Prop (Prop (..), Pred (..), FunSym (..), Term (..))
import Lara.Sigma (declarePred, Sigma (..), SortName (..), Sort (..), ConSig (..))
import qualified Lara.Elaborate as Elaborate
import Lara.Strict (SExpr (..))
import Lara.Wire (parseSExpr, PublicStatus (..))
import qualified Lara.Process.Source.Wire as W
import qualified Lara.Process.Source as S
import qualified Lara.Process.Source.Types as T
import qualified Lara.Process.Source.Diagnostic.Wire as DW
import qualified Lara.Process.Source.Diagnostic as D
import qualified Lara.Process.Source.CoreDiagnostic as C
import qualified Lara.Process.Source.Provenance as P
import qualified Lara.Process.Audit.Types as Audit
import qualified Lara.Process.Types as Process
import qualified Lara.Process.Source.Evidence as E
import Lara.Evidence.Registry (TypedObject (..), runTypedRegistry)
import Lara.Evidence.CSV (CsvTable (..))
import Lara.Evidence.JSON (JsonValue (..))
import Lara.Evidence.Types
import qualified Lara.Evidence.Manifest as Package
import qualified Lara.Evidence.Admission as Admission
import qualified Lara.Evidence.Runner as Runner

sourceTrees :: SExpr -> [SExpr]
sourceTrees value@(SList (SAtom "checked-source" : _)) = [value]
sourceTrees (SList xs) = concatMap sourceTrees xs
sourceTrees _ = []
fragmentTrees :: SExpr -> [SExpr]
fragmentTrees value@(SList (SAtom "checked-fragment" : _)) = [value]
fragmentTrees (SList xs) = concatMap fragmentTrees xs
fragmentTrees _ = []
fixtureTree :: String -> IO (Either String SExpr)
fixtureTree name = do
  text <- readFile ("fixtures/process/inquiry/" ++ name ++ ".sexp")
  pure (either (Left . show) Right (parseSExpr text))
fixtureSources :: String -> IO (Either String [T.SourceInput])
fixtureSources name = do
  tree <- fixtureTree name
  pure $ tree >>= either (Left . show) Right . traverse W.decodeSource . sourceTrees
withSources :: String -> ([T.SourceInput] -> Property) -> Property
withSources name check = once $ ioProperty $ do
  sources <- fixtureSources name
  pure (either (\err -> counterexample err False) check sources)
withSource :: String -> Int -> (T.SourceInput -> Property) -> Property
withSource name index check = withSources name $ \sources -> case drop index sources of
  source : _ -> check source
  [] -> counterexample ("missing source " ++ name ++ " at " ++ show index) False
accepted :: T.SourceInput -> (S.AcceptedObservation -> Property) -> Property
accepted source check = case S.checkSource source of
  Left rejection -> counterexample (show rejection) False
  Right observation -> check observation
rejected :: D.SourceRejection -> T.SourceInput -> Property
rejected expected source = case S.checkSource source of
  Left actual -> actual === expected
  Right _ -> counterexample "unexpected accepted source" False
rebuild :: T.SourceInput -> A.Program -> A.Policy -> Maybe T.EvidenceCapture -> Either String T.SourceInput
rebuild old program policy capture = T.mkSourceInput program policy (T.sourceReplay old) capture
atom :: String -> Prop
atom name = Prop (Pred name) []

roundtripFixture :: String -> Property
roundtripFixture name = once $ ioProperty $ do
  parsed <- fixtureTree name
  pure $ case parsed of
    Left err -> counterexample err False
    Right tree -> conjoin
      [counterexample "missing actual source trees" (not (null (sourceTrees tree))),
       conjoin [case W.decodeSource wire of
         Left err -> counterexample (show err) False
         Right source -> conjoin [W.encodeSource source === wire,W.decodeSource (W.encodeSource source) === Right source] | wire <- sourceTrees tree],
       conjoin [case W.decodeFragment wire of
         Left err -> counterexample (show err) False
         Right fragment -> conjoin [W.encodeFragment fragment === wire,W.decodeFragment (W.encodeFragment fragment) === Right fragment] | wire <- fragmentTrees tree]]

prop_admission :: Property
prop_admission = withSource "admission-evidence-fail" 0 $
  rejected (D.SourceRejection (D.SourceDiagnostic (D.Structural (D.AdmissionRejected (A.LeafId "measured")))))
prop_replay :: Property
prop_replay = withSource "admission-evidence-fail" 0 $ \source ->
  let replay = (T.sourceReplay source){T.replayCore = T.CoreVersion "unsupported"}
  in case T.mkSourceInput (T.sourceProgram source) (T.sourcePolicy source) replay Nothing of
    Left err -> counterexample err False
    Right changed -> rejected (D.ReplayRejection (D.UnsupportedCore (T.CoreVersion "unsupported"))) changed
prop_absentCapture :: Property
prop_absentCapture = withSource "admission-evidence-fail" 0 $ \source ->
  let policy = (T.sourcePolicy source){A.policyAdmission = []}
  in case rebuild source (T.sourceProgram source) policy Nothing of
    Left err -> counterexample err False
    Right changed -> rejected (D.SourceRejection (D.EvidenceDiagnostic (T.EvidenceError T.EvidenceBindingStage (A.LeafId "measured") (Just (ObjectId "data")) "binding"))) changed

prop_blocked :: Property
prop_blocked = withSources "blocked-conditional" $ \sources -> case sources of
  before : _ : after : _ -> conjoin
    [accepted before $ \observation -> conjoin
      [S.publicStatus observation (atom "t") === EvidenceBlocked A.Defeated,
       S.blockedClosure observation [atom "t",atom "t",atom "unknown"] === [atom "t",atom "t"]],
     accepted after $ \observation -> S.publicStatus observation (atom "t") === EvidenceBlocked A.Justified]
  _ -> counterexample "missing blocked endpoints" False
prop_normalizedSupport :: Property
prop_normalizedSupport = withSource "normalized-support" 2 $ \source -> accepted source $ \observation ->
  let query = Prop (Pred "t") [TNum "+01.000"]
  in conjoin [S.observationNames observation === [A.ArgId "witness",A.ArgId "alias"],
    S.observationSupport observation query === [0,1],S.publicStatus observation query === Published A.Justified]
prop_sharedDischarge :: Property
prop_sharedDischarge = withSource "shared-discharge" 2 $ \source -> accepted source $ \observation ->
  conjoin [S.publicStatus observation (atom "t") === Published A.Defeated,
    case P.buildProvenance observation of
      Left err -> counterexample (show err) False
      Right table -> case lookup (A.ArgId "wrapper") (P.provenanceRows table) of
        Nothing -> counterexample "missing wrapper provenance" False
        Just keys -> conjoin [property (Audit.ArgumentKey (A.ArgId "discharger") `elem` keys),
          property (Audit.MethodKey (A.RuleId "r-e") `elem` keys),property (Audit.LeafKey (A.LeafId "dseed") `elem` keys)]]
prop_reindexedHole :: Property
prop_reindexedHole = withSources "reindex-hole" $ \sources -> case sources of
  _ : before : after : _ -> conjoin
    [accepted before $ \observation -> conjoin [S.observationNames observation === [],
      map (\hole -> (T.holeIndex hole,T.holeArgument hole)) (S.observationHoles observation) === [(0,A.ArgId "wrapper")],
      S.publicStatus observation (atom "t") === Published A.Gap],
     accepted after $ \observation -> conjoin [S.observationNames observation === [A.ArgId "discharger",A.ArgId "wrapper"],
      S.observationSupport observation (atom "t") === [1],S.observationHoles observation === []]]
  _ -> counterexample "missing hole endpoints" False

prop_forgedObserved :: Property
prop_forgedObserved = once $ ioProperty $ do
  parsed <- fixtureTree "forged-observed"
  pure $ case parsed of
    Left err -> counterexample err False
    Right tree -> case (traverse W.decodeSource (sourceTrees tree),traverse W.decodeFragment (fragmentTrees tree)) of
      (Right (base:_),Right (fragment:_)) -> accepted (T.appendFragment base fragment) $ \observation ->
        case P.buildProvenance observation of
          Left err -> counterexample (show err) False
          Right provenance ->
            let key = Audit.LeafKey (A.LeafId "support")
                spec = Audit.KindSpec base key Process.Observed (Just (Audit.AssumptionId 0))
                event = Process.Stamped (Process.EventId 5) (Process.Result (Process.RunId 0) 1)
                assumption = Audit.CaptureAssumption (Audit.AssumptionId 0) base key event (Process.RunId 0) Process.InstrumentedLog
                table = P.buildKindTable base provenance [event] [spec] [assumption] [Process.InstrumentedLog] [key] []
                withoutAssumption = P.buildKindTable base provenance [event] [spec] [] [Process.InstrumentedLog] [] []
                withAssumption = P.buildKindTable base provenance [event] [spec] [assumption] [Process.InstrumentedLog] [] []
            in conjoin [S.publicStatus observation (atom "t") === Published A.Justified,
              P.lookupKind table key === (Process.Hypothetical,True),
              P.lookupKind withoutAssumption key === (Process.Conditional,True),
              P.lookupKind withAssumption key === (Process.Observed,True),
              P.lookupKind table (Audit.ArgumentKey (A.ArgId "unknown-attacker")) === (Process.Hypothetical,False)]
      other -> counterexample (show other) False

modeledContext :: T.SourceInput -> (A.Policy,[A.Leaf],T.ObjectMeta,T.EvidenceCapture)
modeledContext source = (policy,leaves,meta,capture)
  where
    policy = (T.sourcePolicy source){A.policyAdmission = []}
    leaves = [leaf{A.leafRefs = [A.SourceRef "../../arbitrary"]} | A.DeclLeaf leaf <- A.programDecls (T.sourceProgram source)]
    meta = T.ObjectMeta (ObjectId "data") "../../arbitrary" 999999999999999999999 "not-a-package-digest"
    payload = CsvPayload (CsvTable [ColumnName "id",ColumnName "value"] [["one","7"]])
    capture = T.EvidenceCapture [(ObjectId "data",Right (meta,payload))] [meta]
prop_modeledMetadata :: Property
prop_modeledMetadata = withSource "admission-evidence-fail" 0 $ \source ->
  let (policy,leaves,_,capture) = modeledContext source
  in case leaves of
    [] -> counterexample "modeled evidence fixture has no leaf" False
    first:_ ->
      let program = (T.sourceProgram source){A.programDecls = map (\decl -> case decl of
            A.DeclLeaf _ -> A.DeclLeaf first
            other -> other) (A.programDecls (T.sourceProgram source))}
      in conjoin [property (isLeft (Package.validatePackagePath "../../arbitrary")),
        case E.runModeledEvidence capture policy leaves of
          Left err -> counterexample (show err) False
          Right judgments -> map E.modeledJudgmentProp judgments === [Prop (Pred "result") [TNum "7"]],
        case rebuild source program policy (Just capture) of
          Left err -> counterexample err False
          Right changed -> accepted changed $ \observation -> S.publicStatus observation (Prop (Pred "result") [TNum "7"]) === Published A.Justified]
prop_captureFailure :: Property
prop_captureFailure = withSource "admission-evidence-fail" 0 $ \source ->
  let (policy,leaves,_,capture) = modeledContext source
      ident = ObjectId "data"
      failed = capture{T.captureSnapshot = (ident,Left "first failure") : T.captureSnapshot capture}
      mismatch = capture{T.captureManifest = [meta{T.objectLength = 1} | meta <- T.captureManifest capture]}
  in conjoin [E.lookupCapture failed ident === Left "first failure",
    E.runModeledEvidence failed policy leaves === Left (T.EvidenceError T.EvidenceCaptureStage (A.LeafId "measured") (Just ident) "first failure"),
    E.runModeledEvidence mismatch policy leaves === Left (T.EvidenceError T.EvidenceCaptureStage (A.LeafId "measured") (Just ident) "metadata")]
prop_modelSelectorBound :: Property
prop_modelSelectorBound = withSource "admission-evidence-fail" 0 $ \source ->
  let (policy,leaves,_,capture) = modeledContext source
      request = CsvRowRequest (CheckerVersion 1) (ObjectId "data") (ColumnName "id") "one" (replicate 257 (CsvSelector (ColumnName "value") Decimal)) (Pred "result")
      selected = [leaf{A.leafExtraction = Just request,A.leafProp = Prop (Pred "result") (replicate 257 (TNum "7"))} | leaf <- leaves]
  in case E.lookupCapture capture (ObjectId "data") of
    Left err -> counterexample err False
    Right (_,payload) -> conjoin [property (isLeft (runTypedRegistry request payload)),
      case E.runModeledEvidence capture policy selected of
        Left err -> counterexample (show err) False
        Right judgments -> map E.modeledJudgmentProp judgments === [Prop (Pred "result") (replicate 257 (TNum "7"))]]
prop_duplicateJson :: Property
prop_duplicateJson = withSource "admission-evidence-fail" 0 $ \source ->
  let (policy,leaves,meta,capture) = modeledContext source
      request = JsonPointerRequest (CheckerVersion 1) (ObjectId "data") [JsonSelector [JsonToken "value"] Decimal] (Pred "result")
      selected = [leaf{A.leafExtraction = Just request,A.leafProvenance = A.Checker "json-pointer" "1"} | leaf <- leaves]
      policy' = policy{A.policyEvidenceCheckers = [(JsonPointer,CheckerVersion 1)]}
      tree = JsonObject [(JsonToken "value",JsonNumber "7"),(JsonToken "off-path",JsonObject [(JsonToken "duplicate",JsonNull),(JsonToken "duplicate",JsonNull)])]
      captured = capture{T.captureSnapshot = [(ObjectId "data",Right (meta,JsonPayload tree))]}
  in conjoin [W.decodeCapture (W.encodeCapture captured) === Right captured,
    E.runModeledEvidence captured policy' selected === Left (T.EvidenceError T.EvidenceExtractionStage (A.LeafId "measured") Nothing "json-selection")]

prop_hugePosition :: Property
prop_hugePosition = forAll (chooseInteger (2^(64 :: Int),2^(128 :: Int))) $ \enormous ->
  let seed = A.SLeaf (A.LeafId "seed")
      term = A.SRule (A.RuleId "r") [] [seed] [] [] A.AssuranceNone
  in subterm term [A.StepPremise enormous] === Nothing
prop_signedCodec :: Property
prop_signedCodec = withSource "normalized-support" 0 $ \source -> forAll (chooseInteger (2^(64 :: Int),2^(128 :: Int))) $ \enormous ->
  let certificate = A.Cert (A.BackendId "nd") (-enormous) (A.TheoryDigest "authored") (SAtom (show enormous))
      term = A.SRule (A.RuleId "r") [] [] [] [] (A.AssuranceCert certificate)
      argument = A.DeclArg (A.Arg (A.ArgId "huge") (A.SupportsDerived (A.PropId "derived")) (A.ExplicitTheta term))
      position = A.DeclAttack (A.SUndercut (A.ArgId "huge") (A.ArgId "selected") [A.StepIndex (-enormous),A.StepIndex enormous])
      program = (T.sourceProgram source){A.programDecls = A.programDecls (T.sourceProgram source) ++ [argument,position]}
      coordinate = T.DeclarationCertificate (fromIntegral (length (A.programDecls (T.sourceProgram source)))) []
      policy = (T.sourcePolicy source){A.policyRules = A.policyRules (T.sourcePolicy source) ++
        [A.Rule (A.RuleId "signed-rule") [] A.Strict [] [] (A.AtomPat (Pred "result") [A.PLit (TNum "7")])
          False [A.CertRef (A.BackendId "nd") (-enormous) (A.TheoryDigest "authored")] []]}
  in case T.mkSourceInputWithPayloads program policy (T.sourceReplay source) Nothing [(coordinate,T.CertificateInteger enormous)] of
    Left err -> counterexample err False
    Right changed -> conjoin [W.decodeSource (W.encodeSource changed) === Right changed,
      case T.mkFragmentWithPayloads [argument,position] [(T.DeclarationCertificate 0 [],T.CertificateInteger enormous)] of
        Left err -> counterexample err False
        Right fragment -> W.decodeFragment (W.encodeFragment fragment) === Right fragment]
prop_negativePosition :: Property
prop_negativePosition = withSource "shared-discharge" 2 $ \source ->
  let program = (T.sourceProgram source){A.programDecls = map replace (A.programDecls (T.sourceProgram source))}
      replace (A.DeclAttack (A.SUndermine a b path)) = A.DeclAttack (A.SUndermine a b [case step of A.StepIndex 0 -> A.StepIndex (-1); other -> other | step <- path])
      replace other = other
  in case T.replaceSourceProgram source program of
    Left err -> counterexample err False
    Right changed -> conjoin [W.decodeSource (W.encodeSource changed) === Right changed,
      rejected (D.SourceRejection (D.SourceDiagnostic
        (D.Structural (D.InvalidSurfaceAttack (A.ArgId "attacker") (A.ArgId "wrapper"))))) changed]

prop_rejectedRows :: Property
prop_rejectedRows = withSource "admission-evidence-fail" 0 $ \source ->
  let (_,rows) = S.observeSource source [atom "t",atom "other"]
      expected = D.SourceRejection (D.SourceDiagnostic (D.Structural (D.AdmissionRejected (A.LeafId "measured"))))
  in rows === [(atom "t",S.QueryRejected expected),(atom "other",S.QueryRejected expected)]

prop_missingConflictCoordinates :: Property
prop_missingConflictCoordinates = withSource "reindex-hole" 1 $ \source ->
  let t = atom "t"
      contrary = atom "opposite"
      newLeaf ident prop = A.DeclLeaf (A.Leaf (A.LeafId ident) prop A.Observed A.User [] Nothing)
      newArg ident leaf = A.DeclArg (A.Arg (A.ArgId ident) (A.SupportsDerived (A.PropId ident))
        (A.ExplicitTheta (A.SLeaf (A.LeafId leaf))))
      program = (T.sourceProgram source){A.programDecls = A.programDecls (T.sourceProgram source)
        ++ [newLeaf "left" t,newLeaf "right" contrary,newArg "left-arg" "left",newArg "right-arg" "right"]}
      policy = (T.sourcePolicy source){A.policySigma = declarePred (Pred "opposite") [] (A.policySigma (T.sourcePolicy source)),
        A.policyContraries = [A.Contrary (A.AtomPat (Pred "t") []) (A.AtomPat (Pred "opposite") [])]}
      expected = D.SourceRejection (D.CoreDiagnostic (C.CoreProgram
        (C.ProgramMissingConflict (C.MissingConflict 0 1 t contrary))))
  in case rebuild source program policy Nothing of
    Left err -> counterexample err False
    Right changed -> rejected expected changed

prunedCertificateSource :: T.SourceInput -> Bool -> Either String T.SourceInput
prunedCertificateSource source nested = rebuild source program policy Nothing
  where
    seed = A.Leaf (A.LeafId "pruned-seed") (atom "pruned-seed") A.Observed A.AiExecuted [] Nothing
    ground = A.AtomPat (Pred "result") [A.PLit (TNum "7")]
    strict = A.Rule (A.RuleId "pruned-rule") [] A.Strict [A.AtomPat (Pred "pruned-seed") []]
      [] ground False [A.CertRef (A.BackendId "unselected") 1 (A.TheoryDigest "opaque")] []
    outer = A.Rule (A.RuleId "outer-rule") [] A.Defeasible [ground] [] ground False [] []
    certificate = A.AssuranceCert (A.Cert (A.BackendId "unselected") 1 (A.TheoryDigest "opaque") (SAtom "opaque"))
    strictTerm = A.SRule (A.RuleId "pruned-rule") [] [] [] [] certificate
    term = if nested then A.SRule (A.RuleId "outer-rule") [] [strictTerm] [] [] A.AssuranceNone else strictTerm
    argument = A.Arg (A.ArgId "pruned") (A.SupportsDerived (A.PropId "pruned")) (A.ExplicitTheta term)
    program = (T.sourceProgram source){A.programDecls = A.programDecls (T.sourceProgram source) ++ [A.DeclLeaf seed,A.DeclArg argument]}
    original = T.sourcePolicy source
    policy = original{A.policySigma = declarePred (Pred "pruned-seed") [] (A.policySigma original),
      A.policyRules = A.policyRules original ++ [strict,outer],
      A.policyAdmission = A.policyAdmission original ++ [((A.Observed,A.AiExecuted),A.Quarantine)]}
prop_declaredSelection :: Property
prop_declaredSelection = withSource "normalized-support" 0 $ \source -> conjoin
  [case prunedCertificateSource source nested of
    Left err -> counterexample err False
    Right changed -> rejected
      (D.UnselectedCertificate 1 (A.ArgId "pruned") (C.CoreBackend (A.BackendId "unselected") 1)) changed
    | nested <- [False,True]]

prop_coreBeforeSelection :: Property
prop_coreBeforeSelection = withSource "normalized-support" 0 $ \source ->
  case prunedCertificateSource source True of
    Left err -> counterexample err False
    Right changed ->
      let original = T.sourcePolicy changed
          badPolicy = original{A.policySigma = (A.policySigma original){sigmaSorts = [SortName "Num"]}}
      in case rebuild changed (T.sourceProgram changed) badPolicy Nothing of
        Left err -> counterexample err False
        Right both -> case S.checkSource both of
          Left actual -> actual === D.SourceRejection (D.CoreDiagnostic (C.CoreSignature C.MalformedSigma))
          Right _ -> counterexample "core failure was suppressed by selection" False

prop_groupBeforeCapture :: Property
prop_groupBeforeCapture = withSource "admission-evidence-fail" 0 $ \source ->
  let (original,_,_,capture) = modeledContext source
      add name value = A.DeclLeaf (A.Leaf (A.LeafId name) (Prop (Pred "result") [TNum value]) A.Observed A.User [] Nothing)
      program = (T.sourceProgram source){A.programDecls = A.programDecls (T.sourceProgram source)
        ++ [add "first" "1",add "second" "2",A.DeclGroup (A.DupGroup (A.GroupId "conflict") [A.LeafId "first",A.LeafId "second"])]}
      policy = original{A.policyGroupMode = A.RejectOnConflict}
      failed = capture{T.captureSnapshot = [(ObjectId "data",Left "capture fails too")]}
  in case rebuild source program policy (Just failed) of
    Left err -> counterexample err False
    Right changed -> rejected (D.SourceRejection (D.SourceDiagnostic (D.GroupConflict (A.GroupId "conflict")))) changed

prop_manifestOrderedCapture :: Property
prop_manifestOrderedCapture = withSource "admission-evidence-fail" 0 $ \source ->
  let (policy,leaves,firstMeta,_) = modeledContext source
  in case leaves of
    [] -> counterexample "modeled evidence fixture has no leaf" False
    first:_ ->
      let secondRequest = CsvRowRequest (CheckerVersion 1) (ObjectId "second") (ColumnName "id") "one"
            [CsvSelector (ColumnName "value") Decimal] (Pred "result")
          second = first{A.leafId = A.LeafId "second-leaf",A.leafExtraction = Just secondRequest}
          secondMeta = firstMeta{T.objectId = ObjectId "second"}
          failed = T.EvidenceCapture [(ObjectId "data",Left "first capture"),(ObjectId "second",Left "second capture")]
            [secondMeta,firstMeta]
      in E.runModeledEvidence failed policy [first,second] ===
        Left (T.EvidenceError T.EvidenceCaptureStage (A.LeafId "second-leaf") (Just (ObjectId "second")) "second capture")

prop_exactDirective :: Property
prop_exactDirective = withSource "normalized-support" 0 $ \source ->
  let replace (A.DeclClaim claim) = A.DeclClaim claim{A.claimNl = "Value { cell measured}"}
      replace other = other
      program = (T.sourceProgram source){A.programDecls = map replace (A.programDecls (T.sourceProgram source))}
  in case T.replaceSourceProgram source program of
    Left err -> counterexample err False
    Right changed -> rejected (D.SourceRejection (D.SourceDiagnostic
      (D.Structural (D.InvalidValueBinding (A.ValueName " cell measured"))))) changed

prop_jsonDepthBoundary :: Property
prop_jsonDepthBoundary = withSource "admission-evidence-fail" 0 $ \source ->
  let (original,leaves,meta,capture) = modeledContext source
      policy = original{A.policyEvidenceCheckers = [(JsonPointer,CheckerVersion 1)]}
      tree 0 = JsonNumber "7"
      tree n = JsonObject [(JsonToken "x",tree (n-1))]
      run depth = E.runModeledEvidence
        capture{T.captureSnapshot = [(ObjectId "data",Right (meta,JsonPayload (tree depth)))]}
        policy [leaf{A.leafProvenance = A.Checker "json-pointer" "1",
          A.leafExtraction = Just (JsonPointerRequest (CheckerVersion 1) (ObjectId "data")
            [JsonSelector (replicate depth (JsonToken "x")) Decimal] (Pred "result"))} | leaf <- leaves]
  in conjoin [case run 128 of
    Left err -> counterexample (show err) False
    Right judgments -> map E.modeledJudgmentProp judgments === [Prop (Pred "result") [TNum "7"]],
    run 129 === Left (T.EvidenceError T.EvidenceExtractionStage (A.LeafId "measured") Nothing "json-selection")]

prop_orderedDuplicateCapture :: Property
prop_orderedDuplicateCapture = withSource "admission-evidence-fail" 0 $ \source ->
  let (policy,leaves,meta,capture) = modeledContext source
      duplicate = capture{T.captureManifest = [meta,meta{T.objectDigest = "different"}]}
      wrongId = capture{T.captureSnapshot =
        [(ObjectId "data",Right (meta{T.objectId = ObjectId "wrong"},JsonPayload JsonNull))]}
      lexemes = capture{T.captureSnapshot =
        [(ObjectId "data",Right (meta,JsonPayload (JsonObject
          [(JsonToken "n",JsonNumber "-0007.00e+000"),(JsonToken "n",JsonNumber "opaque")])))]}
  in conjoin
    [E.runModeledEvidence duplicate policy leaves === Left (T.EvidenceError T.EvidenceCaptureStage (A.LeafId "measured") (Just (ObjectId "data")) "metadata"),
     E.lookupCapture wrongId (ObjectId "data") === Left "metadata",
     W.decodeCapture (W.encodeCapture lexemes) === Right lexemes]

prop_replayBranches :: Property
prop_replayBranches = withSource "normalized-support" 0 $ \source ->
  let program = T.sourceProgram source
      policy = T.sourcePolicy source
      replay = T.sourceReplay source
      backend name version = T.BackendIdentity (A.BackendId name) (T.BackendVersion version)
      check p pol identity expected = case T.mkSourceInput p pol identity Nothing of
        Left err -> counterexample err False
        Right changed -> rejected (D.ReplayRejection expected) changed
  in conjoin
    [check program policy replay{T.replayPolicy = A.PolicyId "wrong"} D.ReplayPolicyMismatch,
     check program policy replay{T.replayBackends = [backend "nd" "1"]} D.BackendMismatch,
     check program{A.programBackends = [(A.BackendId "nd","1"),(A.BackendId "nd","1")]} policy
       replay{T.replayBackends = [backend "nd" "1",backend "nd" "1"]} D.DuplicateBackend,
     check program{A.programBackends = [(A.BackendId "missing-first","1"),(A.BackendId "missing-second","1")]} policy
       replay{T.replayBackends = [backend "missing-first" "1",backend "missing-second" "1"]}
       (D.UnsupportedBackend (backend "missing-first" "1")),
     check program policy{A.policyTheories = [(A.TheoryDigest "duplicate",[]),(A.TheoryDigest "duplicate",[])]}
       replay D.DuplicateTheory,
     check program policy{A.policyTheories = [(A.TheoryDigest "b",[]),(A.TheoryDigest "a",[])]}
       replay{T.replayTheories = [A.TheoryDigest "b",A.TheoryDigest "a"]} D.TheoryMismatch,
     check program policy replay{T.replayArtifact = A.Digest "wrong"} D.ArtifactMismatch]

prop_bindingObjectPayload :: Property
prop_bindingObjectPayload = withSource "admission-evidence-fail" 0 $ \source ->
  let (policy,leaves,_,capture) = modeledContext source
      missing = capture{T.captureManifest = []}
      mismatched = [leaf{A.leafRefs = [A.SourceRef "other-path"]} | leaf <- leaves]
      badProvenance = [leaf{A.leafProvenance = A.User} | leaf <- leaves]
  in conjoin
    [E.runModeledEvidence missing policy leaves === Left (T.EvidenceError T.EvidenceBindingStage (A.LeafId "measured") (Just (ObjectId "data")) "binding"),
     E.runModeledEvidence capture policy mismatched === Left (T.EvidenceError T.EvidenceBindingStage (A.LeafId "measured") (Just (ObjectId "data")) "binding"),
     E.runModeledEvidence capture policy badProvenance === Left (T.EvidenceError T.EvidenceBindingStage (A.LeafId "measured") Nothing "binding")]

prop_modeledStringRendering :: Property
prop_modeledStringRendering = withSource "normalized-support" 0 $ \source -> conjoin
  [ let program = (T.sourceProgram source)
          { A.programValueBindings = [A.ValueBinding (A.ValueName "value") term]
          , A.programDecls = [case declaration of
              A.DeclClaim claim -> A.DeclClaim claim{A.claimNl = "{value}"}
              other -> other | declaration <- A.programDecls (T.sourceProgram source)]
          }
        original = T.sourcePolicy source
        policy = original{A.policySigma = (A.policySigma original){sigmaCons =
          sigmaCons (A.policySigma original) ++ [ConSig (FunSym "wrap") [SortStr,SortStr,SortStr] SortStr]}}
    in case rebuild source program policy Nothing of
      Left err -> counterexample err False
      Right changed -> accepted changed $ \observation ->
        let semantic = Elaborate.acceptedSourceSemantic (S.observationAcceptedSource observation)
        in [A.claimNl claim | A.DeclClaim claim <- A.programDecls semantic] === [expected]
    | (term,expected) <-
      [(TStr "é\SOH","\"é\SOH\""),
       (TCon (FunSym "wrap") [TStr "é",TStr "\SOH",TStr "\n\t\r\"\\"],
        "wrap(\"é\", \"\SOH\", \"\\n\\t\\r\\\"\\\\\")")]]

prop_unknownAttacker :: Property
prop_unknownAttacker = withSource "blocked-conditional" 0 $ \source -> accepted source $ \observation ->
  case P.buildProvenance observation of
    Left err -> counterexample (show err) False
    Right table -> conjoin
      [S.observationNames observation === [A.ArgId "witness",A.ArgId "attacker"],
       P.gradeNode (P.buildKindTable source table [] [] [] [] [] []) 1 === Right (Process.Hypothetical,False),
       P.checkedKeys table 99 === Left (Audit.ProvenanceMissingNode 99)]

prop_nonleafDischarge :: Property
prop_nonleafDischarge = withSource "shared-discharge" 0 $ \source ->
  let replacement (A.DeclArg argument) | A.argId argument == A.ArgId "wrapper" =
        A.DeclArg argument{A.argInstantiation = A.ExplicitTheta
          (A.SRule (A.RuleId "r-d") [] []
            [(A.QuestionId "qd",A.SRule (A.RuleId "r-e") [] [] [] [] A.AssuranceNone)] [] A.AssuranceNone)}
      replacement other = other
      program = (T.sourceProgram source){A.programDecls = map replacement (A.programDecls (T.sourceProgram source))}
  in case T.replaceSourceProgram source program of
    Left err -> counterexample err False
    Right changed -> rejected (D.SourceRejection (D.SourceDiagnostic
      (D.Structural (D.InvalidInferredArgument (A.ArgId "wrapper"))))) changed

prop_missingReconstructedConclusion :: Property
prop_missingReconstructedConclusion = withSource "forged-observed" 0 $
  rejected (D.SourceRejection (D.SourceDiagnostic
    (D.Structural (D.InvalidInferredArgument (A.ArgId "witness")))))

prop_typedVariableConstructor :: Property
prop_typedVariableConstructor = withSource "normalized-support" 0 $ \source ->
  let rule = A.Rule (A.RuleId "variable-rule") [] A.Defeasible [] []
        (A.AtomPat (Pred "result") [A.PVar (A.Param "actual-variable")]) False [] []
      argument = A.DeclArg (A.Arg (A.ArgId "variable-arg") (A.SupportsDerived (A.PropId "variable"))
        (A.InferTheta (A.RuleId "variable-rule") [] [] [] A.AssuranceNone))
      policy = (T.sourcePolicy source){A.policyRules = [rule]}
      program = (T.sourceProgram source){A.programDecls = A.programDecls (T.sourceProgram source) ++ [argument]}
  in case rebuild source program policy Nothing of
    Left err -> counterexample err False
    Right changed -> rejected (D.SourceRejection (D.SourceDiagnostic
      (D.Structural (D.InvalidInferredArgument (A.ArgId "variable-arg"))))) changed

prop_legacyTypedMissingDependency :: Property
prop_legacyTypedMissingDependency = withSource "admission-evidence-fail" 0 $ \source ->
  let leaves = [leaf | A.DeclLeaf leaf <- A.programDecls (T.sourceProgram source)]
      checked = A.policyEvidenceCheckers (T.sourcePolicy source)
      objects = do
        digest <- Package.decodeSha256 ("sha256:" ++ replicate 64 '0')
        metadata <- Package.makeObjectMeta (ObjectId "data") "data.csv" 0 digest
        pure [metadata]
  in case objects of
    Left err -> counterexample err False
    Right metadata -> case Admission.bindEvidenceMetadata metadata checked leaves of
      Left err -> counterexample (show err) False
      Right bound -> Runner.replayTypedEvidence [] [] bound === Left
        (Admission.EvidenceRejection Admission.ExtractionStage (A.LeafId "measured") (Just (ObjectId "data")) "missingdep")

structuralRejection :: D.SurfaceError -> D.SourceRejection
structuralRejection = D.SourceRejection . D.SourceDiagnostic . D.Structural

negativeCertificates :: A.Program -> A.Program
negativeCertificates program = program{A.programDecls = map declaration (A.programDecls program)}
  where
    declaration (A.DeclArg argument) | A.argId argument == A.ArgId "pruned" =
      A.DeclArg argument{A.argInstantiation = case A.argInstantiation argument of
        A.ExplicitTheta term -> A.ExplicitTheta (support term)
        A.InferTheta rule refs discharges holes assurance ->
          A.InferTheta rule refs discharges holes (certificate assurance)}
    declaration other = other
    support (A.SLeaf leaf) = A.SLeaf leaf
    support (A.SRule rule theta premises discharges holes assurance) =
      A.SRule rule theta (map support premises) [(question,support term) | (question,term) <- discharges]
        holes (certificate assurance)
    certificate (A.AssuranceCert cert) = A.AssuranceCert cert{A.certVersion = -1}
    certificate other = other

prop_negativeCertificate :: Property
prop_negativeCertificate = withSource "normalized-support" 0 $ \source -> conjoin
  [case prunedCertificateSource source nested >>= \prepared ->
      T.replaceSourceProgram prepared (negativeCertificates (T.sourceProgram prepared)) of
    Left err -> counterexample err False
    Right changed -> rejected (structuralRejection (D.InvalidNamedCertificate (A.ArgId "pruned"))) changed
    | nested <- [False,True]]

prop_unknownInferredDischarge :: Property
prop_unknownInferredDischarge = withSource "shared-discharge" 2 $ \source ->
  let declaration (A.DeclArg argument) | A.argId argument == A.ArgId "wrapper" =
        A.DeclArg argument{A.argInstantiation = A.InferTheta (A.RuleId "r-d") []
          [(A.QuestionId "not-declared",A.ArgRef "dseed")] [] A.AssuranceNone}
      declaration other = other
      program = (T.sourceProgram source){A.programDecls = map declaration (A.programDecls (T.sourceProgram source))}
  in case T.replaceSourceProgram source program of
    Left err -> counterexample err False
    Right changed -> rejected (structuralRejection (D.InvalidInferredArgument (A.ArgId "wrapper"))) changed

prop_reconstructionBeforeCertificate :: Property
prop_reconstructionBeforeCertificate = withSource "normalized-support" 0 $ \source ->
  case prunedCertificateSource source True of
    Left err -> counterexample err False
    Right prepared ->
      let earlier = negativeCertificates (T.sourceProgram prepared)
          bad = A.SRule (A.RuleId "not-declared") [] [] [] [] A.AssuranceNone
          declaration (A.DeclArg argument)
            | A.argId argument == A.ArgId "pruned"
            , A.ExplicitTheta (A.SRule rule theta premises discharges holes assurance) <- A.argInstantiation argument =
                A.DeclArg argument{A.argInstantiation = A.ExplicitTheta
                  (A.SRule rule theta (premises ++ [bad]) discharges holes assurance)}
          declaration other = other
          program = earlier{A.programDecls = map declaration (A.programDecls earlier)}
          later = A.DeclArg (A.Arg (A.ArgId "later") (A.SupportsDerived (A.PropId "later"))
            (A.ExplicitTheta bad))
          separate = earlier{A.programDecls = A.programDecls earlier ++ [later]}
          check input expected = case T.replaceSourceProgram prepared input of
            Left error' -> counterexample error' False
            Right changed -> rejected (structuralRejection expected) changed
       in conjoin
          [check program (D.InvalidInferredArgument (A.ArgId "pruned")),
           check separate (D.InvalidNamedCertificate (A.ArgId "pruned"))]

prop_authoredInferenceGuard :: Property
prop_authoredInferenceGuard = withSource "normalized-support" 0 $ \source ->
  case [leaf | A.DeclLeaf leaf <- A.programDecls (T.sourceProgram source)] of
    [] -> counterexample "missing normalized-support leaf" False
    template : _ ->
      let seed = template{A.leafId = A.LeafId "bound-seed",
            A.leafProp = Prop (Pred "result") [TCon (FunSym "bound-value") []]}
          result = A.AtomPat (Pred "result") [A.PLit (TNum "7")]
          rule = A.Rule (A.RuleId "bound-rule") [] A.Defeasible [result] [] result False [] []
          argument = A.Arg (A.ArgId "authored-guard") (A.SupportsDerived (A.PropId "authored-guard"))
            (A.InferTheta (A.RuleId "bound-rule") [A.ArgRef "bound-seed"] [] [] A.AssuranceNone)
          program = (T.sourceProgram source){A.programValueBindings = [A.ValueBinding (A.ValueName "bound-value") (TNum "7")],
            A.programDecls = [A.DeclLeaf seed,A.DeclArg argument]}
          policy = (T.sourcePolicy source){A.policyRules = [rule]}
      in case rebuild source program policy Nothing of
        Left err -> counterexample err False
        Right changed -> rejected (structuralRejection (D.InvalidInferredArgument (A.ArgId "authored-guard"))) changed

prop_authoredCellGuard :: Property
prop_authoredCellGuard = withSource "normalized-support" 0 $ \source ->
  case ([leaf | A.DeclLeaf leaf <- A.programDecls (T.sourceProgram source)],
        [claim | A.DeclClaim claim <- A.programDecls (T.sourceProgram source)]) of
    ([], _) -> counterexample "missing normalized-support leaf" False
    (_, []) -> counterexample "missing normalized-support claim" False
    (template : _, templateClaim : _) ->
      let name = A.ValueName "bound-value"
          formal = Prop (Pred "result") [TCon (FunSym "bound-value") []]
          seed = template{A.leafId = A.LeafId "bound-seed", A.leafProp = formal}
          claim = templateClaim{A.claimId = A.PropId "bound-claim", A.claimNl = "{cell bound-seed}", A.claimFormal = formal}
          argument = A.Arg (A.ArgId "bound-argument") (A.SupportsClaim (A.PropId "bound-claim"))
            (A.ExplicitTheta (A.SLeaf (A.LeafId "bound-seed")))
          program = (T.sourceProgram source)
            { A.programValueBindings = [A.ValueBinding name (TNum "7")]
            , A.programDecls = [A.DeclLeaf seed, A.DeclClaim claim, A.DeclArg argument]
            }
          check text expectation =
            let changed = program{A.programDecls =
                  [A.DeclLeaf seed, A.DeclClaim claim{A.claimNl = text}, A.DeclArg argument]}
             in case rebuild source changed (T.sourcePolicy source) Nothing of
                  Left error' -> counterexample error' False
                  Right input -> expectation input
       in conjoin
          [ check "{cell bound-seed}" (rejected (structuralRejection (D.InvalidValueBinding name)))
          , check "value {bound-value}" (\input -> accepted input $ \observation ->
              S.publicStatus observation (Prop (Pred "result") [TNum "7"]) === Published A.Justified)
          ]

prop_inferredScopeOwnership :: Property
prop_inferredScopeOwnership = withSource "normalized-support" 0 $ \source ->
  case [leaf | A.DeclLeaf leaf <- A.programDecls (T.sourceProgram source)] of
    [] -> counterexample "missing normalized-support leaf" False
    seed : _ ->
      let parameter = A.Param "outside"
          ruleName = A.RuleId "scope-rule"
          pattern' = A.AtomPat (Pred "result") [A.PVar parameter]
          rule = A.Rule ruleName [] A.Defeasible [pattern'] [] pattern' False [] []
          argument = A.Arg (A.ArgId "scope-argument") (A.SupportsDerived (A.PropId "scope-result"))
            (A.InferTheta ruleName [A.ArgRef (case A.leafId seed of A.LeafId value -> value)] [] [] A.AssuranceNone)
          program = (T.sourceProgram source){A.programDecls = [A.DeclLeaf seed, A.DeclArg argument]}
          policy = (T.sourcePolicy source){A.policyRules = [rule]}
       in case rebuild source program policy Nothing of
            Left error' -> counterexample error' False
            Right input -> rejected
              (D.SourceRejection (D.CoreDiagnostic (C.CoreScopeViolation ruleName parameter))) input

prop_outOfRangeAttack :: Property
prop_outOfRangeAttack = withSource "shared-discharge" 2 $ \source ->
  let declaration (A.DeclAttack (A.SUndermine sourceId target path)) =
        A.DeclAttack (A.SUndermine sourceId target [case step of A.StepIndex _ -> A.StepIndex (2^(96 :: Int)); other -> other | step <- path])
      declaration other = other
      program = (T.sourceProgram source){A.programDecls = map declaration (A.programDecls (T.sourceProgram source))}
  in case T.replaceSourceProgram source program of
    Left err -> counterexample err False
    Right changed -> rejected (structuralRejection (D.InvalidSurfaceAttack (A.ArgId "attacker") (A.ArgId "wrapper"))) changed

prop_duplicateScanOrder :: Property
prop_duplicateScanOrder = withSource "normalized-support" 0 $ \source ->
  let original = T.sourceProgram source
      policy = T.sourcePolicy source
      declarations = A.programDecls original
  in case ([leaf | A.DeclLeaf leaf <- declarations],
        [argument | A.DeclArg argument <- declarations],
        [claim | A.DeclClaim claim <- declarations]) of
    (leaf : _,argument : _,claim : _) ->
      let names = ["a","b","b","a"]
          check program checkedPolicy fault = case rebuild source program checkedPolicy Nothing of
            Left err -> counterexample err False
            Right changed -> rejected (structuralRejection fault) changed
          leaves = original{A.programDecls = [A.DeclLeaf leaf{A.leafId = A.LeafId name} | name <- names]}
          arguments = original{A.programDecls = [declaration | declaration <- declarations,case declaration of A.DeclArg _ -> False; _ -> True]
            ++ [A.DeclArg argument{A.argId = A.ArgId name} | name <- names]}
          claims = original{A.programDecls = [declaration | declaration <- declarations,case declaration of A.DeclClaim _ -> False; _ -> True]
            ++ [A.DeclClaim claim{A.claimId = A.PropId name} | name <- names]}
          keyA = (A.Observed,A.User)
          keyB = (A.Attested,A.User)
          duplicatePolicy = policy{A.policyAdmission = [(key,A.Quarantine) | key <- [keyA,keyB,keyB,keyA]]}
          second = A.LeafId "group-second"
          groups = original{A.programDecls = [declaration | declaration <- declarations,case declaration of A.DeclGroup _ -> False; _ -> True]
            ++ [A.DeclLeaf leaf{A.leafId = second}]
            ++ [A.DeclGroup (A.DupGroup (A.GroupId name) [A.leafId leaf,second]) | name <- names]}
      in conjoin
        [check leaves policy (D.DuplicateLeafId (A.LeafId "a")),
         check arguments policy (D.DuplicateArgumentId (A.ArgId "a")),
         check claims policy (D.DuplicateClaimId (A.PropId "a")),
         check original duplicatePolicy (D.SourceDuplicateAdmissionKey A.Observed A.User),
         check groups policy (D.SourceDuplicateGroupId (A.GroupId "b"))]
    _ -> counterexample "missing normalized-support declarations" False

codecRoundtrips :: (Eq a, Show a, Eq err, Show err) =>
  (a -> SExpr) -> (SExpr -> Either err a) -> [a] -> Property
codecRoundtrips encode decode values = conjoin
  [counterexample (show value) (decode (encode value) === Right value) | value <- values]

prop_diagnosticConstructorInventory :: Property
prop_diagnosticConstructorInventory = once $ conjoin
  [codecRoundtrips DW.encodeCheckFault DW.decodeCheckFault faults,
   codecRoundtrips DW.encodeCoreError DW.decodeCoreError coreErrors,
   codecRoundtrips DW.encodeSourceDiagnostic DW.decodeSourceDiagnostic diagnostics,
   codecRoundtrips DW.encodeRejection DW.decodeRejection rejections,
   DW.encodeCheckFault (C.CheckR1 C.CoreRoot (C.ReferenceMissingLeaf leaf)) ===
     SList [SAtom "r1",SList [SAtom "root"],SList [SAtom "missing-leaf",SAtom "leaf"]],
   property (isLeft (DW.decodeCheckFault (SList [SAtom "R1",SList [SAtom "root"],SList [SAtom "missing-leaf",SAtom "leaf"]]))),
   property (isLeft (DW.decodeCheckFault (SList [SAtom "r4",SList [SAtom "root"],SList [SAtom "count",SAtom "0001",SAtom "0"]])))]
  where
    leaf = A.LeafId "leaf"
    rule = A.RuleId "rule"
    argument = A.ArgId "argument"
    claim = A.PropId "claim"
    question = A.QuestionId "question"
    parameter = A.Param "parameter"
    group = A.GroupId "group"
    huge = 2^(96 :: Int)
    backend = C.CoreBackend (A.BackendId "backend") huge
    digest = A.TheoryDigest "digest"
    payload = SList [SAtom "\SOH",SList [],SAtom "-7"]
    patternValue = C.CoreAtomPattern (Pred "predicate")
      [C.PatternConstructor (FunSym "constructor") [C.PatternVariable parameter,C.PatternNumber "opaque",C.PatternString "é\n"]]
    proposition = Prop (Pred "predicate") [TCon (FunSym "constructor") [TNum "opaque",TStr "é\n"]]
    other = atom "other"
    support = C.CoreRule rule [(parameter,TCon (FunSym "constructor") [TNum "opaque"])]
      [C.CoreLeaf leaf] [(question,C.CoreLeaf leaf)] [question,question] (C.CoreCertificate backend digest payload)
    location = C.CoreQuestionLocation (C.CorePremiseLocation C.CoreRoot huge) question
    position = [C.CorePremise huge,C.CoreQuestion question]
    faults =
      [C.CheckR1 location reason | reason <- [C.ReferenceMissingLeaf leaf,C.ReferenceMissingRule rule,
        C.ReferenceUndeclaredSource support,C.ReferenceUndeclaredTarget support]]
      ++ [C.CheckR3 location reason | reason <- [C.SubstitutionDuplicateKeys [parameter,parameter],
        C.SubstitutionDomainMismatch [parameter] [],C.SubstitutionPremiseInstantiation [patternValue],
        C.SubstitutionConclusionInstantiation patternValue]]
      ++ [C.CheckR4 location reason | reason <- [C.PremiseCount huge 0,C.PremiseMismatch proposition other]]
      ++ [C.CheckR5 location reason | reason <- [C.QuestionDuplicateDeclarations [question,question],
        C.QuestionDuplicateDischarges [question],C.QuestionDuplicateHoles [question],
        C.QuestionUncovered [question] [] [],C.QuestionOverlap [question] [question],
        C.QuestionUndeclaredDischarge [] [question],C.QuestionUndeclaredHole [] [question]]]
      ++ [C.CheckR6 location reason | reason <- [C.DischargeAnswerInstantiation question patternValue,
        C.DischargeConclusionMismatch question proposition other]]
      ++ [C.CheckR7 location reason | reason <- [C.AssuranceQuestionsPresent [question] [],
        C.AssuranceWrongMode A.Strict C.CoreNone,C.AssuranceWrongMode A.Defeasible C.CoreTrusted,
        C.AssuranceWrongMode A.Strict (C.CoreCertificate backend digest payload),
        C.AssuranceTrustedDisallowed,C.AssuranceCertifierUnallowlisted backend digest]]
      ++ [C.CheckR10 location position kind reason | kind <- [C.RebutKind,C.UndercutKind,C.UndermineKind],
        reason <- [C.UndefinedPosition,C.WrongOccurrenceKind C.RuleOccurrence C.LeafOccurrence]]
      ++ [C.CheckR11 location position kind reason | kind <- [C.RebutKind,C.UndercutKind,C.UndermineKind],
        reason <- [C.RelationMissingRule rule,C.RelationConclusionInstantiation rule patternValue,
          C.RelationMissingLeaf leaf,C.RelationStrictTarget rule,C.RelationMissingContrary proposition other,
          C.RelationMissingException rule,C.RelationExceptionInstantiation rule patternValue,
          C.RelationExceptionMismatch rule proposition other]]
      ++ [C.CheckR13 location reason | reason <- [C.BackendMissing backend,C.DigestMissing backend digest,
        C.ReplayRejected backend digest payload]]
    coreErrors = [C.CoreDuplicateRule rule 0 huge,C.CoreScopeViolation rule parameter,
      C.CorePolicyViolation rule patternValue (patternValue,patternValue)]
      ++ [C.CoreSignature fault | fault <- [C.MalformedSigma,C.PolicyIllSorted,C.GroundIllSorted,C.ArgumentsIllSorted]]
      ++ [C.CoreProgram (C.ProgramRejection site fault) | site <- [C.ArgumentLocation huge,C.AttackLocation 0],fault <- faults]
      ++ [C.CoreProgram (C.ProgramDuplicateArgument 0 huge),
        C.CoreProgram (C.ProgramMissingConflict (C.MissingConflict huge 0 proposition other))]
    surfaces = [D.Unsupported,D.PolicyMismatch (A.PolicyId "a") (A.PolicyId "b"),
      D.DuplicateLeafId leaf,D.DuplicateArgumentId argument,D.DuplicateClaimId claim,D.DuplicateValueName (A.ValueName "value"),
      D.MalformedRuleNamespace rule,D.InvalidValueBinding (A.ValueName "\SOH"),
      D.InvalidComparison claim,D.InvalidInferredArgument argument,D.InvalidNamedCertificate argument,
      D.SourceConclusionMismatch argument claim,D.SourceChallengeTargetUndeclared argument,
      D.InvalidSurfaceAttack argument argument,D.SourceUnknownStatusClaim claim,D.SourceDuplicateGroupId group,
      D.SourceGroupRepeatedMember group leaf,D.SourceGroupTooFewMembers group,D.SourceGroupMemberUndeclared group leaf,
      D.NoncanonicalPremiseLabels rule,D.AdmissionRejected leaf]
      ++ [D.SourceDuplicateAdmissionKey kind provenance | kind <- [A.Observed,A.Attested,A.Assumed,A.Certified],
        provenance <- [A.User,A.AiExecuted,A.Checker "checker" "opaque-version"]]
    diagnostics = map (D.SourceDiagnostic . D.Structural) surfaces
      ++ map D.SourceDiagnostic [D.EvidenceRequired leaf,D.EvidenceSyntax,D.GroupConflict group]
      ++ [D.EvidenceDiagnostic (T.EvidenceError stage leaf object reason) |
        stage <- [T.EvidenceBindingStage,T.EvidenceCaptureStage,T.EvidenceExtractionStage],
        object <- [Nothing,Just (ObjectId "")],reason <- ["","arbitrary\n\SOH","binding"]]
      ++ map D.CoreDiagnostic coreErrors
    rejections = map D.SourceRejection diagnostics
      ++ map D.ReplayRejection [D.UnsupportedCore (T.CoreVersion "opaque"),D.ReplayPolicyMismatch,
        D.BackendMismatch,D.DuplicateBackend,D.UnsupportedBackend
          (T.BackendIdentity (A.BackendId "backend") (T.BackendVersion "opaque-version")),
        D.DuplicateTheory,D.TheoryMismatch,D.ArtifactMismatch]
      ++ [D.MissingEvidence leaf,D.UnselectedCertificate huge argument backend]

inquirySpecProps :: [(String, IO Result)]
inquirySpecProps =
  [("source wire: " ++ name,quickCheckResult (roundtripFixture name)) | name <-
    ["source-rejections","admission-evidence-fail","blocked-conditional","forged-observed","normalized-support","shared-discharge","reindex-hole","verified-certificate","tampered-certificate","unknown-attacker-kind"]]
  ++ [(name,quickCheckResult prop) | (name,prop) <-
    [("source exact admission failure",prop_admission),("source replay precedes admission",prop_replay),
     ("source absent capture reaches binding before final missing gate",prop_absentCapture),
     ("source arbitrary queries preserve blocked conditional status and multiplicity",prop_blocked),
     ("source support uses normalized conclusions and fresh node names",prop_normalizedSupport),
     ("source shared discharge retains inherited authored identity",prop_sharedDischarge),
     ("source holes retain declaration coordinates separately from AF",prop_reindexedHole),
     ("source forged observed labels remain hypothetical and unknown stays explicit",prop_forgedObserved),
     ("source modeled metadata is not package metadata",prop_modeledMetadata),
     ("source capture keeps first failure and structural metadata mismatch",prop_captureFailure),
     ("source model selectors do not inherit package ceiling",prop_modelSelectorBound),
     ("source JSON duplicates survive wire but fail whole-object extraction",prop_duplicateJson),
     ("source huge positions cannot wrap to valid support",prop_hugePosition),
     ("source signed constructors and opaque integer payload roundtrip",prop_signedCodec),
     ("source negative indices fail authored attack reconstruction",prop_negativePosition),
     ("source rejection rows never receive a public status",prop_rejectedRows),
     ("source missing conflict keeps AF coordinates after an earlier hole",prop_missingConflictCoordinates),
     ("source selection scans pruned roots and nested certificates",prop_declaredSelection),
     ("source typed core failure precedes unselected pruned certificate",prop_coreBeforeSelection),
     ("source group conflict precedes capture failure",prop_groupBeforeCapture),
     ("source capture order follows manifest before leaf extraction",prop_manifestOrderedCapture),
     ("source modeled interpolation retains exact authored directive grammar",prop_exactDirective),
     ("source modeled JSON depth uses exact nonempty-container bound",prop_jsonDepthBoundary),
     ("source ordered duplicate metadata and JSON numeric lexemes are retained",prop_orderedDuplicateCapture),
     ("source replay errors preserve exact compatibility ordering",prop_replayBranches),
     ("source binding failures retain object-bearing modeled payloads",prop_bindingObjectPayload),
     ("source modeled Unicode/control/nested term interpolation is exact",prop_modeledStringRendering),
     ("source actual live attacker without kind metadata stays explicitly unknown",prop_unknownAttacker),
     ("source non-leaf explicit discharge is rejected at reconstruction",prop_nonleafDischarge),
     ("source missing reconstructed conclusion rejects before core",prop_missingReconstructedConclusion),
     ("source typed variable constructors are not reparsed as constants",prop_typedVariableConstructor),
     ("source negative certificate versions reject even pruned nested arguments",prop_negativeCertificate),
     ("source unknown inferred discharge question rejects during reconstruction",prop_unknownInferredDischarge),
     ("source complete reconstruction precedes nested certificate lowering",prop_reconstructionBeforeCertificate),
     ("source original authored inference guards survive let substitution",prop_authoredInferenceGuard),
     ("source original cell directive guard uses authored leaves",prop_authoredCellGuard),
     ("source inferred out-of-scope parameters remain core-owned",prop_inferredScopeOwnership),
     ("source out-of-range attack positions reject before evidence and core",prop_outOfRangeAttack),
     ("source duplicate scan preserves earliest declaration with a later duplicate",prop_duplicateScanOrder),
     ("source diagnostics cover every closed constructor with canonical codecs",prop_diagnosticConstructorInventory),
     ("source evidence factoring preserves legacy typed missing-dependency payload",prop_legacyTypedMissingDependency)]]
  ++ auditRuntimeSpecProps
