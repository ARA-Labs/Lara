module EvidenceAdmissionSpec (evidenceAdmissionSpecProps) where

import qualified Data.ByteString.Char8 as B
import System.FilePath ((</>))
import Test.QuickCheck
import EvidenceFixture
import Lara.TempTree
import Lara.AST
import Lara.Admission (renderAdmissionRejection)
import Lara.Elaborate
import Lara.Evidence.Admission
import Lara.Evidence.Load
import Lara.Evidence.Manifest
import Lara.Evidence.Runner
import Lara.Evidence.Snapshot
import Lara.Evidence.Types (ObjectId (..))
import Lara.Syntax

evidenceAdmissionSpecProps :: [(String,IO Result)]
evidenceAdmissionSpecProps =
  [ ("evidence: public preparation rejects unused and quarantined cert declarations",quickCheckResult (once defaults))
  , ("evidence: policy then bindings then capture then extraction first-error precedence",quickCheckResult (once (ioProperty precedence)))
  , ("evidence: a captured object is only usable under its own manifest entry",quickCheckResult (once (ioProperty captureSeal)))
  , ("evidence: successful replay covers quarantined declarations and ignores unrequested bytes",quickCheckResult (once (ioProperty replay)))
  ]
  where
    defaults = case (parseProgram source,parsePolicy quarantining) of
      (Right p,Right pol) -> case prepareSource p pol of
        Right (SourceEvidenceRejected err) -> evidenceLeaf err === LeafId "measured"
        _ -> counterexample "quarantine hid a certification assertion" False
      values -> counterexample (show values) False
    quarantining = policy ++ "admission { (certified, checker(csv-row, 1)) = quarantine }\n"
    rejecting = policy ++ "admission { (certified, checker(csv-row, 1)) = reject }\n"
    precedence = withTempDirectory "evidence-precedence" $ \root -> do
      writePackage root source rejecting "id,value\none,7\n" []
      B.writeFile (root </> "data.csv") (B.pack "tampered")
      rejectedPolicy <- checkPackage root Nothing
      writePackage root (replace "checker(csv-row, 1)" "user" source) policy "id,value\none,7\n" []
      B.writeFile (root </> "data.csv") (B.pack "tampered")
      rejectedBinding <- checkPackage root Nothing
      writePackage root (replace "result(7)" "result(8)" source) policy "id,value\none,7\n" []
      B.writeFile (root </> "data.csv") (B.pack "tampered")
      rejectedCapture <- checkPackage root Nothing
      writePackage root (replace "result(7)" "result(8)" source) policy "id,value\none,7\n" []
      rejectedExtraction <- checkPackage root Nothing
      writePackage root (replace "result(7)" "result(8)" (replace "use backends []" "use backends [unknown_backend@1]" source)) policy "id,value\none,7\n" []
      rejectedBeforeStrictReplay <- checkPackage root Nothing
      pure (conjoin
        [ property (case rejectedPolicy of Left PackageAdmissionRejected{} -> True; _ -> False)
        , property (stage BindingStage rejectedBinding)
        , property (stage CaptureStage rejectedCapture)
        , property (stage ExtractionStage rejectedExtraction)
        , property (stage ExtractionStage rejectedBeforeStrictReplay)
        ])
    captureSeal = withTempDirectory "evidence-capture-seal" $ \root -> do
      writePackage root source policy "id,value\none,7\n" [("decoy.csv","id,value\none,7\n")]
      manifestBytes' <- B.readFile (root </> "lara-evidence.sexp")
      manifest <- requireRight (decodeManifest manifestBytes')
      dataMeta <- requireRight (maybe (Left "missing declared data object") Right (lookupObject manifest (ObjectId "data")))
      decoyBytes <- B.readFile (root </> "decoy.csv")
      decoyMeta <- requireRight (makeObjectMeta (ObjectId "data") "decoy.csv" (fromIntegral (B.length decoyBytes)) (hashBytes decoyBytes))
      program <- requireRight (parseProgram source)
      pol <- requireRight (parsePolicy policy)
      structural <- case prepareSourceStructure program pol of
        Left invalid -> fail (show invalid)
        Right (Left rejection) -> fail (renderAdmissionRejection rejection)
        Right (Right admitted) -> pure admitted
      borrowed <- withPackageRoot root (\handle -> captureObject handle decoyMeta) >>= requireRight >>= requireRight
      honest <- withPackageRoot root (\handle -> captureObject handle dataMeta) >>= requireRight >>= requireRight
      honestPackage <- checkPackage root Nothing
      pure (conjoin
        [ property (case admitSourceEvidence manifest (insertCaptured borrowed emptySnapshot) structural of
            Left rejection -> evidenceStage rejection == CaptureStage
            Right _ -> False)
        , property (case admitSourceEvidence manifest (insertCaptured honest emptySnapshot) structural of
            Right _ -> True
            Left _ -> False)
        , property (case honestPackage of Right _ -> True; Left _ -> False)
        ])
    replay = withTempDirectory "evidence-locality" $ \root -> do
      writePackage root source quarantining "id,value\none,7\n" [("unused.csv","ignored bytes")]
      first <- checkPackage root Nothing
      B.writeFile (root </> "unused.csv") (B.pack "unlisted integrity change")
      second <- checkPackage root Nothing
      pure $ case (first,second) of
        (Right a,Right b) ->
          let jsA = sourceResultEvidence (packageSourceResult a)
              jsB = sourceResultEvidence (packageSourceResult b)
          in conjoin
            [ map judgmentLeaf jsA === [LeafId "measured"]
            , map judgmentDeps jsA === map judgmentDeps jsB
            , map objectId (packageCapturedMetadata a) === [ObjectId "paper",ObjectId "source",ObjectId "policy",ObjectId "data"]
            , property (all ((/=ObjectId "extra0") . objectId) (packageCapturedMetadata b))
            ]
        _ -> counterexample "actual replay failed" False
    stage expected (Left (PackageEvidenceRejected err)) = evidenceStage err == expected
    stage _ _ = False
    replace from to s = go s
      where go [] = []; go rest | take (length from) rest == from = to ++ go (drop (length from) rest); go (c:cs) = c:go cs
