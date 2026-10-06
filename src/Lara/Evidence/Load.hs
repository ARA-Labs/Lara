module Lara.Evidence.Load
  ( PackageResult, PolicyOrigin (..), PackageError (..), checkPackage, packageSourceResult
  , packageManifestHash, packageSourceHash, packagePolicyHash, packagePolicyOrigin
  , packageDeclaredLeaves, packageCapturedMetadata, packageErrorExitCode, renderPackageError
  ) where

import Control.Monad (foldM)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Lara.AST hiding (Reject)
import Lara.Admission (renderAdmissionRejection)
import Lara.Elaborate
import Lara.Evidence.Admission
import Lara.Evidence.Manifest
import Lara.Evidence.Snapshot
import qualified Lara.Syntax as Syntax
import Lara.Wire (Outcome (..), Verdict (..))

data PolicyOrigin = PackagePolicy | VerifierPolicy deriving (Eq,Ord,Show)
data PackageResult = PackageResult
  { packageSourceResult :: SourceResult
  , packageManifestHash :: Sha256
  , packageSourceHash :: Sha256
  , packagePolicyHash :: Sha256
  , packagePolicyOrigin :: PolicyOrigin
  , packageDeclaredLeaves :: [LeafId]
  , packageCapturedMetadata :: [ObjectMeta]
  }
data PackageError = PackageInvalid String | PackageAdmissionRejected String
  | PackageEvidenceRejected EvidenceRejection | PackageCoreRejected SourceResult
packageErrorExitCode :: PackageError -> Int
packageErrorExitCode PackageInvalid{} = 2
packageErrorExitCode _ = 1
renderPackageError :: PackageError -> String
renderPackageError err = case err of
  PackageInvalid reason -> "package invalid: " ++ reason
  PackageAdmissionRejected reason -> reason
  PackageEvidenceRejected reason -> renderEvidenceRejection reason
  PackageCoreRejected result -> case sourceResultDiagnostics result of
    [] -> "package source rejected: " ++ show (verdictOutcome (sourceResultVerdict result))
    ds -> unlines ds

checkPackage :: FilePath -> Maybe FilePath -> IO (Either PackageError PackageResult)
checkPackage path override = do
  opened <- withPackageRoot path (\root -> load root)
  pure (either (Left . PackageInvalid) id opened)
  where
    load root = do
      manifestRead <- case validatePackagePath "lara-evidence.sexp" of
        Left reason -> pure (Left reason)
        Right member -> readPackageFile root member (1024*1024)
      case manifestRead >>= decodeManifest of
        Left reason -> pure (Left (PackageInvalid reason))
        Right manifest -> do
          globals <- captureMany root [manifestPaper manifest, manifestSource manifest, manifestPolicy manifest] manifest emptySnapshot
          case globals of
            Left reason -> pure (Left (PackageInvalid reason))
            Right snapshot -> do
              verifier <- case override of
                Nothing -> pure (Right Nothing)
                Just file -> fmap (fmap Just) (readVerifierPolicy file)
              case verifier of
                Left reason -> pure (Left (PackageInvalid reason))
                Right verifierBytes -> case parsed manifest snapshot verifierBytes of
                  Left err -> pure (Left err)
                  Right (structural,sourceHash,policyHash,origin) -> case sourceEvidenceBindings manifest structural of
                    Left err -> pure (Left (PackageEvidenceRejected err))
                    Right requests -> do
                      let required = requiredObjects manifest requests
                          total = sum (map objectLength required)
                      if total > 16*1024*1024
                        then case requests of
                          first:_ -> pure (Left (PackageEvidenceRejected (EvidenceRejection CaptureStage (leafId (boundLeaf first)) Nothing "requested capture bound exceeded")))
                          [] -> pure (Left (PackageInvalid "requested capture bound exceeded"))
                        else do
                          captured <- foldM (captureRequired root requests) (Right snapshot) required
                          pure $ do
                            checkedSnapshot <- captured
                            accepted <- either (Left . PackageEvidenceRejected) Right (admitSourceEvidence manifest checkedSnapshot structural)
                            let result = runSourceCheck accepted
                            case verdictOutcome (sourceResultVerdict result) of
                              Reject{} -> Left (PackageCoreRejected result)
                              Accept{} -> Right (PackageResult result (hashBytes (manifestBytes manifest)) sourceHash policyHash origin (map leafId (structuralLeaves structural)) (snapshotMetadata checkedSnapshot))
    captureMany root ids manifest initial = foldM (\state ident -> case state of
      Left err -> pure (Left err)
      Right snapshot -> case lookupObject manifest ident of
        Nothing -> pure (Left "missing global object")
        Just meta -> do
          captured <- captureObject root meta
          pure (fmap (\o -> insertCaptured o snapshot) captured)) (Right initial) ids
    captureRequired root requests state meta = case state of
      Left err -> pure (Left err)
      Right snapshot -> case snapshotLookup snapshot (objectId meta) of
        Just _ -> pure (Right snapshot)
        Nothing -> do
          captured <- captureObject root meta
          pure $ case captured of
            Right object -> Right (insertCaptured object snapshot)
            Left reason -> case earliestObjectLeaf requests (objectId meta) of
              Just leaf -> Left (PackageEvidenceRejected (EvidenceRejection CaptureStage leaf (Just (objectId meta)) reason))
              Nothing -> Left (PackageInvalid "capture request without referencing leaf")
    parsed manifest snapshot verifier = do
      source <- globalBytes snapshot (manifestSource manifest)
      packagePolicy <- globalBytes snapshot (manifestPolicy manifest)
      let policyBytes = maybe packagePolicy id verifier
          origin = maybe PackagePolicy (const VerifierPolicy) verifier
      programText <- strictText "source" source
      policyText <- strictText "policy" policyBytes
      program <- either (Left . PackageInvalid . show) Right (Syntax.parseProgram programText)
      policy <- either (Left . PackageInvalid . show) Right (Syntax.parsePolicy policyText)
      structural <- either (Left . PackageInvalid . renderSourceInvalid) Right (prepareSourceStructure program policy)
      input <- either (Left . PackageAdmissionRejected . renderAdmissionRejection) Right structural
      pure (input,hashBytes source,hashBytes policyBytes,origin)
    globalBytes snapshot ident = maybe (Left (PackageInvalid "missing captured global")) (Right . capturedBytes) (snapshotLookup snapshot ident)
    strictText label bytes = either (const (Left (PackageInvalid (label ++ " is not strict UTF8")))) (Right . T.unpack) (T.decodeUtf8' bytes)
