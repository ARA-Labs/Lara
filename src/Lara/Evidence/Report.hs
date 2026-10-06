module Lara.Evidence.Report
  ( evidenceReport, evidenceReportBytes, evidenceIdentity, dependencyReportBytes, writeEvidenceBundle
  ) where

import Control.Exception (IOException, bracketOnError, try)
import qualified Data.ByteString as B
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import System.Directory (removeDirectoryRecursive)
import System.FilePath ((</>), takeDirectory, takeFileName)
import System.Posix.Temp (mkdtemp)
import Lara.AST (LeafId (..))
import Lara.Elaborate (sourceResultEvidence, sourceResultVerdict)
import Lara.Evidence.Load
import Lara.Evidence.Manifest
import Lara.Evidence.Runner
import Lara.Evidence.Snapshot (publishNoReplace)
import Lara.Evidence.Syntax
import Lara.Strict (SExpr (..))
import Lara.Wire (Verdict (..), encodeVerdict, encodeReplayId, printSExpr)

canonical :: SExpr -> B.ByteString
canonical = T.encodeUtf8 . T.pack . (++"\n") . printSExpr

dependencyReportBytes :: PackageResult -> B.ByteString
dependencyReportBytes result = canonical (SList (SAtom "dependencies" : [SList [SAtom "leaf",leafAtom (judgmentLeaf j), SList (SAtom "objects":map objectSExpr (judgmentDeps j))] | j <- judgments]))
  where judgments = sourceResultEvidence (packageSourceResult result)
leafAtom :: LeafId -> SExpr
leafAtom (LeafId raw) = SAtom raw

envelope :: PackageResult -> SExpr
envelope result = SList
  [ SAtom "lara-evidence-report",SAtom "1"
  , SList [SAtom "versions",SAtom "lara-syntax@0.11",SAtom "lara-evidence@0.1"]
  , SList [SAtom "assurance",SAtom assurance]
  , SList [SAtom "manifest",SAtom (sha256Text (packageManifestHash result))]
  , SList [SAtom "source",SAtom (sha256Text (packageSourceHash result))]
  , SList [SAtom "policy",SAtom origin,SAtom (sha256Text (packagePolicyHash result))]
  , SList (SAtom "checked":map (leafAtom . judgmentLeaf) judgments)
  , SList (SAtom "declared":map leafAtom declared)
  , SList (SAtom "replays" : [SList [SAtom "leaf",leafAtom (judgmentLeaf j),encodeRequest (judgmentRequest j),SList (SAtom "deps":map objectSExpr (judgmentDeps j))] | j <- judgments])
  , SList [SAtom "dependency-report-digest",SAtom (sha256Text (hashBytes (dependencyReportBytes result)))]
  , SList (SAtom "captured" : map objectSExpr (packageCapturedMetadata result))
  , SList [SAtom "core-replay",encodeReplayId replay]
  , SList [SAtom "core-verdict",encodeVerdict verdict]
  ]
  where
    verdict@(Verdict replay _) = sourceResultVerdict (packageSourceResult result)
    judgments = sourceResultEvidence (packageSourceResult result)
    checked = map judgmentLeaf judgments
    declared = filter (`notElem` checked) (packageDeclaredLeaves result)
    assurance | null checked = "evidence-declared"
              | null declared = "evidence-checked"
              | otherwise = "mixed"
    origin = case packagePolicyOrigin result of PackagePolicy -> "package"; VerifierPolicy -> "verifier"
evidenceIdentity :: PackageResult -> Sha256
evidenceIdentity = hashBytes . canonical . envelope
evidenceReport :: PackageResult -> SExpr
evidenceReport result = case envelope result of
  SList fields -> SList (fields ++ [SList [SAtom "evidence-digest",SAtom (sha256Text (evidenceIdentity result))]])
  value -> value
evidenceReportBytes :: PackageResult -> B.ByteString
evidenceReportBytes = canonical . evidenceReport

writeEvidenceBundle :: FilePath -> PackageResult -> IO (Either String ())
writeEvidenceBundle destination result = do
  written <- try $ bracketOnError makeTemporary removeDirectoryRecursive $ \temporary -> do
    B.writeFile (temporary </> "report.sexp") (evidenceReportBytes result)
    B.writeFile (temporary </> "core-verdict.sexp") (canonical (encodeVerdict (sourceResultVerdict (packageSourceResult result))))
    publishNoReplace temporary destination
  pure (either (Left . show) Right (written :: Either IOException ()))
  where
    makeTemporary = mkdtemp (takeDirectory destination </> ("." ++ takeFileName destination ++ ".evidence-XXXXXX"))
