module EvidenceReportSpec (evidenceReportSpecProps) where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.Exception (IOException, try)
import qualified Data.ByteString.Char8 as B
import Data.List (isPrefixOf)
import System.Directory (createDirectory, doesDirectoryExist, listDirectory)
import System.FilePath ((</>))
import System.Exit (ExitCode (..))
import System.Process (readProcessWithExitCode)
import Test.QuickCheck
import EvidenceFixture
import Lara.TempTree
import Lara.Evidence.Load
import Lara.Evidence.Report
import Lara.Evidence.Snapshot (publishNoReplace)
import Lara.Strict (SExpr (..))
import Lara.Wire (parseSExpr)
import Lara.ExpectedJson (JValue (..), sourceResultJsonValue)

evidenceReportSpecProps :: [(String,IO Result)]
evidenceReportSpecProps =
  [ ("evidence: exact partitions and policy origin bind report identity",quickCheckResult (once (ioProperty identity)))
  , ("evidence: immutable output publication rejects existing and racing destinations",quickCheckResult (once (ioProperty transaction)))
  , ("evidence: public projections are readable but cannot update sealed carriers",quickCheckResult (once (ioProperty publicBoundary)))
  ]
  where
    identity = withTempDirectory "evidence-report" $ \root -> do
      let mixed = source ++ unlines ["leaf declared : result(7)","kind = assumed","provenance = user","refs = []"]
      writePackage root mixed policy "id,value\none,7\n" []
      package <- checkPackage root Nothing >>= checked
      B.writeFile (root </> "verifier.policy") (B.pack policy)
      verifier <- checkPackage root (Just (root </> "verifier.policy")) >>= checked
      let report = evidenceReport package
          field key = case report of SList (_:_:fields) -> [xs | SList (SAtom k:xs) <- fields,k==key]; _ -> []
          evidenceFields = case sourceResultJsonValue (packageSourceResult package) of
            JObject fields -> case lookup "evidence" fields of
              Just (JObject fields') -> fields'
              _ -> []
            _ -> []
      pure (conjoin
        [ field "assurance" === [[SAtom "mixed"]]
        , field "checked" === [[SAtom "measured"]]
        , field "declared" === [[SAtom "declared"]]
        , packagePolicyHash package === packagePolicyHash verifier
        , property (evidenceIdentity package /= evidenceIdentity verifier)
        , parseSExpr (B.unpack (evidenceReportBytes package)) === Right report
        , lookup "assurance" evidenceFields === Just (JString "mixed")
        , lookup "checked" evidenceFields === Just (JArray [JString "measured"])
        , lookup "declared" evidenceFields === Just (JArray [JString "declared"])
        ])
    transaction = withTempDirectory "evidence-publish" $ \root -> do
      writePackage root source policy "id,value\none,7\n" []
      package <- checkPackage root Nothing >>= checked
      let destination = root </> "bundle"
      first <- writeEvidenceBundle destination package
      report <- B.readFile (destination </> "report.sexp")
      second <- writeEvidenceBundle destination package
      unchanged <- B.readFile (destination </> "report.sexp")
      entries <- listDirectory root
      createDirectory (root </> "race-a")
      createDirectory (root </> "race-b")
      doneA <- newEmptyMVar
      doneB <- newEmptyMVar
      _ <- forkIO (attempt (root </> "race-a") (root </> "race-out") >>= putMVar doneA)
      _ <- forkIO (attempt (root </> "race-b") (root </> "race-out") >>= putMVar doneB)
      raceA <- takeMVar doneA
      raceB <- takeMVar doneB
      exists <- doesDirectoryExist (root </> "race-out")
      pure (conjoin
        [ first === Right ()
        , property (isLeft second)
        , unchanged === report
        , property (not (any (".bundle.evidence-" `isPrefixOf`) entries))
        , property (raceA /= raceB && exists)
        ])
    publicBoundary = withTempDirectory "evidence-public-client" $ \root -> do
      let imports =
            [ "module PublicClient where"
            , "import Lara.Evidence.Admission"
            , "import Lara.Evidence.Load"
            , "import Lara.Evidence.Manifest"
            , "import Lara.Evidence.Runner"
            , "import Lara.Evidence.Snapshot"
            ]
          projections =
            [ ("PackageResult", ["packageSourceResult", "packageManifestHash", "packageSourceHash", "packagePolicyHash", "packagePolicyOrigin", "packageDeclaredLeaves", "packageCapturedMetadata"])
            , ("ObjectMeta", ["objectId", "objectPath", "objectLength", "objectDigest"])
            , ("Manifest", ["manifestPaper", "manifestSource", "manifestPolicy", "manifestObjects"])
            , ("BoundRequest", ["boundLeaf", "boundRequest"])
            , ("CapturedObject", ["capturedMetadata", "capturedBytes"])
            , ("Snapshot", ["snapshotMetadata"])
            , ("SuccessfulJudgment", ["judgmentLeaf", "judgmentRequest", "judgmentProp", "judgmentDeps"])
            ]
          compile name body = do
            let client = root </> name ++ ".hs"
            writeFile client (unlines (imports ++ body))
            readProcessWithExitCode "cabal"
              ["exec", "--", "ghc", "-fno-code", "-fforce-recomp", "-package", "lara", "-outputdir", root, client] ""
          positive = concat
            [ [field ++ "Client x = " ++ field ++ " x"]
            | (_, fields) <- projections, field <- fields
            ]
      (positiveCode, _, positiveError) <- compile "Positive" positive
      negative <- mapM (\(carrier, field) -> do
        (code, _, err) <- compile field
          ["forge :: " ++ carrier ++ " -> " ++ carrier, "forge x = x { " ++ field ++ " = " ++ field ++ " x }"]
        pure (counterexample (field ++ ": " ++ err)
          (code /= ExitSuccess)))
        [(carrier, field) | (carrier, fields) <- projections, field <- fields]
      pure (conjoin (counterexample positiveError (positiveCode === ExitSuccess) : negative))
    checked = either (fail . renderPackageError) pure
    attempt from to = do r <- try (publishNoReplace from to) :: IO (Either IOException ()); pure (case r of Right () -> True; Left _ -> False)
    isLeft (Left _) = True
    isLeft _ = False
