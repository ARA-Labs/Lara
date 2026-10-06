module EvidenceReportSpec (evidenceReportSpecProps) where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.Exception (IOException, try)
import qualified Data.ByteString.Char8 as B
import Data.List (isPrefixOf)
import System.Directory (createDirectory, doesDirectoryExist, listDirectory)
import System.FilePath ((</>))
import Test.QuickCheck
import EvidenceFixture
import Lara.TempTree
import Lara.Evidence.Load
import Lara.Evidence.Manifest
import Lara.Evidence.Report
import Lara.Evidence.Snapshot (publishNoReplace)
import Lara.Strict (SExpr (..))
import Lara.Wire (parseSExpr)
import Lara.ExpectedJson (JValue (..), sourceResultJsonValue)

evidenceReportSpecProps :: [(String,IO Result)]
evidenceReportSpecProps =
  [ ("evidence: exact partitions and policy origin bind report identity",quickCheckResult (once (ioProperty identity)))
  , ("evidence: immutable output publication rejects existing and racing destinations",quickCheckResult (once (ioProperty transaction)))
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
    checked = either (fail . renderPackageError) pure
    attempt from to = do r <- try (publishNoReplace from to) :: IO (Either IOException ()); pure (case r of Right () -> True; Left _ -> False)
    isLeft (Left _) = True
    isLeft _ = False
