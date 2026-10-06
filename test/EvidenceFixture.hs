module EvidenceFixture (writePackage, source, policy, request, requireRight) where

import qualified Data.ByteString.Char8 as B
import System.FilePath ((</>))
import Lara.Evidence.Manifest
import Lara.Strict (SExpr (..))
import Lara.Wire (printSExpr)

requireRight :: Show e => Either e a -> IO a
requireRight = either (fail . show) pure
request :: String
request = "(csv-row 1 data (key id one) (select (value decimal)) (predicate result))"
source :: String
source = unlines
  ["artifact test at sha256:independent-source", "policy p", "use backends []"
  ,"leaf measured : result(7)","kind = certified", "provenance = checker(csv-row, 1)"
  ,"refs = [data.csv]", "extract = " ++ request]
policy :: String
policy = unlines ["policy p","pred result(Num)","evidence-checkers = (checkers (csv-row 1))"]
writePackage :: FilePath -> String -> String -> String -> [(String,String)] -> IO ()
writePackage root program policyText dataText extras = do
  let files = [("paper","PAPER.md","original paper"),("source","source.lara",program),("policy","p.policy.lara",policyText),("data","data.csv",dataText)] ++ [("extra"++show n,path,body) | (n,(path,body)) <- zip [(0::Int)..] extras]
      object (ident,path,body) = SList [SAtom "object",SAtom ident,SAtom path,SAtom (show (B.length (B.pack body))),SAtom (sha256Text (hashBytes (B.pack body)))]
      manifest = SList [SAtom "lara-evidence",SAtom "1",SList [SAtom "paper",SAtom "paper"],SList [SAtom "source",SAtom "source"],SList [SAtom "policy",SAtom "policy"],SList (SAtom "objects":map object files)]
  mapM_ (\(_,path,body) -> B.writeFile (root </> path) (B.pack body)) files
  B.writeFile (root </> "lara-evidence.sexp") (B.pack (printSExpr manifest ++ "\n"))
