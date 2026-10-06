module EvidenceExtractSpec (evidenceExtractSpecProps) where

import Test.QuickCheck
import qualified Data.ByteString.Char8 as B
import Lara.Evidence.Types
import Lara.Evidence.CSV
import Lara.Evidence.JSON
import Lara.Evidence.Decimal
import Lara.Evidence.Syntax
import Lara.Prop (Prop (..), Term (..), Pred (..))
import Lara.Strict (SExpr (..))
import Lara.Syntax (parseProgram,parsePolicy,printProgram,printPolicy)

evidenceExtractSpecProps :: [(String,IO Result)]
evidenceExtractSpecProps =
  [ ("evidence: exact bounded decimal normalization", quickCheckResult (once decimals))
  , ("evidence: strict CSV full-table and unique-row selection", quickCheckResult (once csv))
  , ("evidence: JSON duplicates/scalar/index/decimal-line boundaries", quickCheckResult (once json))
  , ("evidence: request and source codecs preserve concrete syntax", quickCheckResult (once syntax))
  ]
  where
    decimals = conjoin
      [ decimalTerm "-0.000e+12" === Right (TNum "0")
      , decimalTerm "3.0154159758239985e-3" === Right (TNum "0.0030154159758239985")
      , property (isLeft (decimalTerm "1e257"))
      , property (isLeft (decimalTerm "1/3"))
      , property (isLeft (decimalTerm (replicate 257 '1')))
      , property (isLeft (decimalTerm "1e0000"))
      ]
    csv = conjoin
      [ decodeCSV (B.pack "id,value\n0,\"a,b\"\n") === Right (CsvTable [ColumnName "id",ColumnName "value"] [["0","a,b"]])
      , decodeCSV (B.pack "id,value\n0,\"a\r\nb\"\r\n") === Right (CsvTable [ColumnName "id",ColumnName "value"] [["0","a\r\nb"]])
      , decodeCSV (B.pack ",value\n0,7\n") === Right (CsvTable [ColumnName "",ColumnName "value"] [["0","7"]])
      , property (isLeft (decodeCSV (B.pack "id\n\255")))
      , property (isLeft (decodeCSV (B.pack ("id\n" ++ concat (replicate 100001 "one\n")))))
      , property (isLeft (decodeCSV (B.pack (concat (replicate 256 "x,") ++ "x\n"))))
      , property (isLeft (decodeCSV (B.pack "id,value\n0,yes\n1,ragged,extra\n")))
      , property (isLeft (decodeCSV (B.pack "id,id\n0,1\n")))
      , property (isLeft (decodeCSV (B.pack "a,b\r0,1")))
      , property (isLeft (decodeCSV (B.pack "a,b\n0,\"ok\"bad\n")))
      , property (isLeft (selectCSV (CsvTable [ColumnName "id",ColumnName "n"] [["0","7"],["0","8"]]) (ColumnName "id") "0" [CsvSelector (ColumnName "n") Decimal] (Pred "p")))
      ]
    json = conjoin
      [ property (isLeft (decodeJSON (B.pack "{\"x\":1,\"x\":2}")))
      , property (isLeft (decodeJSON (B.pack "\"\\ud800\"")))
      , property (isLeft (decodeJSON (B.pack "[01]")))
      , property (isLeft (decodeJSON (B.pack "\"\255\"")))
      , property (isLeft (decodeJSON (B.pack (replicate 129 '[' ++ "0" ++ replicate 129 ']'))))
      , property (isLeft (selectJSON (JsonArray (replicate 100000 JsonNull)) [] (Pred "p")))
      , selectJSON (JsonObject [(JsonToken "x",JsonString "3.2e-2\n")]) [JsonSelector [JsonToken "x"] DecimalLine] (Pred "p") === Right (Prop (Pred "p") [TNum "0.032"])
      , property (isLeft (selectJSON (JsonNumber "1") [JsonSelector [] DecimalLine] (Pred "p")))
      , property (isLeft (selectJSON (JsonString "1\n\n") [JsonSelector [] DecimalLine] (Pred "p")))
      , selectJSON (JsonObject [(JsonToken "01",JsonNumber "7")]) [JsonSelector [JsonToken "01"] Decimal] (Pred "p") === Right (Prop (Pred "p") [TNum "7"])
      , property (isLeft (selectJSON (JsonArray [JsonNumber "7"]) [JsonSelector [JsonToken "00"] Decimal] (Pred "p")))
      ]
    syntax = conjoin
      [ decodeRequest (encodeRequest request) === Right request
      , parsePointer (renderPointer [JsonToken "a/b",JsonToken "~0"]) === Right [JsonToken "a/b",JsonToken "~0"]
      , property (isLeft (decodeCheckers (SList [SAtom "checkers",SList [SAtom "csv-row",SAtom "1"],SList [SAtom "csv-row",SAtom "1"]])))
      , property (isLeft (parseProgram (source ++ "  extract = " ++ requestText ++ "\n")))
      , property (isLeft (parsePolicy (policy ++ "evidence-checkers = (checkers)\n")))
      , case parseProgram source of Left err -> counterexample (show err) False; Right p -> parseProgram (printProgram p) === Right p
      , case parsePolicy policy of Left err -> counterexample (show err) False; Right p -> parsePolicy (printPolicy p) === Right p
      ]
    request = CsvRowRequest (CheckerVersion 1) (ObjectId "data") (ColumnName "id") "0" [CsvSelector (ColumnName "value") Decimal] (Pred "p")
    requestText = "(csv-row 1 data (key id 0) (select (value decimal)) (predicate p))"
    source = unlines ["artifact test at sha256:source","policy p","use backends []","leaf l : p(7)","kind = certified","provenance = checker(csv-row, 1)","refs = [data.csv]","extract = " ++ requestText]
    policy = unlines ["policy p","pred p(Num)","evidence-checkers = (checkers (csv-row 1))"]
    isLeft (Left _) = True
    isLeft _ = False
