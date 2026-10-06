module Lara.Evidence.Types
  ( LeafCheckerId (..), CheckerVersion (..), ObjectId (..), ColumnName (..)
  , JsonToken (..), JsonPath, TermEncoding (..), CsvSelector (..), JsonSelector (..)
  , ExtractionRequest (..), requestChecker, requestVersion, requestObjects
  , checkerText, parseChecker, encodingText, parseEncoding
  ) where

import Lara.Prop (Pred)

data LeafCheckerId = CsvRow | JsonPointer deriving (Eq, Ord, Show, Enum, Bounded)
newtype CheckerVersion = CheckerVersion Integer deriving (Eq, Ord, Show)
newtype ObjectId = ObjectId String deriving (Eq, Ord, Show)
newtype ColumnName = ColumnName String deriving (Eq, Ord, Show)
newtype JsonToken = JsonToken String deriving (Eq, Ord, Show)
type JsonPath = [JsonToken]
data TermEncoding = Decimal | Text | DecimalLine deriving (Eq, Ord, Show, Enum, Bounded)
data CsvSelector = CsvSelector ColumnName TermEncoding deriving (Eq, Ord, Show)
data JsonSelector = JsonSelector JsonPath TermEncoding deriving (Eq, Ord, Show)
data ExtractionRequest
  = CsvRowRequest CheckerVersion ObjectId ColumnName String [CsvSelector] Pred
  | JsonPointerRequest CheckerVersion ObjectId [JsonSelector] Pred
  deriving (Eq, Ord, Show)

requestChecker :: ExtractionRequest -> LeafCheckerId
requestChecker CsvRowRequest{} = CsvRow
requestChecker JsonPointerRequest{} = JsonPointer
requestVersion :: ExtractionRequest -> CheckerVersion
requestVersion (CsvRowRequest v _ _ _ _ _) = v
requestVersion (JsonPointerRequest v _ _ _) = v
requestObjects :: ExtractionRequest -> [ObjectId]
requestObjects (CsvRowRequest _ o _ _ _ _) = [o]
requestObjects (JsonPointerRequest _ o _ _) = [o]
checkerText :: LeafCheckerId -> String
checkerText CsvRow = "csv-row"
checkerText JsonPointer = "json-pointer"
parseChecker :: String -> Maybe LeafCheckerId
parseChecker s = lookup s [(checkerText x,x) | x <- [minBound..maxBound]]
encodingText :: TermEncoding -> String
encodingText Decimal = "decimal"
encodingText Text = "text"
encodingText DecimalLine = "decimal-line"
parseEncoding :: String -> Maybe TermEncoding
parseEncoding s = lookup s [(encodingText x,x) | x <- [minBound..maxBound]]
