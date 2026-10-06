module Lara.Evidence.Registry
  ( TypedObject (..), runTypedRegistry, runRegistry, implementedChecker
  , PreparedObject, prepareTypedObject, runPreparedRegistry
  , prepareRequestObject, prepareBytesObject
  ) where

import qualified Data.ByteString as B
import Lara.Evidence.CSV
import Lara.Evidence.JSON
import Lara.Evidence.Types
import Lara.Prop (Prop)

data TypedObject = CsvPayload CsvTable | JsonPayload JsonValue deriving (Eq,Show)
data PreparedObject = PreparedCSV CsvIndex | PreparedJSON ValidatedJSON
prepareTypedObject :: TypedObject -> Either String PreparedObject
prepareTypedObject (CsvPayload table) = PreparedCSV <$> indexCSV table
prepareTypedObject (JsonPayload tree) = PreparedJSON <$> validateJSON tree
prepareRequestObject :: LeafCheckerId -> TypedObject -> Either String PreparedObject
prepareRequestObject CsvRow payload@CsvPayload{} = prepareTypedObject payload
prepareRequestObject JsonPointer payload@JsonPayload{} = prepareTypedObject payload
prepareRequestObject _ _ = Left "wrong checker object type"
implementedChecker :: LeafCheckerId -> CheckerVersion -> Bool
implementedChecker _ (CheckerVersion v) = v == 1

prepareBytesObject :: LeafCheckerId -> B.ByteString -> Either String PreparedObject
prepareBytesObject CsvRow = fmap PreparedCSV . decodeCSVIndex
prepareBytesObject JsonPointer = fmap PreparedJSON . decodeValidatedJSON
runTypedRegistry :: ExtractionRequest -> TypedObject -> Either String Prop
runTypedRegistry request payload = prepareRequestObject (requestChecker request) payload >>= runPreparedRegistry request
runPreparedRegistry :: ExtractionRequest -> PreparedObject -> Either String Prop
runPreparedRegistry request payload
  | not (implementedChecker (requestChecker request) (requestVersion request)) = Left "unsupported checker version"
  | otherwise = case (request,payload) of
      (CsvRowRequest _ _ key raw selectors predicate,PreparedCSV table) -> selectIndexedCSV table key raw selectors predicate
      (JsonPointerRequest _ _ selectors predicate,PreparedJSON tree) -> selectValidatedJSON tree selectors predicate
      _ -> Left "wrong checker object type"
runRegistry :: ExtractionRequest -> B.ByteString -> Either String Prop
runRegistry request bytes = prepareBytesObject (requestChecker request) bytes >>= runPreparedRegistry request
