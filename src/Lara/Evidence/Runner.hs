module Lara.Evidence.Runner
  ( SuccessfulJudgment, runEvidence, judgmentLeaf, judgmentRequest, judgmentProp, judgmentDeps
  , EvidenceObservation, replayTypedEvidence
  ) where

import Control.Monad (unless)
import qualified Data.Map.Lazy as Map
import Lara.AST (Leaf (..), LeafId)
import Lara.Evidence.Admission
import Lara.Evidence.Internal
import Lara.Evidence.Manifest
import Lara.Evidence.Registry
import Lara.Evidence.Snapshot
import Lara.Evidence.Types
import Lara.Prop (Prop, equiv)

runEvidence :: Snapshot -> [BoundRequest] -> Either EvidenceRejection [SuccessfulJudgment]
runEvidence snapshot requests = mapM one requests
  where
    decoded = Map.fromList
      [ ((ident,requestChecker request), prepareBytesObject (requestChecker request) (capturedBytes object))
      | bound <- requests
      , let request = boundRequest bound
      , ident <- requestObjects request
      , Just object <- [snapshotLookup snapshot ident]
      ]
    one bound = do
      let leaf = boundLeaf bound
          request = boundRequest bound
          failRun object reason = Left (EvidenceRejection ExtractionStage (leafId leaf) object reason)
      objects <- mapM (\ident -> maybe (failRun (Just ident) "missing captured dependency") Right (snapshotLookup snapshot ident)) (requestObjects request)
      supplied <- mapM (\object ->
        let meta = capturedMetadata object
            ident = objectId meta
        in case Map.lookup (ident,requestChecker request) decoded of
          Nothing -> failRun (Just ident) "missing captured dependency"
          Just result -> fmap (meta,) (either (failRun (Just ident)) Right result)) objects
      (ident,normalizedRequest,output,deps) <- compareExtraction bound supplied
      pure (SuccessfulJudgment ident normalizedRequest output deps)
judgmentLeaf :: SuccessfulJudgment -> LeafId
judgmentLeaf (SuccessfulJudgment leaf _ _ _) = leaf
judgmentRequest :: SuccessfulJudgment -> ExtractionRequest
judgmentRequest (SuccessfulJudgment _ request _ _) = request
judgmentProp :: SuccessfulJudgment -> Prop
judgmentProp (SuccessfulJudgment _ _ prop _) = prop
judgmentDeps :: SuccessfulJudgment -> [ObjectMeta]
judgmentDeps (SuccessfulJudgment _ _ _ deps) = deps

type EvidenceObservation = (LeafId, ExtractionRequest, Prop, [ObjectMeta])

-- The differential adapter uses typed payloads, but the selector and independent
-- output comparison are the same pure production operations.
replayTypedEvidence
  :: [ObjectMeta]
  -> [(ObjectId, Either String (ObjectMeta,TypedObject))]
  -> [BoundRequest]
  -> Either EvidenceRejection [EvidenceObservation]
replayTypedEvidence metadata snapshot requests = do
  mapM_ capture [(meta,leaf) | meta <- metadata, Just leaf <- [earliestObjectLeaf requests (objectId meta)]]
  mapM one requests
  where
    prepared = Map.fromList
      [ ((ident,requestChecker request), fmap (meta,) (prepareRequestObject (requestChecker request) payload))
      | bound <- requests
      , let request = boundRequest bound
      , ident <- requestObjects request
      , Just (Right (meta,payload)) <- [lookup ident snapshot]
      ]
    capture (expected,leaf) =
      let ident = objectId expected
          reject reason = Left (EvidenceRejection CaptureStage leaf (Just ident) reason)
      in case lookup ident snapshot of
        Nothing -> reject "missingdep"
        Just (Left reason) -> reject reason
        Just (Right (actual,_)) -> unless (actual == expected) (reject "metadata")
    one bound = do
      let leaf = boundLeaf bound
          request = boundRequest bound
          reject object reason = Left (EvidenceRejection ExtractionStage (leafId leaf) object reason)
      supplied <- mapM (\ident -> case Map.lookup (ident,requestChecker request) prepared of
        Just result -> either (reject (Just ident)) Right result
        Nothing -> reject (Just ident) "missingdep") (requestObjects request)
      compareExtraction bound supplied

compareExtraction :: BoundRequest -> [(ObjectMeta,PreparedObject)] -> Either EvidenceRejection EvidenceObservation
compareExtraction bound supplied = do
  let leaf = boundLeaf bound
      request = boundRequest bound
      reject object reason = Left (EvidenceRejection ExtractionStage (leafId leaf) object reason)
  output <- case supplied of
    [(meta,payload)] -> either (reject (Just (objectId meta))) Right (runPreparedRegistry request payload)
    _ -> reject Nothing "invalid dependency count"
  unless (equiv output (leafProp leaf)) (reject Nothing "extracted proposition mismatch")
  pure (leafId leaf,request,output,map fst supplied)
