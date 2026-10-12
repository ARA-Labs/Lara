module Lara.Evidence.Runner
  ( SuccessfulJudgment, runEvidence, judgmentLeaf, judgmentRequest, judgmentProp, judgmentDeps
  , EvidenceObservation, replayTypedEvidence
  , TypedReplayFault (..), replayTypedEvidenceWith
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
replayTypedEvidence metadata snapshot requests =
  either (Left . convert) Right $
    replayTypedEvidenceWith objectId prepareRequestObject runPreparedRegistry
      metadata snapshot requests
  where
    convert fault = case fault of
      TypedCaptureFault leaf ident reason -> EvidenceRejection CaptureStage leaf (Just ident) reason
      TypedExtractionFault leaf ident reason -> EvidenceRejection ExtractionStage leaf ident reason
      TypedMismatch leaf -> EvidenceRejection ExtractionStage leaf Nothing "extracted proposition mismatch"
      TypedPayloadCount leaf -> EvidenceRejection ExtractionStage leaf Nothing "invalid dependency count"
      TypedMissingDependency leaf ident -> EvidenceRejection ExtractionStage leaf (Just ident) "missingdep"

data TypedReplayFault failure
  = TypedCaptureFault LeafId ObjectId String
  | TypedExtractionFault LeafId (Maybe ObjectId) failure
  | TypedMismatch LeafId
  | TypedPayloadCount LeafId
  | TypedMissingDependency LeafId ObjectId
  deriving (Eq, Show)

-- Metadata-independent replay: capture every requested manifest row first,
-- then extract in leaf order. Snapshot lookup is deliberately first-match.
replayTypedEvidenceWith
  :: Eq metadata
  => (metadata -> ObjectId)
  -> (LeafCheckerId -> TypedObject -> Either failure PreparedObject)
  -> (ExtractionRequest -> PreparedObject -> Either failure Prop)
  -> [metadata]
  -> [(ObjectId, Either String (metadata,TypedObject))]
  -> [BoundRequest]
  -> Either (TypedReplayFault failure) [(LeafId,ExtractionRequest,Prop,[metadata])]
replayTypedEvidenceWith identOf prepare extract metadata snapshot requests = do
  mapM_ capture [(meta,leaf) | meta <- metadata, Just leaf <- [earliestObjectLeaf requests (identOf meta)]]
  mapM one requests
  where
    prepared = Map.fromList
      [ ((ident,requestChecker request), fmap (meta,) (prepare (requestChecker request) payload))
      | bound <- requests
      , let request = boundRequest bound
      , ident <- requestObjects request
      , Just (Right (meta,payload)) <- [lookup ident snapshot]
      ]
    capture (expected,leaf) =
      let ident = identOf expected
          reject reason = Left (TypedCaptureFault leaf ident reason)
      in case lookup ident snapshot of
        Nothing -> reject "missingdep"
        Just (Left reason) -> reject reason
        Just (Right (actual,_)) -> unless (identOf actual == ident && actual == expected) (reject "metadata")
    one bound = do
      let leaf = boundLeaf bound
          leafIdent = leafId leaf
          request = boundRequest bound
      supplied <- mapM (\ident -> case Map.lookup (ident,requestChecker request) prepared of
        Just result -> either (Left . TypedExtractionFault leafIdent (Just ident)) Right result
        Nothing -> Left (TypedMissingDependency leafIdent ident)) (requestObjects request)
      output <- case supplied of
        [(meta,payload)] -> either (Left . TypedExtractionFault leafIdent (Just (identOf meta))) Right (extract request payload)
        _ -> Left (TypedPayloadCount leafIdent)
      unless (equiv output (leafProp leaf)) (Left (TypedMismatch leafIdent))
      pure (leafIdent,request,output,map fst supplied)

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
