module Lara.Process.Source.Evidence
  ( ModeledJudgment, runModeledEvidence, lookupCapture
  , modeledJudgmentLeaf, modeledJudgmentRequest, modeledJudgmentProp, modeledJudgmentDependencies
  ) where

import Data.Bifunctor (first)
import Lara.AST (Policy (..), Leaf, LeafId)
import qualified Lara.Evidence.Admission as A
import Lara.Evidence.Registry
import Lara.Evidence.Runner (TypedReplayFault (..), replayTypedEvidenceWith)
import Lara.Evidence.Types (ObjectId, ExtractionRequest)
import Lara.Prop (Prop)
import Lara.Process.Source.Types

-- Only admission can mint a successful modeled judgment.
newtype ModeledJudgment = ModeledJudgment EvidenceJudgment deriving (Eq, Show)
modeledJudgmentLeaf :: ModeledJudgment -> LeafId
modeledJudgmentLeaf (ModeledJudgment j) = evidenceLeaf j
modeledJudgmentRequest :: ModeledJudgment -> ExtractionRequest
modeledJudgmentRequest (ModeledJudgment j) = evidenceRequest j
modeledJudgmentProp :: ModeledJudgment -> Prop
modeledJudgmentProp (ModeledJudgment j) = evidenceProp j
modeledJudgmentDependencies :: ModeledJudgment -> [ObjectMeta]
modeledJudgmentDependencies (ModeledJudgment j) = evidenceDependencies j

lookupCapture :: EvidenceCapture -> ObjectId -> Either String (ObjectMeta,TypedObject)
lookupCapture capture ident = case lookup ident (captureSnapshot capture) of
  Nothing -> Left "missingdep"
  Just (Left reason) -> Left reason
  Just (Right object@(metadata,_))
    | objectId metadata == ident -> Right object
    | otherwise -> Left "metadata"

runModeledEvidence :: EvidenceCapture -> Policy -> [Leaf] -> Either EvidenceError [ModeledJudgment]
runModeledEvidence capture policy leaves = do
  requests <- first (\failure -> EvidenceError EvidenceBindingStage (A.evidenceLeaf failure) (A.evidenceObject failure) "binding") $
    A.bindEvidencePaths [(objectId m,objectPath m) | m <- captureManifest capture]
      (policyEvidenceCheckers policy) leaves
  results <- first normalize $
    replayTypedEvidenceWith objectId prepareModeledObject runModeledRegistry
      (captureManifest capture) (captureSnapshot capture) requests
  pure [ModeledJudgment (EvidenceJudgment leaf request prop dependencies) |
    (leaf,request,prop,dependencies) <- results]
  where
    normalize fault = case fault of
      TypedCaptureFault leaf ident reason -> EvidenceError EvidenceCaptureStage leaf (Just ident) reason
      TypedExtractionFault leaf _ reason -> EvidenceError EvidenceExtractionStage leaf Nothing (case reason of
        CSVSelectionFailure -> "csv-selection"
        JSONSelectionFailure -> "json-selection"
        WrongPayload -> "payload-type")
      TypedMismatch leaf -> EvidenceError EvidenceExtractionStage leaf Nothing "mismatch"
      TypedPayloadCount leaf -> EvidenceError EvidenceExtractionStage leaf Nothing "payload-type"
      TypedMissingDependency leaf _ -> EvidenceError EvidenceExtractionStage leaf Nothing "payload-type"
