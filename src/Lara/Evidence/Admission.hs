module Lara.Evidence.Admission
  ( EvidenceRejection (..), EvidenceStage (..), renderEvidenceRejection
  , BoundRequest, boundLeaf, boundRequest, bindEvidence, noEvidenceRejection
  , requiredObjects, earliestObjectLeaf, captureRejection
  , bindEvidenceMetadata, requiredObjectMetadata
  ) where

import Control.Monad (unless)
import Data.List (find)
import Data.Maybe (listToMaybe)
import Lara.AST
import Lara.Evidence.Manifest
import Lara.Evidence.Registry (implementedChecker)
import Lara.Evidence.Snapshot (Snapshot, capturedMetadata, snapshotLookup)
import Lara.Evidence.Types

data EvidenceStage = BindingStage | CaptureStage | ExtractionStage deriving (Eq,Ord,Show)
data EvidenceRejection = EvidenceRejection
  { evidenceStage :: EvidenceStage, evidenceLeaf :: LeafId, evidenceObject :: Maybe ObjectId, evidenceReason :: String
  } deriving (Eq,Show)
renderEvidenceRejection :: EvidenceRejection -> String
renderEvidenceRejection err = "leaf '" ++ lid ++ "': certified evidence " ++ stage ++ ": " ++ evidenceReason err ++ " (R8)"
  where
    LeafId lid = evidenceLeaf err
    stage = case evidenceStage err of BindingStage -> "binding"; CaptureStage -> "capture"; ExtractionStage -> "extraction"
data BoundRequest = BoundRequest { boundLeaf :: Leaf, boundRequest :: ExtractionRequest } deriving (Eq,Show)

noEvidenceRejection :: [Leaf] -> Maybe EvidenceRejection
noEvidenceRejection leaves = fmap (\leaf -> EvidenceRejection BindingStage (leafId leaf) Nothing "no evidence context")
  (find (\leaf -> leafKind leaf == Certified || leafExtraction leaf /= Nothing) leaves)

bindEvidence :: Manifest -> Policy -> [Leaf] -> Either EvidenceRejection [BoundRequest]
bindEvidence manifest policy = bindEvidenceMetadata (manifestObjects manifest) (policyEvidenceCheckers policy)

bindEvidenceMetadata :: [ObjectMeta] -> [(LeafCheckerId,CheckerVersion)] -> [Leaf] -> Either EvidenceRejection [BoundRequest]
bindEvidenceMetadata metadata allowlist = fmap concat . mapM one
  where
    one leaf = case (leafKind leaf,leafExtraction leaf) of
      (Certified,Nothing) -> failLeaf leaf Nothing "missing extraction request"
      (Certified,Just request) -> do
        let checker = requestChecker request
            version@(CheckerVersion v) = requestVersion request
        unless (implementedChecker checker version) (failLeaf leaf Nothing "unsupported checker version")
        unless (leafProvenance leaf == Checker (checkerText checker) (show v)) (failLeaf leaf Nothing "checker provenance mismatch")
        unless ((checker,version) `elem` allowlist) (failLeaf leaf Nothing "checker not allowlisted")
        mapM_ (objectBinding leaf) (requestObjects request)
        pure [BoundRequest leaf request]
      (_,Just _) -> failLeaf leaf Nothing "extraction request on noncertified leaf"
      _ -> Right []
    objectBinding leaf ident = do
      meta <- maybe (failLeaf leaf (Just ident) "undeclared evidence object") Right (find ((==ident) . objectId) metadata)
      let path = packagePathText (objectPath meta)
      unless (any (\(SourceRef r) -> takeWhile (/='#') r == path) (leafRefs leaf)) (failLeaf leaf (Just ident) "object does not resolve an existing leaf reference")
    failLeaf leaf object reason = Left (EvidenceRejection BindingStage (leafId leaf) object reason)

requiredObjects :: Manifest -> [BoundRequest] -> [ObjectMeta]
requiredObjects manifest = requiredObjectMetadata (manifestObjects manifest)
requiredObjectMetadata :: [ObjectMeta] -> [BoundRequest] -> [ObjectMeta]
requiredObjectMetadata metadata requests = filter (\o -> objectId o `elem` concatMap (requestObjects . boundRequest) requests) metadata
earliestObjectLeaf :: [BoundRequest] -> ObjectId -> Maybe LeafId
earliestObjectLeaf requests ident = leafId . boundLeaf <$> find (elem ident . requestObjects . boundRequest) requests

-- | Runtime twin of the model's capture stage (@captureStage@): every manifest
-- object a request depends on must be present in the snapshot __and__ must be
-- the manifest entry itself. 'snapshotLookup' keys on the object ID alone, so
-- without this check a snapshot captured for different metadata could be
-- replayed against a source bound to this manifest, promoting borrowed bytes
-- to evidence-checked assurance and reporting dependencies that contradict the
-- manifest. Errors are reported in manifest order at the earliest referencing
-- leaf, matching the model and the package loader's precedence.
--
-- Request-declared objects always have a referencing bound request, so the
-- comprehension below keeps exactly 'requiredObjects' and never skips a
-- requested object.
captureRejection :: Snapshot -> [ObjectMeta] -> [BoundRequest] -> Maybe EvidenceRejection
captureRejection snapshot metadata requests =
  listToMaybe
    [ rejection
    | meta <- metadata
    , let ident = objectId meta
    , Just leaf <- [earliestObjectLeaf requests ident]
    , Just rejection <- [one meta ident leaf]
    ]
  where
    one meta ident leaf = case snapshotLookup snapshot ident of
      Just object | capturedMetadata object == meta -> Nothing
      present ->
        Just
          ( EvidenceRejection
              CaptureStage
              leaf
              (Just ident)
              (maybe "missingdep" (const "metadata") present)
          )
