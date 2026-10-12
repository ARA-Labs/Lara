module Lara.Process.Source
  ( AcceptedObservation, checkSource, observeSource, QueryOutcome (..)
  , observationInput, observationAcceptedSource, observationResult
  , observationAF, observationNames, observationEdges, observationSupport
  , observationHoles, publicStatus, blockedClosure, replayCompatible
  , observationCarriers, observationBlockedArguments, observationNodeLabel
  ) where

import Control.Monad (unless)
import Data.List (find, sort)
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Map.Lazy as Map
import qualified Data.IntMap.Lazy as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Numeric.Natural (Natural)
import qualified Lara.AST as A
import Lara.Admission (admissionRejectionLeaf)
import Lara.Blocked (carrierReference, carrierChecked, blockedArgs, carriers, pruneChecked, groupConsistent)
import Lara.Check (cuNodes, cuProgram)
import Lara.Driver.Internal (declaredTypedHole, holeRows)
import Lara.Elaborate
import Lara.Grounded (AF (..), Claim (..), grounded, labelWithGrounded, statusWithLabels)
import Lara.Prop (Prop, nf)
import Lara.SupportTerm (cnConclusion)
import Lara.Reporting (nodeArgIds)
import Lara.Runtime (runtimeAF)
import Lara.Wire (PublicStatus (..), HoleRow (..), HoleObligation (..))
import qualified Lara.Strict as St
import qualified Lara.Strict.ND as ND
import qualified Lara.Strict.RA as RA
import qualified Lara.Strict.Ord as Ord
import qualified Lara.Strict.Insp as Insp
import Lara.Process.Source.Types
import Lara.Process.Source.Diagnostic
import Lara.Process.Source.CoreDiagnostic (CoreBackend (..), coreError, corePosition)
import qualified Lara.Replay as Replay

-- A single accepted checker branch owns all projections. Neither the source,
-- its admission audit, nor its checked cache can be swapped independently.
data AcceptedObservation = AcceptedObservation
  { retainedInput :: SourceInput
  , retainedAccepted :: AcceptedSource
  , retainedResult :: SourceResult
  , retainedAF :: AF
  , retainedNaturalCarriers :: ([Natural],[Natural])
  , retainedNames :: [A.ArgId]
  , retainedEdges :: [(Natural,Natural)]
  , retainedHoles :: [SourceHole]
  , retainedNaturalBlocked :: [Natural]
  , retainedBlockedNodes :: IntSet.IntSet
  , retainedLabels :: IntMap.IntMap A.Label
  , retainedSupport :: Map.Map Prop [Int]
  , retainedNaturalSupport :: Map.Map Prop [Natural]
  }
observationInput :: AcceptedObservation -> SourceInput
observationInput = retainedInput
observationAcceptedSource :: AcceptedObservation -> AcceptedSource
observationAcceptedSource = retainedAccepted
observationResult :: AcceptedObservation -> SourceResult
observationResult = retainedResult
observationAF :: AcceptedObservation -> AF
observationAF = retainedAF
observationNames :: AcceptedObservation -> [A.ArgId]
observationNames = retainedNames
observationEdges :: AcceptedObservation -> [(Natural,Natural)]
observationEdges = retainedEdges
observationSupport :: AcceptedObservation -> Prop -> [Natural]
observationSupport observation query = Map.findWithDefault [] (nf query) (retainedNaturalSupport observation)
observationHoles :: AcceptedObservation -> [SourceHole]
observationHoles = retainedHoles
observationCarriers :: AcceptedObservation -> ([Natural],[Natural])
observationCarriers = retainedNaturalCarriers
observationBlockedArguments :: AcceptedObservation -> [Natural]
observationBlockedArguments = retainedNaturalBlocked
observationNodeLabel :: AcceptedObservation -> Natural -> Maybe A.Label
observationNodeLabel observation node
  | node > fromIntegral (maxBound :: Int) = Nothing
  | otherwise = IntMap.lookup (fromIntegral node) (retainedLabels observation)

blockedClosure :: AcceptedObservation -> [Prop] -> [Prop]
blockedClosure observation = filter blocked
  where blocked query = any (`IntSet.member` retainedBlockedNodes observation)
          (Map.findWithDefault [] (nf query) (retainedSupport observation))
publicStatus :: AcceptedObservation -> Prop -> PublicStatus
publicStatus observation query = overlay (statusWithLabels label (Claim support []))
  where
    support = Map.findWithDefault [] (nf query) (retainedSupport observation)
    label index = IntMap.findWithDefault A.LUndec index (retainedLabels observation)
    overlay = if any (`IntSet.member` retainedBlockedNodes observation) support then EvidenceBlocked else Published

data QueryOutcome = QueryRejected SourceRejection | QueryAccepted PublicStatus deriving (Eq, Show)
observeSource :: SourceInput -> [Prop] -> (Either SourceRejection AcceptedObservation,[(Prop,QueryOutcome)])
observeSource input queries = (outcome,[(query,case outcome of
  Left rejection -> QueryRejected rejection
  Right observation -> QueryAccepted (publicStatus observation query)) | query <- queries])
  where outcome = checkSource input

replayCompatible :: SourceInput -> Either ReplayError ()
replayCompatible input = do
  unless (replayCore replay == CoreVersion "lara-core@0.3") (Left (UnsupportedCore (replayCore replay)))
  unless (replayPolicy replay == A.policyId policy && A.programPolicy program == A.policyId policy) (Left ReplayPolicyMismatch)
  unless (selected == A.programBackends program) (Left BackendMismatch)
  unless (unique (map fst selected)) (Left DuplicateBackend)
  case find (not . supported) (replayBackends replay) of
    Just backend -> Left (UnsupportedBackend backend)
    Nothing -> Right ()
  unless (unique theories) (Left DuplicateTheory)
  unless (replayTheories replay == sort theories) (Left TheoryMismatch)
  unless (replayArtifact replay == A.programDigest program) (Left ArtifactMismatch)
  where
    replay = sourceReplay input
    policy = sourcePolicy input
    program = sourceProgram input
    selected = [(b,v) | BackendIdentity b (BackendVersion v) <- replayBackends replay]
    theories = map fst (A.policyTheories policy)
    supported (BackendIdentity (A.BackendId b) (BackendVersion v)) =
      (b,v) `elem` [(St.backendName ident,show (St.backendVersion ident)) |
        ident <- [ND.ndBackendId,RA.raBackendId,Ord.ordBackendId,Insp.inspBackendId]]
    unique [] = True
    unique (x:xs) = x `notElem` xs && unique xs

checkSource :: SourceInput -> Either SourceRejection AcceptedObservation
checkSource input = do
  either (Left . ReplayRejection) Right (replayCompatible input)
  prepared <- either (Left . SourceRejection . sourceInvalidDiagnostic (sourceProgram input)) Right
    (prepareInquirySourceStructure (sourceProgram input) (sourcePolicy input))
  structural <- case prepared of
    Left rejection -> Left (SourceRejection (SourceDiagnostic (Structural (AdmissionRejected (admissionRejectionLeaf rejection)))))
    Right value -> Right value
  -- Source assembly's group decision precedes every capture and extraction.
  let declared = structuralDeclared structural
  case if A.unitGroupMode declared == A.RejectOnConflict
       then find (not . groupConsistent declared) (A.unitGroups declared) else Nothing of
    Just (A.DupGroup ident _) -> Left (SourceRejection (SourceDiagnostic (GroupConflict ident)))
    Nothing -> Right ()
  source <- either (Left . SourceRejection . EvidenceDiagnostic) Right
    (admitModeledSourceEvidence (fromMaybe (EvidenceCapture [] []) (sourceCapture input)) structural)
  let result = runInquirySourceCheck source
  accepted <- either (Left . checkFailureRejection) Right (sourceResultDecision result)
  case firstUnselected (sourceReplay input) (A.unitArgs (acceptedSourceDeclared accepted)) of
    Just rejection -> Left rejection
    Nothing -> Right ()
  case sourceCapture input of
    Just _ -> Right ()
    Nothing -> case find needsEvidence [leaf | A.DeclLeaf leaf <- A.programDecls (acceptedSourceSemantic accepted)] of
      Just leaf -> Left (MissingEvidence (A.leafId leaf))
      Nothing -> Right ()
  let checked = acceptedSourceChecked accepted
      graph = runtimeAF (cuProgram checked)
      extension = grounded graph
      pruned = acceptedSourcePrune accepted
      carrier = carriers pruned (declaredTypedHole (acceptedSourceDeclared accepted)) checked
      declaredUnit = acceptedSourceDeclared accepted
      checkedUnit = pruneChecked pruned
      blocked
        | A.unitArgs declaredUnit == A.unitArgs checkedUnit
        , A.unitAttacks declaredUnit == A.unitAttacks checkedUnit = Set.empty
        | otherwise = blockedArgs pruned carrier
      blockedNodes
        | Set.null blocked = IntSet.empty
        | otherwise = IntSet.fromList [node | (node,declaredIndex) <- zip [0..] (carrierChecked carrier),Set.member declaredIndex blocked]
      support = Map.map reverse (Map.fromListWith (++)
        [(nf (cnConclusion node),[index]) | (index,node) <- zip [0..] (cuNodes checked)])
      holes = [SourceHole (fromIntegral (hrIndex hole)) (hrArgId hole)
        [SourceHoleObligation (hoQuestion obligation) (map corePosition (hoSites obligation)) | obligation <- hrObligations hole]
        (map fromIntegral (hrAttacks hole)) | hole <- holeRows pruned checked]
  pure AcceptedObservation
    { retainedInput = input, retainedAccepted = accepted, retainedResult = result
    , retainedAF = graph, retainedNaturalCarriers = (map fromIntegral (carrierReference carrier),map fromIntegral (carrierChecked carrier))
    , retainedNames = nodeArgIds (pruneChecked pruned) checked
    , retainedEdges = [(fromIntegral a,fromIntegral b) | a <- afArgs graph,b <- afArgs graph,afAttack graph a b]
    , retainedHoles = holes, retainedNaturalBlocked = map fromIntegral (Set.toAscList blocked), retainedBlockedNodes = blockedNodes
    , retainedLabels = IntMap.fromList [(index,labelWithGrounded graph extension index) | index <- afArgs graph]
    , retainedSupport = support, retainedNaturalSupport = Map.map (map fromIntegral) support
    }
  where needsEvidence leaf = A.leafKind leaf == A.Certified || A.leafExtraction leaf /= Nothing

firstUnselected :: ReplayIdentity -> [(A.ArgId,A.SupportTerm)] -> Maybe SourceRejection
firstUnselected replay arguments = listToMaybe
  [UnselectedCertificate index argument backend | (index,(argument,term)) <- zip [0..] arguments,
    Just backend <- [visit term]]
  where
    selected = [(backend,version) | BackendIdentity backend (BackendVersion version) <- replayBackends replay]
    visit A.SLeaf{} = Nothing
    visit (A.SRule _ _ premises discharges _ assurance) =
      case assurance of
        A.AssuranceCert certificate
          | (A.certBackend certificate,show (A.certVersion certificate)) `notElem` selected ->
              Just (CoreBackend (A.certBackend certificate) (fromInteger (A.certVersion certificate)))
        _ -> listToMaybe [backend | term <- premises ++ map snd discharges,Just backend <- [visit term]]

checkFailureRejection :: CheckFailure -> SourceRejection
checkFailureRejection failure = case failure of
  CheckCoreFailure error' -> SourceRejection (CoreDiagnostic (coreError error'))
  CheckGroupFailure group -> SourceRejection (SourceDiagnostic (GroupConflict group))
  CheckReplayFailure replay -> case replay of
    Replay.DuplicateSelectedBackend _ _ -> ReplayRejection DuplicateBackend
    Replay.UnknownSelectedBackend backend version ->
      ReplayRejection (UnsupportedBackend (BackendIdentity backend (BackendVersion version)))
    Replay.CertificateBackendNotSelected index argument backend version ->
      UnselectedCertificate (fromIntegral index) argument (CoreBackend backend (fromInteger (max 0 version)))
