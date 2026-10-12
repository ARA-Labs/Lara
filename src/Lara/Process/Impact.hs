-- | Impact observations and verification share the two retained checker outcomes.
module Lara.Process.Impact
  ( Endpoint, observeEndpoint, endpointFromSnapshot, endpointInput, endpointOutcome
  , Comparison, compareEndpoints, comparisonBefore, comparisonAfter, comparisonQueries
  , comparisonResult, comparisonReads, comparisonPairCount, comparisonReadCount
  , endpointReadKeys, inputReading, endpointReport, endpointStatus
  , Side (..), ReadKey (..), ReadVal (..), ReadEntry, EvidenceSnapshot
  , ImpactTransition (..), EndpointReport (..), QueryImpact (..), ImpactResult (..)
  , ImpactCertificate (..), impactCertificate, certificateResult
  , VerificationFault (..), VerificationResult (..), firstFault, verifyImpact
  ) where

import Data.Either (isRight)
import Data.Maybe (isJust, mapMaybe)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Numeric.Natural (Natural)
import qualified Lara.AST as A
import Lara.Evidence.Types (ObjectId)
import Lara.Evidence.Registry (TypedObject)
import Lara.Prop (Prop)
import Lara.Wire (PublicStatus)
import Lara.Process.History (dedupLast, naturalLength)
import qualified Lara.Process.Locality as Locality
import qualified Lara.Process.Projection as Projection
import Lara.Process.Source
import Lara.Process.Source.Types
import Lara.Process.Source.Diagnostic (SourceRejection)
import Lara.Process.Source.CoreDiagnostic (CoreBackend)

type EvidenceSnapshot = [(ObjectId,Either String (ObjectMeta,TypedObject))]
data Side = BeforeSide | AfterSide deriving (Eq, Ord, Show, Enum, Bounded)
data ReadKey
  = LeafContent A.LeafId | LeafMeta A.LeafId | RuleLookup A.ArgId | AdmissionLookup A.ArgId
  | AbsentLookup A.ArgId | GroupMember A.ArgId | GroupConflict A.ArgId | RawEndpoint Natural
  | Retention Natural | Signature A.ArgId | PolicyContrary A.ArgId | Substitution A.ArgId
  | BackendTheory CoreBackend | BackendDigest CoreBackend | CertificateInput CoreBackend
  | PremiseSubterm Natural | DischargeSubterm Natural | ConclusionEquiv A.ArgId
  | SupportMember Prop Natural | HoleMember Prop Natural | ReferenceCarrier | CheckedCarrier
  | CompiledCarrier | BlockedClosure | BlockedQuery Prop | SupportNodes Prop | HoleNodes Prop
  | AttackEdge Natural Natural | WholeInput deriving (Eq, Ord, Show)
data ReadVal = ReadAbsent | ReadAtom Prop | ReadAtoms [Prop] | ReadNat Natural | ReadNats [Natural]
  | ReadBool Bool | ReadName A.ArgId | ReadNames [A.ArgId] | ReadText String | ReadTexts [String]
  | ReadSource SourceInput deriving (Eq, Show)
type ReadEntry = (Side,ReadKey,ReadVal)

-- Constructor is private: input and outcome cannot be supplied independently.
data Endpoint = Endpoint SourceInput (Either SourceRejection AcceptedObservation) Locality.Graph (Map.Map Natural A.ArgId)
endpointInput :: Endpoint -> SourceInput
endpointInput (Endpoint input _ _ _) = input
endpointOutcome :: Endpoint -> Either SourceRejection AcceptedObservation
endpointOutcome (Endpoint _ outcome _ _) = outcome
endpointGraph :: Endpoint -> Locality.Graph
endpointGraph (Endpoint _ _ framework _) = framework
endpointNameIndex :: Endpoint -> Map.Map Natural A.ArgId
endpointNameIndex (Endpoint _ _ _ names) = names
endpointWithOutcome :: SourceInput -> Either SourceRejection AcceptedObservation -> Endpoint
endpointWithOutcome input outcome = Endpoint input outcome framework names
  where
    framework = either (const (Locality.graph [] [])) Locality.observationGraph outcome
    names = Map.fromDistinctAscList (zip [0..] (either (const []) observationNames outcome))
observeEndpoint :: SourceInput -> Endpoint
observeEndpoint input = endpointWithOutcome input (checkSource input)
endpointFromSnapshot :: Projection.Snapshot -> Endpoint
endpointFromSnapshot snapshot = endpointWithOutcome (Projection.snapshotInput snapshot) (Projection.snapshotOutcome snapshot)
endpointStatus :: Endpoint -> Prop -> Maybe PublicStatus
endpointStatus endpoint query = either (const Nothing) (\observation -> Just (publicStatus observation query)) (endpointOutcome endpoint)
endpointNames :: Endpoint -> [A.ArgId]
endpointNames = either (const []) observationNames . endpointOutcome
endpointSupport :: Endpoint -> Prop -> [Natural]
endpointSupport endpoint query = either (const []) (`observationSupport` query) (endpointOutcome endpoint)
endpointBlocked :: Endpoint -> [Prop] -> [Prop]
endpointBlocked endpoint queries = either (const []) (`blockedClosure` queries) (endpointOutcome endpoint)
endpointSnapshot :: Endpoint -> EvidenceSnapshot
endpointSnapshot endpoint = maybe [] captureSnapshot (sourceCapture (endpointInput endpoint))

data ImpactTransition = RejectedToRejected | RejectedToAccepted | AcceptedToRejected | AcceptedToAccepted deriving (Eq, Ord, Show, Enum, Bounded)
data EndpointReport = EndpointReport
  { endpointAccepted :: Bool, endpointRejection :: Maybe SourceRejection
  , endpointReferenceCarrier :: [Natural], endpointCheckedCarrier :: [Natural], endpointCompiledCarrier :: [Natural]
  , endpointBlockedQueries :: [Prop], endpointSupports :: [(Prop,[A.ArgId])] } deriving (Eq, Show)
endpointReport :: Endpoint -> [Prop] -> EndpointReport
endpointReport endpoint queries = case endpointOutcome endpoint of
  Left rejection -> EndpointReport False (Just rejection) [] [] [] [] [(query,[]) | query <- queries]
  Right observation -> EndpointReport True Nothing reference checked (Locality.graphCarrier (endpointGraph endpoint))
    (blockedClosure observation queries) [(query,mapMaybe (`Map.lookup` endpointNameIndex endpoint) (observationSupport observation query)) | query <- queries]
    where (reference,checked) = observationCarriers observation
data QueryImpact = QueryImpact
  { impactQuery :: Prop, impactBeforeStatus :: Maybe PublicStatus, impactAfterStatus :: Maybe PublicStatus
  , impactQueryChanged :: Bool, impactQueryLocality :: Bool } deriving (Eq, Show)
data ImpactResult = ImpactResult
  { impactTransition :: ImpactTransition, impactRows :: [QueryImpact], impactChanged :: [Prop], impactUnchanged :: [Prop] } deriving (Eq, Show)
data ImpactCertificate = ImpactCertificate
  { certificateBeforeInput :: SourceInput, certificateAfterInput :: SourceInput, certificateQueries :: [Prop]
  , certificateBeforeSnapshot :: EvidenceSnapshot, certificateAfterSnapshot :: EvidenceSnapshot
  , certificateBeforeIdentity :: ReplayIdentity, certificateAfterIdentity :: ReplayIdentity
  , certificateBeforeReport :: EndpointReport, certificateAfterReport :: EndpointReport
  , certificateTransition :: ImpactTransition, certificateRows :: [QueryImpact]
  , certificateChanged :: [Prop], certificateUnchanged :: [Prop], certificateBlockedBefore :: [Prop], certificateBlockedAfter :: [Prop]
  , certificateCarrier :: [A.ArgId], certificateNodeDiff :: [Natural], certificateEdgeDiff :: [(Natural,Natural)]
  , certificateLocality :: [(Prop,Bool)], certificateReads :: [ReadEntry] } deriving (Eq, Show)

-- Values remain ordered on the wire; semantic read equality uses unique keys and
-- requires every supplied triple to have its canonical value (no last-wins map).
data Comparison = Comparison Endpoint Endpoint [Prop] ImpactCertificate (Map.Map (Side,ReadKey) ReadVal)
comparisonBefore :: Comparison -> Endpoint
comparisonBefore (Comparison before _ _ _ _) = before
comparisonAfter :: Comparison -> Endpoint
comparisonAfter (Comparison _ after _ _ _) = after
comparisonQueries :: Comparison -> [Prop]
comparisonQueries (Comparison _ _ queries _ _) = queries
impactCertificate :: Comparison -> ImpactCertificate
impactCertificate (Comparison _ _ _ certificate _) = certificate
comparisonResult :: Comparison -> ImpactResult
comparisonResult = certificateResult . impactCertificate
comparisonReads :: Comparison -> [ReadEntry]
comparisonReads = certificateReads . impactCertificate
comparisonReadCount :: Comparison -> Natural
comparisonReadCount (Comparison _ _ _ _ readEnvironment) = fromIntegral (Map.size readEnvironment)
comparisonPairCount :: Comparison -> Natural
comparisonPairCount comparison = 2 * naturalLength (comparisonQueries comparison) + comparisonReadCount comparison
certificateResult :: ImpactCertificate -> ImpactResult
certificateResult certificate = ImpactResult (certificateTransition certificate) (certificateRows certificate)
  (certificateChanged certificate) (certificateUnchanged certificate)

endpointReadKeys :: Endpoint -> [Prop] -> Set.Set ReadKey
endpointReadKeys endpoint queries = readKeysWithRegions (Locality.graphCarrier framework)
  [(query,support,Locality.ancestors framework support) | query <- dedupLast queries,
    let support = endpointSupport endpoint query]
  where framework = endpointGraph endpoint
readKeysWithRegions :: [Natural] -> [(Prop,[Natural],[Natural])] -> Set.Set ReadKey
readKeysWithRegions carrier plans = Set.fromList
  (WholeInput : ReferenceCarrier : CheckedCarrier : CompiledCarrier : BlockedClosure : concatMap queryKeys plans)
  where
    queryKeys (query,support,region) = SupportNodes query : HoleNodes query : BlockedQuery query :
      map (SupportMember query) support ++ [AttackEdge source target | target <- region,source <- carrier]
inputReading :: Endpoint -> [Prop] -> ReadKey -> ReadVal
inputReading endpoint queries key = case key of
  ReferenceCarrier -> ReadNats (either (const []) (fst . observationCarriers) outcome)
  CheckedCarrier -> ReadNats (either (const []) (snd . observationCarriers) outcome)
  CompiledCarrier -> ReadNats (Locality.graphCarrier (endpointGraph endpoint))
  BlockedClosure -> ReadAtoms (endpointBlocked endpoint queries)
  BlockedQuery query -> ReadBool (not (null (endpointBlocked endpoint [query])))
  SupportNodes query -> ReadNats (endpointSupport endpoint query)
  HoleNodes _ -> ReadNats []
  SupportMember query node -> ReadBool (node `elem` endpointSupport endpoint query)
  HoleMember _ _ -> ReadBool False
  AttackEdge source target -> ReadBool (Locality.attacks (endpointGraph endpoint) source target)
  _ -> ReadSource (endpointInput endpoint)
  where outcome = endpointOutcome endpoint
compareEndpoints :: Endpoint -> Endpoint -> [Prop] -> Comparison
compareEndpoints before after queries = Comparison before after queries certificate reading
  where
    outcomeBefore = endpointOutcome before
    outcomeAfter = endpointOutcome after
    transition = case (isRight outcomeBefore,isRight outcomeAfter) of
      (False,False) -> RejectedToRejected; (False,True) -> RejectedToAccepted
      (True,False) -> AcceptedToRejected; (True,True) -> AcceptedToAccepted
    carrier = Locality.sharedCarrier (endpointNames before) (endpointNames after)
    graphs = case (outcomeBefore,outcomeAfter) of
      (Right first,Right second) -> Just (Locality.liftObservation carrier first,Locality.liftObservation carrier second)
      _ -> Nothing
    compactBefore = endpointGraph before
    compactAfter = endpointGraph after
    -- Native-coordinate regions are shared by read keys and stable-identity
    -- locality. Lift only when checking locality, never when recording reads.
    queryPlans = [(query,supportBefore,Locality.ancestors compactBefore supportBefore,
      supportAfter,Locality.ancestors compactAfter supportAfter) | query <- dedupLast queries,
      let supportBefore = endpointSupport before query,let supportAfter = endpointSupport after query]
    queryLocality supportBefore regionBefore supportAfter regionAfter = case graphs of
      Just (first,second) -> Locality.regionsCorrespond (Locality.liftedGraph first) (Locality.liftedGraph second)
        (Locality.liftedRegion first supportBefore) (Locality.liftedRegion second supportAfter)
        (Locality.liftedRegion first regionBefore) (Locality.liftedRegion second regionAfter)
      Nothing -> False
    queryRows = Map.fromList [(query,let first = endpointStatus before query; second = endpointStatus after query
      in QueryImpact query first second (first /= second) (queryLocality supportBefore regionBefore supportAfter regionAfter)) |
      (query,supportBefore,regionBefore,supportAfter,regionAfter) <- queryPlans]
    rows = mapMaybe (`Map.lookup` queryRows) queries
    changed = [impactQuery row | row <- rows,impactQueryChanged row]
    unchanged = [impactQuery row | row <- rows,isJust (impactBeforeStatus row),isJust (impactAfterStatus row),not (impactQueryChanged row)]
    keysBefore = readKeysWithRegions (Locality.graphCarrier compactBefore)
      [(query,support,region) | (query,support,region,_,_) <- queryPlans]
    keysAfter = readKeysWithRegions (Locality.graphCarrier compactAfter)
      [(query,support,region) | (query,_,_,support,region) <- queryPlans]
    entries = [(side,key,inputReading endpoint queries key) |
      (side,endpoint,keys) <- [(BeforeSide,before,keysBefore),(AfterSide,after,keysAfter)],key <- Set.toAscList keys]
    reading = Map.fromList [((side,key),value) | (side,key,value) <- entries]
    certificate = ImpactCertificate (endpointInput before) (endpointInput after) queries
      (endpointSnapshot before) (endpointSnapshot after) (sourceReplay (endpointInput before)) (sourceReplay (endpointInput after))
      (endpointReport before queries) (endpointReport after queries) transition rows changed unchanged
      (endpointBlocked before queries) (endpointBlocked after queries) carrier
      (maybe [] (\(first,second) -> Locality.nodeDiff (Locality.liftedGraph first) (Locality.liftedGraph second)) graphs)
      (maybe [] (\(first,second) -> Locality.edgeDiff (Locality.liftedGraph first) (Locality.liftedGraph second)) graphs)
      [(impactQuery row,impactQueryLocality row) | row <- rows] entries

data VerificationFault = MismatchedSnapshots | MismatchedIdentities | OutcomeMismatch | StatusMismatch
  | InvalidSupports | InvalidGraph | FalseLocality | FalseReadEvidence deriving (Eq, Ord, Show, Enum, Bounded)
data VerificationResult = Verified | InvalidCertificate VerificationFault deriving (Eq, Show)
firstFault :: Comparison -> ImpactCertificate -> Maybe VerificationFault
firstFault comparison supplied
  | certificateBeforeSnapshot supplied /= certificateBeforeSnapshot expected || certificateAfterSnapshot supplied /= certificateAfterSnapshot expected = Just MismatchedSnapshots
  | certificateBeforeIdentity supplied /= certificateBeforeIdentity expected || certificateAfterIdentity supplied /= certificateAfterIdentity expected = Just MismatchedIdentities
  | certificateTransition supplied /= certificateTransition expected
    || certificateBlockedBefore supplied /= certificateBlockedBefore expected || certificateBlockedAfter supplied /= certificateBlockedAfter expected
    || certificateBeforeReport supplied /= certificateBeforeReport expected || certificateAfterReport supplied /= certificateAfterReport expected = Just OutcomeMismatch
  | certificateRows supplied /= certificateRows expected = Just StatusMismatch
  | certificateChanged supplied /= certificateChanged expected || certificateUnchanged supplied /= certificateUnchanged expected = Just InvalidSupports
  | certificateCarrier supplied /= certificateCarrier expected || certificateNodeDiff supplied /= certificateNodeDiff expected || certificateEdgeDiff supplied /= certificateEdgeDiff expected = Just InvalidGraph
  | certificateLocality supplied /= certificateLocality expected = Just FalseLocality
  | not readsMatch = Just FalseReadEvidence
  | otherwise = Nothing
  where
    -- Certificate queries are authoritative; supplied request endpoints remain
    -- authoritative even when embedded certificate inputs name other sources.
    boundComparison
      | certificateQueries supplied == comparisonQueries comparison = comparison
      | otherwise = compareEndpoints (comparisonBefore comparison) (comparisonAfter comparison) (certificateQueries supplied)
    expected = impactCertificate boundComparison
    Comparison _ _ _ _ canonicalReads = boundComparison
    suppliedReads = certificateReads supplied
    readsMatch = Set.fromList [(side,key) | (side,key,_) <- suppliedReads] == Map.keysSet canonicalReads
      && all (\(side,key,value) -> Map.lookup (side,key) canonicalReads == Just value) suppliedReads
verifyImpact :: Comparison -> ImpactCertificate -> VerificationResult
verifyImpact comparison = maybe Verified InvalidCertificate . firstFault comparison
