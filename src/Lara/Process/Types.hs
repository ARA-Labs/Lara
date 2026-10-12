-- | Symbolic process vocabulary. Names and S-expressions stay at the wire boundary.
module Lara.Process.Types where

import Data.Void (Void)
import Numeric.Natural (Natural)

newtype EventId = EventId { eventIndex :: Natural } deriving (Eq, Ord, Show)
newtype ActorId = ActorId { actorIndex :: Natural } deriving (Eq, Ord, Show)
newtype PlanId = PlanId { planIndex :: Natural } deriving (Eq, Ord, Show)
newtype RunId = RunId { runIndex :: Natural } deriving (Eq, Ord, Show)
newtype ClaimId = ClaimId { claimIndex :: Natural } deriving (Eq, Ord, Show)
newtype SourceId = SourceId { sourceIndex :: Natural } deriving (Eq, Ord, Show)
newtype DataId = DataId { dataIndex :: Natural } deriving (Eq, Ord, Show)
newtype VersionId = VersionId { versionIndex :: Natural } deriving (Eq, Ord, Show)
newtype FamilyId = FamilyId { familyIndex :: Natural } deriving (Eq, Ord, Show)
newtype WitnessId = WitnessId { witnessIndex :: Natural } deriving (Eq, Ord, Show)

data AccessPurpose = Selection | Evaluation deriving (Eq, Ord, Show, Enum, Bounded)
data EventKind = PlanCommit | DataAccess | AnalysisRun | ResultProduced | ClaimAsserted | SourceRetracted | DataUpdated deriving (Eq, Ord, Show, Enum, Bounded)
data Event
  = CommitPlan ActorId PlanId VersionId
  | Access ActorId DataId AccessPurpose
  | Run RunId PlanId VersionId [(DataId, VersionId)] FamilyId
  | Result RunId Natural
  | Assert ClaimId WitnessId
  | Retract SourceId
  | UpdateData DataId VersionId
  deriving (Eq, Ord, Show)
data Stamped = Stamped { stampedId :: EventId, stampedEvent :: Event } deriving (Eq, Ord, Show)
type ProcessHistory = [Stamped]

data RunSpec = RunSpec
  { specRun :: RunId, specPlan :: PlanId, specVersion :: VersionId
  , specInputs :: [(DataId, VersionId)], specFamily :: FamilyId
  } deriving (Eq, Ord, Show)

eventKind :: Event -> EventKind
eventKind event = case event of
  CommitPlan {} -> PlanCommit
  Access {} -> DataAccess
  Run {} -> AnalysisRun
  Result {} -> ResultProduced
  Assert {} -> ClaimAsserted
  Retract {} -> SourceRetracted
  UpdateData {} -> DataUpdated

eventActor :: Event -> Maybe ActorId
eventActor (CommitPlan actor _ _) = Just actor
eventActor (Access actor _ _) = Just actor
eventActor _ = Nothing

eventData :: Event -> [DataId]
eventData (Access _ dataset _) = [dataset]
eventData (Run _ _ _ inputs _) = map fst inputs
eventData (UpdateData dataset _) = [dataset]
eventData _ = []

eventFamily :: Event -> Maybe FamilyId
eventFamily (Run _ _ _ _ family) = Just family
eventFamily _ = Nothing

runSpec :: Event -> Maybe RunSpec
runSpec (Run run plan version inputs family) = Just (RunSpec run plan version inputs family)
runSpec _ = Nothing

commits :: Event -> Maybe (PlanId, VersionId)
commits (CommitPlan _ plan version) = Just (plan, version)
commits _ = Nothing

access :: Event -> Maybe (DataId, AccessPurpose)
access (Access _ dataset purpose) = Just (dataset, purpose)
access _ = Nothing

data CoverageScope = CoverageScope
  { scopeKinds :: [EventKind], scopeFamily :: Maybe FamilyId
  , scopeActors :: Maybe [ActorId], scopeData :: Maybe [DataId], scopeCutoff :: Natural
  } deriving (Eq, Ord, Show)
data RecordCoverage policy
  = Complete CoverageScope | CountBounded CoverageScope Natural
  | DeclaredPolicy CoverageScope policy | OpenWorld CoverageScope
  deriving (Eq, Ord, Show)
coverageScope :: RecordCoverage policy -> CoverageScope
coverageScope (Complete scope) = scope
coverageScope (CountBounded scope _) = scope
coverageScope (DeclaredPolicy scope _) = scope
coverageScope (OpenWorld scope) = scope

data Verdict = Inconsistent | CertainTrue | CertainFalse | Unknown deriving (Eq, Ord, Show, Enum, Bounded)
data EvidenceKind = Hypothetical | Conditional | Supported | Observed deriving (Eq, Ord, Show, Enum, Bounded)
data ErrorKind = Sampling | SelectionError | OptionalStopping | Misspecification | Measurement deriving (Eq, Ord, Show, Enum, Bounded)
data GuaranteeClass = FWER | FDR | MFDR deriving (Eq, Ord, Show, Enum, Bounded)
data Acceptance = GroundedJustified deriving (Eq, Ord, Show, Enum, Bounded)
data AdmissionBasis = InstrumentedLog | SignedAttestation | AuthorDeclaration deriving (Eq, Ord, Show, Enum, Bounded)
data CoverageKind = CompleteKind | CountBoundedKind | OpenWorldKind deriving (Eq, Ord, Show, Enum, Bounded)

data SourceRef = SourceRef
  { refFile :: String, refEntry :: String, refSpan :: Maybe (Natural, Natural)
  } deriving (Eq, Ord, Show)
data CoverageAssertion policy = CoverageAssertion
  { assertionCoverage :: RecordCoverage policy, assertionEvidence :: SourceRef, assertionBasis :: AdmissionBasis
  } deriving (Eq, Ord, Show)
data DecodedEvent = DecodedEvent { decodedEvent :: Stamped, decodedSource :: SourceRef } deriving (Eq, Ord, Show)
data DecodedOrder = DecodedOrder
  { orderFirst :: EventId, orderSecond :: EventId, orderSource :: SourceRef
  } deriving (Eq, Ord, Show)
data DecodedRecord policy = DecodedRecord
  { recordEvents :: [DecodedEvent], recordOrder :: [DecodedOrder]
  , recordCoverage :: [CoverageAssertion policy], recordSubmitted :: [(ClaimId, WitnessId)]
  , recordCutoff :: Natural
  } deriving (Eq, Ord, Show)
data AraEntry policy
  = EventEntry Stamped SourceRef | OrderingEntry EventId EventId SourceRef
  | CoverageEntry (CoverageAssertion policy) | SubmissionEntry ClaimId WitnessId
  deriving (Eq, Ord, Show)
data AraSource policy = AraSource { sourceEntries :: [AraEntry policy], sourceCutoff :: Natural } deriving (Eq, Ord, Show)
data OrderRecord = OrderRecord
  { orderEvents :: [Stamped], orderBefore :: [(EventId, EventId)], orderCutoff :: Natural
  } deriving (Eq, Ord, Show)

data Atom = RunPrecommitted RunId | Predictable | SplitSelection [DataId] [DataId] | FamilyCountAtMost FamilyId Natural deriving (Eq, Ord, Show)
data Formula atom = QueryAtom atom | QueryNot (Formula atom) | QueryAnd (Formula atom) (Formula atom) | QueryOr (Formula atom) (Formula atom) deriving (Eq, Ord, Show)
type Query = Formula Atom

data ProfileSpec = ProfileSpec
  { profileAdmissible :: [EvidenceKind], profileAccepts :: [CoverageKind]
  , profileGuarantee :: GuaranteeClass, profileNum :: Natural, profileDen :: Natural
  , profileProbes :: [ErrorKind], profileAcceptance :: Acceptance
  } deriving (Eq, Ord, Show)
data Profile policy = Profile
  { admissibleEvidence :: EvidenceKind -> Bool, acceptsCoverage :: RecordCoverage policy -> Bool
  , guaranteeLevel :: (GuaranteeClass, Rational), requiredProbe :: ErrorKind -> Bool
  , acceptanceStandard :: Acceptance
  }

data QuerySpec = VerdictQuery String Query | AuditQuery String ClaimId WitnessId ProfileSpec deriving (Eq, Ord, Show)
data Problem = Problem { problemRecord :: DecodedRecord Void, problemUnrecorded :: [Stamped] } deriving (Eq, Ord, Show)
data Answer = Answer
  { answerVerdict :: Verdict, answerCount :: Natural
  , answerHolds :: Maybe ProcessHistory, answerFails :: Maybe ProcessHistory
  } deriving (Eq, Ord, Show)

evidenceRank :: EvidenceKind -> Natural
evidenceRank = fromIntegral . fromEnum

evidenceLabel :: EvidenceKind -> String
evidenceLabel Hypothetical = "hypothetical"
evidenceLabel Conditional = "conditional"
evidenceLabel Supported = "supported"
evidenceLabel Observed = "observed"

verdictLabel :: Verdict -> String
verdictLabel Inconsistent = "inconsistent"
verdictLabel CertainTrue = "certainTrue"
verdictLabel CertainFalse = "certainFalse"
verdictLabel Unknown = "unknown"

errorKindLabel :: ErrorKind -> String
errorKindLabel Sampling = "sampling"
errorKindLabel SelectionError = "selection"
errorKindLabel OptionalStopping = "optional stopping"
errorKindLabel Misspecification = "misspecification"
errorKindLabel Measurement = "measurement"

guaranteeLabel :: GuaranteeClass -> String
guaranteeLabel FWER = "FWER"
guaranteeLabel FDR = "FDR"
guaranteeLabel MFDR = "mFDR"

acceptanceLabel :: Acceptance -> String
acceptanceLabel GroundedJustified = "grounded justified"

admissionBasisLabel :: AdmissionBasis -> String
admissionBasisLabel InstrumentedLog = "instrumented log"
admissionBasisLabel SignedAttestation = "signed attestation"
admissionBasisLabel AuthorDeclaration = "author declaration"

coverageLabel :: (policy -> String) -> RecordCoverage policy -> String
coverageLabel _ (Complete _) = "complete"
coverageLabel _ (CountBounded _ bound) = "at most " ++ show bound
coverageLabel label (DeclaredPolicy _ policy) = label policy
coverageLabel _ (OpenWorld _) = "open world"
