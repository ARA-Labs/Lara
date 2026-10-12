module Lara.Process.Inquiry.Types where

import Numeric.Natural (Natural)
import Lara.Process.Types
import qualified Lara.Process.Wire as W
import Lara.Process.Audit.Types (Slot, SlotId, ChoiceId, ClaimBinding, WitnessSpec, KindSpec, CaptureAssumption)
import Lara.Process.Source.Types (SourceInput)
import Lara.Process.Analysis
import Lara.Process.Impact (ImpactCertificate, ImpactResult, VerificationResult)

data LimitCounter = Histories | Sources | SourceBytes | Declarations | SearchSteps | Pairs | Subsets deriving (Eq, Ord, Show, Enum, Bounded)
data InquiryLimits = InquiryLimits
  { limitHistories :: Natural, limitSources :: Natural, limitSourceBytes :: Natural
  , limitDeclarations :: Natural, limitSearchSteps :: Natural, limitPairs :: Natural, limitSubsets :: Natural
  } deriving (Eq, Show)
data RunRefusal = Malformed String | SyntaxError String | Unsupported String | Version String | Usage String | IOFailure String
  | Limit LimitCounter Natural Natural deriving (Eq, Show)
data ReferenceSpec = ReferenceSpec { referenceHistory :: ProcessHistory, referenceAssignment :: [(SlotId,ChoiceId)] } deriving (Eq, Show)
data RequestSpec = StatusRequest String ClaimId | AuditRequest String ClaimId WitnessId ProfileSpec
  | StableRequest String Observable | SensitivityRequest String ReferenceSpec Observable
  | SlotsSensitiveRequest String ReferenceSpec Observable | MinimalAssumptionsRequest String Target
  | ImpactRequest String SourceInput SourceInput [ClaimId]
  | VerifyImpactRequest String SourceInput SourceInput ImpactCertificate deriving (Eq, Show)
data InquiryInput = InquiryInput
  { inquiryProcess :: W.Document, inquiryBase :: SourceInput, inquirySlots :: [Slot]
  , inquiryClaims :: [ClaimBinding], inquiryWitnesses :: [WitnessSpec], inquiryKinds :: [KindSpec]
  , inquiryAssumptions :: [CaptureAssumption], inquiryCatalog :: [Literal], inquiryLimits :: InquiryLimits
  , inquiryRequests :: [RequestSpec]
  } deriving (Eq, Show)
data OutcomeAnswer = OutcomeAnswer Verdict Natural (Maybe [EventId]) (Maybe [EventId]) deriving (Eq, Show)
data ResultBody = HistoryVerdict Natural OutcomeAnswer | StatusBody FamilyStatusResult | AuditBody FamilyAuditResult
  | StabilityBody StabilityResult | SensitivityBody SensitivityResult | SlotsSensitiveBody SensitivityResult
  | AssumptionsBody AssumptionResult | ImpactBody ImpactResult | VerificationBody VerificationResult deriving (Eq, Show)
data InquiryResult = InquiryResult { resultLabel :: String, resultBody :: ResultBody } deriving (Eq, Show)
data InquiryError = InquiryError { errorLabel :: Maybe String, errorRefusal :: RunRefusal } deriving (Eq, Show)
