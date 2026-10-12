module Lara.Process.Audit.Types where

import Numeric.Natural (Natural)
import qualified Lara.AST as A
import Lara.Prop (Prop)
import Lara.Process.Source.CoreDiagnostic (CheckFault)
import Lara.Process.Types
import Lara.Process.Source.Types (SourceInput, Fragment)

newtype InterpretationId = InterpretationId Natural deriving (Eq, Ord, Show)
newtype AssumptionId = AssumptionId Natural deriving (Eq, Ord, Show)
newtype SlotId = SlotId Natural deriving (Eq, Ord, Show)
newtype ChoiceId = ChoiceId Natural deriving (Eq, Ord, Show)

data ClaimBinding = ClaimBinding
  { bindingClaim :: ClaimId, bindingDeclaration :: A.PropId, bindingQuery :: Prop
  } deriving (Eq, Show)
data SupportBinding = SupportBinding
  { supportArgument :: A.ArgId, supportQuery :: Prop
  } deriving (Eq, Show)
data Method = Two | Low | Up | Disjunction | Conjunction | ConditionalFalse
  deriving (Eq, Ord, Show, Enum, Bounded)
data PayloadMode = ConditionalPayload | AppliedPayload deriving (Eq, Ord, Show, Enum, Bounded)
data ResidualAssumption = InterpretationFidelity | PhysicalSampling | CaptureAdequacy | RuntimeRefinement
  deriving (Eq, Ord, Show, Enum, Bounded)
data MethodBinding = MethodBinding
  { bindingMethod :: Method, bindingMode :: PayloadMode, bindingParameter :: Integer
  , bindingFirst :: Bool, bindingSecond :: Bool, bindingResidual :: [ResidualAssumption]
  } deriving (Eq, Show)
data ArtifactInterpretation = DeclaredInterpretation InterpretationId | CheckedMethod MethodBinding deriving (Eq, Show)
data ArtifactSpec = ArtifactSpec
  { artifactArgument :: A.ArgId, artifactDependencies :: [SupportBinding]
  , artifactInterpretation :: ArtifactInterpretation
  } deriving (Eq, Show)

data StatKind = PValue | EValue deriving (Eq, Ord, Show, Enum, Bounded)
data Ledger = Ledger
  { ledgerKind :: Maybe StatKind, ledgerValue :: Maybe Rational
  , ledgerCountBound :: Maybe Natural, ledgerGuarantee :: Maybe GuaranteeClass
  } deriving (Eq, Show)
data LedgerBinding = LedgerBinding
  { ledgerRun :: RunId, ledgerFamily :: FamilyId, ledgerOutcome :: Natural, ledger :: Ledger
  } deriving (Eq, Show)
data GuaranteeBinding = ConditionalGuarantee GuaranteeClass Rational | LedgerGuarantee LedgerBinding deriving (Eq, Show)
data WitnessSpec = WitnessSpec
  { witnessId :: WitnessId, witnessClaim :: ClaimId, witnessSource :: SourceInput
  , witnessArtifact :: ArtifactSpec, witnessProbed :: [ErrorKind], witnessGuarantee :: GuaranteeBinding
  } deriving (Eq, Show)

data KindKey = LeafKey A.LeafId | MethodKey A.RuleId | ArgumentKey A.ArgId deriving (Eq, Ord, Show)
data KindSpec = KindSpec
  { kindSource :: SourceInput, kindKey :: KindKey, kindUpper :: EvidenceKind
  , kindAssumption :: Maybe AssumptionId
  } deriving (Eq, Show)
data CaptureAssumption = CaptureAssumption
  { captureId :: AssumptionId, captureSource :: SourceInput, captureKey :: KindKey
  , captureEvent :: Stamped, captureRun :: RunId, captureBasis :: AdmissionBasis
  } deriving (Eq, Show)
data AuditConfig = AuditConfig
  { auditClaims :: [ClaimBinding], auditWitnesses :: [WitnessSpec]
  , auditKinds :: [KindSpec], auditAssumptions :: [CaptureAssumption]
  } deriving (Eq, Show)
data WitnessFields = WitnessFields
  { fieldsClaim :: ClaimId, fieldsArgument :: A.ArgId, fieldsProbed :: [ErrorKind]
  , fieldsAchieved :: (GuaranteeClass,Rational)
  } deriving (Eq, Show)

data SupportFault
  = SupportAbsent | SupportInference CheckFault | SupportIncomplete [A.QuestionId]
  | SupportDifferentConclusion | SupportNotRetained | SupportAbsentNode
  | SupportNodeMismatch | SupportBlocked
  deriving (Eq, Show)
data AssociationFault = AssociationInputClaim | AssociationSemanticClaim
  | AssociationMissingDeclaration | AssociationWrongArgument | AssociationNotAlternative
  deriving (Eq, Ord, Show, Enum, Bounded)
data ApplicationError = ApplicationModelMismatch | ApplicationPremiseMismatch
  | ApplicationProgramMismatch | ApplicationPostconditionMismatch | ApplicationRunMismatch
  | ApplicationFailedPrecondition deriving (Eq, Ord, Show, Enum, Bounded)
data BridgeError
  = StaleSnapshot | IncompatibleInterpretation | IncompatibleMethod | IncompatibleClaim
  | IncompatibleDependencies | IncompatibleEvidence | IncompatibleBinding
  | MissingSupport | BlockedSupport | DefeatedSupport | FailedDerivation | FalsePrecondition
  | BridgeApplication ApplicationError deriving (Eq, Show)
data ArtifactFault = ArtifactSupport A.ArgId SupportFault
  | ArtifactAssociation AssociationFault | ArtifactMethod BridgeError deriving (Eq, Show)
data LedgerFault = AbsentRun | FamilyMismatch | AbsentResult | MissingKind | MissingValue
  | MissingGuarantee | MissingBound | ZeroBound | UnsupportedGuarantee | ExceededBound | NonFiniteLevel
  deriving (Eq, Ord, Show, Enum, Bounded)
data GuaranteeFault = InvalidConditionalLevel | GuaranteeLedger LedgerFault deriving (Eq, Show)
data WitnessFault = MissingClaim | MissingWitness | AmbiguousMetadata | WrongClaim
  | StaleSource | WitnessArtifact ArtifactFault | WitnessGuarantee GuaranteeFault deriving (Eq, Show)
data ProvenanceError = ProvenanceShape | ProvenanceMissingRule A.RuleId
  | ProvenanceUnresolvedReference A.ArgRef | ProvenanceImplicitMatch
  | ProvenanceMissingArgument A.ArgId | ProvenanceDuplicateArgument A.ArgId
  | ProvenanceMissingNode Natural deriving (Eq, Show)

data Guard = GuardTruth | GuardQuery Query | GuardPresent Stamped | GuardBefore Stamped Stamped
  | GuardNot Guard | GuardAnd Guard Guard | GuardOr Guard Guard deriving (Eq, Show)
data Choice = Choice
  { choiceId :: ChoiceId, choiceGuard :: Guard, choiceFragment :: Fragment
  } deriving (Eq, Show)
data Slot = Slot { slotId :: SlotId, slotChoices :: [Choice] } deriving (Eq, Show)
data Selection = Selection { selectionSlot :: SlotId, selectionChoice :: Choice } deriving (Eq, Show)
data Completion = Completion
  { completionHistory :: ProcessHistory, completionAssignment :: [Selection]
  } deriving (Eq, Show)
data FamilySpec = FamilySpec
  { familyProblem :: Problem, familyBase :: SourceInput, familySlots :: [Slot]
  } deriving (Eq, Show)
data EnumerationLimits = EnumerationLimits
  { limitHistories :: Natural, limitSteps :: Natural, limitProducts :: Natural
  } deriving (Eq, Show)
data EnumerationRefusal = HistoriesRefusal Natural Natural | StepsRefusal Natural Natural
  | ProductsRefusal Natural Natural deriving (Eq, Show)
