module Lara.Process.Source.Diagnostic where

import Numeric.Natural (Natural)
import Lara.AST
import Lara.Process.Source.CoreDiagnostic (CoreError, CoreBackend)
import Lara.Elaborate (SourceInvalid (..), ElabError (..))
import qualified Lara.Elaborate as E
import Lara.Process.Source.Types (CoreVersion, BackendIdentity, EvidenceError)

data ReplayError
  = UnsupportedCore CoreVersion | ReplayPolicyMismatch | BackendMismatch
  | DuplicateBackend | UnsupportedBackend BackendIdentity | DuplicateTheory
  | TheoryMismatch | ArtifactMismatch
  deriving (Eq, Show)

data SurfaceError
  = Unsupported
  | PolicyMismatch PolicyId PolicyId
  | DuplicateLeafId LeafId | DuplicateArgumentId ArgId | DuplicateClaimId PropId
  | DuplicateValueName ValueName | MalformedRuleNamespace RuleId
  | InvalidValueBinding ValueName | InvalidComparison PropId
  | InvalidInferredArgument ArgId | InvalidNamedCertificate ArgId
  | SourceConclusionMismatch ArgId PropId | SourceChallengeTargetUndeclared ArgId
  | InvalidSurfaceAttack ArgId ArgId | SourceUnknownStatusClaim PropId
  | SourceDuplicateGroupId GroupId | SourceGroupRepeatedMember GroupId LeafId
  | SourceGroupTooFewMembers GroupId | SourceGroupMemberUndeclared GroupId LeafId
  | NoncanonicalPremiseLabels RuleId | SourceDuplicateAdmissionKey LeafKind Provenance
  | AdmissionRejected LeafId
  deriving (Eq, Show)

data SourceError
  = Structural SurfaceError | EvidenceRequired LeafId | EvidenceSyntax | GroupConflict GroupId
  deriving (Eq, Show)
data SourceDiagnostic
  = SourceDiagnostic SourceError | EvidenceDiagnostic EvidenceError | CoreDiagnostic CoreError
  deriving (Eq, Show)
data SourceRejection
  = ReplayRejection ReplayError | SourceRejection SourceDiagnostic
  | MissingEvidence LeafId | UnselectedCertificate Natural ArgId CoreBackend
  deriving (Eq, Show)

sourceInvalidDiagnostic :: Program -> SourceInvalid -> SourceDiagnostic
sourceInvalidDiagnostic program invalid = SourceDiagnostic $ case invalid of
  DuplicateAdmissionKey k p -> Structural (SourceDuplicateAdmissionKey k p)
  DuplicateSourceLeafId l -> Structural (DuplicateLeafId l)
  SourceEvidenceSyntaxError _ -> EvidenceSyntax
  SourceReplayError _ -> Structural Unsupported
  SourceElaborationError err -> Structural (elaborationDiagnostic program err)

elaborationDiagnostic :: Program -> ElabError -> SurfaceError
elaborationDiagnostic program err = case err of
  PolicyIdMismatch a b -> PolicyMismatch a b
  UnknownRule a _ -> InvalidInferredArgument a
  InquiryArgumentUnbuildable argument -> InvalidInferredArgument argument
  SourceExplicitDischargeShape argument _ -> InvalidInferredArgument argument
  InquiryCertificateUnlowerable argument -> InvalidNamedCertificate argument
  InquiryAttackUnresolvable source target -> InvalidSurfaceAttack source target
  InquiryComparisonUnbuildable claim -> InvalidComparison claim
  ThetaReferenceCountMismatch a _ _ _ -> InvalidInferredArgument a
  ThetaReferenceUnresolved a _ _ _ -> InvalidInferredArgument a
  ThetaReferenceAmbiguous a _ _ _ -> InvalidInferredArgument a
  ThetaReferenceShapeMismatch a _ _ _ _ -> InvalidInferredArgument a
  ThetaReferenceConflict a _ _ _ _ _ _ -> InvalidInferredArgument a
  ThetaReferenceConclUnderivable a _ _ _ -> InvalidInferredArgument a
  ThetaParameterUnbound a _ _ -> InvalidInferredArgument a
  CertSlotUnresolved a _ _ _ _ -> InvalidNamedCertificate a
  CertSlotAmbiguous a _ _ _ -> InvalidNamedCertificate a
  CertSlotLabelAmbiguous a _ _ _ _ -> InvalidNamedCertificate a
  CertSlotNotAPremise a _ _ _ -> InvalidNamedCertificate a
  CertSlotMultiSlot a _ _ _ _ _ _ -> InvalidNamedCertificate a
  CertSlotNonCanonicalNumeral a _ _ _ -> InvalidNamedCertificate a
  CertSlotSchemaMismatch a _ _ _ -> InvalidNamedCertificate a
  CertNdBinderUnbound a _ _ _ -> InvalidNamedCertificate a
  CertNdBinderShadowed a _ _ _ -> InvalidNamedCertificate a
  CertNdBinderShadowsPremise a _ _ _ -> InvalidNamedCertificate a
  CertNdMalformedBinder a _ _ _ -> InvalidNamedCertificate a
  CertNdNonCanonicalIndex a _ _ _ -> InvalidNamedCertificate a
  CertNdKernelIndex a _ _ _ -> InvalidNamedCertificate a
  CertNdPremOutOfRange a _ _ _ _ _ -> InvalidNamedCertificate a
  CertNdFormulaMalformed a _ _ _ -> InvalidNamedCertificate a
  CertNdResidualNamed a _ _ _ -> InvalidNamedCertificate a
  ArityMismatch a _ _ _ -> InvalidInferredArgument a
  UnresolvedPremise a _ _ _ -> InvalidInferredArgument a
  AmbiguousPremise a _ _ _ _ -> InvalidInferredArgument a
  UnresolvedDischarge a _ _ -> InvalidInferredArgument a
  AmbiguousDischarge a _ _ -> InvalidInferredArgument a
  ConclusionMismatch a c _ _ -> SourceConclusionMismatch a c
  UnknownStatusClaim c -> SourceUnknownStatusClaim c
  ChallengeTargetUndeclared a -> SourceChallengeTargetUndeclared a
  DuplicateArgId a -> DuplicateArgumentId a
  AttackEndpointUndeclared a -> attackFor a
  E.DuplicateClaimId claim -> Lara.Process.Source.Diagnostic.DuplicateClaimId claim
  E.MalformedRuleNamespace rule -> Lara.Process.Source.Diagnostic.MalformedRuleNamespace rule
  E.NoncanonicalPremiseLabels rule -> Lara.Process.Source.Diagnostic.NoncanonicalPremiseLabels rule
  DuplicateGroupId g -> SourceDuplicateGroupId g
  GroupRepeatedMember g l -> SourceGroupRepeatedMember g l
  GroupTooFewMembers g -> SourceGroupTooFewMembers g
  GroupMemberUndeclared g l -> SourceGroupMemberUndeclared g l
  PremiseLabelCountMismatch r _ _ -> Lara.Process.Source.Diagnostic.NoncanonicalPremiseLabels r
  PremiseLabelDuplicate r _ -> Lara.Process.Source.Diagnostic.NoncanonicalPremiseLabels r
  PremiseLabelReserved r _ -> Lara.Process.Source.Diagnostic.NoncanonicalPremiseLabels r
  PremiseLabelQuestionCollision r _ -> Lara.Process.Source.Diagnostic.NoncanonicalPremiseLabels r
  AttackStepUnresolved a b _ -> InvalidSurfaceAttack a b
  DuplicateValueBinding v -> DuplicateValueName v
  ReservedValueName v -> InvalidValueBinding v
  ValueNameConstructorCollision v -> InvalidValueBinding v
  ValueBindingSortError v _ -> InvalidValueBinding v
  ValueBindingClaimSortError (PropId c) _ -> InvalidValueBinding (ValueName c)
  InquiryNlInvalid name -> InvalidValueBinding name
  NlValueBindingMissing _ name -> InvalidValueBinding name
  NlUnterminatedBrace (PropId c) -> InvalidValueBinding (ValueName c)
  NlStrayBrace (PropId c) -> InvalidValueBinding (ValueName c)
  NlUnknownDirective _ body -> InvalidValueBinding (ValueName body)
  NlCellLeafUndeclared _ (LeafId leaf) -> InvalidValueBinding (ValueName ("cell " ++ leaf))
  NlCellObligation _ (LeafId leaf) -> InvalidValueBinding (ValueName ("cell " ++ leaf))
  ComparisonUndeclaredMeasurand c _ -> InvalidComparison c
  ComparisonMeasurandNoPolarity c _ -> InvalidComparison c
  ComparisonNoScheme c _ _ -> InvalidComparison c
  ComparisonSchemeRuleUnknown c _ -> InvalidComparison c
  ComparisonRecheckNotStrict c _ -> InvalidComparison c
  ComparisonRecheckCertifierMissing c _ -> InvalidComparison c
  ComparisonBridgeNotDefeasible c _ -> InvalidComparison c
  ComparisonBridgeConclusionShape c _ -> InvalidComparison c
  ComparisonBridgePremiseShape c _ -> InvalidComparison c
  ComparisonRecheckConclusionShape c _ -> InvalidComparison c
  ComparisonSchemeDirectionMismatch c _ _ -> InvalidComparison c
  ComparisonConclusionShape c _ -> InvalidComparison c
  ComparisonConclusionPredMismatch c _ _ _ -> InvalidComparison c
  ComparisonLeafUndeclared c _ -> InvalidComparison c
  ComparisonBindingNotLeaf c _ -> InvalidComparison c
  ComparisonBindingNotAdmitted c _ _ -> InvalidComparison c
  ComparisonSameLeaf c _ -> InvalidComparison c
  ComparisonCellObligation c _ -> InvalidComparison c
  ComparisonNoPremiseSlot c _ _ -> InvalidComparison c
  ComparisonAmbiguousPremiseSlot c _ _ _ -> InvalidComparison c
  ComparisonSlotClash c _ _ -> InvalidComparison c
  ComparisonThetaConflict c _ _ _ _ _ -> InvalidComparison c
  ComparisonRecheckRoleMissing c _ _ -> InvalidComparison c
  ComparisonMeasurandInconsistent c _ _ _ -> InvalidComparison c
  ComparisonUnboundParam c _ _ -> InvalidComparison c
  ComparisonCertSlotUndeterminable c _ -> InvalidComparison c
  ComparisonIdCollision c _ -> InvalidComparison c
  ComparisonDuplicateBlock c _ -> InvalidComparison c
  where
    -- The elaborator retains one missing endpoint; its authored declaration
    -- supplies the other endpoint without interpreting diagnostic prose.
    attackFor missing = case [(a,b) | DeclAttack attack <- programDecls program,
      let (a,b) = endpoints attack, missing == a || missing == b] of
        ((a,b):_) -> InvalidSurfaceAttack a b
        [] -> SourceChallengeTargetUndeclared missing
    endpoints (SRebut a b) = (a,b)
    endpoints (SUndercut a b _) = (a,b)
    endpoints (SUndermine a b _) = (a,b)
