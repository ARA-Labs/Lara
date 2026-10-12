module Lara.Process.Source.CoreDiagnostic where

import Numeric.Natural (Natural)
import qualified Lara.AST as A
import Lara.Prop (Prop, Term (..), Pred, FunSym)
import Lara.Strict (SExpr)
import qualified Lara.Check as C
import qualified Lara.SupportTerm as S
import qualified Lara.Policy as P
import qualified Lara.Sigma.WellSorted as Sigma

-- These are the wire-facing core values, without native CLI-only sites, prose,
-- certificate slot labels, or remapped declaration indices.
data CoreBackend = CoreBackend A.BackendId Natural deriving (Eq, Ord, Show)
data CorePattern = PatternVariable A.Param | PatternNumber String | PatternString String
  | PatternConstructor FunSym [CorePattern] deriving (Eq, Show)
data CoreAtomPattern = CoreAtomPattern Pred [CorePattern] deriving (Eq, Show)
data CoreAssurance = CoreNone | CoreTrusted | CoreCertificate CoreBackend A.TheoryDigest SExpr deriving (Eq, Show)
data CoreSupport = CoreLeaf A.LeafId
  | CoreRule A.RuleId [(A.Param,Term)] [CoreSupport] [(A.QuestionId,CoreSupport)] [A.QuestionId] CoreAssurance
  deriving (Eq, Show)
data CorePositionStep = CorePremise Natural | CoreQuestion A.QuestionId deriving (Eq, Ord, Show)
type CorePosition = [CorePositionStep]
data CoreLocation = CoreRoot | CorePremiseLocation CoreLocation Natural
  | CoreQuestionLocation CoreLocation A.QuestionId deriving (Eq, Show)
data DeclarationLocation = ArgumentLocation Natural | AttackLocation Natural deriving (Eq, Show)
data SignatureFault = MalformedSigma | PolicyIllSorted | GroundIllSorted | ArgumentsIllSorted deriving (Eq, Ord, Show)
data ReferenceFault = ReferenceMissingLeaf A.LeafId | ReferenceMissingRule A.RuleId
  | ReferenceUndeclaredSource CoreSupport | ReferenceUndeclaredTarget CoreSupport deriving (Eq, Show)
data SubstitutionFault = SubstitutionDuplicateKeys [A.Param] | SubstitutionDomainMismatch [A.Param] [A.Param]
  | SubstitutionPremiseInstantiation [CoreAtomPattern] | SubstitutionConclusionInstantiation CoreAtomPattern deriving (Eq, Show)
data PremiseFault = PremiseCount Natural Natural | PremiseMismatch Prop Prop deriving (Eq, Show)
data QuestionFault = QuestionDuplicateDeclarations [A.QuestionId] | QuestionDuplicateDischarges [A.QuestionId]
  | QuestionDuplicateHoles [A.QuestionId] | QuestionUncovered [A.QuestionId] [A.QuestionId] [A.QuestionId]
  | QuestionOverlap [A.QuestionId] [A.QuestionId] | QuestionUndeclaredDischarge [A.QuestionId] [A.QuestionId]
  | QuestionUndeclaredHole [A.QuestionId] [A.QuestionId] deriving (Eq, Show)
data DischargeFault = DischargeAnswerInstantiation A.QuestionId CoreAtomPattern
  | DischargeConclusionMismatch A.QuestionId Prop Prop deriving (Eq, Show)
data AssuranceFault = AssuranceQuestionsPresent [A.QuestionId] [A.QuestionId]
  | AssuranceWrongMode A.Mode CoreAssurance | AssuranceTrustedDisallowed
  | AssuranceCertifierUnallowlisted CoreBackend A.TheoryDigest deriving (Eq, Show)
data BackendFault = BackendMissing CoreBackend | DigestMissing CoreBackend A.TheoryDigest
  | ReplayRejected CoreBackend A.TheoryDigest SExpr deriving (Eq, Show)
data AttackKind = RebutKind | UndercutKind | UndermineKind deriving (Eq, Ord, Show)
data OccurrenceKind = RuleOccurrence | LeafOccurrence deriving (Eq, Ord, Show)
data PositionFault = UndefinedPosition | WrongOccurrenceKind OccurrenceKind OccurrenceKind deriving (Eq, Show)
data RelationFault = RelationMissingRule A.RuleId | RelationConclusionInstantiation A.RuleId CoreAtomPattern
  | RelationMissingLeaf A.LeafId | RelationStrictTarget A.RuleId | RelationMissingContrary Prop Prop
  | RelationMissingException A.RuleId | RelationExceptionInstantiation A.RuleId CoreAtomPattern
  | RelationExceptionMismatch A.RuleId Prop Prop deriving (Eq, Show)
data CheckFault
  = CheckR1 CoreLocation ReferenceFault | CheckR3 CoreLocation SubstitutionFault
  | CheckR4 CoreLocation PremiseFault | CheckR5 CoreLocation QuestionFault
  | CheckR6 CoreLocation DischargeFault | CheckR7 CoreLocation AssuranceFault
  | CheckR10 CoreLocation CorePosition AttackKind PositionFault
  | CheckR11 CoreLocation CorePosition AttackKind RelationFault
  | CheckR13 CoreLocation BackendFault deriving (Eq, Show)
data MissingConflict = MissingConflict Natural Natural Prop Prop deriving (Eq, Show)
data ProgramFault = ProgramRejection DeclarationLocation CheckFault
  | ProgramDuplicateArgument Natural Natural | ProgramMissingConflict MissingConflict deriving (Eq, Show)
data CoreError = CoreDuplicateRule A.RuleId Natural Natural | CoreSignature SignatureFault
  | CoreScopeViolation A.RuleId A.Param | CorePolicyViolation A.RuleId CoreAtomPattern (CoreAtomPattern,CoreAtomPattern)
  | CoreProgram ProgramFault deriving (Eq, Show)

nat :: Integral a => a -> Natural
nat = fromInteger . max 0 . toInteger
corePattern :: A.Pat -> CorePattern
corePattern (A.PVar p) = PatternVariable p
corePattern (A.PLit t) = literalPattern t
corePattern (A.PCon f ps) = PatternConstructor f (map corePattern ps)
literalPattern :: Term -> CorePattern
literalPattern (TNum s) = PatternNumber s
literalPattern (TStr s) = PatternString s
literalPattern (TCon f ts) = PatternConstructor f (map literalPattern ts)
coreAtomPattern :: A.AtomPat -> CoreAtomPattern
coreAtomPattern (A.AtomPat p ps) = CoreAtomPattern p (map corePattern ps)
coreAssurance :: A.Assurance -> CoreAssurance
coreAssurance A.AssuranceNone = CoreNone
coreAssurance A.AssuranceTrusted = CoreTrusted
coreAssurance (A.AssuranceCert c) = CoreCertificate (CoreBackend (A.certBackend c) (nat (A.certVersion c))) (A.certTheory c) (A.certPayload c)
coreSupport :: A.SupportTerm -> CoreSupport
coreSupport (A.SLeaf leaf) = CoreLeaf leaf
coreSupport (A.SRule r theta premises discharges holes assurance) =
  CoreRule r theta (map coreSupport premises) [(q,coreSupport term) | (q,term) <- discharges]
    [A.QuestionId q | A.ObligationId q <- holes] (coreAssurance assurance)
coreLocation :: S.CheckLoc -> CoreLocation
coreLocation S.LocRoot = CoreRoot
coreLocation (S.LocPremise parent index) = CorePremiseLocation (coreLocation parent) (nat index)
coreLocation (S.LocQuestion parent question) = CoreQuestionLocation (coreLocation parent) question
corePosition :: A.Position -> CorePosition
corePosition = map step
  where step (A.StepPremise index) = CorePremise (nat index)
        step (A.StepQuestion question) = CoreQuestion question
coreAttackKind :: S.AttackKind -> AttackKind
coreAttackKind S.AKRebut = RebutKind
coreAttackKind S.AKUndercut = UndercutKind
coreAttackKind S.AKUndermine = UndermineKind
coreOccurrence :: S.AttackOccurrenceKind -> OccurrenceKind
coreOccurrence S.OccRule = RuleOccurrence
coreOccurrence S.OccLeaf = LeafOccurrence

coreCheckFault :: S.CheckError -> CheckFault
coreCheckFault error' = case error' of
  S.CE_R1 location reason -> CheckR1 (coreLocation location) (case reason of
    S.MissingLeaf leaf -> ReferenceMissingLeaf leaf
    S.MissingRule rule -> ReferenceMissingRule rule
    S.UndeclaredAttackSource term -> ReferenceUndeclaredSource (coreSupport term)
    S.UndeclaredAttackTarget term -> ReferenceUndeclaredTarget (coreSupport term))
  S.CE_R3 location reason -> CheckR3 (coreLocation location) (case reason of
    S.DuplicateKeys keys -> SubstitutionDuplicateKeys keys
    S.DomainMismatch actual expected -> SubstitutionDomainMismatch actual expected
    S.PremiseInstantiation patterns -> SubstitutionPremiseInstantiation (map coreAtomPattern patterns)
    S.ConclusionInstantiation pattern' -> SubstitutionConclusionInstantiation (coreAtomPattern pattern'))
  S.CE_R4 location reason -> CheckR4 (coreLocation location) (case reason of
    S.PremiseCount actual expected -> PremiseCount (nat actual) (nat expected)
    S.PremiseMismatch actual expected -> PremiseMismatch actual expected)
  S.CE_R5 location reason -> CheckR5 (coreLocation location) (case reason of
    S.DuplicateDeclarations qs -> QuestionDuplicateDeclarations qs
    S.DuplicateDischarges qs -> QuestionDuplicateDischarges qs
    S.DuplicateHoles qs -> QuestionDuplicateHoles qs
    S.Uncovered qs ds hs -> QuestionUncovered qs ds hs
    S.Overlap ds hs -> QuestionOverlap ds hs
    S.UndeclaredDischarge qs ds -> QuestionUndeclaredDischarge qs ds
    S.UndeclaredHole qs hs -> QuestionUndeclaredHole qs hs)
  S.CE_R6 location reason -> CheckR6 (coreLocation location) (case reason of
    S.AnswerInstantiation question pattern' -> DischargeAnswerInstantiation question (coreAtomPattern pattern')
    S.ConclusionMismatch question actual expected -> DischargeConclusionMismatch question actual expected)
  S.CE_R7 location reason -> CheckR7 (coreLocation location) (case reason of
    S.QuestionsPresent ds hs -> AssuranceQuestionsPresent ds hs
    S.WrongMode mode assurance -> AssuranceWrongMode mode (coreAssurance assurance)
    S.TrustedDisallowed -> AssuranceTrustedDisallowed
    S.CertifierUnallowlisted backend version digest -> AssuranceCertifierUnallowlisted (CoreBackend backend (nat version)) digest)
  S.CE_R10 location position kind reason -> CheckR10 (coreLocation location) (corePosition position) (coreAttackKind kind) (case reason of
    S.UndefinedPosition -> UndefinedPosition
    S.WrongOccurrenceKind actual expected -> WrongOccurrenceKind (coreOccurrence actual) (coreOccurrence expected))
  S.CE_R11 location position kind reason -> CheckR11 (coreLocation location) (corePosition position) (coreAttackKind kind) (case reason of
    S.MissingTargetRule rule -> RelationMissingRule rule
    S.TargetConclusionInstantiation rule pattern' -> RelationConclusionInstantiation rule (coreAtomPattern pattern')
    S.MissingTargetLeaf leaf -> RelationMissingLeaf leaf
    S.StrictTarget rule -> RelationStrictTarget rule
    S.MissingContrary actual expected -> RelationMissingContrary actual expected
    S.MissingException rule -> RelationMissingException rule
    S.ExceptionInstantiation rule pattern' -> RelationExceptionInstantiation rule (coreAtomPattern pattern')
    S.ExceptionMismatch rule actual expected -> RelationExceptionMismatch rule actual expected)
  S.CE_R13 location reason -> CheckR13 (coreLocation location) (case reason of
    S.BackendMissing backend version _ _ _ -> BackendMissing (CoreBackend backend (nat version))
    S.DigestMissing backend version digest _ _ -> DigestMissing (CoreBackend backend (nat version)) digest
    S.ReplayRejected backend digest ref payload _ _ -> ReplayRejected (CoreBackend backend (nat (A.certRefVersion ref))) digest payload)

coreError :: C.UnitError -> CoreError
coreError error' = case error' of
  C.UEDuplicateRule duplicate -> CoreDuplicateRule (P.drId duplicate) (nat (P.drFirstIndex duplicate)) (nat (P.drDuplicateIndex duplicate))
  C.UESignature fault -> CoreSignature (case fault of
    Sigma.SEMalformedSigma _ -> MalformedSigma
    Sigma.SERule _ _ -> PolicyIllSorted
    Sigma.SEException _ _ -> PolicyIllSorted
    Sigma.SEContrary _ _ -> PolicyIllSorted
    Sigma.SETheory _ _ _ -> GroundIllSorted
    Sigma.SELeaf _ _ -> GroundIllSorted
    Sigma.SEQuery _ _ -> GroundIllSorted
    Sigma.SESubst _ _ _ _ -> ArgumentsIllSorted)
  C.UEPolicyViolation (P.OutOfScopeParam rule _ parameter) -> CoreScopeViolation rule parameter
  C.UEPolicyViolation (P.StrictContraryOverlap rule conclusion (A.Contrary left right)) ->
    CorePolicyViolation rule (coreAtomPattern conclusion) (coreAtomPattern left,coreAtomPattern right)
  C.UEProgram fault -> CoreProgram (case fault of
    C.PERejection location check -> ProgramRejection (case location of
      C.DLArgument index -> ArgumentLocation (nat index)
      C.DLAttack index -> AttackLocation (nat index)) (coreCheckFault check)
    C.PEDuplicateArgument first second -> ProgramDuplicateArgument (nat first) (nat second)
    C.PEMissingConflict conflict -> ProgramMissingConflict (MissingConflict
      (nat (C.mcSourceNodeIndex conflict)) (nat (C.mcTargetNodeIndex conflict))
      (C.mcSourceConclusion conflict) (C.mcTargetConclusion conflict)))
