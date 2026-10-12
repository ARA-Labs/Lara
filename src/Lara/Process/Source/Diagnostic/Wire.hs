{-# LANGUAGE FlexibleInstances #-}
module Lara.Process.Source.Diagnostic.Wire
  ( encodeRejection, decodeRejection, encodeSourceDiagnostic, decodeSourceDiagnostic
  , encodeCoreError, decodeCoreError, encodeCheckFault, decodeCheckFault
  ) where

import Control.Monad (unless)
import Numeric.Natural (Natural)
import qualified Lara.AST as A
import Lara.Prop (Prop, Term (..), Pred (..), FunSym (..))
import Lara.Strict (SExpr (..))
import qualified Lara.Wire as Raw
import qualified Lara.Process.Wire as W
import qualified Lara.Process.Source.Wire as Source
import qualified Lara.Process.Source.Types as T
import Lara.Process.Source.CoreDiagnostic
import Lara.Process.Source.Diagnostic
import Lara.Evidence.Types (ObjectId (..))

type Result = Either W.Error
class Codec a where
  enc :: a -> SExpr
  dec :: SExpr -> Result a
bad :: Result a
bad = W.bad "malformed source diagnostic constructor"
form :: String -> [SExpr] -> SExpr
form = W.tagged
text :: String -> SExpr
text = SAtom
unText :: SExpr -> Result String
unText = W.decodeText
list :: (a -> SExpr) -> [a] -> SExpr
list f = SList . map f
unList :: (SExpr -> Result a) -> SExpr -> Result [a]
unList f (SList values) = traverse f values
unList _ _ = bad
pair :: (a -> SExpr) -> (b -> SExpr) -> (a,b) -> SExpr
pair f g (a,b) = SList [f a,g b]
unPair :: (SExpr -> Result a) -> (SExpr -> Result b) -> SExpr -> Result (a,b)
unPair f g (SList [a,b]) = (,) <$> f a <*> g b
unPair _ _ _ = bad
optional :: (a -> SExpr) -> Maybe a -> SExpr
optional _ Nothing = form "absent" []
optional f (Just value) = form "present" [f value]
unOptional :: (SExpr -> Result a) -> SExpr -> Result (Maybe a)
unOptional _ (SList [SAtom "absent"]) = Right Nothing
unOptional f (SList [SAtom "present",value]) = Just <$> f value
unOptional _ _ = bad
canonical :: (Eq a,Codec a) => SExpr -> Result a
canonical wire = do
  value <- dec wire
  unless (enc value == wire) (W.bad "non-canonical source diagnostic")
  pure value
instance Codec Natural where enc = W.encodeNat; dec = W.decodeNat
instance Codec Prop where enc = Raw.encodeAtom; dec = either (W.bad . show) Right . Raw.decodeAtomSExpr
instance Codec Term where
  enc (TNum s) = form "num" [text s]
  enc (TStr s) = form "str" [text s]
  enc (TCon (FunSym f) args) = form "con" (text f : map enc args)
  dec (SList [SAtom "num",SAtom s]) = Right (TNum s)
  dec (SList [SAtom "str",SAtom s]) = Right (TStr s)
  dec (SList (SAtom "con" : SAtom f : args)) = TCon (FunSym f) <$> traverse dec args
  dec _ = bad
instance Codec CorePattern where
  enc (PatternVariable param) = form "var" [enc param]
  enc (PatternNumber s) = form "num" [text s]
  enc (PatternString s) = form "str" [text s]
  enc (PatternConstructor (FunSym f) args) = form "con" (text f : map enc args)
  dec (SList [SAtom "var",param]) = PatternVariable <$> dec param
  dec (SList [SAtom "num",SAtom s]) = Right (PatternNumber s)
  dec (SList [SAtom "str",SAtom s]) = Right (PatternString s)
  dec (SList (SAtom "con" : SAtom f : args)) = PatternConstructor (FunSym f) <$> traverse dec args
  dec _ = bad
instance Codec CoreAtomPattern where
  enc (CoreAtomPattern (Pred p) args) = form "apat" (text p : map enc args)
  dec (SList (SAtom "apat" : SAtom p : args)) = CoreAtomPattern (Pred p) <$> traverse dec args
  dec _ = bad
instance Codec CoreAssurance where
  enc CoreNone = text "none"
  enc CoreTrusted = text "trusted"
  enc (CoreCertificate (CoreBackend backend version) digest payload) = form "cert" [enc backend,enc version,enc digest,payload]
  dec (SAtom "none") = Right CoreNone
  dec (SAtom "trusted") = Right CoreTrusted
  dec (SList [SAtom "cert",backend,version,digest,payload]) = CoreCertificate <$> (CoreBackend <$> dec backend <*> dec version) <*> dec digest <*> pure payload
  dec _ = bad
encodePosition :: CorePosition -> SExpr
encodePosition = form "pos" . map enc
decodePosition :: SExpr -> Result CorePosition
decodePosition (SList (SAtom "pos" : steps)) = traverse dec steps
decodePosition _ = bad
instance Codec A.Mode where
  enc A.Strict = text "strict"
  enc A.Defeasible = text "defeasible"
  dec (SAtom "strict") = Right A.Strict
  dec (SAtom "defeasible") = Right A.Defeasible
  dec _ = bad
instance Codec A.LeafKind where enc = Source.encodeLeafKind; dec = Source.decodeLeafKind
instance Codec A.Provenance where enc = Source.encodeProvenance; dec = Source.decodeProvenance
instance Codec CoreSupport where
  enc (CoreLeaf leaf) = form "leaf" [enc leaf]
  enc (CoreRule rule theta premises discharges holes assurance) = form "inst"
    [enc rule,form "subst" (map (pair enc enc) theta),form "premises" (map enc premises),
     form "discharges" (map (pair enc enc) discharges),form "holes" (map enc holes),form "assurance" [enc assurance]]
  dec (SList [SAtom "leaf",leaf]) = CoreLeaf <$> dec leaf
  dec (SList [SAtom "inst",rule,SList (SAtom "subst" : theta),SList (SAtom "premises" : premises),
      SList (SAtom "discharges" : discharges),SList (SAtom "holes" : holes),SList [SAtom "assurance",assurance]]) =
    CoreRule <$> dec rule <*> traverse (unPair dec dec) theta <*> traverse dec premises <*> traverse (unPair dec dec) discharges <*> traverse dec holes <*> dec assurance
  dec _ = bad
instance Codec A.LeafId where enc (A.LeafId s) = text s; dec wire = A.LeafId <$> unText wire
instance Codec A.RuleId where enc (A.RuleId s) = text s; dec wire = A.RuleId <$> unText wire
instance Codec A.ArgId where enc (A.ArgId s) = text s; dec wire = A.ArgId <$> unText wire
instance Codec A.PropId where enc (A.PropId s) = text s; dec wire = A.PropId <$> unText wire
instance Codec A.QuestionId where enc (A.QuestionId s) = text s; dec wire = A.QuestionId <$> unText wire
instance Codec A.Param where enc (A.Param s) = text s; dec wire = A.Param <$> unText wire
instance Codec A.PolicyId where enc (A.PolicyId s) = text s; dec wire = A.PolicyId <$> unText wire
instance Codec A.GroupId where enc (A.GroupId s) = text s; dec wire = A.GroupId <$> unText wire
instance Codec A.ValueName where enc (A.ValueName s) = text s; dec wire = A.ValueName <$> unText wire
instance Codec A.BackendId where enc (A.BackendId s) = text s; dec wire = A.BackendId <$> unText wire
instance Codec A.TheoryDigest where enc (A.TheoryDigest s) = text s; dec wire = A.TheoryDigest <$> unText wire
instance Codec ObjectId where enc (ObjectId s) = text s; dec wire = ObjectId <$> unText wire
instance Codec T.CoreVersion where enc (T.CoreVersion s) = text s; dec wire = T.CoreVersion <$> unText wire
instance Codec T.BackendIdentity where
  enc (T.BackendIdentity backend (T.BackendVersion version)) = form "backend" [enc backend,text version]
  dec (SList [SAtom "backend",backend,version]) = T.BackendIdentity <$> dec backend <*> (T.BackendVersion <$> unText version)
  dec _ = bad

instance Codec CoreBackend where
  enc (CoreBackend a0 a1) = form "backend" [enc a0,enc a1]
  dec (SList [SAtom "backend",a0,a1]) = CoreBackend <$> dec a0 <*> dec a1
  dec _ = bad

instance Codec CorePositionStep where
  enc (CorePremise a0) = form "prem" [enc a0]
  enc (CoreQuestion a0) = form "ques" [enc a0]
  dec (SList [SAtom "prem",a0]) = CorePremise <$> dec a0
  dec (SList [SAtom "ques",a0]) = CoreQuestion <$> dec a0
  dec _ = bad

instance Codec CoreLocation where
  enc CoreRoot = form "root" []
  enc (CorePremiseLocation a0 a1) = form "premise" [enc a0,enc a1]
  enc (CoreQuestionLocation a0 a1) = form "question" [enc a0,enc a1]
  dec (SList [SAtom "root"]) = Right CoreRoot
  dec (SList [SAtom "premise",a0,a1]) = CorePremiseLocation <$> dec a0 <*> dec a1
  dec (SList [SAtom "question",a0,a1]) = CoreQuestionLocation <$> dec a0 <*> dec a1
  dec _ = bad

instance Codec DeclarationLocation where
  enc (ArgumentLocation a0) = form "argument" [enc a0]
  enc (AttackLocation a0) = form "attack" [enc a0]
  dec (SList [SAtom "argument",a0]) = ArgumentLocation <$> dec a0
  dec (SList [SAtom "attack",a0]) = AttackLocation <$> dec a0
  dec _ = bad

instance Codec SignatureFault where
  enc MalformedSigma = form "malformed-sigma" []
  enc PolicyIllSorted = form "policy-ill-sorted" []
  enc GroundIllSorted = form "ground-ill-sorted" []
  enc ArgumentsIllSorted = form "args-ill-sorted" []
  dec (SList [SAtom "malformed-sigma"]) = Right MalformedSigma
  dec (SList [SAtom "policy-ill-sorted"]) = Right PolicyIllSorted
  dec (SList [SAtom "ground-ill-sorted"]) = Right GroundIllSorted
  dec (SList [SAtom "args-ill-sorted"]) = Right ArgumentsIllSorted
  dec _ = bad

instance Codec ReferenceFault where
  enc (ReferenceMissingLeaf a0) = form "missing-leaf" [enc a0]
  enc (ReferenceMissingRule a0) = form "missing-rule" [enc a0]
  enc (ReferenceUndeclaredSource a0) = form "undeclared-attack-source" [enc a0]
  enc (ReferenceUndeclaredTarget a0) = form "undeclared-attack-target" [enc a0]
  dec (SList [SAtom "missing-leaf",a0]) = ReferenceMissingLeaf <$> dec a0
  dec (SList [SAtom "missing-rule",a0]) = ReferenceMissingRule <$> dec a0
  dec (SList [SAtom "undeclared-attack-source",a0]) = ReferenceUndeclaredSource <$> dec a0
  dec (SList [SAtom "undeclared-attack-target",a0]) = ReferenceUndeclaredTarget <$> dec a0
  dec _ = bad

instance Codec SubstitutionFault where
  enc (SubstitutionDuplicateKeys a0) = form "duplicate-keys" [list enc a0]
  enc (SubstitutionDomainMismatch a0 a1) = form "domain-mismatch" [list enc a0,list enc a1]
  enc (SubstitutionPremiseInstantiation a0) = form "premise-instantiation" [list enc a0]
  enc (SubstitutionConclusionInstantiation a0) = form "conclusion-instantiation" [enc a0]
  dec (SList [SAtom "duplicate-keys",a0]) = SubstitutionDuplicateKeys <$> unList dec a0
  dec (SList [SAtom "domain-mismatch",a0,a1]) = SubstitutionDomainMismatch <$> unList dec a0 <*> unList dec a1
  dec (SList [SAtom "premise-instantiation",a0]) = SubstitutionPremiseInstantiation <$> unList dec a0
  dec (SList [SAtom "conclusion-instantiation",a0]) = SubstitutionConclusionInstantiation <$> dec a0
  dec _ = bad

instance Codec PremiseFault where
  enc (PremiseCount a0 a1) = form "count" [enc a0,enc a1]
  enc (PremiseMismatch a0 a1) = form "mismatch" [enc a0,enc a1]
  dec (SList [SAtom "count",a0,a1]) = PremiseCount <$> dec a0 <*> dec a1
  dec (SList [SAtom "mismatch",a0,a1]) = PremiseMismatch <$> dec a0 <*> dec a1
  dec _ = bad

instance Codec QuestionFault where
  enc (QuestionDuplicateDeclarations a0) = form "duplicate-declarations" [list enc a0]
  enc (QuestionDuplicateDischarges a0) = form "duplicate-discharges" [list enc a0]
  enc (QuestionDuplicateHoles a0) = form "duplicate-holes" [list enc a0]
  enc (QuestionUncovered a0 a1 a2) = form "uncovered" [list enc a0,list enc a1,list enc a2]
  enc (QuestionOverlap a0 a1) = form "overlap" [list enc a0,list enc a1]
  enc (QuestionUndeclaredDischarge a0 a1) = form "undeclared-discharge" [list enc a0,list enc a1]
  enc (QuestionUndeclaredHole a0 a1) = form "undeclared-hole" [list enc a0,list enc a1]
  dec (SList [SAtom "duplicate-declarations",a0]) = QuestionDuplicateDeclarations <$> unList dec a0
  dec (SList [SAtom "duplicate-discharges",a0]) = QuestionDuplicateDischarges <$> unList dec a0
  dec (SList [SAtom "duplicate-holes",a0]) = QuestionDuplicateHoles <$> unList dec a0
  dec (SList [SAtom "uncovered",a0,a1,a2]) = QuestionUncovered <$> unList dec a0 <*> unList dec a1 <*> unList dec a2
  dec (SList [SAtom "overlap",a0,a1]) = QuestionOverlap <$> unList dec a0 <*> unList dec a1
  dec (SList [SAtom "undeclared-discharge",a0,a1]) = QuestionUndeclaredDischarge <$> unList dec a0 <*> unList dec a1
  dec (SList [SAtom "undeclared-hole",a0,a1]) = QuestionUndeclaredHole <$> unList dec a0 <*> unList dec a1
  dec _ = bad

instance Codec DischargeFault where
  enc (DischargeAnswerInstantiation a0 a1) = form "answer-instantiation" [enc a0,enc a1]
  enc (DischargeConclusionMismatch a0 a1 a2) = form "conclusion-mismatch" [enc a0,enc a1,enc a2]
  dec (SList [SAtom "answer-instantiation",a0,a1]) = DischargeAnswerInstantiation <$> dec a0 <*> dec a1
  dec (SList [SAtom "conclusion-mismatch",a0,a1,a2]) = DischargeConclusionMismatch <$> dec a0 <*> dec a1 <*> dec a2
  dec _ = bad

instance Codec AssuranceFault where
  enc (AssuranceQuestionsPresent a0 a1) = form "questions-present" [list enc a0,list enc a1]
  enc (AssuranceWrongMode a0 a1) = form "wrong-mode" [enc a0,enc a1]
  enc AssuranceTrustedDisallowed = form "trusted-disallowed" []
  enc (AssuranceCertifierUnallowlisted a0 a1) = form "certifier-unallowlisted" [enc a0,enc a1]
  dec (SList [SAtom "questions-present",a0,a1]) = AssuranceQuestionsPresent <$> unList dec a0 <*> unList dec a1
  dec (SList [SAtom "wrong-mode",a0,a1]) = AssuranceWrongMode <$> dec a0 <*> dec a1
  dec (SList [SAtom "trusted-disallowed"]) = Right AssuranceTrustedDisallowed
  dec (SList [SAtom "certifier-unallowlisted",a0,a1]) = AssuranceCertifierUnallowlisted <$> dec a0 <*> dec a1
  dec _ = bad

instance Codec BackendFault where
  enc (BackendMissing a0) = form "backend-missing" [enc a0]
  enc (DigestMissing a0 a1) = form "digest-missing" [enc a0,enc a1]
  enc (ReplayRejected a0 a1 a2) = form "replay-rejected" [enc a0,enc a1,id a2]
  dec (SList [SAtom "backend-missing",a0]) = BackendMissing <$> dec a0
  dec (SList [SAtom "digest-missing",a0,a1]) = DigestMissing <$> dec a0 <*> dec a1
  dec (SList [SAtom "replay-rejected",a0,a1,a2]) = ReplayRejected <$> dec a0 <*> dec a1 <*> Right a2
  dec _ = bad

instance Codec AttackKind where
  enc RebutKind = form "rebut" []
  enc UndercutKind = form "undercut" []
  enc UndermineKind = form "undermine" []
  dec (SList [SAtom "rebut"]) = Right RebutKind
  dec (SList [SAtom "undercut"]) = Right UndercutKind
  dec (SList [SAtom "undermine"]) = Right UndermineKind
  dec _ = bad

instance Codec OccurrenceKind where
  enc RuleOccurrence = form "rule" []
  enc LeafOccurrence = form "leaf" []
  dec (SList [SAtom "rule"]) = Right RuleOccurrence
  dec (SList [SAtom "leaf"]) = Right LeafOccurrence
  dec _ = bad

instance Codec PositionFault where
  enc UndefinedPosition = form "undefined-position" []
  enc (WrongOccurrenceKind a0 a1) = form "wrong-occurrence-kind" [enc a0,enc a1]
  dec (SList [SAtom "undefined-position"]) = Right UndefinedPosition
  dec (SList [SAtom "wrong-occurrence-kind",a0,a1]) = WrongOccurrenceKind <$> dec a0 <*> dec a1
  dec _ = bad

instance Codec RelationFault where
  enc (RelationMissingRule a0) = form "missing-target-rule" [enc a0]
  enc (RelationConclusionInstantiation a0 a1) = form "target-conclusion-instantiation" [enc a0,enc a1]
  enc (RelationMissingLeaf a0) = form "missing-target-leaf" [enc a0]
  enc (RelationStrictTarget a0) = form "strict-target" [enc a0]
  enc (RelationMissingContrary a0 a1) = form "missing-contrary" [enc a0,enc a1]
  enc (RelationMissingException a0) = form "missing-exception" [enc a0]
  enc (RelationExceptionInstantiation a0 a1) = form "exception-instantiation" [enc a0,enc a1]
  enc (RelationExceptionMismatch a0 a1 a2) = form "exception-mismatch" [enc a0,enc a1,enc a2]
  dec (SList [SAtom "missing-target-rule",a0]) = RelationMissingRule <$> dec a0
  dec (SList [SAtom "target-conclusion-instantiation",a0,a1]) = RelationConclusionInstantiation <$> dec a0 <*> dec a1
  dec (SList [SAtom "missing-target-leaf",a0]) = RelationMissingLeaf <$> dec a0
  dec (SList [SAtom "strict-target",a0]) = RelationStrictTarget <$> dec a0
  dec (SList [SAtom "missing-contrary",a0,a1]) = RelationMissingContrary <$> dec a0 <*> dec a1
  dec (SList [SAtom "missing-exception",a0]) = RelationMissingException <$> dec a0
  dec (SList [SAtom "exception-instantiation",a0,a1]) = RelationExceptionInstantiation <$> dec a0 <*> dec a1
  dec (SList [SAtom "exception-mismatch",a0,a1,a2]) = RelationExceptionMismatch <$> dec a0 <*> dec a1 <*> dec a2
  dec _ = bad

instance Codec CheckFault where
  enc (CheckR1 a0 a1) = form "r1" [enc a0,enc a1]
  enc (CheckR3 a0 a1) = form "r3" [enc a0,enc a1]
  enc (CheckR4 a0 a1) = form "r4" [enc a0,enc a1]
  enc (CheckR5 a0 a1) = form "r5" [enc a0,enc a1]
  enc (CheckR6 a0 a1) = form "r6" [enc a0,enc a1]
  enc (CheckR7 a0 a1) = form "r7" [enc a0,enc a1]
  enc (CheckR10 a0 a1 a2 a3) = form "r10" [enc a0,encodePosition a1,enc a2,enc a3]
  enc (CheckR11 a0 a1 a2 a3) = form "r11" [enc a0,encodePosition a1,enc a2,enc a3]
  enc (CheckR13 a0 a1) = form "r13" [enc a0,enc a1]
  dec (SList [SAtom "r1",a0,a1]) = CheckR1 <$> dec a0 <*> dec a1
  dec (SList [SAtom "r3",a0,a1]) = CheckR3 <$> dec a0 <*> dec a1
  dec (SList [SAtom "r4",a0,a1]) = CheckR4 <$> dec a0 <*> dec a1
  dec (SList [SAtom "r5",a0,a1]) = CheckR5 <$> dec a0 <*> dec a1
  dec (SList [SAtom "r6",a0,a1]) = CheckR6 <$> dec a0 <*> dec a1
  dec (SList [SAtom "r7",a0,a1]) = CheckR7 <$> dec a0 <*> dec a1
  dec (SList [SAtom "r10",a0,a1,a2,a3]) = CheckR10 <$> dec a0 <*> decodePosition a1 <*> dec a2 <*> dec a3
  dec (SList [SAtom "r11",a0,a1,a2,a3]) = CheckR11 <$> dec a0 <*> decodePosition a1 <*> dec a2 <*> dec a3
  dec (SList [SAtom "r13",a0,a1]) = CheckR13 <$> dec a0 <*> dec a1
  dec _ = bad

instance Codec MissingConflict where
  enc (MissingConflict a0 a1 a2 a3) = form "missing-conflict" [enc a0,enc a1,enc a2,enc a3]
  dec (SList [SAtom "missing-conflict",a0,a1,a2,a3]) = MissingConflict <$> dec a0 <*> dec a1 <*> dec a2 <*> dec a3
  dec _ = bad

instance Codec ProgramFault where
  enc (ProgramRejection a0 a1) = form "rejection" [enc a0,enc a1]
  enc (ProgramDuplicateArgument a0 a1) = form "duplicate-argument" [enc a0,enc a1]
  enc (ProgramMissingConflict a0) = form "missing-conflict" [enc a0]
  dec (SList [SAtom "rejection",a0,a1]) = ProgramRejection <$> dec a0 <*> dec a1
  dec (SList [SAtom "duplicate-argument",a0,a1]) = ProgramDuplicateArgument <$> dec a0 <*> dec a1
  dec (SList [SAtom "missing-conflict",a0]) = ProgramMissingConflict <$> dec a0
  dec _ = bad

instance Codec CoreError where
  enc (CoreDuplicateRule rule first second) = form "duplicate-rule" [form "duplicate-rule" [enc rule,enc first,enc second]]
  enc (CoreSignature fault) = form "signature" [enc fault]
  enc (CoreScopeViolation rule parameter) = form "scope-violation" [form "scope-violation" [enc rule,enc parameter]]
  enc (CorePolicyViolation rule conclusion contrary) = form "policy-violation" [form "policy-violation" [enc rule,enc conclusion,pair enc enc contrary]]
  enc (CoreProgram fault) = form "program" [enc fault]
  dec (SList [SAtom "duplicate-rule",SList [SAtom "duplicate-rule",rule,first,second]]) = CoreDuplicateRule <$> dec rule <*> dec first <*> dec second
  dec (SList [SAtom "signature",fault]) = CoreSignature <$> dec fault
  dec (SList [SAtom "scope-violation",SList [SAtom "scope-violation",rule,parameter]]) = CoreScopeViolation <$> dec rule <*> dec parameter
  dec (SList [SAtom "policy-violation",SList [SAtom "policy-violation",rule,conclusion,contrary]]) = CorePolicyViolation <$> dec rule <*> dec conclusion <*> unPair dec dec contrary
  dec (SList [SAtom "program",fault]) = CoreProgram <$> dec fault
  dec _ = bad

instance Codec ReplayError where
  enc (UnsupportedCore a0) = form "unsupported-core" [enc a0]
  enc ReplayPolicyMismatch = form "policy-mismatch" []
  enc BackendMismatch = form "backend-mismatch" []
  enc DuplicateBackend = form "duplicate-backend" []
  enc (UnsupportedBackend a0) = form "unsupported-backend" [enc a0]
  enc DuplicateTheory = form "duplicate-theory" []
  enc TheoryMismatch = form "theory-mismatch" []
  enc ArtifactMismatch = form "artifact-mismatch" []
  dec (SList [SAtom "unsupported-core",a0]) = UnsupportedCore <$> dec a0
  dec (SList [SAtom "policy-mismatch"]) = Right ReplayPolicyMismatch
  dec (SList [SAtom "backend-mismatch"]) = Right BackendMismatch
  dec (SList [SAtom "duplicate-backend"]) = Right DuplicateBackend
  dec (SList [SAtom "unsupported-backend",a0]) = UnsupportedBackend <$> dec a0
  dec (SList [SAtom "duplicate-theory"]) = Right DuplicateTheory
  dec (SList [SAtom "theory-mismatch"]) = Right TheoryMismatch
  dec (SList [SAtom "artifact-mismatch"]) = Right ArtifactMismatch
  dec _ = bad

instance Codec SurfaceError where
  enc Unsupported = form "unsupported" []
  enc (PolicyMismatch a0 a1) = form "policy-mismatch" [enc a0,enc a1]
  enc (DuplicateLeafId a0) = form "duplicate-leaf-id" [enc a0]
  enc (DuplicateArgumentId a0) = form "duplicate-arg-id" [enc a0]
  enc (DuplicateClaimId a0) = form "duplicate-claim-id" [enc a0]
  enc (DuplicateValueName a0) = form "duplicate-value-name" [enc a0]
  enc (MalformedRuleNamespace a0) = form "malformed-rule-namespace" [enc a0]
  enc (InvalidValueBinding a0) = form "invalid-value-binding" [enc a0]
  enc (InvalidComparison a0) = form "invalid-comparison" [enc a0]
  enc (InvalidInferredArgument a0) = form "invalid-inferred-argument" [enc a0]
  enc (InvalidNamedCertificate a0) = form "invalid-named-certificate" [enc a0]
  enc (SourceConclusionMismatch a0 a1) = form "conclusion-mismatch" [enc a0,enc a1]
  enc (SourceChallengeTargetUndeclared a0) = form "challenge-target-undeclared" [enc a0]
  enc (InvalidSurfaceAttack a0 a1) = form "invalid-surface-attack" [enc a0,enc a1]
  enc (SourceUnknownStatusClaim a0) = form "unknown-status-claim" [enc a0]
  enc (SourceDuplicateGroupId a0) = form "duplicate-group-id" [enc a0]
  enc (SourceGroupRepeatedMember a0 a1) = form "group-repeated-member" [enc a0,enc a1]
  enc (SourceGroupTooFewMembers a0) = form "group-too-few-members" [enc a0]
  enc (SourceGroupMemberUndeclared a0 a1) = form "group-member-undeclared" [enc a0,enc a1]
  enc (NoncanonicalPremiseLabels a0) = form "noncanonical-premise-labels" [enc a0]
  enc (SourceDuplicateAdmissionKey a0 a1) = form "duplicate-admission-key" [enc a0,enc a1]
  enc (AdmissionRejected a0) = form "admission-rejected" [enc a0]
  dec (SList [SAtom "unsupported"]) = Right Unsupported
  dec (SList [SAtom "policy-mismatch",a0,a1]) = PolicyMismatch <$> dec a0 <*> dec a1
  dec (SList [SAtom "duplicate-leaf-id",a0]) = DuplicateLeafId <$> dec a0
  dec (SList [SAtom "duplicate-arg-id",a0]) = DuplicateArgumentId <$> dec a0
  dec (SList [SAtom "duplicate-claim-id",a0]) = DuplicateClaimId <$> dec a0
  dec (SList [SAtom "duplicate-value-name",a0]) = DuplicateValueName <$> dec a0
  dec (SList [SAtom "malformed-rule-namespace",a0]) = MalformedRuleNamespace <$> dec a0
  dec (SList [SAtom "invalid-value-binding",a0]) = InvalidValueBinding <$> dec a0
  dec (SList [SAtom "invalid-comparison",a0]) = InvalidComparison <$> dec a0
  dec (SList [SAtom "invalid-inferred-argument",a0]) = InvalidInferredArgument <$> dec a0
  dec (SList [SAtom "invalid-named-certificate",a0]) = InvalidNamedCertificate <$> dec a0
  dec (SList [SAtom "conclusion-mismatch",a0,a1]) = SourceConclusionMismatch <$> dec a0 <*> dec a1
  dec (SList [SAtom "challenge-target-undeclared",a0]) = SourceChallengeTargetUndeclared <$> dec a0
  dec (SList [SAtom "invalid-surface-attack",a0,a1]) = InvalidSurfaceAttack <$> dec a0 <*> dec a1
  dec (SList [SAtom "unknown-status-claim",a0]) = SourceUnknownStatusClaim <$> dec a0
  dec (SList [SAtom "duplicate-group-id",a0]) = SourceDuplicateGroupId <$> dec a0
  dec (SList [SAtom "group-repeated-member",a0,a1]) = SourceGroupRepeatedMember <$> dec a0 <*> dec a1
  dec (SList [SAtom "group-too-few-members",a0]) = SourceGroupTooFewMembers <$> dec a0
  dec (SList [SAtom "group-member-undeclared",a0,a1]) = SourceGroupMemberUndeclared <$> dec a0 <*> dec a1
  dec (SList [SAtom "noncanonical-premise-labels",a0]) = NoncanonicalPremiseLabels <$> dec a0
  dec (SList [SAtom "duplicate-admission-key",a0,a1]) = SourceDuplicateAdmissionKey <$> dec a0 <*> dec a1
  dec (SList [SAtom "admission-rejected",a0]) = AdmissionRejected <$> dec a0
  dec _ = bad

instance Codec SourceError where
  enc (Structural a0) = form "structural" [enc a0]
  enc (EvidenceRequired a0) = form "evidence" [enc a0]
  enc EvidenceSyntax = form "evidence-syntax" []
  enc (GroupConflict a0) = form "group-conflict" [enc a0]
  dec (SList [SAtom "structural",a0]) = Structural <$> dec a0
  dec (SList [SAtom "evidence",a0]) = EvidenceRequired <$> dec a0
  dec (SList [SAtom "evidence-syntax"]) = Right EvidenceSyntax
  dec (SList [SAtom "group-conflict",a0]) = GroupConflict <$> dec a0
  dec _ = bad

instance Codec T.EvidenceStage where
  enc T.EvidenceBindingStage = form "binding" []
  enc T.EvidenceCaptureStage = form "capture" []
  enc T.EvidenceExtractionStage = form "extraction" []
  dec (SList [SAtom "binding"]) = Right T.EvidenceBindingStage
  dec (SList [SAtom "capture"]) = Right T.EvidenceCaptureStage
  dec (SList [SAtom "extraction"]) = Right T.EvidenceExtractionStage
  dec _ = bad

instance Codec T.EvidenceError where
  enc (T.EvidenceError a0 a1 a2 a3) = form "admission-error" [enc a0,enc a1,optional enc a2,text a3]
  dec (SList [SAtom "admission-error",a0,a1,a2,a3]) = T.EvidenceError <$> dec a0 <*> dec a1 <*> unOptional dec a2 <*> unText a3
  dec _ = bad

instance Codec SourceDiagnostic where
  enc (SourceDiagnostic a0) = form "source" [enc a0]
  enc (EvidenceDiagnostic a0) = form "evidence" [enc a0]
  enc (CoreDiagnostic a0) = form "core" [enc a0]
  dec (SList [SAtom "source",a0]) = SourceDiagnostic <$> dec a0
  dec (SList [SAtom "evidence",a0]) = EvidenceDiagnostic <$> dec a0
  dec (SList [SAtom "core",a0]) = CoreDiagnostic <$> dec a0
  dec _ = bad

instance Codec SourceRejection where
  enc (ReplayRejection a0) = form "replay" [enc a0]
  enc (SourceRejection a0) = form "source" [enc a0]
  enc (MissingEvidence a0) = form "missing-evidence" [enc a0]
  enc (UnselectedCertificate a0 a1 a2) = form "unselected-certificate" [enc a0,enc a1,enc a2]
  dec (SList [SAtom "replay",a0]) = ReplayRejection <$> dec a0
  dec (SList [SAtom "source",a0]) = SourceRejection <$> dec a0
  dec (SList [SAtom "missing-evidence",a0]) = MissingEvidence <$> dec a0
  dec (SList [SAtom "unselected-certificate",a0,a1,a2]) = UnselectedCertificate <$> dec a0 <*> dec a1 <*> dec a2
  dec _ = bad

encodeRejection :: SourceRejection -> SExpr
encodeRejection = enc
decodeRejection :: SExpr -> Result SourceRejection
decodeRejection = canonical

encodeSourceDiagnostic :: SourceDiagnostic -> SExpr
encodeSourceDiagnostic = enc
decodeSourceDiagnostic :: SExpr -> Result SourceDiagnostic
decodeSourceDiagnostic = canonical

encodeCoreError :: CoreError -> SExpr
encodeCoreError = enc
decodeCoreError :: SExpr -> Result CoreError
decodeCoreError = canonical

encodeCheckFault :: CheckFault -> SExpr
encodeCheckFault = enc
decodeCheckFault :: SExpr -> Result CheckFault
decodeCheckFault = canonical
