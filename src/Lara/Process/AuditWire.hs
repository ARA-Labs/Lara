-- | Frozen source-audit and family component codecs. Only framing is checked;
-- duplicate metadata and semantically invalid levels remain typed input data.
module Lara.Process.AuditWire
  ( encodeInt, decodeInt, encodeRat, decodeRat, encodeBool, decodeBool
  , encodeOption, decodeOption, encodeAssignment, decodeAssignment
  , encodeMethod, decodeMethod, encodePayloadMode, decodePayloadMode
  , encodeResidualAssumption, decodeResidualAssumption, encodeStatKind, decodeStatKind
  , encodeAssociationFault, decodeAssociationFault, encodeApplicationError, decodeApplicationError
  , encodeBridgeError, decodeBridgeError, encodeSupportFault, decodeSupportFault
  , encodeArtifactFault, decodeArtifactFault, encodeLedgerFault, decodeLedgerFault
  , encodeGuaranteeFault, decodeGuaranteeFault, encodeWitnessFault, decodeWitnessFault
  , encodeProvenanceError, decodeProvenanceError
  , encodeAssumptionId, decodeAssumptionId, encodeInterpretationId, decodeInterpretationId
  , encodeKindKey, decodeKindKey, encodeSupportBinding, decodeSupportBinding
  , encodeMethodBinding, decodeMethodBinding, encodeArtifactInterpretation, decodeArtifactInterpretation
  , encodeArtifactSpec, decodeArtifactSpec, encodeLedger, decodeLedger
  , encodeKindSpec, decodeKindSpec, encodeClaimBinding, decodeClaimBinding
  , encodeLedgerBinding, decodeLedgerBinding, encodeGuaranteeBinding, decodeGuaranteeBinding
  , encodeWitnessSpec, decodeWitnessSpec, encodeCaptureAssumption, decodeCaptureAssumption
  , encodeConfig, decodeConfig
  , encodeSlotId, decodeSlotId, encodeChoiceId, decodeChoiceId
  , encodeGuard, decodeGuard, encodeChoice, decodeChoice, encodeSlot, decodeSlot
  , encodeSelection, decodeSelection, encodeCompletion, decodeCompletion
  ) where

import Control.Monad (unless)
import Data.Ratio ((%), numerator, denominator)
import qualified Lara.AST as A
import Lara.Prop (Prop)
import Lara.Strict (SExpr (..))
import qualified Lara.Wire as Raw
import qualified Lara.Process.Wire as W
import qualified Lara.Process.Types as P
import qualified Lara.Process.Source.Wire as Source
import qualified Lara.Process.Source.Diagnostic.Wire as Diagnostic
import Lara.Process.Audit.Types

type Result = Either W.Error
form :: String -> [SExpr] -> SExpr
form = W.tagged
bad :: Result a
bad = W.bad "malformed audit or family constructor"
canonical :: Eq a => (a -> SExpr) -> (SExpr -> Result a) -> SExpr -> Result a
canonical encode decode wire = do
  value <- decode wire
  unless (encode value == wire) (W.bad "non-canonical audit or family encoding")
  pure value
list :: (a -> SExpr) -> [a] -> SExpr
list encode = SList . map encode
unList :: (SExpr -> Result a) -> SExpr -> Result [a]
unList decode (SList values) = traverse decode values
unList _ _ = bad
closed :: Eq a => [(a,String)] -> a -> SExpr
closed table value = case lookup value table of
  Just tag -> form tag []
  Nothing -> error "closed audit vocabulary"
unClosed :: [(a,String)] -> SExpr -> Result a
unClosed table (SList [SAtom tag]) = go table
  where
    go [] = bad
    go ((value,text) : rest)
      | tag == text = Right value
      | otherwise = go rest
unClosed _ _ = bad

encodeInt :: Integer -> SExpr
encodeInt value
  | value >= 0 = form "integer-natural" [W.encodeNat (fromInteger value)]
  | otherwise = form "integer-negative-successor" [W.encodeNat (fromInteger (-value-1))]
decodeInt :: SExpr -> Result Integer
decodeInt (SList [SAtom "integer-natural",value]) = toInteger <$> W.decodeNat value
decodeInt (SList [SAtom "integer-negative-successor",value]) = (\n -> -toInteger n-1) <$> W.decodeNat value
decodeInt _ = bad
encodeRat :: Rational -> SExpr
encodeRat value = form "rational" [encodeInt (numerator value),W.encodeNat (fromInteger (denominator value))]
decodeRat :: SExpr -> Result Rational
decodeRat = canonical encodeRat raw
  where
    raw (SList [SAtom "rational",num,den]) = do
      n <- decodeInt num
      d <- W.decodeNat den
      if d == 0 then bad else pure (n % toInteger d)
    raw _ = bad
encodeBool :: Bool -> SExpr
encodeBool False = SAtom "false"
encodeBool True = SAtom "true"
decodeBool :: SExpr -> Result Bool
decodeBool (SAtom "false") = Right False
decodeBool (SAtom "true") = Right True
decodeBool _ = bad
encodeOption :: (a -> SExpr) -> Maybe a -> SExpr
encodeOption _ Nothing = form "none" []
encodeOption encode (Just value) = form "some" [encode value]
decodeOption :: (SExpr -> Result a) -> SExpr -> Result (Maybe a)
decodeOption _ (SList [SAtom "none"]) = Right Nothing
decodeOption decode (SList [SAtom "some",value]) = Just <$> decode value
decodeOption _ _ = bad

methods :: [(Method,String)]
methods = [(Two,"two"),(Low,"low"),(Up,"up"),(Disjunction,"disjunction"),(Conjunction,"conjunction"),(ConditionalFalse,"conditional-false")]
encodeMethod :: Method -> SExpr
encodeMethod = closed methods
decodeMethod :: SExpr -> Result Method
decodeMethod = unClosed methods
payloadModes :: [(PayloadMode,String)]
payloadModes = [(ConditionalPayload,"conditional"),(AppliedPayload,"applied")]
encodePayloadMode :: PayloadMode -> SExpr
encodePayloadMode = closed payloadModes
decodePayloadMode :: SExpr -> Result PayloadMode
decodePayloadMode = unClosed payloadModes
residuals :: [(ResidualAssumption,String)]
residuals = [(InterpretationFidelity,"interpretation-fidelity"),(PhysicalSampling,"physical-sampling"),(CaptureAdequacy,"capture-adequacy"),(RuntimeRefinement,"runtime-refinement")]
encodeResidualAssumption :: ResidualAssumption -> SExpr
encodeResidualAssumption = closed residuals
decodeResidualAssumption :: SExpr -> Result ResidualAssumption
decodeResidualAssumption = unClosed residuals
statKinds :: [(StatKind,String)]
statKinds = [(PValue,"p-value"),(EValue,"e-value")]
encodeStatKind :: StatKind -> SExpr
encodeStatKind = closed statKinds
decodeStatKind :: SExpr -> Result StatKind
decodeStatKind = unClosed statKinds
associationFaults :: [(AssociationFault,String)]
associationFaults = [(AssociationInputClaim,"input-claim"),(AssociationSemanticClaim,"semantic-claim"),(AssociationMissingDeclaration,"missing-declaration"),(AssociationWrongArgument,"wrong-argument"),(AssociationNotAlternative,"not-alternative")]
encodeAssociationFault :: AssociationFault -> SExpr
encodeAssociationFault = closed associationFaults
decodeAssociationFault :: SExpr -> Result AssociationFault
decodeAssociationFault = unClosed associationFaults
applicationErrors :: [(ApplicationError,String)]
applicationErrors = [(ApplicationModelMismatch,"model-mismatch"),(ApplicationPremiseMismatch,"premise-mismatch"),(ApplicationProgramMismatch,"program-mismatch"),(ApplicationPostconditionMismatch,"postcondition-mismatch"),(ApplicationRunMismatch,"run-mismatch"),(ApplicationFailedPrecondition,"failed-precondition")]
encodeApplicationError :: ApplicationError -> SExpr
encodeApplicationError = closed applicationErrors
decodeApplicationError :: SExpr -> Result ApplicationError
decodeApplicationError = unClosed applicationErrors
ledgerFaults :: [(LedgerFault,String)]
ledgerFaults = [(AbsentRun,"absent-run"),(FamilyMismatch,"family-mismatch"),(AbsentResult,"absent-result"),(MissingKind,"missing-kind"),(MissingValue,"missing-value"),(MissingGuarantee,"missing-guarantee"),(MissingBound,"missing-bound"),(ZeroBound,"zero-bound"),(UnsupportedGuarantee,"unsupported-guarantee"),(ExceededBound,"exceeded-bound"),(NonFiniteLevel,"non-finite-level")]
encodeLedgerFault :: LedgerFault -> SExpr
encodeLedgerFault = closed ledgerFaults
decodeLedgerFault :: SExpr -> Result LedgerFault
decodeLedgerFault = unClosed ledgerFaults
bridgeErrors :: [(BridgeError,String)]
bridgeErrors = [(StaleSnapshot,"stale-snapshot"),(IncompatibleInterpretation,"incompatible-interpretation"),(IncompatibleMethod,"incompatible-method"),(IncompatibleClaim,"incompatible-claim"),(IncompatibleDependencies,"incompatible-dependencies"),(IncompatibleEvidence,"incompatible-evidence"),(IncompatibleBinding,"incompatible-binding"),(MissingSupport,"missing-support"),(BlockedSupport,"blocked-support"),(DefeatedSupport,"defeated-support"),(FailedDerivation,"failed-derivation"),(FalsePrecondition,"false-precondition")]
encodeBridgeError :: BridgeError -> SExpr
encodeBridgeError (BridgeApplication err) = form "application" [encodeApplicationError err]
encodeBridgeError value = closed bridgeErrors value
decodeBridgeError :: SExpr -> Result BridgeError
decodeBridgeError (SList [SAtom "application",err]) = BridgeApplication <$> decodeApplicationError err
decodeBridgeError wire = unClosed bridgeErrors wire
supportFaults :: [(SupportFault,String)]
supportFaults = [(SupportAbsent,"absent"),(SupportDifferentConclusion,"different-conclusion"),(SupportNotRetained,"not-retained"),(SupportAbsentNode,"absent-node"),(SupportNodeMismatch,"node-mismatch"),(SupportBlocked,"blocked")]
encodeSupportFault :: SupportFault -> SExpr
encodeSupportFault (SupportInference err) = form "inference" [Diagnostic.encodeCheckFault err]
encodeSupportFault (SupportIncomplete questions) = form "incomplete" [list (\(A.QuestionId q) -> SAtom q) questions]
encodeSupportFault value = closed supportFaults value
decodeSupportFault :: SExpr -> Result SupportFault
decodeSupportFault (SList [SAtom "inference",err]) = SupportInference <$> Diagnostic.decodeCheckFault err
decodeSupportFault (SList [SAtom "incomplete",questions]) = SupportIncomplete <$> unList (fmap A.QuestionId . W.decodeText) questions
decodeSupportFault wire = unClosed supportFaults wire
encodeArtifactFault :: ArtifactFault -> SExpr
encodeArtifactFault (ArtifactSupport (A.ArgId argument) fault) = form "support" [SAtom argument,encodeSupportFault fault]
encodeArtifactFault (ArtifactAssociation fault) = form "association" [encodeAssociationFault fault]
encodeArtifactFault (ArtifactMethod fault) = form "method" [encodeBridgeError fault]
decodeArtifactFault :: SExpr -> Result ArtifactFault
decodeArtifactFault (SList [SAtom "support",argument,fault]) = ArtifactSupport <$> (A.ArgId <$> W.decodeText argument) <*> decodeSupportFault fault
decodeArtifactFault (SList [SAtom "association",fault]) = ArtifactAssociation <$> decodeAssociationFault fault
decodeArtifactFault (SList [SAtom "method",fault]) = ArtifactMethod <$> decodeBridgeError fault
decodeArtifactFault _ = bad
encodeGuaranteeFault :: GuaranteeFault -> SExpr
encodeGuaranteeFault InvalidConditionalLevel = form "invalid-conditional-level" []
encodeGuaranteeFault (GuaranteeLedger fault) = form "ledger" [encodeLedgerFault fault]
decodeGuaranteeFault :: SExpr -> Result GuaranteeFault
decodeGuaranteeFault (SList [SAtom "invalid-conditional-level"]) = Right InvalidConditionalLevel
decodeGuaranteeFault (SList [SAtom "ledger",fault]) = GuaranteeLedger <$> decodeLedgerFault fault
decodeGuaranteeFault _ = bad
witnessFaults :: [(WitnessFault,String)]
witnessFaults = [(MissingClaim,"missing-claim"),(MissingWitness,"missing-witness"),(AmbiguousMetadata,"ambiguous-metadata"),(WrongClaim,"wrong-claim"),(StaleSource,"stale-source")]
encodeWitnessFault :: WitnessFault -> SExpr
encodeWitnessFault (WitnessArtifact fault) = form "artifact" [encodeArtifactFault fault]
encodeWitnessFault (WitnessGuarantee fault) = form "guarantee" [encodeGuaranteeFault fault]
encodeWitnessFault value = closed witnessFaults value
decodeWitnessFault :: SExpr -> Result WitnessFault
decodeWitnessFault (SList [SAtom "artifact",fault]) = WitnessArtifact <$> decodeArtifactFault fault
decodeWitnessFault (SList [SAtom "guarantee",fault]) = WitnessGuarantee <$> decodeGuaranteeFault fault
decodeWitnessFault wire = unClosed witnessFaults wire
encodeProvenanceError :: ProvenanceError -> SExpr
encodeProvenanceError ProvenanceShape = form "shape" []
encodeProvenanceError ProvenanceImplicitMatch = form "implicit-match" []
encodeProvenanceError (ProvenanceMissingRule (A.RuleId rule)) = form "missing-rule" [SAtom rule]
encodeProvenanceError (ProvenanceUnresolvedReference (A.ArgRef ref)) = form "unresolved-reference" [SAtom ref]
encodeProvenanceError (ProvenanceMissingArgument (A.ArgId arg)) = form "missing-argument" [SAtom arg]
encodeProvenanceError (ProvenanceDuplicateArgument (A.ArgId arg)) = form "duplicate-argument" [SAtom arg]
encodeProvenanceError (ProvenanceMissingNode node) = form "missing-node" [W.encodeNat node]
decodeProvenanceError :: SExpr -> Result ProvenanceError
decodeProvenanceError (SList [SAtom "shape"]) = Right ProvenanceShape
decodeProvenanceError (SList [SAtom "implicit-match"]) = Right ProvenanceImplicitMatch
decodeProvenanceError (SList [SAtom "missing-rule",rule]) = ProvenanceMissingRule . A.RuleId <$> W.decodeText rule
decodeProvenanceError (SList [SAtom "unresolved-reference",ref]) = ProvenanceUnresolvedReference . A.ArgRef <$> W.decodeText ref
decodeProvenanceError (SList [SAtom "missing-argument",arg]) = ProvenanceMissingArgument . A.ArgId <$> W.decodeText arg
decodeProvenanceError (SList [SAtom "duplicate-argument",arg]) = ProvenanceDuplicateArgument . A.ArgId <$> W.decodeText arg
decodeProvenanceError (SList [SAtom "missing-node",node]) = ProvenanceMissingNode <$> W.decodeNat node
decodeProvenanceError _ = bad

encodeAssumptionId :: AssumptionId -> SExpr
encodeAssumptionId (AssumptionId index) = form "assumption-id" [W.encodeNat index]
decodeAssumptionId :: SExpr -> Result AssumptionId
decodeAssumptionId (SList [SAtom "assumption-id",index]) = AssumptionId <$> W.decodeNat index
decodeAssumptionId _ = bad
encodeInterpretationId :: InterpretationId -> SExpr
encodeInterpretationId (InterpretationId index) = form "interpretation-id" [W.encodeNat index]
decodeInterpretationId :: SExpr -> Result InterpretationId
decodeInterpretationId (SList [SAtom "interpretation-id",index]) = InterpretationId <$> W.decodeNat index
decodeInterpretationId _ = bad
encodeKindKey :: KindKey -> SExpr
encodeKindKey (LeafKey (A.LeafId leaf)) = form "leaf" [SAtom leaf]
encodeKindKey (MethodKey (A.RuleId rule)) = form "method" [SAtom rule]
encodeKindKey (ArgumentKey (A.ArgId arg)) = form "argument" [SAtom arg]
decodeKindKey :: SExpr -> Result KindKey
decodeKindKey (SList [SAtom "leaf",leaf]) = LeafKey . A.LeafId <$> W.decodeText leaf
decodeKindKey (SList [SAtom "method",rule]) = MethodKey . A.RuleId <$> W.decodeText rule
decodeKindKey (SList [SAtom "argument",arg]) = ArgumentKey . A.ArgId <$> W.decodeText arg
decodeKindKey _ = bad
encodeProp :: Prop -> SExpr
encodeProp = Raw.encodeAtom
decodeProp :: SExpr -> Result Prop
decodeProp = canonical encodeProp (either (W.bad . show) Right . Raw.decodeAtomSExpr)
encodeSupportBinding :: SupportBinding -> SExpr
encodeSupportBinding (SupportBinding (A.ArgId argument) query) = form "support-binding" [SAtom argument,encodeProp query]
decodeSupportBinding :: SExpr -> Result SupportBinding
decodeSupportBinding (SList [SAtom "support-binding",argument,query]) = SupportBinding <$> (A.ArgId <$> W.decodeText argument) <*> decodeProp query
decodeSupportBinding _ = bad
encodeMethodBinding :: MethodBinding -> SExpr
encodeMethodBinding (MethodBinding method mode parameter first second residual) = form "method-binding"
  [encodeMethod method,encodePayloadMode mode,encodeInt parameter,encodeBool first,encodeBool second,list encodeResidualAssumption residual]
decodeMethodBinding :: SExpr -> Result MethodBinding
decodeMethodBinding (SList [SAtom "method-binding",method,mode,parameter,first,second,residual]) =
  MethodBinding <$> decodeMethod method <*> decodePayloadMode mode <*> decodeInt parameter <*> decodeBool first <*> decodeBool second <*> unList decodeResidualAssumption residual
decodeMethodBinding _ = bad
encodeArtifactInterpretation :: ArtifactInterpretation -> SExpr
encodeArtifactInterpretation (DeclaredInterpretation ident) = form "declared" [encodeInterpretationId ident]
encodeArtifactInterpretation (CheckedMethod method) = form "checked-method" [encodeMethodBinding method]
decodeArtifactInterpretation :: SExpr -> Result ArtifactInterpretation
decodeArtifactInterpretation (SList [SAtom "declared",ident]) = DeclaredInterpretation <$> decodeInterpretationId ident
decodeArtifactInterpretation (SList [SAtom "checked-method",method]) = CheckedMethod <$> decodeMethodBinding method
decodeArtifactInterpretation _ = bad
encodeArtifactSpec :: ArtifactSpec -> SExpr
encodeArtifactSpec (ArtifactSpec (A.ArgId argument) dependencies interpretation) = form "artifact-spec"
  [SAtom argument,list encodeSupportBinding dependencies,encodeArtifactInterpretation interpretation]
decodeArtifactSpec :: SExpr -> Result ArtifactSpec
decodeArtifactSpec (SList [SAtom "artifact-spec",argument,dependencies,interpretation]) =
  ArtifactSpec <$> (A.ArgId <$> W.decodeText argument) <*> unList decodeSupportBinding dependencies <*> decodeArtifactInterpretation interpretation
decodeArtifactSpec _ = bad
encodeLedger :: Ledger -> SExpr
encodeLedger (Ledger kind value bound guarantee) = form "ledger-fields"
  [encodeOption encodeStatKind kind,encodeOption encodeRat value,encodeOption W.encodeNat bound,encodeOption W.encodeWord guarantee]
decodeLedger :: SExpr -> Result Ledger
decodeLedger (SList [SAtom "ledger-fields",kind,value,bound,guarantee]) = Ledger
  <$> decodeOption decodeStatKind kind <*> decodeOption decodeRat value <*> decodeOption W.decodeNat bound <*> decodeOption (W.decodeWord "-guarantee-class") guarantee
decodeLedger _ = bad
encodeKindSpec :: KindSpec -> SExpr
encodeKindSpec (KindSpec source key upper assumption) = form "kind-spec"
  [Source.encodeSource source,encodeKindKey key,W.encodeWord upper,encodeOption encodeAssumptionId assumption]
decodeKindSpec :: SExpr -> Result KindSpec
decodeKindSpec (SList [SAtom "kind-spec",source,key,upper,assumption]) = KindSpec
  <$> Source.decodeSource source <*> decodeKindKey key <*> W.decodeWord "-evidence-kind" upper <*> decodeOption decodeAssumptionId assumption
decodeKindSpec _ = bad
encodeClaimBinding :: W.Names -> ClaimBinding -> SExpr
encodeClaimBinding names (ClaimBinding (P.ClaimId claim) (A.PropId declaration) query) = form "claim-binding"
  [W.encodeIdx (W.namesClaim names) claim,SAtom declaration,encodeProp query]
decodeClaimBinding :: W.Names -> SExpr -> Result ClaimBinding
decodeClaimBinding names (SList [SAtom "claim-binding",claim,declaration,query]) = ClaimBinding
  <$> (P.ClaimId <$> W.decodeIdx (W.namesClaim names) "claim" claim) <*> (A.PropId <$> W.decodeText declaration) <*> decodeProp query
decodeClaimBinding _ _ = bad
encodeLedgerBinding :: W.Names -> LedgerBinding -> SExpr
encodeLedgerBinding names (LedgerBinding (P.RunId run) (P.FamilyId family) outcome fields) = form "ledger-binding"
  [W.encodeIdx (W.namesRun names) run,W.encodeIdx (W.namesFamily names) family,W.encodeNat outcome,encodeLedger fields]
decodeLedgerBinding :: W.Names -> SExpr -> Result LedgerBinding
decodeLedgerBinding names (SList [SAtom "ledger-binding",run,family,outcome,fields]) = LedgerBinding
  <$> (P.RunId <$> W.decodeIdx (W.namesRun names) "run" run) <*> (P.FamilyId <$> W.decodeIdx (W.namesFamily names) "family" family)
  <*> W.decodeNat outcome <*> decodeLedger fields
decodeLedgerBinding _ _ = bad
encodeGuaranteeBinding :: W.Names -> GuaranteeBinding -> SExpr
encodeGuaranteeBinding _ (ConditionalGuarantee kind level) = form "conditional" [W.encodeWord kind,encodeRat level]
encodeGuaranteeBinding names (LedgerGuarantee binding) = form "ledger" [encodeLedgerBinding names binding]
decodeGuaranteeBinding :: W.Names -> SExpr -> Result GuaranteeBinding
decodeGuaranteeBinding _ (SList [SAtom "conditional",kind,level]) = ConditionalGuarantee <$> W.decodeWord "-guarantee-class" kind <*> decodeRat level
decodeGuaranteeBinding names (SList [SAtom "ledger",binding]) = LedgerGuarantee <$> decodeLedgerBinding names binding
decodeGuaranteeBinding _ _ = bad
encodeWitnessSpec :: W.Names -> WitnessSpec -> SExpr
encodeWitnessSpec names (WitnessSpec (P.WitnessId witness) (P.ClaimId claim) source artifact probed guarantee) = form "witness-spec"
  [W.encodeIdx (W.namesWitness names) witness,W.encodeIdx (W.namesClaim names) claim,Source.encodeSource source,
   encodeArtifactSpec artifact,list W.encodeWord probed,encodeGuaranteeBinding names guarantee]
decodeWitnessSpec :: W.Names -> SExpr -> Result WitnessSpec
decodeWitnessSpec names (SList [SAtom "witness-spec",witness,claim,source,artifact,probed,guarantee]) = WitnessSpec
  <$> (P.WitnessId <$> W.decodeIdx (W.namesWitness names) "witness" witness)
  <*> (P.ClaimId <$> W.decodeIdx (W.namesClaim names) "claim" claim) <*> Source.decodeSource source
  <*> decodeArtifactSpec artifact <*> unList (W.decodeWord "-error-kind") probed <*> decodeGuaranteeBinding names guarantee
decodeWitnessSpec _ _ = bad
encodeCaptureAssumption :: W.Names -> CaptureAssumption -> SExpr
encodeCaptureAssumption names (CaptureAssumption ident source key event (P.RunId run) basis) = form "capture-assumption"
  [encodeAssumptionId ident,Source.encodeSource source,encodeKindKey key,W.encodeStamped names event,W.encodeIdx (W.namesRun names) run,W.encodeWord basis]
decodeCaptureAssumption :: W.Names -> SExpr -> Result CaptureAssumption
decodeCaptureAssumption names (SList [SAtom "capture-assumption",ident,source,key,event,run,basis]) = CaptureAssumption
  <$> decodeAssumptionId ident <*> Source.decodeSource source <*> decodeKindKey key <*> W.decodeStamped names event
  <*> (P.RunId <$> W.decodeIdx (W.namesRun names) "run" run) <*> W.decodeWord "-admission-basis" basis
decodeCaptureAssumption _ _ = bad
encodeConfig :: W.Names -> AuditConfig -> SExpr
encodeConfig names (AuditConfig claims witnesses kinds assumptions) = form "audit-config"
  [list (encodeClaimBinding names) claims,list (encodeWitnessSpec names) witnesses,list encodeKindSpec kinds,list (encodeCaptureAssumption names) assumptions]
decodeConfig :: W.Names -> SExpr -> Result AuditConfig
decodeConfig names (SList [SAtom "audit-config",claims,witnesses,kinds,assumptions]) = AuditConfig
  <$> unList (decodeClaimBinding names) claims <*> unList (decodeWitnessSpec names) witnesses
  <*> unList decodeKindSpec kinds <*> unList (decodeCaptureAssumption names) assumptions
decodeConfig _ _ = bad

-- FamilyWire deliberately has no FamilySpec envelope. The inquiry document
-- owner combines its embedded process problem, source and slots.
encodeSlotId :: SlotId -> SExpr
encodeSlotId (SlotId index) = form "slot-id" [W.encodeNat index]
decodeSlotId :: SExpr -> Result SlotId
decodeSlotId (SList [SAtom "slot-id",index]) = SlotId <$> W.decodeNat index
decodeSlotId _ = bad
encodeChoiceId :: ChoiceId -> SExpr
encodeChoiceId (ChoiceId index) = form "choice-id" [W.encodeNat index]
decodeChoiceId :: SExpr -> Result ChoiceId
decodeChoiceId (SList [SAtom "choice-id",index]) = ChoiceId <$> W.decodeNat index
decodeChoiceId _ = bad
encodeGuard :: W.Names -> Guard -> SExpr
encodeGuard _ GuardTruth = form "truth" []
encodeGuard names (GuardQuery query) = form "query" [W.encodeQuery names query]
encodeGuard names (GuardPresent event) = form "present" [W.encodeStamped names event]
encodeGuard names (GuardBefore first second) = form "before" [W.encodeStamped names first,W.encodeStamped names second]
encodeGuard names (GuardNot guard) = form "not" [encodeGuard names guard]
encodeGuard names (GuardAnd left right) = form "and" [encodeGuard names left,encodeGuard names right]
encodeGuard names (GuardOr left right) = form "or" [encodeGuard names left,encodeGuard names right]
decodeGuard :: W.Names -> SExpr -> Result Guard
decodeGuard _ (SList [SAtom "truth"]) = Right GuardTruth
decodeGuard names (SList [SAtom "query",query]) = GuardQuery <$> W.decodeQuery names query
decodeGuard names (SList [SAtom "present",event]) = GuardPresent <$> W.decodeStamped names event
decodeGuard names (SList [SAtom "before",first,second]) = GuardBefore <$> W.decodeStamped names first <*> W.decodeStamped names second
decodeGuard names (SList [SAtom "not",guard]) = GuardNot <$> decodeGuard names guard
decodeGuard names (SList [SAtom "and",left,right]) = GuardAnd <$> decodeGuard names left <*> decodeGuard names right
decodeGuard names (SList [SAtom "or",left,right]) = GuardOr <$> decodeGuard names left <*> decodeGuard names right
decodeGuard _ _ = bad
encodeChoice :: W.Names -> Choice -> SExpr
encodeChoice names (Choice ident guard fragment) = form "choice" [encodeChoiceId ident,encodeGuard names guard,Source.encodeFragment fragment]
decodeChoice :: W.Names -> SExpr -> Result Choice
decodeChoice names (SList [SAtom "choice",ident,guard,fragment]) = Choice <$> decodeChoiceId ident <*> decodeGuard names guard <*> Source.decodeFragment fragment
decodeChoice _ _ = bad
encodeSlot :: W.Names -> Slot -> SExpr
encodeSlot names (Slot ident choices) = form "slot" [encodeSlotId ident,list (encodeChoice names) choices]
decodeSlot :: W.Names -> SExpr -> Result Slot
decodeSlot names (SList [SAtom "slot",ident,choices@(SList _)]) = Slot <$> decodeSlotId ident <*> unList (decodeChoice names) choices
decodeSlot _ _ = bad
encodeSelection :: W.Names -> Selection -> SExpr
encodeSelection names (Selection slot choice) = form "selection" [encodeSlotId slot,encodeChoice names choice]
decodeSelection :: W.Names -> SExpr -> Result Selection
decodeSelection names (SList [SAtom "selection",slot,choice]) = Selection <$> decodeSlotId slot <*> decodeChoice names choice
decodeSelection _ _ = bad
encodeCompletion :: W.Names -> Completion -> SExpr
encodeCompletion names (Completion history assignment) = form "completion" [list (W.encodeStamped names) history,list (encodeSelection names) assignment]
decodeCompletion :: W.Names -> SExpr -> Result Completion
decodeCompletion names (SList [SAtom "completion",history@(SList _),assignment@(SList _)]) =
  Completion <$> unList (W.decodeStamped names) history <*> unList (decodeSelection names) assignment
decodeCompletion _ _ = bad

-- Inquiry result/reference assignments carry identifiers, not full selections.
encodeAssignment :: [(SlotId,ChoiceId)] -> SExpr
encodeAssignment = list (\(slot,choice) -> SList [encodeSlotId slot,encodeChoiceId choice])
decodeAssignment :: SExpr -> Result [(SlotId,ChoiceId)]
decodeAssignment = unList pair
  where pair (SList [slot,choice]) = (,) <$> decodeSlotId slot <*> decodeChoiceId choice
        pair _ = bad
