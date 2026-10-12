-- | Frozen impact/certificate and family-result constructors. Certificates are
-- syntax data: false fields, reordered reads and duplicate triples still decode.
module Lara.Process.ResultWire where

import Lara.Strict (SExpr (..))
import qualified Lara.AST as A
import Lara.Prop (Prop)
import qualified Lara.Wire as Raw
import Lara.Process.Analysis
import Lara.Process.Impact
import qualified Lara.Process.AnalysisWire as Analysis
import qualified Lara.Process.AuditWire as Audit
import qualified Lara.Process.Wire as W
import qualified Lara.Process.Source.Wire as Source
import qualified Lara.Process.Source.Diagnostic.Wire as Diagnostic

type Result = Either W.Error
data Tag = SideTag | BeforeTag | AfterTag | TransitionTag | RRTag | RATag | ARTag | AATag
  | EndpointTag | QueryImpactTag | ImpactTag | CertificateTag | ReadsTag | VerifiedTag | InvalidTag
  | SnapshotsFaultTag | IdentitiesFaultTag | OutcomeFaultTag | StatusFaultTag | SupportsFaultTag | GraphFaultTag | LocalityFaultTag | ReadsFaultTag
  | AbsentValTag | AtomValTag | AtomsValTag | NatValTag | NatsValTag | BoolValTag | NameValTag | NamesValTag | TextValTag | TextsValTag | SourceValTag
  | LeafContentKeyTag | LeafMetaKeyTag | RuleKeyTag | AdmissionKeyTag | AbsentKeyTag | GroupMemberKeyTag | GroupConflictKeyTag
  | RawEndpointKeyTag | RetentionKeyTag | SignatureKeyTag | ContraryKeyTag | SubstitutionKeyTag
  | TheoryKeyTag | DigestKeyTag | CertificateKeyTag | PremiseKeyTag | DischargeKeyTag | ConclusionKeyTag
  | SupportMemberKeyTag | HoleMemberKeyTag | ReferenceKeyTag | CheckedKeyTag | CompiledKeyTag | BlockedClosureKeyTag
  | BlockedQueryKeyTag | SupportNodesKeyTag | HoleNodesKeyTag | AttackKeyTag | WholeInputKeyTag
  | FamilyStatusTag | FamilyAuditTag | FamilyRowTag | FamilyAuditRowTag
  deriving (Eq, Enum, Bounded)
instance W.WireWord Tag where
  wordText tag = case tag of
    SideTag -> "side"; BeforeTag -> "before"; AfterTag -> "after"; TransitionTag -> "transition"
    RRTag -> "rejected-to-rejected"; RATag -> "rejected-to-accepted"; ARTag -> "accepted-to-rejected"; AATag -> "accepted-to-accepted"
    EndpointTag -> "endpoint-report"; QueryImpactTag -> "query-impact"; ImpactTag -> "impact-result"; CertificateTag -> "impact-certificate"
    ReadsTag -> "reads"; VerifiedTag -> "verified"; InvalidTag -> "invalid-certificate"
    SnapshotsFaultTag -> "mismatched-snapshots"; IdentitiesFaultTag -> "mismatched-identities"; OutcomeFaultTag -> "outcome-mismatch"
    StatusFaultTag -> "status-mismatch"; SupportsFaultTag -> "invalid-supports"; GraphFaultTag -> "invalid-graph"
    LocalityFaultTag -> "false-locality"; ReadsFaultTag -> "false-read-evidence"
    AbsentValTag -> "v-absent"; AtomValTag -> "v-atom"; AtomsValTag -> "v-atoms"; NatValTag -> "v-nat"; NatsValTag -> "v-nats"
    BoolValTag -> "v-bool"; NameValTag -> "v-name"; NamesValTag -> "v-names"; TextValTag -> "v-text"; TextsValTag -> "v-texts"; SourceValTag -> "v-source"
    LeafContentKeyTag -> "k-leaf-content"; LeafMetaKeyTag -> "k-leaf-meta"; RuleKeyTag -> "k-rule-lookup"
    AdmissionKeyTag -> "k-admission-lookup"; AbsentKeyTag -> "k-absent-lookup"; GroupMemberKeyTag -> "k-group-member"; GroupConflictKeyTag -> "k-group-conflict"
    RawEndpointKeyTag -> "k-raw-endpoint"; RetentionKeyTag -> "k-retention"; SignatureKeyTag -> "k-signature"
    ContraryKeyTag -> "k-policy-contrary"; SubstitutionKeyTag -> "k-substitution"; TheoryKeyTag -> "k-backend-theory"
    DigestKeyTag -> "k-backend-digest"; CertificateKeyTag -> "k-certificate-input"; PremiseKeyTag -> "k-premise-subterm"
    DischargeKeyTag -> "k-discharge-subterm"; ConclusionKeyTag -> "k-conclusion-equiv"
    SupportMemberKeyTag -> "k-support-member"; HoleMemberKeyTag -> "k-hole-member"; ReferenceKeyTag -> "k-reference-carrier"
    CheckedKeyTag -> "k-checked-carrier"; CompiledKeyTag -> "k-compiled-carrier"; BlockedClosureKeyTag -> "k-blocked-closure"
    BlockedQueryKeyTag -> "k-blocked-query"; SupportNodesKeyTag -> "k-support-nodes"; HoleNodesKeyTag -> "k-hole-nodes"
    AttackKeyTag -> "k-attack-edge"; WholeInputKeyTag -> "k-whole-input"
    FamilyStatusTag -> "family-status-result"; FamilyAuditTag -> "family-audit-result"; FamilyRowTag -> "family-row"; FamilyAuditRowTag -> "family-audit-row"
form :: Tag -> [SExpr] -> SExpr
form = W.tagged . W.wordText
headTag :: SExpr -> Maybe (Tag,[SExpr])
headTag (SList (SAtom tag:values)) = (,values) <$> W.parseWord tag
headTag _ = Nothing
bad :: Result a
bad = W.bad "malformed impact or family-result constructor"
encodeAtom :: Prop -> SExpr
encodeAtom = Raw.encodeAtom
decodeAtom :: SExpr -> Result Prop
decodeAtom = Analysis.canonical encodeAtom (either (W.bad . show) Right . Raw.decodeAtomSExpr)
encodeArg :: A.ArgId -> SExpr
encodeArg (A.ArgId argument) = SAtom argument
decodeArg :: SExpr -> Result A.ArgId
decodeArg = fmap A.ArgId . W.decodeText
encodeSide :: Side -> SExpr
encodeSide side = form SideTag [W.encodeWord (case side of BeforeSide -> BeforeTag; AfterSide -> AfterTag)]
decodeSide :: SExpr -> Result Side
decodeSide value = case headTag value of
  Just (SideTag,[SAtom text]) -> case W.parseWord text of
    Just BeforeTag -> Right BeforeSide; Just AfterTag -> Right AfterSide; _ -> bad
  _ -> bad
encodeImpactTransition :: ImpactTransition -> SExpr
encodeImpactTransition transition = form TransitionTag [W.encodeWord (case transition of
  RejectedToRejected -> RRTag; RejectedToAccepted -> RATag; AcceptedToRejected -> ARTag; AcceptedToAccepted -> AATag)]
decodeImpactTransition :: SExpr -> Result ImpactTransition
decodeImpactTransition value = case headTag value of
  Just (TransitionTag,[SAtom text]) -> case W.parseWord text of
    Just RRTag -> Right RejectedToRejected; Just RATag -> Right RejectedToAccepted
    Just ARTag -> Right AcceptedToRejected; Just AATag -> Right AcceptedToAccepted; _ -> bad
  _ -> bad
faultTag :: VerificationFault -> Tag
faultTag fault = case fault of
  MismatchedSnapshots -> SnapshotsFaultTag; MismatchedIdentities -> IdentitiesFaultTag; OutcomeMismatch -> OutcomeFaultTag
  StatusMismatch -> StatusFaultTag; InvalidSupports -> SupportsFaultTag; InvalidGraph -> GraphFaultTag
  FalseLocality -> LocalityFaultTag; FalseReadEvidence -> ReadsFaultTag
encodeVerificationFault :: VerificationFault -> SExpr
encodeVerificationFault fault = form (faultTag fault) []
decodeVerificationFault :: SExpr -> Result VerificationFault
decodeVerificationFault value = case headTag value of
  Just (tag,[]) -> maybe bad Right (lookup tag [(faultTag fault,fault) | fault <- [minBound..maxBound]])
  _ -> bad
encodeVerificationResult :: VerificationResult -> SExpr
encodeVerificationResult Verified = form VerifiedTag []
encodeVerificationResult (InvalidCertificate fault) = form InvalidTag [encodeVerificationFault fault]
decodeVerificationResult :: SExpr -> Result VerificationResult
decodeVerificationResult value = case headTag value of
  Just (VerifiedTag,[]) -> Right Verified
  Just (InvalidTag,[fault]) -> InvalidCertificate <$> decodeVerificationFault fault
  _ -> bad
encodeReadKey :: ReadKey -> SExpr
encodeReadKey key = case key of
  LeafContent (A.LeafId leaf) -> form LeafContentKeyTag [SAtom leaf]
  LeafMeta (A.LeafId leaf) -> form LeafMetaKeyTag [SAtom leaf]
  RuleLookup argument -> form RuleKeyTag [encodeArg argument]
  AdmissionLookup argument -> form AdmissionKeyTag [encodeArg argument]
  AbsentLookup argument -> form AbsentKeyTag [encodeArg argument]
  GroupMember argument -> form GroupMemberKeyTag [encodeArg argument]
  GroupConflict argument -> form GroupConflictKeyTag [encodeArg argument]
  RawEndpoint node -> form RawEndpointKeyTag [W.encodeNat node]
  Retention node -> form RetentionKeyTag [W.encodeNat node]
  Signature argument -> form SignatureKeyTag [encodeArg argument]
  PolicyContrary argument -> form ContraryKeyTag [encodeArg argument]
  Substitution argument -> form SubstitutionKeyTag [encodeArg argument]
  BackendTheory backend -> form TheoryKeyTag [Diagnostic.encodeBackend backend]
  BackendDigest backend -> form DigestKeyTag [Diagnostic.encodeBackend backend]
  CertificateInput backend -> form CertificateKeyTag [Diagnostic.encodeBackend backend]
  PremiseSubterm node -> form PremiseKeyTag [W.encodeNat node]
  DischargeSubterm node -> form DischargeKeyTag [W.encodeNat node]
  ConclusionEquiv argument -> form ConclusionKeyTag [encodeArg argument]
  SupportMember query node -> form SupportMemberKeyTag [encodeAtom query,W.encodeNat node]
  HoleMember query node -> form HoleMemberKeyTag [encodeAtom query,W.encodeNat node]
  ReferenceCarrier -> form ReferenceKeyTag []; CheckedCarrier -> form CheckedKeyTag []
  CompiledCarrier -> form CompiledKeyTag []; BlockedClosure -> form BlockedClosureKeyTag []
  BlockedQuery query -> form BlockedQueryKeyTag [encodeAtom query]
  SupportNodes query -> form SupportNodesKeyTag [encodeAtom query]
  HoleNodes query -> form HoleNodesKeyTag [encodeAtom query]
  AttackEdge source target -> form AttackKeyTag [W.encodeNat source,W.encodeNat target]
  WholeInput -> form WholeInputKeyTag []
decodeReadKey :: SExpr -> Result ReadKey
decodeReadKey = Analysis.canonical encodeReadKey raw
  where
    raw value = case headTag value of
      Just (LeafContentKeyTag,[leaf]) -> LeafContent . A.LeafId <$> W.decodeText leaf
      Just (LeafMetaKeyTag,[leaf]) -> LeafMeta . A.LeafId <$> W.decodeText leaf
      Just (RuleKeyTag,[argument]) -> RuleLookup <$> decodeArg argument
      Just (AdmissionKeyTag,[argument]) -> AdmissionLookup <$> decodeArg argument
      Just (AbsentKeyTag,[argument]) -> AbsentLookup <$> decodeArg argument
      Just (GroupMemberKeyTag,[argument]) -> GroupMember <$> decodeArg argument
      Just (GroupConflictKeyTag,[argument]) -> GroupConflict <$> decodeArg argument
      Just (RawEndpointKeyTag,[node]) -> RawEndpoint <$> W.decodeNat node
      Just (RetentionKeyTag,[node]) -> Retention <$> W.decodeNat node
      Just (SignatureKeyTag,[argument]) -> Signature <$> decodeArg argument
      Just (ContraryKeyTag,[argument]) -> PolicyContrary <$> decodeArg argument
      Just (SubstitutionKeyTag,[argument]) -> Substitution <$> decodeArg argument
      Just (TheoryKeyTag,[backend]) -> BackendTheory <$> Diagnostic.decodeBackend backend
      Just (DigestKeyTag,[backend]) -> BackendDigest <$> Diagnostic.decodeBackend backend
      Just (CertificateKeyTag,[backend]) -> CertificateInput <$> Diagnostic.decodeBackend backend
      Just (PremiseKeyTag,[node]) -> PremiseSubterm <$> W.decodeNat node
      Just (DischargeKeyTag,[node]) -> DischargeSubterm <$> W.decodeNat node
      Just (ConclusionKeyTag,[argument]) -> ConclusionEquiv <$> decodeArg argument
      Just (SupportMemberKeyTag,[query,node]) -> SupportMember <$> decodeAtom query <*> W.decodeNat node
      Just (HoleMemberKeyTag,[query,node]) -> HoleMember <$> decodeAtom query <*> W.decodeNat node
      Just (ReferenceKeyTag,[]) -> Right ReferenceCarrier; Just (CheckedKeyTag,[]) -> Right CheckedCarrier
      Just (CompiledKeyTag,[]) -> Right CompiledCarrier; Just (BlockedClosureKeyTag,[]) -> Right BlockedClosure
      Just (BlockedQueryKeyTag,[query]) -> BlockedQuery <$> decodeAtom query
      Just (SupportNodesKeyTag,[query]) -> SupportNodes <$> decodeAtom query
      Just (HoleNodesKeyTag,[query]) -> HoleNodes <$> decodeAtom query
      Just (AttackKeyTag,[source,target]) -> AttackEdge <$> W.decodeNat source <*> W.decodeNat target
      Just (WholeInputKeyTag,[]) -> Right WholeInput
      _ -> bad
encodeReadVal :: ReadVal -> SExpr
encodeReadVal value = case value of
  ReadAbsent -> form AbsentValTag []; ReadAtom atom -> form AtomValTag [encodeAtom atom]
  ReadAtoms atoms -> form AtomsValTag [Analysis.encodeList encodeAtom atoms]
  ReadNat node -> form NatValTag [W.encodeNat node]; ReadNats nodes -> form NatsValTag [Analysis.encodeList W.encodeNat nodes]
  ReadBool flag -> form BoolValTag [Audit.encodeBool flag]; ReadName name -> form NameValTag [encodeArg name]
  ReadNames names -> form NamesValTag [Analysis.encodeList encodeArg names]
  ReadText text -> form TextValTag [SAtom text]; ReadTexts texts -> form TextsValTag [Analysis.encodeList SAtom texts]
  ReadSource source -> form SourceValTag [Source.encodeSource source]
decodeReadVal :: SExpr -> Result ReadVal
decodeReadVal = Analysis.canonical encodeReadVal raw
  where raw value = case headTag value of
          Just (AbsentValTag,[]) -> Right ReadAbsent
          Just (AtomValTag,[atom]) -> ReadAtom <$> decodeAtom atom
          Just (AtomsValTag,[atoms]) -> ReadAtoms <$> Analysis.decodeList decodeAtom atoms
          Just (NatValTag,[node]) -> ReadNat <$> W.decodeNat node
          Just (NatsValTag,[nodes]) -> ReadNats <$> Analysis.decodeList W.decodeNat nodes
          Just (BoolValTag,[flag]) -> ReadBool <$> Audit.decodeBool flag
          Just (NameValTag,[name]) -> ReadName <$> decodeArg name
          Just (NamesValTag,[names]) -> ReadNames <$> Analysis.decodeList decodeArg names
          Just (TextValTag,[text]) -> ReadText <$> W.decodeText text
          Just (TextsValTag,[texts]) -> ReadTexts <$> Analysis.decodeList W.decodeText texts
          Just (SourceValTag,[source]) -> ReadSource <$> Source.decodeSource source
          _ -> bad
encodeReadEntry :: ReadEntry -> SExpr
encodeReadEntry (side,key,value) = form ReadsTag [encodeSide side,encodeReadKey key,encodeReadVal value]
decodeReadEntry :: SExpr -> Result ReadEntry
decodeReadEntry value = case headTag value of
  Just (ReadsTag,[side,key,recorded]) -> (,,) <$> decodeSide side <*> decodeReadKey key <*> decodeReadVal recorded
  _ -> bad
encodeEndpointReport :: EndpointReport -> SExpr
encodeEndpointReport report = form EndpointTag [Audit.encodeBool (endpointAccepted report),
  Analysis.encodeOption Diagnostic.encodeRejection (endpointRejection report),
  Analysis.encodeList W.encodeNat (endpointReferenceCarrier report),Analysis.encodeList W.encodeNat (endpointCheckedCarrier report),
  Analysis.encodeList W.encodeNat (endpointCompiledCarrier report),Analysis.encodeList encodeAtom (endpointBlockedQueries report),
  Analysis.encodeList (Analysis.encodePair encodeAtom (Analysis.encodeList encodeArg)) (endpointSupports report)]
decodeEndpointReport :: SExpr -> Result EndpointReport
decodeEndpointReport = Analysis.canonical encodeEndpointReport raw
  where raw value = case headTag value of
          Just (EndpointTag,[accepted,rejection,reference,checked,compiled,blocked,supports]) -> EndpointReport
            <$> Audit.decodeBool accepted <*> Analysis.decodeOption Diagnostic.decodeRejection rejection
            <*> Analysis.decodeList W.decodeNat reference <*> Analysis.decodeList W.decodeNat checked <*> Analysis.decodeList W.decodeNat compiled
            <*> Analysis.decodeList decodeAtom blocked <*> Analysis.decodeList (Analysis.decodePair decodeAtom (Analysis.decodeList decodeArg)) supports
          _ -> bad
encodeQueryImpact :: QueryImpact -> SExpr
encodeQueryImpact row = form QueryImpactTag [encodeAtom (impactQuery row),
  Analysis.encodeOption Diagnostic.encodePublicStatus (impactBeforeStatus row),Analysis.encodeOption Diagnostic.encodePublicStatus (impactAfterStatus row),
  Audit.encodeBool (impactQueryChanged row),Audit.encodeBool (impactQueryLocality row)]
decodeQueryImpact :: SExpr -> Result QueryImpact
decodeQueryImpact = Analysis.canonical encodeQueryImpact raw
  where raw value = case headTag value of
          Just (QueryImpactTag,[query,before,after,changed,locality]) -> QueryImpact <$> decodeAtom query
            <*> Analysis.decodeOption Diagnostic.decodePublicStatus before <*> Analysis.decodeOption Diagnostic.decodePublicStatus after
            <*> Audit.decodeBool changed <*> Audit.decodeBool locality
          _ -> bad
encodeImpactResult :: ImpactResult -> SExpr
encodeImpactResult result = form ImpactTag [encodeImpactTransition (impactTransition result),Analysis.encodeList encodeQueryImpact (impactRows result),
  Analysis.encodeList encodeAtom (impactChanged result),Analysis.encodeList encodeAtom (impactUnchanged result)]
decodeImpactResult :: SExpr -> Result ImpactResult
decodeImpactResult = Analysis.canonical encodeImpactResult raw
  where raw value = case headTag value of
          Just (ImpactTag,[transition,rows,changed,unchanged]) -> ImpactResult <$> decodeImpactTransition transition
            <*> Analysis.decodeList decodeQueryImpact rows <*> Analysis.decodeList decodeAtom changed <*> Analysis.decodeList decodeAtom unchanged
          _ -> bad
encodeImpactCertificate :: ImpactCertificate -> SExpr
encodeImpactCertificate certificate = form CertificateTag
  [Source.encodeSource (certificateBeforeInput certificate),Source.encodeSource (certificateAfterInput certificate),
   Analysis.encodeList encodeAtom (certificateQueries certificate),Source.encodeSnapshot (certificateBeforeSnapshot certificate),
   Source.encodeSnapshot (certificateAfterSnapshot certificate),Source.encodeReplay (certificateBeforeIdentity certificate),Source.encodeReplay (certificateAfterIdentity certificate),
   encodeEndpointReport (certificateBeforeReport certificate),encodeEndpointReport (certificateAfterReport certificate),
   encodeImpactTransition (certificateTransition certificate),Analysis.encodeList encodeQueryImpact (certificateRows certificate),
   Analysis.encodeList encodeAtom (certificateChanged certificate),Analysis.encodeList encodeAtom (certificateUnchanged certificate),
   Analysis.encodeList encodeAtom (certificateBlockedBefore certificate),Analysis.encodeList encodeAtom (certificateBlockedAfter certificate),
   Analysis.encodeList encodeArg (certificateCarrier certificate),Analysis.encodeList W.encodeNat (certificateNodeDiff certificate),
   Analysis.encodeList (Analysis.encodePair W.encodeNat W.encodeNat) (certificateEdgeDiff certificate),
   Analysis.encodeList (Analysis.encodePair encodeAtom Audit.encodeBool) (certificateLocality certificate),Analysis.encodeList encodeReadEntry (certificateReads certificate)]
decodeImpactCertificate :: SExpr -> Result ImpactCertificate
decodeImpactCertificate = Analysis.canonical encodeImpactCertificate raw
  where raw value = case headTag value of
          Just (CertificateTag,[beforeInput,afterInput,queries,beforeSnapshot,afterSnapshot,beforeIdentity,afterIdentity,
            beforeReport,afterReport,transition,rows,changed,unchanged,blockedBefore,blockedAfter,carrier,nodeDiff,edgeDiff,locality,readEntries]) -> ImpactCertificate
              <$> Source.decodeSource beforeInput <*> Source.decodeSource afterInput <*> Analysis.decodeList decodeAtom queries
              <*> Source.decodeSnapshot beforeSnapshot <*> Source.decodeSnapshot afterSnapshot
              <*> Source.decodeReplay beforeIdentity <*> Source.decodeReplay afterIdentity
              <*> decodeEndpointReport beforeReport <*> decodeEndpointReport afterReport <*> decodeImpactTransition transition
              <*> Analysis.decodeList decodeQueryImpact rows <*> Analysis.decodeList decodeAtom changed <*> Analysis.decodeList decodeAtom unchanged
              <*> Analysis.decodeList decodeAtom blockedBefore <*> Analysis.decodeList decodeAtom blockedAfter
              <*> Analysis.decodeList decodeArg carrier <*> Analysis.decodeList W.decodeNat nodeDiff
              <*> Analysis.decodeList (Analysis.decodePair W.decodeNat W.decodeNat) edgeDiff
              <*> Analysis.decodeList (Analysis.decodePair decodeAtom Audit.decodeBool) locality <*> Analysis.decodeList decodeReadEntry readEntries
          _ -> bad
encodeFamilyStatusRow :: W.Names -> FamilyStatusRow -> SExpr
encodeFamilyStatusRow names row = form FamilyRowTag [Analysis.encodeList (W.encodeStamped names) (familyStatusHistory row),
  Audit.encodeAssignment (familyStatusAssignment row),Analysis.encodeOption Diagnostic.encodeRejection (familyStatusRejection row),
  Analysis.encodeOption Diagnostic.encodePublicStatus (familyStatusValue row)]
decodeFamilyStatusRow :: W.Names -> SExpr -> Result FamilyStatusRow
decodeFamilyStatusRow names = Analysis.canonical (encodeFamilyStatusRow names) raw
  where raw value = case headTag value of
          Just (FamilyRowTag,[history,assignment,rejection,status]) -> FamilyStatusRow <$> Analysis.decodeList (W.decodeStamped names) history
            <*> Audit.decodeAssignment assignment <*> Analysis.decodeOption Diagnostic.decodeRejection rejection <*> Analysis.decodeOption Diagnostic.decodePublicStatus status
          _ -> bad
encodeFamilyAuditRow :: W.Names -> FamilyAuditRow -> SExpr
encodeFamilyAuditRow names row = form FamilyAuditRowTag [Analysis.encodeList (W.encodeStamped names) (familyAuditHistory row),
  Audit.encodeAssignment (familyAuditAssignment row),Analysis.encodeOption Diagnostic.encodeRejection (familyAuditRejection row),
  Analysis.encodeOption Audit.encodeBool (familyAuditValue row)]
decodeFamilyAuditRow :: W.Names -> SExpr -> Result FamilyAuditRow
decodeFamilyAuditRow names = Analysis.canonical (encodeFamilyAuditRow names) raw
  where raw value = case headTag value of
          Just (FamilyAuditRowTag,[history,assignment,rejection,audit]) -> FamilyAuditRow <$> Analysis.decodeList (W.decodeStamped names) history
            <*> Audit.decodeAssignment assignment <*> Analysis.decodeOption Diagnostic.decodeRejection rejection <*> Analysis.decodeOption Audit.decodeBool audit
          _ -> bad
encodeFamilyStatusResult :: W.Names -> FamilyStatusResult -> SExpr
encodeFamilyStatusResult names result = form FamilyStatusTag [Analysis.encodeList (encodeFamilyStatusRow names) (familyStatusRows result),
  W.encodeNat (familyStatusTotal result),W.encodeNat (familyStatusAccepted result),W.encodeNat (familyStatusRejected result),Audit.encodeBool (familyStatusVerdict result)]
decodeFamilyStatusResult :: W.Names -> SExpr -> Result FamilyStatusResult
decodeFamilyStatusResult names = Analysis.canonical (encodeFamilyStatusResult names) raw
  where raw value = case headTag value of
          Just (FamilyStatusTag,[rows,total,accepted,rejected,verdict]) -> FamilyStatusResult <$> Analysis.decodeList (decodeFamilyStatusRow names) rows
            <*> W.decodeNat total <*> W.decodeNat accepted <*> W.decodeNat rejected <*> Audit.decodeBool verdict
          _ -> bad
encodeFamilyAuditResult :: W.Names -> FamilyAuditResult -> SExpr
encodeFamilyAuditResult names result = form FamilyAuditTag [Analysis.encodeList (encodeFamilyAuditRow names) (familyAuditRows result),
  W.encodeNat (familyAuditTotal result),W.encodeNat (familyAuditAccepted result),W.encodeNat (familyAuditRejected result),Audit.encodeBool (familyAuditVerdict result)]
decodeFamilyAuditResult :: W.Names -> SExpr -> Result FamilyAuditResult
decodeFamilyAuditResult names = Analysis.canonical (encodeFamilyAuditResult names) raw
  where raw value = case headTag value of
          Just (FamilyAuditTag,[rows,total,accepted,rejected,verdict]) -> FamilyAuditResult <$> Analysis.decodeList (decodeFamilyAuditRow names) rows
            <*> W.decodeNat total <*> W.decodeNat accepted <*> W.decodeNat rejected <*> Audit.decodeBool verdict
          _ -> bad
