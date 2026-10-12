-- | Canonical frozen analysis constructors. Wrapper profiles deliberately differ
-- from embedded process profiles: bare lists and a structural zero denominator.
module Lara.Process.AnalysisWire where

import Control.Monad (unless)
import Lara.Strict (SExpr (..))
import Lara.Process.Analysis
import qualified Lara.Process.AuditWire as Audit
import Lara.Process.Types
import qualified Lara.Process.Wire as W
import qualified Lara.Process.Source.Diagnostic.Wire as Diagnostic

type Result = Either W.Error
data Tag = ObservableTag | TargetTag | StatusObsTag | AuditObsTag | StatusTargetTag | AuditTargetTag
  | LiteralTag | SlotEqTag | SlotNeTag | PresentTag | AbsentTag | BeforeTag | FormulaTag | NotFormulaTag
  | RowTag | StabilityTag | SensitivityTag | DeletionTag | MinimalSetTag | AssumptionsTag
  deriving (Eq, Enum, Bounded)
instance W.WireWord Tag where
  wordText tag = case tag of
    ObservableTag -> "observable"; TargetTag -> "target"; StatusObsTag -> "status-obs"; AuditObsTag -> "audit-obs"
    StatusTargetTag -> "status-target"; AuditTargetTag -> "audit-target"; LiteralTag -> "literal"
    SlotEqTag -> "slot-eq"; SlotNeTag -> "slot-ne"; PresentTag -> "lit-present"; AbsentTag -> "lit-absent"
    BeforeTag -> "lit-before"; FormulaTag -> "lit-formula"; NotFormulaTag -> "lit-not-formula"
    RowTag -> "row"; StabilityTag -> "stability-result"; SensitivityTag -> "sensitivity-result"
    DeletionTag -> "deletion"; MinimalSetTag -> "minimal-set"; AssumptionsTag -> "assumption-result"
form :: Tag -> [SExpr] -> SExpr
form = W.tagged . W.wordText
headTag :: SExpr -> Maybe (Tag,[SExpr])
headTag (SList (SAtom tag:values)) = (,values) <$> W.parseWord tag
headTag _ = Nothing
bad :: Result a
bad = W.bad "malformed analysis constructor"
canonical :: (a -> SExpr) -> (SExpr -> Result a) -> SExpr -> Result a
canonical encode decode wire = do
  value <- decode wire
  unless (encode value == wire) (W.bad "non-canonical analysis encoding")
  pure value
encodeList :: (a -> SExpr) -> [a] -> SExpr
encodeList encode = SList . map encode
decodeList :: (SExpr -> Result a) -> SExpr -> Result [a]
decodeList decode (SList values) = traverse decode values
decodeList _ _ = bad
encodePair :: (a -> SExpr) -> (b -> SExpr) -> (a,b) -> SExpr
encodePair first second (a,b) = SList [first a,second b]
decodePair :: (SExpr -> Result a) -> (SExpr -> Result b) -> SExpr -> Result (a,b)
decodePair first second (SList [a,b]) = (,) <$> first a <*> second b
decodePair _ _ _ = bad
encodeOption :: (a -> SExpr) -> Maybe a -> SExpr
encodeOption _ Nothing = SList []
encodeOption encode (Just value) = SList [encode value]
decodeOption :: (SExpr -> Result a) -> SExpr -> Result (Maybe a)
decodeOption _ (SList []) = Right Nothing
decodeOption decode (SList [value]) = Just <$> decode value
decodeOption _ _ = bad
encodeProfile :: ProfileSpec -> SExpr
encodeProfile profile = W.form W.ProfileTag
  [encodeList W.encodeWord (profileAdmissible profile),encodeList W.encodeWord (profileAccepts profile),
   W.encodeGuarantee (profileGuarantee profile,profileNum profile,profileDen profile),
   encodeList W.encodeWord (profileProbes profile),W.encodeAcceptance (profileAcceptance profile)]
decodeProfile :: SExpr -> Result ProfileSpec
decodeProfile = canonical encodeProfile raw
  where
    raw value = case W.headTag value of
      Just (W.ProfileTag,[admissible,accepts,guarantee,probes,acceptance]) -> case W.headTag guarantee of
        Just (W.GuaranteeTag,[cls,num,den]) -> ProfileSpec
          <$> decodeList (W.decodeWord "evidence kind") admissible
          <*> decodeList (W.decodeWord "coverage kind") accepts
          <*> W.decodeWord "guarantee class" cls <*> W.decodeNat num <*> W.decodeNat den
          <*> decodeList (W.decodeWord "error kind") probes <*> W.decodeAcceptance acceptance
        _ -> bad
      _ -> bad
encodeClaim :: W.Names -> ClaimId -> SExpr
encodeClaim names = W.encodeIdx (W.namesClaim names) . claimIndex
decodeClaim :: W.Names -> SExpr -> Result ClaimId
decodeClaim names = fmap ClaimId . W.decodeIdx (W.namesClaim names) "claim"
encodeWitness :: W.Names -> WitnessId -> SExpr
encodeWitness names = W.encodeIdx (W.namesWitness names) . witnessIndex
decodeWitness :: W.Names -> SExpr -> Result WitnessId
decodeWitness names = fmap WitnessId . W.decodeIdx (W.namesWitness names) "witness"
encodeObservable :: W.Names -> Observable -> SExpr
encodeObservable names observable = form ObservableTag [case observable of
  StatusObservable claim -> form StatusObsTag [encodeClaim names claim]
  AuditObservable claim witness profile -> form AuditObsTag [encodeClaim names claim,encodeWitness names witness,encodeProfile profile]]
decodeObservable :: W.Names -> SExpr -> Result Observable
decodeObservable names = canonical (encodeObservable names) raw
  where
    raw value = case headTag value of
      Just (ObservableTag,[body]) -> case headTag body of
        Just (StatusObsTag,[claim]) -> StatusObservable <$> decodeClaim names claim
        Just (AuditObsTag,[claim,witness,profile]) -> AuditObservable <$> decodeClaim names claim <*> decodeWitness names witness <*> decodeProfile profile
        _ -> bad
      _ -> bad
encodeTarget :: W.Names -> Target -> SExpr
encodeTarget names target = form TargetTag [case target of
  StatusTarget claim expected -> form StatusTargetTag [encodeClaim names claim,Diagnostic.encodePublicStatus expected]
  AuditTarget claim witness profile -> form AuditTargetTag [encodeClaim names claim,encodeWitness names witness,encodeProfile profile]]
decodeTarget :: W.Names -> SExpr -> Result Target
decodeTarget names = canonical (encodeTarget names) raw
  where
    raw value = case headTag value of
      Just (TargetTag,[body]) -> case headTag body of
        Just (StatusTargetTag,[claim,expected]) -> StatusTarget <$> decodeClaim names claim <*> Diagnostic.decodePublicStatus expected
        Just (AuditTargetTag,[claim,witness,profile]) -> AuditTarget <$> decodeClaim names claim <*> decodeWitness names witness <*> decodeProfile profile
        _ -> bad
      _ -> bad
encodeLiteral :: W.Names -> Literal -> SExpr
encodeLiteral names literal = form LiteralTag [case literal of
  SlotEq slot choice -> form SlotEqTag [Audit.encodeSlotId slot,Audit.encodeChoiceId choice]
  SlotNe slot choice -> form SlotNeTag [Audit.encodeSlotId slot,Audit.encodeChoiceId choice]
  Present event -> form PresentTag [W.encodeStamped names event]
  Absent event -> form AbsentTag [W.encodeStamped names event]
  Before first second -> form BeforeTag [W.encodeStamped names first,W.encodeStamped names second]
  Formula query -> form FormulaTag [W.encodeQuery names query]
  NotFormula query -> form NotFormulaTag [W.encodeQuery names query]]
decodeLiteral :: W.Names -> SExpr -> Result Literal
decodeLiteral names = canonical (encodeLiteral names) raw
  where
    raw value = case headTag value of
      Just (LiteralTag,[body]) -> case headTag body of
        Just (SlotEqTag,[slot,choice]) -> SlotEq <$> Audit.decodeSlotId slot <*> Audit.decodeChoiceId choice
        Just (SlotNeTag,[slot,choice]) -> SlotNe <$> Audit.decodeSlotId slot <*> Audit.decodeChoiceId choice
        Just (PresentTag,[event]) -> Present <$> W.decodeStamped names event
        Just (AbsentTag,[event]) -> Absent <$> W.decodeStamped names event
        Just (BeforeTag,[first,second]) -> Before <$> W.decodeStamped names first <*> W.decodeStamped names second
        Just (FormulaTag,[query]) -> Formula <$> W.decodeQuery names query
        Just (NotFormulaTag,[query]) -> NotFormula <$> W.decodeQuery names query
        _ -> bad
      _ -> bad
encodeStabilityResult :: W.Names -> StabilityResult -> SExpr
encodeStabilityResult names result = form StabilityTag [encodeObservable names (stabilityObservable result),
  W.encodeNat (stabilityTotal result),W.encodeNat (stabilityAccepted result),W.encodeNat (stabilityRejected result),
  Audit.encodeBool (stabilityWhole result),Audit.encodeBool (stabilityAcceptedDomain result)]
decodeStabilityResult :: W.Names -> SExpr -> Result StabilityResult
decodeStabilityResult names = canonical (encodeStabilityResult names) raw
  where raw value = case headTag value of
          Just (StabilityTag,[observable,total,accepted,rejected,whole,domain]) -> StabilityResult
            <$> decodeObservable names observable <*> W.decodeNat total <*> W.decodeNat accepted <*> W.decodeNat rejected
            <*> Audit.decodeBool whole <*> Audit.decodeBool domain
          _ -> bad
encodeSensitivityRow :: W.Names -> SensitivityRow -> SExpr
encodeSensitivityRow names row = form RowTag [Audit.encodeCompletion names (sensitivityCompletion row),encodeList Audit.encodeSlotId (sensitivityChanged row)]
decodeSensitivityRow :: W.Names -> SExpr -> Result SensitivityRow
decodeSensitivityRow names value = case headTag value of
  Just (RowTag,[completion,changed]) -> SensitivityRow <$> Audit.decodeCompletion names completion <*> decodeList Audit.decodeSlotId changed
  _ -> bad
encodeSensitivityResult :: W.Names -> SensitivityResult -> SExpr
encodeSensitivityResult names result = form SensitivityTag [encodeObservable names (sensitivityObservable result),
  Audit.encodeCompletion names (sensitivityReference result),W.encodeNat (sensitivityTotal result),W.encodeNat (sensitivityCount result),
  encodeList (encodeSensitivityRow names) (sensitivityDiffering result),encodeList slots (sensitivityMinimal result),
  encodeList (encodePair slots (Audit.encodeCompletion names)) (sensitivityRealizing result)]
  where slots = encodeList Audit.encodeSlotId
decodeSensitivityResult :: W.Names -> SExpr -> Result SensitivityResult
decodeSensitivityResult names = canonical (encodeSensitivityResult names) raw
  where
    slots = decodeList Audit.decodeSlotId
    raw value = case headTag value of
      Just (SensitivityTag,[observable,reference,total,sensitive,differing,minimal,realizing]) -> SensitivityResult
        <$> decodeObservable names observable <*> Audit.decodeCompletion names reference <*> W.decodeNat total <*> W.decodeNat sensitive
        <*> decodeList (decodeSensitivityRow names) differing <*> decodeList slots minimal
        <*> decodeList (decodePair slots (Audit.decodeCompletion names)) realizing
      _ -> bad
encodeDeletion :: W.Names -> Deletion -> SExpr
encodeDeletion names deletion = form DeletionTag [encodeLiteral names (deletionLiteral deletion),
  encodeList (Audit.encodeCompletion names) (deletionSurviving deletion),encodeOption (Audit.encodeCompletion names) (deletionCounter deletion)]
decodeDeletion :: W.Names -> SExpr -> Result Deletion
decodeDeletion names value = case headTag value of
  Just (DeletionTag,[literal,surviving,counter]) -> Deletion <$> decodeLiteral names literal
    <*> decodeList (Audit.decodeCompletion names) surviving <*> decodeOption (Audit.decodeCompletion names) counter
  _ -> bad
encodeMinimalSet :: W.Names -> MinimalSet -> SExpr
encodeMinimalSet names result = form MinimalSetTag [encodeList (encodeLiteral names) (minimalLiterals result),
  encodeList (Audit.encodeCompletion names) (minimalSurviving result),encodeList (encodeDeletion names) (minimalDeletions result)]
decodeMinimalSet :: W.Names -> SExpr -> Result MinimalSet
decodeMinimalSet names value = case headTag value of
  Just (MinimalSetTag,[literals,surviving,deletions]) -> MinimalSet <$> decodeList (decodeLiteral names) literals
    <*> decodeList (Audit.decodeCompletion names) surviving <*> decodeList (decodeDeletion names) deletions
  _ -> bad
encodeAssumptionResult :: W.Names -> AssumptionResult -> SExpr
encodeAssumptionResult names result = form AssumptionsTag [encodeTarget names (assumptionTarget result),
  encodeList (encodeLiteral names) (assumptionCatalog result),W.encodeNat (assumptionTotal result),encodeList (encodeMinimalSet names) (assumptionMinimal result)]
decodeAssumptionResult :: W.Names -> SExpr -> Result AssumptionResult
decodeAssumptionResult names = canonical (encodeAssumptionResult names) raw
  where raw value = case headTag value of
          Just (AssumptionsTag,[target,catalog,total,minimal]) -> AssumptionResult <$> decodeTarget names target
            <*> decodeList (decodeLiteral names) catalog <*> W.decodeNat total <*> decodeList (decodeMinimalSet names) minimal
          _ -> bad
observableWellNamed :: W.Names -> Observable -> Bool
observableWellNamed names observable = case observable of
  StatusObservable claim -> claimOk claim
  AuditObservable claim witness _ -> claimOk claim && W.indexIn (W.namesWitness names) (witnessIndex witness)
  where claimOk = W.indexIn (W.namesClaim names) . claimIndex
targetWellNamed :: W.Names -> Target -> Bool
targetWellNamed names = observableWellNamed names . targetObservable
literalWellNamed :: W.Names -> Literal -> Bool
literalWellNamed names literal = case literal of
  SlotEq{} -> True; SlotNe{} -> True
  Present event -> W.stampedWellNamed names event; Absent event -> W.stampedWellNamed names event
  Before first second -> W.stampedWellNamed names first && W.stampedWellNamed names second
  Formula query -> W.queryWellNamed names query; NotFormula query -> W.queryWellNamed names query
