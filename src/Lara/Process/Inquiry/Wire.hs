module Lara.Process.Inquiry.Wire
  ( parseInquiryInputBS, parseInquiryInput, encodeInquiryInput
  , parseInquiryResult, encodeInquiryResult, parseInquiryError, encodeInquiryError
  ) where

import Control.Monad (unless)
import Data.ByteString (ByteString)
import Numeric.Natural (Natural)
import Lara.Strict (SExpr(..))
import Lara.Process.Inquiry.Types
import Lara.Process.Types (EventId(..))
import qualified Lara.Process.Wire as W
import qualified Lara.Process.AnalysisWire as A
import qualified Lara.Process.AuditWire as C
import qualified Lara.Process.ResultWire as R
import qualified Lara.Process.Source.Wire as S
import qualified Lara.Wire as Raw

type Result = Either RunRefusal
data Tag = InputTag | ResultTag | ErrorTag | SlotsTag | BindingsTag | KindsTag | AdmittedTag | CatalogTag | LimitsTag | RequestsTag
  | HistoriesTag | SourcesTag | BytesTag | DeclarationsTag | StepsTag | PairsTag | SubsetsTag
  | StatusTag | AuditTag | StableTag | SensitivityTag | SlotsSensitiveTag | MinimalTag | ImpactTag | VerifyTag | QueriesTag
  | ReferenceTag | RefHistoryTag | RefChoicesTag | MalformedTag | SyntaxTag | UnsupportedTag | VersionTag | UsageTag | IOTag
  | LimitTag | CounterTag | ActualTag | CapTag | HistoryVerdictTag | HistoryCountTag
  | StatusBodyTag | AuditBodyTag | StabilityBodyTag | SensitivityBodyTag | SlotsBodyTag | AssumptionsBodyTag | ImpactBodyTag | VerificationBodyTag
  deriving (Eq, Enum, Bounded)
instance W.WireWord Tag where
  wordText tag = case tag of
    InputTag -> "inquiry-input"; ResultTag -> "inquiry-result"; ErrorTag -> "inquiry-error"
    SlotsTag -> "slots"; BindingsTag -> "bindings"; KindsTag -> "kind-metadata"; AdmittedTag -> "admitted-assumptions"
    CatalogTag -> "assumption-catalog"; LimitsTag -> "inquiry-limits"; RequestsTag -> "requests"
    HistoriesTag -> "histories"; SourcesTag -> "sources"; BytesTag -> "source-bytes"; DeclarationsTag -> "declarations"
    StepsTag -> "search-steps"; PairsTag -> "pairs"; SubsetsTag -> "subsets"
    StatusTag -> "status"; AuditTag -> "audit"; StableTag -> "stable"; SensitivityTag -> "sensitivity"
    SlotsSensitiveTag -> "slots-sensitive"; MinimalTag -> "minimal-assumptions"; ImpactTag -> "impact"; VerifyTag -> "verify-impact"; QueriesTag -> "queries"
    ReferenceTag -> "reference"; RefHistoryTag -> "ref-history"; RefChoicesTag -> "ref-choices"
    MalformedTag -> "malformed"; SyntaxTag -> "syntax"; UnsupportedTag -> "unsupported"; VersionTag -> "version"; UsageTag -> "usage"; IOTag -> "io"
    LimitTag -> "limit"; CounterTag -> "counter"; ActualTag -> "actual"; CapTag -> "cap"
    HistoryVerdictTag -> "history-verdict"; HistoryCountTag -> "history-count"
    StatusBodyTag -> "status-body"; AuditBodyTag -> "audit-body"; StabilityBodyTag -> "stability-body"
    SensitivityBodyTag -> "sensitivity-body"; SlotsBodyTag -> "slots-sensitive-body"; AssumptionsBodyTag -> "assumptions-body"
    ImpactBodyTag -> "impact-body"; VerificationBodyTag -> "verification-body"
form :: Tag -> [SExpr] -> SExpr
form = W.tagged . W.wordText
bad :: Result a
bad = Left (Malformed "malformed inquiry constructor")
liftCodec :: Either W.Error a -> Result a
liftCodec = either (const bad) Right
canonical :: (a -> SExpr) -> (SExpr -> Result a) -> SExpr -> Result a
canonical encode decode wire = do
  value <- decode wire
  unless (encode value == wire) bad
  pure value
block :: Tag -> (SExpr -> Either W.Error a) -> SExpr -> Result [a]
block tag decode (SList (SAtom actual:values)) | W.parseWord actual == Just tag = liftCodec (traverse decode values)
block _ _ _ = bad
counterTag :: LimitCounter -> Tag
counterTag counter = case counter of
  Histories -> HistoriesTag; Sources -> SourcesTag; SourceBytes -> BytesTag
  Declarations -> DeclarationsTag; SearchSteps -> StepsTag; Pairs -> PairsTag; Subsets -> SubsetsTag
counterText :: LimitCounter -> String
counterText = W.wordText . counterTag
limitValues :: InquiryLimits -> [Natural]
limitValues l = [limitHistories l,limitSources l,limitSourceBytes l,limitDeclarations l,limitSearchSteps l,limitPairs l,limitSubsets l]
encodeLimits :: InquiryLimits -> SExpr
encodeLimits l = form LimitsTag [form (counterTag c) [W.encodeNat v] | (c,v) <- zip [minBound..maxBound] (limitValues l)]
decodeLimits :: SExpr -> Result InquiryLimits
decodeLimits = canonical encodeLimits $ \wire -> case wire of
  SList (SAtom tag:values) | W.parseWord tag == Just LimitsTag -> do
    counts <- traverse field (zip [minBound..maxBound] values)
    case counts of [h,s,b,d,t,p,u] | length values == 7 -> Right (InquiryLimits h s b d t p u); _ -> bad
  _ -> bad
  where field (counter,SList [SAtom tag,value]) | W.parseWord tag == Just (counterTag counter) = liftCodec (W.decodeNat value)
        field _ = bad
encodeRefusal :: RunRefusal -> SExpr
encodeRefusal refusal = case refusal of
  Malformed d -> form MalformedTag [SAtom d]; SyntaxError d -> form SyntaxTag [SAtom d]
  Unsupported d -> form UnsupportedTag [SAtom d]; Version d -> form VersionTag [SAtom d]
  Usage d -> form UsageTag [SAtom d]; IOFailure d -> form IOTag [SAtom d]
  Limit c actual cap -> form LimitTag [form CounterTag [SAtom (counterText c)],form ActualTag [W.encodeNat actual],form CapTag [W.encodeNat cap]]
decodeRefusal :: SExpr -> Result RunRefusal
decodeRefusal = canonical encodeRefusal $ \wire -> case wire of
  SList [SAtom tag,SAtom detail] -> case W.parseWord tag of
    Just MalformedTag -> Right (Malformed detail)
    Just SyntaxTag -> Right (SyntaxError detail)
    Just UnsupportedTag -> Right (Unsupported detail)
    Just VersionTag -> Right (Version detail)
    Just UsageTag -> Right (Usage detail)
    Just IOTag -> Right (IOFailure detail)
    _ -> bad
  SList [SAtom lim,SList [SAtom ctr,SAtom tag],SList [SAtom act,actual],SList [SAtom cp,cap]]
    | W.parseWord lim == Just LimitTag
    , W.parseWord ctr == Just CounterTag
    , W.parseWord act == Just ActualTag
    , W.parseWord cp == Just CapTag -> do
        counter <- case W.parseWord tag of
          Just HistoriesTag -> Right Histories
          Just SourcesTag -> Right Sources
          Just BytesTag -> Right SourceBytes
          Just DeclarationsTag -> Right Declarations
          Just StepsTag -> Right SearchSteps
          Just PairsTag -> Right Pairs
          Just SubsetsTag -> Right Subsets
          _ -> bad
        Limit counter <$> liftCodec (W.decodeNat actual) <*> liftCodec (W.decodeNat cap)
  _ -> bad
encodeReference :: W.Names -> ReferenceSpec -> SExpr
encodeReference names (ReferenceSpec history assignment) = form ReferenceTag
  [form RefHistoryTag [A.encodeList (W.encodeStamped names) history],form RefChoicesTag [C.encodeAssignment assignment]]
decodeReference :: W.Names -> SExpr -> Result ReferenceSpec
decodeReference names = canonical (encodeReference names) $ \wire -> case wire of
  SList [SAtom ref,SList [SAtom rh,history],SList [SAtom rc,assignment]]
    | W.parseWord ref == Just ReferenceTag
    , W.parseWord rh == Just RefHistoryTag
    , W.parseWord rc == Just RefChoicesTag ->
        ReferenceSpec <$> liftCodec (A.decodeList (W.decodeStamped names) history) <*> liftCodec (C.decodeAssignment assignment)
  _ -> bad
encodeRequest :: W.Names -> RequestSpec -> SExpr
encodeRequest n request = case request of
  StatusRequest l c -> form StatusTag [SAtom l,A.encodeClaim n c]
  AuditRequest l c w p -> form AuditTag [SAtom l,A.encodeClaim n c,A.encodeWitness n w,A.encodeProfile p]
  StableRequest l o -> form StableTag [SAtom l,A.encodeObservable n o]
  SensitivityRequest l r o -> form SensitivityTag [SAtom l,encodeReference n r,A.encodeObservable n o]
  SlotsSensitiveRequest l r o -> form SlotsSensitiveTag [SAtom l,encodeReference n r,A.encodeObservable n o]
  MinimalAssumptionsRequest l t -> form MinimalTag [SAtom l,A.encodeTarget n t]
  ImpactRequest l b a qs -> form ImpactTag [SAtom l,S.encodeSource b,S.encodeSource a,form QueriesTag (map (A.encodeClaim n) qs)]
  VerifyImpactRequest l b a c -> form VerifyTag [SAtom l,S.encodeSource b,S.encodeSource a,R.encodeImpactCertificate c]
decodeRequest :: W.Names -> SExpr -> Result RequestSpec
decodeRequest n = canonical (encodeRequest n) $ \wire -> case wire of
  SList (SAtom tag:args) -> case W.parseWord tag of
    Just StatusTag -> case args of
      [SAtom l,c] -> StatusRequest l <$> liftCodec (A.decodeClaim n c)
      _ -> bad
    Just AuditTag -> case args of
      [SAtom l,c,w,p] -> AuditRequest l <$> liftCodec (A.decodeClaim n c) <*> liftCodec (A.decodeWitness n w) <*> liftCodec (A.decodeProfile p)
      _ -> bad
    Just StableTag -> case args of
      [SAtom l,o] -> StableRequest l <$> liftCodec (A.decodeObservable n o)
      _ -> bad
    Just SensitivityTag -> case args of
      [SAtom l,r,o] -> SensitivityRequest l <$> decodeReference n r <*> liftCodec (A.decodeObservable n o)
      _ -> bad
    Just SlotsSensitiveTag -> case args of
      [SAtom l,r,o] -> SlotsSensitiveRequest l <$> decodeReference n r <*> liftCodec (A.decodeObservable n o)
      _ -> bad
    Just MinimalTag -> case args of
      [SAtom l,t] -> MinimalAssumptionsRequest l <$> liftCodec (A.decodeTarget n t)
      _ -> bad
    Just ImpactTag -> case args of
      [SAtom l,b,a,qs] -> ImpactRequest l <$> liftCodec (S.decodeSource b) <*> liftCodec (S.decodeSource a) <*> block QueriesTag (A.decodeClaim n) qs
      _ -> bad
    Just VerifyTag -> case args of
      [SAtom l,b,a,c] -> VerifyImpactRequest l <$> liftCodec (S.decodeSource b) <*> liftCodec (S.decodeSource a) <*> liftCodec (R.decodeImpactCertificate c)
      _ -> bad
    _ -> bad
  _ -> bad
encodeInquiryInput :: InquiryInput -> SExpr
encodeInquiryInput input = let n = W.documentNames (inquiryProcess input) in form InputTag
  [SAtom "1",W.encodeDocument (inquiryProcess input),S.encodeSource (inquiryBase input)
  ,form SlotsTag (map (C.encodeSlot n) (inquirySlots input))
  ,form BindingsTag [A.encodeList (C.encodeClaimBinding n) (inquiryClaims input),A.encodeList (C.encodeWitnessSpec n) (inquiryWitnesses input)]
  ,form KindsTag (map C.encodeKindSpec (inquiryKinds input))
  ,form AdmittedTag (map (C.encodeCaptureAssumption n) (inquiryAssumptions input))
  ,form CatalogTag (map (A.encodeLiteral n) (inquiryCatalog input))
  ,encodeLimits (inquiryLimits input),form RequestsTag (map (encodeRequest n) (inquiryRequests input))]
decodeInput :: SExpr -> Result InquiryInput
decodeInput = canonical encodeInquiryInput $ \wire -> case wire of
  SList [SAtom inp,SAtom "1",proc,base,slots,SList [SAtom bnd,claims,witnesses],kinds,assumptions,catalog,limits,SList (SAtom req:requests)]
    | W.parseWord inp == Just InputTag
    , W.parseWord bnd == Just BindingsTag
    , W.parseWord req == Just RequestsTag -> do
        document <- liftCodec (W.decodeDocument proc)
        let n = W.documentNames document
        InquiryInput document <$> liftCodec (S.decodeSource base) <*> block SlotsTag (C.decodeSlot n) slots
          <*> liftCodec (A.decodeList (C.decodeClaimBinding n) claims) <*> liftCodec (A.decodeList (C.decodeWitnessSpec n) witnesses)
          <*> block KindsTag C.decodeKindSpec kinds <*> block AdmittedTag (C.decodeCaptureAssumption n) assumptions
          <*> block CatalogTag (A.decodeLiteral n) catalog <*> decodeLimits limits <*> traverse (decodeRequest n) requests
  _ -> bad
parseInquiryInput :: SExpr -> Result InquiryInput
parseInquiryInput wire = case wire of
  SList (SAtom tag:SAtom version:_) | W.parseWord tag == Just InputTag && version /= "1" ->
    Left (Version ("inquiry-input supports version 1 only, found " ++ version))
  SList (SAtom tag:SAtom "1":_) | W.parseWord tag == Just InputTag ->
    either (const (Left (Malformed "malformed inquiry-input"))) Right (decodeInput wire)
  _ -> Left (Malformed "expected an inquiry-input document")
parseInquiryInputBS :: ByteString -> Result InquiryInput
parseInquiryInputBS bytes = case Raw.parseSExprBSWithCharRenderer (\c -> "'" ++ [c] ++ "'") bytes of
  Left (Raw.ParseError line column detail) -> Left (SyntaxError ("line " ++ show line ++ ", column " ++ show column ++ ": " ++ detail))
  Right wire -> parseInquiryInput wire
encodeOutcome :: W.Names -> String -> OutcomeAnswer -> SExpr
encodeOutcome n label (OutcomeAnswer verdict count holds fails) = W.form W.AnswerTag
  ([SAtom label,W.encodeWord verdict,W.form W.CompletionsTag [W.encodeNat count]] ++ optional W.HoldsTag holds ++ optional W.FailsTag fails)
  where optional tag = maybe [] (\events -> [W.form tag [W.form W.HistoryTag [W.encodeIdx (W.namesEvent n) index | EventId index <- events]]])
decodeOutcome :: W.Names -> SExpr -> Result OutcomeAnswer
decodeOutcome n wire = case wire of
  SList (SAtom ans:_:verdict:SList [SAtom comp,count]:rest)
    | W.parseWord ans == Just W.AnswerTag
    , W.parseWord comp == Just W.CompletionsTag -> do
        v <- liftCodec (W.decodeWord "verdict" verdict)
        c <- liftCodec (W.decodeNat count)
        (holds,rest1) <- optional W.HoldsTag rest
        (fails,rest2) <- optional W.FailsTag rest1
        unless (null rest2) bad
        pure (OutcomeAnswer v c holds fails)
  _ -> bad
  where optional tag (SList [SAtom actual,SList (SAtom h:events)]:rest)
          | W.parseWord actual == Just tag
          , W.parseWord h == Just W.HistoryTag = do
              identities <- liftCodec (traverse (fmap EventId . W.decodeIdx (W.namesEvent n) "event") events)
              pure (Just identities,rest)
        optional _ rest = Right (Nothing,rest)
encodeBody :: W.Names -> String -> ResultBody -> SExpr
encodeBody n label body = case body of
  HistoryVerdict count answer -> form HistoryVerdictTag [form HistoryCountTag [W.encodeNat count],encodeOutcome n label answer]
  StatusBody r -> form StatusBodyTag [R.encodeFamilyStatusResult n r]
  AuditBody r -> form AuditBodyTag [R.encodeFamilyAuditResult n r]
  StabilityBody r -> form StabilityBodyTag [A.encodeStabilityResult n r]
  SensitivityBody r -> form SensitivityBodyTag [A.encodeSensitivityResult n r]
  SlotsSensitiveBody r -> form SlotsBodyTag [A.encodeSensitivityResult n r]
  AssumptionsBody r -> form AssumptionsBodyTag [A.encodeAssumptionResult n r]
  ImpactBody r -> form ImpactBodyTag [R.encodeImpactResult r]
  VerificationBody r -> form VerificationBodyTag [R.encodeVerificationResult r]
decodeBody :: W.Names -> SExpr -> Result ResultBody
decodeBody n wire = case wire of
  SList [SAtom hv,SList [SAtom hc,count],answer]
    | W.parseWord hv == Just HistoryVerdictTag
    , W.parseWord hc == Just HistoryCountTag ->
        HistoryVerdict <$> liftCodec (W.decodeNat count) <*> decodeOutcome n answer
  SList [SAtom tag,r] -> case W.parseWord tag of
    Just StatusBodyTag -> StatusBody <$> liftCodec (R.decodeFamilyStatusResult n r)
    Just AuditBodyTag -> AuditBody <$> liftCodec (R.decodeFamilyAuditResult n r)
    Just StabilityBodyTag -> StabilityBody <$> liftCodec (A.decodeStabilityResult n r)
    Just SensitivityBodyTag -> SensitivityBody <$> liftCodec (A.decodeSensitivityResult n r)
    Just SlotsBodyTag -> SlotsSensitiveBody <$> liftCodec (A.decodeSensitivityResult n r)
    Just AssumptionsBodyTag -> AssumptionsBody <$> liftCodec (A.decodeAssumptionResult n r)
    Just ImpactBodyTag -> ImpactBody <$> liftCodec (R.decodeImpactResult r)
    Just VerificationBodyTag -> VerificationBody <$> liftCodec (R.decodeVerificationResult r)
    _ -> bad
  _ -> bad
encodeInquiryResult :: W.Names -> InquiryResult -> SExpr
encodeInquiryResult n (InquiryResult label body) = form ResultTag [SAtom "1",SAtom label,encodeBody n label body]
parseInquiryResult :: W.Names -> SExpr -> Result InquiryResult
parseInquiryResult n wire = case wire of
  SList (SAtom tag:SAtom version:_) | W.parseWord tag == Just ResultTag && version /= "1" ->
    Left (Version ("inquiry-result supports version 1 only, found " ++ version))
  SList (SAtom tag:SAtom "1":_) | W.parseWord tag == Just ResultTag ->
    either (const (Left (Malformed "malformed inquiry-result"))) Right $
      canonical (encodeInquiryResult n) decode wire
  _ -> Left (Malformed "expected an inquiry-result envelope")
  where
    decode (SList [SAtom tag,SAtom "1",SAtom label,body]) | W.parseWord tag == Just ResultTag =
      InquiryResult label <$> decodeBody n body
    decode _ = bad
encodeInquiryError :: InquiryError -> SExpr
encodeInquiryError (InquiryError label refusal) = form ErrorTag [SAtom "1",A.encodeOption SAtom label,encodeRefusal refusal]
parseInquiryError :: SExpr -> Result InquiryError
parseInquiryError wire = case wire of
  SList (SAtom tag:SAtom version:_) | W.parseWord tag == Just ErrorTag && version /= "1" ->
    Left (Version ("inquiry-error supports version 1 only, found " ++ version))
  SList (SAtom tag:SAtom "1":_) | W.parseWord tag == Just ErrorTag ->
    either (const (Left (Malformed "malformed inquiry-error"))) Right $
      canonical encodeInquiryError decode wire
  _ -> Left (Malformed "expected an inquiry-error envelope")
  where
    decode (SList [SAtom tag,SAtom "1",label,refusal]) | W.parseWord tag == Just ErrorTag =
      InquiryError <$> liftCodec (A.decodeOption W.decodeText label) <*> decodeRefusal refusal
    decode _ = bad
