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
block tag decode (SList (SAtom actual:values)) | W.wordText tag == actual = liftCodec (traverse decode values)
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
  SList (SAtom "inquiry-limits":values) -> do
    counts <- traverse field (zip [minBound..maxBound] values)
    case counts of [h,s,b,d,t,p,u] | length values == 7 -> Right (InquiryLimits h s b d t p u); _ -> bad
  _ -> bad
  where field (counter,SList [SAtom tag,value]) | tag == counterText counter = liftCodec (W.decodeNat value)
        field _ = bad
encodeRefusal :: RunRefusal -> SExpr
encodeRefusal refusal = case refusal of
  Malformed d -> form MalformedTag [SAtom d]; SyntaxError d -> form SyntaxTag [SAtom d]
  Unsupported d -> form UnsupportedTag [SAtom d]; Version d -> form VersionTag [SAtom d]
  Usage d -> form UsageTag [SAtom d]; IOFailure d -> form IOTag [SAtom d]
  Limit c actual cap -> form LimitTag [form CounterTag [SAtom (counterText c)],form ActualTag [W.encodeNat actual],form CapTag [W.encodeNat cap]]
decodeRefusal :: SExpr -> Result RunRefusal
decodeRefusal = canonical encodeRefusal $ \wire -> case wire of
  SList [SAtom tag,SAtom detail] -> maybe bad (Right . ($ detail)) (lookup tag
    [("malformed",Malformed),("syntax",SyntaxError),("unsupported",Unsupported),("version",Version),("usage",Usage),("io",IOFailure)])
  SList [SAtom "limit",SList [SAtom "counter",SAtom tag],SList [SAtom "actual",actual],SList [SAtom "cap",cap]] -> do
    counter <- maybe bad Right (lookup tag [(counterText c,c) | c <- [minBound..maxBound]])
    Limit counter <$> liftCodec (W.decodeNat actual) <*> liftCodec (W.decodeNat cap)
  _ -> bad
encodeReference :: W.Names -> ReferenceSpec -> SExpr
encodeReference names (ReferenceSpec history assignment) = form ReferenceTag
  [form RefHistoryTag [A.encodeList (W.encodeStamped names) history],form RefChoicesTag [C.encodeAssignment assignment]]
decodeReference :: W.Names -> SExpr -> Result ReferenceSpec
decodeReference names = canonical (encodeReference names) $ \wire -> case wire of
  SList [SAtom "reference",SList [SAtom "ref-history",history],SList [SAtom "ref-choices",assignment]] ->
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
  SList [SAtom "status",SAtom l,c] -> StatusRequest l <$> liftCodec (A.decodeClaim n c)
  SList [SAtom "audit",SAtom l,c,w,p] -> AuditRequest l <$> liftCodec (A.decodeClaim n c) <*> liftCodec (A.decodeWitness n w) <*> liftCodec (A.decodeProfile p)
  SList [SAtom "stable",SAtom l,o] -> StableRequest l <$> liftCodec (A.decodeObservable n o)
  SList [SAtom "sensitivity",SAtom l,r,o] -> SensitivityRequest l <$> decodeReference n r <*> liftCodec (A.decodeObservable n o)
  SList [SAtom "slots-sensitive",SAtom l,r,o] -> SlotsSensitiveRequest l <$> decodeReference n r <*> liftCodec (A.decodeObservable n o)
  SList [SAtom "minimal-assumptions",SAtom l,t] -> MinimalAssumptionsRequest l <$> liftCodec (A.decodeTarget n t)
  SList [SAtom "impact",SAtom l,b,a,qs] -> ImpactRequest l <$> liftCodec (S.decodeSource b) <*> liftCodec (S.decodeSource a) <*> block QueriesTag (A.decodeClaim n) qs
  SList [SAtom "verify-impact",SAtom l,b,a,c] -> VerifyImpactRequest l <$> liftCodec (S.decodeSource b) <*> liftCodec (S.decodeSource a) <*> liftCodec (R.decodeImpactCertificate c)
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
  SList [SAtom "inquiry-input",SAtom "1",proc,base,slots,SList [SAtom "bindings",claims,witnesses],kinds,assumptions,catalog,limits,SList (SAtom "requests":requests)] -> do
    document <- liftCodec (W.decodeDocument proc)
    let n = W.documentNames document
    InquiryInput document <$> liftCodec (S.decodeSource base) <*> block SlotsTag (C.decodeSlot n) slots
      <*> liftCodec (A.decodeList (C.decodeClaimBinding n) claims) <*> liftCodec (A.decodeList (C.decodeWitnessSpec n) witnesses)
      <*> block KindsTag C.decodeKindSpec kinds <*> block AdmittedTag (C.decodeCaptureAssumption n) assumptions
      <*> block CatalogTag (A.decodeLiteral n) catalog <*> decodeLimits limits <*> traverse (decodeRequest n) requests
  _ -> bad
parseInquiryInput :: SExpr -> Result InquiryInput
parseInquiryInput wire = case wire of
  SList (SAtom "inquiry-input":SAtom version:_) | version /= "1" -> Left (Version ("inquiry-input supports version 1 only, found " ++ version))
  SList (SAtom "inquiry-input":SAtom "1":_) -> either (const (Left (Malformed "malformed inquiry-input"))) Right (decodeInput wire)
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
  SList (SAtom "answer":_:verdict:SList [SAtom "completions",count]:rest) -> do
    v <- liftCodec (W.decodeWord "verdict" verdict)
    c <- liftCodec (W.decodeNat count)
    (holds,rest1) <- optional "holds" rest
    (fails,rest2) <- optional "fails" rest1
    unless (null rest2) bad
    pure (OutcomeAnswer v c holds fails)
  _ -> bad
  where optional tag (SList [SAtom actual,SList (SAtom "history":events)]:rest) | actual == tag = do
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
  SList [SAtom "history-verdict",SList [SAtom "history-count",count],answer] -> HistoryVerdict <$> liftCodec (W.decodeNat count) <*> decodeOutcome n answer
  SList [SAtom "status-body",r] -> StatusBody <$> liftCodec (R.decodeFamilyStatusResult n r)
  SList [SAtom "audit-body",r] -> AuditBody <$> liftCodec (R.decodeFamilyAuditResult n r)
  SList [SAtom "stability-body",r] -> StabilityBody <$> liftCodec (A.decodeStabilityResult n r)
  SList [SAtom "sensitivity-body",r] -> SensitivityBody <$> liftCodec (A.decodeSensitivityResult n r)
  SList [SAtom "slots-sensitive-body",r] -> SlotsSensitiveBody <$> liftCodec (A.decodeSensitivityResult n r)
  SList [SAtom "assumptions-body",r] -> AssumptionsBody <$> liftCodec (A.decodeAssumptionResult n r)
  SList [SAtom "impact-body",r] -> ImpactBody <$> liftCodec (R.decodeImpactResult r)
  SList [SAtom "verification-body",r] -> VerificationBody <$> liftCodec (R.decodeVerificationResult r)
  _ -> bad
encodeInquiryResult :: W.Names -> InquiryResult -> SExpr
encodeInquiryResult n (InquiryResult label body) = form ResultTag [SAtom "1",SAtom label,encodeBody n label body]
parseInquiryResult :: W.Names -> SExpr -> Result InquiryResult
parseInquiryResult n wire = case wire of
  SList (SAtom "inquiry-result":SAtom version:_) | version /= "1" ->
    Left (Version ("inquiry-result supports version 1 only, found " ++ version))
  SList (SAtom "inquiry-result":SAtom "1":_) ->
    either (const (Left (Malformed "malformed inquiry-result"))) Right $
      canonical (encodeInquiryResult n) decode wire
  _ -> Left (Malformed "expected an inquiry-result envelope")
  where
    decode (SList [SAtom "inquiry-result",SAtom "1",SAtom label,body]) =
      InquiryResult label <$> decodeBody n body
    decode _ = bad
encodeInquiryError :: InquiryError -> SExpr
encodeInquiryError (InquiryError label refusal) = form ErrorTag [SAtom "1",A.encodeOption SAtom label,encodeRefusal refusal]
parseInquiryError :: SExpr -> Result InquiryError
parseInquiryError wire = case wire of
  SList (SAtom "inquiry-error":SAtom version:_) | version /= "1" ->
    Left (Version ("inquiry-error supports version 1 only, found " ++ version))
  SList (SAtom "inquiry-error":SAtom "1":_) ->
    either (const (Left (Malformed "malformed inquiry-error"))) Right $
      canonical encodeInquiryError decode wire
  _ -> Left (Malformed "expected an inquiry-error envelope")
  where
    decode (SList [SAtom "inquiry-error",SAtom "1",label,refusal]) =
      InquiryError <$> liftCodec (A.decodeOption W.decodeText label) <*> decodeRefusal refusal
    decode _ = bad
