-- | Frozen process-input 1 codecs, also reused by the embedded inquiry grammar.
-- S-expressions and authored name tables exist only at this boundary.
module Lara.Process.Wire where

import Data.List (find)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Void (Void, absurd)
import Numeric.Natural (Natural)
import Lara.Process.Types
import Lara.Strict (SExpr (..))
import Lara.Wire (parseSExpr)

data Tag
  = ProcessInputTag | NamesTag | EventTag | ActorTag | PlanTag | RunTag | ClaimTag | SourceTag | DataTag | FamilyTag | WitnessTag
  | RecordTag | CutoffTag | OrderTag | CoverageTag | SubmitTag | ReaderTag | UniverseTag | LimitsTag | EventsTag | CompletionsTag
  | QueriesTag | CommitPlanTag | AccessTag | ResultTag | AssertTag | RetractTag | UpdateDataTag | InputTag | InputsTag | AtTag
  | CompleteTag | CountBoundedTag | OpenWorldTag | DeclaredPolicyTag | ScopeTag | KindsTag | ActorsTag
  | VerdictTag | AuditTag | RunPrecommittedTag | PredictableTag | SplitSelectionTag | FamilyCountAtMostTag
  | NotTag | AndTag | OrTag | ProfileTag | AdmissibleTag | AcceptsTag | GuaranteeTag | ProbesTag | AcceptanceTag
  | ProcessResultTag | ProcessErrorTag | AssumptionsTag | AdmittedTag | UnadmittedTag | AnswersTag | AnswerTag | HoldsTag | FailsTag | HistoryTag
  deriving (Eq, Ord, Show, Enum, Bounded)

data ErrorTag = Syntax | Malformed | UnsupportedVersion | Unsupported | LimitExceeded | Usage | IOFailure deriving (Eq, Ord, Show, Enum, Bounded)
data Error = Error { errorTag :: ErrorTag, errorDetail :: String } deriving (Eq, Ord, Show)

class (Eq a, Enum a, Bounded a) => WireWord a where
  wordText :: a -> String

allWords :: (Enum a, Bounded a) => [a]
allWords = [minBound .. maxBound]

instance WireWord Tag where
  wordText tag = case tag of
    ProcessInputTag -> "process-input"; NamesTag -> "names"; EventTag -> "event"; ActorTag -> "actor"; PlanTag -> "plan"; RunTag -> "run"
    ClaimTag -> "claim"; SourceTag -> "source"; DataTag -> "data"; FamilyTag -> "family"; WitnessTag -> "witness"
    RecordTag -> "record"; CutoffTag -> "cutoff"; OrderTag -> "order"; CoverageTag -> "coverage"; SubmitTag -> "submit"
    ReaderTag -> "reader"; UniverseTag -> "universe"; LimitsTag -> "limits"; EventsTag -> "events"; CompletionsTag -> "completions"
    QueriesTag -> "queries"; CommitPlanTag -> "commit-plan"; AccessTag -> "access"; ResultTag -> "result"; AssertTag -> "assert"
    RetractTag -> "retract"; UpdateDataTag -> "update-data"; InputTag -> "input"; InputsTag -> "inputs"; AtTag -> "at"
    CompleteTag -> "complete"; CountBoundedTag -> "count-bounded"; OpenWorldTag -> "open-world"; DeclaredPolicyTag -> "declared-policy"
    ScopeTag -> "scope"; KindsTag -> "kinds"; ActorsTag -> "actors"; VerdictTag -> "verdict"; AuditTag -> "audit"
    RunPrecommittedTag -> "run-precommitted"; PredictableTag -> "predictable"; SplitSelectionTag -> "split-selection"; FamilyCountAtMostTag -> "family-count-at-most"
    NotTag -> "not"; AndTag -> "and"; OrTag -> "or"; ProfileTag -> "profile"; AdmissibleTag -> "admissible"; AcceptsTag -> "accepts"
    GuaranteeTag -> "guarantee"; ProbesTag -> "probes"; AcceptanceTag -> "acceptance"; ProcessResultTag -> "process-result"
    ProcessErrorTag -> "process-error"; AssumptionsTag -> "assumptions"; AdmittedTag -> "admitted"; UnadmittedTag -> "unadmitted"
    AnswersTag -> "answers"; AnswerTag -> "answer"; HoldsTag -> "holds"; FailsTag -> "fails"; HistoryTag -> "history"
instance WireWord AccessPurpose where
  wordText Selection = "selection"
  wordText Evaluation = "evaluation"
instance WireWord EventKind where
  wordText PlanCommit = "plan-commit"
  wordText DataAccess = "data-access"
  wordText AnalysisRun = "analysis-run"
  wordText ResultProduced = "result-produced"
  wordText ClaimAsserted = "claim-asserted"
  wordText SourceRetracted = "source-retracted"
  wordText DataUpdated = "data-updated"
instance WireWord AdmissionBasis where
  wordText InstrumentedLog = "instrumented-log"
  wordText SignedAttestation = "signed-attestation"
  wordText AuthorDeclaration = "author-declaration"
instance WireWord EvidenceKind where
  wordText = evidenceLabel
instance WireWord CoverageKind where
  wordText CompleteKind = "complete"
  wordText CountBoundedKind = "count-bounded"
  wordText OpenWorldKind = "open-world"
instance WireWord GuaranteeClass where
  wordText FWER = "fwer"
  wordText FDR = "fdr"
  wordText MFDR = "mfdr"
instance WireWord ErrorKind where
  wordText OptionalStopping = "optional-stopping"
  wordText kind = errorKindLabel kind
instance WireWord Acceptance where
  wordText GroundedJustified = "grounded-justified"
instance WireWord Verdict where
  wordText = verdictLabel
instance WireWord ErrorTag where
  wordText Syntax = "syntax"
  wordText Malformed = "malformed"
  wordText UnsupportedVersion = "unsupported-version"
  wordText Unsupported = "unsupported"
  wordText LimitExceeded = "limit-exceeded"
  wordText Usage = "usage"
  wordText IOFailure = "io"

parseWord :: WireWord a => String -> Maybe a
parseWord text = find ((== text) . wordText) allWords

bad :: String -> Either Error a
bad = Left . Error Malformed

errorExitCode :: Error -> Int
errorExitCode err = if errorTag err `elem` [Unsupported, LimitExceeded] then 1 else 2

tagged :: String -> [SExpr] -> SExpr
tagged text args = SList (SAtom text : args)

form :: Tag -> [SExpr] -> SExpr
form = tagged . wordText

headTag :: SExpr -> Maybe (Tag, [SExpr])
headTag (SList (SAtom text : args)) = (, args) <$> parseWord text
headTag _ = Nothing

decodeText :: SExpr -> Either Error String
decodeText (SAtom text) = Right text
decodeText _ = bad "expected an atom"

-- Natural is unbounded. Never pass authored counters through machine Int.
decodeNat :: SExpr -> Either Error Natural
decodeNat (SAtom "0") = Right 0
decodeNat (SAtom text@(firstChar : _))
  | firstChar /= '0' && all (\c -> c >= '0' && c <= '9') text = Right (read text)
  | otherwise = bad ("non-canonical number " ++ text)
decodeNat (SAtom "") = bad "non-canonical number "
decodeNat _ = bad "expected a number"

encodeNat :: Natural -> SExpr
encodeNat = SAtom . show

decodeWord :: WireWord a => String -> SExpr -> Either Error a
decodeWord what (SAtom text) = maybe (bad ("unknown " ++ what ++ " " ++ text)) Right (parseWord text)
decodeWord what _ = bad ("expected a " ++ what)

encodeWord :: WireWord a => a -> SExpr
encodeWord = SAtom . wordText

decodeList :: (SExpr -> Either Error a) -> [SExpr] -> Either Error [a]
decodeList = traverse

data Names = Names
  { namesEvent :: [String], namesActor :: [String], namesPlan :: [String], namesRun :: [String]
  , namesClaim :: [String], namesSource :: [String], namesData :: [String], namesFamily :: [String], namesWitness :: [String]
  } deriving (Eq, Ord, Show)

decodeIdx :: [String] -> String -> SExpr -> Either Error Natural
decodeIdx table what value = do
  text <- decodeText value
  let go _ [] = bad ("undeclared " ++ what ++ " name " ++ text)
      go index (name : rest) | name == text = Right index
                             | otherwise = go (index + 1) rest
  go 0 table

-- Frozen P0 encoder behavior for an out-of-range index is the empty atom.
encodeIdx :: [String] -> Natural -> SExpr
encodeIdx table index = SAtom (go table index)
  where go [] _ = ""
        go (x : _) 0 = x
        go (_ : xs) n = go xs (n - 1)

unique :: Ord a => [a] -> Bool
unique = go Set.empty
  where go _ [] = True
        go seen (x : xs) = not (Set.member x seen) && go (Set.insert x seen) xs

decodeTable :: Tag -> SExpr -> Either Error [String]
decodeTable tag value = case headTag value of
  Just (actual, args) | actual == tag -> do
    table <- traverse decodeText args
    if unique table then Right table else bad ("duplicate " ++ wordText tag ++ " name")
  _ -> bad ("expected the " ++ wordText tag ++ " names")

encodeTable :: Tag -> [String] -> SExpr
encodeTable tag = form tag . map SAtom

decodeNames :: SExpr -> Either Error Names
decodeNames value = case headTag value of
  Just (NamesTag, [ev, ac, pl, ru, cl, so, da, fa, wi]) -> Names
    <$> decodeTable EventTag ev <*> decodeTable ActorTag ac <*> decodeTable PlanTag pl <*> decodeTable RunTag ru
    <*> decodeTable ClaimTag cl <*> decodeTable SourceTag so <*> decodeTable DataTag da <*> decodeTable FamilyTag fa <*> decodeTable WitnessTag wi
  _ -> bad "expected the names block"

encodeNames :: Names -> SExpr
encodeNames n = form NamesTag [encodeTable EventTag (namesEvent n), encodeTable ActorTag (namesActor n), encodeTable PlanTag (namesPlan n), encodeTable RunTag (namesRun n), encodeTable ClaimTag (namesClaim n), encodeTable SourceTag (namesSource n), encodeTable DataTag (namesData n), encodeTable FamilyTag (namesFamily n), encodeTable WitnessTag (namesWitness n)]

decodeRef :: SExpr -> Either Error SourceRef
decodeRef value = case headTag value of
  Just (AtTag, [file, entry]) -> SourceRef <$> decodeText file <*> decodeText entry <*> pure Nothing
  Just (AtTag, [file, entry, start, end]) -> SourceRef <$> decodeText file <*> decodeText entry <*> (Just <$> ((,) <$> decodeNat start <*> decodeNat end))
  _ -> bad "expected a source reference"

encodeRef :: SourceRef -> SExpr
encodeRef ref = form AtTag ([SAtom (refFile ref), SAtom (refEntry ref)] ++ maybe [] (\(a, b) -> [encodeNat a, encodeNat b]) (refSpan ref))

decodeInput :: Names -> SExpr -> Either Error (DataId, VersionId)
decodeInput n value = case headTag value of
  Just (InputTag, [dataset, version]) -> (,) <$> (DataId <$> decodeIdx (namesData n) "data" dataset) <*> (VersionId <$> decodeNat version)
  _ -> bad "expected a run input"

encodeInput :: Names -> (DataId, VersionId) -> SExpr
encodeInput n (dataset, version) = form InputTag [encodeIdx (namesData n) (dataIndex dataset), encodeNat (versionIndex version)]

decodeInputs :: Names -> SExpr -> Either Error [(DataId, VersionId)]
decodeInputs n value = case headTag value of
  Just (InputsTag, args) -> traverse (decodeInput n) args
  _ -> bad "expected the run inputs"

encodeInputs :: Names -> [(DataId, VersionId)] -> SExpr
encodeInputs n = form InputsTag . map (encodeInput n)

decodeBody :: Names -> SExpr -> Either Error Event
decodeBody n value = case headTag value of
  Just (CommitPlanTag, [actor, plan, version]) -> CommitPlan <$> actorId actor <*> planId plan <*> versionId version
  Just (AccessTag, [actor, dataset, purpose]) -> Access <$> actorId actor <*> dataId dataset <*> decodeWord "access purpose" purpose
  Just (RunTag, [run, plan, version, inputs, family]) -> Run <$> runId run <*> planId plan <*> versionId version <*> decodeInputs n inputs <*> (FamilyId <$> decodeIdx (namesFamily n) "family" family)
  Just (ResultTag, [run, outcome]) -> Result <$> runId run <*> decodeNat outcome
  Just (AssertTag, [claim, witness]) -> Assert <$> (ClaimId <$> decodeIdx (namesClaim n) "claim" claim) <*> (WitnessId <$> decodeIdx (namesWitness n) "witness" witness)
  Just (RetractTag, [source]) -> Retract <$> (SourceId <$> decodeIdx (namesSource n) "source" source)
  Just (UpdateDataTag, [dataset, version]) -> UpdateData <$> dataId dataset <*> versionId version
  _ -> bad "expected an event"
  where actorId = fmap ActorId . decodeIdx (namesActor n) "actor"
        planId = fmap PlanId . decodeIdx (namesPlan n) "plan"
        dataId = fmap DataId . decodeIdx (namesData n) "data"
        runId = fmap RunId . decodeIdx (namesRun n) "run"
        versionId = fmap VersionId . decodeNat

encodeBody :: Names -> Event -> SExpr
encodeBody n event = case event of
  CommitPlan a p v -> form CommitPlanTag [actor a, plan p, version v]
  Access a d purpose -> form AccessTag [actor a, dataset d, encodeWord purpose]
  Run r p v inputs f -> form RunTag [run r, plan p, version v, encodeInputs n inputs, encodeIdx (namesFamily n) (familyIndex f)]
  Result r outcome -> form ResultTag [run r, encodeNat outcome]
  Assert c w -> form AssertTag [encodeIdx (namesClaim n) (claimIndex c), encodeIdx (namesWitness n) (witnessIndex w)]
  Retract s -> form RetractTag [encodeIdx (namesSource n) (sourceIndex s)]
  UpdateData d v -> form UpdateDataTag [dataset d, version v]
  where actor = encodeIdx (namesActor n) . actorIndex
        plan = encodeIdx (namesPlan n) . planIndex
        dataset = encodeIdx (namesData n) . dataIndex
        run = encodeIdx (namesRun n) . runIndex
        version = encodeNat . versionIndex

decodeStamped :: Names -> SExpr -> Either Error Stamped
decodeStamped n value = case headTag value of
  Just (EventTag, [identifier, body]) -> Stamped <$> (EventId <$> decodeIdx (namesEvent n) "event" identifier) <*> decodeBody n body
  _ -> bad "expected a universe event"

encodeStamped :: Names -> Stamped -> SExpr
encodeStamped n stamped = form EventTag [encodeIdx (namesEvent n) (eventIndex (stampedId stamped)), encodeBody n (stampedEvent stamped)]

decodeOpt :: Tag -> ([SExpr] -> Either Error a) -> [SExpr] -> Either Error (Maybe a, [SExpr])
decodeOpt tag decode values = case values of
  value : rest | Just (actual, args) <- headTag value, actual == tag -> (, rest) . Just <$> decode args
  _ -> Right (Nothing, values)

encodeOpt :: Tag -> (a -> [SExpr]) -> Maybe a -> [SExpr]
encodeOpt tag encode = maybe [] (\value -> [form tag (encode value)])

decodeField :: Tag -> SExpr -> Either Error Natural
decodeField tag value = case headTag value of
  Just (actual, [number]) | actual == tag -> decodeNat number
  _ -> bad ("expected the " ++ wordText tag ++ " field")

encodeField :: Tag -> Natural -> SExpr
encodeField tag number = form tag [encodeNat number]

decodeWords :: WireWord a => Tag -> String -> SExpr -> Either Error [a]
decodeWords tag what value = case headTag value of
  Just (actual, args) | actual == tag -> traverse (decodeWord what) args
  _ -> bad ("expected the " ++ wordText tag ++ " list")

encodeWords :: WireWord a => Tag -> [a] -> SExpr
encodeWords tag = form tag . map encodeWord

decodeOneIdx :: [String] -> String -> [SExpr] -> Either Error Natural
decodeOneIdx table what [value] = decodeIdx table what value
decodeOneIdx _ what _ = bad ("expected one " ++ what ++ " name")

decodeScope :: Names -> SExpr -> Either Error CoverageScope
decodeScope n value = case headTag value of
  Just (ScopeTag, kinds : cutoff : clauses) -> do
    ks <- decodeWords KindsTag "event kind" kinds
    cut <- decodeField CutoffTag cutoff
    (family, afterFamily) <- decodeOpt FamilyTag (fmap FamilyId . decodeOneIdx (namesFamily n) "family") clauses
    (actors, afterActors) <- decodeOpt ActorsTag (traverse (fmap ActorId . decodeIdx (namesActor n) "actor")) afterFamily
    (datasets, rest) <- decodeOpt DataTag (traverse (fmap DataId . decodeIdx (namesData n) "data")) afterActors
    if null rest then Right (CoverageScope ks family actors datasets cut) else bad "unexpected scope clause"
  _ -> bad "expected a coverage scope"

encodeScope :: Names -> CoverageScope -> SExpr
encodeScope n scope = form ScopeTag
  ([encodeWords KindsTag (scopeKinds scope), encodeField CutoffTag (scopeCutoff scope)]
  ++ encodeOpt FamilyTag (\f -> [encodeIdx (namesFamily n) (familyIndex f)]) (scopeFamily scope)
  ++ encodeOpt ActorsTag (map (encodeIdx (namesActor n) . actorIndex)) (scopeActors scope)
  ++ encodeOpt DataTag (map (encodeIdx (namesData n) . dataIndex)) (scopeData scope))

decodeCoverage :: Names -> SExpr -> Either Error (RecordCoverage Void)
decodeCoverage n value = case headTag value of
  Just (CompleteTag, [scope]) -> Complete <$> decodeScope n scope
  Just (CountBoundedTag, [scope, bound]) -> CountBounded <$> decodeScope n scope <*> decodeNat bound
  Just (OpenWorldTag, [scope]) -> OpenWorld <$> decodeScope n scope
  Just (DeclaredPolicyTag, _) -> Left (Error Unsupported "process-input 1 interprets no declared reporting policy")
  _ -> bad "expected a coverage assertion"

encodeCoverage :: Names -> RecordCoverage Void -> SExpr
encodeCoverage n coverage = case coverage of
  Complete scope -> form CompleteTag [encodeScope n scope]
  CountBounded scope bound -> form CountBoundedTag [encodeScope n scope, encodeNat bound]
  OpenWorld scope -> form OpenWorldTag [encodeScope n scope]
  DeclaredPolicy _ policy -> absurd policy

decodeEntry :: Names -> SExpr -> Either Error (AraEntry Void)
decodeEntry n value = case headTag value of
  Just (EventTag, [identifier, body, ref]) -> EventEntry <$> (Stamped <$> eventId identifier <*> decodeBody n body) <*> decodeRef ref
  Just (OrderTag, [a, b, ref]) -> OrderingEntry <$> eventId a <*> eventId b <*> decodeRef ref
  Just (CoverageTag, [coverage, ref, basis]) -> CoverageEntry <$> (CoverageAssertion <$> decodeCoverage n coverage <*> decodeRef ref <*> decodeWord "admission basis" basis)
  Just (SubmitTag, [claim, witness]) -> SubmissionEntry <$> (ClaimId <$> decodeIdx (namesClaim n) "claim" claim) <*> (WitnessId <$> decodeIdx (namesWitness n) "witness" witness)
  _ -> bad "expected a record entry"
  where eventId = fmap EventId . decodeIdx (namesEvent n) "event"

encodeEntry :: Names -> AraEntry Void -> SExpr
encodeEntry n entry = case entry of
  EventEntry event ref -> form EventTag [identifier (stampedId event), encodeBody n (stampedEvent event), encodeRef ref]
  OrderingEntry a b ref -> form OrderTag [identifier a, identifier b, encodeRef ref]
  CoverageEntry assertion -> form CoverageTag [encodeCoverage n (assertionCoverage assertion), encodeRef (assertionEvidence assertion), encodeWord (assertionBasis assertion)]
  SubmissionEntry claim witness -> form SubmitTag [encodeIdx (namesClaim n) (claimIndex claim), encodeIdx (namesWitness n) (witnessIndex witness)]
  where identifier = encodeIdx (namesEvent n) . eventIndex

decodeRecord :: Names -> SExpr -> Either Error (AraSource Void)
decodeRecord n value = case headTag value of
  Just (RecordTag, cutoff : entries) -> do
    cut <- decodeField CutoffTag cutoff
    decoded <- traverse (decodeEntry n) entries
    Right (AraSource decoded cut)
  _ -> bad "expected the record"

encodeRecord :: Names -> AraSource Void -> SExpr
encodeRecord n source = form RecordTag (encodeField CutoffTag (sourceCutoff source) : map (encodeEntry n) (sourceEntries source))

decodeUniverse :: Names -> SExpr -> Either Error [Stamped]
decodeUniverse n value = case headTag value of
  Just (UniverseTag, args) -> traverse (decodeStamped n) args
  _ -> bad "expected the universe"

encodeUniverse :: Names -> [Stamped] -> SExpr
encodeUniverse n = form UniverseTag . map (encodeStamped n)

decodeQuery :: Names -> SExpr -> Either Error Query
decodeQuery n value = case headTag value of
  Just (PredictableTag, []) -> Right (QueryAtom Predictable)
  Just (RunPrecommittedTag, [run]) -> QueryAtom . RunPrecommitted . RunId <$> decodeIdx (namesRun n) "run" run
  Just (FamilyCountAtMostTag, [family, bound]) -> QueryAtom <$> (FamilyCountAtMost <$> (FamilyId <$> decodeIdx (namesFamily n) "family" family) <*> decodeNat bound)
  Just (SplitSelectionTag, [SList selection, SList test]) -> QueryAtom <$> (SplitSelection <$> datasets selection <*> datasets test)
  Just (NotTag, [query]) -> QueryNot <$> decodeQuery n query
  Just (AndTag, [a, b]) -> QueryAnd <$> decodeQuery n a <*> decodeQuery n b
  Just (OrTag, [a, b]) -> QueryOr <$> decodeQuery n a <*> decodeQuery n b
  _ -> bad "expected a query formula"
  where datasets = traverse (fmap DataId . decodeIdx (namesData n) "data")

encodeQuery :: Names -> Query -> SExpr
encodeQuery n query = case query of
  QueryAtom Predictable -> form PredictableTag []
  QueryAtom (RunPrecommitted run) -> form RunPrecommittedTag [encodeIdx (namesRun n) (runIndex run)]
  QueryAtom (FamilyCountAtMost family bound) -> form FamilyCountAtMostTag [encodeIdx (namesFamily n) (familyIndex family), encodeNat bound]
  QueryAtom (SplitSelection selection test) -> form SplitSelectionTag [datasets selection, datasets test]
  QueryNot q -> form NotTag [encodeQuery n q]
  QueryAnd a b -> form AndTag [encodeQuery n a, encodeQuery n b]
  QueryOr a b -> form OrTag [encodeQuery n a, encodeQuery n b]
  where datasets = SList . map (encodeIdx (namesData n) . dataIndex)

decodeGuarantee :: SExpr -> Either Error (GuaranteeClass, Natural, Natural)
decodeGuarantee value = case headTag value of
  Just (GuaranteeTag, [cls, numerator, denominator]) -> do
    c <- decodeWord "guarantee class" cls
    num <- decodeNat numerator
    den <- decodeNat denominator
    if den > 0 then Right (c, num, den) else bad "guarantee level needs a positive denominator"
  _ -> bad "expected the guarantee"

encodeGuarantee :: (GuaranteeClass, Natural, Natural) -> SExpr
encodeGuarantee (cls, num, den) = form GuaranteeTag [encodeWord cls, encodeNat num, encodeNat den]

decodeAcceptance :: SExpr -> Either Error Acceptance
decodeAcceptance value = case headTag value of
  Just (AcceptanceTag, [word]) -> decodeWord "acceptance" word
  _ -> bad "expected the acceptance"

encodeAcceptance :: Acceptance -> SExpr
encodeAcceptance a = form AcceptanceTag [encodeWord a]

decodeProfile :: SExpr -> Either Error ProfileSpec
decodeProfile value = case headTag value of
  Just (ProfileTag, [admissible, accepts, guarantee, probes, acceptance]) -> do
    adm <- decodeWords AdmissibleTag "evidence kind" admissible
    acc <- decodeWords AcceptsTag "coverage kind" accepts
    (cls, num, den) <- decodeGuarantee guarantee
    pr <- decodeWords ProbesTag "error kind" probes
    ac <- decodeAcceptance acceptance
    Right (ProfileSpec adm acc cls num den pr ac)
  _ -> bad "expected a profile"

encodeProfile :: ProfileSpec -> SExpr
encodeProfile profile = form ProfileTag
  [encodeWords AdmissibleTag (profileAdmissible profile), encodeWords AcceptsTag (profileAccepts profile)
  , encodeGuarantee (profileGuarantee profile, profileNum profile, profileDen profile)
  , encodeWords ProbesTag (profileProbes profile), encodeAcceptance (profileAcceptance profile)]

decodeQuerySpec :: Names -> SExpr -> Either Error QuerySpec
decodeQuerySpec n value = case headTag value of
  Just (VerdictTag, [name, query]) -> VerdictQuery <$> decodeText name <*> decodeQuery n query
  Just (AuditTag, [name, claim, witness, profile]) -> AuditQuery <$> decodeText name <*> (ClaimId <$> decodeIdx (namesClaim n) "claim" claim) <*> (WitnessId <$> decodeIdx (namesWitness n) "witness" witness) <*> decodeProfile profile
  _ -> bad "expected a query"

encodeQuerySpec :: Names -> QuerySpec -> SExpr
encodeQuerySpec n query = case query of
  VerdictQuery name q -> form VerdictTag [SAtom name, encodeQuery n q]
  AuditQuery name claim witness profile -> form AuditTag [SAtom name, encodeIdx (namesClaim n) (claimIndex claim), encodeIdx (namesWitness n) (witnessIndex witness), encodeProfile profile]

data Limits = Limits { limitEvents :: Natural, limitCompletions :: Natural } deriving (Eq, Ord, Show)

decodeLimits :: SExpr -> Either Error Limits
decodeLimits value = case headTag value of
  Just (LimitsTag, [events, completions]) -> Limits <$> decodeField EventsTag events <*> decodeField CompletionsTag completions
  _ -> bad "expected the limits"

encodeLimits :: Limits -> SExpr
encodeLimits limits = form LimitsTag [encodeField EventsTag (limitEvents limits), encodeField CompletionsTag (limitCompletions limits)]

decodeQueries :: Names -> SExpr -> Either Error [QuerySpec]
decodeQueries n value = case headTag value of
  Just (QueriesTag, args) -> traverse (decodeQuerySpec n) args
  _ -> bad "expected the queries"

encodeQueries :: Names -> [QuerySpec] -> SExpr
encodeQueries n = form QueriesTag . map (encodeQuerySpec n)

data Document = Document
  { documentNames :: Names, documentSource :: AraSource Void, documentAdmits :: [AdmissionBasis]
  , documentUnrecorded :: [Stamped], documentLimits :: Limits, documentQueries :: [QuerySpec]
  } deriving (Eq, Ord, Show)

processVersion :: String
processVersion = "1"

decodeDocument :: SExpr -> Either Error Document
decodeDocument value = case headTag value of
  Just (ProcessInputTag, SAtom v : rest)
    | v /= processVersion -> unsupportedVersion
    | otherwise -> case rest of
        [names, record, reader, universe, limits, queries] -> do
          n <- decodeNames names
          Document n <$> decodeRecord n record <*> decodeWords ReaderTag "admission basis" reader
            <*> decodeUniverse n universe <*> decodeLimits limits <*> decodeQueries n queries
        _ -> bad "expected names, record, reader, universe, limits and queries"
  Just (ProcessInputTag, _) -> unsupportedVersion
  _ -> bad "expected a process-input document"
  where unsupportedVersion = Left (Error UnsupportedVersion "process-input supports version 1 only")

encodeDocument :: Document -> SExpr
encodeDocument doc = form ProcessInputTag
  [SAtom processVersion, encodeNames n, encodeRecord n (documentSource doc), encodeWords ReaderTag (documentAdmits doc)
  , encodeUniverse n (documentUnrecorded doc), encodeLimits (documentLimits doc), encodeQueries n (documentQueries doc)]
  where n = documentNames doc

decodeDocumentFile :: String -> Either Error Document
decodeDocumentFile text = either (Left . Error Syntax . show) decodeDocument (parseSExpr text)

-- Structural index bounds, independent of the decoder. These are useful to
-- validate constructed values before relying on names-context roundtrips.
uniqueNames :: Names -> Bool
uniqueNames n = all unique [namesEvent n, namesActor n, namesPlan n, namesRun n, namesClaim n, namesSource n, namesData n, namesFamily n, namesWitness n]

indexIn :: [a] -> Natural -> Bool
indexIn table index = fromMaybe False (go table index)
  where go [] _ = Nothing
        go (_ : _) 0 = Just True
        go (_ : rest) i = go rest (i - 1)

inputWellNamed :: Names -> (DataId, VersionId) -> Bool
inputWellNamed n = indexIn (namesData n) . dataIndex . fst

eventWellNamed :: Names -> Event -> Bool
eventWellNamed n event = case event of
  CommitPlan actor plan _ -> actorOk actor && planOk plan
  Access actor dataset _ -> actorOk actor && dataOk dataset
  Run run plan _ inputs family -> runOk run && planOk plan && all (inputWellNamed n) inputs && indexIn (namesFamily n) (familyIndex family)
  Result run _ -> runOk run
  Assert claim witness -> indexIn (namesClaim n) (claimIndex claim) && indexIn (namesWitness n) (witnessIndex witness)
  Retract source -> indexIn (namesSource n) (sourceIndex source)
  UpdateData dataset _ -> dataOk dataset
  where actorOk = indexIn (namesActor n) . actorIndex
        planOk = indexIn (namesPlan n) . planIndex
        dataOk = indexIn (namesData n) . dataIndex
        runOk = indexIn (namesRun n) . runIndex

stampedWellNamed :: Names -> Stamped -> Bool
stampedWellNamed n event = indexIn (namesEvent n) (eventIndex (stampedId event)) && eventWellNamed n (stampedEvent event)

atomWellNamed :: Names -> Atom -> Bool
atomWellNamed n atom = case atom of
  Predictable -> True
  RunPrecommitted run -> indexIn (namesRun n) (runIndex run)
  FamilyCountAtMost family _ -> indexIn (namesFamily n) (familyIndex family)
  SplitSelection selection test -> all (indexIn (namesData n) . dataIndex) selection && all (indexIn (namesData n) . dataIndex) test

queryWellNamed :: Names -> Query -> Bool
queryWellNamed n query = case query of
  QueryAtom atom -> atomWellNamed n atom
  QueryNot q -> queryWellNamed n q
  QueryAnd a b -> queryWellNamed n a && queryWellNamed n b
  QueryOr a b -> queryWellNamed n a && queryWellNamed n b
