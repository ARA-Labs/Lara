module ProcessSpec (processSpecProps, familyEnumerationProps) where

import Data.Either (isLeft)
import Data.List (find)
import Data.Void (Void)
import Numeric.Natural (Natural)
import Test.QuickCheck

import Lara.Process.Types
import Lara.Process.History
import Lara.Process.Wire
import qualified Lara.AST as A
import Lara.Evidence.Types (ObjectId (..))
import Lara.Prop (Prop (..), Pred (..), Term (..))
import Lara.Sigma (emptySigma)
import qualified Lara.Process.Audit.Types as Audit
import qualified Lara.Process.Family as Family
import qualified Lara.Process.Enumerate as Enumerate
import qualified Lara.Process.Source.Types as Source
import Lara.Strict (SExpr (..))
import Lara.Wire (parseSExpr)
import qualified Data.ByteString as BS
import qualified Lara.Process.Inquiry.Wire as InquiryWire
import qualified Lara.Process.Inquiry.Run as InquiryRun
import qualified Lara.Process.Inquiry.Types as Inquiry
import qualified Lara.Wire as RawWire
import qualified Lara.Process.Analysis as InquiryLiteral

fixture :: String -> (Document -> Property) -> Property
fixture name check = once $ ioProperty $ do
  text <- readFile ("fixtures/process/run/" ++ name ++ ".sexp")
  pure $ case decodeDocumentFile text of
    Left err -> counterexample (show err) False
    Right doc -> check doc

problem :: Document -> Problem
problem doc = Problem (extract (`elem` documentAdmits doc) (documentSource doc)) (documentUnrecorded doc)

firstQuery :: Document -> Query
firstQuery doc = case documentQueries doc of
  VerdictQuery _ q : _ -> q
  _ -> QueryAtom Predictable

fixtureVerdict :: String -> Verdict -> Natural -> Property
fixtureVerdict name expected count = fixture name $ \doc ->
  let result = answer (problem doc) (firstQuery doc)
   in conjoin [answerVerdict result === expected, answerCount result === count]

prop_omittedRead :: Property
prop_omittedRead = fixture "omitted-read" $ \doc ->
  let p = problem doc
      q = firstQuery doc
      result = answer p q
      cs = completions p
   in conjoin
      [ answerVerdict result === Unknown
      , answerCount result === 10
      , answerHolds result === find (queryHolds q) cs
      , answerFails result === find (not . queryHolds q) cs
      , fmap (map stampedId) (answerHolds result) === Just [EventId 0, EventId 1, EventId 2]
      , fmap (map stampedId) (answerFails result) === Just [EventId 3, EventId 0, EventId 1, EventId 2]
      ]

prop_admission :: Property
prop_admission = fixture "admitted-coverage" $ \doc ->
  let admitted = problem doc
      unadmitted = Problem (extract (const False) (documentSource doc)) (documentUnrecorded doc)
   in conjoin
      [ answerVerdict (answer admitted (firstQuery doc)) === CertainTrue
      , answerCount (answer admitted (firstQuery doc)) === 2
      , answerVerdict (answer unadmitted (firstQuery doc)) === Unknown
      , property (all (`elem` completions unadmitted) (completions admitted))
      ]

prop_contradictoryCoverage :: Property
prop_contradictoryCoverage = fixture "admitted-coverage" $ \doc ->
  let source = documentSource doc
      scope = CoverageScope [DataAccess] Nothing Nothing Nothing 10
      assertion = CoverageAssertion (CountBounded scope 0) (SourceRef "log" "contradiction" Nothing) InstrumentedLog
      changed = doc { documentSource = source { sourceEntries = sourceEntries source ++ [CoverageEntry assertion] } }
   in answerVerdict (answer (problem changed) (firstQuery changed)) === Inconsistent

prop_selectionRead :: Property
prop_selectionRead = fixture "empty-universe" $ \doc ->
  let q = QueryAtom (SplitSelection [] [DataId 0])
      changed = doc { documentUnrecorded = [Stamped (EventId 3) (Access (ActorId 0) (DataId 0) Selection)] }
   in conjoin
      [ answerVerdict (answer (problem doc) q) === CertainTrue
      , answerVerdict (answer (problem changed) q) === Unknown
      ]

prop_versionTransition :: Property
prop_versionTransition = fixture "empty-universe" $ \doc ->
  let n = documentNames doc
      decoded text = either (Left . show) Right (parseSExpr text) >>= either (Left . show) Right . decodeStamped n
      -- Decode the real run input and update syntax; do not fake state changes.
      run0 = decoded "(event run (run run0 plan 0 (inputs (input test 0)) fam))"
      run1 = decoded "(event run (run run0 plan 0 (inputs (input test 1)) fam))"
      update = decoded "(event early-read (update-data test 1))"
      commit = decoded "(event commit (commit-plan alice plan 0))"
   in case (commit, update, run0, run1) of
      (Right c, Right u, Right old, Right new) -> conjoin
        [ property (validHistory [c, old])
        , property (not (validHistory [c, u, old]))
        , property (validHistory [c, u, new])
        , stateVersion initialState (DataId 0) === VersionId 0
        ]
      _ -> counterexample (show (commit, update, run0, run1)) False

names :: Names
names = Names ["e0", "e1", "e2"] ["a"] ["p"] ["r"] ["c"] ["s"] ["d", "other"] ["f"] ["w"]

genEvent :: Gen Event
genEvent = oneof
  [ CommitPlan (ActorId 0) (PlanId 0) . VersionId <$> nat
  , Access (ActorId 0) (DataId 0) <$> elements [Selection, Evaluation]
  , Run (RunId 0) (PlanId 0) <$> (VersionId <$> nat) <*> pure [(DataId 0, VersionId 0)] <*> pure (FamilyId 0)
  , Result (RunId 0) <$> nat
  , pure (Assert (ClaimId 0) (WitnessId 0))
  , pure (Retract (SourceId 0))
  , UpdateData (DataId 0) . VersionId <$> nat
  ]
  where nat = fromIntegral <$> choose (0, 100000 :: Integer)

genQuery :: Gen Query
genQuery = sized go
  where
    atom = QueryAtom <$> elements [Predictable, RunPrecommitted (RunId 0), SplitSelection [DataId 1] [DataId 0], FamilyCountAtMost (FamilyId 0) 2]
    go 0 = atom
    go size = frequency [(4, atom), (1, QueryNot <$> go (size `div` 2)), (1, QueryAnd <$> go (size `div` 2) <*> go (size `div` 2)), (1, QueryOr <$> go (size `div` 2) <*> go (size `div` 2))]

prop_eventRoundtrip :: Property
prop_eventRoundtrip = forAll genEvent $ \event -> decodeBody names (encodeBody names event) === Right event

prop_formulaRoundtrip :: Property
prop_formulaRoundtrip = forAll genQuery $ \query -> decodeQuery names (encodeQuery names query) === Right query

prop_profileRoundtrip :: Property
prop_profileRoundtrip = forAll (elements [FWER, FDR, MFDR]) $ \guarantee ->
  let profile = ProfileSpec [Observed, Hypothetical, Observed] [CompleteKind, OpenWorldKind, CountBoundedKind] guarantee 2 100 [Measurement, OptionalStopping, Sampling, SelectionError, Misspecification] GroundedJustified
   in decodeProfile (encodeProfile profile) === Right profile

prop_coverageRoundtrip :: Property
prop_coverageRoundtrip = forAll (elements [Nothing, Just (FamilyId 0)]) $ \family ->
  forAll (elements [Nothing, Just [], Just [ActorId 0]]) $ \actors ->
  forAll (elements [Nothing, Just [], Just [DataId 0, DataId 1]]) $ \datasets ->
  let scope = CoverageScope [PlanCommit, DataAccess, AnalysisRun, ResultProduced, ClaimAsserted, SourceRetracted, DataUpdated] family actors datasets 10
      values = [Complete scope, CountBounded scope 1, OpenWorld scope] :: [RecordCoverage Void]
   in conjoin [decodeCoverage names (encodeCoverage names value) === Right value | value <- values]

prop_refusals :: Property
prop_refusals = conjoin
  [ property (isLeft (decodeNat (SAtom value))) | value <- ["00", "01", "+1", "-1", "1.0", "", " 1", "١"] ] .&&.
  conjoin [property (isLeft (decodeBody names (SList [SAtom "commit-plan", SAtom "p", SAtom "a", SAtom "0"]))),
           property (isLeft (decodeNames (encodeNames (names { namesActor = ["a", "a"] })))),
           property (isLeft (decodeBody names (SList [SAtom "retract", SAtom "undeclared"]))),
           decodeNat (SAtom "184467440737095516160000") === Right 184467440737095516160000]

prop_shapeRefusals :: Property
prop_shapeRefusals = conjoin
  [ property (isLeft (decodeBody names (SList [SAtom "result", SAtom "r"])))
  , property (isLeft (decodeBody names (SList [SAtom "result", SAtom "r", SAtom "0", SAtom "extra"])))
  , property (isLeft (decodeScope names (tagged "scope" [tagged "kinds" [], tagged "cutoff" [SAtom "1"], tagged "data" [], tagged "actors" []])))
  , property (isLeft (decodeProfile (tagged "profile" [])))
  , case decodeCoverage names (tagged "declared-policy" []) of
      Left err -> errorTag err === Unsupported
      Right _ -> counterexample "declared policy accepted" False
  ]

prop_fixtureRoundtrip :: Property
prop_fixtureRoundtrip = conjoin [fixture name $ \doc -> decodeDocument (encodeDocument doc) === Right doc | name <- ["empty-universe", "omitted-read", "admitted-coverage", "contradictory-order", "renamed-identifiers"]]

prop_allTransitions :: Property
prop_allTransitions = conjoin [check texts expected | (texts, expected) <- cases]
  where
    check texts expected = case traverse decode texts of
      Left err -> counterexample err False
      Right history -> counterexample (show history) (validHistory history === expected)
    decode text = either (Left . show) Right (parseSExpr text) >>= either (Left . show) Right . decodeStamped names
    commit = "(event e0 (commit-plan a p 0))"
    run = "(event e1 (run r p 0 (inputs (input d 0)) f))"
    result = "(event e2 (result r 1))"
    cases =
      [ ([commit, run, result], True)
      , ([run], False)
      , ([result], False)
      , ([commit, run, "(event e2 (run r p 0 (inputs) f))"], False)
      , ([commit, commit], False)
      , (["(event e0 (retract s))", "(event e1 (retract s))"], False)
      , (["(event e0 (access a d selection))", "(event e1 (assert c w))"], True)
      , ([commit, "(event e1 (commit-plan a p 0))"], True)
      , ([commit, "(event e1 (run r p 1 (inputs) f))"], False)
      ]

prop_scopedSemantics :: Property
prop_scopedSemantics = fixture "empty-universe" $ \doc ->
  let history = case completions (problem doc) of
        h : _ -> h
        [] -> []
      scope = CoverageScope [PlanCommit, DataAccess, AnalysisRun] Nothing Nothing Nothing 10
   in conjoin
      [ map stampedId (scopeEvents scope history) === [EventId 0, EventId 1, EventId 2]
      , map stampedId (scopeEvents (scope { scopeActors = Just [ActorId 0] }) history) === [EventId 0, EventId 1]
      , map stampedId (scopeEvents (scope { scopeData = Just [DataId 0] }) history) === [EventId 1, EventId 2]
      , scopeEvents (scope { scopeData = Just [] }) history === []
      , scopeEvents (scope { scopeActors = Just [] }) history === []
      , map stampedId (scopeEvents (scope { scopeFamily = Just (FamilyId 0) }) history) === [EventId 2]
      , map stampedId (scopeEvents (scope { scopeCutoff = 1 }) history) === [EventId 0]
      , answerVerdict (answer (problem doc) (QueryNot (firstQuery doc))) === CertainFalse
      , answerVerdict (answer (problem doc) (QueryAnd (firstQuery doc) (QueryAtom (FamilyCountAtMost (FamilyId 0) 0)))) === CertainFalse
      , answerVerdict (answer (problem doc) (QueryOr (QueryNot (firstQuery doc)) (QueryAtom (FamilyCountAtMost (FamilyId 0) 1)))) === CertainTrue
      , property (not (validThrough 2 history))
      ]

prop_namespaceIsolation :: Property
prop_namespaceIsolation =
  let n = Names ["x"] ["x"] ["x"] ["x"] ["x"] ["x"] ["x"] ["x"] ["x"]
   in conjoin
      [ decodeNames (encodeNames n) === Right n
      , decodeBody n (tagged "commit-plan" [SAtom "x", SAtom "x", SAtom "0"]) === Right (CommitPlan (ActorId 0) (PlanId 0) (VersionId 0))
      , property (isLeft (decodeNames (tagged "names" [encodeTable ActorTag ["a"], encodeTable EventTag ["e"], encodeTable PlanTag [], encodeTable RunTag [], encodeTable ClaimTag [], encodeTable SourceTag [], encodeTable DataTag [], encodeTable FamilyTag [], encodeTable WitnessTag []])))
      ]

prop_exactEventArity :: Property
prop_exactEventArity = forAll genEvent $ \event -> case encodeBody names event of
  SList args -> conjoin
    [ property (isLeft (decodeBody names (SList (init args))))
    , property (isLeft (decodeBody names (SList (args ++ [SAtom "extra"]))))
    ]
  _ -> counterexample "event encoder did not produce a form" False

prop_profileRefusals :: Property
prop_profileRefusals = conjoin
  [ property (isLeft (decodeGuarantee (tagged "guarantee" [SAtom "fwer", SAtom "1", SAtom "0"])))
  , property (isLeft (decodeGuarantee (tagged "guarantee" [SAtom "FWER", SAtom "1", SAtom "10"])))
  , property (isLeft (decodeAcceptance (tagged "acceptance" [SAtom "justified"])))
  ]

prop_duplicateUniverse :: Property
prop_duplicateUniverse = fixture "omitted-read" $ \doc ->
  let original = problem doc
      duplicated = original { problemUnrecorded = problemUnrecorded original ++ problemUnrecorded original }
   in answer duplicated (firstQuery doc) === answer original (firstQuery doc)

prop_recordedUniverseOverlap :: Property
prop_recordedUniverseOverlap = fixture "omitted-read" $ \doc ->
  let original = problem doc
      overlapping = original { problemUnrecorded = base original ++ problemUnrecorded original }
      reference = dedupLast (filter (problemCompatible overlapping) (candidates overlapping))
   in completions overlapping === reference

prop_fullRecordedOverlap :: Property
prop_fullRecordedOverlap = once $
  let events = [Stamped (EventId i) (Access (ActorId 0) (DataId 0) Evaluation) | i <- [0 .. 7]]
      ref = SourceRef "log" "total-order" Nothing
      record = DecodedRecord (map (`DecodedEvent` ref) events)
        [DecodedOrder (EventId i) (EventId (i + 1)) ref | i <- [0 .. 6]] [] [] 8
   in completions (Problem record events) === [events]

prop_wireVocabulary :: Property
prop_wireVocabulary = conjoin
  [ spelling (allWords :: [Tag]), spelling (allWords :: [AccessPurpose])
  , spelling (allWords :: [EventKind]), spelling (allWords :: [AdmissionBasis])
  , spelling (allWords :: [EvidenceKind]), spelling (allWords :: [CoverageKind])
  , spelling (allWords :: [GuaranteeClass]), spelling (allWords :: [ErrorKind])
  , spelling (allWords :: [Acceptance]), spelling (allWords :: [Verdict])
  , spelling (allWords :: [ErrorTag])
  ]
  where spelling :: (WireWord a, Show a) => [a] -> Property
        spelling values = conjoin [parseWord (wordText value) === Just value | value <- values]

prop_profileMeaning :: Property
prop_profileMeaning =
  let authored = ProfileSpec [Observed, Observed] [CompleteKind] FDR 2 100 [SelectionError] GroundedJustified
      profile = toProfile authored
      scope = CoverageScope [] Nothing Nothing Nothing 0
   in conjoin
      [ property (admissibleEvidence profile Observed)
      , property (not (admissibleEvidence profile Supported))
      , property (acceptsCoverage profile (Complete scope))
      , property (not (acceptsCoverage profile (OpenWorld scope)))
      , guaranteeLevel profile === (FDR, 2 / 100)
      , property (requiredProbe profile SelectionError)
      , property (not (requiredProbe profile Sampling))
      , acceptanceStandard profile === GroundedJustified
      ]

prop_zeroDenominator :: Property
prop_zeroDenominator =
  guaranteeLevel (toProfile (ProfileSpec [] [] FWER 1 0 [] GroundedJustified)) === (FWER, 0)

prop_recordExtraction :: Property
prop_recordExtraction = forAll genEvent $ \event ->
  forAll (choose (0, 2 :: Int)) $ \index ->
  let ref = SourceRef "观测" "entry" (Just (0, 184467440737095516160000))
      record :: DecodedRecord Void
      record = DecodedRecord
        [DecodedEvent (Stamped (EventId (fromIntegral index)) event) ref]
        [DecodedOrder (EventId 2) (EventId 1) ref]
        [CoverageAssertion (OpenWorld (CoverageScope [DataAccess] Nothing (Just []) Nothing 10)) ref AuthorDeclaration]
        [(ClaimId 0, WitnessId 0), (ClaimId 0, WitnessId 0)] 10
   in extract (const True) (encodeSource record) === record

prop_namedRecord :: Property
prop_namedRecord = forAll (choose (1, 8 :: Int)) $ \size ->
  let table prefix = [prefix ++ show index | index <- [0 .. size - 1]]
      n = Names (table "event-") (table "actor-") (table "plan-") (table "run-")
        (table "claim-") (table "source-") (table "data-") (table "family-") (table "witness-")
      i = fromIntegral (size - 1)
      events =
        [ CommitPlan (ActorId i) (PlanId i) (VersionId 3)
        , Access (ActorId i) (DataId i) Evaluation
        , Run (RunId i) (PlanId i) (VersionId 3) [(DataId i, VersionId 0)] (FamilyId i)
        , Result (RunId i) 1, Assert (ClaimId i) (WitnessId i)
        , Retract (SourceId i), UpdateData (DataId i) (VersionId 9)
        ]
      ref = SourceRef "log" "row" Nothing
      scope = CoverageScope [DataAccess] (Just (FamilyId i)) (Just [ActorId i]) (Just [DataId i]) 10
      source = AraSource
        (map (\event -> EventEntry (Stamped (EventId i) event) ref) events
          ++ [OrderingEntry (EventId 0) (EventId i) ref
             , CoverageEntry (CoverageAssertion (Complete scope) ref SignedAttestation)
             , SubmissionEntry (ClaimId i) (WitnessId i)]) 10
      query = QueryAnd (QueryAtom (RunPrecommitted (RunId i)))
        (QueryAtom (SplitSelection [DataId 0] [DataId i]))
   in conjoin
      [ decodeNames (encodeNames n) === Right n
      , decodeRecord n (encodeRecord n source) === Right source
      , decodeQuery n (encodeQuery n query) === Right query
      , conjoin [decodeStamped n (encodeStamped n (Stamped (EventId i) event)) === Right (Stamped (EventId i) event) | event <- events]
      , property (not (stampedWellNamed n (Stamped (EventId (fromIntegral size)) (Retract (SourceId i)))))
      ]

prop_witnessQuantifiers :: Property
prop_witnessQuantifiers = conjoin
  [ property (entitledBy [False, True] [False, True] (==))
  , property (not (argumentEntitledBy [False, True] (==) False))
  , property (not (entitledBy ([] :: [Bool]) [True] (==)))
  , property (not (argumentEntitledBy ([] :: [Bool]) (==) True))
  , listVerdict ([] :: [Bool]) id === Inconsistent
  , listVerdict [True] id === CertainTrue
  , listVerdict [False] id === CertainFalse
  , listVerdict [True, False] id === Unknown
  ]

prop_canonicalFixture :: Property
prop_canonicalFixture = once $ ioProperty $ do
  checks <- traverse check ["empty-universe", "omitted-read", "admitted-coverage", "contradictory-order", "renamed-identifiers"]
  pure (conjoin checks)
  where
    check name = do
      text <- readFile ("fixtures/process/run/" ++ name ++ ".sexp")
      pure $ case (parseSExpr text, decodeDocumentFile text) of
        (Right sx, Right doc) -> encodeDocument doc === sx
        other -> counterexample (show other) False

prop_boundaryArity :: Property
prop_boundaryArity = conjoin
  [ fixed decodeRef (encodeRef (SourceRef "f" "e" (Just (0, 1))))
  , fixed (decodeInput names) (encodeInput names (DataId 0, VersionId 0))
  , fixed (decodeStamped names) (encodeStamped names (Stamped (EventId 0) (Retract (SourceId 0))))
  , fixed (decodeEntry names) (encodeEntry names (OrderingEntry (EventId 0) (EventId 1) (SourceRef "f" "e" Nothing)))
  , fixed (decodeEntry names) (encodeEntry names (SubmissionEntry (ClaimId 0) (WitnessId 0)))
  , fixed decodeLimits (encodeLimits (Limits 10 20))
  , fixed decodeProfile (encodeProfile (ProfileSpec [Observed] [CompleteKind] FWER 1 20 [Sampling] GroundedJustified))
  ]
  where
    fixed decode (SList values) = conjoin
      [ property (isLeft (decode (SList (init values))))
      , property (isLeft (decode (SList (values ++ [SAtom "extra"]))))
      ]
    fixed _ _ = counterexample "encoder did not produce a form" False

familyInput :: Either String Source.SourceInput
familyInput = Source.mkSourceInput program policy replay (Just capture)
  where
    policyId = A.PolicyId "family-policy"
    digest = A.Digest "family-artifact"
    backend = A.BackendId "family-backend"
    theory = A.TheoryDigest "family-theory"
    program = A.Program "family" digest policyId [(backend, "7")]
      [A.ValueBinding (A.ValueName "authored") (TNum "+01.0")] [familyClaim "base" (familyAtom "base")]
    policy = A.Policy policyId emptySigma [] [] [] [] [(theory, [])]
      A.RejectOnConflict [] [] []
    replay = Source.ReplayIdentity (Source.CoreVersion "family-core") policyId
      [Source.BackendIdentity backend (Source.BackendVersion "7")] [theory] digest
    meta = Source.ObjectMeta (ObjectId "captured") "capture.csv" 4 "digest"
    capture = Source.EvidenceCapture [(ObjectId "captured", Left "retained failure")] [meta]

familyAtom :: String -> Prop
familyAtom name = Prop (Pred name) []

familyClaim :: String -> Prop -> A.Decl
familyClaim name formal = A.DeclClaim
  (A.Claim (A.PropId name) ("claim " ++ name) formal (A.Binding "author" "rationale" A.Reviewed))

withFamilyInput :: (Source.SourceInput -> Property) -> Property
withFamilyInput check = case familyInput of
  Left err -> counterexample err False
  Right input -> check input

familyProblemFor :: [Stamped] -> [Stamped] -> Natural -> Problem
familyProblemFor recorded optional cutoff =
  Problem (DecodedRecord [DecodedEvent event ref | event <- recorded] [] [] [] cutoff) optional
  where ref = SourceRef "family" "record" Nothing

familyAccess :: Natural -> Stamped
familyAccess index = Stamped (EventId index) (Access (ActorId 0) (DataId 0) Evaluation)

familyLimits :: Audit.EnumerationLimits
familyLimits = Audit.EnumerationLimits 10000 200000 10000

withEnumeration :: Audit.FamilySpec -> Audit.EnumerationLimits
  -> (Enumerate.EnumeratedFamily -> Property) -> Property
withEnumeration spec limits check = case Enumerate.enumerateFamily spec limits of
  Left err -> counterexample (show err) False
  Right enumerated -> check enumerated

withChoices :: [(Natural, [Audit.Guard])] -> ([Audit.Slot] -> Property) -> Property
withChoices descriptions check = case Source.mkFragment [] of
  Left err -> counterexample err False
  Right fragment -> check
    [Audit.Slot (Audit.SlotId slot)
      [Audit.Choice (Audit.ChoiceId index) guard fragment | (index, guard) <- zip [0 ..] guards]
    | (slot, guards) <- descriptions]

prop_familyGuards :: Property
prop_familyGuards =
  let first = familyAccess 0
      second = familyAccess 1
      different = first { stampedEvent = Access (ActorId 0) (DataId 1) Evaluation }
      h = [first, second, first]
   in conjoin
      [ Family.guardHolds Audit.GuardTruth [] === True
      , Family.guardHolds (Audit.GuardQuery (QueryAtom Predictable)) h === queryHolds (QueryAtom Predictable) h
      , Family.guardHolds (Audit.GuardPresent first) h === True
      , Family.guardHolds (Audit.GuardPresent different) h === False
      , Family.guardHolds (Audit.GuardBefore first second) h === True
      , Family.guardHolds (Audit.GuardBefore first first) h === True
      , Family.guardHolds (Audit.GuardBefore first first) [first] === False
      , Family.guardHolds (Audit.GuardBefore different second) h === False
      , Family.guardHolds (Audit.GuardBefore first second) [second, first] === False
      , Family.guardHolds (Audit.GuardNot (Audit.GuardPresent second)) [first] === True
      , Family.guardHolds (Audit.GuardAnd (Audit.GuardPresent first) (Audit.GuardPresent second)) h === True
      , Family.guardHolds (Audit.GuardOr (Audit.GuardPresent different) (Audit.GuardPresent second)) h === True
      ]

prop_familyIdentity :: Property
prop_familyIdentity = withFamilyInput $ \input ->
  withChoices [(8, [Audit.GuardTruth, Audit.GuardNot Audit.GuardTruth]), (3, [Audit.GuardTruth])] $ \slots ->
  let spec = Audit.FamilySpec (familyProblemFor [] [] 0) input slots
      references = [(Audit.SlotId 8, Audit.ChoiceId 0), (Audit.SlotId 3, Audit.ChoiceId 0)]
   in case (slots,Family.resolveAssignment spec references) of
      (_,Nothing) -> counterexample "declared selection failed to resolve" False
      (firstSlot:_,Just assignment@(firstSelection:rest)) -> conjoin
        [ Family.familyWellFormed spec === True
        , Family.familyWellFormed spec { Audit.familySlots = slots ++ [firstSlot] } === False
        , Family.familyWellFormed spec { Audit.familySlots = [Audit.Slot (Audit.SlotId 0) []] } === False
        , Family.familyWellFormed spec { Audit.familySlots =
            [Audit.Slot (Audit.SlotId 0) [Audit.selectionChoice firstSelection, Audit.selectionChoice firstSelection]] } === False
        , Family.resolveSlot spec (Audit.SlotId 8) (Audit.ChoiceId 0) === Just firstSelection
        , Family.resolveAssignment spec [(Audit.SlotId 8, Audit.ChoiceId 99)] === Nothing
        , Family.resolveAssignment spec [] === Just []
        , Family.assignmentWellFormed spec assignment === True
        , Family.assignmentWellFormed spec (reverse assignment) === False
        , Family.assignmentWellFormed spec (take 1 assignment) === False
        , Family.assignmentMember spec [] assignment === True
        , Family.completionMember spec (Audit.Completion [] assignment) === True
        , Family.completionMember spec (Audit.Completion [familyAccess 99] assignment) === False
        , let forged = firstSelection { Audit.selectionChoice =
                (Audit.selectionChoice firstSelection) { Audit.choiceGuard = Audit.GuardNot Audit.GuardTruth } }
           in Family.assignmentWellFormed spec (forged : rest) === False
        , case Family.resolveAssignment spec [(Audit.SlotId 8, Audit.ChoiceId 1), (Audit.SlotId 3, Audit.ChoiceId 0)] of
            Nothing -> counterexample "guarded declared selection failed to resolve" False
            Just guarded -> conjoin [Family.assignmentWellFormed spec guarded === True,
              Family.assignmentMember spec [] guarded === False]
        ]
      _ -> counterexample "expected nonempty slots and resolved assignment" False

prop_familyFixedClaims :: Property
prop_familyFixedClaims = withFamilyInput $ \input ->
  let spec = Audit.FamilySpec (familyProblemFor [] [] 0) input []
      bound = Audit.ClaimBinding (ClaimId 0) (A.PropId "base") (familyAtom "base")
      changed = bound { Audit.bindingQuery = familyAtom "different" }
      fragmentOnly = bound { Audit.bindingDeclaration = A.PropId "fragment", Audit.bindingQuery = familyAtom "fragment" }
   in case Source.mkFragment [familyClaim "fragment" (familyAtom "fragment")] of
      Left err -> counterexample err False
      Right fragment -> conjoin
        [ Family.claimBindingValid spec bound === True
        , Family.claimBindingValid spec changed === False
        , Family.claimBindingValid spec fragmentOnly === False
        , Family.fixedClaims spec (Audit.AuditConfig [bound] [] [] []) === True
        , Family.fixedClaims spec (Audit.AuditConfig [bound, fragmentOnly] [] [] []) === False
        , A.programDecls (Source.sourceProgram (Family.materialize spec
            (Audit.Completion [] [Audit.Selection (Audit.SlotId 0) (Audit.Choice (Audit.ChoiceId 0) Audit.GuardTruth fragment)])))
            === A.programDecls (Source.sourceProgram input) ++ [familyClaim "fragment" (familyAtom "fragment")]
        ]

prop_familyDFSOrder :: Property
prop_familyDFSOrder = withFamilyInput $ \input ->
  let a = familyAccess 0
      b = familyAccess 1
      spec = Audit.FamilySpec (familyProblemFor [] [a, b] 2) input []
      expected = [[], [a], [a, b], [b], [b, a]]
   in withEnumeration spec (Audit.EnumerationLimits 5 5 5) $ \enumerated -> conjoin
      [ Enumerate.enumeratedSpec enumerated === spec
      , Enumerate.enumeratedHistories enumerated === expected
      , Enumerate.enumeratedCompletions enumerated === [Audit.Completion h [] | h <- expected]
      , Enumerate.enumeratedHistorySteps enumerated === 5
      , Enumerate.enumeratedLogicalExtensions enumerated === 0
      , Enumerate.enumeratedProductCount enumerated === 5
      , completions (Audit.familyProblem spec) === [[], [a], [b], [a, b], [b, a]]
      ]

prop_familyDFSNoPruning :: Property
prop_familyDFSNoPruning = withFamilyInput $ \input ->
  let a = familyAccess 0
      b = familyAccess 1
      p = familyProblemFor [b] [a, b, a] 2
      spec = Audit.FamilySpec p input []
      ref = SourceRef "family" "constraint" Nothing
      ordered = p { problemRecord = (problemRecord p) { recordOrder = [DecodedOrder (EventId 0) (EventId 1) ref] } }
      scope = CoverageScope [DataAccess] Nothing Nothing Nothing 2
      covered = p { problemRecord = (problemRecord p) { recordCoverage = [CoverageAssertion (Complete scope) ref InstrumentedLog] } }
   in conjoin
      [ withEnumeration spec familyLimits $ \e -> conjoin
          [Enumerate.enumeratedHistories e === [[b], [b, a], [a, b]], Enumerate.enumeratedHistorySteps e === 5]
      , withEnumeration spec { Audit.familyProblem = ordered } familyLimits $ \e -> conjoin
          [Enumerate.enumeratedHistories e === [[a, b]], Enumerate.enumeratedHistorySteps e === 5]
      , withEnumeration spec { Audit.familyProblem = covered } familyLimits $ \e -> conjoin
          [Enumerate.enumeratedHistories e === [[b]], Enumerate.enumeratedHistorySteps e === 5]
      , withEnumeration spec { Audit.familyProblem = p { problemRecord = (problemRecord p) { recordCutoff = 0 } } }
          familyLimits $ \e -> conjoin
          [Enumerate.enumeratedHistories e === [], Enumerate.enumeratedHistorySteps e === 5, Enumerate.enumeratedProductCount e === 0]
      , withEnumeration (Audit.FamilySpec (familyProblemFor [] [] 0) input []) (Audit.EnumerationLimits 1 1 1) $ \e ->
          conjoin [Enumerate.enumeratedHistories e === [[]], Enumerate.enumeratedHistorySteps e === 1]
      ]

prop_familyNativeBranches :: Property
prop_familyNativeBranches = withFamilyInput $ \input ->
  let commit = Stamped (EventId 0) (CommitPlan (ActorId 0) (PlanId 0) (VersionId 0))
      run = Stamped (EventId 1) (Run (RunId 0) (PlanId 0) (VersionId 0) [(DataId 0, VersionId 0)] (FamilyId 0))
      result = Stamped (EventId 2) (Result (RunId 0) 1)
      duplicate = Stamped (EventId 3) (Run (RunId 0) (PlanId 0) (VersionId 0) [] (FamilyId 0))
      updated = Stamped (EventId 4) (UpdateData (DataId 0) (VersionId 1))
      retract = Stamped (EventId 5) (Retract (SourceId 0))
      repeated = Stamped (EventId 6) (Retract (SourceId 0))
      collision = Stamped (EventId 0) (Assert (ClaimId 0) (WitnessId 0))
      spec = Audit.FamilySpec (familyProblemFor [] [result, run, commit] 3) input []
   in conjoin
      [ withEnumeration spec familyLimits $ \e -> conjoin
          [Enumerate.enumeratedHistories e === [[], [commit], [commit, run], [commit, run, result]],
           Enumerate.enumeratedHistorySteps e === 4]
      , withEnumeration spec { Audit.familyProblem = familyProblemFor [] [commit, run, duplicate, updated, retract, repeated, collision] 7 }
          familyLimits $ \e -> conjoin
          [property (all validHistory (Enumerate.enumeratedHistories e)),
           property ([commit, run, duplicate] `notElem` Enumerate.enumeratedHistories e),
           property ([commit, updated, run] `notElem` Enumerate.enumeratedHistories e),
           property ([retract, repeated] `notElem` Enumerate.enumeratedHistories e),
           property ([commit, collision] `notElem` Enumerate.enumeratedHistories e)]
      ]

prop_familyExactLimits :: Property
prop_familyExactLimits = once $ withFamilyInput $ \input ->
  let spec = Audit.FamilySpec (familyProblemFor [] [familyAccess 0, familyAccess 1] 2) input []
      refused limits expected = case Enumerate.enumerateFamily spec limits of
        Left actual -> actual === expected
        Right _ -> counterexample "over-cap enumeration returned rows" False
      ceilingSpec = Audit.FamilySpec (familyProblemFor [] (map familyAccess [0 .. 7]) 8) input []
      stepsCeilingSpec = Audit.FamilySpec (familyProblemFor [] (map familyAccess [0 .. 8]) 0) input []
   in conjoin
      [ withEnumeration spec (Audit.EnumerationLimits 5 5 5) $ \e -> Enumerate.enumeratedProductCount e === 5
      , refused (Audit.EnumerationLimits 0 0 0) (Audit.StepsRefusal 5 0)
      , refused (Audit.EnumerationLimits 5 4 5) (Audit.StepsRefusal 5 4)
      , refused (Audit.EnumerationLimits 4 5 5) (Audit.HistoriesRefusal 5 4)
      , refused (Audit.EnumerationLimits 1 5 0) (Audit.HistoriesRefusal 5 1)
      , refused (Audit.EnumerationLimits 5 5 4) (Audit.ProductsRefusal 5 4)
      , refused (Audit.EnumerationLimits 5 5 0) (Audit.ProductsRefusal 1 0)
      , Enumerate.clampedLimits (Audit.EnumerationLimits 10001 200001 10001) === familyLimits
      , case Enumerate.enumerateFamily ceilingSpec (Audit.EnumerationLimits 1000000 1000000 1000000) of
          Left actual -> actual === Audit.HistoriesRefusal 109601 10000
          Right _ -> counterexample "frozen history ceiling was bypassed" False
      , case Enumerate.enumerateFamily stepsCeilingSpec (Audit.EnumerationLimits 1000000 1000000 1000000) of
          Left actual -> actual === Audit.StepsRefusal 986410 200000
          Right _ -> counterexample "frozen step ceiling was bypassed" False
      ]

prop_familyProductsAndLogicalExtensions :: Property
prop_familyProductsAndLogicalExtensions = once $ withFamilyInput $ \input ->
  let emptyProblem = familyProblemFor [] [] 0
      check guards expectedProducts expectedExtensions =
        withChoices (zip [0 ..] guards) $ \slots ->
          withEnumeration (Audit.FamilySpec emptyProblem input slots) familyLimits $ \e -> conjoin
            [Enumerate.enumeratedProductCount e === expectedProducts,
             Enumerate.enumeratedLogicalExtensions e === expectedExtensions]
   in conjoin
      [ check [replicate 3 Audit.GuardTruth, [Audit.GuardNot Audit.GuardTruth]] 0 3
      , check [replicate 3 Audit.GuardTruth, replicate 2 Audit.GuardTruth, [Audit.GuardNot Audit.GuardTruth]] 0 9
      , check [replicate 3 Audit.GuardTruth, replicate 2 Audit.GuardTruth] 6 9
      , withChoices [(0, replicate 10001 Audit.GuardTruth), (1, [Audit.GuardNot Audit.GuardTruth])] $ \slots ->
          withEnumeration (Audit.FamilySpec emptyProblem input slots) (Audit.EnumerationLimits 1 1 0) $ \e -> conjoin
            [Enumerate.enumeratedCompletions e === [], Enumerate.enumeratedProductCount e === 0,
             Enumerate.enumeratedLogicalExtensions e === 10001]
      , withChoices [(0, replicate 10000 Audit.GuardTruth)] $ \slots ->
          withEnumeration (Audit.FamilySpec emptyProblem input slots) (Audit.EnumerationLimits 1 1 10000) $ \e ->
            Enumerate.enumeratedProductCount e === 10000
      , withChoices [(0, replicate 10001 Audit.GuardTruth)] $ \slots ->
          case Enumerate.enumerateFamily (Audit.FamilySpec emptyProblem input slots) (Audit.EnumerationLimits 1 1 1000000) of
            Left err -> err === Audit.ProductsRefusal 10001 10000
            Right _ -> counterexample "frozen product ceiling was bypassed" False
      ]

prop_familyHistoryChoiceOrder :: Property
prop_familyHistoryChoiceOrder = withFamilyInput $ \input ->
  withChoices [(9, [Audit.GuardTruth, Audit.GuardPresent (familyAccess 0)]), (4, replicate 2 Audit.GuardTruth)] $ \slots ->
  withEnumeration (Audit.FamilySpec (familyProblemFor [] [familyAccess 0] 1) input slots) familyLimits $ \e ->
  let identity completion =
        (map stampedId (Audit.completionHistory completion),
         [(Audit.selectionSlot selection, Audit.choiceId (Audit.selectionChoice selection)) | selection <- Audit.completionAssignment completion])
      assignment first second = [(Audit.SlotId 9, Audit.ChoiceId first), (Audit.SlotId 4, Audit.ChoiceId second)]
   in conjoin
      [ map identity (Enumerate.enumeratedCompletions e) ===
          [([], assignment 0 0), ([], assignment 0 1),
           ([EventId 0], assignment 0 0), ([EventId 0], assignment 0 1),
           ([EventId 0], assignment 1 0), ([EventId 0], assignment 1 1)]
      , Enumerate.enumeratedLogicalExtensions e === 9
      , Enumerate.enumeratedProductCount e === 6
      ]

prop_familyMaterialization :: Property
prop_familyMaterialization = withFamilyInput $ \input ->
  let certificate name = A.DeclArg (A.Arg (A.ArgId name) (A.SupportsDerived (A.PropId name))
        (A.ExplicitTheta (A.SRule (A.RuleId "certificate") [] [] [] []
          (A.AssuranceCert (A.Cert (A.BackendId "family-backend") 7 (A.TheoryDigest "family-theory") (SAtom "7"))))))
      firstDecls = [A.DeclLeaf (A.Leaf (A.LeafId "hypothesis") (familyAtom "h") A.Assumed A.User [] Nothing), certificate "first"]
      comparison = A.Comparison (familyAtom "better") (A.MeasurandId "accuracy") (A.DatasetId "data")
        A.StrictlyBetter (A.ArgId "recheck") (A.ArgId "bridge") (A.LeafId "result")
        (A.LeafId "baseline") (A.LeafId "binding") (A.ComparisonClaim (A.PropId "comparison") "raw" (A.Binding "author" "" A.Unreviewed)) Nothing
      secondDecls = [certificate "second", A.DeclComparison comparison, A.DeclStatus (A.PropId "base"), certificate "second"]
      firstPayload = [(Source.DeclarationCertificate 1 [], Source.CertificateInteger 7)]
      secondPayload = [(Source.DeclarationCertificate 0 [], Source.CertificateString "7"),
        (Source.DeclarationCertificate 3 [], Source.CertificateInteger 7)]
   in case (Source.mkFragmentWithPayloads firstDecls firstPayload, Source.mkFragmentWithPayloads secondDecls secondPayload) of
      (Right first, Right second) ->
        let a = Audit.Choice (Audit.ChoiceId 0) Audit.GuardTruth first
            b = Audit.Choice (Audit.ChoiceId 1) Audit.GuardTruth second
            spec = Audit.FamilySpec (familyProblemFor [] [] 0) input [Audit.Slot (Audit.SlotId 0) [a], Audit.Slot (Audit.SlotId 1) [b]]
            completion = Audit.Completion [] [Audit.Selection (Audit.SlotId 0) a, Audit.Selection (Audit.SlotId 1) b]
            materialized = Family.materialize spec completion
         in conjoin
            [ Family.selectedDecls completion === firstDecls ++ secondDecls
            , A.programDecls (Source.sourceProgram materialized) === A.programDecls (Source.sourceProgram input) ++ firstDecls ++ secondDecls
            , (Source.sourceProgram materialized) { A.programDecls = A.programDecls (Source.sourceProgram input) } === Source.sourceProgram input
            , Source.sourcePolicy materialized === Source.sourcePolicy input
            , Source.sourceReplay materialized === Source.sourceReplay input
            , Source.sourceCapture materialized === Source.sourceCapture input
            , Source.sourceCertificatePayloads materialized ===
                [(Source.DeclarationCertificate 2 [], Source.CertificateInteger 7),
                 (Source.DeclarationCertificate 3 [], Source.CertificateString "7"),
                 (Source.DeclarationCertificate 6 [], Source.CertificateInteger 7)]
            , Family.hypotheticalKeys completion ===
                [Audit.LeafKey (A.LeafId "hypothesis"), Audit.ArgumentKey (A.ArgId "first"),
                 Audit.ArgumentKey (A.ArgId "second"), Audit.ArgumentKey (A.ArgId "recheck"),
                 Audit.ArgumentKey (A.ArgId "bridge"), Audit.ArgumentKey (A.ArgId "second")]
            , withEnumeration spec familyLimits $ \e -> Enumerate.enumeratedCompletions e === [completion]
            ]
      other -> counterexample (show other) False

familyEnumerationProps :: [(String, IO Result)]
familyEnumerationProps =
  [(description, quickCheckResult prop) | (description, prop) <-
    [ ("family guards retain exact stamped occurrences and fixed-history semantics", prop_familyGuards)
    , ("family resolution retains exact choices and validates slot identity", prop_familyIdentity)
    , ("family fixed claims bind only exact base declarations", prop_familyFixedClaims)
    , ("family DFS includes root and preserves prefix order without changing P0", prop_familyDFSOrder)
    , ("family compatibility filters output without pruning executable prefixes", prop_familyDFSNoPruning)
    , ("family DFS executes native run version retraction and event-identity gates", prop_familyNativeBranches)
    , ("family refusals report full steps and histories before saturated products", prop_familyExactLimits)
    , ("family late empty guards retain logical prefixes without allocating products", prop_familyProductsAndLogicalExtensions)
    , ("family products retain history outer and choice outer order", prop_familyHistoryChoiceOrder)
    , ("family materialization preserves metadata coordinates duplicates and hypothetical comparisons", prop_familyMaterialization)
    ]]

prop_inquiryUnresolvedBudget :: Property
prop_inquiryUnresolvedBudget = once $ ioProperty $ do
  bytes <- BS.readFile "fixtures/process/inquiry/unresolved-claim-impact.sexp"
  pure $ case InquiryWire.parseInquiryInputBS bytes of
    Left refusal -> counterexample (show refusal) False
    Right input ->
      let withPairs cap = input { Inquiry.inquiryLimits =
            (Inquiry.inquiryLimits input) { Inquiry.limitPairs = cap } }
          run cap = InquiryRun.runBounded (withPairs cap) (fromIntegral (BS.length bytes))
       in conjoin
          [run 17 === Left (Inquiry.Limit Inquiry.Pairs 18 17)
          ,run 18 === Left (Inquiry.Malformed "unresolved claim in impact request")]

prop_inquiryCompleteConsumers :: Property
prop_inquiryCompleteConsumers = once $ ioProperty $ do
  checks <- traverse check
    ["p0-verdict","p0-embedded-audit","fixed-query","fixed-witness","mixed-stability"
    ,"reference-sensitivity","joint-only","minimal-conditions","new-attacker"
    ,"verified-certificate","tampered-certificate","impact-rejected","source-rejections"]
  pure (conjoin checks)
  where
    check name = do
      bytes <- BS.readFile ("fixtures/process/inquiry/" ++ name ++ ".sexp")
      expected <- readFile ("fixtures/process/inquiry/" ++ name ++ ".expected")
      pure $ case InquiryWire.parseInquiryInputBS bytes of
        Left refusal -> counterexample (name ++ ": " ++ show refusal) False
        Right input ->
          let names = documentNames (Inquiry.inquiryProcess input)
              decoded = traverse (\line -> either (Left . show) Right (parseSExpr line)
                >>= either (Left . show) Right . InquiryWire.parseInquiryResult names) (lines expected)
           in case (decoded,InquiryRun.runBounded input (fromIntegral (BS.length bytes))) of
             (Right wanted,Right actual) -> conjoin
               [actual === wanted,conjoin [InquiryWire.parseInquiryResult names
                 (InquiryWire.encodeInquiryResult names result) === Right result | result <- actual]]
             pair -> counterexample (name ++ ": " ++ show pair) False

prop_inquiryRefusalConsumers :: Property
prop_inquiryRefusalConsumers = conjoin
  [ InquiryWire.parseInquiryError (InquiryWire.encodeInquiryError error') === Right error'
  | label <- [Nothing,Just "",Just "report"]
  , refusal <- [Inquiry.Malformed "detail",Inquiry.SyntaxError "line 1",Inquiry.Unsupported "feature"
    ,Inquiry.Version "2",Inquiry.Usage "usage: lara inquiry FILE",Inquiry.IOFailure "cannot read path"]
    ++ [Inquiry.Limit counter (2^(128 :: Natural)) (2^(127 :: Natural)) | counter <- [minBound..maxBound]]
  , let error' = Inquiry.InquiryError label refusal]

prop_inquiryConsumerRefusals :: Property
prop_inquiryConsumerRefusals = once $ ioProperty $ do
  bytes <- BS.readFile "fixtures/process/inquiry/joint-only.sexp"
  pure $ case InquiryWire.parseInquiryInputBS bytes of
    Left refusal -> counterexample (show refusal) False
    Right input ->
      let namespace = documentNames (Inquiry.inquiryProcess input)
          check tag parse = conjoin
            [ parse (SList [SAtom tag,SAtom "2"]) ===
                Left (Inquiry.Version (tag ++ " supports version 1 only, found 2"))
            , parse (SList [SAtom tag,SAtom "1"]) ===
                Left (Inquiry.Malformed ("malformed " ++ tag))
            , parse (SList [SAtom tag]) ===
                Left (Inquiry.Malformed ("expected an " ++ tag ++ " envelope"))
            ]
       in check "inquiry-result" (InquiryWire.parseInquiryResult namespace)
          .&&. check "inquiry-error" InquiryWire.parseInquiryError

prop_inquiryParserRenderer :: Property
prop_inquiryParserRenderer = conjoin
  [ InquiryWire.parseInquiryInputBS (BS.pack bytes) === Left (Inquiry.SyntaxError detail)
  | (bytes,detail) <- [([92],"line 1, column 1: unexpected character '\\'")
    ,([206,177],"line 1, column 1: unexpected character 'α'")
    ,([1],"line 1, column 1: unexpected character '\SOH'")]]
  .&&. RawWire.parseSExprBS (BS.pack [92]) ===
    Left (RawWire.ParseError 1 1 ("unexpected character " ++ show '\\'))

prop_inquiryBudgetBoundaries :: Property
prop_inquiryBudgetBoundaries = once $ ioProperty $ do
  checks <- traverse check
    ["limit-histories-at-cap","limit-histories-cap-plus-one","limit-sources-at-cap","limit-sources"
    ,"limit-declarations-at-cap","limit-declarations-cap-plus-one","limit-pairs-at-cap"
    ,"limit-pairs-cap-plus-one","limit-subsets-at-cap","limit-subsets","limit-search-at-cap","limit-search"
    ,"limit-source-bytes-at-cap","limit-source-bytes-cap-plus-one"]
  pure (conjoin checks)
  where
    check name = do
      bytes <- BS.readFile ("fixtures/process/inquiry/" ++ name ++ ".sexp")
      expected <- readFile ("fixtures/process/inquiry/" ++ name ++ ".expected")
      pure $ case InquiryWire.parseInquiryInputBS bytes of
        Left refusal -> counterexample (name ++ ": " ++ show refusal) False
        Right input ->
          let names = documentNames (Inquiry.inquiryProcess input)
              output = case InquiryRun.runBounded input (fromIntegral (BS.length bytes)) of
                Left refusal -> [InquiryWire.encodeInquiryError (Inquiry.InquiryError Nothing refusal)]
                Right results -> map (InquiryWire.encodeInquiryResult names) results
           in traverse parseSExpr (lines expected) === Right output

prop_inquiryAllocationPrecedence :: Property
prop_inquiryAllocationPrecedence = once $ ioProperty $ do
  bytes <- BS.readFile "fixtures/process/inquiry/minimal-conditions.sexp"
  pure $ case InquiryWire.parseInquiryInputBS bytes of
    Left refusal -> counterexample (show refusal) False
    Right input -> case [target | Inquiry.MinimalAssumptionsRequest _ target <- Inquiry.inquiryRequests input] of
      target:_ ->
        let huge = 2^(128 :: Natural)
            catalog = [InquiryLiteral.SlotEq (Audit.SlotId index) (Audit.ChoiceId 0) | index <- [0..127]]
            changed = input { Inquiry.inquiryCatalog = catalog
              ,Inquiry.inquiryRequests = [Inquiry.MinimalAssumptionsRequest "duplicate" target,Inquiry.MinimalAssumptionsRequest "duplicate" target]
              ,Inquiry.inquiryLimits = (Inquiry.inquiryLimits input) { Inquiry.limitSubsets = 1,Inquiry.limitPairs = 0 } }
         in InquiryRun.runBounded changed (fromIntegral (BS.length bytes)) === Left (Inquiry.Limit Inquiry.Subsets (2*huge) 1)
      [] -> counterexample "missing authored minimal assumption target" False

prop_inquiryLabelsAfterPairs :: Property
prop_inquiryLabelsAfterPairs = once $ ioProperty $ do
  bytes <- BS.readFile "fixtures/process/inquiry/unresolved-claim-impact.sexp"
  pure $ case InquiryWire.parseInquiryInputBS bytes of
    Left refusal -> counterexample (show refusal) False
    Right input -> case Inquiry.inquiryRequests input of
      request@(Inquiry.ImpactRequest label _ _ _):_ ->
        let changed cap = input { Inquiry.inquiryRequests = [request]
              ,Inquiry.inquiryProcess = (Inquiry.inquiryProcess input) { documentQueries = [VerdictQuery label (QueryAtom Predictable)] }
              ,Inquiry.inquiryLimits = (Inquiry.inquiryLimits input) { Inquiry.limitPairs = cap } }
            run cap = InquiryRun.runBounded (changed cap) (fromIntegral (BS.length bytes))
         in conjoin [run 17 === Left (Inquiry.Limit Inquiry.Pairs 18 17)
                    ,run 18 === Left (Inquiry.Malformed "duplicate result labels")]
      _ -> counterexample "missing authored impact request" False

prop_inquiryEventsBeforeBytes :: Property
prop_inquiryEventsBeforeBytes = once $ ioProperty $ do
  bytes <- BS.readFile "fixtures/process/inquiry/p0-verdict.sexp"
  pure $ case InquiryWire.parseInquiryInputBS bytes of
    Left refusal -> counterexample (show refusal) False
    Right input ->
      let document = Inquiry.inquiryProcess input
          p = problem document
          count = naturalLength (dedupLast (base p ++ problemUnrecorded p))
          changed = input { Inquiry.inquiryProcess = document
                { documentLimits = (documentLimits document) { limitEvents = 0 } }
            ,Inquiry.inquiryLimits = (Inquiry.inquiryLimits input) { Inquiry.limitSourceBytes = 0 } }
       in conjoin [property (count > 0)
                  ,InquiryRun.runBounded changed (fromIntegral (BS.length bytes)) === Left (Inquiry.Limit Inquiry.Histories count 0)]

prop_inquiryReferencesBeforeBindings :: Property
prop_inquiryReferencesBeforeBindings = once $ ioProperty $ do
  bytes <- BS.readFile "fixtures/process/inquiry/unresolved-claim-impact.sexp"
  pure $ case InquiryWire.parseInquiryInputBS bytes of
    Left refusal -> counterexample (show refusal) False
    Right input -> case Inquiry.inquiryRequests input of
      impact@(Inquiry.ImpactRequest _ _ _ (claim:_)):_ ->
        let badReference = Inquiry.ReferenceSpec [] [(Audit.SlotId (2^(128 :: Natural)),Audit.ChoiceId 0)]
            changed = input { Inquiry.inquiryRequests =
              [Inquiry.SensitivityRequest "outside-family" badReference (InquiryLiteral.StatusObservable claim),impact]
              ,Inquiry.inquiryLimits = (Inquiry.inquiryLimits input) { Inquiry.limitPairs = 4096 } }
         in InquiryRun.runBounded changed (fromIntegral (BS.length bytes)) ===
              Left (Inquiry.Malformed "unresolved or out-of-family source reference")
      _ -> counterexample "missing authored unresolved claim" False

prop_inquiryAllocationSourcesFirst :: Property
prop_inquiryAllocationSourcesFirst = once $ ioProperty $ do
  bytes <- BS.readFile "fixtures/process/inquiry/minimal-conditions.sexp"
  pure $ case InquiryWire.parseInquiryInputBS bytes of
    Left refusal -> counterexample (show refusal) False
    Right input -> case [target | Inquiry.MinimalAssumptionsRequest _ target <- Inquiry.inquiryRequests input] of
      target:_ ->
        let p = problem (Inquiry.inquiryProcess input)
            spec = Audit.FamilySpec p (Inquiry.inquiryBase input) (Inquiry.inquirySlots input)
            limits = Inquiry.inquiryLimits input
            enumLimits = Audit.EnumerationLimits
              (min (Inquiry.limitHistories limits) (limitCompletions (documentLimits (Inquiry.inquiryProcess input))))
              (Inquiry.limitSearchSteps limits) (Inquiry.limitSources limits)
            changed = input { Inquiry.inquiryRequests =
              [Inquiry.MinimalAssumptionsRequest "subsets" target
              ,Inquiry.ImpactRequest "impact" (Inquiry.inquiryBase input) (Inquiry.inquiryBase input) []]
              ,Inquiry.inquiryLimits = limits { Inquiry.limitSubsets = 0,Inquiry.limitDeclarations = 0,Inquiry.limitPairs = 0 } }
         in case Enumerate.enumerateFamily spec enumLimits of
              Left refusal -> counterexample (show refusal) False
              Right enumeration ->
                let rows = naturalLength (Enumerate.enumeratedCompletions enumeration)
                    actual = rows + 2
                    restricted = changed { Inquiry.inquiryLimits =
                      (Inquiry.inquiryLimits changed) { Inquiry.limitSources = rows } }
                 in InquiryRun.runBounded restricted (fromIntegral (BS.length bytes)) === Left (Inquiry.Limit Inquiry.Sources actual rows)
      _ -> counterexample "missing minimal assumptions request" False



processSpecProps :: [(String, IO Result)]
processSpecProps =
  [ ("process empty universe preserves precommitment", quickCheckResult (fixtureVerdict "empty-universe" CertainTrue 2))
  , ("process omitted evaluation read introduces ordered unknown witnesses", quickCheckResult prop_omittedRead)
  , ("process omitted selection read defeats read separation", quickCheckResult prop_selectionRead)
  , ("process only admitted coverage removes completions", quickCheckResult prop_admission)
  , ("process contradictory coverage is inconsistent", quickCheckResult prop_contradictoryCoverage)
  , ("process contradictory order is inconsistent", quickCheckResult (fixtureVerdict "contradictory-order" Inconsistent 0))
  , ("process renamed identifiers preserve semantics", quickCheckResult (fixtureVerdict "renamed-identifiers" CertainTrue 2))
  , ("process data update invalidates old run input", quickCheckResult prop_versionTransition)
  , ("process all event bodies roundtrip", quickCheckResult prop_eventRoundtrip)
  , ("process formulas roundtrip", quickCheckResult prop_formulaRoundtrip)
  , ("process profiles preserve authored fields", quickCheckResult prop_profileRoundtrip)
  , ("process scoped coverage roundtrip", quickCheckResult prop_coverageRoundtrip)
  , ("process names and canonical naturals refuse aliases", quickCheckResult prop_refusals)
  , ("process codec enforces arity and clause order", quickCheckResult prop_shapeRefusals)
  , ("process decoded fixtures roundtrip", quickCheckResult prop_fixtureRoundtrip)
  , ("process every state transition enforces prerequisites", quickCheckResult prop_allTransitions)
  , ("process scopes and all four verdicts expose exact semantics", quickCheckResult prop_scopedSemantics)
  , ("process namespaces isolate identities without forbidding shared text", quickCheckResult prop_namespaceIsolation)
  , ("process every event body has exact arity", quickCheckResult prop_exactEventArity)
  , ("process profiles refuse zero denominators and unknown vocabulary", quickCheckResult prop_profileRefusals)
  , ("process duplicate universe entries preserve answer witnesses", quickCheckResult prop_duplicateUniverse)
  , ("process recorded universe overlap preserves reference completion order", quickCheckResult prop_recordedUniverseOverlap)
  , ("process eight recorded events ignore impossible overlapping permutations", quickCheckResult prop_fullRecordedOverlap)
  , ("process closed vocabulary spellings are unique", quickCheckResult prop_wireVocabulary)
  , ("process profile interpretation matches authored requirements", quickCheckResult prop_profileMeaning)
  , ("process typed zero denominator has total reference meaning", quickCheckResult prop_zeroDenominator)
  , ("process extraction preserves complete ordered records", quickCheckResult prop_recordExtraction)
  , ("process varied namespaces preserve nonzero record identities", quickCheckResult prop_namedRecord)
  , ("process claim and submitted witness quantifiers remain distinct", quickCheckResult prop_witnessQuantifiers)
  , ("process fixture reencoding is canonical without losing fields", quickCheckResult prop_canonicalFixture)
  , ("process boundary records enforce exact arity", quickCheckResult prop_boundaryArity)
  , ("inquiry unresolved impact charges its exact budget before malformed binding", quickCheckResult prop_inquiryUnresolvedBudget)
  , ("inquiry complete consumers match every frozen result body", quickCheckResult prop_inquiryCompleteConsumers)
  , ("inquiry errors roundtrip optional labels and unbounded structured counters", quickCheckResult prop_inquiryRefusalConsumers)
  , ("inquiry consumers distinguish wrong versions malformed bodies and missing envelopes", quickCheckResult prop_inquiryConsumerRefusals)
  , ("inquiry parser renders portable unicode details without changing legacy", quickCheckResult prop_inquiryParserRenderer)
  , ("inquiry exact caps and cap plus one match frozen whole document outcomes", quickCheckResult prop_inquiryBudgetBoundaries)
  , ("inquiry huge deduplicated catalogs refuse allocation before pair work and labels", quickCheckResult prop_inquiryAllocationPrecedence)
  , ("inquiry pairs precede cross-list labels which precede unresolved bindings", quickCheckResult prop_inquiryLabelsAfterPairs)
  , ("inquiry embedded event limit precedes even a zero byte cap", quickCheckResult prop_inquiryEventsBeforeBytes)
  , ("inquiry references resolve before missing impact bindings after budgets", quickCheckResult prop_inquiryReferencesBeforeBindings)
  , ("inquiry endpoint allocation precedes subset declaration and pair gates", quickCheckResult prop_inquiryAllocationSourcesFirst)
  ]
  ++ familyEnumerationProps
