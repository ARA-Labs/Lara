module ProcessSpec (processSpecProps) where

import Data.Either (isLeft)
import Data.List (find)
import Data.Void (Void)
import Numeric.Natural (Natural)
import Test.QuickCheck

import Lara.Process.Types
import Lara.Process.History
import Lara.Process.Wire
import Lara.Strict (SExpr (..))
import Lara.Wire (parseSExpr)

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
  ]
