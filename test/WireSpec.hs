-- | Ground-truth tests for the S-expression wire codec ("Lara.Wire", the N11
-- differential anchor; M3 plan review D11).
--
-- Three layers, mirroring the "StrictSpec" atom-key pattern:
--
--   * __hand-verified golden vectors__ — exact text ↔ value pairs for the
--     textual codec (bare/quoted atoms, escapes, comments), one full unit,
--     and verdicts;
--   * __round-trip properties__ — @parse ∘ print = id@ on 'SExpr' trees, and
--     @decode ∘ encode = Right id@ on units, checker inputs, and verdicts
--     (generators respect the documented AST invariants: 'PLit' literals
--     only, non-negative versions and indices, unique argument ids, declared
--     attack endpoints; checker inputs and verdicts carry varied canonical
--     replay identities — 0-3 sorted theory digests, occasionally non-ASCII
--     to exercise the quoted-atom path, and varied backend selections —
--     PR #44 review C10);
--   * __malformed-input rejection matrix__ — text-level errors, then one
--     field short / one field long per grammar construct, unknown tags, bad
--     naturals, and the two wire-well-formedness invariants (duplicate
--     argument ids, undeclared attack endpoints).
--
-- The two 'prop_leanDriver*' goldens are hand-authored pins of the wire
-- bytes the Lean driver (@lean/Lara/Driver.lean@) must print for the
-- corresponding fixtures; the differential harness confirms the actual Lean
-- output against them.
module WireSpec (wireSpecProps) where

import Data.Char (ord)
import Data.List (isPrefixOf, nub, sortBy)
import Data.Ord (comparing)
import Test.QuickCheck

import Lara.AST hiding (Reject)
import Lara.Replay
import Lara.Prop (Prop (..), Term (..))
import Lara.Strict (SExpr (..))
import Lara.Wire

-- ---------------------------------------------------------------------------
-- Generators
-- ---------------------------------------------------------------------------

-- | Identifiers: short bare-safe names (quoting paths are exercised by the
-- atom-payload generator below).
genIdent :: Gen String
genIdent = do
  n <- choose (1, 6)
  vectorOf n (elements (['a' .. 'z'] ++ ['0' .. '9'] ++ "-_"))

-- | Lists in recursive generator positions: a small bounded length, keeping
-- the expected branching factor below one so tree sizes stay linear in the
-- QuickCheck size parameter (an unbounded 'listOf' here is supercritical —
-- it made the suite generate multi-gigabyte units).
smallListOf :: Gen a -> Gen [a]
smallListOf g = do
  k <- choose (0, 3 :: Int)
  vectorOf k g

-- | Arbitrary atom payloads, including strings that force quoting and every
-- escaped character.
genAtomString :: Gen String
genAtomString =
  oneof
    [ genIdent
    , pure ""
    , listOf (elements (['a' .. 'd'] ++ " \t\"\\\nπ雪:;()"))
    ]

genNumString :: Gen String
genNumString =
  oneof
    [ show <$> (arbitrary :: Gen (NonNegative Int))
    , do
        sign <- elements ["", "+", "-"]
        digits <- listOf1 (elements ['0' .. '9'])
        frac <-
          oneof
            [ pure ""
            , do
                f <- listOf1 (elements ['0' .. '9'])
                pure ("." ++ f)
            ]
        pure (sign ++ digits ++ frac)
    ]

genCanonicalNat :: Gen Int
genCanonicalNat = choose (0, 9999)

genSExpr :: Gen SExpr
genSExpr = sized go
  where
    go n
      | n <= 0 = SAtom <$> genAtomString
      | otherwise =
          frequency
            [ (3, SAtom <$> genAtomString)
            , (2, SList <$> smallListOf (go (n `div` 2)))
            ]

genTerm :: Gen Term
genTerm = sized go
  where
    go n
      | n <= 0 =
          oneof
            [ TNum <$> genNumString
            , TStr <$> genAtomString
            , TCon <$> (FunSym <$> genIdent) <*> pure []
            ]
      | otherwise =
          frequency
            [ (3, go 0)
            , (1, TCon <$> (FunSym <$> genIdent) <*> smallListOf (go (n `div` 2)))
            ]

genProp :: Gen Prop
genProp = Prop <$> (Pred <$> genIdent) <*> smallListOf genTerm

genPat :: Gen Pat
genPat = sized go
  where
    go n
      | n <= 0 =
          oneof
            [ PVar . Param <$> genIdent
            , PLit . TNum <$> genNumString
            , PLit . TStr <$> genAtomString
            , PCon <$> (FunSym <$> genIdent) <*> pure []
            ]
      | otherwise =
          frequency
            [ (3, go 0)
            , (1, PCon <$> (FunSym <$> genIdent) <*> smallListOf (go (n `div` 2)))
            ]

genAtomPat :: Gen AtomPat
genAtomPat = AtomPat <$> (Pred <$> genIdent) <*> smallListOf genPat

genQuestion :: Gen Question
genQuestion =
  Question
    <$> (QuestionId <$> genIdent)
    <*> genAtomPat
    <*> elements [Mandatory, Optional]

genCertifier :: Gen CertRef
genCertifier =
  CertRef
    <$> (BackendId <$> genIdent)
    <*> genCanonicalNat
    <*> (TheoryDigest <$> genAtomString)

genRule :: Gen Rule
genRule = do
  rid <- RuleId <$> genIdent
  params <- smallListOf (Param <$> genIdent)
  mode <- elements [Strict, Defeasible]
  prems <- smallListOf genAtomPat
  concl <- genAtomPat
  at <- arbitrary
  certs <- smallListOf genCertifier
  qs <- smallListOf genQuestion
  pure
    Rule
      { ruleId = rid
      , ruleParams = params
      , ruleMode = mode
      , rulePremises = prems
      , ruleConclusion = concl
      , ruleAllowTrusted = at
      , ruleCertifiers = certs
      , ruleQuestions = qs
      }

genAssurance :: Gen Assurance
genAssurance =
  oneof
    [ pure AssuranceNone
    , pure AssuranceTrusted
    , AssuranceCert
        <$> ( Cert
                <$> (BackendId <$> genIdent)
                <*> genCanonicalNat
                <*> (TheoryDigest <$> genAtomString)
                <*> genSExpr
            )
    ]

genSupportTerm :: Gen SupportTerm
genSupportTerm = sized go
  where
    go n
      | n <= 0 = SLeaf . LeafId <$> genIdent
      | otherwise =
          frequency
            [ (2, SLeaf . LeafId <$> genIdent)
            , ( 3
              , SRule
                  <$> (RuleId <$> genIdent)
                  <*> smallListOf ((,) <$> (Param <$> genIdent) <*> genTerm)
                  <*> smallListOf (go (n `div` 2))
                  <*> smallListOf
                    ((,) <$> (QuestionId <$> genIdent) <*> go (n `div` 2))
                  <*> smallListOf (ObligationId <$> genIdent)
                  <*> genAssurance
              )
            ]

genPosition :: Gen Position
genPosition =
  listOf
    ( oneof
        [ StepPremise <$> genCanonicalNat
        , StepQuestion . QuestionId <$> genIdent
        ]
    )

genAttackFrom :: [ArgId] -> Gen Attack
genAttackFrom aids =
  oneof
    [ Rebut <$> elements aids <*> elements aids
    , Undercut <$> elements aids <*> elements aids <*> genPosition
    , Undermine <$> elements aids <*> elements aids <*> genPosition
    ]

genUnit :: Gen Unit
genUnit = do
  rules <- smallListOf genRule
  contraries <- smallListOf (Contrary <$> genAtomPat <*> genAtomPat)
  exceptions <-
    smallListOf (Exception <$> (RuleId <$> genIdent) <*> genAtomPat)
  theories <-
    smallListOf ((,) <$> (TheoryDigest <$> genAtomString) <*> smallListOf genProp)
  leaves <- smallListOf ((,) <$> (LeafId <$> genIdent) <*> genProp)
  nArgs <- choose (0, 4)
  argTerms <- vectorOf nArgs (scale (`div` 2) genSupportTerm)
  let args = zip [ArgId ("a" ++ show i) | i <- [0 ..]] argTerms
  attacks <-
    if null args
      then pure []
      else smallListOf (genAttackFrom (map fst args))
  queries <- smallListOf genProp
  let leafIds = nub (map fst leaves)
  groupMembers <-
    if length leafIds < 2
      then pure []
      else choose (0, 2) >>= \n -> vectorOf n (sublistOf leafIds)
  let groups =
        [ DupGroup (GroupId ("g" ++ show i)) (nub ms)
        | (i, ms) <- zip [0 :: Int ..] groupMembers
        , length (nub ms) >= 2
        ]
  -- The conflict mode is only wire-carried when groups exist, so keep it at the
  -- canonical default otherwise (else @decode ∘ encode@ would not be identity).
  groupMode <-
    if null groups
      then pure QuarantineOnConflict
      else elements [QuarantineOnConflict, RejectOnConflict]
  pure
    Unit
      { unitRules = rules
      , unitContraries = contraries
      , unitExceptions = exceptions
      , unitTheories = theories
      , unitLeaves = leaves
      , unitArgs = args
      , unitAttacks = attacks
      , unitQueries = queries
      , unitGroups = groups
      , unitGroupMode = groupMode
      }

-- ---------------------------------------------------------------------------
-- Varied replay identities (PR #44 review C10)
-- ---------------------------------------------------------------------------

-- | Theory-digest text: mostly bare @sha256:@ digests, occasionally carrying
-- non-ASCII characters (@é@, @λ@, @π@, @雪@) to exercise the quoted-atom
-- codec path and make Unicode code-point order observable.
genTheoryDigestText :: Gen String
genTheoryDigestText =
  oneof
    [ ("sha256:" ++) <$> genIdent
    , ("sha256:" ++) <$> listOf1 (elements (['a' .. 'f'] ++ ['0' .. '9'] ++ "éλπ雪"))
    ]

-- | 0-3 distinct theory digests in canonical (strictly increasing Unicode
-- code-point) order, as 'mkReplayId' requires.
genCanonicalTheories :: Gen [TheoryDigest]
genCanonicalTheories = do
  k <- choose (0, 3)
  texts <- vectorOf k genTheoryDigestText
  pure (map TheoryDigest (sortBy (comparing (map ord)) (nub texts)))

-- | A backend selection: 0-3 (name, version) pairs with arbitrary atom
-- payloads, occasionally forcing quoted output. 'mkReplayId' does not
-- validate the selection (that is the runtime preflight's job), so any
-- strings are wire-valid here.
genBackendSelection :: Gen [(BackendId, String)]
genBackendSelection = do
  k <- choose (0, 3)
  vectorOf k ((,) <$> (BackendId <$> genBackendText) <*> genBackendText)
  where
    genBackendText = oneof [genIdent, show <$> genCanonicalNat, genAtomString]

-- | A valid replay identity with varied policy, backend selection, canonical
-- theories, and artifact digest — never the fixed golden identity.
genReplayId :: Gen ReplayId
genReplayId = do
  policy <- PolicyId <$> genAtomString
  backends <- genBackendSelection
  theories <- genCanonicalTheories
  artifact <- Digest <$> genAtomString
  case mkReplayId LaraCoreV01 policy backends theories artifact of
    Right replayId -> pure replayId
    Left _ -> discard -- unreachable: the theories are canonical by construction

-- | A full checker input with a varied replay identity (C10), built directly
-- via 'mkReplayId' / 'mkCheckInput' (not 'testCheckInput''s fixed
-- constants). The unit's theory table carries exactly the identity's digests
-- as @(digest, [])@ pairs — the 'mkCheckInput' consistency gate compares the
-- sorted theory keys only, and the generated digests are distinct and
-- canonical, so construction always succeeds.
genCheckInput :: Gen CheckInput
genCheckInput = do
  generatedUnit <- genUnit
  replayId <- genReplayId
  let unit =
        generatedUnit
          { unitTheories = [(digest, []) | digest <- replayTheories replayId]
          }
  case mkCheckInput replayId unit of
    Right input -> pure input
    Left _ -> discard -- unreachable: unit theory keys are the identity's

genLabel :: Gen Label
genLabel = elements [LIn, LOut, LUndec]

genStatus :: Gen Status
genStatus = elements [Gap, Justified, Contested, Defeated]

-- | A public status: ordinary, or @evidence-blocked@ over a conditional label
-- (spec §4.3, issue #76). Blocked entries are generated at roughly one in three
-- so the conditional section is exercised on most multi-query verdicts.
genPublicStatus :: Gen PublicStatus
genPublicStatus =
  frequency [(2, Published <$> genStatus), (1, EvidenceBlocked <$> genStatus)]

genRejection :: Gen Rejection
genRejection =
  oneof
    [ RejectClass <$> elements [minBound .. maxBound]
    , pure DuplicateRule
    , pure DuplicateArgument
    , pure IncompleteArgument
    , pure MissingConflict
    ]

genVerdict :: Gen Verdict
genVerdict = do
  replayId <- genReplayId
  oneof
    [ do
        n <- choose (0, 5)
        lbls <- zip [0 ..] <$> vectorOf n genLabel
        edges <-
          if n == 0
            then pure []
            else
              listOf
                ((,) <$> choose (0, n - 1) <*> choose (0, n - 1))
        -- Some queries are @evidence-blocked@ (spec §4.3, issue #76), so the
        -- round-trip covers the conditional section. Blockedness lives inside
        -- the status, so the generator cannot construct an inconsistent
        -- statuses/blocked pairing even by accident.
        statuses <- listOf ((,) <$> genProp <*> genPublicStatus)
        pure (Verdict replayId (Accept lbls edges statuses))
    , Verdict replayId . Reject <$> genRejection
    ]

-- ---------------------------------------------------------------------------
-- Text-codec golden vectors (hand-verified)
-- ---------------------------------------------------------------------------

-- | (input text, parsed value, canonical reprint). The reprint is the exact
-- byte string both drivers must emit for the value.
textGoldens :: [(String, SExpr, String)]
textGoldens =
  [ ("a", SAtom "a", "a")
  , ("()", SList [], "()")
  , ("(a b (c))", SList [SAtom "a", SAtom "b", SList [SAtom "c"]], "(a b (c))")
  , -- every bare-set punctuation character stays bare
    ( barePunct
    , SAtom barePunct
    , barePunct
    )
  , -- quoting is forced exactly by space, delimiters, non-ASCII, and emptiness
    ("\"sp ace\"", SAtom "sp ace", "\"sp ace\"")
  , ("\"\"", SAtom "", "\"\"")
  , ("\"uniπ雪\"", SAtom "uniπ雪", "\"uniπ雪\"")
  , ("\"(paren)\"", SAtom "(paren)", "\"(paren)\"")
  , ("\"semi;colon\"", SAtom "semi;colon", "\"semi;colon\"")
  , -- the three escapes, round-tripping exactly
    ("\"quote\\\"x\"", SAtom "quote\"x", "\"quote\\\"x\"")
  , ("\"bs\\\\x\"", SAtom "bs\\x", "\"bs\\\\x\"")
  , ("\"nl\\nx\"", SAtom "nl\nx", "\"nl\\nx\"")
  , -- comments and layout are skipped on parse, canonical on print
    ( "; leading comment\n  (a ; inner\n b)\n; trailing"
    , SList [SAtom "a", SAtom "b"]
    , "(a b)"
    )
  , ("  spaced  ", SAtom "spaced", "spaced")
  ]
  where
    barePunct = "!#$%&'*+,-./:<=>?@[]^_{|}~"

prop_textGoldenVectors :: Bool
prop_textGoldenVectors =
  and
    [ parseSExpr input == Right value
        && printSExpr value == canonical
    | (input, value, canonical) <- textGoldens
    ]

prop_textMalformedRejected :: Bool
prop_textMalformedRejected =
  and
    [ isLeft (parseSExpr "(a b") -- unclosed list
    , isLeft (parseSExpr ")") -- stray close
    , isLeft (parseSExpr "\"\\q\"") -- unknown escape
    , isLeft (parseSExpr "\"abc") -- unterminated string
    , isLeft (parseSExpr "abc\\") -- trailing backslash outside a string
    , isLeft (parseSExpr "(a) (b)") -- second top-level form
    , isLeft (parseSExpr "a b") -- second bare form
    , isLeft (parseSExpr "") -- no form at all
    , isLeft (parseSExpr " ; only a comment\n") -- no form at all
    ]
  where
    isLeft (Left _) = True
    isLeft _ = False

-- | The textual round trip on arbitrary trees (quoting included).
prop_sexprTextRoundTrip :: Property
prop_sexprTextRoundTrip =
  forAll genSExpr $ \s -> parseSExpr (printSExpr s) == Right s

-- | Reprinting is idempotent: print ∘ parse ∘ print = print.
prop_printParsePrintIdempotent :: Property
prop_printParsePrintIdempotent =
  forAll genSExpr $ \s ->
    let text = printSExpr s
     in fmap printSExpr (parseSExpr text) == Right text

-- ---------------------------------------------------------------------------
-- Unit golden vectors (hand-verified)
-- ---------------------------------------------------------------------------

-- | One full unit exercising every section, as a hand-verified text/AST pair.
goldenUnitText :: String
goldenUnitText =
  "(unit \
  \(policy \
  \(rules \
  \(rule rmix (mode defeasible) (params) (premises) \
  \(conclusion (apat p)) \
  \(questions (question q1 (apat q) mandatory) \
  \(question q2 (apat q) optional)) \
  \(allow-trusted false) (certifiers)) \
  \(rule rcert (mode strict) (params) (premises (apat p)) \
  \(conclusion (apat q)) (questions) (allow-trusted false) \
  \(certifiers (certifier nd 1 sha256:theory-a)))) \
  \(contraries (contrary (apat p) (apat q))) \
  \(exceptions (exception rmix (apat q)))) \
  \(theories (theory sha256:theory-a (atom q))) \
  \(leaves (leaf l1 (atom p)) (leaf l2 (atom q))) \
  \(args (arg a0 (leaf l1)) \
  \(arg a1 (inst rcert (subst) (premises (leaf l1)) (discharges) (holes) \
  \(assurance (cert nd 1 sha256:theory-a (hyp 1)))))) \
  \(attacks (rebut a0 a1) (undermine a0 a1 (pos (prem 0)))) \
  \(queries (atom p) (atom q)))"

goldenUnit :: Unit
goldenUnit =
  Unit
    { unitRules =
        [ Rule
            { ruleId = RuleId "rmix"
            , ruleParams = []
            , ruleMode = Defeasible
            , rulePremises = []
            , ruleConclusion = AtomPat (Pred "p") []
            , ruleAllowTrusted = False
            , ruleCertifiers = []
            , ruleQuestions =
                [ Question (QuestionId "q1") (AtomPat (Pred "q") []) Mandatory
                , Question (QuestionId "q2") (AtomPat (Pred "q") []) Optional
                ]
            }
        , Rule
            { ruleId = RuleId "rcert"
            , ruleParams = []
            , ruleMode = Strict
            , rulePremises = [AtomPat (Pred "p") []]
            , ruleConclusion = AtomPat (Pred "q") []
            , ruleAllowTrusted = False
            , ruleCertifiers =
                [CertRef (BackendId "nd") 1 (TheoryDigest "sha256:theory-a")]
            , ruleQuestions = []
            }
        ]
    , unitContraries =
        [Contrary (AtomPat (Pred "p") []) (AtomPat (Pred "q") [])]
    , unitExceptions =
        [Exception (RuleId "rmix") (AtomPat (Pred "q") [])]
    , unitTheories =
        [(TheoryDigest "sha256:theory-a", [Prop (Pred "q") []])]
    , unitLeaves =
        [ (LeafId "l1", Prop (Pred "p") [])
        , (LeafId "l2", Prop (Pred "q") [])
        ]
    , unitArgs =
        [ (ArgId "a0", SLeaf (LeafId "l1"))
        ,
          ( ArgId "a1"
          , SRule
              (RuleId "rcert")
              []
              [SLeaf (LeafId "l1")]
              []
              []
              ( AssuranceCert
                  ( Cert
                      (BackendId "nd")
                      1
                      (TheoryDigest "sha256:theory-a")
                      (SList [SAtom "hyp", SAtom "1"])
                  )
              )
          )
        ]
    , unitAttacks =
        [ Rebut (ArgId "a0") (ArgId "a1")
        , Undermine (ArgId "a0") (ArgId "a1") [StepPremise 0]
        ]
    , unitQueries = [Prop (Pred "p") [], Prop (Pred "q") []]
    , unitGroups = []
    , unitGroupMode = QuarantineOnConflict
    }

goldenReplayText :: String
goldenReplayText =
  "(replay-id (core lara-core@0.1) (policy empirical-v1) "
    ++ "(backends (backend nd 1)) "
    ++ "(theories sha256:theory-a) "
    ++ "(artifact sha256:artifact-0))"

goldenReplayId :: ReplayId
goldenReplayId =
  either (error . replayErrorMessage) id $
    mkReplayId
      LaraCoreV01
      (PolicyId "empirical-v1")
      [(BackendId "nd", "1")]
      [TheoryDigest "sha256:theory-a"]
      (Digest "sha256:artifact-0")

goldenCheckInputText :: String
goldenCheckInputText =
  "(check-input " ++ goldenReplayText ++ " " ++ goldenUnitText ++ ")"

goldenCheckInput :: CheckInput
goldenCheckInput =
  either (error . replayErrorMessage) id (mkCheckInput goldenReplayId goldenUnit)

goldenAcceptText :: String
goldenAcceptText =
  "(verdict " ++ goldenReplayText
    ++ " accept (labels (0 in)) (edges) "
    ++ "(statuses (status (atom p) justified)))"

goldenRejectText :: String
goldenRejectText =
  "(verdict " ++ goldenReplayText ++ " reject R13)"

prop_replayEnvelopeGoldenVectors :: Bool
prop_replayEnvelopeGoldenVectors =
  and
    [ printSExpr (encodeReplayId goldenReplayId) == goldenReplayText
    , decodeText decodeReplayId goldenReplayText == Right goldenReplayId
    , printSExpr (encodeCheckInput goldenCheckInput) == goldenCheckInputText
    , decodeText decodeCheckInput goldenCheckInputText == Right goldenCheckInput
    , decodeCheckInputFile goldenCheckInputText == Right goldenCheckInput
    , printSExpr (encodeVerdict acceptVerdict) == goldenAcceptText
    , decodeText decodeVerdict goldenAcceptText == Right acceptVerdict
    , printSExpr (encodeVerdict rejectVerdict) == goldenRejectText
    , decodeText decodeVerdict goldenRejectText == Right rejectVerdict
    ]
  where
    acceptVerdict =
      Verdict
        goldenReplayId
        (Accept [(0, LIn)] [] [(Prop (Pred "p") [], Published Justified)])
    rejectVerdict = Verdict goldenReplayId (Reject (RejectClass R13))

prop_replayEnvelopeMalformedMatrix :: Bool
prop_replayEnvelopeMalformedMatrix =
  all (isLeft . decodeText decodeReplayId) malformedReplay
    && all (isLeft . decodeText decodeCheckInput) malformedInput
    && isLeft (decodeCheckInputFile "(unit)")
    && isLeft (decodeText decodeVerdict "(verdict reject R1)")
  where
    malformedReplay =
      [ "(replay-id (core lara-core@0.1) (policy empirical-v1) (backends) (theories))"
      , "(replay-id (core lara-core@0.1) (policy empirical-v1) (backends) (theories) (artifact sha256:a) extra)"
      , "(replay-id (core) (policy empirical-v1) (backends) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.1 extra) (policy empirical-v1) (backends) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.1) (policy) (backends) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.1) (policy empirical-v1 extra) (backends) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.1) (policy empirical-v1) (backends (backend nd)) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.1) (policy empirical-v1) (backends (backend nd 1 extra)) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.1) (policy empirical-v1) (backends) (theories (x)) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.1) (policy empirical-v1) (backends) (theories) (artifact))"
      , "(replay-id (core lara-core@0.1) (policy empirical-v1) (backends) (theories) (artifact sha256:a extra))"
      , "(replay-id (policy empirical-v1) (core lara-core@0.1) (backends) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.2) (policy empirical-v1) (backends) (theories) (artifact sha256:a))"
      , "(replay-id (core (lara-core@0.1)) (policy empirical-v1) (backends) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.1) (policy (empirical-v1)) (backends) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.1) (policy empirical-v1) (backends (backend (nd) 1)) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.1) (policy empirical-v1) (backends (backend nd (1))) (theories) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.1) (policy empirical-v1) (backends) (theories (sha256:a)) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.1) (policy empirical-v1) (backends) (theories) (artifact (sha256:a)))"
      , "(replay-id (core lara-core@0.1) (policy empirical-v1) (backends) (theories sha256:z sha256:a) (artifact sha256:a))"
      , "(replay-id (core lara-core@0.1) (policy empirical-v1) (backends) (theories sha256:a sha256:a) (artifact sha256:a))"
      ]
    malformedInput =
      [ "(check-input " ++ goldenReplayText ++ ")"
      , "(check-input " ++ goldenReplayText ++ " " ++ goldenUnitText ++ " extra)"
      , "(check-input "
          ++ goldenReplayText
          ++ " (unit (theories (theory sha256:theory-a) (theory sha256:theory-a))))"
      , "(check-input "
          ++ goldenReplayText
          ++ " (unit (theories (theory sha256:other))))"
      ]
    isLeft (Left _) = True
    isLeft _ = False

decodeText :: (SExpr -> Either WireError a) -> String -> Either WireError a
decodeText decoder text =
  case parseSExpr text of
    Left err -> Left (WireError "text" (show err))
    Right value -> decoder value

prop_unitGoldenVector :: Bool
prop_unitGoldenVector =
  decodeText decodeUnit goldenUnitText == Right goldenUnit
    && printSExpr (encodeUnit goldenUnit) == goldenUnitText
    && decodeText decodeUnit (printSExpr (encodeUnit goldenUnit)) == Right goldenUnit

-- | The same unit decodes identically with noisy layout and comments, and
-- with empty sections spelled out or omitted.
prop_unitGoldenLayoutVariants :: Bool
prop_unitGoldenLayoutVariants =
  decodeText decodeUnit commented == Right goldenUnit
    && decodeText decodeUnit minimal == Right minimalUnit
    && decodeText decodeUnit spelled == Right minimalUnit
  where
    commented = "; header\n" ++ goldenUnitText ++ "\n; footer\n"
    minimal = "(unit)"
    spelled =
      "(unit (policy (rules) (contraries) (exceptions)) (theories) \
      \(leaves) (args) (attacks) (queries))"
    minimalUnit = Unit [] [] [] [] [] [] [] [] [] QuarantineOnConflict

-- | The unit round trip: decode ∘ encode = Right id, through the text layer.
prop_unitRoundTrip :: Property
prop_unitRoundTrip =
  forAll genUnit $ \u ->
    decodeUnit (encodeUnit u) == Right u
      && decodeText decodeUnit (printSExpr (encodeUnit u)) == Right u


-- | The checker-input round trip over varied replay identities (C10):
-- @decode ∘ encode = Right id@ at both the tree and the text layer, with
-- 0-3 canonical theory digests (occasionally non-ASCII, exercising the
-- quoted-atom path) and a varied backend selection in the replay-id.
prop_checkInputRoundTrip :: Property
prop_checkInputRoundTrip =
  forAll genCheckInput $ \input ->
    let encoded = encodeCheckInput input
     in decodeCheckInput encoded == Right input
          && decodeCheckInputFile (printSExpr encoded) == Right input
-- | The wire tag table is self-consistent.
prop_tagRoundTrip :: Property
prop_tagRoundTrip =
  forAll (elements [minBound .. maxBound]) $ \t ->
    parseTag (tagToString t) == Just t

-- ---------------------------------------------------------------------------
-- Verdict golden vectors (hand-verified)
-- ---------------------------------------------------------------------------

prop_verdictGoldenVectors :: Bool
prop_verdictGoldenVectors =
  and
    [ printSExpr (encodeVerdict acceptV) == acceptText
    , decodeVerdict (encodeVerdict acceptV) == Right acceptV
    , parseSExpr acceptText == Right (encodeVerdict acceptV)
    , printSExpr (encodeVerdict rejectR5) == rejectText (RejectClass R5)
    , decodeVerdict (encodeVerdict rejectR5) == Right rejectR5
    , printSExpr (encodeVerdict rejectDup) == rejectText DuplicateRule
    , decodeVerdict (encodeVerdict rejectDup) == Right rejectDup
    , printSExpr (encodeVerdict rejectIncomplete)
        == rejectText IncompleteArgument
    , decodeVerdict (encodeVerdict rejectIncomplete) == Right rejectIncomplete
    , printSExpr (encodeVerdict rejectMissing)
        == rejectText MissingConflict
    , decodeVerdict (encodeVerdict rejectMissing) == Right rejectMissing
    , printSExpr (encodeVerdict blockedV) == blockedText
    , decodeVerdict (encodeVerdict blockedV) == Right blockedV
    , parseSExpr blockedText == Right (encodeVerdict blockedV)
    , printSExpr (encodeVerdict twoBlockedV) == twoBlockedText
    , decodeVerdict (encodeVerdict twoBlockedV) == Right twoBlockedV
    , parseSExpr twoBlockedText == Right (encodeVerdict twoBlockedV)
    ]
  where
    acceptV =
      Verdict goldenReplayId $
        Accept
          [(0, LIn), (1, LOut), (2, LUndec)]
          [(0, 1), (0, 2)]
          [ (Prop (Pred "p") [], Published Justified)
          , (Prop (Pred "q") [TNum "2"], Published Defeated)
          ]
    -- Spec §4.3 / issue #76: @p@'s support could have been affected by
    -- quarantine, so its public status is @evidence-blocked@ and the four-state
    -- label it would have had moves to the @conditional@ section. @q@ is out of
    -- reach of the edit and keeps its ordinary status.
    blockedV =
      Verdict goldenReplayId $
        Accept
          [(0, LIn), (1, LOut), (2, LUndec)]
          [(0, 1), (0, 2)]
          [ (Prop (Pred "p") [], EvidenceBlocked Justified)
          , (Prop (Pred "q") [TNum "2"], Published Defeated)
          ]
    blockedText =
      "(verdict " ++ goldenReplayText
        ++ " accept (labels (0 in) (1 out) (2 undec)) "
        ++ "(edges (0 1) (0 2)) "
        ++ "(statuses (status (atom p) evidence-blocked) "
        ++ "(status (atom q (num 2)) defeated)) "
        ++ "(conditional (status (atom p) justified)))"
    -- Two blocked queries pin the positional invariant: the conditional
    -- projection is in query order, including when an ordinary status sits
    -- between the blocked entries.
    twoBlockedV =
      Verdict goldenReplayId $
        Accept
          [(0, LIn), (1, LOut), (2, LUndec)]
          [(0, 1), (0, 2)]
          [ (Prop (Pred "p") [], EvidenceBlocked Justified)
          , (Prop (Pred "q") [TNum "2"], Published Defeated)
          , (Prop (Pred "r") [], EvidenceBlocked Contested)
          ]
    twoBlockedText =
      "(verdict " ++ goldenReplayText
        ++ " accept (labels (0 in) (1 out) (2 undec)) "
        ++ "(edges (0 1) (0 2)) "
        ++ "(statuses (status (atom p) evidence-blocked) "
        ++ "(status (atom q (num 2)) defeated) "
        ++ "(status (atom r) evidence-blocked)) "
        ++ "(conditional (status (atom p) justified) "
        ++ "(status (atom r) contested)))"
    acceptText =
      "(verdict " ++ goldenReplayText
        ++ " accept (labels (0 in) (1 out) (2 undec)) "
        ++ "(edges (0 1) (0 2)) "
        ++ "(statuses (status (atom p) justified) "
        ++ "(status (atom q (num 2)) defeated)))"
    rejectText rejection =
      "(verdict " ++ goldenReplayText ++ " reject " ++ rejectionText rejection ++ ")"
    rejectionText rejection = case rejection of
      RejectClass R5 -> "R5"
      DuplicateRule -> "duplicate-rule"
      IncompleteArgument -> "incomplete-argument"
      MissingConflict -> "missing-conflict"
      _ -> error "unexpected rejection fixture"
    rejectR5 = Verdict goldenReplayId (Reject (RejectClass R5))
    rejectDup = Verdict goldenReplayId (Reject DuplicateRule)
    rejectIncomplete = Verdict goldenReplayId (Reject IncompleteArgument)
    rejectMissing = Verdict goldenReplayId (Reject MissingConflict)

prop_verdictRoundTrip :: Property
prop_verdictRoundTrip =
  forAll genVerdict $ \v ->
    decodeVerdict (encodeVerdict v) == Right v
      && fmap printSExpr (parseSExpr (printSExpr (encodeVerdict v)))
        == Right (printSExpr (encodeVerdict v))

-- ---------------------------------------------------------------------------
-- Malformed-input rejection matrix (R14)
-- ---------------------------------------------------------------------------

-- | Grammar-level rejections: one field short / one field long per construct,
-- unknown tags, bad naturals, and the two wire-well-formedness invariants.
prop_unitMalformedMatrix :: Bool
prop_unitMalformedMatrix = all isLeft (map decodeUnit malformed)
  where
    isLeft (Left _) = True
    isLeft _ = False
    malformed =
      -- top-level shape and sections
      [ SAtom "unit" -- not a list
      , SList [SAtom "bogus"] -- unknown head tag
      , SList [SAtom "unit", SList [SAtom "bogus"]] -- unknown section
      , SList [SAtom "unit", leavesSec, leavesSec] -- duplicate section
      , SList [SAtom "unit", leavesSec, policySec] -- out-of-order section
      , SList [SAtom "unit", SList [SAtom "policy", rulesSec]] -- policy short
      , SList
          [ SAtom "unit"
          , SList [SAtom "policy", rulesSec, contrariesSec, exceptionsSec, SList []]
          ] -- policy long
      , SList [SAtom "unit", SList [SAtom "policy", SList [SAtom "bogus"], contrariesSec, exceptionsSec]] -- policy subsection tag
      -- rules
      , SList [SAtom "unit", policyWith (SList (SAtom "rule" : take 7 ruleBody))] -- rule short
      , SList [SAtom "unit", policyWith (SList (SAtom "rule" : ruleBody ++ [SAtom "extra"]))] -- rule long
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", SList [SAtom "mode", SAtom "bogus"], paramsSec, premisesSec, conclusionSec, questionsSec, allowTrustedSec, certifiersSec])] -- bad mode
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, premisesSec, conclusionSec, questionsSec, SList [SAtom "allow-trusted", SAtom "bogus"], certifiersSec])] -- bad bool
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, premisesSec, conclusionSec, SList [SAtom "questions", SList [SAtom "question", SAtom "q", apatP, SAtom "bogus"]], allowTrustedSec, certifiersSec])] -- bad necessity
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, premisesSec, conclusionSec, SList [SAtom "questions", SList [SAtom "question", SAtom "q", apatP]], allowTrustedSec, certifiersSec])] -- question short
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, premisesSec, conclusionSec, SList [SAtom "questions", SList [SAtom "question", SAtom "q", apatP, SAtom "mandatory", SAtom "x"]], allowTrustedSec, certifiersSec])] -- question long
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, premisesSec, conclusionSec, questionsSec, allowTrustedSec, SList [SAtom "certifiers", SList [SAtom "certifier", SAtom "nd", SAtom "01", SAtom "h"]]])] -- certifier bad nat
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, premisesSec, conclusionSec, questionsSec, allowTrustedSec, SList [SAtom "certifiers", SList [SAtom "certifier", SAtom "nd", SAtom "1"]]])] -- certifier short
      -- contraries / exceptions
      , SList [SAtom "unit", policyParts (SList [SAtom "contraries", SList [SAtom "contrary", apatP]]) exceptionsSec] -- contrary short
      , SList [SAtom "unit", policyParts (SList [SAtom "contraries", SList [SAtom "contrary", apatP, apatP, apatP]]) exceptionsSec] -- contrary long
      , SList [SAtom "unit", policyParts contrariesSec (SList [SAtom "exceptions", SList [SAtom "exception", SAtom "r"]])] -- exception short
      , SList [SAtom "unit", policyParts contrariesSec (SList [SAtom "exceptions", SList [SAtom "bogus", SAtom "r", apatP]])] -- exception tag
      -- atoms, patterns, terms
      , SList [SAtom "unit", SList [SAtom "queries", SList [SAtom "atom"]]] -- atom without head
      , SList [SAtom "unit", SList [SAtom "queries", SList [SAtom "atom", SAtom "p", SAtom "notalist"]]] -- term not a list
      , SList [SAtom "unit", SList [SAtom "queries", SList [SAtom "atom", SAtom "p", SList [SAtom "num", SAtom "1", SAtom "2"]]]] -- num long
      , SList [SAtom "unit", SList [SAtom "queries", SList [SAtom "atom", SAtom "p", SList [SAtom "con"]]]] -- con without head
      , SList [SAtom "unit", SList [SAtom "queries", SList [SAtom "atom", SAtom "p", SList [SAtom "bogus", SAtom "1"]]]] -- term unknown tag
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, SList [SAtom "premises", SList [SAtom "apat"]], conclusionSec, questionsSec, allowTrustedSec, certifiersSec])] -- apat without head
      , SList [SAtom "unit", policyWith (SList [SAtom "rule", SAtom "r", modeSec, paramsSec, SList [SAtom "premises", SList [SAtom "apat", SAtom "p", SList [SAtom "var", SAtom "X", SAtom "Y"]]], conclusionSec, questionsSec, allowTrustedSec, certifiersSec])] -- var long
      -- support terms
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", substSec, premisesSec, dischargesSec, holesSec])] -- inst short
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", substSec, premisesSec, dischargesSec, holesSec, assuranceSec, SAtom "extra"])] -- inst long
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", SList [SAtom "subst", SList [SAtom "X"]], premisesSec, dischargesSec, holesSec, assuranceSec])] -- binding short
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", SList [SAtom "subst", SList [SAtom "X", SList [SAtom "num", SAtom "1"], SAtom "e"]], premisesSec, dischargesSec, holesSec, assuranceSec])] -- binding long
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", substSec, premisesSec, SList [SAtom "discharges", SList [SAtom "q"]], holesSec, assuranceSec])] -- discharge short
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", substSec, premisesSec, dischargesSec, SList [SAtom "holes", SList [SAtom "notatom"]], assuranceSec])] -- hole not an atom
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", substSec, premisesSec, dischargesSec, holesSec, SList [SAtom "assurance", SAtom "bogus"]])] -- assurance unknown
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", substSec, premisesSec, dischargesSec, holesSec, SList [SAtom "assurance", SList [SAtom "cert", SAtom "nd", SAtom "-1", SAtom "h", SList []]]])] -- cert bad nat
      , SList [SAtom "unit", argsWith (SList [SAtom "inst", SAtom "r", substSec, premisesSec, dischargesSec, holesSec, SList [SAtom "assurance", SList [SAtom "cert", SAtom "nd", SAtom "1", SAtom "h"]]])] -- cert short
      , SList [SAtom "unit", argsWith (SList [SAtom "leaf", SAtom "l", SAtom "extra"])] -- leaf long
      , SList [SAtom "unit", argsWith (SAtom "notalist")] -- sterm not a list
      -- attacks and positions
      , SList [SAtom "unit", argsPairSec, SList [SAtom "attacks", SList [SAtom "rebut", SAtom "a0"]]] -- rebut short
      , SList [SAtom "unit", argsPairSec, SList [SAtom "attacks", SList [SAtom "rebut", SAtom "a0", SAtom "a1", SAtom "e"]]] -- rebut long
      , SList [SAtom "unit", argsPairSec, SList [SAtom "attacks", SList [SAtom "undercut", SAtom "a0", SAtom "a1"]]] -- undercut short
      , SList [SAtom "unit", argsPairSec, SList [SAtom "attacks", SList [SAtom "bogus", SAtom "a0", SAtom "a1"]]] -- attack kind
      , SList [SAtom "unit", argsPairSec, SList [SAtom "attacks", SList [SAtom "undermine", SAtom "a0", SAtom "a1", SList [SAtom "pos", SList [SAtom "prem", SAtom "01"]]]]] -- pos bad nat
      , SList [SAtom "unit", argsPairSec, SList [SAtom "attacks", SList [SAtom "undermine", SAtom "a0", SAtom "a1", SList [SAtom "pos", SList [SAtom "bogus", SAtom "0"]]]]] -- pos step tag
      , SList [SAtom "unit", argsPairSec, SList [SAtom "attacks", SList [SAtom "undermine", SAtom "a0", SAtom "a1", SAtom "notalist"]]] -- pos not a list
      -- wire well-formedness (R14 invariants)
      , SList [SAtom "unit", SList [SAtom "args", argA0, argA0']] -- duplicate arg ids
      , SList [SAtom "unit", SList [SAtom "attacks", SList [SAtom "rebut", SAtom "a0", SAtom "a1"]]] -- undeclared endpoint
      -- duplicate-report groups (spec §4.3): decode shape + R14 well-formedness
      , SList [SAtom "unit", SList [SAtom "groups"]] -- groups section missing its conflict mode
      , SList [SAtom "unit", groupLeaves, SList [SAtom "groups", SAtom "bogus", groupG12]] -- unknown conflict mode
      , SList [SAtom "unit", SList [SAtom "groups", SAtom "reject", SList [SAtom "group", SAtom "g"]]] -- group bad arity (no members list)
      , SList [SAtom "unit", SList [SAtom "groups", SAtom "reject", SList [SAtom "group", SAtom "g", SAtom "notalist"]]] -- members not a list
      , SList [SAtom "unit", groupLeaves, SList [SAtom "groups", SAtom "reject", groupG12, groupG12]] -- duplicate group id
      , SList [SAtom "unit", groupLeaves, SList [SAtom "groups", SAtom "reject", SList [SAtom "group", SAtom "g", SList [SAtom "l1", SAtom "l1"]]]] -- repeated member
      , SList [SAtom "unit", groupLeaves, SList [SAtom "groups", SAtom "reject", SList [SAtom "group", SAtom "g", SList [SAtom "l1"]]]] -- fewer than two members
      , SList [SAtom "unit", groupLeaves, SList [SAtom "groups", SAtom "reject", SList [SAtom "group", SAtom "g", SList [SAtom "l1", SAtom "lX"]]]] -- dangling member (not a declared leaf)
      ]
    leavesSec = SList [SAtom "leaves", SList [SAtom "leaf", SAtom "l", apatAtomP]]
    policySec = SList [SAtom "policy", rulesSec, contrariesSec, exceptionsSec]
    rulesSec = SList [SAtom "rules"]
    contrariesSec = SList [SAtom "contraries"]
    exceptionsSec = SList [SAtom "exceptions"]
    policyWith rule = SList [SAtom "policy", SList [SAtom "rules", rule], contrariesSec, exceptionsSec]
    policyParts cs es = SList [SAtom "policy", rulesSec, cs, es]
    ruleBody =
      [ SAtom "r"
      , modeSec
      , paramsSec
      , premisesSec
      , conclusionSec
      , questionsSec
      , allowTrustedSec
      , certifiersSec
      ]
    modeSec = SList [SAtom "mode", SAtom "defeasible"]
    paramsSec = SList [SAtom "params"]
    premisesSec = SList [SAtom "premises"]
    conclusionSec = SList [SAtom "conclusion", apatP]
    questionsSec = SList [SAtom "questions"]
    allowTrustedSec = SList [SAtom "allow-trusted", SAtom "false"]
    certifiersSec = SList [SAtom "certifiers"]
    apatP = SList [SAtom "apat", SAtom "p"]
    apatAtomP = SList [SAtom "atom", SAtom "p"]
    substSec = SList [SAtom "subst"]
    dischargesSec = SList [SAtom "discharges"]
    holesSec = SList [SAtom "holes"]
    assuranceSec = SList [SAtom "assurance", SAtom "none"]
    argsWith sterm = SList [SAtom "args", SList [SAtom "arg", SAtom "a0", sterm]]
    argA0 = SList [SAtom "arg", SAtom "a0", SList [SAtom "leaf", SAtom "l"]]
    argA0' = SList [SAtom "arg", SAtom "a0", SList [SAtom "leaf", SAtom "m"]]
    argsPairSec =
      SList
        [ SAtom "args"
        , SList [SAtom "arg", SAtom "a0", SList [SAtom "leaf", SAtom "l"]]
        , SList [SAtom "arg", SAtom "a1", SList [SAtom "leaf", SAtom "l"]]
        ]
    groupLeaves =
      SList
        [ SAtom "leaves"
        , SList [SAtom "leaf", SAtom "l1", apatAtomP]
        , SList [SAtom "leaf", SAtom "l2", apatAtomP]
        ]
    groupG12 = SList [SAtom "group", SAtom "g", SList [SAtom "l1", SAtom "l2"]]

-- | Malformed verdicts are rejected at the decode boundary.
prop_verdictMalformedMatrix :: Bool
prop_verdictMalformedMatrix = all isLeft (map decodeVerdict malformed)
  where
    isLeft (Left _) = True
    isLeft _ = False
    malformed =
      [ SAtom "verdict" -- not a list
      , SList [SAtom "bogus", SAtom "reject", SAtom "R5"] -- head tag
      , SList [SAtom "verdict", SAtom "bogus", SAtom "R5"] -- accept|reject tag
      , SList [SAtom "verdict", SAtom "reject"] -- reject short
      , SList [SAtom "verdict", SAtom "reject", SAtom "R5", SAtom "x"] -- reject long
      , SList [SAtom "verdict", SAtom "reject", SAtom "R2"] -- class outside the core
      , SList [SAtom "verdict", SAtom "reject", SAtom "bogus"] -- unknown rejection
      , SList [SAtom "verdict", SAtom "reject", SList []] -- rejection not an atom
      , SList [SAtom "verdict", SAtom "accept", labelsSec, edgesSec] -- accept short
      , SList [SAtom "verdict", SAtom "accept", labelsSec, edgesSec, statusesSec, SList []] -- accept long
      , SList [SAtom "verdict", SAtom "accept", SList [SAtom "labels", SList [SAtom "0", SAtom "bogus"]], edgesSec, statusesSec] -- bad label
      , SList [SAtom "verdict", SAtom "accept", SList [SAtom "labels", SList [SAtom "01", SAtom "in"]], edgesSec, statusesSec] -- label bad nat
      , SList [SAtom "verdict", SAtom "accept", SList [SAtom "labels", SList [SAtom "0"]], edgesSec, statusesSec] -- label short
      , SList [SAtom "verdict", SAtom "accept", labelsSec, SList [SAtom "edges", SList [SAtom "0"]], statusesSec] -- edge short
      , SList [SAtom "verdict", SAtom "accept", labelsSec, edgesSec, SList [SAtom "statuses", SList [SAtom "status", apatAtomP, SAtom "bogus"]]] -- bad status
      , SList [SAtom "verdict", SAtom "accept", labelsSec, edgesSec, SList [SAtom "statuses", SList [SAtom "status", apatAtomP]]] -- status short
      , SList [SAtom "verdict", SAtom "accept", labelsSec, edgesSec, SList [SAtom "statuses", SList [SAtom "bogus", apatAtomP, SAtom "gap"]]] -- status entry tag
      -- The rows above omit the replay-id, so they die on the outer shape and
      -- never reach the section decoders. These carry a well-formed replay-id so
      -- the section checks are the thing under test — including the four
      -- rejection paths the conditional section adds (spec §4.3, issue #76).
      , accept [labelsSec, edgesSec] -- accept short
      , accept [labelsSec, edgesSec, statusesSec, conditionalSec, conditionalSec] -- accept long
      , accept [labelsSec, edgesSec, blockedStatusesSec] -- evidence-blocked, no conditional section
      , accept [labelsSec, edgesSec, statusesSec, conditionalSec] -- conditional entry, nothing blocked
      , accept [labelsSec, edgesSec, blockedStatusesSec, SList [SAtom "conditional"]] -- present but empty
      , accept [labelsSec, edgesSec, blockedStatusesSec, otherConditionalSec] -- conditional names another query
      , accept [labelsSec, edgesSec, blockedStatusesSec, SList [SAtom "bogus", statusEntry "p" "gap"]] -- section tag
      , accept [labelsSec, edgesSec, blockedStatusesSec, SList [SAtom "conditional", SList [SAtom "status", apatAtomP, SAtom "evidence-blocked"]]] -- conditional label not four-state
      -- With multiple blocked queries the conditional projection is positional,
      -- not a lookup table: reversal, truncation, and a duplicate\/extra suffix
      -- are all non-canonical.
      , accept [labelsSec, edgesSec, twoBlockedStatusesSec, SList [SAtom "conditional", statusEntry "q" "defeated", statusEntry "p" "gap"]]
      , accept [labelsSec, edgesSec, twoBlockedStatusesSec, SList [SAtom "conditional", statusEntry "p" "gap"]]
      , accept [labelsSec, edgesSec, twoBlockedStatusesSec, SList [SAtom "conditional", statusEntry "p" "gap", statusEntry "q" "defeated", statusEntry "q" "defeated"]]
      ]
    accept sections =
      SList ([SAtom "verdict", encodeReplayId goldenReplayId, SAtom "accept"] ++ sections)
    labelsSec = SList [SAtom "labels"]
    edgesSec = SList [SAtom "edges"]
    statusesSec = SList [SAtom "statuses", statusEntry "p" "gap"]
    blockedStatusesSec = SList [SAtom "statuses", statusEntry "p" "evidence-blocked"]
    twoBlockedStatusesSec =
      SList
        [ SAtom "statuses"
        , statusEntry "p" "evidence-blocked"
        , statusEntry "q" "evidence-blocked"
        ]
    conditionalSec = SList [SAtom "conditional", statusEntry "p" "gap"]
    otherConditionalSec = SList [SAtom "conditional", statusEntry "q" "gap"]
    statusEntry name value =
      SList [SAtom "status", SList [SAtom "atom", SAtom name], SAtom value]
    apatAtomP = SList [SAtom "atom", SAtom "p"]

-- | Whole-file text and low-level Unit grammar rejections.
prop_fileMalformedRejected :: Bool
prop_fileMalformedRejected =
  and
    [ isLeft (decodeText decodeUnit "(unit") -- truncated text
    , isLeft (decodeText decodeUnit "(unit) (unit)") -- two units
    , isLeft (decodeText decodeUnit "bogus") -- not a unit
    ]
  where
    isLeft (Left _) = True
    isLeft _ = False

-- | Codec errors are located: the failure carries a context path.
prop_errorIsLocated :: Bool
prop_errorIsLocated =
  case decodeText decodeUnit "(unit (leaves (leaf l1 (atom))))" of
    Left (WireError ctx _) -> "leaf" `isPrefixOf` ctx || ctx == "atom"
    Right _ -> False

-- ---------------------------------------------------------------------------
-- Cross-checked Lean-driver goldens
-- ---------------------------------------------------------------------------

-- | Fixture: the self-conflict unit of @lean/Lara/Examples/GroundedConsistency@
-- ('coveredSelfEdgeUnit') over the empty policy — one self-undermining leaf
-- argument. This assertion pins the intended Lean wire output: the bytes the
-- Lean driver must print for this fixture, here checked to decode to exactly
-- this verdict and to be reproduced by 'encodeVerdict'. The differential
-- harness confirms the actual Lean output.
prop_leanDriverAcceptGolden :: Bool
prop_leanDriverAcceptGolden =
  decodeVerdict leanBytes == Right expected
    && printSExpr (encodeVerdict expected) == leanText
  where
    leanText =
      "(verdict " ++ goldenReplayText
        ++ " accept (labels (0 undec)) (edges (0 0)) "
        ++ "(statuses (status (atom p) contested)))"
    Right leanBytes = parseSExpr leanText
    expected =
      Verdict
        goldenReplayId
        (Accept [(0, LUndec)] [(0, 0)] [(Prop (Pred "p") [], Published Contested)])

-- | Fixture: the missing-self-edge unit of the same file
-- ('missingSelfEdgeUnit') — no attack covers the declared contrary. Pins the
-- missing-conflict rejection bytes the Lean driver must print.
prop_leanDriverRejectGolden :: Bool
prop_leanDriverRejectGolden =
  decodeVerdict leanBytes == Right expected
    && printSExpr (encodeVerdict expected) == leanText
  where
    leanText = "(verdict " ++ goldenReplayText ++ " reject missing-conflict)"
    Right leanBytes = parseSExpr leanText
    expected = Verdict goldenReplayId (Reject MissingConflict)

-- ---------------------------------------------------------------------------
-- Exported runner
-- ---------------------------------------------------------------------------

wireSpecProps :: [(String, IO Result)]
wireSpecProps =
  [ ("wire text golden vectors", quickCheckResult prop_textGoldenVectors)
  , ("wire text malformed rejected", quickCheckResult prop_textMalformedRejected)
  , ("wire S-expr text round-trip", quickCheckResult prop_sexprTextRoundTrip)
  , ("wire print∘parse∘print idempotent", quickCheckResult prop_printParsePrintIdempotent)
  , ("wire unit golden vector", quickCheckResult prop_unitGoldenVector)
  , ("wire unit golden layout variants", quickCheckResult prop_unitGoldenLayoutVariants)
  , ("wire unit round-trip", quickCheckResult prop_unitRoundTrip)
  , ("wire check-input round-trip", quickCheckResult prop_checkInputRoundTrip)
  , ("wire tag round-trip", quickCheckResult prop_tagRoundTrip)
  , ("wire replay/envelope golden vectors", quickCheckResult prop_replayEnvelopeGoldenVectors)
  , ("wire replay/envelope malformed matrix", quickCheckResult prop_replayEnvelopeMalformedMatrix)
  , ("wire verdict golden vectors", quickCheckResult prop_verdictGoldenVectors)
  , ("wire verdict round-trip", quickCheckResult prop_verdictRoundTrip)
  , ("wire unit malformed matrix", quickCheckResult prop_unitMalformedMatrix)
  , ("wire verdict malformed matrix", quickCheckResult prop_verdictMalformedMatrix)
  , ("wire file malformed rejected", quickCheckResult prop_fileMalformedRejected)
  , ("wire codec error is located", quickCheckResult prop_errorIsLocated)
  , ("wire Lean-driver accept golden", quickCheckResult prop_leanDriverAcceptGolden)
  , ("wire Lean-driver reject golden", quickCheckResult prop_leanDriverRejectGolden)
  ]
