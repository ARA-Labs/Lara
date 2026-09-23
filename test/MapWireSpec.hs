-- | Ground-truth tests for the multi-artifact map's composition boundary
-- ("Lara.Map.Types") and its codecs ("Lara.Map.Wire").
--
-- Four layers, mirroring "WireSpec"'s shape:
--
--   * __hand-verified golden vectors__ — exact text ↔ value pairs for a minimal
--     path-only manifest, a full manifest with an alignment and a map question,
--     and a composite verdict with a merged argument and member-qualified
--     statuses;
--   * __round-trip properties__ — @decode ∘ encode = Right id@ on manifests and
--     verdicts, and @parse ∘ print = id@ on the trees they produce, with
--     generators that respect the documented invariants (unique aliases,
--     ascending duplicate-free backends, labels covering @0..n-1@, in-range and
--     ascending edges);
--   * __malformed-input rejection matrices__ — empty members, duplicate
--     aliases, unknown tags and fields, the wrong version atom, a trailing
--     form, coordinates that cannot be well-formed, mixed selectors,
--     non-canonical backend order, and one field short and\/or one field long
--     for each of the main constructs; plus the two cross-grammar confusions (a
--     solo @(verdict …)@ is not a map verdict, and vice versa);
--   * __boundary-vocabulary facts__ — the tag table is total and
--     collision-free, alias syntax is exactly what is documented, the
--     length-framed qualified key is injective and its parser a left inverse,
--     and every error class maps to the exit code the contract promises.
--
-- The manifest fixtures deliberately carry __no checksum and no map id__: that
-- absence is part of the frozen contract (a map is rechecked from the members'
-- current bytes), so a future field would break these goldens loudly.
module MapWireSpec (mapWireSpecProps) where

import Data.Either (isLeft)
import Data.List (isInfixOf, nub, nubBy, sort)
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromMaybe, isJust, isNothing)
import Test.QuickCheck

import Lara.AST
  ( ArgId (..)
  , AuditStatus (..)
  , BackendId (..)
  , Binding (..)
  , Digest (..)
  , Label (..)
  , PolicyId (..)
  , PropId (..)
  , QuestionId (..)
  , RejectClass (..)
  , Rejection (..)
  , Status (..)
  )
import Lara.Map.Types
import Lara.Map.Wire
import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..))
import Lara.Replay (CoreVersion (..))
import Lara.Strict (SExpr)
import Lara.Wire (parseSExpr, printSExpr)

-- ---------------------------------------------------------------------------
-- Fixture helpers
-- ---------------------------------------------------------------------------

-- | A member alias that the fixture author asserts is well formed. The @error@
-- is a test-authoring bug, never a decode path.
aliasOf :: String -> MemberAlias
aliasOf name =
  fromMaybe (error ("MapWireSpec: malformed fixture alias " ++ show name)) (mkMemberAlias name)

pathOf :: String -> DeclaredPath
pathOf text =
  fromMaybe (error ("MapWireSpec: malformed fixture path " ++ show text)) (mkDeclaredPath text)

argOf :: Int -> ArgIndex
argOf n = fromMaybe (error ("MapWireSpec: negative fixture arg index " ++ show n)) (mkArgIndex n)

nodeOf :: Int -> NodeIndex
nodeOf n = fromMaybe (error ("MapWireSpec: negative fixture node index " ++ show n)) (mkNodeIndex n)

parseOrDie :: String -> SExpr
parseOrDie text = either (error . show) id (parseSExpr text)

-- ---------------------------------------------------------------------------
-- Golden vectors: manifests
-- ---------------------------------------------------------------------------

-- | Build a manifest that is meant to be valid, or fail loudly.
--
-- 'Lara.Map.Types.mkMapManifest' is the only way to originate a 'MapManifest',
-- and the fixtures below are all valid by construction — so a 'Left' here is a
-- broken fixture, not a property failure, and it should stop the suite at the
-- fixture rather than surface later as a confusing codec mismatch. Fixtures
-- that are meant to be INVALID are built by record-updating a valid one, which
-- is the same escape hatch 'Lara.Replay.CheckInput' leaves open.
validManifest
  :: PolicyId
  -> DeclaredPath
  -> [(BackendId, String)]
  -> NonEmpty MapMember
  -> [Alignment]
  -> [MapQuestion]
  -> MapManifest
validManifest policy policyPath backends members alignments questions =
  case mkMapManifest policy policyPath backends members alignments questions of
    Left err ->
      error
        ( "MapWireSpec: fixture manifest is invalid: "
            ++ mweContext err
            ++ ": "
            ++ mweMessage err
        )
    Right manifest -> manifest

-- | The smallest map anyone can write: one member, an alias and a path, and
-- nothing else. No checksum field, no generated map id.
minimalManifest :: MapManifest
minimalManifest =
  validManifest
    (PolicyId "p1")
    (pathOf "policy.lara")
    []
    (MapMember (aliasOf "paper_a") (pathOf "a/paper.lara") :| [])
    []
    []

minimalManifestText :: String
minimalManifestText =
  "(lara-map@1 (policy p1 policy.lara) (backends)"
    ++ " (members (member paper_a a/paper.lara)) (alignments) (questions))"

-- | A two-member map with a declared alignment and a map question.
fullManifest :: MapManifest
fullManifest =
  validManifest
    (PolicyId "demo-policy")
    (pathOf "policies/demo.lara")
    [(BackendId "nd", "1"), (BackendId "ra", "1")]
    ( MapMember (aliasOf "paper_a") (pathOf "a/paper.lara")
        :| [MapMember (aliasOf "paper_b") (pathOf "b/paper.lara")]
    )
    [ Alignment
        { alignLeft = MapRef (aliasOf "paper_a") (PropId "c1") CoordWhole
        , alignRight = MapRef (aliasOf "paper_b") (PropId "c7") CoordWhole
        , alignAssertion = Same
        , alignBinding = Binding "alice" "same claim" Reviewed
        }
    ]
    [ MapQuestion
        { mapQuestionId = QuestionId "q1"
        , mapQuestionRefs =
            [ MapRef (aliasOf "paper_a") (PropId "c1") (CoordArg (argOf 0))
            , MapRef (aliasOf "paper_b") (PropId "c7") (CoordArg (argOf 0))
            ]
        , mapQuestionNl = "do they agree?"
        }
    ]

fullManifestText :: String
fullManifestText =
  "(lara-map@1 (policy demo-policy policies/demo.lara)"
    ++ " (backends (backend nd 1) (backend ra 1))"
    ++ " (members (member paper_a a/paper.lara) (member paper_b b/paper.lara))"
    ++ " (alignments (alignment (ref paper_a c1 whole) (ref paper_b c7 whole) same"
    ++ " (author alice) (audit-status reviewed) (rationale \"same claim\")))"
    ++ " (questions (question q1 (refs (ref paper_a c1 (arg 0)) (ref paper_b c7 (arg 0)))"
    ++ " (nl \"do they agree?\"))))"

prop_manifestGoldenVectors :: Property
prop_manifestGoldenVectors =
  once $
    conjoin
      [ counterexample "minimal manifest bytes" $
          printSExpr (encodeMapManifest minimalManifest) === minimalManifestText
      , counterexample "minimal manifest decode" $
          decodeMapManifestText minimalManifestText === Right minimalManifest
      , counterexample "full manifest bytes" $
          printSExpr (encodeMapManifest fullManifest) === fullManifestText
      , counterexample "full manifest decode" $
          decodeMapManifestText fullManifestText === Right fullManifest
      ]

-- | A backend reference is the __wire pair__ @(backend nd 1)@ — id and version
-- as two separate atoms — never the surface spelling @nd\@1@.
--
-- This is a regression guard, not a restatement of the goldens. The surface
-- grammar's @backendRef@ ('Lara.Syntax') splits @nd\@1@ on the @\@@, so a
-- 'BackendId' structurally never contains one, and 'Lara.Wire.encodeReplayId'
-- emits the same two-atom pair. A manifest spelling @nd\@1@ would therefore
-- name a backend no member can ever declare, and the shared-contract
-- comparison against it could never succeed. The codec is id-agnostic, so
-- nothing here would fail on its own — hence this check.
prop_backendSpelling :: Property
prop_backendSpelling =
  once $
    conjoin
      [ counterexample "no fixture BackendId contains the surface separator" $
          property (not (any (\(BackendId b, _) -> '@' `elem` b) fixtureBackends))
      , counterexample "the manifest encodes the two-atom pair" $
          property ("(backends (backend nd 1) (backend ra 1))" `isInfixOf` fullManifestText)
      , counterexample "the verdict encodes the two-atom pair" $
          property ("(backends (backend nd 1))" `isInfixOf` fullVerdictText)
      ]
  where
    fixtureBackends = mapBackends fullManifest ++ mvBackends fullVerdict

-- ---------------------------------------------------------------------------
-- Golden vectors: composite verdicts
-- ---------------------------------------------------------------------------

-- | A verdict over the two-member map: @paper_a@'s @a1@ and @paper_b@'s @b1@
-- are structurally identical and merged onto linked index 0, so both handles
-- are retained; the statuses are reported per member and per claim.
fullVerdict :: MapVerdict
fullVerdict =
  MapVerdict
    { mvScope = ScopeMap
    , mvSchema = MapVerdictSchemaV1
    , mvCore = LaraCoreV02
    , mvPolicy = PolicyId "demo-policy"
    , mvBackends = [(BackendId "nd", "1")]
    , mvMembers =
        MemberRecord (aliasOf "paper_a") (pathOf "a/paper.lara") (Digest "sha-a")
          :| [MemberRecord (aliasOf "paper_b") (pathOf "b/paper.lara") (Digest "sha-b")]
    , mvNodes =
        [ MapNode (aliasOf "paper_a") (ArgId "a1") (nodeOf 0)
        , MapNode (aliasOf "paper_b") (ArgId "b1") (nodeOf 0)
        , MapNode (aliasOf "paper_b") (ArgId "b2") (nodeOf 1)
        ]
    , mvLabels = [(nodeOf 0, LIn), (nodeOf 1, LOut)]
    , mvEdges = [(nodeOf 0, nodeOf 1)]
    , mvStatuses =
        [ MapStatus (aliasOf "paper_a") (PropId "c1") agreeAtom Justified
        , MapStatus (aliasOf "paper_b") (PropId "c7") agreeAtom Defeated
        ]
    }
  where
    agreeAtom = Prop (Pred "agree") [TStr "x"]

fullVerdictText :: String
fullVerdictText =
  "(map-verdict@1 (scope map) (schema lara-map-verdict@1) (core lara-core@0.2)"
    ++ " (policy demo-policy) (backends (backend nd 1))"
    ++ " (members (member paper_a a/paper.lara (artifact sha-a))"
    ++ " (member paper_b b/paper.lara (artifact sha-b)))"
    ++ " (nodes (node paper_a a1 0) (node paper_b b1 0) (node paper_b b2 1))"
    ++ " (labels (0 in) (1 out)) (edges (0 1))"
    ++ " (statuses (status paper_a c1 (atom agree (str x)) justified)"
    ++ " (status paper_b c7 (atom agree (str x)) defeated)))"

prop_verdictGoldenVector :: Property
prop_verdictGoldenVector =
  once $
    conjoin
      [ counterexample "verdict bytes" $
          printSExpr (encodeMapVerdict fullVerdict) === fullVerdictText
      , counterexample "verdict decode" $
          decodeMapVerdict (parseOrDie fullVerdictText) === Right fullVerdict
      , counterexample "member-qualified handles read back as alias::local" $
          [ qualifiedDisplay (qualifyId (mnAlias n) (let ArgId a = mnArg n in a))
          | n <- mvNodes fullVerdict
          ]
            === ["paper_a::a1", "paper_b::b1", "paper_b::b2"]
      ]

-- | A solo @lara-core\@0.2@ verdict and a composite map verdict are mutually
-- undecodable: the @scope@ marker exists exactly to make this true.
prop_scopesDoNotCross :: Property
prop_scopesDoNotCross =
  once $
    conjoin
      [ counterexample "a solo verdict is not a map verdict" $
          property (isLeft (decodeMapVerdict (parseOrDie soloVerdictText)))
      , counterexample "a map verdict is not a manifest" $
          property (isLeft (decodeMapManifestText fullVerdictText))
      , counterexample "a manifest is not a map verdict" $
          property (isLeft (decodeMapVerdict (parseOrDie minimalManifestText)))
      ]
  where
    soloVerdictText =
      "(verdict (replay-id (core lara-core@0.2) (policy demo-policy) (backends)"
        ++ " (theories) (artifact sha-a)) accept (labels (0 in)) (edges)"
        ++ " (statuses (status (atom agree (str x)) justified)))"

-- ---------------------------------------------------------------------------
-- Generators
-- ---------------------------------------------------------------------------

genAliasText :: Gen String
genAliasText = do
  n <- choose (1, 4)
  vectorOf n (elements (['a' .. 'e'] ++ ['0' .. '2'] ++ "_-"))

-- | Arbitrary atom payloads, including text that forces quoting.
genFreeText :: Gen String
genFreeText =
  oneof
    [ genAliasText
    , pure ""
    , do
        n <- choose (0, 5)
        vectorOf n (elements (['a' .. 'd'] ++ " \t\"\\\nπ雪:;()"))
    ]

genPathText :: Gen String
genPathText = do
  n <- choose (1, 6)
  oneof
    [ vectorOf n (elements (['a' .. 'e'] ++ "./_-"))
    , (\s -> s ++ " dir/x") <$> vectorOf n (elements ['a' .. 'c'])
    ]

genMembers :: Gen (NonEmpty MapMember)
genMembers = do
  n <- choose (1, 3)
  names <- nub <$> vectorOf n genAliasText
  members <- mapM (\name -> MapMember (aliasOf name) . pathOf <$> genPathText) names
  -- @nub@ over a nonempty vector is nonempty, so this cannot fire; it is here
  -- because 'NE.nonEmpty' is the only way in and a partial pattern would say
  -- less about why.
  case NE.nonEmpty members of
    Nothing -> error "MapWireSpec: genMembers produced no members"
    Just nonEmptyMembers -> pure nonEmptyMembers

-- | Duplicate-free and strictly ascending by @(id, version)@, as the grammar
-- requires: sorting and then deduplicating is exactly that normal form.
genBackends :: Gen [(BackendId, String)]
genBackends = do
  n <- choose (0, 3)
  raw <- vectorOf n ((,) . BackendId <$> genAliasText <*> (show <$> choose (1 :: Int, 3)))
  pure (nub (sort raw))

genRef :: [MemberAlias] -> Bool -> Gen MapRef
genRef aliases wholeSelector = do
  alias <- elements aliases
  claim <- PropId <$> genFreeText
  coord <-
    if wholeSelector
      then pure CoordWhole
      else CoordArg . argOf <$> choose (0, 4)
  pure (MapRef alias claim coord)

genBinding :: Gen Binding
genBinding =
  Binding
    <$> genFreeText
    <*> genFreeText
    <*> elements [Unreviewed, Reviewed, Disputed]

-- | Both coordinates of one alignment select the same kind of target; a mixed
-- pair is a decode error, so the round-trip generator must not produce one.
genAlignment :: [MemberAlias] -> Gen Alignment
genAlignment aliases = do
  wholeSelector <- arbitrary
  Alignment
    <$> genRef aliases wholeSelector
    <*> genRef aliases wholeSelector
    <*> elements [Same, Different]
    <*> genBinding

genMapQuestion :: [MemberAlias] -> Gen MapQuestion
genMapQuestion aliases = do
  n <- choose (2, 3)
  MapQuestion (QuestionId "q") <$> vectorOf n anyRef <*> genFreeText
  where
    anyRef = arbitrary >>= genRef aliases

genManifest :: Gen MapManifest
genManifest = do
  members <- genMembers
  let aliases = NE.toList (fmap memberAlias members)
  policy <- PolicyId <$> genFreeText
  policyPath <- pathOf <$> genPathText
  backends <- genBackends
  alignmentCount <- choose (0, 2)
  alignments <- vectorOf alignmentCount (genAlignment aliases)
  questionCount <- choose (0, 2)
  questions <- vectorOf questionCount (genMapQuestion aliases)
  -- Every component generator already produces the shape 'mkMapManifest'
  -- demands (aliases deduped, backends sorted and deduped, alignments with two
  -- coordinates of one kind, questions with at least two references), so a
  -- rejection here means a GENERATOR drifted away from the invariant, which is
  -- worth stopping on rather than shrinking around.
  pure (validManifest policy policyPath backends members alignments questions)

genProp :: Gen Prop
genProp = do
  n <- choose (0, 2)
  Prop . Pred <$> genFreeText <*> vectorOf n genTerm

genTerm :: Gen Term
genTerm =
  oneof
    [ TStr <$> genFreeText
    , TNum . show <$> choose (0 :: Int, 99)
    , TCon . FunSym <$> genAliasText <*> pure []
    ]

genVerdict :: Gen MapVerdict
genVerdict = do
  members <- genMembers
  records <-
    mapM
      (\member -> MemberRecord (memberAlias member) (memberPath member) . Digest <$> genFreeText)
      members
  let aliases = NE.toList (fmap mrAlias records)
  policy <- PolicyId <$> genFreeText
  backends <- genBackends
  nodeCount <- choose (0, 4)
  labels <-
    mapM
      (\index -> (,) (nodeOf index) <$> elements [LIn, LOut, LUndec])
      [0 .. nodeCount - 1]
  -- The node indices are a SURJECTION onto the labelled arguments, not
  -- independent choices: every labelled index gets at least one handle, and the
  -- extras land wherever. That mirrors what a driver can emit — a linked
  -- argument exists because some member declared its term, so an argument with
  -- no handle is unreachable — and it is what the decoder now requires. The
  -- argument ids are positional (@aN@) so that the @(alias, ArgId)@ handles are
  -- unique by construction; without that a colliding 'genAliasText' would
  -- silently drop a handle and with it the coverage the generator is asserting.
  extraCount <- choose (0, 3)
  extraIndices <-
    if nodeCount == 0 then pure [] else vectorOf extraCount (choose (0, nodeCount - 1))
  let indices = [0 .. nodeCount - 1] ++ extraIndices
  nodes <-
    mapM
      (\(position, index) -> do
          alias <- elements aliases
          pure (MapNode alias (ArgId ("a" ++ show (position :: Int))) (nodeOf index)))
      (zip [0 ..] indices)
  edges <-
    sublistOf
      [ (nodeOf source, nodeOf target)
      | source <- [0 .. nodeCount - 1]
      , target <- [0 .. nodeCount - 1]
      ]
  statusCount <- choose (0, 3)
  -- Unique @(alias, claim)@ handles, which is the invariant 'mvStatuses'
  -- documents and 'decodeStatuses' now enforces. Generating them freely made
  -- the round-trip property fail on a collision — correctly, since such a
  -- verdict no longer decodes; the generator has to produce the population the
  -- codec is defined on. @nubBy@ on the handle keeps whichever row came first,
  -- so the surviving rows still vary in atom and status.
  rawStatuses <-
    vectorOf
      statusCount
      ( MapStatus
          <$> elements aliases
          <*> (PropId <$> genFreeText)
          <*> genProp
          <*> elements [Gap, Justified, Contested, Defeated]
      )
  let statuses =
        nubBy (\a b -> (msAlias a, msClaim a) == (msAlias b, msClaim b)) rawStatuses
  pure
    MapVerdict
      { mvScope = ScopeMap
      , mvSchema = MapVerdictSchemaV1
      , mvCore = LaraCoreV02
      , mvPolicy = policy
      , mvBackends = backends
      , mvMembers = records
      , mvNodes = nodes
      , mvLabels = labels
      , mvEdges = edges
      , mvStatuses = statuses
      }

-- ---------------------------------------------------------------------------
-- Round trips and stability
-- ---------------------------------------------------------------------------

prop_manifestRoundTrip :: Property
prop_manifestRoundTrip =
  forAll genManifest $ \manifest ->
    let tree = encodeMapManifest manifest
        text = printSExpr tree
     in conjoin
          [ counterexample "decode ∘ encode" $ decodeMapManifest tree === Right manifest
          , counterexample "parse ∘ print" $ parseSExpr text === Right tree
          , counterexample "decode ∘ print" $ decodeMapManifestText text === Right manifest
          ]

prop_verdictRoundTrip :: Property
prop_verdictRoundTrip =
  forAll genVerdict $ \verdict ->
    let tree = encodeMapVerdict verdict
        text = printSExpr tree
     in conjoin
          [ counterexample "decode ∘ encode" $ decodeMapVerdict tree === Right verdict
          , counterexample "parse ∘ print" $ parseSExpr text === Right tree
          ]

-- | Encoding is a function of the value alone: equal values print equal bytes,
-- and nothing in the codec depends on how the value was built.
prop_encodingIsStable :: Property
prop_encodingIsStable =
  conjoin
    [ counterexample "equal manifests print equal bytes" $
        forAll genManifest $ \manifest ->
          printSExpr (encodeMapManifest manifest)
            === printSExpr (encodeMapManifest (rebuildManifest manifest))
    , counterexample "equal verdicts print equal bytes" $
        forAll genVerdict $ \verdict ->
          printSExpr (encodeMapVerdict verdict)
            === printSExpr (encodeMapVerdict (rebuildVerdict verdict))
    ]
  where
    -- Rebuild the member list through the smart constructors, so the compared
    -- value's aliases and paths are freshly constructed rather than shared.
    -- The other sections are carried over as-is: this exercises that encoding
    -- depends on a member's /value/ and not on the particular 'MemberAlias' or
    -- 'DeclaredPath' object it was built from, which is the part a smart
    -- constructor could plausibly get wrong. It is not a deep-copy test.
    rebuildManifest manifest =
      manifest
        { mapMembers =
            fmap
              ( \member ->
                  MapMember
                    (aliasOf (aliasText (memberAlias member)))
                    (pathOf (declaredPathText (memberPath member)))
              )
              (mapMembers manifest)
        }
    rebuildVerdict verdict =
      verdict
        { mvMembers =
            fmap
              ( \record ->
                  MemberRecord
                    (aliasOf (aliasText (mrAlias record)))
                    (pathOf (declaredPathText (mrPath record)))
                    (mrArtifact record)
              )
              (mvMembers verdict)
        }

-- | The codec carries order, it does not impose it: the driver decides the
-- canonical order of members and per-member reports, and the bytes must reflect
-- exactly that decision. So a reordered member list is different bytes, and a
-- decode returns the order it read.
prop_orderIsCarriedNotSorted :: Property
prop_orderIsCarriedNotSorted =
  once $
    conjoin
      [ counterexample "reordered members are different bytes" $
          property
            ( printSExpr (encodeMapManifest fullManifest)
                /= printSExpr (encodeMapManifest reversedMembers)
            )
      , counterexample "decode preserves member order" $
          fmap (NE.toList . fmap memberAlias . mapMembers) (decodeMapManifest (encodeMapManifest reversedMembers))
            === Right (NE.toList (fmap memberAlias (mapMembers reversedMembers)))
      , counterexample "decode preserves status order" $
          fmap (map msClaim . mvStatuses) (decodeMapVerdict (encodeMapVerdict reversedStatuses))
            === Right (map msClaim (mvStatuses reversedStatuses))
      , counterexample "reordered statuses are different bytes" $
          property
            ( printSExpr (encodeMapVerdict fullVerdict)
                /= printSExpr (encodeMapVerdict reversedStatuses)
            )
      ]
  where
    -- Record update, not 'mkMapManifest': reversing a valid member list keeps
    -- every invariant, and going through the smart constructor here would say
    -- nothing this property is about. Where a fixture must BREAK an invariant,
    -- record update is also the only door, which is the same escape hatch
    -- 'Lara.Replay.CheckInput' leaves open behind @mkCheckInput@.
    reversedMembers = fullManifest {mapMembers = NE.reverse (mapMembers fullManifest)}
    reversedStatuses = fullVerdict {mvStatuses = reverse (mvStatuses fullVerdict)}

-- ---------------------------------------------------------------------------
-- Malformed manifests
-- ---------------------------------------------------------------------------

-- | Manifest scaffolding shared by the rejection matrix and by its positive
-- controls.
--
-- Top level on purpose. The controls exist to prove that the matrix's wrappers
-- are well formed apart from the one defect each row injects; if the two had a
-- copy each, a drifting copy would leave the controls silently controlling
-- nothing — the exact failure they were written to catch.
manifestWrap :: String -> String
manifestWrap body = "(lara-map@1 " ++ body ++ ")"

-- | A manifest whose @members@ section is the given text.
withMembers :: String -> String
withMembers body = manifestWrap ("(policy p q) (backends) (members " ++ body ++ ") (alignments) (questions)")

-- | A manifest whose @backends@ section is the given text.
withBackends :: String -> String
withBackends body = manifestWrap ("(policy p q) (backends " ++ body ++ ") (members (member a x)) (alignments) (questions)")

-- | A manifest whose @alignments@ section is the given text.
withAlignments :: String -> String
withAlignments body = manifestWrap ("(policy p q) (backends) (members (member a x)) (alignments " ++ body ++ ") (questions)")

-- | A manifest whose @questions@ section is the given text.
withQuestions :: String -> String
withQuestions body = manifestWrap ("(policy p q) (backends) (members (member a x)) (alignments) (questions " ++ body ++ ")")

-- | A reference to member @a@'s claim @c@ at the given coordinate.
refAt :: String -> String
refAt coord = "(ref a c " ++ coord ++ ")"

-- | An otherwise well-formed alignment around two given references.
alignmentOf :: String -> String -> String
alignmentOf left right =
  "(alignment " ++ left ++ " " ++ right ++ " same (author z) (audit-status reviewed) (rationale r))"

-- | Every entry must fail to decode. The names double as the documentation of
-- what the manifest grammar refuses.
malformedManifests :: [(String, String)]
malformedManifests =
  [ ("empty members", manifestWrap "(policy p q) (backends) (members) (alignments) (questions)")
  , ( "duplicate alias"
    , manifestWrap
        "(policy p q) (backends) (members (member a x) (member a y)) (alignments) (questions)"
    )
  , ("wrong version atom", "(lara-map@2 (policy p q) (backends) (members (member a x)) (alignments) (questions))")
  , ("unknown top-level tag", "(laramap (policy p q) (backends) (members (member a x)) (alignments) (questions))")
  , ("trailing section", manifestWrap "(policy p q) (backends) (members (member a x)) (alignments) (questions) (extra)")
  , ("missing questions section", manifestWrap "(policy p q) (backends) (members (member a x)) (alignments)")
  , ("sections out of order", manifestWrap "(backends) (policy p q) (members (member a x)) (alignments) (questions)")
  , ("trailing top-level form", minimalManifestText ++ " (lara-map@1)")
  , ("unknown member tag", withMembers "(memberx a x)")
  , ("member one field short", withMembers "(member a)")
  , ("member one field long", withMembers "(member a x y)")
  , ("empty member path", withMembers "(member a \"\")")
  , ("empty alias", withMembers "(member \"\" x)")
  , ("alias with a colon", withMembers "(member pa:per x)")
  , ("alias with a space", withMembers "(member \"a b\" x)")
  , ("alias with a dot", withMembers "(member a.b x)")
  , ("policy one field short", manifestWrap "(policy p) (backends) (members (member a x)) (alignments) (questions)")
  , ("policy one field long", manifestWrap "(policy p q r) (backends) (members (member a x)) (alignments) (questions)")
  , ("empty policy path", manifestWrap "(policy p \"\") (backends) (members (member a x)) (alignments) (questions)")
  , ("backend one field short", withBackends "(backend nd)")
  , ("backend one field long", withBackends "(backend nd 1 2)")
  , ("backends descending", withBackends "(backend ra 1) (backend nd 1)")
  , ("backends duplicated", withBackends "(backend nd 1) (backend nd 1)")
  , ("unknown backend tag", withBackends "(backendx nd 1)")
  , ("alignment one field short", withAlignments ("(alignment " ++ refAt "whole" ++ " " ++ refAt "whole" ++ " same (author z) (audit-status reviewed))"))
  , ("alignment one field long", withAlignments ("(alignment " ++ refAt "whole" ++ " " ++ refAt "whole" ++ " same (author z) (audit-status reviewed) (rationale r) (rationale r))"))
  , ("alignment mixed selector", withAlignments (alignmentOf (refAt "whole") (refAt "(arg 0)")))
  , ("alignment mixed selector, reversed", withAlignments (alignmentOf (refAt "(arg 0)") (refAt "whole")))
  , ("unknown assertion atom", withAlignments ("(alignment " ++ refAt "whole" ++ " " ++ refAt "whole" ++ " equal (author z) (audit-status reviewed) (rationale r))"))
  , ("unknown audit status", withAlignments ("(alignment " ++ refAt "whole" ++ " " ++ refAt "whole" ++ " same (author z) (audit-status pending) (rationale r))"))
  , ("author section one field long", withAlignments ("(alignment " ++ refAt "whole" ++ " " ++ refAt "whole" ++ " same (author z w) (audit-status reviewed) (rationale r))"))
  , ("ref one field short", withAlignments (alignmentOf "(ref a c)" (refAt "whole")))
  , ("ref one field long", withAlignments (alignmentOf "(ref a c whole extra)" (refAt "whole")))
  , ("unknown ref tag", withAlignments (alignmentOf "(refx a c whole)" (refAt "whole")))
  , ("coordinate with no target", withAlignments (alignmentOf (refAt "(arg)") (refAt "(arg 0)")))
  , ("coordinate with two targets", withAlignments (alignmentOf (refAt "(arg 0 1)") (refAt "(arg 0)")))
  , ("coordinate is not a NAT", withAlignments (alignmentOf (refAt "(arg x)") (refAt "(arg 0)")))
  , ("coordinate has a leading zero", withAlignments (alignmentOf (refAt "(arg 01)") (refAt "(arg 0)")))
  , ("coordinate is negative", withAlignments (alignmentOf (refAt "(arg -1)") (refAt "(arg 0)")))
  , ("coordinate is signed", withAlignments (alignmentOf (refAt "(arg +1)") (refAt "(arg 0)")))
  , ("unknown coordinate keyword", withAlignments (alignmentOf "(ref a c middle)" (refAt "whole")))
  , ("whole coordinate as a list", withAlignments (alignmentOf "(ref a c (whole))" (refAt "whole")))
  , ("question one field short", withQuestions "(question q (refs (ref a c whole) (ref a d whole)))")
  , ("question one field long", withQuestions "(question q (refs (ref a c whole) (ref a d whole)) (nl t) (nl t))")
  , ("question with one ref", withQuestions "(question q (refs (ref a c whole)) (nl t))")
  , ("question with no refs", withQuestions "(question q (refs) (nl t))")
  , ("unknown refs tag", withQuestions "(question q (refsx (ref a c whole) (ref a d whole)) (nl t))")
  , ("nl section one field long", withQuestions "(question q (refs (ref a c whole) (ref a d whole)) (nl t u))")
  , ("manifest is an atom", "lara-map@1")
  , ("manifest is an empty list", "()")
  ]

-- | Positive controls for 'malformedManifests': the same four wrappers, with no
-- defect injected, must decode. Without these the rejection matrix could be
-- passing because every wrapper is broken for an unrelated reason.
prop_manifestMatrixPositiveControls :: Property
prop_manifestMatrixPositiveControls =
  once $
    conjoin
      [ counterexample name (decodes text)
      | (name, text) <-
          [ ("bare wrapper", manifestWrap "(policy p q) (backends) (members (member a x)) (alignments) (questions)")
          , ("two members", withMembers "(member a x) (member b y)")
          , ("two backends", withBackends "(backend nd 1) (backend ra 1)")
          , ("whole-selector alignment", withAlignments (alignmentOf (refAt "whole") (refAt "whole")))
          , ("argument-selector alignment", withAlignments (alignmentOf (refAt "(arg 0)") (refAt "(arg 12)")))
          , ("two-ref question", withQuestions "(question q (refs (ref a c whole) (ref a d (arg 0))) (nl t))")
          ]
      ]
  where
    -- Report the decode error rather than just @False@ when a control fails.
    decodes text = case decodeMapManifestText text of
      Left err -> counterexample (show err) False
      Right _ -> property True

prop_manifestMalformedMatrix :: Property
prop_manifestMalformedMatrix =
  once $
    conjoin
      [ counterexample name (property (isLeft (decodeMapManifestText text)))
      | (name, text) <- malformedManifests
      ]

-- ---------------------------------------------------------------------------
-- Malformed composite verdicts
-- ---------------------------------------------------------------------------

malformedVerdicts :: [(String, String)]
malformedVerdicts =
  [ ("wrong scope atom", verdictWith [("(scope map)", "(scope solo)")])
  , ("scope section missing", "(map-verdict@1 (schema lara-map-verdict@1) (core lara-core@0.2) (policy p) (backends) (members (member a x (artifact d))) (nodes) (labels) (edges) (statuses))")
  , ("wrong schema atom", verdictWith [("(schema lara-map-verdict@1)", "(schema lara-map-verdict@2)")])
  , ("wrong core version", verdictWith [("(core lara-core@0.2)", "(core lara-core@0.1)")])
  , ("empty members", verdictWith [(membersSection, "(members)")])
  , ( "duplicate member alias"
    , verdictWith
        [ (membersSection, "(members (member paper_a a/paper.lara (artifact sha-a)) (member paper_a b/paper.lara (artifact sha-b)))")
        ]
    )
  , ("member missing the artifact section", verdictWith [(membersSection, "(members (member paper_a a/paper.lara))")])
  , ("member artifact one field long", verdictWith [(membersSection, "(members (member paper_a a/paper.lara (artifact sha-a sha-b)))")])
  , ("labels not covering 0..n-1", verdictWith [("(labels (0 in) (1 out))", "(labels (0 in) (2 out))")])
  , ("labels descending", verdictWith [("(labels (0 in) (1 out))", "(labels (1 out) (0 in))")])
  , ("label entry one field short", verdictWith [("(labels (0 in) (1 out))", "(labels (0) (1 out))")])
  , ("label entry one field long", verdictWith [("(labels (0 in) (1 out))", "(labels (0 in undec) (1 out))")])
  , ("unknown label atom", verdictWith [("(labels (0 in) (1 out))", "(labels (0 maybe) (1 out))")])
  , ("edge out of range", verdictWith [("(edges (0 1))", "(edges (0 2))")])
  , ("edges descending", verdictWith [("(edges (0 1))", "(edges (1 0) (0 1))")])
  , ("edges duplicated", verdictWith [("(edges (0 1))", "(edges (0 1) (0 1))")])
  , ("edge entry one field short", verdictWith [("(edges (0 1))", "(edges (0))")])
  , ( -- The coverage half: every labelled argument must have at least one
      -- handle, so dropping the only node that names index 1 is a defect even
      -- though every remaining node is unique and in range.
      "nodes do not cover a labelled argument"
    , verdictWith [(" (node paper_b b2 1)", "")]
    )
  , ("nodes empty with labels present", verdictWith [("(nodes (node paper_a a1 0) (node paper_b b1 0) (node paper_b b2 1))", "(nodes)")])
  , ("node index out of range", verdictWith [("(node paper_b b2 1)", "(node paper_b b2 2)")])
  , ("node with an undeclared alias", verdictWith [("(node paper_b b2 1)", "(node paper_c b2 1)")])
  , ("duplicate node handle", verdictWith [("(node paper_b b2 1)", "(node paper_a a1 1)")])
  , ("node one field short", verdictWith [("(node paper_b b2 1)", "(node paper_b b2)")])
  , ("status with an undeclared alias", verdictWith [("(status paper_b c7", "(status paper_c c7")])
  , -- The sibling of "duplicate node handle": (alias, claim) is what a reader
    -- resolves a status by, so two rows under one handle make lookup silently
    -- first-wins over rows that may disagree.
    ("duplicate claim handle", verdictWith [("(status paper_b c7", "(status paper_a c1")])
  , ("unknown status atom", verdictWith [("justified)", "blocked)")])
  , ("evidence-blocked is not a map status", verdictWith [("justified)", "evidence-blocked)")])
  , ("status one field short", verdictWith [("(status paper_a c1 (atom agree (str x)) justified)", "(status paper_a c1 justified)")])
  , ("malformed status atom", verdictWith [("(atom agree (str x)) justified)", "(atom) justified)")])
  , ("status atom is not an atom form", verdictWith [("(atom agree (str x)) justified)", "(apat agree (str x)) justified)")])
  , ("trailing section", verdictWith [("(statuses", "(spare) (statuses")])
  , ("verdict is an atom", "map-verdict@1")
  ]
  where
    membersSection =
      "(members (member paper_a a/paper.lara (artifact sha-a))"
        ++ " (member paper_b b/paper.lara (artifact sha-b)))"
    -- Each case is the golden verdict with one substring replaced, so the
    -- difference between an accepted and a rejected verdict is exactly the
    -- named defect.
    verdictWith substitutions = foldl substitute fullVerdictText substitutions
    substitute text (needle, replacement) = replaceFirst needle replacement text

replaceFirst :: String -> String -> String -> String
replaceFirst needle replacement haystack = go haystack
  where
    go [] = error ("MapWireSpec: fixture substring not found: " ++ needle)
    go text@(c : cs)
      | take (length needle) text == needle = replacement ++ drop (length needle) text
      | otherwise = c : go cs

prop_verdictMalformedMatrix :: Property
prop_verdictMalformedMatrix =
  once $
    conjoin
      [ counterexample name (property (isLeft (decodeMapVerdict (parseOrDie text))))
      | (name, text) <- malformedVerdicts
      ]

-- | Every rejection is located: a codec error names the grammar position that
-- refused the bytes and says why.
prop_codecErrorIsLocated :: Property
prop_codecErrorIsLocated =
  once $
    conjoin
      [ counterexample name (located (decodeMapManifestText text))
      | (name, text) <- malformedManifests
      ]
      .&&. conjoin
        [ counterexample name (located (decodeMapVerdict (parseOrDie text)))
        | (name, text) <- malformedVerdicts
        ]
  where
    located result = case result of
      Left (MapWireError context message) ->
        counterexample "empty context" (not (null context))
          .&&. counterexample "empty message" (not (null message))
      Right _ -> counterexample "expected a decode failure" False

-- ---------------------------------------------------------------------------
-- The tag vocabulary
-- ---------------------------------------------------------------------------

prop_mapTagRoundTrip :: Property
prop_mapTagRoundTrip =
  forAll (elements [minBound .. maxBound]) $ \t ->
    parseMapTag (mapTagToString t) === Just t

-- | The map tag table round-trips and has unique spellings. A collision would
-- break 'parseMapTag' silently, because 'Data.Map.fromList' keeps one value per
-- key.
prop_mapTagTableTotal :: Property
prop_mapTagTableTotal =
  conjoin
    [ counterexample "some bounded map tag does not round-trip" $
        property (all (\t -> parseMapTag (mapTagToString t) == Just t) tags)
    , counterexample ("colliding map tag spelling(s): " ++ show collisions) $
        length spellings === length (nub spellings)
    ]
  where
    tags = [minBound .. maxBound] :: [MapTag]
    spellings = map mapTagToString tags
    collisions =
      [spelling | spelling <- nub spellings, length (filter (== spelling) spellings) > 1]

-- ---------------------------------------------------------------------------
-- Aliases, qualification, indices
-- ---------------------------------------------------------------------------

prop_aliasSyntax :: Property
prop_aliasSyntax =
  once $
    conjoin
      [ counterexample ("should be accepted: " ++ show name) $
          property (isJust (mkMemberAlias name))
      | name <- ["a", "paper_a", "Paper-A", "a0", "0", "_", "-", "A_b-0"]
      ]
      .&&. conjoin
        [ counterexample ("should be rejected: " ++ show name) $
            property (isNothing (mkMemberAlias name))
        | name <- ["", "a:b", "a b", "a.b", "a/b", "a\"b", "a(b", "π", "雪", "a\n"]
        ]

-- | The qualified key: exact framed bytes, an injective identity, a display
-- form that is /not/ the identity, and a parser that is a left inverse.
prop_qualification :: Property
prop_qualification =
  once $
    conjoin
      [ counterexample "framed key bytes" $
          qualifiedKey (qualifyId (aliasOf "paper_a") "e1") === "7:paper_a2:e1"
      , counterexample "display form" $
          qualifiedDisplay (qualifyId (aliasOf "paper_a") "e1") === "paper_a::e1"
      , counterexample "unqualify recovers both halves" $
          unqualifyId (qualifyId (aliasOf "paper_a") "e1")
            === (aliasOf "paper_a", "e1")
      , counterexample "frames count UTF-8 bytes, not characters" $
          qualifiedKey (qualifyId (aliasOf "a") "雪") === "1:a3:雪"
      , counterexample "the frame boundary is unambiguous" $
          property
            ( qualifiedKey (qualifyId (aliasOf "ab") "c")
                /= qualifiedKey (qualifyId (aliasOf "a") "bc")
            )
      , counterexample "the display form is not a key" $
          property (isNothing (parseQualifiedKey (qualifiedDisplay one)))
      , counterexample "the display form and the key are different bytes" $
          property (qualifiedDisplay one /= qualifiedKey one)
      ]
  where
    one = qualifyId (aliasOf "paper_a") "e1"

prop_qualifiedKeyRoundTrip :: Property
prop_qualifiedKeyRoundTrip =
  forAll ((,) <$> genAliasText <*> genFreeText) $ \(alias, local) ->
    let identity = qualifyId (aliasOf alias) local
     in parseQualifiedKey (qualifiedKey identity) === Just identity

-- | The framed-key parser refuses everything that is not a canonical key, so it
-- cannot be used to launder an arbitrary string into an identity.
prop_qualifiedKeyMalformed :: Property
prop_qualifiedKeyMalformed =
  once $
    conjoin
      [ counterexample name (property (isNothing (parseQualifiedKey text)))
      | (name, text) <-
          [ ("empty", "")
          , ("no frames", "paper_a::e1")
          , ("one frame only", "7:paper_a")
          , ("length too large", "8:paper_a2:e1")
          , ("length too small", "6:paper_a2:e1")
          , ("leading zero", "07:paper_a2:e1")
          , ("signed length", "+7:paper_a2:e1")
          , ("missing colon", "7paper_a2:e1")
          , ("trailing bytes", "7:paper_a2:e1x")
          , ("three frames", "7:paper_a2:e11:x")
          , ("alias half is not a legal alias", "3:a:b2:e1")
          , ("frame splits a UTF-8 character", "1:a1:雪")
          ]
      ]

prop_indexSmartConstructors :: Property
prop_indexSmartConstructors =
  once $
    conjoin
      [ counterexample "arg index 0" $ property (isJust (mkArgIndex 0))
      , counterexample "arg index -1" $ property (isNothing (mkArgIndex (-1)))
      , counterexample "arg index observer" $ fmap argIndexInt (mkArgIndex 3) === Just 3
      , counterexample "node index 0" $ property (isJust (mkNodeIndex 0))
      , counterexample "node index -1" $ property (isNothing (mkNodeIndex (-1)))
      , counterexample "node index observer" $ fmap nodeIndexInt (mkNodeIndex 3) === Just 3
      , counterexample "empty declared path" $ property (isNothing (mkDeclaredPath ""))
      , counterexample "declared path observer" $
          fmap declaredPathText (mkDeclaredPath "a/b.lara") === Just "a/b.lara"
      ]

-- ---------------------------------------------------------------------------
-- Diagnostics
-- ---------------------------------------------------------------------------

-- | One representative of every error constructor.
--
-- The list is hand-maintained, so it does not by itself break when a
-- constructor is added. What breaks is 'renderMapError': its two helpers match
-- exhaustively, so a new constructor without a diagnostic is a compile error
-- there, and this list is the reminder to add a row here as well — it is what
-- pins the exit code and the one-line shape once the diagnostic exists.
everyMapError :: [MapError]
everyMapError =
  map
    MapBoundary
    [ MBWire (MapWireError "map members" "duplicate member alias paper_a")
    , MBUnreadable "/tmp/a/paper.lara" "does not exist"
    , -- A filesystem or member-source payload may itself be multi-line; the
      -- one-line promise has to survive that, not assume it away.
      MBUnreadable "/tmp/a/paper.lara" "openFile: does not exist\n  (No such file)"
    , MBMemberSource one "codec error\n  line 3, column 7"
    , -- The shared __resolved__ file, not either member's spelling: with a
      -- symlink the two aliases spell different paths and only the canonical
      -- target is true of both. A resolved path may be long and, like any
      -- filesystem string, may contain a newline.
      MBDuplicatePath one two "/tmp/checkout/a/paper.lara"
    , MBDuplicatePath one two "/tmp/odd\nname/paper.lara"
    , MBManifestPolicyMismatch (PolicyId "agreement-v1") (PolicyId "empirical-v1")
    , -- A 'PolicyId' and a 'PropId' are free strings, and that is easy to miss:
      -- both reach a diagnostic from a wire atom, and a QUOTED atom may carry a
      -- @\n@ escape. @(policy "a\nb" p.lara)@ and @(ref paper_a "c\n1" whole)@
      -- are decodable manifests, so the one-line promise has to survive an id
      -- as well as a filesystem string.
      MBManifestPolicyMismatch (PolicyId "agreement\nv1") (PolicyId "empirical-v1")
    , MBManifestPolicySource "parse error at policies/shared.lara:4:1: expected an identifier"
    , MBManifestPolicySource "parse error\n  spanning two lines"
    , MBMemberSource one "policy file not found"
    , MBUnknownAlias one
    , MBDuplicateClaim one (PropId "c1")
    , MBUnknownClaim one (PropId "c1")
    , MBUnknownClaim one (PropId "c\n1")
    , MBCoordinateOutOfRange one (PropId "c1") (argOf 3) 2
    , MBCoordinateOutOfRange one (PropId "c\n1") (argOf 3) 2
    , MBMixedSelector one two
    ]
    ++ map
      MapReject
      ( [MRContract one field | field <- [minBound .. maxBound]]
          ++ [ MRUnsupportedAdmission one "1 pruned leaf"
             , MRUnsupportedAdmission one "pruned:\n  e1\n  e2"
             , MRMemberAdmissionStop one "leaf e1 (observed, ai-executed) rejected"
             , MRMemberAdmissionStop one "leaf e1\n  rejected by (observed, ai-executed)"
             , -- All five 'Rejection' constructors appear, and each is carried
               -- by a map error whose rendered line names it. Two of them
               -- (@DuplicateArgument@, @IncompleteArgument@) were missing, and
               -- remapping both to the wrong wire tag left the whole map suite
               -- green: nothing here forced the constructor to reach a
               -- diagnostic, so a map could name the wrong rejection class to
               -- an operator without a test noticing. 'prop_rejectionSpellings'
               -- below is what turns their presence into coverage.
               MRMemberRejected one (RejectClass R2)
             , MRMemberRejected one DuplicateRule
             , MRMemberRejected one DuplicateArgument
             , MRMemberRejected one IncompleteArgument
             , MRMemberRejected one MissingConflict
             , MRAlignmentFalse 0 Same
             , MRAlignmentFalse 1 Different
             , MRLinkRejected (RejectClass R11)
             , MRLinkRejected DuplicateRule
             , MRLinkRejected DuplicateArgument
             , MRLinkRejected IncompleteArgument
             , MRLinkRejected MissingConflict
             , MRLinkBoundary "two members declare the same argument identifier"
             , MRLinkBoundary "boundary\nspanning\nthree lines"
             ]
      )
  where
    one = aliasOf "paper_a"
    two = aliasOf "paper_b"

-- | The exit-code contract: an ill-formed map exits 2, a rejected map exits 1,
-- and every diagnostic is exactly one nonempty line.
prop_errorContract :: Property
prop_errorContract =
  once $
    conjoin
      [ counterexample (show err) $
          conjoin
            [ counterexample "exit code" (mapErrorExitCode err === expected err)
            , counterexample "one nonempty line" $
                property (not (null line) && '\n' `notElem` line)
            ]
      | err <- everyMapError
      , let line = renderMapError err
      ]
  where
    expected err = case err of
      MapBoundary _ -> 2
      MapReject _ -> 1

-- | The thirty error representatives render __thirty different lines__.
--
-- 'prop_errorContract' above pins the exit code and the one-line shape of every
-- representative, and neither is disturbed by two constructors rendering the
-- same text. Making 'MBUnknownClaim' render 'MBUnknownAlias'\'s line survived
-- the whole map suite, which is a diagnostic that sends an operator to the
-- wrong place with no test objecting. The module already does the right check
-- one level down in 'prop_contractFieldSpellings'; this is the same check at
-- the level of the whole error sum.
--
-- Equal /representatives/ would be a fixture bug rather than a code bug, so the
-- counterexample prints the colliding pair.
prop_errorLinesAreDistinct :: Property
prop_errorLinesAreDistinct =
  once $
    let lines' = map renderMapError everyMapError
        collisions =
          [ (a, b)
          | (i, a) <- zip [0 :: Int ..] lines'
          , (j, b) <- zip [0 ..] lines'
          , i < j
          , a == b
          ]
     in counterexample (show collisions) (length (nub lines') === length lines')

-- | Every 'Rejection' constructor gets its own spelling in a map diagnostic.
--
-- 'rejectionText' routes each constructor through "Lara.Wire"\'s frozen tag
-- table, and the routing is a hand-written case: two constructors can be sent
-- to one tag with no compile error. Remapping @DuplicateArgument@ and
-- @IncompleteArgument@ both to @TDupRule@ did exactly that and left every
-- property green, because 'everyMapError' listed neither. So enumerate the sum
-- here rather than relying on the representative list to stay complete, and
-- assert the rendered /tag/, not only that the lines differ: a line naming the
-- wrong rejection class is wrong even when it is unique.
prop_rejectionSpellings :: Property
prop_rejectionSpellings =
  once $
    let rejections =
          [ RejectClass R2
          , DuplicateRule
          , DuplicateArgument
          , IncompleteArgument
          , MissingConflict
          ]
        rendered = map (renderMapError . MapReject . MRLinkRejected) rejections
        expected =
          [ "map link rejected: " ++ tag
          | tag <- ["R2", "duplicate-rule", "duplicate-argument", "incomplete-argument", "missing-conflict"]
          ]
     in conjoin
          [ counterexample "each rejection renders its own tag" (rendered === expected)
          , counterexample "the five spellings are distinct" $
              length (nub rendered) === length rendered
          ]

-- | The contract-field spellings are distinct, so a diagnostic always says
-- which half of the shared contract disagreed.
prop_contractFieldSpellings :: Property
prop_contractFieldSpellings =
  once $
    let spellings = map contractFieldText [minBound .. maxBound]
     in counterexample (show spellings) (length spellings === length (nub spellings))

-- ---------------------------------------------------------------------------
-- Registry
-- ---------------------------------------------------------------------------

mapWireSpecProps :: [(String, IO Result)]
mapWireSpecProps =
  [ ("map manifest golden vectors", quickCheckResult prop_manifestGoldenVectors)
  , ("map verdict golden vector", quickCheckResult prop_verdictGoldenVector)
  , ("map backend spelling is the wire pair", quickCheckResult prop_backendSpelling)
  , ("map and solo verdict scopes do not cross", quickCheckResult prop_scopesDoNotCross)
  , ("map manifest round-trip", quickCheckResult prop_manifestRoundTrip)
  , ("map verdict round-trip", quickCheckResult prop_verdictRoundTrip)
  , ("map encoding is stable for equal values", quickCheckResult prop_encodingIsStable)
  , ("map order is carried, not sorted", quickCheckResult prop_orderIsCarriedNotSorted)
  , ("map manifest matrix positive controls", quickCheckResult prop_manifestMatrixPositiveControls)
  , ("map manifest malformed matrix", quickCheckResult prop_manifestMalformedMatrix)
  , ("map verdict malformed matrix", quickCheckResult prop_verdictMalformedMatrix)
  , ("map codec error is located", quickCheckResult prop_codecErrorIsLocated)
  , ("map tag round-trip", quickCheckResult prop_mapTagRoundTrip)
  , ("map tag table total", quickCheckResult prop_mapTagTableTotal)
  , ("map alias syntax", quickCheckResult prop_aliasSyntax)
  , ("map qualification golden", quickCheckResult prop_qualification)
  , ("map qualified key round-trip", quickCheckResult prop_qualifiedKeyRoundTrip)
  , ("map qualified key malformed rejected", quickCheckResult prop_qualifiedKeyMalformed)
  , ("map index smart constructors", quickCheckResult prop_indexSmartConstructors)
  , ("map error exit codes and diagnostics", quickCheckResult prop_errorContract)
  , ("map contract field spellings distinct", quickCheckResult prop_contractFieldSpellings)
  , ("map error lines are distinct", quickCheckResult prop_errorLinesAreDistinct)
  , ("map rejection spellings distinct", quickCheckResult prop_rejectionSpellings)
  ]
