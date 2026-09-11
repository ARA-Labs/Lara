-- | Ground-truth tests for the map's driver stage ("Lara.Map.Driver"), for the
-- @.laramap@ CLI door, and for the cross-driver parity envelope.
--
-- Six things are pinned here, and between them they are what makes a composite
-- verdict something two implementations can be held to:
--
--   * __the verdict is the map's whole answer, in a fixed order__ — members in
--     manifest order, nodes in member-then-declaration order, labels covering
--     @0 .. n-1@ ascending, edges strictly ascending, statuses in
--     member-then-claim order, and the same bytes on a second run
--     ('prop_verdictOrderingIsCanonical', 'prop_mapIsDeterministic');
--   * __the parity envelope is a faithful projection of the loaded members__ —
--     field for field, in order, and byte-fresh against the committed fixture,
--     so the Lean driver is never compared over stale material
--     ('prop_envelopeMirrorsLoadedMembers', 'prop_envelopeIsFresh',
--     'prop_verdictGoldenIsFresh', 'prop_envelopeRoundTrips');
--   * __relabelling moves the report and not the answer__ — permuting the
--     manifest's members permutes @members@, @nodes@ and @statuses@ and
--     renumbers the framework, and renaming every alias changes every handle,
--     and in both cases each @(claim, status)@ pair is unchanged
--     ('prop_memberPermutationPermutesReport',
--     'prop_aliasRenamingPreservesStatuses');
--   * __a singleton map is the member's own check__ — one member alone gets the
--     statuses its solo verdict gives it, which is the base case the
--     non-monotonicity of the multi-member case is measured against
--     ('prop_singletonMapMatchesSoloStatuses');
--   * __every refusal lands in the right class__ — a false alignment and a
--     contract disagreement are rejections (exit 1), an unresolvable
--     coordinate and a duplicate alias are ill-formed maps (exit 2), and each
--     prints one line and no verdict ('prop_falseAlignment*',
--     'prop_contract*', 'prop_unknown*', 'prop_mixedSelectorInQuestion',
--     'prop_duplicateMemberAlias');
--   * __both decoders refuse the same envelope bytes__ — every committed
--     malformed envelope is refused by the Haskell decoder here, and by the
--     Lean decoder in @scripts\/check-map-conformance.sh@, which is the other
--     half of the same matrix ('prop_malformedEnvelopesAreRefused').
--
-- == What is here and what is in the shell script
--
-- Nothing in this module runs the Lean driver. @cabal test@ has never spawned
-- it — the wire differential is @scripts\/differential.sh@, outside the suite —
-- and the map keeps that division: @scripts\/check-map-conformance.sh@ owns the
-- byte-comparison of the two drivers, and this module owns the in-process half
-- (freshness, the Haskell decoder's refusals, the CLI contract). The two meet
-- at the committed fixtures under @test\/fixtures\/map\/@, which is why the
-- freshness properties here are load-bearing rather than decorative: they are
-- what guarantees the bytes the script hands the Lean driver are the bytes this
-- driver would produce today.
--
-- == Fixtures
--
-- The committed anchors live under @test\/fixtures\/map\/@ and are regenerated
-- with the commands in @scripts\/check-map-conformance.sh@'s header, never by
-- hand. Everything else is built into a fresh temporary directory, as
-- "MapLoadSpec" and "MapLinkSpec" do, so no committed byte is edited by a test
-- and a failure names a single cause. The suite runs from the package root (as
-- @cabal test@ does), the assumption "CliSpec" and "DifferentialSpec" share.
module MapSpec (mapSpecProps, envelopeDefects, readEnvelope) where

import Data.List (intersect, isInfixOf, isPrefixOf, isSuffixOf, nub, sort)
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromMaybe)
import System.Directory (listDirectory)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)
import Test.QuickCheck

import Lara.AST
  ( ArgId (..)
  , AuditStatus (..)
  , BackendId (..)
  , Binding (..)
  , Digest (..)
  , PolicyId (..)
  , PropId (..)
  , Status (..)
  , Unit (..)
  )
import Lara.Elaborate (PreparedSource (..), runSourceCheck, sourceResultVerdict)
import Lara.Map.Driver
  ( EnvTag
  , mkMapCheckInput
  , MapCheckInput (..)
  , MapCheckMember (..)
  , decodeMapCheckInput
  , decodeMapCheckInputText
  , encodeMapCheckInput
  , envTagToString
  , mapCheckInput
  , parseEnvTag
  , resolveReferences
  , runMap
  )
import Lara.Map.Load
  ( checkedMembers
  , cmAlias
  , cmArtifact
  , cmClaims
  , cmDeclaredPath
  , cmUnit
  , loadMap
  )
import Lara.Map.Types
  ( Alignment (..)
  , Assertion (..)
  , ContractField (..)
  , Coord (..)
  , MapBoundaryError (..)
  , MapError (..)
  , MapNode (..)
  , MapRejectError (..)
  , MapStatus (..)
  , MapVerdict (..)
  , DeclaredPath
  , MapRef (..)
  , MapWireError (..)
  , MemberAlias
  , MemberRecord (..)
  , aliasText
  , declaredPathText
  , mapErrorExitCode
  , mkArgIndex
  , mkDeclaredPath
  , mkMemberAlias
  , nodeIndexInt
  , renderMapError
  )
import Lara.Map.Wire (decodeMapVerdict, encodeMapVerdict)
import Lara.Prop (Prop (..))
import Lara.Source.Load (loadSource, loadedPrepared, renderSourceLoadError)
import qualified Lara.TempTree as TempTree
import Lara.Wire (Outcome (..), PublicStatus (..), printSExpr, verdictOutcome)

-- ---------------------------------------------------------------------------
-- Fixture paths and helpers
-- ---------------------------------------------------------------------------

-- | The committed accepting anchor: three members under one shared contract,
-- two of them in direct cross-member conflict and the third about a different
-- setting, plus three alignments and one question.
agreementDir :: FilePath
agreementDir = "test/fixtures/map/agreement"

agreementManifest :: FilePath
agreementManifest = agreementDir </> "map.laramap"

-- | The map whose members share a leaf-free argument, so that the structural
-- merge fires (issue #316). Its goldens are pinned beside the agreement map's.
mergeDir :: FilePath
mergeDir = "test/fixtures/map/merge"

-- | The one fixture in the tree carrying @(audit-status disputed)@, and so the
-- only place the decoder's audit-status table is exercised at all.
falseAlignmentDir :: FilePath
falseAlignmentDir = "test/fixtures/map/false-alignment"

falseAlignmentManifest :: FilePath
falseAlignmentManifest = falseAlignmentDir </> "map.laramap"

malformedDir :: FilePath
malformedDir = "test/fixtures/map/malformed"

-- | The executable name; Cabal puts it on @PATH@ during @cabal test@ via the
-- test-suite's @build-tool-depends: lara:lara@, exactly as "CliSpec" relies on.
laraBin :: String
laraBin = "lara"

runLara :: [String] -> IO (ExitCode, String, String)
runLara args = readProcessWithExitCode laraBin args ""

-- | A member alias the fixture author asserts is well formed. The @error@ is a
-- test-authoring bug, never a decode path.
-- | A declared path, or a loud failure: every path this module builds is a
-- literal it wrote, so 'Nothing' means the fixture is wrong.
pathOf :: String -> DeclaredPath
pathOf text = case mkDeclaredPath text of
  Nothing -> error ("MapSpec: not a declared path: " ++ show text)
  Just declared -> declared

aliasOf :: String -> MemberAlias
aliasOf name =
  fromMaybe (error ("MapSpec: malformed fixture alias " ++ show name)) (mkMemberAlias name)

-- | Build a throwaway directory tree, run the body over its root, then remove
-- it. The one shared helper ("Lara.TempTree"), which reserves the directory
-- rather than deriving its name.
withTree :: [(FilePath, String)] -> (FilePath -> IO a) -> IO a
withTree = TempTree.withTree "lara-mapdriver"

-- | The committed agreement fixture's sources, read once per test that needs
-- them. Copied into a temporary tree rather than edited in place: no fixture in
-- the repository is touched by this suite.
data Sources = Sources
  { srcPolicy :: String
  , srcPos :: String
  , srcNeg :: String
  , srcOther :: String
  }

readSources :: IO Sources
readSources =
  Sources
    <$> readFile (agreementDir </> "empirical-v1.policy.lara")
    <*> readFile (agreementDir </> "pos.lara")
    <*> readFile (agreementDir </> "neg.lara")
    <*> readFile (agreementDir </> "other.lara")

-- | A @lara-map\@1@ manifest over the given sections.
manifestWith :: String -> String -> String -> String -> String
manifestWith policyPath members alignments questions =
  unlines
    [ "(lara-map@1"
    , "  (policy empirical-v1 " ++ policyPath ++ ")"
    , "  (backends (backend nd 1))"
    , "  (members " ++ members ++ ")"
    , "  (alignments " ++ alignments ++ ")"
    , "  (questions " ++ questions ++ "))"
    ]

-- | A tree holding the given @(alias, file name, source)@ members beside one
-- shared policy copy, plus a manifest naming them in the given order.
memberTree :: Sources -> [(String, FilePath, String)] -> String -> String -> [(FilePath, String)]
memberTree sources members alignments questions =
  ("map.laramap", manifest)
    : ("empirical-v1.policy.lara", srcPolicy sources)
    : [(file, source) | (_, file, source) <- members]
  where
    manifest =
      manifestWith
        "empirical-v1.policy.lara"
        (unwords ["(member " ++ alias ++ " " ++ file ++ ")" | (alias, file, _) <- members])
        alignments
        questions

-- | Run a map built from the given members, alignments and questions.
runFixture
  :: Sources -> [(String, FilePath, String)] -> String -> String -> IO (Either MapError MapVerdict)
runFixture sources members alignments questions =
  withTree
    (memberTree sources members alignments questions)
    (\root -> runMap (root </> "map.laramap"))

-- | The pair the agreement fixture's two conflicting members form.
conflictingPair :: Sources -> [(String, FilePath, String)]
conflictingPair sources =
  [ ("paper_pos", "pos.lara", srcPos sources)
  , ("paper_neg", "neg.lara", srcNeg sources)
  ]

-- ---------------------------------------------------------------------------
-- Outcome assertions
-- ---------------------------------------------------------------------------

describe :: Either MapError MapVerdict -> String
describe = either renderMapError (const "accepted")

-- | The map produced a verdict, and the body has something to say about it.
expectVerdict :: String -> Either MapError MapVerdict -> (MapVerdict -> Property) -> Property
expectVerdict what outcome body =
  counterexample (what ++ ": got " ++ describe outcome) $
    case outcome of
      Right verdict -> body verdict
      Left _ -> property False

-- | The outcome is an ill-formed-map diagnostic matching the predicate, and it
-- exits 2. The exit code is asserted with the classification because the pair
-- is the contract.
expectBoundary
  :: String -> Either MapError MapVerdict -> (MapBoundaryError -> Bool) -> Property
expectBoundary what outcome matches =
  counterexample (what ++ ": got " ++ describe outcome) $
    case outcome of
      Left err@(MapBoundary boundary) -> matches boundary .&&. mapErrorExitCode err === 2
      _ -> property False

-- | The outcome is a rejected-map diagnostic matching the predicate, and it
-- exits 1.
expectReject :: String -> Either MapError MapVerdict -> (MapRejectError -> Bool) -> Property
expectReject what outcome matches =
  counterexample (what ++ ": got " ++ describe outcome) $
    case outcome of
      Left err@(MapReject rejection) -> matches rejection .&&. mapErrorExitCode err === 1
      _ -> property False

-- | The @(alias, claim, status)@ triples a verdict reports, which is the
-- map's answer stripped of every handle and every ordering decision.
answersOf :: MapVerdict -> [(String, String, Status)]
answersOf verdict =
  [ (aliasText (msAlias status), let PropId claim = msClaim status in claim, msStatus status)
  | status <- mvStatuses verdict
  ]

-- | The same, keyed by claim name alone — what survives renaming every alias.
claimAnswersOf :: MapVerdict -> [(String, Status)]
claimAnswersOf verdict = [(claim, status) | (_, claim, status) <- answersOf verdict]

-- ---------------------------------------------------------------------------
-- The committed anchor: the verdict and its ordering
-- ---------------------------------------------------------------------------

-- | The committed agreement map accepts, and reports exactly the answer its
-- three members' conflict structure forces: the two members that state
-- opposite results about one setting are both @contested@, and the third,
-- about a different setting, is untouched and stays @justified@.
--
-- This is the anchor the cross-driver harness compares byte for byte, so it is
-- worth stating what makes it non-trivial: neither @contested@ here is
-- declared. Both members are @justified@ on their own; the two attacks that
-- change that are generated by the cross-member saturation from the shared
-- policy's declared contrary, and are then typed by the ordinary checker like
-- any other attack.
prop_agreementMapAccepts :: Property
prop_agreementMapAccepts = once $ ioProperty $ do
  outcome <- runMap agreementManifest
  pure $ expectVerdict "agreement map" outcome $ \verdict ->
    answersOf verdict
      === [ ("paper_pos", "c_pos", Contested)
          , ("paper_neg", "c_neg", Contested)
          , ("paper_other", "c_other", Justified)
          ]

-- | Every section of the composite verdict is in its documented canonical
-- order.
--
-- The encoder never sorts, so this is a statement about the __driver__: the
-- ordering the driver computed is the ordering that reaches the bytes, and an
-- ordering bug shows up here rather than being tidied away by the printer.
prop_verdictOrderingIsCanonical :: Property
prop_verdictOrderingIsCanonical = once $ ioProperty $ do
  outcome <- runMap agreementManifest
  pure $ expectVerdict "agreement map" outcome $ \verdict ->
    let indices = map (nodeIndexInt . fst) (mvLabels verdict)
        n = length (mvLabels verdict)
        edges = [(nodeIndexInt s, nodeIndexInt t) | (s, t) <- mvEdges verdict]
        nodeKeys = [(aliasText (mnAlias node), let ArgId a = mnArg node in a) | node <- mvNodes verdict]
     in conjoin
          [ counterexample "members are in manifest order" $
              map (aliasText . mrAlias) (NE.toList (mvMembers verdict))
                === ["paper_pos", "paper_neg", "paper_other"]
          , counterexample "nodes are in member then declaration order" $
              nodeKeys === [("paper_pos", "pa"), ("paper_neg", "pb"), ("paper_other", "po")]
          , counterexample "every node index is in range" $
              property (all (\node -> nodeIndexInt (mnIndex node) < n) (mvNodes verdict))
          , counterexample "labels cover 0..n-1 ascending" (indices === [0 .. n - 1])
          , counterexample "edges are strictly ascending" $
              property (and (zipWith (<) edges (drop 1 edges)))
          , counterexample "statuses are in member then claim order" $
              map (\s -> aliasText (msAlias s)) (mvStatuses verdict)
                === ["paper_pos", "paper_neg", "paper_other"]
          ]

-- | Running one map twice produces the same verdict. A map is a recheck of
-- current bytes, so nothing may depend on a cache, a traversal order, or a
-- filesystem listing.
prop_mapIsDeterministic :: Property
prop_mapIsDeterministic = once $ ioProperty $ do
  first <- runMap agreementManifest
  second <- runMap agreementManifest
  pure $
    counterexample "two runs of one map disagree" $
      fmap (printSExpr . encodeMapVerdict) first === fmap (printSExpr . encodeMapVerdict) second

-- | The committed golden verdict is what this driver produces today, byte for
-- byte including the trailing newline the CLI adds.
--
-- Regenerated with the command in @scripts\/check-map-conformance.sh@'s header.
-- The freshness matters because the cross-driver harness compares the Lean
-- driver against the /committed/ envelope: if a member could drift away from
-- its goldens, the harness would go on comparing two drivers over bytes neither
-- of them would produce.
prop_verdictGoldenIsFresh :: Property
prop_verdictGoldenIsFresh = once $ ioProperty $
  conjoin <$> mapM fresh [agreementDir, mergeDir]
  where
    fresh dir = do
      outcome <- runMap (dir </> "map.laramap")
      golden <- readFile (dir </> "map.verdict.sexp")
      pure $ expectVerdict dir outcome $ \verdict ->
        counterexample (dir ++ ": committed map.verdict.sexp has drifted") $
          printSExpr (encodeMapVerdict verdict) ++ "\n" === golden

-- ---------------------------------------------------------------------------
-- The parity envelope
-- ---------------------------------------------------------------------------

-- | The committed parity envelope is what the frontend derives today, byte for
-- byte. Same reasoning as 'prop_verdictGoldenIsFresh', and this is the half
-- that guards the __input__ side of the cross-driver comparison.
prop_envelopeIsFresh :: Property
prop_envelopeIsFresh = once $ ioProperty $
  conjoin <$> mapM fresh [agreementDir, mergeDir]
  where
    fresh dir = do
      loaded <- loadMap (dir </> "map.laramap")
      golden <- readFile (dir </> "map.core.sexp")
      pure $ case loaded of
        Left err -> counterexample (dir ++ " did not load: " ++ renderMapError err) (property False)
        Right members -> case mapCheckInput members of
          Left err ->
            counterexample
              (dir ++ ": envelope refused: " ++ mweContext err ++ ": " ++ mweMessage err)
              (property False)
          Right input ->
            counterexample (dir ++ ": committed map.core.sexp has drifted") $
              printSExpr (encodeMapCheckInput input) ++ "\n" === golden

-- | The envelope is a faithful projection of the loaded members: same members,
-- in the same order, each carrying the same alias, the same
-- __manifest-spelled__ path, the same declared @artifact@ digest, the same
-- claim names in the same order paired with the same propositions, and the same
-- elaborated unit.
--
-- This is the frontend-to-envelope mapping stated field by field. Byte
-- freshness alone would not say it: a projection that dropped a member's unit
-- and re-derived it from somewhere else could still produce stable bytes.
prop_envelopeMirrorsLoadedMembers :: Property
prop_envelopeMirrorsLoadedMembers = once $ ioProperty $ do
  loaded <- loadMap agreementManifest
  pure $ case loaded of
    Left err -> counterexample ("agreement map did not load: " ++ renderMapError err) (property False)
    Right members -> case mapCheckInput members of
      Left err ->
        counterexample ("envelope refused: " ++ mweContext err ++ ": " ++ mweMessage err) (property False)
      Right input ->
        let projected = NE.toList (mciMembers input)
            original = NE.toList (checkedMembers members)
         in conjoin
                [ counterexample "member count" (length projected === length original)
                , counterexample "aliases, in order" $
                    map (aliasText . mcmAlias) projected === map (aliasText . cmAlias) original
                , counterexample "manifest-spelled paths, in order" $
                    map (declaredPathText . mcmPath) projected
                      === map (declaredPathText . cmDeclaredPath) original
                , counterexample "declared artifact digests, in order" $
                    map (\m -> let Digest d = mcmArtifact m in d) projected
                      === map (\m -> let Digest d = cmArtifact m in d) original
                , counterexample "claim names and propositions, in declaration order" $
                    map mcmClaims projected === map cmClaims original
                , counterexample "elaborated units" $
                    map (unitArgs . mcmUnit) projected === map (unitArgs . cmUnit) original
                , counterexample "elaborated leaves" $
                    map (unitLeaves . mcmUnit) projected === map (unitLeaves . cmUnit) original
                , counterexample "elaborated attacks" $
                    map (unitAttacks . mcmUnit) projected === map (unitAttacks . cmUnit) original
                , counterexample "queried claim atoms" $
                    map (unitQueries . mcmUnit) projected === map (unitQueries . cmUnit) original
                ]

-- | The envelope codec is an inverse pair on a value the frontend produced, and
-- its bytes are stable: re-encoding what was decoded prints the same text.
--
-- __Run over both committed maps, not just the accepting one.__ The agreement
-- map exercises no @(audit-status …)@ row other than the default;
-- @false-alignment@ is the only fixture in the tree carrying
-- @(audit-status disputed)@, so leaving it out left the decoder's audit-status
-- table with no forcing test at all. A reviewer changed that table so
-- @disputed@ decoded as @Unreviewed@ and the whole map suite stayed green: the
-- positive controls checked @isRight@, and laziness meant the decoded value was
-- never demanded. The Lean parity gate cannot compensate either, because an
-- audit status never reaches a verdict. The @===@ below demands the whole
-- structure, which is what turns this into a table test.
prop_envelopeRoundTrips :: Property
prop_envelopeRoundTrips =
  once $
    conjoin
      [ counterexample manifest (ioProperty (roundTrip manifest))
      | manifest <- [agreementManifest, falseAlignmentManifest]
      ]
  where
    roundTrip manifest = do
      loaded <- loadMap manifest
      pure $ case loaded of
        Left err -> counterexample ("did not load: " ++ renderMapError err) (property False)
        Right members -> case mapCheckInput members of
          Left err ->
            counterexample ("envelope refused: " ++ mweMessage err) (property False)
          Right input ->
            let bytes = encodeMapCheckInput input
             in case decodeMapCheckInput bytes of
                  Left err -> counterexample ("did not decode: " ++ show err) (property False)
                  Right back ->
                    conjoin
                      [ counterexample "decode . encode = id" (back === input)
                      , counterexample "bytes are stable" $
                          printSExpr (encodeMapCheckInput back) === printSExpr bytes
                      ]

-- | The composite verdict codec is an inverse pair on a verdict the driver
-- produced — the terminal-artifact invariants "Lara.Map.Wire" checks at its
-- decode boundary are ones this driver's output actually satisfies, rather than
-- ones only a generator satisfies.
prop_verdictRoundTrips :: Property
prop_verdictRoundTrips = once $ ioProperty $ do
  outcome <- runMap agreementManifest
  pure $ expectVerdict "agreement map" outcome $ \verdict ->
    decodeMapVerdict (encodeMapVerdict verdict) === Right verdict

-- | Each committed malformed envelope is refused __for the reason its filename
-- claims__, and the two committed real envelopes decode.
--
-- The Lean decoder's half of this matrix is
-- @scripts\/check-map-conformance.sh@, which requires exit 2 and an empty
-- stdout for each of the same files. The set is discovered by listing the
-- directory rather than enumerated here, so a fixture added to the tree cannot
-- be silently uncovered on this side; it is also required to be non-empty, so
-- a directory that moved fails loudly instead of passing vacuously.
--
-- __Why the message and not just the refusal.__ An earlier version asserted
-- @either (const True) (const False)@, which accepts /any/ refusal. Each
-- fixture did fail for the reason its name claims, but nothing held it there:
-- a fixture edited into a different malformation, or a decoder change that
-- moves one check ahead of another, keeps a bare @isLeft@ green while the
-- corpus quietly stops covering what it says it covers. The Lean half cannot
-- compensate, since it requires only exit 2 and an empty stdout. So every
-- fixture is paired with a substring of 'mweMessage' below, and the pairing is
-- required to be __total in both directions__: a new fixture with no row, or a
-- row naming a file that is gone, fails this property rather than being
-- skipped. 'prop_codecErrorIsLocated' in "MapWireSpec" sets the same precedent
-- one level down.
prop_malformedEnvelopesAreRefused :: Property
prop_malformedEnvelopesAreRefused = once $ ioProperty $ do
  names <- sort . filter (".sexp" `isSuffixOf`) <$> listDirectory malformedDir
  refusals <- mapM refusal names
  good <-
    mapM
      decodeFile
      [ agreementDir </> "map.core.sexp"
      , falseAlignmentDir </> "map.core.sexp"
      ]
  pure $
    conjoin
      [ counterexample "the malformed corpus is not empty" (property (not (null names)))
      , counterexample "every malformed fixture has an expected-reason row" $
          sort names === sort (map fst malformedReasons)
      , counterexample "every malformed envelope is refused for its stated reason" $
          conjoin
            [ counterexample (name ++ ": " ++ describeRefusal outcome) $
                property (refusedBecause name outcome)
            | (name, outcome) <- zip names refusals
            ]
      , counterexample "every real envelope decodes and re-encodes to its own bytes" $
          conjoin
            [ counterexample path outcome
            | (path, outcome) <- good
            ]
      ]
  where
    refusal name = do
      text <- readFile (malformedDir </> name)
      pure (decodeMapCheckInputText text)
    -- A positive control that checks only @isRight@ never demands the decoded
    -- value, so laziness leaves every field of it untested — which is how a
    -- mutated audit-status table survived this matrix. Re-encoding forces the
    -- whole structure and pins it to the committed bytes at the same time.
    decodeFile path = do
      text <- readFile path
      pure . (,) path $ case decodeMapCheckInputText text of
        Left err ->
          counterexample ("did not decode: " ++ mweContext err ++ ": " ++ mweMessage err) (property False)
        Right decoded -> printSExpr (encodeMapCheckInput decoded) ++ "\n" === text
    describeRefusal = either (\err -> mweContext err ++ ": " ++ mweMessage err) (const "ACCEPTED")
    refusedBecause name outcome = case outcome of
      Right _ -> False
      Left err -> case lookup name malformedReasons of
        Nothing -> False
        Just expected -> expected `isInfixOf` mweMessage err

-- | What each malformed fixture's filename promises, as a substring of the
-- decoder's own message. Kept beside the corpus it describes rather than in the
-- property, because it is the corpus's contract: the filenames already imply
-- these, and writing them down is what makes the implication checkable.
malformedReasons :: [(FilePath, String)]
malformedReasons =
  [ ("alignment-arg-out-of-range.sexp", "has no argument 3 (arity 1)")
  , ("backends-unsorted.sexp", "backends must be duplicate-free and ascending")
  , ("bad-alias.sexp", "malformed member alias")
  , ("duplicate-alias.sexp", "duplicate member alias paper_a")
  , ("duplicate-claim.sexp", "duplicate claim name c1")
  , ("duplicate-leaf.sexp", "duplicate leaf id e1")
  , ("empty-path.sexp", "path must be a nonempty atom")
  , ("mismatched-rules.sexp", "disagree on the shared policy's rules")
  , ("mismatched-signature.sexp", "disagree on the shared policy's signature")
  , ("mismatched-theories.sexp", "disagree on the shared policy's theories")
  , ("mixed-selector.sexp", "must both be whole or both be (arg n)")
  , ("no-members.sexp", "declares at least one member")
  , ("non-ascii-alias.sexp", "malformed member alias")
  , ("unknown-alignment-alias.sexp", "undeclared member alias paper_z")
  , ("unknown-alignment-claim.sexp", "declares no claim c9")
  , ("unknown-tag.sexp", "expected (alignments")
  ]

-- ---------------------------------------------------------------------------
-- The envelope's generator round trip
-- ---------------------------------------------------------------------------

-- | Envelopes built by varying the committed one, rather than from nothing.
--
-- The manifest codec has a generator and the verdict codec has a generator; the
-- envelope, which is the entire basis of the cross-driver parity claim, had
-- neither. What it needs and they do not is a 'Lara.AST.Unit' per member, and a
-- Unit generator would be a second elaborator — large, and liable to generate
-- units no frontend can produce, which is exactly the population a parity
-- anchor should not be drawn from. So the units here are __real__: they come
-- from the loaded agreement map, and the generator varies everything around and
-- between them.
--
-- Varied: member order and count (any non-empty sub-sequence, so a singleton
-- and the full map are both reachable), each member's alias, declared path and
-- artifact digest, the policy id, the backend selection, and each alignment's
-- two coordinates, assertion, author, audit status and rationale. Alignments
-- are re-pointed at whichever members survive, so a generated envelope is
-- always one 'mkMapCheckInput' accepts and the round trip is testing the codec
-- rather than the constructor.
genEnvelope :: [MapCheckMember] -> Gen MapCheckInput
genEnvelope base = do
  kept <- genNonEmptySubsequence base
  renamed <- mapM freshen (zip [0 :: Int ..] kept)
  policy <- PolicyId <$> elements ["empirical-v1", "p", "shared-policy-v3"]
  backends <- genEnvBackends
  alignmentCount <- choose (0, 4)
  alignments <- vectorOf alignmentCount (genEnvAlignment renamed)
  case NE.nonEmpty renamed of
    Nothing -> error "MapSpec: genEnvelope kept no members"
    Just members -> case mkMapCheckInput policy backends members alignments of
      Left err -> error ("MapSpec: genEnvelope built an invalid envelope: " ++ mweMessage err)
      Right envelope -> pure envelope
  where
    freshen (index, member) = do
      suffix <- elements ["a", "b", "z9", "M-1", "_x"]
      digest <- elements ["sha256:aaaa", "sha256:bbbb", "sha256:0"]
      dir <- elements ["", "a/", "../b/", "/abs/"]
      pure
        member
          { mcmAlias = aliasOf ("m" ++ show index ++ suffix)
          , mcmPath = pathOf (dir ++ "member" ++ show index ++ ".lara")
          , mcmArtifact = Digest digest
          }

genNonEmptySubsequence :: [a] -> Gen [a]
genNonEmptySubsequence xs = do
  keeps <- vectorOf (length xs) arbitrary
  case [x | (True, x) <- zip keeps xs] of
    [] -> pure (take 1 xs)
    kept -> pure kept

-- | Duplicate-free and strictly ascending, as the grammar requires.
genEnvBackends :: Gen [(BackendId, String)]
genEnvBackends = do
  n <- choose (0, 3)
  raw <- vectorOf n ((,) . BackendId <$> elements ["nd", "ra", "ord", "insp"] <*> elements ["1", "2"])
  pure (nub (sort raw))

-- | An alignment over the surviving members, with both coordinates the same
-- kind and both in range for the claim they name.
genEnvAlignment :: [MapCheckMember] -> Gen Alignment
genEnvAlignment members = do
  left <- genEnvRef
  right <- genEnvRef
  whole <- arbitrary
  leftCoord <- genCoordFor whole left
  rightCoord <- genCoordFor whole right
  assertion <- elements [Same, Different]
  author <- elements ["reviewer_r", "alice", ""]
  rationale <- elements ["because", "", "a\nmultiline\nnote"]
  audit <- elements [Unreviewed, Reviewed, Disputed]
  pure
    Alignment
      { alignLeft = uncurry3 MapRef (refOf left leftCoord)
      , alignRight = uncurry3 MapRef (refOf right rightCoord)
      , alignAssertion = assertion
      , alignBinding = Binding author rationale audit
      }
  where
    uncurry3 f (a, b, c) = f a b c
    refOf (member, claim, _) coord = (mcmAlias member, claim, coord)
    genEnvRef = do
      member <- elements members
      (claim, proposition) <- elements (mcmClaims member)
      pure (member, claim, proposition)
    genCoordFor whole (_, _, Prop _ terms)
      | whole || null terms = pure CoordWhole
      | otherwise = do
          index <- choose (0, length terms - 1)
          case mkArgIndex index of
            Nothing -> error "MapSpec: genEnvAlignment built a negative coordinate"
            Just argIndex -> pure (CoordArg argIndex)

-- | @decode . encode == id@ on generated envelopes, and the bytes are stable.
--
-- 'prop_envelopeRoundTrips' pins the two committed envelopes; this pins the
-- population around them, which is what a single-fixture round trip cannot: an
-- alias spelling, a path shape, a coordinate, an audit status or an empty
-- rationale that no committed fixture happens to carry.
prop_envelopeGeneratedRoundTrips :: Property
prop_envelopeGeneratedRoundTrips = ioProperty $ do
  loaded <- loadMap agreementManifest
  pure $ case loaded of
    Left err -> counterexample ("agreement map did not load: " ++ renderMapError err) (property False)
    Right members -> case mapCheckInput members of
      Left err -> counterexample ("base envelope refused: " ++ mweMessage err) (property False)
      Right base ->
        forAll (genEnvelope (NE.toList (mciMembers base))) $ \envelope ->
          let bytes = encodeMapCheckInput envelope
           in case decodeMapCheckInput bytes of
                Left err ->
                  counterexample
                    ("did not decode: " ++ mweContext err ++ ": " ++ mweMessage err)
                    (property False)
                Right back ->
                  conjoin
                    [ counterexample "decode . encode = id" (back === envelope)
                    , counterexample "bytes are stable" $
                        printSExpr (encodeMapCheckInput back) === printSExpr bytes
                    ]

-- ---------------------------------------------------------------------------
-- The envelope's single-defect refusal matrix
-- ---------------------------------------------------------------------------

-- | The committed agreement envelope, read once per property that needs it.
--
-- Every row of the matrix below is these bytes with __one__ substring replaced,
-- so the difference between an accepted and a refused envelope is exactly the
-- named defect. This is the manifest matrix's method
-- (@MapWireSpec.malformedManifests@) applied to the codec that had neither a
-- generator nor a refusal matrix, despite being the whole basis of the
-- cross-driver parity claim.
readEnvelope :: IO String
readEnvelope = readFile (agreementDir </> "map.core.sexp")

-- | Replace the first occurrence, erroring when the fixture stops containing
-- what a row edits — so a row cannot silently become a no-op that tests the
-- unmodified envelope.
replaceFirstIn :: String -> String -> String -> String
replaceFirstIn needle replacement = go
  where
    go [] = error ("MapSpec: envelope substring not found: " ++ needle)
    go text@(c : cs)
      | take (length needle) text == needle = replacement ++ drop (length needle) text
      | otherwise = c : go cs

-- | Empty out a whole section, matching parentheses to find its end.
--
-- A section like @members@ spans most of the envelope, so it cannot be named as
-- a literal the way the small ones can. Emptying it (rather than deleting it)
-- keeps the top-level arity intact, which is what makes the row test the
-- section's own emptiness check instead of the arity check above it.
emptySection :: String -> String -> String
emptySection opener = go
  where
    go [] = error ("MapSpec: envelope section not found: " ++ opener)
    go rest@(c : cs)
      | take (length opener) rest == opener =
          let body = drop (length opener) rest
           in init opener ++ ")" ++ drop (closeOf 1 body) body
      | otherwise = c : go cs

    -- How many characters of the section body to drop: everything up to and
    -- including the paren that closes the section.
    closeOf :: Int -> String -> Int
    closeOf _ [] = error ("MapSpec: unbalanced section: " ++ opener)
    closeOf depth (c : cs)
      | c == '(' = 1 + closeOf (depth + 1) cs
      | c == ')' && depth == 1 = 1
      | c == ')' = 1 + closeOf (depth - 1) cs
      | otherwise = 1 + closeOf depth cs

-- | One defect per row, named by the refusal path it reaches.
--
-- The paths here are the ones no test reached before: the arity of the
-- top-level form and of @policy@, @artifact@, @backend@, @member@, @alignment@
-- and @ref@; an unknown assertion or audit-status keyword at @envKeyword@;
-- coordinate syntax; the top-level parse error; and three of the six
-- shared-section fields.
envelopeDefects :: [(String, String -> String)]
envelopeDefects =
  [ -- Top-level form
    ("top-level form one section short", replaceFirstIn "(map-check-input@1 (policy empirical-v1) " "(map-check-input@1 ")
  , ("top-level form one section long", replaceFirstIn "(map-check-input@1 " "(map-check-input@1 (spare) ")
  , ("unknown top-level tag", replaceFirstIn "(map-check-input@1 " "(map-check-input@2 ")
  , ("top-level form is an atom", const "map-check-input@1")
  , ("top-level parse error: unbalanced", (++ ")"))
  , ("top-level parse error: two forms", (++ " (map-check-input@1)"))
  , -- policy
    ("policy section empty", replaceFirstIn "(policy empirical-v1)" "(policy)")
  , ("policy section one field long", replaceFirstIn "(policy empirical-v1)" "(policy empirical-v1 extra)")
  , ("unknown policy tag", replaceFirstIn "(policy empirical-v1)" "(policyx empirical-v1)")
  , -- backends
    ("backend one field short", replaceFirstIn "(backend nd 1)" "(backend nd)")
  , ("backend one field long", replaceFirstIn "(backend nd 1)" "(backend nd 1 2)")
  , ("unknown backend tag", replaceFirstIn "(backend nd 1)" "(backendx nd 1)")
  , ("backends not ascending", replaceFirstIn "(backends (backend nd 1))" "(backends (backend ra 1) (backend nd 1))")
  , ("backends duplicated", replaceFirstIn "(backends (backend nd 1))" "(backends (backend nd 1) (backend nd 1))")
  , -- members
    ("no members", emptySection "(members ")
  , ("duplicate member alias", replaceFirstIn "(member paper_neg neg.lara" "(member paper_pos neg.lara")
  , ("member one field short", replaceFirstIn "(member paper_pos pos.lara (artifact sha256:pos...) " "(member paper_pos pos.lara ")
  , ("unknown member tag", replaceFirstIn "(member paper_pos" "(memberx paper_pos")
  , ("malformed member alias", replaceFirstIn "(member paper_pos" "(member pa:per")
  , ("empty member path", replaceFirstIn "(member paper_pos pos.lara" "(member paper_pos \"\"")
  , -- artifact
    ("artifact section empty", replaceFirstIn "(artifact sha256:pos...)" "(artifact)")
  , ("artifact section one field long", replaceFirstIn "(artifact sha256:pos...)" "(artifact sha256:pos... sha256:b)")
  , ("unknown artifact tag", replaceFirstIn "(artifact sha256:pos...)" "(artifactx sha256:pos...)")
  , -- claims
    ( "duplicate claim name"
    , replaceFirstIn
        "(claims (claim c_pos (atom improves (con M) (con accuracy) (con D))))"
        ( "(claims (claim c_pos (atom improves (con M) (con accuracy) (con D)))"
            ++ " (claim c_pos (atom improves (con M) (con accuracy) (con D))))"
        )
    )
  , ("claim one field short", replaceFirstIn "(claim c_pos (atom improves (con M) (con accuracy) (con D)))" "(claim c_pos)")
  , -- alignment
    ("alignment one field short", replaceFirstIn " (author reviewer_r) (audit-status reviewed) (rationale \"The two" " (audit-status reviewed) (rationale \"The two")
  , ("alignment one field long", replaceFirstIn "(alignment (ref paper_pos c_pos whole)" "(alignment (spare) (ref paper_pos c_pos whole)")
  , ("unknown alignment tag", replaceFirstIn "(alignment (ref paper_pos c_pos whole)" "(alignmentx (ref paper_pos c_pos whole)")
  , ("unknown assertion keyword", replaceFirstIn "c_neg whole) different" "c_neg whole) maybe")
  , ("unknown audit-status keyword", replaceFirstIn "(audit-status reviewed)" "(audit-status pending)")
  , ("audit-status section empty", replaceFirstIn "(audit-status reviewed)" "(audit-status)")
  , ("author section one field long", replaceFirstIn "(author reviewer_r)" "(author reviewer_r reviewer_s)")
  , ("mixed selector", replaceFirstIn "(ref paper_neg c_neg whole)" "(ref paper_neg c_neg (arg 0))")
  , -- ref and coordinate
    ("ref one field short", replaceFirstIn "(ref paper_pos c_pos whole)" "(ref paper_pos c_pos)")
  , ("ref one field long", replaceFirstIn "(ref paper_pos c_pos whole)" "(ref paper_pos c_pos whole extra)")
  , ("unknown ref tag", replaceFirstIn "(ref paper_pos c_pos whole)" "(refx paper_pos c_pos whole)")
  , ("undeclared alignment alias", replaceFirstIn "(ref paper_pos c_pos whole)" "(ref paper_zzz c_pos whole)")
  , ("undeclared alignment claim", replaceFirstIn "(ref paper_pos c_pos whole)" "(ref paper_pos c_zzz whole)")
  , ("coordinate is not a NAT", replaceFirstIn "(arg 0)" "(arg x)")
  , ("coordinate is negative", replaceFirstIn "(arg 0)" "(arg -1)")
  , ("coordinate is signed", replaceFirstIn "(arg 0)" "(arg +1)")
  , ("coordinate has a leading zero", replaceFirstIn "(arg 0)" "(arg 00)")
  , ("coordinate with no target", replaceFirstIn "(arg 0)" "(arg)")
  , ("coordinate with two targets", replaceFirstIn "(arg 0)" "(arg 0 1)")
  , ("coordinate out of range", replaceFirstIn "(arg 0)" "(arg 9)")
  , ("unknown coordinate keyword", replaceFirstIn "c_pos whole)" "c_pos middle)")
  , ("whole coordinate as a list", replaceFirstIn "c_pos whole)" "c_pos (whole))")
  , -- shared sections: change ONE member's copy, so the rest disagree with it
    ("members disagree on contraries", replaceFirstIn "(contraries (contrary (apat improves" "(contraries (contrary (apat generalizes")
  , ("members disagree on exceptions", replaceFirstIn "(exceptions (exception controlled_experiment" "(exceptions (exception null_result")
  , ("members disagree on rules", replaceFirstIn "(rule controlled_experiment (mode defeasible)" "(rule controlled_experiment (mode strict)")
  , ("members disagree on the signature", replaceFirstIn "(sorts Experiment Report" "(sorts Experiment2 Report")
  ]

-- | Every single-defect envelope is refused, and the undefected bytes decode.
--
-- The positive control is the point of the second half: without it, a matrix
-- whose wrapper had broken for an unrelated reason would pass every row while
-- testing nothing.
prop_envelopeMalformedMatrix :: Property
prop_envelopeMalformedMatrix = once $ ioProperty $ do
  envelope <- readEnvelope
  pure $
    conjoin
      ( counterexample
          "the undefected envelope decodes (positive control)"
          ( case decodeMapCheckInputText envelope of
              Left err -> counterexample (mweContext err ++ ": " ++ mweMessage err) (property False)
              Right _ -> property True
          )
          : [ counterexample name $ case decodeMapCheckInputText (defect envelope) of
                Left _ -> property True
                Right _ -> counterexample "decoded, but should have been refused" (property False)
            | (name, defect) <- envelopeDefects
            ]
      )

-- | The envelope's keyword table has no spelling collision.
--
-- 'parseEnvTag' derives its reverse lookup from 'envTagToString' by enumerating
-- the type, and @Map.fromList@ keeps one value per key, so a collision would
-- break the inverse silently rather than failing to compile. The same property
-- @MapWireSpec@ states for the manifest and verdict table.
prop_envTagTableTotal :: Property
prop_envTagTableTotal =
  once $
    conjoin
      [ counterexample (envTagToString tag) (parseEnvTag (envTagToString tag) === Just tag)
      | tag <- [minBound .. maxBound] :: [EnvTag]
      ]

-- ---------------------------------------------------------------------------
-- Permutation and relabelling
-- ---------------------------------------------------------------------------

-- | Reordering the manifest's members permutes the verdict's report and changes
-- nothing else.
--
-- Concretely: @members@, @nodes@ and @statuses@ each come out in the new member
-- order — asserted as /sequences/, since each fixture member declares exactly
-- one argument and one claim, so reversing the manifest reverses each list
-- exactly — while the framework is renumbered, so a node's index moves even
-- though its handle does not. This is what a reader is entitled to assume when
-- the ordering rules say \"member order\", and it is the property the decision
-- record flagged as worth writing once a driver existed.
prop_memberPermutationPermutesReport :: Property
prop_memberPermutationPermutesReport = once $ ioProperty $ do
  sources <- readSources
  let three =
        [ ("paper_pos", "pos.lara", srcPos sources)
        , ("paper_neg", "neg.lara", srcNeg sources)
        , ("paper_other", "other.lara", srcOther sources)
        ]
      reversed = reverse three
  forward <- runFixture sources three "" ""
  backward <- runFixture sources reversed "" ""
  pure $ expectVerdict "members in manifest order" forward $ \a ->
    expectVerdict "members reversed" backward $ \b ->
      let handles v = [(aliasText (mnAlias n), let ArgId i = mnArg n in i) | n <- mvNodes v]
       in conjoin
            [ counterexample "members come out in the new member order" $
                map (aliasText . mrAlias) (NE.toList (mvMembers b))
                  === reverse (map (aliasText . mrAlias) (NE.toList (mvMembers a)))
            , -- Order, not multiset. Each of the three members declares exactly
              -- one argument and one claim, so reversing the manifest reverses
              -- these two sequences exactly; asserting the sequence is what
              -- makes "member order" in D9 a tested claim rather than a
              -- comment. Only the handle is compared, because the INDEX is
              -- expected to change — the framework is renumbered.
              counterexample "nodes come out in the new member order" $
                handles b === reverse (handles a)
            , counterexample "statuses come out in the new member order" $
                answersOf b === reverse (answersOf a)
            , -- "Renumbered" is a claim about the PAIRING, not about either
              -- list alone: both runs label 0..n-1 and both list nodes in
              -- member order, so the index sequence is identical either way.
              -- What moves is which handle holds which index.
              counterexample "the framework is renumbered" $
                property
                  ( [(h, nodeIndexInt (mnIndex n)) | (h, n) <- zip (handles b) (mvNodes b)]
                      /= [(h, nodeIndexInt (mnIndex n)) | (h, n) <- zip (handles a) (mvNodes a)]
                  )
            , counterexample "the framework has the same size" $
                length (mvLabels b) === length (mvLabels a)
            , counterexample "the same multiset of labels is assigned" $
                sort (map snd (mvLabels b)) === sort (map snd (mvLabels a))
            , counterexample "the same number of edges is drawn" $
                length (mvEdges b) === length (mvEdges a)
            ]

-- | Renaming every member alias changes every handle the verdict reports and
-- leaves every claim's status alone.
--
-- The aliases are the map's namespace, so renaming them renames every qualified
-- leaf and argument identity in the linked unit. Nothing about the answer may
-- turn on those names: what a map computes is a statement about the members'
-- propositions, and a proposition is a meaning rather than a handle.
prop_aliasRenamingPreservesStatuses :: Property
prop_aliasRenamingPreservesStatuses = once $ ioProperty $ do
  sources <- readSources
  original <- runFixture sources (conflictingPair sources) "" ""
  renamed <-
    runFixture
      sources
      [ ("x1", "pos.lara", srcPos sources)
      , ("x2", "neg.lara", srcNeg sources)
      ]
      ""
      ""
  pure $ expectVerdict "original aliases" original $ \a ->
    expectVerdict "renamed aliases" renamed $ \b ->
      conjoin
        [ counterexample "every member record's alias differs" $
            property
              ( map (aliasText . mrAlias) (NE.toList (mvMembers a))
                  /= map (aliasText . mrAlias) (NE.toList (mvMembers b))
              )
        , -- The member list is the weaker half. What makes "every handle the
          -- verdict reports" true is that the NODE table's aliases are disjoint
          -- between the two runs: those are the handles a reader resolves an
          -- argument through, and none of them survives the rename.
          counterexample "no node handle's alias survives the rename" $
            property
              ( null
                  ( [aliasText (mnAlias n) | n <- mvNodes a]
                      `intersect` [aliasText (mnAlias n) | n <- mvNodes b]
                  )
              )
        , counterexample "the claim statuses agree" $
            claimAnswersOf b === claimAnswersOf a
        , counterexample "the framework is the same shape" $
            (map snd (mvLabels b), map (\(s, t) -> (nodeIndexInt s, nodeIndexInt t)) (mvEdges b))
              === (map snd (mvLabels a), map (\(s, t) -> (nodeIndexInt s, nodeIndexInt t)) (mvEdges a))
        ]

-- | A one-member map gives that member's claims exactly the statuses its own
-- solo verdict gives them.
--
-- The base case for everything the multi-member cases say: a map with nothing
-- to link adds nothing, so any difference a larger map shows is the field's
-- doing and not the map machinery's. It is also the concrete counterpoint to
-- 'prop_singletonAndPairDisagree' below, which is where the non-monotonicity
-- lives.
prop_singletonMapMatchesSoloStatuses :: Property
prop_singletonMapMatchesSoloStatuses = once $ ioProperty $ do
  sources <- readSources
  let member = ("paper_pos", "pos.lara", srcPos sources)
  outcome <- runFixture sources [member] "" ""
  solo <- withTree (memberTree sources [member] "" "") (soloStatuses . (</> "pos.lara"))
  pure $ expectVerdict "singleton map" outcome $ \verdict ->
    counterexample "map statuses differ from the member's own" $
      [(msAtom status, msStatus status) | status <- mvStatuses verdict] === solo

-- | The same member's statuses read off its own @.lara@ check, through the
-- ordinary source pipeline the CLI uses.
soloStatuses :: FilePath -> IO [(Prop, Status)]
soloStatuses path = do
  loaded <- loadSource path
  case loaded of
    Left err -> error ("MapSpec: fixture member did not load: " ++ renderSourceLoadError err)
    Right source -> case loadedPrepared source of
      SourceRejected _ -> error "MapSpec: fixture member was rejected by policy admission"
      SourceAccepted input -> case verdictOutcome (sourceResultVerdict (runSourceCheck input)) of
        Reject _ -> error "MapSpec: fixture member does not check on its own"
        Accept{verdictStatuses = statuses} ->
          pure [(atom, published status) | (atom, status) <- statuses]
  where
    published status = case status of
      Published s -> s
      EvidenceBlocked s ->
        error ("MapSpec: fixture member has a blocked query with conditional " ++ show s)

-- | Adding the contradicting member changes the first member's status, and both
-- maps are accepted.
--
-- There is no monotonicity theorem anywhere in this development, and this is
-- the shipped-side witness for why: @c_pos@ is @justified@ alone and
-- @contested@ beside @c_neg@, with neither map rejected. Its mechanized
-- counterpart is @linkMembers_status_not_preserved@ in
-- @lean\/Lara\/Map\/Link.lean@.
prop_singletonAndPairDisagree :: Property
prop_singletonAndPairDisagree = once $ ioProperty $ do
  sources <- readSources
  alone <- runFixture sources [("paper_pos", "pos.lara", srcPos sources)] "" ""
  together <- runFixture sources (conflictingPair sources) "" ""
  pure $ expectVerdict "singleton map" alone $ \a ->
    expectVerdict "two-member map" together $ \b ->
      conjoin
        [ counterexample "alone" (lookup "c_pos" (claimAnswersOf a) === Just Justified)
        , counterexample "together" (lookup "c_pos" (claimAnswersOf b) === Just Contested)
        ]

-- ---------------------------------------------------------------------------
-- Alignments
-- ---------------------------------------------------------------------------

-- | An alignment section whose single alignment relates the two conflicting
-- members' claims, with the given coordinates and assertion.
alignmentOf :: String -> String -> String -> String
alignmentOf leftCoord rightCoord assertion =
  unwords
    [ "(alignment"
    , "(ref paper_pos c_pos " ++ leftCoord ++ ")"
    , "(ref paper_neg c_neg " ++ rightCoord ++ ")"
    , assertion
    , "(author reviewer_r) (audit-status reviewed) (rationale \"\"))"
    ]

-- | True alignments hold and the map accepts: the two claims are @different@ as
-- whole propositions, and their first argument positions are @same@ (both
-- members are about system @M@).
prop_trueAlignmentsHold :: Property
prop_trueAlignmentsHold = once $ ioProperty $ do
  sources <- readSources
  outcome <-
    runFixture
      sources
      (conflictingPair sources)
      (alignmentOf "whole" "whole" "different" ++ " " ++ alignmentOf "(arg 0)" "(arg 0)" "same")
      ""
  pure $ expectVerdict "true alignments" outcome (const (property True))

-- | A @same@ assertion about two coordinates that are not identical is a
-- rejection at the alignment's own manifest position, not a warning and not a
-- repair.
prop_falseSameAlignmentRejected :: Property
prop_falseSameAlignmentRejected = once $ ioProperty $ do
  sources <- readSources
  outcome <- runFixture sources (conflictingPair sources) (alignmentOf "whole" "whole" "same") ""
  pure $ expectReject "false same alignment" outcome $ \err -> case err of
    MRAlignmentFalse 0 _ -> True
    _ -> False

-- | A @different@ assertion about two coordinates that /are/ identical is
-- rejected too — the arm that a test asserting only the @same@ direction would
-- leave uncovered.
prop_falseDifferentAlignmentRejected :: Property
prop_falseDifferentAlignmentRejected = once $ ioProperty $ do
  sources <- readSources
  outcome <-
    runFixture sources (conflictingPair sources) (alignmentOf "(arg 0)" "(arg 0)" "different") ""
  pure $ expectReject "false different alignment" outcome $ \err -> case err of
    MRAlignmentFalse 0 _ -> True
    _ -> False

-- | The __lowest-numbered__ failing alignment is the one reported: a true
-- alignment ahead of two false ones does not shift the position, and the second
-- false one is not what is named.
prop_firstFalseAlignmentIsReported :: Property
prop_firstFalseAlignmentIsReported = once $ ioProperty $ do
  sources <- readSources
  outcome <-
    runFixture
      sources
      (conflictingPair sources)
      ( unwords
          [ alignmentOf "whole" "whole" "different" -- position 0, true
          , alignmentOf "whole" "whole" "same" -- position 1, false
          , alignmentOf "(arg 0)" "(arg 0)" "different" -- position 2, also false
          ]
      )
      ""
  pure $ expectReject "three alignments, two false" outcome $ \err -> case err of
    MRAlignmentFalse 1 _ -> True
    _ -> False

-- ---------------------------------------------------------------------------
-- Reference resolution
-- ---------------------------------------------------------------------------

-- | An alignment naming an alias no member declares is an ill-formed map.
prop_unknownAlias :: Property
prop_unknownAlias = once $ ioProperty $ do
  sources <- readSources
  outcome <-
    runFixture
      sources
      (conflictingPair sources)
      ( unwords
          [ "(alignment (ref paper_pos c_pos whole) (ref paper_absent c_neg whole) same"
          , "(author r) (audit-status unreviewed) (rationale \"\"))"
          ]
      )
      ""
  pure $ expectBoundary "unknown alias" outcome $ \err -> case err of
    MBUnknownAlias alias -> alias == aliasOf "paper_absent"
    _ -> False

-- | An alignment naming a claim the member does not declare is an ill-formed
-- map, and the diagnostic names the member as well as the claim.
prop_unknownClaim :: Property
prop_unknownClaim = once $ ioProperty $ do
  sources <- readSources
  outcome <-
    runFixture
      sources
      (conflictingPair sources)
      (alignmentOf "whole" "whole" "same" `replaceFirst` ("c_neg", "c_absent"))
      ""
  pure $ expectBoundary "unknown claim" outcome $ \err -> case err of
    MBUnknownClaim alias (PropId claim) -> alias == aliasOf "paper_neg" && claim == "c_absent"
    _ -> False

-- | An @(arg n)@ past the claim's arity is an ill-formed map, and the
-- diagnostic carries both the requested position and the arity.
prop_coordinateOutOfRange :: Property
prop_coordinateOutOfRange = once $ ioProperty $ do
  sources <- readSources
  outcome <-
    runFixture sources (conflictingPair sources) (alignmentOf "(arg 0)" "(arg 7)" "same") ""
  pure $ expectBoundary "coordinate out of range" outcome $ \err -> case err of
    MBCoordinateOutOfRange alias (PropId claim) _ arity ->
      alias == aliasOf "paper_neg" && claim == "c_neg" && arity == 3
    _ -> False

-- | A __question__ whose references mix a whole-claim selector with an argument
-- selector is an ill-formed map.
--
-- This is the case the manifest decoder deliberately leaves open: an
-- alignment's pair is refused at decode, but a question's reference list is
-- heterogeneous by construction — any number of references with any
-- selectors — so nothing before this stage has looked at it.
prop_mixedSelectorInQuestion :: Property
prop_mixedSelectorInQuestion = once $ ioProperty $ do
  sources <- readSources
  outcome <-
    runFixture
      sources
      (conflictingPair sources)
      ""
      ( unwords
          [ "(question q1 (refs (ref paper_pos c_pos whole) (ref paper_neg c_neg (arg 0)))"
          , "(nl \"mixed\"))"
          ]
      )
  pure $ expectBoundary "mixed selector in a question" outcome $ \err -> case err of
    MBMixedSelector left right -> left == aliasOf "paper_pos" && right == aliasOf "paper_neg"
    _ -> False

-- | A question's references are resolved before their selectors are compared,
-- so a question naming an undeclared claim reports /that/ rather than
-- complaining about the selector of a coordinate that does not exist.
prop_questionClaimResolvedBeforeSelector :: Property
prop_questionClaimResolvedBeforeSelector = once $ ioProperty $ do
  sources <- readSources
  outcome <-
    runFixture
      sources
      (conflictingPair sources)
      ""
      ( unwords
          [ "(question q1 (refs (ref paper_pos c_pos whole) (ref paper_neg c_absent (arg 0)))"
          , "(nl \"mixed and undeclared\"))"
          ]
      )
  pure $ expectBoundary "undeclared claim inside a mixed question" outcome $ \err -> case err of
    MBUnknownClaim alias (PropId claim) -> alias == aliasOf "paper_neg" && claim == "c_absent"
    _ -> False

-- | Reference resolution is a boundary stage and runs __before__ linking, so a
-- map that is both ill-referenced and contract-mismatched is not reported as
-- either of the /rejection/ classes.
--
-- Stated on the loaded members directly rather than through 'runMap', because
-- what is being pinned is that 'resolveReferences' alone decides it: the CLI's
-- @map-input@ door runs exactly this much and no more, and it is why an
-- envelope that gets printed is one that decodes.
prop_resolutionRunsWithoutLinking :: Property
prop_resolutionRunsWithoutLinking = once $ ioProperty $ do
  sources <- readSources
  let alignments =
        unwords
          [ "(alignment (ref paper_pos c_pos whole) (ref paper_absent c_neg whole) same"
          , "(author r) (audit-status unreviewed) (rationale \"\"))"
          ]
  loaded <-
    withTree
      (memberTree sources (conflictingPair sources) alignments "")
      (\root -> loadMap (root </> "map.laramap"))
  pure $ case loaded of
    Left err -> counterexample ("did not load: " ++ renderMapError err) (property False)
    Right members ->
      let resolved :: Either MapError [()]
          resolved = fmap (map (const ())) (resolveReferences members)
       in counterexample "resolution should refuse the undeclared alias" $
            case resolved of
              Left err@(MapBoundary (MBUnknownAlias alias)) ->
                (alias === aliasOf "paper_absent") .&&. mapErrorExitCode err === 2
              other -> counterexample (show (fmap length other)) (property False)

-- ---------------------------------------------------------------------------
-- Shared-contract disagreement, through the driver
-- ---------------------------------------------------------------------------

-- | A member whose backend selection is not the manifest's is a rejection, and
-- the field named is the backend selection.
prop_contractBackendsRejected :: Property
prop_contractBackendsRejected = once $ ioProperty $ do
  sources <- readSources
  let tree = memberTree sources (conflictingPair sources) "" ""
      swap ("map.laramap", text) =
        ("map.laramap", replaceFirst text ("(backend nd 1)", "(backend ra 1)"))
      swap entry = entry
  outcome <- withTree (map swap tree) (\root -> runMap (root </> "map.laramap"))
  pure $ expectReject "manifest selects a backend no member does" outcome $ \err -> case err of
    MRContract alias CFBackends -> alias == aliasOf "paper_pos"
    _ -> False

-- | A member running under a policy that has been __redefined under the same
-- id__ is a rejection on the policy structure.
--
-- The member is given its own copy of the policy with one contrary pair
-- deleted; the manifest still points at the pristine copy. Comparing ids alone
-- would wave this through, which is exactly why the contract compares the
-- parsed policy value.
--
-- The deleted pair is the @generalizes@ one, which no fixture member's argument
-- mentions, so the member still checks on its own under its edited policy. What
-- fails is only the agreement — which is the point: a member that is fine and a
-- map that is not.
prop_contractPolicyStructureRejected :: Property
prop_contractPolicyStructureRejected = once $ ioProperty $ do
  sources <- readSources
  let edited =
        replaceFirst
          (srcPolicy sources)
          ("contrary not_generalizes(M, Q, D) generalizes(M, Q, D)", "")
      tree =
        memberTree sources (conflictingPair sources) "" ""
          ++ [("member-a/empirical-v1.policy.lara", edited)]
      -- Move the first member into its own directory so it resolves its own
      -- (edited) policy copy while the manifest keeps the pristine one.
      relocate ("pos.lara", text) = ("member-a/pos.lara", text)
      relocate ("map.laramap", text) =
        ("map.laramap", replaceFirst text ("member paper_pos pos.lara", "member paper_pos member-a/pos.lara"))
      relocate entry = entry
  outcome <- withTree (map relocate tree) (\root -> runMap (root </> "map.laramap"))
  pure $ expectReject "member policy redefined under the same id" outcome $ \err -> case err of
    MRContract alias CFPolicyStructure -> alias == aliasOf "paper_pos"
    _ -> False

-- | A member that does not check on its own is a rejection naming that member,
-- and the map never reaches the linking stage.
prop_memberRejectionRejected :: Property
prop_memberRejectionRejected = once $ ioProperty $ do
  sources <- readSources
  let broken = replaceFirst (srcNeg sources) ("discharge adequate_power with b_e3", "")
  outcome <-
    runFixture
      sources
      [ ("paper_pos", "pos.lara", srcPos sources)
      , ("paper_neg", "neg.lara", broken)
      ]
      ""
      ""
  pure $ expectReject "member does not check on its own" outcome $ \err -> case err of
    MRMemberRejected alias _ -> alias == aliasOf "paper_neg"
    _ -> False

-- | A member declaring one claim name twice is an ill-formed map, refused
-- before any envelope is produced.
--
-- The @.lara@ frontend does not guard this — it refuses a repeated leaf,
-- argument or group id and says nothing about a repeated @claim@ id — so the
-- member checks on its own and the map is the only thing standing between it
-- and a verdict with two rows under one handle. Both doors must refuse it, and
-- @map-input@ in particular must emit nothing: an envelope carrying the
-- duplicate would be refused by both decoders, so the two drivers would
-- disagree 0 against 2 on the same map.
prop_duplicateClaimName :: Property
prop_duplicateClaimName = once $ ioProperty $ do
  outcome <- runMap "test/fixtures/map/duplicate-claim/map.laramap"
  (checkCode, checkOut, checkErr) <-
    runLara ["check", "test/fixtures/map/duplicate-claim/map.laramap"]
  (inputCode, inputOut, _) <-
    runLara ["map-input", "test/fixtures/map/duplicate-claim/map.laramap"]
  pure $
    conjoin
      [ expectBoundary "duplicate claim name" outcome $ \err -> case err of
          MBDuplicateClaim alias (PropId claim) ->
            alias == aliasOf "paper_pos" && claim == "c_pos"
          _ -> False
      , counterexample "check exits 2 with no verdict" $
          (checkCode === ExitFailure 2) .&&. (checkOut === "")
      , counterexample "and says which member and which claim" $
          property ("declares claim c_pos more than once" `isInfixOf` checkErr)
      , counterexample "map-input emits no envelope" $
          (inputCode === ExitFailure 2) .&&. (inputOut === "")
      ]

-- | Two members under one alias are refused by the manifest __decoder__, so
-- they reach the driver as a codec error rather than as a loader-stage
-- diagnostic. There is deliberately no separate constructor for it.
prop_duplicateMemberAlias :: Property
prop_duplicateMemberAlias = once $ ioProperty $ do
  sources <- readSources
  let tree = memberTree sources (conflictingPair sources) "" ""
      swap ("map.laramap", text) =
        ("map.laramap", replaceFirst text ("member paper_neg", "member paper_pos"))
      swap entry = entry
  outcome <- withTree (map swap tree) (\root -> runMap (root </> "map.laramap"))
  pure $ expectBoundary "duplicate member alias" outcome $ \err -> case err of
    MBWire _ -> True
    _ -> False

-- ---------------------------------------------------------------------------
-- The CLI door
-- ---------------------------------------------------------------------------

-- | @lara check <map.laramap>@ prints exactly the committed golden verdict and
-- exits 0. The CLI is a thin shell, so these bytes equal the in-process
-- 'runMap' + 'encodeMapVerdict' bytes plus the one trailing newline.
prop_cliMapAccept :: Property
prop_cliMapAccept = once $ ioProperty $ do
  (code, out, err) <- runLara ["check", agreementManifest]
  golden <- readFile (agreementDir </> "map.verdict.sexp")
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitSuccess)
      , counterexample "stdout is the golden verdict" (out === golden)
      , counterexample "stderr is silent on acceptance" (err === "")
      ]

-- | @lara map-input <map.laramap>@ prints exactly the committed parity envelope
-- and exits 0 — the command the conformance harness and the regeneration
-- instructions both use.
prop_cliMapInput :: Property
prop_cliMapInput = once $ ioProperty $ do
  (code, out, err) <- runLara ["map-input", agreementManifest]
  golden <- readFile (agreementDir </> "map.core.sexp")
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitSuccess)
      , counterexample "stdout is the golden envelope" (out === golden)
      , counterexample "stderr is silent" (err === "")
      ]

-- | A map rejected after the checked boundary exits 1 with nothing on stdout
-- and exactly one line on stderr — and its envelope is still derivable, which
-- is what lets the Lean driver be asked to refuse the same bytes.
prop_cliMapReject :: Property
prop_cliMapReject = once $ ioProperty $ do
  (code, out, err) <- runLara ["check", "test/fixtures/map/false-alignment/map.laramap"]
  (inputCode, inputOut, _) <- runLara ["map-input", "test/fixtures/map/false-alignment/map.laramap"]
  golden <- readFile "test/fixtures/map/false-alignment/map.core.sexp"
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitFailure 1)
      , counterexample "stdout empty" (out === "")
      , counterexample "exactly one stderr line" (length (lines err) === 1)
      , counterexample "the line names the map door" $
          property ("lara: map alignment 0" `isPrefixOf` err)
      , counterexample "map-input still succeeds" (inputCode === ExitSuccess)
      , counterexample "and prints the committed envelope" (inputOut === golden)
      ]

-- | An ill-formed map exits 2 with nothing on stdout, and __both__ doors stop
-- there: no envelope is emitted for a map whose coordinates do not resolve.
prop_cliMapBoundary :: Property
prop_cliMapBoundary = once $ ioProperty $ do
  (code, out, err) <- runLara ["check", "test/fixtures/map/unknown-claim/map.laramap"]
  (inputCode, inputOut, _) <- runLara ["map-input", "test/fixtures/map/unknown-claim/map.laramap"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitFailure 2)
      , counterexample "stdout empty" (out === "")
      , counterexample "exactly one stderr line" (length (lines err) === 1)
      , counterexample "map-input agrees" (inputCode === ExitFailure 2)
      , counterexample "map-input prints no envelope" (inputOut === "")
      ]

-- | A contract disagreement exits 1 on both doors, and no envelope is emitted:
-- the members never became linkable, so there is nothing at the checked
-- boundary to hand a second implementation.
prop_cliMapContractMismatch :: Property
prop_cliMapContractMismatch = once $ ioProperty $ do
  (code, out, err) <- runLara ["check", "test/fixtures/map/contract-mismatch/map.laramap"]
  (inputCode, inputOut, _) <- runLara ["map-input", "test/fixtures/map/contract-mismatch/map.laramap"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitFailure 1)
      , counterexample "stdout empty" (out === "")
      , counterexample "the line names the contract" $
          property ("lara: map contract:" `isPrefixOf` err)
      , counterexample "map-input agrees" (inputCode === ExitFailure 1)
      , counterexample "map-input prints no envelope" (inputOut === "")
      ]

-- | @lara deps@ on a map manifest is refused by name and exits 2 with nothing
-- on stdout. A map is a set of accepted units and the dependency report is
-- defined per unit, so what a map's report would mean is an open question this
-- door declines to answer rather than guess.
prop_cliMapDepsRefused :: Property
prop_cliMapDepsRefused = once $ ioProperty $ do
  (code, out, err) <- runLara ["deps", agreementManifest]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitFailure 2)
      , counterexample "stdout empty" (out === "")
      , counterexample "the line names the map manifest" $
          property ("is a map manifest" `isInfixOf` err)
      ]

-- | The @.sexp@ and @.lara@ doors are untouched by the map door's arrival: a
-- committed worked example still checks through both, with the same bytes.
--
-- The map arm is an added guard ahead of an unchanged fall-through, so this is
-- the standing check that the fall-through really is unchanged — including for
-- an extension no arm names, which must still reach the wire door and be
-- decided /there/ rather than as a usage error. Both of that door's arms are
-- exercised, because they are different failures behind one exit code: a path
-- it cannot open is a read failure, and readable bytes that are not a
-- @check-input\@1@ envelope are a located codec error.
prop_cliSoloDoorsUnchanged :: Property
prop_cliSoloDoorsUnchanged = once $ ioProperty $ do
  (sexpCode, sexpOut, _) <- runLara ["check", "examples/A/example.core.sexp"]
  (laraCode, laraOut, _) <- runLara ["check", "examples/A/example.lara"]
  (missingCode, missingOut, missingErr) <- runLara ["check", agreementManifest ++ ".unknown"]
  -- A READABLE file whose extension no arm names. Without this the codec arm
  -- would go unexercised and only the read-failure arm would be tested.
  (junkCode, junkOut, junkErr) <-
    withTree
      [("artifact.unknown", "(not-a-check-input 1 2 3)\n")]
      (\root -> runLara ["check", root </> "artifact.unknown"])
  pure $
    conjoin
      [ counterexample "the .sexp door still accepts" (sexpCode === ExitSuccess)
      , counterexample "the .lara door still accepts" (laraCode === ExitSuccess)
      , counterexample "and the two doors agree byte for byte" (laraOut === sexpOut)
      , counterexample "an unreadable unknown extension reaches the wire door" $
          (missingCode === ExitFailure 2) .&&. (missingOut === "")
      , counterexample "and fails there as a read failure, not a usage error" $
          property ("lara: cannot read" `isPrefixOf` missingErr)
      , counterexample "a readable unknown extension reaches the wire door" $
          (junkCode === ExitFailure 2) .&&. (junkOut === "")
      , counterexample "and fails there as a located codec error" $
          property ("lara: codec error at " `isPrefixOf` junkErr)
      ]

-- ---------------------------------------------------------------------------
-- Small string helpers
-- ---------------------------------------------------------------------------

-- | Replace the first occurrence of @needle@ with @replacement@. A test-fixture
-- edit, deliberately not a general rewriter: it @error@s when the needle is
-- absent, so a fixture that stopped containing what a test edits fails loudly
-- instead of silently testing the unedited text.
replaceFirst :: String -> (String, String) -> String
replaceFirst haystack (needle, replacement) = go haystack
  where
    go [] = error ("MapSpec: fixture does not contain " ++ show needle)
    go rest@(c : cs)
      | needle `isPrefixOf` rest = replacement ++ drop (length needle) rest
      | otherwise = c : go cs

-- ---------------------------------------------------------------------------
-- Registry
-- ---------------------------------------------------------------------------

mapSpecProps :: [(String, IO Result)]
mapSpecProps =
  [ ("map agreement anchor accepts", quickCheckResult prop_agreementMapAccepts)
  , ("map verdict ordering is canonical", quickCheckResult prop_verdictOrderingIsCanonical)
  , ("map run is deterministic", quickCheckResult prop_mapIsDeterministic)
  , ("map verdict golden is fresh", quickCheckResult prop_verdictGoldenIsFresh)
  , ("map parity envelope is fresh", quickCheckResult prop_envelopeIsFresh)
  , ("map envelope mirrors loaded members", quickCheckResult prop_envelopeMirrorsLoadedMembers)
  , ("map envelope codec round-trips", quickCheckResult prop_envelopeRoundTrips)
  , ("map verdict codec round-trips", quickCheckResult prop_verdictRoundTrips)
  , ("map malformed envelopes are refused", quickCheckResult prop_malformedEnvelopesAreRefused)
  , ("map envelope single-defect matrix", quickCheckResult prop_envelopeMalformedMatrix)
  , ("map envelope generator round trip", quickCheckResult prop_envelopeGeneratedRoundTrips)
  , ("map envelope tag table is total", quickCheckResult prop_envTagTableTotal)
  , ("map member permutation permutes the report", quickCheckResult prop_memberPermutationPermutesReport)
  , ("map alias renaming preserves statuses", quickCheckResult prop_aliasRenamingPreservesStatuses)
  , ("map singleton matches solo statuses", quickCheckResult prop_singletonMapMatchesSoloStatuses)
  , ("map singleton and pair disagree", quickCheckResult prop_singletonAndPairDisagree)
  , ("map true alignments hold", quickCheckResult prop_trueAlignmentsHold)
  , ("map false same alignment rejected", quickCheckResult prop_falseSameAlignmentRejected)
  , ("map false different alignment rejected", quickCheckResult prop_falseDifferentAlignmentRejected)
  , ("map first false alignment is reported", quickCheckResult prop_firstFalseAlignmentIsReported)
  , ("map unknown alias refused", quickCheckResult prop_unknownAlias)
  , ("map unknown claim refused", quickCheckResult prop_unknownClaim)
  , ("map coordinate out of range refused", quickCheckResult prop_coordinateOutOfRange)
  , ("map mixed selector in a question refused", quickCheckResult prop_mixedSelectorInQuestion)
  , ("map question claim resolved before selector", quickCheckResult prop_questionClaimResolvedBeforeSelector)
  , ("map resolution runs without linking", quickCheckResult prop_resolutionRunsWithoutLinking)
  , ("map contract backends disagreement rejected", quickCheckResult prop_contractBackendsRejected)
  , ("map contract policy structure rejected", quickCheckResult prop_contractPolicyStructureRejected)
  , ("map member rejection rejected", quickCheckResult prop_memberRejectionRejected)
  , ("map duplicate member alias refused", quickCheckResult prop_duplicateMemberAlias)
  , ("map duplicate claim name refused", quickCheckResult prop_duplicateClaimName)
  , ("map cli accepts and prints the golden", quickCheckResult prop_cliMapAccept)
  , ("map cli map-input prints the envelope", quickCheckResult prop_cliMapInput)
  , ("map cli rejection exits 1", quickCheckResult prop_cliMapReject)
  , ("map cli boundary exits 2", quickCheckResult prop_cliMapBoundary)
  , ("map cli contract mismatch exits 1", quickCheckResult prop_cliMapContractMismatch)
  , ("map cli deps on a manifest is refused", quickCheckResult prop_cliMapDepsRefused)
  , ("map cli solo doors unchanged", quickCheckResult prop_cliSoloDoorsUnchanged)
  ]
