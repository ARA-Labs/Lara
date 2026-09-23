-- | Ground-truth tests for the map's loading stage ("Lara.Map.Load") and for
-- the source-loading seam it shares with the CLI ("Lara.Source.Load").
--
-- Four things are pinned here, and they are the four the later stages assume:
--
--   * __path resolution is against the manifest, not the process__ — a member
--     declared relatively, absolutely, or through a parent directory resolves to
--     the same file, and the file that reaches the checker is the one under the
--     manifest's directory rather than one under the test runner's;
--   * __one file is one member__ — two aliases naming one file, including
--     through a symlink, are refused before any member is loaded;
--   * __the shared contract compares structures, not names__ — a policy that
--     differs only in comments and whitespace is accepted, and a policy
--     redefined under the same id is rejected;
--   * __nothing linkable escapes an admission audit__ — a quarantined member, an
--     admission-rejected member, a solo rejection, and an unknown backend all
--     stop at this stage, which is what makes @evidence-blocked@ unreachable in
--     a composite verdict.
--
-- The fixtures are built from the committed @examples\/A@ and @examples\/B@
-- trees, which share one @empirical-v1.policy.lara@ byte for byte and therefore
-- form a real two-member map. Each test copies them into a fresh temporary
-- directory and edits only the one thing it is about, so a failure names a
-- single cause. The suite runs from the package root (as @cabal test@ does), the
-- same assumption "CliSpec" and "DifferentialSpec" rely on.
--
-- __Nothing here asserts a cross-run cache.__ 'prop_mapUnchangedMtimeIsReread'
-- is the standing check that there is none: a valid edit whose modification time
-- and declared paper label are both unchanged is still seen, because a map is a
-- recheck of current bytes and consults no staleness signal.
module MapLoadSpec (mapLoadSpecProps) where

import Data.List (isInfixOf, isPrefixOf, sort)
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromMaybe)
import System.Directory
  ( createDirectoryIfMissing
  , getModificationTime
  , setModificationTime
  )
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Posix.Files (createSymbolicLink)
import System.Process (readProcessWithExitCode)
import Test.QuickCheck

import Lara.AST (BackendId (..), Digest (..), PolicyId (..), PropId (..))
import Lara.Elaborate
  ( PreparedSource (..)
  , runSourceCheck
  , sourceResultVerdict
  )
import Lara.Map.Load
  ( CheckedMembers
  , checkedMembers
  , cmAlias
  , cmArtifact
  , cmClaims
  , cmDeclaredPath
  , cmReplayId
  , loadMap
  )
import Lara.Map.Types
  ( ContractField (..)
  , MapBoundaryError (..)
  , MapError (..)
  , MapRejectError (..)
  , MemberAlias
  , aliasText
  , declaredPathText
  , mapErrorExitCode
  , mkMemberAlias
  , renderMapError
  )
import Lara.Replay (replayBackends)
import Lara.Source.Load
  ( SourceLoadError (..)
  , loadSource
  , loadedPrepared
  , newSourceCache
  , readCachedFile
  , renderSourceLoadError
  )
import qualified Lara.TempTree as TempTree
import Lara.Wire (encodeVerdict, printSExpr)

-- ---------------------------------------------------------------------------
-- Fixture helpers
-- ---------------------------------------------------------------------------

-- | A member alias the fixture author asserts is well formed. The @error@ is a
-- test-authoring bug, never a decode path.
aliasOf :: String -> MemberAlias
aliasOf name =
  fromMaybe (error ("MapLoadSpec: malformed fixture alias " ++ show name)) (mkMemberAlias name)

-- | Build a directory tree from @(relative path, contents)@ pairs, run the body
-- over its root, then remove it.
--
-- The root is under the system temp directory, which is where the /paths
-- resolve against the manifest/ tests get their force: the process working
-- directory is the package root, so a member path that resolves at all can only
-- have been resolved against the manifest's own directory. The directory is
-- reserved, not derived — see "Lara.TempTree".
withTree :: [(FilePath, String)] -> (FilePath -> IO a) -> IO a
withTree = TempTree.withTree "lara-map"

-- | The committed two-member fixture sources: @examples\/A@, @examples\/B@, and
-- the policy file they share byte for byte.
data Sources = Sources
  { srcPaperA :: String
  , srcPaperB :: String
  , srcPolicy :: String
  }

readSources :: IO Sources
readSources =
  Sources
    <$> readFile "examples/A/example.lara"
    <*> readFile "examples/B/example.lara"
    <*> readFile "examples/A/empirical-v1.policy.lara"

-- | The standard tree: a manifest at the root, the contract policy beside it,
-- and the two members in their own directories with their own policy copies.
abTree :: Sources -> String -> [(FilePath, String)]
abTree sources manifest =
  [ ("map.laramap", manifest)
  , ("empirical-v1.policy.lara", srcPolicy sources)
  , ("a/example.lara", srcPaperA sources)
  , ("a/empirical-v1.policy.lara", srcPolicy sources)
  , ("b/example.lara", srcPaperB sources)
  , ("b/empirical-v1.policy.lara", srcPolicy sources)
  ]

-- | A @lara-map\@1@ manifest over the given backend and member sections.
manifestWith :: String -> String -> String
manifestWith backends members =
  unlines
    [ "(lara-map@1"
    , "  (policy empirical-v1 empirical-v1.policy.lara)"
    , "  (backends " ++ backends ++ ")"
    , "  (members " ++ members ++ ")"
    , "  (alignments)"
    , "  (questions))"
    ]

-- | The two-member manifest every positive control uses.
abManifest :: String
abManifest =
  manifestWith
    "(backend nd 1)"
    "(member paper_a a/example.lara) (member paper_b b/example.lara)"

-- | The one-member manifest the singleton tests use.
soloManifest :: String
soloManifest = manifestWith "(backend nd 1)" "(member paper_a a/example.lara)"

-- ---------------------------------------------------------------------------
-- Outcome assertions
-- ---------------------------------------------------------------------------

-- | Show a load outcome for a counterexample: the diagnostic line an operator
-- would read, or the aliases that loaded.
describe :: Either MapError CheckedMembers -> String
describe = either renderMapError (\loaded -> "loaded " ++ show (aliasesOf loaded))

aliasesOf :: CheckedMembers -> [String]
aliasesOf = map (aliasText . cmAlias) . NE.toList . checkedMembers

-- | The outcome is an ill-formed-map diagnostic matching the predicate, and it
-- exits 2. The exit code is asserted with the classification because the pair is
-- the contract: a boundary error that exited 1 would be a boundary error nobody
-- could act on.
expectBoundary :: String -> Either MapError CheckedMembers -> (MapBoundaryError -> Bool) -> Property
expectBoundary what outcome matches =
  counterexample (what ++ ": got " ++ describe outcome) $
    case outcome of
      Left err@(MapBoundary boundary) -> matches boundary .&&. mapErrorExitCode err === 2
      _ -> property False

-- | The outcome is a rejected-map diagnostic matching the predicate, and it
-- exits 1.
expectReject :: String -> Either MapError CheckedMembers -> (MapRejectError -> Bool) -> Property
expectReject what outcome matches =
  counterexample (what ++ ": got " ++ describe outcome) $
    case outcome of
      Left err@(MapReject rejected) -> matches rejected .&&. mapErrorExitCode err === 1
      _ -> property False

-- | The outcome loaded, and the body has something to say about it.
expectLoaded :: String -> Either MapError CheckedMembers -> (CheckedMembers -> Property) -> Property
expectLoaded what outcome body =
  counterexample (what ++ ": got " ++ describe outcome) $
    case outcome of
      Right loaded -> body loaded
      Left _ -> property False

-- ---------------------------------------------------------------------------
-- The happy path
-- ---------------------------------------------------------------------------

-- | An admission-clean singleton map loads, and every field the linking stage
-- reads is the one the member declared.
--
-- The declared path is asserted to be the __manifest's spelling__ and not the
-- absolute path the loader opened: that is the property that makes two runs from
-- different directories produce byte-identical verdicts, and it is enforced by
-- 'Lara.Map.Types.DeclaredPath' being a type a resolved 'FilePath' cannot
-- inhabit. The artifact digest is the member's own declared one, carried through
-- unchanged — the map computes none.
prop_mapSingletonLoads :: Property
prop_mapSingletonLoads = once $ ioProperty $ do
  sources <- readSources
  outcome <- withTree (abTree sources soloManifest) (\root -> loadMap (root </> "map.laramap"))
  pure $
    expectLoaded "admission-clean singleton" outcome $ \loaded ->
      case NE.toList (checkedMembers loaded) of
        [member] ->
          conjoin
            [ counterexample "alias" (cmAlias member === aliasOf "paper_a")
            , counterexample "manifest-spelled path" $
                declaredPathText (cmDeclaredPath member) === "a/example.lara"
            , counterexample "the member's own declared artifact digest" $
                cmArtifact member === Digest "sha256:aaaa..."
            , counterexample "claims, in declaration order" $
                map fst (cmClaims member) === [PropId "c1"]
            , counterexample "the member's selected backends" $
                replayBackends (cmReplayId member) === [(BackendId "nd", "1")]
            ]
        members -> counterexample "expected exactly one member" (length members === 1)

-- | The two-member map loads, in manifest order, with each member's own claims
-- in that member's own declaration order.
--
-- Order is the whole assertion: the composite verdict's @members@, @nodes@, and
-- @statuses@ sections are all keyed by it, so a loader that returned members in
-- any other order would silently reorder a verdict.
prop_mapMembersInManifestOrder :: Property
prop_mapMembersInManifestOrder = once $ ioProperty $ do
  sources <- readSources
  outcome <- withTree (abTree sources abManifest) (\root -> loadMap (root </> "map.laramap"))
  pure $
    expectLoaded "two-member map" outcome $ \loaded ->
      conjoin
        [ counterexample "manifest order" (aliasesOf loaded === ["paper_a", "paper_b"])
        , counterexample "per-member claim declaration order" $
            map (map fst . cmClaims) (NE.toList (checkedMembers loaded))
              === [[PropId "c1"], [PropId "c_pos", PropId "c_neg"]]
        , counterexample "each member's own artifact digest" $
            map cmArtifact (NE.toList (checkedMembers loaded))
              === [Digest "sha256:aaaa...", Digest "sha256:bbbb..."]
        ]

-- ---------------------------------------------------------------------------
-- Path resolution
-- ---------------------------------------------------------------------------

-- | A member spelled relatively, absolutely, or through a parent directory all
-- resolve to one file — and all report the spelling the manifest used.
--
-- The parent-relative case is the sharp one: the manifest sits in a
-- subdirectory and reaches back out with @..@, which can only work if resolution
-- is anchored at the manifest's own directory. The process working directory is
-- the package root throughout, so none of these paths resolves against it.
prop_mapPathSpellings :: Property
prop_mapPathSpellings = once $ ioProperty $ do
  sources <- readSources
  relative <-
    withTree (abTree sources soloManifest) (\root -> loadMap (root </> "map.laramap"))
  absolute <- withTree (abTree sources soloManifest) $ \root -> do
    let manifest = manifestWith "(backend nd 1)" ("(member paper_a " ++ (root </> "a/example.lara") ++ ")")
    writeFile (root </> "map.laramap") manifest
    loadMap (root </> "map.laramap")
  parent <- withTree (abTree sources soloManifest) $ \root -> do
    createDirectoryIfMissing True (root </> "maps")
    writeFile (root </> "maps/map.laramap") (manifestWith "(backend nd 1)" "(member paper_a ../a/example.lara)")
    writeFile (root </> "maps/empirical-v1.policy.lara") (srcPolicy sources)
    loadMap (root </> "maps/map.laramap")
  pure $
    conjoin
      [ expectLoaded "relative spelling" relative (declaresPath "a/example.lara")
      , expectLoaded "absolute spelling" absolute (const (property True))
      , expectLoaded "parent-relative spelling" parent (declaresPath "../a/example.lara")
      ]
  where
    declaresPath expected loaded =
      counterexample "the verdict-facing path is the manifest's spelling" $
        map (declaredPathText . cmDeclaredPath) (NE.toList (checkedMembers loaded)) === [expected]

-- | A member path that resolves to nothing is the map's own boundary error, not
-- a member-attributed one: the operator is told which resolved path to go look
-- at, because the alias alone would not say where the loader looked.
prop_mapMissingMember :: Property
prop_mapMissingMember = once $ ioProperty $ do
  sources <- readSources
  outcome <- withTree (abTree sources (manifestWith "(backend nd 1)" "(member paper_a a/gone.lara)")) $
    \root -> loadMap (root </> "map.laramap")
  pure $
    expectBoundary "missing member file" outcome $ \boundary ->
      case boundary of
        MBUnreadable path _ -> "a/gone.lara" `isInfixOf` path
        _ -> False

-- | A manifest that is not there at all is the same class of failure, reported
-- before anything else can run.
prop_mapMissingManifest :: Property
prop_mapMissingManifest = once $ ioProperty $ do
  outcome <- withTree [] (\root -> loadMap (root </> "absent.laramap"))
  pure $
    expectBoundary "missing manifest" outcome $ \boundary ->
      case boundary of
        MBUnreadable path _ -> "absent.laramap" `isInfixOf` path
        _ -> False

-- | A manifest whose own bytes do not decode is a codec error, and — per the
-- decision record's D10 — so are the two rules the /decoder/ owns outright: an
-- empty member list and a duplicate alias. Neither has a loader-stage
-- constructor, and this is the standing check that neither grows one.
prop_mapDecoderOwnedFailures :: Property
prop_mapDecoderOwnedFailures = once $ ioProperty $ do
  sources <- readSources
  let cases =
        [ ("malformed", "(lara-map@1 (policy")
        , ("empty members", manifestWith "(backend nd 1)" "")
        , ( "duplicate alias"
          , manifestWith "(backend nd 1)" "(member paper_a a/example.lara) (member paper_a b/example.lara)"
          )
        ]
  outcomes <- mapM (run sources) cases
  pure (conjoin [expectBoundary what outcome isWire | ((what, _), outcome) <- zip cases outcomes])
  where
    run sources (_, manifest) =
      withTree (abTree sources manifest) (\root -> loadMap (root </> "map.laramap"))
    isWire boundary = case boundary of
      MBWire _ -> True
      _ -> False

-- | A manifest that names one policy id beside a policy file declaring another
-- is reported once, at the manifest's own boundary.
--
-- It is deliberately __not__ a codec error: the bytes decoded perfectly and the
-- manifest is internally inconsistent, not malformed. And it is deliberately
-- not left to the contract check, which would blame every member in turn for a
-- disagreement none of them caused — the assertion below is that a map whose
-- two members are both perfectly good still fails here, and names the two
-- policy ids rather than a member.
prop_mapManifestPolicyMismatch :: Property
prop_mapManifestPolicyMismatch = once $ ioProperty $ do
  sources <- readSources
  let renamed = replaceFirst "policy empirical-v1" "policy other-v1" (srcPolicy sources)
      tree =
        [ (path, if path == "empirical-v1.policy.lara" then renamed else contents)
        | (path, contents) <- abTree sources abManifest
        ]
  outcome <- withTree tree (\root -> loadMap (root </> "map.laramap"))
  pure $
    conjoin
      [ counterexample "the rename edit applied" (renamed /= srcPolicy sources)
      , expectBoundary "manifest and its policy file disagree" outcome $ \boundary ->
          case boundary of
            MBManifestPolicyMismatch declared actual ->
              declared == PolicyId "empirical-v1" && actual == PolicyId "other-v1"
            _ -> False
      ]

-- ---------------------------------------------------------------------------
-- One file is one member
-- ---------------------------------------------------------------------------

-- | Two aliases that resolve to one file are refused, whether they spell it
-- identically or reach it through a symlink.
--
-- Only the loader can catch the symlink case: the codec deliberately never
-- resolves a path, so to it @a\/example.lara@ and @link.lara@ are two different
-- manifests entries. The check uses the same canonical-path identity the read
-- cache uses, so a pair it declares distinct is also a pair it reads twice.
prop_mapDuplicatePaths :: Property
prop_mapDuplicatePaths = once $ ioProperty $ do
  sources <- readSources
  identical <- withTree (abTree sources duplicateSpellingManifest) $
    \root -> loadMap (root </> "map.laramap")
  symlinked <- withTree (abTree sources symlinkManifest) $ \root -> do
    createSymbolicLink (root </> "a/example.lara") (root </> "link.lara")
    loadMap (root </> "map.laramap")
  pure $
    conjoin
      [ expectBoundary "one file, two identical spellings" identical (namesBoth "paper_a" "paper_b")
      , expectBoundary "one file, reached through a symlink" symlinked (namesBoth "paper_a" "paper_b")
      ]
  where
    duplicateSpellingManifest =
      manifestWith
        "(backend nd 1)"
        "(member paper_a a/example.lara) (member paper_b a/example.lara)"
    symlinkManifest =
      manifestWith
        "(backend nd 1)"
        "(member paper_a a/example.lara) (member paper_b link.lara)"
    -- The reported path is the __shared resolved file__: for the symlink pair
    -- the two aliases spell different things, so a member's own spelling could
    -- not be true of both, and only the canonical target names what collided.
    namesBoth first second boundary = case boundary of
      MBDuplicatePath earlier later shared ->
        aliasText earlier == first
          && aliasText later == second
          && "a/example.lara" `isInfixOf` shared
      _ -> False

-- ---------------------------------------------------------------------------
-- The shared contract
-- ---------------------------------------------------------------------------

-- | A member whose policy file differs from the manifest's only in comments and
-- blank lines is accepted.
--
-- This is why the contract compares __parsed__ policies: after parsing, comments
-- and whitespace are gone, so a member that reformatted its copy of a shared
-- policy still joins the map. Rejecting it would make the contract a check on
-- bytes nobody promised to keep identical.
prop_mapPolicyFormattingOnly :: Property
prop_mapPolicyFormattingOnly = once $ ioProperty $ do
  sources <- readSources
  let reformatted = "# a comment the manifest's copy does not have\n\n" ++ srcPolicy sources ++ "\n\n"
      tree =
        [ (path, if path == "a/empirical-v1.policy.lara" then reformatted else contents)
        | (path, contents) <- abTree sources soloManifest
        ]
  outcome <- withTree tree (\root -> loadMap (root </> "map.laramap"))
  pure (expectLoaded "formatting-only policy difference" outcome (const (property True)))

-- | A member whose policy differs in meaning from the manifest's, under the
-- same policy id, is rejected on @CFPolicyStructure@ — the failure comparing
-- ids alone would wave through, and the reason the contract exists at all.
--
-- The edit deletes the whole @null_result@ __rule block__, which is a change to
-- what the checker will accept and not merely a widening of Σ: without it
-- @not_improves@ has no defeasible route at all.
--
-- It is deleted from the __manifest's__ copy, and that side matters. Deleting
-- it from the member's copy would break the member's own elaboration — example
-- A's @d3@ is built @by null_result@ — and the map would then report
-- 'MBMemberSource', testing the wrong thing entirely. Removing it from the
-- contract instead leaves the member elaborating cleanly under its own complete
-- policy and isolates exactly the disagreement under test: the map declares a
-- policy this member did not run under.
prop_mapPolicyRedefinition :: Property
prop_mapPolicyRedefinition = once $ ioProperty $ do
  sources <- readSources
  let trimmed = deleteBlock "rule null_result" "# --- Conflict" (srcPolicy sources)
      tree =
        [ (path, if path == "empirical-v1.policy.lara" then trimmed else contents)
        | (path, contents) <- abTree sources soloManifest
        ]
  outcome <- withTree tree (\root -> loadMap (root </> "map.laramap"))
  pure $
    conjoin
      [ counterexample "the rule block was actually deleted" $
          conjoin
            [ counterexample "shorter than the original" (property (length trimmed < length (srcPolicy sources)))
            , counterexample "null_result is gone" $
                property (not ("rule null_result" `isInfixOf` trimmed))
            , counterexample "the rest of the policy survives" $
                property ("rule controlled_experiment" `isInfixOf` trimmed)
            ]
      , expectReject "policy redefined under a shared id" outcome $ \rejected ->
          case rejected of
            MRContract alias field -> aliasText alias == "paper_a" && field == CFPolicyStructure
            _ -> False
      ]

-- | A member whose theory table changes payload under an unchanged label is
-- rejected.
--
-- The reported field is @CFPolicyStructure@, not @CFTheories@, and that is the
-- documented precedence rather than a surprise: a theory table lives inside the
-- policy, so changing a payload changes the parsed policy, and the contract
-- reports the most basic field a member disagrees on. What this pins is the
-- outcome the design cares about — a payload change under a shared label does
-- not join the map — and it is a standing check that the theory payload is
-- compared at all, which comparing theory /labels/ (as replay identity does)
-- would not do.
prop_mapTheoryPayloadChange :: Property
prop_mapTheoryPayloadChange = once $ ioProperty $ do
  program <- readFile "examples/S1/example.lara"
  policy <- readFile "examples/S1/strict-v1.policy.lara"
  let manifest =
        unlines
          [ "(lara-map@1"
          , "  (policy strict-v1 strict-v1.policy.lara)"
          , "  (backends (backend nd 1))"
          , "  (members (member paper_s a/example.lara))"
          , "  (alignments)"
          , "  (questions))"
          ]
      repayloaded = replaceFirst "theory sha256:strict-v1-theory-0 = []" theoryWithPayload policy
      theoryWithPayload = "theory sha256:strict-v1-theory-0 = [ holds(safety_invariant, D) ]"
  clean <-
    withTree
      [ ("map.laramap", manifest)
      , ("strict-v1.policy.lara", policy)
      , ("a/example.lara", program)
      , ("a/strict-v1.policy.lara", policy)
      ]
      (\root -> loadMap (root </> "map.laramap"))
  changed <-
    withTree
      [ ("map.laramap", manifest)
      , ("strict-v1.policy.lara", policy)
      , ("a/example.lara", program)
      , ("a/strict-v1.policy.lara", repayloaded)
      ]
      (\root -> loadMap (root </> "map.laramap"))
  pure $
    conjoin
      [ counterexample "the unedited control loads" $
          expectLoaded "S1 singleton" clean (const (property True))
      , counterexample "the payload edit is a real edit" $
          counterexample "theory line not found in the fixture" (repayloaded /= policy)
      , expectReject "theory payload changed under one label" changed $ \rejected ->
          case rejected of
            MRContract alias field -> aliasText alias == "paper_s" && field == CFPolicyStructure
            _ -> False
      ]

-- | A member declaring the wrong policy id disagrees on @CFPolicyId@, the most
-- basic field, before anything structural is compared.
prop_mapPolicyIdMismatch :: Property
prop_mapPolicyIdMismatch = once $ ioProperty $ do
  sources <- readSources
  let renamed = replaceFirst "policy empirical-v1" "policy other-v1" (srcPaperA sources)
      renamedPolicy = replaceFirst "policy empirical-v1" "policy other-v1" (srcPolicy sources)
  outcome <-
    withTree
      [ ("map.laramap", soloManifest)
      , ("empirical-v1.policy.lara", srcPolicy sources)
      , ("a/example.lara", renamed)
      , ("a/other-v1.policy.lara", renamedPolicy)
      ]
      (\root -> loadMap (root </> "map.laramap"))
  pure $
    expectReject "member declares a different policy" outcome $ \rejected ->
      case rejected of
        MRContract alias field -> aliasText alias == "paper_a" && field == CFPolicyId
        _ -> False

-- | __The backend comparison is sorted, not positional__ (design amendment A1).
--
-- The manifest is required to be canonically ascending, but a member's
-- @use backends@ list is passed through in author declaration order. A member
-- written @[ra\@1, nd\@1]@ against a manifest spelling @(backend nd 1)
-- (backend ra 1)@ must therefore __load__: backend selection is a set, and a
-- positional comparison would make that member unable to join any map at all.
-- This test fails loudly if anyone "fixes" the comparison back to positional.
prop_mapBackendSelectionIsASet :: Property
prop_mapBackendSelectionIsASet = once $ ioProperty $ do
  sources <- readSources
  let reordered = replaceFirst "use backends [nd@1]" "use backends [ra@1, nd@1]" (srcPaperA sources)
      manifest =
        manifestWith "(backend nd 1) (backend ra 1)" "(member paper_a a/example.lara)"
  outcome <-
    withTree
      [ ("map.laramap", manifest)
      , ("empirical-v1.policy.lara", srcPolicy sources)
      , ("a/example.lara", reordered)
      , ("a/empirical-v1.policy.lara", srcPolicy sources)
      ]
      (\root -> loadMap (root </> "map.laramap"))
  pure $
    conjoin
      [ counterexample "the reorder edit applied" (reordered /= srcPaperA sources)
      , expectLoaded "declaration order carries no meaning" outcome (const (property True))
      ]

-- | A member selecting a backend the manifest does not list disagrees on
-- @CFBackends@.
prop_mapBackendSelectionMismatch :: Property
prop_mapBackendSelectionMismatch = once $ ioProperty $ do
  sources <- readSources
  let extra = replaceFirst "use backends [nd@1]" "use backends [nd@1, ra@1]" (srcPaperA sources)
      tree =
        [ (path, if path == "a/example.lara" then extra else contents)
        | (path, contents) <- abTree sources soloManifest
        ]
  outcome <- withTree tree (\root -> loadMap (root </> "map.laramap"))
  pure $
    expectReject "member selects a backend the manifest does not" outcome $ \rejected ->
      case rejected of
        MRContract alias field -> aliasText alias == "paper_a" && field == CFBackends
        _ -> False

-- | __The contract check outranks both admission outcomes.__
--
-- A member can be contract-mismatched and policy-quarantined at the same time,
-- and this is the fixture that makes it so: the member's policy copy carries an
-- @admission { (observed, ai-executed) = quarantine }@ row that the manifest's
-- copy lacks, which is simultaneously a @CFPolicyStructure@ disagreement and a
-- quarantine of the member's own leaves.
--
-- The documented precedence says such a member reports 'MRContract', and it is
-- the right answer on the merits: the quarantine was decided by an admission
-- table that is not the map's contract, so reporting it would name a policy the
-- map does not use. Before the contract check was split into a parsed-source
-- half and an elaborated half, this member reported 'MRUnsupportedAdmission'
-- instead — so this property is the regression guard for that split.
prop_mapContractOutranksQuarantine :: Property
prop_mapContractOutranksQuarantine = once $ ioProperty $ do
  sources <- readSources
  let gated = srcPolicy sources ++ "\nadmission { (observed, ai-executed) = quarantine }\n"
      tree =
        [ (path, if path == "a/empirical-v1.policy.lara" then gated else contents)
        | (path, contents) <- abTree sources soloManifest
        ]
  outcome <- withTree tree (\root -> loadMap (root </> "map.laramap"))
  pure $
    expectReject "quarantined AND contract-mismatched" outcome $ \rejected ->
      case rejected of
        MRContract alias field -> aliasText alias == "paper_a" && field == CFPolicyStructure
        _ -> False

-- | The manifest's policy file, missing and malformed.
--
-- The two are attributed differently on purpose. A path __this module__
-- resolved and could not open is 'MBUnreadable', naming that resolved path. A
-- file it read and could not parse is 'MBManifestPolicySource' — deliberately
-- not an 'MBWire', because the manifest's own bytes decoded perfectly and it is
-- a different file that failed.
prop_mapManifestPolicyBoundaries :: Property
prop_mapManifestPolicyBoundaries = once $ ioProperty $ do
  sources <- readSources
  missing <-
    withTree
      [entry | entry@(path, _) <- abTree sources soloManifest, path /= "empirical-v1.policy.lara"]
      (\root -> loadMap (root </> "map.laramap"))
  malformed <- withTree
    [ (path, if path == "empirical-v1.policy.lara" then "policy\n" else contents)
    | (path, contents) <- abTree sources soloManifest
    ]
    (\root -> loadMap (root </> "map.laramap"))
  pure $
    conjoin
      [ expectBoundary "manifest policy file missing" missing $ \boundary ->
          case boundary of
            MBUnreadable path _ -> "empirical-v1.policy.lara" `isInfixOf` path
            _ -> False
      , expectBoundary "manifest policy file malformed" malformed $ \boundary ->
          case boundary of
            MBManifestPolicySource message -> "parse error" `isInfixOf` message
            _ -> False
      ]

-- | A member's own policy file, missing, is attributed to __the member__.
--
-- The path was never chosen by the map: it comes from the member's own @policy@
-- declaration through 'Lara.Source.Load.resolvePolicyPath'. An operator told
-- \"map member paper_a: cannot read policy …\" knows to open @paper_a@; the
-- same words under the map's own boundary would send them to the manifest,
-- which had nothing to do with it. Task 1's frozen diagnostic fixture already
-- expected this shape.
prop_mapMemberPolicyIsMemberAttributed :: Property
prop_mapMemberPolicyIsMemberAttributed = once $ ioProperty $ do
  sources <- readSources
  outcome <-
    withTree
      [ entry
      | entry@(path, _) <- abTree sources soloManifest
      , path /= "a/empirical-v1.policy.lara"
      ]
      (\root -> loadMap (root </> "map.laramap"))
  pure $
    expectBoundary "member policy file missing" outcome $ \boundary ->
      case boundary of
        MBMemberSource alias message ->
          aliasText alias == "paper_a" && "cannot read policy" `isInfixOf` message
        _ -> False

-- | A member that parses but is not a valid source reaches 'MBMemberSource' too.
--
-- Only the parse-error path was covered before; this exercises the third arm of
-- the source loader's error sum. The fixture points the member at a co-located
-- policy file declaring a different id than the member's @policy@ line, which
-- 'Lara.Elaborate.prepareSource' refuses as a source invalidity rather than a
-- parse failure — the member and its policy each parse fine on their own.
prop_mapMemberSourceInvalid :: Property
prop_mapMemberSourceInvalid = once $ ioProperty $ do
  sources <- readSources
  let mismatched = replaceFirst "policy empirical-v1" "policy other-v1" (srcPolicy sources)
      tree =
        [ (path, if path == "a/empirical-v1.policy.lara" then mismatched else contents)
        | (path, contents) <- abTree sources soloManifest
        ]
  outcome <- withTree tree (\root -> loadMap (root </> "map.laramap"))
  pure $
    conjoin
      [ counterexample "the id edit applied" (mismatched /= srcPolicy sources)
      , expectBoundary "member source invalid" outcome $ \boundary ->
          case boundary of
            MBMemberSource alias message ->
              aliasText alias == "paper_a" && "source invalid" `isInfixOf` message
            _ -> False
      ]

-- | __One invocation reads one file once, and a fresh invocation rereads it.__
--
-- Both halves are observed behaviourally, with no counter and no test-only API:
-- the file is __changed on disk between the two reads__, so a second read would
-- be visible as different content. Within one cache, a second request through a
-- /different spelling/ of the same path still returns the original bytes — it
-- was not reread, and the two spellings shared one entry. A fresh cache then
-- returns the new bytes, which is what makes this a per-invocation buffer and
-- not a cache in the staleness sense.
--
-- This is the sharing path the map relies on when a manifest's policy file is
-- also a member's policy file, and nothing else in the suite exercises it.
prop_sourceCacheReadsOncePerInvocation :: Property
prop_sourceCacheReadsOncePerInvocation = once $ ioProperty $ do
  (first, viaOtherSpelling, afterFreshCache) <- withTree [("d/file.txt", "original\n")] $ \root -> do
    let direct = root </> "d/file.txt"
        indirect = root </> "d" </> ".." </> "d" </> "file.txt"
    cache <- newSourceCache
    a <- readCachedFile cache direct
    writeFile direct "edited\n"
    b <- readCachedFile cache indirect
    fresh <- newSourceCache
    c <- readCachedFile fresh direct
    pure (a, b, c)
  pure $
    conjoin
      [ counterexample "first read" (either (const "<io error>") id first === "original\n")
      , counterexample "a second spelling within one cache does not reread" $
          either (const "<io error>") id viaOtherSpelling === "original\n"
      , counterexample "a fresh invocation sees the edit" $
          either (const "<io error>") id afterFreshCache === "edited\n"
      ]

-- ---------------------------------------------------------------------------
-- Nothing linkable escapes an admission audit
-- ---------------------------------------------------------------------------

-- | A member selecting a backend no registry entry supports is rejected as a
-- __member rejection__, not as a contract disagreement.
--
-- The manifest is made to agree with the member on the bogus selection
-- precisely so the contract check passes, which isolates the replay preflight:
-- the map runs each member's ordinary source check, so an unknown backend
-- reaches the map exactly as the R13 rejection the solo door would print.
prop_mapUnknownBackend :: Property
prop_mapUnknownBackend = once $ ioProperty $ do
  sources <- readSources
  let bogus = replaceFirst "use backends [nd@1]" "use backends [nosuch@1]" (srcPaperA sources)
      manifest = manifestWith "(backend nosuch 1)" "(member paper_a a/example.lara)"
  outcome <-
    withTree
      [ ("map.laramap", manifest)
      , ("empirical-v1.policy.lara", srcPolicy sources)
      , ("a/example.lara", bogus)
      , ("a/empirical-v1.policy.lara", srcPolicy sources)
      ]
      (\root -> loadMap (root </> "map.laramap"))
  pure $
    expectReject "unknown selected backend" outcome $ \rejected ->
      case rejected of
        MRMemberRejected alias _ -> aliasText alias == "paper_a"
        _ -> False

-- | A member that does not check on its own does not join a map.
--
-- The fixture is @examples\/S3@'s shape with the recheck rule's conclusion
-- strengthened from @num_le@ to @num_lt@, so the same @ord\@1@ certificate over
-- two equal cells replays false — the same artifact "CliSpec" uses to pin the
-- solo door's R13 line. A map that accepted it would be reporting on an argument
-- the checker refused.
prop_mapSoloRejectionRefused :: Property
prop_mapSoloRejectionRefused = once $ ioProperty $ do
  outcome <-
    withTree
      [ ("map.laramap", tieManifest)
      , ("p.policy.lara", ltTiePolicy)
      , ("a/art.lara", ltTieProgram)
      , ("a/p.policy.lara", ltTiePolicy)
      ]
      (\root -> loadMap (root </> "map.laramap"))
  pure $
    expectReject "member rejects on its own" outcome $ \rejected ->
      case rejected of
        MRMemberRejected alias _ -> aliasText alias == "paper_t"
        _ -> False
  where
    tieManifest =
      unlines
        [ "(lara-map@1"
        , "  (policy p p.policy.lara)"
        , "  (backends (backend ord 1))"
        , "  (members (member paper_t a/art.lara))"
        , "  (alignments)"
        , "  (questions))"
        ]

-- | A member the policy's admission table touched is refused __before__
-- anything linkable is exported — and the two ways it can be touched get two
-- different diagnostics.
--
-- A @quarantine@ row prunes support and leaves an audit behind: the member is
-- otherwise fine and it is v1 that declines to handle pruned material, so that
-- is 'MRUnsupportedAdmission'. A @reject@ row stops the source outright: the
-- member genuinely fails the policy the map checks under, so that is
-- 'MRMemberAdmissionStop'. The rendered lines are asserted to differ, because
-- the remedies differ — "this feature does not cover your artifact yet" versus
-- "fix the artifact or the policy" — and one line for two jobs would leave an
-- operator guessing which they were reading.
--
-- The manifest's contract policy carries the same admission table in both
-- cases, so neither is a contract disagreement in disguise. This is also what
-- makes @evidence-blocked@ unreachable in a composite verdict: no query in a
-- map can be blocked, because no member with pruned support gets in.
prop_mapQuarantinedMemberRefused :: Property
prop_mapQuarantinedMemberRefused = once $ ioProperty $ do
  sources <- readSources
  quarantined <- run sources "quarantine"
  refused <- run sources "reject"
  pure $
    conjoin
      [ expectReject "a quarantined member" quarantined (isUnsupported "paper_a")
      , expectReject "an admission-rejected member" refused (isAdmissionStop "paper_a")
      , counterexample "the two admission outcomes get different diagnostics" $
          fmap renderMapError (leftOf quarantined) =/= fmap renderMapError (leftOf refused)
      ]
  where
    leftOf = either Just (const Nothing)
    run sources decision = do
      let gated = srcPolicy sources ++ "\nadmission { (observed, ai-executed) = " ++ decision ++ " }\n"
      withTree
        [ ("map.laramap", soloManifest)
        , ("empirical-v1.policy.lara", gated)
        , ("a/example.lara", srcPaperA sources)
        , ("a/empirical-v1.policy.lara", gated)
        ]
        (\root -> loadMap (root </> "map.laramap"))
    isUnsupported expected rejected = case rejected of
      MRUnsupportedAdmission alias _ -> aliasText alias == expected
      _ -> False
    isAdmissionStop expected rejected = case rejected of
      MRMemberAdmissionStop alias _ -> aliasText alias == expected
      _ -> False

-- | The __group-pruning__ half of the admission gate, which
-- 'prop_mapQuarantinedMemberRefused' does not reach.
--
-- The two paths into 'MRUnsupportedAdmission' are not the same code. A policy
-- quarantine makes @sourceResultCheckInput@ return 'Left', and the map refuses
-- at that arm; a @≢@ duplicate-report group under @duplicate-reports =
-- quarantine@ prunes support while still returning 'Right', so the member
-- arrives at the /later/ gate carrying a nonempty audit. Every other admission
-- test in this module takes the first arm, and a reviewer deleting the second
-- gate outright left the whole map suite green — which is what this property
-- exists to stop.
--
-- The fixture edits one thing: it declares @group g = [e2, e3]@ over two leaves
-- whose propositions are not @≡@ (@randomized(exp_3)@ and @powered(exp_3)@), so
-- the group conflicts and both members leave @Gamma@ with a
-- @group-quarantine:g@ cause. The rendered audit is asserted to name that
-- cause, not merely to be nonempty: an audit rendered from the policy arm would
-- say @policy-quarantine@ instead, so the assertion also witnesses /which/ gate
-- fired.
prop_mapGroupPrunedMemberRefused :: Property
prop_mapGroupPrunedMemberRefused = once $ ioProperty $ do
  sources <- readSources
  let grouped = srcPaperA sources ++ "\ngroup g = [e2, e3]\n"
      policy = srcPolicy sources ++ "\nduplicate-reports = quarantine\n"
  outcome <-
    withTree
      [ ("map.laramap", soloManifest)
      , ("empirical-v1.policy.lara", policy)
      , ("a/example.lara", grouped)
      , ("a/empirical-v1.policy.lara", policy)
      ]
      (\root -> loadMap (root </> "map.laramap"))
  pure $
    conjoin
      [ counterexample "the group edit applied" (grouped /= srcPaperA sources)
      , expectReject "a group-pruned member" outcome isGroupPruned
      ]
  where
    isGroupPruned rejected = case rejected of
      MRUnsupportedAdmission alias rendered ->
        aliasText alias == "paper_a" && "group-quarantine:g" `isInfixOf` rendered
      _ -> False

-- | A member that does not parse is attributed to the member, carrying its own
-- source-boundary text.
--
-- The split matters: an unreadable file is the map's boundary ('MBUnreadable',
-- which names a resolved path), while a file the map read and could not
-- understand is the member's ('MBMemberSource', under the member's alias). An
-- operator reading the second one knows to open the member, not the manifest.
prop_mapMemberSourceBoundary :: Property
prop_mapMemberSourceBoundary = once $ ioProperty $ do
  sources <- readSources
  let tree =
        [ (path, if path == "a/example.lara" then "artifact\n" else contents)
        | (path, contents) <- abTree sources soloManifest
        ]
  outcome <- withTree tree (\root -> loadMap (root </> "map.laramap"))
  pure $
    expectBoundary "member does not parse" outcome $ \boundary ->
      case boundary of
        MBMemberSource alias message ->
          aliasText alias == "paper_a" && "parse error" `isInfixOf` message
        _ -> False

-- ---------------------------------------------------------------------------
-- A map is a recheck, not a build
-- ---------------------------------------------------------------------------

-- | A valid source edit is evaluated normally even when its modification time
-- and its declared paper label are both unchanged.
--
-- This is the standing check that no cache, digest, or staleness test has crept
-- in. The edit changes the member's declared @artifact@ digest and nothing else,
-- so the paper label the manifest and the reports key on is identical across the
-- two runs — an implementation that skipped the reread would report the first
-- digest twice, and the test would say so.
prop_mapUnchangedMtimeIsReread :: Property
prop_mapUnchangedMtimeIsReread = once $ ioProperty $ do
  sources <- readSources
  digests <- withTree (abTree sources soloManifest) $ \root -> do
    let member = root </> "a/example.lara"
    before <- loadMap (root </> "map.laramap")
    stamp <- getModificationTime member
    writeFile member (replaceFirst "sha256:aaaa..." "sha256:cccc..." (srcPaperA sources))
    setModificationTime member stamp
    after <- loadMap (root </> "map.laramap")
    pure (digestsOf before, digestsOf after)
  pure $
    counterexample "the second run must see the edited bytes" $
      digests === ([Digest "sha256:aaaa..."], [Digest "sha256:cccc..."])
  where
    digestsOf = either (const []) (map cmArtifact . NE.toList . checkedMembers)

-- ---------------------------------------------------------------------------
-- The extracted source-loading seam
-- ---------------------------------------------------------------------------

-- | The seam "Lara.Source.Load" now owns produces exactly what the CLI produces.
--
-- Both halves are pinned against the __real built binary__ (Cabal puts it on
-- @PATH@ via the test-suite's @build-tool-depends@), because the claim being
-- made is that extracting the four steps out of @app\/Main.hs@ moved no byte:
--
--   * on an accepting artifact, the verdict this seam's 'PreparedSource'
--     produces in process is byte-identical to the binary's @stdout@;
--   * on a boundary failure, @\"lara: \" ++ 'renderSourceLoadError'@ is
--     byte-identical to the binary's @stderr@ — which is the whole reason
--     'renderSourceLoadError' carries no tool-name prefix of its own.
--
-- __All five constructors, not one.__ This property is what backs the claim
-- that pulling the four load steps out of the binary changed nothing
-- observable, and it used to byte-compare exactly one 'SourceLoadError'
-- constructor (the unreadable artifact). The other four were reached only
-- through @isInfixOf@ on a prefix, which never forces the located line and
-- column — so the strongest claim this module makes rested on a fifth of the
-- sum. Each constructor gets a fixture below, and each is compared byte for
-- byte.
prop_sourceLoadSeamMatchesCli :: Property
prop_sourceLoadSeamMatchesCli = once $ ioProperty $ do
  loaded <- loadSource "examples/A/example.lara"
  (acceptCode, acceptOut, _) <- runLara ["check", "examples/A/example.lara"]
  boundaries <- mapM checkBoundary sourceLoadBoundaryCases
  pure $
    conjoin
      ( [ counterexample "the binary accepts the control" (acceptCode === ExitSuccess)
        , counterexample "in-process verdict bytes equal the CLI's stdout" $
            case fmap loadedPrepared loaded of
              Right (SourceAccepted input) ->
                (printSExpr (encodeVerdict (sourceResultVerdict (runSourceCheck input))) ++ "\n")
                  === acceptOut
              _ -> property False
        , counterexample "every SourceLoadError constructor has a case" $
            sort [name | (name, _, _) <- sourceLoadBoundaryCases]
              === sort ["SourceUnreadable", "SourceParseError", "PolicyUnreadable",
                        "PolicyParseError", "SourceInvalidError"]
        ]
          ++ boundaries
      )
  where
    -- One tree per case, so a case that stops reaching its constructor fails
    -- here rather than quietly landing on a neighbour's.
    checkBoundary (name, tree, target) = do
      (result, code, err) <- withTree tree $ \root -> do
        loadResult <- loadSource (root </> target)
        (c, _, e) <- runLara ["check", root </> target]
        pure (loadResult, c, e)
      pure . counterexample name $
        conjoin
          [ counterexample "the binary stops at its boundary" (code === ExitFailure 2)
          , counterexample "the fixture reaches the constructor it names" $
              case result of
                Left loadErr -> constructorName loadErr === name
                Right _ -> counterexample "the fixture loaded; it was meant to fail" (property False)
          , counterexample "boundary text equals the CLI's stderr, modulo the CLI's prefix" $
              case result of
                Left loadErr -> ("lara: " ++ renderSourceLoadError loadErr ++ "\n") === err
                Right _ -> property False
          ]

    -- Which constructor fired. Without this a case could drift onto a
    -- neighbour's arm — an unparseable artifact whose policy is also missing
    -- reports the parse error — and the loop would still pass while covering
    -- four constructors under five names.
    constructorName loadErr = case loadErr of
      SourceUnreadable{} -> "SourceUnreadable"
      SourceParseError{} -> "SourceParseError"
      PolicyUnreadable{} -> "PolicyUnreadable"
      PolicyParseError{} -> "PolicyParseError"
      SourceInvalidError{} -> "SourceInvalidError"

-- | A tree and a target path per 'SourceLoadError' constructor.
--
-- Named by the constructor each is meant to reach, and the names are asserted
-- to cover the sum — a constructor added without a case fails the property
-- rather than being silently uncovered.
sourceLoadBoundaryCases :: [(String, [(FilePath, String)], FilePath)]
sourceLoadBoundaryCases =
  [ ("SourceUnreadable", [("other.lara", "")], "missing.lara")
  , ("SourceParseError", [("a.lara", "this is not a program\n")], "a.lara")
  ,
    ( "PolicyUnreadable"
    , [("a.lara", "artifact x at sha256:x\npolicy p\nuse backends []\n")]
    , "a.lara"
    )
  ,
    ( "PolicyParseError"
    , [ ("a.lara", "artifact x at sha256:x\npolicy p\nuse backends []\n")
      , ("p.policy.lara", "this is not a policy\n")
      ]
    , "a.lara"
    )
  ,
    ( "SourceInvalidError"
    , [ ("a.lara", "artifact x at sha256:x\npolicy other\nuse backends []\n")
      , ("other.policy.lara", "policy p\n")
      ]
    , "a.lara"
    )
  ]

-- | The real built binary; Cabal puts it on @PATH@ during @cabal test@ via the
-- test-suite's @build-tool-depends: lara:lara@.
runLara :: [String] -> IO (ExitCode, String, String)
runLara args = readProcessWithExitCode "lara" args ""

-- ---------------------------------------------------------------------------
-- Fixture text
-- ---------------------------------------------------------------------------

-- | Delete from the first occurrence of @start@ up to (not including) the first
-- occurrence of @end@ after it. Returns the text unchanged if either marker is
-- missing; callers assert that the deletion happened.
deleteBlock :: String -> String -> String -> String
deleteBlock start end text = case breakOn start text of
  Nothing -> text
  Just (before, fromStart) -> case breakOn end (drop (length start) fromStart) of
    Nothing -> text
    Just (_, fromEnd) -> before ++ fromEnd

-- | Split at the first occurrence of a needle: the text before it, and the text
-- from it onwards.
breakOn :: String -> String -> Maybe (String, String)
breakOn needle = go []
  where
    go _ [] = Nothing
    go seen text@(c : rest)
      | needle `isPrefixOf` text = Just (reverse seen, text)
      | otherwise = go (c : seen) rest

-- | Replace the first occurrence of a needle, or return the haystack unchanged.
-- Every caller that relies on the edit having happened asserts it separately.
replaceFirst :: String -> String -> String -> String
replaceFirst needle replacement = go
  where
    go [] = []
    go text@(c : rest)
      | needle `isPrefixOf` text = replacement ++ drop (length needle) text
      | otherwise = c : go rest

-- | @examples\/S3@'s artifact against a @num_lt@ rule: two equal reported cells,
-- and a strict step asking @ord\@1@ to certify that one is strictly below the
-- other. Copied from "CliSpec", which pins the solo door's diagnostic for it.
ltTieProgram :: String
ltTieProgram =
  unlines
    [ "artifact ord_tie_demo at sha256:5353535353535353535353535353535353535353535353535353535353535353"
    , "policy p"
    , "use backends [ord@1]"
    , "claim c2"
    , "  nl      = \"The reported baseline accuracy is below the reported system accuracy\""
    , "  formal  = num_lt(0.71, 0.71)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , "leaf e1 : reports(exp1, score_cell(sys_base, accuracy, imagenet_val, 0.71))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/accuracy.md#row=sys_base]"
    , "leaf e2 : reports(exp1, score_cell(sys_new, accuracy, imagenet_val, 0.71))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/accuracy.md#row=sys_new]"
    , "arg a1 : supports(c2) by beats_recheck(sys_new, sys_base, accuracy, imagenet_val, exp1, 0.71, 0.71)"
    , "  assurance = cert(ord@1, sha256:t0, (ordcmp (prem 0) (prem 1)))"
    , "status c2"
    ]

-- | @examples\/S3@'s policy with @num_le@ replaced by @num_lt@ — the one edit
-- that turns an accepting artifact into a rejecting one.
ltTiePolicy :: String
ltTiePolicy =
  unlines
    [ "policy p"
    , "sort System, Measurand, Dataset, Experiment, Cell"
    , "con sys_new : System"
    , "con sys_base : System"
    , "con accuracy : Measurand"
    , "con imagenet_val : Dataset"
    , "con exp1 : Experiment"
    , "con score_cell(System, Measurand, Dataset, Num) : Cell"
    , "pred reports(Experiment, Cell)"
    , "pred num_lt(Num, Num)"
    , "rule beats_recheck(S, B, Q, D, Exp, Sv, Bv)"
    , "  mode       = strict"
    , "  premises   = [ reports(Exp, score_cell(B, Q, D, Bv)),"
    , "                 reports(Exp, score_cell(S, Q, D, Sv)) ]"
    , "  conclusion = num_lt(Bv, Sv)"
    , "  allow-trusted = false"
    , "  certifiers = [ (ord@1, sha256:t0) ]"
    , "theory sha256:t0 = []"
    ]

-- ---------------------------------------------------------------------------
-- Registry
-- ---------------------------------------------------------------------------

mapLoadSpecProps :: [(String, IO Result)]
mapLoadSpecProps =
  [ ("map singleton loads", quickCheckResult prop_mapSingletonLoads)
  , ("map members in manifest order", quickCheckResult prop_mapMembersInManifestOrder)
  , ("map path spellings resolve against the manifest", quickCheckResult prop_mapPathSpellings)
  , ("map missing member file", quickCheckResult prop_mapMissingMember)
  , ("map missing manifest", quickCheckResult prop_mapMissingManifest)
  , ("map decoder-owned failures stay codec errors", quickCheckResult prop_mapDecoderOwnedFailures)
  , ("map manifest policy id mismatch", quickCheckResult prop_mapManifestPolicyMismatch)
  , ("map duplicate member paths", quickCheckResult prop_mapDuplicatePaths)
  , ("map accepts formatting-only policy differences", quickCheckResult prop_mapPolicyFormattingOnly)
  , ("map rejects a policy redefinition", quickCheckResult prop_mapPolicyRedefinition)
  , ("map contract outranks a quarantine", quickCheckResult prop_mapContractOutranksQuarantine)
  , ("map manifest policy boundaries", quickCheckResult prop_mapManifestPolicyBoundaries)
  , ("map member policy is member-attributed", quickCheckResult prop_mapMemberPolicyIsMemberAttributed)
  , ("map member source invalid", quickCheckResult prop_mapMemberSourceInvalid)
  , ("source cache reads once per invocation", quickCheckResult prop_sourceCacheReadsOncePerInvocation)
  , ("map rejects a theory payload change", quickCheckResult prop_mapTheoryPayloadChange)
  , ("map rejects a policy id mismatch", quickCheckResult prop_mapPolicyIdMismatch)
  , ("map backend selection is a set", quickCheckResult prop_mapBackendSelectionIsASet)
  , ("map rejects a backend selection mismatch", quickCheckResult prop_mapBackendSelectionMismatch)
  , ("map rejects an unknown backend", quickCheckResult prop_mapUnknownBackend)
  , ("map rejects a member that rejects solo", quickCheckResult prop_mapSoloRejectionRefused)
  , ("map rejects a quarantined member", quickCheckResult prop_mapQuarantinedMemberRefused)
  , ("map rejects a group-pruned member", quickCheckResult prop_mapGroupPrunedMemberRefused)
  , ("map attributes a member source boundary", quickCheckResult prop_mapMemberSourceBoundary)
  , ("map rereads an edit with an unchanged mtime", quickCheckResult prop_mapUnchangedMtimeIsReread)
  , ("source-load seam matches the CLI", quickCheckResult prop_sourceLoadSeamMatchesCli)
  ]
