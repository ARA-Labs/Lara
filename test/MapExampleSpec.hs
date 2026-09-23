-- | The shipped D3 map (@examples\/agreement-map-multi\/@) and the @--out@
-- product-file door.
--
-- "MapSpec" owns the driver's /contract/ over hand-built fixtures. This module
-- owns the one map a reader actually runs, and the three claims that make it
-- worth shipping rather than merely passing:
--
--   * __each member stands alone__ — all four @paper-{a,b,c,d}@ artifacts check
--     on their own and each one's single claim is @justified@, so nothing in
--     the composite comes from a member that needed the map to be valid
--     ('prop_membersAreSoloJustified');
--   * __the composite reproduces the legacy single-file oracle__ — the same
--     labels, the same edge set, the same four claim propositions and the same
--     four statuses as @examples\/agreement-map\/@ under the node
--     correspondence @pa=0, pb=1, pc=2, pd=3@, even though not one of those
--     edges is declared by any member ('prop_compositeMatchesLegacyOracle');
--   * __a map is a recheck, not a build__ — relocating the tree with unchanged
--     relative paths gives byte-identical bytes, resolution is against the
--     manifest's directory and not the process working directory, and a member
--     edited in place is evaluated on the next run even when its mtime and its
--     declared @artifact@ identity are untouched
--     ('prop_relocatedTreeGivesIdenticalBytes',
--     'prop_resolutionIsManifestRelative',
--     'prop_editedMemberIsRecheckedWithoutManifestUpdate').
--
-- The committed @map.core.sexp@ and @map.verdict.sexp@ beside the manifest are
-- pinned fresh here, for the same reason "MapSpec" pins the fixture tree's:
-- @scripts\/check-map-conformance.sh@ hands the Lean driver the committed
-- envelope, so a stale one would compare two drivers over bytes neither would
-- produce today.
--
-- == @--out@
--
-- @lara check … --out \<path\>@ is a __product file, not a stdout redirect__,
-- and the three properties here are exactly its three outcomes: an accepted
-- check replaces @path@ with the bytes the default form prints
-- ('prop_outWritesAcceptedVerdict'); every nonzero exit leaves the previous
-- @path@ byte-for-byte intact, whether the refusal is a map's or a solo unit's
-- ('prop_outPreservesPreviousOnRefusal'); and a write that cannot complete
-- exits @2@ leaving neither a damaged destination nor a temporary file behind
-- ('prop_outFailedWriteLeavesNothingBehind').
--
-- Nothing here edits a committed byte: every mutation runs against a fresh
-- copy of the example tree in a temporary directory, the convention "MapSpec",
-- "MapLoadSpec" and "MapLinkSpec" share. The suite runs from the package root,
-- as @cabal test@ does.
module MapExampleSpec (mapExampleSpecProps) where

import Control.Monad (forM, forM_)
import Data.List (isInfixOf, isPrefixOf, isSuffixOf)
import System.Directory
  ( createDirectoryIfMissing
  , doesDirectoryExist
  , getModificationTime
  , listDirectory
  , setModificationTime
  )
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, (</>))
import System.Posix.Files
  ( accessModes
  , createSymbolicLink
  , fileMode
  , getFileStatus
  , getSymbolicLinkStatus
  , intersectFileModes
  , isSymbolicLink
  , setFileMode
  )
import System.Process (CreateProcess (..), proc, readCreateProcessWithExitCode)
import Test.QuickCheck

import Lara.AST (ArgId (..), Label (..), PropId (..), Status (..))
import Lara.Elaborate (PreparedSource (..), runSourceCheck, sourceResultVerdict)
import Lara.Map.Driver (encodeMapCheckInput, mapCheckInput, runMap)
import Lara.Map.Load (loadMap)
import Lara.Map.Types
  ( MapNode (..)
  , MapStatus (..)
  , MapVerdict (..)
  , MapWireError (..)
  , aliasText
  , nodeIndexInt
  , renderMapError
  )
import Lara.Map.Wire (encodeMapVerdict)
import Lara.Prop (Prop)
import Lara.Source.Load (loadSource, loadedPrepared, renderSourceLoadError)
import Lara.Strict (SExpr (..))
import Lara.TempTree (withTempDirectory)
import Lara.Wire
  ( Outcome (..)
  , PublicStatus (..)
  , parseSExpr
  , printSExpr
  , verdictOutcome
  )

-- ---------------------------------------------------------------------------
-- The shipped tree
-- ---------------------------------------------------------------------------

-- | The shipped multi-artifact D3 map's directory.
exampleRoot :: FilePath
exampleRoot = "examples/agreement-map-multi"

-- | The legacy single-file D3 artifact, kept byte-unchanged as the oracle the
-- composite is measured against.
legacyArtifact :: FilePath
legacyArtifact = "examples/agreement-map/example.lara"

-- | The member directories, in manifest order. The node correspondence the
-- composite is compared under is this order: @pa=0, pb=1, pc=2, pd=3@.
memberDirs :: [FilePath]
memberDirs = ["paper-a", "paper-b", "paper-c", "paper-d"]

-- | Every hand-written file of the example tree, relative to 'exampleRoot'.
--
-- The derived @example.core.sexp@ / @expected.json@ of each member are
-- deliberately absent: they are the solo worked-example anchors
-- ("Lara.WorkedExamples", @test\/WorkedExamplesSpec.hs@) and no map stage reads
-- them. Copying only these files is therefore also an assertion — a copied tree
-- that still checks proves the map needs nothing derived.
exampleSources :: [FilePath]
exampleSources =
  ["map.laramap", "agreement-v1.policy.lara"]
    ++ concat [[dir </> "example.lara", dir </> policyBase] | dir <- memberDirs]

-- | The co-located policy basename every member declares.
policyBase :: FilePath
policyBase = "agreement-v1.policy.lara"

-- | The shipped manifest.
exampleManifest :: FilePath
exampleManifest = exampleRoot </> "map.laramap"

-- ---------------------------------------------------------------------------
-- Process and filesystem helpers
-- ---------------------------------------------------------------------------

-- | The executable name; Cabal puts it on @PATH@ during @cabal test@ via the
-- test-suite's @build-tool-depends: lara:lara@, exactly as "CliSpec" and
-- "MapSpec" rely on.
laraBin :: String
laraBin = "lara"

runLara :: [String] -> IO (ExitCode, String, String)
runLara = runLaraIn Nothing

-- | Run @lara@ with an explicit working directory. 'Nothing' keeps the suite's
-- own (the package root); a 'Just' is what makes manifest-relative resolution
-- observable, since a manifest whose members resolved against the /process/
-- working directory would stop resolving the moment that directory changed.
runLaraIn :: Maybe FilePath -> [String] -> IO (ExitCode, String, String)
runLaraIn workingDir args =
  readCreateProcessWithExitCode (proc laraBin args) {cwd = workingDir} ""

-- | Run the body over a fresh empty directory, then remove it. The directory is
-- reserved, not derived — see "Lara.TempTree".
withTempRoot :: (FilePath -> IO a) -> IO a
withTempRoot = withTempDirectory "lara-mapexample"

-- | Copy the example tree's hand-written sources into a fresh temporary
-- directory and run the body over that copy's root. The relative layout is
-- preserved exactly, which is what makes the copy a /relocation/ rather than a
-- new tree.
withCopiedExample :: (FilePath -> IO a) -> IO a
withCopiedExample body = withTempRoot $ \root -> do
  forM_ exampleSources $ \relative -> do
    contents <- readFileStrict (exampleRoot </> relative)
    createDirectoryIfMissing True (takeDirectory (root </> relative))
    writeFile (root </> relative) contents
  body root

-- | Read a whole file and force it, so the handle is closed before the same
-- path is read or written again.
readFileStrict :: FilePath -> IO String
readFileStrict path = do
  contents <- readFile path
  length contents `seq` pure contents

-- | Overwrite a member in place while leaving its modification time exactly as
-- it was, and return that preserved time so the caller can assert it did not
-- move. This is the point of the edit test: nothing in the map path may consult
-- a timestamp, so an edit that hides from @make@ must not hide from @lara@.
editPreservingMtime :: FilePath -> (String -> String) -> IO ()
editPreservingMtime path rewrite = do
  before <- getModificationTime path
  contents <- readFileStrict path
  writeFile path (rewrite contents)
  setModificationTime path before

-- ---------------------------------------------------------------------------
-- Small assertion helpers
-- ---------------------------------------------------------------------------

-- | Run the shipped map and hand its verdict to a checker, or fail loudly with
-- the map's own rendered diagnostic.
withShippedVerdict :: FilePath -> (MapVerdict -> Property) -> IO Property
withShippedVerdict manifest k = do
  outcome <- runMap manifest
  pure $ case outcome of
    Left err -> counterexample (manifest ++ ": " ++ renderMapError err) False
    Right verdict -> k verdict

-- | The solo verdict of one @.lara@ artifact, as the accepted outcome, or an
-- explanation of why there is none.
soloOutcome :: FilePath -> IO (Either String Outcome)
soloOutcome path = do
  loaded <- loadSource path
  pure $ case loaded of
    Left err -> Left (renderSourceLoadError err)
    Right source -> case loadedPrepared source of
      SourceRejected _ -> Left "admission rejection"
      SourceAccepted input ->
        case verdictOutcome (sourceResultVerdict (runSourceCheck input)) of
          Reject rejection -> Left ("reject " ++ show rejection)
          accepted@Accept{} -> Right accepted

-- | The composite's labels as plain @(index, label)@ pairs, for comparison
-- against a solo verdict's.
compositeLabels :: MapVerdict -> [(Int, Label)]
compositeLabels verdict = [(nodeIndexInt i, l) | (i, l) <- mvLabels verdict]

-- | The composite's edges as plain index pairs.
compositeEdges :: MapVerdict -> [(Int, Int)]
compositeEdges verdict =
  [(nodeIndexInt s, nodeIndexInt t) | (s, t) <- mvEdges verdict]

-- | The composite's claim answers, dropping the map-only @(alias, claim name)@
-- handles so the remainder is directly comparable with a solo verdict's
-- @(proposition, status)@ list.
compositeAnswers :: MapVerdict -> [(Prop, Status)]
compositeAnswers verdict =
  [(msAtom s, msStatus s) | s <- mvStatuses verdict]

-- | A solo verdict's claim answers in the same shape, with the public wrapper
-- required to be 'Published'. A map never reports @evidence-blocked@ (a member
-- with a nonempty admission audit is refused at load), so an
-- 'EvidenceBlocked' on the legacy side would make the two sides incomparable
-- rather than unequal — hence the explicit constructor match instead of
-- @conditionalStatus@.
soloAnswers :: Outcome -> Either String [(Prop, Status)]
soloAnswers outcome = traverse published (verdictStatuses outcome)
  where
    published (p, Published status) = Right (p, status)
    published (_, EvidenceBlocked _) = Left "solo verdict reports evidence-blocked"

-- ---------------------------------------------------------------------------
-- The shipped map
-- ---------------------------------------------------------------------------

-- | The four member artifacts each check on their own, and each one's single
-- claim is @justified@.
--
-- This is the base case the composite is measured against, and it is what makes
-- the example an example: every member is an ordinary, independently valid
-- paper artifact — registered in "Lara.WorkedExamples" and carrying its own
-- solo anchors — not a fragment that only means something inside a map.
prop_membersAreSoloJustified :: Property
prop_membersAreSoloJustified = once $ ioProperty $ do
  outcomes <- forM memberDirs $ \dir -> do
    outcome <- soloOutcome (exampleRoot </> dir </> "example.lara")
    pure (dir, outcome)
  pure $
    conjoin
      [ case outcome of
        Left reason -> counterexample (dir ++ ": " ++ reason) False
        Right accepted ->
          conjoin
            [ counterexample (dir ++ ": one unattacked support argument") $
                (verdictLabels accepted === [(0, LIn)])
                  .&&. (verdictEdges accepted === [])
            , counterexample (dir ++ ": exactly one justified claim") $
                map snd (verdictStatuses accepted) === [Published Justified]
            ]
      | (dir, outcome) <- outcomes
      ]

-- | The composite verdict is the legacy single-file oracle's answer.
--
-- Every part of the answer is compared: the composite's node table is pinned to
-- @pa=0, pb=1, pc=2, pd=3@, and then the labels, the edge set and the four
-- @(proposition, status)@ pairs must equal @examples\/agreement-map\/@'s.
--
-- Note precisely what the node assertion does and does not buy. It pins __the
-- composite side__ of the correspondence, so the index comparisons below are
-- made against a stated mapping rather than an assumed one on that side. The
-- legacy side's own index-to-argument mapping is not asserted here; it is
-- pinned by @examples\/agreement-map\/expected.json@ through
-- @test\/WorkedExamplesSpec.hs@, which is where the legacy artifact's anchors
-- live and where they would have to change.
--
-- The edges carry the weight. The legacy artifact declares both of them by
-- hand, because all four papers live in one file and each can name the other's
-- argument. No member of this map declares either, and none could. They are
-- generated by cross-member saturation from the declared contrary pair — and
-- the pair that differs in its setting index still gets no edge, which is the
-- feature the demo exists to show, now shown across separate artifacts.
--
-- What is deliberately __not__ asserted is byte equality of the two verdicts:
-- a composite leads with @(scope map)@ and reports each status under its
-- @(member alias, claim name)@ handle, so the bytes differ by construction
-- (plan review point 9).
prop_compositeMatchesLegacyOracle :: Property
prop_compositeMatchesLegacyOracle = once $ ioProperty $ do
  legacy <- soloOutcome legacyArtifact
  case (\o -> (,) o <$> soloAnswers o) =<< legacy of
    Left reason -> pure (counterexample (legacyArtifact ++ ": " ++ reason) False)
    Right (legacyOutcome, legacyAnswers) ->
      withShippedVerdict exampleManifest $ \verdict ->
        conjoin
          [ counterexample "node correspondence pa=0, pb=1, pc=2, pd=3" $
              [ (aliasText (mnAlias n), argIdText (mnArg n), nodeIndexInt (mnIndex n))
              | n <- mvNodes verdict
              ]
                === [ ("paper_a", "pa", 0)
                    , ("paper_b", "pb", 1)
                    , ("paper_c", "pc", 2)
                    , ("paper_d", "pd", 3)
                    ]
          , counterexample "labels match the legacy oracle" $
              compositeLabels verdict === verdictLabels legacyOutcome
          , counterexample "edges match the legacy oracle (and no member declares one)" $
              compositeEdges verdict === verdictEdges legacyOutcome
          , counterexample "claim propositions and statuses match the legacy oracle" $
              compositeAnswers verdict === legacyAnswers
          , counterexample "the answer is contested, contested, justified, justified" $
              map snd (compositeAnswers verdict)
                === [Contested, Contested, Justified, Justified]
          , counterexample "and the claim handles are the members' own names" $
              [ (aliasText (msAlias s), propIdText (msClaim s))
              | s <- mvStatuses verdict
              ]
                === [ ("paper_a", "c_pos")
                    , ("paper_b", "c_neg")
                    , ("paper_c", "c_low")
                    , ("paper_d", "c_high")
                    ]
          ]

-- | The committed @examples\/agreement-map-multi\/map.verdict.sexp@ is what the
-- driver produces today.
prop_shippedVerdictGoldenIsFresh :: Property
prop_shippedVerdictGoldenIsFresh = once $ ioProperty $ do
  golden <- readFileStrict (exampleRoot </> "map.verdict.sexp")
  withShippedVerdict exampleManifest $ \verdict ->
    counterexample "committed map.verdict.sexp has drifted" $
      printSExpr (encodeMapVerdict verdict) ++ "\n" === golden

-- | The @EXPECTED COMPOSITE VERDICT@ comment in the shipped @map.laramap@ is the
-- verdict the map produces today.
--
-- That block is the reader-facing statement of what the example demonstrates,
-- and a comment survives every pipeline change: were the node order, a status
-- spelling or the edge derivation to move, @map.verdict.sexp@ would be
-- regenerated and the comment would not. So the block is written as parseable
-- S-expressions — the verdict's own @nodes@, @labels@, @edges@ and @statuses@
-- sections, each status row minus its @status@ tag and its proposition — and
-- compared here against those sections as 'encodeMapVerdict' prints them for
-- the live run. The spellings on the expected side come from the encoder, not
-- from this test.
prop_manifestVerdictCommentIsCurrent :: Property
prop_manifestVerdictCommentIsCurrent = once $ ioProperty $ do
  manifestText <- readFileStrict exampleManifest
  case expectedVerdictBlock manifestText of
    Left reason -> pure (counterexample (exampleManifest ++ ": " ++ reason) False)
    Right block -> withShippedVerdict exampleManifest $ \verdict ->
      let live = commentedSections verdict
       in counterexample
            ( "the EXPECTED COMPOSITE VERDICT block in "
                ++ exampleManifest
                ++ " no longer matches the verdict.\n  comment says: "
                ++ unwords (map printSExpr block)
                ++ "\n  verdict says: "
                ++ unwords (map printSExpr live)
            )
            (block == live)

-- | The manifest's @EXPECTED COMPOSITE VERDICT@ block, parsed: the comment lines
-- after the banner's closing rule and before the first bare @;@, with the comment
-- leader stripped, read as a sequence of S-expressions.
--
-- Every way the block can go missing or malformed is a 'Left' naming it, so the
-- property fails loudly rather than comparing an empty list with nothing.
expectedVerdictBlock :: String -> Either String [SExpr]
expectedVerdictBlock text =
  case break ("EXPECTED COMPOSITE VERDICT" `isInfixOf`) (lines text) of
    (_, []) -> Left "no EXPECTED COMPOSITE VERDICT banner"
    (_, _banner : rest) ->
      let body = takeWhile (/= ";") (dropWhile ("; ---" `isPrefixOf`) rest)
       in if null body
            then Left "the EXPECTED COMPOSITE VERDICT block is empty"
            else
              if not (all (";" `isPrefixOf`) body)
                then Left "the EXPECTED COMPOSITE VERDICT block runs past the comment"
                else case parseSExpr ("(" ++ unlines (map (drop 1) body) ++ ")") of
                  Left err -> Left ("the EXPECTED COMPOSITE VERDICT block does not parse: " ++ show err)
                  Right (SList sections) -> Right sections
                  Right other -> Left ("unexpected parse: " ++ printSExpr other)

-- | The four verdict sections the manifest comment transcribes, read off the
-- encoded verdict: @nodes@, @labels@ and @edges@ verbatim, and @statuses@ with
-- each row cut to its @(alias claim status)@ handle and answer.
commentedSections :: MapVerdict -> [SExpr]
commentedSections verdict =
  [section "nodes", section "labels", section "edges", statusHandles (section "statuses")]
  where
    encoded = case encodeMapVerdict verdict of
      SList (_ : sections) -> sections
      other -> [other]
    section key =
      case [s | s@(SList (SAtom k : _)) <- encoded, k == key] of
        found : _ -> found
        [] -> SList [SAtom ("missing section " ++ key)]
    statusHandles (SList (headAtom : rows)) = SList (headAtom : map handle rows)
    statusHandles other = other
    handle (SList [_statusTag, alias, claim, _proposition, status]) = SList [alias, claim, status]
    handle other = other

-- | The committed @examples\/agreement-map-multi\/map.core.sexp@ parity envelope
-- is what @lara map-input@ derives today.
--
-- @scripts\/check-map-conformance.sh@ hands the Lean driver /this file/ and
-- makes the same freshness comparison before it does. This is the in-process
-- half of that check: @cabal test@ never spawns the Lean binary, so without it
-- a drifted envelope would stay green until someone ran the shell gate.
prop_shippedEnvelopeIsFresh :: Property
prop_shippedEnvelopeIsFresh = once $ ioProperty $ do
  golden <- readFileStrict (exampleRoot </> "map.core.sexp")
  loaded <- loadMap exampleManifest
  pure $ case loaded of
    Left err -> counterexample (renderMapError err) False
    Right members -> case mapCheckInput members of
      Left err -> counterexample ("envelope refused: " ++ mweMessage err) False
      Right input ->
        counterexample "committed map.core.sexp has drifted" $
          printSExpr (encodeMapCheckInput input) ++ "\n" === golden

-- | @lara check@ on the shipped manifest prints exactly the committed golden
-- and exits 0 — the command the Makefile's @map-check@ target runs.
prop_cliShippedMapAccepts :: Property
prop_cliShippedMapAccepts = once $ ioProperty $ do
  (code, out, err) <- runLara ["check", exampleManifest]
  golden <- readFileStrict (exampleRoot </> "map.verdict.sexp")
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitSuccess)
      , counterexample "stdout is the golden composite verdict" (out === golden)
      , counterexample "stderr is silent on acceptance" (err === "")
      ]

-- ---------------------------------------------------------------------------
-- A map is a recheck, not a build
-- ---------------------------------------------------------------------------

-- | Relocating the tree, with its relative manifest paths and its contents
-- unchanged, gives byte-identical verdict bytes.
--
-- The manifest spells member paths relatively and the verdict carries the
-- __manifest-spelled__ path rather than a resolved one, which is exactly what
-- makes this hold; a verdict that leaked an absolute path would move with the
-- tree.
prop_relocatedTreeGivesIdenticalBytes :: Property
prop_relocatedTreeGivesIdenticalBytes = once $ ioProperty $ do
  golden <- readFileStrict (exampleRoot </> "map.verdict.sexp")
  withCopiedExample $ \root -> do
    (code, out, err) <- runLara ["check", root </> "map.laramap"]
    pure $
      conjoin
        [ counterexample ("relocated tree refused: " ++ err) (code === ExitSuccess)
        , counterexample "relocated verdict bytes are identical" (out === golden)
        ]

-- | Member paths resolve against the __manifest's__ directory, not the process
-- working directory.
--
-- The relocated copy is checked from __three different working directories__,
-- and all three produce the committed golden's bytes:
--
--   1. the tree's own root, naming the manifest relatively (@map.laramap@);
--   2. the package root — the suite's own directory — naming it absolutely;
--   3. @\<root\>\/paper-a@, a directory that is neither, naming it absolutely.
--
-- Runs 2 and 3 are the discriminating ones and run 1 is the control. A member
-- path resolved against the /process/ working directory would still resolve in
-- run 1, because the cwd and the manifest's directory coincide there — so a run
-- from the tree root can never fail for the reason this property is named
-- after. It is runs 2 and 3, where @paper-a\/example.lara@ does not exist
-- beneath the cwd at all, that a cwd-relative implementation cannot survive.
prop_resolutionIsManifestRelative :: Property
prop_resolutionIsManifestRelative = once $ ioProperty $ do
  golden <- readFileStrict (exampleRoot </> "map.verdict.sexp")
  withCopiedExample $ \root -> do
    (relCode, relOut, relErr) <-
      runLaraIn (Just root) ["check", "map.laramap"]
    (pkgCode, pkgOut, pkgErr) <-
      runLaraIn Nothing ["check", root </> "map.laramap"]
    (memberCode, memberOut, memberErr) <-
      runLaraIn (Just (root </> "paper-a")) ["check", root </> "map.laramap"]
    pure $
      conjoin
        [ counterexample ("relative from the tree root: " ++ relErr) (relCode === ExitSuccess)
        , counterexample "relative-path bytes" (relOut === golden)
        , counterexample ("absolute from the package root: " ++ pkgErr) (pkgCode === ExitSuccess)
        , counterexample "package-root bytes" (pkgOut === golden)
        , counterexample ("absolute from a member directory: " ++ memberErr) $
            memberCode === ExitSuccess
        , counterexample "member-directory bytes" (memberOut === golden)
        ]

-- | A member edited in place is rechecked on the next invocation, with no
-- manifest update — even when the edit leaves the file's modification time and
-- the member's declared @artifact@ identity exactly as they were.
--
-- The edit is the demo's own point turned into a mutation: paper B's system
-- constant is changed from @apt@ to @magnitude_pruning@, so its conclusion no
-- longer lands on paper A's atoms, the contrary instance dissolves, both
-- generated edges disappear, and the two @contested@ claims become
-- @justified@. Nothing else moves: the manifest is not touched, paper B still
-- declares @sha256:bbbb...@, and its mtime is restored after the write.
--
-- That is D1 of @docs\/multi-artifact-composition-decision.md@ made
-- observable. A build system keyed on timestamps would have reported the stale
-- answer here; a manifest carrying a checksum would have had to be updated
-- first. This one rereads the member's current bytes because that is the only
-- thing it ever does.
prop_editedMemberIsRecheckedWithoutManifestUpdate :: Property
prop_editedMemberIsRecheckedWithoutManifestUpdate = once $ ioProperty $
  withCopiedExample $ \root -> do
    let member = root </> "paper-b" </> "example.lara"
        manifest = root </> "map.laramap"
    (beforeCode, beforeOut, _) <- runLara ["check", manifest]
    manifestBefore <- readFileStrict manifest
    mtimeBefore <- getModificationTime member
    editPreservingMtime member (replaceAll "apt, cofi" "magnitude_pruning, cofi")
    mtimeAfter <- getModificationTime member
    (afterCode, afterOut, afterErr) <- runLara ["check", manifest]
    manifestAfter <- readFileStrict manifest
    pure $
      conjoin
        [ counterexample "the unedited copy accepts" (beforeCode === ExitSuccess)
        , counterexample "the edit did not move the member's mtime" $
            mtimeAfter === mtimeBefore
        , counterexample ("the edited map still accepts: " ++ afterErr) $
            afterCode === ExitSuccess
        , counterexample "the manifest was not touched" (manifestAfter === manifestBefore)
        , counterexample "the verdict changed" (property (afterOut /= beforeOut))
        , counterexample "paper B's declared artifact identity is unchanged" $
            property ("(member paper_b paper-b/example.lara (artifact sha256:bbbb...))" `isInfixOf` afterOut)
        , counterexample "the dissolved contrary instance leaves no edges" $
            property ("(edges) " `isInfixOf` afterOut)
        , counterexample "and both formerly contested claims are now justified" $
            property (not ("contested" `isInfixOf` afterOut))
        ]

-- | An /invalid/ edit is refused the ordinary way: the member's own rejection,
-- named by alias, one line on stderr, nothing on stdout, exit 1.
--
-- Renaming paper D's experiment constant to one the shared policy's signature
-- does not declare makes that member fail its own solo check (R2). The map
-- reports it as the member's rejection rather than as a map-level failure,
-- because that is what it is — and the exit code is @1@, the "understood and
-- rejected" door, not the @2@ an ill-formed map takes.
prop_invalidMemberEditIsRejected :: Property
prop_invalidMemberEditIsRejected = once $ ioProperty $
  withCopiedExample $ \root -> do
    let member = root </> "paper-d" </> "example.lara"
        manifest = root </> "map.laramap"
    editPreservingMtime member (replaceAll "paperD_exp1" "paperD_exp2")
    (code, out, err) <- runLara ["check", manifest]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 1)
        , counterexample "stdout empty" (out === "")
        , counterexample "exactly one stderr line" (length (lines err) === 1)
        , counterexample "the line names the member and its rejection" $
            property ("lara: map member paper_d rejected:" `isPrefixOf` err)
        ]

-- ---------------------------------------------------------------------------
-- @--out@
-- ---------------------------------------------------------------------------

-- | @--out@ __replaces__ the named path with the accepted verdict and prints
-- nothing on stdout; the file's bytes are exactly the default form's.
--
-- Both destinations already hold something else when the run starts, so this is
-- a replacement and not a creation. That is the half of D13's "@path@ is
-- replaced when and only when the check accepts" that
-- 'prop_outPreservesPreviousOnRefusal' cannot show: that property only ever
-- watches a file /survive/, so on its own it is equally consistent with a
-- @--out@ that never writes at all.
--
-- Both doors are exercised, because @--out@ is a property of @lara check@ and
-- not of the map: the composite verdict of a @.laramap@ and the solo verdict of
-- a @.lara@ take the same route to the same kind of file.
prop_outWritesAcceptedVerdict :: Property
prop_outWritesAcceptedVerdict = once $ ioProperty $
  withTempRoot $ \root -> do
    let mapOut = root </> "map.verdict.sexp"
        soloOut = root </> "solo.verdict.sexp"
        stale = "stale bytes that must not survive an accepting run\n"
    writeFile mapOut stale
    writeFile soloOut stale
    (mapCode, mapStdout, mapErr) <- runLara ["check", exampleManifest, "--out", mapOut]
    (_, mapPiped, _) <- runLara ["check", exampleManifest]
    mapWritten <- readFileStrict mapOut
    (soloCode, soloStdout, _) <-
      runLara ["check", exampleRoot </> "paper-a" </> "example.lara", "--out", soloOut]
    (_, soloPiped, _) <- runLara ["check", exampleRoot </> "paper-a" </> "example.lara"]
    soloWritten <- readFileStrict soloOut
    after <- listDirectory root
    pure $
      conjoin
        [ counterexample ("map exit: " ++ mapErr) (mapCode === ExitSuccess)
        , counterexample "map stdout is empty" (mapStdout === "")
        , counterexample "the file holds the default form's bytes" (mapWritten === mapPiped)
        , counterexample "and the previous contents are gone" $
            property (mapWritten /= stale)
        , counterexample "solo exit" (soloCode === ExitSuccess)
        , counterexample "solo stdout is empty" (soloStdout === "")
        , counterexample "the solo file holds the default form's bytes" (soloWritten === soloPiped)
        , counterexample "and the previous contents are gone" $
            property (soloWritten /= stale)
        , -- The success path renames its temporary away; only a failing one
          -- goes through 'bracketOnError'. Assert the directory holds exactly
          -- the two destinations, so a leaked temporary is caught here and not
          -- only on the failure path.
          counterexample "no temporary survives a successful write" $
            sortedEq after ["map.verdict.sexp", "solo.verdict.sexp"]
        ]

-- | The two @--out@ effects a caller does __not__ choose, and the third door.
--
-- @emitAccepted@'s docstring records both, because it reuses
-- 'Lara.AtomicWrite.atomicWriteWith' — written for generated repository
-- artifacts — against an arbitrary user-named path:
--
--   * __the destination becomes @0644@__, whatever it was. Asserted from a
--     @0600@ destination, so the observed direction is a /widening/, which is
--     the one worth knowing about.
--   * __a symlink destination is replaced, not followed__. @rename(2)@ acts on
--     the link, so @--out@ at a symlink leaves a regular file behind and the
--     link's former target untouched. This is the effect most likely to change
--     silently under a refactor of the atomic-rename path, and it is visible to
--     anyone pointing @--out@ at a symlinked artifact path — so both halves are
--     asserted: the destination is no longer a link, and the old target still
--     holds its original bytes.
--
-- The @.sexp@ door is exercised here too. @--out@ is a property of @lara check@
-- rather than of any one door, and the other two were already covered; this is
-- the third, so the flag is pinned on every door that accepts it.
prop_outContractEffects :: Property
prop_outContractEffects = once $ ioProperty $
  withTempRoot $ \root -> do
    let restricted = root </> "restricted.verdict.sexp"
        linkTarget = root </> "target.sexp"
        linkPath = root </> "link.verdict.sexp"
        sexpOut = root </> "sexp.verdict.sexp"
        targetBytes = "the symlink's former target, which must not be written\n"

    -- 0644: start from a mode that must widen for the effect to be visible.
    writeFile restricted "previous\n"
    setFileMode restricted 0o600
    (restrictedCode, _, _) <- runLara ["check", exampleManifest, "--out", restricted]
    restrictedMode <- fileMode <$> getFileStatus restricted

    -- symlink: replaced, not followed.
    writeFile linkTarget targetBytes
    createSymbolicLink linkTarget linkPath
    (linkCode, _, _) <- runLara ["check", exampleManifest, "--out", linkPath]
    stillLink <- isSymbolicLink <$> getSymbolicLinkStatus linkPath
    targetAfter <- readFileStrict linkTarget
    linkAfter <- readFileStrict linkPath

    -- The .sexp door, which had no --out coverage at all.
    (sexpCode, sexpStdout, sexpErr) <-
      runLara ["check", sexpAnchor, "--out", sexpOut]
    (_, sexpPiped, _) <- runLara ["check", sexpAnchor]
    sexpWritten <- readFileStrict sexpOut

    pure $
      conjoin
        [ counterexample "the 0600 run accepts" (restrictedCode === ExitSuccess)
        , counterexample "the destination's mode becomes 0644" $
            (restrictedMode `intersectFileModes` accessModes) === 0o644
        , counterexample "the symlink run accepts" (linkCode === ExitSuccess)
        , counterexample "the destination is no longer a symlink" $
            property (not stillLink)
        , counterexample "the former target is untouched" (targetAfter === targetBytes)
        , counterexample "and the destination holds the verdict" $
            property (linkAfter /= targetBytes)
        , counterexample ("the .sexp door accepts: " ++ sexpErr) (sexpCode === ExitSuccess)
        , counterexample ".sexp stdout is empty" (sexpStdout === "")
        , counterexample ".sexp --out holds the default form's bytes" (sexpWritten === sexpPiped)
        ]
  where
    -- A committed check-input@1 envelope the wire door accepts, so the third
    -- door is exercised on the same flag as the other two.
    sexpAnchor = "fixtures/corpus/undercut-accept.sexp"

-- | Every nonzero exit leaves a previously written @--out@ file byte-for-byte
-- intact, and behaves precisely as it does without the flag.
--
-- Three refusals are exercised over one already-written destination: a map
-- rejected after the checked boundary (exit 1, one stderr line, empty stdout),
-- an ill-formed map (exit 2), and a rejected solo unit — which still prints its
-- @reject@ verdict on __stdout__, because @--out@ names where an /accepted/
-- verdict goes and a rejection's bytes have never gone anywhere else.
prop_outPreservesPreviousOnRefusal :: Property
prop_outPreservesPreviousOnRefusal = once $ ioProperty $
  withTempRoot $ \root -> do
    let out = root </> "map.verdict.sexp"
    (_, _, _) <- runLara ["check", exampleManifest, "--out", out]
    accepted <- readFileStrict out
    (rejectCode, rejectOut, rejectErr) <-
      runLara ["check", "test/fixtures/map/false-alignment/map.laramap", "--out", out]
    afterReject <- readFileStrict out
    (boundaryCode, boundaryOut, _) <-
      runLara ["check", "test/fixtures/map/unknown-claim/map.laramap", "--out", out]
    afterBoundary <- readFileStrict out
    (soloCode, soloOut, _) <-
      runLara ["check", "examples/R1/example.lara", "--out", out]
    afterSolo <- readFileStrict out
    pure $
      conjoin
        [ counterexample "a rejected map exits 1" (rejectCode === ExitFailure 1)
        , counterexample "and prints no verdict" (rejectOut === "")
        , counterexample "and one stderr line" (length (lines rejectErr) === 1)
        , counterexample "and leaves the previous output intact" (afterReject === accepted)
        , counterexample "an ill-formed map exits 2" (boundaryCode === ExitFailure 2)
        , counterexample "prints no verdict" (boundaryOut === "")
        , counterexample "and leaves the previous output intact" (afterBoundary === accepted)
        , counterexample "a rejected solo unit exits 1" (soloCode === ExitFailure 1)
        , counterexample "and still prints its rejection on stdout" $
            property ("reject" `isInfixOf` soloOut)
        , counterexample "and leaves the previous output intact" (afterSolo === accepted)
        ]

-- | A write that cannot complete exits 2, says so on stderr, damages nothing,
-- and leaves no temporary file behind.
--
-- Two destinations, because they fail at __different stages__ of
-- 'Lara.AtomicWrite.atomicWriteWith' and only one of them reaches the cleanup:
--
--   * an existing __directory__ — the same-directory temporary is created and
--     its @rename@ then fails, so @bracketOnError@ runs and must remove the
--     temporary. This is the case that tests the cleanup at all;
--   * a __nonexistent directory__ — @openTempFile@ fails before any temporary
--     exists, so there is nothing to clean up and only the diagnostic and the
--     exit code are under test. It is here because it is precisely what the
--     @Makefile@'s @map-check@ comment warns @OUT=@ users about, so the
--     behaviour that comment describes should be pinned somewhere.
--
-- The first also checks that the directory that held the temporary contains
-- exactly what it held before, and that an unrelated neighbouring file is
-- untouched.
prop_outFailedWriteLeavesNothingBehind :: Property
prop_outFailedWriteLeavesNothingBehind = once $ ioProperty $
  withTempRoot $ \root -> do
    let keeper = root </> "previous.sexp"
        destination = root </> "a-directory"
        missing = root </> "no-such-directory" </> "verdict.sexp"
    writeFile keeper "untouched\n"
    createDirectoryIfMissing True destination
    before <- listDirectory root
    (code, out, err) <- runLara ["check", exampleManifest, "--out", destination]
    after <- listDirectory root
    keeperContents <- readFileStrict keeper
    stillADirectory <- doesDirectoryExist destination
    (missingCode, missingOut, missingErr) <-
      runLara ["check", exampleManifest, "--out", missing]
    afterMissing <- listDirectory root
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 2)
        , counterexample "stdout empty" (out === "")
        , counterexample "the line names the write" $
            property ("lara: cannot write " `isPrefixOf` err)
        , counterexample "exactly one stderr line" (length (lines err) === 1)
        , counterexample "no temporary file survives" $
            counterexample (show after) (property (not (any (".tmp" `isSuffixOf`) after)))
        , counterexample "the directory is unchanged" (sortedEq after before)
        , counterexample "an unrelated neighbour is untouched" (keeperContents === "untouched\n")
        , counterexample "the destination is still a directory" (stillADirectory === True)
        , counterexample "a nonexistent directory exits 2" (missingCode === ExitFailure 2)
        , counterexample "prints no verdict" (missingOut === "")
        , counterexample "and names the write too" $
            property ("lara: cannot write " `isPrefixOf` missingErr)
        , counterexample "and creates nothing" (sortedEq afterMissing before)
        ]

-- ---------------------------------------------------------------------------
-- Small helpers
-- ---------------------------------------------------------------------------

-- | Set equality of two directory listings, order-insensitively.
sortedEq :: [FilePath] -> [FilePath] -> Property
sortedEq xs ys = counterexample (show xs ++ " /= " ++ show ys) (property (same xs ys))
  where
    same as bs = length as == length bs && all (`elem` bs) as && all (`elem` as) bs

-- | Replace every occurrence of @needle@ with @replacement@. A test-fixture
-- edit, deliberately not a general rewriter: it @error@s when the needle is
-- absent, so an example that stopped containing what a test edits fails loudly
-- instead of silently testing the unedited text.
replaceAll :: String -> String -> String -> String
replaceAll needle replacement haystack
  | not (needle `isInfixOf` haystack) =
      error ("MapExampleSpec: example does not contain " ++ show needle)
  | otherwise = go haystack
  where
    go [] = []
    go rest@(c : cs)
      | needle `isPrefixOf` rest = replacement ++ go (drop (length needle) rest)
      | otherwise = c : go cs

-- | The concrete text of an argument identifier, for the node-correspondence
-- assertion.
argIdText :: ArgId -> String
argIdText (ArgId name) = name

-- | The concrete text of a claim identifier, for the reporting-handle
-- assertion.
propIdText :: PropId -> String
propIdText (PropId name) = name

-- ---------------------------------------------------------------------------
-- Registry
-- ---------------------------------------------------------------------------

mapExampleSpecProps :: [(String, IO Result)]
mapExampleSpecProps =
  [ ("D3 members are solo justified", quickCheckResult prop_membersAreSoloJustified)
  , ("D3 composite matches the legacy oracle", quickCheckResult prop_compositeMatchesLegacyOracle)
  , ("D3 committed map verdict is fresh", quickCheckResult prop_shippedVerdictGoldenIsFresh)
  , ("D3 manifest's expected-verdict comment is current", quickCheckResult prop_manifestVerdictCommentIsCurrent)
  , ("D3 committed map envelope is fresh", quickCheckResult prop_shippedEnvelopeIsFresh)
  , ("D3 cli accepts and prints the golden", quickCheckResult prop_cliShippedMapAccepts)
  , ("D3 relocated tree gives identical bytes", quickCheckResult prop_relocatedTreeGivesIdenticalBytes)
  , ("D3 resolution is manifest-relative", quickCheckResult prop_resolutionIsManifestRelative)
  , ("D3 edited member is rechecked", quickCheckResult prop_editedMemberIsRecheckedWithoutManifestUpdate)
  , ("D3 invalid member edit is rejected", quickCheckResult prop_invalidMemberEditIsRejected)
  , ("check --out writes the accepted verdict", quickCheckResult prop_outWritesAcceptedVerdict)
  , ("check --out contract effects", quickCheckResult prop_outContractEffects)
  , ("check --out preserves the previous file on a refusal", quickCheckResult prop_outPreservesPreviousOnRefusal)
  , ("check --out cleans up a failed write", quickCheckResult prop_outFailedWriteLeavesNothingBehind)
  ]
