-- | End-to-end tests for the @lara@ command-line driver ("app/Main.hs"), the
-- @cabal test@ half of the review's CLI-coverage gap (M3 review item 8).
--
-- @scripts/differential.sh@ exercises the binary against the Lean oracle, but it
-- is not part of @cabal test@; nothing here spawned the executable, so the
-- 0\/1\/2 exit-code contract, the usage path, and the unreadable-file path were
-- untested by the suite. These tests run the real built binary (put on @PATH@ by
-- the test-suite's @build-tool-depends: lara:lara@) over the committed fixtures
-- and assert exactly the stdout bytes and exit code for each outcome.
--
-- The suite runs from the package root (as @cabal test@ does), so the fixture
-- relative paths resolve — the same assumption "DifferentialSpec" relies on.
module CliSpec (cliSpecProps) where

import Control.Exception (bracket)
import Data.List (isInfixOf, isPrefixOf)
import System.Directory
  ( createDirectoryIfMissing
  , getTemporaryDirectory
  , removeDirectoryRecursive
  , removeFile
  )
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.IO (hClose, hPutStr, openTempFile)
import System.Process (readProcessWithExitCode)
import Test.QuickCheck
import Lara.Replay (inputReplayId)
import Lara.Wire (decodeCheckInputFile, encodeReplayId, printSExpr)

-- | The executable name; Cabal puts it on @PATH@ during @cabal test@ via the
-- test-suite's @build-tool-depends: lara:lara@.
laraBin :: String
laraBin = "lara"

runLara :: [String] -> IO (ExitCode, String, String)
runLara args = readProcessWithExitCode laraBin args ""

fixtureReplayText :: FilePath -> IO String
fixtureReplayText path = do
  bytes <- readFile path
  case decodeCheckInputFile bytes of
    Left err -> error (path ++ ": codec: " ++ show err)
    Right input -> pure (printSExpr (encodeReplayId (inputReplayId input)))

-- | Write @contents@ to a fresh temp @.sexp@ file, run the body, then delete it.
withTempSexp :: String -> (FilePath -> IO a) -> IO a
withTempSexp contents k = do
  tmp <- getTemporaryDirectory
  bracket
    ( do
        (path, h) <- openTempFile tmp "lara-cli.sexp"
        hPutStr h contents
        hClose h
        pure path
    )
    removeFile
    k

-- | Write a @.lara@ artifact named @art.lara@ (plus optional co-located files)
-- into a fresh temp directory, run the body over the artifact path, then remove
-- the directory tree. Hermetic: no dependency on the committed @examples/@ tree.
withTempLaraDir
  :: String -- ^ artifact (@art.lara@) contents
  -> [(FilePath, String)] -- ^ co-located siblings (name, contents)
  -> (FilePath -> IO a) -- ^ body over the artifact path
  -> IO a
withTempLaraDir art siblings k = do
  tmp <- getTemporaryDirectory
  bracket
    ( do
        (dirFile, h) <- openTempFile tmp "lara-cli-dir"
        hClose h
        removeFile dirFile
        let dir = dirFile ++ ".d"
        createDirectoryIfMissing True dir
        writeFile (dir </> "art.lara") art
        mapM_ (\(nm, c) -> writeFile (dir </> nm) c) siblings
        pure dir
    )
    removeDirectoryRecursive
    (\dir -> k (dir </> "art.lara"))

-- | A minimal well-formed program (parses, zero declarations). Used by the
-- missing-policy path: parsing must succeed so the policy read is what fails.
minimalProgram :: String
minimalProgram = "artifact x at sha256:aaaa... policy nopolicy use backends []\n"

-- | accept: exit 0 and exactly the verdict bytes plus one trailing newline
-- ('putStrLn'), byte-identical to the pinned Lean-driver golden.
prop_cliAccept :: Property
prop_cliAccept = once $ ioProperty $ do
  replayText <- fixtureReplayText "fixtures/covered-self-edge.sexp"
  (code, out, _) <- runLara ["check", "fixtures/covered-self-edge.sexp"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitSuccess)
      , counterexample "stdout" $
          out
            === ("(verdict " ++ replayText ++ " accept (labels (0 undec)) (edges (0 0))"
              ++ " (statuses (status (atom p) contested)))\n")
      ]

-- | checker rejection: exit 1 and the reject verdict bytes on stdout.
prop_cliReject :: Property
prop_cliReject = once $ ioProperty $ do
  replayText <- fixtureReplayText "fixtures/missing-self-edge.sexp"
  (code, out, _) <- runLara ["check", "fixtures/missing-self-edge.sexp"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitFailure 1)
      , counterexample "stdout" (out === ("(verdict " ++ replayText ++ " reject missing-conflict)\n"))
      ]

-- | A registered backend that replays and refuses says why, on stderr, while
-- the wire verdict on stdout stays the bare class atom.
--
-- This is the rejection class that used to be silent: @reject R13@ with an
-- empty stderr, in a checker built around located rejections. Both halves are
-- pinned — the reason text (so the channel cannot regress to silence) and the
-- stdout bytes (so the diagnostic cannot leak onto the wire).
--
-- Since #130 the reason is followed by the slot → source mapping: the reason
-- names a @(prem i)@ and this is what says what @i@ is. On the raw door the
-- mapping is __structural__ — leaf ids read off the checked 'Lara.AST.Unit' —
-- because a wire program has no authored names to recover.
prop_cliBackendRejectionReason :: Property
prop_cliBackendRejectionReason = once $ ioProperty $ do
  let fixture = "fixtures/corpus/ord-premise-only-reject.sexp"
  replayText <- fixtureReplayText fixture
  (code, out, err) <- runLara ["check", fixture]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitFailure 1)
      , counterexample "stdout" (out === ("(verdict " ++ replayText ++ " reject R13)\n"))
      , counterexample "stderr names the backend, its reason, and its slots" $
          err
            === "certificate replay: ord@1 (theory t0) rejected the certificate: \
                \ord cites premise slots only; slot names theory entry 0\n\
                \  slot 0 = leaf e0\n\
                \  slot 1 = leaf e1\n"
      ]

-- | The value-carrying half: a cell comparison that fails names the offending
-- numerals in the author's own notation, not as @Rational@ 'show' output.
prop_cliBackendRejectionValues :: Property
prop_cliBackendRejectionValues = once $ ioProperty $ do
  (_, _, err) <- runLara ["check", "fixtures/corpus/ord-lt-boundary-reject.sexp"]
  pure $
    counterexample "stderr carries the compared values" $
      err
        === "certificate replay: ord@1 (theory t0) rejected the certificate: \
            \the claimed comparison does not hold: 5 < 5 is false\n\
            \  slot 0 = leaf e0\n"

-- | The same stderr line on the __@.lara@ front door__.
--
-- The two doors reach 'Lara.Driver.runCheckLocatedReported' by different routes
-- — the raw door with the ordinary group-only prune, the source door with
-- 'Lara.Elaborate.prepareSource'\'s source-boundary prune — so the two fixtures
-- above pin only the raw one. This is the author-facing door, and the diagnostic
-- exists for authors.
--
-- The artifact is S3 with its conclusion strengthened from @num_le@ to
-- @num_lt@, which is the boundary @examples\/S3\/example.lara@ names in prose:
-- the same certificate over the same two equal cells now replays false. The
-- @stdout@ verdict is again the bare class atom, so the reason cannot leak onto
-- the wire on this door either.
--
-- The slot mapping beneath the reason (#130) is the __authored__ one here: this
-- artifact's two premises resolve to the leaves @e1@ and @e2@ the source
-- declares, and 'Lara.Elaborate.SlotNames' recovers those names rather than
-- reporting the structural reading the raw door gets. The two coincide for a
-- leaf-fed instance, which is why the sharper cases — a prior argument and a
-- premise label — are pinned in "ElaborateSpec" instead.
prop_cliLaraBackendRejectionReason :: Property
prop_cliLaraBackendRejectionReason = once $ ioProperty $ do
  withTempLaraDir ltTieProgram [("p.policy.lara", ltTiePolicy)] $ \path -> do
    (code, out, err) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 1)
        , counterexample "stdout carries the bare class, not the reason" $
            out
              === ( "(verdict (replay-id (core lara-core@0.2) (policy p)"
                      ++ " (backends (backend ord 1)) (theories sha256:t0)"
                      ++ " (artifact sha256:5353535353535353535353535353535353535353535353535353535353535353))"
                      ++ " reject R13)\n"
                  )
        , counterexample "stderr carries the backend's reason and the authored slots" $
            err
              === "certificate replay: ord@1 (theory sha256:t0) rejected the certificate: \
                  \the claimed comparison does not hold: 0.71 < 0.71 is false\n\
                  \  slot 0 = leaf e1\n\
                  \  slot 1 = leaf e2\n"
        ]

-- | The @lara-syntax\@0.3@ half of the same rejection, and the D5 contract
-- (plan §8 \"diagnostics golden\", eng review 2A): when the argument @ord\@1@
-- refuses was __generated__ by a @comparison@ block, the author reads one
-- surface-context line naming the block and the three fields they wrote,
-- __above__ an unchanged kernel line.
--
-- Three things are pinned together, because the value is in their conjunction:
--
--   * the surface line comes __first__ and names the block's @claims@ id, the
--     generated argument, and @result@\/@baseline@\/measurand;
--   * the kernel line beneath it is __byte-identical__ to the one
--     'prop_cliLaraBackendRejectionReason' pins for the hand-written @0.2@
--     spelling of the same artifact — D5 adds context, it does not reword the
--     backend;
--   * the slot mapping under the kernel line (#130) names the leaves the author
--     wrote in the block's @result@ and @baseline@ fields, which is the whole
--     point on this form: the author never wrote a slot index, so a rejection
--     phrased over @(prem i)@ is unreadable without it;
--   * the raw @.sexp@ door carries __no surface framing__: a wire program has
--     no surface, no @comparison@, and no breadcrumb, so its stderr is the
--     kernel line and the structural mapping, with no @lara:@ line at all.
--
-- The artifact is 'ltTieProgram' rewritten on the @comparison@ form: the same
-- two equal cells, and a policy whose recheck rule concludes @num_lt@, so the
-- generated certificate replays false. Nothing about /what/ is rejected moves —
-- the class, the exit code, and the stdout verdict are the same as the @0.2@
-- spelling's.
prop_cliLaraComparisonRejectionContext :: Property
prop_cliLaraComparisonRejectionContext = once $ ioProperty $ do
  let kernelLine =
        "certificate replay: ord@1 (theory sha256:t0) rejected the certificate: \
        \the claimed comparison does not hold: 0.71 < 0.71 is false\n"
      slotLines =
        "  slot 0 = leaf e1\n\
        \  slot 1 = leaf e2\n"
      surfaceLine =
        "lara: comparison claiming 'c2': argument 'a1' was generated by that block \
        \from result = 'e2', baseline = 'e1', on 'accuracy'\n"
  (rawCode, _, rawErr) <- runLara ["check", "fixtures/corpus/ord-lt-boundary-reject.sexp"]
  withTempLaraDir cmpTieProgram [("p.policy.lara", cmpTiePolicy)] $ \path -> do
    (code, out, err) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 1)
        , counterexample "stdout carries the bare class, not the context" $
            out
              === ( "(verdict (replay-id (core lara-core@0.2) (policy p)"
                      ++ " (backends (backend ord 1)) (theories sha256:t0)"
                      ++ " (artifact sha256:5353535353535353535353535353535353535353535353535353535353535353))"
                      ++ " reject R13)\n"
                  )
        , counterexample "surface context above the unchanged kernel line" $
            err === (surfaceLine ++ kernelLine ++ slotLines)
        , counterexample "the kernel line itself is untouched" $
            take (length kernelLine) (drop (length surfaceLine) err) === kernelLine
        , counterexample "the generated argument's slots name the authored leaves" $
            drop (length surfaceLine + length kernelLine) err === slotLines
        , counterexample ".sexp door exit code unchanged" (rawCode === ExitFailure 1)
        , counterexample ".sexp door stderr has no surface framing" $
            rawErr
              === "certificate replay: ord@1 (theory t0) rejected the certificate: \
                  \the claimed comparison does not hold: 5 < 5 is false\n\
                  \  slot 0 = leaf e0\n"
        ]

-- | The @comparison@-form front door on an __accepting__ artifact
-- (@examples\/S2@): the block generates both arguments, both land @in@, and the
-- author-facing layer stays silent — a surface-context line exists only above a
-- kernel line, and an accept has none.
--
-- 'prop_cliLaraAcceptS1' covers S1 on this door; S2 is the first
-- @lara-syntax\@0.3@ example to reach it.
prop_cliLaraAcceptS2 :: Property
prop_cliLaraAcceptS2 = once $ ioProperty $ do
  replayText <- fixtureReplayText "examples/S2/example.core.sexp"
  (code, out, err) <- runLara ["check", "examples/S2/example.lara"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitSuccess)
      , counterexample "stdout bytes" $
          out
            === ("(verdict " ++ replayText ++ " accept (labels (0 in) (1 in)) (edges)"
              ++ " (statuses (status (atom better (con sys_new) (con sys_base)"
              ++ " (con accuracy) (con imagenet_val)) justified)))\n")
      , counterexample "no surface context on an accept" (err === "")
      ]

-- | 'ltTieProgram' rewritten on the @lara-syntax\@0.3@ @comparison@ form: the
-- two cells, the binding, and the direction are authored; the goal, the two
-- certificate slots, and both θ vectors are generated.
cmpTieProgram :: String
cmpTieProgram =
  unlines
    [ "artifact ord_tie_demo at sha256:5353535353535353535353535353535353535353535353535353535353535353"
    , "policy p"
    , "use backends [ord@1]"
    , "claim c1"
    , "  nl      = \"sys_new is at least as good as sys_base on ImageNet-val accuracy\""
    , "  formal  = at_least_as_good(sys_new, sys_base, accuracy, imagenet_val)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , "leaf e1 : reports(exp1, score_cell(sys_base, accuracy, imagenet_val, 0.71))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/accuracy.md#row=sys_base]"
    , "leaf e2 : reports(exp1, score_cell(sys_new, accuracy, imagenet_val, 0.71))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/accuracy.md#row=sys_new]"
    , "leaf e3 : comparison_setup(sys_new, sys_base, accuracy, imagenet_val, 0.71, 0.71)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [evidence/tables/accuracy.md#caption]"
    , "comparison : at_least_as_good(sys_new, sys_base) on accuracy @ imagenet_val"
    , "  relation = at-least-as-good"
    , "  recheck  = a1"
    , "  bridge   = a2"
    , "  result   = e2"
    , "  baseline = e1"
    , "  binding  = e3"
    , "  claims c2"
    , "    nl      = \"The reported baseline accuracy {cell e1} is at most the reported system accuracy {cell e2}\""
    , "    binding = { author = alice, audit-status = reviewed }"
    , "  supports c1"
    , "status c1"
    ]

-- | S3's scheme with @num_le@ replaced by @num_lt@ in both the recheck rule's
-- conclusion and the bridge's @cmp@ premise — the smallest edit that makes the
-- __generated__ certificate replay false while the block still elaborates.
cmpTiePolicy :: String
cmpTiePolicy =
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
    , "pred at_least_as_good(System, System, Measurand, Dataset)"
    , "pred comparison_setup(System, System, Measurand, Dataset, Num, Num)"
    , "rule tie_recheck(S, B, Q, D, Exp, Sv, Bv)"
    , "  mode       = strict"
    , "  premises   = [ reports(Exp, score_cell(B, Q, D, Bv)),"
    , "                 reports(Exp, score_cell(S, Q, D, Sv)) ]"
    , "  conclusion = num_lt(Bv, Sv)"
    , "  allow-trusted = false"
    , "  certifiers = [ (ord@1, sha256:t0) ]"
    , "theory sha256:t0 = []"
    , "rule no_worse(S, B, Q, D, Sv, Bv)"
    , "  mode       = defeasible"
    , "  premises   = [ cmp:     num_lt(Bv, Sv),"
    , "                 binding: comparison_setup(S, B, Q, D, Sv, Bv) ]"
    , "  conclusion = at_least_as_good(S, B, Q, D)"
    , "measurand accuracy : Num where higher-is-better"
    , "comparison-scheme at-least-as-good higher-is-better"
    , "  recheck = tie_recheck"
    , "  bridge  = no_worse"
    ]

-- | S3's artifact against a @num_lt@ rule: two equal reported cells, and a
-- strict step asking @ord\@1@ to certify that one is strictly below the other.
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

-- | S3's policy with @num_le@ replaced by @num_lt@ — the one edit that turns an
-- accepting artifact into a rejecting one.
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

-- | codec error (a well-formed file with malformed wire text): exit 2, nothing
-- on stdout (the located message goes to stderr).
prop_cliCodecError :: Property
prop_cliCodecError = once $ ioProperty $
  withTempSexp "(unit (policy" $ \path -> do
    (code, out, _) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 2)
        , counterexample "stdout empty" (out === "")
        ]

-- | unreadable input file: exit 2, nothing on stdout.
prop_cliUnreadable :: Property
prop_cliUnreadable = once $ ioProperty $ do
  (code, out, _) <- runLara ["check", "fixtures/does-not-exist.sexp"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitFailure 2)
      , counterexample "stdout empty" (out === "")
      ]

-- | misuse (unrecognized arguments): exit 2, nothing on stdout (usage goes to
-- stderr).
prop_cliUsage :: Property
prop_cliUsage = once $ ioProperty $ do
  (code, out, _) <- runLara ["not-a-subcommand"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitFailure 2)
      , counterexample "stdout empty" (out === "")
      ]

-- | @.lara@ end-to-end, Example A: parse + co-located policy resolution
-- (@empirical-v1.policy.lara@) + 'prepareSource' + 'runSourceCheck',
-- exit 0 and exactly the accept verdict bytes. a1 is @out@
-- (undercut+undermine+rebut, all @in@), d1/d2/d3 @in@, c1 @defeated@. These
-- bytes equal the in-process source-to-'CheckInput' path (the CLI is a thin
-- shell) — the plan's A1 gate for A.
prop_cliLaraAcceptA :: Property
prop_cliLaraAcceptA = once $ ioProperty $ do
  replayText <- fixtureReplayText "examples/A/example.core.sexp"
  (code, out, err) <- runLara ["check", "examples/A/example.lara"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitSuccess)
      , counterexample "stdout" $
          out
            === ("(verdict " ++ replayText ++ " accept (labels (0 out) (1 in) (2 in) (3 in))"
              ++ " (edges (0 3) (1 0) (2 0) (3 0))"
              ++ " (statuses (status (atom improves (con M) (con accuracy) (con D)) defeated)))\n")
      , counterexample "audit stderr empty" (err === "")
      ]

-- | @.lara@ end-to-end, Example B: two mutually-attacking arguments (a 2-cycle),
-- both @undec@, both claims @contested@. Exit 0 and exactly the contested verdict
-- bytes; resolves the same co-located @empirical-v1.policy.lara@.
prop_cliLaraAcceptB :: Property
prop_cliLaraAcceptB = once $ ioProperty $ do
  replayText <- fixtureReplayText "examples/B/example.core.sexp"
  (code, out, err) <- runLara ["check", "examples/B/example.lara"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitSuccess)
      , counterexample "stdout" $
          out
            === ("(verdict " ++ replayText ++ " accept (labels (0 undec) (1 undec)) (edges (0 1) (1 0))"
              ++ " (statuses"
              ++ " (status (atom improves (con M) (con accuracy) (con D)) contested)"
              ++ " (status (atom not_improves (con M) (con accuracy) (con D)) contested)))\n")
      , counterexample "audit stderr empty" (err === "")
      ]

-- | @.lara@ end-to-end, Example S1: policy-carried theory and surface
-- AssuranceCert replay through nd@1 to a justified accept verdict.
prop_cliLaraAcceptS1 :: Property
prop_cliLaraAcceptS1 = once $ ioProperty $ do
  replayText <- fixtureReplayText "examples/S1/example.core.sexp"
  (code, out, err) <- runLara ["check", "examples/S1/example.lara"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitSuccess)
      , counterexample "stdout bytes" $
          out
            === ("(verdict " ++ replayText ++ " accept (labels (0 in)) (edges) (statuses (status (atom holds (con safety_invariant) (con D)) justified)))\n")
      , counterexample "audit stderr empty" (err === "")
      ]

-- | Every named @nd\@1@ presentation failure is rejected at the source
-- boundary, before replay. These are end-to-end pins because the author sees
-- the CLI's prefix and newline, not merely 'elabErrorMessage'.
prop_cliLaraNdNamedDiagnostics :: Property
prop_cliLaraNdNamedDiagnostics = once $ ioProperty $ do
  base <- readFile "examples/S1/example.lara"
  policy <- readFile "examples/S1/strict-v1.policy.lara"
  checks <- mapM (runCase base policy) namedDiagnosticCases
  pure (conjoin checks)
  where
    runCase base policy (payload, expected) =
      withTempLaraDir
        (replaceFirstCli "(hyp 0)" payload base)
        [("strict-v1.policy.lara", policy)]
        (\path -> do
          (code, out, err) <- runLara ["check", path]
          pure $
            conjoin
              [ counterexample (payload ++ ": exit code") (code === ExitFailure 2)
              , counterexample (payload ++ ": stdout") (out === "")
              , counterexample (payload ++ ": stderr") $
                  err === ("lara: source invalid: " ++ expected ++ "\n")
              ])

    namedDiagnosticCases =
      [ ( "(hyp h)"
        , "arg 'a1': certificate 'nd@1' reference 'h' names no enclosing lam binder"
        )
      , ( "(lam h <F> (lam h <G> (hyp h)))"
        , "arg 'a1': certificate 'nd@1' lam binder 'h' shadows an enclosing binder; rename one"
        )
      , ( "(lam e1 <F> (hyp e1))"
        , "arg 'a1': certificate 'nd@1' lam binder 'e1' is also a citable premise name of this instance; rename the binder"
        )
      , ( "(lam 0 <F> (prem e1))"
        , "arg 'a1': certificate 'nd@1' lam binder '0' is not a source identifier"
        )
      , ( "(lam h <F> (hyp 007))"
        , "arg 'a1': certificate 'nd@1' index '007' is not a canonical index (use unsigned decimal with no leading zeros)"
        )
      , ( "(lam h <F> (hyp 0))"
        , "arg 'a1': certificate 'nd@1' kernel index '0' appears in a named-form payload; cite a binder by name, a premise with (prem ...), or a theory entry with (thy ...)"
        )
      , ( "(prem 1)"
        , "arg 'a1': certificate 'nd@1' premise reference '1' names slot 1 but this argument has only 1 premise slot(s)"
        )
      , ( "(foo (prem e1))"
        , "arg 'a1': certificate 'nd@1' named spelling 'e1' sits where the nd@1 grammar gives it no meaning"
        )
      , ( "(lam h (prop \"holds(\") (prem e1))"
        , "arg 'a1': certificate 'nd@1' formula annotation 'holds(' is not a source proposition"
        )
      , ( "(app (prop \"holds(safety_invariant, D)\") (prem e1))"
        , "arg 'a1': certificate 'nd@1' named spelling 'holds(safety_invariant, D)' sits where the nd@1 grammar gives it no meaning"
        )
      ]

replaceFirstCli :: String -> String -> String -> String
replaceFirstCli needle replacement = go
  where
    go [] = []
    go rest@(c : cs)
      | needle `isPrefixOf` rest = replacement ++ drop (length needle) rest
      | otherwise = c : go cs

-- ---------------------------------------------------------------------------
-- Source admission CLI matrix
-- ---------------------------------------------------------------------------

admissionLeaf :: String -> String -> String -> String -> String
admissionLeaf lid proposition kind provenance =
  unlines
    [ "leaf " ++ lid ++ " : " ++ proposition
    , "  kind = " ++ kind
    , "  provenance = " ++ provenance
    , "  refs = []"
    ]

admissionProgram :: [String] -> String
admissionProgram declarations =
  unlines
    [ "artifact admission_cli at sha256:admission-cli"
    , "policy p"
    , "use backends []"
    ]
    ++ concat declarations

-- | @lara-syntax\@0.7@ (#129) on the __production CLI__: a @discharge@ target
-- that names both a declared leaf and a prior argument is an /elaboration/
-- error, not a silent preference for the leaf. It surfaces on the same
-- source-invalidity channel every other pre-check rejection uses — exit 2,
-- empty stdout, one located line on stderr — so every byte is pinned.
prop_cliLaraAmbiguousDischarge :: Property
prop_cliLaraAmbiguousDischarge = once $ ioProperty $
  withTempLaraDir ambiguousDischargeProgram [("dq.policy.lara", ambiguousDischargePolicy)] $ \path -> do
    (code, out, err) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 2)
        , counterexample "stdout empty" (out === "")
        , counterexample "exact stderr" $
            err
              === "lara: source invalid: arg 'a_cite': discharge of 'audit' names 'x', \
                  \which is ambiguous between a declared leaf and a prior argument\n"
        ]

-- | @leaf x@ and @arg x@ both declared, and @a_cite@ discharges through @x@.
ambiguousDischargeProgram :: String
ambiguousDischargeProgram =
  unlines
    [ "artifact paper_129 at sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
    , "policy dq"
    , "use backends [nd@1]"
    , "claim c1"
    , "  nl      = \"The safety invariant holds for D\""
    , "  formal  = holds(safety_invariant, D)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , "claim c_other"
    , "  nl      = \"The other invariant holds for D\""
    , "  formal  = holds(other_invariant, D)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , "leaf e1 : holds(safety_invariant, D)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [evidence/safety.txt]"
    , "leaf e2 : holds(other_invariant, D)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [evidence/other.txt]"
    , "leaf x : audited(safety_invariant)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [evidence/audit.txt]"
    , "arg x : supports(c_other) by cited(other_invariant, D)"
    , "  open audit"
    , "  assurance = trusted"
    , "arg a_cite : supports(c1) by cited(safety_invariant, D)"
    , "  discharge audit with x"
    , "  assurance = trusted"
    , "status c1"
    ]

ambiguousDischargePolicy :: String
ambiguousDischargePolicy =
  unlines
    [ "policy dq"
    , "sort Property, Scope"
    , "con safety_invariant : Property"
    , "con other_invariant : Property"
    , "con D : Scope"
    , "pred holds(Property, Scope)"
    , "pred audited(Property)"
    , "rule cited(X, S)"
    , "  mode       = defeasible"
    , "  premises   = [ holds(X, S) ]"
    , "  conclusion = holds(X, S)"
    , "  question audit : audited(X) (optional)"
    ]

-- | @lara-syntax\@0.8@ (#131) on the __production CLI__: the two certificate
-- premise-slot diagnostics that speak about the /name classes/ now name the
-- citing rule, because \"a premise label\" is only meaningful once the author
-- knows whose labels were consulted. Both surface on the source-invalidity
-- channel — exit 2, empty stdout, one located line — so every byte of the two
-- reworded templates is pinned end to end, not only at the renderer.
prop_cliLaraPremiseLabelDiagnostics :: Property
prop_cliLaraPremiseLabelDiagnostics = once $ ioProperty $ do
  ambiguous <- runLabelFixture "(ordcmp (prem base) (prem 1))"
  unresolved <- runLabelFixture "(ordcmp (prem no_such) (prem 1))"
  pure $
    conjoin
      [ counterexample "label/leaf collision" $
          ambiguous
            === ( ExitFailure 2
                , ""
                , "lara: source invalid: arg 'a1': certificate 'ord@1' premise \
                  \reference 'base' is ambiguous between rule 'pair' premise label \
                  \and a declared leaf or prior argument\n"
                )
      , counterexample "unresolved names all three classes" $
          unresolved
            === ( ExitFailure 2
                , ""
                , "lara: source invalid: arg 'a1': certificate 'ord@1' premise \
                  \reference 'no_such' names neither a premise label of rule 'pair', \
                  \a declared leaf, nor a prior argument\n"
                )
      ]

-- | Run the @\@0.8@ fixture with one certificate payload through the CLI.
runLabelFixture :: String -> IO (ExitCode, String, String)
runLabelFixture payload =
  withTempLaraDir
    (premiseLabelProgram payload)
    [("pl.policy.lara", premiseLabelPolicy)]
    (\path -> runLara ["check", path])

-- | @pair@ labels its premises @base@\/@new@, and the artifact also declares a
-- __leaf__ named @base@ — the cross-class collision decision 2 rejects even
-- though both classes would name slot 0.
premiseLabelProgram :: String -> String
premiseLabelProgram payload =
  unlines
    [ "artifact paper_131 at sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
    , "policy pl"
    , "use backends [ord@1]"
    , "claim c1"
    , "  nl      = \"The two reported cells are paired\""
    , "  formal  = paired(sys_a, 0.74)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , "leaf base : alpha(sys_b, 0.74)"
    , "  kind       = observed"
    , "  provenance = user"
    , "  refs       = [evidence/collision.txt]"
    , "leaf e1 : alpha(sys_a, 0.74)"
    , "  kind       = observed"
    , "  provenance = user"
    , "  refs       = [evidence/alpha.txt]"
    , "leaf e2 : beta(sys_a, 0.74)"
    , "  kind       = observed"
    , "  provenance = user"
    , "  refs       = [evidence/beta.txt]"
    , "arg a1 : supports(c1) by pair from [e1, e2]"
    , "  assurance = cert(ord@1, sha256:pl-theory-0, " ++ payload ++ ")"
    , "status c1"
    ]

premiseLabelPolicy :: String
premiseLabelPolicy =
  unlines
    [ "policy pl"
    , "sort System"
    , "con sys_a : System"
    , "con sys_b : System"
    , "pred alpha(System, Num)"
    , "pred beta(System, Num)"
    , "pred paired(System, Num)"
    , "rule pair(X, V)"
    , "  mode       = strict"
    , "  premises   = [ base: alpha(X, V), new: beta(X, V) ]"
    , "  conclusion = paired(X, V)"
    , "  allow-trusted = false"
    , "  certifiers = [ (ord@1, sha256:pl-theory-0) ]"
    , "theory sha256:pl-theory-0 = []"
    ]

-- | Duplicate admission keys are source invalidity, not first-match R8.
-- Every byte is pinned because this diagnostic is the only observable result.
prop_cliDuplicateAdmissionKey :: Property
prop_cliDuplicateAdmissionKey = once $ ioProperty $
  withTempLaraDir artifact [("p.policy.lara", policyText)] $ \path -> do
    (code, out, err) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 2)
        , counterexample "stdout empty" (out === "")
        , counterexample "exact stderr" $
            err === "lara: source invalid: duplicate admission key (observed, user)\n"
        ]
  where
    artifact = admissionProgram [admissionLeaf "e" "p" "observed" "user"]
    policyText =
      unlines
        [ "policy p"
        , "admission { (observed, user) = reject, (observed, user) = admit }"
        ]

-- | Duplicate source leaf identifiers are rejected before metadata alignment
-- or admission can give either declaration a meaning.
prop_cliDuplicateLeafId :: Property
prop_cliDuplicateLeafId = once $ ioProperty $
  withTempLaraDir artifact [("p.policy.lara", "policy p\n")] $ \path -> do
    (code, out, err) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 2)
        , counterexample "stdout empty" (out === "")
        , counterexample "exact stderr" $
            err === "lara: source invalid: duplicate leaf id 'e'\n"
        ]
  where
    artifact =
      admissionProgram
        [ admissionLeaf "e" "p" "observed" "user"
        , admissionLeaf "e" "q" "attested" "user"
        ]

-- | R8 is outside the core verdict codec: exit 1, no stdout, one line naming
-- the first rejected leaf and its exact matched row.
prop_cliAdmissionR8 :: Property
prop_cliAdmissionR8 = once $ ioProperty $
  withTempLaraDir artifact [("p.policy.lara", policyText)] $ \path -> do
    (code, out, err) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 1)
        , counterexample "stdout empty" (out === "")
        , counterexample "exact stderr" $
            err
              === ( "lara: leaf 'e_first': kind=assumed, provenance=ai-executed matched "
                      ++ "admission row (assumed, ai-executed) = reject (R8)\n"
                  )
        ]
  where
    artifact =
      admissionProgram
        [ admissionLeaf "e_first" "p" "assumed" "ai-executed"
        , admissionLeaf "e_second" "q" "observed" "user"
        ]
    policyText =
      unlines
        [ "policy p"
        , "admission { (assumed, ai-executed) = reject, (observed, user) = reject }"
        ]

-- | Accepted quarantine keeps the normal verdict channel and emits exactly the
-- canonical audit on stderr.
prop_cliAcceptedQuarantineAudit :: Property
prop_cliAcceptedQuarantineAudit = once $ ioProperty $
  withTempLaraDir artifact [("p.policy.lara", policyText)] $ \path -> do
    (code, out, err) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitSuccess)
        , counterexample "verdict stdout" $
            out
              === ( "(verdict (replay-id (core lara-core@0.2) (policy p) (backends)"
                      ++ " (theories) (artifact sha256:admission-cli)) accept"
                      ++ " (labels) (edges) (statuses))\n"
                  )
        , counterexample "canonical audit stderr" $
            err
              === ( "lara: admission audit: leaves [e_q{policy-quarantine}]; "
                      ++ "arguments [a_q]; attacks []\n"
                  )
        ]
  where
    artifact =
      admissionProgram
        [ admissionLeaf "e_q" "p" "observed" "user"
        , "arg a_q : supports(derived) by leaf(e_q)\n"
        ]
    policyText =
      unlines
        [ "policy p"
        , "admission { (observed, user) = quarantine }"
        ]

-- | One artifact contains an error at every source/runtime boundary.  Removing
-- one higher-precedence defect at a time exposes exactly the next class:
-- invalid > R8 > R13 > R9 > core.
prop_cliAdmissionPrecedenceMatrix :: Property
prop_cliAdmissionPrecedenceMatrix = once $ ioProperty $ do
  invalid <- runVariant True True True True
  r8 <- runVariant False True True True
  r13 <- runVariant False False True True
  r9 <- runVariant False False False True
  core <- runVariant False False False False
  pure $
    conjoin
      [ resultIs "invalid" (ExitFailure 2) "" "duplicate admission key" invalid
      , resultIs "R8" (ExitFailure 1) "" "(R8)" r8
      , resultIs "R13" (ExitFailure 1) "reject R13" "replay preflight" r13
      , resultIs "R9" (ExitFailure 1) "reject R9" "group 'g'" r9
      , resultIs "core" (ExitFailure 1) "reject missing-conflict" "" core
      , noSlotBlock "R13" r13
      , noSlotBlock "R9" r9
      ]
  where
    runVariant duplicateKey hasR8 badBackend rejectGroup =
      withTempLaraDir
        (precedenceArtifact badBackend)
        [("p.policy.lara", precedencePolicy duplicateKey hasR8 rejectGroup)]
        (runLara . ("check" :) . (: []))

    resultIs name expectedCode outMarker errMarker (code, out, err) =
      counterexample (name ++ ": " ++ show (code, out, err)) $
        conjoin
          [ code === expectedCode
          , property (if null outMarker then null out else outMarker `isInfixOf` out)
          , property (if null errMarker then null err else errMarker `isInfixOf` err)
          ]

    -- The replay-preflight (R13) and group-conflict (R9) paths report no slot
    -- sources at all -- "Lara.Driver.Internal".@runCheckReported@ returns @[]@
    -- for both -- so the #130 slot mapping must not appear under either.  The
    -- marker assertions above are substring matches and would pass unchanged if
    -- a regression appended a slot block to these two classes' stderr.
    noSlotBlock name (_, _, err) =
      counterexample (name ++ " printed a slot mapping: " ++ show err) $
        property (not (any ((== "  slot ") . take 7) (lines err)))

precedenceArtifact :: Bool -> String
precedenceArtifact badBackend =
  unlines
    [ "artifact admission_precedence at sha256:admission-precedence"
    , "policy p"
    , "use backends " ++ if badBackend then "[bogus@1]" else "[]"
    ]
    ++ admissionLeaf "e_reject" "r8" "assumed" "ai-executed"
    ++ admissionLeaf "e_g1" "group_one" "observed" "user"
    ++ admissionLeaf "e_g2" "group_two" "attested" "user"
    ++ admissionLeaf "e_core" "core" "certified" "user"
    ++ unlines
      [ "group g = [e_g1, e_g2]"
      , "arg a_core : supports(core_claim) by leaf(e_core)"
      ]

precedencePolicy :: Bool -> Bool -> Bool -> String
precedencePolicy duplicateKey hasR8 rejectGroup =
  unlines $
    [ "policy p"
    , "pred r8"
    , "pred group_one"
    , "pred group_two"
    , "pred core"
    , "pred core_claim"
    , "contrary core core"
    ]
      ++ ["admission { " ++ rows ++ " }" | not (null rows)]
      ++ ["duplicate-reports = " ++ if rejectGroup then "reject" else "quarantine"]
  where
    r8Rows = ["(assumed, ai-executed) = reject" | hasR8]
    duplicateRows =
      if duplicateKey
        then ["(observed, user) = admit", "(observed, user) = quarantine"]
        else []
    rows = commaJoin (r8Rows ++ duplicateRows)
    commaJoin [] = ""
    commaJoin (x : xs) = x ++ concatMap (", " ++) xs

-- | @.lara@ parse error: a malformed artifact exits 2 with nothing on stdout (the
-- located parse message goes to stderr, sharing the codec error's exit code).
prop_cliLaraParseError :: Property
prop_cliLaraParseError = once $ ioProperty $
  withTempLaraDir "this is not a program\n" [] $ \path -> do
    (code, out, _) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 2)
        , counterexample "stdout empty" (out === "")
        ]

-- | @lara-syntax\@0.7@ (#135) on the __production CLI__: a @discharge@ under a
-- bare @leaf(…)@ has no rule to attach to, so the front door exits 2 with the
-- located parse message on stderr and nothing on stdout — the same shape the
-- codec error already uses. Pinned here, not only in "SyntaxSpec", because the
-- exit code and the stdout\/stderr split are a CLI contract (spec §10.1 R14).
prop_cliLaraDischargeOnBareLeaf :: Property
prop_cliLaraDischargeOnBareLeaf = once $ ioProperty $
  withTempLaraDir (bareLeafArg "  discharge q with e\n") [] $ \path -> do
    (code, out, err) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 2)
        , counterexample "stdout empty" (out === "")
        , counterexample "diagnostic" $
            property
              ("discharge requires a rule application, not a bare leaf" `isInfixOf` err)
        ]

-- | @lara-syntax\@0.7@ (#135) on the production CLI, @open@ half.
prop_cliLaraOpenOnBareLeaf :: Property
prop_cliLaraOpenOnBareLeaf = once $ ioProperty $
  withTempLaraDir (bareLeafArg "  open q\n") [] $ \path -> do
    (code, out, err) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 2)
        , counterexample "stdout empty" (out === "")
        , counterexample "diagnostic" $
            property
              ("open requires a rule application, not a bare leaf" `isInfixOf` err)
        ]

-- | @lara-syntax\@0.7@ (#133) on the production CLI: the retired @open q as o@
-- spelling exits 2 carrying its repair, so an author migrating a @0.6 source
-- is told what to write instead.
prop_cliLaraLegacyOpenAs :: Property
prop_cliLaraLegacyOpenAs = once $ ioProperty $
  withTempLaraDir legacyOpenAsProgram [] $ \path -> do
    (code, out, err) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 2)
        , counterexample "stdout empty" (out === "")
        , counterexample "diagnostic" $
            property ("lara-syntax@0.7 uses 'open q'; remove 'as …'" `isInfixOf` err)
        ]

-- | A one-argument program whose support term is a bare @leaf(…)@, plus the
-- given body line.
bareLeafArg :: String -> String
bareLeafArg bodyLine =
  unlines
    [ "artifact x at sha256:aaaa..."
    , "policy p"
    , "use backends [nd@1]"
    , "leaf e : fact"
    , "  kind = observed"
    , "  provenance = user"
    , "  refs = []"
    , "arg a : supports(derived) by leaf(e)"
    ]
    ++ bodyLine

legacyOpenAsProgram :: String
legacyOpenAsProgram =
  unlines
    [ "artifact x at sha256:aaaa..."
    , "policy p"
    , "use backends [nd@1]"
    , "arg a : supports(derived) by r(e)"
    , "  open q as q"
    ]

-- | @.lara@ missing co-located policy: the program parses but
-- @<policyId>.policy.lara@ is absent from the artifact's directory, so the policy
-- read fails — exit 2, nothing on stdout.
prop_cliLaraMissingPolicy :: Property
prop_cliLaraMissingPolicy = once $ ioProperty $
  withTempLaraDir minimalProgram [] $ \path -> do
    (code, out, _) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 2)
        , counterexample "stdout empty" (out === "")
        ]

-- | @.lara@ rejects duplicate surface argument ids at elaboration, before the
-- quarantine retained-index and raw\/resolved attack-alignment paths can use an
-- ambiguous id. This is the production-CLI counterpart of the pure elaborator
-- regression; the wire front door already enforces the same invariant.
prop_cliLaraDuplicateArgId :: Property
prop_cliLaraDuplicateArgId = once $ ioProperty $
  withTempLaraDir duplicateArgProgram [("p.policy.lara", "policy p\n")] $ \path -> do
    (code, out, err) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 2)
        , counterexample "stdout empty" (out === "")
        , counterexample "diagnostic" (property ("duplicate argument id" `isInfixOf` err))
        ]
  where
    duplicateArgProgram =
      unlines
        [ "artifact x at sha256:aaaa..."
        , "policy p"
        , "use backends [nd@1]"
        , "leaf e : fact"
        , "  kind = observed"
        , "  provenance = user"
        , "  refs = []"
        , "arg a : supports(derived) by leaf(e)"
        , "arg a : supports(derived) by leaf(e)"
        ]

-- | The @.lara@ front door enforces the same R14 endpoint invariant as the
-- wire decoder. In particular, a leading dangling attack cannot reach the
-- lossy id-to-term resolver and shift quarantine's raw/resolved row alignment.
prop_cliLaraDanglingAttack :: Property
prop_cliLaraDanglingAttack = once $ ioProperty $
  withTempLaraDir danglingAttackProgram [("p.policy.lara", "policy p\n")] $ \path -> do
    (code, out, err) <- runLara ["check", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 2)
        , counterexample "stdout empty" (out === "")
        , counterexample "diagnostic" $
            property ("attack endpoint is not a declared argument" `isInfixOf` err)
        ]
  where
    danglingAttackProgram =
      unlines
        [ "artifact x at sha256:aaaa..."
        , "policy p"
        , "use backends [nd@1]"
        , "leaf e : fact"
        , "  kind = observed"
        , "  provenance = user"
        , "  refs = []"
        , "arg a : supports(derived) by leaf(e)"
        , "rebut missing a"
        ]

-- ---------------------------------------------------------------------------
-- @lara deps@: the certificate dependency report (#204)
-- ---------------------------------------------------------------------------

-- | The report of an accepted @ord\@1@ comparison program, exactly.
--
-- This is the property \#204 was opened for: before it, @certDeps@ was proved
-- in Lean and mirrored in Haskell but no shipped consumer could reach a report,
-- so nothing at this level could be asserted at all. S5's two arguments each
-- compare the same pair of reported cells, and the report names the cells —
-- resolved atoms, not slot indices — which is what makes it an audit of the
-- evidence rather than a restatement of the certificate.
prop_cliDepsAcceptS5 :: Property
prop_cliDepsAcceptS5 = once $ ioProperty $ do
  (code, out, err) <- runLara ["deps", "examples/S5/example.lara"]
  let cell sys score =
        "(atom \"reports\" (con \"exp1\") (con \"score_cell\" (con \"" ++ sys
          ++ "\") (con \"perplexity\") (con \"wikitext103\") (num \"" ++ score ++ "\")))"
      argBlock a =
        "argument " ++ a ++ "\n"
          ++ "  premise 0 " ++ cell "sys_new" "28.4" ++ "\n"
          ++ "  premise 1 " ++ cell "sys_base" "31.6" ++ "\n"
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitSuccess)
      , counterexample "stdout bytes" (out === (argBlock "a1" ++ argBlock "a2"))
      , counterexample "stderr empty" (err === "")
      ]

-- | The two doors agree. S8's @.lara@ artifact and its committed
-- @example.core.sexp@ elaborate to the same unit, so they must produce the same
-- report — the same thin-shell property 'prop_cliLaraAcceptS1' asserts for the
-- verdict, now for the report beside it. It also covers the @nd\@1@ backend and
-- the source-authored @(prop …)@ formulas of @lara-syntax\@0.10@, whose lowered
-- atom is what a premise line prints.
prop_cliDepsDoorsAgree :: Property
prop_cliDepsDoorsAgree = once $ ioProperty $ do
  (codeL, outL, errL) <- runLara ["deps", "examples/S8/example.lara"]
  (codeS, outS, errS) <- runLara ["deps", "examples/S8/example.core.sexp"]
  pure $
    conjoin
      [ counterexample "exit codes" ((codeL, codeS) === (ExitSuccess, ExitSuccess))
      , counterexample "doors agree" (outL === outS)
      , counterexample "stdout bytes" $
          outL
            === ("argument a1\n"
              ++ "  premise 0 (atom \"holds\" (con \"safety_invariant\") (con \"D\"))\n")
      , counterexample "stderr empty" ((errL, errS) === ("", ""))
      ]

-- | An accepted program whose arguments cite nothing still lists them: E1 has
-- one checked argument and no strict certificates, so its report is one header
-- with no lines under it. \"Consulted nothing\" and \"not in the report\" are
-- different facts and the rendering keeps them apart.
prop_cliDepsAcceptEmpty :: Property
prop_cliDepsAcceptEmpty = once $ ioProperty $ do
  (code, out, err) <- runLara ["deps", "examples/E1/example.lara"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitSuccess)
      , counterexample "stdout bytes" (out === "argument a1\n")
      , counterexample "stderr empty" (err === "")
      ]

-- | A rejected input gets no report: nothing on stdout, exit 1, and one stderr
-- line pointing at @lara check@ for the reason. Asserting stdout is /empty/ is
-- the point — a partial report over a refused term would read as an audit of
-- evidence the checker did not accept.
prop_cliDepsReject :: Property
prop_cliDepsReject = once $ ioProperty $ do
  (code, out, err) <- runLara ["deps", "fixtures/missing-self-edge.sexp"]
  pure $
    conjoin
      [ counterexample "exit code" (code === ExitFailure 1)
      , counterexample "stdout empty" (out === "")
      , counterexample "stderr names the file" ("missing-self-edge.sexp" `isInfixOf` err)
      , counterexample "stderr points at check" ("lara check" `isInfixOf` err)
      ]

-- | @deps@ shares @check@'s decode boundary: a codec error is exit 2 with
-- nothing on stdout, not a rejection.
prop_cliDepsCodecError :: Property
prop_cliDepsCodecError = once $ ioProperty $
  withTempSexp "(not-a-check-input)" $ \path -> do
    (code, out, _) <- runLara ["deps", path]
    pure $
      conjoin
        [ counterexample "exit code" (code === ExitFailure 2)
        , counterexample "stdout empty" (out === "")
        ]

cliSpecProps :: [(String, IO Result)]
cliSpecProps =
  [ ("cli accept exit 0 + bytes", quickCheckResult prop_cliAccept)
  , ("cli reject exit 1 + bytes", quickCheckResult prop_cliReject)
  , ("cli backend rejection reason on stderr", quickCheckResult prop_cliBackendRejectionReason)
  , ("cli backend rejection names the values", quickCheckResult prop_cliBackendRejectionValues)
  , ("cli .lara backend rejection reason on stderr", quickCheckResult prop_cliLaraBackendRejectionReason)
  , ( "cli .lara comparison surface context above the kernel line"
    , quickCheckResult prop_cliLaraComparisonRejectionContext
    )
  , ("cli codec error exit 2", quickCheckResult prop_cliCodecError)
  , ("cli unreadable file exit 2", quickCheckResult prop_cliUnreadable)
  , ("cli usage exit 2", quickCheckResult prop_cliUsage)
  , ("cli .lara accept A exit 0 + bytes", quickCheckResult prop_cliLaraAcceptA)
  , ("cli .lara accept B exit 0 + bytes", quickCheckResult prop_cliLaraAcceptB)
  , ("cli .lara accept S1 strict cert exit 0 + bytes", quickCheckResult prop_cliLaraAcceptS1)
  , ("cli .lara nd@1 named diagnostics are exact", quickCheckResult prop_cliLaraNdNamedDiagnostics)
  , ("cli .lara accept S2 comparison form exit 0 + bytes", quickCheckResult prop_cliLaraAcceptS2)
  , ("cli .lara parse error exit 2", quickCheckResult prop_cliLaraParseError)
  , ("cli .lara discharge on bare leaf exit 2 (#135)", quickCheckResult prop_cliLaraDischargeOnBareLeaf)
  , ("cli .lara open on bare leaf exit 2 (#135)", quickCheckResult prop_cliLaraOpenOnBareLeaf)
  , ("cli .lara legacy 'open q as o' exit 2 (#133)", quickCheckResult prop_cliLaraLegacyOpenAs)
  , ("cli .lara ambiguous discharge exit 2 (#129)", quickCheckResult prop_cliLaraAmbiguousDischarge)
  , ("cli .lara premise-label diagnostics exit 2 (#131)", quickCheckResult prop_cliLaraPremiseLabelDiagnostics)
  , ("cli .lara missing policy exit 2", quickCheckResult prop_cliLaraMissingPolicy)
  , ("cli .lara duplicate argument id exit 2", quickCheckResult prop_cliLaraDuplicateArgId)
  , ("cli .lara dangling attack endpoint exit 2", quickCheckResult prop_cliLaraDanglingAttack)
  , ("cli .lara duplicate admission key exact source invalid", quickCheckResult prop_cliDuplicateAdmissionKey)
  , ("cli .lara duplicate LeafId exact source invalid", quickCheckResult prop_cliDuplicateLeafId)
  , ("cli .lara R8 exact first-leaf diagnostic", quickCheckResult prop_cliAdmissionR8)
  , ("cli .lara accepted quarantine verdict+audit", quickCheckResult prop_cliAcceptedQuarantineAudit)
  , ("cli .lara admission precedence invalid>R8>R13>R9>core", quickCheckResult prop_cliAdmissionPrecedenceMatrix)
  , ("cli deps S5 ord@1 report bytes (#204)", quickCheckResult prop_cliDepsAcceptS5)
  , ("cli deps both doors agree on S8 (#204)", quickCheckResult prop_cliDepsDoorsAgree)
  , ("cli deps lists an argument citing nothing (#204)", quickCheckResult prop_cliDepsAcceptEmpty)
  , ("cli deps rejection exit 1, no report (#204)", quickCheckResult prop_cliDepsReject)
  , ("cli deps codec error exit 2 (#204)", quickCheckResult prop_cliDepsCodecError)
  ]
