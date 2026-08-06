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
import Data.List (isInfixOf)
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
              === ( "(verdict (replay-id (core lara-core@0.1) (policy p) (backends)"
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

cliSpecProps :: [(String, IO Result)]
cliSpecProps =
  [ ("cli accept exit 0 + bytes", quickCheckResult prop_cliAccept)
  , ("cli reject exit 1 + bytes", quickCheckResult prop_cliReject)
  , ("cli codec error exit 2", quickCheckResult prop_cliCodecError)
  , ("cli unreadable file exit 2", quickCheckResult prop_cliUnreadable)
  , ("cli usage exit 2", quickCheckResult prop_cliUsage)
  , ("cli .lara accept A exit 0 + bytes", quickCheckResult prop_cliLaraAcceptA)
  , ("cli .lara accept B exit 0 + bytes", quickCheckResult prop_cliLaraAcceptB)
  , ("cli .lara accept S1 strict cert exit 0 + bytes", quickCheckResult prop_cliLaraAcceptS1)
  , ("cli .lara parse error exit 2", quickCheckResult prop_cliLaraParseError)
  , ("cli .lara missing policy exit 2", quickCheckResult prop_cliLaraMissingPolicy)
  , ("cli .lara duplicate argument id exit 2", quickCheckResult prop_cliLaraDuplicateArgId)
  , ("cli .lara dangling attack endpoint exit 2", quickCheckResult prop_cliLaraDanglingAttack)
  , ("cli .lara duplicate admission key exact source invalid", quickCheckResult prop_cliDuplicateAdmissionKey)
  , ("cli .lara duplicate LeafId exact source invalid", quickCheckResult prop_cliDuplicateLeafId)
  , ("cli .lara R8 exact first-leaf diagnostic", quickCheckResult prop_cliAdmissionR8)
  , ("cli .lara accepted quarantine verdict+audit", quickCheckResult prop_cliAcceptedQuarantineAudit)
  , ("cli .lara admission precedence invalid>R8>R13>R9>core", quickCheckResult prop_cliAdmissionPrecedenceMatrix)
  ]
