-- | Golden verdicts for E1–E3 / R1–R3 plus strict-certificate example S1.
--
-- Each property loads the committed @.lara@ artifact and its co-located policy
-- with "Lara.Syntax", 'elaborate's the pair to a 'Unit', validates the source
-- replay boundary with 'sourceCheckInput', runs the real six-stage pipeline
-- ("Lara.Driver".@runCheck@), and asserts the frozen identity-bearing verdict —
-- exactly the in-process path @app\/Main.hs@ takes for a @.lara@ file, so these
-- goldens pin the same bytes the CLI prints. IO lives in the test, never in the
-- elaborator (mirrors "ElaborateSpec").
--
-- Coverage (docs/m4a-checklist.md §2–§3):
--
--   * __E1__ @justified-clean@ — 'Accept'; the single support @in@; status justified.
--   * __E2__ @open-gap@        — 'Accept'; status gap (empty complete support).
--   * __E3__ @defeat-suite@    — 'Accept'; justified + defeated + contested in one
--     graph, and all three attack kinds (undercut, undermine, rebut).
--   * __R1__ @undeclared-leaf@ — 'Reject' R1  (leaf not in Γ).
--   * __R2__ @strict-contrary@ — 'Reject' R12 (policy §8.1 Path-B well-formedness).
--   * __R3__ @bad-attack-target@ — 'Reject' R10 (rebut on a leaf occurrence).
--   * __S1__ @strict-cert@ — 'Accept'; nd@1 cert replay; status justified.
--
-- A final __freshness__ property re-derives all nine @example.core.sexp@
-- anchors (A, B, E1–E3, R1–R3, and S1) from their surface @.lara@ + policy and
-- asserts the committed bytes match, guarding against surface/anchor drift.
module WorkedExamplesSpec (workedExamplesSpecProps) where

import Test.QuickCheck

import Data.List (sort)

import Lara.AST
  ( Attack (..)
  , ArgId (..)
  , Assurance (..)
  , BackendId (..)
  , Cert (..)
  , Digest (..)
  , DupGroup (..)
  , GroupConflictMode (..)
  , GroupId (..)
  , Label (..)
  , LeafId (..)
  , Policy
  , Program
  , PolicyId (..)
  , RejectClass (..)
  , Rejection (..)
  , RuleId (..)
  , Status (..)
  , SupportTerm (..)
  , TheoryDigest (..)
  , Unit (..)
  )
import Lara.Driver (runCheck)
import Lara.Elaborate
  ( defeasibleSuiteSigma
  , elabErrorMessage
  , elaborate
  , registryOf
  )
import Lara.ExpectedJson (JValue (..), expectedJson, expectedJsonValue)
import Lara.Replay
  ( CoreVersion (..)
  , mkCheckInput
  , mkReplayId
  , replayErrorMessage
  , sourceCheckInput
  )
import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..))
import Lara.Syntax (parsePolicy, parseProgram)
import Lara.Strict (SExpr (..))
import Lara.Wire (Outcome (..), Verdict (..), encodeCheckInput, printSExpr)

-- ---------------------------------------------------------------------------
-- Fixtures
-- ---------------------------------------------------------------------------

con :: String -> Term
con s = TCon (FunSym s) []

-- | @improves(m, accuracy, d)@ over two nullary-constant names.
improves :: String -> String -> Prop
improves m d = Prop (Pred "improves") [con m, con "accuracy", con d]

-- | @not_improves(m, accuracy, d)@.
notImproves :: String -> String -> Prop
notImproves m d = Prop (Pred "not_improves") [con m, con "accuracy", con d]

-- | @holds(x, d)@ over two nullary-constant names.
holdsP :: String -> String -> Prop
holdsP x d = Prop (Pred "holds") [con x, con d]

loadProgram :: FilePath -> IO Program
loadProgram path = do
  src <- readFile path
  case parseProgram src of
    Right p -> pure p
    Left e -> error (path ++ ": parse failed: " ++ show e)

loadPolicy :: FilePath -> IO Policy
loadPolicy path = do
  src <- readFile path
  case parsePolicy src of
    Right p -> pure p
    Left e -> error (path ++ ": parse failed: " ++ show e)

-- | Every example's per-example directory paired with its co-located policy
-- basename (the @policy <name>@ header the artifact declares). Each directory is
-- a self-contained paper artifact: @<dir>/example.lara@, @<dir>/<policy>@, and
-- the derived @<dir>/example.core.sexp@ anchor.
examplePolicies :: [(FilePath, FilePath)]
examplePolicies =
  [ ("examples/A", "empirical-v1.policy.lara")
  , ("examples/B", "empirical-v1.policy.lara")
  , ("examples/E1", "empirical-v1.policy.lara")
  , ("examples/E2", "empirical-v1.policy.lara")
  , ("examples/E3", "empirical-v1.policy.lara")
  , ("examples/R1", "empirical-v1.policy.lara")
  , ("examples/R2", "strict-bad-v1.policy.lara")
  , ("examples/R3", "empirical-v1.policy.lara")
  , ("examples/S1", "strict-v1.policy.lara")
  ]

-- | The shared empirical-v1 policy basename (co-located in each example's dir).
empiricalBase :: FilePath
empiricalBase = "empirical-v1.policy.lara"

-- | Load + elaborate + run one example, handing the resulting 'Verdict' to a
-- checker. An elaborate error fails the property loudly (these examples all
-- elaborate; the R-series rejects are checker verdicts, not elaborate errors).
-- @dir@ is the per-example directory; @policyBase@ its co-located policy file.
runExample :: FilePath -> FilePath -> (Verdict -> Property) -> IO Property
runExample dir policyBase k = do
  prog <- loadProgram (dir ++ "/example.lara")
  pol <- loadPolicy (dir ++ "/" ++ policyBase)
  pure $ case elaborate defeasibleSuiteSigma (registryOf pol) prog pol of
    Left e -> counterexample (dir ++ ": unexpected ElabError: " ++ elabErrorMessage e) False
    Right unit -> case sourceCheckInput prog pol unit of
      Left err -> counterexample (dir ++ ": replay identity error: " ++ replayErrorMessage err) False
      Right input -> k (runCheck input)

-- ---------------------------------------------------------------------------
-- E-series — accepted
-- ---------------------------------------------------------------------------

-- | E1: one unattacked support argument @in@, claim justified.
prop_E1 :: Property
prop_E1 = once $ ioProperty $
  runExample "examples/E1" empiricalBase $ \v ->
    case verdictOutcome v of
      Reject rejection -> counterexample ("E1: unexpected reject " ++ show rejection) False
      outcome@Accept{} ->
        conjoin
          [ counterexample "E1 labels: a1 → in" $
              verdictLabels outcome === [(0, LIn)]
          , counterexample "E1 status: c1 → justified" $
              verdictStatuses outcome === [(improves "M" "D", Justified)]
          ]

-- | E2: no arguments; the queried claim has empty complete support ⇒ gap.
prop_E2 :: Property
prop_E2 = once $ ioProperty $
  runExample "examples/E2" empiricalBase $ \v ->
    case verdictOutcome v of
      Reject rejection -> counterexample ("E2: unexpected reject " ++ show rejection) False
      outcome@Accept{} ->
        conjoin
          [ counterexample "E2 labels: no arguments" $
              verdictLabels outcome === []
          , counterexample "E2 status: c1 → gap" $
              verdictStatuses outcome === [(improves "M" "D", Gap)]
          ]

-- | E3: justified (a_j in) + defeated (a_d out, undercut+undermine) + contested
-- (a_c/a_cn 2-cycle undec) in one graph. Arg indices are declaration order
-- a_j=0, a_d=1, d_uc=2, d_um=3, a_c=4, a_cn=5.
prop_E3 :: Property
prop_E3 = once $ ioProperty $
  runExample "examples/E3" empiricalBase $ \v ->
    case verdictOutcome v of
      Reject rejection -> counterexample ("E3: unexpected reject " ++ show rejection) False
      outcome@Accept{} ->
        conjoin
          [ counterexample "E3 labels: a_j in, a_d out, d_uc/d_um in, a_c/a_cn undec" $
              verdictLabels outcome
                === [(0, LIn), (1, LOut), (2, LIn), (3, LIn), (4, LUndec), (5, LUndec)]
          , counterexample "E3 statuses: c_j justified, c_d defeated, c_c/c_cn contested" $
              verdictStatuses outcome
                === [ (improves "M_j" "D_j", Justified)
                    , (improves "M_d" "D_d", Defeated)
                    , (improves "M_c" "D_c", Contested)
                    , (notImproves "M_c" "D_c", Contested)
                    ]
          ]

-- | S1: the strict nd@1 certificate replays; the certified arg is @in@ and
-- the claim is justified.
prop_S1 :: Property
prop_S1 = once $ ioProperty $
  runExample "examples/S1" "strict-v1.policy.lara" $ \v ->
    case verdictOutcome v of
      Reject rejection -> counterexample ("S1: unexpected reject " ++ show rejection) False
      outcome@Accept{} ->
        conjoin
          [ counterexample "S1 labels: a1 → in" $
              verdictLabels outcome === [(0, LIn)]
          , counterexample "S1 status: c1 → justified" $
              verdictStatuses outcome === [(holdsP "safety_invariant" "D", Justified)]
          ]

-- ---------------------------------------------------------------------------
-- R-series — rejected with a specific class
-- ---------------------------------------------------------------------------

-- | R1: an undeclared root leaf ⇒ checker class R1.
prop_R1 :: Property
prop_R1 = once $ ioProperty $
  runExample "examples/R1" empiricalBase $ \v ->
    counterexample ("R1: expected reject R1, got " ++ show v) $
      verdictOutcome v === Reject (RejectClass R1)

-- | R2: a strict-reachable conclusion in a contrary pair ⇒ policy class R12.
prop_R2 :: Property
prop_R2 = once $ ioProperty $
  runExample "examples/R2" "strict-bad-v1.policy.lara" $ \v ->
    counterexample ("R2: expected reject R12, got " ++ show v) $
      verdictOutcome v === Reject (RejectClass R12)

-- | R3: a rebut targeting a leaf occurrence ⇒ attack-position class R10.
prop_R3 :: Property
prop_R3 = once $ ioProperty $
  runExample "examples/R3" empiricalBase $ \v ->
    counterexample ("R3: expected reject R10, got " ++ show v) $
      verdictOutcome v === Reject (RejectClass R10)

prop_replayPreflightExpectedJson :: Property
prop_replayPreflightExpectedJson =
  once $
    conjoin
      [ diagnostic duplicateInput
          === JObject
            [ ("kind", JString "reject")
            , ("class", JString "R13")
            , ("stage", JString "backend")
            , ("constituent", JObject [("kind", JString "policy")])
            , ("reason", JString "duplicate-selection")
            , ("backend", JString "nd@1")
            ]
      , diagnostic unknownInput
          === JObject
            [ ("kind", JString "reject")
            , ("class", JString "R13")
            , ("stage", JString "backend")
            , ("constituent", JObject [("kind", JString "policy")])
            , ("reason", JString "unknown-selection")
            , ("backend", JString "other@2")
            ]
      , diagnostic certificateInput
          === JObject
            [ ("kind", JString "reject")
            , ("class", JString "R13")
            , ("stage", JString "backend")
            , ( "constituent"
              , JObject
                  [ ("kind", JString "argument")
                  , ("id", JString "outer")
                  , ("index", JNumber 0)
                  ]
              )
            , ("reason", JString "certificate-backend-not-selected")
            , ("backend", JString "nd@1")
            ]
      ]
  where
    empty = Unit [] [] [] [] [] [] [] [] [] QuarantineOnConflict
    duplicateInput = preflightInput [(BackendId "nd", "1"), (BackendId "nd", "1")] empty
    unknownInput = preflightInput [(BackendId "nd", "1"), (BackendId "other", "2")] empty
    certificate =
      Cert (BackendId "nd") 1 (TheoryDigest "sha256:t") (SAtom "proof")
    certificateUnit =
      empty
        { unitArgs =
            [ ( ArgId "outer"
              , SRule (RuleId "strict") [] [] [] [] (AssuranceCert certificate)
              )
            ]
        }
    certificateInput = preflightInput [] certificateUnit
    preflightInput backends unit =
      let replayId =
            either (error . replayErrorMessage) id $
              mkReplayId
                LaraCoreV01
                (PolicyId "conformance-v1")
                backends
                []
                (Digest "sha256:conformance-corpus-v1")
       in either (error . replayErrorMessage) id (mkCheckInput replayId unit)
    diagnostic input =
      case expectedJsonValue input of
        JObject
          [ ("replay-id", _)
          , ("verdict-class", JString "reject R13")
          , ("located-diagnostic", value)
          ] -> value
        value -> value

-- | The R9 (escalated duplicate-report-group conflict) @expected.json@ path.
-- Like R13's preflight, an R9 boundary rejection never reaches @checkUnit@, so
-- 'expectedJsonValue' must render it directly ('Lara.ExpectedJson' finding: the
-- 'rejectDiag' @checkUnit@ branch would otherwise mis-locate or return @JNull@).
-- This pins the located diagnostic and the byte-exact @message@ both drivers
-- print on @stderr@.
prop_groupConflictExpectedJson :: Property
prop_groupConflictExpectedJson =
  once $
    r9Diagnostic groupConflictInput
      === JObject
        [ ("kind", JString "reject")
        , ("class", JString "R9")
        , ("stage", JString "group-boundary")
        , ("constituent", JObject [("kind", JString "group"), ("id", JString "g1")])
        , ("members", JArray [JString "e1", JString "e2"])
        , ( "message"
          , JString
              ( "group 'g1': members e1, e2 report one cell with "
                  ++ "≢ propositions and the policy escalates conflicts to reject (§4.3)"
              )
          )
        ]
  where
    effect c = Prop (Pred "effect") [TCon (FunSym c) []]
    empty = Unit [] [] [] [] [] [] [] [] [] QuarantineOnConflict
    groupConflictUnit =
      empty
        { unitLeaves = [(LeafId "e1", effect "up"), (LeafId "e2", effect "down")]
        , unitArgs = [(ArgId "a1", SLeaf (LeafId "e1"))]
        , unitQueries = [effect "up"]
        , unitGroups = [DupGroup (GroupId "g1") [LeafId "e1", LeafId "e2"]]
        , unitGroupMode = RejectOnConflict
        }
    groupConflictInput =
      let replayId =
            either (error . replayErrorMessage) id $
              mkReplayId
                LaraCoreV01
                (PolicyId "conformance-v1")
                [(BackendId "nd", "1")]
                []
                (Digest "sha256:conformance-corpus-v1")
       in either (error . replayErrorMessage) id (mkCheckInput replayId groupConflictUnit)
    r9Diagnostic input =
      case expectedJsonValue input of
        JObject
          [ ("replay-id", _)
          , ("verdict-class", JString "reject R9")
          , ("located-diagnostic", value)
          ] -> value
        value -> value

-- ---------------------------------------------------------------------------
-- Freshness — the derivation path reproduces the committed .core.sexp anchor
-- ---------------------------------------------------------------------------

-- | For every example (all nine: A, B, E1–E3, R1–R3, S1), re-running the full
-- derivation path — @parseProgram@ + @parsePolicy@ + @elaborate@ + @encodeUnit@ +
-- @printSExpr@ — on the committed @example.lara@ + co-located policy reproduces
-- the committed @example.core.sexp@ bytes __exactly__ (matching
-- @scripts/gen-worked-examples.hs@'s single trailing newline). This catches any
-- drift between a hand-edited surface file and its checked-in wire anchor: a
-- @.lara@ edit that is not regenerated fails here.
prop_freshness :: Property
prop_freshness = once (ioProperty (conjoin <$> mapM checkOne examplePolicies))
  where
    checkOne (dir, policyBase) = do
      progText <- readFile (dir ++ "/example.lara")
      polText <- readFile (dir ++ "/" ++ policyBase)
      committed <- readFile (dir ++ "/example.core.sexp")
      pure $ case (parseProgram progText, parsePolicy polText) of
        (Right prog, Right pol) ->
          case elaborate defeasibleSuiteSigma (registryOf pol) prog pol of
            Left e ->
              counterexample (dir ++ ": unexpected ElabError: " ++ elabErrorMessage e) False
            Right unit ->
              case sourceCheckInput prog pol unit of
                Left err ->
                  counterexample (dir ++ ": replay identity error: " ++ replayErrorMessage err) False
                Right input ->
                  counterexample (dir ++ ": .core.sexp is stale — regenerate with scripts/gen-worked-examples.hs") $
                    (printSExpr (encodeCheckInput input) ++ "\n") === committed
        (pr, pp) ->
          counterexample (dir ++ ": parse failed: " ++ show pr ++ " / " ++ show pp) (property False)

-- | For every example (all nine), re-render @expected.json@ from the elaborated
-- 'Unit' ("Lara.ExpectedJson".@expectedJson@) and assert it equals the committed
-- @examples\/\<NAME\>\/expected.json@ bytes exactly — the located-diagnostic
-- freshness sibling of 'prop_freshness'. @expected.json@ is the __Haskell-only__
-- golden (the Lean driver emits only the wire verdict), so it is outside the
-- byte-differential but pinned here.
prop_expectedJsonFresh :: Property
prop_expectedJsonFresh = once (ioProperty (conjoin <$> mapM checkOne examplePolicies))
  where
    checkOne (dir, policyBase) = do
      prog <- loadProgram (dir ++ "/example.lara")
      pol <- loadPolicy (dir ++ "/" ++ policyBase)
      committed <- readFile (dir ++ "/expected.json")
      pure $ case elaborate defeasibleSuiteSigma (registryOf pol) prog pol of
        Left e ->
          counterexample (dir ++ ": unexpected ElabError: " ++ elabErrorMessage e) False
        Right unit ->
          case sourceCheckInput prog pol unit of
            Left err ->
              counterexample (dir ++ ": replay identity error: " ++ replayErrorMessage err) False
            Right input ->
              counterexample
                (dir ++ ": expected.json is stale — regenerate with scripts/gen-worked-examples.hs")
                (expectedJson input === committed)

-- ---------------------------------------------------------------------------
-- Coverage matrix — measured from the examples' verdicts, not asserted in prose
-- ---------------------------------------------------------------------------

-- | The attack-kind tag of a typed attack (for measured attack coverage).
attackKind :: Attack -> String
attackKind Rebut{} = "rebut"
attackKind Undercut{} = "undercut"
attackKind Undermine{} = "undermine"

-- | The measured coverage of the whole suite: every accept status, every attack
-- kind, and the three rejection classes are __read off the elaborated units and
-- their verdicts__ (docs/worked-examples-plan.md §1, docs/m4a-checklist.md §2).
-- This turns the coverage matrix into evidence, not a prose claim: if some cell
-- stops being witnessed (a status vanishes, an attack kind is dropped, a reject
-- reclassifies), this fails.
--
-- The suite is the six §1 examples E1–E3 / R1–R3, the two teaching examples A
-- and B, plus strict-certificate example S1 — all nine in 'examplePolicies'.
prop_coverageMatrix :: Property
prop_coverageMatrix = once $ ioProperty $ do
  verdicts <- mapM loadVerdict examplePolicies -- [(dir, Either err Verdict)]
  units <- mapM loadUnit examplePolicies -- [(dir, Unit)]
  let elabErrs = [dir ++ ": " ++ e | (dir, Left e) <- verdicts]
      statuses = sort (nubOrd [s | (_, Right (Verdict _ (Accept _ _ sts))) <- verdicts, (_, s) <- sts])
      attackTags = sort (nubOrd [attackKind k | (_, u) <- units, k <- unitAttacks u])
      rejects = sort (nubOrd [r | (_, Right (Verdict _ (Reject r))) <- verdicts])
  pure $
    conjoin
      [ counterexample ("elaboration errors: " ++ show elabErrs) (null elabErrs)
      , counterexample
          ("status coverage incomplete — witnessed " ++ show statuses)
          (all (`elem` statuses) [Justified, Gap, Contested, Defeated])
      , counterexample
          ("attack-kind coverage incomplete — witnessed " ++ show attackTags)
          (all (`elem` attackTags) ["rebut", "undercut", "undermine"])
      , counterexample
          ("rejection-class coverage incomplete — witnessed " ++ show rejects)
          (all (`elem` rejects) [RejectClass R1, RejectClass R12, RejectClass R10])
      ]

-- | Load + elaborate + run one example to a labelled 'Verdict' (or its
-- 'elabErrorMessage' on the left).
loadVerdict :: (FilePath, FilePath) -> IO (FilePath, Either String Verdict)
loadVerdict (dir, policyBase) = do
  prog <- loadProgram (dir ++ "/example.lara")
  pol <- loadPolicy (dir ++ "/" ++ policyBase)
  pure $ (,) dir $ case elaborate defeasibleSuiteSigma (registryOf pol) prog pol of
    Left e -> Left (elabErrorMessage e)
    Right unit ->
      case sourceCheckInput prog pol unit of
        Left err -> Left (replayErrorMessage err)
        Right input -> Right (runCheck input)

-- | Load + elaborate one example to its 'Unit'.
loadUnit :: (FilePath, FilePath) -> IO (FilePath, Unit)
loadUnit (dir, policyBase) = do
  prog <- loadProgram (dir ++ "/example.lara")
  pol <- loadPolicy (dir ++ "/" ++ policyBase)
  case elaborate defeasibleSuiteSigma (registryOf pol) prog pol of
    Left e -> error (dir ++ ": unexpected ElabError: " ++ elabErrorMessage e)
    Right u -> pure (dir, u)

-- | Order-preserving-free dedup (small inputs).
nubOrd :: Ord a => [a] -> [a]
nubOrd = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

-- ---------------------------------------------------------------------------
-- Runner
-- ---------------------------------------------------------------------------

workedExamplesSpecProps :: [(String, IO Result)]
workedExamplesSpecProps =
  [ ("E1 justified-clean → accept, arg in, claim justified", quickCheckResult prop_E1)
  , ("E2 open-gap → accept, claim gap", quickCheckResult prop_E2)
  , ("E3 defeat-suite → accept, justified+defeated+contested, all attack kinds", quickCheckResult prop_E3)
  , ("S1 strict nd@1 cert → accept, arg in, claim justified", quickCheckResult prop_S1)
  , ("R1 undeclared-leaf → reject R1", quickCheckResult prop_R1)
  , ("R2 strict-contrary → reject R12", quickCheckResult prop_R2)
  , ("R3 bad-attack-target → reject R10", quickCheckResult prop_R3)
  , ("expected JSON reports every replay preflight reason", quickCheckResult prop_replayPreflightExpectedJson)
  , ("expected JSON reports the escalated group-conflict (R9)", quickCheckResult prop_groupConflictExpectedJson)
  , ("worked-example .core.sexp anchors are fresh (parse+elaborate+encode == committed)", quickCheckResult prop_freshness)
  , ("worked-example expected.json goldens are fresh (elaborate+render == committed)", quickCheckResult prop_expectedJsonFresh)
  , ("coverage matrix: every status, attack kind, and R1/R12/R10 witnessed by the suite", quickCheckResult prop_coverageMatrix)
  ]
