-- | Golden verdicts for E1–E5 / R1–R3 plus strict-certificate example S1;
-- the teaching examples A and B join them in 'examplePolicies' for the
-- freshness and coverage properties, together with the D3 agreement-map and
-- the three D1 rebuttal-replay rounds (round0–round2) — fifteen examples in all.
--
-- Each property loads the committed @.lara@ artifact and its co-located policy
-- with "Lara.Syntax", prepares the pair with 'prepareSource', runs the opaque
-- carrier through 'runSourceCheck', and asserts the frozen identity-bearing verdict —
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
--   * __E4__ @reinstatement@   — 'Accept'; justified UNDER each attack kind
--     (attacker defeated by an unattacked defender).
--   * __E5__ @contested-beyond-rebut@ — 'Accept'; contested via undermine- and
--     undercut-native 2-cycles, plus gap amid attacks.
--   * __R1__ @undeclared-leaf@ — 'Reject' R1  (leaf not in Γ).
--   * __R2__ @strict-contrary@ — 'Reject' R12 (policy §8.1 Path-B well-formedness).
--   * __R3__ @bad-attack-target@ — 'Reject' R10 (rebut on a leaf occurrence).
--   * __S1__ @strict-cert@ — 'Accept'; nd@1 cert replay; status justified.
--   * __agreement-map__ @agreement-v1@ — 'Accept'; a cross-paper agreement map:
--     a same-atom contrary pair contested via a rebut 2-cycle, and a
--     setting-index-mismatch pair left justified (zero attacks).
--
-- A final __freshness__ property re-derives all fifteen @example.core.sexp@
-- anchors (A, B, E1–E5, R1–R3, S1, agreement-map, and the D1 rebuttal-replay
-- rounds round0–round2) from their surface @.lara@ + policy and asserts the
-- committed bytes match, guarding against surface/anchor drift.
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
import Lara.Admission (renderAdmissionAudit, renderAdmissionRejection)
import Lara.Elaborate
  ( PreparedSource (..)
  , SourceResult
  , defeasibleSuiteSigma
  , elabErrorMessage
  , prepareSource
  , renderSourceInvalid
  , registryOf
  , runSourceCheck
  , sourceResultCheckInput
  , sourceResultVerdict
  )
-- The bare, admission-free lowering: this suite pins the elaborator's own
-- output (the @.core.sexp@ anchors), so it is one of the sanctioned
-- escape-hatch callers described in the "Lara.Elaborate.Internal" header.
import Lara.Elaborate.Internal (elaborate)
import Lara.ExpectedJson (JValue (..), expectedJson, expectedJsonValue)
import Lara.Replay
  ( CoreVersion (..)
  , mkCheckInput
  , mkReplayId
  , replayErrorMessage
  )
import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..))
import Lara.Syntax (parsePolicy, parseProgram)
import Lara.Strict (SExpr (..))
import Lara.Wire (PublicStatus (..), conditionalStatus, Outcome (..), Verdict (..), encodeCheckInput, printSExpr)

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

-- | @better(s, b, q, d)@ over four nullary-constant names (agreement-map, D3).
betterP :: String -> String -> String -> String -> Prop
betterP s b q d = Prop (Pred "better") [con s, con b, con q, con d]

-- | @not_better(s, b, q, d)@ (agreement-map, D3).
notBetterP :: String -> String -> String -> String -> Prop
notBetterP s b q d = Prop (Pred "not_better") [con s, con b, con q, con d]
-- | The D1 rebuttal-replay benchmark claim @performs(apt, dense_baseline, openllm_avg)@.
performsP :: Prop
performsP = Prop (Pred "performs") [con "apt", con "dense_baseline", con "openllm_avg"]

-- | The D1 rebuttal-replay ablation claim
-- @contributes(kurtosis_salience, apt_llama2_7b, openllm_avg)@.
contributesP :: Prop
contributesP =
  Prop (Pred "contributes") [con "kurtosis_salience", con "apt_llama2_7b", con "openllm_avg"]

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
  , ("examples/E4", "empirical-v2.policy.lara")
  , ("examples/E5", "empirical-v2.policy.lara")
  , ("examples/R1", "empirical-v1.policy.lara")
  , ("examples/R2", "strict-bad-v1.policy.lara")
  , ("examples/R3", "empirical-v1.policy.lara")
  , ("examples/S1", "strict-v1.policy.lara")
  , ("examples/agreement-map", "agreement-v1.policy.lara")
  , ("examples/rebuttal-replay/round0", "rebuttal-v1.policy.lara")
  , ("examples/rebuttal-replay/round1", "rebuttal-v1.policy.lara")
  , ("examples/rebuttal-replay/round2", "rebuttal-v1.policy.lara")
  , ("examples/running-example/run1", "empirical-v1.policy.lara")
  , ("examples/running-example/run2", "empirical-v1.policy.lara")
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
  pure $ case preparedResult prog pol of
    Left err -> counterexample (dir ++ ": " ++ err) False
    Right result -> k (sourceResultVerdict result)

preparedResult :: Program -> Policy -> Either String SourceResult
preparedResult prog pol =
  case prepareSource defeasibleSuiteSigma prog pol of
    Left invalid -> Left ("source invalid: " ++ renderSourceInvalid invalid)
    Right (SourceRejected rejection) ->
      Left ("admission rejection: " ++ renderAdmissionRejection rejection)
    Right (SourceAccepted input) -> Right (runSourceCheck input)

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
              verdictStatuses outcome === [(improves "M" "D", Published Justified)]
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
              verdictStatuses outcome === [(improves "M" "D", Published Gap)]
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
                === [ (improves "M_j" "D_j", Published Justified)
                    , (improves "M_d" "D_d", Published Defeated)
                    , (improves "M_c" "D_c", Published Contested)
                    , (notImproves "M_c" "D_c", Published Contested)
                    ]
          ]

-- | E4: reinstatement — three claims stay justified UNDER an attack (one per
-- attack kind) because each attacker is itself defeated by an unattacked
-- defender. Arg indices are declaration order a_r=0, a_rn=1, d_sr=2, a_u=3,
-- n_ng=4, n_rm=5, a_x=6, x_shift=7, x_aud=8.
prop_E4 :: Property
prop_E4 = once $ ioProperty $
  runExample "examples/E4" "empirical-v2.policy.lara" $ \v ->
    case verdictOutcome v of
      Reject rejection -> counterexample ("E4: unexpected reject " ++ show rejection) False
      outcome@Accept{} ->
        conjoin
          [ counterexample "E4 labels: a_r/a_u/a_x reinstated in, attackers out, defenders in" $
              verdictLabels outcome
                === [ (0, LIn), (1, LOut), (2, LIn)
                    , (3, LIn), (4, LOut), (5, LIn)
                    , (6, LIn), (7, LOut), (8, LIn)
                    ]
          , counterexample "E4 statuses: c_r/c_u/c_x justified under rebut/undermine/undercut, c_rn defeated" $
              verdictStatuses outcome
                === [ (improves "M_r" "D_r", Published Justified)
                    , (notImproves "M_r" "D_r", Published Defeated)
                    , (improves "M_u" "D_u", Published Justified)
                    , (improves "M_x" "D_x", Published Justified)
                    ]
          ]

-- | E5: contested via an undermine 2-cycle (context V) and an undercut 2-cycle
-- (context W), plus a gap claim in a unit full of attacks (context G). Arg
-- indices are declaration order a_v=0, m_ng=1, m_g=2, a_w=3, w_shift=4, w_aud=5.
prop_E5 :: Property
prop_E5 = once $ ioProperty $
  runExample "examples/E5" "empirical-v2.policy.lara" $ \v ->
    case verdictOutcome v of
      Reject rejection -> counterexample ("E5: unexpected reject " ++ show rejection) False
      outcome@Accept{} ->
        conjoin
          [ counterexample "E5 labels: both cycles and both support args undec" $
              verdictLabels outcome
                === [(0, LUndec), (1, LUndec), (2, LUndec), (3, LUndec), (4, LUndec), (5, LUndec)]
          , counterexample "E5 statuses: c_v contested (undermine), c_w contested (undercut), c_g gap" $
              verdictStatuses outcome
                === [ (improves "M_v" "D_v", Published Contested)
                    , (improves "M_w" "D_w", Published Contested)
                    , (improves "M_g" "D_g", Published Gap)
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
              verdictStatuses outcome === [(holdsP "safety_invariant" "D", Published Justified)]
          ]

-- | agreement-map (D3, issue #64): a cross-paper agreement map at real-corpus
-- grain. The genuine-disagreement pair (P1) shares the SAME (S,B,Q,D) atoms, so
-- @better@/@not_better@ form a contrary instance ⇒ a rebut 2-cycle ⇒ both
-- @contested@. The setting-mismatch pair (P2) differs ONLY in the setting index
-- D, so the contrary pattern does not unify ⇒ ZERO attacks ⇒ both @justified@.
-- Arg indices in declaration order pa=0, pb=1, pc=2, pd=3.
prop_agreementMap :: Property
prop_agreementMap = once $ ioProperty $
  runExample "examples/agreement-map" "agreement-v1.policy.lara" $ \v ->
    case verdictOutcome v of
      Reject rejection -> counterexample ("agreement-map: unexpected reject " ++ show rejection) False
      outcome@Accept{} ->
        conjoin
          [ counterexample "agreement-map labels: pa/pb undec (2-cycle), pc/pd in (unattacked)" $
              verdictLabels outcome
                === [(0, LUndec), (1, LUndec), (2, LIn), (3, LIn)]
          , counterexample "agreement-map statuses: P1 contested×2 (same atoms), P2 justified×2 (setting mismatch)" $
              verdictStatuses outcome
                === [ (betterP "apt" "cofi" "accuracy" "roberta_mnli_s60", Published Contested)
                    , (notBetterP "apt" "cofi" "accuracy" "roberta_mnli_s60", Published Contested)
                    , (betterP "magnitude_pruning" "dense_baseline" "accuracy" "bert_glue_s50", Published Justified)
                    , (notBetterP "magnitude_pruning" "dense_baseline" "accuracy" "llama_openllm_s90", Published Justified)
                    ]
          ]

-- ---------------------------------------------------------------------------
-- D1 rebuttal replay — the paper+reviews trajectory (issue #62)
-- ---------------------------------------------------------------------------

-- | The co-located rebuttal-v1 policy basename (in each round's dir).
rebuttalBase :: FilePath
rebuttalBase = "rebuttal-v1.policy.lara"

-- | D1 round 0 (submission): the paper alone. Both support args unattacked and @in@;
-- the kurtosis ablation has no arg (variance CQ unmet) ⇒ gap. Arg order a_bench=0, a_meas=1.
prop_D1Round0 :: Property
prop_D1Round0 = once $ ioProperty $
  runExample "examples/rebuttal-replay/round0" rebuttalBase $ \v ->
    case verdictOutcome v of
      Reject rejection -> counterexample ("D1 round0: unexpected reject " ++ show rejection) False
      outcome@Accept{} ->
        conjoin
          [ counterexample "D1 round0 labels: a_bench in, a_meas in" $
              verdictLabels outcome === [(0, LIn), (1, LIn)]
          , counterexample "D1 round0 statuses: c_bench/c_measure justified, c_kurt gap" $
              verdictStatuses outcome
                === [ (performsP, Published Justified)
                    , (holdsP "low_memory_footprint" "apt", Published Justified)
                    , (contributesP, Published Gap)
                    ]
          ]

-- | D1 round 1 (reviews): three reviewer attacks. The undermine (d_um) + rebut (d_rebut) drive
-- a_bench out; the undercut (d_meas) drives a_meas out; c_kurt stays gap. Arg order a_bench=0,
-- a_meas=1, d_um=2, d_rebut=3, d_meas=4.
prop_D1Round1 :: Property
prop_D1Round1 = once $ ioProperty $
  runExample "examples/rebuttal-replay/round1" rebuttalBase $ \v ->
    case verdictOutcome v of
      Reject rejection -> counterexample ("D1 round1: unexpected reject " ++ show rejection) False
      outcome@Accept{} ->
        conjoin
          [ counterexample "D1 round1 labels: both paper args out, three reviewer attacks in" $
              verdictLabels outcome
                === [(0, LOut), (1, LOut), (2, LIn), (3, LIn), (4, LIn)]
          , counterexample "D1 round1 statuses: c_bench/c_measure defeated, c_kurt gap" $
              verdictStatuses outcome
                === [ (performsP, Published Defeated)
                    , (holdsP "low_memory_footprint" "apt", Published Defeated)
                    , (contributesP, Published Gap)
                    ]
          ]

-- | D1 round 2 (rebuttal): the author reinstates a_bench (both reviewer attackers defeated),
-- concedes a_meas (no defense), and discharges the c_kurt gap with variance runs. Arg order
-- a_bench=0, a_meas=1, d_um=2, d_rebut=3, d_meas=4, a_kurt=5, r_um=6, r_rebut=7.
prop_D1Round2 :: Property
prop_D1Round2 = once $ ioProperty $
  runExample "examples/rebuttal-replay/round2" rebuttalBase $ \v ->
    case verdictOutcome v of
      Reject rejection -> counterexample ("D1 round2: unexpected reject " ++ show rejection) False
      outcome@Accept{} ->
        conjoin
          [ counterexample "D1 round2 labels: a_bench reinstated in, a_meas out, attackers out, defenders in" $
              verdictLabels outcome
                === [ (0, LIn), (1, LOut), (2, LOut), (3, LOut)
                    , (4, LIn), (5, LIn), (6, LIn), (7, LIn)
                    ]
          , counterexample "D1 round2 statuses: c_bench justified, c_measure defeated, c_kurt justified" $
              verdictStatuses outcome
                === [ (performsP, Published Justified)
                    , (holdsP "low_memory_footprint" "apt", Published Defeated)
                    , (contributesP, Published Justified)
                    ]
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

-- | For every example (all fifteen: A, B, E1–E5, R1–R3, S1, agreement-map, and
-- the D1 rebuttal-replay rounds round0–round2), re-running the full
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
          case preparedResult prog pol of
            Left err -> counterexample (dir ++ ": " ++ err) False
            Right result ->
              case sourceResultCheckInput result of
                Left audit ->
                  counterexample
                    ( dir
                        ++ ": legacy core artifacts cannot encode source admission: "
                        ++ renderAdmissionAudit audit
                    )
                    False
                Right input ->
                  counterexample (dir ++ ": .core.sexp is stale — regenerate with scripts/gen-worked-examples.hs") $
                    (printSExpr (encodeCheckInput input) ++ "\n") === committed
        (pr, pp) ->
          counterexample (dir ++ ": parse failed: " ++ show pr ++ " / " ++ show pp) (property False)

-- | For every example (all fifteen), re-render @expected.json@ from the elaborated
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
      pure $ case preparedResult prog pol of
        Left err -> counterexample (dir ++ ": " ++ err) False
        Right result ->
          case sourceResultCheckInput result of
            Left audit ->
              counterexample
                ( dir
                    ++ ": legacy core artifacts cannot encode source admission: "
                    ++ renderAdmissionAudit audit
                )
                False
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

-- | The attacked argument of a wire attack (for measured label-cell coverage).
attackTargetId :: Attack -> ArgId
attackTargetId (Rebut _ u) = u
attackTargetId (Undercut _ u _) = u
attackTargetId (Undermine _ u _) = u

-- | For one accepted example, the (attack-kind, target-label) pairs its
-- declared attacks realize — the measured form of \"a claim can be justified
-- while attacked\" (target in), \"contested is not a rebut artifact\" (target
-- undec via undercut\/undermine), and E3's defeats (target out). Arg order in
-- 'unitArgs' is label-index order, so the pairing is positional.
attackCells :: Unit -> Outcome -> [(String, Label)]
attackCells u outcome = case outcome of
  Reject _ -> []
  Accept{} ->
    [ (attackKind k, l)
    | k <- unitAttacks u
    , Just i <- [lookupIndex (attackTargetId k) (map fst (unitArgs u))]
    , Just l <- [lookup i (verdictLabels outcome)]
    ]
  where
    lookupIndex x xs = lookup x (zip xs [0 :: Int ..])

-- | The measured coverage of the whole suite: every accept status, every attack
-- kind, and the three rejection classes are __read off the elaborated units and
-- their verdicts__ (docs/worked-examples-plan.md §1, docs/m4a-checklist.md §2).
-- This turns the coverage matrix into evidence, not a prose claim: if some cell
-- stops being witnessed (a status vanishes, an attack kind is dropped, a reject
-- reclassifies), this fails.
--
-- The suite is the §1 examples E1–E3 / R1–R3, the M5 worked cases E4/E5, the
-- two teaching examples A and B, strict-certificate example S1, plus the D3
-- agreement-map and the three D1 rebuttal-replay rounds round0–round2 — all
-- fifteen in 'examplePolicies'.
prop_coverageMatrix :: Property
prop_coverageMatrix = once $ ioProperty $ do
  verdicts <- mapM loadVerdict examplePolicies -- [(dir, Either err Verdict)]
  units <- mapM loadUnit examplePolicies -- [(dir, Unit)]
  let elabErrs = [dir ++ ": " ++ e | (dir, Left e) <- verdicts]
      statuses = sort (nubOrd [conditionalStatus s | (_, Right (Verdict _ (Accept _ _ sts))) <- verdicts, (_, s) <- sts])
      attackTags = sort (nubOrd [attackKind k | (_, u) <- units, k <- unitAttacks u])
      rejects = sort (nubOrd [r | (_, Right (Verdict _ (Reject r))) <- verdicts])
      outcomes = [(dir, o) | (dir, Right (Verdict _ o)) <- verdicts]
      cells =
        sort . nubOrd $
          [ cell
          | (dir, u) <- units
          , Just o <- [lookup dir outcomes]
          , cell <- attackCells u o
          ]
      gapAmidAttacks =
        or
          [ not (null (unitAttacks u)) && Published Gap `elem` map snd sts
          | (dir, u) <- units
          , Just (Accept _ _ sts) <- [lookup dir outcomes]
          ]
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
      , -- The M5/T4 label cells: every attack kind must be witnessed with an
        -- attacked target that survives (LIn — reinstatement, E4), one that is
        -- defeated (LOut — E3/A), and one left undecided (LUndec — contested
        -- beyond rebut, E5).
        counterexample
          ("attack-kind × target-label coverage incomplete — witnessed " ++ show cells)
          ( all
              (`elem` cells)
              [ (kind, l)
              | kind <- ["rebut", "undercut", "undermine"]
              , l <- [LIn, LOut, LUndec]
              ]
          )
      , counterexample
          "no example witnesses a gap claim in a unit that carries attacks (E5 context G)"
          gapAmidAttacks
      ]

-- | Load + elaborate + run one example to a labelled 'Verdict' (or its
-- 'elabErrorMessage' on the left).
loadVerdict :: (FilePath, FilePath) -> IO (FilePath, Either String Verdict)
loadVerdict (dir, policyBase) = do
  prog <- loadProgram (dir ++ "/example.lara")
  pol <- loadPolicy (dir ++ "/" ++ policyBase)
  pure $ (,) dir $ sourceResultVerdict <$> preparedResult prog pol

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
  , ("E4 reinstatement → accept, justified UNDER rebut/undermine/undercut", quickCheckResult prop_E4)
  , ("E5 contested via undermine+undercut cycles, gap amid attacks", quickCheckResult prop_E5)
  , ("S1 strict nd@1 cert → accept, arg in, claim justified", quickCheckResult prop_S1)
  , ("agreement-map (D3): P1 contested×2 (same atoms), P2 justified×2 (setting mismatch)", quickCheckResult prop_agreementMap)
  , ("D1 round0 submission → accept, two justified, one gap", quickCheckResult prop_D1Round0)
  , ("D1 round1 reviews → accept, undermine+rebut+undercut, two defeated, gap", quickCheckResult prop_D1Round1)
  , ("D1 round2 rebuttal → accept, reinstate + concede + gap discharge", quickCheckResult prop_D1Round2)
  , ("R1 undeclared-leaf → reject R1", quickCheckResult prop_R1)
  , ("R2 strict-contrary → reject R12", quickCheckResult prop_R2)
  , ("R3 bad-attack-target → reject R10", quickCheckResult prop_R3)
  , ("expected JSON reports every replay preflight reason", quickCheckResult prop_replayPreflightExpectedJson)
  , ("expected JSON reports the escalated group-conflict (R9)", quickCheckResult prop_groupConflictExpectedJson)
  , ("worked-example .core.sexp anchors are fresh (parse+elaborate+encode == committed)", quickCheckResult prop_freshness)
  , ("worked-example expected.json goldens are fresh (elaborate+render == committed)", quickCheckResult prop_expectedJsonFresh)
  , ("coverage matrix: every status, attack kind, kind×label cell, and R1/R12/R10 witnessed", quickCheckResult prop_coverageMatrix)
  ]
