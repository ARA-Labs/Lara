-- | Tests for the trusted surface elaborator ("Lara.Elaborate": @Program +
-- Policy → Unit@).
--
-- The crux is the frozen end-to-end slice: parse a committed @.lara@ file with
-- "Lara.Syntax", lower it against the shared policy with 'prepareSource', run
-- the opaque carrier through 'runSourceCheck',
-- and assert the frozen A0 verdict (@docs/m4a-checklist.md@ §1). IO lives here,
-- never in the elaborator.
--
--   * __Example B__ (`examples/B/example.lara`) reproduces its frozen golden
--     __byte-exact__: @pa\/pb → LUndec@, @c_pos\/c_neg → Contested@ (the 2-cycle).
--   * __Example A__ (`examples/A/example.lara`) reproduces its frozen golden
--     (the vertical slice): @a1 → LOut@ (rebut + undercut + undermine, all
--     in-paper), @d1\/d2\/d3 → LIn@, and @c1 → Defeated@. It exercises
--     implicit-premise reconstruction, θ re-association, all three attack kinds,
--     and the @Challenges@\/@SupportsDerived@ conclusion arms.
--   * __Negatives__ mutate the parsed A/policy in-memory; each yields the
--     expected @Left ElabError@.
--
-- @lara-syntax\@0.3@ adds a second block of properties (grammar App. B):
--
--   * __the expansion invariant__ — @examples\/S2@ rewritten as a @comparison@
--     block elaborates to the /identical/ 'Unit' the hand-written source
--     produces, and replays through @ord\@1@ to the same verdict;
--   * __polarity__ — the same shape under a @lower-is-better@ measurand
--     generates the flipped goal, with @(prem i)@ slots following that policy's
--     premise order (the 0-based index regression, eng review 6A);
--   * __attack paths__ — @a2.binding.leaf@ and @a2.1.leaf@ resolve to the same
--     @[StepPremise 1]@ and the same 'Unit';
--   * __@nl@ interpolation__ — @{cell l}@ and @{{@\/@}}@ expand on the
--     presentation pass (a claim's prose never reaches 'Unit', so that is where
--     B.6 is observable);
--   * __negatives__ — one per located error App. B.3\/B.4\/B.5\/B.6 promises.
module ElaborateSpec (elaborateSpecProps) where

import Data.List (isInfixOf)
import Test.QuickCheck

import Lara.AST hiding (Reject)
import Lara.Admission
  ( admissionAuditArgs
  , admissionAuditAttacks
  , admissionAuditLeaves
  , renderAdmissionRejection
  )
import Lara.Elaborate
-- The bare, admission-free lowering: the A/B differential properties below
-- compare it against the frozen goldens, so this suite is one of the
-- sanctioned escape-hatch callers ("Lara.Elaborate.Internal" header).
import Lara.Elaborate.Internal (elaborate)
-- The @lara-syntax\@0.3@ surface expansion as its own object of study: the
-- interpolated @nl@ of a generated sub-claim never reaches 'Unit', so the
-- presentation-to-presentation pass is where B.6 is observable.
import Lara.Elaborate.Comparison (expandSurface)
import Lara.Sigma (Sort (..))
import Lara.Prop (Prop (..), Term (..))
import Lara.Strict (SExpr (..))
import Lara.Syntax (parseProgram, parsePolicy)
import Lara.Wire (Outcome (..), PublicStatus (..), Verdict (..))

-- ---------------------------------------------------------------------------
-- Shared fixtures
-- ---------------------------------------------------------------------------

con :: String -> Term
con s = TCon (FunSym s) []

-- | @improves(M, accuracy, D)@ — the c1 / c_pos claim formal.
improvesMAD :: Prop
improvesMAD = Prop (Pred "improves") [con "M", con "accuracy", con "D"]

-- | @not_improves(M, accuracy, D)@ — the c_neg claim formal.
notImprovesMAD :: Prop
notImprovesMAD = Prop (Pred "not_improves") [con "M", con "accuracy", con "D"]

-- | Parse the two files a test needs, or fail loudly with the located error.
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

sourceVerdict :: Program -> Policy -> Unit -> Either String Verdict
sourceVerdict program policy _ =
  case prepareSource program policy of
    Left invalid -> Left (renderSourceInvalid invalid)
    Right (SourceRejected rejection) -> Left (renderAdmissionRejection rejection)
    Right (SourceAccepted input) -> Right (sourceResultVerdict (runSourceCheck input))

policyPath :: FilePath
policyPath = "examples/A/empirical-v1.policy.lara"

strictProgramSource :: String
strictProgramSource =
  unlines
    [ "artifact paper_42 at sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
    , "policy strict-v1"
    , "use backends [nd@1]"
    , ""
    , "claim c1"
    , "  nl = \"The safety invariant holds for deployment D\""
    , "  formal = holds(safety_invariant, D)"
    , "  binding = { author = alice, rationale = \"r\", audit-status = reviewed }"
    , ""
    , "leaf e1 : holds(safety_invariant, D)"
    , "  kind = attested"
    , "  provenance = user"
    , "  refs = [evidence/safety_audit.txt#section=invariants]"
    , ""
    , "arg a1 : supports(c1) by certified_citation(safety_invariant, D)"
    , "  assurance = cert(nd@1, sha256:strict-v1-theory-0, (hyp 0))"
    , ""
    , "status c1"
    ]

strictPolicySource :: Bool -> String
strictPolicySource declareTheory =
  unlines $
    [ "policy strict-v1"
    , "sort Property, Scope"
    , "con safety_invariant : Property"
    , "con D : Scope"
    , "pred holds(Property, Scope)"
    , "rule certified_citation(X, D)"
    , "  mode = strict"
    , "  premises = [ holds(X, D) ]"
    , "  conclusion = holds(X, D)"
    , "  allow-trusted = false"
    , "  certifiers = [ (nd@1, sha256:strict-v1-theory-0) ]"
    ]
      ++ ["theory sha256:strict-v1-theory-0 = []" | declareTheory]

-- | The lara-syntax@0.2 strict-certificate path preserves its assurance,
-- threads the policy theory table, and replays through nd@1 to acceptance.
prop_strictCertificatePresentationAccepts :: Property
prop_strictCertificatePresentationAccepts =
  case (parseProgram strictProgramSource, parsePolicy (strictPolicySource True)) of
    (Left e, _) -> counterexample ("program parse failed: " ++ show e) False
    (_, Left e) -> counterexample ("policy parse failed: " ++ show e) False
    (Right prog, Right pol) ->
      case elaborate (registryOf pol) prog pol of
        Left e -> counterexample ("unexpected ElabError: " ++ elabErrorMessage e) False
        Right unit ->
          conjoin
            [ counterexample "surface assurance survives elaboration" $
                lookup (ArgId "a1") (unitArgs unit)
                  === Just
                    ( SRule
                        (RuleId "certified_citation")
                        [ (Param "X", con "safety_invariant")
                        , (Param "D", con "D")
                        ]
                        [SLeaf (LeafId "e1")]
                        []
                        []
                        ( AssuranceCert
                            ( Cert
                                (BackendId "nd")
                                1
                                (TheoryDigest "sha256:strict-v1-theory-0")
                                (SList [SAtom "hyp", SAtom "0"])
                            )
                        )
                    )
            , counterexample "policy theories reach Unit" $
                unitTheories unit
                  === [(TheoryDigest "sha256:strict-v1-theory-0", [])]
            , counterexample "strict certificate replays to accept" $
                fmap verdictOutcome (sourceVerdict prog pol unit)
                  === Right
                    ( Accept
                        { verdictLabels = [(0, LIn)]
                        , verdictEdges = []
                        , verdictStatuses =
                            [ ( Prop (Pred "holds") [con "safety_invariant", con "D"]
                              , Published Justified
                              )
                            ]
                        }
                    )
            ]

-- | A certifier-allowed certificate whose digest is absent from the policy
-- theory table reaches backend replay and is rejected as R13.
prop_strictCertificateMissingTheoryRejectsR13 :: Property
prop_strictCertificateMissingTheoryRejectsR13 =
  case (parseProgram strictProgramSource, parsePolicy (strictPolicySource False)) of
    (Left e, _) -> counterexample ("program parse failed: " ++ show e) False
    (_, Left e) -> counterexample ("policy parse failed: " ++ show e) False
    (Right prog, Right pol) ->
      case elaborate (registryOf pol) prog pol of
        Left e -> counterexample ("unexpected ElabError: " ++ elabErrorMessage e) False
        Right unit ->
          counterexample ("expected R13, got " ++ show (sourceVerdict prog pol unit)) $
            fmap verdictOutcome (sourceVerdict prog pol unit)
              === Right (Reject (RejectClass R13))

-- ---------------------------------------------------------------------------
-- Example B — the frozen end-to-end golden (byte-exact)
-- ---------------------------------------------------------------------------

-- | The safe source path on B reproduces the frozen
-- A0 verdict exactly: @pa → LUndec@, @pb → LUndec@ (the mutual 2-cycle),
-- @c_pos → Contested@, @c_neg → Contested@ (m4a-checklist §1).
prop_B_frozenGolden :: Property
prop_B_frozenGolden = once $ ioProperty $ do
  prog <- loadProgram "examples/B/example.lara"
  pol <- loadPolicy policyPath
  let expected =
        Accept
          { verdictLabels = [(0, LUndec), (1, LUndec)]
          , verdictEdges = [(0, 1), (1, 0)]
          , verdictStatuses =
              [(improvesMAD, Published Contested), (notImprovesMAD, Published Contested)]
          }
  pure $ case elaborate (registryOf pol) prog pol of
    Left e -> counterexample ("B: unexpected ElabError: " ++ elabErrorMessage e) False
    Right unit -> fmap verdictOutcome (sourceVerdict prog pol unit) === Right expected

-- ---------------------------------------------------------------------------
-- Example A — the frozen end-to-end golden (the vertical slice)
-- ---------------------------------------------------------------------------

-- | The safe source path on A reproduces the frozen A0
-- verdict: a1 (the self-defeating support) is driven @out@ by its three
-- unattacked attackers (@d1@ undercut, @d2@ undermine, @d3@ rebut), and c1 is
-- @Defeated@ (m4a-checklist §1). Arguments are indexed in declaration order
-- a1=0, d1=1,
-- d2=2, d3=3. This slice exercises implicit-premise reconstruction, θ
-- re-association, all three attack kinds, and the @Challenges@ / @SupportsDerived@
-- conclusion arms in one graph.
prop_A_frozenGolden :: Property
prop_A_frozenGolden = once $ ioProperty $ do
  prog <- loadProgram "examples/A/example.lara"
  pol <- loadPolicy policyPath
  pure $ case elaborate (registryOf pol) prog pol of
    Left e -> counterexample ("A: unexpected ElabError: " ++ elabErrorMessage e) False
    Right unit -> case sourceVerdict prog pol unit of
      Left err -> counterexample ("A: replay identity error " ++ show err) False
      Right (Verdict _ (Reject rejection)) ->
        counterexample ("A: unexpected reject " ++ show rejection) False
      Right (Verdict _ outcome@Accept{}) ->
        conjoin
          [ counterexample "grounded labels a1→out, d1/d2/d3→in" $
              verdictLabels outcome === [(0, LOut), (1, LIn), (2, LIn), (3, LIn)]
          , counterexample "claim c1 (improves(M,accuracy,D)) → Defeated" $
              verdictStatuses outcome === [(improvesMAD, Published Defeated)]
          ]

-- | The new source carrier is a conservative wrapper for all-admit artifacts:
-- Example A has no admission rows, produces no audit entries, and keeps its
-- frozen verdict.  This catches accidental divergence between @elaborate +
-- the former manual replay chain and the smart source constructor.
prop_A_prepareSourceAllAdmit :: Property
prop_A_prepareSourceAllAdmit = once $ ioProperty $ do
  prog <- loadProgram "examples/A/example.lara"
  pol <- loadPolicy policyPath
  pure $ case prepareSource prog pol of
    Left invalid -> counterexample ("A: unexpected source invalidity " ++ show invalid) False
    Right (SourceRejected rejection) ->
      counterexample ("A: unexpected R8 " ++ renderAdmissionRejection rejection) False
    Right (SourceAccepted input) ->
      let result = runSourceCheck input
          audit = sourceResultAudit result
       in conjoin
            [ admissionAuditLeaves audit === []
            , admissionAuditArgs audit === []
            , admissionAuditAttacks audit === []
            , case verdictOutcome (sourceResultVerdict result) of
                Reject rejection -> counterexample ("A: unexpected reject " ++ show rejection) False
                Accept labels edges statuses ->
                  conjoin
                    [ labels === [(0, LOut), (1, LIn), (2, LIn), (3, LIn)]
                    , edges === [(0, 3), (1, 0), (2, 0), (3, 0)]
                    , statuses === [(improvesMAD, Published Defeated)]
                    ]
            ]

-- ---------------------------------------------------------------------------
-- lara-syntax@0.3 — the `comparison` expansion (grammar App. B.3, plan §5)
-- ---------------------------------------------------------------------------

-- | @examples\/S2@ authored through a @comparison@ block: the same artifact,
-- the same declaration order, with @claim c2@ / @arg a1@ / @arg a2@ replaced by
-- the one block that stands for them. The author writes no @num_lt@, no slot
-- index, and no θ vector.
comparisonProgramSource :: String
comparisonProgramSource =
  unlines
    [ "artifact ord_demo at sha256:5252525252525252525252525252525252525252525252525252525252525252"
    , "policy ord-v1"
    , "use backends [ord@1]"
    , ""
    , "claim c1"
    , "  nl      = \"sys_new outperforms sys_base on ImageNet-val accuracy ({cell e2} vs {cell e1})\""
    , "  formal  = better(sys_new, sys_base, accuracy, imagenet_val)"
    , "  binding = { author = alice, rationale = \"Ordered comparison of two reported accuracy cells.\", audit-status = reviewed }"
    , ""
    , "leaf e1 : reports(exp1, score_cell(sys_base, accuracy, imagenet_val, 0.71))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/accuracy.md#row=sys_base]"
    , ""
    , "leaf e2 : reports(exp1, score_cell(sys_new, accuracy, imagenet_val, 0.74))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/accuracy.md#row=sys_new]"
    , ""
    , "leaf e3 : comparison_setup(sys_new, sys_base, accuracy, imagenet_val, 0.74, 0.71)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [evidence/tables/accuracy.md#caption]"
    , ""
    , "comparison : better(sys_new, sys_base) on accuracy @ imagenet_val"
    , "  relation = strictly-better"
    , "  recheck  = a1"
    , "  bridge   = a2"
    , "  result   = e2"
    , "  baseline = e1"
    , "  binding  = e3"
    , "  claims c2"
    , "    nl      = \"The reported baseline accuracy {cell e1} is strictly below the reported system accuracy {cell e2}\""
    , "    binding = { author = alice, audit-status = reviewed }"
    , "  supports c1"
    , ""
    , "status c1"
    ]

-- | Parse the comparison fixture against @examples\/S2@'s committed policy.
--
-- The policy is used __verbatim__: since D6 it declares the measurand's
-- polarity (App. B.1) and the (relation, polarity) scheme (App. B.2) itself,
-- so the fixture no longer has to append them. Neither declaration reaches
-- 'Unit', which is what lets the expansion be compared against the hand-written
-- source byte for byte.
loadComparisonFixture :: IO (Program, Policy)
loadComparisonFixture = do
  polSrc <- readFile "examples/S2/ord-v1.policy.lara"
  let parsed = (parseProgram comparisonProgramSource, parsePolicy polSrc)
  case parsed of
    (Right prog, Right pol) -> pure (prog, pol)
    (Left e, _) -> error ("comparison fixture: program parse failed: " ++ show e)
    (_, Left e) -> error ("comparison fixture: policy parse failed: " ++ show e)

-- | __The expansion invariant__ (plan §8): the @comparison@ source elaborates
-- to the /same/ 'Unit' the hand-written @examples\/S2@ source produces — not an
-- equivalent one, the same one. Everything the sugar generates (the goal atom,
-- both θ vectors, the @ord\@1@ certificate with its 0-based @(prem i)@ slots,
-- both premise reconstructions) is pinned by this one equality.
prop_comparisonReproducesS2 :: Property
prop_comparisonReproducesS2 = once $ ioProperty $ do
  handProg <- loadProgram "examples/S2/example.lara"
  handPol <- loadPolicy "examples/S2/ord-v1.policy.lara"
  (sugarProg, sugarPol) <- loadComparisonFixture
  pure $ case ( elaborate (registryOf handPol) handProg handPol
              , elaborate (registryOf sugarPol) sugarProg sugarPol
              ) of
    (Left e, _) -> counterexample ("S2 hand-written: " ++ elabErrorMessage e) False
    (_, Left e) -> counterexample ("S2 comparison: " ++ elabErrorMessage e) False
    (Right hand, Right sugar) ->
      conjoin
        [ counterexample "generated arguments match the hand-written ones" $
            unitArgs sugar === unitArgs hand
        , counterexample "the whole Unit is identical" $ sugar === hand
        ]

-- | The generated structure replays: the source expanded from the block reaches
-- the frozen S2 verdict through @ord\@1@, so the generated certificate is one
-- the backend independently accepts (plan §5, "generating certificates adds no
-- trust").
prop_comparisonReplaysToAccept :: Property
prop_comparisonReplaysToAccept = once $ ioProperty $ do
  (prog, pol) <- loadComparisonFixture
  pure $ case elaborate (registryOf pol) prog pol of
    Left e -> counterexample ("unexpected ElabError: " ++ elabErrorMessage e) False
    Right unit ->
      fmap verdictOutcome (sourceVerdict prog pol unit)
        === Right
          ( Accept
              { verdictLabels = [(0, LIn), (1, LIn)]
              , verdictEdges = []
              , verdictStatuses =
                  [ ( Prop
                        (Pred "better")
                        [con "sys_new", con "sys_base", con "accuracy", con "imagenet_val"]
                    , Published Justified
                    )
                  ]
              }
          )

-- | A comparison names the exact evidence leaves its generated arguments
-- consume. An equivalent, unreferenced binding leaf must not make the bridge
-- ambiguous or replace the authored @binding = e3@ choice.
prop_comparisonBindsNamedLeaves :: Property
prop_comparisonBindsNamedLeaves = once $ ioProperty $ do
  (prog, pol) <- loadComparisonFixture
  pure $ case [l | DeclLeaf l <- programDecls prog, leafId l == LeafId "e3"] of
    [bindingLeaf] ->
      let duplicate = bindingLeaf {leafId = LeafId "e3_equiv"}
          withDuplicate = prog {programDecls = DeclLeaf duplicate : programDecls prog}
       in case elaborate (registryOf pol) withDuplicate pol of
            Left e -> counterexample ("unexpected ElabError: " ++ elabErrorMessage e) False
            Right unit ->
              case lookup (ArgId "a2") (unitArgs unit) of
                Just (SRule _ _ premises _ _ _) ->
                  counterexample "the bridge consumes the named binding leaf" $
                    premises ===
                      [ lookupArg (ArgId "a1") unit
                      , SLeaf (LeafId "e3")
                      ]
                other -> counterexample ("missing generated bridge: " ++ show other) False
    other -> counterexample ("expected one e3 fixture leaf, got " ++ show (length other)) False
  where
    lookupArg aid unit = case lookup aid (unitArgs unit) of
      Just term -> term
      Nothing -> error ("missing generated argument " ++ show aid)

-- | Recheck and bridge rules have independent parameter namespaces. Renaming
-- every recheck parameter must preserve the expansion and its generated goal.
prop_comparisonRenamedRecheckParams :: Property
prop_comparisonRenamedRecheckParams = once $ ioProperty $ do
  (prog, pol) <- loadComparisonFixture
  let renamed = mapRule (RuleId "beats_recheck") renameRecheckParams pol
  pure $
    case ( elaborate (registryOf renamed) prog renamed
         , expandSurface renamed prog
         ) of
      (Left e, _) -> counterexample ("unexpected ElabError: " ++ elabErrorMessage e) False
      (_, Left e) -> counterexample ("unexpected expansion error: " ++ elabErrorMessage e) False
      (Right unit, Right expanded) ->
        conjoin
          [ counterexample "the renamed recheck parameter order is preserved" $
              case lookup (ArgId "a1") (unitArgs unit) of
                Just (SRule _ theta _ _ _ _) ->
                  map fst theta === map Param ["RS", "RB", "RQ", "RD", "RExp", "RSv", "RBv"]
                other -> counterexample ("missing generated recheck: " ++ show other) False
          , counterexample "the generated comparison goal is unchanged" $
              lookup
                (PropId "c2")
                [(claimId c, claimFormal c) | DeclClaim c <- programDecls expanded]
                === Just (Prop (Pred "num_lt") [TNum "0.71", TNum "0.74"])
          ]

-- | Scheme lookup is keyed by the full @(relation, polarity)@ pair. Put the
-- opposite-polarity scheme first so a relation-only lookup selects the wrong
-- rule while each scheme remains internally well-formed in its own direction.
prop_comparisonSchemeLookupUsesPolarity :: Property
prop_comparisonSchemeLookupUsesPolarity = once $ ioProperty $ do
  (prog, pol) <- loadComparisonFixture
  let flippedOrder = AtomPat (Pred "num_lt") [PVar (Param "Sv"), PVar (Param "Bv")]
      clone rid newRid rewrite =
        [ rewrite r {ruleId = newRid}
        | r <- policyRules pol
        , ruleId r == rid
        ]
      lowerRecheck =
        clone (RuleId "beats_recheck") (RuleId "lower_recheck") $
          \r -> r {ruleConclusion = flippedOrder}
      lowerBridge =
        clone (RuleId "beats_baseline") (RuleId "lower_bridge") $
          \r -> r {rulePremises = flippedOrder : drop 1 (rulePremises r)}
      lowerScheme =
        ComparisonScheme
          StrictlyBetter
          LowerIsBetter
          (RuleId "lower_recheck")
          (RuleId "lower_bridge")
      both =
        pol
          { policyRules = policyRules pol ++ lowerRecheck ++ lowerBridge
          , policyComparisonSchemes = lowerScheme : policyComparisonSchemes pol
          }
  pure $ case elaborate (registryOf both) prog both of
    Left e -> counterexample ("unexpected ElabError: " ++ elabErrorMessage e) False
    Right unit ->
      case lookup (ArgId "a1") (unitArgs unit) of
        Just (SRule rid _ _ _ _ _) ->
          counterexample "higher-is-better selects the higher-is-better scheme" $
            rid === RuleId "beats_recheck"
        other -> counterexample ("missing generated recheck: " ++ show other) False

-- | Rename every parameter occurrence in the S2 recheck rule. The bridge rule
-- deliberately keeps its original names, making the two key spaces disjoint.
renameRecheckParams :: Rule -> Rule
renameRecheckParams rule =
  rule
    { ruleParams = map rename (ruleParams rule)
    , rulePremises = map renameAtom (rulePremises rule)
    , ruleConclusion = renameAtom (ruleConclusion rule)
    }
  where
    table =
      zip
        (map Param ["S", "B", "Q", "D", "Exp", "Sv", "Bv"])
        (map Param ["RS", "RB", "RQ", "RD", "RExp", "RSv", "RBv"])
    rename p = case lookup p table of
      Just p' -> p'
      Nothing -> p
    renameAtom (AtomPat pred' pats) = AtomPat pred' (map renamePat pats)
    renamePat pat = case pat of
      PVar p -> PVar (rename p)
      PCon f pats -> PCon f (map renamePat pats)
      PLit t -> PLit t

-- | @nl@ interpolation (App. B.6): @{cell l}@ resolves through the same
-- @premiseCell@ helper @ord\@1@ uses and is rendered back through
-- @renderDecimal@; @{{@\/@}}@ become literal braces. Observed on the expansion,
-- because a claim's prose never reaches 'Unit'.
prop_nlInterpolationExpands :: Property
prop_nlInterpolationExpands = once $ ioProperty $ do
  (prog, pol) <- loadComparisonFixture
  let braced = mapComparison (withNl "cells {{a}} {cell e1} vs {cell e2} {{b}}") prog
  pure $
    conjoin
      [ counterexample "directives resolve to the named leaves' cells" $
          (nlOf (PropId "c2") <$> expandSurface pol prog)
            === Right
              (Just "The reported baseline accuracy 0.71 is strictly below the reported system accuracy 0.74")
      , counterexample "ordinary claim directives use the same interpolation contract" $
          (nlOf (PropId "c1") <$> expandSurface pol prog)
            === Right
              (Just "sys_new outperforms sys_base on ImageNet-val accuracy (0.74 vs 0.71)")
      , counterexample "{{ and }} become literal braces" $
          (nlOf (PropId "c2") <$> expandSurface pol braced)
            === Right (Just "cells {a} 0.71 vs 0.74 {b}")
      , counterexample "the expansion leaves no comparison block behind" $
          (blocksLeft <$> expandSurface pol prog) === Right 0
      ]
  where
    nlOf cid p = lookup cid [(claimId c, claimNl c) | DeclClaim c <- programDecls p]
    blocksLeft p = length [() | DeclComparison _ <- programDecls p]

-- ---------------------------------------------------------------------------
-- Polarity: the same source shape under `lower-is-better` flips the goal
-- ---------------------------------------------------------------------------

-- | A @lower-is-better@ policy (perplexity). Its rules are written in that
-- direction — the strict conclusion is @num_lt(Sv, Bv)@, "ours below theirs" —
-- and the scheme binds them to the (strictly-better, lower-is-better) cell of
-- App. B.3's lookup table.
perplexityPolicySource :: String
perplexityPolicySource =
  unlines
    [ "policy perp-v1"
    , ""
    , "sort System, Measurand, Dataset, Experiment, Cell"
    , "con sys_new : System"
    , "con sys_base : System"
    , "con perplexity : Measurand"
    , "con wikitext : Dataset"
    , "con exp1 : Experiment"
    , "con score_cell(System, Measurand, Dataset, Num) : Cell"
    , "pred reports(Experiment, Cell)"
    , "pred num_lt(Num, Num)"
    , "pred better(System, System, Measurand, Dataset)"
    , "pred comparison_setup(System, System, Measurand, Dataset, Num, Num)"
    , ""
    , "rule ppl_recheck(S, B, Q, D, Exp, Sv, Bv)"
    , "  mode       = strict"
    , "  premises   = [ reports(Exp, score_cell(S, Q, D, Sv)),"
    , "                 reports(Exp, score_cell(B, Q, D, Bv)) ]"
    , "  conclusion = num_lt(Sv, Bv)"
    , "  allow-trusted = false"
    , "  certifiers = [ (ord@1, sha256:perp-v1-theory-0) ]"
    , ""
    , "theory sha256:perp-v1-theory-0 = []"
    , ""
    , "rule ppl_bridge(S, B, Q, D, Sv, Bv)"
    , "  mode       = defeasible"
    , "  premises   = [ num_lt(Sv, Bv),"
    , "                 comparison_setup(S, B, Q, D, Sv, Bv) ]"
    , "  conclusion = better(S, B, Q, D)"
    , ""
    , "measurand perplexity : Num where lower-is-better"
    , ""
    , "comparison-scheme strictly-better lower-is-better"
    , "  recheck = ppl_recheck"
    , "  bridge  = ppl_bridge"
    ]

perplexityProgramSource :: String
perplexityProgramSource =
  unlines
    [ "artifact ppl_demo at sha256:5353535353535353535353535353535353535353535353535353535353535353"
    , "policy perp-v1"
    , "use backends [ord@1]"
    , ""
    , "claim c1"
    , "  nl      = \"sys_new beats sys_base on wikitext perplexity\""
    , "  formal  = better(sys_new, sys_base, perplexity, wikitext)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "leaf e1 : reports(exp1, score_cell(sys_base, perplexity, wikitext, 1.2))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/ppl.md#row=sys_base]"
    , ""
    , "leaf e2 : reports(exp1, score_cell(sys_new, perplexity, wikitext, 0.9))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/ppl.md#row=sys_new]"
    , ""
    , "leaf e3 : comparison_setup(sys_new, sys_base, perplexity, wikitext, 0.9, 1.2)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [evidence/tables/ppl.md#caption]"
    , ""
    , "comparison : better(sys_new, sys_base) on perplexity @ wikitext"
    , "  relation = strictly-better"
    , "  recheck  = a1"
    , "  bridge   = a2"
    , "  result   = e2"
    , "  baseline = e1"
    , "  binding  = e3"
    , "  claims c2"
    , "    nl      = \"{cell e2} is below {cell e1}\""
    , "    binding = { author = alice, audit-status = reviewed }"
    , "  supports c1"
    , ""
    , "status c2"
    ]

-- | The polarity test (plan §8, T1-A). The same block shape under a
-- @lower-is-better@ measurand generates the /flipped/ goal — @num_lt(ours,
-- base)@ rather than @num_lt(base, ours)@ — through that policy's own scheme,
-- and the flipped goal is what @ord\@1@ accepts.
--
-- It doubles as the 0-based index regression (6A): @(prem 0)@ is the /result/
-- cell here, because this policy lists the system's premise first. The slots
-- follow the rule, never a fixed convention baked into the elaborator.
prop_comparisonLowerIsBetter :: Property
prop_comparisonLowerIsBetter = once $ ioProperty $
  case (parseProgram perplexityProgramSource, parsePolicy perplexityPolicySource) of
    (Left e, _) -> pure (counterexample ("program parse failed: " ++ show e) False)
    (_, Left e) -> pure (counterexample ("policy parse failed: " ++ show e) False)
    (Right prog, Right pol) -> pure $
      case elaborate (registryOf pol) prog pol of
        Left e -> counterexample ("unexpected ElabError: " ++ elabErrorMessage e) False
        Right unit ->
          conjoin
            [ counterexample "the generated goal is flipped for lower-is-better" $
                unitQueries unit === [Prop (Pred "num_lt") [TNum "0.9", TNum "1.2"]]
            , counterexample "the recheck argument is a full rule instance" $
                lookup (ArgId "a1") (unitArgs unit)
                  === Just
                    ( SRule
                        (RuleId "ppl_recheck")
                        [ (Param "S", con "sys_new")
                        , (Param "B", con "sys_base")
                        , (Param "Q", con "perplexity")
                        , (Param "D", con "wikitext")
                        , (Param "Exp", con "exp1")
                        , (Param "Sv", TNum "0.9")
                        , (Param "Bv", TNum "1.2")
                        ]
                        [SLeaf (LeafId "e2"), SLeaf (LeafId "e1")]
                        []
                        []
                        ( AssuranceCert
                            ( Cert
                                (BackendId "ord")
                                1
                                (TheoryDigest "sha256:perp-v1-theory-0")
                                ( SList
                                    [ SAtom "ordcmp"
                                    , SList [SAtom "prem", SAtom "0"]
                                    , SList [SAtom "prem", SAtom "1"]
                                    ]
                                )
                            )
                        )
                    )
            , counterexample "ord@1 accepts the flipped goal" $
                fmap verdictOutcome (sourceVerdict prog pol unit)
                  === Right
                    ( Accept
                        { verdictLabels = [(0, LIn), (1, LIn)]
                        , verdictEdges = []
                        , verdictStatuses =
                            [(Prop (Pred "num_lt") [TNum "0.9", TNum "1.2"], Published Justified)]
                        }
                    )
            ]

-- ---------------------------------------------------------------------------
-- Attack-path name segments (grammar App. B.4/B.5)
-- ---------------------------------------------------------------------------

-- | Label @beats_baseline@'s two premises, exactly as App. B.4 spells them.
labelBridgePremises :: Policy -> Policy
labelBridgePremises =
  mapRule (RuleId "beats_baseline") $ \r ->
    r {rulePremiseLabels = [Just (PremiseLabel "cmp"), Just (PremiseLabel "binding")]}

-- | Rewrite S4's @undermine x1 a2.1.leaf@ into the given path spelling.
withUnderminePath :: [SurfaceStep] -> Program -> Program
withUnderminePath steps p = p {programDecls = map go (programDecls p)}
  where
    go (DeclAttack (SUndermine w u _)) = DeclAttack (SUndermine w u steps)
    go d = d

-- | Attack-path equivalence (plan §8): with only the second premise labelled,
-- @a2.binding.leaf@ and @a2.1.leaf@ elaborate to the /same/
-- @Undermine … [StepPremise 1]@. The explicit @Nothing@ hole makes this case
-- fail if label indices are derived by zipping only the present labels.
prop_attackPathSpellingsAgree :: Property
prop_attackPathSpellingsAgree = once $ ioProperty $ do
  prog <- loadProgram "examples/S4/example.lara"
  pol0 <- loadPolicy "examples/S4/ord-setting-v1.policy.lara"
  let pol =
        mapRule (RuleId "beats_baseline")
          (\r -> r {rulePremiseLabels = [Nothing, Just (PremiseLabel "binding")]})
          pol0
      byName = withUnderminePath [StepName "binding"] prog
      elab p = elaborate (registryOf pol) p pol
  pure $ case (elab prog, elab byName) of
    (Left e, _) -> counterexample ("S4 by index: " ++ elabErrorMessage e) False
    (_, Left e) -> counterexample ("S4 by label: " ++ elabErrorMessage e) False
    (Right byIndex, Right labelled) ->
      conjoin
        [ counterexample "both spellings resolve to premise slot 1 (0-based)" $
            unitAttacks labelled
              === [Undermine (ArgId "x1") (ArgId "a2") [StepPremise 1]]
        , counterexample "and produce the same Unit" $ labelled === byIndex
        , counterexample "a premise label never reaches Unit" $
            property (all (null . rulePremiseLabels) (unitRules labelled))
        ]

-- ---------------------------------------------------------------------------
-- Negatives — each mutation yields the expected Left ElabError
-- ---------------------------------------------------------------------------

-- | Rewrite the fixture's single @comparison@ block.
mapComparison :: (Comparison -> Comparison) -> Program -> Program
mapComparison f p = p {programDecls = map go (programDecls p)}
  where
    go (DeclComparison c) = DeclComparison (f c)
    go d = d

-- | Replace the sub-block's raw @nl@ (App. B.6 is checked on the raw string).
withNl :: String -> Comparison -> Comparison
withNl s c = c {cmpClaim = (cmpClaim c) {ccNlRaw = s}}

-- | Rewrite one policy rule in place.
mapRule :: RuleId -> (Rule -> Rule) -> Policy -> Policy
mapRule rid f pol = pol {policyRules = map go (policyRules pol)}
  where
    go r
      | ruleId r == rid = f r
      | otherwise = r

-- | Rewrite the policy's single comparison scheme.
mapScheme :: (ComparisonScheme -> ComparisonScheme) -> Policy -> Policy
mapScheme f pol = pol {policyComparisonSchemes = map f (policyComparisonSchemes pol)}

-- | Prepend extra leaves the negative fixtures point @result@ at.
withExtraLeaves :: [Leaf] -> Program -> Program
withExtraLeaves ls p = p {programDecls = map DeclLeaf ls ++ programDecls p}

-- | An observed leaf carrying one reported cell.
cellLeaf :: String -> Prop -> Leaf
cellLeaf l p = Leaf (LeafId l) p Observed AiExecuted []

reportsCell :: String -> String -> String -> String -> String -> String -> Prop
reportsCell pr experiment system measurand dataset value =
  Prop
    (Pred pr)
    [ con experiment
    , TCon (FunSym "score_cell") [con system, con measurand, con dataset, TNum value]
    ]

-- | Every located error App. B.3 and B.6 promise, plus B.4's policy
-- well-formedness and B.5's unresolvable path segment. Message-infix matching,
-- the same idiom as 'prop_negatives'.
prop_comparisonNegatives :: Property
prop_comparisonNegatives = once $ ioProperty $ do
  (prog, pol) <- loadComparisonFixture
  s4prog <- loadProgram "examples/S4/example.lara"
  s4pol <- loadPolicy "examples/S4/ord-setting-v1.policy.lara"
  polNoScheme <- loadPolicy "examples/S2/ord-v1.policy.lara"
  let elab p q = elaborate (registryOf q) p q
      -- Extra leaves the θ negatives point at.
      wrongPred = cellLeaf "e4" (reportsCell "reports" "exp1" "sys_new" "accuracy" "imagenet_val" "0.74")
      otherExp = cellLeaf "e5" (reportsCell "reports" "exp2" "sys_new" "accuracy" "imagenet_val" "0.74")
      otherMeasurand = cellLeaf "e6" (reportsCell "reports" "exp1" "sys_new" "f1" "imagenet_val" "0.74")
      otherDataset = cellLeaf "e9" (reportsCell "reports" "exp1" "sys_new" "accuracy" "test_set" "0.74")
      -- Two one-cell pairing leaves: each matches the same `comparison_setup`
      -- shaped premise, one on the system side and one on the baseline side.
      pairingLeaf l sv bv =
        cellLeaf l (Prop (Pred "comparison_setup") [con "sys_new", con "sys_base", con "accuracy", con "imagenet_val", sv, bv])
      progPlus =
        withExtraLeaves
          [ wrongPred {leafProp = unrelated}
          , otherExp
          , otherMeasurand
          , pairingLeaf "e7" (TNum "0.74") (con "unset")
          , pairingLeaf "e8" (con "unset") (TNum "0.71")
          , otherDataset
          ]
          prog
      unrelated =
        Prop
          (Pred "notes")
          [TCon (FunSym "cell") [con "sys_new", TNum "0.74"]]
      result l c = c {cmpResult = LeafId l}
      -- A second block over the same cells, with non-colliding ids.
      duplicateBlock =
        prog
          { programDecls =
              programDecls prog
                ++ [DeclComparison (renameBlock c) | DeclComparison c <- programDecls prog]
          }
      renameBlock c =
        c
          { cmpRecheckArg = ArgId "b1"
          , cmpBridgeArg = ArgId "b2"
          , cmpClaim = (cmpClaim c) {ccId = PropId "c3"}
          }
      renamedRecheck = mapRule (RuleId "beats_recheck") renameRecheckParams pol
  pure $
    conjoin
      [ counterexample "undeclared measurand" $
          isErr "is not declared by the policy" $
            elab (mapComparison (\c -> c {cmpMeasurand = MeasurandId "no_such"}) prog) pol
      , counterexample "no scheme for the (relation, polarity) pair" $
          isErr "no comparison-scheme" (elab prog (withMeasurandOnly polNoScheme))
      , counterexample "scheme names an undeclared rule" $
          isErr "the policy does not declare" $
            elab prog (mapScheme (\s -> s {csRecheck = RuleId "nope"}) pol)
      , counterexample "recheck rule is not strict" $
          isErr "is not strict" $
            elab prog (mapScheme (\s -> s {csRecheck = RuleId "beats_baseline"}) pol)
      , counterexample "recheck rule lists no ord@1 certifier" $
          isErr "no ord@1 certifier" $
            elab prog (mapRule (RuleId "beats_recheck") (\r -> r {ruleCertifiers = []}) pol)
      , counterexample "bridge rule is not defeasible" $
          isErr "is not defeasible" $
            elab prog (mapScheme (\s -> s {csBridge = RuleId "beats_recheck"}) pol)
      , counterexample "bridge conclusion is not 4-ary favored-first" $
          isErr "favored system first" $
            elab prog (mapRule (RuleId "beats_baseline") (\r -> r {ruleConclusion = threeAry}) pol)
      , counterexample "bridge conclusion is 4-ary but repeats a parameter" $
          isErr "four distinct parameters" $
            elab prog (mapRule (RuleId "beats_baseline") (\r -> r {ruleConclusion = repeatedParams}) pol)
      , counterexample "recheck conclusion is not a 2-ary comparison" $
          isErr "2-ary comparison atom" $
            elab prog (mapRule (RuleId "beats_recheck") (\r -> r {ruleConclusion = threeAry}) pol)
      , counterexample "recheck conclusion contradicts the declared polarity" $
          isErr "concludes in the wrong direction for a higher-is-better measurand" $
            elab prog (flipDirection pol)
      , -- Non-vacuity for the case above: the *same* flipped rules are accepted
        -- once the measurand and scheme declare the polarity they realize. The
        -- check keys on disagreement with the declaration, not on the spelling
        -- of the rule — which is what makes it the direction-of-goodness
        -- contract and not a hard-coded operand order.
        counterexample "…the same flipped rules are fine under lower-is-better" $
          isOk (elab prog (flipDirection (flipDeclaredPolarity pol)))
      , counterexample "certificate slots cannot be attributed" $
          isErr "cannot attribute the certificate's premise slots" $
            elab prog (mapRule (RuleId "beats_recheck") (\r -> r {ruleConclusion = litGoal}) pol)
      , counterexample "authored conclusion is not a 2-ary pair" $
          isErr "not a 2-ary system pair" $
            elab (mapComparison (\c -> c {cmpConclusion = Prop (Pred "better") []}) prog) pol
      , counterexample "authored conclusion predicate mismatch" $
          isErr "does not match the bridge rule" $
            elab (mapComparison (\c -> c {cmpConclusion = worsePair}) prog) pol
      , counterexample "result names a non-leaf" $
          isErr "'no_such' is not a declared leaf" $
            elab (mapComparison (result "no_such") prog) pol
      , counterexample "binding names a non-leaf" $
          isErr "binding = 'no_such' is not a declared leaf" $
            elab (mapComparison (\c -> c {cmpBinding = LeafId "no_such"}) prog) pol
      , counterexample "binding names a declared leaf the bridge does not admit" $
          isErr "binding = 'e1' is not admitted by the selected bridge rule" $
            elab (mapComparison (\c -> c {cmpBinding = LeafId "e1"}) prog) pol
      , counterexample "result and baseline are the same leaf" $
          isErr "name the same leaf" (elab (mapComparison (result "e1") prog) pol)
      , counterexample "result fails the premise-cell obligation" $
          isErr "exactly one numeric literal" (elab (mapComparison (result "e3") prog) pol)
      , counterexample "result matches no premise pattern" $
          isErr "matches no premise pattern" (elab (mapComparison (result "e4") progPlus) pol)
      , counterexample "result matches two premise slots" $
          isErr "matches premise slots" $
            elab prog (mapRule (RuleId "beats_recheck") duplicatePremise pol)
      , counterexample "result and baseline resolve to the same slot" $
          isErr "both resolve to premise slot" $
            elab
              (mapComparison (\c -> c {cmpResult = LeafId "e7", cmpBaseline = LeafId "e8"}) progPlus)
              (mapRule (RuleId "beats_recheck") pairingPremise pol)
      , counterexample "θ-consistency: the two cells come from different experiments" $
          isErr "bind 'Exp' inconsistently" (elab (mapComparison (result "e5") progPlus) pol)
      , counterexample "measurand/on-field inconsistency" $
          isErr "but the block says on accuracy" (elab (mapComparison (result "e6") progPlus) pol)
      , counterexample "renamed recheck params retain measurand/on-field validation" $
          isErr "but the block says on accuracy" $
            elab (mapComparison (result "e6") progPlus) renamedRecheck
      , counterexample "renamed recheck params retain dataset θ-consistency" $
          isErr "bind 'RD' inconsistently" $
            elab (mapComparison (result "e9") progPlus) renamedRecheck
      , counterexample "a rule parameter left unbound by θ" $
          isErr "is not bound by the derived" $
            elab prog (mapRule (RuleId "beats_recheck") addUnusedParam pol)
      , counterexample "generated id collides with a declared claim" $
          isErr "collides with another declaration" $
            elab (mapComparison (\c -> c {cmpClaim = (cmpClaim c) {ccId = PropId "c1"}}) prog) pol
      , counterexample "recheck and bridge ids collide" $
          isErr "collides with another declaration" $
            elab (mapComparison (\c -> c {cmpRecheckArg = cmpBridgeArg c}) prog) pol
      , counterexample "duplicate comparison blocks" $
          isErr "duplicates the comparison claiming" (elab duplicateBlock pol)
      , counterexample "unknown nl directive" $
          isErr "unknown directive" (elab (mapComparison (withNl "{cel e1}") prog) pol)
      , counterexample "unterminated nl brace" $
          isErr "unterminated" (elab (mapComparison (withNl "{cell e1") prog) pol)
      , counterexample "unescaped closing brace" $
          isErr "unescaped '}'" (elab (mapComparison (withNl "a } b") prog) pol)
      , counterexample "{cell …} names a non-leaf" $
          isErr "which is not a declared leaf" $
            elab (mapComparison (withNl "{cell nope}") prog) pol
      , counterexample "{cell …} names a leaf failing the cell obligation" $
          isErr "premise-cell obligation" (elab (mapComparison (withNl "{cell e3}") prog) pol)
      , counterexample "attack path segment resolves to nothing" $
          isErr "names neither a premise label nor a critical question" $
            elab (withUnderminePath [StepName "nope"] s4prog) s4pol
      , counterexample "premise-label vector length matches premise count" $
          isErr "has 1 premise-label entries for 2 premises" $
            elab s4prog (labelBridge [Just (PremiseLabel "cmp")] s4pol)
      , counterexample "duplicate premise label" $
          isErr "duplicate premise label" $
            elab s4prog (labelBridge [Just (PremiseLabel "cmp"), Just (PremiseLabel "cmp")] s4pol)
      , counterexample "premise label spells a terminal marker" $
          isErr "is reserved" $
            elab s4prog (labelBridge [Just (PremiseLabel "leaf"), Nothing] s4pol)
      , counterexample "premise label collides with a question id" $
          isErr "also names a critical question" $
            elab s4prog (withBridgeQuestion (labelBridgePremises s4pol))
      ]
  where
    -- The S2 policy with a measurand but no scheme: the pair lookup, not the
    -- measurand lookup, is what must fail. The committed policy now declares
    -- both, so the scheme table is cleared explicitly rather than assumed empty.
    withMeasurandOnly p =
      p
        { policyMeasurands = [Measurand (MeasurandId "accuracy") SortNum (Just HigherIsBetter)]
        , policyComparisonSchemes = []
        }
    threeAry = AtomPat (Pred "better") [PVar (Param "S"), PVar (Param "B"), PVar (Param "Q")]
    -- 4-ary but binding one parameter twice: the `nub` half of App. B.2's
    -- favored-first shape check, which the arity half above does not reach.
    repeatedParams =
      AtomPat
        (Pred "better")
        [PVar (Param "S"), PVar (Param "S"), PVar (Param "Q"), PVar (Param "D")]
    -- The direction-of-goodness hazard (§1.2), as a *self-consistent* policy
    -- mutation: the recheck conclusion and the bridge's `cmp` premise are
    -- flipped together, so the shared variables still weld the two rules to
    -- each other and nothing downstream notices. The declared polarity is the
    -- only thing left that knows which direction was meant.
    flippedOrder = AtomPat (Pred "num_lt") [PVar (Param "Sv"), PVar (Param "Bv")]
    flipDirection =
      mapRule (RuleId "beats_recheck") (\r -> r {ruleConclusion = flippedOrder})
        . mapRule
          (RuleId "beats_baseline")
          (\r -> r {rulePremises = flippedOrder : drop 1 (rulePremises r)})
    flipDeclaredPolarity p =
      p
        { policyMeasurands =
            [m {measurandPolarity = Just LowerIsBetter} | m <- policyMeasurands p]
        , policyComparisonSchemes =
            [s {csPolarity = LowerIsBetter} | s <- policyComparisonSchemes p]
        }
    -- Both premise slots then match the result leaf equally well.
    duplicatePremise r = r {rulePremises = [systemPremise, systemPremise]}
    systemPremise =
      AtomPat
        (Pred "reports")
        [ PVar (Param "Exp")
        , PCon
            (FunSym "score_cell")
            [PVar (Param "S"), PVar (Param "Q"), PVar (Param "D"), PVar (Param "Sv")]
        ]
    -- One premise mentioning both systems, so `result` and `baseline` land on it.
    pairingPremise r = r {rulePremises = [pairingPat, systemPremise]}
    pairingPat =
      AtomPat
        (Pred "comparison_setup")
        [ PVar (Param "S")
        , PVar (Param "B")
        , PVar (Param "Q")
        , PVar (Param "D")
        , PVar (Param "Sv")
        , PVar (Param "Bv")
        ]
    litGoal = AtomPat (Pred "num_lt") [PLit (TNum "0.5"), PVar (Param "Sv")]
    worsePair = Prop (Pred "worse") [con "sys_new", con "sys_base"]
    addUnusedParam r = r {ruleParams = ruleParams r ++ [Param "Unused"]}
    labelBridge labels = mapRule (RuleId "beats_baseline") (\r -> r {rulePremiseLabels = labels})
    withBridgeQuestion =
      mapRule (RuleId "beats_baseline") $ \r ->
        r
          { ruleQuestions =
              [ Question
                  (QuestionId "binding")
                  (AtomPat (Pred "ok") [])
                  Optional
              ]
          }
    isErr :: String -> Either ElabError Unit -> Property
    isErr marker r = case r of
      Left e ->
        counterexample ("message was: " ++ elabErrorMessage e) $
          property (marker `isInfixOf` elabErrorMessage e)
      Right _ -> counterexample "expected Left, got Right" (property False)

    isOk :: Either ElabError Unit -> Property
    isOk r = case r of
      Right _ -> property True
      Left e ->
        counterexample ("expected Right, got: " ++ elabErrorMessage e) (property False)

-- | Replace the whole decl list of a program.
withDecls :: [Decl] -> Program -> Program
withDecls ds p = p {programDecls = ds}

-- | Is a decl the leaf named @l@?
isLeaf :: String -> Decl -> Bool
isLeaf l (DeclLeaf lf) = leafId lf == LeafId l
isLeaf _ _ = False

-- | The proposition of a declared leaf. A caller naming a leaf the program does
-- not declare is a broken test, so it fails loudly rather than partially.
leafPropOf :: String -> [Decl] -> Prop
leafPropOf l ds =
  case [leafProp lf | DeclLeaf lf <- ds, leafId lf == LeafId l] of
    p : _ -> p
    [] -> error ("leafPropOf: no declared leaf " ++ show l)

-- | The negative cases share the parsed A + policy; run them (and the
-- duplicate-unrelated-leaf positive control) in one IO property. Cases 10 and
-- 11 pin unique surface argument ids and declared attack endpoints before
-- resolution; the final four cases pin the four
-- 'Lara.Elaborate'.@validateGroups@ error paths (R14 on the @.lara@ door),
-- asserting the same checks in the same order as the wire decoder's
-- @checkGroupInvariants@.
prop_negatives :: Property
prop_negatives = once $ ioProperty $ do
  progA <- loadProgram "examples/A/example.lara"
  pol <- loadPolicy policyPath
  let decls = programDecls progA
      elab p q = elaborate (registryOf q) p q

      -- 1. policy-id mismatch: hand a policy whose id differs from the header.
      polMismatch = pol {policyId = PolicyId "not-empirical-v1"}

      -- 2. unresolved inferred premise: drop leaf e1; named resolution must
      --    fail at the source-reference boundary.
      progNoE1 = withDecls (filter (not . isLeaf "e1") decls) progA

      -- 3. A duplicate proposition under a different leaf id is not ambiguous:
      --    inferred syntax selects the authored reference by exact id. The
      --    leaf/prior-argument collision remains covered by ThetaInferenceSpec.
      dupE1 =
        DeclLeaf
          (Leaf (LeafId "e1_dup") (leafPropOf "e1" decls) Observed AiExecuted [])
      progDupE1 = withDecls (decls ++ [dupE1]) progA

      -- Explicit syntax retains the legacy premise resolver. Keep both
      -- failure paths covered independently of inferred reference resolution.
      progExplicitNoE1 = withDecls (map explicitA1 (filter (not . isLeaf "e1") decls)) progA
      progExplicitDupE1 = withDecls (map explicitA1 (decls ++ [dupE1])) progA
      explicitA1 (DeclArg a)
        | argId a == ArgId "a1" =
            DeclArg a {argInstantiation = ExplicitTheta explicitA1Term}
      explicitA1 d = d
      explicitA1Term =
        SRule
          (RuleId "controlled_experiment")
          [ (Param "1", con "M")
          , (Param "2", con "accuracy")
          , (Param "3", con "D")
          , (Param "4", con "exp_3")
          ]
          []
          [ (QuestionId "randomization", SLeaf (LeafId "e2"))
          , (QuestionId "adequate_power", SLeaf (LeafId "e3"))
          , (QuestionId "external_validity", SLeaf (LeafId "e6"))
          ]
          []
          AssuranceNone

      -- 4. arity mismatch: an explicit rule application with no positional
      --    terms is shorter than controlled_experiment's four parameters.
      progBadArity = withDecls (map dropArgArity decls) progA
      dropArgArity (DeclArg a)
        | argId a == ArgId "a1" =
            DeclArg
              a
                { argInstantiation =
                    ExplicitTheta
                      (SRule (RuleId "controlled_experiment") [] [] [] [] AssuranceNone)
                }
      dropArgArity d = d

      -- 5. undeclared status id.
      progBadStatus = withDecls (decls ++ [DeclStatus (PropId "no_such_claim")]) progA

      -- 6. supports(c1) whose term conclusion ≠ the claim's formal.
      progBadConcl = withDecls (map breakClaim decls) progA
      breakClaim (DeclClaim c)
        | claimId c == PropId "c1" =
            DeclClaim c {claimFormal = Prop (Pred "unrelated") []}
      breakClaim d = d

      -- 7. unknown rule: retarget a1's inferred source rule.
      progUnknownRule = withDecls (map bogusRule decls) progA
      bogusRule (DeclArg a)
        | argId a == ArgId "a1" =
            DeclArg a {argInstantiation = renameRule (argInstantiation a)}
      bogusRule d = d
      renameRule (InferTheta _ refs disch holes assurance) =
        InferTheta (RuleId "no_such_rule") refs disch holes assurance
      renameRule (ExplicitTheta term) =
        ExplicitTheta (renameTerm term)
      renameRule inst = inst
      renameTerm (SRule _ th pr ds hs as) = SRule (RuleId "no_such_rule") th pr ds hs as
      renameTerm term = term

      -- 8. unresolved discharge: repoint a1's inferred discharge targets at
      --    an id that is neither a declared leaf nor a prior argument.
      progBadDischarge = withDecls (map breakDischarge decls) progA
      breakDischarge (DeclArg a)
        | argId a == ArgId "a1" =
            DeclArg a {argInstantiation = danglingDisch (argInstantiation a)}
      breakDischarge d = d
      danglingDisch (InferTheta r refs ds hs as) =
        InferTheta r refs [(q, ArgRef "no_such_ref") | (q, _) <- ds] hs as
      danglingDisch (ExplicitTheta term) =
        ExplicitTheta (danglingTerm term)
      danglingDisch inst = inst
      danglingTerm (SRule r th pr ds hs as) =
        SRule r th pr [(q, SLeaf (LeafId "no_such_ref")) | (q, _) <- ds] hs as
      danglingTerm term = term

      -- 9. challenge target undeclared: repoint d2's challenges(…) at an
      --    undeclared leaf.
      progBadChallenge = withDecls (map breakChallenge decls) progA
      breakChallenge (DeclArg a)
        | argId a == ArgId "d2" =
            DeclArg a {argConcl = Challenges (ChallengesLeaf (LeafId "no_such_leaf"))}
      breakChallenge d = d

      -- 10. Duplicate surface ArgId: the .lara front door must reject this
      -- before raw-id retention or attack alignment can observe ambiguity.
      progDupArgId =
        withDecls (decls ++ take 1 [DeclArg a | DeclArg a <- decls]) progA

      -- 11. Undeclared attack endpoint: the .lara front door must reject this
      -- before resolveAttacks can drop it and misalign raw/resolved rows.
      progDanglingAttack =
        withDecls
          (DeclAttack (SRebut (ArgId "no_such_arg") (ArgId "a1")) : decls)
          progA

      -- 12–15. duplicate-report-group R14 well-formedness (validateGroups):
      -- duplicate group id / repeated member / singleton / undeclared member.
      withGroups gs = withDecls (decls ++ map DeclGroup gs) progA
      progDupGroupId =
        withGroups
          [ DupGroup (GroupId "g") [LeafId "e1", LeafId "e2"]
          , DupGroup (GroupId "g") [LeafId "e3", LeafId "e4"]
          ]
      progGroupRepeat = withGroups [DupGroup (GroupId "g") [LeafId "e1", LeafId "e1"]]
      progGroupSingleton = withGroups [DupGroup (GroupId "g") [LeafId "e1"]]
      progGroupDangling =
        withGroups [DupGroup (GroupId "g") [LeafId "e1", LeafId "no_such_leaf"]]

  pure $
    conjoin
      [ counterexample "policy-id mismatch" $
          isErr "policy" (elab progA polMismatch)
      , counterexample "explicit unresolved premise" $
          isErr "matches no declared leaf or prior argument" (elab progExplicitNoE1 pol)
      , counterexample "explicit ambiguous premise" $
          isErr "is ambiguous" (elab progExplicitDupE1 pol)
      , counterexample "unresolved inferred premise" $
          isErr "neither a declared leaf nor prior argument" (elab progNoE1 pol)
      , counterexample "duplicate unrelated leaf remains unambiguous" $
          case elab progDupE1 pol of
            Right unit ->
              case [term | (ArgId "a1", term) <- unitArgs unit] of
                [SRule _ _ [SLeaf (LeafId "e1")] _ _ _] -> property True
                terms ->
                  counterexample
                    ("authored e1 was not retained in a1 premises: " ++ show terms)
                    (property False)
            Left e -> counterexample ("unexpected error: " ++ elabErrorMessage e) (property False)
      , counterexample "arity mismatch" $
          isErr "argument(s)" (elab progBadArity pol)
      , counterexample "undeclared status id" $
          isErr "not a declared claim" (elab progBadStatus pol)
      , counterexample "conclusion mismatch" $
          isErr "the claim formal" (elab progBadConcl pol)
      , counterexample "unknown rule" $
          isErr "unknown rule" (elab progUnknownRule pol)
      , counterexample "unresolved discharge" $
          isErr "neither a declared leaf" (elab progBadDischarge pol)
      , counterexample "challenge target undeclared" $
          isErr "target is not a declared" (elab progBadChallenge pol)
      , counterexample "duplicate argument id" $
          isErr "duplicate argument id" (elab progDupArgId pol)
      , counterexample "undeclared attack endpoint" $
          isErr "attack endpoint is not a declared argument" (elab progDanglingAttack pol)
      , counterexample "duplicate group id" $
          isErr "duplicate group id" (elab progDupGroupId pol)
      , counterexample "group repeats member" $
          isErr "repeats member" (elab progGroupRepeat pol)
      , counterexample "singleton group" $
          isErr "fewer than two members" (elab progGroupSingleton pol)
      , counterexample "group member undeclared" $
          isErr "is not a declared leaf" (elab progGroupDangling pol)
      ]
  where
    -- | The result is a 'Left' whose rendered message contains the marker.
    isErr :: String -> Either ElabError Unit -> Property
    isErr marker r = case r of
      Left e ->
        counterexample ("message was: " ++ elabErrorMessage e) $
          property (marker `isInfixOf` elabErrorMessage e)
      Right _ -> counterexample "expected Left, got Right" (property False)

-- ---------------------------------------------------------------------------
-- lara-syntax@0.7 (#129) — the discharge-target collision matrix
-- ---------------------------------------------------------------------------

-- | The two surfaces a @discharge q with x@ target can arrive on. An explicit
-- rule application carries it as @'SLeaf' ('LeafId' x)@ (@resolveDischarges@);
-- an inferred one carries it as @'ArgRef' x@ (@resolveArgDischarges@). #129
-- put both on one resolver, so every row below is asserted on both.
data DischargePayload = ExplicitPayload | InferredPayload
  deriving (Eq, Show)

-- | The citing argument's @by …@ spelling. Both reach @cited(safety_invariant,
-- D)@ with @e1@ as the single premise; only the payload constructor differs.
payloadSpelling :: DischargePayload -> String
payloadSpelling ExplicitPayload = "cited(safety_invariant, D)"
payloadSpelling InferredPayload = "cited from [e1]"

-- | A one-rule policy with two same-shaped critical questions, so a row can
-- author two discharge lines and observe which error is reported first.
dischargePolicySource :: String
dischargePolicySource =
  unlines
    [ "policy discharge-v1"
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
    , "  question audit  : audited(X) (optional)"
    , "  question audit2 : audited(X) (optional)"
    ]

-- | @leaf x@ — the declared-leaf half of the collision.
dischargeLeafX :: [String]
dischargeLeafX =
  [ "leaf x : audited(safety_invariant)"
  , "  kind       = attested"
  , "  provenance = user"
  , "  refs       = [evidence/audit.txt]"
  , ""
  ]

-- | @arg x@ — the argument half of the collision. Placed before the citing
-- argument it is a /prior/ argument; placed after it, it is not.
dischargeArgX :: [String]
dischargeArgX =
  [ "arg x : supports(c_other) by cited(other_invariant, D)"
  , "  assurance = trusted"
  , ""
  ]

-- | The term @arg x@ elaborates to — what a prior-argument discharge target
-- must resolve to, exactly.
dischargeArgXTerm :: SupportTerm
dischargeArgXTerm =
  SRule
    (RuleId "cited")
    [(Param "X", con "other_invariant"), (Param "S", con "D")]
    [SLeaf (LeafId "e2")]
    []
    []
    AssuranceTrusted

-- | Assemble one matrix row's program: a fixed spine, the declarations the row
-- wants /before/ the citing argument, the citing argument with the row's
-- @discharge@ lines, then the declarations it wants /after/ (the later-argument
-- row is the only user of that slot).
dischargeProgramSource :: DischargePayload -> [String] -> [String] -> [String] -> String
dischargeProgramSource payload before dischargeLines after =
  unlines $
    [ "artifact paper_129 at sha256:" ++ replicate 64 'c'
    , "policy discharge-v1"
    , "use backends [nd@1]"
    , ""
    , "claim c1"
    , "  nl      = \"The safety invariant holds for D\""
    , "  formal  = holds(safety_invariant, D)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "claim c_other"
    , "  nl      = \"The other invariant holds for D\""
    , "  formal  = holds(other_invariant, D)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "leaf e1 : holds(safety_invariant, D)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [evidence/safety.txt]"
    , ""
    , "leaf e2 : holds(other_invariant, D)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [evidence/other.txt]"
    , ""
    ]
      ++ before
      ++ ["arg a_cite : supports(c1) by " ++ payloadSpelling payload]
      ++ dischargeLines
      ++ ["  assurance = trusted", ""]
      ++ after
      ++ ["status c1"]

-- | Elaborate one assembled @#129@ program against 'dischargePolicySource'.
elabDischarge :: String -> Either ElabError Unit
elabDischarge src =
  case (parseProgram src, parsePolicy dischargePolicySource) of
    (Left e, _) -> error ("#129 fixture: program parse failed: " ++ show e)
    (_, Left e) -> error ("#129 fixture: policy parse failed: " ++ show e)
    (Right prog, Right pol) -> elaborate (registryOf pol) prog pol

-- | What a row asserts: either the citing argument's @audit@ discharge target
-- resolves to exactly this term, or elaboration fails with exactly this error.
data DischargeExpect
  = ResolvesTo SupportTerm
  | FailsWith ElabError
  deriving (Show)

-- | The 10-row matrix: {explicit, inferred} payload × {leaf only, prior-arg
-- only, both, absent, later-arg only}. Rows name the /same/ target @x@ in every
-- case, so the only variable is which namespaces declare it.
dischargeMatrix :: [(String, DischargePayload, String, DischargeExpect)]
dischargeMatrix =
  [ (label payload name, payload, dischargeProgramSource payload before body after, expect)
  | payload <- [ExplicitPayload, InferredPayload]
  , (name, before, after, expect) <- rows
  ]
  where
    body = ["  discharge audit with x"]
    label payload name = show payload ++ ": " ++ name
    rows =
      [ ( "declared leaf only resolves to that leaf"
        , dischargeLeafX
        , []
        , ResolvesTo (SLeaf (LeafId "x"))
        )
      , ( "prior argument only resolves to that argument's term"
        , dischargeArgX
        , []
        , ResolvesTo dischargeArgXTerm
        )
      , ( "leaf and prior argument together are AmbiguousDischarge"
        , dischargeLeafX ++ dischargeArgX
        , []
        , FailsWith (AmbiguousDischarge (ArgId "a_cite") (QuestionId "audit") (ArgRef "x"))
        )
      , ( "neither namespace declares it: UnresolvedDischarge"
        , []
        , []
        , FailsWith (UnresolvedDischarge (ArgId "a_cite") (QuestionId "audit") (ArgRef "x"))
        )
      , ( "later argument only is UnresolvedDischarge, never a forward reference"
        , []
        , dischargeArgX
        , FailsWith (UnresolvedDischarge (ArgId "a_cite") (QuestionId "audit") (ArgRef "x"))
        )
      ]

-- | #129: @discharge q with x@ resolves against declared leaves and /prior/
-- arguments under one collision policy, on both payload surfaces.
--
-- Before this, a name carried by both namespaces silently resolved to the leaf
-- — the last carve-out in a reference namespace where the θ resolver
-- ('ThetaReferenceAmbiguous') and the certificate premise-slot resolver
-- ('CertSlotAmbiguous') both already rejected the same collision. Each row
-- asserts the /exact/ resolved term or the /exact/ error constructor, so a
-- future resolver cannot satisfy this by failing for a different reason.
prop_dischargeCollisionMatrix :: Property
prop_dischargeCollisionMatrix = once $ conjoin (map one dischargeMatrix)
  where
    one (name, _, src, expect) =
      counterexample name $ case (expect, elabDischarge src) of
        (ResolvesTo term, Right unit) ->
          counterexample "resolved discharge target" $
            dischargeTargetsOf unit === [(QuestionId "audit", term)]
        (ResolvesTo _, Left e) ->
          counterexample ("expected acceptance, got: " ++ elabErrorMessage e) (property False)
        (FailsWith err, Left e) -> e === err
        (FailsWith _, Right _) ->
          counterexample "expected Left, got Right" (property False)

    -- The citing argument's own discharge map, straight off the Unit.
    dischargeTargetsOf unit =
      case lookup (ArgId "a_cite") (unitArgs unit) of
        Just (SRule _ _ _ ds _ _) -> ds
        other -> error ("#129 fixture: unexpected a_cite term: " ++ show other)

-- | The admission-free elaborator is a sanctioned test/tooling escape hatch,
-- so its shared reference policy must reject duplicate names even though the
-- production 'prepareSource' boundary rejects duplicate leaf ids first.
prop_dischargeDuplicateLeafAmbiguous :: Property
prop_dischargeDuplicateLeafAmbiguous =
  once $
    conjoin
      [ counterexample (show payload) $
          elabDischarge
            ( dischargeProgramSource
                payload
                (dischargeLeafX ++ dischargeLeafX)
                ["  discharge audit with x"]
                []
            )
            === Left
              (AmbiguousDischarge (ArgId "a_cite") (QuestionId "audit") (ArgRef "x"))
      | payload <- [ExplicitPayload, InferredPayload]
      ]

-- | #129 determinism: two faulty @discharge@ lines in one argument report the
-- /first in declaration order/, whichever error family it belongs to. Both
-- orderings are pinned, on both payload surfaces, so the resolver cannot pass
-- by preferring one constructor over the other.
prop_dischargeFirstErrorInDeclarationOrder :: Property
prop_dischargeFirstErrorInDeclarationOrder =
  once $
    conjoin
      [ counterexample (show payload ++ ": " ++ name) $
          elabDischarge
            (dischargeProgramSource payload (dischargeLeafX ++ dischargeArgX) body [])
            === Left expected
      | payload <- [ExplicitPayload, InferredPayload]
      , (name, body, expected) <-
          [ ( "ambiguous first, unresolved second"
            , ["  discharge audit with x", "  discharge audit2 with no_such_ref"]
            , AmbiguousDischarge (ArgId "a_cite") (QuestionId "audit") (ArgRef "x")
            )
          , ( "unresolved first, ambiguous second"
            , ["  discharge audit with no_such_ref", "  discharge audit2 with x"]
            , UnresolvedDischarge (ArgId "a_cite") (QuestionId "audit") (ArgRef "no_such_ref")
            )
          ]
      ]

-- ---------------------------------------------------------------------------
-- Runner
-- ---------------------------------------------------------------------------

elaborateSpecProps :: [(String, IO Result)]
elaborateSpecProps =
  [ ("elaborate strict nd@1 cert presentation path accepts", quickCheckResult prop_strictCertificatePresentationAccepts)
  , ("elaborate strict cert missing theory rejects R13", quickCheckResult prop_strictCertificateMissingTheoryRejectsR13)
  , ("elaborate A reproduces the frozen A0 golden (vertical slice)", quickCheckResult prop_A_frozenGolden)
  , ("prepareSource A default-admit preserves frozen golden", quickCheckResult prop_A_prepareSourceAllAdmit)
  , ("elaborate B reproduces the frozen A0 golden (byte-exact)", quickCheckResult prop_B_frozenGolden)
  , ("elaborate negatives are located Left ElabError", quickCheckResult prop_negatives)
  , ("#129 discharge collision matrix (payload x namespace)", quickCheckResult prop_dischargeCollisionMatrix)
  , ("#129 duplicate leaf discharge is ambiguous", quickCheckResult prop_dischargeDuplicateLeafAmbiguous)
  , ("#129 discharge reports the first faulty line in declaration order", quickCheckResult prop_dischargeFirstErrorInDeclarationOrder)
  , ("comparison expansion reproduces the hand-written S2 Unit", quickCheckResult prop_comparisonReproducesS2)
  , ("comparison expansion replays through ord@1 to accept", quickCheckResult prop_comparisonReplaysToAccept)
  , ("comparison binds the exact named evidence leaves", quickCheckResult prop_comparisonBindsNamedLeaves)
  , ("nl {cell …} and {{}} expand in the elaborator", quickCheckResult prop_nlInterpolationExpands)
  , ("lower-is-better generates the flipped goal", quickCheckResult prop_comparisonLowerIsBetter)
  , ("attack-path label and index spellings agree (0-based)", quickCheckResult prop_attackPathSpellingsAgree)
  , ("lara-syntax@0.3 negatives are located Left ElabError", quickCheckResult prop_comparisonNegatives)
  , ("comparison keeps recheck and bridge parameter namespaces independent", quickCheckResult prop_comparisonRenamedRecheckParams)
  , ("comparison scheme lookup uses relation and polarity", quickCheckResult prop_comparisonSchemeLookupUsesPolarity)
  ]
