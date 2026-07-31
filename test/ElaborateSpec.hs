-- | Tests for the trusted surface elaborator ("Lara.Elaborate": @Program +
-- Policy → Unit@).
--
-- The crux is the frozen end-to-end slice: parse a committed @.lara@ file with
-- "Lara.Syntax", 'elaborate' it against the shared policy, construct its source
-- 'CheckInput' with 'sourceCheckInput', run it through "Lara.Driver".'runCheck',
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
module ElaborateSpec (elaborateSpecProps) where

import Data.List (isInfixOf)
import Test.QuickCheck

import Lara.AST hiding (Reject)
import Lara.Driver (runCheck)
import Lara.Elaborate
import Lara.Replay (ReplayError, sourceCheckInput)
import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..))
import Lara.Strict (SExpr (..))
import Lara.Syntax (parseProgram, parsePolicy)
import Lara.Wire (Outcome (..), Verdict (..))

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

sourceVerdict :: Program -> Policy -> Unit -> Either ReplayError Verdict
sourceVerdict program policy unit =
  runCheck <$> sourceCheckInput program policy unit

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
      case elaborate defeasibleSuiteSigma (registryOf pol) prog pol of
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
                            [(Prop (Pred "holds") [con "safety_invariant", con "D"], Justified)]
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
      case elaborate defeasibleSuiteSigma (registryOf pol) prog pol of
        Left e -> counterexample ("unexpected ElabError: " ++ elabErrorMessage e) False
        Right unit ->
          counterexample ("expected R13, got " ++ show (sourceVerdict prog pol unit)) $
            fmap verdictOutcome (sourceVerdict prog pol unit)
              === Right (Reject (RejectClass R13))

-- ---------------------------------------------------------------------------
-- Example B — the frozen end-to-end golden (byte-exact)
-- ---------------------------------------------------------------------------

-- | @elaborate@ + @sourceCheckInput@ + @runCheck@ on B reproduces the frozen
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
              [(improvesMAD, Contested), (notImprovesMAD, Contested)]
          }
  pure $ case elaborate defeasibleSuiteSigma (registryOf pol) prog pol of
    Left e -> counterexample ("B: unexpected ElabError: " ++ elabErrorMessage e) False
    Right unit -> fmap verdictOutcome (sourceVerdict prog pol unit) === Right expected

-- ---------------------------------------------------------------------------
-- Example A — the frozen end-to-end golden (the vertical slice)
-- ---------------------------------------------------------------------------

-- | @elaborate@ + @sourceCheckInput@ + @runCheck@ on A reproduces the frozen A0
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
  pure $ case elaborate defeasibleSuiteSigma (registryOf pol) prog pol of
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
              verdictStatuses outcome === [(improvesMAD, Defeated)]
          ]

-- ---------------------------------------------------------------------------
-- Negatives — each mutation yields the expected Left ElabError
-- ---------------------------------------------------------------------------

-- | Replace the whole decl list of a program.
withDecls :: [Decl] -> Program -> Program
withDecls ds p = p {programDecls = ds}

-- | Is a decl the leaf named @l@?
isLeaf :: String -> Decl -> Bool
isLeaf l (DeclLeaf lf) = leafId lf == LeafId l
isLeaf _ _ = False

-- | The proposition of a declared leaf.
leafPropOf :: String -> [Decl] -> Prop
leafPropOf l ds =
  head [leafProp lf | DeclLeaf lf <- ds, leafId lf == LeafId l]

-- | All thirteen negatives share the parsed A + policy; run them in one IO
-- property. Cases 10–13 pin the four 'Lara.Elaborate'.@validateGroups@ error
-- paths (R14 on the @.lara@ door), asserting the same checks in the same order
-- as the wire decoder's @checkGroupInvariants@.
prop_negatives :: Property
prop_negatives = once $ ioProperty $ do
  progA <- loadProgram "examples/A/example.lara"
  pol <- loadPolicy policyPath
  let decls = programDecls progA
      elab p q = elaborate defeasibleSuiteSigma (registryOf q) p q

      -- 1. policy-id mismatch: hand a policy whose id differs from the header.
      polMismatch = pol {policyId = PolicyId "not-empirical-v1"}

      -- 2. unresolved premise: drop leaf e1, so a1's implicit premise
      --    reports(exp_3, effect(M,accuracy,D,positive)) matches nothing.
      progNoE1 = withDecls (filter (not . isLeaf "e1") decls) progA

      -- 3. ambiguous premise: add a second leaf with e1's exact proposition.
      dupE1 =
        DeclLeaf
          (Leaf (LeafId "e1_dup") (leafPropOf "e1" decls) Observed AiExecuted [])
      progDupE1 = withDecls (decls ++ [dupE1]) progA

      -- 4. arity mismatch: drop one positional θ argument from a1's term.
      progBadArity = withDecls (map dropArgArity decls) progA
      dropArgArity (DeclArg a)
        | argId a == ArgId "a1" = DeclArg a {argTerm = shrinkSubst (argTerm a)}
      dropArgArity d = d
      shrinkSubst (SRule r th pr ds hs as) = SRule r (init th) pr ds hs as
      shrinkSubst t = t

      -- 5. undeclared status id.
      progBadStatus = withDecls (decls ++ [DeclStatus (PropId "no_such_claim")]) progA

      -- 6. supports(c1) whose term conclusion ≠ the claim's formal.
      progBadConcl = withDecls (map breakClaim decls) progA
      breakClaim (DeclClaim c)
        | claimId c == PropId "c1" =
            DeclClaim c {claimFormal = Prop (Pred "unrelated") []}
      breakClaim d = d

      -- 7. unknown rule: retarget a1's support term at a rule the policy
      --    never declares.
      progUnknownRule = withDecls (map bogusRule decls) progA
      bogusRule (DeclArg a)
        | argId a == ArgId "a1" = DeclArg a {argTerm = renameRule (argTerm a)}
      bogusRule d = d
      renameRule (SRule _ th pr ds hs as) = SRule (RuleId "no_such_rule") th pr ds hs as
      renameRule t = t

      -- 8. unresolved discharge: repoint a1's discharge targets at an id that
      --    is neither a declared leaf nor a prior argument.
      progBadDischarge = withDecls (map breakDischarge decls) progA
      breakDischarge (DeclArg a)
        | argId a == ArgId "a1" = DeclArg a {argTerm = danglingDisch (argTerm a)}
      breakDischarge d = d
      danglingDisch (SRule r th pr ds hs as) = SRule r th pr (map bustDisch ds) hs as
      danglingDisch t = t
      bustDisch (q, _) = (q, SLeaf (LeafId "no_such_ref"))

      -- 9. challenge target undeclared: repoint d2's challenges(…) at an
      --    undeclared leaf.
      progBadChallenge = withDecls (map breakChallenge decls) progA
      breakChallenge (DeclArg a)
        | argId a == ArgId "d2" =
            DeclArg a {argConcl = Challenges (ChallengesLeaf (LeafId "no_such_leaf"))}
      breakChallenge d = d

      -- 10–13. duplicate-report-group R14 well-formedness (validateGroups):
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
      , counterexample "unresolved premise" $
          isErr "matches no declared leaf" (elab progNoE1 pol)
      , counterexample "ambiguous premise" $
          isErr "ambiguous" (elab progDupE1 pol)
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
-- Runner
-- ---------------------------------------------------------------------------

elaborateSpecProps :: [(String, IO Result)]
elaborateSpecProps =
  [ ("elaborate strict nd@1 cert presentation path accepts", quickCheckResult prop_strictCertificatePresentationAccepts)
  , ("elaborate strict cert missing theory rejects R13", quickCheckResult prop_strictCertificateMissingTheoryRejectsR13)
  , ("elaborate A reproduces the frozen A0 golden (vertical slice)", quickCheckResult prop_A_frozenGolden)
  , ("elaborate B reproduces the frozen A0 golden (byte-exact)", quickCheckResult prop_B_frozenGolden)
  , ("elaborate negatives are located Left ElabError", quickCheckResult prop_negatives)
  ]
