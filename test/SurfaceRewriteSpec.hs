-- | The @lara-syntax\@0.3@ acceptance suite (plan §8): the committed worked
-- examples rewritten onto the @comparison@ surface must elaborate to the
-- __byte-identical__ 'Unit' their hand-written @\@0.2@ sources produced.
--
-- Not an equivalent unit — the same one. That is the whole review surface of
-- the surface track, and it is what makes the sugar reviewable at all: if the
-- expansion reproduces the artifact the author used to write by hand, every
-- property already proved about that artifact (its verdict, its wire anchor,
-- its differential twin, its Lean replay) transfers unchanged, and the new
-- forms cannot have smuggled anything into the core.
--
-- __Why the fixtures are the pre-rewrite sources.__ Each property below
-- elaborates a verbatim copy of the @\@0.2@ @example.lara@ that
-- @examples\/S2@, @S3@ and @S4@ carried before the rewrite, and compares its
-- 'Unit' against the one the committed @\@0.3@ source produces today. The
-- comparison is self-contained: it does not consult the generated
-- @.core.sexp@ anchors, so it still fails if a future change moves the
-- committed source and its anchor together.
--
-- Both sides elaborate against the __same committed policy file__, the one
-- carrying the @\@0.3@ measurand, scheme, and premise labels. That is
-- deliberate and is a second assertion: those three declarations are
-- surface-track only, so a @\@0.2@ program elaborated against a @\@0.3@ policy
-- must be untouched by them.
--
-- Beyond identity, this module carries the rest of plan §8's example-level
-- checks:
--
--   * __relation__ — @at-least-as-good@ selects @tie_recheck@\/@no_worse@ and
--     generates @num_le@, and a relation the policy declares no scheme for is a
--     located error rather than a silent fallback;
--   * __polarity__ — @examples\/S5@'s @lower-is-better@ measurand emits the
--     mirrored goal, which @ord\@1@ then accepts on replay;
--   * __S4 still defeats the bridge__ — generated structure is attackable at
--     exactly the point hand-written structure was;
--   * __attack-path equivalence__ — @a2.binding.leaf@ and @a2.1.leaf@ resolve to
--     the same 'Undermine' at the same 0-based premise, and each round-trips in
--     the spelling it was authored in.
module SurfaceRewriteSpec (surfaceRewriteSpecProps) where

import Test.QuickCheck

import Lara.AST
  ( Arg (..)
  , ArgId (..)
  , Attack (..)
  , Claim (..)
  , Comparison (..)
  , Decl (..)
  , Label (..)
  , Policy
  , Program (..)
  , PropId (..)
  , Relation (..)
  , RuleId (..)
  , Status (..)
  , Step (..)
  , SupportTerm (..)
  , Unit (..)
  )
import Lara.Admission (renderAdmissionRejection)
import Lara.Elaborate
  ( PreparedSource (..)
  , defeasibleSuiteSigma
  , elabErrorMessage
  , prepareSource
  , renderSourceInvalid
  , runSourceCheck
  , sourceResultVerdict
  )
import Lara.Elaborate.Comparison (expandSurface)
import Lara.Elaborate.Internal (elaborate, registryOf)
import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..))
import Lara.Syntax (parsePolicy, parseProgram, printProgram)
import Lara.Wire (Outcome (..), Verdict (..), conditionalStatus)

import Data.List (isPrefixOf, isInfixOf)

-- ---------------------------------------------------------------------------
-- Loading
-- ---------------------------------------------------------------------------

loadPolicy :: FilePath -> IO Policy
loadPolicy path = do
  src <- readFile path
  case parsePolicy src of
    Right p -> pure p
    Left e -> error (path ++ ": parse failed: " ++ show e)

loadProgram :: FilePath -> IO Program
loadProgram path = do
  src <- readFile path
  case parseProgram src of
    Right p -> pure p
    Left e -> error (path ++ ": parse failed: " ++ show e)

parseFixture :: String -> String -> Program
parseFixture name src = case parseProgram src of
  Right p -> p
  Left e -> error (name ++ ": fixture parse failed: " ++ show e)

elab :: Policy -> Program -> Either String Unit
elab pol prog = case elaborate defeasibleSuiteSigma (registryOf pol) prog pol of
  Left e -> Left (elabErrorMessage e)
  Right u -> Right u

-- | Run one prepared source all the way to its 'Verdict', as @app\/Main.hs@
-- does for a @.lara@ file.
runToVerdict :: Policy -> Program -> Either String Verdict
runToVerdict pol prog = case prepareSource defeasibleSuiteSigma prog pol of
  Left invalid -> Left ("source invalid: " ++ renderSourceInvalid invalid)
  Right (SourceRejected r) -> Left ("admission rejection: " ++ renderAdmissionRejection r)
  Right (SourceAccepted input) -> Right (sourceResultVerdict (runSourceCheck input))

-- | The generated sub-claim's @formal@ — the goal atom the block emitted —
-- read off the expansion, which is where it exists before anything else sees it.
generatedGoal :: Policy -> Program -> Either String Prop
generatedGoal pol prog = case expandSurface pol prog of
  Left e -> Left (elabErrorMessage e)
  Right p' ->
    maybe (Left "no generated claim c2") Right $
      lookup (PropId "c2") [(claimId c, claimFormal c) | DeclClaim c <- programDecls p']

-- | The rules named by every rule-headed argument after expansion, in
-- declaration order. On S2\/S3 the only such arguments are the two the block
-- generated, so this reads back the scheme's @recheck@ and @bridge@ choices.
generatedRules :: Policy -> Program -> Either String [RuleId]
generatedRules pol prog = case expandSurface pol prog of
  Left e -> Left (elabErrorMessage e)
  Right p' -> Right [r | DeclArg a <- programDecls p', SRule {srRule = r} <- [argTerm a]]

-- | Rewrite every @comparison@ block's relation, for the negative half of the
-- relation test.
withRelation :: Relation -> Program -> Program
withRelation rel p = p {programDecls = map go (programDecls p)}
  where
    go (DeclComparison c) = DeclComparison c {cmpRelation = rel}
    go d = d

isErr :: String -> Either String a -> Property
isErr needle r = case r of
  Left msg -> counterexample ("message was: " ++ msg) (needle `isInfixOf` msg)
  Right _ -> counterexample ("expected an error mentioning " ++ show needle) False

con :: String -> Term
con s = TCon (FunSym s) []

numRel :: String -> String -> String -> Prop
numRel r a b = Prop (Pred r) [TNum a, TNum b]

-- | The shared shape of the three identity properties: elaborate the committed
-- @\@0.3@ source and the pre-rewrite @\@0.2@ fixture against one policy, and
-- assert the two 'Unit's are equal.
--
-- The two sub-assertions are ordered so a failure reports the most specific
-- thing first: 'unitArgs' is where a mis-generated θ vector, premise
-- reconstruction, or certificate would show up, and the whole-'Unit' equality
-- catches everything else (leaves, attacks, queries, the policy image).
identicalTo :: String -> FilePath -> FilePath -> String -> Property
identicalTo name policyPath sourcePath legacySrc = once $ ioProperty $ do
  pol <- loadPolicy policyPath
  prog <- loadProgram sourcePath
  let legacy = parseFixture (name ++ " @0.2 fixture") legacySrc
  pure $ case (elab pol prog, elab pol legacy) of
    (Left e, _) -> counterexample (name ++ " @0.3 source: " ++ e) False
    (_, Left e) -> counterexample (name ++ " @0.2 fixture: " ++ e) False
    (Right new, Right old) ->
      conjoin
        [ counterexample (name ++ ": generated arguments match the hand-written ones") $
            unitArgs new === unitArgs old
        , counterexample (name ++ ": the whole Unit is identical") $
            new === old
        ]

-- ---------------------------------------------------------------------------
-- The pre-rewrite @0.2 sources
-- ---------------------------------------------------------------------------
--
-- Verbatim bodies of the @example.lara@ files as of commit 30773d1, minus the
-- header comments (which never reach the parser's output). Each hand-writes
-- what the @comparison@ block now generates: the sub-claim's @formal@, both
-- arguments, both θ vectors, the certificate, and its slot indices.

-- | @examples\/S2@ at @\@0.2@ — the strict @num_lt@ comparison plus its bridge.
legacyS2 :: String
legacyS2 =
  unlines
    [ "artifact ord_demo at sha256:5252525252525252525252525252525252525252525252525252525252525252"
    , "policy ord-v1"
    , "use backends [ord@1]"
    , ""
    , "claim c1"
    , "  nl      = \"sys_new outperforms sys_base on ImageNet-val accuracy (0.74 vs 0.71)\""
    , "  formal  = better(sys_new, sys_base, accuracy, imagenet_val)"
    , "  binding = { author = alice, rationale = \"Ordered comparison of two reported accuracy cells.\", audit-status = reviewed }"
    , ""
    , "claim c2"
    , "  nl      = \"The reported baseline accuracy 0.71 is strictly below the reported system accuracy 0.74\""
    , "  formal  = num_lt(0.71, 0.74)"
    , "  binding = { author = alice, audit-status = reviewed }"
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
    , "arg a1 : supports(c2) by beats_recheck(sys_new, sys_base, accuracy, imagenet_val, exp1, 0.74, 0.71)"
    , "  assurance = cert(ord@1, sha256:ord-v1-theory-0, (ordcmp (prem 0) (prem 1)))"
    , ""
    , "arg a2 : supports(c1) by beats_baseline(sys_new, sys_base, accuracy, imagenet_val, 0.74, 0.71)"
    , ""
    , "status c1"
    ]

-- | @examples\/S3@ at @\@0.2@ — the @num_le@ tie, under different rule names and
-- a different policy from S2's.
legacyS3 :: String
legacyS3 =
  unlines
    [ "artifact ord_tie_demo at sha256:5353535353535353535353535353535353535353535353535353535353535353"
    , "policy ord-le-v1"
    , "use backends [ord@1]"
    , ""
    , "claim c1"
    , "  nl      = \"sys_new is at least as good as sys_base on ImageNet-val accuracy (0.71 vs 0.71)\""
    , "  formal  = at_least_as_good(sys_new, sys_base, accuracy, imagenet_val)"
    , "  binding = { author = alice, rationale = \"Ordered comparison of two equal reported accuracy cells.\", audit-status = reviewed }"
    , ""
    , "claim c2"
    , "  nl      = \"The reported baseline accuracy 0.71 is not above the reported system accuracy 0.71\""
    , "  formal  = num_le(0.71, 0.71)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "leaf e1 : reports(exp1, score_cell(sys_base, accuracy, imagenet_val, 0.71))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/accuracy.md#row=sys_base]"
    , ""
    , "leaf e2 : reports(exp1, score_cell(sys_new, accuracy, imagenet_val, 0.71))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/accuracy.md#row=sys_new]"
    , ""
    , "leaf e3 : comparison_setup(sys_new, sys_base, accuracy, imagenet_val, 0.71, 0.71)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [evidence/tables/accuracy.md#caption]"
    , ""
    , "arg a1 : supports(c2) by tie_recheck(sys_new, sys_base, accuracy, imagenet_val, exp1, 0.71, 0.71)"
    , "  assurance = cert(ord@1, sha256:ord-le-v1-theory-0, (ordcmp (prem 0) (prem 1)))"
    , ""
    , "arg a2 : supports(c1) by no_worse(sys_new, sys_base, accuracy, imagenet_val, 0.71, 0.71)"
    , ""
    , "status c1"
    ]

-- | @examples\/S4@ at @\@0.2@ — S2's body plus the audit, the critic, and the
-- positional attack @a2.1.leaf@ the committed source now spells
-- @a2.binding.leaf@.
legacyS4 :: String
legacyS4 =
  unlines
    [ "artifact ord_setting_demo at sha256:5454545454545454545454545454545454545454545454545454545454545454"
    , "policy ord-setting-v1"
    , "use backends [ord@1]"
    , ""
    , "claim c1"
    , "  nl      = \"sys_new outperforms sys_base on ImageNet-val accuracy (0.74 vs 0.71)\""
    , "  formal  = better(sys_new, sys_base, accuracy, imagenet_val)"
    , "  binding = { author = alice, rationale = \"Ordered comparison of two reported accuracy cells.\", audit-status = disputed }"
    , ""
    , "claim c2"
    , "  nl      = \"The reported baseline accuracy 0.71 is strictly below the reported system accuracy 0.74\""
    , "  formal  = num_lt(0.71, 0.74)"
    , "  binding = { author = alice, audit-status = reviewed }"
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
    , "leaf e4 : audits_settings(aud1, sys_new, sys_base, accuracy, imagenet_val)"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/audits/settings.md#sec=resolution]"
    , ""
    , "arg a1 : supports(c2) by beats_recheck(sys_new, sys_base, accuracy, imagenet_val, exp1, 0.74, 0.71)"
    , "  assurance = cert(ord@1, sha256:ord-setting-v1-theory-0, (ordcmp (prem 0) (prem 1)))"
    , ""
    , "arg a2 : supports(c1) by beats_baseline(sys_new, sys_base, accuracy, imagenet_val, 0.74, 0.71)"
    , ""
    , "arg x1 : challenges(e3) by setting_audit(sys_new, sys_base, accuracy, imagenet_val, 0.74, 0.71, aud1)"
    , ""
    , "undermine x1 a2.1.leaf"
    , ""
    , "status c1"
    , "status c2"
    ]

-- ---------------------------------------------------------------------------
-- The acceptance criterion, one property per example
-- ---------------------------------------------------------------------------

-- | __S2__: the @comparison@ block reproduces the hand-written strict step and
-- bridge exactly. Everything the sugar generates is pinned by this one equality
-- — the @num_lt@ goal and its argument order, both θ vectors, the @ord\@1@
-- certificate with its two 0-based @(prem i)@ slots, and both premise
-- reconstructions.
prop_S2Identical :: Property
prop_S2Identical =
  identicalTo "S2" "examples/S2/ord-v1.policy.lara" "examples/S2/example.lara" legacyS2

-- | __S3__, which doubles as plan §8's __relation test__: @at-least-as-good@
-- reproduces the hand-written @num_le@ unit exactly. S3 runs under a different
-- policy with different rule names than S2, so this also pins that the scheme
-- indirection — not a hardcoded rule name — is what resolves the block.
prop_S3Identical :: Property
prop_S3Identical =
  identicalTo "S3" "examples/S3/ord-le-v1.policy.lara" "examples/S3/example.lara" legacyS3

-- | __S4__: the generated structure is byte-identical /including the attack/.
-- The committed source writes @a2.binding.leaf@ and the fixture writes
-- @a2.1.leaf@, so the equality here subsumes the attack-path equivalence at
-- artifact scale ('prop_attackPathSpellings' states it pointwise).
prop_S4Identical :: Property
prop_S4Identical =
  identicalTo "S4" "examples/S4/ord-setting-v1.policy.lara" "examples/S4/example.lara" legacyS4

-- ---------------------------------------------------------------------------
-- Relation — the field that makes S3 expressible at all
-- ---------------------------------------------------------------------------

-- | The positive content of @relation@ (App. B.3): under @ord-le-v1@,
-- @at-least-as-good@ selects @tie_recheck@\/@no_worse@ and generates a @num_le@
-- goal. Asserted on the /expansion/, so the generated sub-claim's @formal@ and
-- the two rules are named directly rather than inferred from a verdict.
--
-- The negative half is the same source with the relation changed to
-- @strictly-better@: @ord-le-v1@ declares no scheme for that pair, so it is a
-- located error at the use site and never a silent fall back to the one scheme
-- the policy does declare.
prop_relationSelectsFamilyMember :: Property
prop_relationSelectsFamilyMember = once $ ioProperty $ do
  pol <- loadPolicy "examples/S3/ord-le-v1.policy.lara"
  prog <- loadProgram "examples/S3/example.lara"
  polS2 <- loadPolicy "examples/S2/ord-v1.policy.lara"
  progS2 <- loadProgram "examples/S2/example.lara"
  pure $
    conjoin
      [ counterexample "at-least-as-good generates the num_le goal" $
          generatedGoal pol prog === Right (numRel "num_le" "0.71" "0.71")
      , counterexample "strictly-better generates the num_lt goal from the same shape" $
          generatedGoal polS2 progS2 === Right (numRel "num_lt" "0.71" "0.74")
      , counterexample "the scheme names ord-le-v1's rules, not ord-v1's" $
          generatedRules pol prog === Right [RuleId "tie_recheck", RuleId "no_worse"]
      , counterexample "a relation the policy declares no scheme for is a located error" $
          isErr "comparison-scheme" (elab pol (withRelation StrictlyBetter prog))
      ]

-- ---------------------------------------------------------------------------
-- Polarity — S5's lower-is-better measurand flips the goal, and ord@1 accepts
-- ---------------------------------------------------------------------------

-- | plan §8's __polarity test__, executed against a committed artifact rather
-- than a fixture (eng review T1-A).
--
-- @examples\/S5@ and @examples\/S2@ state the same relation —
-- @relation = strictly-better@, @result@ = our cell, @baseline@ = theirs — and
-- differ only in a measurand their policies declare with opposite polarity. The
-- generated goals are mirror images: S2 emits @num_lt(theirs, ours)@ and S5
-- emits @num_lt(ours, theirs)@.
--
-- The second half is the one that makes it more than a rename: @ord\@1@ accepts
-- S5's flipped goal on replay. The strict argument is @in@, which cannot happen
-- unless the generated certificate, the generated goal, and the backend's exact
-- rational check all agree.
prop_polarityFlipsGoal :: Property
prop_polarityFlipsGoal = once $ ioProperty $ do
  polS5 <- loadPolicy "examples/S5/ord-ppl-v1.policy.lara"
  progS5 <- loadProgram "examples/S5/example.lara"
  polS2 <- loadPolicy "examples/S2/ord-v1.policy.lara"
  progS2 <- loadProgram "examples/S2/example.lara"
  pure $
    conjoin
      [ counterexample "higher-is-better: the goal is num_lt(baseline, result)" $
          generatedGoal polS2 progS2 === Right (numRel "num_lt" "0.71" "0.74")
      , counterexample "lower-is-better: the SAME source shape emits num_lt(result, baseline)" $
          generatedGoal polS5 progS5 === Right (numRel "num_lt" "28.4" "31.6")
      , counterexample "ord@1 accepts the flipped goal: the strict argument replays and is in" $
          accepted polS5 progS5
            === Right
              ( [(0, LIn), (1, LIn)]
              , [ (Prop (Pred "better") [con "sys_new", con "sys_base", con "perplexity", con "wikitext103"], Justified)
                , (numRel "num_lt" "28.4" "31.6", Justified)
                ]
              )
      ]
  where
    accepted pol prog = case runToVerdict pol prog of
      Left err -> Left err
      Right (Verdict _ (Reject r)) -> Left ("unexpected reject " ++ show r)
      Right (Verdict _ outcome@Accept{}) ->
        Right
          ( verdictLabels outcome
          , map (fmap conditionalStatus) (verdictStatuses outcome)
          )

-- ---------------------------------------------------------------------------
-- Attack-path equivalence (App. B.5)
-- ---------------------------------------------------------------------------

-- | The two spellings of S4's attack resolve to the __same__ 'Undermine' at the
-- __same 0-based__ premise, and each __round-trips in its own spelling__.
--
-- The 0-based half is a regression test in its own right (eng review 6A): the
-- binding is premise index 1 whether it is reached by counting or by name, and
-- it is the same 1 the generated certificate's @(prem 1)@ slot refers to.
--
-- Round-tripping is asserted separately for each spelling because that is the
-- reason the presentation AST carries 'Lara.AST.SurfaceStep' at all: the printer
-- never receives the 'Policy', so it cannot reconstruct which of two equivalent
-- spellings the author wrote — it has to have recorded it.
prop_attackPathSpellings :: Property
prop_attackPathSpellings = once $ ioProperty $ do
  pol <- loadPolicy "examples/S4/ord-setting-v1.policy.lara"
  named <- loadProgram "examples/S4/example.lara"
  let positional = parseFixture "S4 @0.2 fixture" legacyS4
  pure $
    conjoin
      [ counterexample "a2.binding.leaf resolves to Undermine x1 a2 [StepPremise 1]" $
          (unitAttacks <$> elab pol named) === Right [Undermine (ArgId "x1") (ArgId "a2") [StepPremise 1]]
      , counterexample "a2.1.leaf resolves to the very same attack" $
          (unitAttacks <$> elab pol named) === (unitAttacks <$> elab pol positional)
      , counterexample "the labelled spelling round-trips as the labelled spelling" $
          reprint named === Right "undermine x1 a2.binding.leaf"
      , counterexample "the positional spelling round-trips as the positional spelling" $
          reprint positional === Right "undermine x1 a2.1.leaf"
      ]
  where
    -- The printed program's single `undermine` line, re-parsed and re-printed
    -- once, so this pins print ∘ parse ∘ print = print on the attack itself.
    reprint p = case parseProgram (printProgram p) of
      Left e -> Left ("reparse failed: " ++ show e)
      Right p' -> case [l | l <- lines (printProgram p'), "undermine " `isPrefixOf` l] of
        [l] -> Right l
        ls -> Left ("expected one undermine line, got " ++ show ls)

-- ---------------------------------------------------------------------------
-- S4 still defeats the generated bridge
-- ---------------------------------------------------------------------------

-- | Generated structure is ordinary structure. The audit undermines the
-- /generated/ bridge at its binding premise and the bridge goes @out@, so the
-- comparative claim is __defeated__ — while the /generated/ strict step stays
-- @in@ and its comparison stays __justified__.
--
-- This is the property that would fail if the expansion had folded the strict
-- step into the bridge, generated the binding leaf, or otherwise moved a
-- defeasible commitment somewhere a critic cannot reach. The sugar has to
-- produce something attackable at exactly the old point, and this asserts it on
-- the committed artifact.
prop_S4DefeatsGeneratedBridge :: Property
prop_S4DefeatsGeneratedBridge = once $ ioProperty $ do
  pol <- loadPolicy "examples/S4/ord-setting-v1.policy.lara"
  prog <- loadProgram "examples/S4/example.lara"
  pure $ case runToVerdict pol prog of
    Left err -> counterexample ("S4: " ++ err) False
    Right (Verdict _ (Reject r)) -> counterexample ("S4: unexpected reject " ++ show r) False
    Right (Verdict _ outcome@Accept{}) ->
      conjoin
        [ counterexample "the generated a1 is in, the generated a2 is out, the critic x1 is in" $
            verdictLabels outcome === [(0, LIn), (1, LOut), (2, LIn)]
        , counterexample "exactly one edge: x1 → a2" $
            verdictEdges outcome === [(2, 1)]
        , counterexample "better defeated, the generated comparison still justified" $
            map (fmap conditionalStatus) (verdictStatuses outcome)
              === [ (Prop (Pred "better") [con "sys_new", con "sys_base", con "accuracy", con "imagenet_val"], Defeated)
                  , (numRel "num_lt" "0.71" "0.74", Justified)
                  ]
        ]

-- ---------------------------------------------------------------------------
-- Runner
-- ---------------------------------------------------------------------------

surfaceRewriteSpecProps :: [(String, IO Result)]
surfaceRewriteSpecProps =
  [ ("S2 @0.3 comparison elaborates to the identical @0.2 Unit", quickCheckResult prop_S2Identical)
  , ("S3 at-least-as-good elaborates to the identical @0.2 num_le Unit", quickCheckResult prop_S3Identical)
  , ("S4 @0.3 comparison + labelled attack elaborate to the identical @0.2 Unit", quickCheckResult prop_S4Identical)
  , ("relation selects the family member and the policy's own rules", quickCheckResult prop_relationSelectsFamilyMember)
  , ("polarity flips the generated goal and ord@1 accepts the flipped one", quickCheckResult prop_polarityFlipsGoal)
  , ("a2.binding.leaf == a2.1.leaf, each round-tripping in its own spelling", quickCheckResult prop_attackPathSpellings)
  , ("S4 still defeats the generated bridge while the comparison stays justified", quickCheckResult prop_S4DefeatsGeneratedBridge)
  ]
