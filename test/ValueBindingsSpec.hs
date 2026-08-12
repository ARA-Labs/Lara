module ValueBindingsSpec
  ( valueBindingSpecProps
  , strictPolicySource
  , boundSource
  , unboundSource
  ) where

import Data.List (isInfixOf)
import Test.QuickCheck

import Lara.AST
import Lara.Check (UnitError (..), checkUnit)
import Lara.Driver (buildCertOk, buildGamma)
import Lara.Elaborate.Error (ElabError (..), elabErrorMessage)
import Lara.Elaborate.Internal
  ( elaborate
  , elaborateWithSemanticProgram
  , registryOf
  )
import Lara.Elaborate.ValueBinding (expandValueBindings)
import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..))
import Lara.Sigma (Sort (..), SortFault (..), SortName (..))
import Lara.Sigma.WellSorted (SortError (..))
import Lara.Strict (SExpr (..))
import Lara.Syntax (ParseError (..), parsePolicy, parseProgram)
import Lara.Wire (encodeUnit, printSExpr)

strictPolicySource :: String
strictPolicySource =
  unlines
    [ "policy value-bindings-v1"
    , "sort System"
    , "con sys_new : System"
    , "con sys_base : System"
    , "con box(Num) : Num"
    , "pred observed(System, Num)"
    , "pred selected(System, Num)"
    , "pred better(System, System)"
    , "rule select(X, V)"
    , "  mode = strict"
    , "  premises = [ observed(X, V) ]"
    , "  conclusion = selected(X, V)"
    , "  allow-trusted = true"
    , "  certifiers = []"
    ]

boundSource :: String
boundSource =
  semanticProgramSource
    [ "let candidate = sys_new"
    , "let baseline = sys_base"
    , "let candidate_score = 0.74"
    ]
    "candidate"
    "candidate_score"
    "{{{candidate}}} scored {candidate_score}"

unboundSource :: String
unboundSource =
  semanticProgramSource
    []
    "sys_new"
    "0.74"
    "{{sys_new}} scored 0.74"

semanticProgramSource :: [String] -> String -> String -> String -> String
semanticProgramSource bindings candidate score claimNl =
  unlines $
    [ "artifact value_fixture at sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    , "policy value-bindings-v1"
    , "use backends []"
    ]
      ++ bindings
      ++ [ ""
         , "claim c1"
         , "  nl = \"" ++ claimNl ++ "\""
         , "  formal = selected(" ++ candidate ++ ", box(" ++ score ++ "))"
         , "  binding = { author = alice, audit-status = reviewed }"
         , ""
         , "leaf e1 : observed(" ++ candidate ++ ", box(" ++ score ++ "))"
         , "  kind = observed"
         , "  provenance = user"
         , "  refs = [evidence/value.txt]"
         , ""
         , "arg a1 : supports(c1) by select(" ++ candidate ++ ", box(" ++ score ++ "))"
         , "  assurance = trusted"
         , ""
         , "status c1"
         ]

comparisonSource :: String
comparisonSource =
  unlines
    [ "artifact value_fixture at sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    , "policy value-bindings-v1"
    , "use backends []"
    , "let candidate = sys_new"
    , "let baseline = sys_base"
    , "let candidate_score = 0.74"
    , ""
    , "claim c1"
    , "  nl = \"{candidate} scored {candidate_score}\""
    , "  formal = selected(candidate, box(candidate_score))"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "comparison : better(candidate, baseline) on accuracy @ validation"
    , "  relation = strictly-better"
    , "  recheck = a2"
    , "  bridge = a3"
    , "  result = e1"
    , "  baseline = e1"
    , "  binding = e1"
    , "  claims c2"
    , "    nl = \"{candidate} is better than {baseline}\""
    , "    binding = { author = alice, audit-status = reviewed }"
    , "  supports c1"
    ]

programHeader :: [String]
programHeader =
  [ "artifact negative_fixture at sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
  , "policy value-bindings-v1"
  , "use backends []"
  ]

claimWithNl :: String -> String
claimWithNl nl =
  unlines $
    programHeader
      ++ [ ""
         , "claim c1"
         , "  nl = \"" ++ nl ++ "\""
         , "  formal = selected(sys_new, box(0.74))"
         , "  binding = { author = alice, audit-status = reviewed }"
         ]

parserNegatives :: [(String, String, Int, String)]
parserNegatives =
  [ ( "duplicate value binding"
    , unlines (programHeader ++ ["let candidate = sys_new", "let candidate = sys_base"])
    , 5
    , "duplicate value binding"
    )
  , ( "reserved cell binding"
    , unlines (programHeader ++ ["let cell = sys_new"])
    , 4
    , "reserved"
    )
  , ( "malformed binding RHS"
    , unlines (programHeader ++ ["let candidate = @"])
    , 4
    , "expected a term"
    )
  , ( "late value binding"
    , unlines
        ( programHeader
            ++ [ ""
               , "claim c1"
               , "  nl = \"selected\""
               , "  formal = selected(sys_new, box(0.74))"
               , "  binding = { author = alice, audit-status = reviewed }"
               , "let candidate = sys_new"
               ]
        )
    , 9
    , ""
    )
  , ( "multi-token value directive"
    , claimWithNl "score {candidate extra}"
    , 6
    , ""
    )
  , ( "unknown multi-token directive head"
    , claimWithNl "score {cel e1}"
    , 6
    , "unknown nl directive"
    )
  , ( "one-token cell directive"
    , claimWithNl "score {cell}"
    , 6
    , "leaf id"
    )
  ]

prop_parserContract :: Property
prop_parserContract =
  once $
    conjoin
      [ parsed "bound source" (parseProgram boundSource)
      , parsed "expanded source" (parseProgram unboundSource)
      , parsed "strict policy" (parsePolicy strictPolicySource)
      , conjoin
          [ counterexample label (rejectsAt expectedLine reason (parseProgram source))
          | (label, source, expectedLine, reason) <- parserNegatives
          ]
      ]
  where
    parsed label result = counterexample label $ case result of
      Left _ -> False
      Right _ -> True
    rejectsAt expectedLine reason result = case result of
      Left (ParseError line column message) ->
        line == expectedLine && column >= 1 && reason `isInfixOf` message
      Right _ -> False

prop_dedicatedDiagnostics :: Property
prop_dedicatedDiagnostics =
  once $
    conjoin
      [ diagnostic
          (DuplicateValueBinding (ValueName "x"))
          "value binding 'x': duplicate declaration"
      , diagnostic
          (ReservedValueName (ValueName "cell"))
          "value binding 'cell': reserved name"
      , diagnostic
          (ValueNameConstructorCollision (ValueName "sys_new"))
          "value binding 'sys_new': collides with declared constructor"
      , diagnostic
          (ValueBindingSortError (ValueName "x") (FaultUndeclaredCon (FunSym "missing")))
          "value binding 'x': ill-sorted right-hand side: undeclared constructor 'missing'"
      , diagnostic
          (ValueBindingClaimSortError (PropId "c1") (FaultArgSort sortNum sortSystem))
          "claim 'c1': ill-sorted formal after value substitution: expected sort Num but got System"
      , diagnostic
          (NlValueBindingMissing (PropId "c1") (ValueName "missing"))
          "claim 'c1': nl references undeclared value 'missing'"
      ]
  where
    diagnostic err expected =
      counterexample (elabErrorMessage err) (expected `isInfixOf` elabErrorMessage err)
    sortNum = SortNum
    sortSystem = SortDecl (SortName "System")

readSort :: String -> Sort
readSort name
  | name == "Num" = SortNum
  | otherwise = SortDecl (SortName name)

prop_semanticParity :: Property
prop_semanticParity =
  once $
    case (parsePolicy strictPolicySource, parseProgram boundSource, parseProgram unboundSource) of
      (Right policy, Right bound, Right unbound) ->
        case
          ( elaborateWithSemanticProgram (registryOf policy) bound policy
          , elaborateWithSemanticProgram (registryOf policy) unbound policy
          ) of
          (Right (boundUnit, boundGenerated, boundProgram), Right (unboundUnit, unboundGenerated, unboundProgram)) ->
            conjoin
              [ counterexample "post-expansion Programs" (boundProgram === unboundProgram)
              , counterexample "generated provenance" (boundGenerated === unboundGenerated)
              , counterexample "Units" (boundUnit === unboundUnit)
              , counterexample "encoded Unit bytes" $
                  printSExpr (encodeUnit boundUnit) === printSExpr (encodeUnit unboundUnit)
              , counterexample "bindings are consumed" (programValueBindings boundProgram === [])
              ]
          values -> counterexample ("elaboration failed: " ++ show values) False
      values -> counterexample ("fixture parse failed: " ++ show values) False

prop_totalSubstitutionAndCertOpacity :: Property
prop_totalSubstitutionAndCertOpacity =
  once $
    case (parsePolicy strictPolicySource, parseProgram boundSource) of
      (Right policy, Right parsed) ->
        let cert =
              Cert
                { certBackend = BackendId "opaque"
                , certVersion = 7
                , certTheory = TheoryDigest "sha256:opaque"
                , certPayload = SList [SAtom "candidate", SAtom "{candidate_score}"]
                }
            nested =
              SRule
                { srRule = RuleId "outer"
                , srSubst = [(Param "X", ref "candidate")]
                , srPremises =
                    [ SRule
                        { srRule = RuleId "premise"
                        , srSubst = [(Param "V", ref "candidate_score")]
                        , srPremises = []
                        , srDischarge = []
                        , srHoles = []
                        , srAssurance = AssuranceCert cert
                        }
                    ]
                , srDischarge =
                    [ ( QuestionId "q"
                      , SRule
                          { srRule = RuleId "discharge"
                          , srSubst = [(Param "B", ref "baseline")]
                          , srPremises = []
                          , srDischarge = []
                          , srHoles = []
                          , srAssurance = AssuranceNone
                          }
                      )
                    ]
                , srHoles = []
                , srAssurance = AssuranceNone
                }
            authored = parsed {programDecls = mapArgTerm (const nested) (programDecls parsed)}
         in case expandValueBindings (policySigma policy) authored of
              Left err -> counterexample (elabErrorMessage err) False
              Right expanded ->
                case [argTerm a | DeclArg a <- programDecls expanded] of
                  [actual] ->
                    conjoin
                      [ counterexample "nested premise substitution" $
                          substAt [0] actual === Just (TNum "0.74")
                      , counterexample "nested discharge substitution" $
                          dischargeSubst actual === Just (TCon (FunSym "sys_base") [])
                      , counterexample "opaque certificate unchanged" $
                          certs actual === [cert]
                      , counterexample "opaque certificate payload bytes" $
                          map (printSExpr . certPayload) (certs actual)
                            === [printSExpr (certPayload cert)]
                      ]
                  terms -> counterexample ("unexpected args: " ++ show terms) False
      values -> counterexample ("fixture parse failed: " ++ show values) False
  where
    ref n = TCon (FunSym n) []
    substAt path term = case (path, term) of
      ([], SRule {srSubst = (_, t) : _}) -> Just t
      (i : rest, SRule {srPremises = ps})
        | i >= 0 && i < length ps -> substAt rest (ps !! i)
      _ -> Nothing
    dischargeSubst SRule {srDischarge = (_, SRule {srSubst = (_, t) : _}) : _} = Just t
    dischargeSubst _ = Nothing
    certs (SLeaf _) = []
    certs SRule {srPremises = ps, srDischarge = ds, srAssurance = assurance} =
      assuranceCert assurance ++ concatMap certs ps ++ concatMap (certs . snd) ds
    assuranceCert (AssuranceCert cert) = [cert]
    assuranceCert _ = []

prop_comparisonAndNlSinglePass :: Property
prop_comparisonAndNlSinglePass =
  once $
    case (parsePolicy strictPolicySource, parseProgram comparisonSource) of
      (Right policy, Right parsed) ->
        let onceOnly = mapClaimNl (const "{{candidate}}") parsed
         in case (expandValueBindings (policySigma policy) parsed, expandValueBindings (policySigma policy) onceOnly) of
              (Right expanded, Right literalExpanded) ->
                conjoin
                  [ counterexample "ordinary claim formal" $
                      claimFormalOf (PropId "c1") expanded
                        === Just (Prop (Pred "selected") [con "sys_new", TCon (FunSym "box") [TNum "0.74"]])
                  , counterexample "ordinary claim nl" $
                      claimNlOf (PropId "c1") expanded === Just "sys_new scored 0.74"
                  , counterexample "comparison conclusion" $
                      comparisonConclusion expanded
                        === Just (Prop (Pred "better") [con "sys_new", con "sys_base"])
                  , counterexample "comparison claim nl" $
                      comparisonNl expanded === Just "sys_new is better than sys_base"
                  , counterexample "literal brace is not reinterpreted" $
                      claimNlOf (PropId "c1") literalExpanded === Just "{candidate}"
                  ]
              values -> counterexample ("expansion failed: " ++ show values) False
      values -> counterexample ("fixture parse failed: " ++ show values) False
  where
    con n = TCon (FunSym n) []


-- | Binding references render the authored term spelling, while @{cell …}@
-- renders the evidence-derived rational canonically. String terms can only
-- reach this pass through a hand-built AST and retain 'prettyTerm' quotes.
prop_bindingInterpolationRendering :: Property
prop_bindingInterpolationRendering =
  once $
    case (parsePolicy strictPolicySource, parseProgram boundSource) of
      (Right policy, Right parsed) ->
        let precise binding
              | valueName binding == ValueName "candidate_score" =
                  binding {valueTerm = TNum "0.710"}
              | otherwise = binding
            authored =
              mapClaimNl (const "{candidate_score}|{cell e1}|{note}") $
                parsed
                  { programValueBindings =
                      ValueBinding (ValueName "note") (TStr "beta run")
                        : map precise (programValueBindings parsed)
                  }
         in case expandValueBindings (policySigma policy) authored of
              Left err -> counterexample (elabErrorMessage err) False
              Right expanded ->
                claimNlOf (PropId "c1") expanded
                  === Just "0.710|0.71|\"beta run\""
      values -> counterexample ("fixture parse failed: " ++ show values) False

prop_failClosedMatrix :: Property
prop_failClosedMatrix =
  once $
    case (parsePolicy strictPolicySource, parseProgram unboundSource) of
      (Right policy, Right base) ->
        let sigma = policySigma policy
            binding n t = ValueBinding (ValueName n) t
            run bs prog = expandValueBindings sigma prog {programValueBindings = bs}
            missing = TCon (FunSym "missing") []
            box ts = TCon (FunSym "box") ts
            sys = TCon (FunSym "sys_new") []
            onlyClaim = base {programDecls = [DeclClaim c | DeclClaim c <- programDecls base]}
            wrongClaim = run [binding "score" sys] (replaceClaimScore "score" onlyClaim)
         in conjoin
              [ counterexample "hand-built duplicate" $
                  run [binding "x" (TNum "1"), binding "x" (TNum "2")] base
                    === Left (DuplicateValueBinding (ValueName "x"))
              , counterexample "hand-built reserved name" $
                  run [binding "cell" (TNum "1")] base
                    === Left (ReservedValueName (ValueName "cell"))
              , counterexample "constructor collision independent of arity" $
                  run [binding "box" (TNum "1")] base
                    === Left (ValueNameConstructorCollision (ValueName "box"))
              , counterexample "unused undeclared RHS is validated" $
                  run [binding "unused" missing] base
                    === Left (ValueBindingSortError (ValueName "unused") (FaultUndeclaredCon (FunSym "missing")))
              , counterexample "wrong-arity RHS" $
                  run [binding "x" (box [])] base
                    === Left (ValueBindingSortError (ValueName "x") (FaultConArity (FunSym "box") 1 0))
              , counterexample "wrong-sort RHS" $
                  run [binding "x" (box [sys])] base
                    === Left (ValueBindingSortError (ValueName "x") (FaultArgSort SortNum (readSort "System")))
              , counterexample "missing one-token interpolation" $
                  run [] (mapClaimNl (const "{missing}") base)
                    === Left (NlValueBindingMissing (PropId "c1") (ValueName "missing"))
              , counterexample "unsupported unqueried claim is sort-checked" $
                  wrongClaim
                    === Left (ValueBindingClaimSortError (PropId "c1") (FaultArgSort SortNum (readSort "System")))
              , counterexample "simultaneous non-recursive RHS" $
                  run [binding "x" (TCon (FunSym "y") []), binding "y" (TNum "0.74")] base
                    === Left (ValueBindingSortError (ValueName "x") (FaultUndeclaredCon (FunSym "y")))
              ]
      values -> counterexample ("fixture parse failed: " ++ show values) False

prop_survivingUseReachesR2 :: Property
prop_survivingUseReachesR2 =
  once $
    case (parsePolicy strictPolicySource, parseProgram leafOnlySource) of
      (Right policy, Right parsed) ->
        case elaborate (registryOf policy) parsed policy of
          Left err -> counterexample ("unexpected elaboration error: " ++ elabErrorMessage err) False
          Right unit ->
            case checkUnit (buildGamma (unitLeaves unit)) (buildCertOk (unitTheories unit)) unit of
              Left (UESignature (SELeaf (LeafId "e1") _)) -> property True
              other -> counterexample ("wrong boundary: " ++ show other) False
      values -> counterexample ("fixture parse failed: " ++ show values) False
  where
    leafOnlySource =
      unlines $
        programHeader
          ++ [ "let candidate = 0.74"
             , ""
             , "leaf e1 : observed(candidate, 0.74)"
             , "  kind = observed"
             , "  provenance = user"
             , "  refs = [evidence/value.txt]"
             ]

prop_noBindingLegacyBytes :: Property
prop_noBindingLegacyBytes =
  once $
    case (parsePolicy strictPolicySource, parseProgram legacySource) of
      (Right policy, Right parsed) ->
        case
          ( expandValueBindings (policySigma policy) parsed
          , elaborate (registryOf policy) parsed policy
          , elaborateWithSemanticProgram (registryOf policy) parsed policy
          ) of
          (Right expanded, Right legacyUnit, Right (semanticUnit, _, semanticProgram)) ->
            conjoin
              [ counterexample "no-binding expansion value" (expanded === parsed)
              , counterexample "semantic program" (semanticProgram === parsed)
              , counterexample "legacy Unit" (semanticUnit === legacyUnit)
              , counterexample "legacy Unit bytes" $
                  printSExpr (encodeUnit semanticUnit) === printSExpr (encodeUnit legacyUnit)
              ]
          values -> counterexample ("legacy path failed: " ++ show values) False
      values -> counterexample ("fixture parse failed: " ++ show values) False
  where
    legacySource =
      semanticProgramSource
        []
        "sys_new"
        "0.74"
        "sys_new scored 0.74"

mapArgTerm :: (SupportTerm -> SupportTerm) -> [Decl] -> [Decl]
mapArgTerm f = map one
  where
    one (DeclArg a) = DeclArg a {argTerm = f (argTerm a)}
    one d = d

mapClaimNl :: (String -> String) -> Program -> Program
mapClaimNl f prog = prog {programDecls = map one (programDecls prog)}
  where
    one (DeclClaim c) = DeclClaim c {claimNl = f (claimNl c)}
    one d = d

replaceClaimScore :: String -> Program -> Program
replaceClaimScore score prog = prog {programDecls = map one (programDecls prog)}
  where
    one (DeclClaim c) =
      DeclClaim c {claimFormal = Prop (Pred "selected") [TCon (FunSym "sys_new") [], TCon (FunSym "box") [TCon (FunSym score) []]]}
    one d = d

claimFormalOf :: PropId -> Program -> Maybe Prop
claimFormalOf cid prog = lookup cid [(claimId c, claimFormal c) | DeclClaim c <- programDecls prog]

claimNlOf :: PropId -> Program -> Maybe String
claimNlOf cid prog = lookup cid [(claimId c, claimNl c) | DeclClaim c <- programDecls prog]

comparisonConclusion :: Program -> Maybe Prop
comparisonConclusion prog = case [cmpConclusion c | DeclComparison c <- programDecls prog] of
  p : _ -> Just p
  [] -> Nothing

comparisonNl :: Program -> Maybe String
comparisonNl prog = case [ccNlRaw (cmpClaim c) | DeclComparison c <- programDecls prog] of
  s : _ -> Just s
  [] -> Nothing

valueBindingSpecProps :: [(String, IO Result)]
valueBindingSpecProps =
  [ ("value bindings: parser contract", quickCheckResult prop_parserContract)
  , ("value bindings: six dedicated diagnostics", quickCheckResult prop_dedicatedDiagnostics)
  , ("value bindings: semantic Program, Unit, and byte parity", quickCheckResult prop_semanticParity)
  , ("value bindings: nested support substitution and Cert opacity", quickCheckResult prop_totalSubstitutionAndCertOpacity)
  , ("value bindings: comparison fields and one-pass NL", quickCheckResult prop_comparisonAndNlSinglePass)
  , ("value bindings: authored and canonical NL renderings", quickCheckResult prop_bindingInterpolationRendering)
  , ("value bindings: fail-closed validation matrix", quickCheckResult prop_failClosedMatrix)
  , ("value bindings: surviving wrong-sort use reaches R2", quickCheckResult prop_survivingUseReachesR2)
  , ("value bindings: no-binding legacy bytes", quickCheckResult prop_noBindingLegacyBytes)
  ]
