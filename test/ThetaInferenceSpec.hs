module ThetaInferenceSpec
  ( thetaInferenceSpecProps
  ) where

import Data.List (isInfixOf)
import Test.QuickCheck
import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..))

import Lara.AST
import Lara.Elaborate
  ( PreparedSource (..)
  , prepareSource
  , runSourceCheck
  , sourceResultCheckInput
  , sourceResultVerdict
  )
import Lara.Elaborate.Internal
  ( ElabError (..)
  , elabErrorMessage
  , elaborate
  , registryOf
  )
import Lara.ExpectedJson (renderJson, sourceResultJsonValue)
import Lara.Elaborate.Subst (sameTerm)
import Lara.Measure (outcomeExitCode)
import Lara.Syntax (parsePolicy, parseProgram, printProgram)
import Lara.Wire (Outcome (Accept), Verdict (..), encodeCheckInput, encodeUnit, printSExpr, verdictOutcome)

-- ---------------------------------------------------------------------------
-- Policy-local fixtures
-- ---------------------------------------------------------------------------

-- The fixture is deliberately small but exercises all three inference shapes:
-- a leaf premise, a prior argument premise, and a two-premise rule whose X and
-- V bindings must agree across both references.  conclude_only leaves V
-- unbound by its premise list so inferred elaboration must reject it.
thetaPolicySource :: String
thetaPolicySource =
  unlines
    [ "policy theta-inference-v1"
    , "sort System"
    , "con sys_a : System"
    , "con sys_b : System"
    , "pred source(System, Num)"
    , "pred selected(System, Num)"
    , "pred promoted(System, Num)"
    , "pred paired(System, Num)"
    , "pred concluded(System, Num)"
    , "rule select(X, V)"
    , "  mode = strict"
    , "  premises = [ source(X, V) ]"
    , "  conclusion = selected(X, V)"
    , "  allow-trusted = true"
    , "  certifiers = []"
    , "rule promote(X, V)"
    , "  mode = strict"
    , "  premises = [ selected(X, V) ]"
    , "  conclusion = promoted(X, V)"
    , "  allow-trusted = true"
    , "  certifiers = []"
    , "rule pair(X, V)"
    , "  mode = strict"
    , "  premises = [ selected(X, V), source(X, V) ]"
    , "  conclusion = paired(X, V)"
    , "  allow-trusted = true"
    , "  certifiers = []"
    , "rule conclude_only(X, V)"
    , "  mode = strict"
    , "  premises = [ source(X, 0.74) ]"
    , "  conclusion = concluded(X, V)"
    , "  allow-trusted = true"
    , "  certifiers = []"
    ]

thetaProgramSource :: [String] -> String
thetaProgramSource args =
  unlines $
    [ "artifact theta_fixture at sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    , "policy theta-inference-v1"
    , "use backends []"
    , ""
    , "claim c_selected"
    , "  nl = \"selected source\""
    , "  formal = selected(sys_a, 0.74)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "claim c_promoted"
    , "  nl = \"promoted selection\""
    , "  formal = promoted(sys_a, 0.74)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "claim c_paired"
    , "  nl = \"paired evidence\""
    , "  formal = paired(sys_a, 0.74)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "claim c_concluded"
    , "  nl = \"conclusion-only parameter\""
    , "  formal = concluded(sys_a, 0.74)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "leaf e1 : source(sys_a, 0.74)"
    , "  kind = observed"
    , "  provenance = user"
    , "  refs = [evidence/source.txt]"
    , ""
    , "leaf e2 : source(sys_b, 0.74)"
    , "  kind = observed"
    , "  provenance = user"
    , "  refs = [evidence/conflict.txt]"
    , ""
    ]
      ++ args
      ++ [ ""
         , "status c_selected"
         , "status c_promoted"
         , "status c_paired"
         , "status c_concluded"
         ]

explicitSource :: String
explicitSource =
  thetaProgramSource
    [ "arg a1 : supports(c_selected) by select(sys_a, 0.74)"
    , "  assurance = trusted"
    , ""
    , "arg a2 : supports(c_promoted) by promote(sys_a, 0.74)"
    , "  assurance = trusted"
    , ""
    , "arg a3 : supports(c_paired) by pair(sys_a, 0.74)"
    , "  assurance = trusted"
    ]

inferredLeafSource :: String
inferredLeafSource =
  thetaProgramSource
    [ "arg a1 : supports(c_selected) by select from [e1]"
    , "  assurance = trusted"
    , ""
    , "arg a2 : supports(c_promoted) by promote(sys_a, 0.74)"
    , "  assurance = trusted"
    , ""
    , "arg a3 : supports(c_paired) by pair(sys_a, 0.74)"
    , "  assurance = trusted"
    ]

boundLeafInferenceSource :: String
boundLeafInferenceSource =
  unlines
    [ "artifact theta_fixture at sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    , "policy theta-inference-v1"
    , "use backends []"
    , "let candidate = sys_a"
    , ""
    , "claim c_selected"
    , "  nl = \"selected source\""
    , "  formal = selected(candidate, 0.74)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "leaf e1 : source(candidate, 0.74)"
    , "  kind = observed"
    , "  provenance = user"
    , "  refs = [evidence/source.txt]"
    , ""
    , "arg a1 : supports(c_selected) by select from [e1]"
    , "  assurance = trusted"
    , ""
    , "status c_selected"
    ]

explicitBoundLeafSource :: String
explicitBoundLeafSource =
  replaceAll "candidate" "sys_a" $
    replaceOnce "let candidate = sys_a\n" "" boundLeafInferenceSource

inferredPriorArgSource :: String
inferredPriorArgSource =
  thetaProgramSource
    [ "arg a1 : supports(c_selected) by select(sys_a, 0.74)"
    , "  assurance = trusted"
    , ""
    , "arg a2 : supports(c_promoted) by promote from [a1]"
    , "  assurance = trusted"
    , ""
    , "arg a3 : supports(c_paired) by pair(sys_a, 0.74)"
    , "  assurance = trusted"
    ]

inferredPairSource :: String
inferredPairSource =
  thetaProgramSource
    [ "arg a1 : supports(c_selected) by select(sys_a, 0.74)"
    , "  assurance = trusted"
    , ""
    , "arg a3 : supports(c_paired) by pair from [a1, e1]"
    , "  assurance = trusted"
    ]

conflictingPairSource :: String
conflictingPairSource =
  thetaProgramSource
    [ "arg a1 : supports(c_selected) by select(sys_a, 0.74)"
    , "  assurance = trusted"
    , ""
    , "arg a3 : supports(c_paired) by pair from [a1, e2]"
    , "  assurance = trusted"
    ]

unboundConclusionSource :: String
unboundConclusionSource =
  thetaProgramSource
    [ "arg a_bad : supports(c_concluded) by conclude_only from [e1]"
    , "  assurance = trusted"
    ]

emptyInferenceSource :: String
emptyInferenceSource =
  thetaProgramSource
    [ "arg a0 : supports(c_selected) by select from []"
    , "  assurance = trusted"
    ]

twoReferenceInferenceSource :: String
twoReferenceInferenceSource =
  thetaProgramSource
    [ "arg a1 : supports(c_selected) by select(sys_a, 0.74)"
    , "  assurance = trusted"
    , ""
    , "arg a3 : supports(c_paired) by pair from [a1, e1]"
    , "  assurance = trusted"
    ]
threeReferenceInferenceSource :: String
threeReferenceInferenceSource =
  thetaProgramSource
    [ "arg a3 : supports(c_paired) by pair from [a1, e1, e2]"
    ]

malformedInferenceTrailingCommaSource :: String
malformedInferenceTrailingCommaSource =
  thetaProgramSource
    [ "arg malformed : supports(c_selected) by select from [e1,]"
    ]


tooFewReferenceSource :: String
tooFewReferenceSource =
  thetaProgramSource
    [ "arg a_bad : supports(c_paired) by pair from [e1]"
    ]

tooManyReferenceSource :: String
tooManyReferenceSource = threeReferenceInferenceSource

undeclaredReferenceSource :: String
undeclaredReferenceSource =
  thetaProgramSource
    [ "arg a_bad : supports(c_selected) by select from [missing]"
    ]

forwardReferenceSource :: String
forwardReferenceSource =
  thetaProgramSource
    [ "arg a_bad : supports(c_paired) by pair from [a_later, e1]"
    , ""
    , "arg a_later : supports(c_selected) by select from [e1]"
    ]

underivablePriorReferenceSource :: String
underivablePriorReferenceSource =
  thetaProgramSource
    [ "arg a_missing : supports(c_selected) by leaf(e_missing)"
    , ""
    , "arg a_bad : supports(c_paired) by pair from [a_missing, e1]"
    ]

ambiguousReferenceSource :: String
ambiguousReferenceSource =
  thetaProgramSource
    [ "leaf a1 : selected(sys_a, 0.74)"
    , "  kind = observed"
    , "  provenance = user"
    , "  refs = []"
    , ""
    , "arg a1 : supports(c_selected) by select(sys_a, 0.74)"
    , ""
    , "arg a_bad : supports(c_paired) by pair from [a1, e1]"
    ]

shapeMismatchSource :: String
shapeMismatchSource =
  thetaProgramSource
    [ "arg a_bad : supports(c_paired) by pair from [e2, e1]"
    ]

constructorShapePolicySource :: String
constructorShapePolicySource =
  replaceOnce "source(X, V)" "source(sys_b, V)" thetaPolicySource

literalShapePolicySource :: String
literalShapePolicySource =
  replaceOnce "source(X, V)" "source(X, 0.75)" thetaPolicySource

constructorShapeSource :: String
constructorShapeSource =
  thetaProgramSource
    [ "arg a_bad : supports(c_selected) by select from [e1]"
    ]

literalShapeSource :: String
literalShapeSource = constructorShapeSource

arityShapeSource :: String
arityShapeSource =
  replaceOnce
    "source(sys_a, 0.74)"
    "source(sys_a)"
    (thetaProgramSource ["arg a_bad : supports(c_selected) by select from [e1]"])

unknownRulePrecedenceSource :: String
unknownRulePrecedenceSource =
  thetaProgramSource
    [ "arg a_bad : supports(c_selected) by missing from [e1, e1]"
    ]

inferenceBeforeDischargeSource :: String
inferenceBeforeDischargeSource =
  thetaProgramSource
    [ "arg a_bad : supports(c_promoted) by select from [e2]"
    ]

zeroPolicySource :: String
zeroPolicySource =
  unlines
    [ "policy zero-theta-v1"
    , "sort System"
    , "con sys_a : System"
    , "pred selected(System, Num)"
    , "rule empty()"
    , "  mode = strict"
    , "  premises = []"
    , "  conclusion = selected(sys_a, 0.74)"
    , "  allow-trusted = true"
    , "  certifiers = []"
    , "rule unbound(X)"
    , "  mode = strict"
    , "  premises = []"
    , "  conclusion = selected(X, 0.74)"
    , "  allow-trusted = true"
    , "  certifiers = []"
    ]

zeroProgramSource :: [String] -> String
zeroProgramSource args =
  mapPolicy (thetaProgramSource args)
  where
    mapPolicy = replaceOnce "theta-inference-v1" "zero-theta-v1"

replaceOnce :: String -> String -> String -> String
replaceOnce old new = go
  where
    go [] = []
    go text@(c : rest)
      | old `isPrefixOf` text = new ++ drop (length old) text
      | otherwise = c : go rest
    isPrefixOf [] _ = True
    isPrefixOf (_ : _) [] = False
    isPrefixOf (x : xs) (y : ys) = x == y && isPrefixOf xs ys

replaceAll :: String -> String -> String -> String
replaceAll old new text
  | null old = text
  | otherwise = go text
  where
    go [] = []
    go input@(c : rest)
      | old `isPrefixOf` input = new ++ go (drop (length old) input)
      | otherwise = c : go rest
    isPrefixOf [] _ = True
    isPrefixOf (_ : _) [] = False
    isPrefixOf (x : xs) (y : ys) = x == y && isPrefixOf xs ys
malformedInferenceMissingBracketSource :: String
malformedInferenceMissingBracketSource =
  thetaProgramSource
    [ "arg malformed : supports(c_selected) by select from [e1"
    ]

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

parseAndElaborate :: String -> Either String (Policy, Program, Unit)
parseAndElaborate source = do
  program <- either (Left . show) Right (parseProgram source)
  policy <- either (Left . show) Right (parsePolicy thetaPolicySource)
  unit <- either (Left . show) Right (elaborate (registryOf policy) program policy)
  pure (policy, program, unit)

elaborateSource :: String -> Either String (Program, Policy, Either ElabError Unit)
elaborateSource source = do
  program <- either (Left . show) Right (parseProgram source)
  policy <- either (Left . show) Right (parsePolicy thetaPolicySource)
  pure (program, policy, elaborate (registryOf policy) program policy)


checkedVerdictJson :: String -> Either String (Verdict, String, String, Int)
checkedVerdictJson source = do
  program <- either (Left . show) Right (parseProgram source)
  policy <- either (Left . show) Right (parsePolicy thetaPolicySource)
  prepared <- either (Left . show) Right (prepareSource program policy)
  result <- case prepared of
    SourceRejected rejection -> Left ("unexpected admission rejection: " ++ show rejection)
    SourceAccepted sourceInput -> Right (runSourceCheck sourceInput)
  let verdict = sourceResultVerdict result
  case verdict of
    Verdict _ (Accept _ _ _) ->
      case sourceResultCheckInput result of
        Left err -> Left ("accepted source did not retain check input: " ++ show err)
        Right input ->
          Right
            ( verdict
            , renderJson (sourceResultJsonValue result)
            , printSExpr (encodeCheckInput input)
            , outcomeExitCode (verdictOutcome verdict)
            )
    _ -> Left ("expected accepted verdict, got: " ++ show verdict)

expectThetaError :: String -> (ElabError -> Bool) -> [String] -> Property
expectThetaError source matches fragments =
  case elaborateSource source of
    Left err -> counterexample ("fixture parse failed: " ++ err) False
    Right (_, _, Left err) ->
      conjoin
        [ counterexample ("unexpected constructor: " ++ show err) (matches err)
        , counterexample ("message: " ++ elabErrorMessage err) $
            all (`isInfixOf` elabErrorMessage err) fragments
        ]
    Right (_, _, Right unit) ->
      counterexample ("expected theta error, got " ++ show unit) False

expectThetaErrorWithPolicy :: String -> String -> (ElabError -> Bool) -> [String] -> Property
expectThetaErrorWithPolicy policySource source matches fragments =
  case (parseProgram source, parsePolicy policySource) of
    (Left err, _) -> counterexample ("fixture parse failed: " ++ show err) False
    (_, Left err) -> counterexample ("policy parse failed: " ++ show err) False
    (Right program, Right policy) ->
      case elaborate (registryOf policy) program policy of
        Left err ->
          conjoin
            [ counterexample ("unexpected constructor: " ++ show err) (matches err)
            , counterexample ("message: " ++ elabErrorMessage err) $
                all (`isInfixOf` elabErrorMessage err) fragments
            ]
        Right unit -> counterexample ("expected theta error, got " ++ show unit) False

replaceArg :: ArgId -> (Arg -> Arg) -> Program -> Program
replaceArg target f program =
  program
    { programDecls =
        [ case decl of
            DeclArg arg
              | argId arg == target -> DeclArg (f arg)
            _ -> decl
        | decl <- programDecls program
        ]
    }


prop_thetaDiagnosticMessages :: Property
prop_thetaDiagnosticMessages = once $
  conjoin
    [ counterexample "reference-count wording drifted" $
        elabErrorMessage (ThetaReferenceCountMismatch (ArgId "a") (RuleId "r") 2 1) ===
          "arg 'a': rule 'r' inference expects 2 reference(s) but 1 were supplied"
    , counterexample "unresolved-reference wording drifted" $
        elabErrorMessage (ThetaReferenceUnresolved (ArgId "a") (RuleId "r") 1 (ArgRef "x")) ===
          "arg 'a': rule 'r' inference premise #1 reference 'x' names neither a declared leaf nor prior argument"
    , counterexample "ambiguous-reference wording drifted" $
        elabErrorMessage (ThetaReferenceAmbiguous (ArgId "a") (RuleId "r") 1 (ArgRef "x")) ===
          "arg 'a': rule 'r' inference premise #1 reference 'x' is ambiguous between a declared leaf and a prior argument"
    , counterexample "shape-mismatch wording drifted" $
        elabErrorMessage (ThetaReferenceShapeMismatch (ArgId "a") (RuleId "r") 1 (ArgRef "x") (Prop (Pred "p") [])) ===
          "arg 'a': rule 'r' inference premise #1 reference 'x' selected proposition p but it does not match the premise pattern"
    , counterexample "conflict wording drifted" $
        elabErrorMessage
          ( ThetaReferenceConflict
              (ArgId "a")
              (RuleId "r")
              2
              (ArgRef "x")
              (Param "X")
              (TCon (FunSym "old") [])
              (TCon (FunSym "new") [])
          )
          === "arg 'a': rule 'r' inference premise #2 reference 'x' binds parameter 'X' inconsistently: old vs new"
    , counterexample "underivable-conclusion wording drifted" $
        elabErrorMessage (ThetaReferenceConclUnderivable (ArgId "a") (RuleId "r") 1 (ArgRef "x")) ===
          "arg 'a': rule 'r' inference premise #1 reference 'x' resolves to a prior argument whose conclusion is underivable"
    , counterexample "unbound-parameter wording drifted" $
        elabErrorMessage (ThetaParameterUnbound (ArgId "a") (RuleId "r") (Param "X")) ===
          "arg 'a': rule 'r' parameter 'X' is not bound by inferred theta"
    ]

prop_thetaFailureMatrix :: Property
prop_thetaFailureMatrix =
  conjoin
    [ once $
        expectThetaError
          tooFewReferenceSource
          (\err -> case err of
              ThetaReferenceCountMismatch (ArgId "a_bad") (RuleId "pair") 2 1 -> True
              _ -> False)
          ["expects 2", "1 were supplied"]
    , once $
        expectThetaError
          tooManyReferenceSource
          (\err -> case err of
              ThetaReferenceCountMismatch (ArgId "a3") (RuleId "pair") 2 3 -> True
              _ -> False)
          ["expects 2", "3 were supplied"]
    , once $
        expectThetaError
          undeclaredReferenceSource
          (\err -> case err of
              ThetaReferenceUnresolved (ArgId "a_bad") (RuleId "select") 1 (ArgRef "missing") -> True
              _ -> False)
          ["premise #1", "'missing'", "declared leaf nor prior argument"]
    , once $
        expectThetaError
          forwardReferenceSource
          (\err -> case err of
              ThetaReferenceUnresolved (ArgId "a_bad") (RuleId "pair") 1 (ArgRef "a_later") -> True
              _ -> False)
          ["premise #1", "'a_later'", "declared leaf nor prior argument"]
    , once $
        expectThetaError
          underivablePriorReferenceSource
          (\err -> case err of

              ThetaReferenceConclUnderivable (ArgId "a_bad") (RuleId "pair") 1 (ArgRef "a_missing") -> True
              _ -> False)
          ["premise #1", "'a_missing'", "conclusion is underivable"]
    , once $
        expectThetaError
          ambiguousReferenceSource
          (\err -> case err of
              ThetaReferenceAmbiguous (ArgId "a_bad") (RuleId "pair") 1 (ArgRef "a1") -> True
              _ -> False)
          ["premise #1", "'a1'", "declared leaf and a prior argument"]
    , once $
        expectThetaError
          shapeMismatchSource
          (\err -> case err of
              ThetaReferenceShapeMismatch (ArgId "a_bad") (RuleId "pair") 1 (ArgRef "e2") _ -> True
              _ -> False)
          ["premise #1", "'e2'", "selected proposition"]
    , once $
        expectThetaError
          unknownRulePrecedenceSource
          (\err -> case err of
              UnknownRule (ArgId "a_bad") (RuleId "missing") -> True
              _ -> False)
          ["unknown rule 'missing'"]
    ]
prop_shapeMismatchMatrix :: Property
prop_shapeMismatchMatrix =
  conjoin
    [ once $
        expectThetaErrorWithPolicy
          thetaPolicySource
          arityShapeSource
          (\err ->
             case err of
               ThetaReferenceShapeMismatch (ArgId "a_bad") (RuleId "select") 1 (ArgRef "e1") _ -> True
               _ -> False)
          ["premise #1", "'e1'", "selected proposition"]
    , once $
        expectThetaErrorWithPolicy
          constructorShapePolicySource
          constructorShapeSource
          (\err ->
             case err of
               ThetaReferenceShapeMismatch (ArgId "a_bad") (RuleId "select") 1 (ArgRef "e1") _ -> True
               _ -> False)
          ["premise #1", "'e1'", "selected proposition"]
    , once $
        expectThetaErrorWithPolicy
          literalShapePolicySource
          literalShapeSource
          (\err ->
             case err of
               ThetaReferenceShapeMismatch (ArgId "a_bad") (RuleId "select") 1 (ArgRef "e1") _ -> True
               _ -> False)
          ["premise #1", "'e1'", "selected proposition"]
    ]

prop_inferencePayloadCarriesState :: Property
prop_inferencePayloadCarriesState = once $
  case parseProgram payloadStateSource of
    Left err -> counterexample ("payload-state fixture rejected: " ++ show err) False
    Right program ->
      case [arg | DeclArg arg <- programDecls program, argId arg == ArgId "a1"] of
        [arg] ->
          counterexample ("inferred payload lost parser state: " ++ show (argInstantiation arg)) $
            argInstantiation arg
              === InferTheta
                (RuleId "select")
                [ArgRef "e1"]
                [(QuestionId "q", ArgRef "e1")]
                [ObligationId "hole"]
                AssuranceTrusted
        args -> counterexample ("expected one payload-state arg, got " ++ show args) False
  where
    payloadStateSource =
      thetaProgramSource
        [ "arg a1 : supports(c_selected) by select from [e1]"
        , "  discharge q with e1"
        , "  open q as hole"
        , "  assurance = trusted"
        ]

prop_inferencePrecedesDischargeAndConclusion :: Property
prop_inferencePrecedesDischargeAndConclusion = once $
  conjoin
    [ case elaborateSource inferenceBeforeDischargeSource of
        Left err -> counterexample ("conclusion-precedence fixture failed: " ++ err) False
        Right (_, _, Left (ConclusionMismatch (ArgId "a_bad") (PropId "c_promoted") _ _)) ->
          property True
        Right (_, _, Left err) ->
          counterexample ("inferred matching did not reach conclusion validation: " ++ show err) False
        Right (_, _, Right unit) ->
          counterexample ("expected conclusion mismatch, got " ++ show unit) False
    , case (parseProgram inferredLeafSource, parsePolicy thetaPolicySource) of
        (Right program, Right policy) ->
          let brokenProgram =
                replaceLeafProp
                  (LeafId "e1")
                  (Prop (Pred "selected") [TCon (FunSym "sys_a") [], TNum "0.74"])
                  program
              broken =
                replaceArg
                  (ArgId "a1")
                  (\arg ->
                    arg
                      { argConcl = SupportsClaim (PropId "c_promoted")
                      , argInstantiation = addBadDischarge (argInstantiation arg)
                      })
                  brokenProgram
           in case elaborate (registryOf policy) broken policy of
                Left (ThetaReferenceShapeMismatch (ArgId "a1") (RuleId "select") 1 (ArgRef "e1") _) ->
                  property True
                other -> counterexample ("inference did not precede later validation: " ++ show other) False
        other -> counterexample ("precedence fixture failed: " ++ show other) False
    ]
  where
    addBadDischarge (InferTheta r refs _ holes assurance) =
      InferTheta r refs [(QuestionId "missing", ArgRef "missing")] holes assurance
    addBadDischarge inst = inst

prop_duplicateReferenceSelectedTwice :: Property
prop_duplicateReferenceSelectedTwice = once $
  case
      ( parseProgram
          (thetaProgramSource
            [ "arg a_dup : supports(c_paired) by pair from [e1, e1]"
            ])
      , parseProgram
          (thetaProgramSource
            [ "arg a_dup : supports(c_paired) by pair(sys_a, 0.74)"
            ])
      , parsePolicy thetaPolicySource
      ) of
    (Right inferred0, Right explicit0, Right policy0) ->
      let inferred = dropLeaf (LeafId "e2") inferred0
          explicit = dropLeaf (LeafId "e2") explicit0
          policy = duplicatePairPremises policy0
       in case
            ( elaborate (registryOf policy) inferred policy
            , elaborate (registryOf policy) explicit policy
            ) of
            (Right inferredUnit, Right explicitUnit) ->
              case (lookup (ArgId "a_dup") (unitArgs inferredUnit), lookup (ArgId "a_dup") (unitArgs explicitUnit)) of
                (Just inferredTerm, Just explicitTerm) ->
                  conjoin
                    [ counterexample "duplicate references changed the complete term" $
                        inferredTerm === explicitTerm
                    , counterexample "duplicate references did not retain both selected premises" $
                        case inferredTerm of
                          SRule {srPremises = [SLeaf (LeafId "e1"), SLeaf (LeafId "e1")]} -> property True
                          other -> counterexample ("premises: " ++ show other) False
                    ]
                other -> counterexample ("missing duplicate-reference arg: " ++ show other) False
            other -> counterexample ("duplicate-reference fixture failed: " ++ show other) False
    other -> counterexample ("duplicate-reference fixture parse failed: " ++ show other) False

dropLeaf :: LeafId -> Program -> Program
dropLeaf target program =
  program
    { programDecls =
        [ decl
        | decl <- programDecls program
        , not (isTargetLeaf decl)
        ]
    }
  where
    isTargetLeaf (DeclLeaf leaf) = leafId leaf == target
    isTargetLeaf _ = False

duplicatePairPremises :: Policy -> Policy
duplicatePairPremises policy =
  policy
    { policyRules =
        [ if ruleId rule == RuleId "pair"
            then case rulePremises rule of
              _ : second : _ -> rule {rulePremises = [second, second]}
              _ -> rule
            else rule
        | rule <- policyRules policy
        ]
    }

asDerivedArgs :: Program -> Program
asDerivedArgs program =
  program
    { programDecls =
        [ case decl of
            DeclArg arg -> DeclArg (arg {argConcl = SupportsDerived (PropId "derived")})
            _ -> decl
        | decl <- programDecls program
        ]
    }
replaceLeafProp :: LeafId -> Prop -> Program -> Program
replaceLeafProp target prop program =
  program
    { programDecls =
        [ case decl of
            DeclLeaf leaf
              | leafId leaf == target -> DeclLeaf (leaf {leafProp = prop})
            _ -> decl
        | decl <- programDecls program
        ]
    }
prop_zeroPremiseInferenceSemantics :: Property
prop_zeroPremiseInferenceSemantics = once $
  case
      ( parseProgram (zeroProgramSource ["arg a0 : supports(c_selected) by empty()"])
      , parseProgram (zeroProgramSource ["arg a0 : supports(c_selected) by empty from []"])
      , parseProgram (zeroProgramSource ["arg bad : supports(c_selected) by unbound from []"])
      , parsePolicy zeroPolicySource
      ) of
    (Right explicitProgram, Right inferredProgram, Right unboundProgram, Right policy) ->
      case
          ( elaborate (registryOf policy) explicitProgram policy
          , elaborate (registryOf policy) inferredProgram policy
          , elaborate (registryOf policy) unboundProgram policy
          ) of
        (Right explicitUnit, Right inferredUnit, Left (ThetaParameterUnbound (ArgId "bad") (RuleId "unbound") (Param "X"))) ->
          conjoin
            [ counterexample "zero-premise inference changed Unit" $
                explicitUnit === inferredUnit
            , counterexample "zero-premise inference changed encoded Unit" $
                encodeUnit explicitUnit === encodeUnit inferredUnit
            ]
        other -> counterexample ("zero-premise matrix: " ++ show other) False
    other -> counterexample ("zero-premise fixture parse failed: " ++ show other) False


sourceProp :: String -> Prop
sourceProp numeric =
  Prop
    (Pred "source")
    [TCon (FunSym "sys_a") [], TNum numeric]

prop_normalizedNumericInference :: Property
prop_normalizedNumericInference = once $
  let inferredSourceNumeric =
        thetaProgramSource
          [ "arg a1 : supports(c_selected) by select from [e1]"
          , ""
          , "arg a3 : supports(c_paired) by pair from [a1, e2]"
          ]
   in case
        ( parseProgram inferredSourceNumeric
        , parsePolicy thetaPolicySource
        ) of
        (Right inferredProgram0, Right policy) ->
          let inferredProgram =
                asDerivedArgs $
                  replaceLeafProp (LeafId "e1") (sourceProp "0.71") $
                    replaceLeafProp (LeafId "e2") (sourceProp "0.710") inferredProgram0
           in case elaborate (registryOf policy) inferredProgram policy of
                Right inferredUnit ->
                  case lookup (ArgId "a3") (unitArgs inferredUnit) of
                    Just (SRule {srSubst = [(_, TCon (FunSym "sys_a") []), (_, TNum "0.71")]}) ->
                      property True
                    other -> counterexample ("normalized inferred theta: " ++ show other) False
                Left err -> counterexample ("numeric inference failed: " ++ show err) False
        other -> counterexample ("numeric fixture parse failed: " ++ show other) False

prop_boundLeafValueBindingParity :: Property
prop_boundLeafValueBindingParity =
  once $
    case
        ( parseAndElaborate boundLeafInferenceSource
        , parseAndElaborate explicitBoundLeafSource
        ) of
      (Right (_, _, boundUnit), Right (_, _, explicitUnit)) ->
        conjoin
          [ counterexample "value expansion did not precede bound-leaf theta inference" $
              boundUnit === explicitUnit
          , counterexample "bound-leaf inference did not retain the complete selected premise" $
              lookup (ArgId "a1") (unitArgs boundUnit)
                === Just
                  ( SRule
                      { srRule = RuleId "select"
                      , srSubst =
                          [ (Param "X", TCon (FunSym "sys_a") [])
                          , (Param "V", TNum "0.74")
                          ]
                      , srPremises = [SLeaf (LeafId "e1")]
                      , srDischarge = []
                      , srHoles = []
                      , srAssurance = AssuranceTrusted
                      }
                  )
          ]
      values -> counterexample ("bound-leaf parity fixture failed: " ++ show values) False

prop_parserAcceptsInference :: Property
prop_parserAcceptsInference = once $
  case parseProgram inferredLeafSource of
    Left err -> counterexample ("inferred source rejected: " ++ show err) False
    Right program ->
      let printed = printProgram program
       in conjoin
            [ counterexample ("printer dropped inferred refs: " ++ printed) $
                "from [e1]" `isInfixOf` printed
            , counterexample ("printed inferred source did not reparse: " ++ printed) $
                parseProgram printed === Right program
            ]

prop_explicitAndInferredSemanticParity :: Property
prop_explicitAndInferredSemanticParity = once $
  case
      ( parseAndElaborate explicitSource
      , parseAndElaborate inferredLeafSource
      , parseAndElaborate inferredPriorArgSource
      ) of
    (Right (_, _, explicitUnit), Right (_, _, leafUnit), Right (_, _, priorUnit)) ->
      case
          ( checkedVerdictJson explicitSource
          , checkedVerdictJson inferredLeafSource
          , checkedVerdictJson inferredPriorArgSource
          ) of
        ( Right (explicitVerdict, explicitJson, explicitCore, explicitExit)
          , Right (leafVerdict, leafJson, leafCore, leafExit)
          , Right (priorVerdict, priorJson, priorCore, priorExit)
          ) ->
          conjoin
            [ counterexample "leaf inference changed Unit" (explicitUnit === leafUnit)
            , counterexample "prior-argument inference changed Unit" (explicitUnit === priorUnit)
            , counterexample "leaf inference changed encoded Unit" (encodeUnit explicitUnit === encodeUnit leafUnit)
            , counterexample "prior-argument inference changed encoded Unit" (encodeUnit explicitUnit === encodeUnit priorUnit)
            , counterexample "leaf inference changed checked verdict" (explicitVerdict === leafVerdict)
            , counterexample "prior-argument inference changed checked verdict" (explicitVerdict === priorVerdict)
            , counterexample "leaf inference changed checked verdict JSON" (explicitJson === leafJson)
            , counterexample "prior-argument inference changed checked verdict JSON" (explicitJson === priorJson)
            , counterexample "leaf inference changed rendered core S-expression" (explicitCore === leafCore)
            , counterexample "prior-argument inference changed rendered core S-expression" (explicitCore === priorCore)
            , counterexample "leaf inference changed exit classification" (explicitExit === leafExit)
            , counterexample "prior-argument inference changed exit classification" (explicitExit === priorExit)
            ]
        values -> counterexample ("checking failed: " ++ show values) False
    values -> counterexample ("parse/elaboration failed: " ++ show values) False

prop_priorArgumentEmbedsCompleteRule :: Property
prop_priorArgumentEmbedsCompleteRule = once $
  case (parseAndElaborate explicitSource, parseAndElaborate inferredPriorArgSource) of
    (Right (_, _, explicitUnit), Right (_, _, inferredUnit)) ->
      case (lookup (ArgId "a2") (unitArgs explicitUnit), lookup (ArgId "a2") (unitArgs inferredUnit)) of
        (Just explicitTerm, Just inferredTerm) ->
          conjoin
            [ counterexample "inferred a2 differs from explicit a2" $
                inferredTerm === explicitTerm
            , counterexample ("inferred a2 did not embed a complete prior SRule: " ++ show inferredTerm) $
                isCompletePriorRule inferredTerm
            ]
        values -> counterexample ("missing a2 term(s): " ++ show values) False
    values -> counterexample ("prior-argument fixture failed: " ++ show values) False
  where

    isCompletePriorRule (SRule {srRule = RuleId "promote", srPremises = [SRule {}]}) = True
    isCompletePriorRule _ = False
prop_spellingDivergenceIsCheckerEquivalent :: Property
prop_spellingDivergenceIsCheckerEquivalent = once $
  let base =
        thetaProgramSource
          [ "arg a1 : supports(c_selected) by select(sys_a, 0.74)"
          , "  assurance = trusted"
          ]
      explicit =
        replaceAll "select(sys_a, 0.71)" "select(sys_a, 0.710)" $
          replaceAll "0.74" "0.71" base
      inferred =
        replaceAll "0.74" "0.71" $
          replaceAll "select(sys_a, 0.74)" "select from [e1]" base
   in case
        ( parseAndElaborate explicit
        , parseAndElaborate inferred
        , checkedVerdictJson explicit
        , checkedVerdictJson inferred
        ) of
        ( Right (_, _, explicitUnit)
          , Right (_, _, inferredUnit)
          , Right (explicitVerdict, explicitJson, explicitCore, explicitExit)
          , Right (inferredVerdict, inferredJson, inferredCore, inferredExit)
          ) ->
            case
                ( lookup (ArgId "a1") (unitArgs explicitUnit)
                , lookup (ArgId "a1") (unitArgs inferredUnit)
                ) of
                ( Just (SRule {srSubst = explicitTheta})
                  , Just (SRule {srSubst = inferredTheta})
                  ) ->
                  conjoin
                    [ counterexample "spelling divergence changed verdict" $
                        explicitVerdict === inferredVerdict
                    , counterexample "spelling divergence changed exit classification" $
                        explicitExit === inferredExit
                    , counterexample "spelling divergence changed verdict JSON" $
                        explicitJson === inferredJson
                    , counterexample "spelling divergence was not sameTerm-equivalent" $
                        case (lookup (Param "V") explicitTheta, lookup (Param "V") inferredTheta) of
                          (Just old, Just new) -> property (sameTerm old new)
                          _ -> counterexample "missing divergent numeric binding" False
                    , counterexample "spelling divergence did not change core bytes" $
                        explicitCore /= inferredCore
                    ]
                other -> counterexample ("divergent theta terms: " ++ show other) False
        other -> counterexample ("divergence fixture failed before checking: " ++ show other) False
prop_repeatedParameterContracts :: Property
prop_repeatedParameterContracts = once $
  case
      ( parseProgram inferredPairSource
      , parseProgram conflictingPairSource
      , parsePolicy thetaPolicySource
      ) of
    (Right inferredProgram, Right conflictingProgram, Right policy) ->
      case
          ( elaborate (registryOf policy) inferredProgram policy
          , elaborate (registryOf policy) conflictingProgram policy
          ) of
        (Right _, Left err) ->
          case err of
            ThetaReferenceConflict (ArgId "a3") (RuleId "pair") 2 (ArgRef "e2") (Param parameter) old new ->
              conjoin
                [ property (not (sameTerm old new))
                , counterexample ("conflict message: " ++ elabErrorMessage err) $
                    all (`isInfixOf` elabErrorMessage err)
                      ["premise #2", "'e2'", "'" ++ parameter ++ "'", "inconsistently"]
                ]
            _ -> counterexample ("unexpected repeated-parameter error: " ++ show err) False
        (Left err, _) ->
          counterexample ("consistent repeated bindings were rejected: " ++ show err) False
        (_, Right unit) ->
          counterexample ("conflicting repeated bindings were accepted: " ++ show unit) False

prop_unboundConclusionParameterRejected :: Property
prop_unboundConclusionParameterRejected = once $
  case (parseProgram unboundConclusionSource, parsePolicy thetaPolicySource) of
    (Right program, Right policy) ->
      case elaborate (registryOf policy) program policy of
        Left err@(ThetaParameterUnbound (ArgId "a_bad") (RuleId "conclude_only") (Param "V")) ->
          counterexample ("unbound-parameter message: " ++ elabErrorMessage err) $
            all (`isInfixOf` elabErrorMessage err)
              ["arg 'a_bad'", "rule 'conclude_only'", "parameter 'V'", "not bound by inferred theta"]
        Left err ->
          counterexample ("unexpected conclusion-only error: " ++ show err) False
        Right unit ->
          counterexample ("conclusion-only parameter was accepted: " ++ show unit) False
    values -> counterexample ("unbound-parameter fixture parse failed: " ++ show values) False

prop_parserInferenceListsRoundTrip :: Property
prop_parserInferenceListsRoundTrip = once $
  conjoin
    [ roundTrips "empty inference list" emptyInferenceSource "from []"
    , roundTrips "two-reference inference list" twoReferenceInferenceSource "from [a1, e1]"
    , roundTrips "three-reference inference list" threeReferenceInferenceSource "from [a1, e1, e2]"
    , counterexample "trailing comma was accepted" $
        isLeft (parseProgram malformedInferenceTrailingCommaSource)
    , counterexample "missing closing bracket was accepted" $
        isLeft (parseProgram malformedInferenceMissingBracketSource)
    ]
  where
    isLeft (Left _) = True
    isLeft _ = False
    roundTrips fixtureLabel source needle =
      case parseProgram source of
        Left err -> counterexample (fixtureLabel ++ " rejected: " ++ show err) False
        Right program ->
          let printed = printProgram program
           in conjoin
                [ counterexample (fixtureLabel ++ " was not preserved: " ++ printed) $
                    needle `isInfixOf` printed
                , counterexample (fixtureLabel ++ " did not reparse: " ++ printed) $
                    parseProgram printed === Right program
                ]
-- | The word @from@ is contextual in an argument body, not a lexer-reserved
-- identifier. Both a rule and a leaf may therefore carry that spelling.
contextualPolicySource :: String
contextualPolicySource =
  unlines
    [ "policy contextual-from-v1"
    , "sort System"
    , "con sys_a : System"
    , "pred source(System, Num)"
    , "pred selected(System, Num)"
    , "rule from(X)"
    , "  mode = strict"
    , "  premises = [ source(X, 0.74) ]"
    , "  conclusion = selected(X, 0.74)"
    , "  allow-trusted = true"
    , "  certifiers = []"
    ]
contextualFromSource =
  unlines
    [ "artifact contextual_from at sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    , "policy contextual-from-v1"
    , "use backends []"
    , ""
    , "leaf from : source(sys_a, 0.74)"
    , "  kind = observed"
    , "  provenance = user"
    , "  refs = []"
    , ""
    , "arg positional : supports(c) by from(x)"
    , ""
    , "arg inferred : supports(c) by from from [from]"
    ]

prop_contextualFromCollision :: Property
prop_contextualFromCollision = once $
  case (parseProgram contextualFromSource, parsePolicy contextualPolicySource) of
    (Left err, _) -> counterexample ("contextual from fixture rejected: " ++ show err) False
    (_, Left err) -> counterexample ("contextual from policy rejected: " ++ show err) False
    (Right program, Right policy) ->
      case [a | DeclArg a <- programDecls program] of
        [positional, inferred] ->
          conjoin
            [ counterexample "contextual policy did not retain rule named from" $
                any ((== RuleId "from") . ruleId) (policyRules policy)
            , counterexample "from(x) was not parsed as explicit theta" $
                argInstantiation positional ===
                  ExplicitTheta
                    ( SRule
                        { srRule = RuleId "from"
                        , srSubst = [(Param "1", TCon (FunSym "x") [])]
                        , srPremises = []
                        , srDischarge = []
                        , srHoles = []
                        , srAssurance = AssuranceNone
                        }
                    )
            , counterexample "from from [from] was not parsed as inferred theta" $
                argInstantiation inferred ===
                  InferTheta (RuleId "from") [ArgRef "from"] [] [] AssuranceNone
            , counterexample ("contextual from spelling was not preserved: " ++ printProgram program) $
                parseProgram (printProgram program) === Right program
            ]
        args -> counterexample ("expected two contextual-from args, got " ++ show args) False

thetaInferenceSpecProps :: [(String, IO Result)]
thetaInferenceSpecProps =
  [ ("parser accepts plain-argument theta inference", quickCheckResult prop_parserAcceptsInference)
  , ("explicit and inferred forms preserve Unit, wire, checked JSON, core, and exit", quickCheckResult prop_explicitAndInferredSemanticParity)
  , ("spelling divergence preserves checker outcome but changes core bytes", quickCheckResult prop_spellingDivergenceIsCheckerEquivalent)
  , ("prior-argument inference embeds the complete earlier SRule", quickCheckResult prop_priorArgumentEmbedsCompleteRule)
  , ("repeated parameters normalize consistently and reject conflicts", quickCheckResult prop_repeatedParameterContracts)
  , ("conclusion-only parameters are rejected when unbound", quickCheckResult prop_unboundConclusionParameterRejected)
  , ("plain-argument empty and comma-separated lists round-trip", quickCheckResult prop_parserInferenceListsRoundTrip)
  , ("contextual from rule and leaf names round-trip", quickCheckResult prop_contextualFromCollision)
  , ("direct theta diagnostics render stably", quickCheckResult prop_thetaDiagnosticMessages)
  , ("theta inference failure matrix is fail-closed and ordered", quickCheckResult prop_thetaFailureMatrix)
  , ("predicate, constructor, literal, and arity shape failures are explicit", quickCheckResult prop_shapeMismatchMatrix)
  , ("inferred payload retains rule refs, discharges, holes, and assurance", quickCheckResult prop_inferencePayloadCarriesState)
  , ("inference precedes discharge and conclusion validation", quickCheckResult prop_inferencePrecedesDischargeAndConclusion)
  , ("duplicate references retain selected premises", quickCheckResult prop_duplicateReferenceSelectedTwice)
  , ("zero-premise inference has explicit semantic parity", quickCheckResult prop_zeroPremiseInferenceSemantics)
  , ("normalized numeric references use sameTerm", quickCheckResult prop_normalizedNumericInference)
  , ("bound selected leaf expands before theta inference", quickCheckResult prop_boundLeafValueBindingParity)
  ]
