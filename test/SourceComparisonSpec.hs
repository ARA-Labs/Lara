module SourceComparisonSpec (sourceComparisonSpecProps) where

import Data.List (sort)
import Test.QuickCheck
import qualified Lara.AST as A
import qualified Lara.Elaborate as Elaborate
import Lara.Elaborate.ValueBinding (expandInquiryValueBindings)
import Lara.Prop (Prop (..), Term (..), Pred (..), FunSym (..))
import qualified Lara.Syntax as Syntax
import Lara.Strict (SExpr (..))
import Lara.Wire (PublicStatus (..))
import qualified Lara.Process.Source as Source
import qualified Lara.Process.Source.Types as T
import qualified Lara.Process.Source.Diagnostic as D

comparisonSource :: IO (Either String (A.Program, A.Policy, T.SourceInput))
comparisonSource = do
  programText <- readFile "examples/S2/example.lara"
  policyText <- readFile "examples/S2/ord-v1.policy.lara"
  pure $ do
    authored <- either (Left . show) Right (Syntax.parseProgram programText)
    policy <- either (Left . show) Right (Syntax.parsePolicy policyText)
    program <- either (Left . show) Right (expandInquiryValueBindings (A.policySigma policy) authored)
    input <- makeSource program policy
    pure (program, policy, input)

makeSource :: A.Program -> A.Policy -> Either String T.SourceInput
makeSource program policy = T.mkSourceInput program policy identity Nothing
  where
    identity = T.ReplayIdentity (T.CoreVersion "lara-core@0.3") (A.policyId policy)
      [T.BackendIdentity backend (T.BackendVersion version) | (backend, version) <- A.programBackends program]
      (sort (map fst (A.policyTheories policy))) (A.programDigest program)

prop_originalComparisonContext :: Property
prop_originalComparisonContext = once $ ioProperty $ do
  loaded <- comparisonSource
  pure $ case loaded of
    Left error' -> counterexample error' False
    Right (program, policy, input) -> case Source.checkSource input of
      Left rejection -> counterexample (show rejection) False
      Right observation ->
        let accepted = Source.observationAcceptedSource observation
            declared = Elaborate.acceptedSourceDeclared accepted
            semantic = Elaborate.acceptedSourceSemantic accepted
         in case (lookup (A.ArgId "a1") (A.unitArgs declared),
                  [A.claimFormal claim | A.DeclClaim claim <- A.programDecls semantic, A.claimId claim == A.PropId "c2"]) of
              (Just recheck@(A.SRule _ _ _ _ _ (A.AssuranceCert certificate)), [goal]) ->
                let qid = A.LeafId "quarantined"
                    q = A.Leaf qid (Prop (Pred "num_lt") [TNum "0", TNum "1"]) A.Assumed A.User [] Nothing
                    patternOf (Prop predicate terms) = A.AtomPat predicate (map A.PLit terms)
                    outerId = A.RuleId "outer-order"
                    outer = A.Rule outerId [] A.Strict [patternOf goal, patternOf (A.leafProp q)] []
                      (patternOf goal) False [A.CertRef (A.certBackend certificate) (A.certVersion certificate) (A.certTheory certificate)] []
                    key = (A.Assumed, A.User)
                    policy' = policy
                      { A.policyRules = A.policyRules policy ++ [outer]
                      , A.policyAdmission = (key, A.Quarantine) : filter ((/= key) . fst) (A.policyAdmission policy)
                      }
                    payload first = SList [SAtom "ordcmp", SList [SAtom "prem", SAtom first], SList [SAtom "prem", SAtom "quarantined"]]
                    argument first = A.DeclArg (A.Arg (A.ArgId "submitted") (A.SupportsDerived (A.PropId "submitted"))
                      (A.ExplicitTheta (A.SRule outerId [] [recheck, A.SLeaf qid] [] []
                        (A.AssuranceCert certificate{A.certPayload = payload first}))))
                    check first expected = case makeSource program{A.programDecls = A.programDecls program ++ [A.DeclLeaf q, argument first]} policy' of
                      Left error' -> counterexample error' False
                      Right source -> expected (Source.checkSource source)
                    rejected result = case result of
                      Left refusal -> refusal === D.SourceRejection (D.SourceDiagnostic (D.Structural (D.InvalidNamedCertificate (A.ArgId "submitted"))))
                      Right _ -> counterexample "certified semantic comparison rescued the authored certificate" False
                    acceptedResult result = case result of
                      Left refusal -> counterexample (show refusal) False
                      Right actual -> Source.publicStatus actual goal === Published A.Justified
                    derivedId = A.RuleId "comparison-dependent"
                    derivedRule = A.Rule derivedId [] A.Defeasible [patternOf goal] [] (patternOf goal) False [] []
                    dependent = A.DeclArg (A.Arg (A.ArgId "dependent") (A.SupportsDerived (A.PropId "dependent"))
                      (A.InferTheta derivedId [A.ArgRef "a1"] [] [] A.AssuranceNone))
                    namedReference = case makeSource program{A.programDecls = A.programDecls program ++ [dependent]}
                      policy{A.policyRules = A.policyRules policy ++ [derivedRule]} of
                        Left error' -> counterexample error' False
                        Right source -> case Source.checkSource source of
                          Left refusal -> counterexample (show refusal) False
                          Right actual -> conjoin
                            [ Source.publicStatus actual goal === Published A.Justified
                            , property (A.ArgId "dependent" `elem` Source.observationNames actual)
                            ]
                 in conjoin [check "a1" rejected, check "0" acceptedResult, namedReference]
              _ -> counterexample "S2 is missing its checked recheck argument or comparison goal" False

prop_originalComparisonGuards :: Property
prop_originalComparisonGuards = once $ ioProperty $ do
  loaded <- comparisonSource
  pure $ case loaded of
    Left error' -> counterexample error' False
    Right (program, policy, _) ->
      case ([comparison | A.DeclComparison comparison <- A.programDecls program],
            [leaf | A.DeclLeaf leaf <- A.programDecls program, A.leafId leaf == A.LeafId "e2"],
            [leaf | A.DeclLeaf leaf <- A.programDecls program, A.leafId leaf == A.LeafId "e3"]) of
        ([comparison], [result], [binding]) ->
          let check sourceProgram = case makeSource sourceProgram policy of
                Left error' -> counterexample error' False
                Right source -> case Source.checkSource source of
                  Left refusal -> refusal === D.SourceRejection (D.SourceDiagnostic
                    (D.Structural (D.InvalidComparison (A.ccId (A.cmpClaim comparison)))))
                  Right _ -> counterexample "original comparison predicate was bypassed" False
              undeclared (A.DeclComparison item) = A.DeclComparison item{A.cmpSupports = Just (A.PropId "missing")}
              undeclared other = other
              missing = program{A.programDecls = map undeclared (A.programDecls program)}
              rewrite term = case term of
                TNum "0.74" -> TCon (FunSym "late-score") []
                TCon name arguments -> TCon name (map rewrite arguments)
                _ -> term
              rewriteProp (Prop predicate terms) = Prop predicate (map rewrite terms)
              result' = result{A.leafId = A.LeafId "late-result", A.leafProp = rewriteProp (A.leafProp result)}
              binding' = binding{A.leafId = A.LeafId "late-binding", A.leafProp = rewriteProp (A.leafProp binding)}
              later = comparison
                { A.cmpResult = A.LeafId "late-result", A.cmpBinding = A.LeafId "late-binding"
                , A.cmpRecheckArg = A.ArgId "late-recheck", A.cmpBridgeArg = A.ArgId "late-bridge"
                , A.cmpClaim = (A.cmpClaim comparison){A.ccId = A.PropId "late-claim", A.ccNlRaw = ""}
                }
              late = program
                { A.programValueBindings = [A.ValueBinding (A.ValueName "late-score") (TNum "0.75")]
                , A.programDecls = A.programDecls program ++ [A.DeclLeaf result', A.DeclLeaf binding', A.DeclComparison later]
                }
           in conjoin [check missing, check late]
        _ -> counterexample "S2 comparison source fields are missing" False

sourceComparisonSpecProps :: [(String, IO Result)]
sourceComparisonSpecProps =
  [ ("source original comparison priors do not alias certified semantic terms", quickCheckResult prop_originalComparisonContext)
  , ("source original comparison guards require targets and first-comparison blame", quickCheckResult prop_originalComparisonGuards)
  ]
