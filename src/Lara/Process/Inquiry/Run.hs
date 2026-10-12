module Lara.Process.Inquiry.Run (runBounded, runInquiryFile, exitCodeOf) where

import Control.Exception (IOException, evaluate, try)
import Control.Monad (unless)
import qualified Data.ByteString as BS
import Data.List (find, subsequences)
import Numeric.Natural (Natural)
import qualified Lara.AST as AST
import Lara.Prop (Prop(..), Pred(..))
import Lara.Process.Types
import Lara.Process.Inquiry.Types
import Lara.Process.Inquiry.Wire (parseInquiryInputBS)
import qualified Lara.Process.Wire as W
import qualified Lara.Process.History as H
import qualified Lara.Process.Audit.Types as C
import qualified Lara.Process.Family as F
import qualified Lara.Process.Enumerate as E
import qualified Lara.Process.Projection as P
import qualified Lara.Process.Analysis as A
import qualified Lara.Process.Impact as I
import qualified Lara.Process.Source.Types as S

embeddedProblem :: InquiryInput -> Problem
embeddedProblem input = let d = inquiryProcess input in Problem (H.extract (`elem` W.documentAdmits d) (W.documentSource d)) (W.documentUnrecorded d)
familyOf :: InquiryInput -> C.FamilySpec
familyOf input = C.FamilySpec (embeddedProblem input) (inquiryBase input) (inquirySlots input)
configOf :: InquiryInput -> C.AuditConfig
configOf input = C.AuditConfig (inquiryClaims input) (inquiryWitnesses input) (inquiryKinds input) (inquiryAssumptions input)
limitsOf :: InquiryInput -> C.EnumerationLimits
limitsOf input = C.EnumerationLimits (min (limitHistories limits) (W.limitCompletions (W.documentLimits (inquiryProcess input)))) (limitSearchSteps limits) (limitSources limits)
  where limits = inquiryLimits input
ceilingOf :: LimitCounter -> Natural
ceilingOf c = case c of Histories -> 10000; Sources -> 10000; SourceBytes -> 1048576; Declarations -> 10000; SearchSteps -> 200000; Pairs -> 4096; Subsets -> 4096
declaredCap :: InquiryLimits -> LimitCounter -> Natural
declaredCap l c = case c of Histories -> limitHistories l; Sources -> limitSources l; SourceBytes -> limitSourceBytes l; Declarations -> limitDeclarations l; SearchSteps -> limitSearchSteps l; Pairs -> limitPairs l; Subsets -> limitSubsets l
checkCounter :: InquiryLimits -> LimitCounter -> Natural -> Either RunRefusal ()
checkCounter limits counter actual = let cap = min (ceilingOf counter) (declaredCap limits counter) in unless (actual <= cap) (Left (Limit counter actual cap))
declarationsOf :: S.SourceInput -> Natural
declarationsOf = H.naturalLength . AST.programDecls . S.sourceProgram
endpointsOf :: RequestSpec -> Natural
endpointsOf ImpactRequest{} = 2
endpointsOf VerifyImpactRequest{} = 2
endpointsOf _ = 0
endpointDeclarationsOf :: RequestSpec -> Natural
endpointDeclarationsOf (ImpactRequest _ before after _) = declarationsOf before + declarationsOf after
endpointDeclarationsOf (VerifyImpactRequest _ before after _) = declarationsOf before + declarationsOf after
endpointDeclarationsOf _ = 0
subsetsOf :: InquiryInput -> RequestSpec -> Natural
subsetsOf input MinimalAssumptionsRequest{} = 2 ^ H.naturalLength (H.dedupLast (inquiryCatalog input))
subsetsOf _ _ = 0
requestLabel :: RequestSpec -> String
requestLabel request = case request of
  StatusRequest l _ -> l; AuditRequest l _ _ _ -> l; StableRequest l _ -> l
  SensitivityRequest l _ _ -> l; SlotsSensitiveRequest l _ _ -> l
  MinimalAssumptionsRequest l _ -> l; ImpactRequest l _ _ _ -> l; VerifyImpactRequest l _ _ _ -> l
queryLabel :: QuerySpec -> String
queryLabel (VerdictQuery l _) = l
queryLabel (AuditQuery l _ _ _) = l
resolveReference :: C.FamilySpec -> ReferenceSpec -> Maybe C.Completion
resolveReference spec (ReferenceSpec history assignment) = C.Completion history <$> F.resolveAssignment spec assignment
resolvedClaims :: InquiryInput -> [ClaimId] -> Either RunRefusal [Prop]
resolvedClaims input = traverse resolve
  where resolve claim = maybe (Left (Malformed "unresolved claim in impact request")) (Right . C.bindingQuery) (find ((== claim) . C.bindingClaim) (inquiryClaims input))
-- A missing binding is still a typed dispatch failure. The frozen reference's
-- inert atom is used ONLY to compute the pre-validation read footprint, never as
-- an accepted query or a result. This preserves pairs-before-malformed priority.
accountingClaims :: InquiryInput -> [ClaimId] -> [Prop]
accountingClaims input = map (\claim -> maybe (Prop (Pred "") []) C.bindingQuery (find ((== claim) . C.bindingClaim) (inquiryClaims input)))
data PreparedRequest = PreparedRequest RequestSpec (Maybe I.Comparison)
prepareRequest :: InquiryInput -> RequestSpec -> PreparedRequest
prepareRequest input request = PreparedRequest request $ case request of
  ImpactRequest _ before after claims -> Just (I.compareEndpoints (I.observeEndpoint before) (I.observeEndpoint after) (accountingClaims input claims))
  VerifyImpactRequest _ before after certificate -> Just (I.compareEndpoints (I.observeEndpoint before) (I.observeEndpoint after) (I.certificateQueries certificate))
  _ -> Nothing
pairsFor :: InquiryInput -> [C.Completion] -> PreparedRequest -> Natural
pairsFor input rows (PreparedRequest request comparison) = case comparison of
  Just cached -> I.comparisonPairCount cached
  Nothing -> case request of
    MinimalAssumptionsRequest{} -> sum [H.naturalLength (A.restrict rows subset) | subset <- subsequences (H.dedupLast (inquiryCatalog input))]
    _ -> H.naturalLength rows
actualFor :: InquiryInput -> E.EnumeratedFamily -> Natural -> [PreparedRequest] -> LimitCounter -> Natural
actualFor input enumeration bytes prepared counter = case counter of
  Histories -> H.naturalLength (E.enumeratedHistories enumeration)
  SourceBytes -> bytes
  Sources -> H.naturalLength rows + sum (map endpointsOf (inquiryRequests input))
  Declarations -> sum [declarationsOf (inquiryBase input) + sum [H.naturalLength (S.fragmentDecls (C.choiceFragment (C.selectionChoice selection))) | selection <- C.completionAssignment row] | row <- rows]
    + sum (map endpointDeclarationsOf (inquiryRequests input))
  SearchSteps -> E.enumeratedHistorySteps enumeration + E.enumeratedLogicalExtensions enumeration
  Pairs -> sum (map (pairsFor input rows) prepared)
  Subsets -> sum (map (subsetsOf input) (inquiryRequests input))
  where rows = E.enumeratedCompletions enumeration
ofRefusal :: C.EnumerationRefusal -> RunRefusal
ofRefusal refusal = case refusal of C.HistoriesRefusal actual cap -> Limit Histories actual cap; C.StepsRefusal actual cap -> Limit SearchSteps actual cap; C.ProductsRefusal actual cap -> Limit Sources actual cap
runBounded :: InquiryInput -> Natural -> Either RunRefusal [InquiryResult]
runBounded input bytes = do
  let problem = embeddedProblem input
      document = inquiryProcess input
      limits = inquiryLimits input
      eventCount = H.naturalLength (H.dedupLast (H.base problem ++ problemUnrecorded problem))
      eventCap = min 8 (W.limitEvents (W.documentLimits document))
  unless (eventCount <= eventCap) (Left (Limit Histories eventCount eventCap))
  checkCounter limits SourceBytes bytes
  enumeration <- either (Left . ofRefusal) Right (E.enumerateFamily (familyOf input) (limitsOf input))
  let prepared = map (prepareRequest input) (inquiryRequests input)
      actual = actualFor input enumeration bytes prepared
      rows = E.enumeratedCompletions enumeration
      labels = map queryLabel (W.documentQueries document) ++ map requestLabel (inquiryRequests input)
  mapM_ (\counter -> checkCounter limits counter (actual counter)) [Sources,Subsets]
  mapM_ (\counter -> checkCounter limits counter (actual counter)) [SourceBytes,Declarations,Pairs,Subsets,Sources,SearchSteps]
  unless (H.naturalLength labels == H.naturalLength (H.dedupLast labels)) (Left (Malformed "duplicate result labels"))
  let validRef reference = maybe False (`elem` rows) (resolveReference (familyOf input) reference)
      referenceValid request = case request of SensitivityRequest _ r _ -> validRef r; SlotsSensitiveRequest _ r _ -> validRef r; _ -> True
  unless (all referenceValid (inquiryRequests input)) (Left (Malformed "unresolved or out-of-family source reference"))
  mapM_ (\request -> case request of ImpactRequest _ _ _ claims -> () <$ resolvedClaims input claims; _ -> Right ()) (inquiryRequests input)
  let checked = P.checkFamily (configOf input) enumeration
      embedded query = case query of
        VerdictQuery label formula -> let answer = H.answer problem formula in InquiryResult label (HistoryVerdict (H.naturalLength (E.enumeratedHistories enumeration))
          (OutcomeAnswer (answerVerdict answer) (answerCount answer) (map stampedId <$> answerHolds answer) (map stampedId <$> answerFails answer)))
        AuditQuery label claim witness profile -> InquiryResult label (AuditBody (A.familyAudit checked claim witness profile))
  requests <- traverse (dispatch checked input) prepared
  pure (map embedded (W.documentQueries document) ++ requests)
dispatch :: P.CheckedFamily -> InquiryInput -> PreparedRequest -> Either RunRefusal InquiryResult
dispatch checked input (PreparedRequest request comparison) = InquiryResult (requestLabel request) <$> case request of
  StatusRequest _ c -> Right (StatusBody (A.familyStatus checked c))
  AuditRequest _ c w p -> Right (AuditBody (A.familyAudit checked c w p))
  StableRequest _ o -> Right (StabilityBody (A.stability checked o))
  SensitivityRequest _ r o -> sensitivity SensitivityBody r o
  SlotsSensitiveRequest _ r o -> sensitivity SlotsSensitiveBody r o
  MinimalAssumptionsRequest _ t -> Right (AssumptionsBody (A.assumptions checked t (inquiryCatalog input)))
  ImpactRequest _ _ _ claims -> do
    _ <- resolvedClaims input claims
    maybe invalid (Right . ImpactBody . I.comparisonResult) comparison
  VerifyImpactRequest _ _ _ certificate -> maybe invalid (\cached -> Right (VerificationBody (I.verifyImpact cached certificate))) comparison
  where
    invalid = Left (Malformed "unresolved or out-of-family source reference")
    sensitivity constructor reference observable = do
      completion <- maybe invalid Right (resolveReference (familyOf input) reference)
      maybe invalid (Right . constructor) (A.sensitivity checked observable completion)
runInquiryFile :: FilePath -> IO (Either RunRefusal (W.Names,[InquiryResult]))
runInquiryFile path = do
  readResult <- try (BS.readFile path) :: IO (Either IOException BS.ByteString)
  case readResult of
    Left _ -> pure (Left (IOFailure ("cannot read " ++ path)))
    Right bytes | not (BS.isValidUtf8 bytes) -> pure (Left (IOFailure ("cannot read " ++ path)))
    Right bytes -> do
      let result = do
            input <- parseInquiryInputBS bytes
            results <- runBounded input (fromIntegral (BS.length bytes))
            pure (W.documentNames (inquiryProcess input),results)
      -- Force the entire success/refusal decision before the CLI emits any line.
      _ <- evaluate (case result of Left refusal -> refusal `seq` (); Right (_,results) -> foldr (\result' rest -> resultBody result' `seq` rest) () results)
      pure result
exitCodeOf :: RunRefusal -> Int
exitCodeOf Unsupported{} = 1
exitCodeOf Limit{} = 1
exitCodeOf _ = 2
