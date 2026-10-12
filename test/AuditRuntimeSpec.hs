module AuditRuntimeSpec (auditRuntimeSpecProps) where

import Data.Either (isLeft)
import Data.Ratio ((%))
import Test.QuickCheck hiding (witness)
import qualified Lara.AST as A
import Lara.Prop (Prop (..), Pred (..))
import Lara.Sigma (declarePred)
import Lara.Strict (SExpr (..))
import Lara.Wire (parseSExpr,PublicStatus (..))
import qualified Lara.Process.Types as P
import qualified Lara.Process.Source as S
import qualified Lara.Process.Source.Types as T
import qualified Lara.Process.Source.Wire as W
import qualified Lara.Process.Source.Diagnostic as Diagnostic
import qualified Lara.Process.Audit.Types as D
import qualified Lara.Process.Audit as Audit
import qualified Lara.Process.Enumerate as E
import qualified Lara.Process.Projection as R
import qualified Lara.Process.Analysis as Analysis

sourceTrees :: SExpr -> [SExpr]
sourceTrees value@(SList (SAtom "checked-source" : _)) = [value]
sourceTrees (SList xs) = concatMap sourceTrees xs
sourceTrees _ = []

withBase :: (T.SourceInput -> Property) -> Property
withBase check = once $ ioProperty $ do
  text <- readFile "fixtures/process/inquiry/normalized-support.sexp"
  pure $ case parseSExpr text of
    Left err -> counterexample (show err) False
    Right tree -> case sourceTrees tree of
      wire : _ -> case either (Left . show) Right (W.decodeSource wire) >>= simpleSource of
        Left err -> counterexample (show err) False
        Right source -> check source
      [] -> counterexample "missing checked-source template" False

simpleSource :: T.SourceInput -> Either String T.SourceInput
simpleSource template = case [templateClaim | A.DeclClaim templateClaim <- A.programDecls original] of
  templateClaim : _ -> T.mkSourceInput program policy (T.sourceReplay template) Nothing
    where
      program = original{A.programValueBindings = [], A.programDecls =
        [ A.DeclLeaf (A.Leaf seed proposition A.Observed A.User [] Nothing)
        , A.DeclLeaf (A.Leaf otherSeed proposition A.Observed A.User [] Nothing)
        , A.DeclClaim templateClaim{A.claimId = declaration, A.claimFormal = proposition, A.claimNl = "fixed claim"}
        , argument "submitted" seed, argument "other" otherSeed ]}
      policy = (T.sourcePolicy template){A.policySigma = declarePred (Pred "audit-target") []
        (declarePred (Pred "audit-attacker") [] (A.policySigma (T.sourcePolicy template))),
        A.policyAdmission = []}
  [] -> Left "template has no declared claim"
  where
    original = T.sourceProgram template
    argument name leaf = A.DeclArg (A.Arg (A.ArgId name) (A.SupportsClaim declaration) (A.ExplicitTheta (A.SLeaf leaf)))

proposition :: Prop
proposition = Prop (Pred "audit-target") []
seed :: A.LeafId
seed = A.LeafId "audit-seed"
otherSeed :: A.LeafId
otherSeed = A.LeafId "audit-other-seed"
declaration :: A.PropId
declaration = A.PropId "audit-claim"
claim :: D.ClaimBinding
claim = D.ClaimBinding (P.ClaimId 0) declaration proposition
history :: P.ProcessHistory
history = [ P.Stamped (P.EventId 0) (P.CommitPlan (P.ActorId 0) (P.PlanId 0) (P.VersionId 0))
          , P.Stamped (P.EventId 1) (P.Run (P.RunId 0) (P.PlanId 0) (P.VersionId 0) [] (P.FamilyId 0))
          , P.Stamped (P.EventId 2) (P.Result (P.RunId 0) 1)]
ledgerBinding :: D.LedgerBinding
ledgerBinding = D.LedgerBinding (P.RunId 0) (P.FamilyId 0) 1
  (D.Ledger (Just D.PValue) (Just (1 % 100)) (Just 1) (Just P.FWER))
witness :: T.SourceInput -> P.WitnessId -> String -> D.WitnessSpec
witness base ident name = D.WitnessSpec ident (P.ClaimId 0) base
  (D.ArtifactSpec (A.ArgId name) [] (D.DeclaredInterpretation (D.InterpretationId 0)))
  [P.Sampling] (D.LedgerGuarantee ledgerBinding)
config :: T.SourceInput -> D.AuditConfig
config base = D.AuditConfig [claim] [witness base (P.WitnessId 0) "submitted", witness base (P.WitnessId 1) "other"]
  [D.KindSpec base key P.Observed (Just (D.AssumptionId index)) | (index,key) <- zip [0..] keys]
  [D.CaptureAssumption (D.AssumptionId index) base key (last history) (P.RunId 0) P.InstrumentedLog | (index,key) <- zip [0..] keys]
  where keys = [D.LeafKey seed,D.LeafKey otherSeed,D.ArgumentKey (A.ArgId "submitted"),D.ArgumentKey (A.ArgId "other")]
profile :: P.ProfileSpec
profile = P.ProfileSpec [P.Observed] [P.OpenWorldKind,P.CompleteKind,P.CountBoundedKind] P.FWER 1 20 [P.Sampling] P.GroundedJustified
family :: T.SourceInput -> [D.Slot] -> D.FamilySpec
family base slots = D.FamilySpec problem base slots
  where problem = P.Problem (P.DecodedRecord [P.DecodedEvent event (P.SourceRef "test" "event" Nothing) | event <- history] [] [] [] 10) []
checked :: D.FamilySpec -> D.AuditConfig -> (R.CheckedFamily -> Property) -> Property
checked spec metadata check = case E.enumerateFamily spec (D.EnumerationLimits 100 1000 100) of
  Left refusal -> counterexample (show refusal) False
  Right enumerated -> check (R.checkFamily metadata enumerated)

prop_ledgerFailedSibling :: Property
prop_ledgerFailedSibling = conjoin
  [fmap Audit.ledgerCertificateCount (Audit.checkLedger history ledgerBinding) === Right 1,
   Audit.checkLedger (history ++ [P.Stamped (P.EventId 3) (P.Run (P.RunId 1) (P.PlanId 0) (P.VersionId 0) [] (P.FamilyId 0))]) ledgerBinding === Left D.ExceededBound,
   fmap Audit.ledgerCertificateLevel (Audit.checkLedger history ledgerBinding{D.ledger = (D.ledger ledgerBinding){D.ledgerValue = Just (3 % 2),D.ledgerCountBound = Just 2}}) === Right 3,
   fmap Audit.ledgerCertificateLevel (Audit.checkLedger history ledgerBinding{D.ledger = (D.ledger ledgerBinding){D.ledgerKind = Just D.EValue,D.ledgerValue = Just 4,D.ledgerCountBound = Just 2}}) === Right (1 % 2)]
prop_ledgerPrecedence :: Property
prop_ledgerPrecedence = conjoin
  [Audit.checkLedger [] ledgerBinding === Left D.AbsentRun,
   Audit.checkLedger [P.Stamped (P.EventId 0) (P.Run (P.RunId 0) (P.PlanId 0) (P.VersionId 0) [] (P.FamilyId 1))] ledgerBinding === Left D.FamilyMismatch,
   Audit.checkLedger (init history) ledgerBinding === Left D.AbsentResult,
   Audit.checkLedger history ledgerBinding{D.ledger = D.Ledger Nothing Nothing Nothing Nothing} === Left D.MissingKind,
   Audit.checkLedger history ledgerBinding{D.ledger = D.Ledger (Just D.PValue) Nothing Nothing Nothing} === Left D.MissingValue,
   Audit.checkLedger history ledgerBinding{D.ledger = D.Ledger (Just D.PValue) (Just 1) Nothing Nothing} === Left D.MissingGuarantee,
   Audit.checkLedger history ledgerBinding{D.ledger = D.Ledger (Just D.PValue) (Just 1) Nothing (Just P.FDR)} === Left D.UnsupportedGuarantee,
   Audit.checkLedger history ledgerBinding{D.ledger = D.Ledger (Just D.PValue) (Just 1) Nothing (Just P.FWER)} === Left D.MissingBound,
   Audit.checkLedger history ledgerBinding{D.ledger = D.Ledger (Just D.PValue) (Just 1) (Just 0) (Just P.FWER)} === Left D.ZeroBound,
   Audit.checkLedger history ledgerBinding{D.ledger = D.Ledger (Just D.PValue) (Just 0) (Just 1) (Just P.FWER)} === Left D.NonFiniteLevel]
prop_conditionalBounds :: Property
prop_conditionalBounds = conjoin
  [fmap Audit.guaranteeCertificateAttained (Audit.checkGuarantee [] (D.ConditionalGuarantee P.FDR level)) === Right (P.FDR,level) | level <- [0,1,1 % 3]]
  .&&. conjoin [Audit.checkGuarantee [] (D.ConditionalGuarantee P.FWER level) === Left D.InvalidConditionalLevel | level <- [-1,3 % 2]]

prop_submittedIdentity :: Property
prop_submittedIdentity = withBase $ \base ->
  let metadata = config base
      broken spec | D.witnessId spec == P.WitnessId 0 = spec{D.witnessArtifact = (D.witnessArtifact spec){D.artifactDependencies = [D.SupportBinding (A.ArgId "missing") proposition]}}
                  | otherwise = spec
  in checked (family base []) metadata{D.auditWitnesses = map broken (D.auditWitnesses metadata)} $ \result -> conjoin
    [R.audit result profile (P.ClaimId 0) (P.WitnessId 0) === False,
     R.audit result profile (P.ClaimId 0) (P.WitnessId 1) === True,
     R.audit result profile (P.ClaimId 0) (P.WitnessId 999) === False]
prop_metadataComplete :: Property
prop_metadataComplete = withBase $ \base ->
  let metadata = config base
      missing = metadata{D.auditKinds = filter ((/= D.ArgumentKey (A.ArgId "other")) . D.kindKey) (D.auditKinds metadata)}
      duplicate = metadata{D.auditKinds = D.auditKinds metadata ++ take 1 (D.auditKinds metadata)}
  in conjoin
    [checked (family base []) metadata $ \result -> R.audit result profile (P.ClaimId 0) (P.WitnessId 0) === True,
     checked (family base []) missing $ \result -> R.audit result profile (P.ClaimId 0) (P.WitnessId 0) === False,
     checked (family base []) duplicate $ \result -> R.audit result profile (P.ClaimId 0) (P.WitnessId 0) === False]
prop_hypotheticalCapture :: Property
prop_hypotheticalCapture = withBase $ \base ->
  let metadata = config base
      program = T.sourceProgram base
      onlyBase = program{A.programDecls = [decl | decl <- A.programDecls program,case decl of A.DeclArg arg -> A.argId arg /= A.ArgId "other"; _ -> True]}
  in case (T.replaceSourceProgram base onlyBase,T.mkFragment [decl | decl@(A.DeclArg arg) <- A.programDecls program,A.argId arg == A.ArgId "other"]) of
    (Right reduced,Right fragment) ->
      let changed = config reduced
          slots = [D.Slot (D.SlotId 0) [D.Choice (D.ChoiceId 0) D.GuardTruth fragment]]
      in checked (family reduced slots) changed $ \result -> conjoin
        [R.audit result profile (P.ClaimId 0) (P.WitnessId 0) === True,
         R.audit result profile (P.ClaimId 0) (P.WitnessId 1) === False,
         R.audit result profile{P.profileAdmissible = [P.Hypothetical,P.Observed]} (P.ClaimId 0) (P.WitnessId 1) === True]
    other -> counterexample (show other ++ show metadata) False
prop_addedAttacker :: Property
prop_addedAttacker = withBase $ \base ->
  let target = A.AtomPat (Pred "audit-target") []
      opposite = A.AtomPat (Pred "audit-attacker") []
      policy = (T.sourcePolicy base){A.policyContraries = [A.Contrary opposite target]}
      q = Prop (Pred "audit-attacker") []
      attacker = A.ArgId "attacker"
      attackSeed = A.LeafId "attacker-seed"
      declarations = [A.DeclLeaf (A.Leaf attackSeed q A.Observed A.User [] Nothing),
        A.DeclArg (A.Arg attacker (A.SupportsDerived (A.PropId "attacker")) (A.ExplicitTheta (A.SLeaf attackSeed))),
        A.DeclAttack (A.SUndermine attacker (A.ArgId "submitted") []),A.DeclAttack (A.SUndermine attacker (A.ArgId "other") [])]
  in case (T.mkSourceInput (T.sourceProgram base) policy (T.sourceReplay base) Nothing,T.mkFragment declarations) of
    (Right revised,Right fragment) ->
      let metadata = (config revised){D.auditKinds = D.auditKinds (config revised) ++
            [D.KindSpec revised key P.Observed Nothing | key <- [D.LeafKey attackSeed,D.ArgumentKey attacker]]}
          allKinds = profile{P.profileAdmissible = [P.Hypothetical,P.Conditional,P.Supported,P.Observed]}
      in conjoin
        [checked (family revised []) metadata $ \result -> R.audit result allKinds (P.ClaimId 0) (P.WitnessId 0) === True,
         checked (family revised [D.Slot (D.SlotId 0) [D.Choice (D.ChoiceId 0) D.GuardTruth fragment]]) metadata $ \result ->
           R.audit result allKinds (P.ClaimId 0) (P.WitnessId 0) === False]
    other -> counterexample (show other) False

prop_survivingAlternativeTransition :: Property
prop_survivingAlternativeTransition = withBase $ \base ->
  let ruleName = A.RuleId "submitted-only-rule"
      target = A.AtomPat (Pred "audit-target") []
      attackerProp = Prop (Pred "audit-attacker") []
      attacker = A.ArgId "selective-attacker"
      attackerLeaf = A.LeafId "selective-attacker-seed"
      rule = A.Rule ruleName [] A.Defeasible [target] [] target False [] []
      policy = (T.sourcePolicy base)
        { A.policyRules = A.policyRules (T.sourcePolicy base) ++ [rule]
        , A.policyExceptions = A.policyExceptions (T.sourcePolicy base) ++ [A.Exception ruleName (A.AtomPat (Pred "audit-attacker") [])]
        }
      replace (A.DeclArg arg) | A.argId arg == A.ArgId "submitted" =
        A.DeclArg arg{A.argInstantiation = A.ExplicitTheta (A.SRule ruleName [] [A.SLeaf seed] [] [] A.AssuranceNone)}
      replace other = other
      program = (T.sourceProgram base){A.programDecls = map replace (A.programDecls (T.sourceProgram base))}
      additions =
        [A.DeclLeaf (A.Leaf attackerLeaf attackerProp A.Observed A.User [] Nothing),
         A.DeclArg (A.Arg attacker (A.SupportsDerived (A.PropId "selective-attacker")) (A.ExplicitTheta (A.SLeaf attackerLeaf))),
         A.DeclAttack (A.SUndercut attacker (A.ArgId "submitted") [])]
  in case (T.mkSourceInput program policy (T.sourceReplay base) Nothing,T.mkFragment additions) of
    (Right revised,Right fragment) ->
      let original = config revised
          methodKey = D.MethodKey ruleName
          methodAssumption = D.AssumptionId (fromIntegral (length (D.auditAssumptions original)))
          metadata = original
            { D.auditKinds = D.auditKinds original ++
                [D.KindSpec revised methodKey P.Observed (Just methodAssumption)] ++
                [D.KindSpec revised key P.Observed Nothing | key <- [D.LeafKey attackerLeaf,D.ArgumentKey attacker]]
            , D.auditAssumptions = D.auditAssumptions original ++
                [D.CaptureAssumption methodAssumption revised methodKey (last history) (P.RunId 0) P.InstrumentedLog]
            }
          allKinds = profile{P.profileAdmissible = [P.Hypothetical,P.Conditional,P.Supported,P.Observed]}
          methodWitness = (witness revised (P.WitnessId 0) "submitted")
            {D.witnessArtifact = D.ArtifactSpec (A.ArgId "submitted") []
              (D.CheckedMethod (D.MethodBinding D.Two D.AppliedPayload 0 False True []))}
          inspectRows result check = case R.checkedRows result of
            [row] -> case (R.rowView row,R.snapshotOutcome (R.rowSnapshot row)) of
              (Right view,Right observation) -> conjoin
                [R.preparedComplete view === True,
                 map D.queryStatus (R.preparedQueries view) === [Published A.Justified],
                 S.publicStatus observation proposition === Published A.Justified,
                 check observation]
              _ -> counterexample "selective attack source was rejected" False
            _ -> counterexample "expected exactly one fixed history row" False
      in conjoin
        [checked (family revised []) metadata $ \before -> conjoin
          [R.audit before allKinds (P.ClaimId 0) (P.WitnessId 0) === True,
           inspectRows before $ \observation ->
             property (not (isLeft (Audit.observeWitness revised observation history claim methodWitness)))],
         checked (family revised [D.Slot (D.SlotId 0) [D.Choice (D.ChoiceId 0) D.GuardTruth fragment]]) metadata $ \after -> conjoin
          [R.audit after allKinds (P.ClaimId 0) (P.WitnessId 0) === False,
           R.audit after allKinds (P.ClaimId 0) (P.WitnessId 1) === True,
           map snd (Analysis.auditObservations after (P.ClaimId 0) (P.WitnessId 0) allKinds) === [Right False],
           map snd (Analysis.auditObservations after (P.ClaimId 0) (P.WitnessId 1) allKinds) === [Right True],
           inspectRows after $ \observation ->
             Audit.observeWitness revised observation history claim methodWitness
               === Left (D.WitnessArtifact (D.ArtifactMethod D.DefeatedSupport))]]
    other -> counterexample (show other) False
prop_supportAndSourcePrecedence :: Property
prop_supportAndSourcePrecedence = withBase $ \base -> case S.checkSource base of
  Left rejection -> counterexample (show rejection) False
  Right observation ->
    let spec = witness base (P.WitnessId 0) "submitted"
        absent = spec{D.witnessArtifact = (D.witnessArtifact spec){D.artifactArgument = A.ArgId "absent"}}
        wrong = spec{D.witnessClaim = P.ClaimId 1}
    in conjoin
      [property (isLeft (Audit.resolveSupport observation (D.SupportBinding (A.ArgId "absent") proposition))),
       S.observationNodeLabel observation (10^(100 :: Int)) === Nothing,
       S.observationNodeLabel observation 0 === Just A.LIn,
       Audit.observeWitness base observation history claim absent === Left (D.WitnessArtifact (D.ArtifactSupport (A.ArgId "absent") D.SupportAbsent)),
       Audit.observeWitness base observation history claim wrong === Left D.WrongClaim,
       case T.mkFragment [] of
         Left err -> counterexample err False
         Right fragment -> case T.replaceSourceProgram base (T.sourceProgram base){A.programArtifact = "stale"} of
           Left err -> counterexample err False
           Right stale -> Audit.observeWitness (T.appendFragment base fragment) observation history claim wrong{D.witnessSource = stale} === Left D.StaleSource]

prop_familyRowsRetained :: Property
prop_familyRowsRetained = withBase $ \base -> case T.mkFragment [A.DeclArg (A.Arg (A.ArgId "submitted") (A.SupportsClaim declaration) (A.ExplicitTheta (A.SLeaf seed)))] of
  Left err -> counterexample err False
  Right bad -> conjoin
    [checked (family base []) (config base) $ \clean -> conjoin
      [R.audit clean profile (P.ClaimId 0) (P.WitnessId 0) === True,
       length (R.checkedRows clean) === 1],
     checked (family base [D.Slot (D.SlotId 0) [D.Choice (D.ChoiceId 0) D.GuardTruth bad]]) (config base) $ \result -> conjoin
      [map (either Just (const Nothing) . R.rowView) (R.checkedRows result) ===
        [Just (Diagnostic.SourceRejection (Diagnostic.SourceDiagnostic
          (Diagnostic.Structural (Diagnostic.DuplicateArgumentId (A.ArgId "submitted")))))],
       R.audit result profile (P.ClaimId 0) (P.WitnessId 0) === False]]

prop_methodPayload :: Property
prop_methodPayload = withBase $ \base -> case S.checkSource base of
  Left rejection -> counterexample (show rejection) False
  Right observation -> conjoin
    [ let spec mode parameter = (witness base (P.WitnessId 0) "submitted")
            {D.witnessArtifact = D.ArtifactSpec (A.ArgId "submitted") []
              (D.CheckedMethod (D.MethodBinding method mode parameter first second [D.RuntimeRefinement]))}
          observed mode parameter = Audit.observeWitness base observation history claim (spec mode parameter)
      in conjoin
        [property (not (isLeft (observed D.ConditionalPayload (10^(100 :: Int))))),
         if method == D.ConditionalFalse
           then observed D.AppliedPayload 0 === Left (D.WitnessArtifact (D.ArtifactMethod D.FalsePrecondition))
           else property (not (isLeft (observed D.AppliedPayload 0))),
         observed D.AppliedPayload (10^(100 :: Int)) === Left (D.WitnessArtifact (D.ArtifactMethod D.FalsePrecondition))]
    | method <- [minBound..maxBound], first <- [False,True], second <- [False,True]]

prop_authoredAssociation :: Property
prop_authoredAssociation = withBase $ \base ->
  let replace (A.DeclArg arg) | A.argId arg == A.ArgId "submitted" =
        A.DeclArg arg{A.argConcl = A.SupportsDerived (A.PropId "different-authored-claim")}
      replace other = other
      program = (T.sourceProgram base){A.programDecls = map replace (A.programDecls (T.sourceProgram base))}
  in case T.replaceSourceProgram base program of
    Left err -> counterexample err False
    Right changed -> case S.checkSource changed of
      Left rejection -> counterexample (show rejection) False
      Right observation -> Audit.observeWitness changed observation history claim (witness changed (P.WitnessId 0) "submitted")
        === Left (D.WitnessArtifact (D.ArtifactAssociation D.AssociationWrongArgument))

prop_baseFixedClaims :: Property
prop_baseFixedClaims = withBase $ \base ->
  let program = T.sourceProgram base
      claims = [decl | decl@A.DeclClaim{} <- A.programDecls program]
      stripped = program{A.programDecls = [decl | decl <- A.programDecls program,case decl of A.DeclClaim _ -> False; _ -> True]}
  in case (T.replaceSourceProgram base stripped,T.mkFragment claims) of
    (Right changed,Right fragment) ->
      checked (family changed [D.Slot (D.SlotId 0) [D.Choice (D.ChoiceId 0) D.GuardTruth fragment]]) (config changed) $ \result ->
        conjoin [property (all (not . isLeft . R.rowView) (R.checkedRows result)),
          R.audit result profile (P.ClaimId 0) (P.WitnessId 0) === False]
    other -> counterexample (show other) False

prop_profileRequirements :: Property
prop_profileRequirements = withBase $ \base -> checked (family base []) (config base) $ \result -> conjoin
  [R.audit result profile (P.ClaimId 0) (P.WitnessId 0) === True,
   R.audit result profile{P.profileGuarantee = P.FDR} (P.ClaimId 0) (P.WitnessId 0) === False,
   R.audit result profile{P.profileNum = 1,P.profileDen = 1000} (P.ClaimId 0) (P.WitnessId 0) === False,
   R.audit result profile{P.profileProbes = [P.Sampling,P.Measurement]} (P.ClaimId 0) (P.WitnessId 0) === False,
   R.audit result profile{P.profileAccepts = [P.CompleteKind]} (P.ClaimId 0) (P.WitnessId 0) === False]

prop_ambiguousMetadataFailure :: Property
prop_ambiguousMetadataFailure = withBase $ \base ->
  case S.checkSource base of
    Left rejection -> counterexample (show rejection) False
    Right observation ->
      let baseConfig = config base
          dupWitnesses = [witness base (P.WitnessId 0) "submitted", witness base (P.WitnessId 0) "other"]
          ambiguousConfig = baseConfig{D.auditWitnesses = dupWitnesses}
          metadata = Audit.auditMetadata base ambiguousConfig
          checkedResults = Audit.checkWitnesses metadata observation history
          observedResults = Audit.observeWitnesses ambiguousConfig base observation history
      in conjoin
        [ Audit.metadataWellFormed metadata === False,
          map (\(w, r) -> (w, either Left (const (Right ())) r)) checkedResults === [(P.WitnessId 0, Left D.AmbiguousMetadata), (P.WitnessId 0, Left D.AmbiguousMetadata)],
          observedResults === [(P.WitnessId 0, Left D.AmbiguousMetadata), (P.WitnessId 0, Left D.AmbiguousMetadata)] ]
auditRuntimeSpecProps :: [(String,IO Result)]
auditRuntimeSpecProps = [(name,quickCheckResult prop) | (name,prop) <-
  [("audit ledger counts failed/no-result siblings and keeps unclamped exact levels",prop_ledgerFailedSibling),
   ("audit ledger preserves failure precedence",prop_ledgerPrecedence),
   ("audit conditional levels have exact closed interval",prop_conditionalBounds),
   ("audit different valid witness cannot rescue submitted identity",prop_submittedIdentity),
   ("audit unrelated missing kinds and duplicate metadata fail completeness",prop_metadataComplete),
   ("audit hypothetical fragment cannot infer observed capture",prop_hypotheticalCapture),
   ("audit added attacker defeats previously warranted submitted argument",prop_addedAttacker),
   ("audit surviving same-query alternative cannot rescue defeated submitted node across transition",prop_survivingAlternativeTransition),
   ("audit source pin and selected support failures precede guarantee",prop_supportAndSourcePrecedence),
   ("audit rejected source completion remains visible",prop_familyRowsRetained),
   ("audit checked methods distinguish conditional interpretation from actual applicability",prop_methodPayload),
   ("audit authored claim association is not inferred from matching conclusion",prop_authoredAssociation),
   ("audit fragment-only claim cannot alter base-fixed binding",prop_baseFixedClaims),
   ("audit profile enforces coverage, guarantee class and level, and probes",prop_profileRequirements),
   ("audit duplicate conflicting witness IDs fail closed with Left AmbiguousMetadata",prop_ambiguousMetadataFailure)]]
