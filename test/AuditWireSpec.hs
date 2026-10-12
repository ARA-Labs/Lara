module AuditWireSpec (auditWireSpecProps) where

import Data.Either (isLeft)
import Data.Ratio ((%))
import Test.QuickCheck
import qualified Lara.AST as A
import Lara.Prop (Prop (..), Pred (..), Term (..))
import Lara.Strict (SExpr (..))
import Lara.Wire (parseSExpr)
import qualified Lara.Process.Types as P
import qualified Lara.Process.Wire as W
import qualified Lara.Process.Source.Types as S
import qualified Lara.Process.Source.Wire as SW
import qualified Lara.Process.Source.CoreDiagnostic as C
import Lara.Process.Audit.Types
import qualified Lara.Process.AuditWire as AW

names :: W.Names
names = W.Names ["ev","later"] ["actor"] ["plan"] ["run"] ["claim"] ["source"] ["data"] ["family"] ["witness"]
event :: P.Stamped
event = P.Stamped (P.EventId 0) (P.Result (P.RunId 0) 999999999999999999999999999)
query :: Prop
query = Prop (Pred "nonfixture") [TNum "-0001.50",TStr "signed"]
roundtrip :: (Eq a,Show a) => (a -> SExpr) -> (SExpr -> Either W.Error a) -> [a] -> Property
roundtrip encode decode values = conjoin [counterexample (show wire) (decode wire === Right value) | value <- values,let wire = encode value]

prop_primitives :: Integer -> Integer -> Property
prop_primitives numerator denominator =
  let natural = fromInteger (abs numerator)
      rational = numerator % (abs denominator + 1)
  in conjoin
    [roundtrip AW.encodeInt AW.decodeInt [numerator],roundtrip AW.encodeRat AW.decodeRat [rational],
     roundtrip AW.encodeAssumptionId AW.decodeAssumptionId [AssumptionId natural],
     roundtrip AW.encodeInterpretationId AW.decodeInterpretationId [InterpretationId natural],
     roundtrip AW.encodeSlotId AW.decodeSlotId [SlotId natural],
     roundtrip AW.encodeChoiceId AW.decodeChoiceId [ChoiceId natural]]

prop_methods :: Property
prop_methods = conjoin
  [roundtrip AW.encodeMethod AW.decodeMethod [minBound .. maxBound],
   roundtrip AW.encodePayloadMode AW.decodePayloadMode [minBound .. maxBound],
   roundtrip AW.encodeResidualAssumption AW.decodeResidualAssumption [minBound .. maxBound],
   roundtrip AW.encodeStatKind AW.decodeStatKind [minBound .. maxBound],
   roundtrip AW.encodeMethodBinding AW.decodeMethodBinding
     [MethodBinding method mode parameter first second [RuntimeRefinement,PhysicalSampling,RuntimeRefinement]
     | method <- [minBound .. maxBound],mode <- [minBound .. maxBound],
       parameter <- [-999999999999999999999999999999,0,999999999999999999999999999999],first <- [False,True],second <- [False,True]]]

prop_frozenSpellings :: Property
prop_frozenSpellings = conjoin
  [map AW.encodeMethod [minBound .. maxBound] === map (\tag -> W.tagged tag [])
     ["two","low","up","disjunction","conjunction","conditional-false"],
   map AW.encodePayloadMode [minBound .. maxBound] === [W.tagged "conditional" [],W.tagged "applied" []],
   map AW.encodeResidualAssumption [minBound .. maxBound] === map (\tag -> W.tagged tag [])
     ["interpretation-fidelity","physical-sampling","capture-adequacy","runtime-refinement"],
   map AW.encodeStatKind [minBound .. maxBound] === [W.tagged "p-value" [],W.tagged "e-value" []],
   AW.encodeInt (-2) === W.tagged "integer-negative-successor" [SAtom "1"],
   AW.encodeRat ((-3)%2) === W.tagged "rational" [W.tagged "integer-negative-successor" [SAtom "2"],SAtom "2"],
   AW.encodeOption AW.encodeInt Nothing === W.tagged "none" [],
   AW.encodeOption AW.encodeInt (Just 0) === W.tagged "some" [W.tagged "integer-natural" [SAtom "0"]],
   AW.decodeOption AW.decodeInt (W.tagged "none" []) === Right Nothing,
   AW.decodeOption AW.decodeInt (W.tagged "some" [AW.encodeInt (-999999999999999999999999)]) === Right (Just (-999999999999999999999999)),
   AW.encodeBool True === SAtom "true",AW.encodeBool False === SAtom "false",
   roundtrip AW.encodeAssumptionId AW.decodeAssumptionId [AssumptionId 999999999999999999999999999999],
   AW.decodeClaimBinding (names{W.namesClaim = ["claim","claim"]}) (W.tagged "claim-binding" [SAtom "claim",SAtom "decl",frozenAtom]) ===
     Right (ClaimBinding (P.ClaimId 0) (A.PropId "decl") (Prop (Pred "q") []))]
  where frozenAtom = W.tagged "atom" [SAtom "q"]

supportFaults :: [SupportFault]
supportFaults = [SupportAbsent,SupportDifferentConclusion,SupportNotRetained,SupportAbsentNode,SupportNodeMismatch,SupportBlocked,
  SupportInference (C.CheckR1 C.CoreRoot (C.ReferenceMissingLeaf (A.LeafId "missing"))),
  SupportIncomplete [A.QuestionId "q",A.QuestionId "q",A.QuestionId "other"]]
bridgeErrors :: [BridgeError]
bridgeErrors = [StaleSnapshot,IncompatibleInterpretation,IncompatibleMethod,IncompatibleClaim,IncompatibleDependencies,
  IncompatibleEvidence,IncompatibleBinding,MissingSupport,BlockedSupport,DefeatedSupport,FailedDerivation,FalsePrecondition]
  ++ map BridgeApplication [minBound .. maxBound]
artifactFaults :: [ArtifactFault]
artifactFaults = map (ArtifactSupport (A.ArgId "arg")) supportFaults ++ map ArtifactAssociation [minBound .. maxBound] ++ map ArtifactMethod bridgeErrors
guaranteeFaults :: [GuaranteeFault]
guaranteeFaults = InvalidConditionalLevel : map GuaranteeLedger [minBound .. maxBound]
prop_faults :: Property
prop_faults = conjoin
  [roundtrip AW.encodeAssociationFault AW.decodeAssociationFault [minBound .. maxBound],
   roundtrip AW.encodeApplicationError AW.decodeApplicationError [minBound .. maxBound],
   roundtrip AW.encodeLedgerFault AW.decodeLedgerFault [minBound .. maxBound],
   roundtrip AW.encodeSupportFault AW.decodeSupportFault supportFaults,
   roundtrip AW.encodeBridgeError AW.decodeBridgeError bridgeErrors,
   roundtrip AW.encodeArtifactFault AW.decodeArtifactFault artifactFaults,
   roundtrip AW.encodeGuaranteeFault AW.decodeGuaranteeFault guaranteeFaults,
   roundtrip AW.encodeWitnessFault AW.decodeWitnessFault
     ([MissingClaim,MissingWitness,AmbiguousMetadata,WrongClaim,StaleSource] ++ map WitnessArtifact artifactFaults ++ map WitnessGuarantee guaranteeFaults),
   roundtrip AW.encodeProvenanceError AW.decodeProvenanceError
     [ProvenanceShape,ProvenanceImplicitMatch,ProvenanceMissingRule (A.RuleId "r"),ProvenanceUnresolvedReference (A.ArgRef "ref"),
      ProvenanceMissingArgument (A.ArgId "arg"),ProvenanceDuplicateArgument (A.ArgId "arg"),ProvenanceMissingNode 999999999999999999999999999]]

withSource :: (S.SourceInput -> Property) -> Property
withSource check = once $ ioProperty $ do
  text <- readFile "fixtures/process/inquiry/forged-observed.sexp"
  pure $ case parseSExpr text of
    Right (SList (_ : _ : _ : source : _)) -> either (\err -> counterexample (show err) False) check (SW.decodeSource source)
    other -> counterexample (show other) False
prop_metadata :: Property
prop_metadata = withSource $ \source ->
  let keys = [LeafKey (A.LeafId "leaf"),MethodKey (A.RuleId "method"),ArgumentKey (A.ArgId "arg")]
      claims = [ClaimBinding (P.ClaimId 0) (A.PropId "declaration") query]
      supports = [SupportBinding (A.ArgId "a") query,SupportBinding (A.ArgId "a") query]
      interpretations = [DeclaredInterpretation (InterpretationId 999999999999999999999999),
        CheckedMethod (MethodBinding ConditionalFalse AppliedPayload (-99999999999999999999999) False True [CaptureAdequacy,CaptureAdequacy])]
      artifacts = [ArtifactSpec (A.ArgId "a") supports interpretation | interpretation <- interpretations]
      ledgers = [Ledger kind value bound guarantee | kind <- [Nothing,Just PValue,Just EValue],
        value <- [Nothing,Just ((-3)%2),Just 0,Just (17%3)],bound <- [Nothing,Just 0,Just 999999999999999999999999],
        guarantee <- [Nothing,Just P.FWER,Just P.FDR,Just P.MFDR]]
      ledgerBindings = [LedgerBinding (P.RunId 0) (P.FamilyId 0) 999999999999999999999999 ledger' | ledger' <- ledgers]
      guarantees = [ConditionalGuarantee g q | g <- [P.FWER,P.FDR,P.MFDR],q <- [(-3)%2,0,17%3]] ++ map LedgerGuarantee ledgerBindings
      witnesses = [WitnessSpec (P.WitnessId 0) (P.ClaimId 0) source artifact [P.Sampling,P.Sampling] guarantee | artifact <- artifacts,guarantee <- guarantees]
      kinds = [KindSpec source key upper assumption | key <- keys,upper <- [P.Hypothetical,P.Conditional,P.Supported,P.Observed],assumption <- [Nothing,Just (AssumptionId 0)]]
      captures = [CaptureAssumption (AssumptionId 0) source key event (P.RunId 0) basis | key <- keys,basis <- [P.InstrumentedLog,P.SignedAttestation,P.AuthorDeclaration]]
      config = AuditConfig (claims ++ claims) (witnesses ++ take 1 witnesses) (kinds ++ kinds) (captures ++ captures)
  in conjoin
    [roundtrip AW.encodeKindKey AW.decodeKindKey keys,roundtrip AW.encodeSupportBinding AW.decodeSupportBinding supports,
     roundtrip AW.encodeArtifactInterpretation AW.decodeArtifactInterpretation interpretations,roundtrip AW.encodeArtifactSpec AW.decodeArtifactSpec artifacts,
     roundtrip AW.encodeLedger AW.decodeLedger ledgers,roundtrip (AW.encodeLedgerBinding names) (AW.decodeLedgerBinding names) ledgerBindings,
     roundtrip (AW.encodeClaimBinding names) (AW.decodeClaimBinding names) claims,
     roundtrip (AW.encodeGuaranteeBinding names) (AW.decodeGuaranteeBinding names) guarantees,
     roundtrip (AW.encodeWitnessSpec names) (AW.decodeWitnessSpec names) witnesses,
     roundtrip AW.encodeKindSpec AW.decodeKindSpec kinds,roundtrip (AW.encodeCaptureAssumption names) (AW.decodeCaptureAssumption names) captures,
     roundtrip (AW.encodeConfig names) (AW.decodeConfig names) [config]]

prop_family :: Property
prop_family = case S.mkFragment [] of
  Left err -> counterexample err False
  Right fragment ->
    let guards = [GuardTruth,GuardQuery (P.QueryNot (P.QueryAtom P.Predictable)),GuardPresent event,GuardBefore event event,
          GuardNot GuardTruth,GuardAnd GuardTruth (GuardPresent event),GuardOr (GuardNot GuardTruth) (GuardPresent event)]
        choices = [Choice (ChoiceId 999999999999999999999999999) guard fragment | guard <- guards]
        slots = [Slot (SlotId 999999999999999999999999999) (choices ++ choices),Slot (SlotId 0) []]
        selections = [Selection (SlotId 0) choice | choice <- choices]
        completion = Completion [event,event] (selections ++ selections)
    in conjoin [roundtrip (AW.encodeGuard names) (AW.decodeGuard names) guards,
      roundtrip (AW.encodeChoice names) (AW.decodeChoice names) choices,roundtrip (AW.encodeSlot names) (AW.decodeSlot names) slots,
      roundtrip (AW.encodeSelection names) (AW.decodeSelection names) selections,
      roundtrip (AW.encodeCompletion names) (AW.decodeCompletion names) [completion],
      roundtrip AW.encodeAssignment AW.decodeAssignment [[(SlotId 0,ChoiceId 1),(SlotId 0,ChoiceId 1)]]]

prop_errors :: Property
prop_errors = conjoin
  [property (isLeft (AW.decodeRat (W.tagged "rational" [AW.encodeInt 2,W.encodeNat 4]))),
   property (isLeft (AW.decodeRat (W.tagged "rational" [AW.encodeInt 1,W.encodeNat 0]))),
   property (isLeft (AW.decodeInt (W.tagged "integer-natural" [SAtom "01"]))),
   property (isLeft (AW.decodeMethod (SAtom "two"))),
   property (isLeft (AW.decodeMethod (W.tagged "two" [SAtom "extra"]))),
   property (isLeft (AW.decodeSlotId (W.tagged "slot-id" [SAtom "-1"]))),
   property (isLeft (AW.decodeGuard names (W.tagged "before" [SAtom "bad",SAtom "bad"]))),
   property (isLeft (AW.decodeOption AW.decodeInt (W.tagged "some" []))),
   property (isLeft (AW.decodeOption AW.decodeInt (W.tagged "none" [AW.encodeInt 0]))),
   property (isLeft (AW.decodeBool (W.tagged "true" []))),
   property (isLeft (AW.decodeSupportFault (W.tagged "inference" [SAtom "missing-diagnostic"]))),
   property (isLeft (AW.decodeSupportFault (W.tagged "incomplete" [SAtom "q"]))),
   property (isLeft (AW.decodeBridgeError (W.tagged "application" [W.tagged "not-an-error" []]))),
   property (isLeft (AW.decodeArtifactFault (W.tagged "association" [W.tagged "input-claim" [SAtom "extra"]]))),
   property (isLeft (AW.decodeGuaranteeFault (W.tagged "ledger" [W.tagged "absent-run" [SAtom "extra"]]))),
   property (isLeft (AW.decodeWitnessFault (W.tagged "artifact" [W.tagged "method" []]))),
   property (isLeft (AW.decodeProvenanceError (W.tagged "missing-node" [SAtom "01"]))),
   property (isLeft (AW.decodeKindKey (W.tagged "leaf" [SList []]))),
   property (isLeft (AW.decodeMethodBinding (W.tagged "method-binding"
     [W.tagged "two" [],W.tagged "conditional" [],AW.encodeInt 0,SAtom "true",SAtom "false",SAtom "runtime-refinement"]))),
   property (isLeft (AW.decodeLedger (W.tagged "ledger-fields"
     [W.tagged "none" [],W.tagged "some" [W.tagged "rational" [AW.encodeInt 0,SAtom "2"]],W.tagged "none" [],W.tagged "none" []]))),
   property (isLeft (AW.decodeAssignment (SList [SList [AW.encodeSlotId (SlotId 0)]]))),
   AW.decodeClaimBinding names (W.tagged "claim-binding" [SAtom "undeclared",SList [],SList []]) ===
     Left (W.Error W.Malformed "undeclared claim name undeclared"),
   AW.decodeSlot names (W.tagged "slot" [W.tagged "slot-id" [SAtom "01"],SList [SAtom "bad"]]) ===
     Left (W.Error W.Malformed "non-canonical number 01"),
   AW.decodeConfig names (W.tagged "audit-config" [SList [W.tagged "claim-binding" [SAtom "undeclared",SList [],SList []]],SList [],SList [],SList []]) ===
     Left (W.Error W.Malformed "undeclared claim name undeclared"),
   W.decodeRef (W.tagged "at" [SAtom "file",SAtom "entry",W.encodeNat 99999999999999999999999,W.encodeNat 2]) ===
     Right (P.SourceRef "file" "entry" (Just (99999999999999999999999,2)))]

subtrees :: String -> SExpr -> [SExpr]
subtrees tag tree@(SList (SAtom actual : xs)) = [tree | tag == actual] ++ concatMap (subtrees tag) xs
subtrees tag (SList xs) = concatMap (subtrees tag) xs
subtrees _ _ = []
fixtureCodec :: String -> Property
fixtureCodec name = once $ ioProperty $ do
  text <- readFile ("fixtures/process/inquiry/" ++ name ++ ".sexp")
  pure $ case parseSExpr text of
    Left err -> counterexample (show err) False
    Right tree -> case subtrees "names" tree of
      namesTree : _ -> case W.decodeNames namesTree of
        Left err -> counterexample (show err) False
        Right ns ->
          let exercise tag encode decode = conjoin [case decode wire of
                Left err -> counterexample (tag ++ ": " ++ show err) False
                Right value -> encode value === wire | wire <- subtrees tag tree]
          in conjoin [exercise "claim-binding" (AW.encodeClaimBinding ns) (AW.decodeClaimBinding ns),
            exercise "witness-spec" (AW.encodeWitnessSpec ns) (AW.decodeWitnessSpec ns),
            exercise "kind-spec" AW.encodeKindSpec AW.decodeKindSpec,
            exercise "capture-assumption" (AW.encodeCaptureAssumption ns) (AW.decodeCaptureAssumption ns),
            exercise "slot" (AW.encodeSlot ns) (AW.decodeSlot ns),
            exercise "method-binding" AW.encodeMethodBinding AW.decodeMethodBinding,
            exercise "ledger-binding" (AW.encodeLedgerBinding ns) (AW.decodeLedgerBinding ns)]
      [] -> counterexample "missing names subtree" False

auditWireSpecProps :: [(String,IO Result)]
auditWireSpecProps = map (\(description,test) -> (description,quickCheckResult test)) $
  [("audit wire unbounded signed primitives",property prop_primitives),
   ("audit wire frozen constructor spellings and first name lookup",prop_frozenSpellings),
   ("audit wire all method constructors and unconstrained inputs",prop_methods),
   ("audit wire all fault constructors",prop_faults),
   ("audit wire semantic duplicates and invalid levels remain metadata",prop_metadata),
   ("family wire all constructors and ordered duplicate assignments",prop_family),
   ("audit wire strict framing and left-to-right error precedence",prop_errors)]
  ++ [("audit wire actual inquiry subtrees " ++ name,fixtureCodec name) | name <-
    ["fixed-witness","forged-observed","hypothetical-audit","ledger-sibling","fixed-query","profile-reinstatement",
     "shared-discharge","reference-sensitivity","verified-certificate","p0-guard","normalized-support","minimal-conditions"]]
