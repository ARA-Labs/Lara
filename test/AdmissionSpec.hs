-- | Source-boundary policy-admission conformance tests.
--
-- These properties deliberately exercise only the @.lara@ boundary.  The raw
-- @CheckInput@ / @runCheck@ interface remains frozen and is covered elsewhere.
-- In particular, the tests observe the opaque source carrier through verdict
-- and audit projections rather than constructing an admitted/pruned pair by
-- hand.
module AdmissionSpec (admissionSpecProps) where

import Data.List.NonEmpty (NonEmpty (..))
import Test.QuickCheck

import Lara.AST hiding (Reject)
import qualified Lara.AST as AST
import Lara.Admission
  ( AdmissionAudit
  , AdmissionCause (..)
  , admissionAuditArgs
  , admissionAuditAttacks
  , admissionAuditLeaves
  , admissionRejectionKind
  , admissionRejectionLeaf
  , admissionRejectionMatchedRow
  , admissionRejectionProvenance
  , decisionFor
  , renderAdmissionAudit
  , renderAdmissionRejection
  , validateAdmissionKeys
  )
import Lara.Elaborate
  ( PreparedSource (..)
  , SourceCheckInput
  , SourceInvalid (..)
  , prepareSource
  , renderSourceInvalid
  , runSourceCheck
  , sourceResultAudit
  , sourceResultCheckInput
  , sourceResultVerdict
  )
import Lara.Driver (runCheck)
import Lara.ExpectedJson (JValue (..), sourceResultJsonValue)
import Lara.Negatives (Negative (..), admissionReject)
import Lara.Prop (Prop (..))
import Lara.Wire (Outcome (..), PublicStatus (..), Verdict (..), encodeVerdict, printSExpr)
import SigmaFixture (sigmaOf)

-- ---------------------------------------------------------------------------
-- Compact source fixtures
-- ---------------------------------------------------------------------------

atom0 :: String -> Prop
atom0 p = Prop (Pred p) []

apat0 :: String -> AtomPat
apat0 p = AtomPat (Pred p) []

leafD :: String -> String -> LeafKind -> Provenance -> Decl
leafD lid p k provenance =
  DeclLeaf (Leaf (LeafId lid) (atom0 p) k provenance [])

claimD :: String -> String -> Decl
claimD cid p =
  DeclClaim
    ( Claim
        (PropId cid)
        cid
        (atom0 p)
        (Binding "test" "admission conformance" Reviewed)
    )

argLeaf :: String -> String -> Decl
argLeaf aid lid =
  DeclArg
    ( Arg
        { argId = ArgId aid
        , argConcl = SupportsDerived (PropId ("derived_" ++ aid))
        , argInstantiation = ExplicitTheta (SLeaf (LeafId lid))
        }
    )

argClaim :: String -> String -> String -> Decl
argClaim aid cid lid =
  DeclArg
    ( Arg
        { argId = ArgId aid
        , argConcl = SupportsClaim (PropId cid)
        , argInstantiation = ExplicitTheta (SLeaf (LeafId lid))
        }
    )

program :: [(BackendId, String)] -> [Decl] -> Program
program backends decls =
  Program
    { programArtifact = "admission-test"
    , programDigest = Digest "sha256:admission-test"
    , programPolicy = PolicyId "p"
    , programBackends = backends
    , programValueBindings = []
    , programDecls = decls
    }

-- | The authored spelling of a resolved attack (grammar §7, App. B.5): each
-- 'Step' has exactly one 'SurfaceStep' form, so this is the identity these
-- fixtures need to state expectations in terms of the frozen 'Attack' while
-- still building 'DeclAttack's.
surfaceAttack :: Attack -> SurfaceAttack
surfaceAttack k = case k of
  Rebut w u -> SRebut w u
  Undercut w u pos -> SUndercut w u (map surfaceStep pos)
  Undermine w u pos -> SUndermine w u (map surfaceStep pos)
  where
    surfaceStep (StepPremise i) = StepIndex i
    surfaceStep (StepQuestion (QuestionId q)) = StepName q

policy :: [((LeafKind, Provenance), Admission)] -> GroupConflictMode -> Policy
policy admission groupMode =
  Policy
    { policyId = PolicyId "p"
    , policySigma =
        -- One authored fixture signature over this file's whole nullary-atom
        -- vocabulary (@lara-core\@0.2@, D8): every admission fixture is
        -- propositional, so no sort or constructor is needed.
        sigmaOf
          []
          []
          [ (h, [])
          | h <-
              [ "attacker", "discharged", "nested", "not_p", "one", "other"
              , "p", "q", "r", "removed", "s", "target", "two"
              ]
          ]
    , policyRules = []
    , policyContraries = []
    , policyExceptions = []
    , policyAdmission = admission
    , policyTheories = []
    , policyGroupMode = groupMode
    , policyMeasurands = []
    , policyComparisonSchemes = []
    }

accepted :: Program -> Policy -> (SourceCheckInput -> Property) -> Property
accepted prog pol k =
  case prepareSource prog pol of
    Left invalid -> counterexample ("unexpected source invalidity: " ++ show invalid) False
    Right (SourceRejected rejection) ->
      counterexample ("unexpected R8: " ++ renderAdmissionRejection rejection) False
    Right (SourceAccepted input) -> k input

-- | Omitted, empty, and unmatched tables all implement the total default-admit
-- function.  The explicit row is included to ensure lookup is exact rather
-- than a kind-only or provenance-only wildcard.
prop_totalDefaultAdmit :: Property
prop_totalDefaultAdmit =
  conjoin
    [ decisionFor [] Observed User === Admit
    , decisionFor [((Attested, User), AST.Reject)] Observed User === Admit
    , decisionFor [((Observed, AiExecuted), Quarantine)] Observed User === Admit
    ]

-- | An exact @admit@ row is semantically transparent: both arguments and their
-- attack survive, and no audit material is invented.
prop_explicitAdmitPreservesGraph :: Property
prop_explicitAdmitPreservesGraph =
  accepted prog pol $ \input ->
    let result = runSourceCheck input
     in conjoin
          [ sourceResultAudit result `auditLeaves` []
          , admissionAuditArgs (sourceResultAudit result) === []
          , admissionAuditAttacks (sourceResultAudit result) === []
          , case verdictOutcome (sourceResultVerdict result) of
              Reject rejection -> counterexample ("unexpected core reject: " ++ show rejection) False
              Accept labels edges statuses ->
                conjoin
                  [ labels === [(0, LOut), (1, LIn)]
                  , edges === [(1, 0)]
                  , statuses === [(atom0 "p", Published Defeated)]
                  ]
          ]
  where
    prog =
      program
        []
        [ claimD "c" "p"
        , leafD "e_p" "p" Observed User
        , leafD "e_not_p" "not_p" Attested User
        , argClaim "a_p" "c" "e_p"
        , argLeaf "a_not_p" "e_not_p"
        , DeclAttack (SUndermine (ArgId "a_not_p") (ArgId "a_p") [])
        , DeclStatus (PropId "c")
        ]
    pol =
      (policy [((Observed, User), Admit)] QuarantineOnConflict)
        { policyContraries = [Contrary (apat0 "not_p") (apat0 "p")]
        }


-- | The real source carrier/checker seam is observationally identical to the
-- frozen raw checker when every declared leaf is admitted. This compares both
-- the structured verdict and its exact wire encoding; it does not rely on the
-- test-only Haskell/Lean admission adapter.
prop_allAdmitSourceVerdictIdentity :: Property
prop_allAdmitSourceVerdictIdentity =
  accepted prog pol $ \input ->
    let sourceResult = runSourceCheck input
     in case sourceResultCheckInput sourceResult of
          Left audit ->
            counterexample
              ("all-admit source unexpectedly retained an admission audit: " ++ renderAdmissionAudit audit)
              False
          Right legacyInput ->
            let sourceVerdict = sourceResultVerdict sourceResult
                legacyVerdict = runCheck legacyInput
             in conjoin
                  [ sourceVerdict === legacyVerdict
                  , printSExpr (encodeVerdict sourceVerdict)
                      === printSExpr (encodeVerdict legacyVerdict)
                  , admissionAuditLeaves (sourceResultAudit sourceResult) === []
                  , admissionAuditArgs (sourceResultAudit sourceResult) === []
                  , admissionAuditAttacks (sourceResultAudit sourceResult) === []
                  ]
  where
    prog =
      program
        []
        [ claimD "c" "p"
        , leafD "e" "p" Observed User
        , argClaim "a" "c" "e"
        , DeclStatus (PropId "c")
        ]
    pol = policy [((Observed, User), Admit)] QuarantineOnConflict

-- | Group-only quarantine remains representable by the frozen raw core:
-- @lara-core@ already carries duplicate-report groups and performs the same
-- prune. A nonempty group audit must therefore not make the bound raw
-- 'CheckInput' unavailable when policy admission itself removed nothing.
prop_allAdmitGroupOnlyCoreExportIdentity :: Property
prop_allAdmitGroupOnlyCoreExportIdentity =
  accepted prog pol $ \input ->
    let sourceResult = runSourceCheck input
     in case sourceResultCheckInput sourceResult of
          Left audit ->
            counterexample
              ("group-only all-admit source was treated as an unrepresentable policy prune: "
                ++ renderAdmissionAudit audit)
              False
          Right legacyInput ->
            let sourceVerdict = sourceResultVerdict sourceResult
                legacyVerdict = runCheck legacyInput
             in conjoin
                  [ sourceVerdict === legacyVerdict
                  , printSExpr (encodeVerdict sourceVerdict)
                      === printSExpr (encodeVerdict legacyVerdict)
                  , admissionAuditLeaves (sourceResultAudit sourceResult)
                      ===
                        [ ( LeafId "e1"
                          , GroupQuarantine (GroupId "g") :| []
                          )
                        , ( LeafId "e2"
                          , GroupQuarantine (GroupId "g") :| []
                          )
                        ]
                  ]
  where
    prog =
      program
        []
        [ leafD "e1" "p" Observed User
        , leafD "e2" "q" Attested User
        , DeclGroup (DupGroup (GroupId "g") [LeafId "e1", LeafId "e2"])
        ]
    pol = policy [((Observed, User), Admit), ((Attested, User), Admit)] QuarantineOnConflict
-- | Duplicate policy keys are malformed before the matching leaf can select
-- either the first @reject@ or the later @admit@ row.
prop_duplicateAdmissionBeforeDecision :: Property
prop_duplicateAdmissionBeforeDecision =
  case prepareSource prog pol of
    Left invalid@(DuplicateAdmissionKey Observed User) ->
      conjoin
        [ renderSourceInvalid invalid === "duplicate admission key (observed, user)"
        , case validateAdmissionKeys (policyAdmission pol) of
            Left _ -> property True
            Right () -> counterexample "standalone validator accepted duplicate keys" False
        ]
    _ -> counterexample "expected duplicate admission key" False
  where
    prog = program [] [leafD "e" "p" Observed User]
    pol = policy [((Observed, User), AST.Reject), ((Observed, User), Admit)] QuarantineOnConflict

-- | Duplicate source leaf identifiers win over replay metadata construction.
-- The repeated theory digest would independently make source replay identity
-- invalid if the duplicate-leaf guard were deleted.
prop_duplicateLeafBeforeReplayAlignment :: Property
prop_duplicateLeafBeforeReplayAlignment =
  case prepareSource prog pol of
    Left invalid@(DuplicateSourceLeafId (LeafId "e")) ->
      renderSourceInvalid invalid === "duplicate leaf id 'e'"
    _ -> counterexample "expected duplicate LeafId" False
  where
    prog = program [] [leafD "e" "p" Observed User, leafD "e" "q" Attested User]
    pol =
      (policy [] QuarantineOnConflict)
        { policyTheories =
            [ (TheoryDigest "sha256:duplicate", [])
            , (TheoryDigest "sha256:duplicate", [])
            ]
        }

-- | The shipped negative is the canonical first-leaf R8 golden.  Accessors
-- expose every required source constituent without exposing the constructor.
prop_admissionRejectGolden :: Property
prop_admissionRejectGolden =
  case negPolicy admissionReject of
    Nothing -> counterexample "admissionReject has no policy" False
    Just pol -> case prepareSource (negProgram admissionReject) pol of
      Left invalid -> counterexample ("R8 misclassified as invalid: " ++ show invalid) False
      Right (SourceAccepted _) -> counterexample "R8 unexpectedly accepted" False
      Right (SourceRejected rejection) ->
        conjoin
          [ admissionRejectionLeaf rejection === LeafId "e_assumed"
          , admissionRejectionKind rejection === Assumed
          , admissionRejectionProvenance rejection === AiExecuted
          , admissionRejectionMatchedRow rejection === ((Assumed, AiExecuted), AST.Reject)
          , renderAdmissionRejection rejection === negDiagnostic admissionReject
          ]

-- | Policy quarantine follows every support-term occurrence: direct leaf,
-- nested premise, and critical-question discharge.  Missing any recursion arm
-- leaves the corresponding argument visible in this exact projection.
prop_quarantinePrunesEveryDependency :: Property
prop_quarantinePrunesEveryDependency =
  accepted prog pol $ \input ->
    let audit = sourceResultAudit (runSourceCheck input)
     in conjoin
          [ admissionAuditLeaves audit === [(LeafId "e_q", PolicyQuarantine :| [])]
          , admissionAuditArgs audit === map ArgId ["a_nested", "a_direct", "a_discharge"]
          ]
  where
    nested =
      Rule (RuleId "nested") [] Defeasible [apat0 "p"] [] (apat0 "nested") False [] []
    discharge =
      Rule
        (RuleId "discharge")
        []
        Defeasible
        []
        []
        (apat0 "discharged")
        False
        []
        [Question (QuestionId "q") (apat0 "p") Mandatory]
    prog =
      program
        []
        [ leafD "e_q" "p" Observed User
        , DeclArg
            ( Arg
                { argId = ArgId "a_nested"
                , argConcl = SupportsDerived (PropId "n")
                , argInstantiation =
                    ExplicitTheta
                      (SRule (RuleId "nested") [] [] [] [] AssuranceNone)
                }
            )
        , DeclArg
            ( Arg
                { argId = ArgId "a_direct"
                , argConcl = SupportsDerived (PropId "d")
                , argInstantiation = ExplicitTheta (SLeaf (LeafId "e_q"))
                }
            )
        , DeclArg
            ( Arg
                { argId = ArgId "a_discharge"
                , argConcl = SupportsDerived (PropId "x")
                , argInstantiation =
                    ExplicitTheta
                      ( SRule
                          (RuleId "discharge")
                          []
                          []
                          [(QuestionId "q", SLeaf (LeafId "e_q"))]
                          []
                          AssuranceNone
                      )
                }
            )
        ]
    pol =
      (policy [((Observed, User), Quarantine)] QuarantineOnConflict)
        { policyRules = [nested, discharge]
        }

-- | Raw endpoints, not resolved support-term equality, decide which attacks
-- survive.  Both directions involving the removed id disappear; the unrelated
-- declaration remains and retains its source position.
prop_attackEndpointFiltering :: Property
prop_attackEndpointFiltering =
  accepted prog pol $ \input ->
    let result = runSourceCheck input
        audit = sourceResultAudit result
     in conjoin
          [ admissionAuditAttacks audit === take 2 attacks
          , case verdictOutcome (sourceResultVerdict result) of
              Reject rejection -> counterexample ("unexpected reject: " ++ show rejection) False
              Accept _ edges _ -> edges === [(1, 0)]
          ]
  where
    attacks =
      [ Undermine (ArgId "a_removed") (ArgId "a_one") []
      , Undermine (ArgId "a_two") (ArgId "a_removed") []
      , Undermine (ArgId "a_two") (ArgId "a_one") []
      ]
    prog =
      program
        []
        ( [ leafD "e_removed" "removed" Observed User
          , leafD "e_one" "one" Attested User
          , leafD "e_two" "two" Assumed User
          , argLeaf "a_removed" "e_removed"
          , argLeaf "a_one" "e_one"
          , argLeaf "a_two" "e_two"
          ]
            ++ map (DeclAttack . surfaceAttack) attacks
        )
    pol =
      (policy [((Observed, User), Quarantine)] QuarantineOnConflict)
        { policyContraries = [Contrary (apat0 "two") (apat0 "one")]
        }

-- | Policy and every inconsistent group contribute to one declaration-ordered
-- audit.  Causes are deduplicated and canonically ordered, while argument and
-- attack projections preserve their own declaration orders exactly.
prop_combinedAuditCanonical :: Property
prop_combinedAuditCanonical =
  accepted prog pol $ \input ->
    let audit = sourceResultAudit (runSourceCheck input)
     in conjoin
          [ admissionAuditLeaves audit
              === [ ( LeafId "e1"
                    , PolicyQuarantine :| [GroupQuarantine (GroupId "g1"), GroupQuarantine (GroupId "g2")]
                    )
                  , (LeafId "e2", GroupQuarantine (GroupId "g1") :| [])
                  , (LeafId "e3", GroupQuarantine (GroupId "g2") :| [])
                  ]
          , admissionAuditArgs audit === map ArgId ["a3", "a1", "a2"]
          , admissionAuditAttacks audit === attacks
          , renderAdmissionAudit audit
              === ( "admission audit: leaves "
                      ++ "[e1{policy-quarantine,group-quarantine:g1,group-quarantine:g2},"
                      ++ "e2{group-quarantine:g1},e3{group-quarantine:g2}]; "
                      ++ "arguments [a3,a1,a2]; "
                      ++ "attacks [rebut(a3,a4),rebut(a4,a1),rebut(a2,a4)]"
                 )
          ]
  where
    attacks =
      [ Rebut (ArgId "a3") (ArgId "a4")
      , Rebut (ArgId "a4") (ArgId "a1")
      , Rebut (ArgId "a2") (ArgId "a4")
      ]
    prog =
      program
        []
        ( [ leafD "e1" "p" Observed User
          , leafD "e2" "q" Attested User
          , leafD "e3" "r" Assumed User
          , leafD "e4" "s" Certified User
          , DeclGroup (DupGroup (GroupId "g1") [LeafId "e1", LeafId "e2"])
          , DeclGroup (DupGroup (GroupId "g2") [LeafId "e1", LeafId "e3"])
          , argLeaf "a3" "e3"
          , argLeaf "a1" "e1"
          , argLeaf "a4" "e4"
          , argLeaf "a2" "e2"
          ]
            ++ map (DeclAttack . surfaceAttack) attacks
        )
    pol = policy [((Observed, User), Quarantine)] QuarantineOnConflict

-- | Group consistency reads the declared leaf table.  If policy removal were
-- applied first, @g@ would degenerate and this R9 would disappear.
prop_groupChecksDeclaredLeaves :: Property
prop_groupChecksDeclaredLeaves =
  accepted prog pol $ \input ->
    verdictOutcome (sourceResultVerdict (runSourceCheck input)) === Reject (RejectClass R9)
  where
    prog =
      program
        []
        [ leafD "e_policy" "p" Observed User
        , leafD "e_other" "q" Attested User
        , DeclGroup (DupGroup (GroupId "g") [LeafId "e_policy", LeafId "e_other"])
        ]
    pol = policy [((Observed, User), Quarantine)] RejectOnConflict

-- | Removing the sole attacker makes the checked graph conditionally justify
-- its target.  The public result overlays evidence-blocked only on the affected
-- query; the independent query remains an ordinary justified answer.
prop_policyQuarantineBlockedOverlay :: Property
prop_policyQuarantineBlockedOverlay =
  accepted prog pol $ \input ->
    let result = runSourceCheck input
     in conjoin
          [ case verdictOutcome (sourceResultVerdict result) of
              Reject rejection -> counterexample ("unexpected reject: " ++ show rejection) False
              Accept _ _ statuses ->
                statuses
                  === [ (atom0 "target", EvidenceBlocked Justified)
                      , (atom0 "other", Published Justified)
                      ]
          , case sourceResultCheckInput result of
              Left audit -> audit === sourceResultAudit result
              Right _ ->
                counterexample
                  "policy-pruned source escaped as a legacy raw CheckInput"
                  False
          , sourceStatusPairs (sourceResultJsonValue result)
              === Just
                [ ("target", "evidence-blocked", Just "justified")
                , ("other", "justified", Nothing)
                ]
          ]
  where
    prog =
      program
        []
        [ claimD "target_claim" "target"
        , claimD "other_claim" "other"
        , leafD "e_target" "target" Attested User
        , leafD "e_attacker" "attacker" Observed User
        , leafD "e_other" "other" Assumed User
        , argClaim "a_target" "target_claim" "e_target"
        , argLeaf "a_attacker" "e_attacker"
        , argClaim "a_other" "other_claim" "e_other"
        , DeclAttack (SRebut (ArgId "a_attacker") (ArgId "a_target"))
        , DeclStatus (PropId "target_claim")
        , DeclStatus (PropId "other_claim")
        ]
    pol =
      (policy [((Observed, User), Quarantine)] QuarantineOnConflict)
        { policyContraries = [Contrary (apat0 "attacker") (apat0 "target")]
        }

-- | A policy-pruned source that then fails an ordinary checker stage must still
-- publish /where/ it failed.  The pruned envelope cannot be re-derived
-- ('sourceResultCheckInput' fails closed), so the located rejection is the only
-- carrier of the stage and constituent — and the @stderr@ message list is empty
-- for every rejection that is not R13 or R9, so a messages-only rendering would
-- publish nothing at all.
--
-- The constituent index is also the __checked__ one: @a_drop@ is pruned, so the
-- offending @a_bad@ sits at declared index 1 but checked index 0.  Naming it
-- from the declared list would report the wrong argument.
prop_policyPrunedRejectionKeepsLocation :: Property
prop_policyPrunedRejectionKeepsLocation =
  accepted prog pol $ \input ->
    let result = runSourceCheck input
     in conjoin
          [ verdictOutcome (sourceResultVerdict result) === Reject (RejectClass R1)
          , case sourceResultCheckInput result of
              Left _ -> property True
              Right _ ->
                counterexample
                  "policy-pruned source escaped as a legacy raw CheckInput"
                  False
          , sourceRejectDiagnostic (sourceResultJsonValue result)
              === Just
                ( "R1"
                , "support"
                , JObject
                    [ ("kind", JString "argument")
                    , ("id", JString "a_bad")
                    , ("index", JNumber 0)
                    ]
                , []
                )
          ]
  where
    prog =
      program
        []
        [ leafD "e_drop" "p" Observed User
        , leafD "e_ok" "q" Attested User
        , argLeaf "a_drop" "e_drop"
        , -- No such leaf is declared: the elaborator passes it through and
          -- @checkUnit@ rejects it as R1 (kept distinct from the R8 class).
          argLeaf "a_bad" "e_missing"
        ]
    pol = policy [((Observed, User), Quarantine)] QuarantineOnConflict

-- | @(class, stage, constituent, messages)@ of a rendered source rejection.
sourceRejectDiagnostic :: JValue -> Maybe (String, String, JValue, [String])
sourceRejectDiagnostic (JObject top) = do
  JObject diagnostic <- lookup "located-diagnostic" top
  JString cls <- lookup "class" diagnostic
  JString stage <- lookup "stage" diagnostic
  constituent <- lookup "constituent" diagnostic
  JArray messages <- lookup "messages" diagnostic
  texts <- traverse (\m -> case m of JString t -> Just t; _ -> Nothing) messages
  pure (cls, stage, constituent, texts)
sourceRejectDiagnostic _ = Nothing

sourceStatusPairs :: JValue -> Maybe [(String, String, Maybe String)]
sourceStatusPairs (JObject top) = do
  JObject diagnostic <- lookup "located-diagnostic" top
  JArray statuses <- lookup "statuses" diagnostic
  traverse statusRow statuses
  where
    statusRow (JObject row) = do
      JString claim <- lookup "claim" row
      JString status <- lookup "status" row
      let conditional = case lookup "conditional-status" row of
            Just (JString value) -> Just value
            _ -> Nothing
      pure (claim, status, conditional)
    statusRow _ = Nothing
sourceStatusPairs _ = Nothing

auditLeaves :: AdmissionAudit -> [(LeafId, NonEmpty AdmissionCause)] -> Property
auditLeaves audit expected = admissionAuditLeaves audit === expected

admissionSpecProps :: [(String, IO Result)]
admissionSpecProps =
  [ ("admission omitted/unmatched rows default to admit", quickCheckResult prop_totalDefaultAdmit)
  , ("admission explicit admit preserves dependent graph", quickCheckResult prop_explicitAdmitPreservesGraph)
  , ("admission all-admit source verdict equals raw checker bytes", quickCheckResult prop_allAdmitSourceVerdictIdentity)
  , ("admission all-admit group-only core export equals raw checker bytes",
      quickCheckResult prop_allAdmitGroupOnlyCoreExportIdentity)
  , ("admission duplicate key precedes leaf decisions", quickCheckResult prop_duplicateAdmissionBeforeDecision)
  , ("admission duplicate LeafId precedes replay alignment", quickCheckResult prop_duplicateLeafBeforeReplayAlignment)
  , ("admission canonical first-leaf R8 negative", quickCheckResult prop_admissionRejectGolden)
  , ("admission quarantine prunes direct/premise/discharge dependencies", quickCheckResult prop_quarantinePrunesEveryDependency)
  , ("admission quarantine filters attacks by raw endpoints", quickCheckResult prop_attackEndpointFiltering)
  , ("admission policy+group union has canonical audit", quickCheckResult prop_combinedAuditCanonical)
  , ("admission groups inspect declared leaves", quickCheckResult prop_groupChecksDeclaredLeaves)
  , ("admission quarantine applies blocked overlay", quickCheckResult prop_policyQuarantineBlockedOverlay)
  , ("admission pruned rejection keeps its located stage/constituent",
      quickCheckResult prop_policyPrunedRejectionKeepsLocation)
  ]
