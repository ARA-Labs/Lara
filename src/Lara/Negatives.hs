-- | Rejection-class examples: LARA programs the checker is designed to __reject__.
--
-- @PAPER.md@ lists "rejection-class conformance" alongside mechanization and
-- worked examples as the evaluation for this contribution, but "Lara.Examples"
-- only holds /accepted/ programs (their varied @justified@/@gap@/@defeated@
-- statuses are all __Axis B__ — the claim status of a program that /passed/
-- structural checking). This module supplies the missing __Axis A__ negatives:
-- one minimal ill-formed program per rejection class defined in the spec, each
-- paired with the located diagnostic acceptance must produce.
--
-- Two output axes, kept distinct (see 'RejectionClass'):
--
--   * __Axis A — structural acceptance.__ Does the checker /accept/ the
--     certificate? Reject ⇒ a located diagnostic. Every program here is an Axis-A
--     __reject__.
--   * __Axis B — claim status.__ For an accepted program, the four-state grounded
--     status. @defeated@ is /not/ a rejection — it is a successful check with an
--     unfavorable status ("Lara.Examples"). The one subtlety worth stating: a
--     @quarantine@ leaf (§4.3) is __accepted__ and yields a @gap@ (Axis B), which
--     is why only @reject@ admission appears here, contrasted in 'admissionReject'.
--
-- As with "Lara.Examples" this is __data only__: there is no checker yet, so the
-- 'negDiagnostic' strings record the /designed/ rejection, not a runner result.
-- When "Lara.Check" exists, each 'Negative' becomes a golden test: check
-- @negProgram@ against @negPolicy@ and assert it is rejected with a matching
-- located diagnostic.
module Lara.Negatives
  ( -- * Taxonomy
    RejectionClass (..)
  , Negative (..)
    -- * Negatives, one per class
  , danglingReference
  , supportMismatch
  , premiseMismatch
  , unaccountedQuestion
  , illTypedAttack
  , strictReachableContrary
  , admissionReject
  , strictAssuranceViolation
  , duplicateReportGroupConflict
    -- * Index
  , allNegatives
  ) where

import Lara.AST
import Lara.Prop (Prop (..), Term (..))

-- ---------------------------------------------------------------------------
-- Taxonomy
-- ---------------------------------------------------------------------------

-- | The kind of well-formedness rule a 'Negative' violates. Each maps to a spec
-- section; the checker's job (spec result 1) is that all of these are decidable.
data RejectionClass
  = -- | A declaration references a name that is not declared (spec §1).
    DanglingReference
  | -- | @concl(w) ≢ c.formal@: the support term does not conclude the claim's
    -- formal target (spec §3.1, result 11).
    SupportMismatch
  | -- | @concl(w_i) ≠ P_i·theta@: a premise term's conclusion does not match the
    -- rule's premise pattern under the instance substitution (spec §4.1).
    PremiseMismatch
  | -- | A declared critical question is neither discharged nor listed as an open
    -- hole (spec §4.2) — every question must be accounted for.
    UnaccountedQuestion
  | -- | A typed attack is ill-formed: a rebut/undercut on a __strict__ rule, an
    -- undermine whose target is not a leaf, or a rebut/undermine pair that is not
    -- a declared @contrary@ (spec §7).
    IllTypedAttack
  | -- | Policy well-formedness (compile time): a strict-reachable proposition
    -- appears in a @contrary@ pair, which Path B forbids (spec §8.1).
    StrictReachableContrary
  | -- | A leaf's @(kind, provenance)@ maps to @reject@ in the admission table
    -- (spec §4.3) — the declaration itself violates policy.
    LeafAdmissionReject
  | -- | A duplicate-report group has @≢@ members and the policy escalates the
    -- conflict to @reject@ (spec §4.3, R9) — a whole-program data-integrity
    -- error located at the group declaration.
    DuplicateReportGroupConflict
  | -- | A strict instance uses @assurance = trusted@ when the rule has
    -- @allow-trusted = false@, or @cert(beta,h)@ with @(beta,h)@ absent from the
    -- rule's certifiers (spec §4, §5).
    StrictAssuranceViolation
  deriving (Eq, Show)

-- | A rejection-class example: the malformed program, the trusted policy it is
-- checked against (when the violation is policy-relative), the class it belongs
-- to, the spec location of the rule it breaks, and the located diagnostic the
-- checker is /designed/ to emit.
data Negative = Negative
  { negName :: String
  , negClass :: RejectionClass
  , negSpecRef :: String
  , negProgram :: Program
  , negPolicy :: Maybe Policy
  , negDiagnostic :: String
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Construction helpers (kept local so this module is independent)
-- ---------------------------------------------------------------------------

con :: String -> Term
con k = TCon (FunSym k) []

-- | A constructor applied to arguments, e.g. @effect(m, accuracy, d, +2.1)@.
funT :: String -> [Term] -> Term
funT k = TCon (FunSym k)

atom :: String -> [Term] -> Prop
atom p = Prop (Pred p)

leafD :: String -> Prop -> LeafKind -> Provenance -> Leaf
leafD lid p k prov =
  Leaf
    { leafId = LeafId lid
    , leafProp = p
    , leafKind = k
    , leafProvenance = prov
    , leafRefs = []
    }

claimD :: String -> String -> Prop -> Claim
claimD cid nl formal =
  Claim
    { claimId = PropId cid
    , claimNl = nl
    , claimFormal = formal
    , claimBinding = Binding "codex" "" Unreviewed
    }

-- | A defeasible instance (assurance = none) with premises, discharge, holes.
inst
  :: String -> Subst -> [SupportTerm] -> [(QuestionId, SupportTerm)] -> [ObligationId] -> SupportTerm
inst r theta prems disch holes =
  SRule (RuleId r) theta prems disch holes AssuranceNone

-- | A defeasible rule with premise/conclusion atom patterns and questions.
defeasibleRule :: String -> [String] -> [AtomPat] -> AtomPat -> [Question] -> Rule
defeasibleRule r ps prem concl qs =
  Rule
    { ruleId = RuleId r
    , ruleParams = map Param ps
    , ruleMode = Defeasible
    , rulePremises = prem
    , rulePremiseLabels = []
    , ruleConclusion = concl
    , ruleAllowTrusted = False
    , ruleCertifiers = []
    , ruleQuestions = qs
    }

-- | A strict rule; @allow-trusted@ and certifiers spelled out.
strictRule :: String -> [String] -> [AtomPat] -> AtomPat -> Bool -> [CertRef] -> Rule
strictRule r ps prem concl allowTrusted certs =
  Rule
    { ruleId = RuleId r
    , ruleParams = map Param ps
    , ruleMode = Strict
    , rulePremises = prem
    , rulePremiseLabels = []
    , ruleConclusion = concl
    , ruleAllowTrusted = allowTrusted
    , ruleCertifiers = certs
    , ruleQuestions = []
    }

-- | A program shell with a fixed policy id and no backends unless overridden.
prog :: String -> [Decl] -> Program
prog pol decls =
  Program
    { programArtifact = "negatives"
    , programDigest = Digest "sha256:neg…"
    , programPolicy = PolicyId pol
    , programBackends = []
    , programDecls = decls
    }

-- ===========================================================================
-- N1 — DanglingReference (spec §1)
-- ===========================================================================

-- | The @arg@ names a support term over leaf @e_missing@, which is never
-- declared. All references must resolve (spec §1, result 1).
danglingReference :: Negative
danglingReference =
  Negative
    { negName = "dangling leaf reference"
    , negClass = DanglingReference
    , negSpecRef = "§1 (well-formed references)"
    , negProgram =
        prog
          "empirical-v1"
          [ DeclClaim (claimD "c" "M improves accuracy on D" (atom "improves" [con "m", con "accuracy", con "d"]))
          , DeclArg (Arg (ArgId "a") (SupportsClaim (PropId "c")) (SLeaf (LeafId "e_missing")))
          , DeclStatus (PropId "c")
          ]
    , negPolicy = Nothing
    , negDiagnostic = "arg 'a': reference to undeclared leaf 'e_missing'"
    }

-- ===========================================================================
-- N2 — SupportMismatch (spec §3.1, result 11)
-- ===========================================================================

-- | The claim's formal target is @improves(m, accuracy, d)@ but the supporting
-- leaf concludes @reports(exp_3, effect(m, accuracy, d, +2.1))@. @w supports c@
-- requires @concl(w) ≡ c.formal@ (spec §3.1); the raw observation is not
-- positionally identical to the claim, so support fails. (In a real program a
-- @controlled_experiment@ rule would bridge them; here the arg wires the leaf
-- straight to the claim, which is exactly the mistake.)
supportMismatch :: Negative
supportMismatch =
  Negative
    { negName = "support term does not conclude the claim's formal target"
    , negClass = SupportMismatch
    , negSpecRef = "§3.1, result 11"
    , negProgram =
        prog
          "empirical-v1"
          [ DeclClaim (claimD "c" "M improves accuracy on D" (atom "improves" [con "m", con "accuracy", con "d"]))
          , DeclLeaf
              ( leafD
                  "e1"
                  (atom "reports" [con "exp_3", funT "effect" [con "m", con "accuracy", con "d", TNum "+2.1"]])
                  Observed
                  AiExecuted
              )
          , DeclArg (Arg (ArgId "a") (SupportsClaim (PropId "c")) (SLeaf (LeafId "e1")))
          , DeclStatus (PropId "c")
          ]
    , negPolicy = Nothing
    , negDiagnostic =
        "arg 'a': concl(w) = reports(exp_3, effect(m, accuracy, d, 2.1)) "
          ++ "not ≡ c.formal = improves(m, accuracy, d)"
    }

-- ===========================================================================
-- N3 — PremiseMismatch (spec §4.1)
-- ===========================================================================

-- | Rule @controlled_experiment(M, Acc, D, Delta)@ has premise pattern
-- @reports(exp_3, effect(M, Acc, D, Delta))@. The instance binds
-- @M=m, Acc=accuracy, D=d, Delta=+2.1@ but its premise leaf concludes
-- @reports(exp_3, effect(m, accuracy, d_shift, +2.1))@ — @D@ disagrees, so
-- @concl(w_0) ≠ P_0·theta@ (spec §4.1: instance checking is substitution
-- application plus syntactic identity).
premiseMismatch :: Negative
premiseMismatch =
  Negative
    { negName = "premise conclusion does not match pattern under theta"
    , negClass = PremiseMismatch
    , negSpecRef = "§4.1"
    , negProgram =
        prog
          "empirical-v1"
          [ DeclClaim (claimD "c" "M improves accuracy on D" (atom "improves" [con "m", con "accuracy", con "d"]))
          , DeclLeaf
              ( leafD
                  "e1"
                  -- note: d_shift, not d
                  (atom "reports" [con "exp_3", funT "effect" [con "m", con "accuracy", con "d_shift", TNum "+2.1"]])
                  Observed
                  AiExecuted
              )
          , DeclArg
              ( Arg
                  (ArgId "a")
                  (SupportsClaim (PropId "c"))
                  ( inst
                      "controlled_experiment"
                      [ (Param "M", con "m")
                      , (Param "Acc", con "accuracy")
                      , (Param "D", con "d")
                      , (Param "Delta", TNum "+2.1")
                      ]
                      [SLeaf (LeafId "e1")]
                      []
                      []
                  )
              )
          , DeclStatus (PropId "c")
          ]
    , negPolicy =
        Just $
          Policy
            { policyId = PolicyId "empirical-v1"
            , policyRules =
                [ defeasibleRule
                    "controlled_experiment"
                    ["M", "Acc", "D", "Delta"]
                    [AtomPat (Pred "reports") [PCon (FunSym "exp_3") [], PCon (FunSym "effect") [PVar (Param "M"), PVar (Param "Acc"), PVar (Param "D"), PVar (Param "Delta")]]]
                    (AtomPat (Pred "improves") [PVar (Param "M"), PVar (Param "Acc"), PVar (Param "D")])
                    []
                ]
            , policyContraries = []
            , policyExceptions = []
            , policyAdmission = []
            , policyTheories = []
            , policyGroupMode = QuarantineOnConflict
            , policyMeasurands = []
            , policyComparisonSchemes = []
            }
    , negDiagnostic =
        "arg 'a', premise 0: concl(e1) = reports(exp_3, effect(m, accuracy, d_shift, 2.1)) "
          ++ "does not match P0·theta = reports(exp_3, effect(m, accuracy, d, 2.1))"
    }

-- ===========================================================================
-- N4 — UnaccountedQuestion (spec §4.2)
-- ===========================================================================

-- | Rule @controlled_experiment@ declares a mandatory critical question
-- @randomization@. The instance neither discharges it nor lists it in the hole
-- set, which is a well-formedness error (spec §4.2: every declared question is
-- accounted for, by discharge or by an explicit hole). Contrast the accepted
-- "Lara.Examples" C02, which /does/ declare its open question as a hole.
unaccountedQuestion :: Negative
unaccountedQuestion =
  Negative
    { negName = "declared critical question neither discharged nor opened"
    , negClass = UnaccountedQuestion
    , negSpecRef = "§4.2"
    , negProgram =
        prog
          "empirical-v1"
          [ DeclClaim (claimD "c" "M improves accuracy on D" (atom "improves" [con "m", con "accuracy", con "d"]))
          , DeclLeaf
              ( leafD
                  "e1"
                  (atom "reports" [con "exp_3", funT "effect" [con "m", con "accuracy", con "d", TNum "+2.1"]])
                  Observed
                  AiExecuted
              )
          , DeclArg
              ( Arg
                  (ArgId "a")
                  (SupportsClaim (PropId "c"))
                  ( inst
                      "controlled_experiment"
                      [(Param "M", con "m"), (Param "Acc", con "accuracy"), (Param "D", con "d"), (Param "Delta", TNum "+2.1")]
                      [SLeaf (LeafId "e1")]
                      [] -- no discharge
                      [] -- and no open hole for 'randomization'
                  )
              )
          , DeclStatus (PropId "c")
          ]
    , negPolicy =
        Just $
          Policy
            { policyId = PolicyId "empirical-v1"
            , policyRules =
                [ defeasibleRule
                    "controlled_experiment"
                    ["M", "Acc", "D", "Delta"]
                    [AtomPat (Pred "reports") [PCon (FunSym "exp_3") [], PCon (FunSym "effect") [PVar (Param "M"), PVar (Param "Acc"), PVar (Param "D"), PVar (Param "Delta")]]]
                    (AtomPat (Pred "improves") [PVar (Param "M"), PVar (Param "Acc"), PVar (Param "D")])
                    [Question (QuestionId "randomization") (AtomPat (Pred "randomized") [PVar (Param "M")]) Mandatory]
                ]
            , policyContraries = []
            , policyExceptions = []
            , policyAdmission = []
            , policyTheories = []
            , policyGroupMode = QuarantineOnConflict
            , policyMeasurands = []
            , policyComparisonSchemes = []
            }
    , negDiagnostic =
        "arg 'a': question 'randomization' of rule 'controlled_experiment' is "
          ++ "neither discharged nor declared as an open hole"
    }

-- ===========================================================================
-- N5 — IllTypedAttack (spec §7)
-- ===========================================================================

-- | A @rebut@ targets the conclusion of an argument whose top rule is
-- __strict__. Strict rules are deductively valid and unattackable (spec §7:
-- "strict rules cannot be undercut or rebutted"), so the attack is ill-typed
-- regardless of the contrary relation.
illTypedAttack :: Negative
illTypedAttack =
  Negative
    { negName = "rebut targets a strict rule's conclusion"
    , negClass = IllTypedAttack
    , negSpecRef = "§7"
    , negProgram =
        prog
          "mixed-v1"
          [ DeclClaim (claimD "c" "Q holds" (atom "q" []))
          , DeclClaim (claimD "c_not" "not-Q holds" (atom "not_q" []))
          , DeclLeaf (leafD "e_p" (atom "p" []) Assumed AiExecuted)
          , DeclLeaf (leafD "e_nq" (atom "grounds_not_q" []) Observed AiExecuted)
          , DeclArg
              ( Arg
                  (ArgId "a_strict")
                  (SupportsClaim (PropId "c"))
                  (SRule (RuleId "deductive_step") [] [SLeaf (LeafId "e_p")] [] [] AssuranceTrusted)
              )
          , DeclArg (Arg (ArgId "d") (SupportsClaim (PropId "c_not")) (inst "presumption" [] [SLeaf (LeafId "e_nq")] [] []))
          , DeclAttack (SRebut (ArgId "d") (ArgId "a_strict"))
          , DeclStatus (PropId "c")
          ]
    , negPolicy =
        Just $
          Policy
            { policyId = PolicyId "mixed-v1"
            , policyRules =
                [ strictRule "deductive_step" [] [AtomPat (Pred "p") []] (AtomPat (Pred "q") []) True []
                , defeasibleRule "presumption" [] [AtomPat (Pred "grounds_not_q") []] (AtomPat (Pred "not_q") []) []
                ]
            , policyContraries = [Contrary (AtomPat (Pred "q") []) (AtomPat (Pred "not_q") [])]
            , policyExceptions = []
            , policyAdmission = []
            , policyTheories = []
            , policyGroupMode = QuarantineOnConflict
            , policyMeasurands = []
            , policyComparisonSchemes = []
            }
    , negDiagnostic =
        "attack 'rebut d a_strict': target's top rule 'deductive_step' is strict; "
          ++ "strict rules are unattackable (§7)"
    }

-- ===========================================================================
-- N6 — StrictReachableContrary (spec §8.1, Path B)
-- ===========================================================================

-- | A __policy__ well-formedness violation, caught at compile time before any
-- program term is checked. The strict rule @deductive_step@ concludes
-- @derived(X)@, so @derived(X)@ is strict-reachable; declaring
-- @contrary derived(X) refuted(X)@ puts a strict-reachable proposition into a
-- contrary pair, which Path B forbids (spec §8.1) because a conflict behind a
-- strict rule is invisible to the attack relation and could break
-- direct/indirect consistency. A program instantiating this policy is rejected
-- with a located diagnostic naming the offending rule and pair.
strictReachableContrary :: Negative
strictReachableContrary =
  Negative
    { negName = "strict-reachable proposition appears in a contrary pair"
    , negClass = StrictReachableContrary
    , negSpecRef = "§8.1 (Path B compile-time restriction)"
    , negProgram =
        prog
          "illformed-policy-v1"
          [ DeclClaim (claimD "c" "derived(x) holds" (atom "derived" [con "x"]))
          , DeclStatus (PropId "c")
          ]
    , negPolicy =
        Just $
          Policy
            { policyId = PolicyId "illformed-policy-v1"
            , policyRules =
                [ strictRule "deductive_step" ["X"] [AtomPat (Pred "basis") [PVar (Param "X")]] (AtomPat (Pred "derived") [PVar (Param "X")]) True []
                ]
            , -- derived(X) is strict-reachable, yet it appears here:
              policyContraries = [Contrary (AtomPat (Pred "derived") [PVar (Param "X")]) (AtomPat (Pred "refuted") [PVar (Param "X")])]
            , policyExceptions = []
            , policyAdmission = []
            , policyTheories = []
            , policyGroupMode = QuarantineOnConflict
            , policyMeasurands = []
            , policyComparisonSchemes = []
            }
    , negDiagnostic =
        "policy 'illformed-policy-v1': strict-reachable proposition 'derived(X)' "
          ++ "(conclusion of strict rule 'deductive_step') appears in contrary pair "
          ++ "(derived(X), refuted(X)) — forbidden by §8.1 Path B"
    }

-- ===========================================================================
-- N7 — LeafAdmissionReject (spec §4.3)
-- ===========================================================================

-- | The admission table maps @(assumed, ai-executed)@ to @reject@, so declaring
-- a leaf with that kind/provenance violates policy and the checker rejects the
-- certificate (spec §4.3). This is distinct from @quarantine@, which is
-- __accepted__ but keeps the leaf out of Γ (a term using it becomes a @gap@,
-- Axis B) — the reason only @reject@ is a negative here.
admissionReject :: Negative
admissionReject =
  Negative
    { negName = "leaf kind/provenance maps to reject in the admission table"
    , negClass = LeafAdmissionReject
    , negSpecRef = "§4.3"
    , negProgram =
        prog
          "strict-admission-v1"
          [ DeclClaim (claimD "c" "assumption A" (atom "a" []))
          , DeclLeaf (leafD "e_assumed" (atom "a" []) Assumed AiExecuted)
          , DeclArg (Arg (ArgId "a") (SupportsClaim (PropId "c")) (SLeaf (LeafId "e_assumed")))
          , DeclStatus (PropId "c")
          ]
    , negPolicy =
        Just $
          Policy
            { policyId = PolicyId "strict-admission-v1"
            , policyRules = []
            , policyContraries = []
            , policyExceptions = []
            , policyAdmission = [((Assumed, AiExecuted), Reject)]
            , policyTheories = []
            , policyGroupMode = QuarantineOnConflict
            , policyMeasurands = []
            , policyComparisonSchemes = []
            }
    , negDiagnostic =
        "leaf 'e_assumed': kind=assumed, provenance=ai-executed matched "
          ++ "admission row (assumed, ai-executed) = reject (R8)"
    }

-- ===========================================================================
-- N8 — StrictAssuranceViolation (spec §4, §5)
-- ===========================================================================

-- | The strict rule @deductive_step@ has @allow-trusted = false@ and lists a
-- @nd@ certifier, so an instance may only carry @cert(nd, h)@. This instance
-- instead uses @assurance = trusted@, which spec §4 permits only when
-- @allow-trusted = true@. Rejected with a located diagnostic.
strictAssuranceViolation :: Negative
strictAssuranceViolation =
  Negative
    { negName = "assurance=trusted on a rule with allow-trusted=false"
    , negClass = StrictAssuranceViolation
    , negSpecRef = "§4, §5"
    , negProgram =
        (prog "strict-cert-v1" decls) {programBackends = [(BackendId "nd", "1")]}
    , negPolicy =
        Just $
          Policy
            { policyId = PolicyId "strict-cert-v1"
            , policyRules =
                [ strictRule
                    "deductive_step"
                    []
                    [AtomPat (Pred "p") []]
                    (AtomPat (Pred "q") [])
                    False -- allow-trusted = false
                    [CertRef (BackendId "nd") 1 (TheoryDigest "sha256:theory…")]
                ]
            , policyContraries = []
            , policyExceptions = []
            , policyAdmission = []
            , policyTheories = []
            , policyGroupMode = QuarantineOnConflict
            , policyMeasurands = []
            , policyComparisonSchemes = []
            }
    , negDiagnostic =
        "arg 'a': assurance = trusted, but rule 'deductive_step' has "
          ++ "allow-trusted = false; a certificate cert(nd@1, …) is required (§4)"
    }
  where
    decls =
      [ DeclClaim (claimD "c" "Q holds" (atom "q" []))
      , DeclLeaf (leafD "e_p" (atom "p" []) Assumed AiExecuted)
      , DeclArg
          ( Arg
              (ArgId "a")
              (SupportsClaim (PropId "c"))
              -- illegal: trusted assurance on an allow-trusted=false rule
              (SRule (RuleId "deductive_step") [] [SLeaf (LeafId "e_p")] [] [] AssuranceTrusted)
          )
      , DeclStatus (PropId "c")
      ]

-- ===========================================================================
-- N9 — DuplicateReportGroupConflict (spec §4.3, R9)
-- ===========================================================================

-- | Two leaves report one measurand cell with conflicting values
-- (@effect(up) ≢ effect(down)@) and are declared a duplicate-report group. The
-- policy escalates conflicts (@duplicate-reports = reject@), so the checker
-- rejects the whole program with a data-integrity diagnostic located at the
-- group declaration (spec §4.3, R9). Under the default @quarantine@ this would
-- instead __accept__ with the dependent claim routed to @gap@ (spec §10.1), so
-- only the escalated form is a negative here — the @quarantine@ counterpart is
-- to R9 what a @quarantine@ leaf is to 'admissionReject' (R8).
duplicateReportGroupConflict :: Negative
duplicateReportGroupConflict =
  Negative
    { negName = "duplicate-report group with ≢ members, escalated to reject"
    , negClass = DuplicateReportGroupConflict
    , negSpecRef = "§4.3"
    , negProgram =
        prog
          "dup-report-v1"
          [ DeclClaim (claimD "c" "the reported effect" (atom "effect" [con "up"]))
          , DeclLeaf (leafD "e1" (atom "effect" [con "up"]) Observed AiExecuted)
          , DeclLeaf (leafD "e2" (atom "effect" [con "down"]) Observed AiExecuted)
          , DeclGroup (DupGroup (GroupId "g1") [LeafId "e1", LeafId "e2"])
          , DeclArg (Arg (ArgId "a") (SupportsClaim (PropId "c")) (SLeaf (LeafId "e1")))
          , DeclStatus (PropId "c")
          ]
    , negPolicy =
        Just $
          Policy
            { policyId = PolicyId "dup-report-v1"
            , policyRules = []
            , policyContraries = []
            , policyExceptions = []
            , policyAdmission = []
            , policyTheories = []
            , policyGroupMode = RejectOnConflict
            , policyMeasurands = []
            , policyComparisonSchemes = []
            }
    , negDiagnostic =
        "group 'g1': members e1, e2 report one cell with ≢ propositions and "
          ++ "the policy escalates conflicts to reject (§4.3)"
    }

-- ---------------------------------------------------------------------------
-- Index
-- ---------------------------------------------------------------------------

-- | Every rejection-class negative, one per 'RejectionClass'.
allNegatives :: [Negative]
allNegatives =
  [ danglingReference
  , supportMismatch
  , premiseMismatch
  , unaccountedQuestion
  , illTypedAttack
  , strictReachableContrary
  , admissionReject
  , strictAssuranceViolation
  , duplicateReportGroupConflict
  ]
