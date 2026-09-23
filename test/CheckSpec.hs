-- | Conformance tests for the seven-stage checker ("Lara.Check") and the whole
-- pipeline ("Lara.Driver"), per @docs/engineering-plan.md@ §5.
--
-- Three kinds of test:
--
--   * __Golden verdicts.__ The two frozen wire fixtures
--     (@fixtures/covered-self-edge.sexp@ / @missing-self-edge.sexp@) and one
--     hand-built rebut program are decoded and run end-to-end; the printed
--     verdict must equal the byte string the Lean driver emits (the N11
--     differential contract). These are the "three complete + three rejected"
--     goldens the spec asks for, at the executable 'Unit' boundary.
--   * __Rejection-class negatives.__ One minimal 'Unit' per rejection class the
--     executable checker /decides/ (R1, R3, R4, R5, R7, R12, duplicate-rule,
--     duplicate-argument, incomplete-argument, missing-conflict), asserting the
--     wire 'Rejection' the checker produces. (The spec-taxonomy negatives of
--     "Lara.Negatives" are Program-level and target a different, wider surface —
--     see the Task 1 report.)
--   * __Fixpoint termination bound.__ The grounded iteration reaches a fixed
--     point within @|args|@ steps, over random small frameworks — the same
--     bound as the Lean proof (@grounded_stable@).
module CheckSpec
  ( checkSpecProps
  , negMissingConflict
    -- * Quarantine fixtures, shared with "BlockedSpec" (spec §4.3)
  , quarantineFixtures
  , quarantiningConflictBase
  , unquarantinedFixtures
  ) where

import Data.List (nub, sort)
import Test.QuickCheck

import Lara.AST hiding (Reject)
import Lara.Grounded (AF (..), grounded, iter)
import Lara.Prop (Prop (..), Term (..))
import Lara.Replay
import Lara.Sigma (ConSig (..), PredSig (..), Sigma (..), SigmaFault (..), Sort (..), SortName (..))
import Lara.Strict (SExpr (..))
import Lara.Wire
  ( Outcome (..)
  , PublicStatus (..)
  , Verdict (..)
  , conditionalStatus
  , decodeCheckInputFile
  , decodeUnit
  , encodeReplayId
  , encodeVerdict
  , isPublished
  , parseSExpr
  , printSExpr
  )
import Lara.Check (UnitError (..), checkUnit, fullConfig, unitErrorClass)
import Lara.Driver
  ( buildCertOk
  , buildGamma
  , groupConflictMessage
  , runCheck
  , runCheckLocatedReported
  )
import Lara.Sigma.WellSorted (SortError (..))
import SigmaFixture (sigmaOf)
import TestReplay (testCheckInput, testReplayId)

-- ---------------------------------------------------------------------------
-- Golden verdicts (the N11 differential contract, at the Unit boundary)
-- ---------------------------------------------------------------------------

-- | Decode a low-level wire unit, wrap it in the conformance replay identity,
-- and print its identity-bearing verdict, or a codec marker.
verdictString :: String -> String
verdictString text =
  case parseSExpr text of
    Left err -> "CODEC:" ++ show err
    Right value -> case decodeUnit value of
      Left err -> "CODEC:" ++ show err
      Right unit -> printSExpr (encodeVerdict (runCheck (testCheckInput unit)))

emptyUnit :: Unit
emptyUnit = mkUnit [] [] [] [] [] [] []

testReplayText :: String
testReplayText = printSExpr (encodeReplayId (testReplayId emptyUnit))

-- | The @sigma@ section for a wire literal over nullary predicates only: no
-- declared sorts, no constructors, one @pred@ per atom.
sigmaText :: [String] -> String
sigmaText preds =
  "(sigma (sorts) (cons) (preds"
    ++ concat [" (pred " ++ h ++ " (args))" | h <- preds]
    ++ "))"

coveredSelfEdge :: String
coveredSelfEdge =
  "(unit " ++ sigmaText ["p"]
    ++ " (policy (rules) (contraries (contrary (apat p) (apat p))) (exceptions))"
    ++ " (leaves (leaf l1 (atom p))) (args (arg a0 (leaf l1)))"
    ++ " (attacks (undermine a0 a0 (pos))) (queries (atom p)))"

missingSelfEdge :: String
missingSelfEdge =
  "(unit " ++ sigmaText ["p"]
    ++ " (policy (rules) (contraries (contrary (apat p) (apat p))) (exceptions))"
    ++ " (leaves (leaf l1 (atom p))) (args (arg a0 (leaf l1))) (queries (atom p)))"

-- | A two-argument rebut program (the ls20 shape): @a1@ concludes @q@, @a2@
-- concludes @not_q@, the policy declares them contrary, and @a1@ rebuts @a2@.
-- Compiles to the edge 0→1, so @a1@ is @in@ (justified) and @a2@ is @out@
-- (defeated).
rebutProgram :: String
rebutProgram =
  "(unit " ++ sigmaText ["q", "not_q"]
    ++ " (policy"
    ++ " (rules"
    ++ " (rule r1 (mode defeasible) (params) (premises) (conclusion (apat q))"
    ++ " (questions) (allow-trusted false) (certifiers))"
    ++ " (rule r2 (mode defeasible) (params) (premises) (conclusion (apat not_q))"
    ++ " (questions) (allow-trusted false) (certifiers)))"
    ++ " (contraries (contrary (apat q) (apat not_q))) (exceptions))"
    ++ " (args"
    ++ " (arg a1 (inst r1 (subst) (premises) (discharges) (holes) (assurance none)))"
    ++ " (arg a2 (inst r2 (subst) (premises) (discharges) (holes) (assurance none))))"
    ++ " (attacks (rebut a1 a2))"
    ++ " (queries (atom q) (atom not_q)))"

prop_goldenCovered :: Property
prop_goldenCovered =
  once $
    verdictString coveredSelfEdge
      === ("(verdict " ++ testReplayText ++ " accept (labels (0 undec)) (edges (0 0)) (statuses (status (atom p) contested)))")

prop_goldenMissing :: Property
prop_goldenMissing =
  once $ verdictString missingSelfEdge === ("(verdict " ++ testReplayText ++ " reject missing-conflict)")

prop_goldenRebut :: Property
prop_goldenRebut =
  once $
    verdictString rebutProgram
      === ( "(verdict " ++ testReplayText ++ " accept (labels (0 in) (1 out)) (edges (0 1))"
              ++ " (statuses (status (atom q) justified) (status (atom not_q) defeated)))"
          )

-- ---------------------------------------------------------------------------
-- Rejection-class negatives (one minimal Unit per executable class)
-- ---------------------------------------------------------------------------

rejectionOfUnit :: Unit -> Maybe Rejection
rejectionOfUnit unit = case verdictOutcome (runCheck (testCheckInput unit)) of
  Reject rejection -> Just rejection
  Accept{} -> Nothing

-- | The four-state status of a query atom in an accepted unit (or 'Nothing' if
-- the unit is rejected / the atom is not queried).
--
-- Under §4.3 quarantine this is the __conditional__ label, not the public
-- status: see 'blockedOfUnit'.
statusOfUnit :: Unit -> Prop -> Maybe Status
statusOfUnit unit p = case verdictOutcome (runCheck (testCheckInput unit)) of
  Accept{verdictStatuses = sts} -> conditionalStatus <$> lookup p sts
  Reject{} -> Nothing

-- | The queries whose public status is @evidence-blocked@ (spec §4.3):
-- quarantine edited the program under them, so their four-state label is
-- only a conditional diagnostic.
blockedOfUnit :: Unit -> [Prop]
blockedOfUnit unit = case verdictOutcome (runCheck (testCheckInput unit)) of
  Accept{verdictStatuses = sts} -> [p | (p, st) <- sts, not (isPublished st)]
  Reject{} -> []

-- Small AST builders --------------------------------------------------------

mkUnit
  :: [Rule]
  -> [Contrary]
  -> [Exception]
  -> [(LeafId, Prop)]
  -> [(ArgId, SupportTerm)]
  -> [Attack]
  -> [Prop]
  -> Unit
mkUnit rules contraries exceptions ls as ats qs =
  Unit
    { unitSigma = checkSigma
    , unitRules = rules
    , unitContraries = contraries
    , unitExceptions = exceptions
    , unitTheories = []
    , unitLeaves = ls
    , unitArgs = as
    , unitAttacks = ats
    , unitQueries = qs
    , unitGroups = []
    , unitGroupMode = QuarantineOnConflict
    }

-- | The one signature every fixture in this file is built against
-- (@lara-core\@0.2@, D8). Authored rather than derived: a fixture that
-- accidentally goes ill-sorted must fail stage 2, which is the whole point of
-- the stage.
checkSigma :: Sigma
checkSigma =
  sigmaOf
    ["Item"]
    [("a", [], "Item")]
    ( [("basis", ["Item"]), ("derived", ["Item"]), ("refuted", ["Item"])]
        ++ [("score1", ["Num"]), ("score2", ["Num"])]
        ++ [ (nullary, [])
           | nullary <-
               [ "ans", "att", "base", "c", "concl", "conflictq", "cw", "k"
               , "notk", "other", "p", "pp", "q", "r", "rr", "s", "zz"
               , "not_q"
               ]
           ]
    )

defRule :: String -> [String] -> [AtomPat] -> AtomPat -> [Question] -> Rule
defRule rid ps prems concl qs =
  Rule (RuleId rid) (map Param ps) Defeasible prems [] concl False [] qs

strRule :: String -> [String] -> [AtomPat] -> AtomPat -> Bool -> [CertRef] -> Rule
strRule rid ps prems concl allowT certs =
  Rule (RuleId rid) (map Param ps) Strict prems [] concl allowT certs []

apat0 :: String -> [Pat] -> AtomPat
apat0 name = AtomPat (Pred name)

atom0 :: String -> [Term] -> Prop
atom0 name = Prop (Pred name)

instD :: String -> Subst -> [SupportTerm] -> [(QuestionId, SupportTerm)] -> [ObligationId] -> SupportTerm
instD r theta prems disch holes = SRule (RuleId r) theta prems disch holes AssuranceNone

-- The negatives -------------------------------------------------------------

-- duplicate-rule: two rules share an id.
negDuplicateRule :: Unit
negDuplicateRule =
  mkUnit [rr, rr] [] [] [] [] [] []
  where
    rr = defRule "r" [] [] (apat0 "q" []) []

-- R12: a strict-reachable conclusion appears in a contrary pair (Path B).
negR12 :: Unit
negR12 =
  mkUnit
    [strRule "s" ["X"] [apat0 "basis" [PVar (Param "X")]] (apat0 "derived" [PVar (Param "X")]) True []]
    [Contrary (apat0 "derived" [PVar (Param "X")]) (apat0 "refuted" [PVar (Param "X")])]
    []
    []
    []
    []
    []

-- duplicate-argument: two structurally identical argument terms.
negDuplicateArgument :: Unit
negDuplicateArgument =
  mkUnit [] [] [] [(LeafId "l1", atom0 "p" [])]
    [(ArgId "a0", SLeaf (LeafId "l1")), (ArgId "a1", SLeaf (LeafId "l1"))]
    []
    []

-- incomplete-argument: a mandatory question left open as a hole.
negIncompleteArgument :: Unit
negIncompleteArgument =
  mkUnit
    [defRule "d" [] [] (apat0 "c" []) [Question (QuestionId "q1") (apat0 "ans" []) Mandatory]]
    []
    []
    []
    [(ArgId "a", instD "d" [] [] [] [ObligationId "q1"])]
    []
    [atom0 "c" []]

-- R1: an argument references an undeclared leaf.
negR1 :: Unit
negR1 =
  mkUnit [] [] [] []
    [(ArgId "a", SLeaf (LeafId "e_missing"))]
    []
    [atom0 "c" []]

-- R3: the substitution domain does not equal the rule's parameters.
negR3 :: Unit
negR3 =
  mkUnit
    [defRule "d" ["X"] [] (apat0 "q" []) []]
    []
    []
    []
    [(ArgId "a", instD "d" [(Param "Y", TCon (FunSym "a") [])] [] [] [])]
    []
    [atom0 "q" []]

-- R2, the per-instance half's own witness (§3.2, §10). The rule's patterns
-- are all well-sorted and Gamma is well-sorted, so the STATIC half of stage 2
-- accepts this unit outright; only the theta-range check sees the defect. The
-- rule binds X at `score1(Num)`, so X's derived sort is Num, and the instance
-- binds it to a term of the declared sort Item. The conclusion `derived(X)` is
-- theta-instantiated and matches no leaf, so nothing downstream would catch it
-- either.
--
-- Under a static-only stage 2 this unit would be ACCEPTED. That is the whole
-- argument for the per-instance half existing, and it is pinned here as a test
-- rather than only as a mutant.
negR2Theta :: Unit
negR2Theta =
  mkUnit
    [defRule "d" ["X"] [apat0 "score1" [PVar (Param "X")]] (apat0 "derived" [PVar (Param "X")]) []]
    []
    []
    [(LeafId "l1", atom0 "score1" [TNum "1"])]
    [ ( ArgId "a"
      , instD "d" [(Param "X", TCon (FunSym "a") [])] [SLeaf (LeafId "l1")] [] []
      )
    ]
    []
    []

-- R2: an undeclared predicate head in Gamma. The class boundary (§2.3
-- rule 1) puts an undeclared SYMBOL in R2, not R1: R1 is about declaration
-- identifiers and symbols have never been in its list.
negR2Undeclared :: Unit
negR2Undeclared =
  mkUnit [] [] [] [(LeafId "l1", atom0 "mut_not_declared" [])] [] [] []

-- Σ well-formedness is the first arm of R2. Each constructor below pins one
-- located fault, plus the declaration-order precedence between sort and
-- constructor faults.
sigmaFaultCases :: [(String, Sigma, SigmaFault)]
sigmaFaultCases =
  [ ( "duplicate sort"
    , Sigma [SortName "S", SortName "S"] [] []
    , SFDuplicateSort (SortName "S")
    )
  , ( "base-sort shadow"
    , Sigma [SortName "Num"] [] []
    , SFShadowsBase (SortName "Num")
    )
  , ( "duplicate constructor"
    , Sigma
        [SortName "S"]
        [ ConSig (FunSym "k") [] (SortDecl (SortName "S"))
        , ConSig (FunSym "k") [] (SortDecl (SortName "S"))
        ]
        []
    , SFDuplicateCon (FunSym "k")
    )
  , ( "duplicate predicate"
    , Sigma
        [SortName "S"]
        []
        [ PredSig (Pred "p") []
        , PredSig (Pred "p") []
        ]
    , SFDuplicatePred (Pred "p")
    )
  , ( "constructor names undeclared sort"
    , Sigma [] [ConSig (FunSym "k") [] (SortDecl (SortName "Missing"))] []
    , SFConUndeclaredSort (FunSym "k") (SortName "Missing")
    )
  , ( "predicate names undeclared sort"
    , Sigma [] [] [PredSig (Pred "p") [SortDecl (SortName "Missing")]]
    , SFPredUndeclaredSort (Pred "p") (SortName "Missing")
    )
  , ( "sort fault precedes constructor fault"
    , Sigma
        [SortName "S", SortName "S"]
        [ConSig (FunSym "k") [] (SortDecl (SortName "Missing"))]
        []
    , SFDuplicateSort (SortName "S")
    )
  ]

prop_sigmaWellFormedFaults :: Property
prop_sigmaWellFormedFaults =
  once . conjoin $
    [ counterexample name $
        case checkUnit (buildGamma []) (buildCertOk []) emptyUnit{unitSigma = sg} of
          Left err@(UESignature (SEMalformedSigma actual)) ->
            unitErrorClass err === Just R2
              .&&. actual === expected
          result ->
            counterexample ("expected malformed Σ rejection, got " ++ show result) False
    | (name, sg, expected) <- sigmaFaultCases
    ]

-- R3, NOT R2: a theta key off the rule's parameter list, bound to a term that
-- is itself ill-sorted (an undeclared constructor). Stage 2 must not look at a
-- binding whose key is not a declared parameter — theta's DOMAIN is R3's
-- business (§2.3 rule 3). If stage 2 inspected it, the 19 committed
-- `wrong-subst-domain` mutants would silently become R2 and the paper's
-- per-class table would move.
negR3OffDomainIllSorted :: Unit
negR3OffDomainIllSorted =
  mkUnit
    [defRule "d" ["X"] [] (apat0 "q" []) []]
    []
    []
    []
    [ ( ArgId "a"
      , instD "d" [(Param "Y", TCon (FunSym "not_declared_anywhere") [])] [] [] []
      )
    ]
    []
    [atom0 "q" []]

-- R4: a premise term's conclusion does not match the pattern under theta.
negR4 :: Unit
negR4 =
  mkUnit
    [defRule "d" [] [apat0 "pp" []] (apat0 "q" []) []]
    []
    []
    [(LeafId "e", atom0 "rr" [])]
    [(ArgId "a", instD "d" [] [SLeaf (LeafId "e")] [] [])]
    []
    [atom0 "q" []]

-- R5: a declared mandatory question is neither discharged nor opened.
negR5 :: Unit
negR5 =
  mkUnit
    [defRule "d" [] [] (apat0 "c" []) [Question (QuestionId "q1") (apat0 "ans" []) Mandatory]]
    []
    []
    []
    [(ArgId "a", instD "d" [] [] [] [])]
    []
    [atom0 "c" []]

-- R6: a discharge conclusion does not answer its question's pattern
-- (DischargeReason.ConclusionMismatch). Rule @d@ declares mandatory @q1@ with
-- answer pattern @(apat ans)@; the discharge term concludes @(atom other)@, so
-- the answer check rejects before the R5 accounting pass. Mutating the
-- discharged leaf's atom back to @ans@ makes the same unit accept.
negR6 :: Unit
negR6 =
  mkUnit
    [defRule "d" [] [] (apat0 "c" []) [Question (QuestionId "q1") (apat0 "ans" []) Mandatory]]
    []
    []
    [(LeafId "l_wrong", atom0 "other" [])]
    [(ArgId "a", instD "d" [] [] [(QuestionId "q1", SLeaf (LeafId "l_wrong"))] [])]
    []
    [atom0 "c" []]

-- R7: assurance = trusted on a strict rule with allow-trusted = false.
negR7 :: Unit
negR7 =
  mkUnit
    [strRule "s" [] [apat0 "pp" []] (apat0 "q" []) False [CertRef (BackendId "nd") 1 (TheoryDigest "h")]]
    []
    []
    [(LeafId "e_p", atom0 "pp" [])]
    [(ArgId "a", SRule (RuleId "s") [] [SLeaf (LeafId "e_p")] [] [] AssuranceTrusted)]
    []
    [atom0 "q" []]

-- R10: a rebut targets a leaf occurrence — the wrong occurrence kind (a rebut
-- must target a defeasible rule root, spec §7.1). @a0@ concludes @q@ via a
-- defeasible rule; @a1@ is a bare leaf concluding @p@; @(q, p)@ is contrary.
-- Mutating @a1@ into a defeasible rule instance concluding @p@ makes the rebut
-- type (the R10-valid base 'baseR10').
negR10 :: Unit
negR10 =
  mkUnit
    [defRule "r1" [] [] (apat0 "q" []) []]
    [Contrary (apat0 "q" []) (apat0 "p" [])]
    []
    [(LeafId "l1", atom0 "p" [])]
    [ (ArgId "a0", instD "r1" [] [] [] [])
    , (ArgId "a1", SLeaf (LeafId "l1"))
    ]
    [Rebut (ArgId "a0") (ArgId "a1")]
    [atom0 "q" []]

-- The R10-valid base: @a1@ is a defeasible rule instance, so the rebut targets
-- a defeasible root and types.
baseR10 :: Unit
baseR10 =
  mkUnit
    [ defRule "r1" [] [] (apat0 "q" []) []
    , defRule "r2" [] [] (apat0 "p" []) []
    ]
    [Contrary (apat0 "q" []) (apat0 "p" [])]
    []
    []
    [ (ArgId "a0", instD "r1" [] [] [] [])
    , (ArgId "a1", instD "r2" [] [] [] [])
    ]
    [Rebut (ArgId "a0") (ArgId "a1")]
    [atom0 "q" []]

-- R11: a rebut between two defeasible rule arguments whose conclusions are not
-- a declared contrary pair (AttackRelationReason.MissingContrary). @a0@
-- concludes @q@, @a1@ concludes @p@, and no contrary is declared. Adding the
-- contrary @(q, p)@ recovers 'baseR10' (which accepts).
negR11 :: Unit
negR11 =
  mkUnit
    [ defRule "r1" [] [] (apat0 "q" []) []
    , defRule "r2" [] [] (apat0 "p" []) []
    ]
    []
    []
    []
    [ (ArgId "a0", instD "r1" [] [] [] [])
    , (ArgId "a1", instD "r2" [] [] [] [])
    ]
    [Rebut (ArgId "a0") (ArgId "a1")]
    [atom0 "q" []]

-- R13: a strict cert whose @(backend, digest)@ is certifier-allowed by the rule
-- but the registry cannot replay (the theory digest is absent from the empty
-- theory table). Both drivers reach the backend layer and reject as R13.
-- Supplying the theory and a valid certificate makes it accept.
negR13 :: Unit
negR13 =
  mkUnit
    [strRule "s" [] [apat0 "pp" []] (apat0 "q" []) False
      [CertRef (BackendId "nd") 1 (TheoryDigest "sha256:missing")]]
    []
    []
    [(LeafId "e_p", atom0 "pp" [])]
    [ ( ArgId "a"
      , SRule
          (RuleId "s")
          []
          [SLeaf (LeafId "e_p")]
          []
          []
          ( AssuranceCert
              ( Cert
                  (BackendId "nd")
                  1
                  (TheoryDigest "sha256:missing")
                  (SList [SAtom "hyp", SAtom "0"])
              )
          )
      )
    ]
    []
    [atom0 "q" []]

-- missing-conflict: a self-contrary complete argument with no declared attack.
negMissingConflict :: Unit
negMissingConflict =
  mkUnit [] [Contrary (apat0 "p" []) (apat0 "p" [])] []
    [(LeafId "l1", atom0 "p" [])]
    [(ArgId "a0", SLeaf (LeafId "l1"))]
    []
    [atom0 "p" []]

-- Undercut / exception negatives (M3 review item 2). The existing negatives use
-- only rebut/undermine, so the checker's undercut case and its exception scan
-- had zero coverage: deleting or inverting either stayed green.

-- | An accepting undercut: @r_att@ concludes @att@, @r_tgt@ concludes @c@, and
-- an exception licenses undercutting @r_tgt@ instances whose attacker concludes
-- @att@. This is the valid base the two undercut negatives derive from.
baseUndercut :: Unit
baseUndercut =
  mkUnit
    [ defRule "r_att" [] [] (apat0 "att" []) []
    , defRule "r_tgt" [] [] (apat0 "c" []) []
    ]
    []
    [Exception (RuleId "r_tgt") (apat0 "att" [])]
    []
    [ (ArgId "a0", instD "r_att" [] [] [] [])
    , (ArgId "a1", instD "r_tgt" [] [] [] [])
    ]
    [Undercut (ArgId "a0") (ArgId "a1") []]
    [atom0 "att" [], atom0 "c" []]

-- R11 undercut: 'baseUndercut' with the exception removed, so the exception scan
-- finds no licence (AttackRelationReason.MissingException).
negUndercutMissingException :: Unit
negUndercutMissingException =
  mkUnit
    [ defRule "r_att" [] [] (apat0 "att" []) []
    , defRule "r_tgt" [] [] (apat0 "c" []) []
    ]
    []
    []
    []
    [ (ArgId "a0", instD "r_att" [] [] [] [])
    , (ArgId "a1", instD "r_tgt" [] [] [] [])
    ]
    [Undercut (ArgId "a0") (ArgId "a1") []]
    [atom0 "att" [], atom0 "c" []]

-- R10 undercut: 'baseUndercut' with an out-of-range premise position that does
-- not resolve in the one-node target (AttackPositionReason.UndefinedPosition) —
-- a distinct R10 path from 'negR10''s wrong-occurrence-kind case.
negUndercutBadPosition :: Unit
negUndercutBadPosition =
  mkUnit
    [ defRule "r_att" [] [] (apat0 "att" []) []
    , defRule "r_tgt" [] [] (apat0 "c" []) []
    ]
    []
    [Exception (RuleId "r_tgt") (apat0 "att" [])]
    []
    [ (ArgId "a0", instD "r_att" [] [] [] [])
    , (ArgId "a1", instD "r_tgt" [] [] [] [])
    ]
    [Undercut (ArgId "a0") (ArgId "a1") [StepPremise 5]]
    [atom0 "att" [], atom0 "c" []]

-- Multi-violation units (M3 review item 6): each carries two independent
-- violations at different stages; the checker must report the earlier stage's
-- class, pinning the staged priority order of 'checkUnit'. A stage-order swap
-- flips exactly one of these.

r12Rule :: Rule
r12Rule =
  strRule "s" ["X"] [apat0 "basis" [PVar (Param "X")]] (apat0 "derived" [PVar (Param "X")]) True []

r12Contrary :: Contrary
r12Contrary =
  Contrary (apat0 "derived" [PVar (Param "X")]) (apat0 "refuted" [PVar (Param "X")])

-- stage 1 (duplicate-rule) before stage 2 (R12): both hold; expect duplicate-rule.
mvDupRuleAndR12 :: Unit
mvDupRuleAndR12 = mkUnit [r12Rule, r12Rule] [r12Contrary] [] [] [] [] []

-- stage 2 (R12) before stage 3 (duplicate-argument): both hold; expect R12.
mvR12AndDupArg :: Unit
mvR12AndDupArg =
  mkUnit [r12Rule] [r12Contrary] []
    [(LeafId "l1", atom0 "p" [])]
    [(ArgId "a0", SLeaf (LeafId "l1")), (ArgId "a1", SLeaf (LeafId "l1"))]
    []
    []

-- stage 3 (duplicate-argument) before stage 4 (R1 support): the two identical
-- args both reference an undeclared leaf; expect duplicate-argument.
mvDupArgAndR1 :: Unit
mvDupArgAndR1 =
  mkUnit [] [] [] []
    [(ArgId "a0", SLeaf (LeafId "e_missing")), (ArgId "a1", SLeaf (LeafId "e_missing"))]
    []
    [atom0 "c" []]

-- stage 4 (R1 support) before stage 5 (attacks): @a1@ is an undeclared leaf (R1)
-- and the rebut also targets that leaf occurrence (R10); expect R1.
mvSupportR1AndAttack :: Unit
mvSupportR1AndAttack =
  mkUnit
    [defRule "r1" [] [] (apat0 "q" []) []]
    []
    []
    []
    [ (ArgId "a0", instD "r1" [] [] [] [])
    , (ArgId "a1", SLeaf (LeafId "e_missing"))
    ]
    [Rebut (ArgId "a0") (ArgId "a1")]
    [atom0 "q" []]

-- stage 5 (attacks) before stage 6 (missing-conflict): the @(a0=q, a1=p)@
-- contrary pair is left uncovered (missing-conflict) while the declared rebut
-- @a2 -> a1@ fails R11 (@(s, p)@ not contrary); expect R11.
mvAttackR11AndMissingConflict :: Unit
mvAttackR11AndMissingConflict =
  mkUnit
    [ defRule "r1" [] [] (apat0 "q" []) []
    , defRule "r2" [] [] (apat0 "p" []) []
    , defRule "r3" [] [] (apat0 "s" []) []
    ]
    [Contrary (apat0 "q" []) (apat0 "p" [])]
    []
    []
    [ (ArgId "a0", instD "r1" [] [] [] [])
    , (ArgId "a1", instD "r2" [] [] [] [])
    , (ArgId "a2", instD "r3" [] [] [] [])
    ]
    [Rebut (ArgId "a2") (ArgId "a1")]
    [atom0 "q" []]

-- | One minimal 'Unit' per rejection class the executable checker /decides/.
--
-- R1–R14 coverage of the executable checker (spec §10.1; @src/Lara/AST.hs@
-- 'RejectClass' haddock):
--
--   * __Executable classes__ (decided by 'checkUnit', one golden here each):
--     R1, R2, R3, R4, R5, R6, R7, R10, R11, R12 — plus the four structural
--     program-boundary outcomes duplicate-rule, duplicate-argument,
--     incomplete-argument, missing-conflict.
--   * __Driver-boundary classes__ (decided by 'runCheck' before 'checkUnit',
--     one golden here each): R13 (replay preflight) and R9 (an escalated
--     duplicate-report-group conflict, spec §4.3).
--   * __Outside the executable core__: R8 (leaf admission) and R14 (codec).
--     R14 is reported at the wire decode boundary rather than as a checker
--     verdict; its malformed-input matrix lives in "WireSpec".
negatives :: [(String, Unit, Rejection)]
negatives =
  [ ("duplicate-rule", negDuplicateRule, DuplicateRule)
  , ("R12 strict-reachable contrary", negR12, RejectClass R12)
  , ("duplicate-argument", negDuplicateArgument, DuplicateArgument)
  , ("incomplete-argument", negIncompleteArgument, IncompleteArgument)
  , ("R1 dangling leaf", negR1, RejectClass R1)
  , ("R2 undeclared predicate symbol (not R1)", negR2Undeclared, RejectClass R2)
  , ("R2 theta-range sort (static half alone accepts)", negR2Theta, RejectClass R2)
  , ("R3 domain mismatch", negR3, RejectClass R3)
  , ("R3 off-domain key with an ill-sorted term stays R3", negR3OffDomainIllSorted, RejectClass R3)
  , ("R4 premise mismatch", negR4, RejectClass R4)
  , ("R5 unaccounted question", negR5, RejectClass R5)
  , ("R6 discharge conclusion mismatch", negR6, RejectClass R6)
  , ("R7 trusted disallowed", negR7, RejectClass R7)
  , ("R10 rebut on leaf occurrence", negR10, RejectClass R10)
  , ("R10 undercut undefined position", negUndercutBadPosition, RejectClass R10)
  , ("R11 rebut missing contrary", negR11, RejectClass R11)
  , ("R11 undercut missing exception", negUndercutMissingException, RejectClass R11)
  , ("R13 backend replay rejected", negR13, RejectClass R13)
  , ("R9 duplicate-report-group conflict escalated", negR9, RejectClass R9)
  , ("missing-conflict", negMissingConflict, MissingConflict)
  ]

-- | R9 data-integrity (spec §4.3): a ≢ duplicate-report group under the
-- escalating policy (@duplicate-reports = reject@) is a whole-program reject,
-- decided at the driver boundary before 'checkUnit' — like R13's replay
-- preflight. Members @e1 : p@ and @e2 : q@ are not @≡@.
negR9 :: Unit
negR9 =
  ( mkUnit
      []
      []
      []
      [(LeafId "e1", atom0 "p" []), (LeafId "e2", atom0 "q" [])]
      [(ArgId "a1", SLeaf (LeafId "e1"))]
      []
      [atom0 "p" []]
  )
    { unitGroups = [DupGroup (GroupId "g1") [LeafId "e1", LeafId "e2"]]
    , unitGroupMode = RejectOnConflict
    }

-- | The same ≢ group under the default quarantine policy: it must __accept__
-- (quarantine is not a rejection, spec §10.1). The argument on the quarantined
-- @e1@ is dropped, so the queried claim @p@ has no support and is @gap@.
groupQuarantineUnit :: Unit
groupQuarantineUnit = negR9 {unitGroupMode = QuarantineOnConflict}

-- | A ≡-consistent group (both members @: p@) admits normally, so the argument
-- on @e1@ stands and @p@ is justified.
groupConsistentUnit :: Unit
groupConsistentUnit =
  ( mkUnit
      []
      []
      []
      [(LeafId "e1", atom0 "p" []), (LeafId "e2", atom0 "p" [])]
      [(ArgId "a1", SLeaf (LeafId "e1"))]
      []
      [atom0 "p" []]
  )
    { unitGroups = [DupGroup (GroupId "g1") [LeafId "e1", LeafId "e2"]]
    , unitGroupMode = QuarantineOnConflict
    }

prop_negatives :: Property
prop_negatives =
  once $
    conjoin
      [ counterexample name (rejectionOfUnit u === Just expected)
      | (name, u, expected) <- negatives
      ]

-- | Each mutation class has a valid base the mutant is derived from, so the
-- rejection is attributable to the mutation, not to a broken construction. The
-- R10 and R11 rebut mutants derive from 'baseR10' (a valid two-argument rebut);
-- the two undercut mutants derive from 'baseUndercut' (a valid exception-licensed
-- undercut, which must /accept/ — the positive that pins the checker's undercut
-- case). R6 and R13 mutate the discharge answer / theory table of an otherwise
-- valid unit (their valid forms are exercised elsewhere — R6's answer-matching
-- accept in the support checker, R13's replay accept in "StrictSpec" and the
-- @strict-cert-accept@ differential fixture).
-- | Duplicate-report-group admission (spec §4.3): under the default quarantine
-- policy a ≢ group __accepts__ (quarantine is not a rejection) with its
-- dependent claim @gap@; a ≡-consistent group admits normally (justified). The
-- escalated ≢ case (R9 reject) is pinned in 'negatives'.
prop_groupQuarantine :: Property
prop_groupQuarantine =
  once $
    conjoin
      [ counterexample
          "quarantine is not a rejection"
          (rejectionOfUnit groupQuarantineUnit === Nothing)
      , counterexample
          "quarantined claim routes to gap"
          (statusOfUnit groupQuarantineUnit (atom0 "p" []) === Just Gap)
      , counterexample
          "consistent group admits normally (justified)"
          (statusOfUnit groupConsistentUnit (atom0 "p" []) === Just Justified)
      ]

-- | The exact R9 @stderr@ line both drivers print for 'negR9' (members @e1@,
-- @e2@ of group @g1@). Pins the byte content of 'Lara.Driver.groupConflictMessage'
-- — the differential harness byte-compares this line across drivers, so a drift
-- here would desync them.
prop_groupConflictMessage :: Property
prop_groupConflictMessage =
  once $
    groupConflictMessage negR9
      === Just
        ( "group 'g1': members e1, e2 report one cell with "
            ++ "≢ propositions and the policy escalates conflicts to reject (§4.3)"
        )

-- | Precedence: a preflight replay failure (R13) must win over an escalated
-- group conflict (R9). 'runCheck' gates replay identity before the §4.3 group
-- boundary. This unit fires BOTH — the same ≢ group under @reject@ alone gives
-- R9, but wrapped in a check-input whose selected-backend set omits the arg's
-- certificate backend the preflight fails first and the verdict is R13. Swapping
-- the two guards in 'runCheck' flips the second assertion; the third pins the
-- same precedence on @stderr@ ('Lara.Driver.runCheckLocatedReported'): exactly the
-- R13 line, never the R9 'groupConflictMessage' line, when both fire.
mixedR13AndR9 :: Unit
mixedR13AndR9 =
  negR13
    { unitLeaves = unitLeaves negR13 ++ [(LeafId "e_conflict", atom0 "zz" [])]
    , unitGroups = [DupGroup (GroupId "g1") [LeafId "e_p", LeafId "e_conflict"]]
    , unitGroupMode = RejectOnConflict
    }

-- | The stderr lines the production driver would print, from the same single
-- pass that produces the verdict ('Lara.Driver.runCheckLocatedReported').
reportedDiagnostics :: CheckInput -> [String]
reportedDiagnostics input =
  let (_, _, diagnostics) = runCheckLocatedReported fullConfig input
   in diagnostics

prop_groupPrecedenceR13BeatsR9 :: Property
prop_groupPrecedenceR13BeatsR9 =
  once $
    conjoin
      [ counterexample
          "the ≢ group alone escalates to R9 (no preflight failure)"
          (rejectionOfUnit mixedR13AndR9 === Just (RejectClass R9))
      , counterexample
          "preflight R13 wins over R9 when both fire"
          (verdictOutcome (runCheck mixedInput) === Reject (RejectClass R13))
      , counterexample
          "stderr precedence: exactly the R13 line, never the R9 line"
          ( case runtimeReplayFailure mixedInput of
              Nothing -> counterexample "expected a preflight failure" (property False)
              Just failure ->
                reportedDiagnostics mixedInput === [replayFailureMessage failure]
          )
      ]
  where
    mixedReplayId =
      either (error . replayErrorMessage) id $
        mkReplayId
          LaraCoreV02
          (PolicyId "conformance-v1")
          []
          []
          (Digest "sha256:conformance-corpus-v1")
    mixedInput =
      either (error . replayErrorMessage) id (mkCheckInput mixedReplayId mixedR13AndR9)

-- | Quarantine drops an argument whose support term uses a conflicted leaf
-- __nested inside a rule instance__ (exercising 'Lara.Driver.supportUsesLeaf's
-- recursion into rule premises), together with any attack that targets the
-- dropped argument (exercising 'Lara.Driver.quarantineUnit's attack pruning).
-- @a1@'s support is a rule instance whose premise is the quarantined leaf @e1@;
-- @a2@ (a surviving leaf) rebuts @a1@. Under quarantine both @a1@ and the rebut
-- are pruned before 'checkUnit', so the unit accepts (no dangling-endpoint
-- error) and @a1@'s conclusion is @gap@.
groupQuarantineDropsArgUnit :: Unit
groupQuarantineDropsArgUnit =
  ( mkUnit
      [defRule "r" [] [apat0 "p" []] (apat0 "concl" []) []]
      [Contrary (apat0 "concl" []) (apat0 "base" [])]
      []
      [ (LeafId "e1", atom0 "p" [])
      , (LeafId "e2", atom0 "q" [])
      , (LeafId "e3", atom0 "base" [])
      ]
      [ (ArgId "a1", instD "r" [] [SLeaf (LeafId "e1")] [] [])
      , (ArgId "a2", SLeaf (LeafId "e3"))
      ]
      [Rebut (ArgId "a2") (ArgId "a1")]
      [atom0 "concl" []]
  )
    { unitGroups = [DupGroup (GroupId "g1") [LeafId "e1", LeafId "e2"]]
    , unitGroupMode = QuarantineOnConflict
    }

prop_groupQuarantineDropsArgAndAttack :: Property
prop_groupQuarantineDropsArgAndAttack =
  once $
    conjoin
      [ counterexample
          "accepts: the dropped arg's rebut is pruned, no dangling endpoint"
          (rejectionOfUnit groupQuarantineDropsArgUnit === Nothing)
      , counterexample
          "the claim behind the dropped rule-instance arg is gap"
          (statusOfUnit groupQuarantineDropsArgUnit (atom0 "concl" []) === Just Gap)
      ]

-- | __The promotion hazard (spec §4.3).__ The mirror image of
-- 'groupQuarantineDropsArgUnit': here the conflicted leaf backs the
-- __attacker__, not the target.
--
-- @a1@ (rule instance on @e1 : p@) concludes @concl@ and is rebutted by @a2@
-- (leaf @e2 : base@). @e2@ is grouped with @e3 : q@, so the group is @≢@ and
-- @e2@ is quarantined — taking @a2@ and its rebut with it. The checker then sees
-- an /unattacked/ @a1@ and labels @concl@ @justified@: deleting the unavailable
-- attacker made the claim look stronger than the declared program supports.
--
-- @other@ is queried too and is out of the edit's reach, so it must keep its
-- ordinary status — the blocking rule is directed, not "block everything".
groupQuarantinePromotionUnit :: Unit
groupQuarantinePromotionUnit =
  ( mkUnit
      [defRule "r" [] [apat0 "p" []] (apat0 "concl" []) []]
      [Contrary (apat0 "concl" []) (apat0 "base" [])]
      []
      [ (LeafId "e1", atom0 "p" [])
      , (LeafId "e2", atom0 "base" [])
      , (LeafId "e3", atom0 "q" [])
      , (LeafId "e4", atom0 "other" [])
      ]
      [ (ArgId "a1", instD "r" [] [SLeaf (LeafId "e1")] [] [])
      , (ArgId "a2", SLeaf (LeafId "e2"))
      , (ArgId "a3", SLeaf (LeafId "e4"))
      ]
      [Rebut (ArgId "a2") (ArgId "a1")]
      [atom0 "concl" [], atom0 "other" []]
  )
    { unitGroups = [DupGroup (GroupId "g1") [LeafId "e2", LeafId "e3"]]
    , unitGroupMode = QuarantineOnConflict
    }

-- | Quarantining the sole attacker must not promote its target's public status
-- (spec §4.3; Lean @Lara.Blocked.justified_nonpromotion@).
--
-- The first two cases pin that the hazard is real — the unit accepts and the
-- pruned graph really does label @concl@ @justified@ — and the third pins that
-- the label is published as @evidence-blocked@ rather than as the answer. The
-- last two are the completeness half: an unrelated claim keeps its ordinary
-- status, so the directed rule does not block the whole program.
prop_groupQuarantineNoPromotion :: Property
prop_groupQuarantineNoPromotion =
  once $
    conjoin
      [ counterexample
          "accepts: quarantine is not a rejection"
          (rejectionOfUnit groupQuarantinePromotionUnit === Nothing)
      , counterexample
          "the pruned graph would promote the target to justified"
          (statusOfUnit groupQuarantinePromotionUnit (atom0 "concl" []) === Just Justified)
      , counterexample
          "so the target is published evidence-blocked, not justified"
          (blockedOfUnit groupQuarantinePromotionUnit === [atom0 "concl" []])
      , counterexample
          "the unrelated claim is not blocked"
          (notElem (atom0 "other" []) (blockedOfUnit groupQuarantinePromotionUnit))
      , counterexample
          "the unrelated claim keeps its ordinary status"
          (statusOfUnit groupQuarantinePromotionUnit (atom0 "other" []) === Just Justified)
      ]

-- | The wire bytes of the hazard verdict: @concl@ prints @evidence-blocked@ in
-- the @statuses@ section and its conditional label moves to the @conditional@
-- section, while the unaffected @other@ prints its ordinary status.
prop_goldenQuarantineBlocked :: Property
prop_goldenQuarantineBlocked =
  once $
    printSExpr (encodeVerdict (runCheck (testCheckInput groupQuarantinePromotionUnit)))
      === ( "(verdict " ++ testReplayText ++ " accept (labels (0 in) (1 in))"
              ++ " (edges)"
              ++ " (statuses (status (atom concl) evidence-blocked)"
              ++ " (status (atom other) justified))"
              ++ " (conditional (status (atom concl) justified)))"
          )

-- | Production-driver regression for ordered multi-query blocking. The
-- numeric supports deliberately mix surface spellings, so this simultaneously
-- pins canonical claim support and the blocked / published / blocked ordering
-- at the public 'runCheck' boundary.
prop_numericMultiBlockedDriver :: Property
prop_numericMultiBlockedDriver = once (ioProperty check)
  where
    path = "fixtures/corpus/group-quarantine-numeric-multi-blocked.sexp"
    check = do
      bytes <- readFile path
      pure $ case decodeCheckInputFile bytes of
        Left err -> counterexample (path ++ ": CODEC:" ++ show err) False
        Right input -> case verdictOutcome (runCheck input) of
          Reject rejection -> counterexample (path ++ ": " ++ show rejection) False
          Accept{verdictStatuses = statuses} ->
            statuses
              === [ (atom0 "score1" [TNum "1"], EvidenceBlocked Justified)
                  , (atom0 "other" [], Published Justified)
                  , (atom0 "score2" [TNum "2"], EvidenceBlocked Justified)
                  ]

-- | __The lost-edge hazard (spec §4.3).__ Quarantine removes an
-- argument, and with it every attack that named the argument as an endpoint —
-- but under subargument closure such an attack also carried edges onto /other/
-- arguments containing the attacked occurrence. Dropping it therefore deletes an
-- edge between two __retained__ arguments, which is the second, less obvious way
-- a prune can promote a claim.
--
-- The construction has to dodge attack completeness, which is what makes the
-- case subtle. @aS@ (leaf @La : notk@) undermines @aT@ at its @Lk@ premise;
-- @aT@ also uses the quarantined @Lq@, so the prune removes @aT@ and the
-- undermine with it. @aW@ is a /retained/ argument that also contains @SLeaf Lk@
-- as a premise, so subargument closure gave it an incoming edge from @aS@ too —
-- and now silently loses it. Completeness does not catch this: it compares whole
-- conclusions (@notk@ vs @cw@), which are not contraries, so the pruned program
-- accepts. Attacking a retained argument whose /conclusion/ is @k@ would instead
-- be rejected as @missing-conflict@ — see 'groupQuarantineLostEdgeCompleteUnit'.
groupQuarantineLostEdgeUnit :: Unit
groupQuarantineLostEdgeUnit =
  ( mkUnit
      [ defRule "r" [] [apat0 "q" [], apat0 "k" []] (apat0 "concl" []) []
      , defRule "rw" [] [apat0 "k" []] (apat0 "cw" []) []
      ]
      [Contrary (apat0 "k" []) (apat0 "notk" [])]
      []
      [ (LeafId "Lq", atom0 "q" [])
      , (LeafId "Lk", atom0 "k" [])
      , (LeafId "Lc", atom0 "conflictq" [])
      , (LeafId "La", atom0 "notk" [])
      ]
      [ (ArgId "aT", instD "r" [] [SLeaf (LeafId "Lq"), SLeaf (LeafId "Lk")] [] [])
      , (ArgId "aW", instD "rw" [] [SLeaf (LeafId "Lk")] [] [])
      , (ArgId "aS", SLeaf (LeafId "La"))
      ]
      [Undermine (ArgId "aS") (ArgId "aT") [StepPremise 1]]
      [atom0 "cw" []]
  )
    { unitGroups = [DupGroup (GroupId "g1") [LeafId "Lq", LeafId "Lc"]]
    , unitGroupMode = QuarantineOnConflict
    }

-- | The same shape with the undermined leaf declared as its own argument, so the
-- lost edge is one attack completeness /does/ require: the pruned program is
-- rejected as @missing-conflict@ rather than accepted with a promoted status.
-- Together with 'groupQuarantineLostEdgeUnit' this pins both halves — when the
-- lost edge carries a conflict the checker refuses the program, and when it does
-- not, the blocked set has to catch it.
groupQuarantineLostEdgeCompleteUnit :: Unit
groupQuarantineLostEdgeCompleteUnit =
  groupQuarantineLostEdgeUnit
    { unitArgs = unitArgs groupQuarantineLostEdgeUnit ++ [(ArgId "aK", SLeaf (LeafId "Lk"))]
    , unitQueries = [atom0 "k" []]
    }

-- | Quarantine must not promote a claim by deleting an attack /edge/ rather than
-- an attack's target (spec §4.3). Seeding only the removed arguments
-- fails this focused property; the corpus differential independently guards the
-- same retained-to-retained lost-edge path.
prop_groupQuarantineLostEdge :: Property
prop_groupQuarantineLostEdge =
  once $
    conjoin
      [ counterexample
          "accepts: quarantine is not a rejection"
          (rejectionOfUnit groupQuarantineLostEdgeUnit === Nothing)
      , counterexample
          "the pruned graph would promote the argument that lost an edge"
          (statusOfUnit groupQuarantineLostEdgeUnit (atom0 "cw" []) === Just Justified)
      , counterexample
          "so it is published evidence-blocked: it lost an attacker it never declared gone"
          (blockedOfUnit groupQuarantineLostEdgeUnit === [atom0 "cw" []])
      , counterexample
          "a lost edge that carries a conflict is refused by attack completeness"
          (rejectionOfUnit groupQuarantineLostEdgeCompleteUnit === Just MissingConflict)
      ]

-- | The units in this module that exercise a §4.3 prune, shared with
-- "BlockedSpec" so the blocked-set obligations are checked on the same
-- fixtures the status properties above pin.
quarantineFixtures :: [(String, Unit)]
quarantineFixtures =
  [ ("group-quarantine", groupQuarantineUnit)
  , ("group-quarantine-drops-arg", groupQuarantineDropsArgUnit)
  , ("group-quarantine-promotion", groupQuarantinePromotionUnit)
  , ("group-quarantine-lost-edge", groupQuarantineLostEdgeUnit)
  , ("quarantining-conflict", quarantiningConflictBase)
  ]

-- | Units with no @≢@ group: quarantine prunes nothing, so nothing may be
-- blocked and their verdict bytes are the pre-conservative-reporting ones.
unquarantinedFixtures :: [(String, Unit)]
unquarantinedFixtures =
  [ ("group-consistent", groupConsistentUnit)
  , ("group3-consistent", group3ConsistentUnit)
  , ("R10 rebut on leaf occurrence", negR10)
  , ("missing-conflict", negMissingConflict)
  ]

-- | A base whose §4.3 quarantine is not the identity: the leaf group
-- @g1@ is inconsistent (@q@ vs @conflictq@), so quarantine removes @Lq@, the
-- argument @aQ@ built on it, and the declared attack that names @aQ@ as an
-- endpoint. What survives is the minimal covering shape: @aS@ (@notk@)
-- undermines @aK@ (@k@) at its root leaf, the sole cover of the one declared
-- contrary pair. Both index spaces are skewed on purpose — declared argument 0
-- and declared attack 0 are pruned — so checked indices differ from declared
-- indices for every constituent the enumerator touches.
quarantiningConflictBase :: Unit
quarantiningConflictBase =
  Unit
    { unitSigma = sigmaOf [] [] [("q", []), ("conflictq", []), ("k", []), ("notk", [])]
    , unitRules = []
    , unitContraries = [Contrary (AtomPat (Pred "notk") []) (AtomPat (Pred "k") [])]
    , unitExceptions = []
    , unitTheories = []
    , unitLeaves =
        [ (LeafId "Lq", nullary "q")
        , (LeafId "Lc", nullary "conflictq")
        , (LeafId "La", nullary "notk")
        , (LeafId "Lk", nullary "k")
        ]
    , unitArgs =
        [ (ArgId "aQ", SLeaf (LeafId "Lq"))
        , (ArgId "aS", SLeaf (LeafId "La"))
        , (ArgId "aK", SLeaf (LeafId "Lk"))
        ]
    , unitAttacks =
        [ Undermine (ArgId "aS") (ArgId "aQ") []
        , Undermine (ArgId "aS") (ArgId "aK") []
        ]
    , unitQueries = [nullary "k"]
    , unitGroups = [DupGroup (GroupId "g1") [LeafId "Lq", LeafId "Lc"]]
    , unitGroupMode = QuarantineOnConflict
    }
  where
    nullary n = Prop (Pred n) []

-- | A ≡-consistent group of __three__ members admits normally (all @: p@).
group3ConsistentUnit :: Unit
group3ConsistentUnit =
  ( mkUnit
      []
      []
      []
      [ (LeafId "e1", atom0 "p" [])
      , (LeafId "e2", atom0 "p" [])
      , (LeafId "e3", atom0 "p" [])
      ]
      [(ArgId "a1", SLeaf (LeafId "e1"))]
      []
      [atom0 "p" []]
  )
    { unitGroups = [DupGroup (GroupId "g1") [LeafId "e1", LeafId "e2", LeafId "e3"]]
    , unitGroupMode = RejectOnConflict
    }

-- | The same three-member group with __partial__ agreement (@e1@, @e2 : p@ but
-- @e3 : q@) is a conflict — pairwise-≡ fails on @e3@ — so under @reject@ it is R9.
group3PartialConflictUnit :: Unit
group3PartialConflictUnit =
  group3ConsistentUnit
    { unitLeaves =
        [ (LeafId "e1", atom0 "p" [])
        , (LeafId "e2", atom0 "p" [])
        , (LeafId "e3", atom0 "q" [])
        ]
    }

-- | Two independent groups: @g1@ (@e1@, @e2 : p@) is consistent, @g2@ (@e3 : q@,
-- @e4 : r@) is not. A conflict in @g2@ must not quarantine @g1@'s members, so the
-- claim on @e1@ stays justified while the claim on @e3@ is @gap@.
multiGroupUnit :: Unit
multiGroupUnit =
  ( mkUnit
      []
      []
      []
      [ (LeafId "e1", atom0 "p" [])
      , (LeafId "e2", atom0 "p" [])
      , (LeafId "e3", atom0 "q" [])
      , (LeafId "e4", atom0 "r" [])
      ]
      [ (ArgId "a1", SLeaf (LeafId "e1"))
      , (ArgId "a2", SLeaf (LeafId "e3"))
      ]
      []
      [atom0 "p" [], atom0 "q" []]
  )
    { unitGroups =
        [ DupGroup (GroupId "g1") [LeafId "e1", LeafId "e2"]
        , DupGroup (GroupId "g2") [LeafId "e3", LeafId "e4"]
        ]
    , unitGroupMode = QuarantineOnConflict
    }

prop_groupMultiMemberAndMultiGroup :: Property
prop_groupMultiMemberAndMultiGroup =
  once $
    conjoin
      [ counterexample
          "3-member all-≡ group admits (justified)"
          (statusOfUnit group3ConsistentUnit (atom0 "p" []) === Just Justified)
      , counterexample
          "3-member partial agreement is a conflict (R9 under reject)"
          (rejectionOfUnit group3PartialConflictUnit === Just (RejectClass R9))
      , counterexample
          "independent groups: the consistent group's claim stays justified"
          (statusOfUnit multiGroupUnit (atom0 "p" []) === Just Justified)
      , counterexample
          "independent groups: only the conflicted group quarantines (gap)"
          (statusOfUnit multiGroupUnit (atom0 "q" []) === Just Gap)
      ]

prop_mutationBaseAccepts :: Property
prop_mutationBaseAccepts =
  once $
    conjoin
      [ counterexample name (rejectionOfUnit u === Nothing)
      | (name, u) <- [("baseR10", baseR10), ("baseUndercut", baseUndercut)]
      ]

-- | Multi-violation priority (M3 review item 6): a unit carrying two violations
-- at different stages must report the earlier stage's class. Together these pin
-- the established stage boundaries of 'checkUnit'; any covered swap flips one.
multiViolationNegatives :: [(String, Unit, Rejection)]
multiViolationNegatives =
  [ ("stage 1<2: duplicate-rule beats R12", mvDupRuleAndR12, DuplicateRule)
  , ("stage 2<3: R12 beats duplicate-argument", mvR12AndDupArg, RejectClass R12)
  , ("stage 3<4: duplicate-argument beats R1 support", mvDupArgAndR1, DuplicateArgument)
  , ("stage 4<5: R1 support beats attack error", mvSupportR1AndAttack, RejectClass R1)
  , ("stage 5<6: attack R11 beats missing-conflict", mvAttackR11AndMissingConflict, RejectClass R11)
  ]

prop_multiViolationPriority :: Property
prop_multiViolationPriority =
  once $
    conjoin
      [ counterexample name (rejectionOfUnit u === Just expected)
      | (name, u, expected) <- multiViolationNegatives
      ]

prop_verdictsCarryExactlyOneReplayId :: Property
prop_verdictsCarryExactlyOneReplayId =
  once $
    conjoin
      [ counterexample "ordinary R1 verdict replay-id section" $
          replaySectionCount (runCheck (testCheckInput negR1)) === 1
      , counterexample "preflight R13 verdict replay-id section" $
          replaySectionCount (runCheck preflightInput) === 1
      , counterexample "preflight outcome is R13" $
          verdictOutcome (runCheck preflightInput) === Reject (RejectClass R13)
      ]
  where
    preflightReplayId =
      either (error . replayErrorMessage) id $
        mkReplayId
          LaraCoreV02
          (PolicyId "conformance-v1")
          []
          []
          (Digest "sha256:conformance-corpus-v1")
    preflightInput =
      either (error . replayErrorMessage) id (mkCheckInput preflightReplayId negR13)
    replaySectionCount verdict =
      case encodeVerdict verdict of
        SList (SAtom "verdict" : fields) ->
          length
            [ ()
            | SList (SAtom "replay-id" : _) <- fields
            ]
        _ -> 0

-- ---------------------------------------------------------------------------
-- Fixpoint termination bound (Lean @grounded_stable@)
-- ---------------------------------------------------------------------------

-- | A random small framework: @n@ nodes and a random edge set within range.
genFramework :: Gen (Int, [(Int, Int)])
genFramework = do
  n <- choose (0, 5)
  edges <-
    if n == 0
      then pure []
      else smallListOf ((,) <$> choose (0, n - 1) <*> choose (0, n - 1))
  pure (n, edges)

smallListOf :: Gen a -> Gen [a]
smallListOf g = do
  k <- choose (0, 6 :: Int)
  vectorOf k g

sameSet :: [Int] -> [Int] -> Bool
sameSet a b = sort (nub a) == sort (nub b)

-- | The grounded iteration reaches a fixed point within @|args|@ steps, and the
-- extension stays within the carrier.
prop_fixpointBound :: Property
prop_fixpointBound =
  forAll genFramework $ \(n, edges) ->
    let f = AF [0 .. n - 1] (\i j -> (i, j) `elem` edges)
     in counterexample (show (n, edges)) $
          sameSet (iter f n) (iter f (n + 1))
            .&&. property (all (`elem` [0 .. n - 1]) (grounded f))

-- ---------------------------------------------------------------------------
-- Index
-- ---------------------------------------------------------------------------

checkSpecProps :: [(String, IO Result)]
checkSpecProps =
  [ ("check golden covered-self-edge", quickCheckResult prop_goldenCovered)
  , ("check golden missing-self-edge", quickCheckResult prop_goldenMissing)
  , ("check golden rebut program", quickCheckResult prop_goldenRebut)
  , ("check rejection-class negatives", quickCheckResult prop_negatives)
  , ("check Sigma well-formedness fault matrix", quickCheckResult prop_sigmaWellFormedFaults)
  , ("check duplicate-report-group quarantine/gap", quickCheckResult prop_groupQuarantine)
  , ("check duplicate-report-group R9 stderr message", quickCheckResult prop_groupConflictMessage)
  , ("check duplicate-report-group R13-over-R9 precedence", quickCheckResult prop_groupPrecedenceR13BeatsR9)
  , ("check duplicate-report-group quarantine drops arg+attack", quickCheckResult prop_groupQuarantineDropsArgAndAttack)
  , ("check quarantined attacker cannot promote its target", quickCheckResult prop_groupQuarantineNoPromotion)
  , ("check golden evidence-blocked verdict", quickCheckResult prop_goldenQuarantineBlocked)
  , ("check production driver preserves multi-blocked query positions", quickCheckResult prop_numericMultiBlockedDriver)
  , ("check quarantine cannot promote by deleting an attack edge", quickCheckResult prop_groupQuarantineLostEdge)
  , ("check duplicate-report-group multi-member and multi-group", quickCheckResult prop_groupMultiMemberAndMultiGroup)
  , ("check mutation base accepts", quickCheckResult prop_mutationBaseAccepts)
  , ("check multi-violation stage priority", quickCheckResult prop_multiViolationPriority)
  , ("check verdicts carry exactly one replay-id", quickCheckResult prop_verdictsCarryExactlyOneReplayId)
  , ("check fixpoint termination bound", quickCheckResult prop_fixpointBound)
  ]
