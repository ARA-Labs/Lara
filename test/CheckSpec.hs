-- | Conformance tests for the six-stage checker ("Lara.Check") and the whole
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
module CheckSpec (checkSpecProps) where

import Data.List (nub, sort)
import Test.QuickCheck

import Lara.AST
import Lara.Grounded (AF (..), grounded, iter)
import Lara.Prop (Pred (..), Prop (..), Term (..))
import Lara.Strict (SExpr (..))
import Lara.Wire (Verdict (..), decodeUnitFile, encodeVerdict, printSExpr)
import Lara.Driver (runUnit)

-- ---------------------------------------------------------------------------
-- Golden verdicts (the N11 differential contract, at the Unit boundary)
-- ---------------------------------------------------------------------------

-- | Decode a wire unit and print its verdict, or a codec marker.
verdictString :: String -> String
verdictString s = case decodeUnitFile s of
  Left e -> "CODEC:" ++ show e
  Right u -> printSExpr (encodeVerdict (runUnit u))

coveredSelfEdge :: String
coveredSelfEdge =
  "(unit (policy (rules) (contraries (contrary (apat p) (apat p))) (exceptions))"
    ++ " (leaves (leaf l1 (atom p))) (args (arg a0 (leaf l1)))"
    ++ " (attacks (undermine a0 a0 (pos))) (queries (atom p)))"

missingSelfEdge :: String
missingSelfEdge =
  "(unit (policy (rules) (contraries (contrary (apat p) (apat p))) (exceptions))"
    ++ " (leaves (leaf l1 (atom p))) (args (arg a0 (leaf l1))) (queries (atom p)))"

-- | A two-argument rebut program (the ls20 shape): @a1@ concludes @q@, @a2@
-- concludes @not_q@, the policy declares them contrary, and @a1@ rebuts @a2@.
-- Compiles to the edge 0→1, so @a1@ is @in@ (justified) and @a2@ is @out@
-- (defeated).
rebutProgram :: String
rebutProgram =
  "(unit (policy"
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
      === "(verdict accept (labels (0 undec)) (edges (0 0)) (statuses (status (atom p) contested)))"

prop_goldenMissing :: Property
prop_goldenMissing =
  once $ verdictString missingSelfEdge === "(verdict reject missing-conflict)"

prop_goldenRebut :: Property
prop_goldenRebut =
  once $
    verdictString rebutProgram
      === ( "(verdict accept (labels (0 in) (1 out)) (edges (0 1))"
              ++ " (statuses (status (atom q) justified) (status (atom not_q) defeated)))"
          )

-- ---------------------------------------------------------------------------
-- Rejection-class negatives (one minimal Unit per executable class)
-- ---------------------------------------------------------------------------

rejectionOfUnit :: Unit -> Maybe Rejection
rejectionOfUnit u = case runUnit u of
  VReject r -> Just r
  VAccept{} -> Nothing

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
    { unitRules = rules
    , unitContraries = contraries
    , unitExceptions = exceptions
    , unitTheories = []
    , unitLeaves = ls
    , unitArgs = as
    , unitAttacks = ats
    , unitQueries = qs
    }

defRule :: String -> [String] -> [AtomPat] -> AtomPat -> [Question] -> Rule
defRule rid ps prems concl qs =
  Rule (RuleId rid) (map Param ps) Defeasible prems concl False [] qs

strRule :: String -> [String] -> [AtomPat] -> AtomPat -> Bool -> [CertRef] -> Rule
strRule rid ps prems concl allowT certs =
  Rule (RuleId rid) (map Param ps) Strict prems concl allowT certs []

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
-- class, pinning the six-stage priority order of 'checkUnit'. A stage-order swap
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
--     R1, R3, R4, R5, R6, R7, R10, R11, R12, R13 — plus the four structural
--     program-boundary outcomes duplicate-rule, duplicate-argument,
--     incomplete-argument, missing-conflict.
--   * __Out of the executable core__ (no 'checkUnit' golden by design): R2
--     (signature well-formedness), R8 (leaf admission), R9 (data-integrity /
--     replay identity) — outside the executable acceptance boundary per the
--     'RejectClass' haddock and spec §10.1; and R14 (codec), reported at the
--     wire decode boundary, never as a checker verdict — its rejection matrix
--     lives in "WireSpec" (the malformed-input matrix), not here.
negatives :: [(String, Unit, Rejection)]
negatives =
  [ ("duplicate-rule", negDuplicateRule, DuplicateRule)
  , ("R12 strict-reachable contrary", negR12, RejectClass R12)
  , ("duplicate-argument", negDuplicateArgument, DuplicateArgument)
  , ("incomplete-argument", negIncompleteArgument, IncompleteArgument)
  , ("R1 dangling leaf", negR1, RejectClass R1)
  , ("R3 domain mismatch", negR3, RejectClass R3)
  , ("R4 premise mismatch", negR4, RejectClass R4)
  , ("R5 unaccounted question", negR5, RejectClass R5)
  , ("R6 discharge conclusion mismatch", negR6, RejectClass R6)
  , ("R7 trusted disallowed", negR7, RejectClass R7)
  , ("R10 rebut on leaf occurrence", negR10, RejectClass R10)
  , ("R10 undercut undefined position", negUndercutBadPosition, RejectClass R10)
  , ("R11 rebut missing contrary", negR11, RejectClass R11)
  , ("R11 undercut missing exception", negUndercutMissingException, RejectClass R11)
  , ("R13 backend replay rejected", negR13, RejectClass R13)
  , ("missing-conflict", negMissingConflict, MissingConflict)
  ]

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
prop_mutationBaseAccepts :: Property
prop_mutationBaseAccepts =
  once $
    conjoin
      [ counterexample name (rejectionOfUnit u === Nothing)
      | (name, u) <- [("baseR10", baseR10), ("baseUndercut", baseUndercut)]
      ]

-- | Multi-violation priority (M3 review item 6): a unit carrying two violations
-- at different stages must report the earlier stage's class. Together these pin
-- the full six-stage order of 'checkUnit'; any stage-order swap flips one.
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
  , ("check mutation base accepts", quickCheckResult prop_mutationBaseAccepts)
  , ("check multi-violation stage priority", quickCheckResult prop_multiViolationPriority)
  , ("check fixpoint termination bound", quickCheckResult prop_fixpointBound)
  ]
