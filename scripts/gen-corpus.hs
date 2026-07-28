-- | Corpus generator for the differential harness (M3 plan D8).
--
-- Constructs each conformance-corpus 'Unit' as a real symbolic-core value and
-- writes @fixtures/corpus/<name>.sexp@ = @printSExpr (encodeUnit u)@ — the
-- canonical wire text both drivers decode. This is the provenance record for
-- the corpus: the wire denotes exactly the 'Unit' value defined here.
--
-- Run with the built library on the path:
--
-- >  cabal exec -- runghc scripts/gen-corpus.hs
--
-- The both-drivers differential harness ('scripts/differential.sh') is the
-- oracle: it confirms the Lean executable semantics agrees byte-exact with the
-- Haskell driver on every generated fixture. Any disagreement is a bug, fixed
-- with a recorded note — never a silent re-annotation of the expected verdict.
--
-- Numeric-literal caveat: the Lean driver runs at @canon = id@ and does not
-- canonicalize numbers, while the Haskell core does. Every corpus unit below
-- therefore avoids non-canonical numeric literals (the atoms are nullary or
-- constructor atoms; no @num@ terms appear), so the two drivers cannot diverge
-- on numeric canonicalization.
module Main (main) where

import Lara.AST
import Lara.Prop (Prop (..), Term (..))
import Lara.Strict (SExpr (..))
import Lara.Wire (encodeUnit, printSExpr)

-- ---------------------------------------------------------------------------
-- Small AST builders (mirror test/CheckSpec.hs)
-- ---------------------------------------------------------------------------

mkUnit
  :: [Rule] -> [Contrary] -> [Exception]
  -> [(LeafId, Prop)] -> [(ArgId, SupportTerm)] -> [Attack] -> [Prop] -> Unit
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

-- ---------------------------------------------------------------------------
-- The corpus
-- ---------------------------------------------------------------------------

-- Accepts ------------------------------------------------------------------

-- | The two-argument rebut program (ls20 shape): a1 concludes q, a2 concludes
-- not_q, contrary (q, not_q), a1 rebuts a2. Edge 0->1: a1 in, a2 out.
rebutProgram :: Unit
rebutProgram =
  mkUnit
    [ defRule "r1" [] [] (apat0 "q" []) []
    , defRule "r2" [] [] (apat0 "not_q" []) []
    ]
    [Contrary (apat0 "q" []) (apat0 "not_q" [])]
    []
    []
    [ (ArgId "a1", instD "r1" [] [] [] [])
    , (ArgId "a2", instD "r2" [] [] [] [])
    ]
    [Rebut (ArgId "a1") (ArgId "a2")]
    [atom0 "q" [], atom0 "not_q" []]

-- | Three independent leaf arguments over distinct atoms and no contraries: all
-- accepted, all @in@, all @justified@. No numeric literals.
independentAccept :: Unit
independentAccept =
  mkUnit [] [] []
    [(LeafId "l0", atom0 "p0" []), (LeafId "l1", atom0 "p1" []), (LeafId "l2", atom0 "p2" [])]
    [(ArgId "a0", SLeaf (LeafId "l0")), (ArgId "a1", SLeaf (LeafId "l1")), (ArgId "a2", SLeaf (LeafId "l2"))]
    []
    [atom0 "p0" [], atom0 "p1" [], atom0 "p2" []]

-- | Default-heartbeat stress: 120 independent leaf arguments over distinct
-- atoms, all queried. Exercises 120-argument support checking, the O(n^2)
-- missing-conflict scan (all pairs, none contrary), and grounded iteration over
-- 120 isolated nodes. All @in@ / @justified@. No numeric literals. This is the
-- end-to-end (checkUnit + grounded + statuses) analogue of the Lean
-- @AttackCompleteness.stressArgs@ fixture, scaled past 100 arguments.
stressUnit :: Int -> Unit
stressUnit n =
  mkUnit [] [] []
    [(LeafId ("l" ++ show i), atom0 ("p" ++ show i) []) | i <- [0 .. n - 1]]
    [(ArgId ("a" ++ show i), SLeaf (LeafId ("l" ++ show i))) | i <- [0 .. n - 1]]
    []
    [atom0 ("p" ++ show i) [] | i <- [0 .. n - 1]]

-- Structural rejects -------------------------------------------------------

negDuplicateRule :: Unit
negDuplicateRule = mkUnit [rr, rr] [] [] [] [] [] []
  where rr = defRule "r" [] [] (apat0 "q" []) []

negDuplicateArgument :: Unit
negDuplicateArgument =
  mkUnit [] [] [] [(LeafId "l1", atom0 "p" [])]
    [(ArgId "a0", SLeaf (LeafId "l1")), (ArgId "a1", SLeaf (LeafId "l1"))]
    [] []

negIncompleteArgument :: Unit
negIncompleteArgument =
  mkUnit
    [defRule "d" [] [] (apat0 "c" []) [Question (QuestionId "q1") (apat0 "ans" []) Mandatory]]
    [] [] []
    [(ArgId "a", instD "d" [] [] [] [ObligationId "q1"])]
    []
    [atom0 "c" []]

negMissingConflict :: Unit
negMissingConflict =
  mkUnit [] [Contrary (apat0 "p" []) (apat0 "p" [])] []
    [(LeafId "l1", atom0 "p" [])]
    [(ArgId "a0", SLeaf (LeafId "l1"))]
    []
    [atom0 "p" []]

-- Frozen-class rejects -----------------------------------------------------

-- R12: a strict-reachable conclusion appears in a contrary pair.
negR12 :: Unit
negR12 =
  mkUnit
    [strRule "s" ["X"] [apat0 "basis" [PVar (Param "X")]] (apat0 "derived" [PVar (Param "X")]) True []]
    [Contrary (apat0 "derived" [PVar (Param "X")]) (apat0 "refuted" [PVar (Param "X")])]
    [] [] [] [] []

-- R1: an argument references an undeclared leaf.
negR1 :: Unit
negR1 =
  mkUnit [] [] [] []
    [(ArgId "a", SLeaf (LeafId "e_missing"))]
    []
    [atom0 "c" []]

-- R3: substitution domain does not equal the rule's parameters.
negR3 :: Unit
negR3 =
  mkUnit [defRule "d" ["X"] [] (apat0 "q" []) []] [] [] []
    [(ArgId "a", instD "d" [(Param "Y", TCon (FunSym "a") [])] [] [] [])]
    []
    [atom0 "q" []]

-- R4: a premise term's conclusion does not match the pattern under theta.
negR4 :: Unit
negR4 =
  mkUnit [defRule "d" [] [apat0 "pp" []] (apat0 "q" []) []] [] []
    [(LeafId "e", atom0 "rr" [])]
    [(ArgId "a", instD "d" [] [SLeaf (LeafId "e")] [] [])]
    []
    [atom0 "q" []]

-- R5: a declared mandatory question is neither discharged nor opened.
negR5 :: Unit
negR5 =
  mkUnit
    [defRule "d" [] [] (apat0 "c" []) [Question (QuestionId "q1") (apat0 "ans" []) Mandatory]]
    [] [] []
    [(ArgId "a", instD "d" [] [] [] [])]
    []
    [atom0 "c" []]

-- R6: a discharge's conclusion does not answer its question's pattern.
-- Rule d has mandatory q1 with answer pattern (apat ans); the discharge term
-- concludes (atom other), so the answer check (DischargeReason.conclusionMismatch)
-- rejects before the R5 accounting pass.
negR6 :: Unit
negR6 =
  mkUnit
    [defRule "d" [] [] (apat0 "c" []) [Question (QuestionId "q1") (apat0 "ans" []) Mandatory]]
    [] []
    [(LeafId "l_wrong", atom0 "other" [])]
    [(ArgId "a", instD "d" [] [] [(QuestionId "q1", SLeaf (LeafId "l_wrong"))] [])]
    []
    [atom0 "c" []]

-- R7: assurance = trusted on a strict rule with allow-trusted = false.
negR7 :: Unit
negR7 =
  mkUnit
    [strRule "s" [] [apat0 "pp" []] (apat0 "q" []) False [CertRef (BackendId "nd") 1 (TheoryDigest "h")]]
    [] []
    [(LeafId "e_p", atom0 "pp" [])]
    [(ArgId "a", SRule (RuleId "s") [] [SLeaf (LeafId "e_p")] [] [] AssuranceTrusted)]
    []
    [atom0 "q" []]

-- R10: a rebut targets a leaf occurrence (wrong occurrence kind: expected a
-- defeasible rule root, got a leaf). a0 = inst r1 (concludes q); a1 = leaf
-- (atom p); contrary (q, p) declared; rebut a0 a1.
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

-- R11: a rebut between two defeasible rule arguments whose conclusions are not
-- a declared contrary pair (attack-relation failure: MissingContrary). a0
-- concludes q, a1 concludes p, no contrary declared.
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

-- R13: a strict cert whose backend/digest is certifier-allowed by the rule but
-- the registry cannot replay it (the theory digest is absent from the empty
-- theory table). Both drivers reach the backend layer and reject as R13.
negR13 :: Unit
negR13 =
  mkUnit
    [strRule "s" [] [apat0 "pp" []] (apat0 "q" []) False
      [CertRef (BackendId "nd") 1 (TheoryDigest "sha256:missing")]]
    [] []
    [(LeafId "e_p", atom0 "pp" [])]
    [(ArgId "a", SRule (RuleId "s") [] [SLeaf (LeafId "e_p")] [] []
        (AssuranceCert (Cert (BackendId "nd") 1 (TheoryDigest "sha256:missing")
          (SList [SAtom "hyp", SAtom "0"]))))]
    []
    [atom0 "q" []]

-- Undercut / exception conformance (M3 review item 2) -----------------------

-- | Accepting undercut: @r_att@ concludes @att@, @r_tgt@ concludes @c@, and an
-- exception licenses undercutting @r_tgt@ instances whose attacker concludes
-- @att@. Edge 0->1: a0 in, a1 out. Exercises the @checkAttack@ undercut case and
-- the exception scan on the accept path (both invisible to every rebut fixture).
undercutAccept :: Unit
undercutAccept =
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

-- | R11 undercut: identical to 'undercutAccept' but with no exception declared,
-- so the exception scan finds no licence (AttackRelationReason.MissingException).
undercutMissingException :: Unit
undercutMissingException =
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

-- | R10 undercut: the attacked position @(prem 5)@ does not resolve in the
-- one-node target (AttackPositionReason.UndefinedPosition) — a distinct R10 path
-- from the wrong-occurrence-kind case in 'negR10'.
undercutBadPosition :: Unit
undercutBadPosition =
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

-- Strict-assurance accepts (M3 review item 5) -------------------------------

-- | R7 accept: a strict identity rule with @allow-trusted true@ and an
-- @assurance trusted@ instance. The reject twin 'negR7' flips @allow-trusted@ to
-- false; this pins that a strict trusted assurance is actually /accepted/.
strictTrustedAccept :: Unit
strictTrustedAccept =
  mkUnit
    [strRule "s" [] [apat0 "pp" []] (apat0 "pp" []) True []]
    []
    []
    [(LeafId "e_p", atom0 "pp" [])]
    [(ArgId "a", SRule (RuleId "s") [] [SLeaf (LeafId "e_p")] [] [] AssuranceTrusted)]
    []
    [atom0 "pp" []]

-- | R13 accept: a strict identity rule with a certifier-allowed @nd\@1@
-- certificate that the backend /replays/ (@hyp 0 : pp@ from premise @pp@ under
-- the empty theory @t0@). The reject twin 'negR13' points the cert at a theory
-- the registry cannot replay; this pins that a replayable cert is accepted.
strictCertAccept :: Unit
strictCertAccept =
  Unit
    { unitRules =
        [strRule "s" [] [apat0 "pp" []] (apat0 "pp" []) False
          [CertRef (BackendId "nd") 1 (TheoryDigest "t0")]]
    , unitContraries = []
    , unitExceptions = []
    , unitTheories = [(TheoryDigest "t0", [])]
    , unitLeaves = [(LeafId "e_p", atom0 "pp" [])]
    , unitArgs =
        [(ArgId "a", SRule (RuleId "s") [] [SLeaf (LeafId "e_p")] [] []
            (AssuranceCert (Cert (BackendId "nd") 1 (TheoryDigest "t0")
              (SList [SAtom "hyp", SAtom "0"]))))]
    , unitAttacks = []
    , unitQueries = [atom0 "pp" []]
    }

-- ---------------------------------------------------------------------------
-- File table and driver
-- ---------------------------------------------------------------------------

corpus :: [(FilePath, Unit)]
corpus =
  [ ("fixtures/corpus/rebut-program.sexp", rebutProgram)
  , ("fixtures/corpus/independent-accept.sexp", independentAccept)
  , ("fixtures/corpus/stress-independent-120.sexp", stressUnit 120)
  , ("fixtures/corpus/reject-duplicate-rule.sexp", negDuplicateRule)
  , ("fixtures/corpus/reject-duplicate-argument.sexp", negDuplicateArgument)
  , ("fixtures/corpus/reject-incomplete-argument.sexp", negIncompleteArgument)
  , ("fixtures/corpus/reject-missing-conflict.sexp", negMissingConflict)
  , ("fixtures/corpus/reject-r12.sexp", negR12)
  , ("fixtures/corpus/reject-r1.sexp", negR1)
  , ("fixtures/corpus/reject-r3.sexp", negR3)
  , ("fixtures/corpus/reject-r4.sexp", negR4)
  , ("fixtures/corpus/reject-r5.sexp", negR5)
  , ("fixtures/corpus/reject-r6.sexp", negR6)
  , ("fixtures/corpus/reject-r7.sexp", negR7)
  , ("fixtures/corpus/reject-r10.sexp", negR10)
  , ("fixtures/corpus/reject-r11.sexp", negR11)
  , ("fixtures/corpus/reject-r13.sexp", negR13)
  , ("fixtures/corpus/undercut-accept.sexp", undercutAccept)
  , ("fixtures/corpus/reject-undercut-missing-exception.sexp", undercutMissingException)
  , ("fixtures/corpus/reject-undercut-bad-position.sexp", undercutBadPosition)
  , ("fixtures/corpus/strict-trusted-accept.sexp", strictTrustedAccept)
  , ("fixtures/corpus/strict-cert-accept.sexp", strictCertAccept)
  ]

main :: IO ()
main = mapM_ writeFixture corpus
  where
    writeFixture (path, u) = do
      writeFile path (printSExpr (encodeUnit u) ++ "\n")
      putStrLn ("wrote " ++ path)
