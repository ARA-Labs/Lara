-- | Corpus generator for the differential harness (M3 plan D8).
--
-- Constructs each conformance-corpus 'Unit', validates its replay identity, and
-- writes @fixtures/corpus/<name>.sexp@ as a canonical 'CheckInput' envelope.
-- This is the provenance record for the exact checker input defined here.
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
-- Numeric-literal parity is exercised directly by
-- @group-quarantine-numeric-multi-blocked.sexp@: its queries have both exact
-- and surface-variant supports, so identity canonicalization would publish
-- @justified@ while @canonNum@ correctly reports @evidence-blocked@.
--
-- PR #44 review anchors: three replay-preflight fixtures
-- (@reject-preflight-*.sexp@, review C3) pin the runtime preflight's
-- duplicate → unknown → unselected-certificate precedence (each rejects R13
-- under a deliberately broken backend selection), and
-- @strict-cert-unicode-theory.sexp@ (review C11) carries a non-ASCII theory
-- digest so the harness byte-compares both drivers on the quoted-atom path.
module Main (main) where

import Data.Char (ord)
import Data.List (sortBy)

import Lara.AST
import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..))
import Lara.Replay
import Lara.Sigma
  ( ConSig (..)
  , PredSig (..)
  , Sigma (..)
  , Sort (..)
  , SortName (..)
  )
import Lara.Strict (SExpr (..))
import Lara.Wire (encodeCheckInput, printSExpr)

-- ---------------------------------------------------------------------------
-- Small AST builders (mirror test/CheckSpec.hs)
-- ---------------------------------------------------------------------------

mkUnit
  :: [Rule] -> [Contrary] -> [Exception]
  -> [(LeafId, Prop)] -> [(ArgId, SupportTerm)] -> [Attack] -> [Prop] -> Unit
mkUnit rules contraries exceptions ls as ats qs =
  Unit
    { unitSigma = corpusSigma
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

-- | The one authored signature every fixture in this file is built against
-- (@lara-core\@0.2@, #89). It is a single shared Σ rather than one per fixture
-- because the fixtures share one small vocabulary, and because a per-fixture Σ
-- derived from the fixture would make stage 2 vacuous exactly where these
-- anchors are supposed to keep it honest.
--
-- @p0 … p119@ cover 'stressUnit', whose predicate names are index-derived.
corpusSigma :: Sigma
corpusSigma =
  Sigma
    [SortName "Item", SortName "Direction"]
    [ ConSig (FunSym "a") [] item
    , ConSig (FunSym "up") [] direction
    , ConSig (FunSym "down") [] direction
    ]
    ( [ PredSig (Pred "basis") [item]
      , PredSig (Pred "derived") [item]
      , PredSig (Pred "refuted") [item]
      , PredSig (Pred "effect") [direction]
      , PredSig (Pred "score1") [SortNum]
      , PredSig (Pred "score2") [SortNum]
      ]
        ++ [ PredSig (Pred h) []
           | h <-
               [ "ans", "att", "base", "c", "concl", "conflict", "conflictq"
               , "cw", "k", "not_q", "notk", "other", "p", "pp", "q", "rr"
               ]
                 ++ ["p" ++ show i | i <- [0 .. 119 :: Int]]
           ]
    )
  where
    item = SortDecl (SortName "Item")
    direction = SortDecl (SortName "Direction")

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

-- Duplicate-report groups (spec §4.3) --------------------------------------

-- | A constant term (no numeric literals, per the corpus policy).
c :: String -> Term
c name = TCon (FunSym name) []

-- | A ≡-consistent duplicate-report group: two leaves report one cell with the
-- same value (@effect(up) ≡ effect(up)@) and are grouped. The group admits
-- normally; the argument built on a member is @in@ / @justified@.
groupConsistentAccept :: Unit
groupConsistentAccept =
  ( mkUnit
      []
      []
      []
      [(LeafId "e1", atom0 "effect" [c "up"]), (LeafId "e2", atom0 "effect" [c "up"])]
      [(ArgId "a1", SLeaf (LeafId "e1"))]
      []
      [atom0 "effect" [c "up"]]
  )
    { unitGroups = [DupGroup (GroupId "g1") [LeafId "e1", LeafId "e2"]]
    , unitGroupMode = QuarantineOnConflict
    }

-- | A ≢ duplicate-report group under the default quarantine policy: two leaves
-- report one cell with conflicting values (@effect(up) ≢ effect(down)@). Both
-- members are quarantined, the argument on @e1@ is dropped, and the queried
-- claim has no support — @gap@, never a rejection (§4.3).
groupConflictQuarantine :: Unit
groupConflictQuarantine =
  ( mkUnit
      []
      []
      []
      [(LeafId "e1", atom0 "effect" [c "up"]), (LeafId "e2", atom0 "effect" [c "down"])]
      [(ArgId "a1", SLeaf (LeafId "e1"))]
      []
      [atom0 "effect" [c "up"]]
  )
    { unitGroups = [DupGroup (GroupId "g1") [LeafId "e1", LeafId "e2"]]
    , unitGroupMode = QuarantineOnConflict
    }

-- | The §4.3 promotion hazard (issue #76): the quarantined leaf backs the
-- __attacker__, not the target. @a2@ (leaf @e2 : base@) rebuts @a1@ (rule
-- instance on @e1 : p@), and @e2@ is grouped with @e3 : q@, so the group is @≢@
-- and @a2@ is pruned — leaving @a1@ unattacked. The pruned graph therefore says
-- @justified@, which is why @concl@ is published @evidence-blocked@ with that
-- label kept only as a conditional diagnostic. @other@ is out of the edit's
-- reach and keeps its ordinary status, pinning that the rule is directed.
groupConflictQuarantineAttacker :: Unit
groupConflictQuarantineAttacker =
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

-- | Production regression for numeric identity plus positional multi-blocked
-- reporting. Each queried numeric claim has two retained supports: an attacked
-- surface variant and an unattacked exact spelling. The attacker is
-- quarantined. Under @canonNum@ both supports belong to the query, so the
-- attacked variant puts each query in the blocked closure. Under identity
-- canonicalization only the exact support belongs to the query, incorrectly
-- publishing @justified@. The ordinary query between them pins that both
-- drivers project the two conditional entries positionally, not by parallel
-- list lookup.
groupQuarantineNumericMultiBlocked :: Unit
groupQuarantineNumericMultiBlocked =
  ( mkUnit
      [ defRule "r1_variant" [] [] (apat0 "score1" [PLit (TNum "01.0")]) []
      , defRule "r1_exact" [] [] (apat0 "score1" [PLit (TNum "1")]) []
      , defRule "r2_variant" [] [] (apat0 "score2" [PLit (TNum "+02.00")]) []
      , defRule "r2_exact" [] [] (apat0 "score2" [PLit (TNum "2")]) []
      ]
      []
      []
      [ (LeafId "e_other", atom0 "other" [])
      , (LeafId "e_bad", atom0 "base" [])
      , (LeafId "e_conflict", atom0 "conflict" [])
      ]
      [ (ArgId "a1_variant", instD "r1_variant" [] [] [] [])
      , (ArgId "a1_exact", instD "r1_exact" [] [] [] [])
      , (ArgId "a_other", SLeaf (LeafId "e_other"))
      , (ArgId "a2_variant", instD "r2_variant" [] [] [] [])
      , (ArgId "a2_exact", instD "r2_exact" [] [] [] [])
      , (ArgId "a_bad", SLeaf (LeafId "e_bad"))
      ]
      [ Rebut (ArgId "a_bad") (ArgId "a1_variant")
      , Rebut (ArgId "a_bad") (ArgId "a2_variant")
      ]
      [ atom0 "score1" [TNum "1"]
      , atom0 "other" []
      , atom0 "score2" [TNum "2"]
      ]
  )
    { unitGroups = [DupGroup (GroupId "g1") [LeafId "e_bad", LeafId "e_conflict"]]
    , unitGroupMode = QuarantineOnConflict
    }

-- | The lost-edge half of the §4.3 hazard (issue #76), mirroring
-- @test\/CheckSpec.groupQuarantineLostEdgeUnit@ as a cross-driver differential
-- anchor: the prune deletes an attack /edge between two retained arguments/
-- rather than an argument. @aT@ (rule @r@ on premises @Lq@, @Lk@) is
-- quarantined via @Lq@; the undermine on @aT@'s second premise also carried a
-- closure edge onto @aW@ (rule @rw@ on @Lk@ — it contains the attacked
-- occurrence without concluding it), so dropping the attack leaves @aW@
-- unattacked. Attack completeness compares @notk@ vs @cw@ (not contraries) and
-- accepts, so only the lost-edge seed clause catches the promotion: @cw@ is
-- published @evidence-blocked@ with @justified@ as its conditional label.
groupQuarantineLostEdge :: Unit
groupQuarantineLostEdge =
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

-- | The same ≢ group escalated by policy (@duplicate-reports = reject@): the
-- conflict is a whole-program data-integrity error — rejection class R9 (§4.3).
groupConflictReject9 :: Unit
groupConflictReject9 =
  groupConflictQuarantine {unitGroupMode = RejectOnConflict}

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
    { unitSigma = corpusSigma
    , unitRules =
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
    , unitGroups = []
    , unitGroupMode = QuarantineOnConflict
    }

-- | C11 quoted-atom anchor: the 'strictCertAccept' shape with the theory
-- digest renamed to the non-ASCII @sha256:é@ (@é@ is U+00E9, outside the bare
-- atom set, so the digest prints quoted). The replay-id theories section, the
-- unit theories section, the rule certifier, and the assurance certificate
-- all carry the quoted digest; the verdict is unchanged.
strictCertUnicodeTheory :: Unit
strictCertUnicodeTheory =
  Unit
    { unitSigma = corpusSigma
    , unitRules =
        [strRule "s" [] [apat0 "pp" []] (apat0 "pp" []) False
          [CertRef (BackendId "nd") 1 (TheoryDigest "sha256:é")]]
    , unitContraries = []
    , unitExceptions = []
    , unitTheories = [(TheoryDigest "sha256:é", [])]
    , unitLeaves = [(LeafId "e_p", atom0 "pp" [])]
    , unitArgs =
        [(ArgId "a", SRule (RuleId "s") [] [SLeaf (LeafId "e_p")] [] []
            (AssuranceCert (Cert (BackendId "nd") 1 (TheoryDigest "sha256:é")
              (SList [SAtom "hyp", SAtom "0"]))))]
    , unitAttacks = []
    , unitQueries = [atom0 "pp" []]
    , unitGroups = []
    , unitGroupMode = QuarantineOnConflict
    }

-- Replay-preflight anchors (PR #44 review C3) -------------------------------

-- | The shared unit for the preflight anchors: the 'strictCertAccept' shape
-- with the assurance certificate (and its rule certifier) pointing at
-- @nd\@2@, so the certificate's backend pair is unselected under every
-- anchor's selection. The unit itself is checker-valid; only the replay-id
-- backend selection decides which preflight failure fires (all reject R13).
preflightCertUnit :: Unit
preflightCertUnit =
  Unit
    { unitSigma = corpusSigma
    , unitRules =
        [strRule "s" [] [apat0 "pp" []] (apat0 "pp" []) False
          [CertRef (BackendId "nd") 2 (TheoryDigest "t0")]]
    , unitContraries = []
    , unitExceptions = []
    , unitTheories = [(TheoryDigest "t0", [])]
    , unitLeaves = [(LeafId "e_p", atom0 "pp" [])]
    , unitArgs =
        [(ArgId "a", SRule (RuleId "s") [] [SLeaf (LeafId "e_p")] [] []
            (AssuranceCert (Cert (BackendId "nd") 2 (TheoryDigest "t0")
              (SList [SAtom "hyp", SAtom "0"]))))]
    , unitAttacks = []
    , unitQueries = [atom0 "pp" []]
    , unitGroups = []
    , unitGroupMode = QuarantineOnConflict
    }

-- ---------------------------------------------------------------------------
-- File table and driver
-- ---------------------------------------------------------------------------

corpus :: [(FilePath, Unit)]
corpus =
  [ ("fixtures/corpus/rebut-program.sexp", rebutProgram)
  , ("fixtures/corpus/independent-accept.sexp", independentAccept)
  , ("fixtures/corpus/group-consistent-accept.sexp", groupConsistentAccept)
  , ("fixtures/corpus/group-conflict-quarantine.sexp", groupConflictQuarantine)
  , ( "fixtures/corpus/group-conflict-quarantine-attacker.sexp"
    , groupConflictQuarantineAttacker
    )
  , ( "fixtures/corpus/group-quarantine-numeric-multi-blocked.sexp"
    , groupQuarantineNumericMultiBlocked
    )
  , ("fixtures/corpus/group-quarantine-lost-edge.sexp", groupQuarantineLostEdge)
  , ("fixtures/corpus/reject-r9.sexp", groupConflictReject9)
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
  , ("fixtures/corpus/strict-cert-unicode-theory.sexp", strictCertUnicodeTheory)
  ]

-- | The preflight anchors (PR #44 review C3), as
-- @(path, backend selection, unit)@: each selection is a deliberate preflight
-- violation, and lower-precedence violations ride along so the precedence
-- order (duplicate → unknown → unselected certificate) is exercised. All
-- three failure kinds emit the identical stdout verdict @reject R13@, so the
-- precedence is pinned by @scripts/differential.sh@ byte-comparing the
-- stderr @replayFailureMessage@ line for these three anchors.
preflightCorpus :: [(FilePath, [(BackendId, String)], Unit)]
preflightCorpus =
  [ -- Duplicate selection; the unknown @foo\@1@ and the unselected @nd\@2@
    -- certificate ride along to pin that duplicate wins.
    ( "fixtures/corpus/reject-preflight-duplicate-backend.sexp"
    , [(BackendId "nd", "1"), (BackendId "nd", "1"), (BackendId "foo", "1")]
    , preflightCertUnit
    )
  , -- A single unknown selection; the unselected @nd\@2@ certificate rides
    -- along to pin that unknown outranks it (again via the stderr
    -- byte-compare in @scripts/differential.sh@).
    ( "fixtures/corpus/reject-preflight-unknown-backend.sexp"
    , [(BackendId "foo", "1")]
    , preflightCertUnit
    )
  , -- The valid @nd\@1@ selection with an unselected @nd\@2@ certificate:
    -- the only violation is the certificate backend.
    ( "fixtures/corpus/reject-preflight-unselected-certificate.sexp"
    , [(BackendId "nd", "1")]
    , preflightCertUnit
    )
  ]

main :: IO ()
main = do
  mapM_ (writeFixture conformanceBackends) corpus
  mapM_ (\(path, backends, unit) -> writeFixture backends (path, unit)) preflightCorpus
  where
    writeFixture backends (path, unit) = do
      input <- checkInput backends unit
      writeFile path (printSExpr (encodeCheckInput input) ++ "\n")
      putStrLn ("wrote " ++ path)

-- | The backend selection every conformance-corpus fixture shares; the
-- preflight anchors override it with their deliberate violations.
conformanceBackends :: [(BackendId, String)]
conformanceBackends = [(BackendId "nd", "1")]

checkInput :: [(BackendId, String)] -> Unit -> IO CheckInput
checkInput backends unit = do
  replayId <-
    either (fail . replayErrorMessage) pure $
      mkReplayId
        LaraCoreV02
        (PolicyId "conformance-v1")
        backends
        (sortBy compareTheoryDigest (map fst (unitTheories unit)))
        (Digest "sha256:conformance-corpus-v1")
  either (fail . replayErrorMessage) pure (mkCheckInput replayId unit)
  where
    compareTheoryDigest (TheoryDigest a) (TheoryDigest b) =
      compare (map ord a) (map ord b)
