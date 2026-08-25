-- | Where each rejection operator can strike: one enumerator per operator,
-- listing that operator's applicable sites in a decoded 'Unit'.
--
-- An enumerator returns @(specified outcome, ground-truth 'Constituent',
-- rewrite)@ triples — a proposal, not a mutant. 'Lara.Mutate.Suite' picks
-- among them with the seeded stream and assembles the file bytes; the
-- 'Constituent' becomes the @expected-location@ manifest column.
--
-- Two invariants:
--
-- * The /order/ of each returned list is load-bearing. Site selection runs
--   'Lara.Mutate.Seed.pickSome' over the list as given, so reordering a list
--   comprehension changes which sites are picked and moves committed bytes.
--
-- * An enumerator must self-gate: it returns @[]@ at a base that carries no
--   applicable site. That is what lets the corpus sweep run every operator
--   over every base with no special casing — a gap unit with no arguments
--   simply yields nothing for the argument-dependent operators.
--
-- The signature-family enumerators live in "Lara.Mutate.Sorts" and are not
-- re-exported here; 'Lara.Mutate.Suite' imports them directly, so the wrapper
-- that attaches 'Lara.Mutate.Expected' stays at the single assembly site.
--
-- The certificate-family enumerators live in "Lara.Mutate.Sites.Cert" and the
-- attack-completeness one in "Lara.Mutate.Sites.Conflict"; both /are/
-- re-exported here, so 'Lara.Mutate.Suite' keeps its single import of this
-- module; the navigation helpers they share live in "Lara.Mutate.Sites.Nav"
-- (#125, splitting this module back under the 400-line bound
-- @docs\/mutate-module-ownership-decision.md@ fixes).
--
-- Internal to the library: the navigation helpers were private before the
-- split and stay library-internal, and the enumerators have exactly one
-- consumer.
module Lara.Mutate.Sites
  ( undeclaredLeafSites
  , hiddenRuleSites
  , hiddenContrarySites
  , wrongSubstSites
  , wrongPremiseSites
  , openObligationSites
  , holeObligationSites
  , wrongDischargeSites
  , trustedAssuranceSites
  , certTheorySwapSites
  , certPayloadSites
  , certWrongFractionSites
  , badAttackPositionSites
  , unlicensedAttackSites
  , dropCoveringAttackSites
  , groupConflictSites
  ) where

import Data.List (find)

import Lara.AST
import Lara.Diagnostics (Constituent (..))
import Lara.Prop (equiv)
import Lara.Sigma (declarePred)
import Lara.SupportTerm (instAPat, instAPats)

import Lara.Mutate (Expected (..))
import Lara.Mutate.Sites.Cert
  ( certPayloadSites
  , certTheorySwapSites
  , certWrongFractionSites
  )
import Lara.Mutate.Sites.Conflict (dropCoveringAttackSites)
import Lara.Mutate.Sites.Nav
  ( inequivLeaf
  , leafSites
  , ruleOf
  , ruleSites
  , rewriteArg
  , rewriteAt
  )

-- R1: rewrite one leaf reference to an undeclared id.
undeclaredLeafSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
undeclaredLeafSites u =
  [ ( ExpectClass R1
    , CArgument ix
    , rewriteArg ix (rewriteAt pos (const (SLeaf (LeafId "mut_undeclared"))))
    )
  | (ix, pos, _) <- leafSites u
  ]

-- R1: instantiate a rule id the policy section never declares.
hiddenRuleSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
hiddenRuleSites u =
  [ ( ExpectClass R1
    , CArgument ix
    , rewriteArg ix (rewriteAt pos setRule)
    )
  | (ix, pos, _) <- ruleSites u
  ]
  where
    setRule (SRule _ theta ws d hs a) = SRule (RuleId "mut_hidden_rule") theta ws d hs a
    setRule t = t

-- R12: extend the carried policy with a strict rule and a contrary pair on
-- its conclusion (spec §8.1 Path-B well-formedness violation).
hiddenContrarySites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
hiddenContrarySites _ =
  [ ( ExpectClass R12
    , CPolicy
    , \u ->
        u
          { unitRules = unitRules u ++ [mutStrictRule]
          , unitContraries = unitContraries u ++ [mutContrary]
          , unitSigma = declareMut (unitSigma u)
          }
    )
  ]
  where
    mutP = AtomPat (Pred "mut_p") []
    mutQ = AtomPat (Pred "mut_q") []
    mutStrictRule =
      Rule (RuleId "mut_strict") [] Strict [] [] mutP False [] []
    mutContrary = Contrary mutQ mutP
    -- Σ-aware injection (#89 §8): the operator that invents `mut_p`/`mut_q`
    -- declares them, so the mutant tests R12 — the class it seeds — instead of
    -- flipping to R2 on incidental signature noise.
    declareMut sg = declarePred (Pred "mut_p") [] (declarePred (Pred "mut_q") [] sg)

-- R3: rename one substitution key off the rule's parameter list.
wrongSubstSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
wrongSubstSites u =
  [ ( ExpectClass R3
    , CArgument ix
    , rewriteArg ix (rewriteAt pos renameKey)
    )
  | (ix, pos, SRule _ theta _ _ _ _) <- ruleSites u
  , not (null theta)
  ]
  where
    renameKey (SRule r ((_, t0) : theta) ws d hs a) =
      SRule r ((Param "mut_x", t0) : theta) ws d hs a
    renameKey t = t

-- R4: swap the first premise child for a declared leaf whose proposition is
-- ≢ the instantiated premise pattern.
wrongPremiseSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
wrongPremiseSites u =
  [ ( ExpectClass R4
    , CArgument ix
    , rewriteArg ix (rewriteAt pos (swapPremise l'))
    )
  | (ix, pos, SRule rn theta (_ : _) _ _ _) <- ruleSites u
  , Just r <- [ruleOf u rn]
  , Just (expected0 : _) <- [instAPats theta (rulePremises r)]
  , Just l' <- [inequivLeaf u expected0]
  ]
  where
    swapPremise l' (SRule r theta (_ : ws) d hs a) = SRule r theta (SLeaf l' : ws) d hs a
    swapPremise _ t = t

-- R5: drop one discharge of a mandatory question without opening a hole.
openObligationSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
openObligationSites u =
  [ ( ExpectClass R5
    , CArgument ix
    , rewriteArg ix (rewriteAt pos (dropDischarge q))
    )
  | (ix, pos, SRule rn _ _ d _ _) <- ruleSites u
  , Just r <- [ruleOf u rn]
  , (q, _) <- take 1 [entry | entry@(q, _) <- d, mandatoryIn r q]
  ]
  where
    mandatoryIn r q =
      any (\qd -> questionId qd == q && questionNecessity qd == Mandatory) (ruleQuestions r)
    dropDischarge q (SRule r theta ws d hs a) =
      SRule r theta ws [entry | entry@(q', _) <- d, q' /= q] hs a
    dropDischarge _ t = t

-- Obligation gate: replace one mandatory discharge with a declared hole. The
-- clone of 'openObligationSites' that swaps the entry into the hole set
-- instead of deleting it: R5 coverage still holds (the question is covered by
-- the hole), so the schema-valid argument reaches the obligation gate with an
-- open mandatory obligation — the full system rejects with
-- 'IncompleteArgument', and only 'Lara.Check.noCQConfig' accepts it. Only
-- mandatory discharges are sites: holing an optional question's discharge
-- contributes no obligation ('Lara.SupportTerm.openMandatory') and the full
-- system would accept.
holeObligationSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
holeObligationSites u =
  [ ( ExpectIncompleteArgument
    , CArgument ix
    , rewriteArg ix (rewriteAt pos (holeDischarge q))
    )
  | (ix, pos, SRule rn _ _ d _ _) <- ruleSites u
  , Just r <- [ruleOf u rn]
  , (q, _) <- take 1 [entry | entry@(q, _) <- d, mandatoryIn r q]
  ]
  where
    mandatoryIn r q =
      any (\qd -> questionId qd == q && questionNecessity qd == Mandatory) (ruleQuestions r)
    holeDischarge q (SRule r theta ws d hs a) =
      SRule r theta ws [entry | entry@(q', _) <- d, q' /= q] (hs ++ [holeOf q]) a
    holeDischarge _ t = t
    holeOf (QuestionId s) = ObligationId s

-- R6: answer one known question with a declared-but-≢ leaf.
wrongDischargeSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
wrongDischargeSites u =
  [ ( ExpectClass R6
    , CArgument ix
    , rewriteArg ix (rewriteAt pos (swapDischarge q l'))
    )
  | (ix, pos, SRule rn theta _ d _ _) <- ruleSites u
  , Just r <- [ruleOf u rn]
  , (q, answer) <-
      take
        1
        [ (q, answer)
        | (q, _) <- d
        , Just qd <- [find ((== q) . questionId) (ruleQuestions r)]
        , Just answer <- [instAPat theta (questionAnswer qd)]
        ]
  , Just l' <- [inequivLeaf u answer]
  ]
  where
    swapDischarge q l' (SRule r theta ws d hs a) =
      SRule r theta ws [(q', if q' == q then SLeaf l' else w) | (q', w) <- d] hs a
    swapDischarge _ _ t = t

-- R7: claim @trusted@ assurance on a defeasible instance.
trustedAssuranceSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
trustedAssuranceSites u =
  [ ( ExpectClass R7
    , CArgument ix
    , rewriteArg ix (rewriteAt pos setTrusted)
    )
  | (ix, pos, SRule _ _ _ _ _ AssuranceNone) <- ruleSites u
  ]
  where
    setTrusted (SRule r theta ws d hs _) = SRule r theta ws d hs AssuranceTrusted
    setTrusted t = t

-- R10: push an attack position off the target term (undercut/undermine) or
-- retarget a rebut at a leaf-rooted argument (wrong occurrence kind).
badAttackPositionSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
badAttackPositionSites u =
  [ (ExpectClass R10, CAttack i, \u' -> u' {unitAttacks = replaceIx i k' (unitAttacks u')})
  | (i, k) <- zip [0 :: Int ..] (unitAttacks u)
  , Just k' <- [mutateAttack k]
  ]
  where
    leafRootedArg = fst <$> find (isLeaf . snd) (unitArgs u)
    isLeaf SLeaf{} = True
    isLeaf _ = False
    mutateAttack k = case k of
      Rebut w _ -> Rebut w <$> leafRootedArg
      Undercut w t _ -> Just (Undercut w t [StepPremise 99])
      Undermine w t _ -> Just (Undermine w t [StepPremise 99])
    replaceIx i x xs = [if j == i then x else y | (j, y) <- zip [0 ..] xs]

-- R11: declare a self-rebut on a rule-rooted argument; no contrary pair
-- relates a conclusion to itself in any base policy.
unlicensedAttackSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
unlicensedAttackSites u =
  [ ( ExpectClass R11
    , CAttack (length (unitAttacks u)) -- the appended self-rebut's index
    , \u' -> u' {unitAttacks = unitAttacks u' ++ [Rebut aid aid]}
    )
  | Just aid <- [fst <$> find (isRule . snd) (unitArgs u)]
  ]
  where
    isRule SRule{} = True
    isRule _ = False

-- R9: group two ≢ leaves as duplicate reports of one cell under the
-- escalating conflict mode.
groupConflictSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
groupConflictSites u =
  [ ( ExpectClass R9
    , CGroup (GroupId "mut_g")
    , \u' ->
        u'
          { unitGroups = unitGroups u' ++ [DupGroup (GroupId "mut_g") [l1, l2]]
          , unitGroupMode = RejectOnConflict
          }
    )
  | null (unitGroups u)
  , Just (l1, l2) <- [conflictPair]
  ]
  where
    conflictPair =
      case [ (a, b)
           | ((a, pa) : rest) <- [unitLeaves u]
           , (b, pb) <- rest
           , not (equiv pa pb)
           ] of
        (pair : _) -> Just pair
        [] -> Nothing
