-- | Where each rejection operator can strike: one enumerator per operator,
-- listing that operator's applicable sites in a decoded 'Unit'.
--
-- An enumerator returns @(specified outcome, ground-truth 'Constituent',
-- rewrite)@ triples — a proposal, not a mutant. 'Lara.Mutate.Suite' picks
-- among them with the seeded stream and assembles the file bytes; the
-- 'Constituent' becomes the @expected-location@ manifest column.
--
-- Three invariants:
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
-- * A published 'Constituent' index is in __checked__ index space. The
--   checker runs on the §4.3 quarantine of the declared unit
--   ('Lara.Blocked.quarantineUnit') and its verdict names checked indices, so
--   that is the space the ground truth must live in; only the /rewrite/ edits
--   the declared unit, through the prune's retained-index maps. Sites are
--   drawn from the checked unit for the same reason: a mutation into pruned
--   material never reaches the checker, so it cannot witness anything.
--   @test\/MutationSpec.hs@'s checker-agreement property gates this — every
--   proposed site's predicted constituent must be the one
--   'Lara.Driver.runCheckLocated' reports on the mutant.
--
-- The signature-family enumerators live in "Lara.Mutate.Sorts" and are not
-- re-exported here; 'Lara.Mutate.Suite' imports them directly, so the wrapper
-- that attaches 'Lara.Mutate.Expected' stays at the single assembly site.
--
-- The localization family lives in "Lara.Mutate.Sites.Localize" and is not
-- re-exported here either, for a different reason: its composite enumerators
-- import this module's single-site enumerators as components, so a re-export
-- would cycle. 'Lara.Mutate.Suite' imports it directly, following the
-- "Lara.Mutate.Sorts" precedent.
--
-- The certificate-family enumerators live in "Lara.Mutate.Sites.Cert" and the
-- attack-completeness one in "Lara.Mutate.Sites.Conflict"; both /are/
-- re-exported here, so 'Lara.Mutate.Suite' keeps its single import of this
-- module; the navigation helpers they share live in "Lara.Mutate.Sites.Nav"
-- (splitting the certificate family off this module along the seam
-- @docs\/mutate-module-ownership-decision.md@ records).
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
import Lara.Blocked (prune, pruneChecked)
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
  ( CheckedIx (..)
  , attackSites
  , inequivLeaf
  , leafSites
  , ruleOf
  , ruleSites
  , rewriteArg
  , rewriteAt
  , setAttackAt
  )

-- R1: rewrite one leaf reference to an undeclared id.
undeclaredLeafSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
undeclaredLeafSites u =
  [ ( ExpectClass R1
    , CArgument (checkedIx ci)
    , rewriteArg di (rewriteAt pos (const (SLeaf (LeafId "mut_undeclared"))))
    )
  | (ci, di, pos, _) <- leafSites (prune u)
  ]

-- R1: instantiate a rule id the policy section never declares.
hiddenRuleSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
hiddenRuleSites u =
  [ ( ExpectClass R1
    , CArgument (checkedIx ci)
    , rewriteArg di (rewriteAt pos setRule)
    )
  | (ci, di, pos, _) <- ruleSites (prune u)
  ]
  where
    setRule (SRule _ theta ws d hs a) = SRule (RuleId "mut_hidden_rule") theta ws d hs a
    setRule t = t

-- R12: extend the carried policy with a strict rule and a contrary pair on
-- its conclusion (spec §8.1 Path-B well-formedness violation). Policy and Σ
-- material survives quarantine untouched, so the site needs no index mapping.
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
    -- Σ-aware injection (§8): the operator that invents `mut_p`/`mut_q`
    -- declares them, so the mutant tests R12 — the class it seeds — instead of
    -- flipping to R2 on incidental signature noise.
    declareMut sg = declarePred (Pred "mut_p") [] (declarePred (Pred "mut_q") [] sg)

-- R3: rename one substitution key off the rule's parameter list.
wrongSubstSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
wrongSubstSites u =
  [ ( ExpectClass R3
    , CArgument (checkedIx ci)
    , rewriteArg di (rewriteAt pos renameKey)
    )
  | (ci, di, pos, SRule _ theta _ _ _ _) <- ruleSites (prune u)
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
    , CArgument (checkedIx ci)
    , rewriteArg di (rewriteAt pos (swapPremise l'))
    )
  | (ci, di, pos, SRule rn theta (_ : _) _ _ _) <- ruleSites pruned
  , Just r <- [ruleOf checked rn]
  , Just (expected0 : _) <- [instAPats theta (rulePremises r)]
  , Just l' <- [inequivLeaf checked expected0]
  ]
  where
    pruned = prune u
    checked = pruneChecked pruned
    swapPremise l' (SRule r theta (_ : ws) d hs a) = SRule r theta (SLeaf l' : ws) d hs a
    swapPremise _ t = t

-- R5: drop one discharge of a mandatory question without opening a hole.
openObligationSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
openObligationSites u =
  [ ( ExpectClass R5
    , CArgument (checkedIx ci)
    , rewriteArg di (rewriteAt pos (dropDischarge q))
    )
  | (ci, di, pos, SRule rn _ _ d _ _) <- ruleSites pruned
  , Just r <- [ruleOf checked rn]
  , (q, _) <- take 1 [entry | entry@(q, _) <- d, mandatoryIn r q]
  ]
  where
    pruned = prune u
    checked = pruneChecked pruned
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
    , CArgument (checkedIx ci)
    , rewriteArg di (rewriteAt pos (holeDischarge q))
    )
  | (ci, di, pos, SRule rn _ _ d _ _) <- ruleSites pruned
  , Just r <- [ruleOf checked rn]
  , (q, _) <- take 1 [entry | entry@(q, _) <- d, mandatoryIn r q]
  ]
  where
    pruned = prune u
    checked = pruneChecked pruned
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
    , CArgument (checkedIx ci)
    , rewriteArg di (rewriteAt pos (swapDischarge q l'))
    )
  | (ci, di, pos, SRule rn theta _ d _ _) <- ruleSites pruned
  , Just r <- [ruleOf checked rn]
  , (q, answer) <-
      take
        1
        [ (q, answer)
        | (q, _) <- d
        , Just qd <- [find ((== q) . questionId) (ruleQuestions r)]
        , Just answer <- [instAPat theta (questionAnswer qd)]
        ]
  , Just l' <- [inequivLeaf checked answer]
  ]
  where
    pruned = prune u
    checked = pruneChecked pruned
    swapDischarge q l' (SRule r theta ws d hs a) =
      SRule r theta ws [(q', if q' == q then SLeaf l' else w) | (q', w) <- d] hs a
    swapDischarge _ _ t = t

-- R7: claim @trusted@ assurance on a defeasible instance.
trustedAssuranceSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
trustedAssuranceSites u =
  [ ( ExpectClass R7
    , CArgument (checkedIx ci)
    , rewriteArg di (rewriteAt pos setTrusted)
    )
  | (ci, di, pos, SRule _ _ _ _ _ AssuranceNone) <- ruleSites (prune u)
  ]
  where
    setTrusted (SRule r theta ws d hs _) = SRule r theta ws d hs AssuranceTrusted
    setTrusted t = t

-- R10: push an attack position off the target term (undercut/undermine) or
-- retarget a rebut at a leaf-rooted argument (wrong occurrence kind). Only
-- retained attacks are sites — a pruned attack never reaches the typed-attack
-- stage — and the retarget draws from the checked arguments, so the mutated
-- attack keeps both endpoints retained and its checked index.
badAttackPositionSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
badAttackPositionSites u =
  [ (ExpectClass R10, CAttack (checkedIx ci), setAttackAt di k')
  | (ci, di, k) <- attackSites pruned
  , Just k' <- [mutateAttack k]
  ]
  where
    pruned = prune u
    checked = pruneChecked pruned
    leafRootedArg = fst <$> find (isLeaf . snd) (unitArgs checked)
    isLeaf SLeaf{} = True
    isLeaf _ = False
    mutateAttack k = case k of
      Rebut w _ -> Rebut w <$> leafRootedArg
      Undercut w t _ -> Just (Undercut w t [StepPremise 99])
      Undermine w t _ -> Just (Undermine w t [StepPremise 99])

-- R11: declare a self-rebut on a rule-rooted argument; no contrary pair
-- relates a conclusion to itself in any base policy. The attacked argument is
-- drawn from the checked unit, so the appended attack survives quarantine and
-- its checked index is the checked attack count (the prune filters in order,
-- and the appended attack is declared last).
unlicensedAttackSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
unlicensedAttackSites u =
  [ ( ExpectClass R11
    , CAttack (checkedIx appendedIx)
    , \u' -> u' {unitAttacks = unitAttacks u' ++ [Rebut aid aid]}
    )
  | Just aid <- [fst <$> find (isRule . snd) (unitArgs checked)]
  ]
  where
    checked = pruneChecked (prune u)
    -- The appended self-rebut is declared last and both its endpoints are
    -- retained, so the prune keeps it last: its checked index is the checked
    -- attack count, not the declared one.
    appendedIx = CheckedIx (length (unitAttacks checked))
    isRule SRule{} = True
    isRule _ = False

-- R9: group two ≢ leaves as duplicate reports of one cell under the
-- escalating conflict mode. Gated on a groupless base, so the quarantine is
-- the identity and no index mapping arises; the published 'CGroup' is id-keyed
-- and space-free regardless.
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
