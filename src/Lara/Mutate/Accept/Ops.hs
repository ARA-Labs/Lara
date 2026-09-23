-- | The six accept-verdict constructions (split out of "Lara.Mutate.Accept").
--
-- Each operator takes a /justified/ corpus unit and edits it into a mutant that
-- still ACCEPTS but lands the queried claim at a specified status, by attaching
-- an attack @corpus-v1@'s licensing permits:
--
-- > operator             construction                                  status
-- > drop-support         remove the claim's support arg (E2-style)     gap
-- > attach-undercut      leaf arg on the rule's exception, undercut     defeated
-- > attach-undermine     leaf arg contrary to a premise, undermine     defeated
-- > attach-rebut-cycle   leaf arg on a symmetric contrary, mutual rebut contested
-- > attach-reinstate     attach-undercut + a counter-undercut (E4)     justified
-- > quarantine-attacker  attach-undercut + a ≢ duplicate-report group  evidence-blocked
--
-- Where a construction needs vocabulary @corpus-v1@ lacks, the mutant injects it
-- as a /declared/ extension in the unit's policy image (a new leaf proposition,
-- a one-directional or symmetric contrary, or — for reinstatement — a defeasible
-- rule plus its exception). This is legal precisely because these mutants must
-- ACCEPT: every rule stays defeasible, so nothing is smuggled past R12, and the
-- checker verifies the whole construction at generation time.
--
-- The assembly these operators build through, and the justified-unit invariants
-- they assert, live in "Lara.Mutate.Accept.Build"; the operator list that runs
-- them and the structural verification of their output stay in the facade,
-- "Lara.Mutate.Accept".
module Lara.Mutate.Accept.Ops
  ( opDropSupport
  , opAttachUndercut
  , opQuarantineAttacker
  , opAttachUndermine
  , opAttachRebutCycle
  , opAttachReinstate
  ) where

import Lara.AST hiding (Reject)
import Lara.Mutate (Mutant, MutationOp (..))
import Lara.Mutate.Accept.Build
  ( acceptMutant
  , acceptMutantBlocked
  , attackEndpoints
  , attackerArg
  , defenderArg
  , exceptionProp
  , firstPremiseLeaf
  , groundPat
  , propArgs
  , propPred
  , theQuery
  , theSupport
  )
import Lara.Prop (Prop (..))
import Lara.Replay (CheckInput, inputUnit)
import Lara.Sigma (declarePred, declarePredFor)

-- ---------------------------------------------------------------------------
-- The six operators
-- ---------------------------------------------------------------------------

-- | @drop-support@: remove the claim's support argument (and any attack that
-- referenced it), leaving the claim + leaves. The claim then has no complete
-- support and surfaces as @gap@.
opDropSupport :: String -> CheckInput -> [Mutant]
opDropSupport base input =
  acceptMutant base input OpDropSupport Gap $
    u
      { unitArgs = [a | a@(aid, _) <- unitArgs u, aid /= aidS]
      , unitAttacks = [k | k <- unitAttacks u, aidS `notElem` attackEndpoints k]
      }
  where
    u = inputUnit input
    (aidS, _, _, _) = theSupport base u (theQuery base u)

-- | @attach-undercut@: a leaf argument concluding the support rule's declared
-- exception atom, undercutting the support at its rule position. The undercutter
-- is unattacked (IN), so the support goes OUT and the claim is @defeated@.
opAttachUndercut :: String -> CheckInput -> [Mutant]
opAttachUndercut base input =
  acceptMutant base input OpAttachUndercut Defeated $
    u
      { unitLeaves = unitLeaves u ++ [(leaf, excP)]
      , unitArgs = unitArgs u ++ [(attackerArg, SLeaf leaf)]
      , unitAttacks = unitAttacks u ++ [Undercut attackerArg aidS []]
      }
  where
    u = inputUnit input
    (aidS, r, theta, _) = theSupport base u (theQuery base u)
    excP = exceptionProp base u r theta
    leaf = LeafId "mut_undercut_leaf"

-- | @quarantine-attacker@ (spec §4.3): @attach-undercut@'s
-- construction, plus a @≢@ duplicate-report group that quarantines the
-- attacker's own leaf.
--
-- The checker therefore drops the undercutter and its attack before checking and
-- sees the support argument /unattacked/ — the pruned graph says @justified@,
-- the same status the unmutated unit had. That is the promotion hazard: the
-- claim looks exactly as strong as before even though the evidence deciding its
-- only objection turned out to be internally inconsistent. The mutant must
-- therefore come back @accept-evidence-blocked@; an ordinary @accept-justified@
-- here is that bug.
--
-- The group's second member is a fresh leaf with a proposition that is not @≡@
-- the attacker's (the exception atom wrapped in a distinct predicate), which is
-- what makes the group inconsistent.
opQuarantineAttacker :: String -> CheckInput -> [Mutant]
opQuarantineAttacker base input =
  acceptMutantBlocked base input OpQuarantineAttacker $
    u
      { unitLeaves = unitLeaves u ++ [(leaf, excP), (conflictLeaf, conflictP)]
      , unitArgs = unitArgs u ++ [(attackerArg, SLeaf leaf)]
      , unitAttacks = unitAttacks u ++ [Undercut attackerArg aidS []]
      , unitGroups = unitGroups u ++ [DupGroup (GroupId "mut_quarantine_g") [leaf, conflictLeaf]]
      , unitGroupMode = QuarantineOnConflict
      , unitSigma = declarePredFor (propArgs conflictP) (propPred conflictP) (unitSigma u)
      }
  where
    u = inputUnit input
    (aidS, r, theta, _) = theSupport base u (theQuery base u)
    excP = exceptionProp base u r theta
    leaf = LeafId "mut_undercut_leaf"
    conflictLeaf = LeafId "mut_quarantine_leaf"
    -- Not ≡ excP: a distinct predicate over the same arguments.
    conflictP = case excP of Prop _ args -> Prop (Pred "mut_quarantine_conflict") args

-- | @attach-undermine@: a leaf argument whose proposition is a fresh contrary of
-- one of the support's premise leaves, undermining that premise. The contrary is
-- injected in ONE direction only, so attack completeness forces no back edge —
-- the undermine is a clean defeat (attacker IN, support OUT), not a cycle: the
-- claim is @defeated@.
opAttachUndermine :: String -> CheckInput -> [Mutant]
opAttachUndermine base input =
  acceptMutant base input OpAttachUndermine Defeated $
    u
      { unitLeaves = unitLeaves u ++ [(leaf, attP)]
      , unitContraries = unitContraries u ++ [Contrary (groundPat attP) (groundPat premP)]
      , unitArgs = unitArgs u ++ [(attackerArg, SLeaf leaf)]
      , unitAttacks = unitAttacks u ++ [Undermine attackerArg aidS pos]
      , unitSigma = declarePredFor (propArgs attP) (propPred attP) (unitSigma u)
      }
  where
    u = inputUnit input
    (aidS, _, _, term) = theSupport base u (theQuery base u)
    (pos, premP) = firstPremiseLeaf base u term
    attP = Prop (Pred "mut_undermine_contrary") (propArgs premP)
    leaf = LeafId "mut_undermine_leaf"

-- | @attach-rebut-cycle@: a rule-rooted argument concluding the contrary of the
-- claim, with the mutual rebut edge attack completeness mandates for a symmetric
-- contrary. The 2-cycle labels both the support and the attacker @undec@, so the
-- claim is @contested@. Rebut targets must be rule-rooted (a leaf cannot be
-- rebutted — spec R10), so the attacker is a fresh minimal defeasible rule
-- concluding the dual; the CONTRARY, though, is reused when @corpus-v1@ already
-- declares a symmetric pair for the claim's predicate (@better@\/@not_better@)
-- and injected on the claim atom otherwise (only 3 of 9 justified units query a
-- predicate with a declared contrary — eng review D13).
opAttachRebutCycle :: String -> CheckInput -> [Mutant]
opAttachRebutCycle base input =
  acceptMutant base input OpAttachRebutCycle Contested $
    u
      { unitRules = unitRules u ++ [mutRule]
      , unitContraries = unitContraries u ++ injected
      , unitLeaves = unitLeaves u ++ [(premLeaf, premP)]
      , unitArgs =
          unitArgs u
            ++ [(attackerArg, SRule mutRuleId [] [SLeaf premLeaf] [] [] AssuranceNone)]
      , unitAttacks = unitAttacks u ++ [Rebut attackerArg aidS, Rebut aidS attackerArg]
      , unitSigma =
          declarePred (propPred premP) []
            (declarePredFor (propArgs dualP) (propPred dualP) (unitSigma u))
      }
  where
    u = inputUnit input
    q = theQuery base u
    (aidS, _, _, _) = theSupport base u q
    (dualP, injected) = dualOf u q
    mutRuleId = RuleId "mut_rebut_rule"
    premLeaf = LeafId "mut_rebut_premise"
    premP = Prop (Pred "mut_rebut_premise") []
    mutRule = Rule mutRuleId [] Defeasible [groundPat premP] [] (groundPat dualP) False [] []

-- | The contrary proposition of a claim plus any contraries that must be
-- injected: a declared symmetric pair for the claim's predicate is reused (no
-- injection); otherwise a fresh dual predicate and a symmetric ground pair on
-- the claim atom are injected.
dualOf :: Unit -> Prop -> (Prop, [Contrary])
dualOf u q@(Prop qp qArgs) =
  case declaredSymmetricDual of
    Just dp -> (Prop dp qArgs, [])
    Nothing ->
      let dualP = Prop (Pred "mut_rebut_dual") qArgs
       in (dualP, [Contrary (groundPat q) (groundPat dualP), Contrary (groundPat dualP) (groundPat q)])
  where
    declaredSymmetricDual =
      case [ dp
           | Contrary (AtomPat dp _) (AtomPat cp _) <- unitContraries u
           , cp == qp
           , hasContrary qp dp
           ] of
        (dp : _) -> Just dp
        [] -> Nothing
    hasContrary a b =
      any
        (\c -> case c of Contrary (AtomPat x _) (AtomPat y _) -> x == a && y == b)
        (unitContraries u)

-- | @attach-reinstate@: @attach-undercut@ (a rule-rooted attacker undercutting
-- the support) plus a second undercut defeating that attacker (E4 context X).
-- The attacker is a fresh defeasible rule concluding the support rule's
-- exception atom, so it is itself undercuttable; an injected exception on that
-- rule licenses an unattacked leaf defender to undercut it. The defender is IN,
-- the attacker OUT, and the support is reinstated IN — the claim is @justified@,
-- under attack.
opAttachReinstate :: String -> CheckInput -> [Mutant]
opAttachReinstate base input =
  acceptMutant base input OpAttachReinstate Justified $
    u
      { unitRules = unitRules u ++ [mutRule]
      , unitExceptions = unitExceptions u ++ [Exception mutRuleId (groundPat defP)]
      , unitLeaves = unitLeaves u ++ [(premLeaf, premP), (defLeaf, defP)]
      , unitArgs =
          unitArgs u
            ++ [ (attackerArg, SRule mutRuleId [] [SLeaf premLeaf] [] [] AssuranceNone)
               , (defenderArg, SLeaf defLeaf)
               ]
      , unitAttacks =
          unitAttacks u
            ++ [Undercut attackerArg aidS [], Undercut defenderArg attackerArg []]
      , unitSigma =
          declarePred (propPred premP) []
            (declarePred (propPred defP) [] (unitSigma u))
      }
  where
    u = inputUnit input
    (aidS, r, theta, _) = theSupport base u (theQuery base u)
    excP = exceptionProp base u r theta
    mutRuleId = RuleId "mut_reinstate_rule"
    premLeaf = LeafId "mut_reinstate_premise"
    defLeaf = LeafId "mut_reinstate_defender"
    premP = Prop (Pred "mut_reinstate_premise") []
    defP = Prop (Pred "mut_reinstate_defeated") []
    mutRule = Rule mutRuleId [] Defeasible [groundPat premP] [] (groundPat excP) False [] []
