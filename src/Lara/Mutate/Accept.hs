-- | The accept-verdict mutation family (M5 tracker #48, T1 status/attack half).
--
-- The rejection operators of "Lara.Mutate" produce rejects; #48 also requires
-- generated mutants that exercise __every claim status and every attack kind__.
-- This module supplies that half: five /accept-verdict/ operators over the nine
-- @justified@ corpus units, each constructing an attack against @corpus-v1@'s
-- licensing (the E4\/E5 worked-example templates, instantiated per unit) so the
-- queried claim lands at a specified status while the verdict still ACCEPTS.
--
-- > operator            construction                                   status
-- > drop-support        remove the claim's support arg (E2-style)      gap
-- > attach-undercut     leaf arg on the rule's exception, undercut      defeated
-- > attach-undermine    leaf arg contrary to a premise, undermine      defeated
-- > attach-rebut-cycle  leaf arg on a symmetric contrary, mutual rebut  contested
-- > attach-reinstate    attach-undercut + a counter-undercut (E4)       justified
--
-- Where a construction needs vocabulary @corpus-v1@ lacks, the mutant injects it
-- as a /declared/ extension in the unit's policy image (a new leaf proposition,
-- a one-directional or symmetric contrary, or — for reinstatement — a defeasible
-- rule plus its exception). This is legal precisely because these mutants must
-- ACCEPT: every rule stays defeasible, so nothing is smuggled past R12, and the
-- checker verifies the whole construction at generation time.
--
-- Every construction assumes the justified-unit invariant — exactly one query,
-- with exactly one supporting argument (plan D13\/OV-11) — and ASSERTS it loudly
-- ('theQuery' \/ 'theSupport'): a future multi-argument justified unit must fail
-- generation with a clear message, never surface as a confusing verdict.
--
-- Outcomes are verified structurally, not by final status alone
-- ('acceptStructureOk', eng review D7\/4A): status-only verification would pass
-- vacuously on a no-op @attach-reinstate@ whose specified status equals the base
-- status. @scripts\/gen-mutants.hs@ and @test\/MutationSpec.hs@ both call
-- 'acceptStructureOk'.
module Lara.Mutate.Accept
  ( acceptMutants
  , acceptStructureOk
  ) where

import Data.List (elemIndex, find)

import Lara.AST hiding (Reject)
import Lara.Driver (prune, pruneChecked, runCheck)
import Lara.Mutate (Expected (..), Mutant (..), MutationOp (..), mutantFileName)
import Lara.Prop (Prop (..), Term)
import Lara.Replay
  ( CheckInput
  , inputReplayId
  , inputUnit
  , mkCheckInput
  )
import Lara.SupportTerm (instAPat)
import Lara.Wire (Outcome (..), PublicStatus (..), Verdict (..), encodeCheckInput, printSExpr)

-- ---------------------------------------------------------------------------
-- Generation
-- ---------------------------------------------------------------------------

-- | Every accept-verdict mutant of the justified corpus units, base-major then
-- operator order. A unit is /justified/ iff its single query accepts with status
-- 'Justified' (self-gating via the checker, exactly the T2 @expected_status@);
-- non-justified bases contribute nothing. @scripts\/gen-mutants.hs@ and
-- @test\/MutationSpec.hs@ pass the same corpus-base list, so the output matches
-- byte-for-byte.
acceptMutants :: [(String, CheckInput)] -> [Mutant]
acceptMutants bases =
  [ m
  | (base, input) <- bases
  , isJustified input
  , op <- operators
  , m <- op base input
  ]
  where
    operators =
      [ opDropSupport
      , opAttachUndercut
      , opQuarantineAttacker
      , opAttachRebutCycle
      , opAttachUndermine
      , opAttachReinstate
      ]

-- | Whether a corpus unit's single query is @justified@ (an accept whose one
-- queried status is 'Justified').
isJustified :: CheckInput -> Bool
isJustified input = case runCheck input of
  -- The conditional label of an @evidence-blocked@ query is not its status
  -- (spec §4.3, issue #76): such a query is never counted justified.
  Verdict _ (Accept _ _ statuses) -> case unitQueries (inputUnit input) of
    [q] -> lookup q statuses == Just (Published Justified)
    _ -> False
  _ -> False

-- | Assemble one accept mutant from a mutated unit (specified primary status),
-- or nothing if the mutated identity fails to reassemble (unreachable for these
-- theory-preserving edits).
acceptMutant :: String -> CheckInput -> MutationOp -> Status -> Unit -> [Mutant]
acceptMutant base input op status = acceptMutantWith base input op (ExpectPrimaryStatus status)

-- | 'acceptMutant' for the conservative-reporting class: the mutant accepts, but
-- the queried claim's public status is @evidence-blocked@ (spec §4.3, #76).
acceptMutantBlocked :: String -> CheckInput -> MutationOp -> Unit -> [Mutant]
acceptMutantBlocked base input op = acceptMutantWith base input op ExpectEvidenceBlocked

acceptMutantWith :: String -> CheckInput -> MutationOp -> Expected -> Unit -> [Mutant]
acceptMutantWith base input op expected u' =
  [ Mutant (mutantFileName base op 0) base op expected Nothing bytes
  | Right mutated <- [mkCheckInput (inputReplayId input) u']
  , let bytes = printSExpr (encodeCheckInput mutated) ++ "\n"
  ]

-- ---------------------------------------------------------------------------
-- Justified-unit invariants (asserted, plan D13/OV-11)
-- ---------------------------------------------------------------------------

-- | The unit's single query (errors loudly if not exactly one).
theQuery :: String -> Unit -> Prop
theQuery base u = case unitQueries u of
  [q] -> q
  qs ->
    error
      ( "Lara.Mutate.Accept: " ++ base ++ " must have exactly one query, has "
          ++ show (length qs)
      )

-- | The unit's single supporting argument for the query — a rule-rooted arg
-- whose conclusion is the query (errors loudly if not exactly one).
theSupport :: String -> Unit -> Prop -> (ArgId, RuleId, Subst, SupportTerm)
theSupport base u q =
  case [ (aid, r, theta, t)
       | (aid, t@(SRule r theta _ _ _ _)) <- unitArgs u
       , argConclusion u t == Just q
       ] of
    [s] -> s
    ss ->
      error
        ( "Lara.Mutate.Accept: " ++ base
            ++ " expected exactly one rule-rooted supporting arg for the query, found "
            ++ show (length ss)
        )

-- | An argument's conclusion proposition (a rule-rooted arg instantiates its
-- rule's conclusion; a leaf arg is its leaf's proposition).
argConclusion :: Unit -> SupportTerm -> Maybe Prop
argConclusion u t = case t of
  SLeaf l -> lookup l (unitLeaves u)
  SRule r theta _ _ _ _ -> ruleOf u r >>= instAPat theta . ruleConclusion

ruleOf :: Unit -> RuleId -> Maybe Rule
ruleOf u r = find ((== r) . ruleId) (unitRules u)

-- | The instantiated exception atom licensing an undercut of a rule instance
-- (the first declared exception for the rule; every @corpus-v1@ rule has one).
exceptionProp :: String -> Unit -> RuleId -> Subst -> Prop
exceptionProp base u r theta =
  case [ p | e <- unitExceptions u, exceptionRule e == r, Just p <- [instAPat theta (exceptionAtom e)] ] of
    (p : _) -> p
    [] ->
      error
        ("Lara.Mutate.Accept: " ++ base ++ " rule " ++ show r ++ " has no instantiable exception")

-- | The first premise of a rule-rooted support arg that is a leaf: its position
-- and proposition (the undermine target). Every @corpus-v1@ support arg has one.
firstPremiseLeaf :: String -> Unit -> SupportTerm -> (Position, Prop)
firstPremiseLeaf base u (SRule _ _ premises _ _ _) =
  case [ (i, l) | (i, SLeaf l) <- zip [0 ..] premises ] of
    ((i, l) : _) -> case lookup l (unitLeaves u) of
      Just p -> ([StepPremise i], p)
      Nothing -> error ("Lara.Mutate.Accept: " ++ base ++ " premise leaf missing from Gamma")
    [] -> error ("Lara.Mutate.Accept: " ++ base ++ " support arg has no leaf premise to undermine")
firstPremiseLeaf base _ _ =
  error ("Lara.Mutate.Accept: " ++ base ++ " support arg is not rule-rooted")

-- ---------------------------------------------------------------------------
-- The five operators
-- ---------------------------------------------------------------------------

attackerArg, defenderArg :: ArgId
attackerArg = ArgId "mut_attacker"
defenderArg = ArgId "mut_defender"

-- | A ground atom pattern verbatim from a proposition (for injected contraries,
-- exceptions, and rule heads).
groundPat :: Prop -> AtomPat
groundPat (Prop p ts) = AtomPat p (map PLit ts)

propArgs :: Prop -> [Term]
propArgs (Prop _ ts) = ts

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

-- | @quarantine-attacker@ (spec §4.3, issue #76): @attach-undercut@'s
-- construction, plus a @≢@ duplicate-report group that quarantines the
-- attacker's own leaf.
--
-- The checker therefore drops the undercutter and its attack before checking and
-- sees the support argument /unattacked/ — the pruned graph says @justified@,
-- the same status the unmutated unit had. That is the promotion hazard: the
-- claim looks exactly as strong as before even though the evidence deciding its
-- only objection turned out to be internally inconsistent. The mutant must
-- therefore come back @accept-evidence-blocked@; an ordinary @accept-justified@
-- here is the #76 bug.
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
      }
  where
    u = inputUnit input
    q = theQuery base u
    (aidS, _, _, _) = theSupport base u q
    (dualP, injected) = dualOf u q
    mutRuleId = RuleId "mut_rebut_rule"
    premLeaf = LeafId "mut_rebut_premise"
    premP = Prop (Pred "mut_rebut_premise") []
    mutRule = Rule mutRuleId [] Defeasible [groundPat premP] (groundPat dualP) False [] []

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
    mutRule = Rule mutRuleId [] Defeasible [groundPat premP] (groundPat excP) False [] []

attackEndpoints :: Attack -> [ArgId]
attackEndpoints k = case k of
  Rebut w v -> [w, v]
  Undercut w v _ -> [w, v]
  Undermine w v _ -> [w, v]

-- ---------------------------------------------------------------------------
-- Structural verification (eng review D7/4A)
-- ---------------------------------------------------------------------------

-- | Whether an accept mutant's verdict has the operator's specified status AND
-- the constructed attack shape (not status alone — a no-op @attach-reinstate@
-- would pass status-only vacuously). The constructed args have fixed ids
-- (@mut_attacker@\/@mut_defender@); the support arg is the one concluding the
-- query. Grounded labels come from the verdict.
acceptStructureOk :: MutationOp -> Expected -> CheckInput -> Verdict -> Bool
acceptStructureOk op expected input (Verdict _ outcome) = case outcome of
  Reject _ -> False
  Accept labels _edges statuses -> statusOk && shapeOk
    where
      u = inputUnit input
      mq = case unitQueries u of
        [q] -> Just q
        _ -> Nothing
      statusOk = case expected of
        -- A blocked query has no four-state public status, so it can never
        -- match the operator's specified one (spec §4.3, issue #76).
        ExpectPrimaryStatus status -> (mq >>= (`lookup` statuses)) == Just (Published status)
        -- The quarantine class: the query must be published
        -- @evidence-blocked@, and its conditional label must be @justified@ —
        -- pinning that the prune really would have promoted the claim, so the
        -- mutant witnesses the hazard rather than an inert edit.
        ExpectEvidenceBlocked ->
          (mq >>= (`lookup` statuses)) == Just (EvidenceBlocked Justified)
        _ -> False
      -- Verdict labels are indexed by the __checked__ argument list, which a
      -- §4.3 prune can make shorter than the declared one (issue #76). Looking
      -- the id up in the declared list would read the wrong label for any
      -- operator that quarantines a non-final argument.
      labelOf aid =
        elemIndex aid (map fst (unitArgs (pruneChecked (prune u)))) >>= (`lookup` labels)
      attacker = labelOf attackerArg
      defender = labelOf defenderArg
      support = supportArgId u mq >>= labelOf
      shapeOk = case op of
        OpDropSupport -> supportArgId u mq == Nothing
        OpAttachUndercut -> attacker == Just LIn && support == Just LOut
        OpAttachUndermine -> attacker == Just LIn && support == Just LOut
        OpAttachRebutCycle -> attacker == Just LUndec && support == Just LUndec
        OpAttachReinstate -> attacker == Just LOut && defender == Just LIn && support == Just LIn
        -- The undercutter was quarantined away, so it is not in the checked AF
        -- at all and the support stands unattacked in the pruned graph.
        OpQuarantineAttacker -> attacker == Nothing && support == Just LIn
        _ -> False
  where
    -- The argument (other than the constructed attacker/defender) whose
    -- conclusion is the query. Kept at equation level (taking @u@/@mq@ as
    -- explicit arguments rather than closing over the branch-local bindings) so
    -- it stays a standalone pure helper usable from either branch.
    supportArgId u mq = do
      q <- mq
      case [ aid
           | (aid, t) <- unitArgs u
           , aid /= attackerArg
           , aid /= defenderArg
           , argConclusion u t == Just q
           ] of
        (aid : _) -> Just aid
        [] -> Nothing
