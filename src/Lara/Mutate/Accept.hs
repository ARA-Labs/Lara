-- | The accept-verdict mutation family (M5, T1 status/attack half).
--
-- The rejection operators of "Lara.Mutate.Suite" produce rejects; T1 also requires
-- generated mutants that exercise __every claim status and every attack kind__.
-- This family supplies that half: six /accept-verdict/ operators over the nine
-- @justified@ corpus units, each constructing an attack against @corpus-v1@'s
-- licensing (the E4\/E5 worked-example templates, instantiated per unit) so the
-- queried claim lands at a specified status while the verdict still ACCEPTS.
--
-- This module is the family's __facade__ and its whole public surface: which
-- operators run and in what order ('acceptMutants'), which bases they run on
-- ('isJustified'), and whether the result is the mutant that was asked for
-- ('acceptStructureOk'). The parts it composes were split out along
-- the seam @docs\/mutate-module-ownership-decision.md@ records:
--
-- * "Lara.Mutate.Accept.Ops" — the six constructions, and the injected
--   vocabulary each needs.
-- * "Lara.Mutate.Accept.Build" — mutant assembly, the asserted justified-unit
--   invariants, and the attack-site helpers the operators locate through.
--
-- Every construction assumes the justified-unit invariant — exactly one query,
-- with exactly one supporting argument (plan D13\/OV-11) — and the assembly
-- layer ASSERTS it loudly: a future multi-argument justified unit must fail
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

import Data.List (elemIndex)

import Lara.AST hiding (Reject)
import Lara.Driver (prune, pruneChecked, runCheck)
import Lara.Mutate (Expected (..), Mutant, MutationOp (..))
import Lara.Mutate.Accept.Build (argConclusion, attackerArg, defenderArg)
import Lara.Mutate.Accept.Ops
  ( opAttachRebutCycle
  , opAttachReinstate
  , opAttachUndercut
  , opAttachUndermine
  , opDropSupport
  , opQuarantineAttacker
  )
import Lara.Replay (CheckInput, inputUnit)
import Lara.Wire (Outcome (..), PublicStatus (..), Verdict (..))

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
  -- (spec §4.3): such a query is never counted justified.
  Verdict _ (Accept _ _ statuses) -> case unitQueries (inputUnit input) of
    [q] -> lookup q statuses == Just (Published Justified)
    _ -> False
  _ -> False

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
        -- match the operator's specified one (spec §4.3).
        ExpectPrimaryStatus status -> (mq >>= (`lookup` statuses)) == Just (Published status)
        -- The quarantine class: the query must be published
        -- @evidence-blocked@, and its conditional label must be @justified@ —
        -- pinning that the prune really would have promoted the claim, so the
        -- mutant witnesses the hazard rather than an inert edit.
        ExpectEvidenceBlocked ->
          (mq >>= (`lookup` statuses)) == Just (EvidenceBlocked Justified)
        _ -> False
      -- Verdict labels are indexed by the __checked__ argument list, which a
      -- §4.3 prune can make shorter than the declared one. Looking
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
