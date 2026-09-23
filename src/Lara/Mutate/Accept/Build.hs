-- | Mutant assembly and the justified-unit invariants the accept-verdict
-- constructions build on (split out of "Lara.Mutate.Accept").
--
-- Two things live here, both /below/ the operators in
-- "Lara.Mutate.Accept.Ops" so that module can call them:
--
-- * __Assembly__ — 'acceptMutantWith' and its two specializations turn an
--   edited 'Unit' into a 'Mutant', re-deriving the check identity and printing
--   the wire bytes. Every operator emits through exactly this path, which is
--   why the generated suite is byte-stable under a code move.
--
-- * __Invariants and sites__ — 'theQuery' \/ 'theSupport' assert the
--   justified-unit shape (exactly one query, exactly one rule-rooted
--   supporting argument — plan D13\/OV-11) and 'exceptionProp' \/
--   'firstPremiseLeaf' locate the constituent an attack is attached to. The
--   assertions 'error' loudly on purpose: a future multi-argument justified
--   unit must fail generation with a clear message, never surface as a
--   confusing verdict. Their messages name @Lara.Mutate.Accept@, the public
--   entry point, not this module.
module Lara.Mutate.Accept.Build
  ( -- * Assembly
    acceptMutant
  , acceptMutantBlocked
  , acceptMutantWith

    -- * Justified-unit invariants
  , theQuery
  , theSupport
  , argConclusion
  , exceptionProp
  , firstPremiseLeaf

    -- * Attack sites and proposition helpers
  , attackerArg
  , defenderArg
  , groundPat
  , propArgs
  , propPred
  , attackEndpoints
  ) where

import Data.List (find)

import Lara.AST hiding (Reject)
import Lara.Mutate (Expected (..), Mutant (..), MutationOp, mutantFileName)
import Lara.Prop (Prop (..), Term)
import Lara.Replay
  ( CheckInput
  , inputReplayId
  , mkCheckInput
  )
import Lara.SupportTerm (instAPat)
import Lara.Wire (encodeCheckInput, printSExpr)

-- ---------------------------------------------------------------------------
-- Assembly
-- ---------------------------------------------------------------------------

-- | Assemble one accept mutant from a mutated unit (specified primary status),
-- or nothing if the mutated identity fails to reassemble (unreachable for these
-- theory-preserving edits).
acceptMutant :: String -> CheckInput -> MutationOp -> Status -> Unit -> [Mutant]
acceptMutant base input op status = acceptMutantWith base input op (ExpectPrimaryStatus status)

-- | 'acceptMutant' for the conservative-reporting class: the mutant accepts, but
-- the queried claim's public status is @evidence-blocked@ (spec §4.3).
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
-- Attack sites and proposition helpers
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

propPred :: Prop -> Pred
propPred (Prop p _) = p

attackEndpoints :: Attack -> [ArgId]
attackEndpoints k = case k of
  Rebut w v -> [w, v]
  Undercut w v _ -> [w, v]
  Undermine w v _ -> [w, v]
