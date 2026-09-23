-- | Pattern instantiation and __one-way matching__ over the policy's atom
-- patterns: the substitution machinery the elaborator needs, with no error
-- vocabulary of its own.
--
-- Two directions, sharing one notion of equality:
--
--   * 'apatToProp' \/ 'patToTerm' — instantiate a pattern under a known θ (the
--     @lara-syntax\@0.2@ direction: θ is supplied positionally in the surface
--     and premises are then /looked up/ by @≡@-match);
--   * 'matchAPat' \/ 'matchPat' — /derive/ θ by matching a pattern against an
--     already-ground proposition (the @lara-syntax\@0.3@ direction, needed by
--     the @comparison@ expansion, grammar App. B.3 and plan §5 step 3).
--
-- The matcher is one-way: only the /pattern/ side may bind. It never
-- instantiates a variable on the ground side, because there is no variable
-- there — a 'Prop' is ground by construction (spec §3).
--
-- __One notion of equality.__ A variable bound twice must agree under
-- "Lara.Prop"'s normal form ('Lara.Prop.nfTerm', the term half of @≡@), which
-- is the same relation @resolvePremises@ uses through 'Lara.Prop.equiv'. There
-- is deliberately no second equality here: were the matcher to compare terms
-- syntactically, @0.71@ and @0.710@ would bind inconsistently while the very
-- same pair matched a premise, and the two halves of the elaborator would
-- disagree about what a rule instance means.
module Lara.Elaborate.Subst
  ( -- * Instantiation
    apatToProp
  , patToTerm
    -- * One-way matching
  , MatchFailure (..)
  , matchAPat
  , matchPat
  , sameTerm
  ) where

import Control.Monad (foldM)

import Lara.AST
import Lara.Prop (Prop (..), Term (..), nfTerm)

-- ---------------------------------------------------------------------------
-- Instantiation
-- ---------------------------------------------------------------------------

-- | Instantiate an atom pattern to a ground proposition under θ.
apatToProp :: Subst -> AtomPat -> Prop
apatToProp theta (AtomPat p ps) = Prop p (map (patToTerm theta) ps)

-- | Instantiate a pattern to a ground term under θ, reclassifying a bare
-- identifier the parser recorded as a 'PVar': it is a parameter iff it is in
-- θ's domain (= the rule's declared parameters), otherwise a ground constant
-- (grammar §2).
patToTerm :: Subst -> Pat -> Term
patToTerm theta (PVar prm@(Param x)) = case lookup prm theta of
  Just t -> t
  Nothing -> TCon (FunSym x) []
patToTerm _ (PLit t) = t
patToTerm theta (PCon k ps) = TCon k (map (patToTerm theta) ps)

-- ---------------------------------------------------------------------------
-- One-way matching
-- ---------------------------------------------------------------------------

-- | Why a one-way match failed. The two arms are distinguished because they
-- mean different things to an author: 'MatchShape' says "this leaf is not of
-- this premise's shape at all" (so the elaborator keeps looking at other
-- slots), while 'MatchConflict' says "this leaf /is/ of that shape but disagrees
-- with a binding already derived" — the domain fact App. B.2 wants reported
-- with both leaves and the conflicting binding named.
data MatchFailure
  = -- | predicate, arity, constructor, or literal mismatch.
    MatchShape
  | -- | the parameter, its existing binding, and the conflicting one.
    MatchConflict Param Term Term
  deriving (Eq, Show)

-- | One-way match an atom pattern against a ground proposition, extending the
-- accumulated substitution. Bindings already in the input substitution
-- participate: re-binding one to a different term is a 'MatchConflict', which
-- is what makes θ-consistency across two leaves (and across the two rules of a
-- comparison scheme) a checkable property rather than a silent last-wins.
matchAPat :: Subst -> AtomPat -> Prop -> Either MatchFailure Subst
matchAPat sub (AtomPat pr pats) (Prop pr' ts)
  | pr /= pr' = Left MatchShape
  | length pats /= length ts = Left MatchShape
  | otherwise = foldM (\s (p, t) -> matchPat s p t) sub (zip pats ts)

-- | One-way match a pattern against a ground term (see 'matchAPat').
matchPat :: Subst -> Pat -> Term -> Either MatchFailure Subst
matchPat sub (PVar v) t = case lookup v sub of
  Nothing -> Right (sub ++ [(v, t)])
  Just t'
    | sameTerm t' t -> Right sub
    | otherwise -> Left (MatchConflict v t' t)
matchPat sub (PLit t') t
  | sameTerm t' t = Right sub
  | otherwise = Left MatchShape
matchPat sub (PCon k ps) (TCon k' ts)
  | k == k'
  , length ps == length ts =
      foldM (\s (p, t) -> matchPat s p t) sub (zip ps ts)
matchPat _ _ _ = Left MatchShape

-- | Term identity: the term half of "Lara.Prop"'s @≡@, so @0.710@ and @0.71@
-- are the same binding here exactly as they are the same proposition there.
sameTerm :: Term -> Term -> Bool
sameTerm a b = nfTerm a == nfTerm b
