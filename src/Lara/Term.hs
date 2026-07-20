-- | Justification terms of the Logic of Proofs (LP).
--
-- A term @t@ is a piece of evidence. The three operators are Artemov's:
--
--   * @'App' s t@  — application @s '·' t@: combine a justification of an
--     implication with a justification of its antecedent.
--   * @'Sum' s t@  — sum @s '+' t@: monotone choice; a justification stays
--     valid when further evidence is added on either side.
--   * @'Bang' t@   — proof checker @!t@: positive introspection, a
--     justification that @t@ itself justifies its formula.
--
-- Leaves are justification variables ('Var', hypotheses) and proof constants
-- ('Con', pinned to axioms by a 'Lara.ConstantSpec.ConstantSpec').
module Lara.Term
  ( Var (..)
  , Con (..)
  , Term (..)
  , prettyTerm
  ) where

-- | A justification variable (a hypothesis / assumed reason).
newtype Var = Var String
  deriving (Eq, Ord, Show)

-- | A proof constant (justifies an axiom via the constant specification).
newtype Con = Con String
  deriving (Eq, Ord, Show)

-- | The grammar of justification terms.
data Term
  = TVar Var          -- ^ hypothesis @x@
  | TCon Con          -- ^ constant @c@
  | App Term Term     -- ^ application @s '·' t@
  | Sum Term Term     -- ^ sum @s '+' t@
  | Bang Term         -- ^ proof checker @!t@
  deriving (Eq, Ord, Show)

-- | Human-readable rendering, e.g. @(c0 · x) + !y@.
prettyTerm :: Term -> String
prettyTerm = go
  where
    go (TVar (Var x)) = x
    go (TCon (Con c)) = c
    go (App s t)      = "(" ++ go s ++ " · " ++ go t ++ ")"
    go (Sum s t)      = "(" ++ go s ++ " + " ++ go t ++ ")"
    go (Bang t)       = "!" ++ go t
