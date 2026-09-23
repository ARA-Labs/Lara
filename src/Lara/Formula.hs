-- | Formulas of the Logic of Proofs.
--
-- The propositional skeleton (atoms, falsum, implication) plus the defining
-- LP connective @'Col' t F@ read as \"@t@ justifies @F@\" (written @t : F@).
-- Other connectives are omitted from this minimal core on purpose; add them
-- only when the Phase-0 spec fixes the fragment.
module Lara.Formula
  ( Atom (..)
  , Formula (..)
  , prettyFormula
  ) where

import Lara.Term (Term, prettyTerm)

-- | A propositional atom.
newtype Atom = Atom String
  deriving (Eq, Ord, Show)

-- | The grammar of formulas.
data Formula
  = FAtom Atom            -- ^ atom @p@
  | Bot                   -- ^ falsum @⊥@
  | Imp Formula Formula   -- ^ implication @F '→' G@
  | Col Term Formula      -- ^ justification assertion @t ':' F@
  deriving (Eq, Ord, Show)

-- | Human-readable rendering, e.g. @(c0 · x) : (P → Q)@.
prettyFormula :: Formula -> String
prettyFormula = go
  where
    go (FAtom (Atom p)) = p
    go Bot              = "⊥"
    go (Imp f g)        = "(" ++ go f ++ " → " ++ go g ++ ")"
    go (Col t f)        = prettyTerm t ++ " : " ++ go f
