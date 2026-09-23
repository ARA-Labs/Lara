-- | The trusted kernel: the LP proof-term checker.
--
-- == Trust boundary
--
-- This module is the /entire/ trusted base of the local-validity layer. Its
-- job is exactly one thing: decide whether an explicit 'Derivation' is a valid
-- construction of a justification assertion @t : F@ under a given constant
-- specification and hypothesis context.
--
-- The 'Judgment' type is __sealed__: its constructor is not exported, so the
-- only way any client can obtain a @Judgment@ is to call 'check' and have it
-- succeed. A value of type @Judgment@ is therefore a machine-checked
-- certificate that its @(term, formula)@ pair was built solely by the LP rules
-- below — the LCF discipline. Everything upstream (the LLM elaborator that
-- guesses derivations) is untrusted and cannot forge one.
--
-- The checker works on an /explicit derivation tree/ (the de Bruijn criterion:
-- check a proof object rather than search for one). This keeps the kernel a
-- straight structural recursion with no proof search and no inference of
-- intermediate formulas.
--
-- == Rules (LP term calculus)
--
-- > ─────────────── (Const)         c justifies f in the spec
-- >   c : f
-- >
-- > ─────────────── (Hyp)           x : f in the context
-- >   x : f
-- >
-- >   s : (A → B)    t : A
-- > ───────────────────────── (App)
-- >       (s · t) : B
-- >
-- >     s : A                        s : A
-- > ─────────────── (Sum-L)     ─────────────── (Sum-R)
-- >   (s + t) : A                  (t + s) : A
-- >
-- >        t : A
-- > ─────────────────── (Check / positive introspection)
-- >   (!t) : (t : A)
--
-- Monotonicity of @+@ (Sum-L/Sum-R never invalidate a justification) holds by
-- construction and is exercised by the property tests.
module Lara.Kernel
  ( -- * The sealed certificate
    Judgment
  , judgmentTerm
  , judgmentFormula
    -- * Explicit derivations (untrusted input)
  , Derivation (..)
    -- * Checking
  , CheckError (..)
  , check
  ) where

import Lara.ConstantSpec (ConstantSpec, Context, lookupContext, specFor)
import Lara.Formula (Formula (..))
import Lara.Term (Con, Term (..), Var)

-- | A checked @t : F@. Constructor intentionally hidden: only 'check' builds it.
data Judgment = Judgment Term Formula
  deriving (Eq, Show)

-- | The justification term of a checked judgment.
judgmentTerm :: Judgment -> Term
judgmentTerm (Judgment t _) = t

-- | The formula of a checked judgment.
judgmentFormula :: Judgment -> Formula
judgmentFormula (Judgment _ f) = f

-- | An explicit LP derivation. Clients (including the untrusted elaborator)
-- build these freely; validity is decided only by 'check'.
data Derivation
  = DConst Con Formula        -- ^ (Const) @c@ justifies axiom instance @f@
  | DHyp Var Formula          -- ^ (Hyp) hypothesis @x : f@
  | DApp Derivation Derivation -- ^ (App) from @s : A → B@ and @t : A@
  | DSumL Derivation Term     -- ^ (Sum-L) add right summand @t@ to @s : A@
  | DSumR Term Derivation     -- ^ (Sum-R) add left summand @s@ to @t : A@
  | DCheck Derivation         -- ^ (Check) positive introspection on @t : A@
  deriving (Eq, Show)

-- | Why a derivation failed to check.
data CheckError
  = UnknownConstant Con Formula
    -- ^ @c@ is not declared to justify @f@ in the spec.
  | UnboundVariable Var
    -- ^ hypothesis @x@ is absent from the context.
  | HypothesisMismatch Var Formula Formula
    -- ^ (Hyp) claimed formula vs. the one assumed for @x@ (context).
  | NotAnImplication Formula
    -- ^ (App) the function premise is not an implication.
  | ApplicationMismatch Formula Formula
    -- ^ (App) implication domain vs. argument formula disagree.
  deriving (Eq, Show)

-- | Check a derivation. On success the returned 'Judgment' certifies that its
-- @(term, formula)@ was produced only by the LP rules.
check :: ConstantSpec -> Context -> Derivation -> Either CheckError Judgment
check spec ctx = go
  where
    go :: Derivation -> Either CheckError Judgment
    go (DConst c f)
      | f `elem` specFor spec c = Right (Judgment (TCon c) f)
      | otherwise               = Left (UnknownConstant c f)
    go (DHyp x f) =
      case lookupContext ctx x of
        Nothing -> Left (UnboundVariable x)
        Just f'
          | f == f'   -> Right (Judgment (TVar x) f)
          | otherwise -> Left (HypothesisMismatch x f f')
    go (DApp df darg) = do
      jf <- go df
      jarg <- go darg
      case judgmentFormula jf of
        Imp a b
          | a == judgmentFormula jarg ->
              Right (Judgment (App (judgmentTerm jf) (judgmentTerm jarg)) b)
          | otherwise -> Left (ApplicationMismatch a (judgmentFormula jarg))
        other -> Left (NotAnImplication other)
    go (DSumL d t) = do
      j <- go d
      Right (Judgment (Sum (judgmentTerm j) t) (judgmentFormula j))
    go (DSumR t d) = do
      j <- go d
      Right (Judgment (Sum t (judgmentTerm j)) (judgmentFormula j))
    go (DCheck d) = do
      j <- go d
      let t = judgmentTerm j
      Right (Judgment (Bang t) (Col t (judgmentFormula j)))
