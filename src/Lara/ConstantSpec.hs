-- | The constant specification and the hypothesis context — the two leaf
-- sources the kernel closes against.
--
--   * A 'ConstantSpec' pins each proof constant @c@ to the axiom instances it
--     is declared to justify (LP's constant-specification mechanism). This is
--     where propositional tautologies and factivity instances get registered.
--   * A 'Context' assigns formulas to justification variables (hypotheses).
--
-- Both are plain finite maps: untrusted data handed to the kernel, which only
-- ever /reads/ them.
module Lara.ConstantSpec
  ( ConstantSpec
  , Context
    -- * Constant specification
  , emptySpec
  , insertSpec
  , specFor
    -- * Hypothesis context
  , emptyContext
  , insertContext
  , lookupContext
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Lara.Formula (Formula)
import Lara.Term (Con, Var)

-- | Maps each constant to the axiom instances it justifies.
newtype ConstantSpec = ConstantSpec (Map Con [Formula])
  deriving (Eq, Show)

-- | Maps each hypothesis variable to its assumed formula.
newtype Context = Context (Map Var Formula)
  deriving (Eq, Show)

-- | The empty constant specification.
emptySpec :: ConstantSpec
emptySpec = ConstantSpec Map.empty

-- | Declare that constant @c@ justifies axiom instance @f@.
insertSpec :: Con -> Formula -> ConstantSpec -> ConstantSpec
insertSpec c f (ConstantSpec m) = ConstantSpec (Map.insertWith (++) c [f] m)

-- | The axiom instances constant @c@ is declared to justify (empty if unknown).
specFor :: ConstantSpec -> Con -> [Formula]
specFor (ConstantSpec m) c = Map.findWithDefault [] c m

-- | The empty hypothesis context.
emptyContext :: Context
emptyContext = Context Map.empty

-- | Assume @x : f@.
insertContext :: Var -> Formula -> Context -> Context
insertContext x f (Context m) = Context (Map.insert x f m)

-- | The formula assumed for @x@, if any.
lookupContext :: Context -> Var -> Maybe Formula
lookupContext (Context m) x = Map.lookup x m
