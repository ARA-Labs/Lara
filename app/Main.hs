-- | A \"hello, kernel\" demo: build one derivation by hand and check it.
--
-- Claim to justify: @(c0 · x) : Q@, from
--   * constant @c0@ justifying the axiom instance @P → Q@, and
--   * hypothesis @x : P@.
-- Then show sum-monotonicity: wrapping the term in @+ y@ still checks.
module Main (main) where

import Lara.ConstantSpec (emptyContext, emptySpec, insertContext, insertSpec)
import Lara.Formula (Atom (..), Formula (..))
import Lara.Kernel (Derivation (..), check, judgmentFormula, judgmentTerm)
import Lara.Term (Con (..), Term (..), Var (..), prettyTerm)
import Lara.Formula (prettyFormula)

main :: IO ()
main = do
  let p = FAtom (Atom "P")
      q = FAtom (Atom "Q")
      c0 = Con "c0"
      x = Var "x"
      y = Var "y"

      spec = insertSpec c0 (Imp p q) emptySpec
      ctx = insertContext x p (insertContext y p emptyContext)

      -- (c0 · x) : Q
      modusPonens = DApp (DConst c0 (Imp p q)) (DHyp x p)
      -- ((c0 · x) + y) : Q   — monotonicity: extra evidence never invalidates
      withSummand = DSumL modusPonens (TVar y)

  report "modus ponens" (check spec ctx modusPonens)
  report "sum monotonicity" (check spec ctx withSummand)
  where
    report label result = do
      putStr (label ++ ": ")
      case result of
        Left err -> putStrLn ("REJECTED — " ++ show err)
        Right j ->
          putStrLn (prettyTerm (judgmentTerm j) ++ " : " ++ prettyFormula (judgmentFormula j))
