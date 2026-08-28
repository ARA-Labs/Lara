-- | Shared generators and constructors for small argumentation frameworks.
module TestAF (genAF, naiveAF) where

import Test.QuickCheck (Gen, choose, sized, vectorOf)

import Lara.Grounded (AF (..))

-- | A random framework as an explicit edge relation over @[0..n-1]@.
-- Random pairs over the carrier naturally include self-loops, cycles, and
-- isolated arguments. The QuickCheck size bounds the carrier at 12 arguments;
-- callers can use 'Test.QuickCheck.resize' to impose a smaller cap when their
-- algorithm scans the powerset.
genAF :: Gen (Int, [(Int, Int)])
genAF = sized $ \size -> do
  n <- choose (0, min 12 size)
  edges <-
    if n == 0
      then pure []
      else do
        k <- choose (0, 20)
        vectorOf k ((,) <$> choose (0, n - 1) <*> choose (0, n - 1))
  pure (n, edges)

-- | A naive un-memoised framework whose attack predicate scans the edge list.
naiveAF :: Int -> [(Int, Int)] -> AF
naiveAF n edges = AF [0 .. n - 1] (\b a -> (b, a) `elem` edges)
