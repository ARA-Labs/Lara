-- | Hand-linked runner for the map property modules only.
--
-- The package's test suite is one executable with no selector, so iterating on
-- a map property means running all 45 modules. This runner links exactly the
-- five map modules and nothing else, which is what makes a map-only run cheap
-- enough to do after every edit. It is a developer tool, not a gate: CI runs
-- the real suite, and every property here is registered there too.
--
-- Build and run from the package root:
--
--     cabal exec -- runghc -itest scripts/map-props-runner.hs
module Main (main) where

import System.Exit (exitFailure, exitSuccess)
import Test.QuickCheck (Result, isSuccess)

import MapExampleSpec (mapExampleSpecProps)
import MapLinkSpec (mapLinkSpecProps)
import MapLoadSpec (mapLoadSpecProps)
import MapSpec (mapSpecProps)
import MapWireSpec (mapWireSpecProps)

main :: IO ()
main = do
  results <- mapM run (concat groups)
  let failed = length (filter not results)
  putStrLn
    ( show (length results) ++ " map properties, "
        ++ show (length results - failed) ++ " passed, "
        ++ show failed ++ " failed"
    )
  if failed == 0 then exitSuccess else exitFailure
  where
    groups =
      [ mapSpecProps
      , mapWireSpecProps
      , mapLoadSpecProps
      , mapLinkSpecProps
      , mapExampleSpecProps
      ]
    run :: (String, IO Result) -> IO Bool
    run (name, act) = do
      putStrLn ("=== " ++ name)
      isSuccess <$> act
