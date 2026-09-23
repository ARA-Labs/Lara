-- | Emit the running example's pinned checker reports (P6).
--
-- Thin IO shim over the pure "Lara.RunningExample": load both run programs,
-- check them through the CLI's own pipeline, and write the golden document
-- the paper pastes from. Writes directly to the frozen path — the rendering
-- is environment-free, so re-running reproduces the committed bytes, and
-- @test\/RunningExampleSpec.hs@ enforces exactly that.
--
-- Run with the built library on the path:
--
-- >  cabal exec -- runghc scripts/render-running-example.hs
module Main (main) where

import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Lara.RunningExample (checkRun, goldenPath, loadRun, renderRuns, runPaths)

main :: IO ()
main = do
  runs <- mapM checkOne runPaths
  writeFile goldenPath (renderRuns runs)
  putStrLn ("wrote " ++ show (length runs) ++ " run reports to " ++ goldenPath)
  where
    checkOne path = do
      (progText, polText) <- loadRun path
      case checkRun progText polText of
        Left err -> do
          hPutStrLn stderr ("render-running-example: " ++ path ++ ": " ++ err)
          exitFailure
        Right verdict -> pure (path, verdict)
