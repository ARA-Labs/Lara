-- | D2 — mechanical reviewer (#63): the IO around the pure
-- "Lara.MechReview" renderer. One command that turns the checker's own per-claim
-- verdicts over the frozen 60-unit corpus sample
-- (@corpus-units\/MANIFEST.tsv@, seed 20260801) into reviewer-style markdown — one review
-- comment per non-@justified@ claim, generated from the located diagnostics, NOT
-- from an LLM and with no new trusted code.
--
-- Discovery is manifest-driven (never a glob), reusing
-- 'Lara.Measure.parseCorpusManifest'. The per-unit decode + surface parse live in
-- 'Lara.MechReview.Load', shared with the freshness test so the two cannot
-- drift. Haskell-only, deterministic: no Lean subprocess, no timing, no
-- environment block — the rendered document is a pure function of the corpus.
--
-- Output: @measurements\/frozen\/mechanical-reviews.md@ — the committed golden
-- itself (unlike @claim-support.hs@, whose JSON carries an environment block and
-- so lands under @measurements\/@ first). The content here is env-free, so the
-- renderer writes the frozen deliverable directly and re-running reproduces the
-- committed bytes byte-for-byte.
--
-- Run with the built library on the path:
--
-- >  cabal exec -- runghc scripts/render-reviews.hs
module Main (main) where

import Control.Monad (when)
import System.Directory (createDirectoryIfMissing)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Lara.MechReview (renderReviews)
import Lara.MechReview.Load (loadReviewUnits)

manifestPath, policyPath :: FilePath
manifestPath = "corpus-units/MANIFEST.tsv"
policyPath = "corpus-units/corpus-v1.policy.lara"

outputPath :: FilePath
outputPath = "measurements/frozen/mechanical-reviews.md"

main :: IO ()
main = do
  units <- loadReviewUnits manifestPath policyPath
  when (null units) (die ("no corpus units discovered from " ++ manifestPath))
  createDirectoryIfMissing True "measurements/frozen"
  writeFile outputPath (renderReviews units)
  putStrLn
    ( "wrote mechanical-reviewer reviews over " ++ show (length units)
        ++ " corpus units to " ++ outputPath
    )

die :: String -> IO a
die msg = hPutStrLn stderr ("render-reviews: " ++ msg) >> exitFailure
