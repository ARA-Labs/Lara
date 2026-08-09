-- | The shared IO loader for the mechanical-reviewer renderer (#63, D2): the one
-- place that, per corpus unit, decodes its @unit.core.sexp@ wire anchor and
-- parses its @unit.lara@ surface, returning exactly the triple
-- "Lara.MechReview".'Lara.MechReview.renderReviews' consumes.
--
-- Both the renderer (@scripts\/render-reviews.hs@) and the freshness guard
-- (@test\/MechReviewSpec.hs@) call THIS module, so the per-unit IO cannot drift
-- between them — the same discipline "Lara.ClaimSupport.Load" applies to the
-- claim-support pass.
--
-- A decode\/parse failure is a hard 'error': every frozen corpus unit decodes
-- and parses, so any failure here means the freeze or a decode path drifted.
module Lara.MechReview.Load
  ( loadReviewUnit
  , loadReviewUnits
  ) where

import Lara.AST (Program)
import Lara.Elaborate.Comparison (expandClaimNls)
import Lara.Measure (InputMeta (..), parseCorpusManifest)
import Lara.Replay (CheckInput)
import Lara.Syntax (parseProgram)
import Lara.Wire (decodeCheckInputFile)

-- | Decode one unit's core and parse its @.lara@ surface, tagged with the
-- manifest unit name (@artifact.claim@).
loadReviewUnit :: InputMeta -> IO (String, CheckInput, Program)
loadReviewUnit im = do
  coreBytes <- readFile (imPath im)
  ci <- case decodeCheckInputFile coreBytes of
    Left err -> error ("render-reviews: wire decode failed (" ++ imPath im ++ "): " ++ show err)
    Right ok -> pure ok
  laraBytes <- readFile laraPath
  parsed <- case parseProgram laraBytes of
    Left err -> error ("render-reviews: surface parse failed (" ++ laraPath ++ "): " ++ show err)
    Right ok -> pure ok
  prog <- case expandClaimNls parsed of
    Left err -> error ("render-reviews: nl expansion failed (" ++ laraPath ++ "): " ++ show err)
    Right ok -> pure ok
  pure (imBase im, ci, prog)
  where
    laraPath = replaceCoreSuffix (imPath im)

-- | Load every unit named by a corpus manifest, in manifest order.
loadReviewUnits :: FilePath -> IO [(String, CheckInput, Program)]
loadReviewUnits manifestPath = do
  manifest <- readFile manifestPath
  mapM loadReviewUnit (parseCorpusManifest manifest)

-- | @…\/unit.core.sexp@ ⇒ @…\/unit.lara@ (the surface sibling of the core file).
replaceCoreSuffix :: FilePath -> FilePath
replaceCoreSuffix path
  | core `isSuffixOf'` path = take (length path - length core) path ++ "unit.lara"
  | otherwise = path
  where
    core = "unit.core.sexp"
    isSuffixOf' s xs = reverse s `isPrefixOf'` reverse xs
    isPrefixOf' [] _ = True
    isPrefixOf' _ [] = False
    isPrefixOf' (a : as) (b : bs) = a == b && isPrefixOf' as bs
