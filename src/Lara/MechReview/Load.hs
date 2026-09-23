-- | Shared IO loader for the mechanical-review renderer.
--
-- Each surface is elaborated once against the supplied policy. The decoded core
-- must equal that elaboration's 'Unit', and the renderer receives the exact
-- semantic 'Program' returned by the same pass.
module Lara.MechReview.Load
  ( loadReviewUnit
  , loadReviewUnits
  ) where

import Lara.AST (Policy, Program)
import Lara.Elaborate.Internal (elaborateWithSemanticProgram, registryOf)
import Lara.Measure (InputMeta (..), parseCorpusManifest)
import Lara.Replay (CheckInput, inputUnit)
import Lara.Syntax (parsePolicy, parseProgram)
import Lara.Wire (decodeCheckInputFile)

-- | Decode one unit's core and elaborate its surface against the shared policy.
loadReviewUnit :: Policy -> InputMeta -> IO (String, CheckInput, Program)
loadReviewUnit policy im = do
  coreBytes <- readFile (imPath im)
  ci <- case decodeCheckInputFile coreBytes of
    Left err -> error ("render-reviews: wire decode failed (" ++ imPath im ++ "): " ++ show err)
    Right ok -> pure ok
  laraBytes <- readFile laraPath
  parsed <- case parseProgram laraBytes of
    Left err -> error ("render-reviews: surface parse failed (" ++ laraPath ++ "): " ++ show err)
    Right ok -> pure ok
  (surfaceUnit, _, semanticProgram) <-
    case elaborateWithSemanticProgram (registryOf policy) parsed policy of
      Left err -> error ("render-reviews: surface elaboration failed (" ++ laraPath ++ "): " ++ show err)
      Right ok -> pure ok
  if surfaceUnit /= inputUnit ci
    then error ("render-reviews: surface/core mismatch (" ++ laraPath ++ ")")
    else pure (imBase im, ci, semanticProgram)
  where
    laraPath = replaceCoreSuffix (imPath im)

-- | Load every manifest unit in order, parsing the policy only once.
loadReviewUnits :: FilePath -> FilePath -> IO [(String, CheckInput, Program)]
loadReviewUnits manifestPath policyPath = do
  manifest <- readFile manifestPath
  policyBytes <- readFile policyPath
  policy <- case parsePolicy policyBytes of
    Left err -> error ("render-reviews: policy parse failed (" ++ policyPath ++ "): " ++ show err)
    Right ok -> pure ok
  mapM (loadReviewUnit policy) (parseCorpusManifest manifest)

-- | @…/unit.core.sexp@ ⇒ @…/unit.lara@.
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
