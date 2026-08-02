-- | The shared IO loader for the corpus claim-support pass (#56): the one
-- place that decodes a unit's @unit.core.sexp@, runs the T3 core, parses the
-- @unit.lara@ surface, and reads the documented @strict_certifier@ header flag.
--
-- Both the harness (@scripts\/claim-support.hs@) and the regression guard
-- (@test\/ClaimSupportSpec.hs@) call THIS module, so the per-unit IO — in
-- particular the @flavored@ predicate — cannot drift between them. (It did:
-- an earlier test copy dropped the @strict-flavored@ disjunct and computed a
-- different documented-strict-flavored count than the shipped artifact.)
--
-- A decode\/parse failure or a non-accept verdict is a hard 'error': every
-- frozen corpus unit is accept-class with a well-formed surface, so any failure
-- here means the freeze or a decode path drifted.
module Lara.ClaimSupport.Load
  ( loadRuleModes
  , loadUnitRecord
  , loadRecords
  ) where

import Data.List (isInfixOf)

import Lara.AST (Mode (Defeasible), Policy (..), Rule (..), RuleId)
import Lara.ClaimSupport (UnitRecord, computeUnit)
import Lara.Driver (runCheck)
import Lara.Measure (InputMeta (..), parseCorpusManifest)
import Lara.Syntax (parseProgram, parsePolicy)
import Lara.Wire (decodeCheckInputFile)

-- | Build the @RuleId -> Mode@ resolver from the shared policy (parsed once).
-- Rules absent from the policy default to 'Defeasible' (they cannot be strict).
loadRuleModes :: FilePath -> IO (RuleId -> Mode)
loadRuleModes policyPath = do
  raw <- readFile policyPath
  case parsePolicy raw of
    Left err -> error ("claim-support: policy parse failed (" ++ policyPath ++ "): " ++ show err)
    Right policy ->
      let table = [(ruleId r, ruleMode r) | r <- policyRules policy]
       in pure (\rid -> maybe Defeasible id (lookup rid table))

-- | Decode + 'runCheck' one unit's core, parse its @.lara@ surface, and read the
-- documented @strict_certifier@\/@strict-flavored@ header flag (both spellings
-- occur in the M0 annotations; dropping either undercounts the flavored set).
loadUnitRecord :: (RuleId -> Mode) -> InputMeta -> IO UnitRecord
loadUnitRecord ruleModeOf im = do
  coreBytes <- readFile (imPath im)
  ci <- case decodeCheckInputFile coreBytes of
    Left err -> error ("claim-support: wire decode failed (" ++ imPath im ++ "): " ++ show err)
    Right ok -> pure ok
  laraBytes <- readFile laraPath
  prog <- case parseProgram laraBytes of
    Left err -> error ("claim-support: surface parse failed (" ++ laraPath ++ "): " ++ show err)
    Right ok -> pure ok
  let flavored = "strict_certifier" `isInfixOf` laraBytes || "strict-flavored" `isInfixOf` laraBytes
  pure (computeUnit ruleModeOf flavored (imBase im) ci (runCheck ci) prog)
  where
    laraPath = replaceCoreSuffix (imPath im)

-- | Load every unit named by a corpus manifest, in manifest order.
loadRecords :: FilePath -> FilePath -> IO [UnitRecord]
loadRecords manifestPath policyPath = do
  manifest <- readFile manifestPath
  ruleModeOf <- loadRuleModes policyPath
  mapM (loadUnitRecord ruleModeOf) (parseCorpusManifest manifest)

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
