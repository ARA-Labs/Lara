-- | The corpus claim-support aggregation (#56) as a standing test: the pure
-- "Lara.ClaimSupport" classifiers, plus an end-to-end run over the FROZEN 60
-- corpus units that PINS every headline number the paper cites AND re-diffs the
-- committed frozen deliverable byte-for-byte. The integration props are the
-- regression guard — if a corpus edit or a checker change moves any headline
-- number, or the committed @measurements\/frozen\/claim-support.{json,tsv}@
-- drifts from what the pass now computes, this fails loudly (the freeze
-- discipline for the descriptive pass).
--
-- The per-unit IO is loaded through 'Lara.ClaimSupport.Load' — the same loader
-- the harness (@scripts\/claim-support.hs@) uses — so the records under test
-- are exactly the records that produced the shipped artifact, with no room for
-- the flavored\/decode logic to drift between test and harness.
module ClaimSupportSpec (claimSupportSpecProps) where

import Data.List (isPrefixOf)
import Test.QuickCheck

import Lara.AST
  ( LeafKind (Attested, Observed)
  , Provenance (AiExecuted)
  , SourceRef (..)
  , Status (Defeated, Gap, Justified)
  )
import Lara.ClaimSupport
import Lara.ClaimSupport.Load (loadRecords)
import Lara.Measure (EnvBlock (..))

manifestPath, policyPath, frozenJsonPath, frozenTsvPath :: FilePath
manifestPath = "corpus-units/MANIFEST.tsv"
policyPath = "corpus-units/corpus-v1.policy.lara"
frozenJsonPath = "measurements/frozen/claim-support.json"
frozenTsvPath = "measurements/frozen/claim-support.tsv"

claimSupportSpecProps :: [(String, IO Result)]
claimSupportSpecProps =
  [ ("claim-support: paper-anchor ref classifier", quickCheckResult prop_paperAnchor)
  , ("claim-support: frozen corpus numbers (status/leaves/attacks/strict)", quickCheckResult prop_frozenNumbers)
  , ("claim-support: recomputed json/tsv re-diff the committed frozen deliverable", quickCheckResult prop_frozenDeliverable)
  ]

-- | Direct paper-document locators are recognised; agent-artifact paths are not.
prop_paperAnchor :: Property
prop_paperAnchor =
  once $
    counterexample "paper locators" (all (isPaperAnchorRef . SourceRef) paperRefs)
      .&&. counterexample "agent paths" (not (any (isPaperAnchorRef . SourceRef) agentRefs))
  where
    paperRefs =
      [ "E01#Table-2"
      , "E04#Table-10"
      , "Table-5"
      , "Table-4-row-total"
      , "Figure-3a"
      , "Appendix-B"
      , "Theorem-2"
      , "section-4"
      , "paper-section-5.1"
      , "PAPER.md#overview"
      ]
    agentRefs =
      [ "logic/claims.md#C03"
      , "trace/exploration_tree.yaml#N15"
      , "evidence/tables/table4_reward_subset_ablation.md"
      , "src/model.py#L10"
      , "rl_finetune_best_of_n.py#118-139"
      ]

-- | The full aggregation over the frozen 60 units, with EVERY headline number
-- (and its by-provenance/by-kind breakdown) pinned — not only the four the plan
-- names but every field the committed @claim-support.json@ reports, so a
-- classifier edit that flips one leaf cannot pass silently.
prop_frozenNumbers :: Property
prop_frozenNumbers = once $ ioProperty $ do
  rep <- aggregate <$> loadRecords manifestPath policyPath
  let has k n = lookup k (csStatus rep) == Just n
  pure $
    conjoin
      [ counterexample "units" (csUnits rep === 60)
      , counterexample "gap" (property (has Gap 48))
      , counterexample "justified" (property (has Justified 9))
      , counterexample "defeated" (property (has Defeated 3))
      , counterexample "load-bearing total" (csLoadBearingTotal rep === 38)
      , counterexample "load-bearing provenance" (csLoadBearingProvenance rep === [(AiExecuted, 38)])
      , counterexample "load-bearing kind" (csLoadBearingKind rep === [(Attested, 20), (Observed, 18)])
      , counterexample "load-bearing paper-anchored" (csLoadBearingPaperAnchored rep === 15)
      , counterexample "all leaves total" (csAllTotal rep === 169)
      , counterexample "all leaves provenance" (csAllProvenance rep === [(AiExecuted, 169)])
      , counterexample "all leaves kind" (csAllKind rep === [(Attested, 106), (Observed, 63)])
      , counterexample "all leaves paper-anchored" (csAllPaperAnchored rep === 51)
      , counterexample "typed attacks" (csTypedAttacks rep === 3)
      , counterexample "dead-end attacks" (csDeadEndAttacks rep === 2)
      , counterexample "strict steps" (csStrictSteps rep === 1)
      , counterexample "strict certified" (csStrictCertified rep === 1)
      , counterexample "documented strict-flavored" (csStrictFlavored rep === 5)
      ]

-- | Render the JSON and TSV from the freshly recomputed records and require
-- them to reproduce the COMMITTED frozen deliverable byte-for-byte (the JSON
-- modulo its environment block, which is reconstructed from the frozen file so
-- the compare is exact). This pins all 60 per-unit rows and the JSON notes, and
-- catches any hand-edit or corpus-vs-artifact staleness of the committed files
-- — the byte-identical re-diff the house freeze discipline applies elsewhere.
prop_frozenDeliverable :: Property
prop_frozenDeliverable = once $ ioProperty $ do
  records <- loadRecords manifestPath policyPath
  let rep = aggregate records
  frozenJson <- readFile frozenJsonPath
  frozenTsv <- readFile frozenTsvPath
  let env = envFromFrozenJson frozenJson
  pure $
    conjoin
      [ counterexample "frozen tsv (all 60 per-unit rows)" (claimSupportTsv records === frozenTsv)
      , counterexample
          "frozen json (aggregate + per-unit + notes, modulo env)"
          (claimSupportJson env rep records === frozenJson)
      ]

-- | Reconstruct the 'EnvBlock' from a frozen @claim-support.json@'s environment
-- object, so the re-diff can be byte-exact rather than env-sensitive. The six
-- keys are unique to that object and it is the first object in the file.
envFromFrozenJson :: String -> EnvBlock
envFromFrozenJson s =
  EnvBlock
    { envGitRev = field "git-rev"
    , envGitDirty = field "git-dirty" == "true"
    , envGhc = field "ghc"
    , envLean = field "lean"
    , envOs = field "os"
    , envCpu = field "cpu"
    }
  where
    field k =
      case [ dropWhile (== ' ') (drop (length prefix) t)
           | l <- lines s
           , let t = dropWhile (== ' ') l
           , prefix `isPrefixOf` t
           ] of
        (v : _) -> stripQuotes (stripComma v)
        [] -> error ("claim-support test: env field " ++ k ++ " not found in frozen json")
      where
        prefix = "\"" ++ k ++ "\":"
    stripComma xs = if not (null xs) && last xs == ',' then init xs else xs
    stripQuotes ('"' : rest) | not (null rest) && last rest == '"' = init rest
    stripQuotes xs = xs
