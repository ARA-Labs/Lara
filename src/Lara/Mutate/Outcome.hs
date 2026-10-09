-- | The specified-outcome vocabulary for the seeded mutation generators: the
-- 'Expected' type (what a mutant is specified to do) and the one table each for
-- how that outcome is spelled in @MANIFEST.tsv@ and parsed back out.
--
-- This module sits below "Lara.Mutate" and imports no module in the
-- @Lara.Mutate@ namespace, which lets the root import it: 'Lara.Mutate.Mutant'
-- carries an 'Expected' field, so the dependency runs one way. The root
-- re-exports every name here, so importers say @Lara.Mutate@ as before; this
-- is the one sanctioned re-export in the namespace (see the re-export rule in
-- @docs\/evaluation.md#mutation-generation-and-module-ownership@).
--
-- The split exists because the root's growth had concentrated in one place
-- (@docs\/evaluation.md#mutation-generation-and-module-ownership@, module size). The seam is
-- *specified outcome* versus *operator vocabulary*: adding an 'Expected'
-- constructor now costs this module rather than the root, which is the growth
-- that was pushing it.
module Lara.Mutate.Outcome
  ( Expected (..)
  , expectedText
  , parseExpected
  , statusText
  ) where

import Lara.AST

-- | The outcome a mutant is specified to have (spec §10.1): a rejection with
-- a fixed class, the structural completeness reject this suite specifies
-- ('Rejection' has two more, 'DuplicateRule' and 'DuplicateArgument', which no
-- operator targets), a codec-boundary reject (exit 2, no verdict), an accept
-- that reports a located hole, or — for the cycle family — an accept where
-- every label is @undec@ and every queried status is @contested@.
data Expected
  = ExpectClass RejectClass
  | ExpectLocatedHole
  -- ^ the located-gap outcome (spec §4.4, spelled @accept-located-hole@): the
  -- mutant is schema-valid — R5 coverage holds because the open question is
  -- covered by a declared hole — and the argument it edits types with an
  -- open mandatory root obligation, so the full system accepts and reports
  -- that argument in the verdict's @holes@ section instead of making it an AF
  -- node. Up to @lara-core\@0.2@ this was the @incomplete-argument@
  -- rejection (retired, @docs\/theory-core.md#holes-located-gaps-and-term-level-critical-questions@ D3).
  | ExpectMissingConflict
  -- ^ the structural completeness reject ('Lara.AST.MissingConflict', a
  -- 'Rejection' with no R-class by design): the mutant declares an attackable
  -- contrary pair between complete arguments and no attack covering it, so the
  -- full system rejects it at the seventh stage's completeness scan
  -- ('Lara.Check.ccConflictScan') — the executable witness of the
  -- attack-completeness theorem.
  | ExpectCodecReject
  | ExpectAllContested
  | ExpectEvidenceBlocked
  -- ^ the conservative-reporting outcome (spec §4.3, spelled
  -- @accept-evidence-blocked@): the verdict accepts, but §4.3 quarantine edited
  -- the program under the queried claim, so its four-state label is only a
  -- conditional diagnostic and its public status is @evidence-blocked@. A
  -- mutant of this class that reported an ordinary status would be that bug
  -- back again.
  | ExpectPrimaryStatus Status
  -- ^ the accept-family outcome: the verdict accepts and the queried claim's
  -- status is exactly this one (spelled @accept-\<status\>@). Structural
  -- verification of the constructed attack shape lives in "Lara.Mutate.Accept"
  -- ('Lara.Mutate.Accept.acceptStructureOk'), not in the manifest spelling.
  deriving (Eq, Ord, Show)

-- | Manifest spelling of an expected outcome.
expectedText :: Expected -> String
expectedText e = case e of
  ExpectClass c -> "reject-" ++ show c
  ExpectLocatedHole -> "accept-located-hole"
  ExpectMissingConflict -> "reject-" ++ show MissingConflict
  ExpectCodecReject -> "codec-reject"
  ExpectAllContested -> "accept-all-contested"
  ExpectEvidenceBlocked -> "accept-evidence-blocked"
  ExpectPrimaryStatus s -> "accept-" ++ statusText s

-- | Manifest spelling of a claim status (the accept-family @accept-\<status\>@
-- suffix; matches @corpus-units/expected.json@'s status strings).
statusText :: Status -> String
statusText s = case s of
  Gap -> "gap"
  Justified -> "justified"
  Contested -> "contested"
  Defeated -> "defeated"

-- | Inverse of 'expectedText' — the one parse table for the @expected@ manifest
-- column (shared by @test\/MutationSpec.hs@, "Lara.Measure", and
-- @scripts\/measure.hs@). 'Nothing' on any spelling this table does not produce.
parseExpected :: String -> Maybe Expected
parseExpected s =
  lookup s $
    ("codec-reject", ExpectCodecReject)
      : ("accept-all-contested", ExpectAllContested)
      : (expectedText ExpectEvidenceBlocked, ExpectEvidenceBlocked)
      : (expectedText ExpectLocatedHole, ExpectLocatedHole)
      : (expectedText ExpectMissingConflict, ExpectMissingConflict)
      : [(expectedText (ExpectClass c), ExpectClass c) | c <- [minBound .. maxBound]]
      ++ [ (expectedText (ExpectPrimaryStatus st), ExpectPrimaryStatus st)
         | st <- [Gap, Justified, Contested, Defeated]
         ]
