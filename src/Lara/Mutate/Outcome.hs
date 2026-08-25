-- | The specified-outcome vocabulary for the seeded mutation generators: the
-- 'Expected' type (what a mutant is specified to do) and the one table each for
-- how that outcome is spelled in @MANIFEST.tsv@ and parsed back out.
--
-- This module sits below "Lara.Mutate" and imports no module in the
-- @Lara.Mutate@ namespace, which lets the root import it: 'Lara.Mutate.Mutant'
-- carries an 'Expected' field, so the dependency runs one way. The root
-- re-exports every name here, so importers say @Lara.Mutate@ as before; this
-- is the one sanctioned re-export in the namespace (ownership record D1, #157).
--
-- The split exists because the root's growth had concentrated in one place
-- (@docs\/mutate-module-ownership-decision.md@, module size). The seam is
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
-- a fixed class, one of the two structural rejects this suite specifies (the
-- obligation gate, the completeness scan; 'Rejection' has two more,
-- 'DuplicateRule' and 'DuplicateArgument', which no operator targets), a
-- codec-boundary reject (exit 2, no verdict), or — for the cycle family — an
-- accept where every label is @undec@ and every queried status is @contested@.
data Expected
  = ExpectClass RejectClass
  | ExpectIncompleteArgument
  -- ^ the structural obligation-gate reject ('Lara.AST.IncompleteArgument', a
  -- 'Rejection' with no R-class by design): the mutant is schema-valid — R5
  -- coverage holds because the open question is covered by a declared hole —
  -- and the full system rejects it only at the obligation gate
  -- ('Lara.Check.ccObligationGate'), i.e. an argument reaching the root with
  -- an open mandatory obligation.
  | ExpectMissingConflict
  -- ^ the structural completeness reject ('Lara.AST.MissingConflict', a
  -- 'Rejection' with no R-class by design): the mutant declares an attackable
  -- contrary pair between complete arguments and no attack covering it, so the
  -- full system rejects it at the seventh stage's completeness scan
  -- ('Lara.Check.ccConflictScan') — the executable witness of the
  -- attack-completeness theorem (#124).
  | ExpectCodecReject
  | ExpectAllContested
  | ExpectEvidenceBlocked
  -- ^ the conservative-reporting outcome (spec §4.3, issue #76, spelled
  -- @accept-evidence-blocked@): the verdict accepts, but §4.3 quarantine edited
  -- the program under the queried claim, so its four-state label is only a
  -- conditional diagnostic and its public status is @evidence-blocked@. A
  -- mutant of this class that reported an ordinary status would be the #76 bug
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
  ExpectIncompleteArgument -> "reject-" ++ show IncompleteArgument
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
      : (expectedText ExpectIncompleteArgument, ExpectIncompleteArgument)
      : (expectedText ExpectMissingConflict, ExpectMissingConflict)
      : [(expectedText (ExpectClass c), ExpectClass c) | c <- [minBound .. maxBound]]
      ++ [ (expectedText (ExpectPrimaryStatus st), ExpectPrimaryStatus st)
         | st <- [Gap, Justified, Contested, Defeated]
         ]
