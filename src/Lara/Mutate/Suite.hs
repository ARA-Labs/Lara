-- | Seeded assembly of the rejection suite: turning enumerated sites into
-- verified-shaped 'Mutant' values, over both base populations.
--
-- \"Suite\" here means the seeded rejection suite, not the whole fixture set.
-- The two populations are the same job:
--
-- * 'mutantsForBase' runs the full operator list over one worked-example
--   anchor with per-operator caps, and
-- * 'corpusMutants' sweeps the same rejection operators over the corpus units
--   under a uniform derived-applicability rule (eng review D9), one mutant per
--   selected base.
--
-- They share the site enumerators, the operator order, and the assembly step,
-- which is why they live together. @scripts\/gen-mutants.hs@ combines this
-- module's output with the codec ("Lara.Mutate.Codec"), rebut-cycle
-- ("Lara.Mutate.Cycle"), and accept ("Lara.Mutate.Accept") families to form the
-- complete suite.
--
-- The invariants are the ones the committed bytes depend on: the operator
-- lists here are in fixed order, sites are drawn by
-- 'Lara.Mutate.Seed.pickSome' over each enumerator's output /in list order/,
-- and 'corpusSweepReport' publishes the per-operator applicable and selected
-- counts so a budget cap is recorded rather than silent. This module only
-- proposes mutants; @scripts\/gen-mutants.hs@ re-checks each one against the
-- production checker before writing it.
module Lara.Mutate.Suite
  ( mutantsForBase
  , corpusBudget
  , corpusMutants
  , corpusSweepReport
    -- * Site enumerators reachable for testing
    --
    -- | "Lara.Mutate.Sites" and its children are @other-modules@: the
    -- enumerators are an implementation detail of the suite, not API. This one
    -- is re-exported because @test\/MutationSpec.hs@'s
    -- @prop_conflictSiteMatchesChecker@ has to compare the /predicted/ pair
    -- against the checker's, which means calling the enumerator directly —
    -- going through 'mutantsForBase' would only see the seeded subset and the
    -- rendered bytes, not the prediction.
  , dropCoveringAttackSites
  ) where

import Lara.AST
import Lara.Diagnostics (Constituent (..))
import Lara.Replay
  ( CheckInput
  , inputReplayId
  , inputUnit
  , mkCheckInput
  , mkReplayId
  , replayArtifact
  , replayBackends
  , replayCore
  , replayPolicy
  , replayTheories
  )
import Lara.Wire (encodeCheckInput, printSExpr)

import Lara.Mutate
import Lara.Mutate.Seed (pickSome, pickWithStream, streamForKey)
import Lara.Mutate.Sites
import qualified Lara.Mutate.Sorts as Sorts

-- | All verdict-level mutants of one decoded base anchor, in fixed operator
-- order, sites picked by the seeded stream. Inapplicable operators produce no
-- mutants for the base. Codec mutants are separate
-- ("Lara.Mutate.Codec".@codecMutantsForBase@).
mutantsForBase :: String -> CheckInput -> [Mutant]
mutantsForBase base input =
  concat
    [ unitMutants base input OpUndeclaredLeaf 2 undeclaredLeafSites
    , unitMutants base input OpHiddenRule 1 hiddenRuleSites
    , unitMutants base input OpHiddenContrary 1 hiddenContrarySites
    , unitMutants base input OpWrongSubstDomain 1 wrongSubstSites
    , unitMutants base input OpWrongPremise 1 wrongPremiseSites
    , unitMutants base input OpOpenObligation 1 openObligationSites
    , unitMutants base input OpHoleObligation 1 holeObligationSites
    , unitMutants base input OpWrongDischarge 1 wrongDischargeSites
    , unitMutants base input OpTrustedAssurance 1 trustedAssuranceSites
    , unitMutants base input OpCertTheorySwap 1 certTheorySwapSites
    , unitMutants base input OpCertPayloadTamper 1 certPayloadSites
    , unitMutants base input OpCertWrongFraction 1 certWrongFractionSites
    , unitMutants base input OpBadAttackPosition 2 badAttackPositionSites
    , unitMutants base input OpUnlicensedAttack 1 unlicensedAttackSites
    , unitMutants base input OpDropCoveringAttack 1 dropCoveringAttackSites
    , unitMutants base input OpGroupConflict 1 groupConflictSites
    , -- The signature family (@lara-core\@0.2@, #89 D10): R2 had zero mutants
      -- before this pass, and spec §10.1 requires every class to be exercised.
      unitMutants base input OpUndeclaredPred 1 (classed Sorts.undeclaredPredSites)
    , unitMutants base input OpWrongPredArity 1 (classed Sorts.wrongPredAritySites)
    , unitMutants base input OpWrongArgSort 2 (classed Sorts.wrongArgSortSites)
    , unitMutants base input OpUndeclaredCon 1 (classed Sorts.undeclaredConSites)
    , unitMutants base input OpWrongThetaSort 1 (classed Sorts.wrongThetaSortSites)
    , unitMutants base input OpOutOfScopeVar 1 (classed Sorts.outOfScopeVarSites)
    , -- Integrated Σ well-formedness fixtures are dedicated negatives, not a
      -- sweep: one row per clause, anchored once at the first worked example.
      dedicatedSigma OpSigmaDuplicateSort Sorts.duplicateSortSites
    , dedicatedSigma OpSigmaShadowBase Sorts.shadowBaseSortSites
    , dedicatedSigma OpSigmaDuplicateCon Sorts.duplicateConSites
    , dedicatedSigma OpSigmaDuplicatePred Sorts.duplicatePredSites
    , dedicatedSigma OpSigmaConUndeclaredSort Sorts.conUndeclaredSortSites
    , dedicatedSigma OpSigmaPredUndeclaredSort Sorts.predUndeclaredSortSites
    , replayMutants base input
    ]
  where
    -- "Lara.Mutate.Sorts" sits below the operator vocabulary and yields bare
    -- rejection classes; wrapping them here keeps 'Expected' owned by exactly
    -- one module.
    classed sites u = [(ExpectClass c, loc, f) | (c, loc, f) <- sites u]
    dedicatedSigma op sites
      | base == "A" = unitMutants base input op 1 (classed sites)
      | otherwise = []

-- | Assemble the picked unit-mutation sites of one operator into mutants. Each
-- site carries its seeded ground-truth 'Constituent', threaded into
-- 'mutantSite'.
unitMutants
  :: String
  -> CheckInput
  -> MutationOp
  -> Int
  -> (Unit -> [(Expected, Constituent, Unit -> Unit)])
  -> [Mutant]
unitMutants base input op cap sites =
  [ Mutant (mutantFileName base op k) base op expected (Just site) bytes
  | (k, (expected, site, mutate)) <- zip [0 :: Int ..] picked
  , Right mutated <- [mkCheckInput (inputReplayId input) (mutate u)]
  , let bytes = printSExpr (encodeCheckInput mutated) ++ "\n"
  ]
  where
    u = inputUnit input
    picked = pickSome base op cap (sites u)

-- R13 (replay preflight): duplicate or unknown selected backend. Both replay
-- operators over one base.
replayMutants :: String -> CheckInput -> [Mutant]
replayMutants base input =
  replayMutant base input OpDuplicateBackend
    ++ replayMutant base input OpUnknownBackend

-- | The single R13 replay-preflight mutant of one base for one replay operator
-- ('OpDuplicateBackend' repeats a selected backend, 'OpUnknownBackend' appends
-- an unselected one). Empty when the base declares no backends to corrupt; the
-- seeded ground truth is the replay envelope ('CReplayEnvelope').
replayMutant :: String -> CheckInput -> MutationOp -> [Mutant]
replayMutant base input op
  | null backends = []
  | otherwise =
      [ Mutant (mutantFileName base op 0) base op (ExpectClass R13) (Just CReplayEnvelope) bytes
      | Right rid' <-
          [ mkReplayId
              (replayCore rid)
              (replayPolicy rid)
              (corruptedBackends op)
              (replayTheories rid)
              (replayArtifact rid)
          ]
      , Right mutated <- [mkCheckInput rid' (inputUnit input)]
      , let bytes = printSExpr (encodeCheckInput mutated) ++ "\n"
      ]
  where
    rid = inputReplayId input
    backends = replayBackends rid
    corruptedBackends OpUnknownBackend = backends ++ [(BackendId "mut_backend", "9")]
    corruptedBackends OpDuplicateBackend = backends ++ take 1 backends
    corruptedBackends other = error ("replayMutant: not a replay operator: " ++ opName other)

-- ---------------------------------------------------------------------------
-- Corpus sweep (uniform derived-applicability rule, eng review D9)
-- ---------------------------------------------------------------------------

-- | The per-operator base budget for the corpus sweep. When an operator's
-- applicable set exceeds this, a budget-sized subset is picked by the
-- operator-keyed stream; at or below it, the whole set is taken (full
-- coverage). A frozen generation constant — changing it regenerates a
-- different, equally valid corpus half and must be an explicit decision.
corpusBudget :: Int
corpusBudget = 12

-- | One rejection operator, viewed for the corpus sweep: its applicability
-- predicate (does this base carry ≥1 site?) and its cap-1 producer at a base.
data SweepOp = SweepOp
  { sweepOp :: MutationOp
  , sweepApplicable :: CheckInput -> Bool
  , sweepAt :: String -> CheckInput -> [Mutant]
  }

-- | The rejection operators swept over corpus bases, in fixed order. This is
-- the same operator set 'mutantsForBase' runs over the worked examples (cert
-- and other arg-dependent operators self-gate via their site enumerators — a
-- gap corpus unit with no args yields no sites, so they propose nothing there,
-- no special casing). Codec corruption and the constructed cycle family are not
-- part of the corpus sweep (they are base-independent structural families).
sweepOps :: [SweepOp]
sweepOps =
  [ unitSweep OpUndeclaredLeaf undeclaredLeafSites
  , unitSweep OpHiddenRule hiddenRuleSites
  , unitSweep OpHiddenContrary hiddenContrarySites
  , unitSweep OpWrongSubstDomain wrongSubstSites
  , unitSweep OpWrongPremise wrongPremiseSites
  , unitSweep OpOpenObligation openObligationSites
  , unitSweep OpHoleObligation holeObligationSites
  , unitSweep OpWrongDischarge wrongDischargeSites
  , unitSweep OpTrustedAssurance trustedAssuranceSites
  , unitSweep OpCertTheorySwap certTheorySwapSites
  , unitSweep OpCertPayloadTamper certPayloadSites
  , unitSweep OpCertWrongFraction certWrongFractionSites
  , unitSweep OpBadAttackPosition badAttackPositionSites
  , unitSweep OpUnlicensedAttack unlicensedAttackSites
  , unitSweep OpDropCoveringAttack dropCoveringAttackSites
  , unitSweep OpGroupConflict groupConflictSites
  , -- The signature family. Sweeping it over the corpus is what makes the
    -- applicability assertion meaningful: `wrong-arg-sort` must find real sites
    -- in corpus-v1's own vocabulary, not only in hand-built examples (#89 §8).
    unitSweep OpUndeclaredPred (classedSites Sorts.undeclaredPredSites)
  , unitSweep OpWrongPredArity (classedSites Sorts.wrongPredAritySites)
  , unitSweep OpWrongArgSort (classedSites Sorts.wrongArgSortSites)
  , unitSweep OpUndeclaredCon (classedSites Sorts.undeclaredConSites)
  , unitSweep OpWrongThetaSort (classedSites Sorts.wrongThetaSortSites)
  , unitSweep OpOutOfScopeVar (classedSites Sorts.outOfScopeVarSites)
  , replaySweep OpDuplicateBackend
  , replaySweep OpUnknownBackend
  ]
  where
    classedSites sites u = [(ExpectClass c, loc, f) | (c, loc, f) <- sites u]
    unitSweep op sites =
      SweepOp
        op
        (\input -> not (null (sites (inputUnit input))))
        (\base input -> unitMutants base input op 1 sites)
    replaySweep op =
      SweepOp
        op
        (\input -> not (null (replayBackends (inputReplayId input))))
        (\base input -> replayMutant base input op)

-- | The bases at which a sweep operator finds ≥1 site (corpus manifest order).
sweepApplicableBases :: SweepOp -> [(String, CheckInput)] -> [(String, CheckInput)]
sweepApplicableBases op bases = [b | b@(_, input) <- bases, sweepApplicable op input]

-- | The bases one sweep operator selects: all applicable bases when they number
-- ≤ 'corpusBudget', else a 'corpusBudget'-sized subset picked by the
-- operator-keyed stream. Order is the applicable-set order (corpus manifest
-- order), so the selection is deterministic.
sweepSelected :: SweepOp -> [(String, CheckInput)] -> [(String, CheckInput)]
sweepSelected op bases =
  pickWithStream
    (streamForKey ("corpus-sweep/" ++ opName (sweepOp op)))
    corpusBudget
    (sweepApplicableBases op bases)

-- | Every corpus-base mutant, operator-major: for each rejection operator, one
-- mutant at each selected base (the seeded first site). The @(base, input)@
-- list is the corpus units in manifest order, each base labelled
-- @\<artifact\>.\<claim_id\>@; @scripts\/gen-mutants.hs@ and
-- @test\/MutationSpec.hs@ pass the same list, so the output is identical.
corpusMutants :: [(String, CheckInput)] -> [Mutant]
corpusMutants bases =
  concat
    [ sweepAt op base input
    | op <- sweepOps
    , (base, input) <- sweepSelected op bases
    ]

-- | The measured per-operator applicable and selected base counts of the corpus
-- sweep, in operator order — the "no silent caps" record the regenerated
-- @README.md@ prints and @test\/MutationSpec.hs@ pins against the manifest.
-- Operators that find no corpus site (the cert operators) appear with
-- @(applicable, selected) = (0, 0)@, so absence is documented, not hidden.
corpusSweepReport :: [(String, CheckInput)] -> [(MutationOp, Int, Int)]
corpusSweepReport bases =
  [ (sweepOp op, length (sweepApplicableBases op bases), length (sweepSelected op bases))
  | op <- sweepOps
  ]
