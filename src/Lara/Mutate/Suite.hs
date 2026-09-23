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
    -- enumerators are an implementation detail of the suite, not API. These
    -- are re-exported because @test\/MutationSpec.hs@'s checker-agreement
    -- properties have to compare each /predicted/ constituent against the
    -- checker's, which means calling the enumerators directly — going through
    -- 'mutantsForBase' would only see the seeded subset and the rendered
    -- bytes, not the prediction. 'siteOps' is the whole table
    -- (@prop_siteMatchesChecker@); 'dropCoveringAttackSites' stays
    -- exported for the conflict-specific property that carries the
    -- @drop-covering-attack@ design rationale.
  , SiteOp (..)
  , siteOps
  , dropCoveringAttackSites
  ) where

import Lara.AST
import Lara.Diagnostics (Constituent (..), SeededSites, seededSite)
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
import qualified Lara.Mutate.Sites.Localize as Localize
import qualified Lara.Mutate.Sorts as Sorts

-- | One rejection-site operator, as generation sees it: its per-base cap at a
-- worked-example anchor, whether it is a dedicated Σ closeout fixture
-- (anchored once at base @\"A\"@, excluded from the corpus sweep), and its
-- site enumerator. 'mutantsForBase', 'sweepOps', and
-- @test\/MutationSpec.hs@'s checker-agreement property all read 'siteOps', so
-- the generated suite, the corpus sweep, and the gated answer key cannot
-- drift apart.
data SiteOp = SiteOp
  { siteOp :: MutationOp
  , siteCap :: Int
  , siteDedicated :: Bool
  , siteSites :: Unit -> [(Expected, SeededSites, Unit -> Unit)]
  -- ^ each proposed site carries its ordered ground truth ('mutantSites'
  -- contract: head = the spec-order-first constituent, every element
  -- admissible). 'SeededSites' is non-empty by construction, so an enumerator
  -- cannot publish a site seeded at nothing. The single-defect
  -- enumerators publish singletons via 'single'.
  }

-- | The rejection-site operators in the frozen generation order. The replay
-- operators are not here — they corrupt the replay envelope, not the unit, so
-- they have no site enumerator ('replayMutants' \/ 'replaySweep').
siteOps :: [SiteOp]
siteOps =
  [ SiteOp OpUndeclaredLeaf 2 False (single undeclaredLeafSites)
  , SiteOp OpHiddenRule 1 False (single hiddenRuleSites)
  , SiteOp OpHiddenContrary 1 False (single hiddenContrarySites)
  , SiteOp OpWrongSubstDomain 1 False (single wrongSubstSites)
  , SiteOp OpWrongPremise 1 False (single wrongPremiseSites)
  , SiteOp OpOpenObligation 1 False (single openObligationSites)
  , SiteOp OpHoleObligation 1 False (single holeObligationSites)
  , SiteOp OpWrongDischarge 1 False (single wrongDischargeSites)
  , SiteOp OpTrustedAssurance 1 False (single trustedAssuranceSites)
  , SiteOp OpCertTheorySwap 1 False (single certTheorySwapSites)
  , SiteOp OpCertPayloadTamper 1 False (single certPayloadSites)
  , SiteOp OpCertWrongFraction 1 False (single certWrongFractionSites)
  , SiteOp OpBadAttackPosition 2 False (single badAttackPositionSites)
  , SiteOp OpUnlicensedAttack 1 False (single unlicensedAttackSites)
  , SiteOp OpDropCoveringAttack 1 False (single dropCoveringAttackSites)
  , SiteOp OpGroupConflict 1 False (single groupConflictSites)
  , -- The localization family (@docs\/localization-metric-decision.md@):
    -- the only enumerators publishing composite ground-truth lists — off-site
    -- manifestation and multi-defect ordering ("Lara.Mutate.Sites.Localize").
    SiteOp OpRetractRule 1 False Localize.retractRuleSites
  , SiteOp OpTwinSupportDefect 1 False Localize.twinSupportDefectSites
  , SiteOp OpCrossStageDefect 1 False Localize.crossStageDefectSites
  , -- The signature family (@lara-core\@0.2@, D10): R2 had zero mutants
    -- before this pass, and spec §10.1 requires every class to be exercised.
    SiteOp OpUndeclaredPred 1 False (classed Sorts.undeclaredPredSites)
  , SiteOp OpWrongPredArity 1 False (classed Sorts.wrongPredAritySites)
  , SiteOp OpWrongArgSort 2 False (classed Sorts.wrongArgSortSites)
  , SiteOp OpUndeclaredCon 1 False (classed Sorts.undeclaredConSites)
  , SiteOp OpWrongThetaSort 1 False (classed Sorts.wrongThetaSortSites)
  , SiteOp OpOutOfScopeVar 1 False (classed Sorts.outOfScopeVarSites)
  , -- Integrated Σ well-formedness fixtures are dedicated negatives, not a
    -- sweep: one row per clause, anchored once at the first worked example.
    SiteOp OpSigmaDuplicateSort 1 True (classed Sorts.duplicateSortSites)
  , SiteOp OpSigmaShadowBase 1 True (classed Sorts.shadowBaseSortSites)
  , SiteOp OpSigmaDuplicateCon 1 True (classed Sorts.duplicateConSites)
  , SiteOp OpSigmaDuplicatePred 1 True (classed Sorts.duplicatePredSites)
  , SiteOp OpSigmaConUndeclaredSort 1 True (classed Sorts.conUndeclaredSortSites)
  , SiteOp OpSigmaPredUndeclaredSort 1 True (classed Sorts.predUndeclaredSortSites)
  ]
  where
    -- Every enumerator above seeds exactly one defect, so its ground truth is
    -- the singleton of the mutated constituent — the degenerate case under
    -- which membership and head-equality coincide.
    single sites u = [(e, seededSite loc, f) | (e, loc, f) <- sites u]
    -- "Lara.Mutate.Sorts" sits below the operator vocabulary and yields bare
    -- rejection classes; wrapping them here keeps 'Expected' owned by exactly
    -- one module.
    classed sites = single (\u -> [(ExpectClass c, loc, f) | (c, loc, f) <- sites u])

-- | All verdict-level mutants of one decoded base anchor, in fixed operator
-- order ('siteOps'), sites picked by the seeded stream. Inapplicable operators
-- produce no mutants for the base. Codec mutants are separate
-- ("Lara.Mutate.Codec".@codecMutantsForBase@).
mutantsForBase :: String -> CheckInput -> [Mutant]
mutantsForBase base input =
  concat
    [ unitMutants base input (siteOp op) (siteCap op) (siteSites op)
    | op <- siteOps
    , not (siteDedicated op) || base == "A"
    ]
    ++ replayMutants base input

-- | Assemble the picked unit-mutation sites of one operator into mutants. Each
-- site carries its ordered seeded ground truth, threaded into 'mutantSites'.
unitMutants
  :: String
  -> CheckInput
  -> MutationOp
  -> Int
  -> (Unit -> [(Expected, SeededSites, Unit -> Unit)])
  -> [Mutant]
unitMutants base input op cap sites =
  [ Mutant (mutantFileName base op k) base op expected (Just locs) bytes
  | (k, (expected, locs, mutate)) <- zip [0 :: Int ..] picked
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
      [ Mutant
          (mutantFileName base op 0)
          base
          op
          (ExpectClass R13)
          (Just (seededSite CReplayEnvelope))
          bytes
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

-- | The rejection operators swept over corpus bases, in fixed order: the
-- non-dedicated 'siteOps' (the Σ closeout fixtures are one-row negatives
-- anchored at base @\"A\"@, not a sweep), then the replay operators. This is
-- the same operator set 'mutantsForBase' runs over the worked examples (cert
-- and other arg-dependent operators self-gate via their site enumerators — a
-- gap corpus unit with no args yields no sites, so they propose nothing there,
-- no special casing; sweeping the signature family is what makes its
-- applicability assertion meaningful — `wrong-arg-sort` must find real sites
-- in corpus-v1's own vocabulary, not only in hand-built examples, §8).
-- Codec corruption and the constructed cycle family are not part of the corpus
-- sweep (they are base-independent structural families).
sweepOps :: [SweepOp]
sweepOps =
  [ unitSweep (siteOp op) (siteSites op)
  | op <- siteOps
  , not (siteDedicated op)
  ]
    ++ [ replaySweep OpDuplicateBackend
       , replaySweep OpUnknownBackend
       ]
  where
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
