-- | Golden cases for full claim holes and incomplete-alternative diagnostics
-- ("Lara.Reporting", spec §8 / N17 point 1).
--
-- The reporting analysis is /lenient/: it scans raw 'Unit' arguments and
-- retains incomplete alternatives (open mandatory critical questions, spec
-- §6.1) instead of rejecting the way 'Lara.Check.checkUnit' does. Units here are
-- built directly as Haskell values so a claim can have both a complete argument
-- and a separate incomplete alternative — a shape @checkUnit@ would reject at
-- the first incomplete argument, but which reporting must still analyze.
--
-- Three spec §8 status branches are covered where holes interact:
--
--   * (a) empty complete support + a hole → @gap@ + @incompleteAlternative@;
--   * (b) several unresolved alternatives, each hole located with its
--     obligations;
--   * (c) a complete /winning/ alternative (@in@) plus a separate incomplete
--     alternative → @justified@ / label @in@ NOT suppressed, hole still surfaced;
--   * plus @contested@ (self-attack cycle) and @defeated@ (rebutted) with a
--     coexisting hole, confirming the diagnostic fires without changing status.
--
-- Step-5 guard: a claim with an incomplete alternative distinguishes the
-- complete-only 'Lara.Grounded.completeClaimFor' (holes @[]@) from the full
-- 'Lara.Reporting.reportClaimFor' (holes @≠ []@) — the two paths are never
-- conflated.
module ReportingSpec (reportingSpecProps) where

import Test.QuickCheck (Result, quickCheckResult)

import Lara.AST
import Lara.Grounded
  ( Claim (..)
  , claimSupportFor
  , completeClaimFor
  , labelC
  , statusC
  )
import Lara.Policy (lookupRule)
import Lara.Prop (Prop (..))
import Lara.Reporting
import Lara.SupportTerm (CertOk, CheckedNode, cnConclusion)

-- ---------------------------------------------------------------------------
-- Shared vocabulary
-- ---------------------------------------------------------------------------

pP, pNotP, pA :: Prop
pP = Prop (Pred "p") []
pNotP = Prop (Pred "not_p") []
pA = Prop (Pred "a") []

-- | A defeasible rule @r1@ concluding @p@ with one /mandatory/ critical
-- question @q1@ answered by @a@. An instance leaving @q1@ open is incomplete; an
-- instance discharging it with a leaf concluding @a@ is complete.
ruleR1 :: Rule
ruleR1 =
  Rule
    { ruleId = RuleId "r1"
    , ruleParams = []
    , ruleMode = Defeasible
    , rulePremises = []
    , ruleConclusion = AtomPat (Pred "p") []
    , ruleAllowTrusted = False
    , ruleCertifiers = []
    , ruleQuestions = [Question (QuestionId "q1") (AtomPat (Pred "a") []) Mandatory]
    }

-- | A defeasible rule @r2@ concluding @not_p@ with no questions (always
-- complete).
ruleR2 :: Rule
ruleR2 =
  Rule
    { ruleId = RuleId "r2"
    , ruleParams = []
    , ruleMode = Defeasible
    , rulePremises = []
    , ruleConclusion = AtomPat (Pred "not_p") []
    , ruleAllowTrusted = False
    , ruleCertifiers = []
    , ruleQuestions = []
    }

-- | An @r1@ instance with @q1@ left open — incomplete (obligation @q1@), concl @p@.
incompleteR1 :: SupportTerm
incompleteR1 =
  SRule (RuleId "r1") [] [] [] [ObligationId "q1"] AssuranceNone

-- | An @r1@ instance discharging @q1@ with leaf @la : a@ — complete, concl @p@.
completeR1 :: SupportTerm
completeR1 =
  SRule (RuleId "r1") [] [] [(QuestionId "q1", SLeaf (LeafId "la"))] [] AssuranceNone

-- | An @r2@ instance — complete, concl @not_p@.
completeR2 :: SupportTerm
completeR2 = SRule (RuleId "r2") [] [] [] [] AssuranceNone

leavesGamma :: [(LeafId, Prop)]
leavesGamma = [(LeafId "la", pA)]

gamma :: LeafId -> Maybe Prop
gamma l = lookup l leavesGamma

-- | No strict rule appears, so the certificate oracle is never consulted.
noCert :: CertOk
noCert _ _ _ = False

-- | Assemble a unit over @[r1, r2]@ with the shared leaf context, given
-- arguments, attacks, and queries.
mkUnit :: [(ArgId, SupportTerm)] -> [Attack] -> [Prop] -> Unit
mkUnit args attacks queries =
  Unit
    { unitRules = [ruleR1, ruleR2]
    , unitContraries =
        [ Contrary (AtomPat (Pred "p") []) (AtomPat (Pred "p") [])
        , Contrary (AtomPat (Pred "not_p") []) (AtomPat (Pred "p") [])
        ]
    , unitExceptions = []
    , unitTheories = []
    , unitLeaves = leavesGamma
    , unitArgs = args
    , unitAttacks = attacks
    , unitQueries = queries
    , unitGroups = []
    , unitGroupMode = QuarantineOnConflict
    }

-- | Run the reporting analysis on a unit's queries.
reportsOf :: Unit -> [ClaimReport]
reportsOf u = claimReports (lookupRule (unitRules u)) gamma noCert u

-- | The single report for the first query.
report1 :: Unit -> ClaimReport
report1 u = case reportsOf u of
  (r : _) -> r
  [] -> error "report1: expected at least one query report"

-- ---------------------------------------------------------------------------
-- Golden case (a): empty complete support + a hole → gap + incompleteAlternative
-- ---------------------------------------------------------------------------

unitA :: Unit
unitA = mkUnit [(ArgId "a0", incompleteR1)] [] [pP]

prop_gapWithHole :: Bool
prop_gapWithHole =
  crStatus r == Gap
    && crIncompleteAlternative r
    && claimSupport (crClaim r) == [] -- no complete support for p
    && claimHoles (crClaim r) == [0] -- located at raw arg index 0
    && map iaObligations (crAlternatives r) == [[QuestionId "q1"]]
  where
    r = report1 unitA

-- ---------------------------------------------------------------------------
-- Golden case (b): several unresolved alternatives, holes located
-- ---------------------------------------------------------------------------

unitB :: Unit
unitB =
  mkUnit
    [ (ArgId "a0", incompleteR1)
    , (ArgId "a1", incompleteR1)
    ]
    []
    [pP]

prop_multipleHolesReported :: Bool
prop_multipleHolesReported =
  crStatus r == Gap
    && crIncompleteAlternative r
    && claimHoles (crClaim r) == [0, 1]
    && map iaIndex alts == [0, 1]
    && map iaArgId alts == [ArgId "a0", ArgId "a1"]
    && all ((== [QuestionId "q1"]) . iaObligations) alts
  where
    r = report1 unitB
    alts = crAlternatives r

-- ---------------------------------------------------------------------------
-- Golden case (c): complete winning alternative + a separate incomplete one
-- ---------------------------------------------------------------------------

unitC :: Unit
unitC =
  mkUnit
    [ (ArgId "a0", completeR1) -- complete, in
    , (ArgId "a1", incompleteR1) -- incomplete alternative, hole
    ]
    []
    [pP]

-- | The winning complete @in@ argument decides the status; the hole surfaces
-- only through the diagnostic (both invariants at once).
prop_completeNotSuppressed :: Bool
prop_completeNotSuppressed =
  crStatus r == Justified -- winning complete argument not downgraded
    && crIncompleteAlternative r -- hole still surfaced
    && claimSupport (crClaim r) == [0] -- complete node index 0 (a0)
    && claimHoles (crClaim r) == [1] -- incomplete alternative at raw index 1
    && map iaObligations (crAlternatives r) == [[QuestionId "q1"]]
  where
    r = report1 unitC

-- | Directly witness invariant one on the same shape: the full claim and the
-- complete-only projection agree on status (holes never change it).
prop_holesDoNotChangeStatus :: Bool
prop_holesDoNotChangeStatus =
  statusC af full == statusC af complete
    && labelC af 0 == LIn
    && statusC af full == Justified
  where
    (nodes, alts) = scanArguments (lookupRule (unitRules unitC)) gamma noCert (unitArgs unitC)
    af = reportAF (unitArgs unitC) (unitAttacks unitC) nodes
    full = reportClaimFor nodes alts pP
    complete = completeClaimFor nodes pP

-- ---------------------------------------------------------------------------
-- Golden case (contested): self-attack cycle + a coexisting hole
-- ---------------------------------------------------------------------------

unitContested :: Unit
unitContested =
  mkUnit
    [ (ArgId "a0", completeR1) -- complete, self-rebutting → undec
    , (ArgId "a1", incompleteR1) -- incomplete alternative, hole
    ]
    [Rebut (ArgId "a0") (ArgId "a0")]
    [pP]

prop_contestedWithHole :: Bool
prop_contestedWithHole =
  crStatus r == Contested -- support nonempty, its only complete arg is undec
    && crIncompleteAlternative r -- diagnostic still fires
    && claimSupport (crClaim r) == [0]
    && claimHoles (crClaim r) == [1]
  where
    r = report1 unitContested

-- ---------------------------------------------------------------------------
-- Golden case (defeated): rebutted complete support + a coexisting hole
-- ---------------------------------------------------------------------------

unitDefeated :: Unit
unitDefeated =
  mkUnit
    [ (ArgId "a0", completeR1) -- complete, concl p, gets rebutted → out
    , (ArgId "a1", completeR2) -- complete, concl not_p, unattacked → in
    , (ArgId "a2", incompleteR1) -- incomplete alternative for p, hole
    ]
    [Rebut (ArgId "a1") (ArgId "a0")]
    [pP]

prop_defeatedWithHole :: Bool
prop_defeatedWithHole =
  crStatus r == Defeated -- support nonempty, every complete arg out
    && crIncompleteAlternative r -- diagnostic still fires
    && claimSupport (crClaim r) == [0] -- only node concluding p
    && claimHoles (crClaim r) == [2] -- raw index of the incomplete alternative
  where
    r = report1 unitDefeated

-- ---------------------------------------------------------------------------
-- Step-5 guard: completeClaimFor vs. reportClaimFor are distinct
-- ---------------------------------------------------------------------------

-- | On a claim with an incomplete alternative, the complete-only projection has
-- empty holes while the full reporting path does not — the two are never the
-- same 'Claim'.
prop_completeVsReportDistinct :: Bool
prop_completeVsReportDistinct =
  claimHoles complete == []
    && claimHoles full /= []
    && complete /= full
    && claimSupport complete == claimSupport full -- same complete support
  where
    (nodes, alts) = scanArguments (lookupRule (unitRules unitC)) gamma noCert (unitArgs unitC)
    complete = completeClaimFor nodes pP
    full = reportClaimFor nodes alts pP

-- | The complete/incomplete partition itself is sound: exactly the complete
-- arguments become nodes (obligation-free) and exactly the incomplete ones
-- become located alternatives.
prop_scanPartition :: Bool
prop_scanPartition =
  map cnConclusion nodes == [pP, pNotP] -- a0 (r1 complete), a1 (r2)
    && map iaIndex alts == [2] -- a2 incomplete at raw index 2
    && claimSupportFor nodes pP == [0]
    && claimSupportFor nodes pNotP == [1]
  where
    (nodes, alts) = scanArguments (lookupRule (unitRules unitDefeated)) gamma noCert (unitArgs unitDefeated)

-- ---------------------------------------------------------------------------
-- Exported runner
-- ---------------------------------------------------------------------------

reportingSpecProps :: [(String, IO Result)]
reportingSpecProps =
  [ ("reporting (a) gap + incompleteAlternative on empty support", quickCheckResult prop_gapWithHole)
  , ("reporting (b) multiple unresolved alternatives located", quickCheckResult prop_multipleHolesReported)
  , ("reporting (c) complete winning argument not suppressed", quickCheckResult prop_completeNotSuppressed)
  , ("reporting (c) holes do not change status", quickCheckResult prop_holesDoNotChangeStatus)
  , ("reporting contested support with coexisting hole", quickCheckResult prop_contestedWithHole)
  , ("reporting defeated support with coexisting hole", quickCheckResult prop_defeatedWithHole)
  , ("reporting completeClaimFor vs reportClaimFor distinct", quickCheckResult prop_completeVsReportDistinct)
  , ("reporting lenient scan partitions complete/incomplete", quickCheckResult prop_scanPartition)
  ]
