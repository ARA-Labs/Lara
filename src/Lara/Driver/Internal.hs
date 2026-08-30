-- | The whole-unit pipeline: decode → check → verdict (the Haskell side of the
-- N11 differential anchor, mirroring @lean/Lara/Driver.lean@).
--
-- 'runCheck' runs replay preflight and the real seven-stage checker
-- ("Lara.Check.checkUnit") on a validated 'CheckInput', producing the wire
-- 'Verdict' both drivers print. On acceptance it reads the grounded labels
-- ('Lara.Runtime.runtimeAF' — the cached-adjacency production backend, whose
-- verdict is byte-identical to the un-cached 'Lara.Compile.checkedAF' path),
-- the compiled closure edges in ascending order,
-- and one public status per query atom: an ordinary four-state answer, or
-- @evidence-blocked@ with the checked graph's label retained only as a
-- conditional diagnostic. On rejection it maps the located
-- 'Lara.Check.UnitError' to the wire class ('Lara.Diagnostics.rejectionOf').
--
-- The @lara@ CLI ("app/Main.hs") is a thin shell over this: it adds file I/O,
-- codec-error reporting, and the exit-code convention (0 accept, 1 reject, 2
-- codec\/usage).
module Lara.Driver.Internal
  ( buildGamma
    -- * The §4.3 prune, re-exported from "Lara.Blocked"
  , quarantinedLeaves
  , groupConsistent
  , supportUsesLeaf
  , quarantineUnit
  , Prune
  , prune
  , pruneWithPolicySeed
  , pruneDeclared
  , pruneChecked
  , groupConflictReject
  , groupConflictMessage
  , backendRejectionMessage
  , backendRejectionSlots
  , slotMappingLines
  , buildCertOk
  , buildAccept
  , runCheck
  , runCheckLocated
  , runCheckLocatedWith
  , runCheckLocatedReported
  , runCheckWithPrune
  , runCheckReported
  ) where

import Data.List (intercalate)

import Lara.AST
  ( BackendId (..)
  , Cert (..)
  , certRefVersion
  , DupGroup (..)
  , GroupConflictMode (..)
  , GroupId (..)
  , LeafId (..)
  , RuleId (..)
  , TheoryDigest (..)
  , RejectClass (..)
  , Rejection (..)
  , Unit (..)
  )
import Lara.Blocked
  ( Prune
  , blockedQueries
  , groupConsistent
  , prune
  , pruneWithPolicySeed
  , pruneChecked
  , pruneDeclared
  , pruneInconsistentGroups
  , quarantineUnit
  , quarantinedLeaves
  , supportUsesLeaf
  )
import Lara.Check
  ( CheckConfig
  , CheckedUnit
  , ProgramError (..)
  , UnitError (..)
  , checkUnitWith
  , cuNodes
  , cuProgram
  , fullConfig
  )
import Lara.Replay
  ( CheckInput
  , ReplayFailure (..)
  , inputReplayId
  , inputUnit
  , replayFailureMessage
  , runtimeReplayFailure
  )
import Lara.Diagnostics
  ( Constituent (..)
  , LocatedRejection (..)
  , Stage (..)
  , locate
  , rejectionOf
  )
import Lara.Grounded (AF (..), completeClaimFor, labelC, statusC)
import Lara.Runtime (runtimeAF)
import Lara.Prop (Prop)
import Lara.SupportTerm
  ( BackendReason (..)
  , CertOk
  , CertOutcome (..)
  , CheckError (..)
  , SlotSource (..)
  )
import qualified Lara.Strict as St
import qualified Lara.Strict.ND as ND
import qualified Lara.Strict.Ord as Ord
import qualified Lara.Strict.RA as RA
import Lara.Wire (Outcome (..), PublicStatus (..), Verdict (..))

-- | Run replay preflight, the duplicate-report-group boundary check, and the
-- checker, retaining the validated identity. Precedence mirrors the spec's
-- layering: replay identity (R13) gates first; then the §4.3 group check applies
-- — an escalated conflict rejects the whole program (R9); otherwise every
-- argument that uses a quarantined leaf is dropped from the checked program (its
-- claim then has no support and surfaces as @gap@, per §4.3 — quarantine is not
-- a rejection); then @checkUnit@ runs on the reduced unit.
runCheck :: CheckInput -> Verdict
runCheck = fst . runCheckLocated

-- | 'runCheck' paired with the located rejection that produced its verdict, from
-- the /same/ decision path — so every reject carries a 'Constituent' located by
-- the code that also picked its class, across all three reject paths: the
-- replay preflight (R13) and the §4.3 group check (R9), which both reject here
-- before 'checkUnit' and never become a 'Lara.Check.UnitError' that 'locate'
-- could reach, plus the ordinary seven-stage 'checkUnit' rejection ('locate').
-- 'Nothing' on acceptance. The iron invariant @runCheck ≡ fst . runCheckLocated@
-- holds by construction (the measurement harness re-asserts it over every
-- manifest-discovered input).
runCheckLocated :: CheckInput -> (Verdict, Maybe LocatedRejection)
runCheckLocated = runCheckLocatedWith fullConfig

-- | 'runCheckLocated' under an explicit 'Lara.Check.CheckConfig' (the M5
-- ablation entry point): the config reaches only 'Lara.Check.checkUnitWith' —
-- the R13 replay preflight and the R9 group boundary are never ablated.
-- @runCheckLocatedWith fullConfig = runCheckLocated@ definitionally, and the
-- config is never carried on the wire.
runCheckLocatedWith :: CheckConfig -> CheckInput -> (Verdict, Maybe LocatedRejection)
runCheckLocatedWith cfg input =
  runCheckWithPrune cfg input (prune (inputUnit input))

-- | 'runCheckLocatedWith' plus the @stderr@ lines the rejection warrants — the
-- raw @.sexp@ door's entry point, and the only reporting entry point
-- "Lara.Driver" exposes publicly.
--
-- It exists so that a raw-door caller never has to build a 'Prune' itself: the
-- ordinary group-only prune is this module's business, and pairing a raw
-- 'CheckInput' with a 'Prune' stays package-internal (see the "Lara.Driver"
-- header).  Source callers reach the same single pass through
-- 'Lara.Elaborate.prepareSource', which supplies the source-boundary prune.
runCheckLocatedReported
  :: CheckConfig
  -> CheckInput
  -> (Verdict, Maybe LocatedRejection, [String])
runCheckLocatedReported cfg input =
  let (verdict, located, diagnostics, slots) =
        runCheckReported cfg input (prune (inputUnit input))
   in (verdict, located, diagnostics ++ slotMappingLines slots)

-- | Execute the checker against a source-boundary prune while retaining replay
-- preflight and group decisions over the original declared unit.  The source
-- smart constructor is the production caller; raw @.sexp@ inputs continue to
-- enter through 'runCheckLocatedWith' and obtain the ordinary group-only prune.
--
-- @
-- replay(declared) -> groups(declared) -> check(pruneChecked) -> overlay(prune)
-- @
runCheckWithPrune :: CheckConfig -> CheckInput -> Prune -> (Verdict, Maybe LocatedRejection)
runCheckWithPrune cfg input pruned =
  let (verdict, located, _, _) = runCheckReported cfg input pruned
   in (verdict, located)

-- | 'runCheckWithPrune' plus the @stderr@ lines the rejection warrants, all
-- from __one__ pass: the verdict, its located rejection, and its diagnostics
-- are three readings of the same decision, so a diagnostic can never explain a
-- rejection the driver did not make.
--
-- That single-pass property is the whole reason this exists. The alternative —
-- computing diagnostics from the input in a second traversal — either re-runs
-- the checker (doubling the work the E1 bench measures) or reconstructs the
-- decision independently and risks disagreeing with it.
runCheckReported
  :: CheckConfig
  -> CheckInput
  -> Prune
  -> (Verdict, Maybe LocatedRejection, [String], [SlotSource])
runCheckReported cfg input pruned =
  let replayId = inputReplayId input
      verdict outcome = Verdict replayId outcome
   in case runtimeReplayFailure input of
        Just failure ->
          ( verdict (Reject (RejectClass R13))
          , Just (LocatedRejection (RejectClass R13) StageReplayPreflight (replayFailureConstituent failure))
          , [replayFailureMessage failure]
          , []
          )
        Nothing
          | groupConflictRejectPrune pruned ->
              ( verdict (Reject (RejectClass R9))
              , Just (LocatedRejection (RejectClass R9) StageGroupBoundary (groupConflictConstituent pruned))
              , maybe [] (: []) (groupConflictMessageWithPrune pruned)
              , []
              )
          | otherwise ->
              let checked = pruneChecked pruned
               in case checkUnitWith cfg (buildGamma (unitLeaves checked)) (buildCertOk (unitTheories checked)) checked of
                    Left err ->
                      ( verdict (Reject (rejectionOf err))
                      , Just (locate err)
                      , maybe [] (: []) (backendRejectionMessage err)
                      , backendRejectionSlots err
                      )
                    Right accepted -> (verdict (buildAccept pruned accepted), Nothing, [], [])

-- | The one @stderr@ line explaining a __checker-side__ R13: the registered
-- backend replayed the certificate and refused it, and this is the reason it
-- gave. 'Nothing' for every other rejection class, and for the R13s raised by
-- replay preflight before the checker runs ('replayFailureMessage' covers
-- those).
--
-- Without this the only rejection produced by a registered backend was also the
-- only one that said nothing: bare @(verdict … reject R13)@ on @stdout@ and an
-- empty @stderr@, even though the adapter had a precise reason in hand. An
-- author who trips @ord\@1@'s premise-only guard now reads @ord cites premise
-- slots only; slot names theory entry 0@ instead of guessing.
--
-- __Why the Lean driver stays silent here.__ The two drivers reach the same
-- acceptance set by different routes: the Haskell adapters enforce premise-only
-- slots directly, while Lean's abstract @Backend@ core is handed a single
-- context @Γ = Δ ++ T@ and cannot see @Δ.length@, so @buildRegistry@ gets the
-- same effect by resolving a known digest to the empty theory. The two agree on
-- every verdict, and would /not/ agree on the wording of a slot rejection.
-- @scripts\/differential.sh@ byte-compares @stdout@ and the exit code on every
-- anchor and leaves @stderr@ free except on the preflight and group-conflict
-- anchors, whose templates are byte-identical by construction; this line is on
-- neither. Making Lean reproduce these strings would mean widening the
-- mechanized seam to carry prose, which buys nothing a proof depends on.
backendRejectionMessage :: UnitError -> Maybe String
backendRejectionMessage err = case err of
  UEProgram (PERejection _ (CE_R13 _ (ReplayRejected (BackendId name) (TheoryDigest digest) ref reason _)))
    | not (null reason) ->
        Just
          ( "certificate replay: "
              ++ name
              ++ "@"
              ++ show (certRefVersion ref)
              ++ " (theory "
              ++ digest
              ++ ") rejected the certificate: "
              ++ reason
          )
  _ -> Nothing

-- | The slot → source mapping of a __checker-side__ R13 (#130): what the
-- checked term put in each premise slot the refused certificate cites. Empty
-- for every other rejection class, and for the preflight R13s, which reject
-- before a premise list exists.
--
-- It is read off the /same/ 'UnitError' that produced the verdict — the
-- mapping is built where the rejection is raised
-- ("Lara.SupportTerm".@assuranceError@), never reconstructed from the input,
-- so it cannot describe a different instance than the one that was refused.
backendRejectionSlots :: UnitError -> [SlotSource]
backendRejectionSlots err = case err of
  UEProgram (PERejection _ (CE_R13 _ (ReplayRejected _ _ _ _ slots))) -> slots
  _ -> []

-- | Render a slot → source mapping as one @stderr@ line per slot, under the
-- rejection reason it explains (#130).
--
-- __Why this is worth a line each.__ The bare reason names a @(prem i)@ the
-- author is left to decode by hand against the policy declarations. A numeric
-- certificate, an @nd\@1@ proof term, and a third-party artifact all reject
-- this way, and none of them is reached by the @lara-syntax\@0.6@ named slots,
-- which fix the same mistake at authoring time on the @.lara@ door only.
--
-- This is the __structural__ reading, so it is what both doors can always say.
-- The @.lara@ door replaces it with the authored spelling where it has one
-- ('Lara.Elaborate.sourceResultAuthorDiagnostics'); this rendering is what a
-- raw @.sexp@ input gets, and what the source door falls back to.
--
-- Empty in, empty out — a rejection with no premise list adds nothing.
slotMappingLines :: [SlotSource] -> [String]
slotMappingLines = zipWith line [0 :: Int ..]
  where
    line i src = "  slot " ++ show i ++ " = " ++ renderSlotSource src

-- | The structural spelling of one slot's source (#130).
renderSlotSource :: SlotSource -> String
renderSlotSource src = case src of
  SlotLeaf (LeafId l) -> "leaf " ++ l
  SlotDerived (RuleId r) -> "derived by " ++ r

-- | The located constituent of a replay-preflight (R13) failure: the
-- backend-selection failures locate at the replay envelope (the ground truth
-- the @duplicate-backend@\/@unknown-backend@ operators seed); an unselected
-- certificate backend locates at its argument (mirroring the @expected.json@
-- rendering).
replayFailureConstituent :: ReplayFailure -> Constituent
replayFailureConstituent failure = case failure of
  DuplicateSelectedBackend{} -> CReplayEnvelope
  UnknownSelectedBackend{} -> CReplayEnvelope
  CertificateBackendNotSelected index _ _ _ -> CArgument index

-- | The located constituent of an escalated group-conflict (R9): the first @≢@
-- group in declaration order (the same group 'groupConflictMessage' names).
-- 'CPolicy' is unreachable when 'groupConflictReject' held.
groupConflictConstituent :: Prune -> Constituent
groupConflictConstituent pruned =
  case pruneInconsistentGroups pruned of
    DupGroup gid _ : _ -> CGroup gid
    [] -> CPolicy

-- | The leaf context @Gamma@ from the wire @leaves@ section (first-match lookup,
-- Lean @buildGamma@).
buildGamma :: [(LeafId, Prop)] -> LeafId -> Maybe Prop
buildGamma leaves l = lookup l leaves

-- | Whether the policy escalates a detected group conflict to a whole-program
-- data-integrity rejection (R9, spec §4.3): the mode is 'RejectOnConflict' and
-- at least one declared group is @≢@.
groupConflictReject :: Unit -> Bool
groupConflictReject = groupConflictRejectPrune . prune

groupConflictRejectPrune :: Prune -> Bool
groupConflictRejectPrune pruned =
  unitGroupMode (pruneDeclared pruned) == RejectOnConflict
    && not (null (pruneInconsistentGroups pruned))

-- | The one @stderr@ line explaining an escalated group-conflict rejection (R9):
-- it names the first @≢@ group in declaration order and its members. @Nothing@
-- when no group is inconsistent (the caller only prints it on the R9 branch).
-- Both drivers print this exact template — like R13's 'replayFailureMessage' —
-- because the bare @(verdict reject R9)@ cannot say /which/ group conflicted, and
-- the differential harness byte-compares stderr.
groupConflictMessage :: Unit -> Maybe String
groupConflictMessage = groupConflictMessageWithPrune . prune

groupConflictMessageWithPrune :: Prune -> Maybe String
groupConflictMessageWithPrune pruned =
  case pruneInconsistentGroups pruned of
    [] -> Nothing
    DupGroup (GroupId g) members : _ ->
      Just $
        "group '" ++ g ++ "': members "
          ++ intercalate ", " [m | LeafId m <- members]
          ++ " report one cell with ≢ propositions and "
          ++ "the policy escalates conflicts to reject (§4.3)"

-- | The certificate oracle from the wire @theories@ section over the fixed
-- backend registry — @nd\@1@, @ra\@1@ and @ord\@1@ (Lean @buildRegistry@). A
-- unit referencing any other backend falls through to certificate rejection.
--
-- Every backend is handed the same artifact-supplied table. @ord\@1@ is the
-- one that refuses to /cite/ it: it rejects any certificate slot at or beyond
-- the premise count, so its compared values always trace to a consulted
-- premise (see "Lara.Strict.Ord"). On the Lean side the same acceptance set
-- is reached by resolving a known @ord\@1@ digest to the empty theory.
buildCertOk :: [(TheoryDigest, [Prop])] -> CertOk
buildCertOk theories cert as c = case cert of
  Cert (BackendId name) v _ payload ->
    case St.lookupBackend registry (St.BackendId name v) of
      Nothing -> CertRejected ("no registered backend " ++ name ++ "@" ++ show v)
      Just backend ->
        case St.runBackend backend (toStrictDigest (certTheory cert)) as c payload of
          -- The adapter's 'St.Dependency' report is retained, not discarded:
          -- this is the production path that reaches backends (@strictCheck@ is
          -- test-only), so accounting built on anything else would account
          -- nothing the shipped checker ran. It stays inert with respect to
          -- acceptance — 'certAccepted' is a 'Bool' — and is read only by
          -- "Lara.Strict.Deps" (design note D9 in "Lara.SupportTerm").
          Right deps -> CertAccepted deps
          Left reason -> CertRejected reason
  where
    registry =
      St.mkRegistry [ND.mkNDBackend table, RA.mkRABackend table, Ord.mkOrdBackend table]
    table = [(toStrictDigest d, ps) | (d, ps) <- theories]

toStrictDigest :: TheoryDigest -> St.TheoryDigest
toStrictDigest (TheoryDigest s) = St.TheoryDigest s

-- | Read the accept outcome off an accepted unit (Lean @buildAccept@).
--
-- Two units, because §4.3 quarantine makes them differ: @declared@ is the unit
-- as submitted and @checked@ is 'quarantineUnit'\'s reduced program, the one the
-- labels, edges, and statuses are computed on. When the two differ, the
-- statuses are __conditional__ — grounded status is non-monotonic across graph
-- changes, so a deleted attacker can inflate its target. 'blockedQueries' names
-- the queries that could have moved; they are reported @evidence-blocked@ and
-- their conditional label is retained as a diagnostic (issue #76; metatheory in
-- @lean\/Lara\/Blocked.lean@). With nothing quarantined the two units are equal,
-- the blocked list is empty, and this is the pre-#76 outcome exactly.
buildAccept :: Prune -> CheckedUnit -> Outcome
buildAccept pruned accepted =
  Accept
    { verdictLabels = [(i, labelC af i) | i <- [0 .. n - 1]]
    , verdictEdges = [(i, j) | i <- [0 .. n - 1], j <- [0 .. n - 1], afAttack af i j]
    , verdictStatuses =
        [ (p, publicStatus p (statusC af (completeClaimFor (cuNodes accepted) p)))
        | p <- queries
        ]
    }
  where
    af = runtimeAF (cuProgram accepted)
    n = length (afArgs af)
    queries = unitQueries (pruneDeclared pruned)
    blocked = blockedQueries pruned (cuNodes accepted) queries
    publicStatus p
      | p `elem` blocked = EvidenceBlocked
      | otherwise = Published
