-- | The whole-unit pipeline: decode → check → verdict (the Haskell side of the
-- N11 differential anchor, mirroring @lean/Lara/Driver.lean@).
--
-- 'runCheck' runs replay preflight and the real six-stage checker
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
module Lara.Driver
  ( buildGamma
    -- * The §4.3 prune, re-exported from "Lara.Blocked"
  , quarantinedLeaves
  , groupConsistent
  , supportUsesLeaf
  , quarantineUnit
  , Prune
  , prune
  , pruneDeclared
  , pruneChecked
  , groupConflictReject
  , groupConflictMessage
  , rejectionDiagnostics
  , buildCertOk
  , buildAccept
  , runCheck
  , runCheckLocated
  , runCheckLocatedWith
  ) where

import Data.List (intercalate)

import Lara.AST
  ( BackendId (..)
  , Cert (..)
  , DupGroup (..)
  , GroupConflictMode (..)
  , GroupId (..)
  , LeafId (..)
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
  , pruneChecked
  , pruneDeclared
  , quarantineUnit
  , quarantinedLeaves
  , supportUsesLeaf
  )
import Lara.Check (CheckConfig, CheckedUnit, checkUnitWith, cuNodes, cuProgram, fullConfig)
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
import Lara.SupportTerm (CertOk)
import qualified Lara.Strict as St
import qualified Lara.Strict.ND as ND
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
-- could reach, plus the ordinary six-stage 'checkUnit' rejection ('locate').
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
  let replayId = inputReplayId input
      unit = inputUnit input
      verdict outcome = Verdict replayId outcome
   in case runtimeReplayFailure input of
        Just failure ->
          ( verdict (Reject (RejectClass R13))
          , Just (LocatedRejection (RejectClass R13) StageReplayPreflight (replayFailureConstituent failure))
          )
        Nothing
          | groupConflictReject unit ->
              ( verdict (Reject (RejectClass R9))
              , Just (LocatedRejection (RejectClass R9) StageGroupBoundary (groupConflictConstituent unit))
              )
          | otherwise ->
              let pruned = prune unit
                  checked = pruneChecked pruned
               in case checkUnitWith cfg (buildGamma (unitLeaves checked)) (buildCertOk (unitTheories checked)) checked of
                    Left err -> (verdict (Reject (rejectionOf err)), Just (locate err))
                    Right accepted -> (verdict (buildAccept pruned accepted), Nothing)

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
groupConflictConstituent :: Unit -> Constituent
groupConflictConstituent unit =
  case filter (not . groupConsistent unit) (unitGroups unit) of
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
groupConflictReject unit =
  unitGroupMode unit == RejectOnConflict
    && any (not . groupConsistent unit) (unitGroups unit)

-- | The one @stderr@ line explaining an escalated group-conflict rejection (R9):
-- it names the first @≢@ group in declaration order and its members. @Nothing@
-- when no group is inconsistent (the caller only prints it on the R9 branch).
-- Both drivers print this exact template — like R13's 'replayFailureMessage' —
-- because the bare @(verdict reject R9)@ cannot say /which/ group conflicted, and
-- the differential harness byte-compares stderr.
groupConflictMessage :: Unit -> Maybe String
groupConflictMessage unit =
  case filter (not . groupConsistent unit) (unitGroups unit) of
    [] -> Nothing
    DupGroup (GroupId g) members : _ ->
      Just $
        "group '" ++ g ++ "': members "
          ++ intercalate ", " [m | LeafId m <- members]
          ++ " report one cell with ≢ propositions and "
          ++ "the policy escalates conflicts to reject (§4.3)"

-- | The @stderr@ diagnostic lines a driver prints alongside the verdict, in
-- 'runCheck's precedence: a replay-preflight failure (R13) explains itself,
-- otherwise an escalated group conflict (R9) does. Empty for an accept or an
-- ordinary checker rejection (those carry their location in the verdict alone).
-- Centralizing the precedence here keeps both @.sexp@ and @.lara@ front doors
-- byte-identical on stderr.
rejectionDiagnostics :: CheckInput -> [String]
rejectionDiagnostics input =
  case runtimeReplayFailure input of
    Just failure -> [replayFailureMessage failure]
    Nothing
      | groupConflictReject unit -> maybe [] (: []) (groupConflictMessage unit)
      | otherwise -> []
  where
    unit = inputUnit input

-- | The certificate oracle from the wire @theories@ section over the fixed
-- backend registry — @nd\@1@ and @ra\@1@ (Lean @buildRegistry@ \/
-- 'Lara.Examples' style). A unit referencing any other backend falls through
-- to certificate rejection.
buildCertOk :: [(TheoryDigest, [Prop])] -> CertOk
buildCertOk theories cert as c = case cert of
  Cert (BackendId name) v _ payload ->
    case St.lookupBackend registry (St.BackendId name v) of
      Nothing -> False
      Just backend ->
        case St.runBackend backend (toStrictDigest (certTheory cert)) as c payload of
          Right _ -> True
          Left _ -> False
  where
    registry = St.mkRegistry [ND.mkNDBackend table, RA.mkRABackend table]
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
