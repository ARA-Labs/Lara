-- | The whole-unit pipeline: decode → check → verdict (the Haskell side of the
-- N11 differential anchor, mirroring @lean/Lara/Driver.lean@).
--
-- 'runCheck' runs replay preflight and the real six-stage checker
-- ("Lara.Check.checkUnit") on a validated 'CheckInput', producing the wire
-- 'Verdict' both drivers print. On acceptance it reads the grounded labels
-- ('Lara.Runtime.runtimeAF' — the cached-adjacency production backend, whose
-- verdict is byte-identical to the un-cached 'Lara.Compile.checkedAF' path),
-- the compiled closure edges in ascending order,
-- and one four-state status per query atom; on rejection it maps the located
-- 'Lara.Check.UnitError' to the wire class ('Lara.Diagnostics.rejectionOf').
--
-- The @lara@ CLI ("app/Main.hs") is a thin shell over this: it adds file I/O,
-- codec-error reporting, and the exit-code convention (0 accept, 1 reject, 2
-- codec\/usage).
module Lara.Driver
  ( buildGamma
  , quarantinedLeaves
  , groupConsistent
  , groupConflictReject
  , groupConflictMessage
  , rejectionDiagnostics
  , supportUsesLeaf
  , quarantineUnit
  , buildCertOk
  , buildAccept
  , runCheck
  , runCheckLocated
  , runCheckLocatedWith
  ) where

import Data.List (intercalate)

import Lara.AST
  ( Attack (..)
  , ArgId
  , BackendId (..)
  , Cert (..)
  , DupGroup (..)
  , GroupConflictMode (..)
  , GroupId (..)
  , LeafId (..)
  , SupportTerm (..)
  , TheoryDigest (..)
  , RejectClass (..)
  , Rejection (..)
  , Unit (..)
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
import Lara.Prop (Prop, equiv)
import Lara.SupportTerm (CertOk)
import qualified Lara.Strict as St
import qualified Lara.Strict.ND as ND
import qualified Lara.Strict.RA as RA
import Lara.Wire (Outcome (..), Verdict (..))

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
              let checked = quarantineUnit unit
               in case checkUnitWith cfg (buildGamma (unitLeaves checked)) (buildCertOk (unitTheories checked)) checked of
                    Left err -> (verdict (Reject (rejectionOf err)), Just (locate err))
                    Right accepted -> (verdict (buildAccept checked accepted), Nothing)

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

-- | A declared duplicate-report group is @≡@-consistent iff its members'
-- propositions are pairwise @≡@ (spec §4.3). Because @≡@ is transitive, this is
-- exactly "every member @≡@ the first member". Both front doors validate group
-- well-formedness before a 'Unit' reaches here (wire "Lara.Wire".@checkGroupInvariants@
-- / @.lara@ "Lara.Elaborate".@validateGroups@), so every member normally resolves;
-- as defense-in-depth an /unresolvable/ member is treated as a conflict rather
-- than silently skipped, so a dangling member can never degrade a group to a
-- vacuously-consistent singleton and evade R9. The empty/singleton cases are
-- vacuously consistent.
groupConsistent :: Unit -> DupGroup -> Bool
groupConsistent unit (DupGroup _ members) =
  case mapM (`lookup` unitLeaves unit) members of
    Nothing -> False -- a member with no Γ entry cannot be shown ≡-consistent
    Just [] -> True
    Just (p : ps) -> all (equiv p) ps

-- | The leaf ids quarantined by a @≢@ duplicate-report group (spec §4.3): every
-- member of every inconsistent group leaves @Gamma@.
quarantinedLeaves :: Unit -> [LeafId]
quarantinedLeaves unit =
  [ l
  | g <- unitGroups unit
  , not (groupConsistent unit g)
  , l <- dgMembers g
  ]

-- | Whether a support term uses any of the given leaves anywhere in its tree
-- (spec §4.3 "any argument using a conflicted cell"): the principal leaf, or a
-- premise\/discharge sub-term's leaf.
supportUsesLeaf :: [LeafId] -> SupportTerm -> Bool
supportUsesLeaf qs = go
  where
    go (SLeaf l) = l `elem` qs
    go (SRule _ _ premises discharges _ _) =
      any go premises || any (go . snd) discharges

-- | The unit the checker actually sees under §4.3 quarantine: every argument
-- that uses a quarantined leaf is removed (its claim loses that support and
-- surfaces as @gap@, never a rejection), together with every attack whose
-- endpoints no longer resolve, and the quarantined leaves themselves leave the
-- context. When no group conflicts, this is the identity.
quarantineUnit :: Unit -> Unit
quarantineUnit unit =
  let quarantined = quarantinedLeaves unit
      keptArgs = [pair | pair@(_, t) <- unitArgs unit, not (supportUsesLeaf quarantined t)]
      keptIds = map fst keptArgs
      keptAttacks = [k | k <- unitAttacks unit, all (`elem` keptIds) (attackEndpoints k)]
   in unit
        { unitArgs = keptArgs
        , unitAttacks = keptAttacks
        , unitLeaves = [entry | entry@(l, _) <- unitLeaves unit, l `notElem` quarantined]
        }
  where
    attackEndpoints :: Attack -> [ArgId]
    attackEndpoints k = case k of
      Rebut w u -> [w, u]
      Undercut w u _ -> [w, u]
      Undermine w u _ -> [w, u]

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
buildAccept :: Unit -> CheckedUnit -> Outcome
buildAccept unit accepted =
  Accept
    { verdictLabels = [(i, labelC af i) | i <- [0 .. n - 1]]
    , verdictEdges = [(i, j) | i <- [0 .. n - 1], j <- [0 .. n - 1], afAttack af i j]
    , verdictStatuses =
        [(p, statusC af (completeClaimFor (cuNodes accepted) p)) | p <- unitQueries unit]
    }
  where
    af = runtimeAF (cuProgram accepted)
    n = length (afArgs af)
