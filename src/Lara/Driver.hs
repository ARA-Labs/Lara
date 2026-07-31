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
  , buildCertOk
  , buildAccept
  , runCheck
  ) where

import Lara.AST
  ( BackendId (..)
  , Cert (..)
  , LeafId
  , TheoryDigest (..)
  , RejectClass (..)
  , Rejection (..)
  , Unit (..)
  )
import Lara.Check (CheckedUnit, checkUnit, cuNodes, cuProgram)
import Lara.Replay (CheckInput, inputReplayId, inputUnit, runtimeReplayFailure)
import Lara.Diagnostics (rejectionOf)
import Lara.Grounded (AF (..), completeClaimFor, labelC, statusC)
import Lara.Runtime (runtimeAF)
import Lara.Prop (Prop)
import Lara.SupportTerm (CertOk)
import qualified Lara.Strict as St
import qualified Lara.Strict.ND as ND
import Lara.Wire (Outcome (..), Verdict (..))

-- | Run replay preflight and the checker, retaining the validated identity.
runCheck :: CheckInput -> Verdict
runCheck input =
  let replayId = inputReplayId input
      unit = inputUnit input
   in Verdict replayId $
        case runtimeReplayFailure input of
          Just _ -> Reject (RejectClass R13)
          Nothing ->
            case checkUnit (buildGamma (unitLeaves unit)) (buildCertOk (unitTheories unit)) unit of
              Left err -> Reject (rejectionOf err)
              Right accepted -> buildAccept unit accepted

-- | The leaf context @Gamma@ from the wire @leaves@ section (first-match lookup,
-- Lean @buildGamma@).
buildGamma :: [(LeafId, Prop)] -> LeafId -> Maybe Prop
buildGamma leaves l = lookup l leaves

-- | The certificate oracle from the wire @theories@ section over the one
-- implemented backend @nd\@1@ (Lean @buildRegistry@ \/ 'Lara.Examples' style). A
-- unit referencing any other backend falls through to certificate rejection.
buildCertOk :: [(TheoryDigest, [Prop])] -> CertOk
buildCertOk theories cert as c = case cert of
  Cert (BackendId name) v _ payload ->
    (name, v) == (St.backendName ND.ndBackendId, St.backendVersion ND.ndBackendId)
      && case St.runBackend ndBackend (toStrictDigest (certTheory cert)) as c payload of
        Right _ -> True
        Left _ -> False
  where
    ndBackend = ND.mkNDBackend [(toStrictDigest d, ps) | (d, ps) <- theories]

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
