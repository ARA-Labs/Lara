/-
# Located holes in the surface claim map, kernel-checked

The surface classifies a claim's alternatives by the accepted unit's cached
partition (`Surface.claimsOf`, D8). This fixture runs the core checker in the
kernel on one retained ledger that mixes every acceptance case the cutover
names, and reads the claim map off the checked cache:

* `tMix` leaves mandatory `q1` open at its root (and optional `q2` beside it);
* `tUse` inherits `q1` from its premise `tMix` (transitive premise hole);
* `tDisUse` discharges `q1` with `tUse`, whose open `q1` comes back up through
  the discharge, leaving exactly one `q1` (transitive discharge hole);
* `tOpt` discharges `q1` with a leaf and leaves only optional `q2` open: it is
  complete support, although its authored root open set is nonempty;
* `.leaf l1` is a plain complete alternative.

The ledger rows are what `Surface.claimAlternativesOf` produces when each
argument's authored conclusion names the claim of its proposition. Nothing
here evaluates support inference outside the checker.
-/
import Lara.Examples
import Lara.Surface.Observation

namespace Lara.Examples.SurfaceHoles

open Lara.Support Lara.Check.Unit

/-- `ruleMix` with mandatory `q1` discharged by a leaf: only optional `q2`
stays open. -/
def tOpt : SupportTerm := .inst rMixId [] [] [(q1, .leaf l2)] [q2] .none

/-- The retained ledger: hole, complete, hole, hole, complete. -/
def holesUnit : Lara.Unit :=
  { sigma := sigmaEx
  , policy := unitPolicyEx
  , args := [tMix, .leaf l1, tUse, tDisUse, tOpt]
  , atts := [] }

def holesCheck := checkUnit ΓEx registryEx groundEx holesUnit

/-- The unit is accepted: no hole rejects it. -/
theorem holesCheck_ok : holesCheck.isOk = true := by decide

def holesChecked : Lara.Unit.CheckedUnit id ΓEx (certOkOf registryEx) :=
  holesCheck.toOption.get (by decide)

/-- The claim alternative ledger: `claim-p` is concluded at positions 0, 1, 3
and 4; `claim-q` only by the premise hole at position 2. -/
def holesLedger : List (Lara.Presentation.PropId × List Nat) :=
  [(⟨"claim-p"⟩, [0, 1, 3, 4]), (⟨"claim-q"⟩, [2])]

/-- **The cached partition.** The AF nodes sit at declarations 1 and 4; the
three holes are located at 0, 2 and 3, each with exactly `[q1]`: the
transitive premise and discharge obligations are deduplicated, and optional
`q2` never counts. -/
theorem holes_partition :
    holesChecked.nodeDecls = [1, 4] ∧
      holesChecked.holes.map (fun hole => (hole.index, hole.obligations)) =
        [(0, [q1]), (2, [q1]), (3, [q1])] ∧
      holesChecked.holes.map (·.conclusion) = [pA, pB, pA] := by
  decide

/-- **The claim map.** `claim-p` has complete support (AF nodes 0 and 1, i.e.
`.leaf l1` and `tOpt`) and reports the root and discharge holes beside it;
`claim-q` has only the premise hole. -/
theorem holes_claims :
    (Lara.Surface.claimsOf holesChecked.nodeDecls
        (holesChecked.holes.map (·.index)) holesLedger).map
        (fun row => (row.1, row.2.support, row.2.holes)) =
      [ (⟨"claim-p"⟩, [0, 1], [0, 3])
      , (⟨"claim-q"⟩, [], [2]) ] := by
  decide

/-- The classified claim map read off the checked cache. -/
def holesClaims : List (Lara.Presentation.PropId × Grounded.Claim) :=
  Lara.Surface.claimsOf holesChecked.nodeDecls
    (holesChecked.holes.map (·.index)) holesLedger

/-- **Complete and incomplete alternatives for one conclusion:** status comes
from complete support, and the holes are still reported. -/
theorem holes_complete_alternative_status :
    (Lara.Surface.lookupClaim? holesClaims ⟨"claim-p"⟩).map
        (fun claim =>
          (Grounded.statusC (Compile.checkedAF holesChecked.program) claim,
            Grounded.incompleteAlternative claim)) =
      some (.justified, true) := by
  decide

/-- **Only incomplete alternatives:** `gap`. -/
theorem holes_only_incomplete_gap :
    (Lara.Surface.lookupClaim? holesClaims ⟨"claim-q"⟩).map
        (Grounded.statusC (Compile.checkedAF holesChecked.program)) =
      some .gap := by
  decide

/-- **Optional-only open questions are complete support.** `tOpt` is an AF
argument and no hole sits at its position, while its authored root open set —
the separate diagnostic ledger (`Surface.openQuestionsOf`) — still records
`q2`. -/
theorem holes_optional_only :
    tOpt ∈ holesChecked.program.args ∧
      4 ∉ holesChecked.holes.map (·.index) ∧
      Lara.Surface.rootHoles tOpt = [q2] := by
  decide

end Lara.Examples.SurfaceHoles
