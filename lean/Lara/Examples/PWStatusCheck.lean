/-
Conformance cells for the executable StatusBridge checker (issue #239).
Each positive T8 bridge is re-established by one `decide`; the T7 negative
goes through completeness: a `false` decider refutes the Prop.
`native_decide` is not used.
-/

import Lara.PW.StatusCheck
import Lara.Examples.PWStatus

namespace Lara.Examples.PW.StatusCheck

open Lara.PW Lara.Examples.PW Lara.Examples.PW.Status

/-- The S1/R1 cell, one `decide`. -/
theorem s1_r1_decider : statusBridgeB symR leafMapR wS1 wR1 = true := by
  decide

/-- The S2/R2 cell (a real edge on each side), one `decide`. -/
theorem s2_r2_decider : statusBridgeB symR leafMapR wS2 wR2 = true := by
  decide

/-- The S3/R3 cell (two symmetric attacks), one `decide`. -/
theorem s3_r3_decider : statusBridgeB symR leafMapR wS3 wR3 = true := by
  decide

/-- Soundness turns each decider cell back into the Prop-level bridge. -/
theorem s2_r2_statusBridge_via_decider :
    Lara.PW.StatusBridge (κ := ctxS) (lam := ctxR) symR leafMapR wS2 wR2 :=
  statusBridgeB_sound s2_r2_decider

/-- The T7 identity pair fails the scan. -/
theorem t7_decider_rejects :
    statusBridgeB SymMap.id (fun l => l) wT7src wT7tgt = false := by
  decide

/-- Completeness makes the `false` cell a refutation: T7 is not a
`StatusBridge`, now through the decider rather than by hand. -/
theorem t7_not_statusBridge_via_decider :
    ¬ Lara.PW.StatusBridge (κ := ctxT7) (lam := ctxT7) SymMap.id (fun l => l)
      wT7src wT7tgt := fun h => by
  have hc := statusBridgeB_complete h
  rw [t7_decider_rejects] at hc
  exact Bool.false_ne_true hc

/-! ### Isolating negatives for `admitsB` and `matchedB`
(eng review, decision 6A)

`statusBridgeB` is a four-way `&&`, so a `false` result does not say which
conjunct fired — and the T7 pair shares its arguments, failing only on the
attack clauses. An accidentally always-*true* `admitsB` or `matchedB` would
therefore pass every other cell in this module. These four cells pin each
conjunct independently, and need **no new fixtures**: cross-pairing the
existing renaming worlds already separates them (`wS1`/`wR1` carry one
argument, `wS2`/`wR2` carry two).

All four are *[scratch-verified]* against `main` (0c5ffd9). -/

/-- `wS2` has an argument that lands outside `wR1`: `admits` fails … -/
theorem s2_r1_admits_fails : admitsB symR leafMapR wS2 wR1 = false := by decide

/-- … while `matched` still holds, so the failure is isolated. -/
theorem s2_r1_matched_holds : matchedB symR leafMapR wS2 wR1 = true := by decide

/-- `wR2` carries an argument that is nobody's transport: `matched` fails … -/
theorem s1_r2_matched_fails : matchedB symR leafMapR wS1 wR2 = false := by decide

/-- … while `admits` still holds, so that failure is isolated too. -/
theorem s1_r2_admits_holds : admitsB symR leafMapR wS1 wR2 = true := by decide

end Lara.Examples.PW.StatusCheck
