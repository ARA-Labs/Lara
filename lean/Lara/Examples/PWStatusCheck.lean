/-
Conformance cells for the executable StatusBridge checker.
Each positive T8 bridge is re-established by one `decide`; the T7 negative
goes through completeness: a `false` decider refutes the Prop.
`native_decide` is not used.

Beyond the four-way verdict, clause-level cells pin each conjunct
independently. T7 fails on *two* clauses — `matched` (the hand diagnosis at
`t7_unmatched`) and `back` (which the hand proofs never recorded) — while
`admits` and `forth` hold. Cross-paired fixtures isolate `admits`,
`matched`, `forth`, and `back` failures one at a time, guarding against a
clause scan that silently degenerates to always-true.
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

/-! ### T7, clause by clause

The four-way `&&` says only *that* T7 fails. These cells say *where*: the
forward-side failure is pinned to `matched` — `admits` and `forth` hold,
`matched` does not — and `back` fails too, a second clause the hand proofs
never recorded. -/

/-- The checker localises the failure to the `matched` clause, agreeing with
the hand diagnosis at `t7_unmatched`. -/
theorem t7_matchedB_false :
    matchedB SymMap.id (fun l => l) wT7src wT7tgt = false := by decide

/-- T7 *is* a forward homomorphism — `admits` and `forth` both hold, clause
for clause with `t7_forward_hom_insufficient`. -/
theorem t7_admits_forth_hold :
    admitsB SymMap.id (fun l => l) wT7src wT7tgt = true ∧
      forthB SymMap.id (fun l => l) wT7src wT7tgt = true := by decide

/-- The scan additionally reports `backB = false`: the target's `1 → 0`
attack has no counterpart back across the identity correlation (the source
program has no attacks at all), which the hand proofs never recorded. -/
theorem t7_backB_false :
    backB SymMap.id (fun l => l) wT7src wT7tgt = false := by decide

/-! ### Isolating negatives for `admitsB` and `matchedB`
(eng review, decision 6A)

`statusBridgeB` is a four-way `&&`, so a `false` result does not say which
conjunct fired — and the T7 pair fails on `matched` and `back` regardless,
so an accidentally always-*true* `admitsB` would pass every other cell in
this module. These four cells pin each conjunct independently, and need
**no new fixtures**: cross-pairing the
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

/-! ### Isolating negatives for `forthB` and `backB`

The duals of the cells above (and of T7's `matched`/`back` failures): a
deliberately mismatched cross-pair makes each directed scan fail while the
other three clauses hold, so neither scan can silently degenerate to a
vacuous or always-true pass. -/

/-- **The `forth` scan discriminates.** At the mismatched pair `wS3`/`wR2`
the other three clauses hold and only `forth` fails: `wS3`'s `0 → 1`
attack has no counterpart across the correlation into `wR2` (whose only
edge is `1 → 0`). Guards against a `forthB` that silently degenerates to a
vacuous scan. -/
theorem forthB_discriminates :
    admitsB symR leafMapR wS3 wR2 = true ∧
      matchedB symR leafMapR wS3 wR2 = true ∧
        backB symR leafMapR wS3 wR2 = true ∧
          forthB symR leafMapR wS3 wR2 = false := by decide

/-- **The `back` scan discriminates.** `wR3`'s `0 → 1` attack has no
counterpart back across the correlation into `wS2` (whose only edge is
`1 → 0`), while the other three clauses hold. -/
theorem backB_discriminates :
    admitsB symR leafMapR wS2 wR3 = true ∧
      matchedB symR leafMapR wS2 wR3 = true ∧
        forthB symR leafMapR wS2 wR3 = true ∧
          backB symR leafMapR wS2 wR3 = false := by decide

end Lara.Examples.PW.StatusCheck
