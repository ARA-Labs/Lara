import Lara.Process.Inquiry
import Lara.Examples.ProcessEntitlement

/-!
Fixtures for the inquiry interface, over the two-history model of
`Lara.Examples.ProcessEntitlement`.

* `sensitivity_fixture`: the audit of witness `w1` is unstable over both
  histories; `right` is the history that flips it.
* `stable_not_entitled`: a claim that is true in every completion of an inquiry
  is stable, yet no witness warrants it, so it is not entitled. Stability is not
  scientific adequacy.
* `status_does_not_transport`: the claim keeps the grounded status `justified`
  in both histories, yet the submitted argument `w1` is entitled on the record
  of `left` and not on the record of `right`.
-/

namespace Lara.Examples.ProcessInquiry

open Lara.Grounded
open Lara.Process
open Lara.Examples.ProcessEntitlement

def both : Inquiry Hist := ⟨{.left, .right}⟩

/-- The audit of `w1` flips between the histories. -/
theorem sensitivity_fixture :
    ¬ both.Stable (fun h => Warranted model strict h claimC .w1) ∧
      both.sensitivity (fun h => Warranted model strict h claimC .w1) .left = {.right} := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- A claim nobody argues for. -/
def unargued : ClaimId := ⟨1⟩

/-- A record that reports the history itself. -/
abbrev exact : ProcessModel Hist _root_.Unit Hist where
  Valid _ := True
  Report h _ := h

instance : DecidablePred exact.Valid := fun _ => isTrue True.intro

/-- The inquiry of the record that reports `left`: its compatible completions. -/
def leftOnly : Inquiry (Hist × _root_.Unit) :=
  Inquiry.ofRecord (Compatible exact admitted.assumptions .left)

theorem leftOnly_completions : leftOnly.completions = {(.left, ())} := by decide +kernel

/-- The claim is true in every completion of `leftOnly`, so it is stable, but no
witness concludes it, so it is not entitled on the record of `left`. -/
theorem stable_not_entitled :
    leftOnly.Stable (fun x => model.truth x.1 unargued) ∧
      ¬ Entitled model strict exact admitted .left unargued := by
  refine ⟨by decide +kernel, by decide +kernel⟩

/-- The claim's status, with both witnesses' arguments as support. -/
def claimStatus (h : Hist) : Status := statusC (af h) ⟨[1, 2], []⟩

/-- Equal status, different entitlement of the submitted argument. -/
theorem status_does_not_transport :
    claimStatus .left = .justified ∧ claimStatus .right = .justified ∧
      ArgumentEntitled model strict exact admitted .left claimC .w1 ∧
      ¬ ArgumentEntitled model strict exact admitted .right claimC .w1 := by
  refine ⟨by decide, by decide, by decide +kernel, by decide +kernel⟩

end Lara.Examples.ProcessInquiry
