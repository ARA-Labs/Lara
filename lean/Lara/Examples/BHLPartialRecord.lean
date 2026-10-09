import Lara.BHL.FiniteExecution
import Lara.BHL.FiniteModel

namespace Lara.Examples.BHLPartialRecord

open Lara.BHL
open Lara.Examples.BHLBinaryModel
open Lara.Examples.BHLBinaryRuns
open Lara.Examples.BHLSoundnessScience (alternative)
open Lara.Examples.BHLFiniteBelief (RunKind bundleTest)

namespace E
export Lara.Examples.BHLExecution (Event Source report eventsWorld)
end E

/-- A reported test retains its actual target, test identity, datum and exact
numeric result. The submitted projection below does not claim complete history. -/
structure SubmittedTest where
  target : VarId
  test : TestId
  datum : Bool
  value : ℚ
  deriving DecidableEq, Repr

/-- Extract an actual reported test from an emitted command and its resulting
visible state. Silent steps and non-test commands supply no test entry. -/
def reportedTest (event : E.Event) : Option SubmittedTest :=
  match event.emission with
  | some (.test target data name) =>
      (event.state.rationals target.id).map fun value =>
        ⟨target.id, name, event.state.datasets data, value⟩
  | _ => none

/-- This submission reports only the latest test. Earlier tests can exist in the
complete modeled run without appearing in this nonempty submitted record. -/
def submittedRecord (outcome : FiniteExecution.Outcome) : List SubmittedTest :=
  match (outcome.events.filterMap reportedTest).getLast? with
  | none => []
  | some entry => [entry]

inductive Completion where
  | reportedOnly
  | unreportedEarlier
  deriving DecidableEq, Repr

def outcome : Completion → FiniteExecution.Outcome
  | .reportedOnly => FiniteExecution.Smoke.single
  | .unreportedEarlier => FiniteExecution.Smoke.hidden

def source : Completion → E.Source
  | .reportedOnly => singleSource firstId
  | .unreportedEarlier => hiddenSource

def runKind : Completion → RunKind
  | .reportedOnly => .single firstId
  | .unreportedEarlier => .hidden

/-- The shared record is an actual firstId report, not an empty observation. -/
def record : List SubmittedTest := [⟨E.report.id, firstId, true, 1 / 4⟩]

def Compatible (submitted : List SubmittedTest) (completion : Completion) : Prop :=
  (outcome completion).status = .completed ∧ submittedRecord (outcome completion) = submitted

instance (submitted : List SubmittedTest) (completion : Completion) :
    Decidable (Compatible submitted completion) := inferInstanceAs (Decidable (_ ∧ _))

def conclusion : Assertion [] := .modal
  (statisticalBelief .equal (.rational (1 / 4)) (bundleTest (.single firstId)) alternative)

def conclusionSupport : FiniteModel.Supported conclusion :=
  .modal (.belief (.single firstId) .equal (1 / 4))

def checkConclusion (completion : Completion) : Bool :=
  FiniteModel.evalFinite conclusionSupport GhostEnv.empty (runKind completion) 0 true false

theorem completed_runs (completion : Completion) : (outcome completion).status = .completed := by
  cases completion <;> rfl

theorem record_compatible (completion : Completion) : Compatible record completion := by
  cases completion <;> refine ⟨rfl, ?_⟩ <;>
    change [⟨E.report.id, firstId, true, Tests.Binary.pvalue true⟩] = record
  all_goals norm_num [record]

theorem different_full_ledgers :
    (outcome .reportedOnly).state.ledger.card = 1 ∧
      (outcome .unreportedEarlier).state.ledger.card = 2 := by
  decide

theorem reported_conclusion : checkConclusion .reportedOnly = true := by
  norm_num [checkConclusion, conclusionSupport, runKind, FiniteModel.evalFinite,
    FiniteModel.evalModal, BHLFiniteBelief.checkBelief, BHLFiniteBelief.endpointSnapshot,
    singleFinal, runTest, initialSnapshot, Lara.Examples.BHLExecution.initialSnapshot,
    BHLFiniteBelief.bundleHistory, BHLFiniteBelief.eventMass, BHLFiniteBelief.compareRational,
    Lara.Examples.BHLExecution.dataId, Lara.Examples.BHLExecution.aliasId]

theorem omitted_test_conclusion : checkConclusion .unreportedEarlier = false := by decide

noncomputable section

def world : Completion → World Bool Primitive
  | .reportedOnly => singleWorld 0 true false firstId
  | .unreportedEarlier => hiddenWorld 0 true false

/-- Both histories are real complete reference executions in the same admitted
binary model, not arbitrarily authored lists of reports. -/
theorem complete_reference_run (completion : Completion) :
    executes (context .two) (source completion).quote (sampledWorld 0 true false)
      (world completion) := by
  cases completion with
  | reportedOnly => exact single_executes .two 0 true false firstId (by decide)
  | unreportedEarlier => exact hidden_executes 0 true false (by decide)

theorem computed_endpoint (completion : Completion) :
    E.eventsWorld (sampledWorld 0 true false) (outcome completion).events = world completion := by
  cases completion <;> rfl

/-- The actual finite check is connected to independent satisfaction in each
complete history. Compatibility of the shorter submission does not replace it. -/
theorem checkConclusion_correct (completion : Completion) :
    checkConclusion completion = true ↔
      satisfies interpretation (context .two).model GhostEnv.empty (world completion) conclusion := by
  cases completion <;>
    exact FiniteModel.evalFinite_correct conclusionSupport GhostEnv.empty _ 0 true false (by decide)

theorem reported_satisfaction :
    satisfies interpretation (context .two).model GhostEnv.empty (world .reportedOnly) conclusion :=
  (checkConclusion_correct .reportedOnly).mp reported_conclusion

theorem omitted_test_not_satisfaction :
    ¬ satisfies interpretation (context .two).model GhostEnv.empty (world .unreportedEarlier) conclusion := by
  intro satisfied
  have checked := (checkConclusion_correct .unreportedEarlier).mpr satisfied
  rw [omitted_test_conclusion] at checked
  cases checked

/-- No decision from this submitted record alone can agree with the method
conclusion in every compatible complete history. This is a witness-specific
limitation, not a general claim that all partial records are useless. -/
theorem record_does_not_determine_conclusion :
    ¬ ∃ infer : List SubmittedTest → Bool, ∀ completion,
      Compatible record completion →
        (infer record = true ↔ satisfies interpretation (context .two).model
          GhostEnv.empty (world completion) conclusion) := by
  rintro ⟨infer, correct⟩
  have inferred := (correct .reportedOnly (record_compatible .reportedOnly)).mpr reported_satisfaction
  exact omitted_test_not_satisfaction
    ((correct .unreportedEarlier (record_compatible .unreportedEarlier)).mp inferred)

end
end Lara.Examples.BHLPartialRecord
