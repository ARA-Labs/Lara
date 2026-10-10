import Lara.Process.Kleene
import Lara.Process.Conservative
import Lara.Examples.BHLPartialRecord

/-!
Witnesses for the compatible-history core.

* `refine_needs_nonempty`: refining to an empty compatible set yields
  `inconsistent`, not the old certainty.
* `kleene_incomplete`: the compositional evaluator answers `unknown` on
  `p ∨ ¬p` while supervaluation answers `certainTrue`.
* `coverage_incomparable`: complete and count-bounded coverage of one scope
  allow incomparable sets of histories, so coverage constructors are not a
  strength order.
* `partialRecord_unknown`: the existing BHL partial-record witness, restated as
  a verdict of the process model built from it (`partial_compatible` shows
  both histories are compatible). The local `Fintype Completion` instance
  enumerates that example's two completions; `BHLPartialRecord` itself stays
  unchanged so its recorded theorem inventory lines stay exact.
* `partialRecord_not_factors`: the same witness read through naive evaluation:
  the method conclusion does not factor through the submitted record.
-/

namespace Lara.Examples.ProcessCore

open Lara.Process

/-! ### Refinement needs a nonempty refined set -/

/-- Every Boolean is compatible with the coarse record and none with the refined
one. -/
theorem refine_needs_nonempty :
    verdict (fun _ : Bool => True) (fun _ => True) = .certainTrue ∧
      verdict (fun _ : Bool => False) (fun _ => True) = .inconsistent := by
  decide

/-! ### The Kleene evaluator is incomplete -/

/-- One atom, `p`, true exactly at `true`. -/
def pVal : _root_.Unit → Bool → Prop := fun _ x => x = true

instance (a : _root_.Unit) : DecidablePred (pVal a) := fun x => inferInstanceAs (Decidable (x = true))

def excludedMiddle : Formula _root_.Unit := .disj (.atom ()) (.neg (.atom ()))

/-- Both Booleans are compatible, so `p` is undetermined and the compositional
evaluator gives up on `p ∨ ¬p`, which supervaluation certifies. -/
theorem kleene_incomplete :
    kleeneVerdictFinite (fun _ : Bool => True) (finiteAtoms (fun _ => True) pVal)
        excludedMiddle = .unknown ∧
      verdict (fun _ : Bool => True) (excludedMiddle.holds pVal) = .certainTrue := by
  decide

/-! ### Coverage constructors are not a strength order -/

def familyF : FamilyId := ⟨0⟩
def runOne : Stamped := ⟨⟨0⟩, .run ⟨0⟩ ⟨0⟩ ⟨0⟩ [] familyF⟩
def runTwo : Stamped := ⟨⟨1⟩, .run ⟨1⟩ ⟨0⟩ ⟨0⟩ [] familyF⟩

/-- Two candidate histories: both runs reported, or one run left unreported. -/
inductive Candidate where
  | bothReported
  | oneOmitted
  deriving DecidableEq, Repr, Fintype

def Candidate.trace : Candidate → ProcessHistory
  | .bothReported => [runOne, runTwo]
  | .oneOmitted => [runOne]

def Candidate.exposed : Candidate → _root_.Unit → List Stamped
  | .bothReported, _ => [runOne, runTwo]
  | .oneOmitted, _ => []

def runScope : CoverageScope :=
  ⟨[.analysisRun], some familyF, none, none, 10⟩

def noPolicy : Empty → ProcessHistory → List Stamped → Prop := fun e => e.elim

instance (p : Empty) (h : ProcessHistory) (r : List Stamped) : Decidable (noPolicy p h r) :=
  p.elim

abbrev completeRuns : Assumptions Candidate _root_.Unit :=
  (RecordCoverage.complete runScope).assumptions noPolicy Candidate.trace Candidate.exposed

abbrev atMostOneRun : Assumptions Candidate _root_.Unit :=
  (RecordCoverage.countBounded runScope 1).assumptions noPolicy Candidate.trace
    Candidate.exposed

/-- Complete reporting allows the two-run history and forbids the omission;
a count bound of one does the opposite. Neither assumption is stronger. -/
theorem coverage_incomparable :
    ¬ completeRuns.Stronger atMostOneRun ∧ ¬ atMostOneRun.Stronger completeRuns := by
  constructor
  · intro stronger
    have allowed : completeRuns.Allowed .bothReported () := by decide
    exact absurd (stronger _ _ allowed) (by decide)
  · intro stronger
    have allowed : atMostOneRun.Allowed .oneOmitted () := by decide
    exact absurd (stronger _ _ allowed) (by decide)

/-- A model in which every candidate reports the same uninformative record. -/
def silentModel : ProcessModel Candidate _root_.Unit _root_.Unit where
  Valid _ := True
  Report _ _ := ()

instance : DecidablePred silentModel.Valid := fun _ => isTrue True.intro

/-- Assumptions under which no candidate is allowed: complete reporting and a
count bound of one together. -/
abbrev bothCoverages : Assumptions Candidate _root_.Unit := completeRuns.and atMostOneRun

/-- Strengthening admitted assumptions can empty the compatible set: a certain
verdict then becomes `inconsistent`, never a stronger certainty. -/
theorem weaken_assumption_needs_nonempty :
    bothCoverages.Stronger Assumptions.trivial ∧
      verdict (Compatible silentModel Assumptions.trivial ()) (fun _ => True) = .certainTrue ∧
      verdict (Compatible silentModel bothCoverages ()) (fun _ => True) = .inconsistent :=
  ⟨fun _ _ _ => True.intro, by decide, by decide⟩

/-! ### The BHL partial record as a verdict -/

section PartialRecord

open Lara.BHL
open Lara.Examples.BHLPartialRecord

instance : Fintype Completion :=
  ⟨{.reportedOnly, .unreportedEarlier}, fun c => by cases c <;> simp⟩

/-- The two complete BHL histories of `BHLPartialRecord`, reported through its
latest-test projection. The reporting choice is fixed by the projection. -/
def partialModel : ProcessModel Completion _root_.Unit (List SubmittedTest) where
  Valid c := (outcome c).status = .completed
  Report c _ := submittedRecord (outcome c)

/-- The method conclusion at a complete history. -/
def conclusionHolds (x : Completion × _root_.Unit) : Prop :=
  satisfies Lara.Examples.BHLBinaryModel.interpretation
    (Lara.Examples.BHLBinaryModel.context .two).model GhostEnv.empty (world x.1) conclusion

theorem partial_compatible (c : Completion) :
    Compatible partialModel Assumptions.trivial record (c, ()) :=
  ⟨(record_compatible c).1, trivial, (record_compatible c).2⟩

/-- `record_does_not_determine_conclusion`, restated: the submitted record's
verdict on the method conclusion is `unknown`. -/
theorem partialRecord_unknown :
    verdictOf (Compatible partialModel Assumptions.trivial record) conclusionHolds = .unknown :=
  (verdictOf_unknown_iff _ _).mpr
    ⟨(.reportedOnly, ()), (.unreportedEarlier, ()), partial_compatible _, partial_compatible _,
      reported_satisfaction, omitted_test_not_satisfaction⟩

/-- Naive evaluation is unsound here: the conclusion does not factor through the
submitted record on valid histories. -/
theorem partialRecord_not_factors :
    ¬ Factors (fun c : Completion => (outcome c).status = .completed)
      (fun c => submittedRecord (outcome c))
      (fun c => conclusionHolds (c, ())) := by
  intro factors
  exact omitted_test_not_satisfaction
    ((factors .reportedOnly .unreportedEarlier (completed_runs _) (completed_runs _)
      ((record_compatible _).2.trans (record_compatible _).2.symm)).mp reported_satisfaction)

instance : DecidablePred partialModel.Valid := fun c =>
  inferInstanceAs (Decidable ((outcome c).status = .completed))

end PartialRecord

end Lara.Examples.ProcessCore
