import Lara.Process.WorldView
import Lara.Process.Coverage

/-!
R3 fixtures for ordered process histories.

A plan version `v0` of `plan` is committed (`commit`), the evaluation dataset is
read (`read`), and run `run0` uses that plan version on that dataset (`run`).
A violating history has an additional, earlier read (`earlyRead`) before the
commit.

* `omitted_read_unknown` / `complete_access_certain`: the record states the
  commit precedes the reported read. Without access coverage an unreported
  earlier read stays possible, so precommitment is `unknown`; with complete
  coverage of evaluation reads the violating history is excluded and it is
  `certainTrue`.
* `unordered_record_unknown`, `record_order_irrelevant`: without a precedence
  constraint both orders of commit and read are compatible; listing the
  record's events in another order changes nothing.
* `contradictory_record_inconsistent`: contradictory constraints give
  `inconsistent`.
* `failed_sibling_counts`: a failed sibling run yields no argument, so no
  support and no attack, but it is still in the family count.
* `run_uses_current_version`, `cutoff_excludes_longer`, `refusing_evaluator`:
  runs use current dataset versions, completions stop at the cutoff, and a
  refusing evaluator stays conservative.
* `history_forgets_precommitment`: two valid histories with the same event
  multiset differ on `RunPrecommitted`.
* `split_selection_fixture`: selecting on one dataset and testing on another is
  structural split selection; selecting on the test data is not.
-/

namespace Lara.Examples.ProcessOrder

open Lara.Process

def actor : ActorId := ⟨0⟩
def plan : PlanId := ⟨0⟩
def v0 : VersionId := ⟨0⟩
def testData : DataId := ⟨1⟩
def selectData : DataId := ⟨2⟩
def run0 : RunId := ⟨0⟩
def family : FamilyId := ⟨0⟩

def commit : Stamped := ⟨⟨0⟩, .commitPlan actor plan v0⟩
def read : Stamped := ⟨⟨1⟩, .access actor testData .evaluation⟩
def run : Stamped := ⟨⟨2⟩, .run run0 plan v0 [(testData, v0)] family⟩
def earlyRead : Stamped := ⟨⟨3⟩, .access actor testData .evaluation⟩

/-- The candidate complete histories of the fixture. -/
inductive Candidate where
  | committedFirst
  | readFirst
  | earlierRead
  deriving DecidableEq, Repr, Fintype

def Candidate.trace : Candidate → ProcessHistory
  | .committedFirst => [commit, read, run]
  | .readFirst => [read, commit, run]
  | .earlierRead => [earlyRead, commit, read, run]

def precommitted (x : Candidate) : Prop := RunPrecommitted x.trace run0

instance : DecidablePred precommitted := fun _ => inferInstanceAs (Decidable (RunPrecommitted _ _))

/-- The record: commit, read and run were reported, and the commit precedes the
reported read. -/
def ordered : OrderRecord := ⟨[commit, read, run], [(commit.id, read.id)], 10⟩

/-- Coverage of every evaluation read before the cutoff. -/
def accessScope : CoverageScope := ⟨[.dataAccess], none, none, none, 10⟩

def noPolicy : Empty → ProcessHistory → List Stamped → Prop := fun e => e.elim

instance (p : Empty) (h : ProcessHistory) (r : List Stamped) : Decidable (noPolicy p h r) :=
  p.elim

def openCompat (x : Candidate) : Prop := OrderCompatible ordered x.trace

def coveredCompat (x : Candidate) : Prop :=
  OrderCompatible ordered x.trace ∧
    (RecordCoverage.complete accessScope).Allowed noPolicy x.trace ordered.events

instance : DecidablePred openCompat := fun _ => inferInstanceAs (Decidable (OrderCompatible _ _))
instance : DecidablePred coveredCompat := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The stated order alone leaves an unreported earlier read possible. -/
theorem omitted_read_unknown : verdict openCompat precommitted = .unknown := by decide

/-- Complete coverage of evaluation reads excludes the violating history. -/
theorem complete_access_certain : verdict coveredCompat precommitted = .certainTrue := by
  decide

/-- Without a precedence constraint, both orders are compatible. -/
def unordered : OrderRecord := ⟨[commit, read, run], [], 10⟩
def unorderedShuffled : OrderRecord := ⟨[run, read, commit], [], 10⟩

def unorderedCompat (r : OrderRecord) (x : Candidate) : Prop := OrderCompatible r x.trace

instance (r : OrderRecord) : DecidablePred (unorderedCompat r) :=
  fun _ => inferInstanceAs (Decidable (OrderCompatible _ _))

theorem unordered_record_unknown :
    verdict (unorderedCompat unordered) precommitted = .unknown := by decide

/-- The order in which the record lists its events is not temporal evidence. -/
theorem record_order_irrelevant (x : Candidate) :
    unorderedCompat unordered x ↔ unorderedCompat unorderedShuffled x := by
  exact orderCompatible_perm (r := unordered) (r' := unorderedShuffled) (by decide) rfl rfl x.trace

/-- Contradictory precedence constraints. -/
def contradictory : OrderRecord :=
  ⟨[commit, read], [(commit.id, read.id), (read.id, commit.id)], 10⟩

theorem contradictory_record_inconsistent :
    verdictOf (fun x : Candidate => OrderCompatible contradictory x.trace) precommitted =
      .inconsistent :=
  contradictory_constraints_inconsistent (a := commit.id) (b := read.id) (by decide) (by decide)
    _ _

/-! ### A failed sibling trial -/

def siblingRun : Stamped := ⟨⟨4⟩, .run ⟨1⟩ plan v0 [(testData, v0)] family⟩
def success : Stamped := ⟨⟨5⟩, .result run0 1⟩
def failure : Stamped := ⟨⟨6⟩, .result ⟨1⟩ 0⟩

def withSibling : ProcessHistory := [commit, read, run, siblingRun, success, failure]
def withoutSibling : ProcessHistory := [commit, read, run, success]

/-- The failed sibling yields no argument (only successful runs are lowered, so
it can neither support nor attack) but raises the family count from one to two;
both histories are valid. -/
theorem failed_sibling_counts :
    ValidHistory withSibling ∧ ValidHistory withoutSibling ∧
      successfulRuns withSibling = successfulRuns withoutSibling ∧
      familyCount withSibling family = 2 ∧ familyCount withoutSibling family = 1 := by
  decide

/-! ### Versions, cutoff and conservative evaluation -/

def update : Stamped := ⟨⟨8⟩, .updateData testData ⟨1⟩⟩

/-- A run must use the current version of each input: after the dataset is
updated to version `1`, a run claiming version `0` is not a valid history. -/
theorem run_uses_current_version :
    ValidHistory [commit, read, run] ∧ ¬ ValidHistory [commit, update, read, run] := by
  decide

/-- The submission cutoff bounds completions: the earlier-read history has four
events, so a record with cutoff three excludes it. -/
theorem cutoff_excludes_longer :
    ¬ OrderCompatible { ordered with cutoff := 3 } Candidate.earlierRead.trace ∧
      OrderCompatible { ordered with cutoff := 3 } Candidate.committedFirst.trace := by
  decide

/-- A refusing evaluator is conservative: on the omitted-read record it says
`unknown`, and on the contradictory record it still says `inconsistent`. -/
theorem refusing_evaluator :
    refuse (verdict openCompat precommitted) = .unknown ∧
      refuse (verdict (fun x : Candidate => OrderCompatible contradictory x.trace) precommitted) =
        .inconsistent ∧
      ConservativeFor (refuse (verdict openCompat precommitted)) (verdict openCompat precommitted) :=
  ⟨by decide, by decide, refuse_conservative _⟩

/-! ### Order separation and split selection -/

/-- Two valid histories with one event multiset disagree on precommitment. -/
theorem history_forgets_precommitment :
    ValidHistory Candidate.committedFirst.trace ∧ ValidHistory Candidate.readFirst.trace ∧
      (Candidate.committedFirst.trace : Multiset Stamped) = Candidate.readFirst.trace ∧
      RunPrecommitted Candidate.committedFirst.trace run0 ∧
      ¬ RunPrecommitted Candidate.readFirst.trace run0 := by
  refine ⟨by decide, by decide, Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ _), by decide,
    by decide⟩

def selectRead : Stamped := ⟨⟨7⟩, .access actor selectData .selection⟩
def selectOnTest : Stamped := ⟨⟨7⟩, .access actor testData .selection⟩

theorem split_selection_fixture :
    SplitSelection [selectRead, commit, read, run] [selectData] [testData] ∧
      ¬ SplitSelection [selectOnTest, commit, read, run] [selectData] [testData] ∧
      ¬ SplitSelection [selectOnTest, commit, read, run] [testData] [testData] := by
  decide

/-- The annotation contract is inhabited: a world that has just started has no
steps, no tests and an empty, valid process history. -/
def startAnnotated : AnnotatedWorld Bool _root_.Unit :=
  ⟨Lara.BHL.World.start (fun _ _ _ => none) (fun _ => false), [], rfl, by simp, by decide⟩

theorem startAnnotated_process : startAnnotated.process = [] := rfl

end Lara.Examples.ProcessOrder
