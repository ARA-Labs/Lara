import Lara.Process.Bridge
import Lara.Process.Prov
import Lara.Examples.ProcessCore
import Lara.Examples.ProcessRevision
import Lara.Examples.ProcessFalseLaws

/-!
R6 adequacy, part A4: every specified coarsening of a complete history erases a
distinction entitlement depends on.

For each coarsening `π` there are two complete histories with the same
projection that disagree on a warrant, and the shared coarse record gets the one
verdict `unknown` (`separation_unknown`), never two contradictory
entitlements.

| Coarsening | Theorem |
| --- | --- |
| latest-test projection | `latestTest_separates` |
| event multiset (`History` shape) | `multiset_separates` |
| dropping failed or unreported analyses | `dropFailed_separates` |
| dropping selection-read provenance | `selectionProvenance_separates` |
| collapsing source identities | `collapse_separates` |
| dropping retractions | `dropRetractions_separates` |
| the PROV graph | `prov_separates` |
-/

namespace Lara.Examples.ProcessAdequacy

open Lara.Process

/-! ### Latest-test projection -/

section LatestTest
open Lara.BHL
open Lara.Examples.BHLPartialRecord
open Lara.Examples.ProcessCore

theorem latestTest_separates :
    Separates (fun c : Completion => submittedRecord (outcome c)) (fun c => conclusionHolds (c, ())) :=
  ⟨.reportedOnly, .unreportedEarlier,
    (record_compatible _).2.trans (record_compatible _).2.symm,
    reported_satisfaction, omitted_test_not_satisfaction⟩

end LatestTest

/-! ### Event multiset -/

section Order
open Lara.Examples.ProcessOrder

theorem multiset_separates :
    Separates (fun x : Candidate => (x.trace : Multiset Stamped))
      (fun x => RunPrecommitted x.trace run0) :=
  ⟨.committedFirst, .readFirst, Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ _),
    by decide, by decide⟩

/-! ### Dropping failed or unreported analyses -/

/-- Drop every run without a successful result, and every failed result. -/
def dropFailed (h : ProcessHistory) : ProcessHistory :=
  h.filter fun e => match e.event with
    | .run r .. => decide (r ∈ successfulRuns h)
    | .result _ outcome => decide (0 < outcome)
    | _ => true

theorem dropFailed_separates :
    Separates (fun h : ProcessHistory => dropFailed h)
      (fun h => Lara.Examples.ProcessRevision.bonferroniWarrant h) :=
  ⟨withoutSibling, withSibling, by decide,
    Lara.Examples.ProcessRevision.failed_sibling_changes_warrant.2.1,
    Lara.Examples.ProcessRevision.failed_sibling_changes_warrant.2.2⟩

/-! ### Dropping selection-read provenance -/

/-- Forget which dataset a selection read touched. -/
def dropSelectionProvenance (h : ProcessHistory) : ProcessHistory :=
  h.map fun e => match e.event with
    | .access actor _ .selection => ⟨e.id, .access actor ⟨0⟩ .selection⟩
    | _ => e

theorem selectionProvenance_separates :
    Separates dropSelectionProvenance (fun h => SplitSelection h [selectData] [testData]) :=
  ⟨[selectRead, commit, read, run], [selectOnTest, commit, read, run], by decide, by decide,
    by decide⟩

end Order

/-! ### Collapsing source identities -/

section Sources
open Lara.Examples.ProcessRevision

/-- Corroboration by two distinct sources. -/
def corroborated (avail : Finset (Nat × ProcessRevision.Atom)) : Prop :=
  2 ≤ corroboration avail ProcessRevision.Atom.a

instance (avail : Finset (Nat × ProcessRevision.Atom)) : Decidable (corroborated avail) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem collapse_separates :
    Separates (renameSupplies (fun _ : Nat => (0 : Nat))) corroborated :=
  ⟨twoSources, {(1, ProcessRevision.Atom.a)}, by decide, by decide, by decide⟩

end Sources

/-! ### Dropping retractions -/

section Retractions
open Lara.Examples.ProcessFalseLaws

def dropRetractions (h : ProcessHistory) : ProcessHistory :=
  h.filter fun e => e.event.kind != .sourceRetracted

theorem dropRetractions_separates : Separates dropRetractions warranted :=
  ⟨asserted, retracted, by decide, by decide, by decide⟩

end Retractions

/-! ### The PROV graph -/

section Prov
open Lara.Examples.ProcessOrder

/-- The committed-first and read-first histories have equivalent PROV graphs but
disagree on precommitment, so the record "this PROV graph" leaves it
`unknown`. -/
theorem prov_separates :
    (provGraph Candidate.committedFirst.trace).Equiv (provGraph Candidate.readFirst.trace) ∧
      RunPrecommitted Candidate.committedFirst.trace run0 ∧
      ¬ RunPrecommitted Candidate.readFirst.trace run0 ∧
      verdictOf (fun x : Candidate =>
          (provGraph x.trace).Equiv (provGraph Candidate.committedFirst.trace))
        (fun x => RunPrecommitted x.trace run0) = .unknown := by
  have equiv := provGraph_perm (h := Candidate.committedFirst.trace)
    (h' := Candidate.readFirst.trace) (List.Perm.swap _ _ _)
  refine ⟨equiv, by decide, by decide, (verdictOf_unknown_iff _ _).mpr
    ⟨.committedFirst, .readFirst, ?_, ?_, by decide, by decide⟩⟩
  · exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  · obtain ⟨a, b, c, d, e⟩ := equiv
    exact ⟨fun x => (a x).symm, fun x => (b x).symm, fun x => (c x).symm, fun x => (d x).symm,
      fun x => (e x).symm⟩

end Prov

/-- The multiset pair's shared coarse record has the verdict `unknown`. -/
theorem multiset_record_unknown :
    verdictOf (fun x : Lara.Examples.ProcessOrder.Candidate =>
        (x.trace : Multiset Stamped) = (Lara.Examples.ProcessOrder.Candidate.committedFirst.trace : Multiset Stamped))
      (fun x => RunPrecommitted x.trace Lara.Examples.ProcessOrder.run0) = .unknown :=
  separation_unknown (π := fun x : Lara.Examples.ProcessOrder.Candidate => (x.trace : Multiset Stamped))
    (h₂ := .readFirst) (Multiset.coe_eq_coe.mpr (List.Perm.swap _ _ _)) (by decide) (by decide)

end Lara.Examples.ProcessAdequacy
