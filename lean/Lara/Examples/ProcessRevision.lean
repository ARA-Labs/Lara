import Lara.Process.Revision
import Lara.Examples.ProcessOrder

/-!
Fixtures for revision and transport.

* `quarantine_one_support` / `quarantine_all_supports`: with two independent
  supports, quarantining one source keeps the claim and quarantining both loses
  it, as `quarantine_iff_support` predicts.
* `support_avoids_but_defeated`: with attacks, a support that avoids the
  quarantine is not enough; an undefeated attacker still defeats the claim.
* `stable_not_directional`: adding a self-attacking argument that attacks
  nothing in the claim's ancestry removes every stable extension, while the
  grounded label is unchanged.
* `failed_sibling_changes_warrant`: a failed sibling run adds no argument and
  no attack edge, yet raises the family count and flips the e-Bonferroni
  warrant; entitlement reads process inputs beyond the argument graph.
* `merge_breaks_corroboration`: merging two sources keeps derivability but
  halves the corroboration count.
* `incomplete_reads_unsound`: reuse with an incompletely recorded read set
  returns a stale result.
* `update_and_revision`: a new dataset version keeps the old-version warrant;
  declaring the old version defective withdraws it.
-/

namespace Lara.Examples.ProcessRevision

open Lara.Grounded
open Lara.Process

/-! ### Quarantine on the support-only fragment -/

inductive Atom where
  | a
  | b
  | claim
  deriving DecidableEq, Repr

/-- Two independent rules derive the claim, one from `a`, one from `b`. -/
def system : SupportSystem Nat Atom := ⟨[([.a], .claim), ([.b], .claim)]⟩

/-- Source `1` supplies `a`, source `2` supplies `b`. -/
def supplies : Finset (Nat × Atom) := {(1, .a), (2, .b)}

theorem quarantine_one_support :
    Derives system (supplies.filter fun p => p.1 ∉ ({1} : Finset Nat)) .claim := by
  refine .rule (r := ([Atom.b], Atom.claim)) (by decide) fun p hp => ?_
  simp only [List.mem_singleton] at hp
  subst hp
  exact .source (s := 2) (by decide)

theorem quarantine_all_supports :
    ¬ Derives system (supplies.filter fun p => p.1 ∉ ({1, 2} : Finset Nat)) .claim := by
  have empty : (supplies.filter fun p => p.1 ∉ ({1, 2} : Finset Nat)) = ∅ := by decide
  rw [empty]
  exact not_derives_empty (by simp [system])

/-! ### Attacks make the support criterion only necessary -/

/-- The claim's argument `0` and its attacker `1` both rest on unquarantined
sources. -/
def attacked : AF := ⟨[0, 1], fun x y => x == 1 && y == 0⟩

theorem support_avoids_but_defeated : labelC attacked 0 = .out := by decide

/-! ### Directionality is a grounded property -/

def single : AF := ⟨[0], fun _ _ => false⟩

/-- `5` attacks only itself, outside the ancestry of `0`. -/
def withSelfAttack : AF := ⟨[0, 5], fun x y => x == 5 && y == 5⟩

theorem stable_not_directional :
    StableCredulous single 0 ∧ ¬ StableCredulous withSelfAttack 0 ∧
      labelC single 0 = .inn ∧ labelC withSelfAttack 0 = .inn := by
  decide

/-- The same edit through the general theorem: the ancestry of `0` is just `0`,
and it has no attackers in either framework. -/
theorem grounded_locality_instance : labelC single 0 = labelC withSelfAttack 0 := by
  have only : ∀ y, Ancestor single 0 y → y = 0 := by
    intro y hy
    induction hy with
    | self => rfl
    | attacker _ _ hxy => simp [single] at hxy
  refine grounded_directional_locality (by decide) (fun y hy => ?_) (fun y hy x => ?_)
  · rw [only y hy]; decide
  · rw [only y hy]
    constructor
    · rintro ⟨_, h⟩; simp [single] at h
    · rintro ⟨_, h⟩; simp [withSelfAttack] at h

/-! ### A failed sibling changes the statistical family -/

section Sibling
open Lara.Examples.ProcessOrder

/-- e-Bonferroni at the family's actual size, for a reported e-value of `30` at
`α = 1/20`. -/
def bonferroniWarrant (h : ProcessHistory) : Prop :=
  (familyCount h family : ℚ) / (1 / 20) ≤ 30

instance (h : ProcessHistory) : Decidable (bonferroniWarrant h) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The failed sibling leaves the lowered arguments, and so every attack edge,
unchanged, but the warrant holds without it (`20 ≤ 30`) and fails with it
(`40 > 30`). -/
theorem failed_sibling_changes_warrant :
    successfulRuns withSibling = successfulRuns withoutSibling ∧
      bonferroniWarrant withoutSibling ∧ ¬ bonferroniWarrant withSibling := by
  refine ⟨by decide, ?_, ?_⟩ <;> norm_num [bonferroniWarrant, failed_sibling_counts.2.2.2.1,
    failed_sibling_counts.2.2.2.2]

end Sibling

/-! ### Renaming -/

/-- Two sources both supply `a`. -/
def twoSources : Finset (Nat × Atom) := {(1, .a), (2, .a)}

/-- Merging both sources into one keeps `a` derivable but halves its
corroboration: injectivity matters exactly where a profile counts sources. -/
theorem merge_breaks_corroboration :
    corroboration twoSources .a = 2 ∧
      corroboration (renameSupplies (fun _ : Nat => (0 : Nat)) twoSources) .a = 1 ∧
      (Derives (system.rename (Src' := Nat)) (renameSupplies (fun _ : Nat => (0 : Nat)) twoSources)
        .a ↔ Derives system twoSources .a) :=
  ⟨by decide, by decide, warranted_natural system _ twoSources .a⟩

/-! ### Verifying traces -/

/-- A check that reads keys `0` and `1`. -/
def check (env : Nat → Bool) : Bool := env 0 && env 1

/-- Recording only key `0` is incomplete: the recorded read is unchanged, yet
the recomputed result differs from the stored one. -/
theorem incomplete_reads_unsound :
    ¬ RecordsReads check {0} ∧
      (∀ k ∈ ({0} : Finset Nat), (fun _ => true : Nat → Bool) k = (fun k => k == 0) k) ∧
      check (fun k => k == 0) ≠ check (fun _ => true) := by
  refine ⟨fun h => ?_, by decide, by decide⟩
  have := h (fun _ => true) (fun k => k == 0) (by decide)
  exact absurd this (by decide)

/-- Recording both keys is complete. -/
theorem complete_reads : RecordsReads check {0, 1} := by
  intro e₁ e₂ same
  simp only [check, same 0 (by simp), same 1 (by simp)]

/-! ### Update versus revision -/

def dataD : DataId := ⟨1⟩
def oldV : DataId × VersionId := (dataD, ⟨0⟩)
def newV : DataId × VersionId := (dataD, ⟨1⟩)

theorem update_and_revision :
    VersionWarranted [oldV] [oldV] [] ∧ VersionWarranted [newV, oldV] [oldV] [] ∧
      ¬ VersionWarranted [newV, oldV] [oldV] [oldV] ∧ VersionWarranted [newV, oldV] [newV] [oldV] :=
  by decide

end Lara.Examples.ProcessRevision
