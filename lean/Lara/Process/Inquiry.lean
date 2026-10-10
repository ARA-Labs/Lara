import Lara.Process.Verdict

/-!
The inquiry interface issue #22 builds on.

A finite inquiry is a finite family of compatible completions; `Inquiry.ofRecord`
builds it from a record's compatibility predicate over a declared finite
carrier. A claim is
*stable* over the inquiry when the family is nonempty and no two completions
disagree on it, which is `determined_iff_no_witness` over the family
(`stable_iff_determinate`). The *sensitivity* of a claim relative to a reference
completion is the set of completions that flip it; it is empty exactly when the
claim is stable (`sensitivity_empty_iff_stable`).

Stability is not scientific adequacy: a claim can be stably unwarranted, and a
stable verdict says nothing about entitlement
(`Lara.Examples.ProcessInquiry.stable_not_entitled`). Unchanged status does not
transport entitlement either (`Lara.Examples.ProcessInquiry.status_does_not_transport`).
This module does not implement the inquiry procedures of #22.
-/

namespace Lara.Process

universe u

variable {X : Type u}

/-- A finite inquiry: the completions it considers. -/
structure Inquiry (X : Type u) where
  completions : Finset X

namespace Inquiry

/-- A claim is stable over an inquiry when the inquiry is nonempty and no two of
its completions disagree on the claim. -/
def Stable (I : Inquiry X) (φ : X → Prop) : Prop :=
  I.completions.Nonempty ∧ ∀ x ∈ I.completions, ∀ y ∈ I.completions, (φ x ↔ φ y)

instance (I : Inquiry X) (φ : X → Prop) [DecidablePred φ] : Decidable (I.Stable φ) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Stability is determinacy of the verdict over the inquiry's completions. -/
theorem stable_iff_determinate (I : Inquiry X) (φ : X → Prop) :
    I.Stable φ ↔ Determinate (verdictOf (· ∈ I.completions) φ) := by
  rw [determined_iff_no_witness]
  exact ⟨fun ⟨ne, agree⟩ => ⟨ne, fun x y hx hy => agree x hx y hy⟩,
    fun ⟨ne, agree⟩ => ⟨ne, fun x hx y hy => agree x y hx hy⟩⟩

/-- The completions that flip the claim relative to a reference completion. -/
def sensitivity (I : Inquiry X) (φ : X → Prop) [DecidablePred φ] (reference : X) : Finset X :=
  I.completions.filter fun x => ¬ (φ x ↔ φ reference)

/-- With the reference among the completions, no completion flips the claim
exactly when the claim is stable. -/
theorem sensitivity_empty_iff_stable (I : Inquiry X) (φ : X → Prop) [DecidablePred φ]
    {reference : X} (mem : reference ∈ I.completions) :
    I.sensitivity φ reference = ∅ ↔ I.Stable φ := by
  unfold sensitivity Stable
  rw [Finset.filter_eq_empty_iff]
  constructor
  · intro none
    refine ⟨⟨reference, mem⟩, fun x hx y hy => ?_⟩
    have hx' := not_not.mp (none hx)
    have hy' := not_not.mp (none hy)
    exact hx'.trans hy'.symm
  · rintro ⟨_, agree⟩ x hx
    exact not_not.mpr (agree x hx reference mem)

/-- Every member of the sensitivity set disagrees with the reference. -/
theorem mem_sensitivity (I : Inquiry X) (φ : X → Prop) [DecidablePred φ] {reference x : X} :
    x ∈ I.sensitivity φ reference ↔ x ∈ I.completions ∧ ¬ (φ x ↔ φ reference) := by
  unfold sensitivity
  exact Finset.mem_filter

/-- The inquiry of a record over a declared finite carrier: its compatible
completions. -/
def ofRecord [Fintype X] (compat : X → Prop) [DecidablePred compat] : Inquiry X :=
  ⟨Finset.univ.filter compat⟩

theorem mem_ofRecord [Fintype X] (compat : X → Prop) [DecidablePred compat] (x : X) :
    x ∈ (ofRecord compat).completions ↔ compat x := by
  simp [ofRecord]

/-- Over a record's inquiry, stability is determinacy of the record's verdict. -/
theorem ofRecord_stable_iff [Fintype X] (compat : X → Prop) [DecidablePred compat]
    (φ : X → Prop) : (ofRecord compat).Stable φ ↔ Determinate (verdictOf compat φ) := by
  rw [stable_iff_determinate]
  have : (· ∈ (ofRecord compat).completions) = compat := funext fun x => propext (mem_ofRecord _ x)
  rw [this]

end Inquiry

end Lara.Process
