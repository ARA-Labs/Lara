import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Lex

/-! Canonical representations and colex ordering of subsets of a declared universe. -/
namespace Lara.Process.CanonicalSubsets

variable {α : Type} [DecidableEq α]

/-- Normalize membership in the universe's declaration order. -/
def normalize (u changed : List α) : List α :=
  u.filter fun s => decide (s ∈ changed)

@[simp] theorem mem_normalize {u c : List α} {s : α} :
    s ∈ normalize u c ↔ s ∈ u ∧ s ∈ c := by simp [normalize]

theorem normalize_sublist (u c : List α) : (normalize u c).Sublist u :=
  List.filter_sublist

/-- A sublist of a duplicate-free universe is recovered from its membership. -/
theorem normalize_eq {u s : List α} (hu : u.Nodup) (hs : s.Sublist u) :
    normalize u s = s := by
  induction hs with
  | slnil => rfl
  | @cons l₁ l₂ a hs ih =>
      have ha : a ∉ l₁ := fun h => (List.nodup_cons.mp hu).1 (hs.subset h)
      simpa [normalize, ha] using ih hu.of_cons
  | @cons_cons l₁ l₂ a hs ih =>
      have ha : a ∉ l₂ := (List.nodup_cons.mp hu).1
      simp only [normalize, List.filter_cons, List.mem_cons, true_or, decide_true,
        ↓reduceIte]
      congr 1
      rw [← ih hu.of_cons]
      apply List.filter_congr
      intro b hb
      have hba : b ≠ a := fun h => ha (h ▸ hb)
      simp [hba, hb, normalize]

theorem sublist_of_subset {u s t : List α} (hu : u.Nodup)
    (hs : s.Sublist u) (ht : t.Sublist u) (h : s ⊆ t) : s.Sublist t := by
  rw [← normalize_eq hu hs, ← normalize_eq hu ht]
  have he : normalize u s = normalize (normalize u t) s := by
    unfold normalize
    rw [List.filter_filter]
    apply List.filter_congr
    intro a _
    by_cases ha : a ∈ s
    · simp [ha, h ha]
    · simp [ha]
  rw [he]
  exact normalize_sublist _ _

/-- Reversed declaration positions give the lexicographic key of `List.sublists`. -/
def key (u s : List α) : List Nat := (s.map u.idxOf).reverse

private theorem map_idx_injective {u s t : List α} (hs : s ⊆ u) (ht : t ⊆ u)
    (h : s.map u.idxOf = t.map u.idxOf) : s = t := by
  induction s generalizing t with
  | nil => simpa using h
  | cons a s ih =>
      cases t with
      | nil => simp at h
      | cons b t =>
          obtain ⟨hab, hst⟩ := List.cons.inj h
          have ab : a = b := (List.idxOf_inj (hs (by simp))).mp hab
          subst b
          congr 1
          exact ih (fun _ hm => hs (by simp [hm]))
            (fun _ hm => ht (by simp [hm])) hst

theorem key_injective {u s t : List α} (hs : s.Sublist u) (ht : t.Sublist u)
    (h : key u s = key u t) : s = t :=
  map_idx_injective hs.subset ht.subset (List.reverse_injective h)

private theorem idx_pairwise {u : List α} (hu : u.Nodup) :
    u.Pairwise (fun a b => u.idxOf a < u.idxOf b) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simpa only [hu.idxOf_getElem] using hij

private theorem lex_map_idx {u : List α} {s t : List α}
    (h : List.Lex (fun a b => u.idxOf a < u.idxOf b) s t) :
    List.Lex (· < ·) (s.map u.idxOf) (t.map u.idxOf) := by
  induction h with
  | nil => exact .nil
  | rel h => exact .rel h
  | cons _ ih => exact .cons ih

theorem sublists_key_pairwise {u : List α} (hu : u.Nodup) :
    u.sublists.Pairwise (fun s t => key u s ≤ key u t) := by
  apply (List.pairwise_sublists (idx_pairwise hu)).imp
  intro s t h
  have h' := lex_map_idx h
  simp only [List.map_reverse] at h'
  exact le_of_lt h'

/-- Sort only retained candidates, never enumerate the universe's powerset. -/
def sort (u : List α) (candidates : List (List α)) : List (List α) :=
  candidates.mergeSort (fun s t => decide (key u s ≤ key u t))

/-- Sorting already ordered canonical subsets preserves their exact list. -/
theorem sort_eq_self {u : List α} {candidates : List (List α)}
    (hc : ∀ s ∈ candidates, s.Sublist u)
    (hs : candidates.Pairwise (fun s t => key u s ≤ key u t)) :
    sort u candidates = candidates := by
  have hp := List.mergeSort_perm candidates (fun s t => decide (key u s ≤ key u t))
  apply hp.eq_of_pairwise
  · intro s t hs ht hst hts
    exact key_injective (hc s (hp.mem_iff.mp hs)) (hc t ht) (le_antisymm hst hts)
  · have sorted := List.pairwise_mergeSort
      (le := fun s t => decide (key u s ≤ key u t))
      (fun _ _ _ h₁ h₂ => by simpa using le_trans (of_decide_eq_true h₁) (of_decide_eq_true h₂))
      (fun a b => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total (key u a) (key u b))
      candidates
    simpa only [decide_eq_true_eq] using sorted
  · exact hs

theorem sort_eq_filter {u : List α} (hu : u.Nodup) (p : List α → Bool)
    (candidates : List (List α)) (hn : candidates.Nodup)
    (hm : ∀ s, s ∈ candidates ↔ s ∈ u.sublists.filter p) :
    sort u candidates = u.sublists.filter p := by
  have hp : (sort u candidates).Perm (u.sublists.filter p) :=
    (List.mergeSort_perm candidates _).trans
      ((List.perm_ext_iff_of_nodup hn (hu.sublists.filter p)).mpr hm)
  apply hp.eq_of_pairwise
  · intro s t hs ht hst hts
    apply key_injective
      (List.mem_sublists.mp (List.mem_filter.mp (hp.mem_iff.mp hs)).1)
      (List.mem_sublists.mp (List.mem_filter.mp ht).1)
    exact le_antisymm hst hts
  · have sorted := List.pairwise_mergeSort
      (le := fun s t => decide (key u s ≤ key u t))
      (fun _ _ _ h₁ h₂ => by simpa using le_trans (of_decide_eq_true h₁) (of_decide_eq_true h₂))
      (fun a b => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total (key u a) (key u b))
      candidates
    simpa only [sort, decide_eq_true_eq] using sorted
  · exact (sublists_key_pairwise hu).filter p

end Lara.Process.CanonicalSubsets
