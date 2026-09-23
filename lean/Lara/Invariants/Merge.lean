/-
# Node-merging morphisms of argumentation frameworks

Generic vocabulary, extracted from the M4 context calculus because
nothing in it mentions fragments, contexts, or linking: **the grounded
observation is invariant under a morphism that collapses duplicate nodes.** A
map that sends every node of one framework onto a node of another, covers the
target's nodes, and preserves the edge relation preserves every grounded label
and every claim's four-state status.

The M4 use is the structural merge of two sides' argument lists
(`Lara.Context.Merge`), but the statement is about frameworks, so it lives with
the M1 carrier it is stated over. The three iteration lemmas extend
`Lara.Grounded`'s namespace: they say the grounded extension is *any*
sufficiently long iterate, which is what lets two frameworks of different sizes
be compared at one shared stage.
-/

import Lara.Invariants

namespace Lara.Grounded

/-! ### Reaching the fixed point from any sufficiently long iteration -/

/-- The iteration is ascending along any offset. -/
theorem iter_add {F : AF} : ∀ (j k : Nat) (a : Arg), a ∈ iter F k → a ∈ iter F (k + j)
  | 0, _, _, h => h
  | j + 1, k, a, h => by
      have hj := iter_add j k a h
      rw [Nat.add_succ]
      exact iter_mono (k + j) a hj

/-- Past a stable stage the iteration adds nothing. -/
theorem stable_iter_add {F : AF} {n : Nat} (h : stable F n) :
    ∀ (j : Nat) (a : Arg), a ∈ iter F (n + j) → a ∈ iter F n
  | 0, _, ha => ha
  | j + 1, a, ha => by
      have hs : stable F (n + j) := stable_add h j
      rw [Nat.add_succ] at ha
      exact stable_iter_add h j a (hs a ha)

/-- **The grounded extension is any long-enough iterate.** `grounded_stable`
puts the fixed point at `|args|`; this lets two frameworks of different sizes be
compared at one shared stage. -/
theorem mem_grounded_iff_iter {F : AF} {m : Nat} (hm : F.args.length ≤ m) (a : Arg) :
    a ∈ grounded F ↔ a ∈ iter F m := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
  constructor
  · intro h; exact iter_add j _ a h
  · intro h; exact stable_iter_add grounded_stable j a h

end Lara.Grounded

namespace Lara.Invariants

open Lara.Grounded

/-! ### Node-merging morphisms -/

/-- **A node-merging morphism.** `φ` sends arguments of `F₁` to arguments of
`F₂`, covers every argument of `F₂`, and preserves the edge relation on the
carrier. It is deliberately *not* required to be injective: collapsing
duplicates is the intended instance. -/
structure AFMerge (F₁ F₂ : AF) (φ : Arg → Arg) : Prop where
  /-- the carrier is mapped into the carrier -/
  maps : ∀ a ∈ F₁.args, φ a ∈ F₂.args
  /-- every target argument is hit — no node appears out of nowhere -/
  surj : ∀ b ∈ F₂.args, ∃ a ∈ F₁.args, φ a = b
  /-- edges correspond on the carrier -/
  edge : ∀ a ∈ F₁.args, ∀ b ∈ F₁.args, F₁.attack a b = F₂.attack (φ a) (φ b)

namespace AFMerge

variable {F₁ F₂ : AF} {φ : Arg → Arg}

/-- The grounded iteration corresponds stage by stage. Both directions are
needed at every stage, because defence quantifies over attackers on one side
and witnesses a defender on the other. -/
theorem iter_iff (h : AFMerge F₁ F₂ φ) :
    ∀ (k : Nat) (a : Arg), a ∈ F₁.args → (a ∈ iter F₁ k ↔ φ a ∈ iter F₂ k)
  | 0, _, _ => by simp [iter]
  | k + 1, a, ha => by
      have IH := h.iter_iff k
      simp only [iter, mem_step, defendedB_iff]
      constructor
      · rintro ⟨-, hdef⟩
        refine ⟨h.maps a ha, ?_⟩
        intro b' hb' hattack
        obtain ⟨b, hb, rfl⟩ := h.surj b' hb'
        obtain ⟨c, hc, hcb⟩ := hdef b hb (by rw [h.edge b hb a ha]; exact hattack)
        exact ⟨φ c, (IH c (iter_subset_args k c hc)).mp hc,
          by rw [← h.edge c (iter_subset_args k c hc) b hb]; exact hcb⟩
      · rintro ⟨-, hdef⟩
        refine ⟨ha, ?_⟩
        intro b hb hattack
        obtain ⟨c', hc', hcb⟩ :=
          hdef (φ b) (h.maps b hb) (by rw [← h.edge b hb a ha]; exact hattack)
        obtain ⟨c, hc, rfl⟩ := h.surj c' (iter_subset_args k c' hc')
        exact ⟨c, (IH c hc).mpr hc', by rw [h.edge c hc b hb]; exact hcb⟩

/-- **The grounded extension corresponds.** -/
theorem grounded_iff (h : AFMerge F₁ F₂ φ) {a : Arg} (ha : a ∈ F₁.args) :
    a ∈ grounded F₁ ↔ φ a ∈ grounded F₂ := by
  rw [mem_grounded_iff_iter (Nat.le_max_left F₁.args.length F₂.args.length) a,
    mem_grounded_iff_iter (Nat.le_max_right F₁.args.length F₂.args.length) (φ a)]
  exact h.iter_iff _ a ha

/-- Being attacked by an `in` argument corresponds. -/
theorem attackedByIn_eq (h : AFMerge F₁ F₂ φ) {a : Arg} (ha : a ∈ F₁.args) :
    F₁.args.any (fun c => memB c (grounded F₁) && F₁.attack c a)
      = F₂.args.any (fun c => memB c (grounded F₂) && F₂.attack c (φ a)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, memB_iff]
  constructor
  · rintro ⟨c, hc, hcin, hca⟩
    exact ⟨φ c, h.maps c hc, (h.grounded_iff hc).mp hcin,
      by rw [← h.edge c hc a ha]; exact hca⟩
  · rintro ⟨c', hc', hcin, hca⟩
    obtain ⟨c, hc, rfl⟩ := h.surj c' hc'
    exact ⟨c, hc, (h.grounded_iff hc).mpr hcin, by rw [h.edge c hc a ha]; exact hca⟩

/-- **The grounded label is invariant under a node merge.** -/
theorem labelC_eq (h : AFMerge F₁ F₂ φ) {a : Arg} (ha : a ∈ F₁.args) :
    labelC F₁ a = labelC F₂ (φ a) := by
  unfold labelC
  by_cases hin : a ∈ grounded F₁
  · rw [if_pos (memB_iff.mpr hin), if_pos (memB_iff.mpr ((h.grounded_iff ha).mp hin))]
  · rw [if_neg (fun hc => hin (memB_iff.mp hc)),
      if_neg (fun hc => hin ((h.grounded_iff ha).mpr (memB_iff.mp hc))),
      h.attackedByIn_eq ha]

/-! ### Claim status -/

/-- **Four-state status is invariant under a node merge**, for any two claims
whose support lists correspond under `φ`. The hypotheses are exactly what a
claim rebuilt on the merged side satisfies: every supporting position maps to a
supporting position, and every supporting position on the merged side comes
from one. -/
theorem statusC_eq (h : AFMerge F₁ F₂ φ) {c₁ c₂ : Claim}
    (hmaps : ∀ a ∈ c₁.support, a ∈ F₁.args ∧ φ a ∈ c₂.support)
    (hsurj : ∀ b ∈ c₂.support, ∃ a ∈ c₁.support, φ a = b) :
    statusC F₁ c₁ = statusC F₂ c₂ := by
  have hany : ∀ L : Label,
      c₁.support.any (fun a => labelC F₁ a == L)
        = c₂.support.any (fun b => labelC F₂ b == L) := by
    intro L
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨a, ha, hlab⟩
      obtain ⟨haArgs, hmem⟩ := hmaps a ha
      exact ⟨φ a, hmem, by rw [← h.labelC_eq haArgs]; exact hlab⟩
    · rintro ⟨b, hb, hlab⟩
      obtain ⟨a, ha, rfl⟩ := hsurj b hb
      exact ⟨a, ha, by rw [h.labelC_eq (hmaps a ha).1]; exact hlab⟩
  have hnil : c₁.support = [] ↔ c₂.support = [] := by
    constructor
    · intro h1
      cases hc2 : c₂.support with
      | nil => rfl
      | cons b bs =>
          obtain ⟨a, ha, -⟩ := hsurj b (by rw [hc2]; exact List.mem_cons_self)
          rw [h1] at ha
          exact absurd ha (by simp)
    · intro h2
      cases hc1 : c₁.support with
      | nil => rfl
      | cons a as =>
          have hmem := (hmaps a (by rw [hc1]; exact List.mem_cons_self)).2
          rw [h2] at hmem
          exact absurd hmem (by simp)
  unfold statusC
  by_cases h1 : c₁.support = []
  · rw [if_pos h1, if_pos (hnil.mp h1)]
  · rw [if_neg h1, if_neg (fun hc => h1 (hnil.mpr hc)), hany Label.inn, hany Label.undec]

end AFMerge

/-! ### The M1 carrier layer

M4's observation reads statuses off `StructuredAF` (the conclusion
labelling plus the compiled edge relation), so the merge statement is restated
one level up, where a node carries its conclusion. -/

/-- Membership in the carrier's claim support, characterized. -/
theorem mem_support_iff {canon : String → String}
    {F : StructuredAF} {p : Atom} {i : Nat} :
    i ∈ support canon F p ↔
      ∃ a, F.nodes[i]? = some a ∧ equiv canon a p := by
  simp only [support, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hres⟩
    by_cases h : equiv canon e.1 p
    · rw [if_pos h] at hres
      have hi : e.2 = i := Option.some.inj hres
      refine ⟨e.1, ?_, h⟩
      rw [← hi]
      exact List.mem_zipIdx_iff_getElem?.mp he
    · rw [if_neg h] at hres; exact absurd hres (by simp)
  · rintro ⟨a, ha, heq⟩
    exact ⟨(a, i), List.mem_zipIdx_iff_getElem?.mpr ha, by rw [if_pos heq]⟩

/-- **A node-merging morphism of carriers.** The extra clause over `AFMerge` is
that the merge preserves each node's conclusion — without it the claim
projection could move. -/
structure CarrierMerge (F₁ F₂ : StructuredAF) (φ : Nat → Nat) : Prop where
  maps : ∀ i, i < F₁.size → φ i < F₂.size
  surj : ∀ j, j < F₂.size → ∃ i, i < F₁.size ∧ φ i = j
  node : ∀ i, i < F₁.size → F₂.nodes[φ i]? = F₁.nodes[i]?
  edge : ∀ i, i < F₁.size → ∀ j, j < F₁.size → F₁.attack i j = F₂.attack (φ i) (φ j)

namespace CarrierMerge

variable {F₁ F₂ : StructuredAF} {φ : Nat → Nat}

/-- Forgetting the conclusions leaves a framework merge. -/
theorem toAFMerge (h : CarrierMerge F₁ F₂ φ) :
    AFMerge (eraseAF F₁) (eraseAF F₂) φ where
  maps := by
    intro a ha
    simp only [eraseAF, List.mem_range] at ha ⊢
    exact h.maps a ha
  surj := by
    intro b hb
    simp only [eraseAF, List.mem_range] at hb ⊢
    obtain ⟨i, hi, hφ⟩ := h.surj b hb
    exact ⟨i, by simpa [List.mem_range] using hi, hφ⟩
  edge := by
    intro a ha b hb
    simp only [eraseAF, List.mem_range] at ha hb
    exact h.edge a ha b hb

/-- **The carrier observation is invariant under a node merge.** Every claim's
four-state status agrees, for every atom. -/
theorem status_eq (h : CarrierMerge F₁ F₂ φ) (canon : String → String) (p : Atom) :
    status canon F₁ p = status canon F₂ p := by
  unfold status claim
  refine h.toAFMerge.statusC_eq ?_ ?_
  · intro i hi
    obtain ⟨a, ha, heq⟩ := mem_support_iff.mp hi
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
    refine ⟨by simpa [eraseAF, StructuredAF.size, List.mem_range] using hlt, ?_⟩
    exact mem_support_iff.mpr ⟨a, by rw [h.node i hlt]; exact ha, heq⟩
  · intro j hj
    obtain ⟨a, ha, heq⟩ := mem_support_iff.mp hj
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha
    obtain ⟨i, hi, rfl⟩ := h.surj j hlt
    exact ⟨i, mem_support_iff.mpr ⟨a, by rw [← h.node i hi]; exact ha, heq⟩, rfl⟩

end CarrierMerge


end Lara.Invariants
