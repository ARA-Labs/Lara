/-
Executable StatusBridge checker (issue #239, tracker #189).

`StatusBridge.forth`/`back` quantify over all Nat indices, but `corr_lt`
bounds every corresponded pair and `Compile.edgeB_faithful.ranged` bounds
every attacking index, so a finite scan over the two compiled programs'
index ranges decides the contract. This module only imports: the T8 layer
(`Lara.PW.Status`) is unchanged.

**Intended scale (eng review, decision 8A).** `forthB`/`backB` nest four
bounded quantifiers over the two argument ranges plus an inner `List.range`
witness scan, so the decider is `O(n²m²)` steps, and each step recomputes a
full `trSupport` traversal (inside `corrB`) and a `coveredB` scan over
`atts` (inside `edgeB`). This runs in the *kernel*: `decide` only,
`native_decide` is banned repo-wide. That is free on the T8 conformance
fixtures — every cell in `Lara/Examples/PWStatusCheck.lean` elaborates
instantly — and it is the only scale this decider is for. Pointing it at a
program with a realistic argument count will not reduce in practical time;
hoisting `trSupport` out of `corrB` would fix that but changes `corrB`'s
shape and so re-opens `corrB_iff` and both halves of
`statusBridgeB_sound`/`_complete`. Do not do that speculatively.
-/

import Lara.PW.Status

namespace Lara.PW

open Lara.Support Lara.Grounded Lara.Compile Lara.PW.Instance

section Decider
variable {κ lam : Instance.Context}

/-- Executable index correspondence: `Corr` as a `Bool` scan. -/
def corrB (m : SymMap) (lm : LeafId → LeafId) (w : World κ) (v : World lam)
    (i j : Nat) : Bool :=
  match w.unit.program.args[i]?, v.unit.program.args[j]? with
  | some t, some t' => decide (trSupport m lm t = some t')
  | _, _ => false

theorem corrB_iff (m : SymMap) (lm : LeafId → LeafId) (w : World κ)
    (v : World lam) (i j : Nat) :
    corrB m lm w v i j = true ↔ Corr m lm w v i j := by
  unfold corrB Corr
  cases ht : w.unit.program.args[i]? <;>
    cases ht' : v.unit.program.args[j]? <;> simp

/-- Executable `Admits`. -/
def admitsB (m : SymMap) (lm : LeafId → LeafId) (w : World κ) (v : World lam) :
    Bool :=
  w.unit.program.args.all fun t =>
    match trSupport m lm t with
    | some t' => v.unit.program.args.any fun u => decide (u = t')
    | none => false

theorem admitsB_iff (m : SymMap) (lm : LeafId → LeafId) (w : World κ)
    (v : World lam) : admitsB m lm w v = true ↔ Admits m lm w v := by
  unfold admitsB Admits
  rw [List.all_eq_true]
  constructor
  · intro h t ht
    have := h t ht
    cases htr : trSupport m lm t with
    | none => rw [htr] at this; exact absurd this (by simp)
    | some t' =>
      rw [htr] at this
      rcases List.any_eq_true.mp this with ⟨u, hu, hut⟩
      exact ⟨t', rfl, (of_decide_eq_true hut) ▸ hu⟩
  · intro h t ht
    rcases h t ht with ⟨t', htr, hmem⟩
    rw [htr]
    exact List.any_eq_true.mpr ⟨t', hmem, decide_eq_true rfl⟩

/-- Executable `matched`. -/
def matchedB (m : SymMap) (lm : LeafId → LeafId) (w : World κ) (v : World lam) :
    Bool :=
  v.unit.program.args.all fun t' =>
    w.unit.program.args.any fun t => decide (trSupport m lm t = some t')

theorem matchedB_iff (m : SymMap) (lm : LeafId → LeafId) (w : World κ)
    (v : World lam) :
    matchedB m lm w v = true ↔
      ∀ t', t' ∈ v.unit.program.args →
        ∃ t, t ∈ w.unit.program.args ∧ trSupport m lm t = some t' := by
  unfold matchedB
  rw [List.all_eq_true]
  constructor
  · intro h t' ht'
    rcases List.any_eq_true.mp (h t' ht') with ⟨t, ht, htr⟩
    exact ⟨t, ht, of_decide_eq_true htr⟩
  · intro h t' ht'
    rcases h t' ht' with ⟨t, ht, htr⟩
    exact List.any_eq_true.mpr ⟨t, ht, decide_eq_true htr⟩

/-- Executable `forth`: a bounded scan over the two finite index ranges.
The witness search is a `List.range` scan (a `Bool`), so the whole formula
stays within the `Nat.decidableBallLT` idiom the example cells already use. -/
def forthB (m : SymMap) (lm : LeafId → LeafId) (w : World κ) (v : World lam) :
    Bool :=
  decide (∀ i, i < w.unit.program.args.length →
    ∀ j, j < v.unit.program.args.length →
      corrB m lm w v i j = true →
        ∀ k, k < w.unit.program.args.length →
          edgeB w.unit.program k i = true →
            ((List.range v.unit.program.args.length).any fun k' =>
              corrB m lm w v k k' && edgeB v.unit.program k' j) = true)

/-- Executable `back`. -/
def backB (m : SymMap) (lm : LeafId → LeafId) (w : World κ) (v : World lam) :
    Bool :=
  decide (∀ i, i < w.unit.program.args.length →
    ∀ j, j < v.unit.program.args.length →
      corrB m lm w v i j = true →
        ∀ k', k' < v.unit.program.args.length →
          edgeB v.unit.program k' j = true →
            ((List.range w.unit.program.args.length).any fun k =>
              corrB m lm w v k k' && edgeB w.unit.program k i) = true)

/-- The `StatusBridge` decider. -/
def statusBridgeB (m : SymMap) (lm : LeafId → LeafId) (w : World κ)
    (v : World lam) : Bool :=
  admitsB m lm w v && matchedB m lm w v && forthB m lm w v && backB m lm w v

/-- Soundness: the finite scans cover the unbounded quantifiers because
`corr_lt` bounds the corresponding indices and `edgeB_faithful` bounds the
attacking index. -/
theorem statusBridgeB_sound {m : SymMap} {lm : LeafId → LeafId} {w : World κ}
    {v : World lam} (h : statusBridgeB m lm w v = true) :
    StatusBridge m lm w v := by
  unfold statusBridgeB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hadm, hmat⟩, hforth⟩, hback⟩ := h
  refine ⟨(admitsB_iff m lm w v).mp hadm, (matchedB_iff m lm w v).mp hmat,
    ?_, ?_⟩
  · intro i j k hC hE
    have hb := corr_lt hC
    have hk := ((edgeB_faithful w.unit.program).ranged k i hE).1
    have hf := of_decide_eq_true hforth
    have hw := hf i hb.1 j hb.2 ((corrB_iff m lm w v i j).mpr hC) k hk hE
    rcases List.any_eq_true.mp hw with ⟨k', _, hk'⟩
    rcases Bool.and_eq_true_iff.mp hk' with ⟨hck', he'⟩
    exact ⟨k', (corrB_iff m lm w v k k').mp hck', he'⟩
  · intro i j k' hC hE
    have hb := corr_lt hC
    have hk' := ((edgeB_faithful v.unit.program).ranged k' j hE).1
    have hf := of_decide_eq_true hback
    have hw := hf i hb.1 j hb.2 ((corrB_iff m lm w v i j).mpr hC) k' hk' hE
    rcases List.any_eq_true.mp hw with ⟨k, _, hk⟩
    rcases Bool.and_eq_true_iff.mp hk with ⟨hck, he⟩
    exact ⟨k, (corrB_iff m lm w v k k').mp hck, he⟩

/-- Completeness: every scanned triple either fails its guards or gets its
witness from the corresponding `StatusBridge` field, and the witness is in
range by `corr_lt`. -/
theorem statusBridgeB_complete {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} (h : StatusBridge m lm w v) :
    statusBridgeB m lm w v = true := by
  unfold statusBridgeB
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨(admitsB_iff m lm w v).mpr h.admits,
    (matchedB_iff m lm w v).mpr h.matched⟩, ?_⟩, ?_⟩
  · refine decide_eq_true ?_
    intro i _ j _ hC k _ hE
    rcases h.forth i j k ((corrB_iff m lm w v i j).mp hC) hE with ⟨k', hC', hE'⟩
    refine List.any_eq_true.mpr ⟨k', List.mem_range.mpr (corr_lt hC').2, ?_⟩
    exact Bool.and_eq_true_iff.mpr
      ⟨(corrB_iff m lm w v k k').mpr hC', hE'⟩
  · refine decide_eq_true ?_
    intro i _ j _ hC k' _ hE
    rcases h.back i j k' ((corrB_iff m lm w v i j).mp hC) hE with ⟨k, hC', hE'⟩
    refine List.any_eq_true.mpr ⟨k, List.mem_range.mpr (corr_lt hC').1, ?_⟩
    exact Bool.and_eq_true_iff.mpr
      ⟨(corrB_iff m lm w v k k').mpr hC', hE'⟩

end Decider
end Lara.PW
