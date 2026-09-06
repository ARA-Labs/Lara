/-
Sublist enumeration and representative uniqueness (`Lara.Semantics.Sublists`).

A core-Lean stand-in for the part of `Mathlib.Data.List.Sublists` this
development needs. Core Lean 4 at this toolchain has the `List.Sublist`
*relation* but not `List.sublists`, and the repository has no Mathlib
dependency, so the enumeration and its characterization are defined and proved
here by hand.

**What is here.** Two generic `Bool` case-split facts; `subseqs`, the
powerset scan; `mem_subseqs`, its characterization against `List.Sublist`; and
the `Nodup` layer — `sublist_ext`, `subseqs_ext`, `nodup_flatMap_pair`,
`subseqs_nodup` — which is what makes "one representative per subset" a
theorem rather than a convention. `exists_max_length` closes the file: the
finiteness principle that turns "the scan is finite" into a maximal *element*.

**Why it is its own module.** No declaration here mentions `AF`, an extension,
or a semantics: every one is a statement about lists or about `Bool`.
`Lara.Semantics` transports the three list results it needs to the carrier of a
framework (`candidates`, `candidates_ext`, `candidates_nodup`) and states the
representation claim these lemmas discharge; this module is the list-level half,
readable and checkable on its own.

The declarations stay in the `Lara.Semantics` namespace, so `open Lara.Semantics`
picks them up unqualified exactly as before this file was split out.

`Arg` is imported rather than restated: it is `Lara.Grounded.Arg`, and importing
it keeps every statement here byte-identical to the form `Lara.Semantics` proved
them in.
-/

import Lara.Grounded

namespace Lara.Semantics

open Lara.Grounded

/-! ### Boolean helpers

Two generic `Bool` facts the decider adequacy proofs need repeatedly. Both are
proved by exhaustive case split rather than by a `simp` chain: the case split is
what survives a toolchain bump, whereas a `simp` chain depends on whichever
normal form the current core `Bool` simp set happens to produce. They sit in this
module, at the top, because they mention no `AF` at all — and because anyone doing
`open Lara.Semantics` picks them up unqualified, so they had better be easy to
find. -/

/-- A negated `Bool` is `true` exactly when the original is not. Stated once and
used at all four sites in `completeB_iff` and `leastCompleteB_iff` that have to
move between `¬ (b = true)` and `(! b) = true`; without it, a change in the core
`Bool` normal form would have to be re-diagnosed four times independently. -/
theorem not_eq_true_iff {b : Bool} : (! b) = true ↔ ¬ (b = true) := by
  cases b <;> simp

/-- The boolean shape of "the guard fails or the conclusion holds", spelled out
so the maximality proofs never have to reason about `&&` under a negation. -/
theorem not_and_eq_true {a b : Bool} : (! (a && b)) = true ↔ ¬ (a = true ∧ b = true) := by
  cases a <;> cases b <;> simp

/-! ### The enumeration primitive

`subseqs` is the powerset scan, phrased so that its characterization against the
core `List.Sublist` relation is a two-case induction. Core Lean 4 at this
toolchain has the `List.Sublist` *relation* but not `List.sublists`, so the
enumeration is defined here rather than imported. -/

/-- Order-preserving subsequences of a list, no Mathlib. For each element the
recursion branches on "drop it" / "keep it". On a duplicate-free input the result
lists every sublist exactly once — `mem_subseqs` gives "every", `subseqs_nodup`
gives "at most once", and `subseqs_ext` gives the sharper statement that even two
*syntactically* distinct outputs would have to differ as sets. -/
def subseqs : List Arg → List (List Arg)
  | [] => [[]]
  | a :: l => (subseqs l).flatMap (fun s => [s, a :: s])

/-- `subseqs` enumerates exactly the sublists. This is the only fact about the
enumeration primitive any later proof needs: it converts a *membership in a
finite list* obligation (which `List.all` can decide) into a *structural
sublist* obligation (which the `ExtensionSemantics.sound` contract speaks). -/
theorem mem_subseqs {l s : List Arg} : s ∈ subseqs l ↔ s.Sublist l := by
  induction l generalizing s with
  | nil => simp [subseqs, List.sublist_nil]
  | cons a l ih =>
      simp only [subseqs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨t, ht, rfl | rfl⟩
        · exact (ih.mp ht).cons a
        · exact (ih.mp ht).cons_cons a
      · intro h
        cases h with
        | cons _ h => exact ⟨s, ih.mpr h, Or.inl rfl⟩
        | cons_cons _ h => exact ⟨_, ih.mpr h, Or.inr rfl⟩

/-! ### Uniqueness of representatives under `Nodup`

This is the section that discharges the central representation claim of
`Lara.Semantics`'s module header. `ExtensionSemantics.sound` never needs `Nodup`;
this does, and it is the whole of what the hypothesis is for. -/

/-- Under `Nodup`, a sublist is determined by its member set. The induction is on
the carrier: at `a :: l` the two "one keeps `a`, the other drops it" cases are
killed by `a ∉ l`, and in the "both keep `a`" case the same fact strips `a` off
both member sets so the induction hypothesis applies. -/
theorem sublist_ext : ∀ {l : List Arg}, l.Nodup → ∀ (s t : List Arg),
    s.Sublist l → t.Sublist l → (∀ x, x ∈ s ↔ x ∈ t) → s = t := by
  intro l
  induction l with
  | nil =>
      intro _ s t hs ht _
      rw [List.sublist_nil.mp hs, List.sublist_nil.mp ht]
  | cons a l ih =>
      intro hl s t hs ht h
      obtain ⟨hal, hnd⟩ := List.nodup_cons.mp hl
      cases hs with
      | cons _ hs' =>
          cases ht with
          | cons _ ht' => exact ih hnd _ _ hs' ht' h
          | cons_cons _ ht' =>
              exact absurd (hs'.subset ((h a).mpr List.mem_cons_self)) hal
      | cons_cons _ hs' =>
          cases ht with
          | cons _ ht' =>
              exact absurd (ht'.subset ((h a).mp List.mem_cons_self)) hal
          | cons_cons _ ht' =>
              refine congrArg (List.cons a) (ih hnd _ _ hs' ht' ?_)
              intro x
              constructor
              · intro hx
                have hxl : x ∈ l := hs'.subset hx
                rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem a hx)) with hxa | hx'
                · subst hxa; exact absurd hxl hal
                · exact hx'
              · intro hx
                have hxl : x ∈ l := ht'.subset hx
                rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem a hx)) with hxa | hx'
                · subst hxa; exact absurd hxl hal
                · exact hx'

/-- The same fact phrased for the enumeration primitive: over a duplicate-free
list, two enumerated subsequences with the same members are literally equal.
This is the "exactly one representative" half of the representation choice. -/
theorem subseqs_ext {l s t : List Arg} (hl : l.Nodup) (hs : s ∈ subseqs l)
    (ht : t ∈ subseqs l) (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t :=
  sublist_ext hl s t (mem_subseqs.mp hs) (mem_subseqs.mp ht) h

/-- Auxiliary for `subseqs_nodup`: the "drop it / keep it" branching of one
recursion step preserves duplicate-freedom, provided the element being branched
on occurs in none of the sets enumerated so far. The four disjointness cases are
all decided by that one fact. -/
theorem nodup_flatMap_pair {a : Arg} : ∀ {L : List (List Arg)}, L.Nodup →
    (∀ s ∈ L, a ∉ s) → (L.flatMap (fun s => [s, a :: s])).Nodup := by
  intro L
  induction L with
  | nil => intro _ _; simp
  | cons s rest ih =>
      intro hnd hmem
      obtain ⟨hs, hrest⟩ := List.nodup_cons.mp hnd
      have has : a ∉ s := hmem s List.mem_cons_self
      have hmem' : ∀ t ∈ rest, a ∉ t := fun t ht => hmem t (List.mem_cons_of_mem s ht)
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨?_, ih hrest hmem', ?_⟩
      · have hne : s ≠ a :: s := fun hcon => has (by rw [hcon]; exact List.mem_cons_self)
        simp [hne]
      · intro u hu v hv
        rw [List.mem_flatMap] at hv
        obtain ⟨t, ht, hvt⟩ := hv
        have hat : a ∉ t := hmem' t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hvt
        rcases hu with rfl | rfl <;> rcases hvt with rfl | rfl
        · intro hcon; subst hcon; exact hs ht
        · intro hcon; exact has (by rw [hcon]; exact List.mem_cons_self)
        · intro hcon; exact hat (by rw [← hcon]; exact List.mem_cons_self)
        · intro hcon; injection hcon with _ h2; subst h2; exact hs ht

/-- The enumeration repeats nothing on a duplicate-free input: it is a list of
distinct subsequences, not a multiset with hidden copies. -/
theorem subseqs_nodup : ∀ {l : List Arg}, l.Nodup → (subseqs l).Nodup
  | [], _ => by simp [subseqs]
  | a :: l, hl => by
      obtain ⟨hal, hnd⟩ := List.nodup_cons.mp hl
      rw [subseqs]
      exact nodup_flatMap_pair (subseqs_nodup hnd)
        (fun s hs hc => hal ((mem_subseqs.mp hs).subset hc))

/-! ### A maximal element of a finite scan

The finiteness principle `Lara.Semantics.preferred_exists` runs on. Core Lean has
`List.max?` for the *value* of a maximum but nothing that hands back the element
attaining it, and the element is the whole point: a preferred extension is a
witness, not a number. -/

/-- A non-empty list has a member of maximal length. Length — rather than an
abstract order — because that is what the caller can compare: `⊆`-maximality
among sublists of a common carrier follows from length-maximality through
`List.Sublist.eq_of_length`, so no order-theoretic machinery (and no Mathlib) is
needed. The `[a]` base case is separated from `a :: b :: t` so the recursive call
never has to defend a `≠ []` side condition. -/
theorem exists_max_length :
    ∀ (l : List (List Arg)), l ≠ [] → ∃ x ∈ l, ∀ y ∈ l, y.length ≤ x.length
  | [], h => absurd rfl h
  | [a], _ => ⟨a, List.mem_singleton.mpr rfl, by
      intro y hy
      rw [List.mem_singleton.mp hy]
      exact Nat.le_refl _⟩
  | a :: b :: t, _ => by
      obtain ⟨m, hm, hmax⟩ := exists_max_length (b :: t) (by simp)
      by_cases hle : m.length ≤ a.length
      · refine ⟨a, List.mem_cons_self, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Nat.le_refl _
        · exact Nat.le_trans (hmax y hy) hle
      · refine ⟨m, List.mem_cons_of_mem _ hm, ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Nat.le_of_lt (Nat.lt_of_not_le hle)
        · exact hmax y hy

end Lara.Semantics
