/-
# Pointwise relations on lists

`Forall₂ Rel l₁ l₂` holds when the two lists have the same length and
corresponding elements are `Rel`-related. Core Lean 4.32.0 has no such family
(it is a Mathlib name) and this development needs one for attack lists, cache
entry lists and node lists.

**Why this is its own module.** CLAUDE.md's seam test: its own vocabulary
(lists, not certificates), its own dependencies (core only), its own reason to
be read alone. `Lara.Context.Parametricity` is about one theorem; this is not.

**Why `RelTerms`/`RelDis` are NOT instances of this.** They must be defined in
the same `mutual` block as `RelTerm`, which recurses through `SupportTerm`'s
nested `List` fields. `Lara/Support.lean:60` records the general constraint.
`relTerms_iff_forall₂` (`Lara.Context.Parametricity`) is the bridge.
-/

set_option autoImplicit false

namespace Lara

/-- Two lists of the same length whose corresponding elements are related. -/
inductive Forall₂ {α β : Type} (Rel : α → β → Prop) : List α → List β → Prop where
  | nil : Forall₂ Rel [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β}
      (h : Rel a b) (hs : Forall₂ Rel as bs) : Forall₂ Rel (a :: as) (b :: bs)

end Lara

namespace Lara.Forall₂

variable {α β : Type} {Rel : α → β → Prop}

/-- Related lists have equal length. Replaces `List.Forall₂.length_eq`. -/
theorem length_eq : ∀ {as : List α} {bs : List β},
    Forall₂ Rel as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => by simp only [List.length_cons, length_eq hs]

/-- A list is related to itself when every element is related to itself.
Replaces `List.forall₂_same`.

The local `Rel` deliberately shadows the section variable: this is the one
lemma in the file whose two lists have the *same* type, so it needs a
homogeneous `α → α → Prop` where the section binds `α → β → Prop`. -/
theorem of_same {Rel : α → α → Prop} : ∀ {as : List α},
    (∀ a ∈ as, Rel a a) → Forall₂ Rel as as
  | [], _ => .nil
  | a :: as, h =>
      .cons (h a (by simp)) (of_same (fun x hx => h x (by simp [hx])))

/-- A list is related to its image under `f` when `Rel a (f a)` always holds.
Replaces `List.forall₂_map_right_iff` in the one direction consumed here. -/
theorem of_map_right {f : α → β} : ∀ {as : List α},
    (∀ a ∈ as, Rel a (f a)) → Forall₂ Rel as (as.map f)
  | [], _ => .nil
  | a :: as, h =>
      .cons (h a (by simp)) (of_map_right (fun x hx => h x (by simp [hx])))

/-- Concatenation. Replaces `List.forall₂_append`. -/
theorem append : ∀ {as₁ as₂ : List α} {bs₁ bs₂ : List β},
    Forall₂ Rel as₁ bs₁ → Forall₂ Rel as₂ bs₂ →
    Forall₂ Rel (as₁ ++ as₂) (bs₁ ++ bs₂)
  | _, _, _, _, .nil, h₂ => h₂
  | _, _, _, _, .cons h hs, h₂ => .cons h (append hs h₂)

/-- Positional lookup, right to left. Replaces `List.forall₂_getElem?`. -/
theorem getElem?_right : ∀ {as : List α} {bs : List β},
    Forall₂ Rel as bs → ∀ {i : Nat} {b : β}, bs[i]? = some b →
    ∃ a, as[i]? = some a ∧ Rel a b
  | _, _, .nil, i, _, hi => by simp at hi
  | _, _, .cons h hs, i, b, hi => by
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          exact ⟨_, rfl, hi ▸ h⟩
      | succ n =>
          simp only [List.getElem?_cons_succ] at hi ⊢
          exact getElem?_right hs hi

/-- Positional lookup, left to right. The mirror of `getElem?_right`; the #215
carrier lemmas navigate forwards along the relation and need this direction. -/
theorem getElem?_left : ∀ {as : List α} {bs : List β},
    Forall₂ Rel as bs → ∀ {i : Nat} {a : α}, as[i]? = some a →
    ∃ b, bs[i]? = some b ∧ Rel a b
  | _, _, .nil, i, _, hi => by simp at hi
  | _, _, .cons h hs, i, a, hi => by
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          exact ⟨_, rfl, hi ▸ h⟩
      | succ n =>
          simp only [List.getElem?_cons_succ] at hi ⊢
          exact getElem?_left hs hi

/-- Off the end on one side is off the end on the other — the lists have equal
length. -/
theorem getElem?_none {as : List α} {bs : List β} (h : Forall₂ Rel as bs)
    {i : Nat} (hi : as[i]? = none) : bs[i]? = none := by
  rw [List.getElem?_eq_none_iff] at hi ⊢
  rw [← length_eq h]
  exact hi

/-- Membership, right to left. -/
theorem mem_right : ∀ {as : List α} {bs : List β},
    Forall₂ Rel as bs → ∀ {b : β}, b ∈ bs → ∃ a, a ∈ as ∧ Rel a b
  | _, _, .nil, _, hb => by simp at hb
  | _, _, .cons h hs, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact ⟨_, by simp, h⟩
      · obtain ⟨a, ha, hr⟩ := mem_right hs hb'
        exact ⟨a, by simp [ha], hr⟩

/-- Membership, left to right. -/
theorem mem_left : ∀ {as : List α} {bs : List β},
    Forall₂ Rel as bs → ∀ {a : α}, a ∈ as → ∃ b, b ∈ bs ∧ Rel a b
  | _, _, .nil, _, ha => by simp at ha
  | _, _, .cons h hs, a, ha => by
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨_, by simp, h⟩
      · obtain ⟨b, hb, hr⟩ := mem_left hs ha'
        exact ⟨b, by simp [hb], hr⟩

end Lara.Forall₂
