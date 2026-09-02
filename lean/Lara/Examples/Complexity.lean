/-
The fixed-context realizable quartic witness (issue #209, Task 10).

`quarticAF k` is the three-block carrier: for `k + 1` it lists, in
declaration order, `k` neutral `g` nodes followed by the defender `d`, then
`k + 1` attacked `b` nodes, then `k + 1` target `a` nodes; the edges are
exactly `d → b(i)` and `b(i) → a(j)` (the `b(X) → a(Y)` schema row has
independent variables, so every `b` attacks every `a`).  `quarticAF 0` is the
empty carrier.

Three results are mechanized:

* **Class membership** (`quartic_realizable`): the carrier is realized under
  the frozen M2b context — identity canon, `m2bSigma`, `m2bPolicy`,
  `m2bRegistry` — by a raw unit with leaf-only support terms and one explicit
  root undermine per edge, through the executable checker
  (`quartic_checkUnit_ok`) with ground coverage and a `StructuredAFIso` at
  the identity reindexing (`quarticIso`).  `quartic_size` pins the node
  count at `3k`.
* **Iterate shape** (`quartic_iter_one`, `quartic_iter_fix`): round one of
  the grounded iteration is exactly the defender block (the `g` nodes and
  `d`, with `d` declared *last*), and every later round is the defender
  block plus the target block.  The `b` nodes never enter; the fixpoint is
  reached at round two but the reference evaluator keeps paying full scans.
* **Quartic cost** (`quartic_cost_ge`): for `2 ≤ k`, the instrumented
  grounded run on the erased carrier pays at least `k⁴` attack queries.
  Each round from the second on pays ≥ `k³`: every `a`-defense scans each of
  the `k` `b`-attackers, and each such attacker's defense scan walks the
  iterate past all `k − 1` neutral `g` members before `d` — declared last in
  the defender block — answers; the evaluator runs `3k` rounds.

* **Carrier-status transfer** (`carrierStatus_quartic_cost_ge`): the floor
  transfers to the shared carrier-status query —
  the `d` claim has nonempty complete support, so `carrierStatusC` takes
  the grounded branch and pays the complete `groundedC` count.

**Quantifier discipline (constraint D4, `docs/theory-m2b-complexity.md`).**
Together with
`quartic_size` and `groundedC_cost_le`, this is a *worst-case* `Θ(n⁴)`
result over the fixed-context realizable class — an existential family on
which the `n³(1 + n)` ceiling is attained up to a constant — NOT a universal
per-instance floor.  The proved universal lower bound is quadratic
(`groundedC_cost_ge`), and `groundedC_twoNodeAllAttacks_cost` refutes only
the rejected exact pointwise cubic inequality at `n = 2`.  The closed
evaluations `quartic_cost_eval_two/three/four`
assert the theorem's inequality at `k = 2, 3, 4`.
-/

import Lara.Complexity
import Lara.Complexity.Gadget
import Lara.Realizability

namespace Lara.Examples.Complexity

open Lara Lara.Complexity Lara.Support Lara.Attack

/-! ## The closed leaf vocabulary of the witness

Fresh per-`k` leaf identifiers, following the repo's symbolic-core
discipline: a closed sum with a single injective spelling table
(`QuarticLeaf.encode`), and one ground atom per leaf (`QuarticLeaf.atom`). -/

/-- Closed leaf vocabulary of the quartic witness. -/
inductive QuarticLeaf where
  | g (i : Nat)
  | d
  | b (i : Nat)
  | a (i : Nat)
deriving DecidableEq

/-- The single spelling table for quartic-witness leaf identifiers. -/
def QuarticLeaf.encode : QuarticLeaf → LeafId
  | .g i => ⟨"quartic-g-" ++ Nat.repr i⟩
  | .d => ⟨"quartic-d"⟩
  | .b i => ⟨"quartic-b-" ++ Nat.repr i⟩
  | .a i => ⟨"quartic-a-" ++ Nat.repr i⟩

/-- The ground conclusion each leaf contributes. -/
def QuarticLeaf.atom : QuarticLeaf → Lara.Atom
  | .g i => gAtom i
  | .d => dAtom
  | .b i => bAtom i
  | .a i => aAtom i

/-- The declaration order of `quarticAF (k + 1)`: `k` neutral `g` leaves,
then the defender `d` — deliberately *last* in its block — then `k + 1` `b`
leaves, then `k + 1` `a` leaves. -/
def quarticLeaves (k : Nat) : List QuarticLeaf :=
  ((List.range k).map .g ++ [.d]) ++
    ((List.range (k + 1)).map .b ++ (List.range (k + 1)).map .a)

theorem quarticLeaves_length (k : Nat) :
    (quarticLeaves k).length = 3 * (k + 1) := by
  simp only [quarticLeaves, List.length_append, List.length_map,
    List.length_range, List.length_cons, List.length_nil]
  omega

/-! ## The carrier -/

/-- The intended edge relation over declaration-order positions of
`quarticAF (k + 1)`: `d` (position `k`) attacks every `b`
(positions `k+1 … 2(k+1)−1`), and every `b` attacks every `a`
(positions `2(k+1) … 3(k+1)−1`). -/
def quarticAttack (k : Nat) (i j : Nat) : Bool :=
  decide ((i = k ∧ k + 1 ≤ j ∧ j < 2 * (k + 1)) ∨
    (k + 1 ≤ i ∧ i < 2 * (k + 1) ∧ 2 * (k + 1) ≤ j ∧ j < 3 * (k + 1)))

theorem quarticAttack_eq_true_iff {k i j : Nat} :
    quarticAttack k i j = true ↔
      (i = k ∧ k + 1 ≤ j ∧ j < 2 * (k + 1)) ∨
      (k + 1 ≤ i ∧ i < 2 * (k + 1) ∧ 2 * (k + 1) ≤ j ∧ j < 3 * (k + 1)) := by
  simp [quarticAttack]

private theorem quarticAttack_true {k i j : Nat}
    (h : (i = k ∧ k + 1 ≤ j ∧ j < 2 * (k + 1)) ∨
      (k + 1 ≤ i ∧ i < 2 * (k + 1) ∧ 2 * (k + 1) ≤ j ∧ j < 3 * (k + 1))) :
    quarticAttack k i j = true :=
  decide_eq_true h

private theorem quarticAttack_false {k i j : Nat}
    (h : ¬ ((i = k ∧ k + 1 ≤ j ∧ j < 2 * (k + 1)) ∨
      (k + 1 ≤ i ∧ i < 2 * (k + 1) ∧ 2 * (k + 1) ≤ j ∧ j < 3 * (k + 1)))) :
    quarticAttack k i j = false :=
  decide_eq_false h

/-- **The three-block carrier.**  `quarticAF 0` is the empty carrier; for
`k + 1` the nodes are the leaf conclusions in declaration order and the
edges are exactly `d → b(i)` and `b(i) → a(j)`. -/
def quarticAF : Nat → Invariants.StructuredAF
  | 0 => { nodes := [], attack := fun _ _ => false }
  | k + 1 =>
      { nodes := (quarticLeaves k).map QuarticLeaf.atom
        attack := quarticAttack k }

/-- **The frozen node count** (statement frozen by the #209 decision
record, `docs/theory-m2b-complexity.md`). -/
theorem quartic_size (k : Nat) : (quarticAF k).size = 3 * k := by
  cases k with
  | zero => rfl
  | succ k =>
      show ((quarticLeaves k).map QuarticLeaf.atom).length = 3 * (k + 1)
      rw [List.length_map, quarticLeaves_length]

/-! ## Injectivity of the spelling table -/

private theorem toDigits_inj {m n : Nat}
    (h : Nat.toDigits 10 m = Nat.toDigits 10 n) : m = n :=
  Numeral.natRepr_toList_inj (by rw [Nat.toList_repr, Nat.toList_repr]; exact h)

/-- The single spelling table never collides: `QuarticLeaf.encode` is
injective.  Same-constructor cases cancel the fixed prefix and reduce to
decimal-numeral injectivity; cross-constructor cases differ at the fixed
block letter. -/
theorem QuarticLeaf.encode_inj : Function.Injective QuarticLeaf.encode := by
  intro x y h
  have hlist : (QuarticLeaf.encode x).name.toList =
      (QuarticLeaf.encode y).name.toList := by rw [h]
  cases x with
  | g v =>
      cases y with
      | g w =>
          simp [QuarticLeaf.encode, String.toList_append] at hlist
          rw [toDigits_inj hlist]
      | d => simp [QuarticLeaf.encode, String.toList_append] at hlist
      | b w => simp [QuarticLeaf.encode, String.toList_append] at hlist
      | a w => simp [QuarticLeaf.encode, String.toList_append] at hlist
  | d =>
      cases y with
      | g w => simp [QuarticLeaf.encode, String.toList_append] at hlist
      | d => rfl
      | b w => simp [QuarticLeaf.encode, String.toList_append] at hlist
      | a w => simp [QuarticLeaf.encode, String.toList_append] at hlist
  | b v =>
      cases y with
      | g w => simp [QuarticLeaf.encode, String.toList_append] at hlist
      | d => simp [QuarticLeaf.encode, String.toList_append] at hlist
      | b w =>
          simp [QuarticLeaf.encode, String.toList_append] at hlist
          rw [toDigits_inj hlist]
      | a w => simp [QuarticLeaf.encode, String.toList_append] at hlist
  | a v =>
      cases y with
      | g w => simp [QuarticLeaf.encode, String.toList_append] at hlist
      | d => simp [QuarticLeaf.encode, String.toList_append] at hlist
      | b w => simp [QuarticLeaf.encode, String.toList_append] at hlist
      | a w =>
          simp [QuarticLeaf.encode, String.toList_append] at hlist
          rw [toDigits_inj hlist]

/-! ## The raw unit under the fixed context -/

/-- The leaf support term of a quartic leaf (leaf-only support, per the
#209 decision record). -/
def leafArg (l : QuarticLeaf) : SupportTerm := .leaf l.encode

private theorem leafArg_inj {l l' : QuarticLeaf} (h : leafArg l = leafArg l') :
    l = l' := by
  have h' : SupportTerm.leaf l.encode = SupportTerm.leaf l'.encode := h
  injection h' with h''
  exact QuarticLeaf.encode_inj h''

private theorem leafArg_injective : Function.Injective leafArg :=
  fun _ _ h => leafArg_inj h

/-- The per-`k` Γ table: every leaf paired with its ground conclusion. -/
def quarticTable (k : Nat) : List (LeafId × Lara.Atom) :=
  (quarticLeaves k).map fun l => (l.encode, l.atom)

/-- The formula-free Γ of the witness (the fixed policy and registry do not
depend on `k`). -/
def quarticGamma (k : Nat) : LeafId → Option Lara.Atom :=
  lookupLeaf (quarticTable k)

/-- Explicit finite ground list covering every witness leaf entry. -/
def quarticGround (k : Nat) : List Lara.Atom :=
  (quarticTable k).map Prod.snd

/-- The declared arguments: one leaf term per carrier node, in declaration
order. -/
def quarticArgs (k : Nat) : List SupportTerm :=
  (quarticLeaves k).map leafArg

/-- The declared attacks: one explicit root undermine per intended edge —
`d → b(i)` and `b(i) → a(j)` for all `i, j < k + 1`. -/
def quarticAtts (k : Nat) : List Attack :=
  (List.range (k + 1)).map
      (fun x => .undermine (leafArg .d) (leafArg (.b x)) []) ++
    (List.range (k + 1)).flatMap fun x =>
      (List.range (k + 1)).map fun y =>
        .undermine (leafArg (.b x)) (leafArg (.a y)) []

/-- The raw unit of `quarticAF (k + 1)` under the fixed context. -/
def quarticRaw (k : Nat) : Lara.Unit :=
  { sigma := m2bSigma
    policy := m2bPolicy
    args := quarticArgs k
    atts := quarticAtts k }

/-! ## Leaf-list bookkeeping -/

private theorem nodup_map_of_injective {α β : Type _} {f : α → β}
    (hf : Function.Injective f) {l : List α} (hl : l.Nodup) :
    (l.map f).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact hl.imp fun hne heq => hne (hf heq)

private theorem g_injective : Function.Injective QuarticLeaf.g :=
  fun _ _ h => by injection h

private theorem b_injective : Function.Injective QuarticLeaf.b :=
  fun _ _ h => by injection h

private theorem a_injective : Function.Injective QuarticLeaf.a :=
  fun _ _ h => by injection h

private theorem quarticLeaves_nodup (k : Nat) : (quarticLeaves k).Nodup := by
  rw [quarticLeaves, List.nodup_append, List.nodup_append, List.nodup_append]
  refine ⟨⟨nodup_map_of_injective g_injective List.nodup_range, by simp, ?_⟩,
    ⟨nodup_map_of_injective b_injective List.nodup_range,
      nodup_map_of_injective a_injective List.nodup_range, ?_⟩, ?_⟩
  · intro x hx y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    have hy' : y = QuarticLeaf.d := by simpa using hy
    subst hy'
    simp
  · intro x hx y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    simp
  · intro x hx y hy
    rcases List.mem_append.mp hy with hyb | hya
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hyb
      rcases List.mem_append.mp hx with hxg | hxd
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hxg
        simp
      · have hx' : x = QuarticLeaf.d := by simpa using hxd
        subst hx'
        simp
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hya
      rcases List.mem_append.mp hx with hxg | hxd
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hxg
        simp
      · have hx' : x = QuarticLeaf.d := by simpa using hxd
        subst hx'
        simp

private theorem d_mem (k : Nat) : QuarticLeaf.d ∈ quarticLeaves k :=
  List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)

private theorem b_mem {k x : Nat} (h : x < k + 1) :
    QuarticLeaf.b x ∈ quarticLeaves k :=
  List.mem_append_right _
    (List.mem_append_left _ (List.mem_map.mpr ⟨x, List.mem_range.mpr h, rfl⟩))

private theorem a_mem {k x : Nat} (h : x < k + 1) :
    QuarticLeaf.a x ∈ quarticLeaves k :=
  List.mem_append_right _
    (List.mem_append_right _ (List.mem_map.mpr ⟨x, List.mem_range.mpr h, rfl⟩))

/-! ## Positional characterization of the declaration order -/

private theorem quarticLeaves_getElem?_g {k i : Nat} (h : i < k) :
    (quarticLeaves k)[i]? = some (.g i) := by
  rw [quarticLeaves,
    List.getElem?_append_left (by
      simp only [List.length_append, List.length_map, List.length_range,
        List.length_cons, List.length_nil]
      omega),
    List.getElem?_append_left (by
      simp only [List.length_map, List.length_range]
      omega),
    List.getElem?_map, List.getElem?_range h]
  rfl

private theorem quarticLeaves_getElem?_d (k : Nat) :
    (quarticLeaves k)[k]? = some .d := by
  rw [quarticLeaves,
    List.getElem?_append_left (by
      simp only [List.length_append, List.length_map, List.length_range,
        List.length_cons, List.length_nil]
      omega),
    List.getElem?_append_right (by
      simp only [List.length_map, List.length_range]
      omega)]
  simp

private theorem quarticLeaves_getElem?_b {k x : Nat} (h : x < k + 1) :
    (quarticLeaves k)[k + 1 + x]? = some (.b x) := by
  rw [quarticLeaves,
    List.getElem?_append_right (by
      simp only [List.length_append, List.length_map, List.length_range,
        List.length_cons, List.length_nil]
      omega)]
  have hidx : k + 1 + x -
      ((List.range k).map QuarticLeaf.g ++ [QuarticLeaf.d]).length = x := by
    simp only [List.length_append, List.length_map, List.length_range,
      List.length_cons, List.length_nil]
    omega
  rw [hidx,
    List.getElem?_append_left (by
      simp only [List.length_map, List.length_range]
      omega),
    List.getElem?_map, List.getElem?_range h]
  rfl

private theorem quarticLeaves_getElem?_a {k x : Nat} (h : x < k + 1) :
    (quarticLeaves k)[2 * (k + 1) + x]? = some (.a x) := by
  rw [quarticLeaves,
    List.getElem?_append_right (by
      simp only [List.length_append, List.length_map, List.length_range,
        List.length_cons, List.length_nil]
      omega)]
  have hidx : 2 * (k + 1) + x -
      ((List.range k).map QuarticLeaf.g ++ [QuarticLeaf.d]).length
        = k + 1 + x := by
    simp only [List.length_append, List.length_map, List.length_range,
      List.length_cons, List.length_nil]
    omega
  rw [hidx,
    List.getElem?_append_right (by
      simp only [List.length_map, List.length_range]
      omega)]
  have hidx' : k + 1 + x - ((List.range (k + 1)).map QuarticLeaf.b).length
      = x := by
    simp only [List.length_map, List.length_range]
    omega
  rw [hidx', List.getElem?_map, List.getElem?_range h]
  rfl

/-- Positional inversion: the leaf at each in-range position, block by
block. -/
private theorem quarticLeaves_inv {k i : Nat} {l : QuarticLeaf}
    (hi : (quarticLeaves k)[i]? = some l) :
    (i < k ∧ l = .g i) ∨ (i = k ∧ l = .d) ∨
      (k + 1 ≤ i ∧ i < 2 * (k + 1) ∧ l = .b (i - (k + 1))) ∨
      (2 * (k + 1) ≤ i ∧ i < 3 * (k + 1) ∧ l = .a (i - 2 * (k + 1))) := by
  have hlt : i < (quarticLeaves k).length := Support.lt_of_getElem?_some hi
  rw [quarticLeaves_length] at hlt
  rcases Nat.lt_or_ge i k with h1 | h1
  · left
    exact ⟨h1, (Option.some.inj
      ((quarticLeaves_getElem?_g h1).symm.trans hi)).symm⟩
  · rcases Nat.lt_or_ge i (k + 1) with h2 | h2
    · have hik : i = k := by omega
      refine Or.inr (Or.inl ⟨hik, ?_⟩)
      rw [hik] at hi
      exact (Option.some.inj
        ((quarticLeaves_getElem?_d k).symm.trans hi)).symm
    · rcases Nat.lt_or_ge i (2 * (k + 1)) with h3 | h3
      · refine Or.inr (Or.inr (Or.inl ⟨h2, h3, ?_⟩))
        obtain ⟨x, rfl⟩ : ∃ x, i = k + 1 + x := ⟨i - (k + 1), by omega⟩
        have hx : x < k + 1 := by omega
        have hlx := (Option.some.inj
          ((quarticLeaves_getElem?_b hx).symm.trans hi)).symm
        rw [hlx]
        congr 1
        omega
      · refine Or.inr (Or.inr (Or.inr ⟨h3, hlt, ?_⟩))
        obtain ⟨x, rfl⟩ : ∃ x, i = 2 * (k + 1) + x := ⟨i - 2 * (k + 1), by omega⟩
        have hx : x < k + 1 := by omega
        have hlx := (Option.some.inj
          ((quarticLeaves_getElem?_a hx).symm.trans hi)).symm
        rw [hlx]
        congr 1
        omega

private theorem index_of_d {k i : Nat}
    (hi : (quarticLeaves k)[i]? = some .d) : i = k := by
  rcases quarticLeaves_inv hi with ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
  · exact absurd h (by simp)
  · exact h
  · exact absurd h (by simp)
  · exact absurd h (by simp)

private theorem index_of_b {k i x : Nat}
    (hi : (quarticLeaves k)[i]? = some (.b x)) :
    k + 1 ≤ i ∧ i < 2 * (k + 1) := by
  rcases quarticLeaves_inv hi with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h1, h2, -⟩ | ⟨-, -, h⟩
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact ⟨h1, h2⟩
  · exact absurd h (by simp)

private theorem index_of_a {k i x : Nat}
    (hi : (quarticLeaves k)[i]? = some (.a x)) :
    2 * (k + 1) ≤ i ∧ i < 3 * (k + 1) := by
  rcases quarticLeaves_inv hi with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨h1, h2, -⟩
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact ⟨h1, h2⟩

private theorem mem_b_bound {k x : Nat}
    (h : QuarticLeaf.b x ∈ quarticLeaves k) : x < k + 1 := by
  rw [List.mem_iff_getElem?] at h
  obtain ⟨i, hi⟩ := h
  rcases quarticLeaves_inv hi with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨h1, h2, h'⟩ | ⟨-, -, h'⟩
  · exact absurd h' (by simp)
  · exact absurd h' (by simp)
  · have hx : x = i - (k + 1) := by injection h'
    omega
  · exact absurd h' (by simp)

private theorem mem_a_bound {k x : Nat}
    (h : QuarticLeaf.a x ∈ quarticLeaves k) : x < k + 1 := by
  rw [List.mem_iff_getElem?] at h
  obtain ⟨i, hi⟩ := h
  rcases quarticLeaves_inv hi with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, -, h'⟩ | ⟨h1, h2, h'⟩
  · exact absurd h' (by simp)
  · exact absurd h' (by simp)
  · exact absurd h' (by simp)
  · have hx : x = i - 2 * (k + 1) := by injection h'
    omega

/-! ## The Γ table lookup spec and ground coverage -/

private theorem quarticTable_keys_nodup (k : Nat) :
    ((quarticTable k).map Prod.fst).Nodup := by
  rw [quarticTable, List.map_map]
  exact nodup_map_of_injective QuarticLeaf.encode_inj (quarticLeaves_nodup k)

theorem quarticGamma_encode {k : Nat} {l : QuarticLeaf}
    (h : l ∈ quarticLeaves k) :
    quarticGamma k l.encode = some l.atom :=
  lookupLeaf_eq_some_of_nodup (quarticTable_keys_nodup k)
    (List.mem_map.mpr ⟨l, h, rfl⟩)

/-- `quarticGround` is the `Prod.snd` projection of the table `quarticGamma`
reads, so every successful lookup's atom is a ground member. -/
theorem quarticGround_covers (k : Nat) :
    Realizability.GroundCoversUsedLeaves (quarticGamma k) (quarticGround k)
      (quarticRaw k).args := by
  intro w _ l _ p hlookup
  exact lookupLeaf_mem_snd hlookup

/-! ## The checker premises: Nodup, sorts, support -/

private theorem quarticArgs_nodup (k : Nat) : (quarticArgs k).Nodup :=
  nodup_map_of_injective leafArg_injective (quarticLeaves_nodup k)

private theorem quarticGround_eq (k : Nat) :
    quarticGround k = (quarticLeaves k).map QuarticLeaf.atom := by
  rw [quarticGround, quarticTable, List.map_map]
  rfl

private theorem quarticGround_wellSorted (k : Nat) :
    Lara.groundWellSorted m2bSigma (quarticGround k) = true := by
  rw [Lara.groundWellSorted, List.all_eq_true, quarticGround_eq]
  intro a ha
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha
  cases l <;> rfl

private theorem termsWellSorted_eq_all (l : List SupportTerm) :
    Lara.termsWellSorted m2bSigma m2bPolicy l =
      l.all (Lara.termWellSorted m2bSigma m2bPolicy) := by
  induction l with
  | nil => rfl
  | cons w ws ih => rw [Lara.termsWellSorted, List.all_cons, ih]

private theorem quarticArgs_wellSorted (k : Nat) :
    Lara.argsWellSorted m2bSigma m2bPolicy (quarticArgs k) = true := by
  rw [Lara.argsWellSorted, termsWellSorted_eq_all, List.all_eq_true]
  intro w hw
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hw
  rfl

private theorem quartic_signatureStage (k : Nat) :
    Check.Unit.signatureStage (quarticGround k) (quarticRaw k) = none := by
  unfold Check.Unit.signatureStage
  rw [show (quarticRaw k).sigma = m2bSigma from rfl,
    show (quarticRaw k).policy = m2bPolicy from rfl,
    show (quarticRaw k).args = quarticArgs k from rfl]
  simp [m2bSigma_wellFormed, m2bPolicy_wellSorted, quarticGround_wellSorted,
    quarticArgs_wellSorted]

private theorem quartic_supported (k : Nat) :
    ∀ w ∈ (quarticRaw k).args, ∃ C,
      Support.HasSupport id m2bPolicy.ruleLookup (quarticGamma k)
        (Support.certOkOf m2bRegistry) w C [] := by
  intro w hw
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hw
  exact ⟨l.atom, .leaf (quarticGamma_encode hl)⟩

/-! ## The checker premises: typed attacks and endpoint membership -/

/-- The `d → b(X)` schema row fires at any payload (`X` is bound once, on the
target side only). -/
theorem contraryMatch_d_b (x : Nat) :
    ContraryMatch id m2bPolicy.defeat dAtom (bAtom x) :=
  ⟨(⟨⟨"d"⟩, .nil⟩, ⟨⟨"b"⟩, .cons (.var ⟨"X"⟩) .nil⟩),
    List.mem_cons_self,
    [(⟨"X"⟩, numTerm x)], dAtom, bAtom x, rfl, rfl, rfl, rfl⟩

/-- The `b(X) → a(Y)` schema row fires at any pair of payloads — the two
variables are independent, so every `b` is contrary to every `a`. -/
theorem contraryMatch_b_a (x y : Nat) :
    ContraryMatch id m2bPolicy.defeat (bAtom x) (aAtom y) :=
  ⟨(⟨⟨"b"⟩, .cons (.var ⟨"X"⟩) .nil⟩, ⟨⟨"a"⟩, .cons (.var ⟨"Y"⟩) .nil⟩),
    List.mem_cons_of_mem _ List.mem_cons_self,
    [(⟨"X"⟩, numTerm x), (⟨"Y"⟩, numTerm y)], bAtom x, aAtom y,
    rfl, rfl, rfl, rfl⟩

private theorem hasAttack_d_b {k x : Nat} (hx : x < k + 1) :
    HasAttack id m2bPolicy.ruleLookup (quarticGamma k)
      (Support.certOkOf m2bRegistry) m2bPolicy.defeat
      (.undermine (leafArg .d) (leafArg (.b x)) []) :=
  .undermine (.leaf (quarticGamma_encode (d_mem k))) rfl
    (quarticGamma_encode (b_mem hx)) (contraryMatch_d_b x)

private theorem hasAttack_b_a {k x y : Nat} (hx : x < k + 1) (hy : y < k + 1) :
    HasAttack id m2bPolicy.ruleLookup (quarticGamma k)
      (Support.certOkOf m2bRegistry) m2bPolicy.defeat
      (.undermine (leafArg (.b x)) (leafArg (.a y)) []) :=
  .undermine (.leaf (quarticGamma_encode (b_mem hx))) rfl
    (quarticGamma_encode (a_mem hy)) (contraryMatch_b_a x y)

private theorem mem_quarticAtts {k : Nat} {att : Attack}
    (h : att ∈ quarticAtts k) :
    (∃ x, x < k + 1 ∧ att = .undermine (leafArg .d) (leafArg (.b x)) []) ∨
      (∃ x y, x < k + 1 ∧ y < k + 1 ∧
        att = .undermine (leafArg (.b x)) (leafArg (.a y)) []) := by
  rcases List.mem_append.mp h with h1 | h2
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h1
    exact Or.inl ⟨x, List.mem_range.mp hx, rfl⟩
  · obtain ⟨x, hx, hmem⟩ := List.mem_flatMap.mp h2
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hmem
    exact Or.inr ⟨x, y, List.mem_range.mp hx, List.mem_range.mp hy, rfl⟩

private theorem d_b_attack_mem {k x : Nat} (hx : x < k + 1) :
    (Attack.undermine (leafArg .d) (leafArg (.b x)) []) ∈ quarticAtts k :=
  List.mem_append_left _ (List.mem_map.mpr ⟨x, List.mem_range.mpr hx, rfl⟩)

private theorem b_a_attack_mem {k x y : Nat} (hx : x < k + 1)
    (hy : y < k + 1) :
    (Attack.undermine (leafArg (.b x)) (leafArg (.a y)) []) ∈ quarticAtts k :=
  List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨x, List.mem_range.mpr hx,
      List.mem_map.mpr ⟨y, List.mem_range.mpr hy, rfl⟩⟩)

private theorem quarticAtts_typed (k : Nat) :
    ∀ att ∈ (quarticRaw k).atts,
      HasAttack id m2bPolicy.ruleLookup (quarticGamma k)
        (Support.certOkOf m2bRegistry) m2bPolicy.defeat att := by
  intro att hatt
  rcases mem_quarticAtts hatt with ⟨x, hx, rfl⟩ | ⟨x, y, hx, hy, rfl⟩
  · exact hasAttack_d_b hx
  · exact hasAttack_b_a hx hy

private theorem quarticAtts_source_mem (k : Nat) :
    ∀ att ∈ (quarticRaw k).atts, att.source ∈ (quarticRaw k).args := by
  intro att hatt
  rcases mem_quarticAtts hatt with ⟨x, hx, rfl⟩ | ⟨x, y, hx, hy, rfl⟩
  · exact List.mem_map.mpr ⟨.d, d_mem k, rfl⟩
  · exact List.mem_map.mpr ⟨.b x, b_mem hx, rfl⟩

private theorem quarticAtts_target_mem (k : Nat) :
    ∀ att ∈ (quarticRaw k).atts, att.target ∈ (quarticRaw k).args := by
  intro att hatt
  rcases mem_quarticAtts hatt with ⟨x, hx, rfl⟩ | ⟨x, y, hx, hy, rfl⟩
  · exact List.mem_map.mpr ⟨.b x, b_mem hx, rfl⟩
  · exact List.mem_map.mpr ⟨.a y, a_mem hy, rfl⟩

/-! ## Attack completeness

`ContraryMatch` over the witness's root conclusions is exactly the two
declared families: the `g` predicate keys no contrary row, `d → b(X)` binds
its variable on the target side only, and `b(X) → a(Y)` has independent
variables.  The four `lit`/`occ`/`clause`/`query` rows miss every witness
predicate head.  Unlike the gadget's characterization, no numeral
injectivity is needed here: no schema row binds a variable on both sides. -/

mutual
  private theorem nfTerm_id (t : Lara.Term) : nfTerm id t = t := by
    match t with
    | .num s => simp [nfTerm]
    | .str _ => simp [nfTerm]
    | .con k ts => simp [nfTerm, nfTerms_id ts]
  private theorem nfTerms_id (ts : Lara.Terms) : nfTerms id ts = ts := by
    match ts with
    | .nil => simp [nfTerms]
    | .cons t rest => simp [nfTerms, nfTerm_id t, nfTerms_id rest]
end

private theorem equiv_id_eq {a b : Lara.Atom} (h : equiv id a b) : a = b := by
  have h' : nf id a = nf id b := h
  cases a with
  | atom p ts =>
    cases b with
    | atom p' ts' =>
      simpa [nf, nfTerms_id] using h'

private theorem gAtom_eq (i : Nat) :
    gAtom i = .atom "g" (.cons (.num (Nat.repr i)) .nil) := rfl

private theorem dAtom_eq : dAtom = .atom "d" .nil := rfl

private theorem bAtom_eq (i : Nat) :
    bAtom i = .atom "b" (.cons (.num (Nat.repr i)) .nil) := rfl

private theorem aAtom_eq (i : Nat) :
    aAtom i = .atom "a" (.cons (.num (Nat.repr i)) .nil) := rfl

/-- The six contrary rows of the fixed policy, re-spelled literally (a drift
in `Lara.Complexity.Context` breaks this `rfl` at compile time). -/
private theorem m2bDefeat_contraries :
    m2bPolicy.defeat.contraries =
      [ (⟨⟨"d"⟩, .nil⟩, ⟨⟨"b"⟩, .cons (.var ⟨"X"⟩) .nil⟩)
      , (⟨⟨"b"⟩, .cons (.var ⟨"X"⟩) .nil⟩, ⟨⟨"a"⟩, .cons (.var ⟨"Y"⟩) .nil⟩)
      , (⟨⟨"lit"⟩, .cons (.num "0") (.cons (.var ⟨"X"⟩) .nil)⟩,
          ⟨⟨"lit"⟩, .cons (.num "1") (.cons (.var ⟨"X"⟩) .nil)⟩)
      , (⟨⟨"lit"⟩, .cons (.num "1") (.cons (.var ⟨"X"⟩) .nil)⟩,
          ⟨⟨"lit"⟩, .cons (.num "0") (.cons (.var ⟨"X"⟩) .nil)⟩)
      , (⟨⟨"lit"⟩, .cons (.var ⟨"S"⟩) (.cons (.var ⟨"X"⟩) .nil)⟩,
          ⟨⟨"occ"⟩, .cons (.var ⟨"S"⟩) (.cons (.var ⟨"X"⟩) .nil)⟩)
      , (⟨⟨"clause"⟩, .cons (.var ⟨"J"⟩) .nil⟩, ⟨⟨"query"⟩, .nil⟩) ] := rfl

private theorem instAPat_head {θ : Subst} {pn : String} {ps : Pats}
    {a : Lara.Atom} (h : instAPat θ ⟨⟨pn⟩, ps⟩ = some a) :
    ∃ ts, a = .atom pn ts := by
  simp only [instAPat] at h
  cases hts : instPats θ ps with
  | none => rw [hts] at h; exact nomatch h
  | some ts => rw [hts] at h; exact ⟨ts, (Option.some.inj h).symm⟩

/-- The root conclusions of the witness arguments. -/
private def QRoot (a : Lara.Atom) : Prop :=
  (∃ i, a = gAtom i) ∨ a = dAtom ∨ (∃ i, a = bAtom i) ∨ (∃ i, a = aAtom i)

private theorem qroot_atom (l : QuarticLeaf) : QRoot l.atom := by
  cases l with
  | g i => exact Or.inl ⟨i, rfl⟩
  | d => exact Or.inr (Or.inl rfl)
  | b i => exact Or.inr (Or.inr (Or.inl ⟨i, rfl⟩))
  | a i => exact Or.inr (Or.inr (Or.inr ⟨i, rfl⟩))

/-- **`ContraryMatch` over witness root conclusions, forward direction.**
Between witness root conclusions only the two declared families fire. -/
private theorem contraryMatch_qroot {p q : Lara.Atom}
    (hp : QRoot p) (hq : QRoot q)
    (h : ContraryMatch id m2bPolicy.defeat p q) :
    (p = dAtom ∧ ∃ x, q = bAtom x) ∨
      ((∃ x, p = bAtom x) ∧ ∃ y, q = aAtom y) := by
  obtain ⟨ab, hab, ρ, pa, pb, hpa, hpb, hep, heq⟩ := h
  rw [equiv_id_eq hep] at hpa
  rw [equiv_id_eq heq] at hpb
  rw [m2bDefeat_contraries] at hab
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with rfl | rfl | rfl | rfl | rfl | rfl
  · -- `d → b(X)`
    obtain ⟨ts, rfl⟩ := instAPat_head hpa
    rcases hp with ⟨i, hpv⟩ | hpv | ⟨i, hpv⟩ | ⟨i, hpv⟩
    · simp [gAtom_eq] at hpv
    · obtain ⟨ts', rfl⟩ := instAPat_head hpb
      rcases hq with ⟨i', hqv⟩ | hqv | ⟨i', hqv⟩ | ⟨i', hqv⟩
      · simp [gAtom_eq] at hqv
      · simp [dAtom_eq] at hqv
      · exact Or.inl ⟨hpv, i', hqv⟩
      · simp [aAtom_eq] at hqv
    · simp [bAtom_eq] at hpv
    · simp [aAtom_eq] at hpv
  · -- `b(X) → a(Y)`
    obtain ⟨ts, rfl⟩ := instAPat_head hpa
    rcases hp with ⟨i, hpv⟩ | hpv | ⟨i, hpv⟩ | ⟨i, hpv⟩
    · simp [gAtom_eq] at hpv
    · simp [dAtom_eq] at hpv
    · obtain ⟨ts', rfl⟩ := instAPat_head hpb
      rcases hq with ⟨i', hqv⟩ | hqv | ⟨i', hqv⟩ | ⟨i', hqv⟩
      · simp [gAtom_eq] at hqv
      · simp [dAtom_eq] at hqv
      · simp [bAtom_eq] at hqv
      · exact Or.inr ⟨⟨i, hpv⟩, i', hqv⟩
    · simp [aAtom_eq] at hpv
  · -- `lit(0,X) → lit(1,X)`: the head `lit` is not a witness predicate
    obtain ⟨ts, rfl⟩ := instAPat_head hpa
    rcases hp with ⟨i, hpv⟩ | hpv | ⟨i, hpv⟩ | ⟨i, hpv⟩ <;>
      simp [gAtom_eq, dAtom_eq, bAtom_eq, aAtom_eq] at hpv
  · -- `lit(1,X) → lit(0,X)`
    obtain ⟨ts, rfl⟩ := instAPat_head hpa
    rcases hp with ⟨i, hpv⟩ | hpv | ⟨i, hpv⟩ | ⟨i, hpv⟩ <;>
      simp [gAtom_eq, dAtom_eq, bAtom_eq, aAtom_eq] at hpv
  · -- `lit(S,X) → occ(S,X)`
    obtain ⟨ts, rfl⟩ := instAPat_head hpa
    rcases hp with ⟨i, hpv⟩ | hpv | ⟨i, hpv⟩ | ⟨i, hpv⟩ <;>
      simp [gAtom_eq, dAtom_eq, bAtom_eq, aAtom_eq] at hpv
  · -- `clause(J) → query`
    obtain ⟨ts, rfl⟩ := instAPat_head hpa
    rcases hp with ⟨i, hpv⟩ | hpv | ⟨i, hpv⟩ | ⟨i, hpv⟩ <;>
      simp [gAtom_eq, dAtom_eq, bAtom_eq, aAtom_eq] at hpv

private theorem atom_inv_d {l : QuarticLeaf} (h : l.atom = dAtom) :
    l = .d := by
  cases l with
  | g i => exact absurd h (by simp [QuarticLeaf.atom, gAtom_eq, dAtom_eq])
  | d => rfl
  | b i => exact absurd h (by simp [QuarticLeaf.atom, bAtom_eq, dAtom_eq])
  | a i => exact absurd h (by simp [QuarticLeaf.atom, aAtom_eq, dAtom_eq])

private theorem atom_inv_b {l : QuarticLeaf} {x : Nat}
    (h : l.atom = bAtom x) : ∃ i, l = .b i := by
  cases l with
  | g i => exact absurd h (by simp [QuarticLeaf.atom, gAtom_eq, bAtom_eq])
  | d => exact absurd h (by simp [QuarticLeaf.atom, dAtom_eq, bAtom_eq])
  | b i => exact ⟨i, rfl⟩
  | a i => exact absurd h (by simp [QuarticLeaf.atom, aAtom_eq, bAtom_eq])

private theorem atom_inv_a {l : QuarticLeaf} {x : Nat}
    (h : l.atom = aAtom x) : ∃ i, l = .a i := by
  cases l with
  | g i => exact absurd h (by simp [QuarticLeaf.atom, gAtom_eq, aAtom_eq])
  | d => exact absurd h (by simp [QuarticLeaf.atom, dAtom_eq, aAtom_eq])
  | b i => exact absurd h (by simp [QuarticLeaf.atom, bAtom_eq, aAtom_eq])
  | a i => exact ⟨i, rfl⟩

/-- Root-conclusion determination: every supported witness argument is a
declared leaf whose conclusion is its Γ entry. -/
private theorem quartic_conclusion {k : Nat} {w : SupportTerm}
    {C : Lara.Atom} (hw : w ∈ (quarticRaw k).args)
    (hs : Support.HasSupport id m2bPolicy.ruleLookup (quarticGamma k)
      (Support.certOkOf m2bRegistry) w C []) :
    ∃ l, l ∈ quarticLeaves k ∧ w = leafArg l ∧ C = l.atom := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hw
  have hs' : Support.HasSupport id m2bPolicy.ruleLookup (quarticGamma k)
      (Support.certOkOf m2bRegistry) (.leaf l.encode) C [] := hs
  cases hs' with
  | leaf hΓ =>
      exact ⟨l, hl, rfl,
        (Option.some.inj ((quarticGamma_encode hl).symm.trans hΓ)).symm⟩

private theorem quartic_attackComplete (k : Nat) :
    Compile.AttackComplete id m2bPolicy.ruleLookup (quarticGamma k)
      (Support.certOkOf m2bRegistry) m2bPolicy.defeat
      (quarticRaw k).args (quarticRaw k).atts := by
  intro source hsource target htarget Cs Ct hsupS hsupT hcon _hattackable
  obtain ⟨ls, hls, rfl, rfl⟩ := quartic_conclusion hsource hsupS
  obtain ⟨lt, hlt, rfl, rfl⟩ := quartic_conclusion htarget hsupT
  rcases contraryMatch_qroot (qroot_atom ls) (qroot_atom lt) hcon with
    ⟨hd, x, hb⟩ | ⟨⟨x, hb⟩, y, ha⟩
  · have hls' : ls = .d := atom_inv_d hd
    obtain ⟨i, hlt'⟩ := atom_inv_b hb
    subst hls'
    subst hlt'
    exact ⟨.undermine (leafArg .d) (leafArg (.b i)) [],
      d_b_attack_mem (mem_b_bound hlt), rfl,
      leafArg (.b i), rfl, Compile.contains_refl _⟩
  · obtain ⟨i, hls'⟩ := atom_inv_b hb
    obtain ⟨j, hlt'⟩ := atom_inv_a ha
    subst hls'
    subst hlt'
    exact ⟨.undermine (leafArg (.b i)) (leafArg (.a j)) [],
      b_a_attack_mem (mem_b_bound hls) (mem_a_bound hlt), rfl,
      leafArg (.a j), rfl, Compile.contains_refl _⟩

/-! ## The checker equation -/

/-- Assembled acceptance: the ten discharged premises, in the checker's
public fixed order — the same assembly as `checkUnit_formula_accepts`, with
leaf-only support. -/
theorem quartic_checkUnit_accepts (k : Nat) :
    ∃ accepted, Check.Unit.checkUnit (quarticGamma k) m2bRegistry
      (quarticGround k) (quarticRaw k) = .ok accepted :=
  Check.Unit.checkUnit_complete
    (quartic_signatureStage k)
    m2bPolicy_scopesWellFormed
    ((Policy.firstDuplicateRuleId?_none_iff m2bPolicy.rules).mp
      m2bPolicy_ruleIds_unique)
    ((Policy.firstViolation_none_iff).mp m2bPolicy_noViolation)
    (quarticArgs_nodup k)
    (quartic_supported k)
    (quarticAtts_typed k)
    (quarticAtts_source_mem k)
    (quarticAtts_target_mem k)
    (quartic_attackComplete k)

/-- The accepted checker output, named once for the whole family. -/
def quarticAccepted (k : Nat) :
    Lara.Unit.CheckedUnit id (quarticGamma k) (Support.certOkOf m2bRegistry) :=
  (Check.Unit.checkUnit (quarticGamma k) m2bRegistry
    (quarticGround k) (quarticRaw k)).toOption.get
    (by
      obtain ⟨accepted, h⟩ := quartic_checkUnit_accepts k
      simp [h, Except.toOption])

/-- **The family-wide checker equation** for the quartic witness. -/
theorem quartic_checkUnit_ok (k : Nat) :
    Check.Unit.checkUnit (quarticGamma k) m2bRegistry
      (quarticGround k) (quarticRaw k) = .ok (quarticAccepted k) := by
  obtain ⟨accepted, h⟩ := quartic_checkUnit_accepts k
  have hoption : (Check.Unit.checkUnit (quarticGamma k) m2bRegistry
      (quarticGround k) (quarticRaw k)).toOption = some accepted :=
    congrArg Except.toOption h
  have haccepted : quarticAccepted k = accepted := by
    unfold quarticAccepted
    apply Option.get_of_eq_some
    exact hoption
  rw [haccepted]
  exact h

/-! ## The compilation image -/

private theorem quartic_compile_nodes (k : Nat) :
    (Invariants.compileUnit (quarticAccepted k)).nodes
      = (quarticLeaves k).map QuarticLeaf.atom := by
  have hsound := Check.Unit.checkUnit_sound (quartic_checkUnit_ok k)
  have hpol : (quarticAccepted k).policy = m2bPolicy :=
    hsound.2.2.2.2.2.1
  have hterms : (quarticAccepted k).nodes.map (·.term) = quarticArgs k := by
    rw [(quarticAccepted k).nodes_terms]
    exact hsound.2.2.2.2.2.2.2.2.1
  show (quarticAccepted k).nodes.map (·.conclusion) = _
  have hlen : (quarticAccepted k).nodes.length = (quarticLeaves k).length := by
    have h := congrArg List.length hterms
    simpa [quarticArgs] using h
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, List.getElem?_map]
  cases hnode : (quarticAccepted k).nodes[i]? with
  | none =>
      have hi : (quarticLeaves k).length ≤ i := by
        rw [← hlen]
        exact List.getElem?_eq_none_iff.mp hnode
      rw [List.getElem?_eq_none hi]
      rfl
  | some node =>
      have hi : i < (quarticLeaves k).length := by
        rw [← hlen]
        exact Support.lt_of_getElem?_some hnode
      obtain ⟨l, hl⟩ := Support.getElem?_some_of_lt (quarticLeaves k) i hi
      rw [hl]
      have hterm : node.term = leafArg l := by
        have h := congrArg (fun s => s[i]?) hterms
        simp only [List.getElem?_map, hnode, Option.map_some] at h
        rw [quarticArgs, List.getElem?_map, hl] at h
        exact Option.some.inj h
      have hvalid : Support.HasSupport id m2bPolicy.ruleLookup
          (quarticGamma k) (Support.certOkOf m2bRegistry)
          node.term node.conclusion [] := by
        simpa only [hpol] using node.valid
      rw [hterm] at hvalid
      have hvalid' : Support.HasSupport id m2bPolicy.ruleLookup
          (quarticGamma k) (Support.certOkOf m2bRegistry)
          (.leaf l.encode) node.conclusion [] := hvalid
      cases hvalid' with
      | leaf hΓ =>
          have hcon : l.atom = node.conclusion :=
            Option.some.inj
              ((quarticGamma_encode (List.mem_of_getElem? hl)).symm.trans hΓ)
          simp [hcon]

private theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) :
    a = b := by
  cases a <;> cases b <;> simp_all

/-- The attacked occurrence of a root undermine of a leaf is that leaf, so
its closure test on another leaf is bare equality — a leaf contains only
itself (leaf-only support makes positional closure trivial). -/
private theorem attackClosureB_leaf (w : SupportTerm) (l l' : QuarticLeaf) :
    Compile.attackClosureB (.undermine w (leafArg l) []) (leafArg l')
      = decide (l' = l) := by
  have h1 : Compile.attackClosureB (.undermine w (leafArg l) []) (leafArg l')
      = decide (leafArg l' = leafArg l) := rfl
  rw [h1]
  by_cases h : l' = l
  · subst h
    simp
  · rw [decide_eq_false (fun heq => h (leafArg_inj heq)), decide_eq_false h]

/-- The compiled closure-edge scan over the witness's declared attacks is
exactly the intended arithmetic edge relation, position by position. -/
private theorem coveredB_quartic {k i j : Nat} {li lj : QuarticLeaf}
    (hi : (quarticLeaves k)[i]? = some li)
    (hj : (quarticLeaves k)[j]? = some lj) :
    Compile.coveredB (quarticAtts k) (leafArg li) (leafArg lj)
      = quarticAttack k i j := by
  apply bool_eq_of_iff
  rw [quarticAttack_eq_true_iff]
  constructor
  · intro hcov
    rw [Compile.coveredB, List.any_eq_true] at hcov
    obtain ⟨att, hmem, hpred⟩ := hcov
    rw [Bool.and_eq_true, decide_eq_true_eq] at hpred
    obtain ⟨hsrc, hclosure⟩ := hpred
    rcases mem_quarticAtts hmem with ⟨x, hx, rfl⟩ | ⟨x, y, hx, hy, rfl⟩
    · have hli : li = .d := (leafArg_inj hsrc).symm
      rw [attackClosureB_leaf] at hclosure
      have hlj : lj = .b x := of_decide_eq_true hclosure
      subst hli
      subst hlj
      have hik := index_of_d hi
      have hjb := index_of_b hj
      exact Or.inl ⟨hik, hjb.1, hjb.2⟩
    · have hli : li = .b x := (leafArg_inj hsrc).symm
      rw [attackClosureB_leaf] at hclosure
      have hlj : lj = .a y := of_decide_eq_true hclosure
      subst hli
      subst hlj
      have hib := index_of_b hi
      have hja := index_of_a hj
      exact Or.inr ⟨hib.1, hib.2, hja.1, hja.2⟩
  · intro h
    rw [Compile.coveredB, List.any_eq_true]
    rcases h with ⟨hik, hj1, hj2⟩ | ⟨hi1, hi2, hj1, hj2⟩
    · subst hik
      have hli : li = .d := by
        rcases quarticLeaves_inv hi with
          ⟨h', rfl⟩ | ⟨-, rfl⟩ | ⟨h', -, rfl⟩ | ⟨h', -, rfl⟩
        · omega
        · rfl
        · omega
        · omega
      have hlj : lj = .b (j - (i + 1)) := by
        rcases quarticLeaves_inv hj with
          ⟨h', rfl⟩ | ⟨h', rfl⟩ | ⟨-, -, rfl⟩ | ⟨h', -, rfl⟩
        · omega
        · omega
        · rfl
        · omega
      subst hli
      subst hlj
      refine ⟨.undermine (leafArg .d) (leafArg (.b (j - (i + 1)))) [],
        d_b_attack_mem (by omega), ?_⟩
      rw [Bool.and_eq_true, decide_eq_true_eq, attackClosureB_leaf]
      exact ⟨rfl, decide_eq_true rfl⟩
    · have hli : li = .b (i - (k + 1)) := by
        rcases quarticLeaves_inv hi with
          ⟨h', rfl⟩ | ⟨h', rfl⟩ | ⟨-, -, rfl⟩ | ⟨h', -, rfl⟩
        · omega
        · omega
        · rfl
        · omega
      have hlj : lj = .a (j - 2 * (k + 1)) := by
        rcases quarticLeaves_inv hj with
          ⟨h', rfl⟩ | ⟨h', rfl⟩ | ⟨h', h'', rfl⟩ | ⟨-, -, rfl⟩
        · omega
        · omega
        · omega
        · rfl
      subst hli
      subst hlj
      refine ⟨.undermine (leafArg (.b (i - (k + 1))))
          (leafArg (.a (j - 2 * (k + 1)))) [],
        b_a_attack_mem (by omega) (by omega), ?_⟩
      rw [Bool.and_eq_true, decide_eq_true_eq, attackClosureB_leaf]
      exact ⟨rfl, decide_eq_true rfl⟩

private theorem quartic_compile_attack (k : Nat) (i j : Nat) :
    (Invariants.compileUnit (quarticAccepted k)).attack i j
      = quarticAttack k i j := by
  have hsound := Check.Unit.checkUnit_sound (quartic_checkUnit_ok k)
  have hargs : (quarticAccepted k).program.args = quarticArgs k :=
    hsound.2.2.2.2.2.2.2.2.1
  have hatts : (quarticAccepted k).program.atts = quarticAtts k :=
    hsound.2.2.2.2.2.2.2.2.2.1
  show Compile.edgeB (quarticAccepted k).program i j = _
  unfold Compile.edgeB
  rw [hargs, hatts, quarticArgs]
  cases hgi : (quarticLeaves k)[i]? with
  | none =>
      have hli : 3 * (k + 1) ≤ i := by
        have h := List.getElem?_eq_none_iff.mp hgi
        rw [quarticLeaves_length] at h
        exact h
      rw [List.getElem?_map, hgi, quarticAttack_false (by omega)]
      rfl
  | some li =>
      cases hgj : (quarticLeaves k)[j]? with
      | none =>
          have hlj : 3 * (k + 1) ≤ j := by
            have h := List.getElem?_eq_none_iff.mp hgj
            rw [quarticLeaves_length] at h
            exact h
          rw [List.getElem?_map, List.getElem?_map, hgi, hgj,
            quarticAttack_false (by omega)]
          rfl
      | some lj =>
          rw [List.getElem?_map, List.getElem?_map, hgi, hgj]
          show Compile.coveredB (quarticAtts k) (leafArg li) (leafArg lj) = _
          exact coveredB_quartic hgi hgj

/-- **The compilation image**: the structured compilation of the accepted
witness unit is exactly `quarticAF (k + 1)`, at the identity position
reindexing — same conclusion labels, exactly the intended edges, no
closure-generated extras (a leaf contains only itself). -/
def quarticIso (k : Nat) :
    Realizability.StructuredAFIso
      (Invariants.compileUnit (quarticAccepted k)) (quarticAF (k + 1)) where
  nodeEquiv := Realizability.Equiv.refl Nat
  labels := by
    intro i
    rw [show (quarticAF (k + 1)).nodes
        = (quarticLeaves k).map QuarticLeaf.atom from rfl,
      quartic_compile_nodes k]
    simp [Realizability.Equiv.refl]
  attacks := by
    intro i j
    have h := quartic_compile_attack k i j
    simp only [Realizability.Equiv.refl]
    exact h

/-! ## The empty witness (`quarticAF 0`) -/

/-- The empty raw unit under the fixed context. -/
def quarticEmptyRaw : Lara.Unit :=
  { sigma := m2bSigma, policy := m2bPolicy, args := [], atts := [] }

private theorem quarticEmpty_signatureStage :
    Check.Unit.signatureStage [] quarticEmptyRaw = none := by
  unfold Check.Unit.signatureStage
  rw [show quarticEmptyRaw.sigma = m2bSigma from rfl,
    show quarticEmptyRaw.policy = m2bPolicy from rfl,
    show quarticEmptyRaw.args = ([] : List SupportTerm) from rfl]
  simp [m2bSigma_wellFormed, m2bPolicy_wellSorted, Lara.groundWellSorted,
    Lara.argsWellSorted, Lara.termsWellSorted]

theorem quarticEmpty_accepts :
    ∃ accepted, Check.Unit.checkUnit (fun _ => none) m2bRegistry []
      quarticEmptyRaw = .ok accepted :=
  Check.Unit.checkUnit_complete
    quarticEmpty_signatureStage
    m2bPolicy_scopesWellFormed
    ((Policy.firstDuplicateRuleId?_none_iff m2bPolicy.rules).mp
      m2bPolicy_ruleIds_unique)
    ((Policy.firstViolation_none_iff).mp m2bPolicy_noViolation)
    List.nodup_nil
    (fun _ hw => nomatch hw)
    (fun _ ha => nomatch ha)
    (fun _ ha => nomatch ha)
    (fun _ ha => nomatch ha)
    (fun _ hsource => nomatch hsource)

/-- The accepted empty unit. -/
def quarticEmptyAccepted :
    Lara.Unit.CheckedUnit id (fun _ => none) (Support.certOkOf m2bRegistry) :=
  (Check.Unit.checkUnit (fun _ => none) m2bRegistry []
    quarticEmptyRaw).toOption.get
    (by
      obtain ⟨accepted, h⟩ := quarticEmpty_accepts
      simp [h, Except.toOption])

theorem quarticEmpty_checkUnit_ok :
    Check.Unit.checkUnit (fun _ => none) m2bRegistry [] quarticEmptyRaw
      = .ok quarticEmptyAccepted := by
  obtain ⟨accepted, h⟩ := quarticEmpty_accepts
  have hoption : (Check.Unit.checkUnit (fun _ => none) m2bRegistry []
      quarticEmptyRaw).toOption = some accepted :=
    congrArg Except.toOption h
  have haccepted : quarticEmptyAccepted = accepted := by
    unfold quarticEmptyAccepted
    apply Option.get_of_eq_some
    exact hoption
  rw [haccepted]
  exact h

private theorem quarticEmpty_nodes : quarticEmptyAccepted.nodes = [] := by
  have hargs : quarticEmptyAccepted.program.args = ([] : List SupportTerm) :=
    (Check.Unit.checkUnit_sound quarticEmpty_checkUnit_ok).2.2.2.2.2.2.2.2.1
  have hterms := quarticEmptyAccepted.nodes_terms
  rw [hargs] at hterms
  exact List.map_eq_nil_iff.mp hterms

/-- The empty compilation image is the empty carrier. -/
def quarticEmptyIso :
    Realizability.StructuredAFIso
      (Invariants.compileUnit quarticEmptyAccepted) (quarticAF 0) where
  nodeEquiv := Realizability.Equiv.refl Nat
  labels := by
    intro i
    rw [show (Invariants.compileUnit quarticEmptyAccepted).nodes
        = ([] : List Lara.Atom) from by
      show quarticEmptyAccepted.nodes.map (·.conclusion) = _
      rw [quarticEmpty_nodes]
      rfl]
    simp [Realizability.Equiv.refl, quarticAF]
  attacks := by
    intro i j
    have h : (Invariants.compileUnit quarticEmptyAccepted).attack i j
        = false := by
      show Compile.edgeB quarticEmptyAccepted.program i j = false
      unfold Compile.edgeB
      rw [(Check.Unit.checkUnit_sound
        quarticEmpty_checkUnit_ok).2.2.2.2.2.2.2.2.1]
      rfl
    rw [h]
    simp [Realizability.Equiv.refl, quarticAF]

/-! ## Realizability (statements frozen by the #209 decision record) -/

/-- **The quartic witness is realizable in the fixed M2b context**, for every
`k`: the leaf-only raw unit passes the executable checker, its ground list
covers every used leaf, and its structured compilation is isomorphic to
`quarticAF k` (identity reindexing). -/
theorem quartic_realizable (k : Nat) :
    Realizability.Realizable id m2bSigma m2bPolicy m2bRegistry (quarticAF k) := by
  cases k with
  | zero =>
      exact ⟨{ Gamma := fun _ => none
               ground := []
               raw := quarticEmptyRaw
               accepted := quarticEmptyAccepted
               checked := quarticEmpty_checkUnit_ok
               sigma_eq :=
                 (Check.Unit.checkUnit_sound quarticEmpty_checkUnit_ok).1
               policy_eq :=
                 (Check.Unit.checkUnit_sound
                   quarticEmpty_checkUnit_ok).2.2.2.2.2.1
               ground_covers := fun _ hw => nomatch hw
               compiled_iso := quarticEmptyIso }⟩
  | succ k =>
      exact ⟨{ Gamma := quarticGamma k
               ground := quarticGround k
               raw := quarticRaw k
               accepted := quarticAccepted k
               checked := quartic_checkUnit_ok k
               sigma_eq :=
                 (Check.Unit.checkUnit_sound (quartic_checkUnit_ok k)).1
               policy_eq :=
                 (Check.Unit.checkUnit_sound
                   (quartic_checkUnit_ok k)).2.2.2.2.2.1
               ground_covers := quarticGround_covers k
               compiled_iso := quarticIso k }⟩

/-! ## The erased carrier and its attack arithmetic -/

private theorem quartic_attack_eq (k : Nat) :
    (Invariants.eraseAF (quarticAF (k + 1))).attack = quarticAttack k := rfl

private theorem quartic_args_eq (k : Nat) :
    (Invariants.eraseAF (quarticAF (k + 1))).args = List.range (3 * (k + 1)) := by
  show List.range (quarticAF (k + 1)).size = _
  rw [quartic_size]

private theorem range_three_split (m : Nat) :
    List.range (3 * m) = List.range m ++
      ((List.range m).map (fun x => m + x) ++
        (List.range m).map (fun x => 2 * m + x)) := by
  have h3 : 3 * m = m + (m + m) := by omega
  rw [h3, List.range_add, List.range_add, List.map_append, List.map_map]
  congr 2
  exact List.map_congr_left fun x _ => by
    simp only [Function.comp_apply]
    omega

/-! ## The iterate shape

The defender block (`g` nodes and `d`, with `d` declared last) is unattacked
and enters at round one; the `b` block is attacked by `d`, which nothing
counter-attacks, so it never enters; the `a` block enters from round two
because every `b`-attacker is countered by `d ∈ S`. -/

private theorem defendedB_low {k : Nat} (S : List Nat) {t : Nat}
    (ht : t < k + 1) :
    Grounded.defendedB (Invariants.eraseAF (quarticAF (k + 1))) S t = true := by
  rw [Grounded.defendedB, List.all_eq_true]
  intro b _
  have hatt : (Invariants.eraseAF (quarticAF (k + 1))).attack b t = false := by
    rw [quartic_attack_eq]
    exact quarticAttack_false (by omega)
  rw [hatt]
  simp

private theorem defendedB_b_false {k : Nat} (S : List Nat) {t : Nat}
    (h1 : k + 1 ≤ t) (h2 : t < 2 * (k + 1)) :
    Grounded.defendedB (Invariants.eraseAF (quarticAF (k + 1))) S t = false := by
  rw [Bool.eq_false_iff]
  intro hall
  rw [Grounded.defendedB, List.all_eq_true] at hall
  have hkmem : k ∈ (Invariants.eraseAF (quarticAF (k + 1))).args := by
    rw [quartic_args_eq]
    exact List.mem_range.mpr (by omega)
  have hk := hall k hkmem
  rw [quartic_attack_eq] at hk
  rw [quarticAttack_true (by omega)] at hk
  simp only [Bool.not_true, Bool.false_or] at hk
  rw [List.any_eq_true] at hk
  obtain ⟨c, -, hc⟩ := hk
  rw [quarticAttack_false (by omega)] at hc
  exact absurd hc (by simp)

private theorem defendedB_a_of_d {k : Nat} {S : List Nat} {t : Nat}
    (h1 : 2 * (k + 1) ≤ t) (_h2 : t < 3 * (k + 1)) (hd : k ∈ S) :
    Grounded.defendedB (Invariants.eraseAF (quarticAF (k + 1))) S t = true := by
  rw [Grounded.defendedB, List.all_eq_true]
  intro b _
  rw [quartic_attack_eq]
  by_cases hatt : quarticAttack k b t = true
  · have hbrange : k + 1 ≤ b ∧ b < 2 * (k + 1) := by
      rcases quarticAttack_eq_true_iff.mp hatt with ⟨-, -, h'⟩ | ⟨h', h'', -, -⟩
      · omega
      · exact ⟨h', h''⟩
    have hany : S.any (fun c => quarticAttack k c b) = true := by
      rw [List.any_eq_true]
      exact ⟨k, hd, quarticAttack_true (Or.inl ⟨rfl, hbrange.1, hbrange.2⟩)⟩
    rw [hatt, hany]
    simp
  · rw [Bool.not_eq_true] at hatt
    rw [hatt]
    simp

private theorem defendedB_a_no_d {k : Nat} {S : List Nat} {t : Nat}
    (h1 : 2 * (k + 1) ≤ t) (h2 : t < 3 * (k + 1)) (hd : k ∉ S) :
    Grounded.defendedB (Invariants.eraseAF (quarticAF (k + 1))) S t = false := by
  rw [Bool.eq_false_iff]
  intro hall
  rw [Grounded.defendedB, List.all_eq_true] at hall
  have hbmem : k + 1 ∈ (Invariants.eraseAF (quarticAF (k + 1))).args := by
    rw [quartic_args_eq]
    exact List.mem_range.mpr (by omega)
  have hb := hall (k + 1) hbmem
  rw [quartic_attack_eq] at hb
  rw [quarticAttack_true (by omega)] at hb
  simp only [Bool.not_true, Bool.false_or] at hb
  rw [List.any_eq_true] at hb
  obtain ⟨c, hcS, hc⟩ := hb
  have hck : c = k := by
    rcases quarticAttack_eq_true_iff.mp hc with ⟨h', -, -⟩ | ⟨-, -, h', -⟩
    · exact h'
    · omega
  exact hd (hck ▸ hcS)

private theorem quartic_step_no_d {k : Nat} {S : List Nat} (hd : k ∉ S) :
    Grounded.step (Invariants.eraseAF (quarticAF (k + 1))) S
      = List.range (k + 1) := by
  rw [Grounded.step, quartic_args_eq, range_three_split,
    List.filter_append, List.filter_append]
  rw [List.filter_eq_self.mpr fun a ha =>
      defendedB_low S (List.mem_range.mp ha),
    List.filter_eq_nil_iff.mpr fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      have hx' := List.mem_range.mp hx
      have hfalse : Grounded.defendedB (Invariants.eraseAF (quarticAF (k + 1)))
          S (k + 1 + x) = false := defendedB_b_false S (by omega) (by omega)
      simp [hfalse],
    List.filter_eq_nil_iff.mpr fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      have hx' := List.mem_range.mp hx
      have hfalse : Grounded.defendedB (Invariants.eraseAF (quarticAF (k + 1)))
          S (2 * (k + 1) + x) = false :=
        defendedB_a_no_d (by omega) (by omega) hd
      simp [hfalse]]
  simp

private theorem quartic_step_of_d {k : Nat} {S : List Nat} (hd : k ∈ S) :
    Grounded.step (Invariants.eraseAF (quarticAF (k + 1))) S
      = List.range (k + 1) ++
          (List.range (k + 1)).map (fun x => 2 * (k + 1) + x) := by
  rw [Grounded.step, quartic_args_eq, range_three_split,
    List.filter_append, List.filter_append]
  rw [List.filter_eq_self.mpr fun a ha =>
      defendedB_low S (List.mem_range.mp ha),
    List.filter_eq_nil_iff.mpr fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      have hx' := List.mem_range.mp hx
      have hfalse : Grounded.defendedB (Invariants.eraseAF (quarticAF (k + 1)))
          S (k + 1 + x) = false := defendedB_b_false S (by omega) (by omega)
      simp [hfalse],
    List.filter_eq_self.mpr fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      have hx' := List.mem_range.mp hx
      exact defendedB_a_of_d (by omega) (by omega) hd]
  simp

/-- **Round one is exactly the defender block**: the `k` neutral `g` nodes
and the defender `d` — with `d` last, at position `k`. -/
theorem quartic_iter_one (k : Nat) :
    Grounded.iter (Invariants.eraseAF (quarticAF (k + 1))) 1
      = List.range (k + 1) := by
  show Grounded.step (Invariants.eraseAF (quarticAF (k + 1)))
    (Grounded.iter (Invariants.eraseAF (quarticAF (k + 1))) 0) = _
  rw [show Grounded.iter (Invariants.eraseAF (quarticAF (k + 1))) 0
      = ([] : List Nat) from rfl]
  exact quartic_step_no_d (by simp)

/-- **Every later round is the defender block plus the target block**: the
`b` nodes never enter (nothing counter-attacks `d`), and every `a` node is
defended once `d` is in the iterate.  The fixpoint is reached at round two,
but the reference evaluator keeps recomputing it — and paying for it —
through all `3(k+1)` rounds. -/
theorem quartic_iter_fix (k t : Nat) :
    Grounded.iter (Invariants.eraseAF (quarticAF (k + 1))) (t + 2)
      = List.range (k + 1) ++
          (List.range (k + 1)).map (fun x => 2 * (k + 1) + x) := by
  induction t with
  | zero =>
      show Grounded.step (Invariants.eraseAF (quarticAF (k + 1)))
        (Grounded.iter (Invariants.eraseAF (quarticAF (k + 1))) 1) = _
      rw [quartic_iter_one]
      exact quartic_step_of_d (List.mem_range.mpr (by omega))
  | succ t ih =>
      show Grounded.step (Invariants.eraseAF (quarticAF (k + 1)))
        (Grounded.iter (Invariants.eraseAF (quarticAF (k + 1))) (t + 2)) = _
      rw [ih]
      exact quartic_step_of_d
        (List.mem_append_left _ (List.mem_range.mpr (by omega)))

private theorem quartic_iter_shape (k n : Nat) :
    ∃ rest, Grounded.iter (Invariants.eraseAF (quarticAF (k + 1))) (n + 1)
      = List.range (k + 1) ++ rest := by
  cases n with
  | zero => exact ⟨[], by rw [quartic_iter_one, List.append_nil]⟩
  | succ n =>
      exact ⟨(List.range (k + 1)).map (fun x => 2 * (k + 1) + x),
        quartic_iter_fix k n⟩

/-! ## Counting the short-circuit scans

Witness-specific exact costs, assembled from the generic short-circuit
composition lemmas in `Lara.Complexity` (`anyAttackerC_cons_*`,
`defendedAuxC_*`, `stepAuxC_cost_*`).  All counts are stated against that
file's short-circuit model: one count per `F.attack` evaluation, an
attacker scan stops at its first hit, a defense scan stops at its first
undefeated attacker. -/

/-- The scan of an iterate for the sole attacker of a `b` node costs exactly
`k + 1` queries: the `k` neutral `g` members are walked first, and `d` —
declared last in the defender block — answers on the final query. -/
private theorem quartic_scan {k b : Nat} (hb1 : k + 1 ≤ b)
    (hb2 : b < 2 * (k + 1)) (rest : List Nat) :
    anyAttackerC (Invariants.eraseAF (quarticAF (k + 1)))
      (List.range (k + 1) ++ rest) b = (true, k + 1) := by
  have hsplit : List.range (k + 1) ++ rest = List.range k ++ (k :: rest) := by
    rw [List.range_succ, List.append_assoc]
    rfl
  rw [hsplit,
    anyAttackerC_prefix fun c hc => by
      rw [quartic_attack_eq]
      have := List.mem_range.mp hc
      exact quarticAttack_false (by omega),
    anyAttackerC_cons_hit (by
      rw [quartic_attack_eq]
      exact quarticAttack_true (by omega))]
  refine Prod.ext rfl ?_
  simp [List.length_range]

/-- The full defense check of a target (`a`) node against any iterate that
starts with the defender block: `k + 1` misses on the defender block,
`k + 1` attackers each paying one query plus a `k + 1`-query iterate scan,
and `k + 1` misses on the target block.  The scan never fails, so — unlike a
`b` node's defense — it never short-circuits. -/
private theorem quartic_defendedC_a {k : Nat} (rest : List Nat) {t : Nat}
    (h1 : 2 * (k + 1) ≤ t) (h2 : t < 3 * (k + 1)) :
    defendedC (Invariants.eraseAF (quarticAF (k + 1)))
        (List.range (k + 1) ++ rest) t
      = (true, (k + 1) + ((k + 1) * (1 + (k + 1)) + (k + 1))) := by
  have hR1 : defendedAuxC (Invariants.eraseAF (quarticAF (k + 1)))
      (List.range (k + 1) ++ rest) t (List.range (k + 1)) = (true, k + 1) := by
    rw [defendedAuxC_no_attack fun b hb => by
      rw [quartic_attack_eq]
      have := List.mem_range.mp hb
      exact quarticAttack_false (by omega)]
    rw [List.length_range]
  have hR2 : defendedAuxC (Invariants.eraseAF (quarticAF (k + 1)))
      (List.range (k + 1) ++ rest) t
      ((List.range (k + 1)).map (fun x => (k + 1) + x))
      = (true, (k + 1) * (1 + (k + 1))) := by
    rw [defendedAuxC_uniform
      (fun b hb => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
        have := List.mem_range.mp hx
        rw [quartic_attack_eq]
        exact quarticAttack_true (by omega))
      (fun b hb => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
        have := List.mem_range.mp hx
        exact quartic_scan (by omega) (by omega) rest)]
    rw [List.length_map, List.length_range]
  have hR3 : defendedAuxC (Invariants.eraseAF (quarticAF (k + 1)))
      (List.range (k + 1) ++ rest) t
      ((List.range (k + 1)).map (fun x => 2 * (k + 1) + x))
      = (true, k + 1) := by
    rw [defendedAuxC_no_attack fun b hb => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
      have := List.mem_range.mp hx
      rw [quartic_attack_eq]
      exact quarticAttack_false (by omega)]
    rw [List.length_map, List.length_range]
  rw [defendedC, quartic_args_eq, range_three_split,
    defendedAuxC_append_true (by rw [hR1]),
    defendedAuxC_append_true (by rw [hR2]), hR1, hR2, hR3]

/-- **The per-round cubic floor on the witness**: any round whose iterate
starts with the defender block pays at least `(k+1)³` queries, all of it
from the target block — `k + 1` target nodes, each scanning `k + 1`
`b`-attackers, each of whose defenses walks the iterate past the `k` neutral
members before `d` answers. -/
private theorem quartic_step_cost {k : Nat} (rest : List Nat) :
    (k + 1) * ((k + 1) * (k + 1))
      ≤ (stepC (Invariants.eraseAF (quarticAF (k + 1)))
          (List.range (k + 1) ++ rest)).2 := by
  rw [stepC, quartic_args_eq, range_three_split,
    stepAuxC_cost_append, stepAuxC_cost_append]
  have hR3 : (stepAuxC (Invariants.eraseAF (quarticAF (k + 1)))
      (List.range (k + 1) ++ rest)
      ((List.range (k + 1)).map (fun x => 2 * (k + 1) + x))).2
      = (k + 1) * ((k + 1) + ((k + 1) * (1 + (k + 1)) + (k + 1))) := by
    rw [stepAuxC_cost_uniform fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      have := List.mem_range.mp hx
      rw [quartic_defendedC_a rest (by omega) (by omega)]]
    rw [List.length_map, List.length_range]
  rw [hR3]
  have hfac : (k + 1) * (k + 1)
      ≤ (k + 1) + ((k + 1) * (1 + (k + 1)) + (k + 1)) := by
    have hmono : (k + 1) * (k + 1) ≤ (k + 1) * (1 + (k + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    refine Nat.le_trans hmono ?_
    generalize (k + 1) * (1 + (k + 1)) = K
    omega
  refine Nat.le_trans (Nat.mul_le_mul_left _ hfac) ?_
  exact Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_left _ _)

private theorem quartic_iterC_ge (k : Nat) :
    ∀ n, n * ((k + 1) * ((k + 1) * (k + 1)))
      ≤ (iterC (Invariants.eraseAF (quarticAF (k + 1))) (n + 1)).2
  | 0 => by simp
  | n + 1 => by
      have hstep : (k + 1) * ((k + 1) * (k + 1))
          ≤ (stepC (Invariants.eraseAF (quarticAF (k + 1)))
              (iterC (Invariants.eraseAF (quarticAF (k + 1))) (n + 1)).1).2 := by
        rw [iterC_fst]
        obtain ⟨rest, hrest⟩ := quartic_iter_shape k n
        rw [hrest]
        exact quartic_step_cost rest
      show _ ≤ (iterC (Invariants.eraseAF (quarticAF (k + 1))) (n + 1)).2
        + (stepC (Invariants.eraseAF (quarticAF (k + 1)))
            (iterC (Invariants.eraseAF (quarticAF (k + 1))) (n + 1)).1).2
      rw [Nat.succ_mul]
      exact Nat.add_le_add (quartic_iterC_ge k n) hstep

/-! ## The quartic worst case -/

/-- **Quartic worst-case cost on the realizable witness.**  For `2 ≤ k`, the
instrumented grounded run on the erased carrier pays at least `k⁴` attack
queries: `3k` rounds, of which every round past the first pays ≥ `k³`.

**Quantifier discipline** (constraint D4, `docs/theory-m2b-complexity.md`):
together with
`quartic_size` and `groundedC_cost_le` this is a *worst-case* `Θ(n⁴)` result
over the fixed-context realizable class — an existential statement about a
realizable family, NOT a universal per-instance floor.  The proved universal
lower bound is quadratic (`groundedC_cost_ge`). -/
theorem quartic_cost_ge (k : Nat) (hk : 2 ≤ k) :
    k ^ 4 ≤ (groundedC (Invariants.eraseAF (quarticAF k))).2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hlen : (Invariants.eraseAF (quarticAF (j + 1))).args.length
      = 3 * (j + 1) := by
    rw [quartic_args_eq, List.length_range]
  have hgc : (groundedC (Invariants.eraseAF (quarticAF (j + 1)))).2
      = (iterC (Invariants.eraseAF (quarticAF (j + 1))) (3 * (j + 1))).2 := by
    rw [show groundedC (Invariants.eraseAF (quarticAF (j + 1)))
        = iterC (Invariants.eraseAF (quarticAF (j + 1)))
            (Invariants.eraseAF (quarticAF (j + 1))).args.length from rfl,
      hlen]
  rw [hgc, show 3 * (j + 1) = (3 * j + 2) + 1 from by omega]
  refine Nat.le_trans ?_ (quartic_iterC_ge j (3 * j + 2))
  have hpow : (j + 1) ^ 4 = (j + 1) * ((j + 1) * ((j + 1) * (j + 1))) := by
    rw [show (4 : Nat) = 3 + 1 from rfl, Nat.pow_succ,
      show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ,
      show (2 : Nat) = 1 + 1 from rfl, Nat.pow_succ, Nat.pow_one,
      Nat.mul_assoc, Nat.mul_assoc]
  rw [hpow]
  exact Nat.mul_le_mul_right _ (by omega)

/-! ## Closed evaluations

The theorem's inequality, asserted by evaluation at `k = 2, 3, 4`. -/

theorem quartic_cost_eval_two :
    2 ^ 4 ≤ (groundedC (Invariants.eraseAF (quarticAF 2))).2 := by decide

theorem quartic_cost_eval_three :
    3 ^ 4 ≤ (groundedC (Invariants.eraseAF (quarticAF 3))).2 := by decide

theorem quartic_cost_eval_four :
    4 ^ 4 ≤ (groundedC (Invariants.eraseAF (quarticAF 4))).2 := by decide

/-! ## Carrier-status transfer (issue #209)

The quartic floor transfers to the actual carrier-status surface: the
carrier claim for the unique `d` node has nonempty complete support, so
`carrierStatusC` takes the grounded branch and its count includes the
complete `groundedC` count of the erased carrier. -/

/-- Position `k` — the defender `d`, declared last in its block — supports
the carrier claim for `dAtom`. -/
private theorem quartic_d_support_mem (k : Nat) :
    k ∈ Invariants.support id (quarticAF (k + 1)) dAtom := by
  unfold Invariants.support
  apply List.mem_filterMap.mpr
  refine ⟨(dAtom, k), ?_, ?_⟩
  · apply List.mem_zipIdx_iff_getElem?.mpr
    show ((quarticLeaves k).map QuarticLeaf.atom)[k]? = some dAtom
    rw [List.getElem?_map, quarticLeaves_getElem?_d k]
    rfl
  · exact if_pos (show equiv id dAtom dAtom from rfl)

/-- **The grounded branch runs and is fully counted**: on the witness's
`d` claim, `carrierStatusC`'s count includes the complete `groundedC`
count of the erased carrier. -/
private theorem quartic_carrierStatus_ge_grounded (k : Nat) :
    (groundedC (Invariants.eraseAF (quarticAF (k + 1)))).2
      ≤ (carrierStatusC id (quarticAF (k + 1)) dAtom).2 :=
  statusSharedC_cost_ge_grounded _ _
    (List.ne_nil_of_mem (quartic_d_support_mem k))

/-- **Quartic worst-case cost on the carrier-status surface**.
For `2 ≤ k`, the shared carrier-status query on the
realizable witness at the `d` claim pays at least `k⁴` attack queries.

**Quantifier discipline** (constraint D4, `docs/theory-m2b-complexity.md`):
together with
`quartic_size` and `carrierStatusC_cost_le`, this is the tight *worst-case*
degree result for the actual carrier-status surface — an existential
statement on the fixed-context realizable family, NOT a universal
per-instance floor.  The proved universal lower bound remains quadratic
(`groundedC_cost_ge`). -/
theorem carrierStatus_quartic_cost_ge (k : Nat) (hk : 2 ≤ k) :
    k ^ 4 ≤ (carrierStatusC id (quarticAF k) dAtom).2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact Nat.le_trans (quartic_cost_ge (j + 1) hk)
    (quartic_carrierStatus_ge_grounded j)

end Lara.Examples.Complexity
