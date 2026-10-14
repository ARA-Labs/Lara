import Lara.Process.Statistics

/-!
Online FDR over complete ordered ledgers.

An online procedure tests hypotheses `0, 1, 2, …` in order and sets each level
from the rejections before it. `onlineRun` replays such a procedure over a
complete ordered ledger: every test, rejected or not, occupies its position, so
the state at test `n` is the rejection set among tests `0, …, n - 1`. This is
the premise that `online_replay_anticonservative` shows a count bound cannot
supply.

* `elond_fdp_le`, `elond_fdr`: e-LOND (Xu–Ramdas) rejects test `n` when
  `e n ≥ 1 / (α γ n (|rejections before n| + 1))`. Its false discovery
  proportion is pathwise at most `α Σ_{null} γ n e n`, so FDR is at most `α`
  under arbitrary dependence when the null e-values have expectation at most
  one and `Σ γ ≤ 1`.
* `monotone_online_fdr`: a p-value rule whose level is nonnegative, monotone in
  the past rejection set, and whose levels sum to at most `α · max(R, 1)` on
  every path (the GAI++ condition `FDP̂ ≤ α`) controls FDR at `α` when every
  null p-value is calibrated and independent of the other tests
  (`IndependentNull`). The non-null p-values may depend on each other
  arbitrarily; a product law meets the premise (`splitsAt_of_product`). A null
  test's rejection is coupled to the run with its p-value set to zero, which
  has the same rejections when the test is rejected and at least as many
  otherwise.
* `lord_nonneg`, `lord_mono`, `lord_fdpHat`, `lord_fdr`: LORD++ (Ramdas et al.
  2017) meets the three conditions, so it controls FDR at `α` under the
  paper's independence condition: nulls independent of each other and of the
  non-nulls.
-/

namespace Lara.Process.Statistics

open Lara.BHL.FiniteProbability
open scoped BigOperators

/-! ### Online runs -/

/-- The rejection set among the first `n` tests of an online procedure. Test `n`
is rejected when `test n` accepts the level that `level` sets from the
rejections before it. -/
def onlineRun (level : ℕ → Finset ℕ → ℚ) (test : ℕ → ℚ → Bool) : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 =>
      if test n (level n (onlineRun level test n)) then insert n (onlineRun level test n)
      else onlineRun level test n

section Run

variable {level : ℕ → Finset ℕ → ℚ} {test : ℕ → ℚ → Bool}

/-- Test `t` is rejected within the first `m` tests exactly when `t < m` and its
test accepts the level set by the rejections before it. -/
theorem mem_onlineRun {m t : ℕ} :
    t ∈ onlineRun level test m ↔ t < m ∧ test t (level t (onlineRun level test t)) = true := by
  induction m with
  | zero => simp [onlineRun]
  | succ m ih =>
      simp only [onlineRun]
      split
      · rename_i h
        rw [Finset.mem_insert, ih]
        constructor
        · rintro (rfl | ⟨hlt, ht⟩)
          · exact ⟨Nat.lt_succ_self _, h⟩
          · exact ⟨by omega, ht⟩
        · rintro ⟨hlt, ht⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | rfl
          · exact Or.inr ⟨hlt, ht⟩
          · exact Or.inl rfl
      · rename_i h
        rw [ih]
        constructor
        · rintro ⟨hlt, ht⟩
          exact ⟨by omega, ht⟩
        · rintro ⟨hlt, ht⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | rfl
          · exact ⟨hlt, ht⟩
          · exact absurd ht h

/-- The rejections before test `n` are the later run's rejections below `n`. -/
theorem onlineRun_filter {n m : ℕ} (h : n ≤ m) :
    (onlineRun level test m).filter (· < n) = onlineRun level test n := by
  ext t
  simp only [Finset.mem_filter, mem_onlineRun]
  constructor
  · rintro ⟨⟨_, hp⟩, hn⟩
    exact ⟨hn, hp⟩
  · rintro ⟨hn, hp⟩
    exact ⟨⟨by omega, hp⟩, hn⟩

theorem onlineRun_subset_range (m : ℕ) : onlineRun level test m ⊆ Finset.range m :=
  fun _ ht => Finset.mem_range.mpr (mem_onlineRun.mp ht).1

end Run

/-- The false discovery proportion of rejection set `R` with null set `N`. -/
def onlineFdp (R N : Finset ℕ) : ℚ := ((R ∩ N).card : ℚ) / max (R.card : ℚ) 1

theorem onlineFdp_eq_sum (R N : Finset ℕ) :
    onlineFdp R N = ∑ t ∈ N, if t ∈ R then 1 / max (R.card : ℚ) 1 else 0 := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    Finset.filter_mem_eq_inter, Finset.inter_comm, onlineFdp, mul_one_div]

theorem onlineFdp_nonneg (R N : Finset ℕ) : 0 ≤ onlineFdp R N :=
  div_nonneg (Nat.cast_nonneg _) (le_max_of_le_right zero_le_one)

/-! ### e-LOND -/

/-- The e-LOND level of test `n` after the rejections `S`. -/
def elondLevel (α : ℚ) (γ : ℕ → ℚ) (n : ℕ) (S : Finset ℕ) : ℚ := α * γ n * (S.card + 1)

/-- e-LOND over the first `T` tests: reject `n` when `e n` times its level is at
least one. -/
def elond (α : ℚ) (γ e : ℕ → ℚ) (T : ℕ) : Finset ℕ :=
  onlineRun (elondLevel α γ) (fun n a => decide (1 ≤ a * e n)) T

/-- Pathwise, e-LOND's false discovery proportion is at most `Σ_{null} α γ n e n`. -/
theorem elond_fdp_le {α : ℚ} (hα : 0 ≤ α) {γ e : ℕ → ℚ} (hγ : ∀ n, 0 ≤ γ n)
    (he : ∀ n, 0 ≤ e n) (T : ℕ) (N : Finset ℕ) :
    onlineFdp (elond α γ e T) N ≤ ∑ t ∈ N, α * γ t * e t := by
  rw [onlineFdp_eq_sum]
  apply Finset.sum_le_sum
  intro t _
  split
  · rename_i ht
    obtain ⟨htT, hrej⟩ := mem_onlineRun.mp ht
    set R := elond α γ e T
    set Rt := onlineRun (elondLevel α γ) (fun n a => decide (1 ≤ a * e n)) t
    have h1 : 1 ≤ α * γ t * ((Rt.card : ℚ) + 1) * e t := of_decide_eq_true hrej
    have hsub : insert t Rt ⊆ R := by
      rw [Finset.insert_subset_iff]
      refine ⟨ht, ?_⟩
      have := onlineRun_filter (level := elondLevel α γ)
        (test := fun n a => decide (1 ≤ a * e n)) htT.le
      intro x hx
      have hx' : x ∈ ({x ∈ onlineRun (elondLevel α γ) (fun n a => decide (1 ≤ a * e n)) T |
          x < t}) := this ▸ hx
      exact (Finset.mem_filter.mp hx').1
    have hnot : t ∉ Rt := fun h => (lt_irrefl t) (mem_onlineRun.mp h).1
    have hcard : (Rt.card : ℚ) + 1 ≤ max (R.card : ℚ) 1 := by
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at this
      exact le_max_of_le_left (by exact_mod_cast this)
    have hpos : (0 : ℚ) < (Rt.card : ℚ) + 1 := by positivity
    calc 1 / max (R.card : ℚ) 1 ≤ 1 / ((Rt.card : ℚ) + 1) :=
          one_div_le_one_div_of_le hpos hcard
      _ ≤ α * γ t * e t := by
          rw [div_le_iff₀ hpos]
          linarith [show α * γ t * ((Rt.card : ℚ) + 1) * e t =
            α * γ t * e t * ((Rt.card : ℚ) + 1) by ring]
  · exact mul_nonneg (mul_nonneg hα (hγ t)) (he t)

/-- e-LOND controls FDR at `α` under arbitrary dependence: the e-values are
nonnegative, each null e-value has expectation at most one, and the weights are
nonnegative with every partial sum at most one. -/
theorem elond_fdr {Ω : Type} [Fintype Ω] (law : Law Ω) {α : ℚ} (hα : 0 ≤ α) {γ : ℕ → ℚ}
    (hγ : ∀ n, 0 ≤ γ n) (hγsum : ∀ m, ∑ k ∈ Finset.range m, γ k ≤ 1) (e : ℕ → Ω → ℚ)
    (he : ∀ n ω, 0 ≤ e n ω) (T : ℕ) (N : Finset ℕ) (hN : N ⊆ Finset.range T)
    (hnull : ∀ t ∈ N, expect law (e t) ≤ 1) :
    expect law (fun ω => onlineFdp (elond α γ (fun n => e n ω) T) N) ≤ α := by
  calc expect law (fun ω => onlineFdp (elond α γ (fun n => e n ω) T) N)
      ≤ expect law (fun ω => ∑ t ∈ N, α * γ t * e t ω) := by
        unfold expect
        exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
          (elond_fdp_le hα hγ (fun n => he n ω) T N) (law.nonnegative ω)
    _ = ∑ t ∈ N, α * γ t * expect law (e t) := by
        unfold expect
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun ω _ => by ring
    _ ≤ ∑ t ∈ N, α * γ t := Finset.sum_le_sum fun t ht =>
        mul_le_of_le_one_right (mul_nonneg hα (hγ t)) (hnull t ht)
    _ = α * ∑ t ∈ N, γ t := by rw [Finset.mul_sum]
    _ ≤ α * ∑ t ∈ Finset.range T, γ t :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hN
          fun n _ _ => hγ n) hα
    _ ≤ α * 1 := mul_le_mul_of_nonneg_left (hγsum T) hα
    _ = α := mul_one α

/-! ### Monotone p-value rules under independence -/

/-- Reject test `n` when its p-value is at most the level. -/
def pTest (p : ℕ → ℚ) : ℕ → ℚ → Bool := fun n a => decide (p n ≤ a)

section Monotone

variable {level : ℕ → Finset ℕ → ℚ}

theorem onlineRun_pTest_succ (p : ℕ → ℚ) (n : ℕ) :
    onlineRun level (pTest p) (n + 1) =
      if p n ≤ level n (onlineRun level (pTest p) n) then insert n (onlineRun level (pTest p) n)
      else onlineRun level (pTest p) n := by
  simp only [onlineRun, pTest, decide_eq_true_eq]

/-- The run before test `n` reads only the p-values before `n`. -/
theorem onlineRun_congr {p p' : ℕ → ℚ} {n : ℕ} (h : ∀ m < n, p m = p' m) :
    onlineRun level (pTest p) n = onlineRun level (pTest p') n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [onlineRun_pTest_succ, onlineRun_pTest_succ, ih fun m hm => h m (by omega),
        h n (Nat.lt_succ_self n)]

/-- With a level monotone in the past rejections, smaller p-values reject at
least as much. -/
theorem onlineRun_mono (hmono : ∀ n S S', S ⊆ S' → level n S ≤ level n S')
    {p p' : ℕ → ℚ} (hle : ∀ n, p' n ≤ p n) :
    ∀ n, onlineRun level (pTest p) n ⊆ onlineRun level (pTest p') n := by
  intro n
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ n ih =>
      rw [onlineRun_pTest_succ, onlineRun_pTest_succ]
      by_cases hp : p n ≤ level n (onlineRun level (pTest p) n)
      · have hp' : p' n ≤ level n (onlineRun level (pTest p') n) :=
          (hle n).trans (hp.trans (hmono n _ _ ih))
        rw [if_pos hp, if_pos hp']
        exact Finset.insert_subset_insert n ih
      · rw [if_neg hp]
        split
        · exact ih.trans (Finset.subset_insert _ _)
        · exact ih

/-- Setting a rejected test's p-value to zero changes no rejection. -/
theorem onlineRun_couple (hnonneg : ∀ n S, 0 ≤ level n S) {p : ℕ → ℚ} {t T : ℕ}
    (ht : t ∈ onlineRun level (pTest p) T) :
    ∀ n, onlineRun level (pTest (Function.update p t 0)) n = onlineRun level (pTest p) n := by
  have hrej := (mem_onlineRun.mp ht).2
  simp only [pTest, decide_eq_true_eq] at hrej
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [onlineRun_pTest_succ, onlineRun_pTest_succ, ih]
      by_cases hn : n = t
      · subst hn
        rw [Function.update_self, if_pos (hnonneg _ _), if_pos hrej]
      · rw [Function.update_of_ne hn]

end Monotone

section Independence

variable {T : ℕ} {V : Type} [Fintype V]

/-- The joint law splits at test `t` into the law `μ` of its coordinate and a
law of the other coordinates: coordinate `t` is independent of the rest. -/
def SplitsAt (law : Law (Fin T → V)) (μ : Law V) (t : Fin T) : Prop :=
  ∃ rest : Law ({j // j ≠ t} → V), ∀ ω, law.mass ω = μ.mass (ω t) * rest.mass (fun j => ω j)

/-- Null `t` is calibrated and independent of every other test: the law splits
at `t` into a law under which `pval t` is a p-value and a law of the rest. The
other coordinates may depend on each other arbitrarily. -/
def IndependentNull (law : Law (Fin T → V)) (pval : Fin T → V → ℚ) (t : Fin T) : Prop :=
  ∃ μ : Law V, SplitsAt law μ t ∧ IsPValue μ (pval t)

/-- A product law splits at every coordinate. -/
theorem splitsAt_of_product (law : Law (Fin T → V)) (marg : Fin T → Law V)
    (product : ∀ ω, law.mass ω = ∏ j, (marg j).mass (ω j)) (t : Fin T) :
    SplitsAt law (marg t) t := by
  refine ⟨⟨fun w => ∏ j : {j // j ≠ t}, (marg j).mass (w j),
    fun w => Finset.prod_nonneg fun j _ => (marg j).nonnegative _, ?_⟩, fun ω => ?_⟩
  · rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one fun j _ => (marg j).normalized
  · rw [product, Fintype.prod_eq_mul_prod_subtype_ne _ t]

/-- Integrating out one independent coordinate: if `F` and `G` read only the
other coordinates and the coordinate's p-value is calibrated, the mass on which
it is at most `F`, weighted by `G`, is at most `𝔼[F G]`. -/
theorem coordinate_bound (law : Law (Fin T → V)) (μ : Law V) (t : Fin T)
    (hsplit : SplitsAt law μ t) (p : V → ℚ) (hp : IsPValue μ p) (F G : ({j // j ≠ t} → V) → ℚ)
    (hF : ∀ w, 0 ≤ F w) (hG : ∀ w, 0 ≤ G w) :
    ∑ ω, law.mass ω * (if p (ω t) ≤ F (fun j => ω j) then G (fun j => ω j) else 0) ≤
      ∑ ω, law.mass ω * (F (fun j => ω j) * G (fun j => ω j)) := by
  obtain ⟨rest, hrest⟩ := hsplit
  have split : ∀ H : V → ({j // j ≠ t} → V) → ℚ,
      ∑ ω, law.mass ω * H (ω t) (fun j => ω j) =
        ∑ w, ∑ v, μ.mass v * rest.mass w * H v w := by
    intro H
    rw [Finset.sum_comm, ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (Equiv.funSplitAt t V) _ _ fun ω => ?_
    simp only [Equiv.funSplitAt_apply, hrest]
  rw [split (fun v w => if p v ≤ F w then G w else 0), split (fun _ w => F w * G w)]
  apply Finset.sum_le_sum
  intro w _
  calc ∑ v, μ.mass v * rest.mass w * (if p v ≤ F w then G w else 0)
      = rest.mass w * G w * eventMass μ (fun v => decide (p v ≤ F w)) := by
        unfold eventMass
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases h : p v ≤ F w
        · simp only [h, if_true, decide_true]; ring
        · simp [h]
    _ ≤ rest.mass w * G w * F w :=
        mul_le_mul_of_nonneg_left (hp _ (hF w)) (mul_nonneg (rest.nonnegative w) (hG w))
    _ = ∑ v, μ.mass v * rest.mass w * (F w * G w) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, μ.normalized]
        ring

/-- The p-values of an outcome as a sequence; positions from `T` on are inert. -/
def pvec (pval : Fin T → V → ℚ) (ω : Fin T → V) : ℕ → ℚ :=
  fun n => if h : n < T then pval ⟨n, h⟩ (ω ⟨n, h⟩) else 1

/-- The p-values with test `t` set to zero, read from the other coordinates. -/
def pvecZero (pval : Fin T → V → ℚ) (t : Fin T) (w : {j // j ≠ t} → V) : ℕ → ℚ :=
  fun n =>
    if hn : n = t then 0
    else if h : n < T then pval ⟨n, h⟩ (w ⟨⟨n, h⟩, fun e => hn (congrArg Fin.val e)⟩) else 1

omit [Fintype V] in
theorem pvecZero_eq (pval : Fin T → V → ℚ) (t : Fin T) (ω : Fin T → V) :
    pvecZero pval t (fun j => ω j) = Function.update (pvec pval ω) t 0 := by
  funext n
  by_cases hn : n = t
  · subst hn; simp [pvecZero]
  · rw [Function.update_of_ne hn]
    simp [pvecZero, pvec, hn]

/-- A monotone online p-value rule controls FDR at `α` when every null is
independent of the other tests. The level is nonnegative and monotone in the
past rejections, and on every path its levels sum to at most `α · max(R, 1)`
(GAI++'s `FDP̂ ≤ α`). The p-values are nonnegative, and every null p-value is
calibrated and independent of the rest (`IndependentNull`); the non-null
p-values may depend on each other arbitrarily. -/
theorem monotone_online_fdr {level : ℕ → Finset ℕ → ℚ} {α : ℚ}
    (hnonneg : ∀ n S, 0 ≤ level n S) (hmono : ∀ n S S', S ⊆ S' → level n S ≤ level n S')
    (hfdp : ∀ S ⊆ Finset.range T,
      ∑ n ∈ Finset.range T, level n (S.filter (· < n)) ≤ α * max (S.card : ℚ) 1)
    (law : Law (Fin T → V)) (pval : Fin T → V → ℚ) (pnonneg : ∀ t v, 0 ≤ pval t v)
    (N : Finset ℕ) (hN : N ⊆ Finset.range T)
    (hnull : ∀ t : Fin T, (t : ℕ) ∈ N → IndependentNull law pval t) :
    expect law (fun ω => onlineFdp (onlineRun level (pTest (pvec pval ω)) T) N) ≤ α := by
  set R : (Fin T → V) → Finset ℕ := fun ω => onlineRun level (pTest (pvec pval ω)) T
  set L : (Fin T → V) → ℕ → ℚ := fun ω n => level n (onlineRun level (pTest (pvec pval ω)) n)
  have hL : ∀ ω n, 0 ≤ L ω n := fun ω n => hnonneg _ _
  have hinv : ∀ m : ℚ, 0 ≤ 1 / max m 1 := fun m => one_div_nonneg.mpr (le_max_of_le_right zero_le_one)
  -- Each null contributes at most `𝔼[L t / max(R, 1)]`.
  have hnullTerm : ∀ t ∈ N,
      ∑ ω, law.mass ω * (if t ∈ R ω then 1 / max ((R ω).card : ℚ) 1 else 0) ≤
        ∑ ω, law.mass ω * (L ω t * (1 / max ((R ω).card : ℚ) 1)) := by
    intro t htN
    have htT : t < T := Finset.mem_range.mp (hN htN)
    set tt : Fin T := ⟨t, htT⟩
    set F : ({j // j ≠ tt} → V) → ℚ := fun w => level t (onlineRun level (pTest (pvecZero pval tt w)) t)
    set G : ({j // j ≠ tt} → V) → ℚ :=
      fun w => 1 / max ((onlineRun level (pTest (pvecZero pval tt w)) T).card : ℚ) 1
    have hpz : ∀ ω : Fin T → V, pvecZero pval tt (fun j => ω j) = Function.update (pvec pval ω) t 0 :=
      pvecZero_eq pval tt
    have hF : ∀ ω : Fin T → V, F (fun j => ω j) = L ω t := by
      intro ω
      simp only [F, L, hpz]
      rw [onlineRun_congr fun m hm => Function.update_of_ne (Nat.ne_of_lt hm) _ _]
    have hmem : ∀ ω : Fin T → V, t ∈ R ω ↔ pval tt (ω tt) ≤ L ω t := by
      intro ω
      simp only [R, L, mem_onlineRun, pTest, decide_eq_true_eq, pvec, dif_pos htT]
      exact ⟨fun h => h.2, fun h => ⟨htT, h⟩⟩
    have hpoint : ∀ ω : Fin T → V,
        (if t ∈ R ω then 1 / max ((R ω).card : ℚ) 1 else 0) =
          if pval tt (ω tt) ≤ F (fun j => ω j) then G (fun j => ω j) else 0 := by
      intro ω
      rw [hF]
      by_cases h : t ∈ R ω
      · rw [if_pos h, if_pos ((hmem ω).mp h)]
        simp only [G, hpz]
        rw [onlineRun_couple hnonneg h T]
      · rw [if_neg h, if_neg (fun h' => h ((hmem ω).mpr h'))]
    calc ∑ ω, law.mass ω * (if t ∈ R ω then 1 / max ((R ω).card : ℚ) 1 else 0)
        = ∑ ω, law.mass ω * (if pval tt (ω tt) ≤ F (fun j => ω j) then G (fun j => ω j) else 0) :=
          Finset.sum_congr rfl fun ω _ => by rw [hpoint]
      _ ≤ ∑ ω, law.mass ω * (F (fun j => ω j) * G (fun j => ω j)) := by
          obtain ⟨μ, hsplit, hp⟩ := hnull tt htN
          exact coordinate_bound law μ tt hsplit (pval tt) hp F G
            (fun _ => hnonneg _ _) (fun _ => hinv _)
      _ ≤ ∑ ω, law.mass ω * (L ω t * (1 / max ((R ω).card : ℚ) 1)) := by
          refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (law.nonnegative ω)
          rw [hF]
          refine mul_le_mul_of_nonneg_left ?_ (hL ω t)
          have hsub : R ω ⊆ onlineRun level (pTest (pvecZero pval tt fun j => ω j)) T := by
            rw [hpz]
            refine onlineRun_mono hmono (fun n => ?_) T
            by_cases hn : n = t
            · subst hn
              rw [Function.update_self]
              simp only [pvec, dif_pos htT]
              exact pnonneg _ _
            · rw [Function.update_of_ne hn]
          have hc : ((R ω).card : ℚ) ≤
              ((onlineRun level (pTest (pvecZero pval tt fun j => ω j)) T).card : ℚ) := by
            exact_mod_cast Finset.card_le_card hsub
          exact one_div_le_one_div_of_le (lt_max_of_lt_right zero_lt_one) (max_le_max hc le_rfl)
  calc expect law (fun ω => onlineFdp (R ω) N)
      = ∑ t ∈ N, ∑ ω, law.mass ω * (if t ∈ R ω then 1 / max ((R ω).card : ℚ) 1 else 0) := by
        unfold expect
        simp_rw [onlineFdp_eq_sum, Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ t ∈ N, ∑ ω, law.mass ω * (L ω t * (1 / max ((R ω).card : ℚ) 1)) :=
        Finset.sum_le_sum hnullTerm
    _ = ∑ ω, law.mass ω * ((∑ t ∈ N, L ω t) * (1 / max ((R ω).card : ℚ) 1)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
    _ ≤ ∑ ω, law.mass ω * α := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (law.nonnegative ω)
        have hpos : (0 : ℚ) < max ((R ω).card : ℚ) 1 := lt_max_of_lt_right zero_lt_one
        have hsum : ∑ t ∈ N, L ω t ≤ α * max ((R ω).card : ℚ) 1 := by
          refine (Finset.sum_le_sum_of_subset_of_nonneg hN fun n _ _ => hL ω n).trans ?_
          have := hfdp (R ω) (onlineRun_subset_range T)
          refine le_of_eq_of_le (Finset.sum_congr rfl fun n hn => ?_) this
          simp only [L, R]
          rw [onlineRun_filter (Finset.mem_range.mp hn).le]
        rw [mul_one_div, div_le_iff₀ hpos]
        exact hsum
    _ = α := by rw [← Finset.sum_mul, law.normalized, one_mul]

end Independence

/-! ### LORD++ -/

section Lord

/-- The LORD++ level of test `n` (0-based) after the rejections `S`, with
initial wealth `W₀` and weights `γ`: `W₀ γ n + α Σ_{j ∈ S} γ (n - 1 - j)`, less
`W₀ γ (n - 1 - τ₁)` for the first rejection `τ₁`. -/
def lordLevel (α W₀ : ℚ) (γ : ℕ → ℚ) (n : ℕ) (S : Finset ℕ) : ℚ :=
  W₀ * γ n + α * ∑ j ∈ S, γ (n - 1 - j) -
    if h : S.Nonempty then W₀ * γ (n - 1 - S.min' h) else 0

/-- LORD++ over the first `T` tests with p-values `p`. -/
def lord (α W₀ : ℚ) (γ p : ℕ → ℚ) (T : ℕ) : Finset ℕ :=
  onlineRun (lordLevel α W₀ γ) (pTest p) T

variable {α W₀ : ℚ} {γ : ℕ → ℚ}

theorem lord_nonneg (hW₀ : 0 ≤ W₀) (hW₀α : W₀ ≤ α) (hγ : ∀ n, 0 ≤ γ n) (n : ℕ)
    (S : Finset ℕ) : 0 ≤ lordLevel α W₀ γ n S := by
  unfold lordLevel
  have hα : 0 ≤ α := hW₀.trans hW₀α
  have hsum : 0 ≤ ∑ j ∈ S, γ (n - 1 - j) := Finset.sum_nonneg fun j _ => hγ _
  split
  · rename_i h
    have hmin : γ (n - 1 - S.min' h) ≤ ∑ j ∈ S, γ (n - 1 - j) :=
      Finset.single_le_sum (fun j _ => hγ (n - 1 - j)) (S.min'_mem h)
    nlinarith [hγ n, hγ (n - 1 - S.min' h)]
  · nlinarith [hγ n]

theorem lord_mono (hW₀ : 0 ≤ W₀) (hW₀α : W₀ ≤ α) (hγ : ∀ n, 0 ≤ γ n) (n : ℕ)
    (S S' : Finset ℕ) (hS : S ⊆ S') : lordLevel α W₀ γ n S ≤ lordLevel α W₀ γ n S' := by
  unfold lordLevel
  have hα : 0 ≤ α := hW₀.trans hW₀α
  have hsplit : ∑ j ∈ S', γ (n - 1 - j) =
      ∑ j ∈ S' \ S, γ (n - 1 - j) + ∑ j ∈ S, γ (n - 1 - j) :=
    (Finset.sum_sdiff hS).symm
  have hdiff : 0 ≤ ∑ j ∈ S' \ S, γ (n - 1 - j) := Finset.sum_nonneg fun j _ => hγ _
  by_cases h' : S'.Nonempty
  · rw [dif_pos h']
    set a' := S'.min' h'
    by_cases h : S.Nonempty
    · rw [dif_pos h]
      set a := S.min' h
      have ha : a ∈ S := S.min'_mem h
      by_cases heq : a' = a
      · rw [heq]
        nlinarith
      · have hnot : a' ∉ S := fun ha' =>
          heq (le_antisymm (S'.min'_le _ (hS ha)) (S.min'_le _ ha'))
        have hmem : a' ∈ S' \ S := Finset.mem_sdiff.mpr ⟨S'.min'_mem h', hnot⟩
        have hone : γ (n - 1 - a') ≤ ∑ j ∈ S' \ S, γ (n - 1 - j) :=
          Finset.single_le_sum (fun j _ => hγ (n - 1 - j)) hmem
        nlinarith [hγ (n - 1 - a), hγ (n - 1 - a')]
    · rw [dif_neg h]
      have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      have hone : γ (n - 1 - a') ≤ ∑ j ∈ S', γ (n - 1 - j) :=
        Finset.single_le_sum (fun j _ => hγ (n - 1 - j)) (S'.min'_mem h')
      subst hS0
      simp only [Finset.sum_empty, mul_zero, add_zero, sub_zero]
      nlinarith [hγ (n - 1 - a')]
  · have hS' : S' = ∅ := Finset.not_nonempty_iff_eq_empty.mp h'
    subst hS'
    rw [Finset.subset_empty.mp hS]

/-- The weights after a rejection at `j` sum to at most one over the horizon. -/
theorem gap_sum_le (hγ : ∀ n, 0 ≤ γ n) (hγsum : ∀ m, ∑ k ∈ Finset.range m, γ k ≤ 1)
    (j T : ℕ) : ∑ n ∈ (Finset.range T).filter (j < ·), γ (n - 1 - j) ≤ 1 := by
  set s := (Finset.range T).filter (j < ·)
  have hinj : ∀ x ∈ s, ∀ y ∈ s, x - 1 - j = y - 1 - j → x = y := by
    intro x hx y hy hxy
    simp only [s, Finset.mem_filter] at hx hy
    omega
  rw [← Finset.sum_image hinj]
  refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hγ k).trans (hγsum T)
  intro k hk
  simp only [s, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hk
  obtain ⟨x, ⟨hx, _⟩, rfl⟩ := hk
  exact Finset.mem_range.mpr (by omega)

/-- LORD++ satisfies GAI++'s `FDP̂ ≤ α`: on every path its levels over the
first `T` tests sum to at most `α · max(R, 1)`. -/
theorem lord_fdpHat (hW₀ : 0 ≤ W₀) (hW₀α : W₀ ≤ α) (hγ : ∀ n, 0 ≤ γ n)
    (hγsum : ∀ m, ∑ k ∈ Finset.range m, γ k ≤ 1) (T : ℕ) (S : Finset ℕ) :
    ∑ n ∈ Finset.range T, lordLevel α W₀ γ n (S.filter (· < n)) ≤ α * max (S.card : ℚ) 1 := by
  have hα : 0 ≤ α := hW₀.trans hW₀α
  set g : ℕ → ℚ := fun j => ∑ n ∈ (Finset.range T).filter (j < ·), γ (n - 1 - j)
  have hg : ∀ j, g j ≤ 1 := fun j => gap_sum_le hγ hγsum j T
  have hg0 : ∀ j, 0 ≤ g j := fun j => Finset.sum_nonneg fun n _ => hγ _
  have hA : ∑ n ∈ Finset.range T, W₀ * γ n ≤ W₀ := by
    rw [← Finset.mul_sum]
    exact mul_le_of_le_one_right hW₀ (hγsum T)
  have hB : ∑ n ∈ Finset.range T, α * ∑ j ∈ S.filter (· < n), γ (n - 1 - j) =
      α * ∑ j ∈ S, g j := by
    rw [← Finset.mul_sum]
    congr 1
    simp only [g, Finset.sum_filter]
    exact Finset.sum_comm
  unfold lordLevel
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hB]
  by_cases hS : S.Nonempty
  · set a := S.min' hS
    have ha : a ∈ S := S.min'_mem hS
    have hC : ∑ n ∈ Finset.range T,
        (if h : (S.filter (· < n)).Nonempty then W₀ * γ (n - 1 - (S.filter (· < n)).min' h)
          else 0) = W₀ * g a := by
      simp only [g, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases han : a < n
      · have hne : (S.filter (· < n)).Nonempty := ⟨a, Finset.mem_filter.mpr ⟨ha, han⟩⟩
        rw [dif_pos hne, if_pos han]
        have hmin : (S.filter (· < n)).min' hne = a := le_antisymm
          ((S.filter (· < n)).min'_le a (Finset.mem_filter.mpr ⟨ha, han⟩))
          (S.min'_le _ (Finset.mem_filter.mp ((S.filter (· < n)).min'_mem hne)).1)
        rw [hmin]
      · have hne : ¬ (S.filter (· < n)).Nonempty := by
          rintro ⟨x, hx⟩
          have hx' := Finset.mem_filter.mp hx
          exact han (lt_of_le_of_lt (S.min'_le x hx'.1) hx'.2)
        rw [dif_neg hne, if_neg han, mul_zero]
    rw [hC, ← Finset.add_sum_erase S g ha]
    have herase : ∑ j ∈ S.erase a, g j ≤ ((S.erase a).card : ℚ) := by
      have := Finset.sum_le_card_nsmul (S.erase a) g 1 fun j _ => hg j
      simpa using this
    have hcard : ((S.erase a).card : ℚ) + 1 = S.card := by
      exact_mod_cast Finset.card_erase_add_one ha
    have hle : (S.card : ℚ) ≤ max (S.card : ℚ) 1 := le_max_left _ _
    nlinarith [hg a, hg0 a]
  · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst hS0
    simp only [Finset.filter_empty, Finset.not_nonempty_empty, dite_false, Finset.sum_const_zero,
      sub_zero, Finset.sum_empty, mul_zero, add_zero, Finset.card_empty, Nat.cast_zero]
    calc ∑ n ∈ Finset.range T, W₀ * γ n ≤ W₀ := hA
      _ ≤ α := hW₀α
      _ = α * max (0 : ℚ) 1 := by norm_num

/-- LORD++ controls FDR at `α` when the p-values are nonnegative, every null
p-value is calibrated and independent of the other tests, `0 ≤ W₀ ≤ α`, and the
weights are nonnegative with every partial sum at most one. The non-null
p-values may depend on each other arbitrarily, as in Ramdas et al. (2017). -/
theorem lord_fdr {T : ℕ} {V : Type} [Fintype V] (hW₀ : 0 ≤ W₀) (hW₀α : W₀ ≤ α)
    (hγ : ∀ n, 0 ≤ γ n) (hγsum : ∀ m, ∑ k ∈ Finset.range m, γ k ≤ 1)
    (law : Law (Fin T → V)) (pval : Fin T → V → ℚ) (pnonneg : ∀ t v, 0 ≤ pval t v)
    (N : Finset ℕ) (hN : N ⊆ Finset.range T)
    (hnull : ∀ t : Fin T, (t : ℕ) ∈ N → IndependentNull law pval t) :
    expect law (fun ω => onlineFdp (lord α W₀ γ (pvec pval ω) T) N) ≤ α :=
  monotone_online_fdr (lord_nonneg hW₀ hW₀α hγ) (lord_mono hW₀ hW₀α hγ)
    (fun S _ => lord_fdpHat hW₀ hW₀α hγ hγsum T S) law pval pnonneg N hN hnull

end Lord

end Lara.Process.Statistics
