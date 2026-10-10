import Lara.BHL.FiniteProbability
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Order.Nat

/-!
R4: finite statistical validity over incomplete ledgers.

The style follows `Lara.BHL.Tests.Binary`: finite carriers, exact rational
masses (`Lara.BHL.FiniteProbability.Law`) and expectations as finite sums. The
pinned Mathlib has no Ville inequality and no e-values, p-values or FDR, so
every bound is proved directly here.

A guarantee survives an incomplete ledger only through a bounded quantity:

* `eBonferroni_bounded`: rejecting when `e ≥ K/α` controls FWER at `α` for every
  completion with at most `K` tests, under arbitrary dependence, whichever tests
  were reported.
* `selfConsistent_fdr` and `eBH_bounded`: e-BH run at the bound `K` controls FDR
  at `α`. Unreported tests enter the procedure as non-rejections (e-value `0`).
  This is proved directly; Wang–Ramdas Prop. 2 is stated for a fixed family size.
* `ville_finite`, `ville_crossing`: a nonnegative test supermartingale is at or
  above `1/α` at a stopping time within a finite horizon with probability at
  most `α`, under any stopping rule; stopping at the first crossing gives the
  crossing probability. `stoppedHitProb` is that probability, computed by
  conditioning on each next observation. Proved by induction on the horizon, not from Mathlib's `maximal_ineq`
  (which is Doob's inequality for submartingales).
* `split_selection_valid`: selection on one sample and a calibrated test on an
  independent sample keeps the test's level. Independence is the explicit
  product-law premise; read separation alone does not supply it.
-/

namespace Lara.Process.Statistics

open Lara.BHL.FiniteProbability
open scoped BigOperators

variable {Ω : Type} [Fintype Ω]

/-- Expectation under a finite rational law. -/
def expect (law : Law Ω) (f : Ω → ℚ) : ℚ := ∑ ω, law.mass ω * f ω

/-- An e-value for a null law: nonnegative with expectation at most one. -/
def IsEValue (law : Law Ω) (e : Ω → ℚ) : Prop := (∀ ω, 0 ≤ e ω) ∧ expect law e ≤ 1

/-- Markov's inequality for an e-value. -/
theorem markov {law : Law Ω} {e : Ω → ℚ} (he : IsEValue law e) {t : ℚ} (ht : 0 < t) :
    eventMass law (fun ω => decide (t ≤ e ω)) ≤ 1 / t := by
  have bound : eventMass law (fun ω => decide (t ≤ e ω)) ≤ expect law e / t := by
    unfold eventMass expect
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro ω _
    have m := law.nonnegative ω
    split
    · rename_i h
      have h' : t ≤ e ω := of_decide_eq_true h
      rw [mul_div_assoc]
      exact le_mul_of_one_le_right m ((one_le_div ht).mpr h')
    · exact div_nonneg (mul_nonneg m (he.1 ω)) ht.le
  exact bound.trans (div_le_div_of_nonneg_right he.2 ht.le)

/-- The event that some index in `s` has its event `p i` occur. -/
def anyOf {ι : Type} (s : Finset ι) (p : ι → Ω → Bool) (ω : Ω) : Bool :=
  decide (∃ i ∈ s, p i ω = true)

/-- The union bound for finite events. -/
theorem eventMass_exists_le {ι : Type} (law : Law Ω) (s : Finset ι) (p : ι → Ω → Bool) :
    eventMass law (anyOf s p) ≤ ∑ i ∈ s, eventMass law (p i) := by
  classical
  unfold eventMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  unfold anyOf
  split
  · rename_i h
    obtain ⟨i, hi, hp⟩ := of_decide_eq_true h
    calc law.mass ω = if p i ω then law.mass ω else 0 := by rw [hp]; rfl
      _ ≤ ∑ j ∈ s, if p j ω then law.mass ω else 0 :=
        Finset.single_le_sum (f := fun j => if p j ω then law.mass ω else 0)
          (fun j _ => by split <;> simp [law.nonnegative ω]) hi
  · exact Finset.sum_nonneg fun j _ => by split <;> simp [law.nonnegative ω]

/-- No index, no event. -/
theorem eventMass_anyOf_empty {ι : Type} (law : Law Ω) (p : ι → Ω → Bool) :
    eventMass law (anyOf ∅ p) = 0 := by
  unfold eventMass anyOf
  exact Finset.sum_eq_zero fun ω _ => by simp

/-- A set of tests in a family of `k ≤ K` has at most `K` members. -/
theorem card_le_bound {k K : ℕ} (hk : k ≤ K) (s : Finset (Fin k)) : (s.card : ℚ) ≤ K := by
  have := (Finset.card_le_univ s).trans (le_of_eq (Fintype.card_fin k))
  exact_mod_cast this.trans hk

/-- With a zero bound the family is empty. -/
theorem eq_empty_of_bound_zero {k : ℕ} (hk : k ≤ 0) (s : Finset (Fin k)) : s = ∅ := by
  ext i; exact ⟨fun _ => absurd i.2 (by omega), fun h => absurd h (Finset.notMem_empty i)⟩

/-- e-Bonferroni: for any completion with `k ≤ K` tests and any set of null
tests carrying e-values, rejecting a null whose e-value reaches `K/α` happens
with probability at most `α`, under arbitrary dependence. -/
theorem eBonferroni_bounded {k K : ℕ} (hk : k ≤ K) {α : ℚ} (hα : 0 < α) (law : Law Ω)
    (e : Fin k → Ω → ℚ) (nulls : Finset (Fin k)) (he : ∀ i ∈ nulls, IsEValue law (e i)) :
    eventMass law (anyOf nulls fun i ω => decide ((K : ℚ) / α ≤ e i ω)) ≤ α := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    rw [eq_empty_of_bound_zero hk nulls, eventMass_anyOf_empty]
    exact hα.le
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK
  have ht : 0 < (K : ℚ) / α := div_pos hKq hα
  refine (eventMass_exists_le law nulls _).trans ?_
  calc ∑ i ∈ nulls, eventMass law (fun ω => decide ((K : ℚ) / α ≤ e i ω))
      ≤ ∑ _i ∈ nulls, 1 / ((K : ℚ) / α) := Finset.sum_le_sum fun i hi => markov (he i hi) ht
    _ = nulls.card * (α / K) := by rw [Finset.sum_const, nsmul_eq_mul, one_div_div]
    _ ≤ K * (α / K) := mul_le_mul_of_nonneg_right (card_le_bound hk nulls) (div_nonneg hα.le hKq.le)
    _ = α := mul_div_cancel₀ α hKq.ne'

/-- A p-value for a null law: calibrated at every nonnegative threshold. -/
def IsPValue (law : Law Ω) (p : Ω → ℚ) : Prop :=
  ∀ t, 0 ≤ t → eventMass law (fun ω => decide (p ω ≤ t)) ≤ t

/-- Bonferroni: for any completion with `k ≤ K` tests and calibrated null
p-values, rejecting a null whose p-value is at most `α/K` happens with
probability at most `α`, under arbitrary dependence. -/
theorem bonferroni_bounded {k K : ℕ} (hk : k ≤ K) {α : ℚ} (hα : 0 < α) (law : Law Ω)
    (p : Fin k → Ω → ℚ) (nulls : Finset (Fin k)) (hp : ∀ i ∈ nulls, IsPValue law (p i)) :
    eventMass law (anyOf nulls fun i ω => decide (p i ω ≤ α / K)) ≤ α := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    rw [eq_empty_of_bound_zero hk nulls, eventMass_anyOf_empty]
    exact hα.le
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK
  refine (eventMass_exists_le law nulls _).trans ?_
  calc ∑ i ∈ nulls, eventMass law (fun ω => decide (p i ω ≤ α / K))
      ≤ ∑ _i ∈ nulls, α / K :=
        Finset.sum_le_sum fun i hi => hp i hi _ (div_nonneg hα.le hKq.le)
    _ = nulls.card * (α / K) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ K * (α / K) := mul_le_mul_of_nonneg_right (card_le_bound hk nulls) (div_nonneg hα.le hKq.le)
    _ = α := mul_div_cancel₀ α hKq.ne'

/-! ### e-BH at a count bound -/

/-- False discovery proportion of a rejection set. -/
def fdp {k : ℕ} (rejected nulls : Finset (Fin k)) : ℚ :=
  ((rejected ∩ nulls).card : ℚ) / max (rejected.card : ℚ) 1

/-- A rejection rule is self-consistent at bound `K` and level `α` when every
rejected e-value reaches `K / (α · |rejected|)`. -/
def SelfConsistent {k : ℕ} (K : ℕ) (α : ℚ) (e : Fin k → ℚ) (rejected : Finset (Fin k)) : Prop :=
  ∀ i ∈ rejected, (K : ℚ) ≤ α * rejected.card * e i

/-- Pointwise: a self-consistent rejection set's false discovery proportion is
at most `Σ_{null} α e_i / K`. -/
theorem fdp_le_sum {k K : ℕ} (hK : 0 < K) {α : ℚ} (hα : 0 < α) {e : Fin k → ℚ}
    (nonneg : ∀ i, 0 ≤ e i) {rejected : Finset (Fin k)} (sc : SelfConsistent K α e rejected)
    (nulls : Finset (Fin k)) : fdp rejected nulls ≤ ∑ i ∈ nulls, α * e i / K := by
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK
  have terms : ∀ i ∈ nulls, 0 ≤ α * e i / K := fun i _ =>
    div_nonneg (mul_nonneg hα.le (nonneg i)) hKq.le
  rcases rejected.eq_empty_or_nonempty with h | h
  · subst h; simpa [fdp] using Finset.sum_nonneg terms
  have hcard : (0 : ℚ) < rejected.card := by exact_mod_cast h.card_pos
  have hmax : max (rejected.card : ℚ) 1 = rejected.card :=
    max_eq_left (by exact_mod_cast h.card_pos)
  unfold fdp
  rw [hmax, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_div]
  calc ∑ i ∈ rejected ∩ nulls, ((1 : ℕ) : ℚ) / rejected.card
      ≤ ∑ i ∈ rejected ∩ nulls, α * e i / K := by
        apply Finset.sum_le_sum
        intro i hi
        have hsc := sc i (Finset.mem_inter.mp hi).1
        rw [Nat.cast_one, div_le_div_iff₀ hcard hKq, one_mul]
        linarith [hsc]
    _ ≤ ∑ i ∈ nulls, α * e i / K :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          (fun i hi _ => terms i hi)

/-- Any self-consistent rejection rule has FDR at most `α |nulls| / K` when the
null e-values are e-values, under arbitrary dependence. -/
theorem selfConsistent_fdr {k K : ℕ} (hK : 0 < K) {α : ℚ} (hα : 0 < α) (law : Law Ω)
    (e : Fin k → Ω → ℚ) (nonneg : ∀ i ω, 0 ≤ e i ω) (nulls : Finset (Fin k))
    (he : ∀ i ∈ nulls, IsEValue law (e i)) (rejected : Ω → Finset (Fin k))
    (sc : ∀ ω, SelfConsistent K α (fun i => e i ω) (rejected ω)) :
    expect law (fun ω => fdp (rejected ω) nulls) ≤ α * nulls.card / K := by
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK
  calc expect law (fun ω => fdp (rejected ω) nulls)
      ≤ expect law (fun ω => ∑ i ∈ nulls, α * e i ω / K) := by
        apply Finset.sum_le_sum
        intro ω _
        exact mul_le_mul_of_nonneg_left
          (fdp_le_sum hK hα (fun i => nonneg i ω) (sc ω) nulls) (law.nonnegative ω)
    _ = ∑ i ∈ nulls, α / K * expect law (e i) := by
        unfold expect
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro ω _
        ring
    _ ≤ ∑ _i ∈ nulls, α / K * 1 :=
        Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left (he i hi).2 (div_nonneg hα.le hKq.le)
    _ = α * nulls.card / K := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The number of e-BH rejections at bound `K`: the largest `r ≤ k` such that at
least `r` e-values reach `K / (α r)`. -/
def eBHCount {k : ℕ} (K : ℕ) (α : ℚ) (e : Fin k → ℚ) : ℕ :=
  Nat.findGreatest (fun r => r ≤ (Finset.univ.filter fun i => (K : ℚ) / (α * r) ≤ e i).card) k

/-- The e-BH rejection set at bound `K`. -/
def eBH {k : ℕ} (K : ℕ) (α : ℚ) (e : Fin k → ℚ) : Finset (Fin k) :=
  if eBHCount K α e = 0 then ∅
  else Finset.univ.filter fun i => (K : ℚ) / (α * eBHCount K α e) ≤ e i

/-- e-BH at bound `K` is self-consistent. -/
theorem eBH_selfConsistent {k K : ℕ} {α : ℚ} (hα : 0 < α) (e : Fin k → ℚ) :
    SelfConsistent K α e (eBH K α e) := by
  intro i hi
  unfold eBH at hi ⊢
  split at hi
  · simp at hi
  · rename_i hR
    rw [if_neg hR]
    set R := eBHCount K α e
    have spec : R ≤ (Finset.univ.filter fun i => (K : ℚ) / (α * R) ≤ e i).card :=
      Nat.findGreatest_spec (P := fun r => r ≤ (Finset.univ.filter fun i =>
        (K : ℚ) / (α * r) ≤ e i).card) (m := 0) (Nat.zero_le _) (Nat.zero_le _)
    have hRpos : (0 : ℚ) < R := by exact_mod_cast Nat.pos_of_ne_zero hR
    have hi' : (K : ℚ) / (α * R) ≤ e i := (Finset.mem_filter.mp hi).2
    have hK : (K : ℚ) ≤ α * R * e i := by
      rwa [div_le_iff₀ (mul_pos hα hRpos), mul_comm] at hi'
    have hR : (R : ℚ) ≤ (Finset.univ.filter fun i => (K : ℚ) / (α * R) ≤ e i).card := by
      exact_mod_cast spec
    have e_nonneg : 0 ≤ e i := le_trans (div_nonneg (Nat.cast_nonneg K)
      (mul_pos hα hRpos).le) hi'
    calc (K : ℚ) ≤ α * R * e i := hK
      _ ≤ α * (Finset.univ.filter fun i => (K : ℚ) / (α * R) ≤ e i).card * e i := by
        apply mul_le_mul_of_nonneg_right _ e_nonneg
        exact mul_le_mul_of_nonneg_left hR hα.le

/-- e-BH at the count bound controls FDR at `α` for every completion with at
most `K` tests. Unreported tests enter the procedure with e-value `0`, so they
are never rejected. Which tests are reported may depend on the outcome (for
instance, reporting only the largest e-value): the bound still holds. -/
theorem eBH_bounded {k K : ℕ} (hk : k ≤ K) {α : ℚ} (hα : 0 < α) (law : Law Ω)
    (e : Fin k → Ω → ℚ) (nonneg : ∀ i ω, 0 ≤ e i ω) (reported : Ω → Finset (Fin k))
    (nulls : Finset (Fin k)) (he : ∀ i ∈ nulls, IsEValue law (e i)) :
    expect law (fun ω => fdp (eBH K α (fun i => if i ∈ reported ω then e i ω else 0)) nulls) ≤ α := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    have zero : ∀ ω, fdp (eBH 0 α (fun i => if i ∈ reported ω then e i ω else 0)) nulls = 0 := by
      intro ω
      simp [fdp, eq_empty_of_bound_zero hk nulls]
    simp only [expect, zero, mul_zero, Finset.sum_const_zero]
    exact hα.le
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK
  let masked : Fin k → Ω → ℚ := fun i ω => if i ∈ reported ω then e i ω else 0
  have maskedE : ∀ i ∈ nulls, IsEValue law (masked i) := by
    intro i hi
    refine ⟨fun ω => by simp only [masked]; split <;> simp [nonneg i ω], ?_⟩
    refine le_trans ?_ (he i hi).2
    apply Finset.sum_le_sum
    intro ω _
    apply mul_le_mul_of_nonneg_left _ (law.nonnegative ω)
    simp only [masked]; split <;> simp [nonneg i ω]
  have bound := selfConsistent_fdr hK hα law masked
    (fun i ω => by simp only [masked]; split <;> simp [nonneg i ω]) nulls maskedE
    (fun ω => eBH K α fun i => masked i ω) (fun ω => eBH_selfConsistent hα _)
  refine bound.trans ?_
  rw [mul_div_assoc]
  apply mul_le_of_le_one_right hα.le
  rw [div_le_one hKq]
  exact_mod_cast (Finset.card_le_univ nulls).trans (by simpa using hk)

/-! ### Finite-horizon Ville -/

section Ville

variable {A : Type} [Fintype A]

/-- The probability, under the sequential law `kernel`, that `hit` holds when
the stopping rule `stop` (or the horizon) ends observation. `kernel past a` is
the conditional mass of the next symbol `a` after `past`. -/
def stoppedHitProb (kernel : List A → A → ℚ) (hit stop : List A → Bool) :
    ℕ → List A → ℚ
  | 0, past => if hit past then 1 else 0
  | n + 1, past =>
      if stop past then (if hit past then 1 else 0)
      else ∑ a, kernel past a * stoppedHitProb kernel hit stop n (past ++ [a])

/-- A nonnegative test supermartingale under the sequential law `kernel`, whose
conditional masses are nonnegative and sum to one. -/
structure TestSupermartingale (kernel : List A → A → ℚ) (M : List A → ℚ) : Prop where
  kernel_nonneg : ∀ past a, 0 ≤ kernel past a
  kernel_sum : ∀ past, ∑ a, kernel past a = 1
  nonneg : ∀ past, 0 ≤ M past
  super : ∀ past, ∑ a, kernel past a * M (past ++ [a]) ≤ M past

/-- The stopped crossing probability of level `c` is at most `M past / c`, for
every stopping rule and horizon. -/
theorem stoppedHitProb_le {kernel : List A → A → ℚ} {M : List A → ℚ}
    (hM : TestSupermartingale kernel M) {c : ℚ} (hc : 0 < c) (stop : List A → Bool) :
    ∀ n past, stoppedHitProb kernel (fun p => decide (c ≤ M p)) stop n past ≤ M past / c := by
  have base : ∀ past, (if decide (c ≤ M past) = true then (1 : ℚ) else 0) ≤ M past / c := by
    intro past
    split
    · rename_i h; exact (one_le_div hc).mpr (of_decide_eq_true h)
    · exact div_nonneg (hM.nonneg past) hc.le
  intro n
  induction n with
  | zero => exact base
  | succ n ih =>
      intro past
      simp only [stoppedHitProb]
      split
      · exact base past
      · calc ∑ a, kernel past a * stoppedHitProb kernel (fun p => decide (c ≤ M p)) stop n
              (past ++ [a])
            ≤ ∑ a, kernel past a * (M (past ++ [a]) / c) :=
              Finset.sum_le_sum fun a _ =>
                mul_le_mul_of_nonneg_left (ih _) (hM.kernel_nonneg past a)
          _ = (∑ a, kernel past a * M (past ++ [a])) / c := by
              rw [Finset.sum_div]; congr 1; funext a; ring
          _ ≤ M past / c := div_le_div_of_nonneg_right (hM.super past) hc.le

/-- Finite-horizon Ville: a test supermartingale started at most `1` reaches
`1/α` at any stopping time within any finite horizon with probability at most
`α`. Stopping the first time the level is reached gives the crossing event. -/
theorem ville_finite {kernel : List A → A → ℚ} {M : List A → ℚ}
    (hM : TestSupermartingale kernel M) (start : M [] ≤ 1) {α : ℚ} (hα : 0 < α)
    (stop : List A → Bool) (n : ℕ) :
    stoppedHitProb kernel (fun p => decide (1 / α ≤ M p)) stop n [] ≤ α := by
  have := stoppedHitProb_le hM (one_div_pos.mpr hα) stop n []
  calc _ ≤ M [] / (1 / α) := this
    _ = M [] * α := by rw [div_div_eq_mul_div, div_one]
    _ ≤ 1 * α := mul_le_mul_of_nonneg_right start hα.le
    _ = α := one_mul α

/-- The stopped event mass is a probability: it lies in `[0, 1]`. -/
theorem stoppedHitProb_mem_unit {kernel : List A → A → ℚ}
    (nonneg : ∀ past a, 0 ≤ kernel past a) (sum : ∀ past, ∑ a, kernel past a = 1)
    (hit stop : List A → Bool) :
    ∀ n past, 0 ≤ stoppedHitProb kernel hit stop n past ∧
      stoppedHitProb kernel hit stop n past ≤ 1 := by
  have base : ∀ past, 0 ≤ (if hit past then (1 : ℚ) else 0) ∧
      (if hit past then (1 : ℚ) else 0) ≤ 1 := fun past => by split <;> norm_num
  intro n
  induction n with
  | zero => exact base
  | succ n ih =>
      intro past
      simp only [stoppedHitProb]
      split
      · exact base past
      · refine ⟨Finset.sum_nonneg fun a _ => mul_nonneg (nonneg past a) (ih _).1, ?_⟩
        calc ∑ a, kernel past a * stoppedHitProb kernel hit stop n (past ++ [a])
            ≤ ∑ a, kernel past a * 1 :=
              Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (ih _).2 (nonneg past a)
          _ = 1 := by simp [sum]

/-- Ville's crossing form: stopping the first time `1/α` is reached, the
probability of reaching it within the horizon is at most `α`. -/
theorem ville_crossing {kernel : List A → A → ℚ} {M : List A → ℚ}
    (hM : TestSupermartingale kernel M) (start : M [] ≤ 1) {α : ℚ} (hα : 0 < α) (n : ℕ) :
    stoppedHitProb kernel (fun p => decide (1 / α ≤ M p)) (fun p => decide (1 / α ≤ M p)) n []
      ≤ α :=
  ville_finite hM start hα _ n

end Ville

/-! ### Split selection -/

/-- Selection reads only the first sample and the selected test reads only the
second. If the joint law is the product of the marginals (the independence
premise) and every candidate test is calibrated at `α` under the second
marginal, the selected test rejects with probability at most `α`. -/
theorem split_selection_valid {Ω₁ Ω₂ S : Type} [Fintype Ω₁] [Fintype Ω₂]
    (law₁ : Law Ω₁) (law₂ : Law Ω₂) (joint : Law (Ω₁ × Ω₂))
    (product : ∀ ω, joint.mass ω = law₁.mass ω.1 * law₂.mass ω.2)
    (select : Ω₁ → S) (test : S → Ω₂ → Bool) {α : ℚ}
    (calibrated : ∀ s, eventMass law₂ (test s) ≤ α) :
    eventMass joint (fun ω => test (select ω.1) ω.2) ≤ α := by
  unfold eventMass
  rw [Fintype.sum_prod_type]
  calc ∑ ω₁, ∑ ω₂, (if test (select ω₁) ω₂ then joint.mass (ω₁, ω₂) else 0)
      = ∑ ω₁, law₁.mass ω₁ * eventMass law₂ (test (select ω₁)) := by
        apply Finset.sum_congr rfl
        intro ω₁ _
        unfold eventMass
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω₂ _
        rw [product]
        split <;> simp
    _ ≤ ∑ ω₁, law₁.mass ω₁ * α :=
        Finset.sum_le_sum fun ω₁ _ =>
          mul_le_mul_of_nonneg_left (calibrated _) (law₁.nonnegative ω₁)
    _ = α := by rw [← Finset.sum_mul, law₁.normalized, one_mul]

end Lara.Process.Statistics
