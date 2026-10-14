import Mathlib.Probability.Martingale.OptionalStopping

/-!
Ville's inequality on an infinite horizon.

`Lara.Process.Statistics` proves Ville's inequality over a finite carrier with
exact rational masses and a fixed horizon (`ville_finite`). This module states
it for an arbitrary probability space, a filtration indexed by `ℕ` and no
horizon, which is what an e-process run without a fixed end needs:

* `ville_horizon`: within any horizon `n`, a nonnegative supermartingale reaches
  `ε` with mass at most `𝔼[f 0] / ε`. Stop at the first crossing before `n`,
  apply optional stopping to `-f` (a submartingale), then Markov's inequality.
* `ville_supermartingale`: the same bound for reaching `ε` at any time. The
  crossing events grow with the horizon, so continuity from below passes the
  bound to their union.
* `ville_anytime`: a test supermartingale (`𝔼[f 0] ≤ 1`) ever reaches `1/α`
  with probability at most `α`.
* `ville_stopped`: the same bound for the value at any random time, however it
  is chosen, on the event that the time is finite. The time need not be a
  stopping time: it is bounded by the crossing event.

Mathlib's `maximal_ineq` is Doob's inequality for nonnegative submartingales and
does not give these bounds; they are proved here from its optional stopping
theorem.
-/

namespace Lara.Process.Statistics

open MeasureTheory
open scoped NNReal ENNReal ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  {f : ℕ → Ω → ℝ}

/-- Finite-horizon Ville for a nonnegative supermartingale on a finite measure:
`ε` times the mass of reaching `ε` by time `n` is at most `𝔼[f 0]`. -/
theorem ville_horizon [IsFiniteMeasure μ] (hf : Supermartingale f 𝒢 μ) (hnonneg : 0 ≤ f)
    (ε : ℝ≥0) (n : ℕ) :
    ε * μ {ω | ∃ k ≤ n, (ε : ℝ) ≤ f k ω} ≤ ENNReal.ofReal (μ[f 0]) := by
  set τ : Ω → ℕ∞ := fun ω => (hittingBtwn f {y : ℝ | (ε : ℝ) ≤ y} 0 n ω : ℕ)
  set g : Ω → ℝ := stoppedValue f τ
  have hτ : IsStoppingTime 𝒢 τ :=
    hf.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hbdd : ∀ ω, τ ω ≤ n := fun ω => by
    simp only [τ]
    exact_mod_cast hittingBtwn_le (u := f) (s := {y : ℝ | (ε : ℝ) ≤ y}) (n := 0) (m := n) ω
  have hg_int : Integrable g μ := by
    have := hf.neg.integrable_stoppedValue hτ hbdd
    simpa [g, stoppedValue] using this.neg
  -- Optional stopping for the submartingale `-f` between times `0` and `τ`.
  have hstop : μ[g] ≤ μ[f 0] := by
    have := hf.neg.expected_stoppedValue_mono (isStoppingTime_const 𝒢 0) hτ
      (fun _ => zero_le) hbdd
    change ∫ ω, -f 0 ω ∂μ ≤ ∫ ω, -g ω ∂μ at this
    rw [integral_neg, integral_neg] at this
    linarith
  have hsub : {ω | ∃ k ≤ n, (ε : ℝ) ≤ f k ω} ⊆ {ω | (ε : ℝ) ≤ g ω} := by
    rintro ω ⟨k, hk, h⟩
    exact stoppedValue_hittingBtwn_mem (s := {y : ℝ | (ε : ℝ) ≤ y}) ⟨k, ⟨Nat.zero_le k, hk⟩, h⟩
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => hnonneg _ ω) hg_int (ε : ℝ)
  calc (ε : ℝ≥0∞) * μ {ω | ∃ k ≤ n, (ε : ℝ) ≤ f k ω}
      ≤ ε * μ {ω | (ε : ℝ) ≤ g ω} := by gcongr
    _ = ENNReal.ofReal ((ε : ℝ) * μ.real {ω | (ε : ℝ) ≤ g ω}) := by
        rw [ENNReal.ofReal_mul ε.coe_nonneg, ENNReal.ofReal_coe_nnreal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (μ[g]) := ENNReal.ofReal_le_ofReal hmarkov
    _ ≤ ENNReal.ofReal (μ[f 0]) := ENNReal.ofReal_le_ofReal hstop

/-- Infinite-horizon Ville for a nonnegative supermartingale on a finite
measure: `ε` times the mass of ever reaching `ε` is at most `𝔼[f 0]`. -/
theorem ville_supermartingale [IsFiniteMeasure μ] (hf : Supermartingale f 𝒢 μ)
    (hnonneg : 0 ≤ f) (ε : ℝ≥0) :
    ε * μ {ω | ∃ n, (ε : ℝ) ≤ f n ω} ≤ ENNReal.ofReal (μ[f 0]) := by
  have hU : {ω | ∃ n, (ε : ℝ) ≤ f n ω} = ⋃ n, {ω | ∃ k ≤ n, (ε : ℝ) ≤ f k ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun ⟨n, h⟩ => ⟨n, n, le_rfl, h⟩, fun ⟨_, k, _, h⟩ => ⟨k, h⟩⟩
  have hmono : Monotone fun n => {ω | ∃ k ≤ n, (ε : ℝ) ≤ f k ω} :=
    fun _ _ hab _ ⟨k, hk, h⟩ => ⟨k, hk.trans hab, h⟩
  rw [hU, hmono.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun n => ville_horizon hf hnonneg ε n

/-- Ville's inequality: a test supermartingale, nonnegative with `𝔼[f 0] ≤ 1`,
ever reaches `1/α` with probability at most `α`. -/
theorem ville_anytime [IsProbabilityMeasure μ] (hf : Supermartingale f 𝒢 μ)
    (hnonneg : 0 ≤ f) (start : μ[f 0] ≤ 1) {α : ℝ} (hα : 0 < α) :
    μ {ω | ∃ n, 1 / α ≤ f n ω} ≤ ENNReal.ofReal α := by
  have hε : ((Real.toNNReal (1 / α) : ℝ≥0) : ℝ) = 1 / α :=
    Real.coe_toNNReal _ (one_div_pos.mpr hα).le
  have h := ville_supermartingale hf hnonneg (Real.toNNReal (1 / α))
  rw [hε] at h
  have hle : ENNReal.ofReal (1 / α) * μ {ω | ∃ n, 1 / α ≤ f n ω} ≤ 1 :=
    h.trans (ENNReal.ofReal_le_one.mpr start)
  have hinv : ENNReal.ofReal (1 / α) = (ENNReal.ofReal α)⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hα]
  rw [hinv] at hle
  have hne0 : ENNReal.ofReal α ≠ 0 := by simpa using hα
  calc μ {ω | ∃ n, 1 / α ≤ f n ω}
      = ENNReal.ofReal α * ((ENNReal.ofReal α)⁻¹ * μ {ω | ∃ n, 1 / α ≤ f n ω}) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hne0 ENNReal.ofReal_ne_top, one_mul]
    _ ≤ ENNReal.ofReal α * 1 := by gcongr
    _ = ENNReal.ofReal α := mul_one _

/-- Ville at an arbitrary random time: whatever rule picks the time `τ`, the
value there is at least `1/α` with probability at most `α`, on the event that
`τ` is finite. `τ` need not be a stopping time or even measurable. -/
theorem ville_stopped [IsProbabilityMeasure μ] (hf : Supermartingale f 𝒢 μ)
    (hnonneg : 0 ≤ f) (start : μ[f 0] ≤ 1) {α : ℝ} (hα : 0 < α) (τ : Ω → ℕ∞) :
    μ {ω | ∃ n : ℕ, τ ω = n ∧ 1 / α ≤ f n ω} ≤ ENNReal.ofReal α :=
  (measure_mono (by rintro ω ⟨n, -, h⟩; exact ⟨n, h⟩)).trans (ville_anytime hf hnonneg start hα)

end Lara.Process.Statistics
