import Lara.Process.Statistics
import Lara.Process.Vocabulary
import Mathlib.Order.WithBot

/-!
R4: the warranted level of a ledger, which fails closed by type.

`warrantedLevel` returns the smallest level at which the ledger's reported
statistic is warranted under its count bound, or `⊤` (no warrant) when any field
the guarantee needs is missing. An e-value `e` under a certified bound `K` is
warranted at `K / e`, the e-Bonferroni threshold; a p-value `p` at `K · p`, the
Bonferroni threshold. A missing count bound is never replaced by the number of
reported tests, and a bound of zero certifies no test at all.

Online procedures replay their levels from the full ordered ledger.
`onlineLevel` is a simple wealth-spending rule: it spends half its wealth on
each test and earns `reward` on a rejection. Replaying it over a ledger with an
omitted non-rejection overstates the wealth (`Lara.Examples.ProcessStatistics.
online_replay_anticonservative`), so online replay needs a complete ledger,
not a count bound.
-/

namespace Lara.Process.Statistics

open Lara.Process

/-- Whether a reported statistic is a p-value or an e-value. -/
inductive StatKind where
  | pValue
  | eValue
  deriving DecidableEq, Repr

/-- The fields a ledger must certify for a family-wise guarantee. Every field is
optional: a record may simply not say. -/
structure Ledger where
  kind : Option StatKind
  value : Option ℚ
  countBound : Option ℕ
  guarantee : Option GuaranteeClass
  deriving DecidableEq, Repr

/-- The warranted level, `⊤` when no warrant follows. -/
def warrantedLevel (l : Ledger) : WithTop ℚ :=
  match l.kind, l.value, l.countBound, l.guarantee with
  | some .eValue, some e, some K, some .fwer => if 0 < e ∧ 0 < K then ((K : ℚ) / e : ℚ) else ⊤
  | some .pValue, some p, some K, some .fwer => if 0 < p ∧ 0 < K then ((K : ℚ) * p : ℚ) else ⊤
  | _, _, _, _ => ⊤

/-- Any missing required field yields no warrant. -/
theorem warrantedLevel_failClosed (l : Ledger)
    (missing : l.kind = none ∨ l.value = none ∨ l.countBound = none ∨ l.guarantee = none) :
    warrantedLevel l = ⊤ := by
  unfold warrantedLevel
  rcases missing with h | h | h | h <;> rw [h] <;>
    rcases l.kind with _ | _ | _ <;> rcases l.value with _ | _ <;>
    rcases l.countBound with _ | _ <;> rcases l.guarantee with _ | _ | _ | _ <;> rfl

/-- A guarantee class other than FWER yields no family-wise warrant. -/
theorem warrantedLevel_needs_fwer (l : Ledger) {g : GuaranteeClass} (h : l.guarantee = some g)
    (notFwer : g ≠ .fwer) : warrantedLevel l = ⊤ := by
  unfold warrantedLevel
  rw [h]
  cases g with
  | fwer => exact absurd rfl notFwer
  | fdr | mfdr =>
      rcases l.kind with _ | _ | _ <;> rcases l.value with _ | _ <;>
        rcases l.countBound with _ | _ <;> rfl

/-- An e-value ledger warranted at a finite level `a` has an e-value reaching the
e-Bonferroni threshold `K / a` of its certified bound, so `eBonferroni_bounded`
gives family-wise error at most `a` for every completion with at most `K` tests. -/
theorem warrantedLevel_eValue {l : Ledger} {a : ℚ} (level : warrantedLevel l = a)
    (kind : l.kind = some .eValue) :
    ∃ e K, l.value = some e ∧ l.countBound = some K ∧ 0 < a ∧ (K : ℚ) / a ≤ e := by
  unfold warrantedLevel at level
  rw [kind] at level
  rcases hv : l.value with _ | e <;> rw [hv] at level
  · cases level
  rcases hK : l.countBound with _ | K <;> rw [hK] at level
  · cases level
  rcases hg : l.guarantee with _ | g <;> rw [hg] at level
  · cases level
  cases g
  · simp only at level
    split at level
    · rename_i pos
      have eq : (K : ℚ) / e = a := WithTop.coe_injective level
      subst eq
      have hKq : (0 : ℚ) < K := by exact_mod_cast pos.2
      exact ⟨e, K, rfl, rfl, div_pos hKq pos.1, le_of_eq (div_div_cancel₀ hKq.ne')⟩
    · cases level
  all_goals cases level

/-- A p-value ledger warranted at a finite level `a` has a p-value at or below
the Bonferroni threshold `a / K` of its certified bound, so `bonferroni_bounded`
gives family-wise error at most `a` for every completion with at most `K` tests. -/
theorem warrantedLevel_pValue {l : Ledger} {a : ℚ} (level : warrantedLevel l = a)
    (kind : l.kind = some .pValue) :
    ∃ p K, l.value = some p ∧ l.countBound = some K ∧ 0 < a ∧ p ≤ a / K := by
  unfold warrantedLevel at level
  rw [kind] at level
  rcases hv : l.value with _ | p <;> rw [hv] at level
  · cases level
  rcases hK : l.countBound with _ | K <;> rw [hK] at level
  · cases level
  rcases hg : l.guarantee with _ | g <;> rw [hg] at level
  · cases level
  cases g
  · simp only at level
    split at level
    · rename_i pos
      have eq : (K : ℚ) * p = a := WithTop.coe_injective level
      subst eq
      have hKq : (0 : ℚ) < K := by exact_mod_cast pos.2
      exact ⟨p, K, rfl, rfl, mul_pos hKq pos.1, le_of_eq (by field_simp)⟩
    · cases level
  all_goals cases level

/-- The level an online wealth-spending rule assigns to the next test after
replaying an ordered ledger of rejection outcomes: spend half the wealth on
each test, earn `reward` on each rejection. -/
def onlineLevel (reward : ℚ) : ℚ → List Bool → ℚ
  | wealth, [] => wealth / 2
  | wealth, rejected :: rest =>
      onlineLevel reward (wealth - wealth / 2 + if rejected then reward else 0) rest

end Lara.Process.Statistics
