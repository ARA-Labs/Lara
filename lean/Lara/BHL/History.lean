import Lara.BHL.Types
import Mathlib.Data.Multiset.AddSub
import Mathlib.Logic.Function.Basic

/-!
The canonical history records mathematical dataset values, not dataset names.
Each test occurrence contributes one multiset entry, including repeated tests.
Named history variables are read through the current dataset valuation.
-/

namespace Lara.BHL

universe u

/-- A finite ledger over an arbitrary, possibly infinite, dataset value type. -/
abbrev History (D : Type u) := Multiset (D × TestId)

namespace History

variable {D : Type u}

/-- The initial ledger contains no test occurrences. -/
def empty : History D := 0

@[simp] theorem empty_eq_zero : (empty : History D) = 0 := rfl

/-- Recording adds exactly one occurrence; it never deduplicates an entry. -/
def record (H : History D) (d : D) (test : TestId) : History D :=
  (d, test) ::ₘ H

@[simp] theorem record_card (H : History D) (d : D) (test : TestId) :
    Multiset.card (record H d test) = Multiset.card H + 1 :=
  Multiset.card_cons _ _

/-- Previous entries, including their multiplicities, remain in the ledger. -/
theorem record_preserves_entries (H : History D) (d : D) (test : TestId) :
    H ≤ record H d test :=
  Multiset.le_cons_self _ _

theorem record_strict (H : History D) (d : D) (test : TestId) :
    H < record H d test :=
  Multiset.lt_cons_self _ _

/-- Even a repeated or unobserved extra test changes the full ledger. -/
theorem record_ne_self (H : History D) (d : D) (test : TestId) :
    record H d test ≠ H :=
  ne_of_gt (record_strict H d test)

/-- Ledger equality ignores recording order, but not multiplicity. -/
theorem record_comm (H : History D) (d₁ d₂ : D) (test₁ test₂ : TestId) :
    record (record H d₁ test₁) d₂ test₂ =
      record (record H d₂ test₂) d₁ test₁ :=
  Multiset.cons_swap _ _ _

/-- The unbounded reference operation for any finite number of repetitions. -/
def recordRepeated (H : History D) (d : D) (test : TestId) : Nat → History D
  | 0 => H
  | n + 1 => record (recordRepeated H d test n) d test

@[simp] theorem recordRepeated_zero (H : History D) (d : D) (test : TestId) :
    recordRepeated H d test 0 = H := rfl

@[simp] theorem recordRepeated_succ (H : History D) (d : D) (test : TestId)
    (n : Nat) :
    recordRepeated H d test (n + 1) = record (recordRepeated H d test n) d test := rfl

section Count

variable [DecidableEq D]

/-- The derived multiplicity of a mathematical dataset/test pair. -/
def count (H : History D) (d : D) (test : TestId) : Nat :=
  Multiset.count (d, test) H

@[simp] theorem empty_count (d : D) (test : TestId) :
    count empty d test = 0 :=
  Multiset.count_zero _

@[simp] theorem record_count_self (H : History D) (d : D) (test : TestId) :
    count (record H d test) d test = count H d test + 1 :=
  Multiset.count_cons_self _ _

theorem record_count_other (H : History D) (d d' : D) (test test' : TestId)
    (h : (d', test') ≠ (d, test)) :
    count (record H d test) d' test' = count H d' test' :=
  Multiset.count_cons_of_ne h _

/-- Repetition increases the existing count, rather than replacing it. -/
theorem recordRepeated_count_self (H : History D) (d : D) (test : TestId)
    (n : Nat) :
    count (recordRepeated H d test n) d test = count H d test + n := by
  induction n with
  | zero => simp only [recordRepeated_zero, Nat.add_zero]
  | succ n ih =>
      simp only [recordRepeated_succ, record_count_self, ih, Nat.add_succ]

theorem recordRepeated_count_other (H : History D) (d d' : D)
    (test test' : TestId) (h : (d', test') ≠ (d, test)) (n : Nat) :
    count (recordRepeated H d test n) d' test' = count H d' test' := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [recordRepeated_succ, record_count_other _ _ _ _ _ h, ih]

/-- All value-indexed multiplicities characterize the full canonical ledger. -/
theorem eq_iff_counts (H H' : History D) :
    H = H' ↔ ∀ d test, count H d test = count H' d test := by
  constructor
  · intro h
    subst H'
    intro d test
    rfl
  · intro h
    apply Multiset.ext.2
    intro entry
    exact h entry.1 entry.2

end Count

end History

variable {D : Type u}

/-- A named history variable is a lookup into the canonical value-indexed ledger. -/
def historyCount [DecidableEq D] (datasetVal : DatasetId → D) (H : History D)
    (name : DatasetId) (test : TestId) : Nat :=
  History.count H (datasetVal name) test

@[simp] theorem history_count_lookup [DecidableEq D] (datasetVal : DatasetId → D)
    (H : History D) (name : DatasetId) (test : TestId) :
    historyCount datasetVal H name test = History.count H (datasetVal name) test := rfl

/-- Equal dataset values give equal counters, regardless of their symbolic names. -/
theorem history_count_alias [DecidableEq D] (datasetVal : DatasetId → D)
    (H : History D) (name₁ name₂ : DatasetId) (test : TestId)
    (h : datasetVal name₁ = datasetVal name₂) :
    historyCount datasetVal H name₁ test = historyCount datasetVal H name₂ test := by
  simp only [historyCount, h]

/-- Reassignment changes the lookup, never the previously recorded ledger. -/
theorem history_count_reassignment [DecidableEq D]
    (datasetVal' : DatasetId → D) (H : History D)
    (name : DatasetId) (test : TestId) (d : D) (h : datasetVal' name = d) :
    historyCount datasetVal' H name test = History.count H d test := by
  simp only [historyCount, h]

@[simp] theorem history_count_update_self [DecidableEq D]
    (datasetVal : DatasetId → D) (H : History D) (name : DatasetId)
    (test : TestId) (d : D) :
    historyCount (Function.update datasetVal name d) H name test =
      History.count H d test := by
  simp only [historyCount, Function.update_self]

theorem history_count_update_other [DecidableEq D]
    (datasetVal : DatasetId → D) (H : History D) (name name' : DatasetId)
    (test : TestId) (d : D) (h : name' ≠ name) :
    historyCount (Function.update datasetVal name d) H name' test =
      historyCount datasetVal H name' test := by
  simp only [historyCount, Function.update_of_ne h]

/-- Finite test syntax whose two connectives both retain every leaf occurrence. -/
inductive TestCombination (D : Type u) where
  | leaf : D → TestId → TestCombination D
  | disj : TestCombination D → TestCombination D → TestCombination D
  | conj : TestCombination D → TestCombination D → TestCombination D

/-- Flatten test syntax into a multiset, retaining repeated leaves. -/
def decomposeTests : TestCombination D → History D
  | .leaf d test => {(d, test)}
  | .disj left right => decomposeTests left + decomposeTests right
  | .conj left right => decomposeTests left + decomposeTests right

@[simp] theorem decompose_leaf (d : D) (test : TestId) :
    decomposeTests (.leaf d test) = {(d, test)} := rfl

@[simp] theorem decompose_disj (left right : TestCombination D) :
    decomposeTests (.disj left right) = decomposeTests left + decomposeTests right := rfl

@[simp] theorem decompose_conj (left right : TestCombination D) :
    decomposeTests (.conj left right) = decomposeTests left + decomposeTests right := rfl

theorem decompose_disj_comm (left right : TestCombination D) :
    decomposeTests (.disj left right) = decomposeTests (.disj right left) :=
  Multiset.add_comm _ _

theorem decompose_conj_comm (left right : TestCombination D) :
    decomposeTests (.conj left right) = decomposeTests (.conj right left) :=
  Multiset.add_comm _ _

theorem decompose_disj_assoc (a b c : TestCombination D) :
    decomposeTests (.disj (.disj a b) c) = decomposeTests (.disj a (.disj b c)) :=
  Multiset.add_assoc _ _ _

theorem decompose_conj_assoc (a b c : TestCombination D) :
    decomposeTests (.conj (.conj a b) c) = decomposeTests (.conj a (.conj b c)) :=
  Multiset.add_assoc _ _ _

@[simp] theorem decompose_count_leaf_self [DecidableEq D] (d : D) (test : TestId) :
    History.count (decomposeTests (.leaf d test)) d test = 1 :=
  Multiset.count_singleton_self _

@[simp] theorem decompose_count_disj [DecidableEq D]
    (left right : TestCombination D) (d : D) (test : TestId) :
    History.count (decomposeTests (.disj left right)) d test =
      History.count (decomposeTests left) d test +
        History.count (decomposeTests right) d test :=
  Multiset.count_add _ _ _

@[simp] theorem decompose_count_conj [DecidableEq D]
    (left right : TestCombination D) (d : D) (test : TestId) :
    History.count (decomposeTests (.conj left right)) d test =
      History.count (decomposeTests left) d test +
        History.count (decomposeTests right) d test :=
  Multiset.count_add _ _ _

/-- A repeated pair occurs twice, even under disjunction. -/
@[simp] theorem decompose_repeated_pair_disj [DecidableEq D] (d : D) (test : TestId) :
    History.count (decomposeTests (.disj (.leaf d test) (.leaf d test))) d test = 2 := by
  simp only [decompose_count_disj, decompose_count_leaf_self]

@[simp] theorem decompose_repeated_pair_conj [DecidableEq D] (d : D) (test : TestId) :
    History.count (decomposeTests (.conj (.leaf d test) (.leaf d test))) d test = 2 := by
  simp only [decompose_count_conj, decompose_count_leaf_self]

end Lara.BHL
