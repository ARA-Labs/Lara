import Lara.Process.Ledger
import Lara.Process.Coverage
import Lara.Process.Order
import Lara.Examples.ProcessCore

/-!
Fixtures: what a count bound can and cannot certify, and the counterexample
twin of every positive statistical result.

* `evalue_calibrated`, `countBounded_determinate`, `countBounded_rejection_valid`,
  `warrantsRejection_valid`:
  a calibrated e-value fixture with score `60`. Under an admitted count bound
  of two and `α = 1/20` the bound-adjusted threshold is `40`, every compatible
  completion warrants the rejection, and e-Bonferroni gives FWER at most `α`.
  Allowing four tests introduces threshold `80` and a failing completion.
* `partialRecord_unknown_countBounded`: the original BHL conclusion stays
  `unknown` under a bound of two, because its one-test and two-test completions
  both satisfy it.
* `optional_stopping_inflation`: a p-value calibrated at every fixed time
  inflates past its level under data-dependent stopping, while
  `likelihoodRatio_ville` keeps a test martingale's crossing probability at its
  level.
* `same_data_selection_inflates`, `same_data_identical_record`,
  `dependent_split_invalid`: selecting on the test data, or on structurally
  separate but dependent data, breaks the level that `split_selection_valid`
  guarantees under independence, although the reported record can be the same.
* `online_replay_anticonservative`: replaying an online rule over a ledger
  missing a non-rejection grants a larger level, although both ledgers satisfy
  the same count bound.
* `mfdr_not_fdr`: an outcome law with mFDR at most `α` and FDR above it, so the
  guarantee class must be stated.
* `eBH_reported_count_unsound`: running e-BH with the reported count instead of
  the bound inflates the error.
* `warrantedLevel_fixtures`: the ledger level fails closed.
-/

namespace Lara.Examples.ProcessStatistics

open Lara.BHL.FiniteProbability
open Lara.Process
open Lara.Process.Statistics

/-! ### The calibrated e-value fixture -/

/-- The null law of the fixture: outcome `true` has mass `1/60`. -/
def evLaw : Law Bool where
  mass b := if b then 1 / 60 else 59 / 60
  nonnegative b := by cases b <;> norm_num
  normalized := by simp; norm_num

/-- The e-value: `60` on `true`, `0` otherwise. -/
def evalue (b : Bool) : ℚ := if b then 60 else 0

/-- The fixture is a valid e-value and its reported score has positive null
mass. -/
theorem evalue_calibrated : IsEValue evLaw evalue ∧ 0 < evLaw.mass true ∧ evalue true = 60 := by
  refine ⟨⟨fun b => by cases b <;> norm_num [evalue], ?_⟩, by norm_num [evLaw], rfl⟩
  simp [expect, evLaw, evalue]

def alpha : ℚ := 1 / 20
def familyF : FamilyId := ⟨0⟩

/-- The `i+1`-th run of the family. -/
def runEvent (i : Nat) : Stamped := ⟨⟨i⟩, .run ⟨i⟩ ⟨0⟩ ⟨0⟩ [] familyF⟩

/-- Completion `i` has `i + 1` runs in the family; only the first is reported. -/
def completionTrace (i : Fin 4) : ProcessHistory :=
  ⟨⟨100⟩, .commitPlan ⟨0⟩ ⟨0⟩ ⟨0⟩⟩ :: (List.range (i.val + 1)).map runEvent

def reported : List Stamped := [runEvent 0]

def familyScope : CoverageScope := ⟨[.analysisRun], some familyF, none, none, 10⟩

def noPolicy : Empty → ProcessHistory → List Stamped → Prop := fun e => e.elim

instance (p : Empty) (h : ProcessHistory) (r : List Stamped) : Decidable (noPolicy p h r) :=
  p.elim

/-- Completions compatible with the reported run under a count bound. -/
def boundedCompat (bound : Nat) (i : Fin 4) : Prop :=
  ValidHistory (completionTrace i) ∧ (∀ e ∈ reported, e ∈ completionTrace i) ∧
    (RecordCoverage.countBounded familyScope bound).Allowed noPolicy (completionTrace i) reported

instance (bound : Nat) : DecidablePred (boundedCompat bound) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The bound-adjusted e-Bonferroni rejection at the admitted bound `K̄ = 2`: it
is warranted in a completion when the completion has at most two family tests,
so `eBonferroni_bounded` applies to it, and the score reaches `2/α`. -/
def warrantsRejection (i : Fin 4) : Prop :=
  familyCount (completionTrace i) familyF ≤ 2 ∧ (2 : ℚ) / alpha ≤ evalue true

instance : DecidablePred warrantsRejection := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Under a count bound of two, every compatible completion warrants rejecting
at the bound-adjusted threshold `2/α = 40 ≤ 60`; allowing four tests admits
completions with three and four tests, where the two-test rejection is not
warranted and the four-test threshold `4/α = 80` exceeds the score. -/
theorem countBounded_determinate :
    (2 : ℚ) / alpha = 40 ∧ (4 : ℚ) / alpha = 80 ∧ ¬ (4 : ℚ) / alpha ≤ evalue true ∧
      verdict (boundedCompat 2) warrantsRejection = .certainTrue ∧
      verdict (boundedCompat 4) warrantsRejection = .unknown := by
  refine ⟨by norm_num [alpha], by norm_num [alpha], by norm_num [alpha, evalue],
    by decide +kernel, by decide +kernel⟩

/-- For every completion with at most two tests and any dependence among their
e-values, rejecting a null whose e-value reaches `2/α` has probability at most
`α`. -/
theorem countBounded_rejection_valid {k : ℕ} (hk : k ≤ 2) {Ω : Type} [Fintype Ω] (law : Law Ω)
    (e : Fin k → Ω → ℚ) (nulls : Finset (Fin k)) (he : ∀ i ∈ nulls, IsEValue law (e i)) :
    eventMass law (anyOf nulls fun i ω => decide ((2 : ℚ) / alpha ≤ e i ω)) ≤ alpha := by
  exact eBonferroni_bounded (α := alpha) hk (by norm_num [alpha]) law e nulls he

/-- A warranted completion's family-wise error is controlled: for its family of
tests, with any null e-values under any joint law, the bound-adjusted rejection
has probability at most `α`. -/
theorem warrantsRejection_valid {i : Fin 4} (warranted : warrantsRejection i) {Ω : Type}
    [Fintype Ω] (law : Law Ω) (e : Fin (familyCount (completionTrace i) familyF) → Ω → ℚ)
    (nulls : Finset (Fin (familyCount (completionTrace i) familyF)))
    (he : ∀ j ∈ nulls, IsEValue law (e j)) :
    eventMass law (anyOf nulls fun j ω => decide ((2 : ℚ) / alpha ≤ e j ω)) ≤ alpha :=
  countBounded_rejection_valid warranted.1 law e nulls he

/-! ### The original BHL conclusion under a count bound -/

section PartialRecord

open Lara.BHL
open Lara.Examples.BHLPartialRecord
open Lara.Examples.ProcessCore

/-- A count bound of two on the complete BHL ledger. -/
def ledgerBoundTwo : Assumptions Completion _root_.Unit :=
  ⟨fun c _ => (outcome c).state.ledger.card ≤ 2⟩

instance (c : Completion) : DecidablePred (ledgerBoundTwo.Allowed c) :=
  fun _ => inferInstanceAs (Decidable (_ ≤ _))

/-- Both completions of the BHL partial record have at most two tests, so the
bound does not make its method conclusion determinate. -/
theorem partialRecord_unknown_countBounded :
    verdictOf (Compatible partialModel ledgerBoundTwo record) conclusionHolds = .unknown := by
  have cards := different_full_ledgers
  have compat : ∀ c, Compatible partialModel ledgerBoundTwo record (c, ()) := by
    intro c
    refine ⟨(record_compatible c).1, ?_, (record_compatible c).2⟩
    cases c
    · show (outcome .reportedOnly).state.ledger.card ≤ 2
      rw [cards.1]; decide
    · show (outcome .unreportedEarlier).state.ledger.card ≤ 2
      rw [cards.2]
  exact (verdictOf_unknown_iff _ _).mpr
    ⟨(.reportedOnly, ()), (.unreportedEarlier, ()), compat _, compat _,
      reported_satisfaction, omitted_test_not_satisfaction⟩

end PartialRecord

/-! ### Optional stopping -/

/-- Fair coin flips under the null. -/
def coin : List Bool → Bool → ℚ := fun _ _ => 1 / 2

/-- A p-value calibrated at every fixed time: `1/2` after a `true` flip. -/
def pv (past : List Bool) : ℚ := if past.getLast? = some true then 1 / 2 else 1

def crossed (past : List Bool) : Bool := decide (pv past ≤ 1 / 2)

/-- At the fixed time two, the p-value is calibrated at `1/2`; stopping as soon
as it crosses gives probability `3/4`. -/
theorem optional_stopping_inflation :
    stoppedHitProb coin crossed (fun _ => false) 2 [] = 1 / 2 ∧
      stoppedHitProb coin crossed crossed 2 [] = 3 / 4 := by
  constructor <;> simp [stoppedHitProb, coin, crossed, pv] <;> norm_num

/-- The likelihood ratio of a `3/4`-biased coin against the fair null: each flip
multiplies by `3/2` (heads) or `1/2` (tails). It is a test martingale. -/
def likelihoodRatio (flips : List Bool) : ℚ :=
  (flips.map fun b => if b then (3 / 2 : ℚ) else 1 / 2).prod

theorem likelihoodRatio_martingale : TestSupermartingale coin likelihoodRatio := by
  refine ⟨fun _ _ => by norm_num [coin], fun _ => by norm_num [coin], fun past => ?_, ?_⟩
  · apply List.prod_nonneg
    intro x hx
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
    split <;> norm_num
  · intro past
    simp only [likelihoodRatio, coin, Fintype.sum_bool, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, if_true, Bool.false_eq_true,
      if_false]
    exact le_of_eq (by ring)

/-- Ville at `α = 1/4` for the likelihood-ratio martingale: the
probability of reaching `4` within four flips (it takes four heads, mass
`1/16`) is at most `1/4`. -/
theorem likelihoodRatio_ville :
    stoppedHitProb coin (fun p => decide (1 / (1 / 4) ≤ likelihoodRatio p))
      (fun p => decide (1 / (1 / 4) ≤ likelihoodRatio p)) 4 [] ≤ 1 / 4 :=
  ville_crossing likelihoodRatio_martingale (by simp [likelihoodRatio]) (by norm_num) 4

/-! ### Selection -/

/-- A fair coin. -/
def fair : Law Bool where
  mass _ := 1 / 2
  nonnegative _ := by norm_num
  normalized := by simp

/-- A concrete p-value: under a fair coin, `1/2` after heads and `1` after tails
is calibrated at every nonnegative threshold, so `IsPValue` is inhabited. -/
theorem fair_pvalue : IsPValue fair fun b => if b then 1 / 2 else 1 := by
  intro t ht
  simp only [eventMass, fair, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false,
    decide_eq_true_eq]
  split_ifs <;> linarith

/-- Analysis `s` rejects when its outcome is `true`; each is calibrated at `1/2`. -/
def analysis (s : Bool) (ω : Bool × Bool) : Bool := if s then ω.2 else ω.1

/-- Selection on the test data: pick an analysis that rejects, if any. Each
analysis alone is calibrated at `1/2`, but the selected one rejects with
probability `3/4`. The reported record (selected analysis, rejection) is the
same whichever data selection read. -/
theorem same_data_selection_inflates :
    eventMass (product fair fair) (analysis false) = 1 / 2 ∧
      eventMass (product fair fair) (analysis true) = 1 / 2 ∧
      eventMass (product fair fair) (fun ω => analysis (!ω.1) ω) = 3 / 4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [eventMass, analysis, product, fair, Fintype.sum_prod_type] <;> norm_num

/-- What a selection reports: the selected analysis and whether it rejected. -/
def selectionRecord (selected : Bool) (ω : Bool × Bool) : Bool × Bool :=
  (selected, analysis selected ω)

/-- Split selection reads an independent coin `c` and tests on the analysis
outcomes; same-data selection reads the outcomes themselves. Both can report
exactly the same record, "analysis `true` was selected and rejected", so the
record does not reveal which data the selection read, while the selected test's
level is `1/2` in the split world and `3/4` in the same-data world. -/
theorem same_data_identical_record :
    selectionRecord true (false, true) = selectionRecord (!(false : Bool)) (false, true) ∧
      eventMass (product fair (product fair fair))
          (fun ω => analysis ω.1 ω.2) ≤ 1 / 2 ∧
      eventMass (product fair fair) (fun ω => analysis (!ω.1) ω) = 3 / 4 := by
  refine ⟨rfl, ?_, same_data_selection_inflates.2.2⟩
  apply split_selection_valid fair (product fair fair) _ (fun _ => rfl) id analysis
  intro s
  cases s <;> norm_num [eventMass, analysis, product, fair, Fintype.sum_prod_type]

/-- Selection data and test data with identical outcomes: each marginal is fair. -/
def correlated : Law (Bool × Bool) where
  mass ω := if ω.1 = ω.2 then 1 / 2 else 0
  nonnegative ω := by split <;> norm_num
  normalized := by simp [Fintype.sum_prod_type]

/-- The test selected by `s` rejects when the test outcome equals `s`. -/
def matchTest (s : Bool) (t : Bool) : Bool := t == s

/-- Selection reads one sample and the test the other, and each candidate test is
calibrated at `1/2` under the test marginal. Under the product law the selected
test keeps its level (`split_selection_valid`); under the dependent law with the
same marginals it always rejects. A structurally split process history with
distinct dataset identities is compatible with both laws. -/
theorem dependent_split_invalid :
    (∀ s, eventMass fair (matchTest s) ≤ 1 / 2) ∧
      eventMass (product fair fair) (fun ω => matchTest ω.1 ω.2) ≤ 1 / 2 ∧
      eventMass correlated (fun ω => matchTest ω.1 ω.2) = 1 ∧
      SplitSelection [⟨⟨0⟩, .access ⟨0⟩ ⟨1⟩ .selection⟩, ⟨⟨1⟩, .access ⟨0⟩ ⟨2⟩ .evaluation⟩]
        [⟨1⟩] [⟨2⟩] := by
  have calibrated : ∀ s, eventMass fair (matchTest s) ≤ 1 / 2 := by
    intro s; cases s <;> simp [eventMass, matchTest, fair]
  refine ⟨calibrated, split_selection_valid fair fair _ (fun _ => rfl) id matchTest calibrated,
    ?_, by decide⟩
  simp [eventMass, matchTest, correlated, Fintype.sum_prod_type]

/-! ### Online replay and guarantee classes -/

/-- Omitting a non-rejection from the replayed ledger raises the next test's
level from `1/80` to `1/40`, although both ledgers satisfy a count bound of one. -/
theorem online_replay_anticonservative :
    onlineLevel (1 / 20) (1 / 20) [false] = 1 / 80 ∧ onlineLevel (1 / 20) (1 / 20) [] = 1 / 40 ∧
      [false].length ≤ 1 ∧ ([] : List Bool).length ≤ 1 := by
  refine ⟨?_, ?_, by decide, by decide⟩ <;> norm_num [onlineLevel]

/-- Marginal FDR with smoothing `η`, and FDR, of an outcome law over
(false discoveries, discoveries). -/
def mfdr (law : Law Bool) (V R : Bool → ℚ) (η : ℚ) : ℚ := expect law V / (expect law R + η)
def fdr (law : Law Bool) (V R : Bool → ℚ) : ℚ := expect law fun ω => V ω / max (R ω) 1

/-- Half the time one false discovery alone, half the time nine true ones: mFDR
is at most `1/10` but FDR is `1/2`. A procedure guaranteeing mFDR, as
alpha-investing does, need not guarantee FDR. -/
theorem mfdr_not_fdr :
    mfdr fair (fun ω => if ω then 1 else 0) (fun ω => if ω then 1 else 9) 0 ≤ 1 / 10 ∧
      fdr fair (fun ω => if ω then 1 else 0) (fun ω => if ω then 1 else 9) = 1 / 2 := by
  constructor <;> norm_num [mfdr, fdr, expect, fair]

/-! ### e-BH needs the bound, not the reported count -/

/-- Two null e-values, each `2` with probability `1/2`; only their maximum is
reported. -/
def pair : Fin 1 → Bool × Bool → ℚ := fun _ ω => if ω.1 || ω.2 then 2 else 0

/-- Running e-BH at `α = 1/2` with the reported count one rejects the null with
probability `3/4`; at the bound two it never rejects here. -/
theorem eBH_reported_count_unsound :
    expect (product fair fair) (fun ω => fdp (eBH 1 (1 / 2) fun i => pair i ω) {0}) = 3 / 4 ∧
      expect (product fair fair) (fun ω => fdp (eBH 2 (1 / 2) fun i => pair i ω) {0}) = 0 := by
  constructor <;> decide +kernel

/-! ### The warranted level -/

/-- The warranted level of concrete ledgers: finite for complete e-value and
p-value ledgers, `⊤` when a field is missing, the bound is zero or the guarantee
is not FWER. -/
theorem warrantedLevel_fixtures :
    warrantedLevel ⟨some .eValue, some 60, some 2, some .fwer⟩ = ((1 / 30 : ℚ) : WithTop ℚ) ∧
      warrantedLevel ⟨some .eValue, some 60, none, some .fwer⟩ = ⊤ ∧
      warrantedLevel ⟨some .eValue, some 60, some 2, some .fdr⟩ = ⊤ ∧
      warrantedLevel ⟨none, some 60, some 2, some .fwer⟩ = ⊤ ∧
      warrantedLevel ⟨some .pValue, some (1 / 40), some 2, some .fwer⟩ = ((1 / 20 : ℚ) : WithTop ℚ) ∧
      warrantedLevel ⟨some .pValue, some (1 / 40), some 0, some .fwer⟩ = ⊤ := by
  refine ⟨?_, warrantedLevel_failClosed _ (by simp), warrantedLevel_needs_fwer _ rfl (by decide),
    warrantedLevel_failClosed _ (by simp), ?_, ?_⟩ <;> simp only [warrantedLevel] <;> norm_num

end Lara.Examples.ProcessStatistics
