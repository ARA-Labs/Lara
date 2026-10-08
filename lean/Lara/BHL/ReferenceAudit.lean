import Std
/-!
Countermodels for printed reference contracts, not replacement BHL semantics.
Sources: arXiv:2208.07074v3 §4.3, §5.2.2, equations (8)/(11), Appendix B.4.
-/

namespace Lara.BHL.ReferenceAudit

structure Memory where
  x : Nat
  deriving DecidableEq, Repr

inductive Assertion where
  | atom
  deriving DecidableEq

abbrev valuation (m : Memory) : Prop := m.x = 0
abbrev satisfies (m : Memory) (_ : Assertion) : Prop := valuation m

/-- A nullary predicate has no variable occurrence to replace. -/
def substitute (_ : Nat) (a : Assertion) : Assertion := a

def assign (n : Nat) (_ : Memory) : Memory := ⟨n⟩

theorem equal_memory_equal_valuation (a b : Memory) (h : a = b) :
    valuation a = valuation b := by cases h; rfl

/-- The permitted memory-dependent predicate invalidates literal UpdVar. -/
theorem assignment_substitution_counterexample :
    satisfies ⟨0⟩ (substitute 1 .atom) ∧
      ¬ satisfies (assign 1 ⟨0⟩) .atom := by
  constructor
  · rfl
  · decide

inductive DatasetVar where
  | y | z
  deriving DecidableEq, Repr

def dataset (_ : DatasetVar) : Nat := 7

def history (d : Nat) : Nat := if d = 7 then 1 else 0

def historyVariable (v : DatasetVar) : Nat := history (dataset v)

abbrev equation8 : Prop := historyVariable .y = 1 ∧ historyVariable .z = 0

def equation11 : Prop := ∀ d, history d = if d = dataset .y then 1 else 0

theorem alias_history_consistent :
    historyVariable .y = 1 ∧ historyVariable .z = 1 := by decide

theorem history_assertion_counterexample : equation11 ∧ ¬ equation8 := by
  constructor
  · intro d; rfl
  · decide

def namedUpdate (v : DatasetVar) : Nat := if v = .y then 1 else 0

theorem named_history_update_inconsistent :
    namedUpdate .z ≠ history (dataset .z) := by decide

/-- Substituting the actual invisible value under K erases other possibilities.
The two worlds observe the same constant and differ only in an invisible bit. -/
def knows (p : Bool → Prop) : Prop := ∀ hidden, p hidden

theorem modal_memory_encoding_counterexample :
    ¬ knows (fun hidden => hidden = false) ∧ knows (fun _ => false = false) := by
  constructor
  · intro h
    have impossible := h true
    cases impossible
  · intro _; rfl

/-- Equality of p-values is not monotone in the proposed bound. -/
theorem equality_threshold_not_monotone :
    (1 : Nat) = 1 ∧ (1 : Nat) ≤ 2 ∧ ¬ (1 : Nat) = 2 := by decide

end Lara.BHL.ReferenceAudit
