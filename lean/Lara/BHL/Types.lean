import Std
/-!
Symbolic identities for the audited BHL contract. Identifiers are not their
mathematical denotations; in particular, dataset aliases may have equal values.
-/

namespace Lara.BHL

structure VarId where
  index : Nat
  deriving DecidableEq, Repr

structure TestId where
  index : Nat
  deriving DecidableEq, Repr

structure DatasetId where
  index : Nat
  deriving DecidableEq, Repr

structure HypothesisId where
  index : Nat
  deriving DecidableEq, Repr

structure GhostId where
  index : Nat
  deriving DecidableEq, Repr

structure PopulationId where
  index : Nat
  deriving DecidableEq, Repr

inductive Visibility where
  | observable | invisible
  deriving DecidableEq, Repr

inductive Tail where
  | lower | upper | twoSided
  deriving DecidableEq, Repr

inductive Comparison where
  | equal | less | lessEqual | greater | greaterEqual
  deriving DecidableEq, Repr

/-- Products and lists preserve the paper's recursive value sorts.
Population carries the measurable sample sort of its mathematical law. -/
inductive ValueSort where
  | boolean | integer | real
  | population : ValueSort → ValueSort
  | product : ValueSort → ValueSort → ValueSort
  | list : ValueSort → ValueSort
  deriving DecidableEq, Repr

/-- Phantom sort and visibility indices prevent cross-sort program bindings. -/
structure Variable (sort : ValueSort) (visibility : Visibility) where
  id : VarId
  deriving DecidableEq, Repr

@[simp] theorem varId_index_injective (a b : VarId) :
    a.index = b.index ↔ a = b := by cases a; cases b; simp

@[simp] theorem testId_index_injective (a b : TestId) :
    a.index = b.index ↔ a = b := by cases a; cases b; simp

@[simp] theorem datasetId_index_injective (a b : DatasetId) :
    a.index = b.index ↔ a = b := by cases a; cases b; simp

@[simp] theorem hypothesisId_index_injective (a b : HypothesisId) :
    a.index = b.index ↔ a = b := by cases a; cases b; simp

@[simp] theorem ghostId_index_injective (a b : GhostId) :
    a.index = b.index ↔ a = b := by cases a; cases b; simp

@[simp] theorem populationId_index_injective (a b : PopulationId) :
    a.index = b.index ↔ a = b := by cases a; cases b; simp

@[simp] theorem variable_id_injective {s : ValueSort} {v : Visibility}
    (a b : Variable s v) : a.id = b.id ↔ a = b := by
  cases a; cases b; simp

end Lara.BHL
