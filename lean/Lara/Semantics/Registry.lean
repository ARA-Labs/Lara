import Lara.Semantics

/-! The supported, named repository semantics. The interface remains open; this
registry owns the finite vocabulary used by executable tables and coverage gates. -/
namespace Lara.Semantics.Registry

/-- The five extension semantics of `Lara.Semantics`, as a closed sum type.
Appending `Sem` to a constructor name gives the Lean identifier of the instance:
`groundedSem`, `completeSem`, `preferredSem`, `stableSem`, `semiStableSem`. -/
inductive SemanticsName where
  /-- `Semantics.groundedSem` -/
  | grounded
  /-- `Semantics.completeSem` -/
  | complete
  /-- `Semantics.preferredSem` -/
  | preferred
  /-- `Semantics.stableSem` -/
  | stable
  /-- `Semantics.semiStableSem` -/
  | semiStable
deriving DecidableEq, Repr

/-- The one place a semantics' printed spelling is written. -/
def semanticsLabel : SemanticsName → String
  | .grounded   => "grounded"
  | .complete   => "complete"
  | .preferred  => "preferred"
  | .stable     => "stable"
  | .semiStable => "semiStable"

/-- The one place a name is mapped to its instance. Every table cell reads the
semantics through this function, so no row can name one instance and evaluate
another. -/
def semanticsInstance : SemanticsName → ExtensionSemantics
  | .grounded   => groundedSem
  | .complete   => completeSem
  | .preferred  => preferredSem
  | .stable     => stableSem
  | .semiStable => semiStableSem

/-- Row order for the semantics axis, in the order the module introduces them:
the singleton instance first, then the four that can disagree with it. -/
def allSemantics : List SemanticsName :=
  [.grounded, .complete, .preferred, .stable, .semiStable]

/-- **`allSemantics` lists every constructor.** `semanticsLabel` and
`semanticsInstance` are total matches, so a new constructor breaks them; a
hand-written list is not checked that way and would silently drop a table row.
This theorem is the check. `cases` before `decide` is required: there is no
`Decidable` instance for the quantifier itself, only for each instantiation. -/
theorem allSemantics_complete : ∀ s : SemanticsName, s ∈ allSemantics := by
  intro s; cases s <;> decide

end Lara.Semantics.Registry
