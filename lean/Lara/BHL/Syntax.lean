import Lara.BHL.Ghost

namespace Lara.BHL

structure ConstantId (sort : GhostSort) where
  index : Nat
  deriving DecidableEq, Repr

structure FunctionId (inputs : List ValueSort) (output : ValueSort) where
  index : Nat
  deriving DecidableEq, Repr

structure PredicateId (inputs : List ValueSort) where
  index : Nat
  deriving DecidableEq, Repr

structure DatasetFunctionId (inputs : List ValueSort) where
  index : Nat
  deriving DecidableEq, Repr

structure CouplingId where
  index : Nat
  deriving DecidableEq, Repr

structure CommandId where
  index : Nat
  deriving DecidableEq, Repr

/-- Ghost replacements are rigid: they cannot read any ambient memory or view. -/
inductive GhostTerm (context : List GhostSort) : GhostSort → Type where
  | bound : BoundGhost context sort → GhostTerm context sort
  | constant : ConstantId sort → GhostTerm context sort

/-- Internal term carriers include structural projections used by expanded
local effect equations. Outer binders quantify only GhostSort carriers. -/
inductive TermSort where
  | value : ValueSort → TermSort
  | dataset | world | trace | state | view | visible | hidden | history | provenance | compatible
  deriving DecidableEq, Repr

def GhostSort.termSort : GhostSort → TermSort
  | .value sort => .value sort
  | .dataset => .dataset
  | .world => .world
  | .trace => .trace

mutual
/-- Every field is finite syntax or a typed symbolic identity. Partial reads
and operations are interpreted by Option, never by invented default values. -/
inductive AssertionTerm (context : List GhostSort) : TermSort → Type where
  | ghost : GhostTerm context sort → AssertionTerm context sort.termSort
  | boolean : Bool → AssertionTerm context (.value .boolean)
  | integer : Int → AssertionTerm context (.value .integer)
  | rational : ℚ → AssertionTerm context (.value .real)
  | apply : FunctionId inputs output → ValueArguments context inputs →
      AssertionTerm context (.value output)
  | datasetApply : DatasetFunctionId inputs → ValueArguments context inputs →
      AssertionTerm context .dataset
  | ambient : AssertionTerm context .view
  | currentView : AssertionTerm context .world → AssertionTerm context .view
  | currentState : AssertionTerm context .world → AssertionTerm context .state
  | worldTrace : AssertionTerm context .world → AssertionTerm context .trace
  | appendWorld : AssertionTerm context .world → AssertionTerm context .trace →
      AssertionTerm context .world
  | traceEmpty : AssertionTerm context .trace
  | traceSingleton : AssertionTerm context .state → AssertionTerm context .trace
  | traceAppend : AssertionTerm context .trace → AssertionTerm context .trace →
      AssertionTerm context .trace
  | traceLength : AssertionTerm context .trace → AssertionTerm context (.value .integer)
  | traceTake : AssertionTerm context .trace → AssertionTerm context (.value .integer) →
      AssertionTerm context .trace
  | traceIndex : AssertionTerm context .trace → AssertionTerm context (.value .integer) →
      AssertionTerm context .state
  | valueRead : AssertionTerm context .view → Variable sort visibility →
      AssertionTerm context (.value sort)
  | datasetRead : AssertionTerm context .view → DatasetId → AssertionTerm context .dataset
  | visibleOf : AssertionTerm context .view → AssertionTerm context .visible
  | hiddenOf : AssertionTerm context .view → AssertionTerm context .hidden
  | historyOf : AssertionTerm context .view → AssertionTerm context .history
  | provenanceOf : AssertionTerm context .view → AssertionTerm context .provenance
  | compatibleOf : AssertionTerm context .view → AssertionTerm context .compatible
  | makeView : AssertionTerm context .visible → AssertionTerm context .history →
      AssertionTerm context .hidden → AssertionTerm context .compatible →
      AssertionTerm context .provenance → AssertionTerm context .view
  | writeValue : AssertionTerm context .view → Variable sort .observable →
      AssertionTerm context (.value sort) → AssertionTerm context .view
  | writeDataset : AssertionTerm context .view → DatasetId → AssertionTerm context .dataset →
      AssertionTerm context .view
  | addHistory : AssertionTerm context .view → AssertionTerm context .history →
      AssertionTerm context .view
  | historyEmpty : AssertionTerm context .history
  | historySingleton : AssertionTerm context .dataset → TestId → AssertionTerm context .history
  | historyAdd : AssertionTerm context .history → AssertionTerm context .history →
      AssertionTerm context .history
  | historyCount : AssertionTerm context .history → AssertionTerm context .dataset → TestId →
      AssertionTerm context (.value .integer)
  | provenanceEmpty : AssertionTerm context .provenance
  | provenanceSingleton : AssertionTerm context .dataset → PopulationId →
      AssertionTerm context .provenance
  | provenanceAdd : AssertionTerm context .provenance → AssertionTerm context .provenance →
      AssertionTerm context .provenance
  | pvalue : TestExpression context → AssertionTerm context (.value .real)
  | realAdd : AssertionTerm context (.value .real) → AssertionTerm context (.value .real) →
      AssertionTerm context (.value .real)
  | realMin : AssertionTerm context (.value .real) → AssertionTerm context (.value .real) →
      AssertionTerm context (.value .real)
  | intAdd : AssertionTerm context (.value .integer) → AssertionTerm context (.value .integer) →
      AssertionTerm context (.value .integer)
  | intSub : AssertionTerm context (.value .integer) → AssertionTerm context (.value .integer) →
      AssertionTerm context (.value .integer)
  | intLess : AssertionTerm context (.value .integer) → AssertionTerm context (.value .integer) →
      AssertionTerm context (.value .boolean)
  | booleanNot : AssertionTerm context (.value .boolean) → AssertionTerm context (.value .boolean)

inductive ValueArguments (context : List GhostSort) : List ValueSort → Type where
  | nil : ValueArguments context []
  | cons : AssertionTerm context (.value sort) → ValueArguments context rest →
      ValueArguments context (sort :: rest)

/-- Each leaf explicitly binds hypothesis, data, test and population. Composite
numerical events use an explicitly named coupling with checked marginals. -/
inductive TestExpression (context : List GhostSort) where
  | leaf : HypothesisId → AssertionTerm context .dataset → TestId → PopulationId →
      TestExpression context
  | disj : CouplingId → TestExpression context → TestExpression context → TestExpression context
  | conj : CouplingId → TestExpression context → TestExpression context → TestExpression context
end

/-- User predicates see explicit ordinary value arguments only. Structural and
statistical atoms expose their dependencies through fixed constructors. -/
inductive AssertionAtom (context : List GhostSort) where
  | rigid : PredicateId inputs → ValueArguments context inputs → AssertionAtom context
  | equal : AssertionTerm context sort → AssertionTerm context sort → AssertionAtom context
  | defined : AssertionTerm context sort → AssertionAtom context
  | realCompare : Comparison → AssertionTerm context (.value .real) →
      AssertionTerm context (.value .real) → AssertionAtom context
  | intCompare : Comparison → AssertionTerm context (.value .integer) →
      AssertionTerm context (.value .integer) → AssertionAtom context
  | hypothesis : HypothesisId → AssertionTerm context .hidden → AssertionAtom context
  | sampling : AssertionTerm context .dataset → PopulationId →
      AssertionTerm context .provenance → AssertionAtom context
  | requirements : TestExpression context → AssertionTerm context .view → AssertionAtom context
  | admitted : AssertionTerm context .world → AssertionAtom context
  | action : CommandId → AssertionTerm context .state → AssertionAtom context

/-- No quantifier constructor can occur beneath K. References to ghosts bound
outside K remain legal and rigid. Scoped atView targets are reevaluated at each
accessible alternative under K. -/
inductive ModalFormula (context : List GhostSort) where
  | atom : AssertionAtom context → ModalFormula context
  | neg : ModalFormula context → ModalFormula context
  | conj : ModalFormula context → ModalFormula context → ModalFormula context
  | knows : ModalFormula context → ModalFormula context
  | atWorld : AssertionTerm context .world → ModalFormula context → ModalFormula context
  | atView : AssertionTerm context .view → ModalFormula context → ModalFormula context

inductive Assertion : List GhostSort → Type where
  | modal : ModalFormula context → Assertion context
  | neg : Assertion context → Assertion context
  | conj : Assertion context → Assertion context → Assertion context
  | all : (sort : GhostSort) → Assertion (sort :: context) → Assertion context
  | atWorld : AssertionTerm context .world → Assertion context → Assertion context
  | atView : AssertionTerm context .view → Assertion context → Assertion context

def ModalFormula.disj (left right : ModalFormula context) : ModalFormula context :=
  .neg (.conj (.neg left) (.neg right))

def ModalFormula.implies (left right : ModalFormula context) : ModalFormula context :=
  .disj (.neg left) right

def ModalFormula.possible (formula : ModalFormula context) : ModalFormula context :=
  .neg (.knows (.neg formula))

def Assertion.disj (left right : Assertion context) : Assertion context :=
  .neg (.conj (.neg left) (.neg right))

def Assertion.implies (left right : Assertion context) : Assertion context :=
  .disj (.neg left) right

def Assertion.exists (sort : GhostSort) (body : Assertion (sort :: context)) : Assertion context :=
  .neg (.all sort (.neg body))

end Lara.BHL
