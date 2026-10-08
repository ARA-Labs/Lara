import Lara.BHL.Substitution

namespace Lara.BHL

mutual
/-- Pure finite expressions. Every mutable read is observable; static symbols
have a rigid mathematical interpretation. Calculating a p-value is not a test run. -/
inductive ProgramExpr : ValueSort → Type where
  | boolean : Bool → ProgramExpr .boolean
  | integer : Int → ProgramExpr .integer
  | rational : ℚ → ProgramExpr .real
  | constant : ConstantId (.value sort) → ProgramExpr sort
  | read : Variable sort .observable → ProgramExpr sort
  | apply : FunctionId inputs output → ProgramArgs inputs → ProgramExpr output
  | pvalue : HypothesisId → DatasetExpr → TestId → PopulationId → ProgramExpr .real
  | realAdd : ProgramExpr .real → ProgramExpr .real → ProgramExpr .real
  | realMin : ProgramExpr .real → ProgramExpr .real → ProgramExpr .real
  | intAdd : ProgramExpr .integer → ProgramExpr .integer → ProgramExpr .integer
  | intSub : ProgramExpr .integer → ProgramExpr .integer → ProgramExpr .integer
  | intLess : ProgramExpr .integer → ProgramExpr .integer → ProgramExpr .boolean
  | booleanNot : ProgramExpr .boolean → ProgramExpr .boolean

inductive ProgramArgs : List ValueSort → Type where
  | nil : ProgramArgs []
  | cons : ProgramExpr sort → ProgramArgs rest → ProgramArgs (sort :: rest)

inductive DatasetExpr where
  | constant : ConstantId .dataset → DatasetExpr
  | read : DatasetId → DatasetExpr
  | apply : DatasetFunctionId inputs → ProgramArgs inputs → DatasetExpr
end

/-- Cells include the sort: the same identifier at two value sorts is not one cell. -/
inductive ProgramCell where
  | value : ValueSort → VarId → ProgramCell
  | dataset : DatasetId → ProgramCell
  deriving DecidableEq

def ProgramCell.Agrees (cell : ProgramCell) (left right : VisibleState D) : Prop :=
  match cell with
  | .value sort name => left.memory sort name = right.memory sort name
  | .dataset name => left.datasets name = right.datasets name

def ProgramAgreement (support : List ProgramCell) (left right : VisibleState D) : Prop :=
  ∀ cell ∈ support, cell.Agrees left right

def ProgramFrame (writes : List ProgramCell) (before after : VisibleState D) : Prop :=
  ∀ cell, cell ∉ writes → cell.Agrees before after

mutual
def ProgramExpr.reads : ProgramExpr sort → List ProgramCell
  | .boolean _ | .integer _ | .rational _ | .constant _ => []
  | .read (sort := s) x => [.value s x.id]
  | .apply _ args => args.reads
  | .pvalue _ data _ _ => data.reads
  | .realAdd left right | .realMin left right | .intAdd left right |
      .intSub left right | .intLess left right => left.reads ++ right.reads
  | .booleanNot value => value.reads

def ProgramArgs.reads : ProgramArgs inputs → List ProgramCell
  | .nil => []
  | .cons value rest => value.reads ++ rest.reads

def DatasetExpr.reads : DatasetExpr → List ProgramCell
  | .constant _ => []
  | .read name => [.dataset name]
  | .apply _ args => args.reads
end

/-- A source command, including the observable action emitted by skip. -/
inductive Primitive where
  | skip
  | assign : Variable sort .observable → ProgramExpr sort → Primitive
  | assignDataset : DatasetId → DatasetExpr → Primitive
  | test : Variable .real .observable → HypothesisId → DatasetExpr → TestId →
      PopulationId → Primitive

def Primitive.reads : Primitive → List ProgramCell
  | .skip => []
  | .assign _ rhs => rhs.reads
  | .assignDataset _ rhs => rhs.reads
  | .test _ _ data _ _ => data.reads

def Primitive.writes : Primitive → List ProgramCell
  | .skip => []
  | .assign (sort := s) x _ => [.value s x.id]
  | .assignDataset name _ => [.dataset name]
  | .test result _ _ _ _ => [.value .real result.id]

inductive Program where
  | command : Primitive → Program
  | seq : Program → Program → Program
  | ite : ProgramExpr .boolean → Program → Program → Program
  | loop : ProgramExpr .boolean → Program → Program
  | par : Program → Program → Program

def Program.skip : Program := .command .skip

def Program.reads : Program → List ProgramCell
  | .command primitive => primitive.reads
  | .seq left right | .par left right => left.reads ++ right.reads
  | .ite guard left right => guard.reads ++ left.reads ++ right.reads
  | .loop guard body => guard.reads ++ body.reads

def Program.writes : Program → List ProgramCell
  | .command primitive => primitive.writes
  | .seq left right | .par left right | .ite _ left right => left.writes ++ right.writes
  | .loop _ body => body.writes

def Program.used (program : Program) : List ProgramCell := program.reads ++ program.writes

def Noninterfering (left right : Program) : Prop :=
  (∀ cell ∈ left.writes, cell ∉ right.used) ∧
  (∀ cell ∈ right.writes, cell ∉ left.used)

def Program.WellFormed : Program → Prop
  | .command _ => True
  | .seq left right | .ite _ left right => left.WellFormed ∧ right.WellFormed
  | .loop _ body => body.WellFormed
  | .par left right => left.WellFormed ∧ right.WellFormed ∧ Noninterfering left right

def noninterferingCheck (left right : Program) : Bool :=
  left.writes.all (fun cell => decide (cell ∉ right.used)) &&
    right.writes.all (fun cell => decide (cell ∉ left.used))

def Program.wellFormedCheck : Program → Bool
  | .command _ => true
  | .seq left right | .ite _ left right => left.wellFormedCheck && right.wellFormedCheck
  | .loop _ body => body.wellFormedCheck
  | .par left right =>
      left.wellFormedCheck && right.wellFormedCheck && noninterferingCheck left right

mutual
def ProgramExpr.toAssertionTerm (context : List GhostSort) :
    ProgramExpr sort → AssertionTerm context (.value sort)
  | .boolean value => .boolean value
  | .integer value => .integer value
  | .rational value => .rational value
  | .constant name => .ghost (.constant name)
  | .read x => .valueRead .ambient x
  | .apply symbol args => .apply symbol (args.toAssertionArgs context)
  | .pvalue hypothesis data test population =>
      .pvalue (.leaf hypothesis (data.toAssertionTerm context) test population)
  | .realAdd left right => .realAdd (left.toAssertionTerm context) (right.toAssertionTerm context)
  | .realMin left right => .realMin (left.toAssertionTerm context) (right.toAssertionTerm context)
  | .intAdd left right => .intAdd (left.toAssertionTerm context) (right.toAssertionTerm context)
  | .intSub left right => .intSub (left.toAssertionTerm context) (right.toAssertionTerm context)
  | .intLess left right => .intLess (left.toAssertionTerm context) (right.toAssertionTerm context)
  | .booleanNot value => .booleanNot (value.toAssertionTerm context)

def ProgramArgs.toAssertionArgs (context : List GhostSort) :
    ProgramArgs inputs → ValueArguments context inputs
  | .nil => .nil
  | .cons value rest => .cons (value.toAssertionTerm context) (rest.toAssertionArgs context)

def DatasetExpr.toAssertionTerm (context : List GhostSort) :
    DatasetExpr → AssertionTerm context .dataset
  | .constant name => .ghost (.constant name)
  | .read name => .datasetRead .ambient name
  | .apply symbol args => .datasetApply symbol (args.toAssertionArgs context)
end

/-- A finite, expanded local effect. It is not an execution or WLP atom. -/
def Primitive.viewTerm (context : List GhostSort) : Primitive → AssertionTerm context .view
  | .skip => .ambient
  | .assign x rhs => assignmentView x (rhs.toAssertionTerm context)
  | .assignDataset name rhs => datasetAssignmentView name (rhs.toAssertionTerm context)
  | .test result hypothesis data testName population =>
      testAssignmentView result hypothesis (data.toAssertionTerm context) testName population

def Primitive.preimage (primitive : Primitive) (post : Assertion context) : Assertion context :=
  liberalPreimage (primitive.viewTerm context) post

noncomputable section
variable {D Command : Type} [MeasurableSpace D]

mutual
def evalProgramExpr (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) : ProgramExpr sort → Option (Value sort)
  | .boolean value => some value
  | .integer value => some value
  | .rational value => some (value : ℝ)
  | .constant name => some (interpretation.constants _ name)
  | .read x => visible.memory _ x.id
  | .apply symbol args => (evalProgramArgs interpretation visible args).map
      (interpretation.functions _ _ symbol)
  | .pvalue hypothesis data test _ => (evalDatasetExpr interpretation visible data).map
      (interpretation.tests hypothesis test).tailProbability
  | .realAdd left right => do
      let a ← evalProgramExpr interpretation visible left
      let b ← evalProgramExpr interpretation visible right
      pure (a + b)
  | .realMin left right => do
      let a ← evalProgramExpr interpretation visible left
      let b ← evalProgramExpr interpretation visible right
      pure (min a b)
  | .intAdd left right => do
      let a ← evalProgramExpr interpretation visible left
      let b ← evalProgramExpr interpretation visible right
      pure (a + b)
  | .intSub left right => do
      let a ← evalProgramExpr interpretation visible left
      let b ← evalProgramExpr interpretation visible right
      pure (a - b)
  | .intLess left right => do
      let a ← evalProgramExpr interpretation visible left
      let b ← evalProgramExpr interpretation visible right
      pure (a < b)
  | .booleanNot value => (evalProgramExpr interpretation visible value).map Bool.not

def evalProgramArgs (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) : ProgramArgs inputs → Option (ValueTuple inputs)
  | .nil => some PUnit.unit
  | .cons value rest => do
      let a ← evalProgramExpr interpretation visible value
      let b ← evalProgramArgs interpretation visible rest
      pure (a, b)

def evalDatasetExpr (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) : DatasetExpr → Option D
  | .constant name => some (interpretation.constants _ name)
  | .read name => some (visible.datasets name)
  | .apply symbol args => (evalProgramArgs interpretation visible args).map
      (interpretation.datasetFunctions _ symbol)
end

/-- Evaluated mathematical payload, never part of the symbolic source AST. -/
inductive VisibleWrite (D : Type) where
  | unchanged
  | value : Variable sort .observable → Value sort → VisibleWrite D
  | dataset : DatasetId → D → VisibleWrite D

def VisibleWrite.cells : VisibleWrite D → List ProgramCell
  | .unchanged => []
  | .value (sort := s) x _ => [.value s x.id]
  | .dataset name _ => [.dataset name]

def VisibleWrite.apply (visible : VisibleState D) : VisibleWrite D → VisibleState D
  | .unchanged => visible
  | .value x newValue => {visible with memory :=
      ((Memory.assemble visible.memory (fun _ _ => none)).update x (some newValue)).observable}
  | .dataset name data => {visible with datasets := Function.update visible.datasets name data}

def evalPrimitive (interpretation : AssertionInterpretation D Command)
    (visible : VisibleState D) : Primitive → Option (VisibleWrite D × History D)
  | .skip => some (.unchanged, 0)
  | .assign x rhs => (evalProgramExpr interpretation visible rhs).map
      (fun value => (.value x value, 0))
  | .assignDataset name rhs => (evalDatasetExpr interpretation visible rhs).map
      (fun data => (.dataset name data, 0))
  | .test result hypothesis data test _ => (evalDatasetExpr interpretation visible data).map
      (fun d => (.value result ((interpretation.tests hypothesis test).tailProbability d), {(d, test)}))

def primitiveEffect (interpretation : AssertionInterpretation D Command)
    (primitive : Primitive) (visible : VisibleState D) : Option (VisibleState D × History D) :=
  (evalPrimitive interpretation visible primitive).map
    (fun out => (out.1.apply visible, out.2))

/-- Exact local model binding, including disabled commands. It contains no
execution, modal, replay, validity or soundness conclusion. -/
def ProgramModelBinding (interpretation : AssertionInterpretation D Primitive)
    (model : Model D Primitive) : Prop :=
  ∀ primitive visible, model.dynamics.command primitive visible =
    primitiveEffect interpretation primitive visible

/-- The interpreter and locally lawful model have one exact command meaning.
The only additional evidence is an ordinary equation between their local effects. -/
structure ProgramContext (D : Type) [MeasurableSpace D] where
  interpretation : AssertionInterpretation D Primitive
  model : Model D Primitive
  command_binding : ProgramModelBinding interpretation model

/-- Preserve independent initial and sampling relations while installing the
actual visible-only primitive effects. This realizes the local binding contract. -/
def ProgramContext.ofRelations (interpretation : AssertionInterpretation D Primitive)
    (initial : HiddenMemory → VisibleState D → Prop)
    (sampling : HiddenMemory → VisibleState D → VisibleState D → D → PopulationId → Prop)
    (inhabited : ∃ hidden visible, initial hidden visible) : ProgramContext D :=
  { interpretation := interpretation
    model :=
      { dynamics :=
          { initial := initial
            command := primitiveEffect interpretation
            sampling := sampling }
        initial_nonempty := inhabited }
    command_binding := fun _ _ => rfl }

end
end Lara.BHL
