import Lara.BHL.ControlLogData
import Lara.BHL.GhostSubstitution

namespace Lara.BHL

namespace ControlLogSyntax

/-- Four outer binders, in source/state-trace/metadata-seed/metadata-trace order. -/
abbrev Context (Γ : List GhostSort) := .trace :: .world :: .trace :: .world :: Γ

structure Terms (Γ : List GhostSort) where
  source : AssertionTerm Γ .world
  programStates : AssertionTerm Γ .trace
  controlSeed : AssertionTerm Γ .world
  controlStates : AssertionTerm Γ .trace

namespace Terms

 def bound : Terms (Context Γ) where
  source := .ghost (.bound (.there (.there (.there .here))))
  programStates := .ghost (.bound (.there (.there .here)))
  controlSeed := .ghost (.bound (.there .here))
  controlStates := .ghost (.bound .here)

 def rename (terms : Terms Γ) (ρ : GhostRenaming Γ Δ) : Terms Δ where
  source := terms.source.renameGhosts ρ
  programStates := terms.programStates.renameGhosts ρ
  controlSeed := terms.controlSeed.renameGhosts ρ
  controlStates := terms.controlStates.renameGhosts ρ

 def metadataWorld (terms : Terms Γ) (index : AssertionTerm Γ (.value .integer)) :
    AssertionTerm Γ .world :=
  .appendWorld terms.controlSeed (.traceTake terms.controlStates index)

 def cell (terms : Terms Γ) (index : AssertionTerm Γ (.value .integer)) (name : LogCell) :
    AssertionTerm Γ (.value .integer) :=
  .valueRead (.currentView (terms.metadataWorld index)) name.toVariable

 def count (terms : Terms Γ) (index : AssertionTerm Γ (.value .integer)) :=
  terms.cell index .commands

 def programWorld (terms : Terms Γ) (index : AssertionTerm Γ (.value .integer)) :
    AssertionTerm Γ .world :=
  .appendWorld terms.source (.traceTake terms.programStates (terms.count index))

 def programView (terms : Terms Γ) (index : AssertionTerm Γ (.value .integer)) :
    AssertionTerm Γ .view := .currentView (terms.programWorld index)

 def terminal (terms : Terms Γ) : AssertionTerm Γ .world :=
  .appendWorld terms.source terms.programStates

end Terms

 def weakenOriginal : GhostRenaming Γ (Context Γ) :=
  fun _ index => .there (.there (.there (.there index)))

 def trueFormula : ModalFormula Γ := .atom (.equal (.integer 0) (.integer 0))
 def falseFormula : ModalFormula Γ := .neg trueFormula
 def conjunction (formulas : List (ModalFormula Γ)) : ModalFormula Γ :=
  formulas.foldr ModalFormula.conj trueFormula
 def disjunction (formulas : List (ModalFormula Γ)) : ModalFormula Γ :=
  formulas.foldr ModalFormula.disj falseFormula

noncomputable section

/-- Every edge is expanded into finite typed equalities and successful local
primitive/guard evaluation. No whole-program predicate is an assertion atom. -/
def edge (terms : Terms Γ) (program current : Program)
    (target : Option Program) (label : ControlLabel)
    (index : AssertionTerm Γ (.value .integer)) : ModalFormula Γ :=
  let next := AssertionTerm.intAdd index (.integer 1)
  conjunction [
    .atom (.equal (terms.cell index .control) (.integer (program.controlCode (some current)))),
    .atom (.equal (terms.cell next .control) (.integer (program.controlCode target))),
    .atom (.intCompare .lessEqual (.integer 0) (terms.count index)),
    .atom (.intCompare .lessEqual (terms.count index) (.traceLength terms.programStates)),
    .atom (.intCompare .lessEqual (.integer 0) (terms.count next)),
    .atom (.intCompare .lessEqual (terms.count next) (.traceLength terms.programStates)),
    .atom (.admitted (terms.programWorld index)),
    .atom (.admitted (terms.programWorld next)),
    match label with
    | .guard expression value =>
        .conj (.atom (.equal (terms.count next) (terms.count index)))
          (.atView (terms.programView index)
            (.atom (.equal (expression.toAssertionTerm Γ) (.boolean value))))
    | .command primitive =>
        .conj (.atom (.equal (terms.count next) (.intAdd (terms.count index) (.integer 1))))
          (.atView (terms.programView index)
            (.atom (.equal (primitive.viewTerm Γ) (terms.programView next))))]

def edges (terms : Terms Γ) (program : Program)
    (index : AssertionTerm Γ (.value .integer)) : ModalFormula Γ :=
  disjunction (program.residuals.flatMap (fun current =>
    current.controlEdges.map (fun choice => edge terms program current choice.1 choice.2 index)))

def header (terms : Terms Γ) (program : Program) : ModalFormula Γ :=
  let finalIndex := AssertionTerm.traceLength terms.controlStates
  conjunction [
    .atom (.admitted terms.source),
    .atom (.equal (.currentView terms.source) .ambient),
    .atom (.equal (terms.cell (.integer 0) .control)
      (.integer (program.controlCode (some program)))),
    .atom (.equal (terms.count (.integer 0)) (.integer 0)),
    .atom (.equal (terms.cell finalIndex .control) (.integer 0)),
    .atom (.equal (terms.count finalIndex) (.traceLength terms.programStates))]

/-- One outer integer binder ranges over the finite metadata trace. It never
occurs underneath knowledge; formula size depends on syntax, not run length. -/
def validLocalLog (terms : Terms Γ) (program : Program) : Assertion Γ :=
  .conj (.modal (header terms program))
    (.all (.value .integer)
      ((Assertion.modal (conjunction [
        .atom (.intCompare .lessEqual (.integer 0) (.ghost (.bound .here))),
        .atom (.intCompare .less (.ghost (.bound .here))
          (.traceLength (terms.rename GhostRenaming.weaken).controlStates))])).implies
        (.modal (edges (terms.rename GhostRenaming.weaken) program (.ghost (.bound .here))))))

/-- Universal quantification over four actual mathematical carriers; the body
uses only the frozen legal assertion constructors and capture-avoiding weakening. -/
def representative (program : Program) (post : Assertion Γ) : Assertion Γ :=
  .all .world (.all .trace (.all .world (.all .trace
    ((validLocalLog Terms.bound program).implies
      (.atWorld Terms.bound.terminal (post.renameGhosts weakenOriginal))))))

end
end ControlLogSyntax
end Lara.BHL
