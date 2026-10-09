import Lara.BHL.Assertion

namespace Lara.BHL

/-- Full canonical history syntax; no named-counter shortcut or deduplication. -/
def testHistoryTerm : TestExpression context → AssertionTerm context .history
  | .leaf _ data test _ => .historySingleton data test
  | .disj _ left right | .conj _ left right =>
      .historyAdd (testHistoryTerm left) (testHistoryTerm right)

def exactHistory (test : TestExpression context) : ModalFormula context :=
  .atom (.equal (.historyOf .ambient) (testHistoryTerm test))

def pvalueAtom (comparison : Comparison) (threshold : AssertionTerm context (.value .real))
    (test : TestExpression context) : ModalFormula context :=
  .atom (.realCompare comparison (.pvalue test) threshold)

def samplingAtom (data : AssertionTerm context .dataset) (population : PopulationId) :
    ModalFormula context :=
  .atom (.sampling data population (.provenanceOf .ambient))

def modelRequirementsFormula (test : TestExpression context) : ModalFormula context :=
  .atom (.requirements test .ambient)

def exception (comparison : Comparison) (threshold : AssertionTerm context (.value .real))
    (test : TestExpression context) : ModalFormula context :=
  .conj (pvalueAtom comparison threshold test) (exactHistory test)

/-- Published epistemic meaning, with canonical ledger and explicit model failure.
It is neither alternative truth nor a posterior probability. -/
def statisticalBelief (comparison : Comparison)
    (threshold : AssertionTerm context (.value .real)) (test : TestExpression context)
    (alternative : ModalFormula context) : ModalFormula context :=
  .knows (.disj alternative (.disj (exception comparison threshold test)
    (.neg (modelRequirementsFormula test))))

def statisticalPossibility (comparison : Comparison)
    (threshold : AssertionTerm context (.value .real)) (test : TestExpression context)
    (alternative : ModalFormula context) : ModalFormula context :=
  .neg (statisticalBelief comparison threshold test (.neg alternative))

def nullAlternative (upper lower : ModalFormula context) : ModalFormula context :=
  .conj (.neg upper) (.neg lower)

noncomputable section

variable {D Command : Type} [MeasurableSpace D]

/-- Observation invariance is a proved semantic restriction, not a caller Boolean.
Rigid ghosts and ordinary visible dataset reads supply its standard inhabitants. -/
def ObservationInvariantTerm (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context)
    (term : AssertionTerm context sort) : Prop :=
  ∀ left right, Accessible left right →
    evalTerm interpretation model env (semanticView model.dynamics left) term =
      evalTerm interpretation model env (semanticView model.dynamics right) term

def ObservableTestExpression (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) : TestExpression context → Prop
  | .leaf _ data _ _ => ObservationInvariantTerm interpretation model env data
  | .disj _ left right | .conj _ left right =>
      ObservableTestExpression interpretation model env left ∧
        ObservableTestExpression interpretation model env right

/-- Fixed real thresholds, including rigid real ghosts, expose their exact value.
A source law about fixed ε is not silently generalized to hidden-varying terms. -/
def FixedRealTerm (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (term : AssertionTerm context (.value .real))
    (value : ℝ) : Prop :=
  ∀ view, evalTerm interpretation model env view term = some value

end
end Lara.BHL
