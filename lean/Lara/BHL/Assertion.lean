import Lara.BHL.Interpretation

namespace Lara.BHL

noncomputable section

variable {D Command : Type} [MeasurableSpace D]

/-- Reference knowledge quantifies over every admitted full-observation alternative. -/
def knows (model : Model D Command) (world : World D Command)
    (predicate : World D Command → Prop) : Prop :=
  ∀ alternative, Admitted model.dynamics alternative → Accessible world alternative → predicate alternative

def possible (model : Model D Command) (world : World D Command)
    (predicate : World D Command → Prop) : Prop :=
  ¬ knows model world (fun alternative => ¬ predicate alternative)

/-- Independent modal meaning on the realized semantic-view image. Scoped view
expressions are evaluated anew at the current node, including beneath K. -/
def viewModalSatisfaction (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (view : SemanticView D) :
    ModalFormula context → Prop
  | .atom atom => atomMeaning interpretation model env view atom
  | .neg formula => ¬ viewModalSatisfaction interpretation model env view formula
  | .conj left right => viewModalSatisfaction interpretation model env view left ∧
      viewModalSatisfaction interpretation model env view right
  | .knows formula => ∀ alternative, alternative ∈ model.views → ViewAccessible view alternative →
      viewModalSatisfaction interpretation model env alternative formula
  | .atWorld target formula => ∃ world, evalTerm interpretation model env view target = some world ∧
      Admitted model.dynamics world ∧
      viewModalSatisfaction interpretation model env (semanticView model.dynamics world) formula
  | .atView target formula => ∃ alternative,
      evalTerm interpretation model env view target = some alternative ∧ alternative ∈ model.views ∧
      viewModalSatisfaction interpretation model env alternative formula

/-- Independent reference meaning retains the full ordered observation relation.
A scoped realized view can have several full-world representatives; its body is
required at all of them, rather than picking a hidden actual-world encoding. -/
def referenceModalSatisfaction (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context) (world : World D Command) :
    ModalFormula context → Prop
  | .atom atom => atomMeaning interpretation model env (semanticView model.dynamics world) atom
  | .neg formula => ¬ referenceModalSatisfaction interpretation model env world formula
  | .conj left right => referenceModalSatisfaction interpretation model env world left ∧
      referenceModalSatisfaction interpretation model env world right
  | .knows formula => knows model world
      (fun alternative => referenceModalSatisfaction interpretation model env alternative formula)
  | .atWorld target formula => ∃ alternative,
      evalTerm interpretation model env (semanticView model.dynamics world) target = some alternative ∧
      Admitted model.dynamics alternative ∧ referenceModalSatisfaction interpretation model env alternative formula
  | .atView target formula => ∃ view,
      evalTerm interpretation model env (semanticView model.dynamics world) target = some view ∧
      view ∈ model.views ∧ ∀ alternative, Admitted model.dynamics alternative →
        semanticView model.dynamics alternative = view →
        referenceModalSatisfaction interpretation model env alternative formula

/-- Outer ghost binders quantify over actual mathematical values, worlds and
finite traces. Quantifier constructors cannot enter K; references to ghosts
bound outside K remain legal and rigid across accessible alternatives. -/
def viewAssertionSatisfaction (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) : {context : List GhostSort} → GhostEnv D Command context →
    SemanticView D → Assertion context → Prop
  | _, env, view, .modal formula => viewModalSatisfaction interpretation model env view formula
  | _, env, view, .neg assertion => ¬ viewAssertionSatisfaction interpretation model env view assertion
  | _, env, view, .conj left right => viewAssertionSatisfaction interpretation model env view left ∧
      viewAssertionSatisfaction interpretation model env view right
  | _, env, view, .all sort body => ∀ value : GhostValue D Command sort,
      viewAssertionSatisfaction interpretation model (GhostEnv.push value env) view body
  | _, env, view, .atWorld target body => ∃ world,
      evalTerm interpretation model env view target = some world ∧ Admitted model.dynamics world ∧
      viewAssertionSatisfaction interpretation model env (semanticView model.dynamics world) body
  | _, env, view, .atView target body => ∃ alternative,
      evalTerm interpretation model env view target = some alternative ∧ alternative ∈ model.views ∧
      viewAssertionSatisfaction interpretation model env alternative body

def referenceAssertionSatisfaction (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) : {context : List GhostSort} → GhostEnv D Command context →
    World D Command → Assertion context → Prop
  | _, env, world, .modal formula => referenceModalSatisfaction interpretation model env world formula
  | _, env, world, .neg assertion => ¬ referenceAssertionSatisfaction interpretation model env world assertion
  | _, env, world, .conj left right => referenceAssertionSatisfaction interpretation model env world left ∧
      referenceAssertionSatisfaction interpretation model env world right
  | _, env, world, .all sort body => ∀ value : GhostValue D Command sort,
      referenceAssertionSatisfaction interpretation model (GhostEnv.push value env) world body
  | _, env, world, .atWorld target body => ∃ alternative,
      evalTerm interpretation model env (semanticView model.dynamics world) target = some alternative ∧
      Admitted model.dynamics alternative ∧ referenceAssertionSatisfaction interpretation model env alternative body
  | _, env, world, .atView target body => ∃ view,
      evalTerm interpretation model env (semanticView model.dynamics world) target = some view ∧
      view ∈ model.views ∧ ∀ alternative, Admitted model.dynamics alternative →
        semanticView model.dynamics alternative = view →
        referenceAssertionSatisfaction interpretation model env alternative body

/-- Public satisfaction includes membership in the independently admitted model. -/
def satisfies (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (world : World D Command) (assertion : Assertion context) : Prop :=
  Admitted model.dynamics world ∧ referenceAssertionSatisfaction interpretation model env world assertion

def satisfiesView (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (view : SemanticView D) (assertion : Assertion context) : Prop :=
  view ∈ model.views ∧ viewAssertionSatisfaction interpretation model env view assertion

end
end Lara.BHL
