import Lara.BHL.GhostTransforms
import Lara.BHL.Assertion

namespace Lara.BHL

noncomputable section

variable {D Command : Type} [MeasurableSpace D]

/-- Rigid replacements are interpreted without an ambient world or view. -/
def substitutionEnv (interpretation : AssertionInterpretation D Command)
    (σ : GhostSubstitution context target) (env : GhostEnv D Command target) :
    GhostEnv D Command context := fun sort index => (σ sort index).eval interpretation env

theorem GhostTerm.eval_renameGhosts (interpretation : AssertionInterpretation D Command)
    (ρ : GhostRenaming context target) (env : GhostEnv D Command target)
    (term : GhostTerm context sort) :
    (term.renameGhosts ρ).eval interpretation env =
      term.eval interpretation (GhostEnv.reindex ρ env) := by cases term <;> rfl

theorem GhostTerm.eval_substituteGhosts (interpretation : AssertionInterpretation D Command)
    (σ : GhostSubstitution context target) (env : GhostEnv D Command target)
    (term : GhostTerm context sort) :
    (term.substituteGhosts σ).eval interpretation env =
      term.eval interpretation (substitutionEnv interpretation σ env) := by cases term <;> rfl

@[simp] theorem substitutionEnv_id (interpretation : AssertionInterpretation D Command)
    (env : GhostEnv D Command context) : substitutionEnv interpretation GhostSubstitution.id env = env := rfl

theorem substitutionEnv_ofRenaming (interpretation : AssertionInterpretation D Command)
    (ρ : GhostRenaming context target) (env : GhostEnv D Command target) :
    substitutionEnv interpretation (GhostSubstitution.ofRenaming ρ) env = GhostEnv.reindex ρ env := rfl

theorem substitutionEnv_comp (interpretation : AssertionInterpretation D Command)
    (σ : GhostSubstitution context target) (τ : GhostSubstitution target next)
    (env : GhostEnv D Command next) :
    substitutionEnv interpretation (GhostSubstitution.comp σ τ) env =
      substitutionEnv interpretation σ (substitutionEnv interpretation τ env) := by
  apply GhostEnv.ext
  intro sort index
  exact GhostTerm.eval_substituteGhosts interpretation τ env (σ sort index)

/-- Lifting a rigid substitution preserves the new binder, without capture. -/
@[simp] theorem substitutionEnv_lift_push (interpretation : AssertionInterpretation D Command)
    (σ : GhostSubstitution context target) (value : GhostValue D Command other)
    (env : GhostEnv D Command target) :
    substitutionEnv interpretation (GhostSubstitution.lift σ) (GhostEnv.push value env) =
      GhostEnv.push value (substitutionEnv interpretation σ env) := by
  apply GhostEnv.ext
  intro sort index
  cases index with
  | here => rfl
  | there index =>
      exact GhostTerm.eval_renameGhosts interpretation GhostRenaming.weaken
        (GhostEnv.push value env) (σ sort index)

/-- The environment under a lifted substitution is its new value and pulled-back tail. -/
theorem substitutionEnv_lift (interpretation : AssertionInterpretation D Command)
    (σ : GhostSubstitution context target) (env : GhostEnv D Command (other :: target)) :
    substitutionEnv interpretation (GhostSubstitution.lift σ) env =
      GhostEnv.push (GhostEnv.lookup env (.here : BoundGhost (other :: target) other))
        (substitutionEnv interpretation σ (GhostEnv.reindex GhostRenaming.weaken env)) := by
  apply GhostEnv.ext
  intro sort index
  cases index with
  | here => rfl
  | there index =>
      exact GhostTerm.eval_renameGhosts interpretation GhostRenaming.weaken env (σ sort index)

mutual
theorem evalTerm_substituteGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (σ : GhostSubstitution context target)
    (env : GhostEnv D Command target) (view : SemanticView D) :
    (term : AssertionTerm context sort) →
    evalTerm interpretation model env view (AssertionTerm.substituteGhosts σ term) =
      evalTerm interpretation model (substitutionEnv interpretation σ env) view term
  | .ghost g => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, GhostTerm.eval_substituteGhosts]
  | .boolean v => by
      simp only [AssertionTerm.substituteGhosts, evalTerm]
  | .integer v => by
      simp only [AssertionTerm.substituteGhosts, evalTerm]
  | .rational v => by
      simp only [AssertionTerm.substituteGhosts, evalTerm]
  | .apply f a => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalArguments_substituteGhosts interpretation model σ env view a]
  | .datasetApply f a => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalArguments_substituteGhosts interpretation model σ env view a]
  | .ambient => by
      simp only [AssertionTerm.substituteGhosts, evalTerm]
  | .currentView w => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view w]
  | .currentState w => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view w]
  | .worldTrace w => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view w]
  | .appendWorld w t => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view w, evalTerm_substituteGhosts interpretation model σ env view t]
  | .traceEmpty => by
      simp only [AssertionTerm.substituteGhosts, evalTerm]
  | .traceSingleton s => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view s]
  | .traceAppend a b => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view a, evalTerm_substituteGhosts interpretation model σ env view b]
  | .traceLength t => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view t]
  | .traceTake t i => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view t, evalTerm_substituteGhosts interpretation model σ env view i]
  | .traceIndex t i => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view t, evalTerm_substituteGhosts interpretation model σ env view i]
  | .valueRead v x => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view v]
  | .datasetRead v n => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view v]
  | .visibleOf v => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view v]
  | .hiddenOf v => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view v]
  | .historyOf v => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view v]
  | .provenanceOf v => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view v]
  | .compatibleOf v => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view v]
  | .makeView v h s c p => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view v, evalTerm_substituteGhosts interpretation model σ env view h, evalTerm_substituteGhosts interpretation model σ env view s, evalTerm_substituteGhosts interpretation model σ env view c, evalTerm_substituteGhosts interpretation model σ env view p]
  | .writeValue v x a => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view v, evalTerm_substituteGhosts interpretation model σ env view a]
  | .writeDataset v n d => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view v, evalTerm_substituteGhosts interpretation model σ env view d]
  | .addHistory v h => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view v, evalTerm_substituteGhosts interpretation model σ env view h]
  | .historyEmpty => by
      simp only [AssertionTerm.substituteGhosts, evalTerm]
  | .historySingleton d t => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view d]
  | .historyAdd a b => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view a, evalTerm_substituteGhosts interpretation model σ env view b]
  | .historyCount h d t => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view h, evalTerm_substituteGhosts interpretation model σ env view d]
  | .provenanceEmpty => by
      simp only [AssertionTerm.substituteGhosts, evalTerm]
  | .provenanceSingleton d p => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view d]
  | .provenanceAdd a b => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view a, evalTerm_substituteGhosts interpretation model σ env view b]
  | .pvalue t => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalNumericalEvent_substituteGhosts interpretation model σ env view t]
  | .realAdd a b => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view a, evalTerm_substituteGhosts interpretation model σ env view b]
  | .realMin a b => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view a, evalTerm_substituteGhosts interpretation model σ env view b]
  | .intAdd a b => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view a, evalTerm_substituteGhosts interpretation model σ env view b]
  | .intSub a b => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view a, evalTerm_substituteGhosts interpretation model σ env view b]
  | .intLess a b => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view a, evalTerm_substituteGhosts interpretation model σ env view b]
  | .booleanNot a => by
      simp only [AssertionTerm.substituteGhosts, evalTerm, evalTerm_substituteGhosts interpretation model σ env view a]
theorem evalArguments_substituteGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (σ : GhostSubstitution context target)
    (env : GhostEnv D Command target) (view : SemanticView D) :
    (term : ValueArguments context inputs) →
    evalArguments interpretation model env view (ValueArguments.substituteGhosts σ term) =
      evalArguments interpretation model (substitutionEnv interpretation σ env) view term
  | .nil => by
      simp only [ValueArguments.substituteGhosts, evalArguments]
  | .cons a r => by
      simp only [ValueArguments.substituteGhosts, evalArguments, evalTerm_substituteGhosts interpretation model σ env view a, evalArguments_substituteGhosts interpretation model σ env view r]
theorem evalNumericalEvent_substituteGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (σ : GhostSubstitution context target)
    (env : GhostEnv D Command target) (view : SemanticView D) :
    (term : TestExpression context) →
    evalNumericalEvent interpretation model env view (TestExpression.substituteGhosts σ term) =
      evalNumericalEvent interpretation model (substitutionEnv interpretation σ env) view term
  | .leaf h d t p => by
      simp only [TestExpression.substituteGhosts, evalNumericalEvent, evalTerm_substituteGhosts interpretation model σ env view d]
  | .disj n a b => by
      simp only [TestExpression.substituteGhosts, evalNumericalEvent, evalNumericalEvent_substituteGhosts interpretation model σ env view a, evalNumericalEvent_substituteGhosts interpretation model σ env view b]
  | .conj n a b => by
      simp only [TestExpression.substituteGhosts, evalNumericalEvent, evalNumericalEvent_substituteGhosts interpretation model σ env view a, evalNumericalEvent_substituteGhosts interpretation model σ env view b]
end

theorem evalTestEntries_substituteGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (σ : GhostSubstitution context target)
    (env : GhostEnv D Command target) (view : SemanticView D) :
    (expression : TestExpression context) →
    evalTestEntries interpretation model env view (expression.substituteGhosts σ) =
      evalTestEntries interpretation model (substitutionEnv interpretation σ env) view expression
  | .leaf h d t pop => by
      simp only [TestExpression.substituteGhosts, evalTestEntries,
        evalTerm_substituteGhosts interpretation model σ env view d]
  | .disj n a b => by
      simp only [TestExpression.substituteGhosts, evalTestEntries,
        evalTestEntries_substituteGhosts interpretation model σ env view a,
        evalTestEntries_substituteGhosts interpretation model σ env view b]
  | .conj n a b => by
      simp only [TestExpression.substituteGhosts, evalTestEntries,
        evalTestEntries_substituteGhosts interpretation model σ env view a,
        evalTestEntries_substituteGhosts interpretation model σ env view b]

theorem evalTestHistory_substituteGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (σ : GhostSubstitution context target)
    (env : GhostEnv D Command target) (view : SemanticView D) (expression : TestExpression context) :
    evalTestHistory interpretation model env view (expression.substituteGhosts σ) =
      evalTestHistory interpretation model (substitutionEnv interpretation σ env) view expression := by
  simp only [evalTestHistory, evalTestEntries_substituteGhosts]

theorem modelRequirements_substituteGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (σ : GhostSubstitution context target)
    (env : GhostEnv D Command target) (view : SemanticView D) :
    (expression : TestExpression context) →
    (modelRequirements interpretation model env view (expression.substituteGhosts σ) ↔
      modelRequirements interpretation model (substitutionEnv interpretation σ env) view expression)
  | .leaf h d t pop => by
      simp only [TestExpression.substituteGhosts, modelRequirements, evalTerm_substituteGhosts]
  | .disj n a b => by
      have ht := evalTestEntries_substituteGhosts interpretation model σ env view (.disj n a b)
      simp only [TestExpression.substituteGhosts] at ht
      simp only [TestExpression.substituteGhosts, modelRequirements, ht,
        modelRequirements_substituteGhosts interpretation model σ env view a,
        modelRequirements_substituteGhosts interpretation model σ env view b]
  | .conj n a b => by
      have ht := evalTestEntries_substituteGhosts interpretation model σ env view (.conj n a b)
      simp only [TestExpression.substituteGhosts] at ht
      simp only [TestExpression.substituteGhosts, modelRequirements, ht,
        modelRequirements_substituteGhosts interpretation model σ env view a,
        modelRequirements_substituteGhosts interpretation model σ env view b]

theorem atomMeaning_substituteGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (σ : GhostSubstitution context target)
    (env : GhostEnv D Command target) (view : SemanticView D) (atom : AssertionAtom context) :
    atomMeaning interpretation model env view (atom.substituteGhosts σ) ↔
      atomMeaning interpretation model (substitutionEnv interpretation σ env) view atom := by
  cases atom <;> simp only [AssertionAtom.substituteGhosts, atomMeaning,
    evalTerm_substituteGhosts, evalArguments_substituteGhosts, modelRequirements_substituteGhosts]

theorem viewModalSatisfaction_substituteGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (σ : GhostSubstitution context target)
    (env : GhostEnv D Command target) (view : SemanticView D) :
    (formula : ModalFormula context) →
    (viewModalSatisfaction interpretation model env view (formula.substituteGhosts σ) ↔
      viewModalSatisfaction interpretation model (substitutionEnv interpretation σ env) view formula)
  | .atom a => by
      simp only [ModalFormula.substituteGhosts, viewModalSatisfaction, atomMeaning_substituteGhosts]
  | .neg a => by
      have ha (node : SemanticView D) := viewModalSatisfaction_substituteGhosts interpretation model σ env node a
      simp only [ModalFormula.substituteGhosts, viewModalSatisfaction, ha]
  | .conj a b => by
      have ha (node : SemanticView D) := viewModalSatisfaction_substituteGhosts interpretation model σ env node a
      have hb (node : SemanticView D) := viewModalSatisfaction_substituteGhosts interpretation model σ env node b
      simp only [ModalFormula.substituteGhosts, viewModalSatisfaction, ha, hb]
  | .knows a => by
      have ha (node : SemanticView D) := viewModalSatisfaction_substituteGhosts interpretation model σ env node a
      simp only [ModalFormula.substituteGhosts, viewModalSatisfaction, ha]
  | .atWorld w a => by
      have ha (node : SemanticView D) := viewModalSatisfaction_substituteGhosts interpretation model σ env node a
      simp only [ModalFormula.substituteGhosts, viewModalSatisfaction, evalTerm_substituteGhosts, ha]
  | .atView v a => by
      have ha (node : SemanticView D) := viewModalSatisfaction_substituteGhosts interpretation model σ env node a
      simp only [ModalFormula.substituteGhosts, viewModalSatisfaction, evalTerm_substituteGhosts, ha]

theorem viewAssertionSatisfaction_substituteGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) {context target : List GhostSort}
    (σ : GhostSubstitution context target) (env : GhostEnv D Command target)
    (view : SemanticView D) : (assertion : Assertion context) →
    (viewAssertionSatisfaction interpretation model env view (assertion.substituteGhosts σ) ↔
      viewAssertionSatisfaction interpretation model (substitutionEnv interpretation σ env) view assertion)
  | .modal a => by
      simp only [Assertion.substituteGhosts, viewAssertionSatisfaction, viewModalSatisfaction_substituteGhosts]
  | .neg a => by
      have ha (node : SemanticView D) := viewAssertionSatisfaction_substituteGhosts interpretation model σ env node a
      simp only [Assertion.substituteGhosts, viewAssertionSatisfaction, ha]
  | .conj a b => by
      have ha (node : SemanticView D) := viewAssertionSatisfaction_substituteGhosts interpretation model σ env node a
      have hb (node : SemanticView D) := viewAssertionSatisfaction_substituteGhosts interpretation model σ env node b
      simp only [Assertion.substituteGhosts, viewAssertionSatisfaction, ha, hb]
  | .all s a => by
      have ha (value : GhostValue D Command s) :=
        viewAssertionSatisfaction_substituteGhosts interpretation model (GhostSubstitution.lift σ)
          (GhostEnv.push value env) view a
      simp only [Assertion.substituteGhosts, viewAssertionSatisfaction, ha, substitutionEnv_lift_push]
  | .atWorld w a => by
      have ha (node : SemanticView D) := viewAssertionSatisfaction_substituteGhosts interpretation model σ env node a
      simp only [Assertion.substituteGhosts, viewAssertionSatisfaction, evalTerm_substituteGhosts, ha]
  | .atView v a => by
      have ha (node : SemanticView D) := viewAssertionSatisfaction_substituteGhosts interpretation model σ env node a
      simp only [Assertion.substituteGhosts, viewAssertionSatisfaction, evalTerm_substituteGhosts, ha]

theorem referenceModalSatisfaction_substituteGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (σ : GhostSubstitution context target)
    (env : GhostEnv D Command target) (world : World D Command) :
    (formula : ModalFormula context) →
    (referenceModalSatisfaction interpretation model env world (formula.substituteGhosts σ) ↔
      referenceModalSatisfaction interpretation model (substitutionEnv interpretation σ env) world formula)
  | .atom a => by
      simp only [ModalFormula.substituteGhosts, referenceModalSatisfaction, atomMeaning_substituteGhosts]
  | .neg a => by
      have ha (node : World D Command) := referenceModalSatisfaction_substituteGhosts interpretation model σ env node a
      simp only [ModalFormula.substituteGhosts, referenceModalSatisfaction, ha]
  | .conj a b => by
      have ha (node : World D Command) := referenceModalSatisfaction_substituteGhosts interpretation model σ env node a
      have hb (node : World D Command) := referenceModalSatisfaction_substituteGhosts interpretation model σ env node b
      simp only [ModalFormula.substituteGhosts, referenceModalSatisfaction, ha, hb]
  | .knows a => by
      have ha (node : World D Command) := referenceModalSatisfaction_substituteGhosts interpretation model σ env node a
      simp only [ModalFormula.substituteGhosts, referenceModalSatisfaction, knows, ha]
  | .atWorld w a => by
      have ha (node : World D Command) := referenceModalSatisfaction_substituteGhosts interpretation model σ env node a
      simp only [ModalFormula.substituteGhosts, referenceModalSatisfaction, evalTerm_substituteGhosts, ha]
  | .atView v a => by
      have ha (node : World D Command) := referenceModalSatisfaction_substituteGhosts interpretation model σ env node a
      simp only [ModalFormula.substituteGhosts, referenceModalSatisfaction, evalTerm_substituteGhosts, ha]

theorem referenceAssertionSatisfaction_substituteGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) {context target : List GhostSort}
    (σ : GhostSubstitution context target) (env : GhostEnv D Command target)
    (world : World D Command) : (assertion : Assertion context) →
    (referenceAssertionSatisfaction interpretation model env world (assertion.substituteGhosts σ) ↔
      referenceAssertionSatisfaction interpretation model (substitutionEnv interpretation σ env) world assertion)
  | .modal a => by
      simp only [Assertion.substituteGhosts, referenceAssertionSatisfaction, referenceModalSatisfaction_substituteGhosts]
  | .neg a => by
      have ha (node : World D Command) := referenceAssertionSatisfaction_substituteGhosts interpretation model σ env node a
      simp only [Assertion.substituteGhosts, referenceAssertionSatisfaction, ha]
  | .conj a b => by
      have ha (node : World D Command) := referenceAssertionSatisfaction_substituteGhosts interpretation model σ env node a
      have hb (node : World D Command) := referenceAssertionSatisfaction_substituteGhosts interpretation model σ env node b
      simp only [Assertion.substituteGhosts, referenceAssertionSatisfaction, ha, hb]
  | .all s a => by
      have ha (value : GhostValue D Command s) :=
        referenceAssertionSatisfaction_substituteGhosts interpretation model (GhostSubstitution.lift σ)
          (GhostEnv.push value env) world a
      simp only [Assertion.substituteGhosts, referenceAssertionSatisfaction, ha, substitutionEnv_lift_push]
  | .atWorld w a => by
      have ha (node : World D Command) := referenceAssertionSatisfaction_substituteGhosts interpretation model σ env node a
      simp only [Assertion.substituteGhosts, referenceAssertionSatisfaction, evalTerm_substituteGhosts, ha]
  | .atView v a => by
      have ha (node : World D Command) := referenceAssertionSatisfaction_substituteGhosts interpretation model σ env node a
      simp only [Assertion.substituteGhosts, referenceAssertionSatisfaction, evalTerm_substituteGhosts, ha]

theorem satisfies_substituteGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (σ : GhostSubstitution context target)
    (env : GhostEnv D Command target) (world : World D Command) (assertion : Assertion context) :
    satisfies interpretation model env world (assertion.substituteGhosts σ) ↔
      satisfies interpretation model (substitutionEnv interpretation σ env) world assertion := by
  simp only [satisfies, referenceAssertionSatisfaction_substituteGhosts]

theorem satisfiesView_substituteGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (σ : GhostSubstitution context target)
    (env : GhostEnv D Command target) (view : SemanticView D) (assertion : Assertion context) :
    satisfiesView interpretation model env view (assertion.substituteGhosts σ) ↔
      satisfiesView interpretation model (substitutionEnv interpretation σ env) view assertion := by
  simp only [satisfiesView, viewAssertionSatisfaction_substituteGhosts]

theorem evalTerm_renameGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (ρ : GhostRenaming context target)
    (env : GhostEnv D Command target) (view : SemanticView D)
    (term : AssertionTerm context sort) :
    evalTerm interpretation model env view (term.renameGhosts ρ) =
      evalTerm interpretation model (GhostEnv.reindex ρ env) view term := by
  rw [AssertionTerm.renameGhosts_eq_substituteGhosts]
  simpa only [substitutionEnv_ofRenaming] using
    evalTerm_substituteGhosts interpretation model (GhostSubstitution.ofRenaming ρ) env view term

theorem evalArguments_renameGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (ρ : GhostRenaming context target)
    (env : GhostEnv D Command target) (view : SemanticView D)
    (term : ValueArguments context inputs) :
    evalArguments interpretation model env view (term.renameGhosts ρ) =
      evalArguments interpretation model (GhostEnv.reindex ρ env) view term := by
  rw [ValueArguments.renameGhosts_eq_substituteGhosts]
  simpa only [substitutionEnv_ofRenaming] using
    evalArguments_substituteGhosts interpretation model (GhostSubstitution.ofRenaming ρ) env view term

theorem evalNumericalEvent_renameGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (ρ : GhostRenaming context target)
    (env : GhostEnv D Command target) (view : SemanticView D)
    (term : TestExpression context) :
    evalNumericalEvent interpretation model env view (term.renameGhosts ρ) =
      evalNumericalEvent interpretation model (GhostEnv.reindex ρ env) view term := by
  rw [TestExpression.renameGhosts_eq_substituteGhosts]
  simpa only [substitutionEnv_ofRenaming] using
    evalNumericalEvent_substituteGhosts interpretation model (GhostSubstitution.ofRenaming ρ) env view term

theorem atomMeaning_renameGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (ρ : GhostRenaming context target)
    (env : GhostEnv D Command target) (view : SemanticView D)
    (term : AssertionAtom context) :
    atomMeaning interpretation model env view (term.renameGhosts ρ) ↔
      atomMeaning interpretation model (GhostEnv.reindex ρ env) view term := by
  rw [AssertionAtom.renameGhosts_eq_substituteGhosts]
  simpa only [substitutionEnv_ofRenaming] using
    atomMeaning_substituteGhosts interpretation model (GhostSubstitution.ofRenaming ρ) env view term

theorem viewModalSatisfaction_renameGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (ρ : GhostRenaming context target)
    (env : GhostEnv D Command target) (view : SemanticView D)
    (term : ModalFormula context) :
    viewModalSatisfaction interpretation model env view (term.renameGhosts ρ) ↔
      viewModalSatisfaction interpretation model (GhostEnv.reindex ρ env) view term := by
  rw [ModalFormula.renameGhosts_eq_substituteGhosts]
  simpa only [substitutionEnv_ofRenaming] using
    viewModalSatisfaction_substituteGhosts interpretation model (GhostSubstitution.ofRenaming ρ) env view term

theorem referenceModalSatisfaction_renameGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (ρ : GhostRenaming context target)
    (env : GhostEnv D Command target) (world : World D Command)
    (term : ModalFormula context) :
    referenceModalSatisfaction interpretation model env world (term.renameGhosts ρ) ↔
      referenceModalSatisfaction interpretation model (GhostEnv.reindex ρ env) world term := by
  rw [ModalFormula.renameGhosts_eq_substituteGhosts]
  simpa only [substitutionEnv_ofRenaming] using
    referenceModalSatisfaction_substituteGhosts interpretation model (GhostSubstitution.ofRenaming ρ) env world term

theorem viewAssertionSatisfaction_renameGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (ρ : GhostRenaming context target)
    (env : GhostEnv D Command target) (view : SemanticView D)
    (term : Assertion context) :
    viewAssertionSatisfaction interpretation model env view (term.renameGhosts ρ) ↔
      viewAssertionSatisfaction interpretation model (GhostEnv.reindex ρ env) view term := by
  rw [Assertion.renameGhosts_eq_substituteGhosts]
  simpa only [substitutionEnv_ofRenaming] using
    viewAssertionSatisfaction_substituteGhosts interpretation model (GhostSubstitution.ofRenaming ρ) env view term

theorem referenceAssertionSatisfaction_renameGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (ρ : GhostRenaming context target)
    (env : GhostEnv D Command target) (world : World D Command)
    (term : Assertion context) :
    referenceAssertionSatisfaction interpretation model env world (term.renameGhosts ρ) ↔
      referenceAssertionSatisfaction interpretation model (GhostEnv.reindex ρ env) world term := by
  rw [Assertion.renameGhosts_eq_substituteGhosts]
  simpa only [substitutionEnv_ofRenaming] using
    referenceAssertionSatisfaction_substituteGhosts interpretation model (GhostSubstitution.ofRenaming ρ) env world term

theorem satisfies_renameGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (ρ : GhostRenaming context target)
    (env : GhostEnv D Command target) (world : World D Command)
    (term : Assertion context) :
    satisfies interpretation model env world (term.renameGhosts ρ) ↔
      satisfies interpretation model (GhostEnv.reindex ρ env) world term := by
  rw [Assertion.renameGhosts_eq_substituteGhosts]
  simpa only [substitutionEnv_ofRenaming] using
    satisfies_substituteGhosts interpretation model (GhostSubstitution.ofRenaming ρ) env world term

theorem satisfiesView_renameGhosts (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (ρ : GhostRenaming context target)
    (env : GhostEnv D Command target) (view : SemanticView D)
    (term : Assertion context) :
    satisfiesView interpretation model env view (term.renameGhosts ρ) ↔
      satisfiesView interpretation model (GhostEnv.reindex ρ env) view term := by
  rw [Assertion.renameGhosts_eq_substituteGhosts]
  simpa only [substitutionEnv_ofRenaming] using
    satisfiesView_substituteGhosts interpretation model (GhostSubstitution.ofRenaming ρ) env view term

end
end Lara.BHL
