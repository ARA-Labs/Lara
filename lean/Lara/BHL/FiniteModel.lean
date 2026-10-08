import Lara.Examples.BHLFiniteBelief

/-!
Executable satisfaction of an indexed fragment of the canonical assertion AST,
for the named binary run endpoints. The three hidden representatives cover the
entire accessible semantic-view image, not merely three chosen full worlds.
Only Boolean and Boolean-dataset ghost quantifiers have finite support. Integer,
real, world and trace quantifiers, arbitrary predicates/functions, and scoped
atWorld/atView formulas are deliberately outside this executable fragment.
-/

namespace Lara.BHL.FiniteModel

open Lara.Examples.BHLBinaryModel
open Lara.Examples.BHLFiniteBelief
open Lara.Examples.BHLSoundnessScience (allowed hiddenMemory theta lower upper alternative)
open Lara.Examples.BHLExecution (dataId aliasId)

/-- The declared hidden carrier, justified below from the model's initial law. -/
def hiddenCarrier : List Int := [-1, 0, 1]

/-- These sorts quantify over their whole mathematical carriers, both Bool. -/
inductive FiniteGhostSort : GhostSort → Type where
  | boolean : FiniteGhostSort (.value .boolean)
  | dataset : FiniteGhostSort .dataset

inductive BooleanTerm : AssertionTerm Γ (.value .boolean) → Type where
  | literal (value : Bool) : BooleanTerm (.boolean value)
  | bound (index : BoundGhost Γ (.value .boolean)) : BooleanTerm (.ghost (.bound index))
  | neg {term} : BooleanTerm term → BooleanTerm (.booleanNot term)

inductive DatasetTerm : AssertionTerm Γ .dataset → Type where
  | bound (index : BoundGhost Γ .dataset) : DatasetTerm (.ghost (.bound index))
  | read (name : DatasetId) : DatasetTerm (.datasetRead .ambient name)

/-- Support evidence is indexed by existing syntax, not a second formula AST.
The belief constructor supports exactly the independently proved PR07 bundle
family; recursive knowledge is also supported for every formula below. -/
inductive ModalSupported : ModalFormula Γ → Type where
  | booleanEqual {left right} : BooleanTerm left → BooleanTerm right →
      ModalSupported (.atom (.equal left right))
  | datasetEqual {left right} : DatasetTerm left → DatasetTerm right →
      ModalSupported (.atom (.equal left right))
  | lower : ModalSupported (lower : ModalFormula Γ)
  | upper : ModalSupported (upper : ModalFormula Γ)
  | belief (bundle : Bundle) (comparison : Comparison) (threshold : ℚ) :
      ModalSupported (statisticalBelief comparison (.rational threshold) (bundleTest bundle)
        (alternative : ModalFormula Γ))
  | neg {formula} : ModalSupported formula → ModalSupported (.neg formula)
  | conj {left right} : ModalSupported left → ModalSupported right →
      ModalSupported (.conj left right)
  | knows {formula} : ModalSupported formula → ModalSupported (.knows formula)

inductive Supported : {Γ : List GhostSort} → Assertion Γ → Type where
  | modal {formula : ModalFormula Γ} : ModalSupported formula → Supported (.modal formula)
  | neg {assertion : Assertion Γ} : Supported assertion → Supported (.neg assertion)
  | conj {left right : Assertion Γ} : Supported left → Supported right →
      Supported (.conj left right)
  | all {sort : GhostSort} {body : Assertion (sort :: Γ)} :
      FiniteGhostSort sort → Supported body → Supported (.all sort body)

def evalBoolean (env : GhostEnv Bool Primitive Γ) :
    {term : AssertionTerm Γ (.value .boolean)} → BooleanTerm term → Bool
  | _, .literal value => value
  | _, .bound index => env _ index
  | _, .neg term => !evalBoolean env term

def evalDataset (env : GhostEnv Bool Primitive Γ) (run : RunKind) (first second : Bool) :
    {term : AssertionTerm Γ .dataset} → DatasetTerm term → Bool
  | _, .bound index => env _ index
  | _, .read name => (endpointSnapshot run first second).datasets name

def evalModal (env : GhostEnv Bool Primitive Γ) (run : RunKind) (n : Int)
    (first second : Bool) : {formula : ModalFormula Γ} → ModalSupported formula → Bool
  | _, .booleanEqual left right => decide (evalBoolean env left = evalBoolean env right)
  | _, .datasetEqual left right =>
      decide (evalDataset env run first second left = evalDataset env run first second right)
  | _, .lower => decide (n < 0)
  | _, .upper => decide (0 < n)
  | _, .belief bundle comparison threshold => checkBelief run bundle first second comparison threshold
  | _, .neg formula => !evalModal env run n first second formula
  | _, .conj left right =>
      evalModal env run n first second left && evalModal env run n first second right
  | _, .knows formula => hiddenCarrier.all (fun m => evalModal env run m first second formula)

def evalFinite : {Γ : List GhostSort} → {assertion : Assertion Γ} → Supported assertion →
    GhostEnv Bool Primitive Γ → RunKind → Int → Bool → Bool → Bool
  | _, _, .modal formula, env, run, n, first, second => evalModal env run n first second formula
  | _, _, .neg assertion, env, run, n, first, second =>
      !evalFinite assertion env run n first second
  | _, _, .conj left right, env, run, n, first, second =>
      evalFinite left env run n first second && evalFinite right env run n first second
  | _, _, .all .boolean body, env, run, n, first, second =>
      evalFinite body (GhostEnv.push false env) run n first second &&
        evalFinite body (GhostEnv.push true env) run n first second
  | _, _, .all .dataset body, env, run, n, first, second =>
      evalFinite body (GhostEnv.push false env) run n first second &&
        evalFinite body (GhostEnv.push true env) run n first second

theorem hiddenCarrier_complete (n : Int) : n ∈ hiddenCarrier ↔ allowed .two n := by
  simp [hiddenCarrier, allowed, eq_comm]

/-- Admission fixes *all* hidden cells to an initially allowed canonical memory;
knowing only that the parameter lies in the carrier would not suffice. -/
theorem admitted_hidden_canonical {world : World Bool Primitive}
    (admitted : Admitted (context .two).model.dynamics world) :
    ∃ n ∈ hiddenCarrier, world.current.memory.hidden = hiddenMemory n := by
  obtain ⟨⟨n, hn, he⟩, _⟩ := (admitted_initial admitted).2
  exact ⟨n, (hiddenCarrier_complete n).mpr hn, (admitted_current_hidden admitted).trans he⟩

theorem endpoint_hidden (run : RunKind) (n : Int) (first second : Bool) :
    (endpointWorld run n first second).current.memory.hidden = hiddenMemory n := by
  cases run <;> rfl

theorem endpoint_datasets (run : RunKind) (n : Int) (first second : Bool) :
    (endpointWorld run n first second).current.datasets =
      (endpointSnapshot run first second).datasets := by
  cases run <;> rfl

private theorem view_eq_of_accessible_hidden {left right : World Bool Primitive}
    (accessible : Accessible left right)
    (hidden : left.current.memory.hidden = right.current.memory.hidden) :
    semanticView (context .two).model.dynamics left =
      semanticView (context .two).model.dynamics right := by
  unfold semanticView
  rw [accessible_current_visible accessible, accessible_history_eq accessible,
    hidden, compatibleHidden_eq_of_accessible accessible, accessible_sampling_provenance accessible]

/-- Every admitted full-observation alternative has the view of a carrier
endpoint, including the entire visible memory, ledger, compatible set and
sampling provenance. No bound on the number of full-world encodings is assumed. -/
theorem accessible_endpoint_coverage (run : RunKind) (n : Int) (first second : Bool)
    (world : World Bool Primitive)
    (admitted : Admitted (context .two).model.dynamics world)
    (accessible : Accessible (endpointWorld run n first second) world) :
    ∃ m ∈ hiddenCarrier, semanticView (context .two).model.dynamics world =
      semanticView (context .two).model.dynamics (endpointWorld run m first second) := by
  obtain ⟨m, hm, hidden⟩ := admitted_hidden_canonical admitted
  refine ⟨m, hm, view_eq_of_accessible_hidden ?_ ?_⟩
  · exact accessible_trans (accessible_symm accessible) (endpoint_accessible run n m first second)
  · exact hidden.trans (endpoint_hidden run m first second).symm

/-- Back reconstruction turns arbitrary admitted accessible *views* into full
alternatives. Rebuilding changes exactly the hidden field, by the existing
semanticView_rebuildHidden law used in view_accessible_back. -/
theorem accessible_view_coverage (run : RunKind) (n : Int) (first second : Bool)
    (view : SemanticView Bool) (realized : view ∈ (context .two).model.views)
    (accessible : ViewAccessible
      (semanticView (context .two).model.dynamics (endpointWorld run n first second)) view) :
    ∃ m ∈ hiddenCarrier, view =
      semanticView (context .two).model.dynamics (endpointWorld run m first second) := by
  rcases realized with ⟨target, htarget⟩
  have hview : ViewAccessible
      (semanticView (context .two).model.dynamics (endpointWorld run n first second))
      (semanticView (context .two).model.dynamics target.val) := by
    rw [htarget]
    exact accessible
  obtain ⟨rebuilt, admitted, full, semantic⟩ := view_accessible_back target.property hview
  obtain ⟨m, hm, covered⟩ := accessible_endpoint_coverage run n first second rebuilt admitted full
  exact ⟨m, hm, htarget.symm.trans (semantic.symm.trans covered)⟩

theorem carrier_endpoint_admitted (run : RunKind) (m : Int) (first second : Bool)
    (member : m ∈ hiddenCarrier) :
    Admitted (context .two).model.dynamics (endpointWorld run m first second) :=
  endpoint_admitted run m first second ((hiddenCarrier_complete m).mp member)

/-- Exact equality of the accessible admitted-view image with the finite frame. -/
theorem accessible_views_exact (run : RunKind) (n : Int) (first second : Bool)
    (view : SemanticView Bool) :
    (view ∈ (context .two).model.views ∧ ViewAccessible
      (semanticView (context .two).model.dynamics (endpointWorld run n first second)) view) ↔
      ∃ m ∈ hiddenCarrier, view =
        semanticView (context .two).model.dynamics (endpointWorld run m first second) := by
  constructor
  · rintro ⟨realized, accessible⟩
    exact accessible_view_coverage run n first second view realized accessible
  · rintro ⟨m, hm, rfl⟩
    exact ⟨semanticView_mem_views _ (carrier_endpoint_admitted run m first second hm),
      view_accessible_forth _ (endpoint_accessible run n m first second)⟩

private theorem reference_modal_same_view (env : GhostEnv Bool Primitive Γ)
    (formula : ModalFormula Γ) {left right : World Bool Primitive}
    (same : semanticView (context .two).model.dynamics left =
      semanticView (context .two).model.dynamics right) :
    referenceModalSatisfaction interpretation (context .two).model env left formula ↔
      referenceModalSatisfaction interpretation (context .two).model env right formula := by
  rw [reference_view_modal_correspondence, reference_view_modal_correspondence, same]

theorem evalBoolean_correct {term : AssertionTerm Γ (.value .boolean)}
    (support : BooleanTerm term) (env : GhostEnv Bool Primitive Γ) (view : SemanticView Bool) :
    evalTerm interpretation (context .two).model env view term = some (evalBoolean env support) := by
  induction support with
  | literal value => rfl
  | bound index => rfl
  | neg support ih => simp [evalTerm, evalBoolean, ih]

theorem evalDataset_correct {term : AssertionTerm Γ .dataset} (support : DatasetTerm term)
    (env : GhostEnv Bool Primitive Γ) (run : RunKind) (n : Int) (first second : Bool) :
    evalTerm interpretation (context .two).model env
      (semanticView (context .two).model.dynamics (endpointWorld run n first second)) term =
      some (evalDataset env run first second support) := by
  cases support with
  | bound index => rfl
  | read name =>
      simp [evalTerm, evalDataset, semanticView, State.visible, endpoint_datasets]

theorem evalModal_correct {formula : ModalFormula Γ} (support : ModalSupported formula)
    (env : GhostEnv Bool Primitive Γ) (run : RunKind) (n : Int) (first second : Bool) :
    evalModal env run n first second support = true ↔
      referenceModalSatisfaction interpretation (context .two).model env
        (endpointWorld run n first second) formula := by
  induction support generalizing n with
  | booleanEqual left right =>
      simp [evalModal, referenceModalSatisfaction, atomMeaning,
        evalBoolean_correct left env, evalBoolean_correct right env, eq_comm]
  | datasetEqual left right =>
      simp [evalModal, referenceModalSatisfaction, atomMeaning,
        evalDataset_correct left env run n first second,
        evalDataset_correct right env run n first second, eq_comm]
  | lower =>
      simp [evalModal, lower_iff, endpoint_hidden,
        Lara.Examples.BHLSoundnessScience.theta_hiddenMemory]
  | upper =>
      simp [evalModal, upper_iff, endpoint_hidden,
        Lara.Examples.BHLSoundnessScience.theta_hiddenMemory]
  | belief bundle comparison threshold =>
      exact checkBelief_correct run bundle env n first second comparison threshold
  | neg support ih =>
      simp only [evalModal, Bool.not_eq_true', referenceModalSatisfaction]
      exact (Bool.eq_false_iff).trans (not_congr (ih n))
  | conj left right ihleft ihright =>
      simp only [evalModal, Bool.and_eq_true, referenceModalSatisfaction]
      exact and_congr (ihleft n) (ihright n)
  | @knows body support ih =>
      change hiddenCarrier.all (fun m => evalModal env run m first second support) = true ↔
        knows (context .two).model (endpointWorld run n first second)
          (fun world => referenceModalSatisfaction interpretation (context .two).model env world body)
      rw [List.all_eq_true]
      constructor
      · intro checked world admitted accessible
        obtain ⟨m, hm, same⟩ := accessible_endpoint_coverage run n first second world admitted accessible
        exact (reference_modal_same_view env body same).mpr ((ih m).mp (checked m hm))
      · intro knowledge m hm
        exact (ih m).mpr (knowledge _ (carrier_endpoint_admitted run m first second hm)
          (endpoint_accessible run n m first second))

/-- The environment is arbitrary and generalized at every binder. Thus each
finite quantifier checks *every* value of its declared sort, not selected
example environments. This correspondence itself does not require admission. -/
theorem evalFinite_reference_correct {assertion : Assertion Γ} (support : Supported assertion)
    (env : GhostEnv Bool Primitive Γ) (run : RunKind) (n : Int) (first second : Bool) :
    evalFinite support env run n first second = true ↔
      referenceAssertionSatisfaction interpretation (context .two).model env
        (endpointWorld run n first second) assertion := by
  induction support with
  | modal formula => exact evalModal_correct formula env run n first second
  | neg support ih =>
      simp only [evalFinite, Bool.not_eq_true', referenceAssertionSatisfaction]
      exact (Bool.eq_false_iff).trans (not_congr (ih env))
  | conj left right ihleft ihright =>
      simp only [evalFinite, Bool.and_eq_true, referenceAssertionSatisfaction]
      exact and_congr (ihleft env) (ihright env)
  | @all Γ sort body finite support ih =>
      cases finite <;>
        simp only [evalFinite, Bool.and_eq_true, referenceAssertionSatisfaction]
      all_goals
        constructor
        · rintro ⟨hf, ht⟩ value
          cases value
          · exact (ih (GhostEnv.push false env)).mp hf
          · exact (ih (GhostEnv.push true env)).mp ht
        · intro h
          exact ⟨(ih (GhostEnv.push false env)).mpr (h false),
            (ih (GhostEnv.push true env)).mpr (h true)⟩

/-- Public satisfaction retains the independent model-admission obligation. -/
theorem evalFinite_correct {assertion : Assertion Γ} (support : Supported assertion)
    (env : GhostEnv Bool Primitive Γ) (run : RunKind) (n : Int) (first second : Bool)
    (admission : allowed .two n) :
    evalFinite support env run n first second = true ↔
      satisfies interpretation (context .two).model env (endpointWorld run n first second) assertion := by
  rw [satisfies, ← evalFinite_reference_correct support env run n first second]
  exact ⟨fun checked => ⟨endpoint_admitted run n first second admission, checked⟩, And.right⟩

/-- Entailment over the fixed run's endpoint carrier only. This is intentionally
not AssertionEntails, whose scope includes all admitted worlds and environments. -/
def FiniteEntails (run : RunKind) (env : GhostEnv Bool Primitive Γ)
    (pre post : Assertion Γ) : Prop :=
  ∀ n ∈ hiddenCarrier, ∀ first second,
    satisfies interpretation (context .two).model env (endpointWorld run n first second) pre →
      satisfies interpretation (context .two).model env (endpointWorld run n first second) post

def checkFiniteEntailment {pre post : Assertion Γ} (preSupport : Supported pre)
    (postSupport : Supported post) (env : GhostEnv Bool Primitive Γ) (run : RunKind) : Bool :=
  hiddenCarrier.all fun n => [false, true].all fun first => [false, true].all fun second =>
    !evalFinite preSupport env run n first second || evalFinite postSupport env run n first second

theorem checkFiniteEntailment_correct {pre post : Assertion Γ}
    (preSupport : Supported pre) (postSupport : Supported post)
    (env : GhostEnv Bool Primitive Γ) (run : RunKind) :
    checkFiniteEntailment preSupport postSupport env run = true ↔ FiniteEntails run env pre post := by
  simp only [checkFiniteEntailment, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', FiniteEntails]
  constructor
  · intro checked n hn first second satisfied
    have hp := (evalFinite_correct preSupport env run n first second
      ((hiddenCarrier_complete n).mp hn)).mpr satisfied
    rcases checked n hn first (by cases first <;> simp) second (by cases second <;> simp) with hf | ht
    · simp [hp] at hf
    · exact (evalFinite_correct postSupport env run n first second
        ((hiddenCarrier_complete n).mp hn)).mp ht
  · intro entails n hn first _ second _
    cases hp : evalFinite preSupport env run n first second with
    | false => exact Or.inl rfl
    | true =>
        exact Or.inr ((evalFinite_correct postSupport env run n first second
          ((hiddenCarrier_complete n).mp hn)).mpr (entails n hn first second
            ((evalFinite_correct preSupport env run n first second
              ((hiddenCarrier_complete n).mp hn)).mp hp)))

inductive AssertionRole where
  | precondition | postcondition
  deriving DecidableEq, Repr

inductive SatisfactionResult where
  | satisfied | failedPrecondition | falsePostcondition | outsideDeclaredFrame
  deriving DecidableEq, Repr

/-- Admission is checked independently of the formula evaluation. False pre/post
conditions remain distinct from execution exhaustion and undefined source steps. -/
def checkSatisfaction {assertion : Assertion Γ} (role : AssertionRole)
    (support : Supported assertion) (env : GhostEnv Bool Primitive Γ) (run : RunKind)
    (n : Int) (first second : Bool) : SatisfactionResult :=
  if allowed .two n then
    if evalFinite support env run n first second then .satisfied
    else match role with
      | .precondition => .failedPrecondition
      | .postcondition => .falsePostcondition
  else .outsideDeclaredFrame

theorem checkSatisfaction_correct {assertion : Assertion Γ} (role : AssertionRole)
    (support : Supported assertion) (env : GhostEnv Bool Primitive Γ) (run : RunKind)
    (n : Int) (first second : Bool) (admission : allowed .two n) :
    checkSatisfaction role support env run n first second = .satisfied ↔
      satisfies interpretation (context .two).model env (endpointWorld run n first second) assertion := by
  cases role <;> simp [checkSatisfaction, admission, ← evalFinite_correct support env run n first second admission]

theorem checkSatisfaction_pre_false {assertion : Assertion Γ}
    (support : Supported assertion) (env : GhostEnv Bool Primitive Γ) (run : RunKind)
    (n : Int) (first second : Bool) (admission : allowed .two n) :
    checkSatisfaction .precondition support env run n first second = .failedPrecondition ↔
      ¬ satisfies interpretation (context .two).model env (endpointWorld run n first second) assertion := by
  simp [checkSatisfaction, admission, ← evalFinite_correct support env run n first second admission]

theorem checkSatisfaction_post_false {assertion : Assertion Γ}
    (support : Supported assertion) (env : GhostEnv Bool Primitive Γ) (run : RunKind)
    (n : Int) (first second : Bool) (admission : allowed .two n) :
    checkSatisfaction .postcondition support env run n first second = .falsePostcondition ↔
      ¬ satisfies interpretation (context .two).model env (endpointWorld run n first second) assertion := by
  simp [checkSatisfaction, admission, ← evalFinite_correct support env run n first second admission]

namespace Examples

/-- Existential data chosen outside K remains rigid at every alternative. -/
def rigidDataset : Assertion [] := Assertion.exists .dataset
  (.modal (.knows (.atom (.equal (.ghost (.bound .here)) (.datasetRead .ambient dataId)))))

def rigidDatasetSupport : Supported rigidDataset :=
  .neg (.all .dataset (.neg (.modal (.knows (.datasetEqual (.bound .here) (.read dataId))))))

def allDatasetsKnown : Assertion [] := .all .dataset
  (.modal (.knows (.atom (.equal (.ghost (.bound .here)) (.datasetRead .ambient dataId)))))

def allDatasetsKnownSupport : Supported allDatasetsKnown :=
  .all .dataset (.modal (.knows (.datasetEqual (.bound .here) (.read dataId))))

def allBooleansReflexive : Assertion [] := .all (.value .boolean)
  (.modal (.knows (.atom (.equal (.ghost (.bound .here)) (.ghost (.bound .here))))))

def allBooleansReflexiveSupport : Supported allBooleansReflexive :=
  .all .boolean (.modal (.knows (.booleanEqual (.bound .here) (.bound .here))))

def lowerPossible : Assertion [] := .modal (lower.possible)

def lowerPossibleSupport : Supported lowerPossible := .modal (.neg (.knows (.neg .lower)))

def alternativeSupport : ModalSupported (alternative : ModalFormula Γ) :=
  .neg (.conj (.neg .lower) (.neg .upper))

def beliefWithoutTruth : Assertion [] := .modal
  ((statisticalBelief .equal (.rational (1 / 4)) (bundleTest (.single firstId)) alternative).conj
    (.neg alternative))

def beliefWithoutTruthSupport : Supported beliefWithoutTruth :=
  .modal (.conj (.belief (.single firstId) .equal (1 / 4)) (.neg alternativeSupport))

theorem quantified_examples :
    evalFinite rigidDatasetSupport GhostEnv.empty (.single firstId) 0 true true = true ∧
    evalFinite allDatasetsKnownSupport GhostEnv.empty (.single firstId) 0 true true = false ∧
    evalFinite allBooleansReflexiveSupport GhostEnv.empty (.single firstId) 0 true true = true := by
  norm_num [evalFinite, evalModal, evalDataset, evalBoolean, hiddenCarrier,
    rigidDatasetSupport, allDatasetsKnownSupport, allBooleansReflexiveSupport,
    GhostEnv.push, GhostEnv.empty, endpointSnapshot,
    Lara.Examples.BHLBinaryRuns.singleFinal, Lara.Examples.BHLBinaryRuns.runTest,
    Lara.Examples.BHLBinaryModel.initialSnapshot,
    Lara.Examples.BHLExecution.initialSnapshot, dataId, aliasId]

theorem epistemic_examples :
    evalFinite (.modal (.knows (.lower : ModalSupported (lower : ModalFormula []))))
      GhostEnv.empty (.single firstId) 0 true true = false ∧
    evalFinite lowerPossibleSupport GhostEnv.empty (.single firstId) 0 true true = true ∧
    evalFinite beliefWithoutTruthSupport GhostEnv.empty (.single firstId) 0 true true = true := by
  have checked : checkBelief (.single firstId) (.single firstId) true true .equal (1 / 4) = true :=
    exceptional_single_checked
  norm_num [evalFinite, evalModal, hiddenCarrier, lowerPossibleSupport,
    beliefWithoutTruthSupport, alternativeSupport, checked]

theorem belief_ledger_examples :
    evalFinite (.modal (.belief .disj .lessEqual (1 / 2)))
      GhostEnv.empty .pair 0 true true = true ∧
    evalFinite (.modal (.belief (.single firstId) .equal (1 / 4)))
      GhostEnv.empty .hidden 0 true true = false :=
  ⟨accounted_pair_checked.1, checkHiddenSingle_false true true .equal (1 / 4)⟩

end Examples
end Lara.BHL.FiniteModel
