import Lara.BHL.Assertion

namespace Lara.BHL

noncomputable section

variable {D Command : Type} [mD : MeasurableSpace D]

omit mD in
/-- Every admitted full world realizes a view in the independent view carrier. -/
theorem semanticView_mem_views (model : Model D Command) {world : World D Command}
    (hadmitted : Admitted model.dynamics world) :
    semanticView model.dynamics world ∈ model.views :=
  ⟨⟨world, hadmitted⟩, rfl⟩

/-- The correspondence holds even at raw, non-admitted source worlds. Knowledge
uses full-observation forth and reconstructs an admitted full alternative for
back. Scoped views require every full representative, without changing ghosts. -/
theorem reference_view_modal_correspondence
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (world : World D Command)
    (formula : ModalFormula context) :
    referenceModalSatisfaction interpretation model env world formula ↔
      viewModalSatisfaction interpretation model env (semanticView model.dynamics world) formula := by
  induction formula generalizing world with
  | atom atom => rfl
  | neg formula ih =>
      exact not_congr (ih world)
  | conj left right ihleft ihright =>
      exact and_congr (ihleft world) (ihright world)
  | knows formula ih =>
      change knows model world (fun alternative =>
        referenceModalSatisfaction interpretation model env alternative formula) ↔
        ∀ alternative, alternative ∈ model.views →
          ViewAccessible (semanticView model.dynamics world) alternative →
          viewModalSatisfaction interpretation model env alternative formula
      constructor
      · intro h alternative hrealized haccessible
        rcases hrealized with ⟨target, htarget⟩
        have hview : ViewAccessible (semanticView model.dynamics world)
            (semanticView model.dynamics target.val) := by
          rw [htarget]
          exact haccessible
        rcases view_accessible_back target.property hview with
          ⟨rebuilt, hadmitted, hfull, hsemantic⟩
        have hbody := (ih rebuilt).mp (h rebuilt hadmitted hfull)
        simpa only [hsemantic, htarget] using hbody
      · intro h alternative hadmitted haccessible
        exact (ih alternative).mpr
          (h (semanticView model.dynamics alternative)
            (semanticView_mem_views model hadmitted)
            (view_accessible_forth model.dynamics haccessible))
  | atWorld target formula ih =>
      change (∃ alternative,
        evalTerm interpretation model env (semanticView model.dynamics world) target = some alternative ∧
        Admitted model.dynamics alternative ∧
        referenceModalSatisfaction interpretation model env alternative formula) ↔
        ∃ alternative,
          evalTerm interpretation model env (semanticView model.dynamics world) target = some alternative ∧
          Admitted model.dynamics alternative ∧
          viewModalSatisfaction interpretation model env (semanticView model.dynamics alternative) formula
      constructor
      · rintro ⟨alternative, heval, hadmitted, hbody⟩
        exact ⟨alternative, heval, hadmitted, (ih alternative).mp hbody⟩
      · rintro ⟨alternative, heval, hadmitted, hbody⟩
        exact ⟨alternative, heval, hadmitted, (ih alternative).mpr hbody⟩
  | atView target formula ih =>
      change (∃ view,
        evalTerm interpretation model env (semanticView model.dynamics world) target = some view ∧
        view ∈ model.views ∧ ∀ alternative, Admitted model.dynamics alternative →
          semanticView model.dynamics alternative = view →
          referenceModalSatisfaction interpretation model env alternative formula) ↔
        ∃ view,
          evalTerm interpretation model env (semanticView model.dynamics world) target = some view ∧
          view ∈ model.views ∧ viewModalSatisfaction interpretation model env view formula
      constructor
      · rintro ⟨view, heval, hrealized, hbody⟩
        rcases hrealized with ⟨representative, hrepresentative⟩
        refine ⟨view, heval, ⟨representative, hrepresentative⟩, ?_⟩
        have h := (ih representative.val).mp
          (hbody representative.val representative.property hrepresentative)
        simpa only [hrepresentative] using h
      · rintro ⟨view, heval, hrealized, hbody⟩
        refine ⟨view, heval, hrealized, ?_⟩
        intro alternative _ hsemantic
        apply (ih alternative).mpr
        rw [hsemantic]
        exact hbody

/-- Outer induction generalizes the environment: unrestricted ghost binders
extend it with each actual value while both semantics retain the same binding. -/
theorem reference_view_assertion_correspondence
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (world : World D Command)
    (assertion : Assertion context) :
    referenceAssertionSatisfaction interpretation model env world assertion ↔
      viewAssertionSatisfaction interpretation model env (semanticView model.dynamics world) assertion := by
  induction assertion generalizing world with
  | modal formula =>
      exact reference_view_modal_correspondence interpretation model env world formula
  | neg assertion ih =>
      exact not_congr (ih env world)
  | conj left right ihleft ihright =>
      exact and_congr (ihleft env world) (ihright env world)
  | all sort body ih =>
      change (∀ value : GhostValue D Command sort,
        referenceAssertionSatisfaction interpretation model (GhostEnv.push value env) world body) ↔
        ∀ value : GhostValue D Command sort,
          viewAssertionSatisfaction interpretation model (GhostEnv.push value env)
            (semanticView model.dynamics world) body
      constructor
      · intro h value
        exact (ih (GhostEnv.push value env) world).mp (h value)
      · intro h value
        exact (ih (GhostEnv.push value env) world).mpr (h value)
  | atWorld target body ih =>
      change (∃ alternative,
        evalTerm interpretation model env (semanticView model.dynamics world) target = some alternative ∧
        Admitted model.dynamics alternative ∧
        referenceAssertionSatisfaction interpretation model env alternative body) ↔
        ∃ alternative,
          evalTerm interpretation model env (semanticView model.dynamics world) target = some alternative ∧
          Admitted model.dynamics alternative ∧
          viewAssertionSatisfaction interpretation model env (semanticView model.dynamics alternative) body
      constructor
      · rintro ⟨alternative, heval, hadmitted, hbody⟩
        exact ⟨alternative, heval, hadmitted, (ih env alternative).mp hbody⟩
      · rintro ⟨alternative, heval, hadmitted, hbody⟩
        exact ⟨alternative, heval, hadmitted, (ih env alternative).mpr hbody⟩
  | atView target body ih =>
      change (∃ view,
        evalTerm interpretation model env (semanticView model.dynamics world) target = some view ∧
        view ∈ model.views ∧ ∀ alternative, Admitted model.dynamics alternative →
          semanticView model.dynamics alternative = view →
          referenceAssertionSatisfaction interpretation model env alternative body) ↔
        ∃ view,
          evalTerm interpretation model env (semanticView model.dynamics world) target = some view ∧
          view ∈ model.views ∧ viewAssertionSatisfaction interpretation model env view body
      constructor
      · rintro ⟨view, heval, hrealized, hbody⟩
        rcases hrealized with ⟨representative, hrepresentative⟩
        refine ⟨view, heval, ⟨representative, hrepresentative⟩, ?_⟩
        have h := (ih env representative.val).mp
          (hbody representative.val representative.property hrepresentative)
        simpa only [hrepresentative] using h
      · rintro ⟨view, heval, hrealized, hbody⟩
        refine ⟨view, heval, hrealized, ?_⟩
        intro alternative _ hsemantic
        apply (ih env alternative).mpr
        rw [hsemantic]
        exact hbody

theorem satisfies_view_iff
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (world : World D Command)
    (hadmitted : Admitted model.dynamics world) (assertion : Assertion context) :
    satisfies interpretation model env world assertion ↔
      satisfiesView interpretation model env (semanticView model.dynamics world) assertion := by
  constructor
  · intro h
    exact ⟨semanticView_mem_views model hadmitted,
      (reference_view_assertion_correspondence interpretation model env world assertion).mp h.2⟩
  · intro h
    exact ⟨hadmitted,
      (reference_view_assertion_correspondence interpretation model env world assertion).mpr h.2⟩

/-- Equal semantic views preserve public satisfaction with ghosts unchanged;
this does not identify the worlds' ordered observation traces. -/
theorem satisfies_congr
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) {left right : World D Command}
    (hleft : Admitted model.dynamics left) (hright : Admitted model.dynamics right)
    (hview : semanticView model.dynamics left = semanticView model.dynamics right)
    (assertion : Assertion context) :
    satisfies interpretation model env left assertion ↔
      satisfies interpretation model env right assertion := by
  rw [satisfies_view_iff interpretation model env left hleft assertion,
    satisfies_view_iff interpretation model env right hright assertion, hview]

omit mD
/-- Truth needs admission because the current world must be a quantified witness. -/
theorem know_truth (model : Model D Command) {world : World D Command}
    {predicate : World D Command → Prop} (hadmitted : Admitted model.dynamics world)
    (h : knows model world predicate) : predicate world :=
  h world hadmitted (accessible_refl world)

theorem know_distribution (model : Model D Command) {world : World D Command}
    {left right : World D Command → Prop}
    (himp : knows model world (fun alternative => left alternative → right alternative))
    (hleft : knows model world left) : knows model world right := by
  intro alternative hadmitted haccessible
  exact himp alternative hadmitted haccessible (hleft alternative hadmitted haccessible)

theorem knows_mono (model : Model D Command) {world : World D Command}
    {left right : World D Command → Prop}
    (himp : ∀ alternative, Admitted model.dynamics alternative → Accessible world alternative →
      left alternative → right alternative)
    (hleft : knows model world left) : knows model world right :=
  know_distribution model himp hleft

theorem knows_congr (model : Model D Command) {world : World D Command}
    {left right : World D Command → Prop}
    (hiff : ∀ alternative, Admitted model.dynamics alternative → Accessible world alternative →
      (left alternative ↔ right alternative)) :
    knows model world left ↔ knows model world right := by
  constructor
  · exact knows_mono model (fun alternative hadmitted haccessible =>
      (hiff alternative hadmitted haccessible).mp)
  · exact knows_mono model (fun alternative hadmitted haccessible =>
      (hiff alternative hadmitted haccessible).mpr)

/-- Reference knowledge is constant on a full-observation accessibility class. -/
theorem knows_invariant (model : Model D Command) {left right : World D Command}
    (haccessible : Accessible left right) (predicate : World D Command → Prop) :
    knows model left predicate ↔ knows model right predicate := by
  constructor
  · intro h alternative hadmitted hright
    exact h alternative hadmitted (accessible_trans haccessible hright)
  · intro h alternative hadmitted hleft
    exact h alternative hadmitted (accessible_trans (accessible_symm haccessible) hleft)

theorem know_positive_introspection (model : Model D Command) {world : World D Command}
    {predicate : World D Command → Prop} (h : knows model world predicate) :
    knows model world (fun alternative => knows model alternative predicate) := by
  intro alternative _ haccessible
  exact (knows_invariant model haccessible predicate).mp h

theorem know_negative_introspection (model : Model D Command) {world : World D Command}
    {predicate : World D Command → Prop} (h : ¬ knows model world predicate) :
    knows model world (fun alternative => ¬ knows model alternative predicate) := by
  intro alternative _ haccessible hknow
  exact h ((knows_invariant model haccessible predicate).mpr hknow)

theorem possible_iff_exists (model : Model D Command) (world : World D Command)
    (predicate : World D Command → Prop) :
    possible model world predicate ↔ ∃ alternative, Admitted model.dynamics alternative ∧
      Accessible world alternative ∧ predicate alternative := by
  classical
  simp only [possible, knows, not_forall, not_not, exists_prop]

theorem possible_mono (model : Model D Command) {world : World D Command}
    {left right : World D Command → Prop}
    (himp : ∀ alternative, Admitted model.dynamics alternative → Accessible world alternative →
      left alternative → right alternative)
    (hleft : possible model world left) : possible model world right := by
  rcases (possible_iff_exists model world left).mp hleft with
    ⟨alternative, hadmitted, haccessible, hbody⟩
  exact (possible_iff_exists model world right).mpr
    ⟨alternative, hadmitted, haccessible, himp alternative hadmitted haccessible hbody⟩

theorem possible_congr (model : Model D Command) {world : World D Command}
    {left right : World D Command → Prop}
    (hiff : ∀ alternative, Admitted model.dynamics alternative → Accessible world alternative →
      (left alternative ↔ right alternative)) :
    possible model world left ↔ possible model world right := by
  constructor
  · exact possible_mono model (fun alternative hadmitted haccessible =>
      (hiff alternative hadmitted haccessible).mp)
  · exact possible_mono model (fun alternative hadmitted haccessible =>
      (hiff alternative hadmitted haccessible).mpr)

theorem possible_invariant (model : Model D Command) {left right : World D Command}
    (haccessible : Accessible left right) (predicate : World D Command → Prop) :
    possible model left predicate ↔ possible model right predicate :=
  not_congr (knows_invariant model haccessible (fun alternative => ¬ predicate alternative))

/-- Possibility is known throughout the same full-observation class. -/
theorem possible_known (model : Model D Command) {world : World D Command}
    {predicate : World D Command → Prop} (h : possible model world predicate) :
    knows model world (fun alternative => possible model alternative predicate) :=
  know_negative_introspection model h

theorem know_possible_iff (model : Model D Command) {world : World D Command}
    (hadmitted : Admitted model.dynamics world) (predicate : World D Command → Prop) :
    knows model world (fun alternative => possible model alternative predicate) ↔
      possible model world predicate :=
  ⟨know_truth model hadmitted, possible_known model⟩

/-- Possibly knowing a predicate is equivalent to knowing it at an admitted
current world; the witness-to-knowledge direction needs no self witness. -/
theorem possible_know_iff (model : Model D Command) {world : World D Command}
    (hadmitted : Admitted model.dynamics world) (predicate : World D Command → Prop) :
    possible model world (fun alternative => knows model alternative predicate) ↔
      knows model world predicate := by
  constructor
  · intro h
    rcases (possible_iff_exists model world (fun alternative =>
      knows model alternative predicate)).mp h with ⟨alternative, _, haccessible, hknow⟩
    exact (knows_invariant model haccessible predicate).mpr hknow
  · intro h
    exact (possible_iff_exists model world (fun alternative =>
      knows model alternative predicate)).mpr ⟨world, hadmitted, accessible_refl world, h⟩

include mD

@[simp] theorem referenceModalSatisfaction_disj
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (world : World D Command)
    (left right : ModalFormula context) :
    referenceModalSatisfaction interpretation model env world (left.disj right) ↔
      referenceModalSatisfaction interpretation model env world left ∨
        referenceModalSatisfaction interpretation model env world right := by
  classical
  simp only [ModalFormula.disj, referenceModalSatisfaction, not_and_or, not_not]

@[simp] theorem referenceModalSatisfaction_implies
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (world : World D Command)
    (left right : ModalFormula context) :
    referenceModalSatisfaction interpretation model env world (left.implies right) ↔
      (referenceModalSatisfaction interpretation model env world left →
        referenceModalSatisfaction interpretation model env world right) := by
  classical
  constructor
  · intro h hp
    by_contra hq
    exact h ⟨fun hnp => hnp hp, hq⟩
  · intro h hneg
    exact hneg.2 (h (Classical.not_not.mp hneg.1))

@[simp] theorem referenceModalSatisfaction_possible
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (world : World D Command) (formula : ModalFormula context) :
    referenceModalSatisfaction interpretation model env world formula.possible ↔
      possible model world (fun alternative =>
        referenceModalSatisfaction interpretation model env alternative formula) := Iff.rfl

@[simp] theorem viewModalSatisfaction_disj
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (view : SemanticView D)
    (left right : ModalFormula context) :
    viewModalSatisfaction interpretation model env view (left.disj right) ↔
      viewModalSatisfaction interpretation model env view left ∨
        viewModalSatisfaction interpretation model env view right := by
  classical
  simp only [ModalFormula.disj, viewModalSatisfaction, not_and_or, not_not]

@[simp] theorem viewModalSatisfaction_implies
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (view : SemanticView D)
    (left right : ModalFormula context) :
    viewModalSatisfaction interpretation model env view (left.implies right) ↔
      (viewModalSatisfaction interpretation model env view left →
        viewModalSatisfaction interpretation model env view right) := by
  classical
  constructor
  · intro h hp
    by_contra hq
    exact h ⟨fun hnp => hnp hp, hq⟩
  · intro h hneg
    exact hneg.2 (h (Classical.not_not.mp hneg.1))

@[simp] theorem referenceAssertionSatisfaction_disj
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (world : World D Command)
    (left right : Assertion context) :
    referenceAssertionSatisfaction interpretation model env world (left.disj right) ↔
      referenceAssertionSatisfaction interpretation model env world left ∨
        referenceAssertionSatisfaction interpretation model env world right := by
  classical
  simp only [Assertion.disj, referenceAssertionSatisfaction, not_and_or, not_not]

@[simp] theorem referenceAssertionSatisfaction_implies
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (world : World D Command)
    (left right : Assertion context) :
    referenceAssertionSatisfaction interpretation model env world (left.implies right) ↔
      (referenceAssertionSatisfaction interpretation model env world left →
        referenceAssertionSatisfaction interpretation model env world right) := by
  classical
  constructor
  · intro h hp
    by_contra hq
    exact h ⟨fun hnp => hnp hp, hq⟩
  · intro h hneg
    exact hneg.2 (h (Classical.not_not.mp hneg.1))

@[simp] theorem referenceAssertionSatisfaction_exists
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (world : World D Command)
    (sort : GhostSort) (body : Assertion (sort :: context)) :
    referenceAssertionSatisfaction interpretation model env world (Assertion.exists sort body) ↔
      ∃ value : GhostValue D Command sort,
        referenceAssertionSatisfaction interpretation model (GhostEnv.push value env) world body := by
  classical
  simp only [Assertion.exists, referenceAssertionSatisfaction, not_forall, not_not]

@[simp] theorem viewAssertionSatisfaction_disj
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (view : SemanticView D)
    (left right : Assertion context) :
    viewAssertionSatisfaction interpretation model env view (left.disj right) ↔
      viewAssertionSatisfaction interpretation model env view left ∨
        viewAssertionSatisfaction interpretation model env view right := by
  classical
  simp only [Assertion.disj, viewAssertionSatisfaction, not_and_or, not_not]

@[simp] theorem viewAssertionSatisfaction_implies
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (view : SemanticView D)
    (left right : Assertion context) :
    viewAssertionSatisfaction interpretation model env view (left.implies right) ↔
      (viewAssertionSatisfaction interpretation model env view left →
        viewAssertionSatisfaction interpretation model env view right) := by
  classical
  constructor
  · intro h hp
    by_contra hq
    exact h ⟨fun hnp => hnp hp, hq⟩
  · intro h hneg
    exact hneg.2 (h (Classical.not_not.mp hneg.1))

@[simp] theorem viewAssertionSatisfaction_exists
    (interpretation : AssertionInterpretation D Command) (model : Model D Command)
    (env : GhostEnv D Command context) (view : SemanticView D)
    (sort : GhostSort) (body : Assertion (sort :: context)) :
    viewAssertionSatisfaction interpretation model env view (Assertion.exists sort body) ↔
      ∃ value : GhostValue D Command sort,
        viewAssertionSatisfaction interpretation model (GhostEnv.push value env) view body := by
  classical
  simp only [Assertion.exists, viewAssertionSatisfaction, not_forall, not_not]

end
end Lara.BHL
