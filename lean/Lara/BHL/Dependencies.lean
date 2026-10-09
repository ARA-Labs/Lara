import Lara.BHL.GhostTransforms
import Lara.BHL.Interpretation

namespace Lara.BHL

/-- Symbolic regions of the ambient view, not a finite enumeration of program
variables. Whole-carrier regions cover every name at every value sort, including
undefined cells. They therefore remain meaningful for an unbounded namespace. -/
inductive ReadRegion where
  | variable (sort : ValueSort) (visibility : Visibility) (name : Variable sort visibility)
  | dataset (name : DatasetId)
  | observableValues
  | datasets
  | hiddenValues
  | history
  | compatible
  | provenance

abbrev ReadSupport := List ReadRegion

/-- Lists are unions; duplicates have no semantic significance. -/
def visibleReadSupport : ReadSupport := [.observableValues, .datasets]

def observableReadSupport : ReadSupport :=
  visibleReadSupport ++ [.history, .compatible, .provenance]

def wholeViewReadSupport : ReadSupport :=
  visibleReadSupport ++ [.hiddenValues, .history, .compatible, .provenance]

/-- Coverage is semantic namespace coverage, not just occurrence in the list. -/
def ReadRegion.CoversVariable (region : ReadRegion) (x : Variable sort visibility) : Prop :=
  region = .variable sort visibility x ∨
    (visibility = .observable ∧ region = .observableValues) ∨
    (visibility = .invisible ∧ region = .hiddenValues)

def ReadSupport.CoversVariable (support : ReadSupport)
    (x : Variable sort visibility) : Prop :=
  ∃ region ∈ support, region.CoversVariable x

def ReadSupport.CoversDataset (support : ReadSupport) (name : DatasetId) : Prop :=
  .dataset name ∈ support ∨ .datasets ∈ support

mutual
/-- Conservative ambient read support. Direct ambient reads and projections are
precise. Other targets retain their entire support (including partiality), so
updates and reconstructed views can have false positives. Fixed ghost worlds
and traces have empty ambient support: their cells are not ambient cells.
This is not a modal frame theorem; knowledge additionally requires matching
accessible alternatives in both directions. -/
def AssertionTerm.readSupport : AssertionTerm context sort → ReadSupport
  | .ghost _ => []
  | .boolean _ => []
  | .integer _ => []
  | .rational _ => []
  | .apply _ args => ValueArguments.readSupport args
  | .datasetApply _ args => ValueArguments.readSupport args
  | .ambient => wholeViewReadSupport
  | .currentView world => AssertionTerm.readSupport world
  | .currentState world => AssertionTerm.readSupport world
  | .worldTrace world => AssertionTerm.readSupport world
  | .appendWorld world trace => AssertionTerm.readSupport world ++ AssertionTerm.readSupport trace
  | .traceEmpty => []
  | .traceSingleton state => AssertionTerm.readSupport state
  | .traceAppend left right => AssertionTerm.readSupport left ++ AssertionTerm.readSupport right
  | .traceLength trace => AssertionTerm.readSupport trace
  | .traceTake trace index => AssertionTerm.readSupport trace ++ AssertionTerm.readSupport index
  | .traceIndex trace index => AssertionTerm.readSupport trace ++ AssertionTerm.readSupport index
  | .valueRead .ambient x => [.variable _ _ x]
  | .valueRead target _ => AssertionTerm.readSupport target
  | .datasetRead .ambient name => [.dataset name]
  | .datasetRead target _ => AssertionTerm.readSupport target
  | .visibleOf .ambient => visibleReadSupport
  | .visibleOf target => AssertionTerm.readSupport target
  | .hiddenOf .ambient => [.hiddenValues]
  | .hiddenOf target => AssertionTerm.readSupport target
  | .historyOf .ambient => [.history]
  | .historyOf target => AssertionTerm.readSupport target
  | .provenanceOf .ambient => [.provenance]
  | .provenanceOf target => AssertionTerm.readSupport target
  | .compatibleOf .ambient => [.compatible]
  | .compatibleOf target => AssertionTerm.readSupport target
  | .makeView visible history hidden compatible provenance =>
      AssertionTerm.readSupport visible ++ AssertionTerm.readSupport history ++
      AssertionTerm.readSupport hidden ++ AssertionTerm.readSupport compatible ++
      AssertionTerm.readSupport provenance
  | .writeValue target _ rhs => AssertionTerm.readSupport target ++ AssertionTerm.readSupport rhs
  | .writeDataset target _ rhs => AssertionTerm.readSupport target ++ AssertionTerm.readSupport rhs
  | .addHistory target history => AssertionTerm.readSupport target ++ AssertionTerm.readSupport history
  | .historyEmpty => []
  | .historySingleton data _ => AssertionTerm.readSupport data
  | .historyAdd left right => AssertionTerm.readSupport left ++ AssertionTerm.readSupport right
  | .historyCount history data _ => AssertionTerm.readSupport history ++ AssertionTerm.readSupport data
  | .provenanceEmpty => []
  | .provenanceSingleton data _ => AssertionTerm.readSupport data
  | .provenanceAdd left right => AssertionTerm.readSupport left ++ AssertionTerm.readSupport right
  | .pvalue test => TestExpression.readSupport test
  | .realAdd left right => AssertionTerm.readSupport left ++ AssertionTerm.readSupport right
  | .realMin left right => AssertionTerm.readSupport left ++ AssertionTerm.readSupport right
  | .intAdd left right => AssertionTerm.readSupport left ++ AssertionTerm.readSupport right
  | .intSub left right => AssertionTerm.readSupport left ++ AssertionTerm.readSupport right
  | .intLess left right => AssertionTerm.readSupport left ++ AssertionTerm.readSupport right
  | .booleanNot term => AssertionTerm.readSupport term

def ValueArguments.readSupport : ValueArguments context inputs → ReadSupport
  | .nil => []
  | .cons term rest => AssertionTerm.readSupport term ++ ValueArguments.readSupport rest

def TestExpression.readSupport : TestExpression context → ReadSupport
  | .leaf _ data _ _ => AssertionTerm.readSupport data
  | .disj _ left right => TestExpression.readSupport left ++ TestExpression.readSupport right
  | .conj _ left right => TestExpression.readSupport left ++ TestExpression.readSupport right
end

def AssertionAtom.readSupport : AssertionAtom context → ReadSupport
  | .rigid _ args => args.readSupport
  | .equal left right => left.readSupport ++ right.readSupport
  | .defined term => term.readSupport
  | .realCompare _ left right => left.readSupport ++ right.readSupport
  | .intCompare _ left right => left.readSupport ++ right.readSupport
  | .hypothesis _ hidden => hidden.readSupport
  | .sampling data _ provenance => data.readSupport ++ provenance.readSupport
  | .requirements test view => test.readSupport ++ view.readSupport
  | .admitted world => world.readSupport
  | .action _ state => state.readSupport

/-- Scoped bodies are counted relative to their local view as an overapproximation
of ambient support; targets are always counted. Knowledge also records all
components defining accessibility. Absence alone does not justify modal framing. -/
def ModalFormula.readSupport : ModalFormula context → ReadSupport
  | .atom a => a.readSupport
  | .neg formula => formula.readSupport
  | .conj left right => left.readSupport ++ right.readSupport
  | .knows formula => observableReadSupport ++ formula.readSupport
  | .atWorld world formula => world.readSupport ++ formula.readSupport
  | .atView view formula => view.readSupport ++ formula.readSupport

def Assertion.readSupport : Assertion context → ReadSupport
  | .modal formula => formula.readSupport
  | .neg assertion => assertion.readSupport
  | .conj left right => left.readSupport ++ right.readSupport
  | .all _ assertion => assertion.readSupport
  | .atWorld world assertion => world.readSupport ++ assertion.readSupport
  | .atView view assertion => view.readSupport ++ assertion.readSupport

/-- Independently defined agreement on actual view components. In particular,
whole memory agreement includes both definedness and every typed cell value. -/
def ReadRegion.Agrees (region : ReadRegion) (left right : SemanticView D) : Prop :=
  match region with
  | .variable _ _ x =>
      (Memory.assemble left.visible.memory left.hidden).read x =
      (Memory.assemble right.visible.memory right.hidden).read x
  | .dataset name => left.visible.datasets name = right.visible.datasets name
  | .observableValues => left.visible.memory = right.visible.memory
  | .datasets => left.visible.datasets = right.visible.datasets
  | .hiddenValues => left.hidden = right.hidden
  | .history => left.history = right.history
  | .compatible => left.compatible = right.compatible
  | .provenance => left.provenance = right.provenance

def SupportAgreement (support : ReadSupport) (left right : SemanticView D) : Prop :=
  ∀ region, region ∈ support → region.Agrees left right

/-- Inventory: agreement decomposition for all compositional frame lemmas. -/
theorem SupportAgreement.append_iff (leftSupport rightSupport : ReadSupport)
    (left right : SemanticView D) :
    SupportAgreement (leftSupport ++ rightSupport) left right ↔
      SupportAgreement leftSupport left right ∧ SupportAgreement rightSupport left right := by
  simp only [SupportAgreement, List.mem_append]
  constructor
  · intro h
    exact ⟨fun region hr => h region (Or.inl hr), fun region hr => h region (Or.inr hr)⟩
  · rintro ⟨hl, hr⟩ region (h | h)
    · exact hl region h
    · exact hr region h

theorem SupportAgreement.append_left
    (h : SupportAgreement (a ++ b) left right) : SupportAgreement a left right :=
  (SupportAgreement.append_iff a b left right).mp h |>.1

theorem SupportAgreement.append_right
    (h : SupportAgreement (a ++ b) left right) : SupportAgreement b left right :=
  (SupportAgreement.append_iff a b left right).mp h |>.2

theorem SupportAgreement.visible_eq
    (h : SupportAgreement visibleReadSupport left right) : left.visible = right.visible := by
  have hm : left.visible.memory = right.visible.memory := h .observableValues (by simp [visibleReadSupport])
  have hd : left.visible.datasets = right.visible.datasets := h .datasets (by simp [visibleReadSupport])
  exact congrArg₂ VisibleState.mk hm hd

theorem SupportAgreement.view_eq
    (h : SupportAgreement wholeViewReadSupport left right) : left = right := by
  have hv : left.visible = right.visible :=
    SupportAgreement.visible_eq (SupportAgreement.append_left h)
  have hh : left.history = right.history := h .history (by simp [wholeViewReadSupport])
  have hm : left.hidden = right.hidden := h .hiddenValues (by simp [wholeViewReadSupport])
  have hc : left.compatible = right.compatible := h .compatible (by simp [wholeViewReadSupport])
  have hp : left.provenance = right.provenance := h .provenance (by simp [wholeViewReadSupport])
  cases left
  cases right
  cases hv
  cases hh
  cases hm
  cases hc
  cases hp
  rfl

/-- Inventory: exact direct-read and direct-projection support equations. -/
@[simp] theorem readSupport_valueRead_ambient (x : Variable sort visibility) :
    (AssertionTerm.valueRead (.ambient : AssertionTerm context .view) x).readSupport =
      [.variable sort visibility x] := rfl

@[simp] theorem readSupport_datasetRead_ambient (name : DatasetId) :
    (AssertionTerm.datasetRead (.ambient : AssertionTerm context .view) name).readSupport =
      [.dataset name] := rfl

@[simp] theorem readSupport_visibleOf_ambient :
    (AssertionTerm.visibleOf (.ambient : AssertionTerm context .view)).readSupport =
      visibleReadSupport := rfl

@[simp] theorem readSupport_hiddenOf_ambient :
    (AssertionTerm.hiddenOf (.ambient : AssertionTerm context .view)).readSupport =
      [.hiddenValues] := rfl

@[simp] theorem readSupport_historyOf_ambient :
    (AssertionTerm.historyOf (.ambient : AssertionTerm context .view)).readSupport = [.history] := rfl

@[simp] theorem readSupport_provenanceOf_ambient :
    (AssertionTerm.provenanceOf (.ambient : AssertionTerm context .view)).readSupport = [.provenance] := rfl

@[simp] theorem readSupport_compatibleOf_ambient :
    (AssertionTerm.compatibleOf (.ambient : AssertionTerm context .view)).readSupport = [.compatible] := rfl

/-- Inventory: whole-projection regression covers arbitrary names, not a sample list. -/
theorem readSupport_visibleOf_covers_variable (x : Variable sort .observable) :
    (AssertionTerm.visibleOf (.ambient : AssertionTerm context .view)).readSupport.CoversVariable x := by
  refine ⟨.observableValues, by simp [AssertionTerm.readSupport, visibleReadSupport], ?_⟩
  exact Or.inr (Or.inl ⟨rfl, rfl⟩)

theorem readSupport_visibleOf_covers_dataset (name : DatasetId) :
    (AssertionTerm.visibleOf (.ambient : AssertionTerm context .view)).readSupport.CoversDataset name := by
  exact Or.inr (by simp [AssertionTerm.readSupport, visibleReadSupport])

theorem readSupport_hiddenOf_covers_variable (x : Variable sort .invisible) :
    (AssertionTerm.hiddenOf (.ambient : AssertionTerm context .view)).readSupport.CoversVariable x := by
  refine ⟨.hiddenValues, by simp [AssertionTerm.readSupport], ?_⟩
  exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- The old empty-support counterexample, for any rigid ghost world. -/
def wholeVisibleRegression (world : GhostTerm context .world) : Assertion context :=
  .modal (.atom (.equal (.visibleOf .ambient) (.visibleOf (.currentView (.ghost world)))))

theorem wholeVisibleRegression_readSupport (world : GhostTerm context .world) :
    (wholeVisibleRegression world).readSupport = visibleReadSupport := by
  simp [wholeVisibleRegression, Assertion.readSupport, ModalFormula.readSupport,
    AssertionAtom.readSupport, AssertionTerm.readSupport]

theorem wholeVisibleRegression_covers_variable (world : GhostTerm context .world)
    (x : Variable sort .observable) : (wholeVisibleRegression world).readSupport.CoversVariable x := by
  rw [wholeVisibleRegression_readSupport]
  exact readSupport_visibleOf_covers_variable (context := context) x

theorem wholeVisibleRegression_covers_dataset (world : GhostTerm context .world)
    (name : DatasetId) : (wholeVisibleRegression world).readSupport.CoversDataset name := by
  rw [wholeVisibleRegression_readSupport]
  exact readSupport_visibleOf_covers_dataset (context := context) name

/-- The analogous structural-hidden regression consumes the entire hidden carrier. -/
def wholeHiddenRegression (world : GhostTerm context .world) : Assertion context :=
  .modal (.atom (.equal (.hiddenOf .ambient) (.hiddenOf (.currentView (.ghost world)))))

theorem wholeHiddenRegression_readSupport (world : GhostTerm context .world) :
    (wholeHiddenRegression world).readSupport = [.hiddenValues] := by
  simp [wholeHiddenRegression, Assertion.readSupport, ModalFormula.readSupport,
    AssertionAtom.readSupport, AssertionTerm.readSupport]

theorem wholeHiddenRegression_covers_variable (world : GhostTerm context .world)
    (x : Variable sort .invisible) : (wholeHiddenRegression world).readSupport.CoversVariable x := by
  rw [wholeHiddenRegression_readSupport]
  exact readSupport_hiddenOf_covers_variable (context := context) x

/-- Inventory: updates retain the target's pre-state support and the RHS support;
there is no destination-name pseudo-read and no post-state rebasing of the RHS. -/
theorem readSupport_writeValue (target : AssertionTerm context .view)
    (x : Variable sort .observable) (rhs : AssertionTerm context (.value sort)) :
    (AssertionTerm.writeValue target x rhs).readSupport = target.readSupport ++ rhs.readSupport := rfl

theorem readSupport_writeDataset (target : AssertionTerm context .view)
    (name : DatasetId) (rhs : AssertionTerm context .dataset) :
    (AssertionTerm.writeDataset target name rhs).readSupport = target.readSupport ++ rhs.readSupport := rfl

theorem readSupport_addHistory (target : AssertionTerm context .view)
    (history : AssertionTerm context .history) :
    (AssertionTerm.addHistory target history).readSupport = target.readSupport ++ history.readSupport := rfl

/-- Inventory: fixed ghost worlds/traces do not acquire ambient dependencies. -/
theorem readSupport_currentView_ghost (world : GhostTerm context .world) :
    (AssertionTerm.currentView (.ghost world)).readSupport = [] := rfl

theorem readSupport_worldTrace_ghost (world : GhostTerm context .world) :
    (AssertionTerm.worldTrace (.ghost world)).readSupport = [] := rfl

/-- A syntactic fragment for the proved frame theorem. It includes primitive
ambient reads/projections, rigid world/state/trace projections, and reconstructed
views with updates. It deliberately excludes modal formulas, statistical terms,
and general read/projection targets; their support is still conservatively
computed above, but their semantic frame lemmas are not asserted here. -/
inductive StructuralFrameTerm : {sort : TermSort} → AssertionTerm context sort → Prop where
  | ghost (term : GhostTerm context ghostSort) : StructuralFrameTerm (.ghost term)
  | boolean (value : Bool) : StructuralFrameTerm (.boolean value)
  | integer (value : Int) : StructuralFrameTerm (.integer value)
  | rational (value : ℚ) : StructuralFrameTerm (.rational value)
  | ambient : StructuralFrameTerm (.ambient : AssertionTerm context .view)
  | valueRead (x : Variable valueSort visibility) : StructuralFrameTerm (.valueRead .ambient x)
  | datasetRead (name : DatasetId) : StructuralFrameTerm (.datasetRead .ambient name)
  | visible : StructuralFrameTerm (.visibleOf (.ambient : AssertionTerm context .view))
  | hidden : StructuralFrameTerm (.hiddenOf (.ambient : AssertionTerm context .view))
  | history : StructuralFrameTerm (.historyOf (.ambient : AssertionTerm context .view))
  | compatible : StructuralFrameTerm (.compatibleOf (.ambient : AssertionTerm context .view))
  | provenance : StructuralFrameTerm (.provenanceOf (.ambient : AssertionTerm context .view))
  | currentView (world : GhostTerm context .world) : StructuralFrameTerm (.currentView (.ghost world))
  | currentState (world : GhostTerm context .world) : StructuralFrameTerm (.currentState (.ghost world))
  | worldTrace (world : GhostTerm context .world) : StructuralFrameTerm (.worldTrace (.ghost world))
  | traceEmpty : StructuralFrameTerm (.traceEmpty : AssertionTerm context .trace)
  | historyEmpty : StructuralFrameTerm (.historyEmpty : AssertionTerm context .history)
  | provenanceEmpty : StructuralFrameTerm (.provenanceEmpty : AssertionTerm context .provenance)
  | makeView {visible history hidden compatible provenance}
      : StructuralFrameTerm visible → StructuralFrameTerm history → StructuralFrameTerm hidden →
        StructuralFrameTerm compatible → StructuralFrameTerm provenance →
        StructuralFrameTerm (.makeView visible history hidden compatible provenance)
  | writeValue {target rhs} (x : Variable valueSort .observable)
      : StructuralFrameTerm target → StructuralFrameTerm rhs → StructuralFrameTerm (.writeValue target x rhs)
  | writeDataset {target rhs} (name : DatasetId)
      : StructuralFrameTerm target → StructuralFrameTerm rhs → StructuralFrameTerm (.writeDataset target name rhs)
  | addHistory {target history} : StructuralFrameTerm target → StructuralFrameTerm history →
      StructuralFrameTerm (.addHistory target history)
  | historySingleton {data} (test : TestId) : StructuralFrameTerm data →
      StructuralFrameTerm (.historySingleton data test)
  | historyAdd {left right} : StructuralFrameTerm left → StructuralFrameTerm right →
      StructuralFrameTerm (.historyAdd left right)
  | provenanceSingleton {data} (population : PopulationId) : StructuralFrameTerm data →
      StructuralFrameTerm (.provenanceSingleton data population)
  | provenanceAdd {left right} : StructuralFrameTerm left → StructuralFrameTerm right →
      StructuralFrameTerm (.provenanceAdd left right)

noncomputable section

variable {D Command : Type} [mD : MeasurableSpace D]

omit mD in
/-- Inventory: an actual observable write changes a whole visible carrier whenever
the destination did not already contain the written value. -/
theorem writeViewValue_visible_ne (before : SemanticView D)
    (x : Variable sort .observable) (value : Value sort)
    (different : before.visible.memory sort x.id ≠ some value) :
    (writeViewValue before x value).visible ≠ before.visible := by
  intro equal
  have hread := congrArg (fun visible : VisibleState D => visible.memory sort x.id) equal
  have hw : (writeViewValue before x value).visible.memory sort x.id = some value := by
    change ((Memory.assemble before.visible.memory before.hidden).update x (some value)).read x = some value
    exact Memory.read_update_self _ x (some value)
  exact different (hread.symm.trans hw)

/-- Inventory: the concrete old counterexample really changes truth under x := 1
when the fixed world initially has x = 0. Both sides initially denote the same
whole visible state; the ghost world remains rigid after the ambient write. -/
theorem wholeVisibleRegression_zero_to_one (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context)
    (world : GhostTerm context .world) (x : Variable .integer .observable)
    (zero : (semanticView model.dynamics (world.eval interpretation env)).visible.memory .integer x.id = some 0) :
    let before := semanticView model.dynamics (world.eval interpretation env)
    let atom : AssertionAtom context :=
      .equal (.visibleOf .ambient) (.visibleOf (.currentView (.ghost world)))
    atomMeaning interpretation model env before atom ∧
      ¬ atomMeaning interpretation model env (writeViewValue before x 1) atom := by
  dsimp only
  have different : (semanticView model.dynamics (world.eval interpretation env)).visible.memory
      .integer x.id ≠ some (1 : Int) := by
    rw [zero]
    simp
  have changed := writeViewValue_visible_ne
    (semanticView model.dynamics (world.eval interpretation env)) x (1 : Int) different
  constructor
  · exact ⟨_, rfl, rfl⟩
  · rintro ⟨visible, afterEqual, fixedEqual⟩
    exact changed ((Option.some.inj afterEqual).trans (Option.some.inj fixedEqual).symm)

/-- Inventory: semantic framing for exactly the independently specified structural
fragment. The interpretation, model and ghost environment are fixed, and support
agreement concerns actual carrier equality rather than permission flags. -/
theorem evalTerm_structural_frame (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context)
    {term : AssertionTerm context sort} (fragment : StructuralFrameTerm term)
    {left right : SemanticView D} (agreement : SupportAgreement term.readSupport left right) :
    evalTerm interpretation model env left term = evalTerm interpretation model env right term := by
  revert agreement
  induction fragment with
  | ghost term => intro _; rfl
  | boolean value => intro _; rfl
  | integer value => intro _; rfl
  | rational value => intro _; rfl
  | ambient => intro agreement; exact congrArg some (SupportAgreement.view_eq agreement)
  | valueRead x =>
      intro agreement
      have h := agreement (.variable _ _ x) (by simp [AssertionTerm.readSupport])
      change (Memory.assemble left.visible.memory left.hidden).read x =
        (Memory.assemble right.visible.memory right.hidden).read x at h
      exact h
  | datasetRead name =>
      intro agreement
      have h := agreement (.dataset name) (by simp [AssertionTerm.readSupport])
      simpa only [evalTerm, Option.map_some] using congrArg some h
  | visible =>
      intro agreement
      exact congrArg some (SupportAgreement.visible_eq agreement)
  | hidden =>
      intro agreement
      exact congrArg some (agreement .hiddenValues (by simp [AssertionTerm.readSupport]))
  | history =>
      intro agreement
      exact congrArg some (agreement .history (by simp [AssertionTerm.readSupport]))
  | compatible =>
      intro agreement
      exact congrArg some (agreement .compatible (by simp [AssertionTerm.readSupport]))
  | provenance =>
      intro agreement
      exact congrArg some (agreement .provenance (by simp [AssertionTerm.readSupport]))
  | currentView world => intro _; rfl
  | currentState world => intro _; rfl
  | worldTrace world => intro _; rfl
  | traceEmpty => intro _; rfl
  | historyEmpty => intro _; rfl
  | provenanceEmpty => intro _; rfl
  | makeView fv fh fs fc fp iv ih is ic ip =>
      intro agreement
      change SupportAgreement (_ ++ _ ++ _ ++ _ ++ _) left right at agreement
      have h1 := agreement.append_left
      have h2 := h1.append_left
      have h3 := h2.append_left
      simp only [evalTerm, iv h3.append_left, ih h3.append_right,
        is h2.append_right, ic h1.append_right, ip agreement.append_right]
  | writeValue x ft fr it ir =>
      intro agreement
      change SupportAgreement (_ ++ _) left right at agreement
      simp only [evalTerm, it agreement.append_left, ir agreement.append_right]
  | writeDataset name ft fr it ir =>
      intro agreement
      change SupportAgreement (_ ++ _) left right at agreement
      simp only [evalTerm, it agreement.append_left, ir agreement.append_right]
  | addHistory ft fh it ih =>
      intro agreement
      change SupportAgreement (_ ++ _) left right at agreement
      simp only [evalTerm, it agreement.append_left, ih agreement.append_right]
  | historySingleton test fd id =>
      intro agreement
      simp only [evalTerm, id agreement]
  | historyAdd fl fr il ir =>
      intro agreement
      change SupportAgreement (_ ++ _) left right at agreement
      simp only [evalTerm, il agreement.append_left, ir agreement.append_right]
  | provenanceSingleton population fd id =>
      intro agreement
      simp only [evalTerm, id agreement]
  | provenanceAdd fl fr il ir =>
      intro agreement
      change SupportAgreement (_ ++ _) left right at agreement
      simp only [evalTerm, il agreement.append_left, ir agreement.append_right]

/-- Inventory: ghost world and trace evaluations remain fixed even if the ambient
view is an actual write result; no agreement premise is needed. -/
theorem evalTerm_currentView_ghost_fixed (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context)
    (world : GhostTerm context .world) (left right : SemanticView D) :
    evalTerm interpretation model env left (.currentView (.ghost world)) =
      evalTerm interpretation model env right (.currentView (.ghost world)) := rfl

theorem evalTerm_worldTrace_ghost_fixed (interpretation : AssertionInterpretation D Command)
    (model : Model D Command) (env : GhostEnv D Command context)
    (world : GhostTerm context .world) (left right : SemanticView D) :
    evalTerm interpretation model env left (.worldTrace (.ghost world)) =
      evalTerm interpretation model env right (.worldTrace (.ghost world)) := rfl

end
end Lara.BHL
