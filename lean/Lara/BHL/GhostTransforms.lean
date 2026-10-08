import Lara.BHL.Syntax

namespace Lara.BHL

abbrev GhostSubstitution (context target : List GhostSort) :=
  (sort : GhostSort) → BoundGhost context sort → GhostTerm target sort

namespace GhostTerm

def renameGhosts (ρ : GhostRenaming context target) : GhostTerm context sort → GhostTerm target sort
  | .bound index => .bound (ρ _ index)
  | .constant name => .constant name

def substituteGhosts (σ : GhostSubstitution context target) : GhostTerm context sort → GhostTerm target sort
  | .bound index => σ _ index
  | .constant name => .constant name

@[simp] theorem renameGhosts_id (term : GhostTerm context sort) :
    term.renameGhosts GhostRenaming.id = term := by cases term <;> rfl

theorem renameGhosts_comp (ρ : GhostRenaming context target) (τ : GhostRenaming target next)
    (term : GhostTerm context sort) :
    (term.renameGhosts ρ).renameGhosts τ = term.renameGhosts (GhostRenaming.comp ρ τ) := by
  cases term <;> rfl

end GhostTerm

namespace GhostSubstitution

def id : GhostSubstitution context context := fun _ index => .bound index

def ofRenaming (ρ : GhostRenaming context target) : GhostSubstitution context target :=
  fun _ index => .bound (ρ _ index)

def comp (σ : GhostSubstitution context target) (τ : GhostSubstitution target next) :
    GhostSubstitution context next := fun _ index => (σ _ index).substituteGhosts τ

def lift (σ : GhostSubstitution context target) : GhostSubstitution (other :: context) (other :: target)
  | _, .here => .bound .here
  | _, .there index => (σ _ index).renameGhosts GhostRenaming.weaken

@[simp] theorem lift_here (σ : GhostSubstitution context target) :
    lift (other := other) σ other .here = .bound .here := rfl

@[simp] theorem lift_there (σ : GhostSubstitution context target) (index : BoundGhost context sort) :
    lift (other := other) σ sort (.there index) = (σ sort index).renameGhosts GhostRenaming.weaken := rfl

@[simp] theorem lift_id : lift (other := other) (id (context := context)) = id := by
  funext sort index
  cases index <;> rfl

@[simp] theorem lift_ofRenaming (ρ : GhostRenaming context target) :
    lift (other := other) (ofRenaming ρ) = ofRenaming (GhostRenaming.lift ρ) := by
  funext sort index
  cases index <;> rfl

end GhostSubstitution

namespace GhostTerm

@[simp] theorem substituteGhosts_id (term : GhostTerm context sort) :
    term.substituteGhosts GhostSubstitution.id = term := by cases term <;> rfl

theorem substituteGhosts_comp (σ : GhostSubstitution context target)
    (τ : GhostSubstitution target next) (term : GhostTerm context sort) :
    (term.substituteGhosts σ).substituteGhosts τ =
      term.substituteGhosts (GhostSubstitution.comp σ τ) := by cases term <;> rfl

theorem renameGhosts_eq_substituteGhosts (ρ : GhostRenaming context target)
    (term : GhostTerm context sort) :
    term.renameGhosts ρ = term.substituteGhosts (GhostSubstitution.ofRenaming ρ) := by
  cases term <;> rfl

theorem weaken_substitute_lift (σ : GhostSubstitution context target) (term : GhostTerm context sort) :
    (term.renameGhosts (GhostRenaming.weaken (other := other))).substituteGhosts
      (GhostSubstitution.lift σ) =
    (term.substituteGhosts σ).renameGhosts GhostRenaming.weaken := by cases term <;> rfl

end GhostTerm

namespace GhostSubstitution

@[simp] theorem id_comp (σ : GhostSubstitution context target) : comp id σ = σ := rfl

@[simp] theorem comp_id (σ : GhostSubstitution context target) : comp σ id = σ := by
  funext sort index
  exact GhostTerm.substituteGhosts_id (σ sort index)

theorem comp_assoc (σ : GhostSubstitution context target) (τ : GhostSubstitution target next)
    (υ : GhostSubstitution next last) : comp (comp σ τ) υ = comp σ (comp τ υ) := by
  funext sort index
  exact GhostTerm.substituteGhosts_comp τ υ (σ sort index)

theorem lift_comp (σ : GhostSubstitution context target) (τ : GhostSubstitution target next) :
    lift (other := other) (comp σ τ) = comp (lift σ) (lift τ) := by
  funext sort index
  cases index with
  | here => rfl
  | there index => exact (GhostTerm.weaken_substitute_lift τ (σ sort index)).symm

end GhostSubstitution

mutual
def AssertionTerm.renameGhosts (ρ : GhostRenaming context target) :
    AssertionTerm context sort → AssertionTerm target sort
  | .ghost g => .ghost (g.renameGhosts ρ)
  | .boolean v => .boolean v
  | .integer v => .integer v
  | .rational v => .rational v
  | .apply f a => .apply f (ValueArguments.renameGhosts ρ a)
  | .datasetApply f a => .datasetApply f (ValueArguments.renameGhosts ρ a)
  | .ambient => .ambient
  | .currentView w => .currentView (AssertionTerm.renameGhosts ρ w)
  | .currentState w => .currentState (AssertionTerm.renameGhosts ρ w)
  | .worldTrace w => .worldTrace (AssertionTerm.renameGhosts ρ w)
  | .appendWorld w t => .appendWorld (AssertionTerm.renameGhosts ρ w) (AssertionTerm.renameGhosts ρ t)
  | .traceEmpty => .traceEmpty
  | .traceSingleton s => .traceSingleton (AssertionTerm.renameGhosts ρ s)
  | .traceAppend a b => .traceAppend (AssertionTerm.renameGhosts ρ a) (AssertionTerm.renameGhosts ρ b)
  | .traceLength t => .traceLength (AssertionTerm.renameGhosts ρ t)
  | .traceTake t i => .traceTake (AssertionTerm.renameGhosts ρ t) (AssertionTerm.renameGhosts ρ i)
  | .traceIndex t i => .traceIndex (AssertionTerm.renameGhosts ρ t) (AssertionTerm.renameGhosts ρ i)
  | .valueRead v x => .valueRead (AssertionTerm.renameGhosts ρ v) x
  | .datasetRead v n => .datasetRead (AssertionTerm.renameGhosts ρ v) n
  | .visibleOf v => .visibleOf (AssertionTerm.renameGhosts ρ v)
  | .hiddenOf v => .hiddenOf (AssertionTerm.renameGhosts ρ v)
  | .historyOf v => .historyOf (AssertionTerm.renameGhosts ρ v)
  | .provenanceOf v => .provenanceOf (AssertionTerm.renameGhosts ρ v)
  | .compatibleOf v => .compatibleOf (AssertionTerm.renameGhosts ρ v)
  | .makeView v h s c p => .makeView (AssertionTerm.renameGhosts ρ v) (AssertionTerm.renameGhosts ρ h) (AssertionTerm.renameGhosts ρ s) (AssertionTerm.renameGhosts ρ c) (AssertionTerm.renameGhosts ρ p)
  | .writeValue v x a => .writeValue (AssertionTerm.renameGhosts ρ v) x (AssertionTerm.renameGhosts ρ a)
  | .writeDataset v n d => .writeDataset (AssertionTerm.renameGhosts ρ v) n (AssertionTerm.renameGhosts ρ d)
  | .addHistory v h => .addHistory (AssertionTerm.renameGhosts ρ v) (AssertionTerm.renameGhosts ρ h)
  | .historyEmpty => .historyEmpty
  | .historySingleton d t => .historySingleton (AssertionTerm.renameGhosts ρ d) t
  | .historyAdd a b => .historyAdd (AssertionTerm.renameGhosts ρ a) (AssertionTerm.renameGhosts ρ b)
  | .historyCount h d t => .historyCount (AssertionTerm.renameGhosts ρ h) (AssertionTerm.renameGhosts ρ d) t
  | .provenanceEmpty => .provenanceEmpty
  | .provenanceSingleton d p => .provenanceSingleton (AssertionTerm.renameGhosts ρ d) p
  | .provenanceAdd a b => .provenanceAdd (AssertionTerm.renameGhosts ρ a) (AssertionTerm.renameGhosts ρ b)
  | .pvalue t => .pvalue (TestExpression.renameGhosts ρ t)
  | .realAdd a b => .realAdd (AssertionTerm.renameGhosts ρ a) (AssertionTerm.renameGhosts ρ b)
  | .realMin a b => .realMin (AssertionTerm.renameGhosts ρ a) (AssertionTerm.renameGhosts ρ b)
  | .intAdd a b => .intAdd (AssertionTerm.renameGhosts ρ a) (AssertionTerm.renameGhosts ρ b)
  | .intSub a b => .intSub (AssertionTerm.renameGhosts ρ a) (AssertionTerm.renameGhosts ρ b)
  | .intLess a b => .intLess (AssertionTerm.renameGhosts ρ a) (AssertionTerm.renameGhosts ρ b)
  | .booleanNot a => .booleanNot (AssertionTerm.renameGhosts ρ a)
def ValueArguments.renameGhosts (ρ : GhostRenaming context target) :
    ValueArguments context inputs → ValueArguments target inputs
  | .nil => .nil
  | .cons a r => .cons (AssertionTerm.renameGhosts ρ a) (ValueArguments.renameGhosts ρ r)
def TestExpression.renameGhosts (ρ : GhostRenaming context target) :
    TestExpression context → TestExpression target
  | .leaf h d t p => .leaf h (AssertionTerm.renameGhosts ρ d) t p
  | .disj n a b => .disj n (TestExpression.renameGhosts ρ a) (TestExpression.renameGhosts ρ b)
  | .conj n a b => .conj n (TestExpression.renameGhosts ρ a) (TestExpression.renameGhosts ρ b)
end

def AssertionAtom.renameGhosts (ρ : GhostRenaming context target) :
    AssertionAtom context → AssertionAtom target
  | .rigid p a => .rigid p (ValueArguments.renameGhosts ρ a)
  | .equal a b => .equal (AssertionTerm.renameGhosts ρ a) (AssertionTerm.renameGhosts ρ b)
  | .defined a => .defined (AssertionTerm.renameGhosts ρ a)
  | .realCompare c a b => .realCompare c (AssertionTerm.renameGhosts ρ a) (AssertionTerm.renameGhosts ρ b)
  | .intCompare c a b => .intCompare c (AssertionTerm.renameGhosts ρ a) (AssertionTerm.renameGhosts ρ b)
  | .hypothesis h a => .hypothesis h (AssertionTerm.renameGhosts ρ a)
  | .sampling d p a => .sampling (AssertionTerm.renameGhosts ρ d) p (AssertionTerm.renameGhosts ρ a)
  | .requirements e v => .requirements (TestExpression.renameGhosts ρ e) (AssertionTerm.renameGhosts ρ v)
  | .admitted w => .admitted (AssertionTerm.renameGhosts ρ w)
  | .action c s => .action c (AssertionTerm.renameGhosts ρ s)

def ModalFormula.renameGhosts (ρ : GhostRenaming context target) :
    ModalFormula context → ModalFormula target
  | .atom a => .atom (AssertionAtom.renameGhosts ρ a)
  | .neg a => .neg (ModalFormula.renameGhosts ρ a)
  | .conj a b => .conj (ModalFormula.renameGhosts ρ a) (ModalFormula.renameGhosts ρ b)
  | .knows a => .knows (ModalFormula.renameGhosts ρ a)
  | .atWorld w a => .atWorld (AssertionTerm.renameGhosts ρ w) (ModalFormula.renameGhosts ρ a)
  | .atView v a => .atView (AssertionTerm.renameGhosts ρ v) (ModalFormula.renameGhosts ρ a)

def Assertion.renameGhosts (ρ : GhostRenaming context target) :
    Assertion context → Assertion target
  | .modal a => .modal (ModalFormula.renameGhosts ρ a)
  | .neg a => .neg (Assertion.renameGhosts ρ a)
  | .conj a b => .conj (Assertion.renameGhosts ρ a) (Assertion.renameGhosts ρ b)
  | .all s a => .all s (Assertion.renameGhosts (GhostRenaming.lift ρ) a)
  | .atWorld w a => .atWorld (AssertionTerm.renameGhosts ρ w) (Assertion.renameGhosts ρ a)
  | .atView v a => .atView (AssertionTerm.renameGhosts ρ v) (Assertion.renameGhosts ρ a)

mutual
def AssertionTerm.substituteGhosts (σ : GhostSubstitution context target) :
    AssertionTerm context sort → AssertionTerm target sort
  | .ghost g => .ghost (g.substituteGhosts σ)
  | .boolean v => .boolean v
  | .integer v => .integer v
  | .rational v => .rational v
  | .apply f a => .apply f (ValueArguments.substituteGhosts σ a)
  | .datasetApply f a => .datasetApply f (ValueArguments.substituteGhosts σ a)
  | .ambient => .ambient
  | .currentView w => .currentView (AssertionTerm.substituteGhosts σ w)
  | .currentState w => .currentState (AssertionTerm.substituteGhosts σ w)
  | .worldTrace w => .worldTrace (AssertionTerm.substituteGhosts σ w)
  | .appendWorld w t => .appendWorld (AssertionTerm.substituteGhosts σ w) (AssertionTerm.substituteGhosts σ t)
  | .traceEmpty => .traceEmpty
  | .traceSingleton s => .traceSingleton (AssertionTerm.substituteGhosts σ s)
  | .traceAppend a b => .traceAppend (AssertionTerm.substituteGhosts σ a) (AssertionTerm.substituteGhosts σ b)
  | .traceLength t => .traceLength (AssertionTerm.substituteGhosts σ t)
  | .traceTake t i => .traceTake (AssertionTerm.substituteGhosts σ t) (AssertionTerm.substituteGhosts σ i)
  | .traceIndex t i => .traceIndex (AssertionTerm.substituteGhosts σ t) (AssertionTerm.substituteGhosts σ i)
  | .valueRead v x => .valueRead (AssertionTerm.substituteGhosts σ v) x
  | .datasetRead v n => .datasetRead (AssertionTerm.substituteGhosts σ v) n
  | .visibleOf v => .visibleOf (AssertionTerm.substituteGhosts σ v)
  | .hiddenOf v => .hiddenOf (AssertionTerm.substituteGhosts σ v)
  | .historyOf v => .historyOf (AssertionTerm.substituteGhosts σ v)
  | .provenanceOf v => .provenanceOf (AssertionTerm.substituteGhosts σ v)
  | .compatibleOf v => .compatibleOf (AssertionTerm.substituteGhosts σ v)
  | .makeView v h s c p => .makeView (AssertionTerm.substituteGhosts σ v) (AssertionTerm.substituteGhosts σ h) (AssertionTerm.substituteGhosts σ s) (AssertionTerm.substituteGhosts σ c) (AssertionTerm.substituteGhosts σ p)
  | .writeValue v x a => .writeValue (AssertionTerm.substituteGhosts σ v) x (AssertionTerm.substituteGhosts σ a)
  | .writeDataset v n d => .writeDataset (AssertionTerm.substituteGhosts σ v) n (AssertionTerm.substituteGhosts σ d)
  | .addHistory v h => .addHistory (AssertionTerm.substituteGhosts σ v) (AssertionTerm.substituteGhosts σ h)
  | .historyEmpty => .historyEmpty
  | .historySingleton d t => .historySingleton (AssertionTerm.substituteGhosts σ d) t
  | .historyAdd a b => .historyAdd (AssertionTerm.substituteGhosts σ a) (AssertionTerm.substituteGhosts σ b)
  | .historyCount h d t => .historyCount (AssertionTerm.substituteGhosts σ h) (AssertionTerm.substituteGhosts σ d) t
  | .provenanceEmpty => .provenanceEmpty
  | .provenanceSingleton d p => .provenanceSingleton (AssertionTerm.substituteGhosts σ d) p
  | .provenanceAdd a b => .provenanceAdd (AssertionTerm.substituteGhosts σ a) (AssertionTerm.substituteGhosts σ b)
  | .pvalue t => .pvalue (TestExpression.substituteGhosts σ t)
  | .realAdd a b => .realAdd (AssertionTerm.substituteGhosts σ a) (AssertionTerm.substituteGhosts σ b)
  | .realMin a b => .realMin (AssertionTerm.substituteGhosts σ a) (AssertionTerm.substituteGhosts σ b)
  | .intAdd a b => .intAdd (AssertionTerm.substituteGhosts σ a) (AssertionTerm.substituteGhosts σ b)
  | .intSub a b => .intSub (AssertionTerm.substituteGhosts σ a) (AssertionTerm.substituteGhosts σ b)
  | .intLess a b => .intLess (AssertionTerm.substituteGhosts σ a) (AssertionTerm.substituteGhosts σ b)
  | .booleanNot a => .booleanNot (AssertionTerm.substituteGhosts σ a)
def ValueArguments.substituteGhosts (σ : GhostSubstitution context target) :
    ValueArguments context inputs → ValueArguments target inputs
  | .nil => .nil
  | .cons a r => .cons (AssertionTerm.substituteGhosts σ a) (ValueArguments.substituteGhosts σ r)
def TestExpression.substituteGhosts (σ : GhostSubstitution context target) :
    TestExpression context → TestExpression target
  | .leaf h d t p => .leaf h (AssertionTerm.substituteGhosts σ d) t p
  | .disj n a b => .disj n (TestExpression.substituteGhosts σ a) (TestExpression.substituteGhosts σ b)
  | .conj n a b => .conj n (TestExpression.substituteGhosts σ a) (TestExpression.substituteGhosts σ b)
end

def AssertionAtom.substituteGhosts (σ : GhostSubstitution context target) :
    AssertionAtom context → AssertionAtom target
  | .rigid p a => .rigid p (ValueArguments.substituteGhosts σ a)
  | .equal a b => .equal (AssertionTerm.substituteGhosts σ a) (AssertionTerm.substituteGhosts σ b)
  | .defined a => .defined (AssertionTerm.substituteGhosts σ a)
  | .realCompare c a b => .realCompare c (AssertionTerm.substituteGhosts σ a) (AssertionTerm.substituteGhosts σ b)
  | .intCompare c a b => .intCompare c (AssertionTerm.substituteGhosts σ a) (AssertionTerm.substituteGhosts σ b)
  | .hypothesis h a => .hypothesis h (AssertionTerm.substituteGhosts σ a)
  | .sampling d p a => .sampling (AssertionTerm.substituteGhosts σ d) p (AssertionTerm.substituteGhosts σ a)
  | .requirements e v => .requirements (TestExpression.substituteGhosts σ e) (AssertionTerm.substituteGhosts σ v)
  | .admitted w => .admitted (AssertionTerm.substituteGhosts σ w)
  | .action c s => .action c (AssertionTerm.substituteGhosts σ s)

def ModalFormula.substituteGhosts (σ : GhostSubstitution context target) :
    ModalFormula context → ModalFormula target
  | .atom a => .atom (AssertionAtom.substituteGhosts σ a)
  | .neg a => .neg (ModalFormula.substituteGhosts σ a)
  | .conj a b => .conj (ModalFormula.substituteGhosts σ a) (ModalFormula.substituteGhosts σ b)
  | .knows a => .knows (ModalFormula.substituteGhosts σ a)
  | .atWorld w a => .atWorld (AssertionTerm.substituteGhosts σ w) (ModalFormula.substituteGhosts σ a)
  | .atView v a => .atView (AssertionTerm.substituteGhosts σ v) (ModalFormula.substituteGhosts σ a)

def Assertion.substituteGhosts (σ : GhostSubstitution context target) :
    Assertion context → Assertion target
  | .modal a => .modal (ModalFormula.substituteGhosts σ a)
  | .neg a => .neg (Assertion.substituteGhosts σ a)
  | .conj a b => .conj (Assertion.substituteGhosts σ a) (Assertion.substituteGhosts σ b)
  | .all s a => .all s (Assertion.substituteGhosts (GhostSubstitution.lift σ) a)
  | .atWorld w a => .atWorld (AssertionTerm.substituteGhosts σ w) (Assertion.substituteGhosts σ a)
  | .atView v a => .atView (AssertionTerm.substituteGhosts σ v) (Assertion.substituteGhosts σ a)

mutual
theorem AssertionTerm.renameGhosts_id :
    (term : AssertionTerm context sort) → AssertionTerm.renameGhosts GhostRenaming.id term = term
  | .ghost g => by
      simp only [AssertionTerm.renameGhosts, GhostTerm.renameGhosts_id g]
  | .boolean v => by
      simp only [AssertionTerm.renameGhosts]
  | .integer v => by
      simp only [AssertionTerm.renameGhosts]
  | .rational v => by
      simp only [AssertionTerm.renameGhosts]
  | .apply f a => by
      simp only [AssertionTerm.renameGhosts, ValueArguments.renameGhosts_id a]
  | .datasetApply f a => by
      simp only [AssertionTerm.renameGhosts, ValueArguments.renameGhosts_id a]
  | .ambient => by
      simp only [AssertionTerm.renameGhosts]
  | .currentView w => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id w]
  | .currentState w => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id w]
  | .worldTrace w => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id w]
  | .appendWorld w t => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id w, AssertionTerm.renameGhosts_id t]
  | .traceEmpty => by
      simp only [AssertionTerm.renameGhosts]
  | .traceSingleton s => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id s]
  | .traceAppend a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id a, AssertionTerm.renameGhosts_id b]
  | .traceLength t => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id t]
  | .traceTake t i => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id t, AssertionTerm.renameGhosts_id i]
  | .traceIndex t i => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id t, AssertionTerm.renameGhosts_id i]
  | .valueRead v x => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id v]
  | .datasetRead v n => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id v]
  | .visibleOf v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id v]
  | .hiddenOf v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id v]
  | .historyOf v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id v]
  | .provenanceOf v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id v]
  | .compatibleOf v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id v]
  | .makeView v h s c p => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id v, AssertionTerm.renameGhosts_id h, AssertionTerm.renameGhosts_id s, AssertionTerm.renameGhosts_id c, AssertionTerm.renameGhosts_id p]
  | .writeValue v x a => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id v, AssertionTerm.renameGhosts_id a]
  | .writeDataset v n d => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id v, AssertionTerm.renameGhosts_id d]
  | .addHistory v h => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id v, AssertionTerm.renameGhosts_id h]
  | .historyEmpty => by
      simp only [AssertionTerm.renameGhosts]
  | .historySingleton d t => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id d]
  | .historyAdd a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id a, AssertionTerm.renameGhosts_id b]
  | .historyCount h d t => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id h, AssertionTerm.renameGhosts_id d]
  | .provenanceEmpty => by
      simp only [AssertionTerm.renameGhosts]
  | .provenanceSingleton d p => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id d]
  | .provenanceAdd a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id a, AssertionTerm.renameGhosts_id b]
  | .pvalue t => by
      simp only [AssertionTerm.renameGhosts, TestExpression.renameGhosts_id t]
  | .realAdd a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id a, AssertionTerm.renameGhosts_id b]
  | .realMin a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id a, AssertionTerm.renameGhosts_id b]
  | .intAdd a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id a, AssertionTerm.renameGhosts_id b]
  | .intSub a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id a, AssertionTerm.renameGhosts_id b]
  | .intLess a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id a, AssertionTerm.renameGhosts_id b]
  | .booleanNot a => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_id a]
theorem ValueArguments.renameGhosts_id :
    (term : ValueArguments context inputs) → ValueArguments.renameGhosts GhostRenaming.id term = term
  | .nil => by
      simp only [ValueArguments.renameGhosts]
  | .cons a r => by
      simp only [ValueArguments.renameGhosts, AssertionTerm.renameGhosts_id a, ValueArguments.renameGhosts_id r]
theorem TestExpression.renameGhosts_id :
    (term : TestExpression context) → TestExpression.renameGhosts GhostRenaming.id term = term
  | .leaf h d t p => by
      simp only [TestExpression.renameGhosts, AssertionTerm.renameGhosts_id d]
  | .disj n a b => by
      simp only [TestExpression.renameGhosts, TestExpression.renameGhosts_id a, TestExpression.renameGhosts_id b]
  | .conj n a b => by
      simp only [TestExpression.renameGhosts, TestExpression.renameGhosts_id a, TestExpression.renameGhosts_id b]
end

theorem AssertionAtom.renameGhosts_id :
    (term : AssertionAtom context) → AssertionAtom.renameGhosts GhostRenaming.id term = term
  | .rigid p a => by
      simp only [AssertionAtom.renameGhosts, ValueArguments.renameGhosts_id a]
  | .equal a b => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_id a, AssertionTerm.renameGhosts_id b]
  | .defined a => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_id a]
  | .realCompare c a b => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_id a, AssertionTerm.renameGhosts_id b]
  | .intCompare c a b => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_id a, AssertionTerm.renameGhosts_id b]
  | .hypothesis h a => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_id a]
  | .sampling d p a => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_id d, AssertionTerm.renameGhosts_id a]
  | .requirements e v => by
      simp only [AssertionAtom.renameGhosts, TestExpression.renameGhosts_id e, AssertionTerm.renameGhosts_id v]
  | .admitted w => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_id w]
  | .action c s => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_id s]

theorem ModalFormula.renameGhosts_id :
    (term : ModalFormula context) → ModalFormula.renameGhosts GhostRenaming.id term = term
  | .atom a => by
      simp only [ModalFormula.renameGhosts, AssertionAtom.renameGhosts_id a]
  | .neg a => by
      simp only [ModalFormula.renameGhosts, ModalFormula.renameGhosts_id a]
  | .conj a b => by
      simp only [ModalFormula.renameGhosts, ModalFormula.renameGhosts_id a, ModalFormula.renameGhosts_id b]
  | .knows a => by
      simp only [ModalFormula.renameGhosts, ModalFormula.renameGhosts_id a]
  | .atWorld w a => by
      simp only [ModalFormula.renameGhosts, AssertionTerm.renameGhosts_id w, ModalFormula.renameGhosts_id a]
  | .atView v a => by
      simp only [ModalFormula.renameGhosts, AssertionTerm.renameGhosts_id v, ModalFormula.renameGhosts_id a]

theorem Assertion.renameGhosts_id :
    (term : Assertion context) → Assertion.renameGhosts GhostRenaming.id term = term
  | .modal a => by
      simp only [Assertion.renameGhosts, ModalFormula.renameGhosts_id a]
  | .neg a => by
      simp only [Assertion.renameGhosts, Assertion.renameGhosts_id a]
  | .conj a b => by
      simp only [Assertion.renameGhosts, Assertion.renameGhosts_id a, Assertion.renameGhosts_id b]
  | .all s a => by
      simp only [Assertion.renameGhosts, Assertion.renameGhosts_id a, GhostRenaming.lift_id]
  | .atWorld w a => by
      simp only [Assertion.renameGhosts, AssertionTerm.renameGhosts_id w, Assertion.renameGhosts_id a]
  | .atView v a => by
      simp only [Assertion.renameGhosts, AssertionTerm.renameGhosts_id v, Assertion.renameGhosts_id a]

mutual
theorem AssertionTerm.renameGhosts_comp (σ : GhostRenaming context target) (τ : GhostRenaming target next) :
    (term : AssertionTerm context sort) → AssertionTerm.renameGhosts τ (AssertionTerm.renameGhosts σ term) = AssertionTerm.renameGhosts (GhostRenaming.comp σ τ) term
  | .ghost g => by
      simp only [AssertionTerm.renameGhosts, GhostTerm.renameGhosts_comp σ τ g]
  | .boolean v => by
      simp only [AssertionTerm.renameGhosts]
  | .integer v => by
      simp only [AssertionTerm.renameGhosts]
  | .rational v => by
      simp only [AssertionTerm.renameGhosts]
  | .apply f a => by
      simp only [AssertionTerm.renameGhosts, ValueArguments.renameGhosts_comp σ τ a]
  | .datasetApply f a => by
      simp only [AssertionTerm.renameGhosts, ValueArguments.renameGhosts_comp σ τ a]
  | .ambient => by
      simp only [AssertionTerm.renameGhosts]
  | .currentView w => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ w]
  | .currentState w => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ w]
  | .worldTrace w => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ w]
  | .appendWorld w t => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ w, AssertionTerm.renameGhosts_comp σ τ t]
  | .traceEmpty => by
      simp only [AssertionTerm.renameGhosts]
  | .traceSingleton s => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ s]
  | .traceAppend a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ a, AssertionTerm.renameGhosts_comp σ τ b]
  | .traceLength t => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ t]
  | .traceTake t i => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ t, AssertionTerm.renameGhosts_comp σ τ i]
  | .traceIndex t i => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ t, AssertionTerm.renameGhosts_comp σ τ i]
  | .valueRead v x => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ v]
  | .datasetRead v n => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ v]
  | .visibleOf v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ v]
  | .hiddenOf v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ v]
  | .historyOf v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ v]
  | .provenanceOf v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ v]
  | .compatibleOf v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ v]
  | .makeView v h s c p => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ v, AssertionTerm.renameGhosts_comp σ τ h, AssertionTerm.renameGhosts_comp σ τ s, AssertionTerm.renameGhosts_comp σ τ c, AssertionTerm.renameGhosts_comp σ τ p]
  | .writeValue v x a => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ v, AssertionTerm.renameGhosts_comp σ τ a]
  | .writeDataset v n d => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ v, AssertionTerm.renameGhosts_comp σ τ d]
  | .addHistory v h => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ v, AssertionTerm.renameGhosts_comp σ τ h]
  | .historyEmpty => by
      simp only [AssertionTerm.renameGhosts]
  | .historySingleton d t => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ d]
  | .historyAdd a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ a, AssertionTerm.renameGhosts_comp σ τ b]
  | .historyCount h d t => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ h, AssertionTerm.renameGhosts_comp σ τ d]
  | .provenanceEmpty => by
      simp only [AssertionTerm.renameGhosts]
  | .provenanceSingleton d p => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ d]
  | .provenanceAdd a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ a, AssertionTerm.renameGhosts_comp σ τ b]
  | .pvalue t => by
      simp only [AssertionTerm.renameGhosts, TestExpression.renameGhosts_comp σ τ t]
  | .realAdd a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ a, AssertionTerm.renameGhosts_comp σ τ b]
  | .realMin a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ a, AssertionTerm.renameGhosts_comp σ τ b]
  | .intAdd a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ a, AssertionTerm.renameGhosts_comp σ τ b]
  | .intSub a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ a, AssertionTerm.renameGhosts_comp σ τ b]
  | .intLess a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ a, AssertionTerm.renameGhosts_comp σ τ b]
  | .booleanNot a => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.renameGhosts_comp σ τ a]
theorem ValueArguments.renameGhosts_comp (σ : GhostRenaming context target) (τ : GhostRenaming target next) :
    (term : ValueArguments context inputs) → ValueArguments.renameGhosts τ (ValueArguments.renameGhosts σ term) = ValueArguments.renameGhosts (GhostRenaming.comp σ τ) term
  | .nil => by
      simp only [ValueArguments.renameGhosts]
  | .cons a r => by
      simp only [ValueArguments.renameGhosts, AssertionTerm.renameGhosts_comp σ τ a, ValueArguments.renameGhosts_comp σ τ r]
theorem TestExpression.renameGhosts_comp (σ : GhostRenaming context target) (τ : GhostRenaming target next) :
    (term : TestExpression context) → TestExpression.renameGhosts τ (TestExpression.renameGhosts σ term) = TestExpression.renameGhosts (GhostRenaming.comp σ τ) term
  | .leaf h d t p => by
      simp only [TestExpression.renameGhosts, AssertionTerm.renameGhosts_comp σ τ d]
  | .disj n a b => by
      simp only [TestExpression.renameGhosts, TestExpression.renameGhosts_comp σ τ a, TestExpression.renameGhosts_comp σ τ b]
  | .conj n a b => by
      simp only [TestExpression.renameGhosts, TestExpression.renameGhosts_comp σ τ a, TestExpression.renameGhosts_comp σ τ b]
end

theorem AssertionAtom.renameGhosts_comp (σ : GhostRenaming context target) (τ : GhostRenaming target next) :
    (term : AssertionAtom context) → AssertionAtom.renameGhosts τ (AssertionAtom.renameGhosts σ term) = AssertionAtom.renameGhosts (GhostRenaming.comp σ τ) term
  | .rigid p a => by
      simp only [AssertionAtom.renameGhosts, ValueArguments.renameGhosts_comp σ τ a]
  | .equal a b => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_comp σ τ a, AssertionTerm.renameGhosts_comp σ τ b]
  | .defined a => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_comp σ τ a]
  | .realCompare c a b => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_comp σ τ a, AssertionTerm.renameGhosts_comp σ τ b]
  | .intCompare c a b => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_comp σ τ a, AssertionTerm.renameGhosts_comp σ τ b]
  | .hypothesis h a => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_comp σ τ a]
  | .sampling d p a => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_comp σ τ d, AssertionTerm.renameGhosts_comp σ τ a]
  | .requirements e v => by
      simp only [AssertionAtom.renameGhosts, TestExpression.renameGhosts_comp σ τ e, AssertionTerm.renameGhosts_comp σ τ v]
  | .admitted w => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_comp σ τ w]
  | .action c s => by
      simp only [AssertionAtom.renameGhosts, AssertionTerm.renameGhosts_comp σ τ s]

theorem ModalFormula.renameGhosts_comp (σ : GhostRenaming context target) (τ : GhostRenaming target next) :
    (term : ModalFormula context) → ModalFormula.renameGhosts τ (ModalFormula.renameGhosts σ term) = ModalFormula.renameGhosts (GhostRenaming.comp σ τ) term
  | .atom a => by
      simp only [ModalFormula.renameGhosts, AssertionAtom.renameGhosts_comp σ τ a]
  | .neg a => by
      simp only [ModalFormula.renameGhosts, ModalFormula.renameGhosts_comp σ τ a]
  | .conj a b => by
      simp only [ModalFormula.renameGhosts, ModalFormula.renameGhosts_comp σ τ a, ModalFormula.renameGhosts_comp σ τ b]
  | .knows a => by
      simp only [ModalFormula.renameGhosts, ModalFormula.renameGhosts_comp σ τ a]
  | .atWorld w a => by
      simp only [ModalFormula.renameGhosts, AssertionTerm.renameGhosts_comp σ τ w, ModalFormula.renameGhosts_comp σ τ a]
  | .atView v a => by
      simp only [ModalFormula.renameGhosts, AssertionTerm.renameGhosts_comp σ τ v, ModalFormula.renameGhosts_comp σ τ a]

theorem Assertion.renameGhosts_comp (σ : GhostRenaming context target) (τ : GhostRenaming target next) :
    (term : Assertion context) → Assertion.renameGhosts τ (Assertion.renameGhosts σ term) = Assertion.renameGhosts (GhostRenaming.comp σ τ) term
  | .modal a => by
      simp only [Assertion.renameGhosts, ModalFormula.renameGhosts_comp σ τ a]
  | .neg a => by
      simp only [Assertion.renameGhosts, Assertion.renameGhosts_comp σ τ a]
  | .conj a b => by
      simp only [Assertion.renameGhosts, Assertion.renameGhosts_comp σ τ a, Assertion.renameGhosts_comp σ τ b]
  | .all s a => by
      simp only [Assertion.renameGhosts, Assertion.renameGhosts_comp (GhostRenaming.lift σ) (GhostRenaming.lift τ) a, GhostRenaming.lift_comp]
  | .atWorld w a => by
      simp only [Assertion.renameGhosts, AssertionTerm.renameGhosts_comp σ τ w, Assertion.renameGhosts_comp σ τ a]
  | .atView v a => by
      simp only [Assertion.renameGhosts, AssertionTerm.renameGhosts_comp σ τ v, Assertion.renameGhosts_comp σ τ a]

mutual
theorem AssertionTerm.substituteGhosts_id :
    (term : AssertionTerm context sort) → AssertionTerm.substituteGhosts GhostSubstitution.id term = term
  | .ghost g => by
      simp only [AssertionTerm.substituteGhosts, GhostTerm.substituteGhosts_id g]
  | .boolean v => by
      simp only [AssertionTerm.substituteGhosts]
  | .integer v => by
      simp only [AssertionTerm.substituteGhosts]
  | .rational v => by
      simp only [AssertionTerm.substituteGhosts]
  | .apply f a => by
      simp only [AssertionTerm.substituteGhosts, ValueArguments.substituteGhosts_id a]
  | .datasetApply f a => by
      simp only [AssertionTerm.substituteGhosts, ValueArguments.substituteGhosts_id a]
  | .ambient => by
      simp only [AssertionTerm.substituteGhosts]
  | .currentView w => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id w]
  | .currentState w => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id w]
  | .worldTrace w => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id w]
  | .appendWorld w t => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id w, AssertionTerm.substituteGhosts_id t]
  | .traceEmpty => by
      simp only [AssertionTerm.substituteGhosts]
  | .traceSingleton s => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id s]
  | .traceAppend a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id a, AssertionTerm.substituteGhosts_id b]
  | .traceLength t => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id t]
  | .traceTake t i => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id t, AssertionTerm.substituteGhosts_id i]
  | .traceIndex t i => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id t, AssertionTerm.substituteGhosts_id i]
  | .valueRead v x => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id v]
  | .datasetRead v n => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id v]
  | .visibleOf v => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id v]
  | .hiddenOf v => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id v]
  | .historyOf v => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id v]
  | .provenanceOf v => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id v]
  | .compatibleOf v => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id v]
  | .makeView v h s c p => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id v, AssertionTerm.substituteGhosts_id h, AssertionTerm.substituteGhosts_id s, AssertionTerm.substituteGhosts_id c, AssertionTerm.substituteGhosts_id p]
  | .writeValue v x a => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id v, AssertionTerm.substituteGhosts_id a]
  | .writeDataset v n d => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id v, AssertionTerm.substituteGhosts_id d]
  | .addHistory v h => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id v, AssertionTerm.substituteGhosts_id h]
  | .historyEmpty => by
      simp only [AssertionTerm.substituteGhosts]
  | .historySingleton d t => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id d]
  | .historyAdd a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id a, AssertionTerm.substituteGhosts_id b]
  | .historyCount h d t => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id h, AssertionTerm.substituteGhosts_id d]
  | .provenanceEmpty => by
      simp only [AssertionTerm.substituteGhosts]
  | .provenanceSingleton d p => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id d]
  | .provenanceAdd a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id a, AssertionTerm.substituteGhosts_id b]
  | .pvalue t => by
      simp only [AssertionTerm.substituteGhosts, TestExpression.substituteGhosts_id t]
  | .realAdd a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id a, AssertionTerm.substituteGhosts_id b]
  | .realMin a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id a, AssertionTerm.substituteGhosts_id b]
  | .intAdd a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id a, AssertionTerm.substituteGhosts_id b]
  | .intSub a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id a, AssertionTerm.substituteGhosts_id b]
  | .intLess a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id a, AssertionTerm.substituteGhosts_id b]
  | .booleanNot a => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_id a]
theorem ValueArguments.substituteGhosts_id :
    (term : ValueArguments context inputs) → ValueArguments.substituteGhosts GhostSubstitution.id term = term
  | .nil => by
      simp only [ValueArguments.substituteGhosts]
  | .cons a r => by
      simp only [ValueArguments.substituteGhosts, AssertionTerm.substituteGhosts_id a, ValueArguments.substituteGhosts_id r]
theorem TestExpression.substituteGhosts_id :
    (term : TestExpression context) → TestExpression.substituteGhosts GhostSubstitution.id term = term
  | .leaf h d t p => by
      simp only [TestExpression.substituteGhosts, AssertionTerm.substituteGhosts_id d]
  | .disj n a b => by
      simp only [TestExpression.substituteGhosts, TestExpression.substituteGhosts_id a, TestExpression.substituteGhosts_id b]
  | .conj n a b => by
      simp only [TestExpression.substituteGhosts, TestExpression.substituteGhosts_id a, TestExpression.substituteGhosts_id b]
end

theorem AssertionAtom.substituteGhosts_id :
    (term : AssertionAtom context) → AssertionAtom.substituteGhosts GhostSubstitution.id term = term
  | .rigid p a => by
      simp only [AssertionAtom.substituteGhosts, ValueArguments.substituteGhosts_id a]
  | .equal a b => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_id a, AssertionTerm.substituteGhosts_id b]
  | .defined a => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_id a]
  | .realCompare c a b => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_id a, AssertionTerm.substituteGhosts_id b]
  | .intCompare c a b => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_id a, AssertionTerm.substituteGhosts_id b]
  | .hypothesis h a => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_id a]
  | .sampling d p a => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_id d, AssertionTerm.substituteGhosts_id a]
  | .requirements e v => by
      simp only [AssertionAtom.substituteGhosts, TestExpression.substituteGhosts_id e, AssertionTerm.substituteGhosts_id v]
  | .admitted w => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_id w]
  | .action c s => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_id s]

theorem ModalFormula.substituteGhosts_id :
    (term : ModalFormula context) → ModalFormula.substituteGhosts GhostSubstitution.id term = term
  | .atom a => by
      simp only [ModalFormula.substituteGhosts, AssertionAtom.substituteGhosts_id a]
  | .neg a => by
      simp only [ModalFormula.substituteGhosts, ModalFormula.substituteGhosts_id a]
  | .conj a b => by
      simp only [ModalFormula.substituteGhosts, ModalFormula.substituteGhosts_id a, ModalFormula.substituteGhosts_id b]
  | .knows a => by
      simp only [ModalFormula.substituteGhosts, ModalFormula.substituteGhosts_id a]
  | .atWorld w a => by
      simp only [ModalFormula.substituteGhosts, AssertionTerm.substituteGhosts_id w, ModalFormula.substituteGhosts_id a]
  | .atView v a => by
      simp only [ModalFormula.substituteGhosts, AssertionTerm.substituteGhosts_id v, ModalFormula.substituteGhosts_id a]

theorem Assertion.substituteGhosts_id :
    (term : Assertion context) → Assertion.substituteGhosts GhostSubstitution.id term = term
  | .modal a => by
      simp only [Assertion.substituteGhosts, ModalFormula.substituteGhosts_id a]
  | .neg a => by
      simp only [Assertion.substituteGhosts, Assertion.substituteGhosts_id a]
  | .conj a b => by
      simp only [Assertion.substituteGhosts, Assertion.substituteGhosts_id a, Assertion.substituteGhosts_id b]
  | .all s a => by
      simp only [Assertion.substituteGhosts, Assertion.substituteGhosts_id a, GhostSubstitution.lift_id]
  | .atWorld w a => by
      simp only [Assertion.substituteGhosts, AssertionTerm.substituteGhosts_id w, Assertion.substituteGhosts_id a]
  | .atView v a => by
      simp only [Assertion.substituteGhosts, AssertionTerm.substituteGhosts_id v, Assertion.substituteGhosts_id a]

mutual
theorem AssertionTerm.substituteGhosts_comp (σ : GhostSubstitution context target) (τ : GhostSubstitution target next) :
    (term : AssertionTerm context sort) → AssertionTerm.substituteGhosts τ (AssertionTerm.substituteGhosts σ term) = AssertionTerm.substituteGhosts (GhostSubstitution.comp σ τ) term
  | .ghost g => by
      simp only [AssertionTerm.substituteGhosts, GhostTerm.substituteGhosts_comp σ τ g]
  | .boolean v => by
      simp only [AssertionTerm.substituteGhosts]
  | .integer v => by
      simp only [AssertionTerm.substituteGhosts]
  | .rational v => by
      simp only [AssertionTerm.substituteGhosts]
  | .apply f a => by
      simp only [AssertionTerm.substituteGhosts, ValueArguments.substituteGhosts_comp σ τ a]
  | .datasetApply f a => by
      simp only [AssertionTerm.substituteGhosts, ValueArguments.substituteGhosts_comp σ τ a]
  | .ambient => by
      simp only [AssertionTerm.substituteGhosts]
  | .currentView w => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ w]
  | .currentState w => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ w]
  | .worldTrace w => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ w]
  | .appendWorld w t => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ w, AssertionTerm.substituteGhosts_comp σ τ t]
  | .traceEmpty => by
      simp only [AssertionTerm.substituteGhosts]
  | .traceSingleton s => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ s]
  | .traceAppend a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ a, AssertionTerm.substituteGhosts_comp σ τ b]
  | .traceLength t => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ t]
  | .traceTake t i => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ t, AssertionTerm.substituteGhosts_comp σ τ i]
  | .traceIndex t i => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ t, AssertionTerm.substituteGhosts_comp σ τ i]
  | .valueRead v x => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ v]
  | .datasetRead v n => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ v]
  | .visibleOf v => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ v]
  | .hiddenOf v => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ v]
  | .historyOf v => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ v]
  | .provenanceOf v => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ v]
  | .compatibleOf v => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ v]
  | .makeView v h s c p => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ v, AssertionTerm.substituteGhosts_comp σ τ h, AssertionTerm.substituteGhosts_comp σ τ s, AssertionTerm.substituteGhosts_comp σ τ c, AssertionTerm.substituteGhosts_comp σ τ p]
  | .writeValue v x a => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ v, AssertionTerm.substituteGhosts_comp σ τ a]
  | .writeDataset v n d => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ v, AssertionTerm.substituteGhosts_comp σ τ d]
  | .addHistory v h => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ v, AssertionTerm.substituteGhosts_comp σ τ h]
  | .historyEmpty => by
      simp only [AssertionTerm.substituteGhosts]
  | .historySingleton d t => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ d]
  | .historyAdd a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ a, AssertionTerm.substituteGhosts_comp σ τ b]
  | .historyCount h d t => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ h, AssertionTerm.substituteGhosts_comp σ τ d]
  | .provenanceEmpty => by
      simp only [AssertionTerm.substituteGhosts]
  | .provenanceSingleton d p => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ d]
  | .provenanceAdd a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ a, AssertionTerm.substituteGhosts_comp σ τ b]
  | .pvalue t => by
      simp only [AssertionTerm.substituteGhosts, TestExpression.substituteGhosts_comp σ τ t]
  | .realAdd a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ a, AssertionTerm.substituteGhosts_comp σ τ b]
  | .realMin a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ a, AssertionTerm.substituteGhosts_comp σ τ b]
  | .intAdd a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ a, AssertionTerm.substituteGhosts_comp σ τ b]
  | .intSub a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ a, AssertionTerm.substituteGhosts_comp σ τ b]
  | .intLess a b => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ a, AssertionTerm.substituteGhosts_comp σ τ b]
  | .booleanNot a => by
      simp only [AssertionTerm.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ a]
theorem ValueArguments.substituteGhosts_comp (σ : GhostSubstitution context target) (τ : GhostSubstitution target next) :
    (term : ValueArguments context inputs) → ValueArguments.substituteGhosts τ (ValueArguments.substituteGhosts σ term) = ValueArguments.substituteGhosts (GhostSubstitution.comp σ τ) term
  | .nil => by
      simp only [ValueArguments.substituteGhosts]
  | .cons a r => by
      simp only [ValueArguments.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ a, ValueArguments.substituteGhosts_comp σ τ r]
theorem TestExpression.substituteGhosts_comp (σ : GhostSubstitution context target) (τ : GhostSubstitution target next) :
    (term : TestExpression context) → TestExpression.substituteGhosts τ (TestExpression.substituteGhosts σ term) = TestExpression.substituteGhosts (GhostSubstitution.comp σ τ) term
  | .leaf h d t p => by
      simp only [TestExpression.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ d]
  | .disj n a b => by
      simp only [TestExpression.substituteGhosts, TestExpression.substituteGhosts_comp σ τ a, TestExpression.substituteGhosts_comp σ τ b]
  | .conj n a b => by
      simp only [TestExpression.substituteGhosts, TestExpression.substituteGhosts_comp σ τ a, TestExpression.substituteGhosts_comp σ τ b]
end

theorem AssertionAtom.substituteGhosts_comp (σ : GhostSubstitution context target) (τ : GhostSubstitution target next) :
    (term : AssertionAtom context) → AssertionAtom.substituteGhosts τ (AssertionAtom.substituteGhosts σ term) = AssertionAtom.substituteGhosts (GhostSubstitution.comp σ τ) term
  | .rigid p a => by
      simp only [AssertionAtom.substituteGhosts, ValueArguments.substituteGhosts_comp σ τ a]
  | .equal a b => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ a, AssertionTerm.substituteGhosts_comp σ τ b]
  | .defined a => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ a]
  | .realCompare c a b => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ a, AssertionTerm.substituteGhosts_comp σ τ b]
  | .intCompare c a b => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ a, AssertionTerm.substituteGhosts_comp σ τ b]
  | .hypothesis h a => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ a]
  | .sampling d p a => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ d, AssertionTerm.substituteGhosts_comp σ τ a]
  | .requirements e v => by
      simp only [AssertionAtom.substituteGhosts, TestExpression.substituteGhosts_comp σ τ e, AssertionTerm.substituteGhosts_comp σ τ v]
  | .admitted w => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ w]
  | .action c s => by
      simp only [AssertionAtom.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ s]

theorem ModalFormula.substituteGhosts_comp (σ : GhostSubstitution context target) (τ : GhostSubstitution target next) :
    (term : ModalFormula context) → ModalFormula.substituteGhosts τ (ModalFormula.substituteGhosts σ term) = ModalFormula.substituteGhosts (GhostSubstitution.comp σ τ) term
  | .atom a => by
      simp only [ModalFormula.substituteGhosts, AssertionAtom.substituteGhosts_comp σ τ a]
  | .neg a => by
      simp only [ModalFormula.substituteGhosts, ModalFormula.substituteGhosts_comp σ τ a]
  | .conj a b => by
      simp only [ModalFormula.substituteGhosts, ModalFormula.substituteGhosts_comp σ τ a, ModalFormula.substituteGhosts_comp σ τ b]
  | .knows a => by
      simp only [ModalFormula.substituteGhosts, ModalFormula.substituteGhosts_comp σ τ a]
  | .atWorld w a => by
      simp only [ModalFormula.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ w, ModalFormula.substituteGhosts_comp σ τ a]
  | .atView v a => by
      simp only [ModalFormula.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ v, ModalFormula.substituteGhosts_comp σ τ a]

theorem Assertion.substituteGhosts_comp (σ : GhostSubstitution context target) (τ : GhostSubstitution target next) :
    (term : Assertion context) → Assertion.substituteGhosts τ (Assertion.substituteGhosts σ term) = Assertion.substituteGhosts (GhostSubstitution.comp σ τ) term
  | .modal a => by
      simp only [Assertion.substituteGhosts, ModalFormula.substituteGhosts_comp σ τ a]
  | .neg a => by
      simp only [Assertion.substituteGhosts, Assertion.substituteGhosts_comp σ τ a]
  | .conj a b => by
      simp only [Assertion.substituteGhosts, Assertion.substituteGhosts_comp σ τ a, Assertion.substituteGhosts_comp σ τ b]
  | .all s a => by
      simp only [Assertion.substituteGhosts, Assertion.substituteGhosts_comp (GhostSubstitution.lift σ) (GhostSubstitution.lift τ) a, GhostSubstitution.lift_comp]
  | .atWorld w a => by
      simp only [Assertion.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ w, Assertion.substituteGhosts_comp σ τ a]
  | .atView v a => by
      simp only [Assertion.substituteGhosts, AssertionTerm.substituteGhosts_comp σ τ v, Assertion.substituteGhosts_comp σ τ a]

mutual
theorem AssertionTerm.renameGhosts_eq_substituteGhosts (σ : GhostRenaming context target) :
    (term : AssertionTerm context sort) → AssertionTerm.renameGhosts σ term = AssertionTerm.substituteGhosts (GhostSubstitution.ofRenaming σ) term
  | .ghost g => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, GhostTerm.renameGhosts_eq_substituteGhosts σ g]
  | .boolean v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts]
  | .integer v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts]
  | .rational v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts]
  | .apply f a => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, ValueArguments.renameGhosts_eq_substituteGhosts σ a]
  | .datasetApply f a => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, ValueArguments.renameGhosts_eq_substituteGhosts σ a]
  | .ambient => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts]
  | .currentView w => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ w]
  | .currentState w => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ w]
  | .worldTrace w => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ w]
  | .appendWorld w t => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ w, AssertionTerm.renameGhosts_eq_substituteGhosts σ t]
  | .traceEmpty => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts]
  | .traceSingleton s => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ s]
  | .traceAppend a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ a, AssertionTerm.renameGhosts_eq_substituteGhosts σ b]
  | .traceLength t => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ t]
  | .traceTake t i => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ t, AssertionTerm.renameGhosts_eq_substituteGhosts σ i]
  | .traceIndex t i => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ t, AssertionTerm.renameGhosts_eq_substituteGhosts σ i]
  | .valueRead v x => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ v]
  | .datasetRead v n => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ v]
  | .visibleOf v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ v]
  | .hiddenOf v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ v]
  | .historyOf v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ v]
  | .provenanceOf v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ v]
  | .compatibleOf v => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ v]
  | .makeView v h s c p => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ v, AssertionTerm.renameGhosts_eq_substituteGhosts σ h, AssertionTerm.renameGhosts_eq_substituteGhosts σ s, AssertionTerm.renameGhosts_eq_substituteGhosts σ c, AssertionTerm.renameGhosts_eq_substituteGhosts σ p]
  | .writeValue v x a => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ v, AssertionTerm.renameGhosts_eq_substituteGhosts σ a]
  | .writeDataset v n d => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ v, AssertionTerm.renameGhosts_eq_substituteGhosts σ d]
  | .addHistory v h => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ v, AssertionTerm.renameGhosts_eq_substituteGhosts σ h]
  | .historyEmpty => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts]
  | .historySingleton d t => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ d]
  | .historyAdd a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ a, AssertionTerm.renameGhosts_eq_substituteGhosts σ b]
  | .historyCount h d t => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ h, AssertionTerm.renameGhosts_eq_substituteGhosts σ d]
  | .provenanceEmpty => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts]
  | .provenanceSingleton d p => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ d]
  | .provenanceAdd a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ a, AssertionTerm.renameGhosts_eq_substituteGhosts σ b]
  | .pvalue t => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, TestExpression.renameGhosts_eq_substituteGhosts σ t]
  | .realAdd a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ a, AssertionTerm.renameGhosts_eq_substituteGhosts σ b]
  | .realMin a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ a, AssertionTerm.renameGhosts_eq_substituteGhosts σ b]
  | .intAdd a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ a, AssertionTerm.renameGhosts_eq_substituteGhosts σ b]
  | .intSub a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ a, AssertionTerm.renameGhosts_eq_substituteGhosts σ b]
  | .intLess a b => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ a, AssertionTerm.renameGhosts_eq_substituteGhosts σ b]
  | .booleanNot a => by
      simp only [AssertionTerm.renameGhosts, AssertionTerm.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ a]
theorem ValueArguments.renameGhosts_eq_substituteGhosts (σ : GhostRenaming context target) :
    (term : ValueArguments context inputs) → ValueArguments.renameGhosts σ term = ValueArguments.substituteGhosts (GhostSubstitution.ofRenaming σ) term
  | .nil => by
      simp only [ValueArguments.renameGhosts, ValueArguments.substituteGhosts]
  | .cons a r => by
      simp only [ValueArguments.renameGhosts, ValueArguments.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ a, ValueArguments.renameGhosts_eq_substituteGhosts σ r]
theorem TestExpression.renameGhosts_eq_substituteGhosts (σ : GhostRenaming context target) :
    (term : TestExpression context) → TestExpression.renameGhosts σ term = TestExpression.substituteGhosts (GhostSubstitution.ofRenaming σ) term
  | .leaf h d t p => by
      simp only [TestExpression.renameGhosts, TestExpression.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ d]
  | .disj n a b => by
      simp only [TestExpression.renameGhosts, TestExpression.substituteGhosts, TestExpression.renameGhosts_eq_substituteGhosts σ a, TestExpression.renameGhosts_eq_substituteGhosts σ b]
  | .conj n a b => by
      simp only [TestExpression.renameGhosts, TestExpression.substituteGhosts, TestExpression.renameGhosts_eq_substituteGhosts σ a, TestExpression.renameGhosts_eq_substituteGhosts σ b]
end

theorem AssertionAtom.renameGhosts_eq_substituteGhosts (σ : GhostRenaming context target) :
    (term : AssertionAtom context) → AssertionAtom.renameGhosts σ term = AssertionAtom.substituteGhosts (GhostSubstitution.ofRenaming σ) term
  | .rigid p a => by
      simp only [AssertionAtom.renameGhosts, AssertionAtom.substituteGhosts, ValueArguments.renameGhosts_eq_substituteGhosts σ a]
  | .equal a b => by
      simp only [AssertionAtom.renameGhosts, AssertionAtom.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ a, AssertionTerm.renameGhosts_eq_substituteGhosts σ b]
  | .defined a => by
      simp only [AssertionAtom.renameGhosts, AssertionAtom.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ a]
  | .realCompare c a b => by
      simp only [AssertionAtom.renameGhosts, AssertionAtom.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ a, AssertionTerm.renameGhosts_eq_substituteGhosts σ b]
  | .intCompare c a b => by
      simp only [AssertionAtom.renameGhosts, AssertionAtom.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ a, AssertionTerm.renameGhosts_eq_substituteGhosts σ b]
  | .hypothesis h a => by
      simp only [AssertionAtom.renameGhosts, AssertionAtom.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ a]
  | .sampling d p a => by
      simp only [AssertionAtom.renameGhosts, AssertionAtom.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ d, AssertionTerm.renameGhosts_eq_substituteGhosts σ a]
  | .requirements e v => by
      simp only [AssertionAtom.renameGhosts, AssertionAtom.substituteGhosts, TestExpression.renameGhosts_eq_substituteGhosts σ e, AssertionTerm.renameGhosts_eq_substituteGhosts σ v]
  | .admitted w => by
      simp only [AssertionAtom.renameGhosts, AssertionAtom.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ w]
  | .action c s => by
      simp only [AssertionAtom.renameGhosts, AssertionAtom.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ s]

theorem ModalFormula.renameGhosts_eq_substituteGhosts (σ : GhostRenaming context target) :
    (term : ModalFormula context) → ModalFormula.renameGhosts σ term = ModalFormula.substituteGhosts (GhostSubstitution.ofRenaming σ) term
  | .atom a => by
      simp only [ModalFormula.renameGhosts, ModalFormula.substituteGhosts, AssertionAtom.renameGhosts_eq_substituteGhosts σ a]
  | .neg a => by
      simp only [ModalFormula.renameGhosts, ModalFormula.substituteGhosts, ModalFormula.renameGhosts_eq_substituteGhosts σ a]
  | .conj a b => by
      simp only [ModalFormula.renameGhosts, ModalFormula.substituteGhosts, ModalFormula.renameGhosts_eq_substituteGhosts σ a, ModalFormula.renameGhosts_eq_substituteGhosts σ b]
  | .knows a => by
      simp only [ModalFormula.renameGhosts, ModalFormula.substituteGhosts, ModalFormula.renameGhosts_eq_substituteGhosts σ a]
  | .atWorld w a => by
      simp only [ModalFormula.renameGhosts, ModalFormula.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ w, ModalFormula.renameGhosts_eq_substituteGhosts σ a]
  | .atView v a => by
      simp only [ModalFormula.renameGhosts, ModalFormula.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ v, ModalFormula.renameGhosts_eq_substituteGhosts σ a]

theorem Assertion.renameGhosts_eq_substituteGhosts (σ : GhostRenaming context target) :
    (term : Assertion context) → Assertion.renameGhosts σ term = Assertion.substituteGhosts (GhostSubstitution.ofRenaming σ) term
  | .modal a => by
      simp only [Assertion.renameGhosts, Assertion.substituteGhosts, ModalFormula.renameGhosts_eq_substituteGhosts σ a]
  | .neg a => by
      simp only [Assertion.renameGhosts, Assertion.substituteGhosts, Assertion.renameGhosts_eq_substituteGhosts σ a]
  | .conj a b => by
      simp only [Assertion.renameGhosts, Assertion.substituteGhosts, Assertion.renameGhosts_eq_substituteGhosts σ a, Assertion.renameGhosts_eq_substituteGhosts σ b]
  | .all s a => by
      simp only [Assertion.renameGhosts, Assertion.substituteGhosts, Assertion.renameGhosts_eq_substituteGhosts (GhostRenaming.lift σ) a, GhostSubstitution.lift_ofRenaming]
  | .atWorld w a => by
      simp only [Assertion.renameGhosts, Assertion.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ w, Assertion.renameGhosts_eq_substituteGhosts σ a]
  | .atView v a => by
      simp only [Assertion.renameGhosts, Assertion.substituteGhosts, AssertionTerm.renameGhosts_eq_substituteGhosts σ v, Assertion.renameGhosts_eq_substituteGhosts σ a]

abbrev GhostUse (context : List GhostSort) := Sigma (BoundGhost context)

def GhostTerm.freeGhosts : GhostTerm context sort → List (GhostUse context)
  | .bound index => [⟨_, index⟩]
  | .constant _ => []

/-- Remove the newly bound index and shift every remaining index outward. -/
def GhostUse.dropBinder : GhostUse (other :: context) → Option (GhostUse context)
  | ⟨_, .here⟩ => none
  | ⟨_, .there index⟩ => some ⟨_, index⟩

def dischargeGhosts (uses : List (GhostUse (other :: context))) : List (GhostUse context) :=
  uses.filterMap GhostUse.dropBinder

theorem mem_dischargeGhosts_of_there (uses : List (GhostUse (other :: context)))
    (index : BoundGhost context sort) (h : (⟨sort, .there index⟩ : GhostUse (other :: context)) ∈ uses) :
    (⟨sort, index⟩ : GhostUse context) ∈ dischargeGhosts uses := by
  apply List.mem_filterMap.mpr
  exact ⟨⟨sort, .there index⟩, h, rfl⟩

mutual
def AssertionTerm.freeGhosts : AssertionTerm context sort → List (GhostUse context)
  | .ghost g => g.freeGhosts
  | .boolean v => []
  | .integer v => []
  | .rational v => []
  | .apply _ a => ValueArguments.freeGhosts a
  | .datasetApply _ a => ValueArguments.freeGhosts a
  | .ambient => []
  | .currentView w => AssertionTerm.freeGhosts w
  | .currentState w => AssertionTerm.freeGhosts w
  | .worldTrace w => AssertionTerm.freeGhosts w
  | .appendWorld w t => AssertionTerm.freeGhosts w ++ AssertionTerm.freeGhosts t
  | .traceEmpty => []
  | .traceSingleton s => AssertionTerm.freeGhosts s
  | .traceAppend a b => AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b
  | .traceLength t => AssertionTerm.freeGhosts t
  | .traceTake t i => AssertionTerm.freeGhosts t ++ AssertionTerm.freeGhosts i
  | .traceIndex t i => AssertionTerm.freeGhosts t ++ AssertionTerm.freeGhosts i
  | .valueRead v x => AssertionTerm.freeGhosts v
  | .datasetRead v n => AssertionTerm.freeGhosts v
  | .visibleOf v => AssertionTerm.freeGhosts v
  | .hiddenOf v => AssertionTerm.freeGhosts v
  | .historyOf v => AssertionTerm.freeGhosts v
  | .provenanceOf v => AssertionTerm.freeGhosts v
  | .compatibleOf v => AssertionTerm.freeGhosts v
  | .makeView v h s c p => AssertionTerm.freeGhosts v ++ AssertionTerm.freeGhosts h ++ AssertionTerm.freeGhosts s ++ AssertionTerm.freeGhosts c ++ AssertionTerm.freeGhosts p
  | .writeValue v _ a => AssertionTerm.freeGhosts v ++ AssertionTerm.freeGhosts a
  | .writeDataset v _ d => AssertionTerm.freeGhosts v ++ AssertionTerm.freeGhosts d
  | .addHistory v h => AssertionTerm.freeGhosts v ++ AssertionTerm.freeGhosts h
  | .historyEmpty => []
  | .historySingleton d t => AssertionTerm.freeGhosts d
  | .historyAdd a b => AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b
  | .historyCount h d t => AssertionTerm.freeGhosts h ++ AssertionTerm.freeGhosts d
  | .provenanceEmpty => []
  | .provenanceSingleton d p => AssertionTerm.freeGhosts d
  | .provenanceAdd a b => AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b
  | .pvalue t => TestExpression.freeGhosts t
  | .realAdd a b => AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b
  | .realMin a b => AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b
  | .intAdd a b => AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b
  | .intSub a b => AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b
  | .intLess a b => AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b
  | .booleanNot a => AssertionTerm.freeGhosts a

def ValueArguments.freeGhosts : ValueArguments context inputs → List (GhostUse context)
  | .nil => []
  | .cons a r => AssertionTerm.freeGhosts a ++ ValueArguments.freeGhosts r

def TestExpression.freeGhosts : TestExpression context → List (GhostUse context)
  | .leaf _ d _ _ => AssertionTerm.freeGhosts d
  | .disj _ a b => TestExpression.freeGhosts a ++ TestExpression.freeGhosts b
  | .conj _ a b => TestExpression.freeGhosts a ++ TestExpression.freeGhosts b

end

def AssertionAtom.freeGhosts : AssertionAtom context → List (GhostUse context)
  | .rigid _ a => ValueArguments.freeGhosts a
  | .equal a b => AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b
  | .defined a => AssertionTerm.freeGhosts a
  | .realCompare _ a b => AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b
  | .intCompare _ a b => AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b
  | .hypothesis _ a => AssertionTerm.freeGhosts a
  | .sampling d _ a => AssertionTerm.freeGhosts d ++ AssertionTerm.freeGhosts a
  | .requirements e v => TestExpression.freeGhosts e ++ AssertionTerm.freeGhosts v
  | .admitted w => AssertionTerm.freeGhosts w
  | .action _ s => AssertionTerm.freeGhosts s

def ModalFormula.freeGhosts : ModalFormula context → List (GhostUse context)
  | .atom a => AssertionAtom.freeGhosts a
  | .neg a => ModalFormula.freeGhosts a
  | .conj a b => ModalFormula.freeGhosts a ++ ModalFormula.freeGhosts b
  | .knows a => ModalFormula.freeGhosts a
  | .atWorld w a => AssertionTerm.freeGhosts w ++ ModalFormula.freeGhosts a
  | .atView v a => AssertionTerm.freeGhosts v ++ ModalFormula.freeGhosts a

def Assertion.freeGhosts : Assertion context → List (GhostUse context)
  | .modal a => ModalFormula.freeGhosts a
  | .neg a => Assertion.freeGhosts a
  | .conj a b => Assertion.freeGhosts a ++ Assertion.freeGhosts b
  | .all _ a => dischargeGhosts (Assertion.freeGhosts a)
  | .atWorld w a => AssertionTerm.freeGhosts w ++ Assertion.freeGhosts a
  | .atView v a => AssertionTerm.freeGhosts v ++ Assertion.freeGhosts a

def GhostSubstitution.Fixes (σ : GhostSubstitution context context)
    (uses : List (GhostUse context)) : Prop :=
  ∀ (sort : GhostSort) (index : BoundGhost context sort),
    (⟨sort, index⟩ : GhostUse context) ∈ uses → σ sort index = .bound index

theorem GhostSubstitution.Fixes.append_left
    {σ : GhostSubstitution context context} {left right : List (GhostUse context)}
    (h : σ.Fixes (left ++ right)) : σ.Fixes left := by
  intro sort index hi
  exact h sort index (List.mem_append.mpr (Or.inl hi))

theorem GhostSubstitution.Fixes.append_right
    {σ : GhostSubstitution context context} {left right : List (GhostUse context)}
    (h : σ.Fixes (left ++ right)) : σ.Fixes right := by
  intro sort index hi
  exact h sort index (List.mem_append.mpr (Or.inr hi))

theorem GhostSubstitution.Fixes.lift
    {σ : GhostSubstitution context context} {uses : List (GhostUse (other :: context))}
    (h : σ.Fixes (dischargeGhosts uses)) : (GhostSubstitution.lift σ).Fixes uses := by
  intro sort index hi
  cases index with
  | here => rfl
  | there index =>
      dsimp [GhostSubstitution.lift]
      rw [h sort index (mem_dischargeGhosts_of_there uses index hi)]
      rfl

theorem GhostTerm.substituteGhosts_of_fixes (σ : GhostSubstitution context context) :
    (term : GhostTerm context sort) → σ.Fixes term.freeGhosts → term.substituteGhosts σ = term
  | .bound index, h => h _ index (by simp [GhostTerm.freeGhosts])
  | .constant _, _ => rfl

mutual
theorem AssertionTerm.substituteGhosts_of_fixes (σ : GhostSubstitution context context) :
    (term : AssertionTerm context sort) → σ.Fixes (AssertionTerm.freeGhosts term) →
      AssertionTerm.substituteGhosts σ term = term
  | .ghost g, h => by
      change σ.Fixes (GhostTerm.freeGhosts g) at h
      have h0 := GhostTerm.substituteGhosts_of_fixes σ g h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .boolean v, h => by
      rfl
  | .integer v, h => by
      rfl
  | .rational v, h => by
      rfl
  | .apply f a, h => by
      change σ.Fixes (ValueArguments.freeGhosts a) at h
      have h0 := ValueArguments.substituteGhosts_of_fixes σ a h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .datasetApply f a, h => by
      change σ.Fixes (ValueArguments.freeGhosts a) at h
      have h0 := ValueArguments.substituteGhosts_of_fixes σ a h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .ambient, h => by
      rfl
  | .currentView w, h => by
      change σ.Fixes (AssertionTerm.freeGhosts w) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ w h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .currentState w, h => by
      change σ.Fixes (AssertionTerm.freeGhosts w) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ w h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .worldTrace w, h => by
      change σ.Fixes (AssertionTerm.freeGhosts w) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ w h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .appendWorld w t, h => by
      change σ.Fixes (AssertionTerm.freeGhosts w ++ AssertionTerm.freeGhosts t) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ w (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ t (h.append_right)
      simp only [AssertionTerm.substituteGhosts, h0, h1]
  | .traceEmpty, h => by
      rfl
  | .traceSingleton s, h => by
      change σ.Fixes (AssertionTerm.freeGhosts s) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ s h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .traceAppend a b, h => by
      change σ.Fixes (AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ b (h.append_right)
      simp only [AssertionTerm.substituteGhosts, h0, h1]
  | .traceLength t, h => by
      change σ.Fixes (AssertionTerm.freeGhosts t) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ t h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .traceTake t i, h => by
      change σ.Fixes (AssertionTerm.freeGhosts t ++ AssertionTerm.freeGhosts i) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ t (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ i (h.append_right)
      simp only [AssertionTerm.substituteGhosts, h0, h1]
  | .traceIndex t i, h => by
      change σ.Fixes (AssertionTerm.freeGhosts t ++ AssertionTerm.freeGhosts i) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ t (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ i (h.append_right)
      simp only [AssertionTerm.substituteGhosts, h0, h1]
  | .valueRead v x, h => by
      change σ.Fixes (AssertionTerm.freeGhosts v) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ v h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .datasetRead v n, h => by
      change σ.Fixes (AssertionTerm.freeGhosts v) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ v h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .visibleOf v, h => by
      change σ.Fixes (AssertionTerm.freeGhosts v) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ v h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .hiddenOf v, h => by
      change σ.Fixes (AssertionTerm.freeGhosts v) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ v h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .historyOf v, h => by
      change σ.Fixes (AssertionTerm.freeGhosts v) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ v h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .provenanceOf v, h => by
      change σ.Fixes (AssertionTerm.freeGhosts v) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ v h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .compatibleOf v, h => by
      change σ.Fixes (AssertionTerm.freeGhosts v) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ v h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .makeView v history s c p, h => by
      change σ.Fixes (AssertionTerm.freeGhosts v ++ AssertionTerm.freeGhosts history ++ AssertionTerm.freeGhosts s ++ AssertionTerm.freeGhosts c ++ AssertionTerm.freeGhosts p) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ v h.append_left.append_left.append_left.append_left
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ history h.append_left.append_left.append_left.append_right
      have h2 := AssertionTerm.substituteGhosts_of_fixes σ s h.append_left.append_left.append_right
      have h3 := AssertionTerm.substituteGhosts_of_fixes σ c h.append_left.append_right
      have h4 := AssertionTerm.substituteGhosts_of_fixes σ p h.append_right
      simp only [AssertionTerm.substituteGhosts, h0, h1, h2, h3, h4]
  | .writeValue v x a, h => by
      change σ.Fixes (AssertionTerm.freeGhosts v ++ AssertionTerm.freeGhosts a) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ v (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ a (h.append_right)
      simp only [AssertionTerm.substituteGhosts, h0, h1]
  | .writeDataset v n d, h => by
      change σ.Fixes (AssertionTerm.freeGhosts v ++ AssertionTerm.freeGhosts d) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ v (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ d (h.append_right)
      simp only [AssertionTerm.substituteGhosts, h0, h1]
  | .addHistory v history, h => by
      change σ.Fixes (AssertionTerm.freeGhosts v ++ AssertionTerm.freeGhosts history) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ v (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ history (h.append_right)
      simp only [AssertionTerm.substituteGhosts, h0, h1]
  | .historyEmpty, h => by
      rfl
  | .historySingleton d t, h => by
      change σ.Fixes (AssertionTerm.freeGhosts d) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ d h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .historyAdd a b, h => by
      change σ.Fixes (AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ b (h.append_right)
      simp only [AssertionTerm.substituteGhosts, h0, h1]
  | .historyCount history d t, h => by
      change σ.Fixes (AssertionTerm.freeGhosts history ++ AssertionTerm.freeGhosts d) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ history (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ d (h.append_right)
      simp only [AssertionTerm.substituteGhosts, h0, h1]
  | .provenanceEmpty, h => by
      rfl
  | .provenanceSingleton d p, h => by
      change σ.Fixes (AssertionTerm.freeGhosts d) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ d h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .provenanceAdd a b, h => by
      change σ.Fixes (AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ b (h.append_right)
      simp only [AssertionTerm.substituteGhosts, h0, h1]
  | .pvalue t, h => by
      change σ.Fixes (TestExpression.freeGhosts t) at h
      have h0 := TestExpression.substituteGhosts_of_fixes σ t h
      simp only [AssertionTerm.substituteGhosts, h0]
  | .realAdd a b, h => by
      change σ.Fixes (AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ b (h.append_right)
      simp only [AssertionTerm.substituteGhosts, h0, h1]
  | .realMin a b, h => by
      change σ.Fixes (AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ b (h.append_right)
      simp only [AssertionTerm.substituteGhosts, h0, h1]
  | .intAdd a b, h => by
      change σ.Fixes (AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ b (h.append_right)
      simp only [AssertionTerm.substituteGhosts, h0, h1]
  | .intSub a b, h => by
      change σ.Fixes (AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ b (h.append_right)
      simp only [AssertionTerm.substituteGhosts, h0, h1]
  | .intLess a b, h => by
      change σ.Fixes (AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ b (h.append_right)
      simp only [AssertionTerm.substituteGhosts, h0, h1]
  | .booleanNot a, h => by
      change σ.Fixes (AssertionTerm.freeGhosts a) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ a h
      simp only [AssertionTerm.substituteGhosts, h0]
theorem ValueArguments.substituteGhosts_of_fixes (σ : GhostSubstitution context context) :
    (term : ValueArguments context inputs) → σ.Fixes (ValueArguments.freeGhosts term) →
      ValueArguments.substituteGhosts σ term = term
  | .nil, h => by
      rfl
  | .cons a r, h => by
      change σ.Fixes (AssertionTerm.freeGhosts a ++ ValueArguments.freeGhosts r) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := ValueArguments.substituteGhosts_of_fixes σ r (h.append_right)
      simp only [ValueArguments.substituteGhosts, h0, h1]
theorem TestExpression.substituteGhosts_of_fixes (σ : GhostSubstitution context context) :
    (term : TestExpression context) → σ.Fixes (TestExpression.freeGhosts term) →
      TestExpression.substituteGhosts σ term = term
  | .leaf _hypothesis d t p, h => by
      change σ.Fixes (AssertionTerm.freeGhosts d) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ d h
      simp only [TestExpression.substituteGhosts, h0]
  | .disj n a b, h => by
      change σ.Fixes (TestExpression.freeGhosts a ++ TestExpression.freeGhosts b) at h
      have h0 := TestExpression.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := TestExpression.substituteGhosts_of_fixes σ b (h.append_right)
      simp only [TestExpression.substituteGhosts, h0, h1]
  | .conj n a b, h => by
      change σ.Fixes (TestExpression.freeGhosts a ++ TestExpression.freeGhosts b) at h
      have h0 := TestExpression.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := TestExpression.substituteGhosts_of_fixes σ b (h.append_right)
      simp only [TestExpression.substituteGhosts, h0, h1]
end

theorem AssertionAtom.substituteGhosts_of_fixes (σ : GhostSubstitution context context) :
    (term : AssertionAtom context) → σ.Fixes (AssertionAtom.freeGhosts term) →
      AssertionAtom.substituteGhosts σ term = term
  | .rigid p a, h => by
      change σ.Fixes (ValueArguments.freeGhosts a) at h
      have h0 := ValueArguments.substituteGhosts_of_fixes σ a h
      simp only [AssertionAtom.substituteGhosts, h0]
  | .equal a b, h => by
      change σ.Fixes (AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ b (h.append_right)
      simp only [AssertionAtom.substituteGhosts, h0, h1]
  | .defined a, h => by
      change σ.Fixes (AssertionTerm.freeGhosts a) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ a h
      simp only [AssertionAtom.substituteGhosts, h0]
  | .realCompare c a b, h => by
      change σ.Fixes (AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ b (h.append_right)
      simp only [AssertionAtom.substituteGhosts, h0, h1]
  | .intCompare c a b, h => by
      change σ.Fixes (AssertionTerm.freeGhosts a ++ AssertionTerm.freeGhosts b) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ b (h.append_right)
      simp only [AssertionAtom.substituteGhosts, h0, h1]
  | .hypothesis _hypothesis a, h => by
      change σ.Fixes (AssertionTerm.freeGhosts a) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ a h
      simp only [AssertionAtom.substituteGhosts, h0]
  | .sampling d p a, h => by
      change σ.Fixes (AssertionTerm.freeGhosts d ++ AssertionTerm.freeGhosts a) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ d (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ a (h.append_right)
      simp only [AssertionAtom.substituteGhosts, h0, h1]
  | .requirements e v, h => by
      change σ.Fixes (TestExpression.freeGhosts e ++ AssertionTerm.freeGhosts v) at h
      have h0 := TestExpression.substituteGhosts_of_fixes σ e (h.append_left)
      have h1 := AssertionTerm.substituteGhosts_of_fixes σ v (h.append_right)
      simp only [AssertionAtom.substituteGhosts, h0, h1]
  | .admitted w, h => by
      change σ.Fixes (AssertionTerm.freeGhosts w) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ w h
      simp only [AssertionAtom.substituteGhosts, h0]
  | .action c s, h => by
      change σ.Fixes (AssertionTerm.freeGhosts s) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ s h
      simp only [AssertionAtom.substituteGhosts, h0]

theorem ModalFormula.substituteGhosts_of_fixes (σ : GhostSubstitution context context) :
    (term : ModalFormula context) → σ.Fixes (ModalFormula.freeGhosts term) →
      ModalFormula.substituteGhosts σ term = term
  | .atom a, h => by
      change σ.Fixes (AssertionAtom.freeGhosts a) at h
      have h0 := AssertionAtom.substituteGhosts_of_fixes σ a h
      simp only [ModalFormula.substituteGhosts, h0]
  | .neg a, h => by
      change σ.Fixes (ModalFormula.freeGhosts a) at h
      have h0 := ModalFormula.substituteGhosts_of_fixes σ a h
      simp only [ModalFormula.substituteGhosts, h0]
  | .conj a b, h => by
      change σ.Fixes (ModalFormula.freeGhosts a ++ ModalFormula.freeGhosts b) at h
      have h0 := ModalFormula.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := ModalFormula.substituteGhosts_of_fixes σ b (h.append_right)
      simp only [ModalFormula.substituteGhosts, h0, h1]
  | .knows a, h => by
      change σ.Fixes (ModalFormula.freeGhosts a) at h
      have h0 := ModalFormula.substituteGhosts_of_fixes σ a h
      simp only [ModalFormula.substituteGhosts, h0]
  | .atWorld w a, h => by
      change σ.Fixes (AssertionTerm.freeGhosts w ++ ModalFormula.freeGhosts a) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ w (h.append_left)
      have h1 := ModalFormula.substituteGhosts_of_fixes σ a (h.append_right)
      simp only [ModalFormula.substituteGhosts, h0, h1]
  | .atView v a, h => by
      change σ.Fixes (AssertionTerm.freeGhosts v ++ ModalFormula.freeGhosts a) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ v (h.append_left)
      have h1 := ModalFormula.substituteGhosts_of_fixes σ a (h.append_right)
      simp only [ModalFormula.substituteGhosts, h0, h1]

theorem Assertion.substituteGhosts_of_fixes (σ : GhostSubstitution context context) :
    (term : Assertion context) → σ.Fixes (Assertion.freeGhosts term) →
      Assertion.substituteGhosts σ term = term
  | .modal a, h => by
      change σ.Fixes (ModalFormula.freeGhosts a) at h
      have h0 := ModalFormula.substituteGhosts_of_fixes σ a h
      simp only [Assertion.substituteGhosts, h0]
  | .neg a, h => by
      change σ.Fixes (Assertion.freeGhosts a) at h
      have h0 := Assertion.substituteGhosts_of_fixes σ a h
      simp only [Assertion.substituteGhosts, h0]
  | .conj a b, h => by
      change σ.Fixes (Assertion.freeGhosts a ++ Assertion.freeGhosts b) at h
      have h0 := Assertion.substituteGhosts_of_fixes σ a (h.append_left)
      have h1 := Assertion.substituteGhosts_of_fixes σ b (h.append_right)
      simp only [Assertion.substituteGhosts, h0, h1]
  | .all s a, h => by
      change σ.Fixes (dischargeGhosts (Assertion.freeGhosts a)) at h
      have h0 := Assertion.substituteGhosts_of_fixes (GhostSubstitution.lift σ) a h.lift
      simp only [Assertion.substituteGhosts, h0]
  | .atWorld w a, h => by
      change σ.Fixes (AssertionTerm.freeGhosts w ++ Assertion.freeGhosts a) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ w (h.append_left)
      have h1 := Assertion.substituteGhosts_of_fixes σ a (h.append_right)
      simp only [Assertion.substituteGhosts, h0, h1]
  | .atView v a, h => by
      change σ.Fixes (AssertionTerm.freeGhosts v ++ Assertion.freeGhosts a) at h
      have h0 := AssertionTerm.substituteGhosts_of_fixes σ v (h.append_left)
      have h1 := Assertion.substituteGhosts_of_fixes σ a (h.append_right)
      simp only [Assertion.substituteGhosts, h0, h1]

end Lara.BHL
