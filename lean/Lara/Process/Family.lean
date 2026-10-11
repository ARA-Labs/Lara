import Lara.Process.Universe
import Lara.Process.SourceInput
import Lara.Process.SourceKinds

/-!
A declared finite product of source alternatives over the P0 history carrier.
Guards are modeling constraints, not observations. Neither slot order nor source
order adds event precedence. Materialization only appends declarations: the source
checker must elaborate and check the complete resulting input, including duplicate
identifiers, missing dependencies and unresolved attacks.
-/

namespace Lara.Process.Family

structure SlotId where
  index : Nat
  deriving DecidableEq, Repr

structure ChoiceId where
  index : Nat
  deriving DecidableEq, Repr

/-- Reuse the complete typed source vocabulary, including extraction declarations. -/
abbrev SourceFragment := List Presentation.Decl

inductive Guard where
  | truth
  | query : Universe.Query → Guard
  | present : Stamped → Guard
  | before : Stamped → Stamped → Guard
  | not : Guard → Guard
  | and : Guard → Guard → Guard
  | or : Guard → Guard → Guard
  deriving DecidableEq, Repr

/-- Strictly ordered occurrences, not event identifiers or declaration positions. -/
def Before (first second : Stamped) (history : ProcessHistory) : Prop :=
  ∃ pre suffix, history = pre ++ first :: suffix ∧ second ∈ suffix

private def beforeEval (first second : Stamped) : ProcessHistory → Bool
  | [] => false
  | event :: rest => (decide (event = first) && rest.contains second) ||
      beforeEval first second rest

private theorem before_cons (first second event : Stamped) (rest : ProcessHistory) :
    Before first second (event :: rest) ↔
      (event = first ∧ second ∈ rest) ∨ Before first second rest := by
  constructor
  · rintro ⟨pre, suffix, equal, member⟩
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at equal
      exact Or.inl ⟨equal.1, equal.2.symm ▸ member⟩
    | cons head tail =>
      simp only [List.cons_append, List.cons.injEq] at equal
      exact Or.inr ⟨tail, suffix, equal.2, member⟩
  · rintro (⟨rfl, member⟩ | ⟨pre, suffix, rfl, member⟩)
    · exact ⟨[], rest, rfl, member⟩
    · exact ⟨event :: pre, suffix, rfl, member⟩

private theorem beforeEval_iff (first second : Stamped) (history : ProcessHistory) :
    beforeEval first second history = true ↔ Before first second history := by
  induction history with
  | nil => simp [beforeEval, Before]
  | cons event rest ih => simp [beforeEval, before_cons, ih]

/-- Propositional semantics independent of the Boolean guard interpreter. -/
def Guard.Holds : Guard → ProcessHistory → Prop
  | .truth, _ => True
  | .query q, history => q.holds Universe.Atom.holds history
  | .present event, history => event ∈ history
  | .before first second, history => Before first second history
  | .not guard, history => ¬ guard.Holds history
  | .and left right, history => left.Holds history ∧ right.Holds history
  | .or left right, history => left.Holds history ∨ right.Holds history

def Guard.eval : Guard → ProcessHistory → Bool
  | .truth, _ => true
  | .query q, history => decide (q.holds Universe.Atom.holds history)
  | .present event, history => history.contains event
  | .before first second, history => beforeEval first second history
  | .not guard, history => !(guard.eval history)
  | .and left right, history => left.eval history && right.eval history
  | .or left right, history => left.eval history || right.eval history

theorem Guard.eval_iff (guard : Guard) (history : ProcessHistory) :
    guard.eval history = true ↔ guard.Holds history := by
  induction guard with
  | truth => simp [eval, Holds]
  | query query => simp [eval, Holds]
  | present event => simp [eval, Holds]
  | before first second => exact beforeEval_iff first second history
  | not guard ih => simpa [eval, Holds] using not_congr ih
  | and left right il ir => simp [eval, Holds, il, ir]
  | or left right il ir => simp [eval, Holds, il, ir]

structure Choice where
  id : ChoiceId
  guard : Guard
  fragment : SourceFragment
  deriving DecidableEq

structure Slot where
  id : SlotId
  choices : List Choice
  deriving DecidableEq

/-- Store the declared choice itself; materialization never needs a lookup fallback. -/
structure Selection where
  slot : SlotId
  choice : Choice
  deriving DecidableEq

structure Completion where
  history : ProcessHistory
  assignment : List Selection
  deriving DecidableEq

structure FamilySpec where
  problem : Universe.Problem
  base : Source.SourceInput
  slots : List Slot
  deriving DecidableEq

/-- Identity and nonemptiness constraints, separate from source acceptance. -/
def WellFormed (spec : FamilySpec) : Prop :=
  (spec.slots.map Slot.id).Nodup ∧
    ∀ slot ∈ spec.slots, slot.choices ≠ [] ∧ (slot.choices.map Choice.id).Nodup

def wellFormed (spec : FamilySpec) : Bool :=
  decide (spec.slots.map Slot.id).Nodup && spec.slots.all fun slot =>
    !slot.choices.isEmpty && decide (slot.choices.map Choice.id).Nodup

theorem wellFormed_iff (spec : FamilySpec) :
    wellFormed spec = true ↔ WellFormed spec := by
  simp [wellFormed, WellFormed]

/-- Ordered Cartesian product: earlier slots and earlier alternatives come first. -/
def product : List Slot → List (List Selection)
  | [] => [[]]
  | slot :: rest =>
      match slot.choices with
      | [] => []
      | choices@(_ :: _) =>
          let suffixes := product rest
          choices.flatMap fun choice => suffixes.map (Selection.mk slot.id choice :: ·)

private theorem product_cons (slot : Slot) (rest : List Slot) :
    product (slot :: rest) = slot.choices.flatMap (fun choice =>
      (product rest).map (Selection.mk slot.id choice :: ·)) := by
  cases choices : slot.choices <;> simp [product, choices]

def guardsHold (history : ProcessHistory) (assignment : List Selection) : Bool :=
  assignment.all fun selection => selection.choice.guard.eval history

/-- Independently stated relation: exactly one declared choice for each slot in
slot order, with every chosen guard true of the same history. -/
def Chooses (history : ProcessHistory) : List Slot → List Selection → Prop
  | [], [] => True
  | slot :: slots, selection :: assignment =>
      selection.slot = slot.id ∧ selection.choice ∈ slot.choices ∧
      selection.choice.guard.Holds history ∧ Chooses history slots assignment
  | _, _ => False

private theorem mem_product_guards (history : ProcessHistory) (slots : List Slot)
    (assignment : List Selection) :
    (assignment ∈ product slots ∧ guardsHold history assignment = true) ↔
      Chooses history slots assignment := by
  induction slots generalizing assignment with
  | nil => cases assignment <;> simp [product, guardsHold, Chooses]
  | cons slot slots ih =>
    rw [product_cons]
    cases assignment with
    | nil => simp [Chooses]
    | cons selection assignment =>
      simp only [List.mem_flatMap, List.mem_map, List.cons.injEq,
        guardsHold, List.all_cons, Bool.and_eq_true, Guard.eval_iff, Chooses]
      constructor
      · rintro ⟨⟨choice, member, tail, htail, equal, rfl⟩, guard, guards⟩
        cases equal
        exact ⟨rfl, member, guard, (ih _).mp ⟨htail, guards⟩⟩
      · rintro ⟨equal, member, guard, chosen⟩
        obtain ⟨htail, guards⟩ := (ih _).mpr chosen
        refine ⟨⟨selection.choice, member, assignment, htail, ?_, rfl⟩, guard, guards⟩
        cases selection
        simp_all

/-- No acceptance filter: source-rejected completions are still family members. -/
def referenceFamily (spec : FamilySpec) : List Completion :=
  match spec.problem.completions with
  | [] => []
  | histories@(_ :: _) =>
      let assignments := product spec.slots
      histories.flatMap fun history =>
        (assignments.filter (guardsHold history)).map (Completion.mk history)

private theorem referenceFamily_eq (spec : FamilySpec) :
    referenceFamily spec = spec.problem.completions.flatMap (fun history =>
      ((product spec.slots).filter (guardsHold history)).map (Completion.mk history)) := by
  cases histories : spec.problem.completions <;> simp [referenceFamily, histories]

theorem mem_referenceFamily (spec : FamilySpec) (completion : Completion) :
    completion ∈ referenceFamily spec ↔
      completion.history ∈ spec.problem.completions ∧
        Chooses completion.history spec.slots completion.assignment := by
  cases completion with
  | mk history assignment =>
    simp only [referenceFamily_eq, List.mem_flatMap, List.mem_map, List.mem_filter,
      Completion.mk.injEq]
    constructor
    · rintro ⟨h, member, a, valid, rfl, rfl⟩
      exact ⟨member, (mem_product_guards _ _ _).mp valid⟩
    · rintro ⟨member, chosen⟩
      exact ⟨history, member, assignment, (mem_product_guards _ _ _).mpr chosen, rfl, rfl⟩

private theorem product_nodup (slots : List Slot)
    (unique : ∀ slot ∈ slots, (slot.choices.map Choice.id).Nodup) :
    (product slots).Nodup := by
  induction slots with
  | nil => simp [product]
  | cons slot slots ih =>
    rw [product_cons]
    have tail := ih (fun slot member => unique slot (List.mem_cons_of_mem _ member))
    have choices : slot.choices.Nodup :=
      (unique slot List.mem_cons_self).of_map Choice.id
    apply List.nodup_flatMap.mpr
    constructor
    · intro choice _
      exact tail.map (fun _ _ equal => (List.cons.inj equal).2)
    · apply choices.imp
      intro left right different assignment hleft hright
      obtain ⟨a, _, ha⟩ := List.mem_map.mp hleft
      obtain ⟨b, _, hb⟩ := List.mem_map.mp hright
      have equal : Selection.mk slot.id left = Selection.mk slot.id right :=
        (List.cons.inj (ha.trans hb.symm)).1
      exact different (congrArg Selection.choice equal)

theorem referenceFamily_nodup (spec : FamilySpec) (wf : wellFormed spec = true) :
    (referenceFamily spec).Nodup := by
  rw [referenceFamily_eq]
  have unique := product_nodup spec.slots
    (fun slot member => ((wellFormed_iff spec).mp wf).2 slot member |>.2)
  apply List.nodup_flatMap.mpr
  constructor
  · intro history _
    exact (unique.filter _).map (fun _ _ equal => congrArg Completion.assignment equal)
  · apply spec.problem.completions_nodup.imp
    intro left right different completion hleft hright
    obtain ⟨a, _, ha⟩ := List.mem_map.mp hleft
    obtain ⟨b, _, hb⟩ := List.mem_map.mp hright
    exact different (congrArg Completion.history (ha.trans hb.symm))

theorem referenceFamily_no_slots (problem : Universe.Problem) (base : Source.SourceInput) :
    referenceFamily ⟨problem, base, []⟩ = problem.completions.map (fun h => ⟨h, []⟩) := by
  rw [referenceFamily_eq]
  change (problem.completions.flatMap fun h => [Completion.mk h []]) = _
  exact List.map_eq_flatMap.symm

theorem referenceFamily_no_slots_projection (problem : Universe.Problem)
    (base : Source.SourceInput) :
    (referenceFamily ⟨problem, base, []⟩).map Completion.history = problem.completions := by
  rw [referenceFamily_no_slots]
  simp [List.map_map, Function.comp_def]

/-- Every fragment is appended once, in slot and declaration order. -/
def selectedDecls (completion : Completion) : List Presentation.Decl :=
  completion.assignment.flatMap fun selection => selection.choice.fragment

def materialize (spec : FamilySpec) (completion : Completion) : Source.SourceInput :=
  { spec.base with surface := { spec.base.surface with
      program := { spec.base.surface.program with
        decls := spec.base.surface.program.decls ++ selectedDecls completion } } }

theorem materialize_decls (spec : FamilySpec) (completion : Completion) :
    (materialize spec completion).surface.program.decls =
      spec.base.surface.program.decls ++ selectedDecls completion := rfl

/-- All non-declaration program fields, policy, replay and capture stay common. -/
theorem materialize_common (spec : FamilySpec) (completion : Completion) :
    (materialize spec completion).surface.policy = spec.base.surface.policy ∧
    (materialize spec completion).replay = spec.base.replay ∧
    (materialize spec completion).capture = spec.base.capture ∧
    { (materialize spec completion).surface.program with
      decls := spec.base.surface.program.decls } = spec.base.surface.program := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Source contribution keys include the arguments introduced by comparisons.
This identifies hypothetical inputs; dependency propagation is checked separately. -/
def declarationKeys : Presentation.Decl → List Source.KindKey
  | .leaf leaf => [.leaf leaf.id]
  | .arg argument => [.argument argument.id]
  | .comparison comparison => [.argument comparison.recheckArg, .argument comparison.bridgeArg]
  | _ => []

def selectedKeys (completion : Completion) : List Source.KindKey :=
  (selectedDecls completion).flatMap declarationKeys

theorem mem_selectedKeys (completion : Completion) (key : Source.KindKey) :
    key ∈ selectedKeys completion ↔
      (∃ leaf, Presentation.Decl.leaf leaf ∈ selectedDecls completion ∧
        key = .leaf leaf.id) ∨
      (∃ argument, Presentation.Decl.arg argument ∈ selectedDecls completion ∧
        key = .argument argument.id) ∨
      (∃ comparison, Presentation.Decl.comparison comparison ∈ selectedDecls completion ∧
        (key = .argument comparison.recheckArg ∨ key = .argument comparison.bridgeArg)) := by
  constructor
  · intro member
    obtain ⟨declaration, member, used⟩ := List.mem_flatMap.mp member
    cases declaration <;> simp only [declarationKeys, List.mem_nil_iff,
      List.mem_cons, or_false] at used
    · exact Or.inl ⟨_, member, used⟩
    · exact Or.inr (Or.inl ⟨_, member, used⟩)
    · exact Or.inr (Or.inr ⟨_, member, used⟩)
  · rintro (⟨leaf, member, rfl⟩ | ⟨argument, member, rfl⟩ | ⟨comparison, member, used⟩)
    · exact List.mem_flatMap.mpr ⟨.leaf leaf, member, List.mem_singleton_self _⟩
    · exact List.mem_flatMap.mpr ⟨.arg argument, member, List.mem_singleton_self _⟩
    · exact List.mem_flatMap.mpr ⟨.comparison comparison, member, by
        simpa only [declarationKeys, List.mem_cons, List.mem_nil_iff, or_false] using used⟩

/-- Comparison-generated arguments remain hypothetical regardless of producer
metadata, admitted capture assumptions, or the kind of their support terms. -/
theorem comparison_nodeKind_hypothetical (spec : FamilySpec) (completion : Completion)
    (comparison : Presentation.Comparison) (argument : Presentation.ArgId)
    (selected : Presentation.Decl.comparison comparison ∈ selectedDecls completion)
    (generated : argument = comparison.recheckArg ∨ argument = comparison.bridgeArg)
    (specs : List Source.KindSpec) (assumptions : List Source.CaptureAssumption)
    (admitted : List AdmissionBasis) (term : Support.SupportTerm) :
    (Source.nodeKind (materialize spec completion) completion.history specs assumptions
      admitted (selectedKeys completion) argument term).1 = .hypothetical := by
  apply Source.nodeKind_no_promotion (key := .argument argument)
    (used := List.mem_cons_self)
  apply (mem_selectedKeys completion (.argument argument)).mpr
  right
  right
  refine ⟨comparison, selected, ?_⟩
  rcases generated with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

end Lara.Process.Family
