/-
Binding and typed-renaming laws for the presentation surface.
-/

import Lara.Presentation

namespace Lara.Surface.Binding

open Lara
open Lara.Presentation

/-! ### Rule parameters -/

mutual
  def freeParamsPat : Pat → List Param
    | .var param => [param]
    | .lit _ => []
    | .con _ args => freeParamsPats args
  def freeParamsPats : Pats → List Param
    | .nil => []
    | .cons pat rest => freeParamsPat pat ++ freeParamsPats rest
end

def freeParamsAtomPat (atom : AtomPat) : List Param :=
  freeParamsPats atom.args

def freeParamsRule (rule : Rule) : List Param :=
  (rule.premises.flatMap freeParamsAtomPat) ++
    freeParamsAtomPat rule.conclusion ++
    rule.questions.flatMap (fun question => freeParamsAtomPat question.answer)

mutual
  def substPat (target : Param) (replacement : Pat) : Pat → Pat
    | .var param => if param = target then replacement else .var param
    | .lit term => .lit term
    | .con name args => .con name (substPats target replacement args)
  def substPats (target : Param) (replacement : Pat) : Pats → Pats
    | .nil => .nil
    | .cons pat rest =>
        .cons (substPat target replacement pat)
          (substPats target replacement rest)
end

def substAtomPat (target : Param) (replacement : Pat)
    (atom : AtomPat) : AtomPat :=
  ⟨atom.pred, substPats target replacement atom.args⟩

private def substQuestion (target : Param) (replacement : Pat)
    (question : Question) : Question :=
  { question with answer := substAtomPat target replacement question.answer }

private def replacementParams (replacement : Pat) : List Param :=
  (freeParamsPat replacement).eraseDups

private def substParamList (target : Param) (replacement : Pat) :
    List Param → List Param
  | [] => []
  | param :: rest =>
      if param = target then
        replacementParams replacement ++ substParamList target replacement rest
      else param :: substParamList target replacement rest

private def captures (target : Param) (replacement : Pat)
    (params : List Param) : Bool :=
  (replacementParams replacement).any fun param =>
    param != target && (params.erase target).contains param

/-- Substitute one declared rule parameter by a presentation pattern.  Free
parameters of the replacement are spliced into the declaration at the old
parameter's position.  The operation fails exactly when an existing distinct
rule parameter would capture one of those free names. -/
def substParam (target : Param) (replacement : Pat) (rule : Rule) : Option Rule :=
  if rule.params.contains target then
    if captures target replacement rule.params then none
    else
      some
        { rule with
          params := substParamList target replacement rule.params
          premises := rule.premises.map (substAtomPat target replacement)
          conclusion := substAtomPat target replacement rule.conclusion
          questions := rule.questions.map (substQuestion target replacement) }
  else some rule

/-- Binding-level well-sortedness: every parameter occurrence in a rule body is
accounted for by the rule's declared parameter scope. -/
def WellSorted (rule : Rule) : Prop :=
  ∀ param, param ∈ freeParamsRule rule → param ∈ rule.params

@[simp] theorem substParam_fresh_identity (target : Param)
    (replacement : Pat) (rule : Rule) (fresh : target ∉ rule.params) :
    substParam target replacement rule = some rule := by
  simp [substParam, fresh]

mutual
  private theorem mem_freeParams_substPat (target : Param) (replacement : Pat)
      (pat : Pat) (param : Param) :
      param ∈ freeParamsPat (substPat target replacement pat) ↔
        (param ≠ target ∧ param ∈ freeParamsPat pat) ∨
        (target ∈ freeParamsPat pat ∧ param ∈ freeParamsPat replacement) := by
    cases pat with
    | var source =>
        by_cases h : source = target
        · subst source
          simp [substPat, freeParamsPat]
        · simp [substPat, freeParamsPat, h]
          grind
    | lit term => simp [substPat, freeParamsPat]
    | con name args =>
        simpa [substPat, freeParamsPat] using
          mem_freeParams_substPats target replacement args param
  private theorem mem_freeParams_substPats (target : Param) (replacement : Pat)
      (pats : Pats) (param : Param) :
      param ∈ freeParamsPats (substPats target replacement pats) ↔
        (param ≠ target ∧ param ∈ freeParamsPats pats) ∨
        (target ∈ freeParamsPats pats ∧ param ∈ freeParamsPat replacement) := by
    cases pats with
    | nil => simp [substPats, freeParamsPats]
    | cons pat rest =>
        simp only [substPats, freeParamsPats, List.mem_append]
        rw [mem_freeParams_substPat, mem_freeParams_substPats]
        grind
end

private theorem mem_freeParams_substAtomPat (target : Param)
    (replacement : Pat) (atom : AtomPat) (param : Param) :
    param ∈ freeParamsAtomPat (substAtomPat target replacement atom) ↔
      (param ≠ target ∧ param ∈ freeParamsAtomPat atom) ∨
      (target ∈ freeParamsAtomPat atom ∧ param ∈ freeParamsPat replacement) := by
  cases atom
  exact mem_freeParams_substPats target replacement _ param

mutual
  private theorem substPat_eq_self_of_fresh (target : Param)
      (replacement pat : Pat) (fresh : target ∉ freeParamsPat pat) :
      substPat target replacement pat = pat := by
    cases pat with
    | var source =>
        simp only [freeParamsPat, List.mem_singleton] at fresh
        have different : source ≠ target := fun equal => fresh equal.symm
        simp [substPat, different]
    | lit term => rfl
    | con name args =>
        simp only [freeParamsPat] at fresh
        simp [substPat, substPats_eq_self_of_fresh target replacement args fresh]
  private theorem substPats_eq_self_of_fresh (target : Param)
      (replacement : Pat) (pats : Pats) (fresh : target ∉ freeParamsPats pats) :
      substPats target replacement pats = pats := by
    cases pats with
    | nil => rfl
    | cons pat rest =>
        simp only [freeParamsPats, List.mem_append, not_or] at fresh
        simp [substPats, substPat_eq_self_of_fresh target replacement pat fresh.1,
          substPats_eq_self_of_fresh target replacement rest fresh.2]
end

mutual
  /-- Ordinary capture-free substitution composition on presentation
  patterns. -/
  theorem substPat_compose_of_fresh (first second : Param)
      (firstReplacement secondReplacement pat : Pat)
      (distinct : first ≠ second)
      (fresh : first ∉ freeParamsPat secondReplacement) :
      substPat second secondReplacement
          (substPat first firstReplacement pat) =
        substPat first (substPat second secondReplacement firstReplacement)
          (substPat second secondReplacement pat) := by
    cases pat with
    | var param =>
        by_cases hfirst : param = first
        · subst param
          simp [substPat, distinct]
        · by_cases hsecond : param = second
          · subst param
            simp only [substPat, hfirst, ↓reduceIte]
            exact (substPat_eq_self_of_fresh first
              (substPat second secondReplacement firstReplacement)
              secondReplacement fresh).symm
          · simp [substPat, hfirst, hsecond]
    | lit term => rfl
    | con name args =>
        simp only [substPat, Pat.con.injEq, true_and]
        exact substPats_compose_of_fresh first second firstReplacement
          secondReplacement args distinct fresh
  private theorem substPats_compose_of_fresh (first second : Param)
      (firstReplacement secondReplacement : Pat) (pats : Pats)
      (distinct : first ≠ second)
      (fresh : first ∉ freeParamsPat secondReplacement) :
      substPats second secondReplacement
          (substPats first firstReplacement pats) =
        substPats first (substPat second secondReplacement firstReplacement)
          (substPats second secondReplacement pats) := by
    cases pats with
    | nil => rfl
    | cons pat rest =>
        simp only [substPats, Pats.cons.injEq]
        exact ⟨substPat_compose_of_fresh first second firstReplacement
          secondReplacement pat distinct fresh,
          substPats_compose_of_fresh first second firstReplacement
            secondReplacement rest distinct fresh⟩
end

private theorem substAtomPat_compose_of_fresh (first second : Param)
    (firstReplacement secondReplacement : Pat) (atom : AtomPat)
    (distinct : first ≠ second)
    (fresh : first ∉ freeParamsPat secondReplacement) :
    substAtomPat second secondReplacement
        (substAtomPat first firstReplacement atom) =
      substAtomPat first
        (substPat second secondReplacement firstReplacement)
        (substAtomPat second secondReplacement atom) := by
  cases atom
  simp [substAtomPat,
    substPats_compose_of_fresh first second firstReplacement
      secondReplacement _ distinct fresh]

private theorem substQuestion_compose_of_fresh (first second : Param)
    (firstReplacement secondReplacement : Pat) (question : Question)
    (distinct : first ≠ second)
    (fresh : first ∉ freeParamsPat secondReplacement) :
    substQuestion second secondReplacement
        (substQuestion first firstReplacement question) =
      substQuestion first
        (substPat second secondReplacement firstReplacement)
        (substQuestion second secondReplacement question) := by
  cases question
  simp [substQuestion,
    substAtomPat_compose_of_fresh first second firstReplacement
      secondReplacement _ distinct fresh]

/-- Composition for the public partial rule substitution.  The Boolean
hypotheses expose the four capture checks and scope-membership checks performed
by the two evaluation orders; `paramsCompose` is the structural agreement of
their declaration-list splices. -/
theorem substParam_compose_of_fresh (first second : Param)
    (firstReplacement secondReplacement : Pat) (rule : Rule)
    (distinct : first ≠ second)
    (fresh : first ∉ freeParamsPat secondReplacement)
    (firstMember : rule.params.contains first = true)
    (firstNoCapture : captures first firstReplacement rule.params = false)
    (secondAfterFirstMember :
      (substParamList first firstReplacement rule.params).contains second = true)
    (secondAfterFirstNoCapture :
      captures second secondReplacement
        (substParamList first firstReplacement rule.params) = false)
    (secondMember : rule.params.contains second = true)
    (secondNoCapture : captures second secondReplacement rule.params = false)
    (firstAfterSecondMember :
      (substParamList second secondReplacement rule.params).contains first = true)
    (firstAfterSecondNoCapture :
      captures first (substPat second secondReplacement firstReplacement)
        (substParamList second secondReplacement rule.params) = false)
    (paramsCompose :
      substParamList second secondReplacement
          (substParamList first firstReplacement rule.params) =
        substParamList first
          (substPat second secondReplacement firstReplacement)
          (substParamList second secondReplacement rule.params)) :
    (substParam first firstReplacement rule).bind
        (substParam second secondReplacement) =
      (substParam second secondReplacement rule).bind
        (substParam first
          (substPat second secondReplacement firstReplacement)) := by
  simp only [substParam, firstMember, firstNoCapture, secondMember,
    secondNoCapture, ↓reduceIte]
  simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_some]
  simp only [substParam, secondAfterFirstMember, secondAfterFirstNoCapture,
    firstAfterSecondMember, firstAfterSecondNoCapture, ↓reduceIte,
    Bool.false_eq_true]
  apply congrArg some
  cases rule
  simp only [Rule.mk.injEq, paramsCompose, true_and, List.map_map]
  constructor
  · apply List.map_congr_left
    intro atom _
    exact substAtomPat_compose_of_fresh first second firstReplacement
      secondReplacement atom distinct fresh
  constructor
  · exact substAtomPat_compose_of_fresh first second firstReplacement
      secondReplacement _ distinct fresh
  · apply List.map_congr_left
    intro question _
    exact substQuestion_compose_of_fresh first second firstReplacement
      secondReplacement question distinct fresh

private theorem mem_replacementParams {replacement : Pat} {param : Param} :
    param ∈ replacementParams replacement ↔
      param ∈ freeParamsPat replacement := by
  simp [replacementParams]

private theorem mem_substParamList_old {target : Param} {replacement : Pat}
    {params : List Param} {param : Param}
    (member : param ∈ params) (different : param ≠ target) :
    param ∈ substParamList target replacement params := by
  induction params with
  | nil => contradiction
  | cons head rest ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp [substParamList, different]
      · by_cases hhead : head = target
        · simp [substParamList, hhead, ih member]
        · simp [substParamList, hhead, ih member]

private theorem mem_substParamList_new {target : Param} {replacement : Pat}
    {params : List Param} (targetMember : target ∈ params) {param : Param}
    (member : param ∈ freeParamsPat replacement) :
    param ∈ substParamList target replacement params := by
  induction params with
  | nil => contradiction
  | cons head rest ih =>
      simp only [List.mem_cons] at targetMember
      rcases targetMember with rfl | targetMember
      · simp [substParamList, mem_replacementParams.mpr member]
      · by_cases hhead : head = target
        · simp [substParamList, hhead, mem_replacementParams.mpr member]
        · simp [substParamList, hhead, ih targetMember]

private theorem mem_freeParamsRule_substBody
    (target : Param) (replacement : Pat) (rule : Rule) (param : Param) :
    param ∈ freeParamsRule
      { rule with
        params := substParamList target replacement rule.params
        premises := rule.premises.map (substAtomPat target replacement)
        conclusion := substAtomPat target replacement rule.conclusion
        questions := rule.questions.map (substQuestion target replacement) } ↔
      (param ≠ target ∧ param ∈ freeParamsRule rule) ∨
      (target ∈ freeParamsRule rule ∧ param ∈ freeParamsPat replacement) := by
  simp only [freeParamsRule, List.flatMap_map,
    List.mem_append, List.mem_flatMap,
    mem_freeParams_substAtomPat, substQuestion]
  grind

/-- Capture-avoiding parameter substitution preserves binding-level
well-sortedness. -/
theorem substParam_preserves_wellSorted {target : Param} {replacement : Pat}
    {rule result : Rule} (sorted : WellSorted rule)
    (substituted : substParam target replacement rule = some result) :
    WellSorted result := by
  unfold substParam at substituted
  split at substituted
  next targetMember =>
    split at substituted
    next => contradiction
    next =>
      simp only [Option.some.injEq] at substituted
      subst result
      intro param member
      rw [mem_freeParamsRule_substBody] at member
      rcases member with old | new
      · exact mem_substParamList_old (sorted param old.2) old.1
      · exact mem_substParamList_new
          (target := target) (replacement := replacement)
          (params := rule.params) (param := param)
          (by simpa using targetMember) new.2
  next =>
    simp only [Option.some.injEq] at substituted
    subst result
    exact sorted

/-! ### Rule alpha-equivalence -/

inductive ParamRef where
  | bound : Nat → ParamRef
  | free : Param → ParamRef
deriving DecidableEq

mutual
  inductive AlphaPat where
    | var : ParamRef → AlphaPat
    | lit : Term → AlphaPat
    | con : String → AlphaPats → AlphaPat
  inductive AlphaPats where
    | nil : AlphaPats
    | cons : AlphaPat → AlphaPats → AlphaPats
end
deriving instance DecidableEq for AlphaPat, AlphaPats

structure AlphaAtomPat where
  pred : String
  args : AlphaPats
deriving DecidableEq

structure AlphaQuestion where
  id : QuestionId
  answer : AlphaAtomPat
  necessity : Necessity
deriving DecidableEq

structure RuleView where
  id : RuleId
  paramCount : Nat
  paramAliases : List Nat
  mode : Mode
  premises : List AlphaAtomPat
  premiseLabels : List (Option PremiseLabel)
  conclusion : AlphaAtomPat
  allowTrusted : Bool
  certifiers : List CertRef
  questions : List AlphaQuestion
deriving DecidableEq

private def paramIndex (sought : Param) : List Param → Option Nat
  | [] => none
  | param :: rest =>
      if param = sought then some 0 else (paramIndex sought rest).map Nat.succ

/-- The first declaration slot occupied by each parameter occurrence.  Unlike
`paramCount`, this retains duplicate/aliasing patterns such as `[X, X]`. -/
private def paramAliases (params : List Param) : List Nat :=
  params.map fun param => (paramIndex param params).getD params.length

mutual
  private def abstractPat (params : List Param) : Pat → AlphaPat
    | .var param =>
        match paramIndex param params with
        | some index => .var (.bound index)
        | none => .var (.free param)
    | .lit term => .lit term
    | .con name args => .con name (abstractPats params args)
  private def abstractPats (params : List Param) : Pats → AlphaPats
    | .nil => .nil
    | .cons pat rest =>
        .cons (abstractPat params pat) (abstractPats params rest)
end

private def abstractAtomPat (params : List Param) (atom : AtomPat) : AlphaAtomPat :=
  ⟨atom.pred, abstractPats params atom.args⟩

private def abstractQuestion (params : List Param) (question : Question) : AlphaQuestion :=
  ⟨question.id, abstractAtomPat params question.answer, question.necessity⟩

def ruleView (rule : Rule) : RuleView :=
  { id := rule.id
    paramCount := rule.params.length
    paramAliases := paramAliases rule.params
    mode := rule.mode
    premises := rule.premises.map (abstractAtomPat rule.params)
    premiseLabels := rule.premiseLabels
    conclusion := abstractAtomPat rule.params rule.conclusion
    allowTrusted := rule.allowTrusted
    certifiers := rule.certifiers
    questions := rule.questions.map (abstractQuestion rule.params) }

def RuleAlpha (left right : Rule) : Prop :=
  ruleView left = ruleView right

theorem ruleAlpha_refl (rule : Rule) : RuleAlpha rule rule := rfl

theorem ruleAlpha_symm {left right : Rule} :
    RuleAlpha left right → RuleAlpha right left := Eq.symm

theorem ruleAlpha_trans {left middle right : Rule} :
    RuleAlpha left middle → RuleAlpha middle right → RuleAlpha left right := Eq.trans

/-! ### Typed global renaming -/

structure GlobalRenaming where
  prop : PropId → PropId
  question : QuestionId → QuestionId
  leaf : LeafId → LeafId
  rule : RuleId → RuleId
  arg : ArgId → ArgId
  argRef : ArgRef → ArgRef
  obligation : ObligationId → ObligationId
  source : SourceRef → SourceRef
  group : GroupId → GroupId
  measurand : MeasurandId → MeasurandId
  dataset : DatasetId → DatasetId
  premiseLabel : PremiseLabel → PremiseLabel
  valueName : ValueName → ValueName
  prop_injective : Function.Injective prop
  question_injective : Function.Injective question
  leaf_injective : Function.Injective leaf
  rule_injective : Function.Injective rule
  arg_injective : Function.Injective arg
  argRef_injective : Function.Injective argRef
  obligation_injective : Function.Injective obligation
  source_injective : Function.Injective source
  group_injective : Function.Injective group
  measurand_injective : Function.Injective measurand
  dataset_injective : Function.Injective dataset
  premiseLabel_injective : Function.Injective premiseLabel
  valueName_injective : Function.Injective valueName
  question_coherent : ∀ x, (question x).val = (prop ⟨x.val⟩).val
  leaf_coherent : ∀ x, (leaf x).val = (prop ⟨x.val⟩).val
  rule_coherent : ∀ x, (rule x).val = (prop ⟨x.val⟩).val
  arg_coherent : ∀ x, (arg x).val = (prop ⟨x.val⟩).val
  argRef_coherent : ∀ x, (argRef x).val = (prop ⟨x.val⟩).val
  obligation_coherent : ∀ x, (obligation x).val = (prop ⟨x.val⟩).val
  group_coherent : ∀ x, (group x).val = (prop ⟨x.val⟩).val
  measurand_coherent : ∀ x, (measurand x).val = (prop ⟨x.val⟩).val
  dataset_coherent : ∀ x, (dataset x).val = (prop ⟨x.val⟩).val
  premiseLabel_coherent :
    ∀ x, (premiseLabel x).val = (prop ⟨x.val⟩).val
  valueName_coherent : ∀ x, (valueName x).val = (prop ⟨x.val⟩).val


namespace GlobalRenaming

protected def id : GlobalRenaming where
  prop := id
  question := id
  leaf := id
  rule := id
  arg := id
  argRef := id
  obligation := id
  source := id
  group := id
  measurand := id
  dataset := id
  premiseLabel := id
  valueName := id
  prop_injective := fun _ _ equal => equal
  question_injective := fun _ _ equal => equal
  leaf_injective := fun _ _ equal => equal
  rule_injective := fun _ _ equal => equal
  arg_injective := fun _ _ equal => equal
  argRef_injective := fun _ _ equal => equal
  obligation_injective := fun _ _ equal => equal
  source_injective := fun _ _ equal => equal
  group_injective := fun _ _ equal => equal
  measurand_injective := fun _ _ equal => equal
  dataset_injective := fun _ _ equal => equal
  premiseLabel_injective := fun _ _ equal => equal
  valueName_injective := fun _ _ equal => equal
  question_coherent := fun _ => rfl
  leaf_coherent := fun _ => rfl
  rule_coherent := fun _ => rfl
  arg_coherent := fun _ => rfl
  argRef_coherent := fun _ => rfl
  obligation_coherent := fun _ => rfl
  group_coherent := fun _ => rfl
  measurand_coherent := fun _ => rfl
  dataset_coherent := fun _ => rfl
  premiseLabel_coherent := fun _ => rfl
  valueName_coherent := fun _ => rfl

/-- A nontrivial renaming family for metadata-only source references. -/
def sourceOnly (f : SourceRef → SourceRef) (injective : Function.Injective f) :
    GlobalRenaming :=
  { GlobalRenaming.id with
    source := f
    source_injective := injective }

@[simp] theorem sourceOnly_prop (f) (hf) (x : PropId) :
    (sourceOnly f hf).prop x = x := rfl
@[simp] theorem sourceOnly_question (f) (hf) (x : QuestionId) :
    (sourceOnly f hf).question x = x := rfl
@[simp] theorem sourceOnly_leaf (f) (hf) (x : LeafId) :
    (sourceOnly f hf).leaf x = x := rfl
@[simp] theorem sourceOnly_rule (f) (hf) (x : RuleId) :
    (sourceOnly f hf).rule x = x := rfl
@[simp] theorem sourceOnly_arg (f) (hf) (x : ArgId) :
    (sourceOnly f hf).arg x = x := rfl
@[simp] theorem sourceOnly_argRef (f) (hf) (x : ArgRef) :
    (sourceOnly f hf).argRef x = x := rfl
@[simp] theorem sourceOnly_obligation (f) (hf) (x : ObligationId) :
    (sourceOnly f hf).obligation x = x := rfl
@[simp] theorem sourceOnly_source (f) (hf) (x : SourceRef) :
    (sourceOnly f hf).source x = f x := rfl
@[simp] theorem sourceOnly_group (f) (hf) (x : GroupId) :
    (sourceOnly f hf).group x = x := rfl
@[simp] theorem sourceOnly_measurand (f) (hf) (x : MeasurandId) :
    (sourceOnly f hf).measurand x = x := rfl
@[simp] theorem sourceOnly_dataset (f) (hf) (x : DatasetId) :
    (sourceOnly f hf).dataset x = x := rfl
@[simp] theorem sourceOnly_premiseLabel (f) (hf) (x : PremiseLabel) :
    (sourceOnly f hf).premiseLabel x = x := rfl
@[simp] theorem sourceOnly_valueName (f) (hf) (x : ValueName) :
    (sourceOnly f hf).valueName x = x := rfl
@[simp] theorem sourceOnly_valueName_fun (f) (hf) :
    (sourceOnly f hf).valueName = id := rfl
@[simp] theorem sourceOnly_prop_fun (f) (hf) :
    (sourceOnly f hf).prop = id := rfl
@[simp] theorem sourceOnly_question_fun (f) (hf) :
    (sourceOnly f hf).question = id := rfl
@[simp] theorem sourceOnly_leaf_fun (f) (hf) :
    (sourceOnly f hf).leaf = id := rfl
@[simp] theorem sourceOnly_rule_fun (f) (hf) :
    (sourceOnly f hf).rule = id := rfl
@[simp] theorem sourceOnly_arg_fun (f) (hf) :
    (sourceOnly f hf).arg = id := rfl
@[simp] theorem sourceOnly_argRef_fun (f) (hf) :
    (sourceOnly f hf).argRef = id := rfl
@[simp] theorem sourceOnly_obligation_fun (f) (hf) :
    (sourceOnly f hf).obligation = id := rfl
@[simp] theorem sourceOnly_group_fun (f) (hf) :
    (sourceOnly f hf).group = id := rfl
@[simp] theorem sourceOnly_measurand_fun (f) (hf) :
    (sourceOnly f hf).measurand = id := rfl
@[simp] theorem sourceOnly_dataset_fun (f) (hf) :
    (sourceOnly f hf).dataset = id := rfl
@[simp] theorem sourceOnly_premiseLabel_fun (f) (hf) :
    (sourceOnly f hf).premiseLabel = id := rfl

protected def comp (after before : GlobalRenaming) : GlobalRenaming where
  prop := after.prop ∘ before.prop
  question := after.question ∘ before.question
  leaf := after.leaf ∘ before.leaf
  rule := after.rule ∘ before.rule
  arg := after.arg ∘ before.arg
  argRef := after.argRef ∘ before.argRef
  obligation := after.obligation ∘ before.obligation
  source := after.source ∘ before.source
  group := after.group ∘ before.group
  measurand := after.measurand ∘ before.measurand
  dataset := after.dataset ∘ before.dataset
  premiseLabel := after.premiseLabel ∘ before.premiseLabel
  valueName := after.valueName ∘ before.valueName
  prop_injective := after.prop_injective.comp before.prop_injective
  question_injective := after.question_injective.comp before.question_injective
  leaf_injective := after.leaf_injective.comp before.leaf_injective
  rule_injective := after.rule_injective.comp before.rule_injective
  arg_injective := after.arg_injective.comp before.arg_injective
  argRef_injective := after.argRef_injective.comp before.argRef_injective
  obligation_injective :=
    after.obligation_injective.comp before.obligation_injective
  source_injective := after.source_injective.comp before.source_injective
  group_injective := after.group_injective.comp before.group_injective
  measurand_injective :=
    after.measurand_injective.comp before.measurand_injective
  dataset_injective := after.dataset_injective.comp before.dataset_injective
  premiseLabel_injective :=
    after.premiseLabel_injective.comp before.premiseLabel_injective
  valueName_injective :=
    after.valueName_injective.comp before.valueName_injective
  question_coherent := by
    intro x
    calc
      _ = (after.prop ⟨(before.question x).val⟩).val :=
        after.question_coherent _
      _ = (after.prop ⟨(before.prop ⟨x.val⟩).val⟩).val := by
        rw [before.question_coherent]
      _ = _ := rfl
  leaf_coherent := by
    intro x
    calc
      _ = (after.prop ⟨(before.leaf x).val⟩).val := after.leaf_coherent _
      _ = (after.prop ⟨(before.prop ⟨x.val⟩).val⟩).val := by
        rw [before.leaf_coherent]
      _ = _ := rfl
  rule_coherent := by
    intro x
    calc
      _ = (after.prop ⟨(before.rule x).val⟩).val := after.rule_coherent _
      _ = (after.prop ⟨(before.prop ⟨x.val⟩).val⟩).val := by
        rw [before.rule_coherent]
      _ = _ := rfl
  arg_coherent := by
    intro x
    calc
      _ = (after.prop ⟨(before.arg x).val⟩).val := after.arg_coherent _
      _ = (after.prop ⟨(before.prop ⟨x.val⟩).val⟩).val := by
        rw [before.arg_coherent]
      _ = _ := rfl
  argRef_coherent := by
    intro x
    calc
      _ = (after.prop ⟨(before.argRef x).val⟩).val :=
        after.argRef_coherent _
      _ = (after.prop ⟨(before.prop ⟨x.val⟩).val⟩).val := by
        rw [before.argRef_coherent]
      _ = _ := rfl
  obligation_coherent := by
    intro x
    calc
      _ = (after.prop ⟨(before.obligation x).val⟩).val :=
        after.obligation_coherent _
      _ = (after.prop ⟨(before.prop ⟨x.val⟩).val⟩).val := by
        rw [before.obligation_coherent]
      _ = _ := rfl
  group_coherent := by
    intro x
    calc
      _ = (after.prop ⟨(before.group x).val⟩).val := after.group_coherent _
      _ = (after.prop ⟨(before.prop ⟨x.val⟩).val⟩).val := by
        rw [before.group_coherent]
      _ = _ := rfl
  measurand_coherent := by
    intro x
    calc
      _ = (after.prop ⟨(before.measurand x).val⟩).val :=
        after.measurand_coherent _
      _ = (after.prop ⟨(before.prop ⟨x.val⟩).val⟩).val := by
        rw [before.measurand_coherent]
      _ = _ := rfl
  dataset_coherent := by
    intro x
    calc
      _ = (after.prop ⟨(before.dataset x).val⟩).val := after.dataset_coherent _
      _ = (after.prop ⟨(before.prop ⟨x.val⟩).val⟩).val := by
        rw [before.dataset_coherent]
      _ = _ := rfl
  premiseLabel_coherent := by
    intro x
    calc
      _ = (after.prop ⟨(before.premiseLabel x).val⟩).val :=
        after.premiseLabel_coherent _
      _ = (after.prop ⟨(before.prop ⟨x.val⟩).val⟩).val := by
        rw [before.premiseLabel_coherent]
      _ = _ := rfl
  valueName_coherent := by
    intro x
    calc
      _ = (after.prop ⟨(before.valueName x).val⟩).val :=
        after.valueName_coherent _
      _ = (after.prop ⟨(before.prop ⟨x.val⟩).val⟩).val := by
        rw [before.valueName_coherent]
      _ = _ := rfl

/-- Every renamable namespace is injective.  Replay identities are absent from
this structure and therefore cannot be altered by a `GlobalRenaming`. -/
def Injective (ρg : GlobalRenaming) : Prop :=
  Function.Injective ρg.prop ∧
  Function.Injective ρg.question ∧
  Function.Injective ρg.leaf ∧
  Function.Injective ρg.rule ∧
  Function.Injective ρg.arg ∧
  Function.Injective ρg.argRef ∧
  Function.Injective ρg.obligation ∧
  Function.Injective ρg.source ∧
  Function.Injective ρg.group ∧
  Function.Injective ρg.measurand ∧
  Function.Injective ρg.dataset ∧
  Function.Injective ρg.premiseLabel ∧
  Function.Injective ρg.valueName

theorem injective (ρg : GlobalRenaming) : Injective ρg :=
  ⟨ρg.prop_injective, ρg.question_injective, ρg.leaf_injective,
    ρg.rule_injective, ρg.arg_injective, ρg.argRef_injective,
    ρg.obligation_injective, ρg.source_injective, ρg.group_injective,
    ρg.measurand_injective, ρg.dataset_injective,
    ρg.premiseLabel_injective, ρg.valueName_injective⟩

end GlobalRenaming
@[simp] theorem id_prop (x : PropId) : GlobalRenaming.id.prop x = x := rfl
@[simp] theorem id_question (x : QuestionId) : GlobalRenaming.id.question x = x := rfl
@[simp] theorem id_leaf (x : LeafId) : GlobalRenaming.id.leaf x = x := rfl
@[simp] theorem id_rule (x : RuleId) : GlobalRenaming.id.rule x = x := rfl
@[simp] theorem id_arg (x : ArgId) : GlobalRenaming.id.arg x = x := rfl
@[simp] theorem id_argRef (x : ArgRef) : GlobalRenaming.id.argRef x = x := rfl
@[simp] theorem id_obligation (x : ObligationId) : GlobalRenaming.id.obligation x = x := rfl
@[simp] theorem id_source (x : SourceRef) : GlobalRenaming.id.source x = x := rfl
@[simp] theorem id_group (x : GroupId) : GlobalRenaming.id.group x = x := rfl
@[simp] theorem id_measurand (x : MeasurandId) : GlobalRenaming.id.measurand x = x := rfl
@[simp] theorem id_dataset (x : DatasetId) : GlobalRenaming.id.dataset x = x := rfl
@[simp] theorem id_premiseLabel (x : PremiseLabel) :
    GlobalRenaming.id.premiseLabel x = x := rfl
@[simp] theorem id_valueName (x : ValueName) : GlobalRenaming.id.valueName x = x := rfl

@[simp] theorem comp_prop (a b : GlobalRenaming) (x : PropId) :
    (GlobalRenaming.comp a b).prop x = a.prop (b.prop x) := rfl
@[simp] theorem comp_question (a b : GlobalRenaming) (x : QuestionId) :
    (GlobalRenaming.comp a b).question x = a.question (b.question x) := rfl
@[simp] theorem comp_leaf (a b : GlobalRenaming) (x : LeafId) :
    (GlobalRenaming.comp a b).leaf x = a.leaf (b.leaf x) := rfl
@[simp] theorem comp_rule (a b : GlobalRenaming) (x : RuleId) :
    (GlobalRenaming.comp a b).rule x = a.rule (b.rule x) := rfl
@[simp] theorem comp_arg (a b : GlobalRenaming) (x : ArgId) :
    (GlobalRenaming.comp a b).arg x = a.arg (b.arg x) := rfl
@[simp] theorem comp_argRef (a b : GlobalRenaming) (x : ArgRef) :
    (GlobalRenaming.comp a b).argRef x = a.argRef (b.argRef x) := rfl
@[simp] theorem comp_obligation (a b : GlobalRenaming) (x : ObligationId) :
    (GlobalRenaming.comp a b).obligation x = a.obligation (b.obligation x) := rfl
@[simp] theorem comp_source (a b : GlobalRenaming) (x : SourceRef) :
    (GlobalRenaming.comp a b).source x = a.source (b.source x) := rfl
@[simp] theorem comp_group (a b : GlobalRenaming) (x : GroupId) :
    (GlobalRenaming.comp a b).group x = a.group (b.group x) := rfl
@[simp] theorem comp_measurand (a b : GlobalRenaming) (x : MeasurandId) :
    (GlobalRenaming.comp a b).measurand x = a.measurand (b.measurand x) := rfl
@[simp] theorem comp_dataset (a b : GlobalRenaming) (x : DatasetId) :
    (GlobalRenaming.comp a b).dataset x = a.dataset (b.dataset x) := rfl
@[simp] theorem comp_premiseLabel (a b : GlobalRenaming) (x : PremiseLabel) :
    (GlobalRenaming.comp a b).premiseLabel x = a.premiseLabel (b.premiseLabel x) := rfl
@[simp] theorem comp_valueName (a b : GlobalRenaming) (x : ValueName) :
    (GlobalRenaming.comp a b).valueName x = a.valueName (b.valueName x) := rfl

@[simp] theorem id_prop_fun : GlobalRenaming.id.prop = id := rfl
@[simp] theorem id_question_fun : GlobalRenaming.id.question = id := rfl
@[simp] theorem id_leaf_fun : GlobalRenaming.id.leaf = id := rfl
@[simp] theorem id_rule_fun : GlobalRenaming.id.rule = id := rfl
@[simp] theorem id_arg_fun : GlobalRenaming.id.arg = id := rfl
@[simp] theorem id_argRef_fun : GlobalRenaming.id.argRef = id := rfl
@[simp] theorem id_obligation_fun : GlobalRenaming.id.obligation = id := rfl
@[simp] theorem id_source_fun : GlobalRenaming.id.source = id := rfl
@[simp] theorem id_group_fun : GlobalRenaming.id.group = id := rfl
@[simp] theorem id_measurand_fun : GlobalRenaming.id.measurand = id := rfl
@[simp] theorem id_dataset_fun : GlobalRenaming.id.dataset = id := rfl
@[simp] theorem id_premiseLabel_fun : GlobalRenaming.id.premiseLabel = id := rfl
@[simp] theorem id_valueName_fun : GlobalRenaming.id.valueName = id := rfl

@[simp] theorem comp_prop_fun (a b : GlobalRenaming) :
    (GlobalRenaming.comp a b).prop = a.prop ∘ b.prop := rfl
@[simp] theorem comp_question_fun (a b : GlobalRenaming) :
    (GlobalRenaming.comp a b).question = a.question ∘ b.question := rfl
@[simp] theorem comp_leaf_fun (a b : GlobalRenaming) :
    (GlobalRenaming.comp a b).leaf = a.leaf ∘ b.leaf := rfl
@[simp] theorem comp_rule_fun (a b : GlobalRenaming) :
    (GlobalRenaming.comp a b).rule = a.rule ∘ b.rule := rfl
@[simp] theorem comp_arg_fun (a b : GlobalRenaming) :
    (GlobalRenaming.comp a b).arg = a.arg ∘ b.arg := rfl
@[simp] theorem comp_argRef_fun (a b : GlobalRenaming) :
    (GlobalRenaming.comp a b).argRef = a.argRef ∘ b.argRef := rfl
@[simp] theorem comp_obligation_fun (a b : GlobalRenaming) :
    (GlobalRenaming.comp a b).obligation = a.obligation ∘ b.obligation := rfl
@[simp] theorem comp_source_fun (a b : GlobalRenaming) :
    (GlobalRenaming.comp a b).source = a.source ∘ b.source := rfl
@[simp] theorem comp_group_fun (a b : GlobalRenaming) :
    (GlobalRenaming.comp a b).group = a.group ∘ b.group := rfl
@[simp] theorem comp_measurand_fun (a b : GlobalRenaming) :
    (GlobalRenaming.comp a b).measurand = a.measurand ∘ b.measurand := rfl
@[simp] theorem comp_dataset_fun (a b : GlobalRenaming) :
    (GlobalRenaming.comp a b).dataset = a.dataset ∘ b.dataset := rfl
@[simp] theorem comp_premiseLabel_fun (a b : GlobalRenaming) :
    (GlobalRenaming.comp a b).premiseLabel =
      a.premiseLabel ∘ b.premiseLabel := rfl
@[simp] theorem comp_valueName_fun (a b : GlobalRenaming) :
    (GlobalRenaming.comp a b).valueName = a.valueName ∘ b.valueName := rfl

def renameText (ρg : GlobalRenaming) (text : String) : String :=
  (ρg.prop ⟨text⟩).val

@[simp] theorem renameText_id (text : String) :
    renameText GlobalRenaming.id text = text := rfl

@[simp] theorem renameText_comp (after before : GlobalRenaming) (text : String) :
    renameText (GlobalRenaming.comp after before) text =
      renameText after (renameText before text) := rfl

@[simp] theorem renameText_injective (ρg : GlobalRenaming) :
    Function.Injective (renameText ρg) := by
  intro left right equal
  unfold renameText at equal
  have h1 : ρg.prop ⟨left⟩ = ρg.prop ⟨right⟩ := by
    exact congrArg (fun s : String => (⟨s⟩ : PropId)) equal
  have h2 : (⟨left⟩ : PropId) = (⟨right⟩ : PropId) := ρg.prop_injective h1
  exact congrArg (fun (x : PropId) => x.val) h2

@[simp] theorem rename_question_val (ρg : GlobalRenaming) (x : QuestionId) :
    (ρg.question x).val = (ρg.prop ⟨x.val⟩).val := ρg.question_coherent x
@[simp] theorem rename_leaf_val (ρg : GlobalRenaming) (x : LeafId) :
    (ρg.leaf x).val = (ρg.prop ⟨x.val⟩).val := ρg.leaf_coherent x
@[simp] theorem rename_rule_val (ρg : GlobalRenaming) (x : RuleId) :
    (ρg.rule x).val = (ρg.prop ⟨x.val⟩).val := ρg.rule_coherent x
@[simp] theorem rename_arg_val (ρg : GlobalRenaming) (x : ArgId) :
    (ρg.arg x).val = (ρg.prop ⟨x.val⟩).val := ρg.arg_coherent x
@[simp] theorem rename_argRef_val (ρg : GlobalRenaming) (x : ArgRef) :
    (ρg.argRef x).val = (ρg.prop ⟨x.val⟩).val := ρg.argRef_coherent x
@[simp] theorem rename_obligation_val (ρg : GlobalRenaming) (x : ObligationId) :
    (ρg.obligation x).val = (ρg.prop ⟨x.val⟩).val := ρg.obligation_coherent x
@[simp] theorem rename_group_val (ρg : GlobalRenaming) (x : GroupId) :
    (ρg.group x).val = (ρg.prop ⟨x.val⟩).val := ρg.group_coherent x
@[simp] theorem rename_measurand_val (ρg : GlobalRenaming) (x : MeasurandId) :
    (ρg.measurand x).val = (ρg.prop ⟨x.val⟩).val := ρg.measurand_coherent x
@[simp] theorem rename_dataset_val (ρg : GlobalRenaming) (x : DatasetId) :
    (ρg.dataset x).val = (ρg.prop ⟨x.val⟩).val := ρg.dataset_coherent x
@[simp] theorem rename_premiseLabel_val (ρg : GlobalRenaming) (x : PremiseLabel) :
    (ρg.premiseLabel x).val = (ρg.prop ⟨x.val⟩).val := ρg.premiseLabel_coherent x
@[simp] theorem rename_valueName_val (ρg : GlobalRenaming) (x : ValueName) :
    (ρg.valueName x).val = (ρg.prop ⟨x.val⟩).val := ρg.valueName_coherent x

def renameCertPayload (ρg : GlobalRenaming) : Sx → Sx
  | .node "prem" (.cons (.str source) .nil) =>
      .node "prem" (.cons (.str (renameText ρg source)) .nil)
  | .node "lam" (.cons formula (.cons body .nil)) =>
      .node "lam" (.cons formula (.cons (renameCertPayload ρg body) .nil))
  | .node "lam" (.cons binder (.cons formula (.cons body .nil))) =>
      .node "lam"
        (.cons binder (.cons formula (.cons (renameCertPayload ρg body) .nil)))
  | .node "app" (.cons fn (.cons arg .nil)) =>
      .node "app"
        (.cons (renameCertPayload ρg fn)
          (.cons (renameCertPayload ρg arg) .nil))
  | .node "abort" (.cons formula (.cons body .nil)) =>
      .node "abort"
        (.cons formula (.cons (renameCertPayload ρg body) .nil))
  | expression => expression
termination_by expression => sizeOf expression

mutual
  /-- Symbolic premise spellings occurring anywhere in a certificate payload. -/
  def allPayloadPremiseSpellings : Sx → List String
    | .node "prem" (.cons (.str source) .nil) => [source]
    | .node _ children => allPayloadPremiseSpellingsList children
    | .str _ => []
    | .int _ => []
  /-- Symbolic premise spellings occurring anywhere in a certificate payload list. -/
  def allPayloadPremiseSpellingsList : SxList → List String
    | .nil => []
    | .cons expression rest =>
        allPayloadPremiseSpellings expression ++ allPayloadPremiseSpellingsList rest
end

/-- Symbolic premise spellings in subtrees that `renameCertPayload` leaves opaque. -/
def opaquePayloadPremiseSpellings : Sx → List String
  | .node "prem" (.cons (.str _) .nil) => []
  | .node "lam" (.cons _ (.cons body .nil)) =>
      opaquePayloadPremiseSpellings body
  | .node "lam" (.cons _ (.cons _ (.cons body .nil))) =>
      opaquePayloadPremiseSpellings body
  | .node "app" (.cons fn (.cons arg .nil)) =>
      opaquePayloadPremiseSpellings fn ++ opaquePayloadPremiseSpellings arg
  | .node "abort" (.cons _ (.cons body .nil)) =>
      opaquePayloadPremiseSpellings body
  | expression => allPayloadPremiseSpellings expression

def stripPrefixChars : List Char → List Char → Option (List Char)
  | [], input => some input
  | expected :: expectRest, actual :: inputRest =>
      if expected = actual then stripPrefixChars expectRest inputRest else none
  | _ :: _, [] => none

def renameDirective (ρg : GlobalRenaming) (body : List Char) : List Char :=
  match stripPrefixChars "cell ".toList body with
  | some leaf =>
      "cell ".toList ++ (renameText ρg (String.ofList leaf)).toList
  | none => (renameText ρg (String.ofList body)).toList

def takeNlDirective : List Char → Option (List Char × List Char)
  | [] => none
  | '}' :: rest => some ([], rest)
  | char :: rest => do
      let (body, after) ← takeNlDirective rest
      some (char :: body, after)

def renameNlChars (ρg : GlobalRenaming) : Nat → List Char → List Char
  | 0, chars => chars
  | _ + 1, [] => []
  | fuel + 1, '{' :: '{' :: rest =>
      '{' :: '{' :: renameNlChars ρg fuel rest
  | fuel + 1, '}' :: '}' :: rest =>
      '}' :: '}' :: renameNlChars ρg fuel rest
  | fuel + 1, '{' :: rest =>
      match takeNlDirective rest with
      | none => '{' :: rest
      | some (body, after) =>
          '{' :: (renameDirective ρg body ++
            ('}' :: renameNlChars ρg fuel after))
  | fuel + 1, char :: rest => char :: renameNlChars ρg fuel rest

def renameNl (ρg : GlobalRenaming) (text : String) : String :=
  String.ofList (renameNlChars ρg (text.toList.length + 1) text.toList)

mutual
  def renameValueTerm (ρg : GlobalRenaming)
      (values : List ValueName) : Term → Term
    | term@(.num _) => term
    | term@(.str _) => term
    | .con name .nil =>
        if values.contains ⟨name⟩ then .con (renameText ρg name) .nil
        else .con name .nil
    | .con name terms => .con name (renameValueTerms ρg values terms)
  def renameValueTerms (ρg : GlobalRenaming)
      (values : List ValueName) : Terms → Terms
    | .nil => .nil
    | .cons term rest =>
        .cons (renameValueTerm ρg values term)
          (renameValueTerms ρg values rest)
end


def renameValueAtom (ρg : GlobalRenaming)
    (values : List ValueName) : Atom → Atom
  | .atom pred terms => .atom pred (renameValueTerms ρg values terms)

def renameSubstValues (ρg : GlobalRenaming)
    (values : List ValueName) (subst : Subst) : Subst :=
  subst.map fun entry => (entry.1, renameValueTerm ρg values entry.2)

def renameAssurance (ρg : GlobalRenaming) : Assurance → Assurance
  | .none => .none
  | .trusted => .trusted
  | .cert cert =>
      .cert { cert with payload := renameCertPayload ρg cert.payload }

mutual
  def renameSupportTerm (ρg : GlobalRenaming)
      (values : List ValueName) : SupportTerm → SupportTerm
    | .leaf leaf => .leaf (ρg.leaf leaf)
    | .rule rule subst premises discharges holes assurance =>
        .rule (ρg.rule rule) (renameSubstValues ρg values subst)
          (renameSupportTerms ρg values premises)
          (renameDischarges ρg values discharges)
          (holes.map ρg.obligation)
          (renameAssurance ρg assurance)
  def renameSupportTerms (ρg : GlobalRenaming)
      (values : List ValueName) : SupportTerms → SupportTerms
    | .nil => .nil
    | .cons term rest =>
        .cons (renameSupportTerm ρg values term)
          (renameSupportTerms ρg values rest)
  def renameDischarges (ρg : GlobalRenaming)
      (values : List ValueName) : Discharges → Discharges
    | .nil => .nil
    | .cons question term rest =>
        .cons (ρg.question question) (renameSupportTerm ρg values term)
          (renameDischarges ρg values rest)
end

def renameSurfaceStep (ρg : GlobalRenaming) : SurfaceStep → SurfaceStep
  | .index index => .index index
  | .name name => .name (renameText ρg name)

def renameSurfaceAttack (ρg : GlobalRenaming) :
    SurfaceAttack → SurfaceAttack
  | .rebut attacker target => .rebut (ρg.arg attacker) (ρg.arg target)
  | .undercut attacker target path =>
      .undercut (ρg.arg attacker) (ρg.arg target)
        (path.map (renameSurfaceStep ρg))
  | .undermine attacker target path =>
      .undermine (ρg.arg attacker) (ρg.arg target)
        (path.map (renameSurfaceStep ρg))

def renameArgConcl (ρg : GlobalRenaming) : ArgConcl → ArgConcl
  | .supportsClaim claim => .supportsClaim (ρg.prop claim)
  | .supportsDerived claim => .supportsDerived (ρg.prop claim)
  | .challenges (.question question argument) =>
      .challenges (.question (ρg.question question) (ρg.arg argument))
  | .challenges (.leaf leaf) => .challenges (.leaf (ρg.leaf leaf))

def renameArgInstantiation (ρg : GlobalRenaming)
    (values : List ValueName) : ArgInstantiation → ArgInstantiation
  | .explicitTheta term =>
      .explicitTheta (renameSupportTerm ρg values term)
  | .inferTheta rule refs discharges obligations assurance =>
      .inferTheta (ρg.rule rule) (refs.map ρg.argRef)
        (discharges.map fun discharge =>
          (ρg.question discharge.1, ρg.argRef discharge.2))
        (obligations.map ρg.obligation)
        (renameAssurance ρg assurance)

def renameArg (ρg : GlobalRenaming) (values : List ValueName)
    (argument : Arg) : Arg :=
  ⟨ρg.arg argument.id, renameArgConcl ρg argument.concl,
    renameArgInstantiation ρg values argument.instantiation⟩

def renameComparison (ρg : GlobalRenaming)
    (values : List ValueName) (comparison : Comparison) : Comparison :=
  { comparison with
    conclusion := renameValueAtom ρg values comparison.conclusion
    measurand := ρg.measurand comparison.measurand
    dataset := ρg.dataset comparison.dataset
    recheckArg := ρg.arg comparison.recheckArg
    bridgeArg := ρg.arg comparison.bridgeArg
    result := ρg.leaf comparison.result
    baseline := ρg.leaf comparison.baseline
    binding := ρg.leaf comparison.binding
    claim :=
      { comparison.claim with
        id := ρg.prop comparison.claim.id
        nlRaw := renameNl ρg comparison.claim.nlRaw }
    supports := comparison.supports.map ρg.prop }

def renameDecl (ρg : GlobalRenaming)
    (values : List ValueName) : Decl → Decl
  | .leaf leaf =>
      .leaf
        { leaf with
          id := ρg.leaf leaf.id
          prop := renameValueAtom ρg values leaf.prop
          refs := leaf.refs.map ρg.source }
  | .claim claim =>
      .claim
        { claim with
          id := ρg.prop claim.id
          nl := renameNl ρg claim.nl
          formal := renameValueAtom ρg values claim.formal }
  | .arg argument => .arg (renameArg ρg values argument)
  | .attack attack => .attack (renameSurfaceAttack ρg attack)
  | .status proposition => .status (ρg.prop proposition)
  | .group group =>
      .group
        { group with
          id := ρg.group group.id
          members := group.members.map ρg.leaf }
  | .comparison comparison =>
      .comparison (renameComparison ρg values comparison)

/-- Rename every typed global namespace and every supported authored reference
in a program.  Artifact/digest/policy/backend replay identities and formula
text remain fixed. -/
def renameProgram (ρg : GlobalRenaming) (program : Program) : Program :=
  let values := program.valueBindings.map (·.name)
  { program with
    valueBindings := program.valueBindings.map fun binding =>
      { binding with name := ρg.valueName binding.name }
    decls := program.decls.map (renameDecl ρg values) }

def renameRule (ρg : GlobalRenaming) (rule : Rule) : Rule :=
  { rule with
    id := ρg.rule rule.id
    premiseLabels := rule.premiseLabels.map (Option.map ρg.premiseLabel)
    questions := rule.questions.map fun question =>
      { question with id := ρg.question question.id } }

def renamePolicyException (ρg : GlobalRenaming)
    (exception : Exception) : Exception :=
  { exception with rule := ρg.rule exception.rule }

def renameComparisonScheme (ρg : GlobalRenaming)
    (scheme : ComparisonScheme) : ComparisonScheme :=
  { scheme with

    recheck := ρg.rule scheme.recheck
    bridge := ρg.rule scheme.bridge }

/-- Rename every typed global namespace in a policy.  Policy identity, sigma,
backend/version/theory references, and theory digests remain fixed. -/
def renamePolicy (ρg : GlobalRenaming) (policy : Policy) : Policy :=
  { policy with
    rules := policy.rules.map (renameRule ρg)
    exceptions := policy.exceptions.map (renamePolicyException ρg)
    measurands := policy.measurands.map fun measurand =>

      { measurand with id := ρg.measurand measurand.id }

    comparisonSchemes :=
      policy.comparisonSchemes.map (renameComparisonScheme ρg) }
def renameSourceRefsDecl (f : SourceRef → SourceRef) : Decl → Decl
  | .leaf leaf => .leaf { leaf with refs := leaf.refs.map f }
  | declaration => declaration

def renameSourceRefsProgram (f : SourceRef → SourceRef)
    (program : Program) : Program :=
  { program with decls := program.decls.map (renameSourceRefsDecl f) }
def SourcesFixed (f : SourceRef → SourceRef) : List Decl → Prop
  | [] => True
  | .leaf leaf :: rest =>
      (∀ source ∈ leaf.refs, f source = source) ∧ SourcesFixed f rest
  | _ :: rest => SourcesFixed f rest

private theorem map_eq_self_of_pointwise {α : Type} (f : α → α)
    (items : List α) (fixed : ∀ item ∈ items, f item = item) :
    items.map f = items := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
      simp [fixed head (by simp), ih (by
        intro item member
        exact fixed item (by simp [member]))]

private theorem renameSourceRefsDecls_eq_of_fixed
    (f : SourceRef → SourceRef) (decls : List Decl)
    (fixed : SourcesFixed f decls) :
    decls.map (renameSourceRefsDecl f) = decls := by
  induction decls with
  | nil => rfl
  | cons declaration rest ih =>
      cases declaration with
      | leaf leaf =>
          have refsFixed :=
            map_eq_self_of_pointwise f leaf.refs fixed.1
          simp [renameSourceRefsDecl, refsFixed, ih fixed.2]
      | claim claim => simpa [renameSourceRefsDecl] using ih fixed
      | arg argument => simpa [renameSourceRefsDecl] using ih fixed
      | attack attack => simpa [renameSourceRefsDecl] using ih fixed
      | status status => simpa [renameSourceRefsDecl] using ih fixed
      | group group => simpa [renameSourceRefsDecl] using ih fixed
      | comparison comparison => simpa [renameSourceRefsDecl] using ih fixed

theorem renameSourceRefsProgram_eq_of_fixed (f : SourceRef → SourceRef)
    (program : Program) (fixed : SourcesFixed f program.decls) :
    renameSourceRefsProgram f program = program := by
  cases program
  simp [renameSourceRefsProgram,
    renameSourceRefsDecls_eq_of_fixed f _ fixed]

mutual
  @[simp] private theorem renameValueTerm_id (values : List ValueName)
      (term : Term) :
      renameValueTerm GlobalRenaming.id values term = term := by
    cases term with
    | num source => rfl
    | str source => rfl
    | con name terms =>
        cases terms with
        | nil => simp [renameValueTerm]
        | cons term rest =>
            simp [renameValueTerm, renameValueTerms_id values (.cons term rest)]
  @[simp] private theorem renameValueTerms_id (values : List ValueName)
      (terms : Terms) :
      renameValueTerms GlobalRenaming.id values terms = terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp [renameValueTerms, renameValueTerm_id values term,
          renameValueTerms_id values rest]
end

private theorem stripPrefixChars_some {pre input rest : List Char}
    (found : stripPrefixChars pre input = some rest) :
    pre ++ rest = input := by
  induction pre generalizing input with
  | nil => simpa [stripPrefixChars] using (congrArg id found).symm
  | cons expected expectRest ih =>
      cases input with
      | nil => simp [stripPrefixChars] at found
      | cons actual inputRest =>
          by_cases equal : expected = actual
          · subst actual
            simp only [stripPrefixChars, ↓reduceIte] at found
            simp [ih found]
          · simp [stripPrefixChars, equal] at found

private theorem takeNlDirective_some {input body after : List Char}
    (found : takeNlDirective input = some (body, after)) :
    body ++ '}' :: after = input := by
  induction input generalizing body after with
  | nil => simp [takeNlDirective] at found
  | cons char rest ih =>
      by_cases closing : char = '}'
      · subst char
        simp [takeNlDirective] at found
        obtain ⟨rfl, rfl⟩ := found
        rfl
      · cases htail : takeNlDirective rest with
        | none => simp [takeNlDirective, htail] at found
        | some pair =>
            cases pair with
            | mk tail remaining =>
                simp [takeNlDirective, htail] at found
                obtain ⟨rfl, rfl⟩ := found
                simp [ih htail]

@[simp] private theorem renameDirective_id (body : List Char) :
    renameDirective GlobalRenaming.id body = body := by
  unfold renameDirective
  cases found : stripPrefixChars "cell ".toList body with
  | none => simp
  | some rest =>
      have joined := stripPrefixChars_some found
      simpa using joined

@[simp] private theorem renameNlChars_id (fuel : Nat) (chars : List Char) :
    renameNlChars GlobalRenaming.id fuel chars = chars := by
  induction fuel generalizing chars with
  | zero => rfl
  | succ fuel ih =>
      cases chars with
      | nil => rfl
      | cons char rest =>
          by_cases hopen : char = '{'
          · subst char
            cases rest with
            | nil => simp [renameNlChars, takeNlDirective]
            | cons next tail =>
                by_cases escaped : next = '{'
                · subst next
                  simp [renameNlChars, ih]
                · cases hdir : takeNlDirective (next :: tail) with
                  | none => simp [renameNlChars, escaped, hdir]
                  | some pair =>
                      cases pair with
                      | mk body after =>
                          have joined := takeNlDirective_some hdir
                          simp [renameNlChars, escaped, hdir, ih, joined]
          · by_cases hclose : char = '}'
            · subst char
              cases rest with
              | nil => simp [renameNlChars, ih]
              | cons next tail =>
                  by_cases escaped : next = '}'
                  · subst next
                    simp [renameNlChars, ih]
                  · simp [renameNlChars, hopen, escaped, ih]
            · simp [renameNlChars, hopen, hclose, ih]

@[simp] private theorem renameNl_id (text : String) :
    renameNl GlobalRenaming.id text = text := by
  simp [renameNl]
private theorem renameCertPayload_id (payload : Sx) :
    renameCertPayload GlobalRenaming.id payload = payload := by
  cases payload with
  | str value => simp [renameCertPayload]
  | int value => simp [renameCertPayload]
  | node tag children =>
      cases children with
      | nil => simp [renameCertPayload]
      | cons first rest =>
          cases rest with
          | nil =>
              cases first with
              | str source =>
                  by_cases prem : tag = "prem"
                  · subst tag
                    simp [renameCertPayload]
                  · simp [renameCertPayload, prem]
              | int value => simp [renameCertPayload]
              | node innerTag innerChildren => simp [renameCertPayload]
          | cons second tail =>
              cases tail with
              | nil =>
                  by_cases lam : tag = "lam"
                  · subst tag
                    simp [renameCertPayload, renameCertPayload_id second]
                  · by_cases app : tag = "app"
                    · subst tag
                      simp [renameCertPayload, renameCertPayload_id first,
                        renameCertPayload_id second]
                    · by_cases abort : tag = "abort"
                      · subst tag
                        simp [renameCertPayload, renameCertPayload_id second]
                      · simp [renameCertPayload, lam, app, abort]
              | cons third remaining =>
                  cases remaining with
                  | nil =>
                      by_cases lam : tag = "lam"
                      · subst tag
                        simp [renameCertPayload, renameCertPayload_id third]
                      · simp [renameCertPayload, lam]
                  | cons fourth more => simp [renameCertPayload]
termination_by sizeOf payload

private theorem renameCertPayload_comp
    (after before : GlobalRenaming) (payload : Sx) :
    renameCertPayload (GlobalRenaming.comp after before) payload =
      renameCertPayload after (renameCertPayload before payload) := by
  cases payload with
  | str value => simp [renameCertPayload]
  | int value => simp [renameCertPayload]
  | node tag children =>
      cases children with
      | nil => simp [renameCertPayload]
      | cons first rest =>
          cases rest with
          | nil =>
              cases first with
              | str source =>
                  by_cases prem : tag = "prem"
                  · subst tag
                    simp [renameCertPayload, renameText_comp]
                  · simp [renameCertPayload, prem]
              | int value => simp [renameCertPayload]
              | node innerTag innerChildren => simp [renameCertPayload]
          | cons second tail =>
              cases tail with
              | nil =>
                  by_cases lam : tag = "lam"
                  · subst tag
                    simp [renameCertPayload,
                      renameCertPayload_comp after before second]
                  · by_cases app : tag = "app"
                    · subst tag
                      simp [renameCertPayload,
                        renameCertPayload_comp after before first,
                        renameCertPayload_comp after before second]
                    · by_cases abort : tag = "abort"
                      · subst tag
                        simp [renameCertPayload,
                          renameCertPayload_comp after before second]
                      · simp [renameCertPayload, lam, app, abort]
              | cons third remaining =>
                  cases remaining with
                  | nil =>
                      by_cases lam : tag = "lam"
                      · subst tag
                        simp [renameCertPayload,
                          renameCertPayload_comp after before third]
                      · simp [renameCertPayload, lam]
                  | cons fourth more => simp [renameCertPayload]
termination_by sizeOf payload

/-- Structural reference composition premises.  These are freshness/safety
obligations for declared value occurrences and interpolation bodies; certificate
and attack references compose unconditionally. -/
structure ReferenceComposition (after before : GlobalRenaming)
    (values : List ValueName) : Prop where
  valueTerm : ∀ term,
    renameValueTerm (GlobalRenaming.comp after before) values term =
      renameValueTerm after (values.map before.valueName)
        (renameValueTerm before values term)
  nl : ∀ text,
    renameNl (GlobalRenaming.comp after before) text =
      renameNl after (renameNl before text)

@[simp] private theorem renameValueTerms_comp (after before : GlobalRenaming)
    (values : List ValueName) (reference : ReferenceComposition after before values)
    (terms : Terms) :
    renameValueTerms (GlobalRenaming.comp after before) values terms =
      renameValueTerms after (values.map before.valueName)
        (renameValueTerms before values terms) := by
  cases terms with
  | nil => rfl
  | cons term rest =>
      simp [renameValueTerms, reference.valueTerm term,
        renameValueTerms_comp after before values reference rest]

@[simp] private theorem renameValueAtom_id (values : List ValueName)
    (atom : Atom) :
    renameValueAtom GlobalRenaming.id values atom = atom := by
  cases atom
  simp [renameValueAtom]

private theorem renameValueAtom_comp (after before : GlobalRenaming)
    (values : List ValueName) (reference : ReferenceComposition after before values)
    (atom : Atom) :
    renameValueAtom (GlobalRenaming.comp after before) values atom =
      renameValueAtom after (values.map before.valueName)
        (renameValueAtom before values atom) := by
  cases atom
  simp [renameValueAtom, renameValueTerms_comp after before values reference]

@[simp] private theorem renameSubstValues_id (values : List ValueName)
    (subst : Subst) :
    renameSubstValues GlobalRenaming.id values subst = subst := by
  simp [renameSubstValues]

private theorem renameSubstValues_comp (after before : GlobalRenaming)
    (values : List ValueName) (reference : ReferenceComposition after before values)
    (subst : Subst) :
    renameSubstValues (GlobalRenaming.comp after before) values subst =
      renameSubstValues after (values.map before.valueName)
        (renameSubstValues before values subst) := by
  simp [renameSubstValues, List.map_map, Function.comp_def,
    reference.valueTerm]

@[simp] private theorem renameAssurance_id (assurance : Assurance) :
    renameAssurance GlobalRenaming.id assurance = assurance := by
  cases assurance <;> simp [renameAssurance, renameCertPayload_id]

@[simp] private theorem renameAssurance_comp (after before : GlobalRenaming)
    (assurance : Assurance) :
    renameAssurance (GlobalRenaming.comp after before) assurance =
      renameAssurance after (renameAssurance before assurance) := by
  cases assurance <;>
    simp [renameAssurance, renameCertPayload_comp after before]

mutual
  @[simp] theorem renameSupportTerm_id (values : List ValueName)
      (term : SupportTerm) :
      renameSupportTerm GlobalRenaming.id values term = term := by
    cases term with
    | leaf leaf => rfl
    | rule rule subst premises discharges holes assurance =>
        simp [renameSupportTerm, renameSupportTerms_id values premises,
          renameDischarges_id values discharges]
  @[simp] theorem renameSupportTerms_id (values : List ValueName)
      (terms : SupportTerms) :
      renameSupportTerms GlobalRenaming.id values terms = terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp [renameSupportTerms, renameSupportTerm_id values term,
          renameSupportTerms_id values rest]
  @[simp] theorem renameDischarges_id (values : List ValueName)
      (discharges : Discharges) :
      renameDischarges GlobalRenaming.id values discharges = discharges := by
    cases discharges with
    | nil => rfl
    | cons question term rest =>
        simp [renameDischarges, renameSupportTerm_id values term,
          renameDischarges_id values rest]
end

mutual
  private theorem renameSupportTerm_comp (after before : GlobalRenaming)
      (values : List ValueName) (reference : ReferenceComposition after before values)
      (term : SupportTerm) :
      renameSupportTerm (GlobalRenaming.comp after before) values term =
        renameSupportTerm after (values.map before.valueName)
          (renameSupportTerm before values term) := by
    cases term with
    | leaf leaf => rfl
    | rule rule subst premises discharges holes assurance =>
        simp [renameSupportTerm,
          renameSubstValues_comp after before values reference subst,
          renameSupportTerms_comp after before values reference premises,
          renameDischarges_comp after before values reference discharges,
          List.map_map, Function.comp_def]
  private theorem renameSupportTerms_comp
      (after before : GlobalRenaming) (values : List ValueName)
      (reference : ReferenceComposition after before values)
      (terms : SupportTerms) :
      renameSupportTerms (GlobalRenaming.comp after before) values terms =
        renameSupportTerms after (values.map before.valueName)
          (renameSupportTerms before values terms) := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp [renameSupportTerms,
          renameSupportTerm_comp after before values reference term,
          renameSupportTerms_comp after before values reference rest]
  private theorem renameDischarges_comp
      (after before : GlobalRenaming) (values : List ValueName)
      (reference : ReferenceComposition after before values)
      (discharges : Discharges) :
      renameDischarges (GlobalRenaming.comp after before) values discharges =
        renameDischarges after (values.map before.valueName)
          (renameDischarges before values discharges) := by
    cases discharges with
    | nil => rfl
    | cons question term rest =>
        simp [renameDischarges,
          renameSupportTerm_comp after before values reference term,
          renameDischarges_comp after before values reference rest]
end

@[simp] private theorem renameSurfaceStep_id (step : SurfaceStep) :
    renameSurfaceStep GlobalRenaming.id step = step := by
  cases step <;> simp [renameSurfaceStep]

@[simp] private theorem renameSurfaceStep_id_fun :
    renameSurfaceStep GlobalRenaming.id = id :=
  funext renameSurfaceStep_id

@[simp] private theorem renameSurfaceStep_comp (after before : GlobalRenaming)
    (step : SurfaceStep) :
    renameSurfaceStep (GlobalRenaming.comp after before) step =
      renameSurfaceStep after (renameSurfaceStep before step) := by
  cases step <;> simp [renameSurfaceStep]

@[simp] private theorem renameSurfaceAttack_id (attack : SurfaceAttack) :
    renameSurfaceAttack GlobalRenaming.id attack = attack := by
  cases attack <;> simp [renameSurfaceAttack]

@[simp] private theorem renameSurfaceAttack_comp (after before : GlobalRenaming)
    (attack : SurfaceAttack) :
    renameSurfaceAttack (GlobalRenaming.comp after before) attack =
      renameSurfaceAttack after (renameSurfaceAttack before attack) := by
  cases attack <;>
    simp [renameSurfaceAttack, List.map_map, Function.comp_def]

@[simp] private theorem renameArgConcl_id (conclusion : ArgConcl) :
    renameArgConcl GlobalRenaming.id conclusion = conclusion := by
  cases conclusion with
  | supportsClaim claim => rfl
  | supportsDerived claim => rfl
  | challenges target => cases target <;> rfl

@[simp] private theorem renameArgConcl_comp (after before : GlobalRenaming)
    (conclusion : ArgConcl) :
    renameArgConcl (GlobalRenaming.comp after before) conclusion =
      renameArgConcl after (renameArgConcl before conclusion) := by
  cases conclusion with
  | supportsClaim claim => rfl
  | supportsDerived claim => rfl
  | challenges target => cases target <;> rfl

@[simp] private theorem renameArgInstantiation_id (values : List ValueName)
    (instantiation : ArgInstantiation) :
    renameArgInstantiation GlobalRenaming.id values instantiation =
      instantiation := by
  cases instantiation <;> simp [renameArgInstantiation]

private theorem renameArgInstantiation_comp
    (after before : GlobalRenaming) (values : List ValueName)
    (reference : ReferenceComposition after before values)
    (instantiation : ArgInstantiation) :
    renameArgInstantiation (GlobalRenaming.comp after before) values instantiation =
      renameArgInstantiation after (values.map before.valueName)
        (renameArgInstantiation before values instantiation) := by
  cases instantiation <;>
    simp [renameArgInstantiation,
      renameSupportTerm_comp after before values reference,
      List.map_map, Function.comp_def]

@[simp] private theorem renameArg_id (values : List ValueName)
    (argument : Arg) :
    renameArg GlobalRenaming.id values argument = argument := by
  cases argument
  simp [renameArg]

private theorem renameArg_comp (after before : GlobalRenaming)
    (values : List ValueName) (reference : ReferenceComposition after before values)
    (argument : Arg) :
    renameArg (GlobalRenaming.comp after before) values argument =
      renameArg after (values.map before.valueName)
        (renameArg before values argument) := by
  cases argument
  simp [renameArg, renameArgInstantiation_comp after before values reference]

@[simp] private theorem renameComparison_id (values : List ValueName)
    (comparison : Comparison) :
    renameComparison GlobalRenaming.id values comparison = comparison := by
  cases comparison
  simp [renameComparison]

private theorem renameComparison_comp (after before : GlobalRenaming)
    (values : List ValueName) (reference : ReferenceComposition after before values)
    (comparison : Comparison) :
    renameComparison (GlobalRenaming.comp after before) values comparison =
      renameComparison after (values.map before.valueName)
        (renameComparison before values comparison) := by
  cases comparison
  simp [renameComparison,
    renameValueAtom_comp after before values reference,
    reference.nl, Function.comp_def]

@[simp] private theorem renameDecl_id (values : List ValueName)
    (declaration : Decl) :
    renameDecl GlobalRenaming.id values declaration = declaration := by
  cases declaration <;> simp [renameDecl]

@[simp] private theorem renameDecl_id_fun (values : List ValueName) :
    renameDecl GlobalRenaming.id values = id :=
  funext (renameDecl_id values)

private theorem renameDecl_comp (after before : GlobalRenaming)
    (values : List ValueName) (reference : ReferenceComposition after before values)
    (declaration : Decl) :
    renameDecl (GlobalRenaming.comp after before) values declaration =
      renameDecl after (values.map before.valueName)
        (renameDecl before values declaration) := by
  cases declaration <;>
    simp [renameDecl,
      renameValueAtom_comp after before values reference,
      renameArg_comp after before values reference,
      renameComparison_comp after before values reference,
      reference.nl, List.map_map, Function.comp_def]

theorem renameProgram_id (program : Program) :
    renameProgram GlobalRenaming.id program = program := by
  cases program
  simp [renameProgram]

theorem renameProgram_comp (after before : GlobalRenaming)
    (program : Program)
    (reference : ReferenceComposition after before
      (program.valueBindings.map (·.name))) :
    renameProgram (GlobalRenaming.comp after before) program =
      renameProgram after (renameProgram before program) := by
  cases program
  simp [renameProgram,
    renameDecl_comp after before _ reference,
    List.map_map, Function.comp_def]
@[simp] private theorem renameRule_id (rule : Rule) :
    renameRule GlobalRenaming.id rule = rule := by
  cases rule
  simp [renameRule]

@[simp] private theorem renameRule_id_fun :
    renameRule GlobalRenaming.id = id :=
  funext renameRule_id

@[simp] private theorem renameRule_comp (after before : GlobalRenaming) (rule : Rule) :
    renameRule (GlobalRenaming.comp after before) rule =
      renameRule after (renameRule before rule) := by
  cases rule
  simp [renameRule, List.map_map, Function.comp_def]

@[simp] private theorem renameRule_comp_fun (after before : GlobalRenaming) :
    renameRule (GlobalRenaming.comp after before) =
      renameRule after ∘ renameRule before :=
  funext (renameRule_comp after before)

@[simp] private theorem renamePolicyException_id (exception : Exception) :
    renamePolicyException GlobalRenaming.id exception = exception := by
  cases exception
  rfl

@[simp] private theorem renamePolicyException_id_fun :
    renamePolicyException GlobalRenaming.id = id :=
  funext renamePolicyException_id

@[simp] private theorem renamePolicyException_comp (after before : GlobalRenaming)
    (exception : Exception) :
    renamePolicyException (GlobalRenaming.comp after before) exception =
      renamePolicyException after (renamePolicyException before exception) := by
  cases exception
  rfl

@[simp] private theorem renamePolicyException_comp_fun
    (after before : GlobalRenaming) :
    renamePolicyException (GlobalRenaming.comp after before) =
      renamePolicyException after ∘ renamePolicyException before :=
  funext (renamePolicyException_comp after before)

@[simp] private theorem renameComparisonScheme_id (scheme : ComparisonScheme) :
    renameComparisonScheme GlobalRenaming.id scheme = scheme := by
  cases scheme
  rfl

@[simp] private theorem renameComparisonScheme_id_fun :
    renameComparisonScheme GlobalRenaming.id = id :=
  funext renameComparisonScheme_id

@[simp] private theorem renameComparisonScheme_comp (after before : GlobalRenaming)
    (scheme : ComparisonScheme) :
    renameComparisonScheme (GlobalRenaming.comp after before) scheme =
      renameComparisonScheme after (renameComparisonScheme before scheme) := by
  cases scheme
  rfl

@[simp] private theorem renameComparisonScheme_comp_fun
    (after before : GlobalRenaming) :
    renameComparisonScheme (GlobalRenaming.comp after before) =
      renameComparisonScheme after ∘ renameComparisonScheme before :=
  funext (renameComparisonScheme_comp after before)

theorem renamePolicy_id (policy : Policy) :
    renamePolicy GlobalRenaming.id policy = policy := by
  cases policy
  simp [renamePolicy]

theorem renamePolicy_comp (after before : GlobalRenaming) (policy : Policy) :
    renamePolicy (GlobalRenaming.comp after before) policy =
      renamePolicy after (renamePolicy before policy) := by
  cases policy
  simp [renamePolicy, List.map_map, Function.comp_def]


mutual
  @[simp] private theorem renameValueTerm_sourceOnly
      (f : SourceRef → SourceRef) (hf : Function.Injective f)
      (values : List ValueName) (term : Term) :
      renameValueTerm (GlobalRenaming.sourceOnly f hf) values term = term := by
    cases term with
    | num source => rfl
    | str source => rfl
    | con name terms =>
        cases terms with
        | nil => simp [renameValueTerm, renameText]
        | cons term rest =>
            simp [renameValueTerm,
              renameValueTerms_sourceOnly f hf values (.cons term rest)]
  @[simp] private theorem renameValueTerms_sourceOnly
      (f : SourceRef → SourceRef) (hf : Function.Injective f)
      (values : List ValueName) (terms : Terms) :
      renameValueTerms (GlobalRenaming.sourceOnly f hf) values terms = terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp [renameValueTerms, renameValueTerm_sourceOnly f hf values term,
          renameValueTerms_sourceOnly f hf values rest]
end

@[simp] private theorem renameValueAtom_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f)
    (values : List ValueName) (atom : Atom) :
    renameValueAtom (GlobalRenaming.sourceOnly f hf) values atom = atom := by
  cases atom
  simp [renameValueAtom]

@[simp] private theorem renameSubstValues_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f)
    (values : List ValueName) (subst : Subst) :
    renameSubstValues (GlobalRenaming.sourceOnly f hf) values subst = subst := by
  simp [renameSubstValues]

@[simp] private theorem renameDirective_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f)
    (body : List Char) :
    renameDirective (GlobalRenaming.sourceOnly f hf) body = body := by
  unfold renameDirective
  cases found : stripPrefixChars "cell ".toList body with
  | none => simp [renameText]
  | some rest =>
      have joined := stripPrefixChars_some found
      simpa [renameText] using joined

@[simp] private theorem renameNlChars_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f)
    (fuel : Nat) (chars : List Char) :
    renameNlChars (GlobalRenaming.sourceOnly f hf) fuel chars = chars := by
  induction fuel generalizing chars with
  | zero => rfl
  | succ fuel ih =>
      cases chars with
      | nil => rfl
      | cons char rest =>
          by_cases hopen : char = '{'
          · subst char
            cases rest with
            | nil => simp [renameNlChars, takeNlDirective]
            | cons next tail =>
                by_cases escaped : next = '{'
                · subst next
                  simp [renameNlChars, ih]
                · cases hdir : takeNlDirective (next :: tail) with
                  | none => simp [renameNlChars, escaped, hdir]
                  | some pair =>
                      cases pair with
                      | mk body after =>
                          have joined := takeNlDirective_some hdir
                          simp [renameNlChars, escaped, hdir, ih, joined]
          · by_cases hclose : char = '}'
            · subst char
              cases rest with
              | nil => simp [renameNlChars, ih]
              | cons next tail =>
                  by_cases escaped : next = '}'
                  · subst next
                    simp [renameNlChars, ih]
                  · simp [renameNlChars, hopen, escaped, ih]
            · simp [renameNlChars, hopen, hclose, ih]

@[simp] private theorem renameNl_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f)
    (text : String) :
    renameNl (GlobalRenaming.sourceOnly f hf) text = text := by
  simp [renameNl]

private theorem renameCertPayload_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f)
    (payload : Sx) :
    renameCertPayload (GlobalRenaming.sourceOnly f hf) payload = payload := by
  cases payload with
  | str value => simp [renameCertPayload]
  | int value => simp [renameCertPayload]
  | node tag children =>
      cases children with
      | nil => simp [renameCertPayload]
      | cons first rest =>
          cases rest with
          | nil =>
              cases first with
              | str source =>
                  by_cases prem : tag = "prem"
                  · subst tag
                    simp [renameCertPayload, renameText]
                  · simp [renameCertPayload, prem]
              | int value => simp [renameCertPayload]
              | node innerTag innerChildren => simp [renameCertPayload]
          | cons second tail =>
              cases tail with
              | nil =>
                  by_cases lam : tag = "lam"
                  · subst tag
                    simp [renameCertPayload,
                      renameCertPayload_sourceOnly f hf second]
                  · by_cases app : tag = "app"
                    · subst tag
                      simp [renameCertPayload,
                        renameCertPayload_sourceOnly f hf first,
                        renameCertPayload_sourceOnly f hf second]
                    · by_cases abort : tag = "abort"
                      · subst tag
                        simp [renameCertPayload,
                          renameCertPayload_sourceOnly f hf second]
                      · simp [renameCertPayload, lam, app, abort]
              | cons third remaining =>
                  cases remaining with
                  | nil =>
                      by_cases lam : tag = "lam"
                      · subst tag
                        simp [renameCertPayload,
                          renameCertPayload_sourceOnly f hf third]
                      · simp [renameCertPayload, lam]
                  | cons fourth more => simp [renameCertPayload]
termination_by sizeOf payload

@[simp] private theorem renameAssurance_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f)
    (assurance : Assurance) :
    renameAssurance (GlobalRenaming.sourceOnly f hf) assurance = assurance := by
  cases assurance <;>
    simp [renameAssurance, renameCertPayload_sourceOnly f hf]

mutual
  @[simp] private theorem renameSupportTerm_sourceOnly
      (f : SourceRef → SourceRef) (hf : Function.Injective f)
      (values : List ValueName) (term : SupportTerm) :
      renameSupportTerm (GlobalRenaming.sourceOnly f hf) values term = term := by
    cases term with
    | leaf leaf => rfl
    | rule rule subst premises discharges holes assurance =>
        simp [renameSupportTerm, renameSubstValues,
          renameSupportTerms_sourceOnly f hf values premises,
          renameDischarges_sourceOnly f hf values discharges]
  @[simp] private theorem renameSupportTerms_sourceOnly
      (f : SourceRef → SourceRef) (hf : Function.Injective f)
      (values : List ValueName) (terms : SupportTerms) :
      renameSupportTerms (GlobalRenaming.sourceOnly f hf) values terms = terms := by
    cases terms with
    | nil => rfl
    | cons term rest =>
        simp [renameSupportTerms,
          renameSupportTerm_sourceOnly f hf values term,
          renameSupportTerms_sourceOnly f hf values rest]
  @[simp] private theorem renameDischarges_sourceOnly
      (f : SourceRef → SourceRef) (hf : Function.Injective f)
      (values : List ValueName) (discharges : Discharges) :
      renameDischarges (GlobalRenaming.sourceOnly f hf) values discharges =
        discharges := by
    cases discharges with
    | nil => rfl
    | cons question term rest =>
        simp [renameDischarges,
          renameSupportTerm_sourceOnly f hf values term,
          renameDischarges_sourceOnly f hf values rest]
end

@[simp] private theorem renameSurfaceStep_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f)
    (step : SurfaceStep) :
    renameSurfaceStep (GlobalRenaming.sourceOnly f hf) step = step := by
  cases step <;> simp [renameSurfaceStep, renameText]

@[simp] private theorem renameSurfaceStep_sourceOnly_fun
    (f : SourceRef → SourceRef) (hf : Function.Injective f) :
    renameSurfaceStep (GlobalRenaming.sourceOnly f hf) = id :=
  funext (renameSurfaceStep_sourceOnly f hf)

@[simp] private theorem renameSurfaceAttack_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f)
    (attack : SurfaceAttack) :
    renameSurfaceAttack (GlobalRenaming.sourceOnly f hf) attack = attack := by
  cases attack <;> simp [renameSurfaceAttack]

@[simp] private theorem renameArgConcl_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f)
    (conclusion : ArgConcl) :
    renameArgConcl (GlobalRenaming.sourceOnly f hf) conclusion = conclusion := by
  cases conclusion with
  | supportsClaim claim => rfl
  | supportsDerived claim => rfl
  | challenges target => cases target <;> rfl

@[simp] private theorem renameArgInstantiation_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f)
    (values : List ValueName) (instantiation : ArgInstantiation) :
    renameArgInstantiation (GlobalRenaming.sourceOnly f hf) values instantiation =
      instantiation := by
  cases instantiation <;> simp [renameArgInstantiation]

@[simp] private theorem renameArg_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f)
    (values : List ValueName) (argument : Arg) :
    renameArg (GlobalRenaming.sourceOnly f hf) values argument = argument := by
  cases argument
  simp [renameArg]

@[simp] private theorem renameComparison_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f)
    (values : List ValueName) (comparison : Comparison) :
    renameComparison (GlobalRenaming.sourceOnly f hf) values comparison =
      comparison := by
  cases comparison
  simp [renameComparison]

private theorem renameDecl_sourceOnly (f : SourceRef → SourceRef)
    (injective : Function.Injective f) (values : List ValueName)
    (declaration : Decl) :
    renameDecl (GlobalRenaming.sourceOnly f injective) values declaration =
      renameSourceRefsDecl f declaration := by
  cases declaration <;>
    simp [renameDecl, renameSourceRefsDecl]

theorem renameProgram_sourceOnly (f : SourceRef → SourceRef)
    (injective : Function.Injective f) (program : Program) :
    renameProgram (GlobalRenaming.sourceOnly f injective) program =
      renameSourceRefsProgram f program := by
  cases program
  simp [renameProgram, renameSourceRefsProgram, renameDecl_sourceOnly]

@[simp] private theorem renameRule_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f) (rule : Rule) :
    renameRule (GlobalRenaming.sourceOnly f hf) rule = rule := by
  cases rule
  simp [renameRule]

@[simp] private theorem renameRule_sourceOnly_fun
    (f : SourceRef → SourceRef) (hf : Function.Injective f) :
    renameRule (GlobalRenaming.sourceOnly f hf) = id :=
  funext (renameRule_sourceOnly f hf)

@[simp] private theorem renamePolicyException_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f)
    (exception : Exception) :
    renamePolicyException (GlobalRenaming.sourceOnly f hf) exception =
      exception := by
  cases exception
  rfl

@[simp] private theorem renamePolicyException_sourceOnly_fun
    (f : SourceRef → SourceRef) (hf : Function.Injective f) :
    renamePolicyException (GlobalRenaming.sourceOnly f hf) = id :=
  funext (renamePolicyException_sourceOnly f hf)

@[simp] private theorem renameComparisonScheme_sourceOnly
    (f : SourceRef → SourceRef) (hf : Function.Injective f)
    (scheme : ComparisonScheme) :
    renameComparisonScheme (GlobalRenaming.sourceOnly f hf) scheme = scheme := by
  cases scheme
  rfl

@[simp] private theorem renameComparisonScheme_sourceOnly_fun
    (f : SourceRef → SourceRef) (hf : Function.Injective f) :
    renameComparisonScheme (GlobalRenaming.sourceOnly f hf) = id :=
  funext (renameComparisonScheme_sourceOnly f hf)

theorem renamePolicy_sourceOnly (f : SourceRef → SourceRef)
    (injective : Function.Injective f) (policy : Policy) :
    renamePolicy (GlobalRenaming.sourceOnly f injective) policy = policy := by
  cases policy
  simp [renamePolicy]

namespace GlobalRenaming

/-- A proposed before/after application.  `Valid` rejects hand-written output
that changes replay identities because valid output must be exactly the result
of the typed renamer. -/
structure Attempt where
  maps : GlobalRenaming
  sourceProgram : Program
  targetProgram : Program
  sourcePolicy : Policy
  targetPolicy : Policy


def Valid (attempt : Attempt) : Prop :=
  attempt.targetProgram = renameProgram attempt.maps attempt.sourceProgram ∧
  attempt.targetPolicy = renamePolicy attempt.maps attempt.sourcePolicy

end GlobalRenaming
