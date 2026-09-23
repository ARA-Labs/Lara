import Lara.Context.Holes.Syntax
import Lara.Context.Parametricity

/-! Assurance transport through CQ substitution, including context fillings. -/
set_option autoImplicit false

namespace Lara.Context.Holes
open Lara.Support Lara.Erase

mutual
  def mapTemplate (f : Assurance → Assurance) : Template → Template
    | .core w => .core (mapAssur f w)
    | .inst rn θ ws D H α => .inst rn θ (mapTemplates f ws) (mapAnswers f D) H (f α)
  def mapAnswer (f : Assurance → Assurance) : AnswerTemplate → AnswerTemplate
    | .term t => .term (mapTemplate f t)
    | .hole h => .hole h
  def mapTemplates (f : Assurance → Assurance) : List Template → List Template
    | [] => []
    | t :: ts => mapTemplate f t :: mapTemplates f ts
  def mapAnswers (f : Assurance → Assurance) : List (QuestionId × AnswerTemplate) →
      List (QuestionId × AnswerTemplate)
    | [] => []
    | (q, a) :: rest => (q, mapAnswer f a) :: mapAnswers f rest
end

def mapFilling (f : Assurance → Assurance) (ρ : Filling) : Filling :=
  ρ.map (fun p => (p.1, mapAssur f p.2))

theorem lookupFilling_map (f : Assurance → Assurance) (ρ : Filling) (h : HoleId) :
    lookupFilling (mapFilling f ρ) h = (lookupFilling ρ h).map (mapAssur f) := by
  induction ρ with
  | nil => rfl
  | cons p ρ ih =>
    rcases p with ⟨k, w⟩
    simp only [mapFilling, List.map_cons, lookupFilling] at *
    split <;> simp_all

theorem mapFilling_keys (f : Assurance → Assurance) (ρ : Filling) :
    (mapFilling f ρ).map Prod.fst = ρ.map Prod.fst := by simp [mapFilling, List.map_map]

theorem firstDuplicate_map (f : Assurance → Assurance) (ρ : Filling) :
    firstDuplicate (mapFilling f ρ) = firstDuplicate ρ := by
  induction ρ with
  | nil => rfl
  | cons p ρ ih =>
    rcases p with ⟨h, w⟩
    change (if ((mapFilling f ρ).map Prod.fst).contains h then some h
      else firstDuplicate (mapFilling f ρ)) = _
    rw [mapFilling_keys, ih]
    rfl

mutual
  theorem instantiateAux_map (f : Assurance → Assurance) (ρ : Filling) (t : Template) :
      instantiateAux (mapFilling f ρ) (mapTemplate f t) =
        (instantiateAux ρ t).map (mapAssur f) := by
    cases t with
    | core w => rfl
    | inst rn θ ws D H α =>
      simp only [mapTemplate, instantiateAux, instantiateList_map, instantiateDis_map]
      cases instantiateList ρ ws <;> cases instantiateDis ρ D <;> rfl
  theorem instantiateAnswer_map (f : Assurance → Assurance) (ρ : Filling) (a : AnswerTemplate) :
      instantiateAnswer (mapFilling f ρ) (mapAnswer f a) =
        (instantiateAnswer ρ a).map (mapAssur f) := by
    cases a with
    | term t => exact instantiateAux_map f ρ t
    | hole h =>
      simp only [mapAnswer, instantiateAnswer, lookupFilling_map]
      cases lookupFilling ρ h <;> rfl
  theorem instantiateList_map (f : Assurance → Assurance) (ρ : Filling) (ts : List Template) :
      instantiateList (mapFilling f ρ) (mapTemplates f ts) =
        (instantiateList ρ ts).map (mapAssurList f) := by
    cases ts with
    | nil => rfl
    | cons t ts =>
      simp only [mapTemplates, instantiateList, instantiateAux_map, instantiateList_map]
      cases instantiateAux ρ t <;> cases instantiateList ρ ts <;> rfl
  theorem instantiateDis_map (f : Assurance → Assurance) (ρ : Filling)
      (D : List (QuestionId × AnswerTemplate)) :
      instantiateDis (mapFilling f ρ) (mapAnswers f D) =
        (instantiateDis ρ D).map (mapAssurDis f) := by
    cases D with
    | nil => rfl
    | cons p rest =>
      rcases p with ⟨q, a⟩
      simp only [mapAnswers, instantiateDis, instantiateAnswer_map, instantiateDis_map]
      cases instantiateAnswer ρ a <;> cases instantiateDis ρ rest <;> rfl
end

theorem instantiate_map (f : Assurance → Assurance) (ρ : Filling) (t : Template) :
    instantiate (mapFilling f ρ) (mapTemplate f t) =
      (instantiate ρ t).map (mapAssur f) := by
  simp only [instantiate, firstDuplicate_map]
  cases firstDuplicate ρ with
  | some h => rfl
  | none => exact instantiateAux_map f ρ t

mutual
  inductive RelTemplate (R : Assurance → Assurance → Prop) : Template → Template → Prop where
    | core {w v} (h : Lara.Context.RelTerm R w v) : RelTemplate R (.core w) (.core v)
    | inst {rn θ ws vs D E H α β}
        (hw : RelTemplates R ws vs) (hd : RelAnswers R D E) (ha : R α β) :
        RelTemplate R (.inst rn θ ws D H α) (.inst rn θ vs E H β)
  inductive RelAnswer (R : Assurance → Assurance → Prop) :
      AnswerTemplate → AnswerTemplate → Prop where
    | term {t u} (h : RelTemplate R t u) : RelAnswer R (.term t) (.term u)
    | hole (h : HoleId) : RelAnswer R (.hole h) (.hole h)
  inductive RelTemplates (R : Assurance → Assurance → Prop) :
      List Template → List Template → Prop where
    | nil : RelTemplates R [] []
    | cons {t u ts us} (h : RelTemplate R t u) (hs : RelTemplates R ts us) :
        RelTemplates R (t :: ts) (u :: us)
  inductive RelAnswers (R : Assurance → Assurance → Prop) :
      List (QuestionId × AnswerTemplate) → List (QuestionId × AnswerTemplate) → Prop where
    | nil : RelAnswers R [] []
    | cons {q a b D E} (h : RelAnswer R a b) (hs : RelAnswers R D E) :
        RelAnswers R ((q, a) :: D) ((q, b) :: E)
end

def RelFilling (R : Assurance → Assurance → Prop) (ρ σ : Filling) : Prop :=
  Lara.Forall₂ (fun p q => p.1 = q.1 ∧ Lara.Context.RelTerm R p.2 q.2) ρ σ

theorem relTemplates_iff_forall₂ {R : Assurance → Assurance → Prop} {ts us} :
    RelTemplates R ts us ↔ Lara.Forall₂ (RelTemplate R) ts us := by
  constructor
  · intro h
    induction ts generalizing us with
    | nil => cases h; exact .nil
    | cons _ _ ih => cases h with | cons ht hs => exact .cons ht (ih hs)
  · intro h
    induction ts generalizing us with
    | nil => cases h; exact .nil
    | cons _ _ ih => cases h with | cons ht hs => exact .cons ht (ih hs)

theorem lookupFilling_rel {R : Assurance → Assurance → Prop} {ρ σ : Filling}
    (h : RelFilling R ρ σ) {k : HoleId} {w : SupportTerm}
    (hw : lookupFilling ρ k = some w) :
    ∃ v, lookupFilling σ k = some v ∧ Lara.Context.RelTerm R w v := by
  induction h with
  | nil => simp [lookupFilling] at hw
  | @cons p q ρ σ hp hs ih =>
    rcases p with ⟨i, u⟩
    rcases q with ⟨j, v⟩
    obtain ⟨rfl, hp⟩ := hp
    simp only [lookupFilling] at hw ⊢
    split at hw
    · exact ⟨v, by simp_all, by cases hw; exact hp⟩
    · simp_all

/- Successful relational instantiation constructs the right result. -/
mutual
  theorem instantiateAux_rel {R : Assurance → Assurance → Prop} {ρ σ : Filling}
      (hρ : RelFilling R ρ σ) {t u : Template} (h : RelTemplate R t u)
      {w : SupportTerm} (hw : instantiateAux ρ t = .ok w) :
      ∃ v, instantiateAux σ u = .ok v ∧ Lara.Context.RelTerm R w v := by
    cases h with
    | core hr => exact ⟨_, rfl, (Except.ok.inj hw) ▸ hr⟩
    | @inst rn θ ts us D E H α β hts hD ha =>
      cases hws : instantiateList ρ ts with
      | error e => simp [instantiateAux, hws, Bind.bind, Except.bind] at hw
      | ok ws =>
        cases hds : instantiateDis ρ D with
        | error e => simp [instantiateAux, hws, hds, Bind.bind, Except.bind] at hw
        | ok ds =>
          obtain ⟨vs, hvs, hrvs⟩ := instantiateList_rel hρ hts hws
          obtain ⟨es, hes, hres⟩ := instantiateDis_rel hρ hD hds
          have he : SupportTerm.inst rn θ ws ds H α = w := by
            simpa [instantiateAux, hws, hds, Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map] using hw
          subst w
          exact ⟨_, by simp [instantiateAux, hvs, hes, Bind.bind, Except.bind, Pure.pure, Except.pure], .inst hrvs hres ha⟩
  theorem instantiateAnswer_rel {R : Assurance → Assurance → Prop} {ρ σ : Filling}
      (hρ : RelFilling R ρ σ) {a b : AnswerTemplate} (h : RelAnswer R a b)
      {w : SupportTerm} (hw : instantiateAnswer ρ a = .ok w) :
      ∃ v, instantiateAnswer σ b = .ok v ∧ Lara.Context.RelTerm R w v := by
    cases h with
    | term ht => exact instantiateAux_rel hρ ht hw
    | hole k =>
      cases hk : lookupFilling ρ k with
      | none => simp [instantiateAnswer, hk] at hw
      | some t =>
        have he : t = w := by simpa [instantiateAnswer, hk] using hw
        subst w
        obtain ⟨v, hv, hr⟩ := lookupFilling_rel hρ hk
        exact ⟨v, by simp [instantiateAnswer, hv], hr⟩
  theorem instantiateList_rel {R : Assurance → Assurance → Prop} {ρ σ : Filling}
      (hρ : RelFilling R ρ σ) {ts us : List Template} (h : RelTemplates R ts us)
      {ws : List SupportTerm} (hw : instantiateList ρ ts = .ok ws) :
      ∃ vs, instantiateList σ us = .ok vs ∧ Lara.Context.RelTerms R ws vs := by
    cases h with
    | nil => exact ⟨[], rfl, (Except.ok.inj hw) ▸ Lara.Context.RelTerms.nil⟩
    | @cons t u ts us ht hts =>
      cases ha : instantiateAux ρ t with
      | error e => simp [instantiateList, ha, Bind.bind, Except.bind] at hw
      | ok a =>
        cases htail : instantiateList ρ ts with
        | error e => simp [instantiateList, ha, htail, Bind.bind, Except.bind] at hw
        | ok tail =>
          obtain ⟨b, hb, hab⟩ := instantiateAux_rel hρ ht ha
          obtain ⟨rest, hrest, hrel⟩ := instantiateList_rel hρ hts htail
          have he : a :: tail = ws := by simpa [instantiateList, ha, htail, Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map] using hw
          subst ws
          exact ⟨_, by simp [instantiateList, hb, hrest, Bind.bind, Except.bind, Pure.pure, Except.pure], .cons hab hrel⟩
  theorem instantiateDis_rel {R : Assurance → Assurance → Prop} {ρ σ : Filling}
      (hρ : RelFilling R ρ σ) {D E : List (QuestionId × AnswerTemplate)}
      (h : RelAnswers R D E) {ds : List (QuestionId × SupportTerm)}
      (hw : instantiateDis ρ D = .ok ds) :
      ∃ es, instantiateDis σ E = .ok es ∧ Lara.Context.RelDis R ds es := by
    cases h with
    | nil => exact ⟨[], rfl, (Except.ok.inj hw) ▸ Lara.Context.RelDis.nil⟩
    | @cons q a b D E ha hD =>
      cases hw0 : instantiateAnswer ρ a with
      | error e => simp [instantiateDis, hw0, Bind.bind, Except.bind] at hw
      | ok w =>
        cases htail : instantiateDis ρ D with
        | error e => simp [instantiateDis, hw0, htail, Bind.bind, Except.bind] at hw
        | ok tail =>
          obtain ⟨v, hv, hrel⟩ := instantiateAnswer_rel hρ ha hw0
          obtain ⟨rest, hrest, hrels⟩ := instantiateDis_rel hρ hD htail
          have he : (q, w) :: tail = ds := by
            simpa [instantiateDis, hw0, htail, Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map] using hw
          subst ds
          exact ⟨_, by simp [instantiateDis, hv, hrest, Bind.bind, Except.bind, Pure.pure, Except.pure], .cons hrel hrels⟩
end

end Lara.Context.Holes
