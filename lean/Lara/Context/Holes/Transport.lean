import Lara.Context.Holes
import Lara.Context.Holes.Assurance

/-! Functional and relational backend transport through answer substitution.
The surrounding frame and its supplied answer terms both constrain transport.
The old merge's injectivity requirement remains a certificate-transport premise,
never an assumption that hole substitution is injective. -/
set_option autoImplicit false

namespace Lara.Context.Holes
open Lara.Support Lara.Attack Lara.Compile Lara.Erase

def mapTemplateAttack (f : Assurance → Assurance) : TemplateAttack → TemplateAttack
  | .rebut s t => .rebut (mapTemplate f s) (mapTemplate f t)
  | .undercut s t π => .undercut (mapTemplate f s) (mapTemplate f t) π
  | .undermine s t π => .undermine (mapTemplate f s) (mapTemplate f t) π

def mapHoleFragment (f : Assurance → Assurance) (F : HoleFragment) : HoleFragment :=
  { F with args := mapTemplates f F.args, atts := F.atts.map (mapTemplateAttack f) }

/-- Substitution commutes with certificate mapping at both attack endpoints. -/
theorem instantiateAttack_map (f : Assurance → Assurance) (ρ : Filling) (k : TemplateAttack) :
    instantiateAttack (mapFilling f ρ) (mapTemplateAttack f k) =
      (instantiateAttack ρ k).map (mapAssurAtt f) := by
  cases k with
  | rebut s t =>
    simp only [mapTemplateAttack, instantiateAttack, instantiateAux_map]
    cases instantiateAux ρ s <;> cases instantiateAux ρ t <;> rfl
  | undercut s t π =>
    simp only [mapTemplateAttack, instantiateAttack, instantiateAux_map]
    cases instantiateAux ρ s <;> cases instantiateAux ρ t <;> rfl
  | undermine s t π =>
    simp only [mapTemplateAttack, instantiateAttack, instantiateAux_map]
    cases instantiateAux ρ s <;> cases instantiateAux ρ t <;> rfl

theorem instantiateAttacks_map (f : Assurance → Assurance) (ρ : Filling)
    (ks : List TemplateAttack) :
    instantiateAttacks (mapFilling f ρ) (ks.map (mapTemplateAttack f)) =
      (instantiateAttacks ρ ks).map (List.map (mapAssurAtt f)) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.map_cons, instantiateAttacks, instantiateAttack_map, ih]
    cases instantiateAttack ρ k <;> cases instantiateAttacks ρ ks <;> rfl

/-- All fragment endpoints commute with assurance mapping, including failures. -/
theorem instantiateFragment_map (f : Assurance → Assurance) (ρ : Filling) (F : HoleFragment) :
    instantiateFragment (mapFilling f ρ) (mapHoleFragment f F) =
      (instantiateFragment ρ F).map (mapAssurFrag f) := by
  simp only [instantiateFragment, firstDuplicate_map]
  cases firstDuplicate ρ with
  | some h => rfl
  | none =>
    simp only [mapHoleFragment, instantiateList_map, instantiateAttacks_map]
    cases hw : instantiateList ρ F.args with
    | error e => rfl
    | ok ws =>
      cases hk : instantiateAttacks ρ F.atts with
      | error e => rfl
      | ok ks =>
        simp [Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure,
          realize, mapAssurFrag, mapAssurList_eq]

/-- Fillings belong to the surrounding context just as its declared terms do. -/
structure FixesContext (f : Assurance → Assurance) (C : HoleContext) : Prop where
  frame : Lara.Context.FixesContext f C.frame
  filling : mapFilling f C.filling = C.filling

/-- Context-local functional replacement fixes both frame and supplied answers. -/
theorem obsGen_congr {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
    {f : Assurance → Assurance} {C : HoleContext} {F : HoleFragment} {G : Fragment}
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hi : instantiateFragment C.filling F = .ok G)
    (hadm : Admissible reg₁ C.frame G) (hfix : FixesContext f C) :
    obsGen g reg₁ C F = obsGen g reg₂ C (mapHoleFragment f F) := by
  have hm := instantiateFragment_map f C.filling F
  rw [hfix.filling, hi] at hm
  change instantiateFragment C.filling (mapHoleFragment f F) = .ok (mapAssurFrag f G) at hm
  rw [obsGen_of_instantiate g reg₁ hi, obsGen_of_instantiate g reg₂ hm,
    Lara.Context.obsGen_congr g hf hpres hadm hfix.frame]

theorem backend_replacement_congruence_sem (sem : Semantics.ExtensionSemantics)
    {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
    {f : Assurance → Assurance} {C : HoleContext} {F : HoleFragment} {G : Fragment}
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hi : instantiateFragment C.filling F = .ok G)
    (hadm : Admissible reg₁ C.frame G) (hfix : FixesContext f C) :
    obsSem sem reg₁ C F = obsSem sem reg₂ C (mapHoleFragment f F) :=
  obsGen_congr _ hf hpres hi hadm hfix

theorem backend_replacement_congruence
    {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
    {f : Assurance → Assurance} {C : HoleContext} {F : HoleFragment} {G : Fragment}
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hi : instantiateFragment C.filling F = .ok G)
    (hadm : Admissible reg₁ C.frame G) (hfix : FixesContext f C) :
    obs reg₁ C F = obs reg₂ C (mapHoleFragment f F) :=
  obsGen_congr _ hf hpres hi hadm hfix

/-- Relate every endpoint structurally, retaining the attack kind and position. -/
inductive RelTemplateAttack (R : Assurance → Assurance → Prop) :
    TemplateAttack → TemplateAttack → Prop where
  | rebut {s₁ s₂ t₁ t₂ : Template} (hs : RelTemplate R s₁ s₂) (ht : RelTemplate R t₁ t₂) :
      RelTemplateAttack R (.rebut s₁ t₁) (.rebut s₂ t₂)
  | undercut {s₁ s₂ t₁ t₂ : Template} {π : Pos}
      (hs : RelTemplate R s₁ s₂) (ht : RelTemplate R t₁ t₂) :
      RelTemplateAttack R (.undercut s₁ t₁ π) (.undercut s₂ t₂ π)
  | undermine {s₁ s₂ t₁ t₂ : Template} {π : Pos}
      (hs : RelTemplate R s₁ s₂) (ht : RelTemplate R t₁ t₂) :
      RelTemplateAttack R (.undermine s₁ t₁ π) (.undermine s₂ t₂ π)

/-- Related templates and related filling terms produce related core attacks. -/
theorem instantiateAttack_rel {R : Assurance → Assurance → Prop} {ρ σ : Filling}
    {k₁ k₂ : TemplateAttack} {a₁ : Attack}
    (hρ : RelFilling R ρ σ) (hk : RelTemplateAttack R k₁ k₂)
    (hi : instantiateAttack ρ k₁ = .ok a₁) :
    ∃ a₂, instantiateAttack σ k₂ = .ok a₂ ∧ RelAtt R a₁ a₂ := by
  cases hk with
  | @rebut s₁ s₂ t₁ t₂ hs ht =>
    cases es : instantiateAux ρ s₁ with
    | error e => simp [instantiateAttack, es, Bind.bind, Except.bind] at hi
    | ok s₁' =>
      cases et : instantiateAux ρ t₁ with
      | error e => simp [instantiateAttack, es, et, Bind.bind, Except.bind] at hi
      | ok t₁' =>
        simp [instantiateAttack, es, et, Bind.bind, Except.bind, Pure.pure, Except.pure] at hi
        subst a₁
        obtain ⟨s₂', es₂, hsr⟩ := instantiateAux_rel hρ hs es
        obtain ⟨t₂', et₂, htr⟩ := instantiateAux_rel hρ ht et
        refine ⟨.rebut s₂' t₂', ?_, .rebut hsr htr⟩
        simp [instantiateAttack, es₂, et₂, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | @undercut s₁ s₂ t₁ t₂ π hs ht =>
    cases es : instantiateAux ρ s₁ with
    | error e => simp [instantiateAttack, es, Bind.bind, Except.bind] at hi
    | ok s₁' =>
      cases et : instantiateAux ρ t₁ with
      | error e => simp [instantiateAttack, es, et, Bind.bind, Except.bind] at hi
      | ok t₁' =>
        simp [instantiateAttack, es, et, Bind.bind, Except.bind, Pure.pure, Except.pure] at hi
        subst a₁
        obtain ⟨s₂', es₂, hsr⟩ := instantiateAux_rel hρ hs es
        obtain ⟨t₂', et₂, htr⟩ := instantiateAux_rel hρ ht et
        refine ⟨.undercut s₂' t₂' π, ?_, .undercut hsr htr⟩
        simp [instantiateAttack, es₂, et₂, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | @undermine s₁ s₂ t₁ t₂ π hs ht =>
    cases es : instantiateAux ρ s₁ with
    | error e => simp [instantiateAttack, es, Bind.bind, Except.bind] at hi
    | ok s₁' =>
      cases et : instantiateAux ρ t₁ with
      | error e => simp [instantiateAttack, es, et, Bind.bind, Except.bind] at hi
      | ok t₁' =>
        simp [instantiateAttack, es, et, Bind.bind, Except.bind, Pure.pure, Except.pure] at hi
        subst a₁
        obtain ⟨s₂', es₂, hsr⟩ := instantiateAux_rel hρ hs es
        obtain ⟨t₂', et₂, htr⟩ := instantiateAux_rel hρ ht et
        refine ⟨.undermine s₂' t₂' π, ?_, .undermine hsr htr⟩
        simp [instantiateAttack, es₂, et₂, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem instantiateAttacks_rel {R : Assurance → Assurance → Prop} {ρ σ : Filling}
    {ks₁ ks₂ : List TemplateAttack} {as₁ : List Attack}
    (hρ : RelFilling R ρ σ) (hk : Forall₂ (RelTemplateAttack R) ks₁ ks₂)
    (hi : instantiateAttacks ρ ks₁ = .ok as₁) :
    ∃ as₂, instantiateAttacks σ ks₂ = .ok as₂ ∧ Forall₂ (RelAtt R) as₁ as₂ := by
  induction hk generalizing as₁ with
  | nil => simp [instantiateAttacks] at hi; subst as₁; exact ⟨[], rfl, .nil⟩
  | @cons k₁ k₂ ks₁ ks₂ hk hks ih =>
    cases he : instantiateAttack ρ k₁ with
    | error e => simp [instantiateAttacks, he, Bind.bind, Except.bind] at hi
    | ok a₁ =>
      cases hs : instantiateAttacks ρ ks₁ with
      | error e => simp [instantiateAttacks, he, hs, Bind.bind, Except.bind] at hi
      | ok rest₁ =>
        simp [instantiateAttacks, he, hs, Bind.bind, Except.bind, Pure.pure, Except.pure] at hi
        subst as₁
        obtain ⟨a₂, he₂, hr⟩ := instantiateAttack_rel hρ hk he
        obtain ⟨rest₂, hs₂, hrs⟩ := ih hs
        refine ⟨a₂ :: rest₂, ?_, .cons hr hrs⟩
        simp [instantiateAttacks, he₂, hs₂, Bind.bind, Except.bind, Pure.pure, Except.pure]

structure RelHoleFragment (R : Assurance → Assurance → Prop) (F G : HoleFragment) : Prop where
  sigma : G.sigma = F.sigma
  policy : G.policy = F.policy
  gammaFrag : G.gammaFrag = F.gammaFrag
  ground : G.ground = F.ground
  imports : G.imports = F.imports
  exports : G.exports = F.exports
  args : RelTemplates R F.args G.args
  atts : Forall₂ (RelTemplateAttack R) F.atts G.atts

/-- A structural template relation survives successful substitution. The target
fragment is constructed here; no equality or relation of final outputs is assumed. -/
theorem instantiateFragment_rel {R : Assurance → Assurance → Prop} {ρ σ : Filling}
    {F₁ F₂ : HoleFragment} {G₁ : Fragment}
    (hρ : RelFilling R ρ σ) (hn : FillingNodup σ) (hF : RelHoleFragment R F₁ F₂)
    (hi : instantiateFragment ρ F₁ = .ok G₁) :
    ∃ G₂, instantiateFragment σ F₂ = .ok G₂ ∧ RelFrag R G₁ G₂ := by
  obtain ⟨_, ws₁, ks₁, hw₁, hk₁, rfl⟩ := instantiateFragment_inv hi
  obtain ⟨ws₂, hw₂, hwr⟩ := instantiateList_rel hρ hF.args hw₁
  obtain ⟨ks₂, hk₂, hkr⟩ := instantiateAttacks_rel hρ hF.atts hk₁
  refine ⟨realize F₂ ws₂ ks₂, ?_, ?_⟩
  · simp [instantiateFragment, (firstDuplicate_none_iff _).mpr hn,
      hw₂, hk₂, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · exact ⟨hF.sigma, hF.policy, hF.gammaFrag, hF.ground, hF.imports, hF.exports,
      relTerms_iff_forall₂.mp hwr, hkr⟩

structure RelFixesContext (R : Assurance → Assurance → Prop) (C : HoleContext) : Prop where
  frame : Lara.Context.RelFixesContext R C.frame
  filling : RelFilling R C.filling C.filling

/-- Relational backend replacement derives the relation of instantiated
fragments, then uses the existing carrier theorem. RelInj is retained. -/
theorem obsGen_parametricity {α : Type} (g : Invariants.StructuredAF → Atom → α)
    {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
    {R : Assurance → Assurance → Prop} {C : HoleContext}
    {F₁ F₂ : HoleFragment} {G₁ : Fragment}
    (hR : RelInj R) (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hi : instantiateFragment C.filling F₁ = .ok G₁)
    (hadm : Admissible reg₁ C.frame G₁) (hF : RelHoleFragment R F₁ F₂)
    (hfix : RelFixesContext R C) :
    obsGen g reg₁ C F₁ = obsGen g reg₂ C F₂ := by
  obtain ⟨G₂, hi₂, hG⟩ := instantiateFragment_rel hfix.filling
    (instantiateFragment_inv hi).1 hF hi
  rw [obsGen_of_instantiate g reg₁ hi, obsGen_of_instantiate g reg₂ hi₂,
    Lara.Context.obsGen_parametricity g hR hpres hadm hG hfix.frame]

theorem backend_replacement_parametricity_sem (sem : Semantics.ExtensionSemantics)
    {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
    {R : Assurance → Assurance → Prop} {C : HoleContext}
    {F₁ F₂ : HoleFragment} {G₁ : Fragment}
    (hR : RelInj R) (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hi : instantiateFragment C.filling F₁ = .ok G₁)
    (hadm : Admissible reg₁ C.frame G₁) (hF : RelHoleFragment R F₁ F₂)
    (hfix : RelFixesContext R C) :
    obsSem sem reg₁ C F₁ = obsSem sem reg₂ C F₂ :=
  obsGen_parametricity _ hR hpres hi hadm hF hfix

theorem backend_replacement_parametricity
    {canon : String → String} {reg₁ reg₂ : BackendRegistry canon}
    {R : Assurance → Assurance → Prop} {C : HoleContext}
    {F₁ F₂ : HoleFragment} {G₁ : Fragment}
    (hR : RelInj R) (hpres : RelPreserving R (certOkOf reg₁) (certOkOf reg₂))
    (hi : instantiateFragment C.filling F₁ = .ok G₁)
    (hadm : Admissible reg₁ C.frame G₁) (hF : RelHoleFragment R F₁ F₂)
    (hfix : RelFixesContext R C) :
    obs reg₁ C F₁ = obs reg₂ C F₂ :=
  obsGen_parametricity _ hR hpres hi hadm hF hfix

end Lara.Context.Holes
