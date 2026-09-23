/-
# Finite realization of partial-injective assurance relations

Only finitely many pairs are needed to realize a fragment and its context.
Extending an arbitrary infinite partial injection in its entirety is false;
this construction instead extends its restriction to any given finite list.
-/
import Lara.Context.Parametricity

set_option autoImplicit false

namespace Lara.Context
open Lara.Support Lara.Attack Lara.Erase

/-- Exchange two assurances, leaving every other assurance fixed. -/
def swapAssurance (a b x : Assurance) : Assurance :=
  if x = a then b else if x = b then a else x

/-- An exchange is its own inverse, including when its endpoints coincide. -/
theorem swapAssurance_involutive (a b x : Assurance) :
    swapAssurance a b (swapAssurance a b x) = x := by
  unfold swapAssurance
  repeat first | split | simp_all

/-- Exchanging two assurances preserves injectivity. -/
theorem swapAssurance_injective (a b : Assurance) :
    Function.Injective (swapAssurance a b) := by
  intro x y h
  have := congrArg (swapAssurance a b) h
  simpa only [swapAssurance_involutive] using this

/-- Every finite restriction of a partial injection has a total injective
extension. No countability, range enumeration, or decidability of `R` is needed.
Pairs whose source is outside `xs` are deliberately unconstrained. -/
theorem exists_total_injective_extension_on {R : Assurance → Assurance → Prop}
    (hR : RelInj R) (xs : List Assurance) :
    ∃ f : Assurance → Assurance, Function.Injective f ∧
      ∀ a ∈ xs, ∀ b, R a b → f a = b := by
  classical
  induction xs with
  | nil => exact ⟨id, fun _ _ h => h, by simp⟩
  | cons a xs ih =>
    obtain ⟨f, hf, hext⟩ := ih
    by_cases ha : ∃ b, R a b
    · obtain ⟨b, hab⟩ := ha
      refine ⟨fun x => swapAssurance (f a) b (f x),
        fun _ _ h => hf (swapAssurance_injective _ _ h), ?_⟩
      intro x hx y hxy
      rcases List.mem_cons.mp hx with rfl | hx
      · have hy := relInj_functional hR hab hxy
        simp [swapAssurance, hy]
      · by_cases hxa : x = a
        · subst x
          have hy := relInj_functional hR hab hxy
          simp [swapAssurance, hy]
        · have hfa : f x ≠ f a := fun h => hxa (hf h)
          have hfb : f x ≠ b := by
            intro h
            have hy : y = b := (hext x hx y hxy).symm.trans h
            exact hxa ((hR _ _ _ _ hxy hab).mpr hy)
          simpa only [swapAssurance, if_neg hfa, if_neg hfb] using hext x hx y hxy
    · refine ⟨f, hf, ?_⟩
      intro x hx y hxy
      rcases List.mem_cons.mp hx with rfl | hx
      · exact False.elim (ha ⟨y, hxy⟩)
      · exact hext x hx y hxy


mutual
  /-- Agreement on a term's occurrences realizes its relational image. -/
  theorem relTerm_eq_mapAssur {R : Assurance → Assurance → Prop}
      (f : Assurance → Assurance) : ∀ {w₁ w₂ : SupportTerm},
      RelTerm R w₁ w₂ →
      (∀ a ∈ occurs w₁, ∀ b, R a b → f a = b) → w₂ = mapAssur f w₁
    | _, _, .leaf _, _ => rfl
    | _, _, .inst hws hD ha, h => by
      simp only [mapAssur]
      rw [relTerms_eq_mapAssurList f hws (fun a ha => h a (by simp [occurs, ha])),
        relDis_eq_mapAssurDis f hD (fun a ha => h a (by simp [occurs, ha])),
        h _ (by simp [occurs]) _ ha]
  /-- Agreement on premise occurrences realizes the related premise list. -/
  theorem relTerms_eq_mapAssurList {R : Assurance → Assurance → Prop}
      (f : Assurance → Assurance) : ∀ {ws₁ ws₂ : List SupportTerm},
      RelTerms R ws₁ ws₂ →
      (∀ a ∈ occursList ws₁, ∀ b, R a b → f a = b) →
      ws₂ = mapAssurList f ws₁
    | _, _, .nil, _ => rfl
    | _, _, .cons hw hws, h => by
      simp only [mapAssurList]
      rw [relTerm_eq_mapAssur f hw (fun a ha => h a (by simp [occursList, ha])),
        relTerms_eq_mapAssurList f hws (fun a ha => h a (by simp [occursList, ha]))]
  /-- Agreement on discharge occurrences realizes the related discharge list. -/
  theorem relDis_eq_mapAssurDis {R : Assurance → Assurance → Prop}
      (f : Assurance → Assurance) : ∀ {D₁ D₂ : List (QuestionId × SupportTerm)},
      RelDis R D₁ D₂ →
      (∀ a ∈ occursDis D₁, ∀ b, R a b → f a = b) →
      D₂ = mapAssurDis f D₁
    | _, _, .nil, _ => rfl
    | _, _, .cons hw hD, h => by
      simp only [mapAssurDis]
      rw [relTerm_eq_mapAssur f hw (fun a ha => h a (by simp [occursDis, ha])),
        relDis_eq_mapAssurDis f hD (fun a ha => h a (by simp [occursDis, ha]))]
end

/-- Agreement on an attack's occurrences realizes its relational image. -/
theorem relAtt_eq_mapAssurAtt {R : Assurance → Assurance → Prop}
    (f : Assurance → Assurance) {k₁ k₂ : Attack.Attack} (hk : RelAtt R k₁ k₂)
    (h : ∀ a ∈ occursAtt k₁, ∀ b, R a b → f a = b) :
    k₂ = mapAssurAtt f k₁ := by
  cases hk with
  | rebut hw hu | undercut hw hu | undermine hw hu =>
    simp only [mapAssurAtt]
    rw [relTerm_eq_mapAssur f hw (fun a ha => h a (by simp [occursAtt, ha])),
      relTerm_eq_mapAssur f hu (fun a ha => h a (by simp [occursAtt, ha]))]

/-- Agreement on every attack occurrence realizes a related attack list. -/
theorem relAtts_eq_map {R : Assurance → Assurance → Prop}
    (f : Assurance → Assurance) : ∀ {ks₁ ks₂ : List Attack.Attack},
    Forall₂ (RelAtt R) ks₁ ks₂ →
    (∀ a ∈ (ks₁.map occursAtt).flatten, ∀ b, R a b → f a = b) →
    ks₂ = ks₁.map (mapAssurAtt f)
  | _, _, .nil, _ => rfl
  | _, _, .cons hk hks, h => by
    simp only [List.map_cons]
    rw [relAtt_eq_mapAssurAtt f hk (fun a ha => h a (by simp [ha])),
      relAtts_eq_map f hks (fun a ha => h a (by simp [ha]))]

/-- A finite occurrence agreement realizes a whole fragment. -/
theorem relFrag_eq_mapAssurFrag {R : Assurance → Assurance → Prop}
    (f : Assurance → Assurance) {F₁ F₂ : Fragment} (hF : RelFrag R F₁ F₂)
    (h : ∀ a ∈ occurrences F₁, ∀ b, R a b → f a = b) :
    F₂ = mapAssurFrag f F₁ := by
  have hargs := relTerms_eq_mapAssurList f (relTerms_iff_forall₂.mpr hF.args)
    (fun a ha => h a (by simp [occurrences, ha]))
  have hatts := relAtts_eq_map f hF.atts
    (fun a ha => h a (by simp [occurrences, ha]))
  simp only [mapAssurList_eq] at hargs
  obtain ⟨hs, hp, hg, hground, hi, he, _, _⟩ := hF
  cases F₁; cases F₂
  simp_all [mapAssurFrag]

/-- Related fragments always have a total injective functional realization. -/
theorem relFrag_exists_injective {R : Assurance → Assurance → Prop}
    (hR : RelInj R) {F₁ F₂ : Fragment} (hF : RelFrag R F₁ F₂) :
    ∃ f : Assurance → Assurance, Function.Injective f ∧ F₂ = mapAssurFrag f F₁ := by
  obtain ⟨f, hf, hext⟩ := exists_total_injective_extension_on hR (occurrences F₁)
  exact ⟨f, hf, relFrag_eq_mapAssurFrag f hF hext⟩

/-- The same finite construction can realize the fragment while fixing all
context material, which is the structural part of functional congruence. -/
theorem relFrag_exists_injective_fixesContext {R : Assurance → Assurance → Prop}
    (hR : RelInj R) {F₁ F₂ : Fragment} {C : Context}
    (hF : RelFrag R F₁ F₂) (hC : RelFixesContext R C) :
    ∃ f : Assurance → Assurance, Function.Injective f ∧
      F₂ = mapAssurFrag f F₁ ∧ FixesContext f C := by
  obtain ⟨f, hf, hext⟩ := exists_total_injective_extension_on hR
    (occurrences F₁ ++ occurrences C.frame)
  refine ⟨f, hf, relFrag_eq_mapAssurFrag f hF
    (fun a ha => hext a (List.mem_append_left _ ha)), ?_⟩
  have hctx : ∀ a ∈ occurrences C.frame, ∀ b, R a b → f a = b :=
    fun a ha => hext a (List.mem_append_right _ ha)
  constructor
  · exact (mapAssurList_eq C.frame.args).symm.trans
      (relTerms_eq_mapAssurList f (relTerms_iff_forall₂.mpr hC.args)
        (fun a ha => hctx a (by simp [occurrences, ha]))).symm
  · exact (relAtts_eq_map f hC.atts
      (fun a ha => hctx a (by simp [occurrences, ha]))).symm


/-- A proper self-embedding: certificate backend versions advance by one. -/
def shiftAssurance : Assurance → Assurance
  | .none => .none
  | .trusted => .trusted
  | .cert b d c => .cert { b with version := b.version + 1 } d c

/-- The version shift loses no information. -/
theorem shiftAssurance_injective : Function.Injective shiftAssurance := by
  intro x y h
  cases x <;> cases y <;> simp_all [shiftAssurance]
  case cert.cert b d c b' d' c' =>
    cases b; cases b'
    simp_all

/-- No shifted certificate has backend version zero. -/
theorem shiftAssurance_ne_zero (x : Assurance) (name : String)
    (d : Digest) (c : CertRef) :
    shiftAssurance x ≠ .cert ⟨name, 0⟩ d c := by
  cases x <;> simp [shiftAssurance]

/-- The unrestricted extension is false on `Assurance`
itself. The inverse graph of the shift already exhausts the target type,
leaving no image for a certificate with backend version zero. -/
theorem not_every_relInj_has_total_extension :
    ¬ (∀ R : Assurance → Assurance → Prop, RelInj R →
      ∃ f : Assurance → Assurance, Function.Injective f ∧
        ∀ a b, R a b → f a = b) := by
  intro hall
  let R : Assurance → Assurance → Prop := fun a b => a = shiftAssurance b
  have hR : RelInj R := by
    intro a₁ a₂ b₁ b₂ h₁ h₂
    change a₁ = shiftAssurance b₁ at h₁
    change a₂ = shiftAssurance b₂ at h₂
    subst a₁; subst a₂
    exact ⟨fun h => shiftAssurance_injective h, congrArg shiftAssurance⟩
  obtain ⟨f, hf, hext⟩ := hall R hR
  let z : Assurance := .cert ⟨"extension-witness", 0⟩ ⟨"digest"⟩ ⟨.atom "payload"⟩
  have hz : f (shiftAssurance (f z)) = f z := hext _ _ rfl
  exact shiftAssurance_ne_zero (f z) _ _ _ (hf hz)

end Lara.Context
