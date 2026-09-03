/-
# Theory M4, phase F1 — composition of contexts (D11)

Congruence is unstateable without composition: "unobservable in every
compatible context" is a closure property only if contexts are themselves
closed under plugging one into another. This module proves that closure and the
algebra of a composite's interface.

**What associativity means here.** `compose` is not associative on the nose,
and claiming it were would be false rather than hard: `residualImports` filters
and concatenates two lists and the structural merge keeps the last occurrence
of each term, so the two bracketings of a triple produce lists that differ in
*order* whenever the same identifier or term is contributed by more than one
side. What is true — and what closure needs — is that the two bracketings
declare the same leaves, owe the same imports, and carry the same material.
Every statement below is therefore membership-level, and `compose_assoc_mem`
bundles them.
-/

import Lara.Context.Link

namespace Lara.Context

open Lara.Support Lara.Attack Lara.Compile

/-! ### The composition guard -/

/-- **The composition guard, characterized.** The same two classes as the link
guard minus R-L2: a composite may still owe imports. -/
theorem composeOk_eq_true_iff {C D : Context} :
    composeOk C D = true ↔
      C.frame.declared.Nodup ∧ D.frame.declared.Nodup ∧
      (∀ l ∈ C.frame.declared, l ∉ D.frame.declared) ∧
      C.frame.sigma = D.frame.sigma ∧ C.frame.policy = D.frame.policy := by
  rw [composeOk, Option.isNone_iff_eq_none, composeFault]
  cases hH : idHygieneFault C.frame D.frame with
  | some fault =>
      simp only [reduceCtorEq, false_iff, not_and]
      intro hnd1 hnd2 hdisj
      exact absurd (idHygieneFault_none_iff.mpr ⟨hnd1, hnd2, hdisj⟩) (by rw [hH]; simp)
  | none =>
      obtain ⟨hnd1, hnd2, hdisj⟩ := idHygieneFault_none_iff.mp hH
      rw [sigmaPolicyFault_none_iff]
      constructor
      · rintro ⟨hs, hp⟩; exact ⟨hnd1, hnd2, hdisj, hs, hp⟩
      · rintro ⟨-, -, -, hs, hp⟩; exact ⟨hs, hp⟩

theorem compose_eq_some {C D : Context} (h : composeOk C D = true) :
    compose C D = some (composedContext C D) := by
  simp only [compose, if_pos h]

theorem compose_eq_none {C D : Context} (h : composeOk C D = false) :
    compose C D = none := by
  simp only [compose, h, Bool.false_eq_true, if_false]

/-- A rejected composition carries a fault witness. -/
theorem exists_fault_of_not_composeOk {C D : Context} (h : composeOk C D = false) :
    ∃ fault, composeFault C D = some fault := by
  rw [composeOk, Bool.eq_false_iff, Ne, Option.isNone_iff_eq_none] at h
  exact Option.ne_none_iff_exists'.mp h

/-- A successful composition is *the* composite. -/
theorem eq_composedContext {C D E : Context} (h : compose C D = some E) :
    composeOk C D = true ∧ E = composedContext C D := by
  by_cases hok : composeOk C D = true
  · exact ⟨hok, Option.some.inj (h.symm.trans (compose_eq_some hok))⟩
  · rw [Bool.not_eq_true] at hok
    rw [compose_eq_none hok] at h
    exact absurd h (by simp)

/-! ### What a composite declares, owes, and carries -/

theorem mem_residualImports {C D : Context} {l : LeafId} :
    l ∈ (residualImports C D).leaves ↔
      (l ∈ C.frame.imports.leaves ∧ l ∉ D.frame.declared) ∨
      (l ∈ D.frame.imports.leaves ∧ l ∉ C.frame.declared) := by
  simp [residualImports, mem_dedupList, List.mem_filter]

theorem composed_declared {C D : Context} {l : LeafId} :
    l ∈ (composedContext C D).frame.declared ↔
      l ∈ C.frame.declared ∨ l ∈ D.frame.declared := by
  simp only [composedContext, Fragment.declared, List.map_append, List.mem_append]

theorem composed_args {C D : Context} {w : SupportTerm} :
    w ∈ (composedContext C D).frame.args ↔
      w ∈ C.frame.args ∨ w ∈ D.frame.args := by
  simp only [composedContext, mem_dedupList, List.mem_append]

theorem composed_atts {C D : Context} {k : Attack} :
    k ∈ (composedContext C D).frame.atts ↔
      k ∈ C.frame.atts ∨ k ∈ D.frame.atts := by
  simp only [composedContext, List.mem_append]

theorem composed_imports {C D : Context} {l : LeafId} :
    l ∈ (composedContext C D).frame.imports.leaves ↔
      (l ∈ C.frame.imports.leaves ∧ l ∉ D.frame.declared) ∨
      (l ∈ D.frame.imports.leaves ∧ l ∉ C.frame.declared) :=
  mem_residualImports

/-- A composite's declared identifiers stay duplicate-free: R-L1 survives
composition, which is what lets a composite be linked in turn. -/
theorem composed_ownIds {C D : Context} (hok : composeOk C D = true) :
    (composedContext C D).frame.declared.Nodup := by
  obtain ⟨hC, hD, hdisj, -, -⟩ := composeOk_eq_true_iff.mp hok
  show (List.map (·.1) (C.frame.gammaFrag ++ D.frame.gammaFrag)).Nodup
  rw [List.map_append]
  refine List.nodup_append.mpr ⟨hC, hD, ?_⟩
  intro a ha b hb hab
  exact hdisj a ha (hab ▸ hb)

/-! ### Closure: a composite is a context that links

The point of composition. Given a fragment whose imports the composite as a
whole satisfies and whose declarations clash with neither side, the link guard
holds of the composite — so the congruence theorem's quantifier, which ranges
over contexts, already ranges over every composite. -/

theorem linkOk_composed {C D : Context} {F : Fragment}
    (hok : composeOk C D = true)
    (hF : F.declared.Nodup)
    (hdisjC : ∀ l ∈ C.frame.declared, l ∉ F.declared)
    (hdisjD : ∀ l ∈ D.frame.declared, l ∉ F.declared)
    (himp : ∀ l ∈ F.imports.leaves, l ∈ C.frame.declared ∨ l ∈ D.frame.declared)
    (hres : ∀ l ∈ (composedContext C D).frame.imports.leaves, l ∈ F.declared)
    (hsigma : C.frame.sigma = F.sigma) (hpolicy : C.frame.policy = F.policy) :
    linkOk (composedContext C D) F = true := by
  refine linkOk_eq_true_iff.mpr
    ⟨composed_ownIds hok, hF, ?_, ?_, hres, hsigma, hpolicy⟩
  · intro l hl
    rcases composed_declared.mp hl with h | h
    · exact hdisjC l h
    · exact hdisjD l h
  · intro l hl
    rcases himp l hl with h | h
    · exact composed_declared.mpr (Or.inl h)
    · exact composed_declared.mpr (Or.inr h)

/-! ### Associativity, at the level at which it holds -/

/-- The propositional shape of residual-import associativity, isolated from the
list plumbing. -/
private theorem residual_assoc_prop (iC iD iE dC dD dE : Prop) :
    ((((iC ∧ ¬dD) ∨ (iD ∧ ¬dC)) ∧ ¬dE) ∨ (iE ∧ ¬(dC ∨ dD)))
      ↔ ((iC ∧ ¬(dD ∨ dE)) ∨ (((iD ∧ ¬dE) ∨ (iE ∧ ¬dD)) ∧ ¬dC)) := by
  constructor
  · rintro (⟨(⟨hi, hnd⟩ | ⟨hi, hnc⟩), hne⟩ | ⟨hi, hn⟩)
    · exact Or.inl ⟨hi, fun h => h.elim hnd hne⟩
    · exact Or.inr ⟨Or.inl ⟨hi, hne⟩, hnc⟩
    · exact Or.inr ⟨Or.inr ⟨hi, fun h => hn (Or.inr h)⟩, fun h => hn (Or.inl h)⟩
  · rintro (⟨hi, hn⟩ | ⟨(⟨hi, hne⟩ | ⟨hi, hnd⟩), hnc⟩)
    · exact Or.inl ⟨Or.inl ⟨hi, fun h => hn (Or.inl h)⟩, fun h => hn (Or.inr h)⟩
    · exact Or.inl ⟨Or.inr ⟨hi, hnc⟩, hne⟩
    · exact Or.inr ⟨hi, fun h => h.elim hnc hnd⟩

variable {C D E : Context}

/-- **The residual interface associates.** What a triple still owes does not
depend on the bracketing. -/
theorem residualImports_assoc {l : LeafId} :
    l ∈ (composedContext (composedContext C D) E).frame.imports.leaves ↔
      l ∈ (composedContext C (composedContext D E)).frame.imports.leaves := by
  rw [composed_imports, composed_imports, composed_imports, composed_imports,
    composed_declared, composed_declared]
  exact residual_assoc_prop _ _ _ _ _ _

/-- **The composition guard associates.** Pairwise compatibility of three
contexts makes both bracketings defined — so "composite" is not a shape that
can only be built one way round. -/
theorem composeOk_assoc_left
    (hCD : composeOk C D = true) (hDE : composeOk D E = true)
    (hCE : composeOk C E = true) :
    composeOk (composedContext C D) E = true := by
  obtain ⟨hC, hD, hCDdisj, hCDsig, hCDpol⟩ := composeOk_eq_true_iff.mp hCD
  obtain ⟨-, hE, hDEdisj, -, -⟩ := composeOk_eq_true_iff.mp hDE
  obtain ⟨-, -, hCEdisj, hCEsig, hCEpol⟩ := composeOk_eq_true_iff.mp hCE
  refine composeOk_eq_true_iff.mpr ⟨composed_ownIds hCD, hE, ?_, hCEsig, hCEpol⟩
  intro l hl
  rcases composed_declared.mp hl with h | h
  · exact hCEdisj l h
  · exact hDEdisj l h

theorem composeOk_assoc_right
    (hCD : composeOk C D = true) (hDE : composeOk D E = true)
    (hCE : composeOk C E = true) :
    composeOk C (composedContext D E) = true := by
  obtain ⟨hC, -, hCDdisj, hCDsig, hCDpol⟩ := composeOk_eq_true_iff.mp hCD
  obtain ⟨-, -, -, hDEsig, hDEpol⟩ := composeOk_eq_true_iff.mp hDE
  obtain ⟨-, -, hCEdisj, -, -⟩ := composeOk_eq_true_iff.mp hCE
  refine composeOk_eq_true_iff.mpr ⟨hC, composed_ownIds hDE, ?_, hCDsig, hCDpol⟩
  intro l hl hcon
  rcases composed_declared.mp hcon with h | h
  · exact hCDdisj l hl h
  · exact hCEdisj l hl h

/-- The remaining components associate on the nose: Σ and the policy are the
left frame's, and the ground and export lists are concatenations. -/
theorem compose_assoc_fields :
    (composedContext (composedContext C D) E).frame.sigma
        = (composedContext C (composedContext D E)).frame.sigma ∧
      (composedContext (composedContext C D) E).frame.policy
        = (composedContext C (composedContext D E)).frame.policy ∧
      (composedContext (composedContext C D) E).frame.ground
        = (composedContext C (composedContext D E)).frame.ground ∧
      (composedContext (composedContext C D) E).frame.exports
        = (composedContext C (composedContext D E)).frame.exports :=
  ⟨rfl, rfl, List.append_assoc _ _ _, List.append_assoc _ _ _⟩

/-- **The material associates.** Both bracketings declare the same leaves and
carry the same arguments and attacks. -/
theorem compose_assoc_mem :
    (∀ l : LeafId, l ∈ (composedContext (composedContext C D) E).frame.declared ↔
        l ∈ (composedContext C (composedContext D E)).frame.declared) ∧
    (∀ w : SupportTerm, w ∈ (composedContext (composedContext C D) E).frame.args ↔
        w ∈ (composedContext C (composedContext D E)).frame.args) ∧
    (∀ k : Attack, k ∈ (composedContext (composedContext C D) E).frame.atts ↔
        k ∈ (composedContext C (composedContext D E)).frame.atts) ∧
    (∀ l : LeafId, l ∈ (composedContext (composedContext C D) E).frame.imports.leaves ↔
        l ∈ (composedContext C (composedContext D E)).frame.imports.leaves) := by
  refine ⟨fun l => ?_, fun w => ?_, fun k => ?_, fun l => residualImports_assoc⟩
  · rw [composed_declared, composed_declared, composed_declared, composed_declared,
      or_assoc]
  · rw [composed_args, composed_args, composed_args, composed_args, or_assoc]
  · rw [composed_atts, composed_atts, composed_atts, composed_atts, or_assoc]

/-! ### A composite is linkable only if its halves already cover each other

`compose` does **not** saturate. Saturation is `link`'s job, and `link` covers
the conflicts between the *whole* context and the fragment — not the conflicts
between the two halves of a composite. So a composite of two contexts that
attack each other across their own boundary is not `SideOk`, and therefore not
admissible: the missing edges are exactly the ones no later step emits.

That is a real boundary of the calculus, not an oversight of this lemma, and it
is why the cross-coverage hypotheses below are explicit rather than derived.
Making `compose` saturate would give it a registry and a Γ — which it does not
have, by design, since a context is data — so the alternative is tracked
separately rather than folded in here. -/

/-- **Composite linkability, from the halves.** The four quadrants of
`AttackComplete` over the composite: two within-side, discharged by each half's
own `SideOk`, and two cross-boundary, which the halves must already cover
because nothing downstream will. -/
theorem sideOk_composed {canon : String → String} {reg : BackendRegistry canon}
    {Gamma : LeafId → Option Atom} {P : Policy.Policy} {C D : Context}
    (hC : SideOk canon reg Gamma P C.frame.args C.frame.atts)
    (hD : SideOk canon reg Gamma P D.frame.args D.frame.atts)
    (hcross : ∀ source ∈ C.frame.args, ∀ target ∈ D.frame.args,
      ∀ Cs Ct, HasSupport canon P.ruleLookup Gamma (certOkOf reg) source Cs [] →
        HasSupport canon P.ruleLookup Gamma (certOkOf reg) target Ct [] →
        Attack.ContraryMatch canon P.defeat Cs Ct →
        Compile.ConflictAttackable P.ruleLookup target →
        Compile.Covered (C.frame.atts ++ D.frame.atts) source target)
    (hcross' : ∀ source ∈ D.frame.args, ∀ target ∈ C.frame.args,
      ∀ Cs Ct, HasSupport canon P.ruleLookup Gamma (certOkOf reg) source Cs [] →
        HasSupport canon P.ruleLookup Gamma (certOkOf reg) target Ct [] →
        Attack.ContraryMatch canon P.defeat Cs Ct →
        Compile.ConflictAttackable P.ruleLookup target →
        Compile.Covered (C.frame.atts ++ D.frame.atts) source target) :
    SideOk canon reg Gamma P (composedContext C D).frame.args
      (composedContext C D).frame.atts where
  support := by
    intro w hw
    rcases (composed_args (C := C) (D := D)).mp hw with h | h
    · exact hC.support w h
    · exact hD.support w h
  typed := by
    intro k hk
    rcases (composed_atts (C := C) (D := D)).mp hk with h | h
    · exact hC.typed k h
    · exact hD.typed k h
  source_declared := by
    intro k hk
    rcases (composed_atts (C := C) (D := D)).mp hk with h | h
    · exact composed_args.mpr (Or.inl (hC.source_declared k h))
    · exact composed_args.mpr (Or.inr (hD.source_declared k h))
  target_declared := by
    intro k hk
    rcases (composed_atts (C := C) (D := D)).mp hk with h | h
    · exact composed_args.mpr (Or.inl (hC.target_declared k h))
    · exact composed_args.mpr (Or.inr (hD.target_declared k h))
  attack_complete := by
    intro source hs target ht Cs Ct hsSup htSup hcm hca
    have hleft : ∀ k ∈ C.frame.atts, k ∈ (composedContext C D).frame.atts :=
      fun k hk => composed_atts.mpr (Or.inl hk)
    have hright : ∀ k ∈ D.frame.atts, k ∈ (composedContext C D).frame.atts :=
      fun k hk => composed_atts.mpr (Or.inr hk)
    have hboth : ∀ k ∈ C.frame.atts ++ D.frame.atts,
        k ∈ (composedContext C D).frame.atts := by
      intro k hk
      rcases List.mem_append.mp hk with h | h
      · exact hleft k h
      · exact hright k h
    rcases (composed_args (C := C) (D := D)).mp hs with hsC | hsD <;>
      rcases (composed_args (C := C) (D := D)).mp ht with htC | htD
    · exact covered_mono hleft
        (hC.attack_complete source hsC target htC Cs Ct hsSup htSup hcm hca)
    · exact covered_mono hboth (hcross source hsC target htD Cs Ct hsSup htSup hcm hca)
    · exact covered_mono hboth (hcross' source hsD target htC Cs Ct hsSup htSup hcm hca)
    · exact covered_mono hright
        (hD.attack_complete source hsD target htD Cs Ct hsSup htSup hcm hca)

end Lara.Context
