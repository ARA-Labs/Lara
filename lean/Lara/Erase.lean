/-
# Result 9 — backend replacement (Theorem 2), Model A

Mechanizes spec §9 result 9 / `docs/strict-backend-decision.md:274` (Theorem 2:
"backend replacement preserves claim status") under the *uniform injective
certificate relabel* model.

`mapAssur f` rewrites every `Assurance` node of a support term through a single
function `f`, applied uniformly across the whole term forest. Two
`CheckedProgram`s related by such a relabel — `P₂.args = P₁.args.map (mapAssur f)`
and `P₂.atts = P₁.atts.map (mapAssurAtt f)` with `f` injective — compile to the
*same* abstract AF (identity node bijection, since AF nodes are list positions,
`Compile.toAF`), hence agree on every grounded label and every claim status.

This models a genuine backend swap: a source step certifies to one payload per
backend, so a shared source subterm carries the same payload at every
occurrence, and distinct source certificates stay distinct after the swap
(injectivity). Note the doc's non-injective erase-to-a-single-`certified`-marker
is *not* an isomorphism: collapsing distinct subterms can merge occurrences and
add subargument-closure edges. Injectivity-on-used-certs is the faithful
condition; both programs being well-checked `CheckedProgram`s discharges the
"accept the same strict instances" hypothesis. This is a Lean-only, additive
result: it touches no wire codec, no Haskell, and no differential anchor.
-/

import Lara.Compile

namespace Lara.Erase

open Lara.Support Lara.Attack Lara.Compile Lara.Grounded

/-! ### Uniform assurance relabeling -/

/- Relabel every assurance node of a support term through `f`, applied
uniformly. Mirrors `leaves`/`containsB`: explicit list recursion, since Lean
4.32 cannot recurse through `SupportTerm`'s nested `List` fields via a lambda. -/
mutual
  /-- Relabel every assurance node of a support term through `f`. -/
  def mapAssur (f : Assurance → Assurance) : SupportTerm → SupportTerm
    | .leaf l => .leaf l
    | .inst rn θ ws D H α =>
        .inst rn θ (mapAssurList f ws) (mapAssurDis f D) H (f α)
  def mapAssurList (f : Assurance → Assurance) :
      List SupportTerm → List SupportTerm
    | [] => []
    | w :: ws => mapAssur f w :: mapAssurList f ws
  def mapAssurDis (f : Assurance → Assurance) :
      List (QuestionId × SupportTerm) → List (QuestionId × SupportTerm)
    | [] => []
    | (q, w) :: rest => (q, mapAssur f w) :: mapAssurDis f rest
end

/-- Relabel the stored terms of an attack, preserving kind and position. -/
def mapAssurAtt (f : Assurance → Assurance) : Attack → Attack
  | .rebut w u => .rebut (mapAssur f w) (mapAssur f u)
  | .undercut w u π => .undercut (mapAssur f w) (mapAssur f u) π
  | .undermine w u π => .undermine (mapAssur f w) (mapAssur f u) π

section Lemmas
variable {f : Assurance → Assurance}

/-- The list helper is `List.map (mapAssur f)`. -/
theorem mapAssurList_eq (ws : List SupportTerm) :
    mapAssurList f ws = ws.map (mapAssur f) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [mapAssurList, List.map_cons, ih]

theorem mapAssurAtt_source (k : Attack) :
    (mapAssurAtt f k).source = mapAssur f k.source := by
  cases k <;> rfl

/-! ### Injectivity of a uniform relabel -/

mutual
  theorem mapAssur_inj (hf : Function.Injective f) :
      ∀ {a b : SupportTerm}, mapAssur f a = mapAssur f b → a = b
    | .leaf _, .leaf _, h => by simpa only [mapAssur, SupportTerm.leaf.injEq] using h
    | .leaf _, .inst _ _ _ _ _ _, h => by simp only [mapAssur, reduceCtorEq] at h
    | .inst _ _ _ _ _ _, .leaf _, h => by simp only [mapAssur, reduceCtorEq] at h
    | .inst _ _ _ _ _ _, .inst _ _ _ _ _ _, h => by
        simp only [mapAssur, SupportTerm.inst.injEq] at h
        obtain ⟨hrn, hθ, hws, hD, hH, hα⟩ := h
        subst hrn; subst hθ; subst hH
        rw [mapAssurList_inj hf hws, mapAssurDis_inj hf hD, hf hα]
  theorem mapAssurList_inj (hf : Function.Injective f) :
      ∀ {xs ys : List SupportTerm}, mapAssurList f xs = mapAssurList f ys → xs = ys
    | [], [], _ => rfl
    | [], _ :: _, h => by simp only [mapAssurList, reduceCtorEq] at h
    | _ :: _, [], h => by simp only [mapAssurList, reduceCtorEq] at h
    | _ :: _, _ :: _, h => by
        simp only [mapAssurList, List.cons.injEq] at h
        rw [mapAssur_inj hf h.1, mapAssurList_inj hf h.2]
  theorem mapAssurDis_inj (hf : Function.Injective f) :
      ∀ {xs ys : List (QuestionId × SupportTerm)},
        mapAssurDis f xs = mapAssurDis f ys → xs = ys
    | [], [], _ => rfl
    | [], _ :: _, h => by simp only [mapAssurDis, reduceCtorEq] at h
    | _ :: _, [], h => by simp only [mapAssurDis, reduceCtorEq] at h
    | (_, _) :: _, (_, _) :: _, h => by
        simp only [mapAssurDis, List.cons.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨hq, hx⟩, htl⟩ := h
        subst hq
        rw [mapAssur_inj hf hx, mapAssurDis_inj hf htl]
end

theorem mapAssur_injective (hf : Function.Injective f) :
    Function.Injective (mapAssur f) := fun _ _ h => mapAssur_inj hf h

theorem mapAssur_eq_iff (hf : Function.Injective f) (a b : SupportTerm) :
    mapAssur f a = mapAssur f b ↔ a = b :=
  ⟨fun h => mapAssur_injective hf h, fun h => h ▸ rfl⟩

/-! ### Relabel commutes with positional navigation -/

theorem lookupDis_mapAssurDis (D : List (QuestionId × SupportTerm)) (q : QuestionId) :
    lookupDis (mapAssurDis f D) q = (lookupDis D q).map (mapAssur f) := by
  induction D with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨q', w⟩ := p
    simp only [mapAssurDis, lookupDis, ih]
    split <;> rfl

theorem mapAssur_subterm :
    ∀ (v : SupportTerm) (π : Pos),
      subterm (mapAssur f v) π = (subterm v π).map (mapAssur f) := by
  intro v π
  induction π generalizing v with
  | nil => rfl
  | cons pe π ih =>
    cases v with
    | leaf l => rfl
    | inst rn θ ws D H α =>
      cases pe with
      | prem i =>
        simp only [mapAssur, subterm, mapAssurList_eq, List.getElem?_map]
        cases ws[i]? with
        | none => rfl
        | some w => exact ih w
      | ques q =>
        simp only [mapAssur, subterm, lookupDis_mapAssurDis]
        cases lookupDis D q with
        | none => rfl
        | some w => exact ih w

/-! ### Relabel preserves structural containment (via injectivity) -/

mutual
  theorem containsB_mapAssur (hf : Function.Injective f) :
      ∀ (v t : SupportTerm),
        containsB (mapAssur f v) (mapAssur f t) = containsB v t
    | .leaf l, t =>
        decide_eq_decide.mpr (mapAssur_eq_iff hf (.leaf l) t)
    | .inst rn θ ws D H α, t => by
        show (decide (mapAssur f (.inst rn θ ws D H α) = mapAssur f t)
              || containsBList (mapAssurList f ws) (mapAssur f t)
              || containsBDis (mapAssurDis f D) (mapAssur f t))
            = (decide (SupportTerm.inst rn θ ws D H α = t)
              || containsBList ws t || containsBDis D t)
        rw [decide_eq_decide.mpr (mapAssur_eq_iff hf (.inst rn θ ws D H α) t),
          containsBList_mapAssur hf ws t, containsBDis_mapAssur hf D t]
  theorem containsBList_mapAssur (hf : Function.Injective f) :
      ∀ (ws : List SupportTerm) (t : SupportTerm),
        containsBList (mapAssurList f ws) (mapAssur f t) = containsBList ws t
    | [], _ => rfl
    | w :: ws, t => by
        simp only [mapAssurList, containsBList]
        rw [containsB_mapAssur hf w t, containsBList_mapAssur hf ws t]
  theorem containsBDis_mapAssur (hf : Function.Injective f) :
      ∀ (D : List (QuestionId × SupportTerm)) (t : SupportTerm),
        containsBDis (mapAssurDis f D) (mapAssur f t) = containsBDis D t
    | [], _ => rfl
    | (q, w) :: rest, t => by
        simp only [mapAssurDis, containsBDis]
        rw [containsB_mapAssur hf w t, containsBDis_mapAssur hf rest t]
end

theorem attackClosureB_mapAssur (hf : Function.Injective f)
    (k : Attack) (target : SupportTerm) :
    attackClosureB (mapAssurAtt f k) (mapAssur f target)
      = attackClosureB k target := by
  cases k with
  | rebut w u =>
    simp only [mapAssurAtt, attackClosureB]
    exact containsB_mapAssur hf target u
  | undercut w u π =>
    simp only [mapAssurAtt, attackClosureB, mapAssur_subterm]
    cases subterm u π with
    | none => rfl
    | some t => exact containsB_mapAssur hf target t
  | undermine w u π =>
    simp only [mapAssurAtt, attackClosureB, mapAssur_subterm]
    cases subterm u π with
    | none => rfl
    | some t => exact containsB_mapAssur hf target t

theorem coveredB_relabel (hf : Function.Injective f)
    (atts : List Attack) (s t : SupportTerm) :
    coveredB (atts.map (mapAssurAtt f)) (mapAssur f s) (mapAssur f t)
      = coveredB atts s t := by
  simp only [coveredB]
  induction atts with
  | nil => rfl
  | cons k rest ih =>
    simp only [List.map_cons, List.any_cons, ih]
    rw [mapAssurAtt_source, attackClosureB_mapAssur hf,
      decide_eq_decide.mpr (mapAssur_eq_iff hf k.source s)]

end Lemmas

/-! ### The AF is invariant under a uniform injective relabel -/

section Replacement
variable {canon : String → String} {Pi : RuleId → Option Rule}
  {Gamma : LeafId → Option Atom}
  {CertOk₁ CertOk₂ : BackendId → Digest → CertRef → List Atom → Atom → Prop}
  {dp : DefeatPolicy} {f : Assurance → Assurance}

/-- **The compiled edge decider is relabel-invariant.** With arguments and
attacks relabeled uniformly by an injective `f`, `edgeB` agrees at every index
pair (nodes are list positions, so the bijection is the identity). -/
theorem edgeB_relabel
    {P₁ : CheckedProgram canon Pi Gamma CertOk₁ dp}
    {P₂ : CheckedProgram canon Pi Gamma CertOk₂ dp}
    (hf : Function.Injective f)
    (hargs : P₂.args = P₁.args.map (mapAssur f))
    (hatts : P₂.atts = P₁.atts.map (mapAssurAtt f)) :
    ∀ i j, edgeB P₁ i j = edgeB P₂ i j := by
  intro i j
  simp only [edgeB, hargs, hatts, List.getElem?_map]
  cases P₁.args[i]? with
  | none => rfl
  | some source =>
    cases P₁.args[j]? with
    | none => rfl
    | some target =>
      exact (coveredB_relabel hf P₁.atts source target).symm

/-- **The compiled AF is relabel-invariant.** Equal argument count (a `map`) and
`edgeB_relabel` give a definitionally equal `Grounded.AF` — the identity node
bijection realizing Theorem 2's graph isomorphism. -/
theorem checkedAF_relabel
    {P₁ : CheckedProgram canon Pi Gamma CertOk₁ dp}
    {P₂ : CheckedProgram canon Pi Gamma CertOk₂ dp}
    (hf : Function.Injective f)
    (hargs : P₂.args = P₁.args.map (mapAssur f))
    (hatts : P₂.atts = P₁.atts.map (mapAssurAtt f)) :
    checkedAF P₁ = checkedAF P₂ := by
  have hlen : P₁.args.length = P₂.args.length := by
    rw [hargs, List.length_map]
  simp only [checkedAF, toAF]
  congr 1
  · rw [hlen]
  · funext i j; exact edgeB_relabel hf hargs hatts i j

/-- **Backend replacement preserves claim status (Theorem 2 conclusion).** Every
claim gets the same four-state status under either program. -/
theorem backend_replacement
    {P₁ : CheckedProgram canon Pi Gamma CertOk₁ dp}
    {P₂ : CheckedProgram canon Pi Gamma CertOk₂ dp}
    (hf : Function.Injective f)
    (hargs : P₂.args = P₁.args.map (mapAssur f))
    (hatts : P₂.atts = P₁.atts.map (mapAssurAtt f))
    (c : Claim) :
    statusC (checkedAF P₁) c = statusC (checkedAF P₂) c := by
  rw [checkedAF_relabel hf hargs hatts]

/-- The grounded labelling agrees node-for-node (the identity bijection). -/
theorem labelC_relabel
    {P₁ : CheckedProgram canon Pi Gamma CertOk₁ dp}
    {P₂ : CheckedProgram canon Pi Gamma CertOk₂ dp}
    (hf : Function.Injective f)
    (hargs : P₂.args = P₁.args.map (mapAssur f))
    (hatts : P₂.atts = P₁.atts.map (mapAssurAtt f))
    (a : Arg) :
    labelC (checkedAF P₁) a = labelC (checkedAF P₂) a := by
  rw [checkedAF_relabel hf hargs hatts]

end Replacement

end Lara.Erase
