/-
# PW-T9 — exact structural-path composition (issue #190, tracker #189)

Composition of the T6 layer, three levels deep:

* **Translations compose Kleisli-style** (`SymMap.comp` and the `_comp`
  lemma family): every structural lift satisfies
  `trX (m₂.comp m₁) x = (trX m₁ x).bind (trX m₂)`, which *is* the design's
  composed-domain law `dom(τ_d∘τ_b) = {c ∈ dom τ_b | τ_b c ∈ dom τ_d}` —
  the composite is defined exactly when the first leg is defined and its
  image is in the second leg's vocabulary. A mid-path vocabulary gap
  surfaces as `none`, i.e. as incomparability at the comparison layer,
  never as a local status (`trAtom_comp_none_mid`,
  `Examples.PW.Compose.mid_path_translationUndefined`).
* **Bridges compose** (`StructuralBridge.comp`): each contract clause of
  the composite is discharged by chaining the two legs' clauses through
  the intermediate environment.
* **Transport composes coherently** (`support_transport_comp`,
  `BridgePath.trans_eq_compose`, `path_support_transport`): stepwise
  transport along a chosen typed path equals transport along the path's
  folded composite, so T6's `support_transport` at the composite *is* the
  path theorem. The path is data — theorems are stated per chosen path,
  which is how intermediate-environment dependence stays explicit.
* **Named direct bridges must agree with a chosen path** (`Commutes`,
  `direct_transport_agrees`): the path-level commuting triangle compares one
  direct bridge with an arbitrary `BridgePath` sharing its endpoints.
  Because support terms expose constructor translation through substitutions,
  the induced equalities are equivalent to full symbol-map and leaf-map
  equality (`Commutes.of_maps_eq`). Target policy and evidence typing then pin
  rule and admitted-leaf atom translations (`commutes_on_rules`,
  `commutes_on_leaves`) as consequences, not as extra commuting fields or
  "free corners".

Nothing here concerns approximation bridges: composition for those needs
separate domains, observables, comparison spaces, and error/convergence
laws, and remains deferred (issue #190's boundary).

This new module imports T6 without modifying its modules or definitions; the
composition definitions and theorems below are local to this module.
-/

import Lara.PW.Structural

namespace Lara.PW

open Lara.Support

/-- Kleisli composition of partial symbol translations: `m₂.comp m₁`
applies `m₁` first — the design's `τ_d ∘ τ_b`. A symbol is in the composed
vocabulary exactly when it is in `m₁`'s vocabulary and its image is in
`m₂`'s. -/
def SymMap.comp (m₂ m₁ : SymMap) : SymMap where
  predMap := fun s => (m₁.predMap s).bind m₂.predMap
  conMap  := fun s => (m₁.conMap s).bind m₂.conMap

/-- Left identity for Kleisli composition of partial symbol translations. -/
theorem SymMap.id_comp (m : SymMap) : SymMap.id.comp m = m := by
  cases m with
  | mk predMap conMap =>
    change SymMap.mk (fun s => (predMap s).bind some)
        (fun s => (conMap s).bind some) = SymMap.mk predMap conMap
    have hp : (fun s => (predMap s).bind some) = predMap := by
      funext s
      cases predMap s <;> rfl
    have hc : (fun s => (conMap s).bind some) = conMap := by
      funext s
      cases conMap s <;> rfl
    rw [hp, hc]

/-- Right identity for Kleisli composition of partial symbol translations. -/
theorem SymMap.comp_id (m : SymMap) : m.comp SymMap.id = m := by
  cases m
  rfl

mutual
  /-- `trTerm` along the composite is the Kleisli composition of the legs. -/
  theorem trTerm_comp (m₂ m₁ : SymMap) : ∀ t : Term,
      trTerm (m₂.comp m₁) t = (trTerm m₁ t).bind (trTerm m₂)
    | .num _ => rfl
    | .str _ => rfl
    | .con k ts => by
        unfold trTerm
        rw [trTerms_comp]
        simp only [SymMap.comp]
        cases hk : m₁.conMap k with
        | none => simp
        | some k' =>
          cases hts : trTerms m₁ ts with
          | none => simp
          | some ts' => simp [trTerm]
  /-- `trTerms` along the composite is the Kleisli composition of the legs. -/
  theorem trTerms_comp (m₂ m₁ : SymMap) : ∀ ts : Terms,
      trTerms (m₂.comp m₁) ts = (trTerms m₁ ts).bind (trTerms m₂)
    | .nil => rfl
    | .cons t ts => by
        unfold trTerms
        rw [trTerm_comp, trTerms_comp]
        cases ht : trTerm m₁ t with
        | none => simp
        | some t' =>
          cases hts : trTerms m₁ ts with
          | none => simp
          | some ts' => simp [trTerms]
end

/-- `trAtom` along the composite is the Kleisli composition of the legs —
the composed-domain law at claim level. -/
theorem trAtom_comp (m₂ m₁ : SymMap) (a : Atom) :
    trAtom (m₂.comp m₁) a = (trAtom m₁ a).bind (trAtom m₂) := by
  obtain ⟨p, ts⟩ := a
  simp only [trAtom]
  rw [trTerms_comp]
  simp only [SymMap.comp]
  cases hp : m₁.predMap p with
  | none => simp
  | some p' =>
    cases hts : trTerms m₁ ts with
    | none => simp
    | some ts' => simp [trAtom]

/-- `trAtoms` along the composite is the Kleisli composition of the legs. -/
theorem trAtoms_comp (m₂ m₁ : SymMap) : ∀ as : List Atom,
    trAtoms (m₂.comp m₁) as = (trAtoms m₁ as).bind (trAtoms m₂)
  | [] => rfl
  | a :: as => by
      unfold trAtoms
      rw [trAtom_comp, trAtoms_comp]
      cases ha : trAtom m₁ a with
      | none => simp
      | some a' =>
        cases has : trAtoms m₁ as with
        | none => simp
        | some as' => simp [trAtoms]

/-- A first-leg gap is a composite gap. -/
theorem trAtom_comp_none_left {m₂ m₁ : SymMap} {a : Atom}
    (h : trAtom m₁ a = none) : trAtom (m₂.comp m₁) a = none := by
  rw [trAtom_comp, h]
  rfl

/-- **Missing intermediate translation**: the first leg succeeds but its
image is out of the second leg's vocabulary, so the composite is undefined —
the failure mode that must surface as incomparability, not as a status. -/
theorem trAtom_comp_none_mid {m₂ m₁ : SymMap} {a a' : Atom}
    (h₁ : trAtom m₁ a = some a') (h₂ : trAtom m₂ a' = none) :
    trAtom (m₂.comp m₁) a = none := by
  rw [trAtom_comp, h₁, Option.bind_some]
  exact h₂

mutual
  /-- `trPat` along the composite is the Kleisli composition of the legs. -/
  theorem trPat_comp (m₂ m₁ : SymMap) : ∀ p : Pat,
      trPat (m₂.comp m₁) p = (trPat m₁ p).bind (trPat m₂)
    | .var _ => rfl
    | .num _ => rfl
    | .str _ => rfl
    | .con k ps => by
        unfold trPat
        rw [trPats_comp]
        simp only [SymMap.comp]
        cases hk : m₁.conMap k.name with
        | none => simp
        | some k' =>
          cases hps : trPats m₁ ps with
          | none => simp
          | some ps' => simp [trPat]
  /-- `trPats` along the composite is the Kleisli composition of the legs. -/
  theorem trPats_comp (m₂ m₁ : SymMap) : ∀ ps : Pats,
      trPats (m₂.comp m₁) ps = (trPats m₁ ps).bind (trPats m₂)
    | .nil => rfl
    | .cons p ps => by
        unfold trPats
        rw [trPat_comp, trPats_comp]
        cases hp : trPat m₁ p with
        | none => simp
        | some p' =>
          cases hps : trPats m₁ ps with
          | none => simp
          | some ps' => simp [trPats]
end

/-- `trAPat` along the composite is the Kleisli composition of the legs. -/
theorem trAPat_comp (m₂ m₁ : SymMap) (ap : APat) :
    trAPat (m₂.comp m₁) ap = (trAPat m₁ ap).bind (trAPat m₂) := by
  unfold trAPat
  rw [trPats_comp]
  simp only [SymMap.comp]
  cases hp : m₁.predMap ap.pred.name with
  | none => simp
  | some p' =>
    cases hps : trPats m₁ ap.args with
    | none => simp
    | some ps' => simp

/-- `trAPats` along the composite is the Kleisli composition of the legs. -/
theorem trAPats_comp (m₂ m₁ : SymMap) : ∀ aps : List APat,
    trAPats (m₂.comp m₁) aps = (trAPats m₁ aps).bind (trAPats m₂)
  | [] => rfl
  | ap :: aps => by
      unfold trAPats
      rw [trAPat_comp, trAPats_comp]
      cases hap : trAPat m₁ ap with
      | none => simp
      | some ap' =>
        cases haps : trAPats m₁ aps with
        | none => simp
        | some aps' => simp [trAPats]

/-- `trSubst` along the composite is the Kleisli composition of the legs. -/
theorem trSubst_comp (m₂ m₁ : SymMap) : ∀ θ : Subst,
    trSubst (m₂.comp m₁) θ = (trSubst m₁ θ).bind (trSubst m₂)
  | [] => rfl
  | (x, t) :: θ => by
      unfold trSubst
      rw [trTerm_comp, trSubst_comp]
      cases ht : trTerm m₁ t with
      | none => simp
      | some t' =>
        cases hθ : trSubst m₁ θ with
        | none => simp
        | some θ' => simp [trSubst]

mutual
  /-- **The composed dependent partial support map is the Kleisli
  composition of the legs** — T9's "coherence of support transport" at the
  level of the map itself. Defined exactly when the first leg is defined
  and its image is in the second leg's domain. -/
  theorem trSupport_comp (m₂ m₁ : SymMap) (lm₂ lm₁ : LeafId → LeafId) :
      ∀ w : SupportTerm,
        trSupport (m₂.comp m₁) (lm₂ ∘ lm₁) w =
          (trSupport m₁ lm₁ w).bind (trSupport m₂ lm₂)
    | .leaf _ => rfl
    | .inst rn θ ws D H α => by
        simp only [trSupport, trSubst_comp m₂ m₁ θ,
          trSupportList_comp m₂ m₁ lm₂ lm₁ ws,
          trSupportDis_comp m₂ m₁ lm₂ lm₁ D]
        cases hθ₁ : trSubst m₁ θ with
        | none =>
          simp only [Option.bind_none]
        | some θ₁ =>
          simp only [Option.bind_some]
          cases hws₁ : trSupportList m₁ lm₁ ws with
          | none =>
            simp only [Option.bind_none]
            cases hθ₂ : trSubst m₂ θ₁ with
            | none => rfl
            | some θ₂ => rfl
          | some ws₁ =>
            simp only [Option.bind_some]
            cases hD₁ : trSupportDis m₁ lm₁ D with
            | none =>
              simp only [Option.bind_none]
              cases hθ₂ : trSubst m₂ θ₁ with
              | none => rfl
              | some θ₂ =>
                cases hws₂ : trSupportList m₂ lm₂ ws₁ with
                | none => rfl
                | some ws₂ => rfl
            | some D₁ =>
              simp only [Option.bind_some]
              unfold trSupport
              cases hθ₂ : trSubst m₂ θ₁ with
              | none => rfl
              | some θ₂ =>
                cases hws₂ : trSupportList m₂ lm₂ ws₁ with
                | none => rfl
                | some ws₂ =>
                  cases hD₂ : trSupportDis m₂ lm₂ D₁ with
                  | none => rfl
                  | some D₂ => rfl
  /-- `trSupportList` along the composite is the Kleisli composition. -/
  theorem trSupportList_comp (m₂ m₁ : SymMap) (lm₂ lm₁ : LeafId → LeafId) :
      ∀ ws : List SupportTerm,
        trSupportList (m₂.comp m₁) (lm₂ ∘ lm₁) ws =
          (trSupportList m₁ lm₁ ws).bind (trSupportList m₂ lm₂)
    | [] => rfl
    | w :: ws => by
        unfold trSupportList
        rw [trSupport_comp, trSupportList_comp]
        cases hw₁ : trSupport m₁ lm₁ w with
        | none =>
          simp only [Option.bind_none]
        | some w₁ =>
          simp only [Option.bind_some]
          cases hws₁ : trSupportList m₁ lm₁ ws with
          | none =>
            simp only [Option.bind_none]
            cases hw₂ : trSupport m₂ lm₂ w₁ with
            | none => rfl
            | some w₂ => rfl
          | some ws₁ =>
            simp only [Option.bind_some, trSupportList]
  /-- `trSupportDis` along the composite is the Kleisli composition. -/
  theorem trSupportDis_comp (m₂ m₁ : SymMap) (lm₂ lm₁ : LeafId → LeafId) :
      ∀ D : List (QuestionId × SupportTerm),
        trSupportDis (m₂.comp m₁) (lm₂ ∘ lm₁) D =
          (trSupportDis m₁ lm₁ D).bind (trSupportDis m₂ lm₂)
    | [] => rfl
    | (q, w) :: D => by
        unfold trSupportDis
        rw [trSupport_comp, trSupportDis_comp]
        cases hw₁ : trSupport m₁ lm₁ w with
        | none =>
          simp only [Option.bind_none]
        | some w₁ =>
          simp only [Option.bind_some]
          cases hD₁ : trSupportDis m₁ lm₁ D with
          | none =>
            simp only [Option.bind_none]
            cases hw₂ : trSupport m₂ lm₂ w₁ with
            | none => rfl
            | some w₂ => rfl
          | some D₁ =>
            simp only [Option.bind_some, trSupportDis]
end

/-- `trQuestion` along the composite is the Kleisli composition of the legs. -/
theorem trQuestion_comp (m₂ m₁ : SymMap) (q : Question) :
    trQuestion (m₂.comp m₁) q = (trQuestion m₁ q).bind (trQuestion m₂) := by
  unfold trQuestion
  rw [trAPat_comp]
  cases ha : trAPat m₁ q.answer with
  | none => simp
  | some a' =>
    simp only [Option.bind_some]

/-- `trQuestions` along the composite is the Kleisli composition of the legs. -/
theorem trQuestions_comp (m₂ m₁ : SymMap) : ∀ qs : List Question,
    trQuestions (m₂.comp m₁) qs = (trQuestions m₁ qs).bind (trQuestions m₂)
  | [] => rfl
  | q :: qs => by
      unfold trQuestions
      rw [trQuestion_comp, trQuestions_comp]
      cases hq : trQuestion m₁ q with
      | none => simp
      | some q' =>
        cases hqs : trQuestions m₁ qs with
        | none => simp
        | some qs' => simp [trQuestions]

/-- `trRule` along the composite is the Kleisli composition of the legs:
premises, conclusion, and answers compose; mode, parameters, the trusted
flag, and the certifier allowlist are untouched by both legs. -/
theorem trRule_comp (m₂ m₁ : SymMap) (r : Rule) :
    trRule (m₂.comp m₁) r = (trRule m₁ r).bind (trRule m₂) := by
  unfold trRule
  rw [trAPats_comp, trAPat_comp, trQuestions_comp]
  cases hps : trAPats m₁ r.premises with
  | none => simp
  | some ps' =>
    cases hc : trAPat m₁ r.concl with
    | none => simp
    | some c' =>
      cases hqs : trQuestions m₁ r.questions with
      | none => simp
      | some qs' =>
        simp only [Option.bind_some]

/-- **Composition of structural bridges** through a shared intermediate
checking environment. The symbol translation composes Kleisli-style, the
leaf renaming composes as functions, and each contract clause is the two
legs' clauses chained through the middle. The intermediate environment
(`Pi'`, `Gamma'`, `CertOk'`) is existential history here — but transport
along the composite still factors through it, which is what
`support_transport_comp` keeps explicit. -/
def StructuralBridge.comp
    {canon : String → String} {Pi Pi' Pi'' : RuleId → Option Rule}
    {Gamma Gamma' Gamma'' : LeafId → Option Atom}
    {CertOk CertOk' CertOk'' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (B₂ : StructuralBridge canon Pi' Pi'' Gamma' Gamma'' CertOk' CertOk'')
    (B₁ : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk') :
    StructuralBridge canon Pi Pi'' Gamma Gamma'' CertOk CertOk'' where
  sym := B₂.sym.comp B₁.sym
  leafMap := B₂.leafMap ∘ B₁.leafMap
  leaf_ok := fun l p h => by
    obtain ⟨p', hp', h'⟩ := B₁.leaf_ok l p h
    obtain ⟨p'', hp'', h''⟩ := B₂.leaf_ok (B₁.leafMap l) p' h'
    exact ⟨p'', by rw [trAtom_comp, hp', Option.bind_some]; exact hp'', h''⟩
  rule_ok := fun rn r h => by
    obtain ⟨r', hr', h'⟩ := B₁.rule_ok rn r h
    obtain ⟨r'', hr'', h''⟩ := B₂.rule_ok rn r' h'
    exact ⟨r'', by rw [trRule_comp, hr', Option.bind_some]; exact hr'', h''⟩
  cert_ok := fun β hd κ As C As'' C'' hAs hC hacc => by
    rw [trAtoms_comp] at hAs
    rw [trAtom_comp] at hC
    obtain ⟨As', hAs₁, hAs₂⟩ := Option.bind_eq_some_iff.mp hAs
    obtain ⟨C', hC₁, hC₂⟩ := Option.bind_eq_some_iff.mp hC
    exact B₂.cert_ok β hd κ As' C' As'' C'' hAs₂ hC₂
      (B₁.cert_ok β hd κ As C As' C' hAs₁ hC₁ hacc)

/-! ### Exact applicability factorization -/

/-- The explicit two-step form of checker-tied applicability for a binary
composite. Every source program term has a chosen intermediate translation,
whose second translation belongs to the target program. -/
def AdmitsSteps
    {canon : String → String} {Pi Pi' Pi'' : RuleId → Option Rule}
    {Gamma Gamma' Gamma'' : LeafId → Option Atom}
    {CertOk CertOk' CertOk'' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (B₂ : StructuralBridge canon Pi' Pi'' Gamma' Gamma'' CertOk' CertOk'')
    (B₁ : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk')
    {κ μ : Instance.Context}
    (w : Instance.World κ) (u : Instance.World μ) : Prop :=
  ∀ t, t ∈ w.unit.program.args →
    ∃ t' t'', trSupport B₁.sym B₁.leafMap t = some t' ∧
      trSupport B₂.sym B₂.leafMap t' = some t'' ∧
      t'' ∈ u.unit.program.args

/-- Applicability of a binary composite is exactly its two-step Kleisli
factorization. This is an equality of the checker-tied `accept` conjunct, not
of PW0's full accepted-edge relation. -/
theorem admits_comp
    {canon : String → String} {Pi Pi' Pi'' : RuleId → Option Rule}
    {Gamma Gamma' Gamma'' : LeafId → Option Atom}
    {CertOk CertOk' CertOk'' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (B₂ : StructuralBridge canon Pi' Pi'' Gamma' Gamma'' CertOk' CertOk'')
    (B₁ : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk')
    {κ μ : Instance.Context}
    (w : Instance.World κ) (u : Instance.World μ) :
    Admits (B₂.comp B₁).sym (B₂.comp B₁).leafMap w u ↔
      AdmitsSteps B₂ B₁ w u := by
  constructor
  · intro hadm t ht
    obtain ⟨t'', htr, hmem⟩ := hadm t ht
    change trSupport (B₂.sym.comp B₁.sym) (B₂.leafMap ∘ B₁.leafMap) t =
      some t'' at htr
    rw [trSupport_comp] at htr
    obtain ⟨t', ht₁, ht₂⟩ := Option.bind_eq_some_iff.mp htr
    exact ⟨t', t'', ht₁, ht₂, hmem⟩
  · intro hsteps t ht
    obtain ⟨t', t'', ht₁, ht₂, hmem⟩ := hsteps t ht
    refine ⟨t'', ?_, hmem⟩
    change trSupport (B₂.sym.comp B₁.sym) (B₂.leafMap ∘ B₁.leafMap) t =
      some t''
    rw [trSupport_comp, ht₁, Option.bind_some]
    exact ht₂

/-- Two admitted legs through an explicitly chosen intermediate world give
the binary step predicate. The arbitrary intermediate world is input data;
the converse `admits_comp` does not attempt to reconstruct one. -/
theorem admits_steps_of_intermediate
    {canon : String → String} {Pi Pi' Pi'' : RuleId → Option Rule}
    {Gamma Gamma' Gamma'' : LeafId → Option Atom}
    {CertOk CertOk' CertOk'' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (B₂ : StructuralBridge canon Pi' Pi'' Gamma' Gamma'' CertOk' CertOk'')
    (B₁ : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk')
    {κ lam μ : Instance.Context}
    {w : Instance.World κ} (v : Instance.World lam) {u : Instance.World μ}
    (h₁ : Admits B₁.sym B₁.leafMap w v)
    (h₂ : Admits B₂.sym B₂.leafMap v u) :
    AdmitsSteps B₂ B₁ w u := by
  intro t ht
  obtain ⟨t', ht₁, hmem'⟩ := h₁ t ht
  obtain ⟨t'', ht₂, hmem''⟩ := h₂ t' hmem'
  exact ⟨t', t'', ht₁, ht₂, hmem''⟩

/-- **T9, two-step form.** Stepwise transport along `B₁` then `B₂` is
transport along the composed bridge: the composite's partial support map
sends `w` to the same `w''`, the composed translated conclusion is the
translation of the translated conclusion, and both the intermediate and the
final checked judgments hold — the intermediate environment's role is in
evidence, not erased. -/
theorem support_transport_comp
    {canon : String → String} {Pi Pi' Pi'' : RuleId → Option Rule}
    {Gamma Gamma' Gamma'' : LeafId → Option Atom}
    {CertOk CertOk' CertOk'' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (B₂ : StructuralBridge canon Pi' Pi'' Gamma' Gamma'' CertOk' CertOk'')
    (B₁ : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk')
    {w w' w'' : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk w C O)
    (hw₁ : trSupport B₁.sym B₁.leafMap w = some w')
    (hw₂ : trSupport B₂.sym B₂.leafMap w' = some w'') :
    trSupport (B₂.comp B₁).sym (B₂.comp B₁).leafMap w = some w'' ∧
      ∃ C' C'', trAtom B₁.sym C = some C' ∧ trAtom B₂.sym C' = some C'' ∧
        trAtom (B₂.comp B₁).sym C = some C'' ∧
        HasSupport canon Pi' Gamma' CertOk' w' C' O ∧
        HasSupport canon Pi'' Gamma'' CertOk'' w'' C'' O := by
  obtain ⟨C', hC₁, h₁⟩ := support_transport B₁ h hw₁
  obtain ⟨C'', hC₂, h₂⟩ := support_transport B₂ h₁ hw₂
  refine ⟨?_, C', C'', hC₁, hC₂, ?_, h₁, h₂⟩
  · show trSupport (B₂.sym.comp B₁.sym) (B₂.leafMap ∘ B₁.leafMap) w = some w''
    rw [trSupport_comp, hw₁, Option.bind_some]
    exact hw₂
  · show trAtom (B₂.sym.comp B₁.sym) C = some C''
    rw [trAtom_comp, hC₁, Option.bind_some]
    exact hC₂


/-- **A chosen typed path of structural bridges** between checking
environments over one shared canonicalizer. The intermediate environments
are constructor data: two paths with the same endpoints need not agree, and
every theorem below is stated per chosen path — this is how the design's
"independence from intermediate-world choices, or an explicit path in the
result" resolves here: the path is explicit in the result. (The constructor
quantifies over intermediate environments, hence `Type 1`.) -/
inductive BridgePath (canon : String → String) :
    (RuleId → Option Rule) → (RuleId → Option Rule) →
    (LeafId → Option Atom) → (LeafId → Option Atom) →
    (BackendId → Digest → CertRef → List Atom → Atom → Prop) →
    (BackendId → Digest → CertRef → List Atom → Atom → Prop) → Type 1 where
  | nil : BridgePath canon Pi Pi Gamma Gamma CertOk CertOk
  | cons :
      StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk' →
      BridgePath canon Pi' Pi'' Gamma' Gamma'' CertOk' CertOk'' →
      BridgePath canon Pi Pi'' Gamma Gamma'' CertOk CertOk''

/-- The path's named composite: fold of binary composition, the identity
endobridge at the empty path. -/
def BridgePath.compose {canon Pi Pi' Gamma Gamma' CertOk CertOk'} :
    BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk' →
      StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk'
  | .nil => .refl canon Pi Gamma CertOk
  | .cons B P => P.compose.comp B

/-- Stepwise transport along the path: the Kleisli chain of the per-edge
partial support maps, in path order. `none` as soon as any edge's
translation is undefined on the running image — a mid-path vocabulary gap
is a gap of the whole path. -/
def BridgePath.trans {canon Pi Pi' Gamma Gamma' CertOk CertOk'} :
    BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk' →
      SupportTerm → Option SupportTerm
  | .nil => fun w => some w
  | .cons B P => fun w => (trSupport B.sym B.leafMap w).bind P.trans

/-- **Path coherence**: stepwise transport along a chosen path equals the
partial support map of the path's named composite. The transported result
depends on the chosen path only through its composite. -/
theorem BridgePath.trans_eq_compose
    {canon Pi Pi' Gamma Gamma' CertOk CertOk'}
    (P : BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk') :
    ∀ w : SupportTerm,
      P.trans w = trSupport P.compose.sym P.compose.leafMap w := by
  induction P with
  | nil => intro w; exact (trSupport_id w).symm
  | cons B P ih =>
    intro w
    show (trSupport B.sym B.leafMap w).bind P.trans =
      trSupport (P.compose.comp B).sym (P.compose.comp B).leafMap w
    rw [show (P.compose.comp B).sym = P.compose.sym.comp B.sym from rfl,
        show (P.compose.comp B).leafMap = P.compose.leafMap ∘ B.leafMap
          from rfl,
        trSupport_comp]
    cases trSupport B.sym B.leafMap w with
    | none => rfl
    | some w' => simp only [Option.bind_some]; exact ih w'

/-- A named direct structural bridge commutes with a chosen path sharing its
endpoints when they induce the same atom translation and support transport.
The support equation names the path's stepwise transport explicitly, so
agreement is with the chosen path rather than merely with an unnamed
composite. -/
structure Commutes
    {canon : String → String} {Pi Pi' : RuleId → Option Rule}
    {Gamma Gamma' : LeafId → Option Atom}
    {CertOk CertOk' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (B : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk')
    (P : BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk') : Prop where
  atom_eq : ∀ a, trAtom B.sym a = trAtom P.compose.sym a
  support_eq : ∀ w, trSupport B.sym B.leafMap w = P.trans w

/-- Support-map agreement exposes equality of the direct and composite leaf
maps pointwise. This is a consequence of `Commutes`, not an additional field:
on a leaf support, path coherence leaves only constructor injectivity. -/
theorem Commutes.leafMap_eq
    {canon : String → String} {Pi Pi' : RuleId → Option Rule}
    {Gamma Gamma' : LeafId → Option Atom}
    {CertOk CertOk' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {B : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk'}
    {P : BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk'}
    (hc : Commutes B P) (l : LeafId) :
    B.leafMap l = P.compose.leafMap l := by
  have h := hc.support_eq (.leaf l)
  rw [P.trans_eq_compose] at h
  simpa only [trSupport, Option.some.injEq, SupportTerm.leaf.injEq] using h

/-- Atom-map agreement exposes equality of the direct and composite predicate
maps pointwise. A nullary atom observes its predicate map without involving
the constructor map. -/
theorem Commutes.predMap_eq
    {canon : String → String} {Pi Pi' : RuleId → Option Rule}
    {Gamma Gamma' : LeafId → Option Atom}
    {CertOk CertOk' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {B : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk'}
    {P : BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk'}
    (hc : Commutes B P) (p : String) :
    B.sym.predMap p = P.compose.sym.predMap p := by
  have h := hc.atom_eq (.atom p .nil)
  cases hB : B.sym.predMap p <;>
    cases hP : P.compose.sym.predMap p <;>
    simp [hB, hP, trAtom, trTerms] at h ⊢
  exact h

/-- Support-map agreement also exposes equality of the direct and composite
constructor maps pointwise: substitutions inside `.inst` support terms
translate constructors without consulting a predicate map. -/
theorem Commutes.conMap_eq
    {canon : String → String} {Pi Pi' : RuleId → Option Rule}
    {Gamma Gamma' : LeafId → Option Atom}
    {CertOk CertOk' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {B : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk'}
    {P : BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk'}
    (hc : Commutes B P) (k : String) :
    B.sym.conMap k = P.compose.sym.conMap k := by
  have h := hc.support_eq
    (.inst ⟨"r"⟩ [(⟨"X"⟩, .con k .nil)] [] [] [] .none)
  rw [P.trans_eq_compose] at h
  cases hB : B.sym.conMap k <;>
    cases hP : P.compose.sym.conMap k <;>
    simp [hB, hP, trSupport, trSupportList, trSupportDis, trSubst, trTerm,
      trTerms] at h ⊢
  exact h

/-- A commuting direct/path pair has identical structural symbol maps. -/
theorem Commutes.sym_eq
    {canon : String → String} {Pi Pi' : RuleId → Option Rule}
    {Gamma Gamma' : LeafId → Option Atom}
    {CertOk CertOk' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {B : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk'}
    {P : BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk'}
    (hc : Commutes B P) :
    B.sym = P.compose.sym := by
  cases hB : B.sym with
  | mk predB conB =>
    cases hP : P.compose.sym with
    | mk predP conP =>
      congr
      · funext p
        simpa [hB, hP] using hc.predMap_eq p
      · funext k
        simpa [hB, hP] using hc.conMap_eq k

/-- A direct bridge commutes with a chosen path exactly when its symbol and
leaf maps equal those of the path composite. -/
theorem Commutes.of_maps_eq
    {canon : String → String} {Pi Pi' : RuleId → Option Rule}
    {Gamma Gamma' : LeafId → Option Atom}
    {CertOk CertOk' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {B : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk'}
    {P : BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk'} :
    Commutes B P ↔
      (B.sym = P.compose.sym ∧ B.leafMap = P.compose.leafMap) := by
  constructor
  · intro hc
    exact ⟨hc.sym_eq, funext hc.leafMap_eq⟩
  · rintro ⟨sym_eq, leafMap_eq⟩
    constructor
    · intro a
      rw [sym_eq]
    · intro w
      rw [sym_eq, leafMap_eq]
      exact (P.trans_eq_compose w).symm

/-- A checked source support translated stepwise along a commuting path has
exactly the same final support term under the direct bridge. Both symbol maps
translate its conclusion to the same atom, which is checked in their common
target environment with the source obligation list unchanged. -/
theorem direct_transport_agrees
    {canon : String → String} {Pi Pi' : RuleId → Option Rule}
    {Gamma Gamma' : LeafId → Option Atom}
    {CertOk CertOk' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (B : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk')
    (P : BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk')
    (hc : Commutes B P)
    {w w' : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk w C O)
    (hw : P.trans w = some w') :
    trSupport B.sym B.leafMap w = some w' ∧
      ∃ C', trAtom B.sym C = some C' ∧
        trAtom P.compose.sym C = some C' ∧
        HasSupport canon Pi' Gamma' CertOk' w' C' O := by
  have hwB : trSupport B.sym B.leafMap w = some w' := by
    rw [hc.support_eq]
    exact hw
  have hwP :
      trSupport P.compose.sym P.compose.leafMap w = some w' := by
    rw [← P.trans_eq_compose]
    exact hw
  obtain ⟨C', hCP, htarget⟩ := support_transport P.compose h hwP
  refine ⟨hwB, C', ?_, hCP, htarget⟩
  rw [hc.atom_eq]
  exact hCP

/-- The common target policy pins translation of every source rule: the
direct bridge and path composite cannot choose different translated rules at
the same retained rule identifier. This consequence does not provide global
atom or support commutation. -/
theorem commutes_on_rules
    {canon : String → String} {Pi Pi' : RuleId → Option Rule}
    {Gamma Gamma' : LeafId → Option Atom}
    {CertOk CertOk' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (B : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk')
    (P : BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk')
    {rn : RuleId} {r : Rule} (h : Pi rn = some r) :
    trRule B.sym r = trRule P.compose.sym r := by
  obtain ⟨rB, hrB, htargetB⟩ := B.rule_ok rn r h
  obtain ⟨rP, hrP, htargetP⟩ := P.compose.rule_ok rn r h
  rw [hrB, hrP]
  exact htargetB.symm.trans htargetP

/-- Once the direct and composite leaf maps agree at an admitted source leaf,
the common target evidence environment pins their translations of that
leaf's atom. This local consequence does not replace either global equation
required by `Commutes`. -/
theorem commutes_on_leaves
    {canon : String → String} {Pi Pi' : RuleId → Option Rule}
    {Gamma Gamma' : LeafId → Option Atom}
    {CertOk CertOk' :
      BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (B : StructuralBridge canon Pi Pi' Gamma Gamma' CertOk CertOk')
    (P : BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk')
    {l : LeafId} {p : Atom}
    (hleaf : B.leafMap l = P.compose.leafMap l)
    (h : Gamma l = some p) :
    trAtom B.sym p = trAtom P.compose.sym p := by
  obtain ⟨pB, hpB, htargetB⟩ := B.leaf_ok l p h
  obtain ⟨pP, hpP, htargetP⟩ := P.compose.leaf_ok l p h
  rw [hpB, hpP]
  rw [hleaf] at htargetB
  exact htargetB.symm.trans htargetP

/-! ### Direct/path applicability and accepted edges -/

/-- A commuting direct bridge and path induce the same checker-tied
applicability conjunct. The proof uses only support-map coherence: this does
not identify PW0's arbitrary candidate relations. -/
theorem admits_iff_of_commutes
    {κ μ : Instance.Context}
    {B : StructuralBridge κ.canon κ.policy.ruleLookup μ.policy.ruleLookup
      κ.Gamma μ.Gamma κ.CertOk μ.CertOk}
    {P : BridgePath κ.canon κ.policy.ruleLookup μ.policy.ruleLookup
      κ.Gamma μ.Gamma κ.CertOk μ.CertOk}
    (hc : Commutes B P) (w : Instance.World κ) (u : Instance.World μ) :
    Admits B.sym B.leafMap w u ↔
      Admits P.compose.sym P.compose.leafMap w u := by
  constructor
  · intro hadm t ht
    obtain ⟨t', htr, hmem⟩ := hadm t ht
    refine ⟨t', ?_, hmem⟩
    rw [← P.trans_eq_compose, ← hc.support_eq]
    exact htr
  · intro hadm t ht
    obtain ⟨t', htr, hmem⟩ := hadm t ht
    refine ⟨t', ?_, hmem⟩
    rw [← P.trans_eq_compose] at htr
    rw [← hc.support_eq] at htr
    exact htr

/-- The accepted edge relation for an exact bridge: literally the
intersection of a caller-supplied candidate relation with the bridge's
checker-tied applicability judgment. This instantiates PW0 `Frame.A` when
`R` is the bridge candidate relation and `Admits` supplies `Frame.accept`. -/
def Accepted
    {κ μ : Instance.Context}
    (R : Instance.World κ → Instance.World μ → Prop)
    (m : SymMap) (lm : LeafId → LeafId)
    (w : Instance.World κ) (u : Instance.World μ) : Prop :=
  R w u ∧ Admits m lm w u

/-- Full accepted edges agree between a direct bridge and a commuting path
only when the caller also supplies coherence of their candidate relations.
`Commutes` accounts for the `Admits` conjunct; it cannot determine arbitrary
PW0 candidate relations. -/
theorem accepted_iff_of_commutes
    {κ μ : Instance.Context}
    {B : StructuralBridge κ.canon κ.policy.ruleLookup μ.policy.ruleLookup
      κ.Gamma μ.Gamma κ.CertOk μ.CertOk}
    {P : BridgePath κ.canon κ.policy.ruleLookup μ.policy.ruleLookup
      κ.Gamma μ.Gamma κ.CertOk μ.CertOk}
    (hc : Commutes B P)
    (Rdirect Rpath : Instance.World κ → Instance.World μ → Prop)
    (w : Instance.World κ) (u : Instance.World μ)
    (hR : Rdirect w u ↔ Rpath w u) :
    Accepted Rdirect B.sym B.leafMap w u ↔
      Accepted Rpath P.compose.sym P.compose.leafMap w u := by
  exact and_congr hR (admits_iff_of_commutes hc w u)

/-- **T9, path transport.** A checked source support transports along any
chosen path of exact structural bridges whose stepwise translation is
defined: the result is checked in the path's final environment, concludes
the composite-translated claim, and carries the *same* obligations — T6's
`support_transport` applied to the path's composite, which path coherence
makes the same thing as the stepwise chain. -/
theorem path_support_transport
    {canon Pi Pi' Gamma Gamma' CertOk CertOk'}
    (P : BridgePath canon Pi Pi' Gamma Gamma' CertOk CertOk')
    {w w' : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk w C O)
    (hw : P.trans w = some w') :
    ∃ C', trAtom P.compose.sym C = some C' ∧
      HasSupport canon Pi' Gamma' CertOk' w' C' O := by
  rw [P.trans_eq_compose] at hw
  exact support_transport P.compose h hw

end Lara.PW
