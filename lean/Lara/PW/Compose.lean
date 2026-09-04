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
* **Named direct-bridge agreement is reserved for stacked PR 2.** The
  commuting-triangle relation, direct-versus-composite transport theorem,
  rule and leaf consequences, and witness examples are intentionally absent
  from this foundation module.

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
