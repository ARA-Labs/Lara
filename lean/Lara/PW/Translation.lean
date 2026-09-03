/-
# PW-T6 — the partial symbol translation (issue #191, tracker #189)

The bridge-global typed partial claim translation of the possible-world design
(`lara-paper/plan/possible-world-semantics-brainstorm.md` §Structural Bridge),
realized at the level the checker actually types: a partial map on predicate
and constructor symbols, lifted structurally to terms, atoms, patterns,
substitutions, rules, and support terms. Everything else — variables, numeric
and string literals, rule identifiers, question keys, leaf hole sets,
assurances — is carried across unchanged; leaves are renamed by a separate
total `LeafId` map supplied by the bridge (`Lara.PW.Structural`).

Partiality is the design's "explicit translation-domain evidence": every
lifted map is `Option`-valued, `none` exactly when a symbol falls outside the
bridge's vocabulary, and the transport theorem takes the `some` hypotheses as
its domain evidence rather than assuming totality.

Two structural facts carry the whole file, and both are proved here:

* **Instantiation commutes with translation** (`instAPat_tr`): translating a
  substitution and a pattern and then instantiating equals instantiating and
  then translating. Variables are untouched by the translation, and the
  instantiated constructor name is the pattern's own, so the two routes meet.
* **`≡` survives translation** (`equiv_tr`): `nf` canonicalizes numeric
  literals only, the translation renames predicate/constructor names only, so
  the two commute and `nf`-equality is preserved.

This module only imports; no local definition is touched (PW0's gate 1
discipline, `docs/theory-pw0-outer-model.md` §3).
-/

import Lara.Support

namespace Lara.PW

open Lara.Support

/-- A partial symbol translation: where the bridge's vocabulary map is
defined. Predicate and constructor namespaces are translated independently —
they are distinct symbol classes in the core AST (`PredSym` vs `ConSym`), so
one may be renamed while the other is out of vocabulary. -/
structure SymMap where
  predMap : String → Option String
  conMap  : String → Option String

/-- The identity translation: every symbol is in vocabulary and unchanged. -/
def SymMap.id : SymMap where
  predMap := some
  conMap  := some

/-! ### Lifting to ground terms and atoms -/

mutual
  /-- Translate a ground term: literals unchanged, constructor names through
  `conMap`, argument order preserved. -/
  def trTerm (m : SymMap) : Term → Option Term
    | .num s => some (.num s)
    | .str s => some (.str s)
    | .con k ts =>
      match m.conMap k, trTerms m ts with
      | some k', some ts' => some (.con k' ts')
      | _, _ => none
  /-- Translate a ground argument list. -/
  def trTerms (m : SymMap) : Terms → Option Terms
    | .nil => some .nil
    | .cons t ts =>
      match trTerm m t, trTerms m ts with
      | some t', some ts' => some (.cons t' ts')
      | _, _ => none
end

/-- Translate an atom: predicate name through `predMap`, arguments through
`trTerms`. This is the claim translation `τ` a structural bridge exposes. -/
def trAtom (m : SymMap) : Atom → Option Atom
  | .atom p ts =>
    match m.predMap p, trTerms m ts with
    | some p', some ts' => some (.atom p' ts')
    | _, _ => none

/-- Translate a list of atoms elementwise; `none` if any element is out of
vocabulary. -/
def trAtoms (m : SymMap) : List Atom → Option (List Atom)
  | [] => some []
  | a :: as =>
    match trAtom m a, trAtoms m as with
    | some a', some as' => some (a' :: as')
    | _, _ => none

/-! ### Lifting to patterns, substitutions, and rules -/

mutual
  /-- Translate a rule-body pattern: variables and literals unchanged,
  constructor names through `conMap`. -/
  def trPat (m : SymMap) : Pat → Option Pat
    | .var x => some (.var x)
    | .num s => some (.num s)
    | .str s => some (.str s)
    | .con k ps =>
      match m.conMap k.name, trPats m ps with
      | some k', some ps' => some (.con ⟨k'⟩ ps')
      | _, _ => none
  /-- Translate a pattern argument list. -/
  def trPats (m : SymMap) : Pats → Option Pats
    | .nil => some .nil
    | .cons p ps =>
      match trPat m p, trPats m ps with
      | some p', some ps' => some (.cons p' ps')
      | _, _ => none
end

/-- Translate an atom pattern. -/
def trAPat (m : SymMap) (ap : APat) : Option APat :=
  match m.predMap ap.pred.name, trPats m ap.args with
  | some p', some ps' => some ⟨⟨p'⟩, ps'⟩
  | _, _ => none

/-- Translate a premise list. -/
def trAPats (m : SymMap) : List APat → Option (List APat)
  | [] => some []
  | ap :: aps =>
    match trAPat m ap, trAPats m aps with
    | some ap', some aps' => some (ap' :: aps')
    | _, _ => none

/-- Translate a substitution: bindings keep their variables, bound terms are
translated. The domain is untouched, which is what lets `θNodup`/`θDom`
transport verbatim. -/
def trSubst (m : SymMap) : Subst → Option Subst
  | [] => some []
  | (x, t) :: θ =>
    match trTerm m t, trSubst m θ with
    | some t', some θ' => some ((x, t') :: θ')
    | _, _ => none

/-- Translate a critical question: the answer pattern is translated, the
name and the mandatory flag are preserved — question keys are rule-local
vocabulary, not claim vocabulary. -/
def trQuestion (m : SymMap) (q : Question) : Option Question :=
  match trAPat m q.answer with
  | some a' => some { q with answer := a' }
  | none => none

/-- Translate a question list. -/
def trQuestions (m : SymMap) : List Question → Option (List Question)
  | [] => some []
  | q :: qs =>
    match trQuestion m q, trQuestions m qs with
    | some q', some qs' => some (q' :: qs')
    | _, _ => none

/-- Translate a rule: premises, conclusion, and question answers are
translated; mode, declared parameters, the trusted flag, and the certifier
allowlist are preserved. A structural bridge's target policy must map each
rule identifier to exactly this translated rule (`StructuralBridge.rule_ok`). -/
def trRule (m : SymMap) (r : Rule) : Option Rule :=
  match trAPats m r.premises, trAPat m r.concl, trQuestions m r.questions with
  | some ps', some c', some qs' =>
      some { r with premises := ps', concl := c', questions := qs' }
  | _, _, _ => none

/-! ### Lifting to support terms

The dependent partial support map `T_{b}` of the design's `StructuralBridge`:
rule identifiers, hole sets, and assurances (including the frozen certificate
triple) are carried verbatim; substitutions are translated; leaves are renamed
by the bridge's total `LeafId` map. -/

mutual
  /-- Translate a support term. -/
  def trSupport (m : SymMap) (lm : LeafId → LeafId) :
      SupportTerm → Option SupportTerm
    | .leaf l => some (.leaf (lm l))
    | .inst rn θ ws D H α =>
      match trSubst m θ, trSupportList m lm ws, trSupportDis m lm D with
      | some θ', some ws', some D' => some (.inst rn θ' ws' D' H α)
      | _, _, _ => none
  /-- Translate a premise-subterm list. -/
  def trSupportList (m : SymMap) (lm : LeafId → LeafId) :
      List SupportTerm → Option (List SupportTerm)
    | [] => some []
    | w :: ws =>
      match trSupport m lm w, trSupportList m lm ws with
      | some w', some ws' => some (w' :: ws')
      | _, _ => none
  /-- Translate a discharge map; question keys are preserved. -/
  def trSupportDis (m : SymMap) (lm : LeafId → LeafId) :
      List (QuestionId × SupportTerm) →
      Option (List (QuestionId × SupportTerm))
    | [] => some []
    | (q, w) :: D =>
      match trSupport m lm w, trSupportDis m lm D with
      | some w', some D' => some ((q, w') :: D')
      | _, _ => none
end

/-! ### List bookkeeping: lengths, elements, keys -/

/-- Elementwise reading of a translated atom list. Stated in `bind` form so
it serves both directions: a defined slot forces a defined translated slot
and vice versa. -/
theorem trAtoms_getElem? {m : SymMap} :
    ∀ {As As' : List Atom}, trAtoms m As = some As' →
      ∀ i : Nat, As'[i]? = (As[i]?).bind (trAtom m) := by
  intro As
  induction As with
  | nil =>
    intro As' h i
    cases h
    simp
  | cons a as ih =>
    intro As' h i
    unfold trAtoms at h
    cases ha : trAtom m a with
    | none => rw [ha] at h; exact nomatch h
    | some a' =>
      rw [ha] at h
      cases has : trAtoms m as with
      | none => rw [has] at h; exact nomatch h
      | some as' =>
        rw [has] at h
        cases h
        cases i with
        | zero => simp [ha]
        | succ j => simpa using ih has j

/-- Translating an atom list preserves length. -/
theorem trAtoms_length {m : SymMap} :
    ∀ {As As' : List Atom}, trAtoms m As = some As' → As'.length = As.length := by
  intro As
  induction As with
  | nil => intro As' h; cases h; rfl
  | cons a as ih =>
    intro As' h
    unfold trAtoms at h
    cases ha : trAtom m a with
    | none => rw [ha] at h; exact nomatch h
    | some a' =>
      rw [ha] at h
      cases has : trAtoms m as with
      | none => rw [has] at h; exact nomatch h
      | some as' =>
        rw [has] at h
        cases h
        simpa using ih has

/-- Elementwise definedness gives whole-list definedness: the translation-
domain evidence for a list of atoms can be assembled slot by slot. -/
theorem trAtoms_defined {m : SymMap} :
    ∀ {As : List Atom},
      (∀ (i : Nat) (a : Atom), As[i]? = some a → (trAtom m a).isSome = true) →
      ∃ As', trAtoms m As = some As' := by
  intro As
  induction As with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons a as ih =>
    intro h
    have ha : (trAtom m a).isSome = true := h 0 a (by simp)
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha
    obtain ⟨as', has⟩ := ih fun i b hb => h (i + 1) b (by simpa using hb)
    exact ⟨a' :: as', by unfold trAtoms; rw [ha', has]⟩

/-- Translating a substitution preserves its domain, order included. -/
theorem trSubst_fst {m : SymMap} :
    ∀ {θ θ' : Subst}, trSubst m θ = some θ' →
      θ'.map Prod.fst = θ.map Prod.fst := by
  intro θ
  induction θ with
  | nil => intro θ' h; cases h; rfl
  | cons xt θ ih =>
    intro θ' h
    obtain ⟨x, t⟩ := xt
    unfold trSubst at h
    cases ht : trTerm m t with
    | none => rw [ht] at h; exact nomatch h
    | some t' =>
      rw [ht] at h
      cases hθ : trSubst m θ with
      | none => rw [hθ] at h; exact nomatch h
      | some θ'' =>
        rw [hθ] at h
        cases h
        simpa using ih hθ

/-- A defined lookup translates: the bound term is in the translation's
domain (it is a binding of a translated substitution), and the translated
substitution binds the translated term at the same variable. -/
theorem lookupSubst_tr {m : SymMap} :
    ∀ {θ θ' : Subst}, trSubst m θ = some θ' →
      ∀ {x : VarId} {t : Term}, lookupSubst θ x = some t →
        ∃ t', trTerm m t = some t' ∧ lookupSubst θ' x = some t' := by
  intro θ
  induction θ with
  | nil => intro θ' h x t hl; exact nomatch hl
  | cons yt θ ih =>
    intro θ' h x t hl
    obtain ⟨y, s⟩ := yt
    unfold trSubst at h
    cases hs : trTerm m s with
    | none => rw [hs] at h; exact nomatch h
    | some s' =>
      rw [hs] at h
      cases hθ : trSubst m θ with
      | none => rw [hθ] at h; exact nomatch h
      | some θ'' =>
        rw [hθ] at h
        cases h
        unfold lookupSubst at hl ⊢
        by_cases hxy : y = x
        · simp only [if_pos hxy] at hl ⊢
          cases hl
          exact ⟨s', hs, rfl⟩
        · simp only [if_neg hxy] at hl ⊢
          exact ih hθ hl

/-! ### Instantiation commutes with translation -/

mutual
  /-- Instantiating a translated pattern under the translated substitution
  yields exactly the translated instance. Variables are untouched by the
  translation and the instantiated constructor name is the pattern's own,
  so the two routes meet. -/
  theorem instPat_tr {m : SymMap} {θ θ' : Subst} (hθ : trSubst m θ = some θ') :
      ∀ (p : Pat) {p' : Pat} {t : Term}, trPat m p = some p' →
        instPat θ p = some t →
        ∃ t', trTerm m t = some t' ∧ instPat θ' p' = some t'
    | .var x, p', t, hp, ht => by
        unfold trPat at hp
        cases hp
        unfold instPat at ht ⊢
        exact lookupSubst_tr hθ ht
    | .num s, p', t, hp, ht => by
        unfold trPat at hp
        cases hp
        unfold instPat at ht ⊢
        cases ht
        exact ⟨.num s, rfl, rfl⟩
    | .str s, p', t, hp, ht => by
        unfold trPat at hp
        cases hp
        unfold instPat at ht ⊢
        cases ht
        exact ⟨.str s, rfl, rfl⟩
    | .con k ps, p', t, hp, ht => by
        unfold trPat at hp
        cases hk : m.conMap k.name with
        | none => rw [hk] at hp; exact nomatch hp
        | some k' =>
          rw [hk] at hp
          cases hps : trPats m ps with
          | none => rw [hps] at hp; exact nomatch hp
          | some ps' =>
            rw [hps] at hp
            cases hp
            unfold instPat at ht
            cases hts : instPats θ ps with
            | none => rw [hts] at ht; exact nomatch ht
            | some ts =>
              rw [hts] at ht
              cases ht
              obtain ⟨ts', htr, hinst⟩ := instPats_tr hθ ps hps hts
              refine ⟨.con k' ts', ?_, ?_⟩
              · unfold trTerm
                rw [hk, htr]
              · unfold instPat
                rw [hinst]
                rfl

  /-- List form of `instPat_tr`. -/
  theorem instPats_tr {m : SymMap} {θ θ' : Subst} (hθ : trSubst m θ = some θ') :
      ∀ (ps : Pats) {ps' : Pats} {ts : Terms}, trPats m ps = some ps' →
        instPats θ ps = some ts →
        ∃ ts', trTerms m ts = some ts' ∧ instPats θ' ps' = some ts'
    | .nil, ps', ts, hp, ht => by
        unfold trPats at hp
        cases hp
        unfold instPats at ht ⊢
        cases ht
        exact ⟨.nil, rfl, rfl⟩
    | .cons p ps, ps', ts, hp, ht => by
        unfold trPats at hp
        cases hp1 : trPat m p with
        | none => rw [hp1] at hp; exact nomatch hp
        | some p1 =>
          rw [hp1] at hp
          cases hp2 : trPats m ps with
          | none => rw [hp2] at hp; exact nomatch hp
          | some ps1 =>
            rw [hp2] at hp
            cases hp
            unfold instPats at ht
            cases ht1 : instPat θ p with
            | none => rw [ht1] at ht; exact nomatch ht
            | some t1 =>
              rw [ht1] at ht
              cases ht2 : instPats θ ps with
              | none => rw [ht2] at ht; exact nomatch ht
              | some ts1 =>
                rw [ht2] at ht
                cases ht
                obtain ⟨t1', htr1, hin1⟩ := instPat_tr hθ p hp1 ht1
                obtain ⟨ts1', htr2, hin2⟩ := instPats_tr hθ ps hp2 ht2
                refine ⟨.cons t1' ts1', ?_, ?_⟩
                · unfold trTerms
                  rw [htr1, htr2]
                · unfold instPats
                  rw [hin1, hin2]
end

/-- Atom-pattern instantiation commutes with translation: the translated
conclusion of an instance is the instance of the translated pattern. This is
the conclusion law `concl (T b t) = τ b (concl t)` at the pattern level. -/
theorem instAPat_tr {m : SymMap} {θ θ' : Subst} (hθ : trSubst m θ = some θ')
    {ap ap' : APat} {a : Atom} (hap : trAPat m ap = some ap')
    (ha : instAPat θ ap = some a) :
    ∃ a', trAtom m a = some a' ∧ instAPat θ' ap' = some a' := by
  unfold trAPat at hap
  cases hp : m.predMap ap.pred.name with
  | none => rw [hp] at hap; exact nomatch hap
  | some p' =>
    rw [hp] at hap
    cases hps : trPats m ap.args with
    | none => rw [hps] at hap; exact nomatch hap
    | some ps' =>
      rw [hps] at hap
      cases hap
      unfold instAPat at ha
      cases hts : instPats θ ap.args with
      | none => rw [hts] at ha; exact nomatch ha
      | some ts =>
        rw [hts] at ha
        cases ha
        obtain ⟨ts', htr, hinst⟩ := instPats_tr hθ ap.args hps hts
        refine ⟨.atom p' ts', ?_, ?_⟩
        · simp only [trAtom]
          rw [hp, htr]
        · unfold instAPat
          rw [hinst]
          rfl

/-- Premise-list instantiation commutes with translation. -/
theorem instAPats_tr {m : SymMap} {θ θ' : Subst} (hθ : trSubst m θ = some θ') :
    ∀ (aps : List APat) {aps' : List APat} {as : List Atom},
      trAPats m aps = some aps' → instAPats θ aps = some as →
      ∃ as', trAtoms m as = some as' ∧ instAPats θ' aps' = some as' := by
  intro aps
  induction aps with
  | nil =>
    intro aps' as hap ha
    cases hap
    cases ha
    exact ⟨[], rfl, rfl⟩
  | cons ap aps ih =>
    intro aps' as hap ha
    unfold trAPats at hap
    cases h1 : trAPat m ap with
    | none => rw [h1] at hap; exact nomatch hap
    | some ap1 =>
      rw [h1] at hap
      cases h2 : trAPats m aps with
      | none => rw [h2] at hap; exact nomatch hap
      | some aps1 =>
        rw [h2] at hap
        cases hap
        unfold instAPats at ha
        cases h3 : instAPat θ ap with
        | none => rw [h3] at ha; exact nomatch ha
        | some a1 =>
          rw [h3] at ha
          cases h4 : instAPats θ aps with
          | none => rw [h4] at ha; exact nomatch ha
          | some as1 =>
            rw [h4] at ha
            cases ha
            obtain ⟨a1', htr1, hin1⟩ := instAPat_tr hθ h1 h3
            obtain ⟨as1', htr2, hin2⟩ := ih h2 h4
            refine ⟨a1' :: as1', ?_, ?_⟩
            · unfold trAtoms
              rw [htr1, htr2]
            · unfold instAPats
              rw [hin1, hin2]

/-! ### `≡` survives translation -/

mutual
  /-- Normal form commutes with translation: `nf` canonicalizes numeric
  literals only, the translation renames constructor names only. -/
  theorem trTerm_nf {m : SymMap} (canon : String → String) :
      ∀ (t : Term) {t' : Term}, trTerm m t = some t' →
        trTerm m (nfTerm canon t) = some (nfTerm canon t')
    | .num s, t', h => by
        unfold trTerm at h
        cases h
        rfl
    | .str s, t', h => by
        unfold trTerm at h
        cases h
        rfl
    | .con k ts, t', h => by
        unfold trTerm at h
        cases hk : m.conMap k with
        | none => rw [hk] at h; exact nomatch h
        | some k' =>
          rw [hk] at h
          cases hts : trTerms m ts with
          | none => rw [hts] at h; exact nomatch h
          | some ts' =>
            rw [hts] at h
            cases h
            show trTerm m (.con k (nfTerms canon ts)) = _
            unfold trTerm
            rw [hk, trTerms_nf canon ts hts]
            rfl

  /-- List form of `trTerm_nf`. -/
  theorem trTerms_nf {m : SymMap} (canon : String → String) :
      ∀ (ts : Terms) {ts' : Terms}, trTerms m ts = some ts' →
        trTerms m (nfTerms canon ts) = some (nfTerms canon ts')
    | .nil, ts', h => by
        unfold trTerms at h
        cases h
        rfl
    | .cons t ts, ts', h => by
        unfold trTerms at h
        cases ht : trTerm m t with
        | none => rw [ht] at h; exact nomatch h
        | some t1 =>
          rw [ht] at h
          cases hts : trTerms m ts with
          | none => rw [hts] at h; exact nomatch h
          | some ts1 =>
            rw [hts] at h
            cases h
            show trTerms m (.cons (nfTerm canon t) (nfTerms canon ts)) = _
            unfold trTerms
            rw [trTerm_nf canon t ht, trTerms_nf canon ts hts]
            rfl
end

/-- Atom normal form commutes with translation. -/
theorem trAtom_nf {m : SymMap} (canon : String → String) {a a' : Atom}
    (h : trAtom m a = some a') :
    trAtom m (nf canon a) = some (nf canon a') := by
  obtain ⟨p, ts⟩ := a
  simp only [trAtom] at h
  cases hp : m.predMap p with
  | none => rw [hp] at h; exact nomatch h
  | some p' =>
    rw [hp] at h
    cases hts : trTerms m ts with
    | none => rw [hts] at h; exact nomatch h
    | some ts' =>
      rw [hts] at h
      cases h
      show trAtom m (.atom p (nfTerms canon ts)) = _
      simp only [trAtom]
      rw [hp, trTerms_nf canon ts hts]
      rfl

/-- **`≡` survives translation.** Two `≡`-identical atoms translate to
`≡`-identical atoms; premise identity and discharge answers therefore
transport verbatim. -/
theorem equiv_tr {m : SymMap} {canon : String → String} {a b a' b' : Atom}
    (ha : trAtom m a = some a') (hb : trAtom m b = some b')
    (h : equiv canon a b) : equiv canon a' b' := by
  have ha' := trAtom_nf (m := m) canon ha
  have hb' := trAtom_nf (m := m) canon hb
  unfold equiv at h
  rw [h, hb'] at ha'
  exact (Option.some.inj ha').symm

/-! ### Rule and question inversions

A translated rule is the source rule with translated premises, conclusion,
and answers; every carrier the typing judgment reads off the rule that is
*not* claim vocabulary — mode, parameters, the trusted flag, certifiers,
question names, mandatory flags — is preserved on the nose. -/

/-- Inversion for `trQuestion`. -/
theorem trQuestion_inv {m : SymMap} {q q' : Question}
    (h : trQuestion m q = some q') :
    ∃ a', trAPat m q.answer = some a' ∧ q' = { q with answer := a' } := by
  unfold trQuestion at h
  cases ha : trAPat m q.answer with
  | none => rw [ha] at h; exact nomatch h
  | some a' =>
    rw [ha] at h
    cases h
    exact ⟨a', rfl, rfl⟩

/-- A source question translates into the translated list. -/
theorem trQuestions_mem {m : SymMap} :
    ∀ {qs qs' : List Question}, trQuestions m qs = some qs' →
      ∀ {qd : Question}, qd ∈ qs →
        ∃ qd', trQuestion m qd = some qd' ∧ qd' ∈ qs' := by
  intro qs
  induction qs with
  | nil => intro qs' h qd hm; exact absurd hm (List.not_mem_nil)
  | cons q qs ih =>
    intro qs' h qd hm
    unfold trQuestions at h
    cases h1 : trQuestion m q with
    | none => rw [h1] at h; exact nomatch h
    | some q1 =>
      rw [h1] at h
      cases h2 : trQuestions m qs with
      | none => rw [h2] at h; exact nomatch h
      | some qs1 =>
        rw [h2] at h
        cases h
        cases List.mem_cons.mp hm with
        | inl he => exact he ▸ ⟨q1, h1, List.mem_cons_self ..⟩
        | inr ht =>
          obtain ⟨qd', hq, hmem⟩ := ih h2 ht
          exact ⟨qd', hq, List.mem_cons_of_mem _ hmem⟩

/-- Every translated question comes from a source question. -/
theorem trQuestions_mem_rev {m : SymMap} :
    ∀ {qs qs' : List Question}, trQuestions m qs = some qs' →
      ∀ {qd' : Question}, qd' ∈ qs' →
        ∃ qd, qd ∈ qs ∧ trQuestion m qd = some qd' := by
  intro qs
  induction qs with
  | nil =>
    intro qs' h qd' hm
    cases h
    exact absurd hm (List.not_mem_nil)
  | cons q qs ih =>
    intro qs' h qd' hm
    unfold trQuestions at h
    cases h1 : trQuestion m q with
    | none => rw [h1] at h; exact nomatch h
    | some q1 =>
      rw [h1] at h
      cases h2 : trQuestions m qs with
      | none => rw [h2] at h; exact nomatch h
      | some qs1 =>
        rw [h2] at h
        cases h
        cases List.mem_cons.mp hm with
        | inl he => exact ⟨q, List.mem_cons_self .., he ▸ h1⟩
        | inr ht =>
          obtain ⟨qd, hmem, hq⟩ := ih h2 ht
          exact ⟨qd, List.mem_cons_of_mem _ hmem, hq⟩

/-- Question names survive translation, order included. -/
theorem trQuestions_names {m : SymMap} :
    ∀ {qs qs' : List Question}, trQuestions m qs = some qs' →
      qs'.map (·.name) = qs.map (·.name) := by
  intro qs
  induction qs with
  | nil => intro qs' h; cases h; rfl
  | cons q qs ih =>
    intro qs' h
    unfold trQuestions at h
    cases h1 : trQuestion m q with
    | none => rw [h1] at h; exact nomatch h
    | some q1 =>
      rw [h1] at h
      cases h2 : trQuestions m qs with
      | none => rw [h2] at h; exact nomatch h
      | some qs1 =>
        rw [h2] at h
        cases h
        obtain ⟨a', _, he⟩ := trQuestion_inv h1
        simp only [List.map_cons, he, ih h2]

/-- Mandatory question names survive translation, order included. -/
theorem trQuestions_mand_names {m : SymMap} :
    ∀ {qs qs' : List Question}, trQuestions m qs = some qs' →
      (qs'.filter (·.mandatory)).map (·.name) =
        (qs.filter (·.mandatory)).map (·.name) := by
  intro qs
  induction qs with
  | nil => intro qs' h; cases h; rfl
  | cons q qs ih =>
    intro qs' h
    unfold trQuestions at h
    cases h1 : trQuestion m q with
    | none => rw [h1] at h; exact nomatch h
    | some q1 =>
      rw [h1] at h
      cases h2 : trQuestions m qs with
      | none => rw [h2] at h; exact nomatch h
      | some qs1 =>
        rw [h2] at h
        cases h
        obtain ⟨a', _, he⟩ := trQuestion_inv h1
        subst he
        by_cases hmand : q.mandatory = true
        · simp [hmand, ih h2]
        · simp [hmand, ih h2]

/-- Inversion for `trRule`. -/
theorem trRule_inv {m : SymMap} {r r' : Rule} (h : trRule m r = some r') :
    ∃ ps' c' qs', trAPats m r.premises = some ps' ∧
      trAPat m r.concl = some c' ∧ trQuestions m r.questions = some qs' ∧
      r' = { r with premises := ps', concl := c', questions := qs' } := by
  unfold trRule at h
  cases h1 : trAPats m r.premises with
  | none => rw [h1] at h; exact nomatch h
  | some ps' =>
    rw [h1] at h
    cases h2 : trAPat m r.concl with
    | none => rw [h2] at h; exact nomatch h
    | some c' =>
      rw [h2] at h
      cases h3 : trQuestions m r.questions with
      | none => rw [h3] at h; exact nomatch h
      | some qs' =>
        rw [h3] at h
        cases h
        exact ⟨ps', c', qs', rfl, rfl, rfl, rfl⟩


/-- Mode survives translation. -/
theorem trRule_mode {m : SymMap} {r r' : Rule} (h : trRule m r = some r') :
    r'.mode = r.mode := by
  obtain ⟨_, _, _, _, _, _, he⟩ := trRule_inv h
  subst he; rfl

/-- Declared parameters survive translation. -/
theorem trRule_params {m : SymMap} {r r' : Rule} (h : trRule m r = some r') :
    r'.params = r.params := by
  obtain ⟨_, _, _, _, _, _, he⟩ := trRule_inv h
  subst he; rfl

/-- The trusted-assurance flag survives translation. -/
theorem trRule_allowTrusted {m : SymMap} {r r' : Rule}
    (h : trRule m r = some r') : r'.allowTrusted = r.allowTrusted := by
  obtain ⟨_, _, _, _, _, _, he⟩ := trRule_inv h
  subst he; rfl

/-- The certifier allowlist survives translation: the frozen `(β, digest)`
pairs a rule admits are backend identity, not claim vocabulary. -/
theorem trRule_certifiers {m : SymMap} {r r' : Rule}
    (h : trRule m r = some r') : r'.certifiers = r.certifiers := by
  obtain ⟨_, _, _, _, _, _, he⟩ := trRule_inv h
  subst he; rfl

/-- Question names survive rule translation. -/
theorem trRule_questionNames {m : SymMap} {r r' : Rule}
    (h : trRule m r = some r') : questionNames r' = questionNames r := by
  obtain ⟨_, _, _, _, _, h3, he⟩ := trRule_inv h
  subst he
  exact trQuestions_names h3

/-- Mandatory names survive rule translation, hence so do open-obligation
computations. -/
theorem trRule_mandatoryNames {m : SymMap} {r r' : Rule}
    (h : trRule m r = some r') : mandatoryNames r' = mandatoryNames r := by
  obtain ⟨_, _, _, _, _, h3, he⟩ := trRule_inv h
  subst he
  exact trQuestions_mand_names h3

/-! ### Support-term bookkeeping -/

/-- Elementwise reading of a translated premise-subterm list, `bind` form. -/
theorem trSupportList_getElem? {m : SymMap} {lm : LeafId → LeafId} :
    ∀ {ws ws' : List SupportTerm}, trSupportList m lm ws = some ws' →
      ∀ i : Nat, ws'[i]? = (ws[i]?).bind (trSupport m lm) := by
  intro ws
  induction ws with
  | nil => intro ws' h i; cases h; simp
  | cons w ws ih =>
    intro ws' h i
    unfold trSupportList at h
    cases hw : trSupport m lm w with
    | none => rw [hw] at h; exact nomatch h
    | some w' =>
      rw [hw] at h
      cases hws : trSupportList m lm ws with
      | none => rw [hws] at h; exact nomatch h
      | some ws1 =>
        rw [hws] at h
        cases h
        cases i with
        | zero => simp [hw]
        | succ j => simpa using ih hws j

/-- Translating a premise-subterm list preserves length. -/
theorem trSupportList_length {m : SymMap} {lm : LeafId → LeafId} :
    ∀ {ws ws' : List SupportTerm}, trSupportList m lm ws = some ws' →
      ws'.length = ws.length := by
  intro ws
  induction ws with
  | nil => intro ws' h; cases h; rfl
  | cons w ws ih =>
    intro ws' h
    unfold trSupportList at h
    cases hw : trSupport m lm w with
    | none => rw [hw] at h; exact nomatch h
    | some w' =>
      rw [hw] at h
      cases hws : trSupportList m lm ws with
      | none => rw [hws] at h; exact nomatch h
      | some ws1 =>
        rw [hws] at h
        cases h
        simpa using ih hws

/-- Discharge keys survive translation, order included. -/
theorem trSupportDis_fst {m : SymMap} {lm : LeafId → LeafId} :
    ∀ {D D' : List (QuestionId × SupportTerm)},
      trSupportDis m lm D = some D' → D'.map Prod.fst = D.map Prod.fst := by
  intro D
  induction D with
  | nil => intro D' h; cases h; rfl
  | cons qw D ih =>
    intro D' h
    obtain ⟨q, w⟩ := qw
    unfold trSupportDis at h
    cases hw : trSupport m lm w with
    | none => rw [hw] at h; exact nomatch h
    | some w' =>
      rw [hw] at h
      cases hD : trSupportDis m lm D with
      | none => rw [hD] at h; exact nomatch h
      | some D1 =>
        rw [hD] at h
        cases h
        simpa using ih hD

/-- Elementwise reading of a translated discharge map, `bind` form: keys are
preserved, discharge terms are translated. -/
theorem trSupportDis_getElem? {m : SymMap} {lm : LeafId → LeafId} :
    ∀ {D D' : List (QuestionId × SupportTerm)},
      trSupportDis m lm D = some D' →
      ∀ j : Nat, D'[j]? =
        (D[j]?).bind fun qw => (trSupport m lm qw.2).map ((qw.1, ·)) := by
  intro D
  induction D with
  | nil => intro D' h j; cases h; simp
  | cons qw D ih =>
    intro D' h j
    obtain ⟨q, w⟩ := qw
    unfold trSupportDis at h
    cases hw : trSupport m lm w with
    | none => rw [hw] at h; exact nomatch h
    | some w' =>
      rw [hw] at h
      cases hD : trSupportDis m lm D with
      | none => rw [hD] at h; exact nomatch h
      | some D1 =>
        rw [hD] at h
        cases h
        cases j with
        | zero => simp [hw]
        | succ j' => simpa using ih hD j'

/-! ### The identity translation is total and inert

The endobridge case: with `SymMap.id` and the identity leaf map, every lift
is `some` of its argument. This is what lets the T7 pair be read as a
(degenerate) structural bridge, mechanizing "exact support transport holds
and grounded status still flips" at a live instance. -/

mutual
  /-- `trTerm` is inert under the identity translation. -/
  theorem trTerm_id : ∀ t : Term, trTerm SymMap.id t = some t
    | .num _ => rfl
    | .str _ => rfl
    | .con k ts => by
        unfold trTerm
        rw [trTerms_id ts]
        rfl
  /-- `trTerms` is inert under the identity translation. -/
  theorem trTerms_id : ∀ ts : Terms, trTerms SymMap.id ts = some ts
    | .nil => rfl
    | .cons t ts => by
        unfold trTerms
        rw [trTerm_id t, trTerms_id ts]
end

/-- `trAtom` is inert under the identity translation. -/
theorem trAtom_id (a : Atom) : trAtom SymMap.id a = some a := by
  obtain ⟨p, ts⟩ := a
  simp only [trAtom]
  rw [trTerms_id ts]
  rfl

/-- `trAtoms` is inert under the identity translation. -/
theorem trAtoms_id : ∀ as : List Atom, trAtoms SymMap.id as = some as
  | [] => rfl
  | a :: as => by
      unfold trAtoms
      rw [trAtom_id a, trAtoms_id as]

mutual
  /-- `trPat` is inert under the identity translation. -/
  theorem trPat_id : ∀ p : Pat, trPat SymMap.id p = some p
    | .var _ => rfl
    | .num _ => rfl
    | .str _ => rfl
    | .con k ps => by
        unfold trPat
        rw [trPats_id ps]
        rfl
  /-- `trPats` is inert under the identity translation. -/
  theorem trPats_id : ∀ ps : Pats, trPats SymMap.id ps = some ps
    | .nil => rfl
    | .cons p ps => by
        unfold trPats
        rw [trPat_id p, trPats_id ps]
end

/-- `trAPat` is inert under the identity translation. -/
theorem trAPat_id (ap : APat) : trAPat SymMap.id ap = some ap := by
  unfold trAPat
  rw [trPats_id ap.args]
  rfl

/-- `trAPats` is inert under the identity translation. -/
theorem trAPats_id : ∀ aps : List APat, trAPats SymMap.id aps = some aps
  | [] => rfl
  | ap :: aps => by
      unfold trAPats
      rw [trAPat_id ap, trAPats_id aps]

/-- `trSubst` is inert under the identity translation. -/
theorem trSubst_id : ∀ θ : Subst, trSubst SymMap.id θ = some θ
  | [] => rfl
  | (x, t) :: θ => by
      unfold trSubst
      rw [trTerm_id t, trSubst_id θ]

/-- `trQuestion` is inert under the identity translation. -/
theorem trQuestion_id (q : Question) : trQuestion SymMap.id q = some q := by
  unfold trQuestion
  rw [trAPat_id q.answer]

/-- `trQuestions` is inert under the identity translation. -/
theorem trQuestions_id : ∀ qs : List Question,
    trQuestions SymMap.id qs = some qs
  | [] => rfl
  | q :: qs => by
      unfold trQuestions
      rw [trQuestion_id q, trQuestions_id qs]

/-- `trRule` is inert under the identity translation. -/
theorem trRule_id (r : Rule) : trRule SymMap.id r = some r := by
  unfold trRule
  rw [trAPats_id r.premises, trAPat_id r.concl, trQuestions_id r.questions]

mutual
  /-- `trSupport` is inert under the identity translation and leaf map. -/
  theorem trSupport_id : ∀ w : SupportTerm,
      trSupport SymMap.id (fun l => l) w = some w
    | .leaf _ => rfl
    | .inst rn θ ws D H α => by
        unfold trSupport
        rw [trSubst_id θ, trSupportList_id ws, trSupportDis_id D]
  /-- `trSupportList` is inert under the identity translation. -/
  theorem trSupportList_id : ∀ ws : List SupportTerm,
      trSupportList SymMap.id (fun l => l) ws = some ws
    | [] => rfl
    | w :: ws => by
        unfold trSupportList
        rw [trSupport_id w, trSupportList_id ws]
  /-- `trSupportDis` is inert under the identity translation. -/
  theorem trSupportDis_id : ∀ D : List (QuestionId × SupportTerm),
      trSupportDis SymMap.id (fun l => l) D = some D
    | [] => rfl
    | (q, w) :: D => by
        unfold trSupportDis
        rw [trSupport_id w, trSupportDis_id D]
end

end Lara.PW
