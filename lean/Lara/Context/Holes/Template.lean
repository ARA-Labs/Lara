import Lara.Context.Holes.Syntax

namespace Lara.Context.Holes
open Lara.Support

/-! Template typing contains only the original rule metadata and recursive
typing premises. No constructor assumes support of the substituted result. -/

structure InstMeta (canon : String → String) (Pi : RuleId → Option Rule)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop)
    (rn : RuleId) (θ : Subst) (r : Rule)
    (premCount : Nat) (dischargeKeys : List QuestionId)
    (H : List QuestionId) (α : Assurance) (As Cs : List Atom)
    (Os : List (List QuestionId))
    (DCs : List Atom) (DOs : List (List QuestionId)) (C : Atom) : Prop where
  /-- the rule is policy content, looked up — never program-defined (§4) -/
  rule   : Pi rn = some r
  /-- `theta` is duplicate-free … -/
  θNodup : (θ.map Prod.fst).Nodup
  /-- … and `dom(theta) = {X1..Xm}` exactly — the §6.1 side condition (no
  extra bindings, no omitted declared parameters, questions/exceptions
  included since their variables are among `params` by rule wf, §4.1) -/
  θDom   : ∀ x : VarId, x ∈ θ.map Prod.fst ↔ x ∈ r.params
  /-- premise patterns instantiate … -/
  prems  : instAPats θ r.premises = some As
  /-- … and so does the conclusion pattern: `concl(w) = Ap_c theta` -/
  concl  : instAPat θ r.concl = some C
  lenAs  : premCount = As.length
  lenCs  : Cs.length = premCount
  lenOs  : Os.length = premCount
  /-- premise identity is `≡` (folded into `supports(...)`, §6.1) -/
  premEq : ∀ (i : Nat) (A B : Atom),
             Cs[i]? = some A → As[i]? = some B → equiv canon A B
  lenDCs : DCs.length = dischargeKeys.length
  lenDOs : DOs.length = dischargeKeys.length
  /-- each discharge answers its question's pattern under the same `theta` (§4.2) -/
  ans    : ∀ (j : Nat) (q : QuestionId) (A : Atom),
             dischargeKeys[j]? = some q → DCs[j]? = some A →
             ∃ qd, qd ∈ r.questions ∧ qd.name = q ∧
               ∃ Aq, instAPat θ qd.answer = some Aq ∧ equiv canon A Aq
  /-- the policy's question names are duplicate-free (rule wf) … -/
  qNodup : (questionNames r).Nodup
  /-- … as are the discharge keys … -/
  dNodup : dischargeKeys.Nodup
  /-- … and the hole set — so `D ⊎ H = questions(r)` is a genuine partition -/
  hNodup : H.Nodup
  /-- `D ⊎ H = questions(r)`: cover … -/
  cover  : ∀ qd, qd ∈ r.questions → qd.name ∈ dischargeKeys ∨ qd.name ∈ H
  /-- … disjointness … -/
  disj   : ∀ n, n ∈ dischargeKeys → n ∉ H
  /-- … and no junk on either side (a question absent from both is ill-formed) -/
  keysD  : ∀ n, n ∈ dischargeKeys → n ∈ questionNames r
  keysH  : ∀ n, n ∈ H → n ∈ questionNames r
  /-- strict rules declare no questions (§5), so `D` and `H` are empty -/
  strictNoQ : r.mode = .strict → dischargeKeys = [] ∧ H = []
  /-- the `assurance(m, alpha)` side condition -/
  assur  : AssuranceOk CertOk r As C α


variable {canon : String → String} {Pi : RuleId → Option Rule}
  {Γ : LeafId → Option Atom}
  {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}

variable {rn : RuleId} {θ : Subst} {r : Rule} {ws : List SupportTerm}
  {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {α : Assurance}
  {As Cs : List Atom} {Os : List (List QuestionId)}
  {DCs : List Atom} {DOs : List (List QuestionId)} {C : Atom}

theorem InstMeta.toInstSide
    (h : InstMeta canon Pi CertOk rn θ r ws.length (D.map Prod.fst)
      H α As Cs Os DCs DOs C) :
    InstSide canon Pi CertOk rn θ r ws D H α As Cs Os DCs DOs C where
  rule := h.rule
  θNodup := h.θNodup
  θDom := h.θDom
  prems := h.prems
  concl := h.concl
  lenAs := h.lenAs
  lenCs := h.lenCs
  lenOs := h.lenOs
  premEq := h.premEq
  lenDCs := by simpa using h.lenDCs
  lenDOs := by simpa using h.lenDOs
  qNodup := h.qNodup
  dNodup := h.dNodup
  hNodup := h.hNodup
  cover := h.cover
  disj := h.disj
  keysD := h.keysD
  keysH := h.keysH
  assur := h.assur
  ans := by
    intro j q w A hj hA
    apply h.ans j q A _ hA
    simpa using congrArg (Option.map Prod.fst) hj
  strictNoQ := by
    intro hm
    obtain ⟨hD, hH⟩ := h.strictNoQ hm
    exact ⟨List.map_eq_nil_iff.mp hD, hH⟩

theorem InstMeta.ofInstSide
    (h : InstSide canon Pi CertOk rn θ r ws D H α As Cs Os DCs DOs C) :
    InstMeta canon Pi CertOk rn θ r ws.length (D.map Prod.fst)
      H α As Cs Os DCs DOs C where
  rule := h.rule
  θNodup := h.θNodup
  θDom := h.θDom
  prems := h.prems
  concl := h.concl
  lenAs := h.lenAs
  lenCs := h.lenCs
  lenOs := h.lenOs
  premEq := h.premEq
  lenDCs := by simpa using h.lenDCs
  lenDOs := by simpa using h.lenDOs
  qNodup := h.qNodup
  dNodup := h.dNodup
  hNodup := h.hNodup
  cover := h.cover
  disj := h.disj
  keysD := h.keysD
  keysH := h.keysH
  assur := h.assur
  ans := by
    intro j q A hj hA
    cases hd : D[j]? with
    | none => simp [List.getElem?_map, hd] at hj
    | some pair =>
      rcases pair with ⟨q', w⟩
      have hq : q' = q := by simpa [List.getElem?_map, hd] using hj
      subst q'
      exact h.ans j q w A hd hA
  strictNoQ := by
    intro hm
    obtain ⟨hD, hH⟩ := h.strictNoQ hm
    exact ⟨by simp [hD], hH⟩

/-- The discharge rule accepts equivalent actual answer conclusions. -/
theorem InstMeta.answers_equiv {n : Nat} {keys : List QuestionId} {DCs' : List Atom}
    (h : InstMeta canon Pi CertOk rn θ r n keys H α As Cs Os DCs DOs C)
    (hlen : DCs'.length = DCs.length)
    (heq : ∀ (i : Nat) (A B : Atom), DCs'[i]? = some A → DCs[i]? = some B → equiv canon A B) :
    InstMeta canon Pi CertOk rn θ r n keys H α As Cs Os DCs' DOs C where
  rule := h.rule
  θNodup := h.θNodup
  θDom := h.θDom
  prems := h.prems
  concl := h.concl
  lenAs := h.lenAs
  lenCs := h.lenCs
  lenOs := h.lenOs
  premEq := h.premEq
  lenDOs := by simpa using h.lenDOs
  qNodup := h.qNodup
  dNodup := h.dNodup
  hNodup := h.hNodup
  cover := h.cover
  disj := h.disj
  keysD := h.keysD
  keysH := h.keysH
  assur := h.assur
  lenDCs := hlen.trans h.lenDCs
  strictNoQ := h.strictNoQ
  ans := by
    intro j q A hj hA
    obtain ⟨B, hB⟩ := getElem?_some_of_lt DCs j
      (by have := lt_of_getElem?_some hA; omega)
    obtain ⟨qd, hqd, hq, Aq, hinst, hequiv⟩ := h.ans j q B hj hB
    exact ⟨qd, hqd, hq, Aq, hinst, equiv_trans canon (heq j A B hA hB) hequiv⟩

mutual
  inductive HasTemplate (canon : String → String) (Pi : RuleId → Option Rule)
      (Γ : LeafId → Option Atom)
      (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop)
      (Δ : HoleSignature) : Template → Atom → List QuestionId → Prop where
    | core {w : SupportTerm} {C : Atom} {O : List QuestionId} (h : HasSupport canon Pi Γ CertOk w C O) :
        HasTemplate canon Pi Γ CertOk Δ (.core w) C O
    | inst {rn : RuleId} {θ : Subst} {ws : List Template}
        {D : List (QuestionId × AnswerTemplate)} {H : List QuestionId} {α : Assurance}
        {r : Rule} {As Cs DCs : List Atom} {Os DOs : List (List QuestionId)} {C : Atom}
        (hmeta : InstMeta canon Pi CertOk rn θ r ws.length (D.map Prod.fst)
          H α As Cs Os DCs DOs C)
        (hprems : ∀ (i : Nat) (t : Template) (A : Atom) (O : List QuestionId), ws[i]? = some t → Cs[i]? = some A → Os[i]? = some O →
          HasTemplate canon Pi Γ CertOk Δ t A O)
        (hdis : ∀ (j : Nat) (q : QuestionId) (a : AnswerTemplate) (A : Atom) (O : List QuestionId), D[j]? = some (q, a) → DCs[j]? = some A → DOs[j]? = some O →
          HasAnswer canon Pi Γ CertOk Δ a A O) :
        HasTemplate canon Pi Γ CertOk Δ (.inst rn θ ws D H α) C
          (collectObligations Os DOs r H)
  inductive HasAnswer (canon : String → String) (Pi : RuleId → Option Rule)
      (Γ : LeafId → Option Atom)
      (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop)
      (Δ : HoleSignature) : AnswerTemplate → Atom → List QuestionId → Prop where
    | term {t : Template} {C : Atom} {O : List QuestionId} (h : HasTemplate canon Pi Γ CertOk Δ t C O) :
        HasAnswer canon Pi Γ CertOk Δ (.term t) C O
    | hole {id A} (h : Δ id = some A) :
        HasAnswer canon Pi Γ CertOk Δ (.hole id) A []
end

/-- Fillings independently derive complete support of the demanded answer,
up to precisely the equivalence used by the existing discharge rule. -/
def FillingTyped (canon : String → String) (Pi : RuleId → Option Rule)
    (Γ : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop)
    (Δ : HoleSignature) (ρ : Filling) : Prop :=
  ∀ id A, Δ id = some A → ∃ w C, lookupFilling ρ id = some w ∧
    HasSupport canon Pi Γ CertOk w C [] ∧ equiv canon C A


/-- Assemble independently instantiated premises without choosing a checker result. -/
theorem instantiateList_supported {ρ : Filling} {ts : List Template}
    {Cs : List Atom} {Os : List (List QuestionId)}
    (hC : Cs.length = ts.length) (hO : Os.length = ts.length)
    (h : ∀ (i : Nat) t A O, ts[i]? = some t → Cs[i]? = some A → Os[i]? = some O →
      ∃ w, instantiateAux ρ t = .ok w ∧ HasSupport canon Pi Γ CertOk w A O) :
    ∃ ws, instantiateList ρ ts = .ok ws ∧ ws.length = ts.length ∧
      ∀ (i : Nat) w A O, ws[i]? = some w → Cs[i]? = some A → Os[i]? = some O →
        HasSupport canon Pi Γ CertOk w A O := by
  induction ts generalizing Cs Os with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons t ts ih =>
    cases Cs with
    | nil => simp at hC
    | cons A Cs =>
      cases Os with
      | nil => simp at hO
      | cons O Os =>
        obtain ⟨w, hw, hs⟩ := h 0 t A O (by simp) (by simp) (by simp)
        obtain ⟨ws, hws, hlen, hsup⟩ := ih (by simpa using hC) (by simpa using hO)
          (fun i t A O ht hA hO => h (i+1) t A O (by simpa using ht)
            (by simpa using hA) (by simpa using hO))
        refine ⟨w :: ws, by simp only [instantiateList, hw, hws]; rfl, by simp [hlen], ?_⟩
        intro i w' A' O' hi hA hO
        cases i with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi hA hO
                  cases hi; cases hA; cases hO; exact hs
        | succ i =>
          exact hsup i w' A' O' (by simpa using hi)
            (by simpa using hA) (by simpa using hO)

/-- Answers may realize canonically equivalent atoms; retain their actual
conclusions when assembling the old support derivation. -/
theorem instantiateDis_supported {ρ : Filling} {ds : List (QuestionId × AnswerTemplate)}
    {Cs : List Atom} {Os : List (List QuestionId)}
    (hC : Cs.length = ds.length) (hO : Os.length = ds.length)
    (h : ∀ (i : Nat) q a A O, ds[i]? = some (q,a) → Cs[i]? = some A → Os[i]? = some O →
      ∃ w B, instantiateAnswer ρ a = .ok w ∧
        HasSupport canon Pi Γ CertOk w B O ∧ equiv canon B A) :
    ∃ (D : List (QuestionId × SupportTerm)) (Bs : List Atom), instantiateDis ρ ds = .ok D ∧ D.map Prod.fst = ds.map Prod.fst ∧
      Bs.length = Cs.length ∧
      (∀ (i : Nat) w q B O, D[i]? = some (q,w) → Bs[i]? = some B → Os[i]? = some O →
        HasSupport canon Pi Γ CertOk w B O) ∧
      (∀ (i : Nat) B A, Bs[i]? = some B → Cs[i]? = some A → equiv canon B A) := by
  induction ds generalizing Cs Os with
  | nil =>
    have hc : Cs = [] := List.eq_nil_of_length_eq_zero hC
    subst Cs
    exact ⟨[], [], rfl, rfl, rfl, by simp, by simp⟩
  | cons p ds ih =>
    rcases p with ⟨q,a⟩
    cases Cs with
    | nil => simp at hC
    | cons A Cs =>
      cases Os with
      | nil => simp at hO
      | cons O Os =>
        obtain ⟨w, B, hw, hs, he⟩ := h 0 q a A O (by simp) (by simp) (by simp)
        obtain ⟨D, Bs, hD, hkeys, hlen, hsup, heq⟩ :=
          ih (by simpa using hC) (by simpa using hO)
            (fun i q a A O hd hA hO => h (i+1) q a A O (by simpa using hd)
              (by simpa using hA) (by simpa using hO))
        refine ⟨(q,w) :: D, B :: Bs, by simp only [instantiateDis, hw, hD]; rfl,
          by simp [hkeys], by simp [hlen], ?_, ?_⟩
        · intro i w' q' B' O' hi hB hO
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi hB hO
            rcases hi with ⟨rfl,rfl⟩; cases hB; cases hO; exact hs
          | succ i =>
            exact hsup i w' q' B' O' (by simpa using hi)
              (by simpa using hB) (by simpa using hO)
        · intro i B' A' hB hA
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hB hA
            cases hB; cases hA; exact he
          | succ i => exact heq i B' A' (by simpa using hB) (by simpa using hA)


theorem instantiateAux_hasSupport {Δ : HoleSignature} {ρ : Filling}
      {t : Template} {C : Atom} {O : List QuestionId}
      (h : HasTemplate canon Pi Γ CertOk Δ t C O)
      (hρ : FillingTyped canon Pi Γ CertOk Δ ρ) :
      ∃ w, instantiateAux ρ t = .ok w ∧ HasSupport canon Pi Γ CertOk w C O := by
    induction h using HasTemplate.rec (motive_2 := fun a C O _ =>
      ∃ w B, instantiateAnswer ρ a = .ok w ∧
        HasSupport canon Pi Γ CertOk w B O ∧ equiv canon B C) with
    | core h => exact ⟨_, rfl, h⟩
    | @inst rn θ ws D H α r As Cs DCs Os DOs C hm hp hd ihp ihd =>
      obtain ⟨ws', hws', hlen, hps⟩ := instantiateList_supported hm.lenCs hm.lenOs
        (fun i t A O ht hA hO => ihp i t A O ht hA hO)
      obtain ⟨D', Bs, hD', hkeys, hBlen, hds, heq⟩ :=
        instantiateDis_supported (by simpa using hm.lenDCs) (by simpa using hm.lenDOs)
          (fun i q a A O ha hA hO => ihd i q a A O ha hA hO)
      have hm' := hm.answers_equiv hBlen heq
      have hm'' : InstMeta canon Pi CertOk rn θ r ws'.length (D'.map Prod.fst)
          H α As Cs Os Bs DOs C := by rw [hlen, hkeys]; exact hm'
      refine ⟨.inst rn θ ws' D' H α, ?_, .inst hm''.toInstSide hps ?_⟩
      · simp only [instantiateAux, hws', hD']; rfl
      · intro j q w A O hj hA hO
        exact hds j w q A O hj hA hO
    | term h ih =>
      obtain ⟨w, hw, hs⟩ := ih
      exact ⟨w, _, hw, hs, equiv_refl canon _⟩
    | hole hA =>
      obtain ⟨w, B, hw, hs, he⟩ := hρ _ _ hA
      exact ⟨w, B, by simp [instantiateAnswer, hw], hs, he⟩

  theorem instantiateAnswer_hasSupport {Δ : HoleSignature} {ρ : Filling}
      {a : AnswerTemplate} {C : Atom} {O : List QuestionId}
      (h : HasAnswer canon Pi Γ CertOk Δ a C O)
      (hρ : FillingTyped canon Pi Γ CertOk Δ ρ) :
      ∃ w B, instantiateAnswer ρ a = .ok w ∧
        HasSupport canon Pi Γ CertOk w B O ∧ equiv canon B C := by
    cases h with
    | term h =>
      obtain ⟨w, hw, hs⟩ := instantiateAux_hasSupport h hρ
      exact ⟨w, _, hw, hs, equiv_refl canon _⟩
    | hole hA =>
      obtain ⟨w, B, hw, hs, he⟩ := hρ _ _ hA
      exact ⟨w, B, by simp [instantiateAnswer, hw], hs, he⟩

/-- Typed substitution: recursive source typing and independently typed
fillings construct the core derivation, preserving its conclusion and residual
obligations. In particular an abstractly complete template becomes complete. -/
theorem instantiate_hasSupport {Δ : HoleSignature} {ρ : Filling}
    {t : Template} {C : Atom} {O : List QuestionId}
    (h : HasTemplate canon Pi Γ CertOk Δ t C O)
    (hρ : FillingTyped canon Pi Γ CertOk Δ ρ) (hn : FillingNodup ρ) :
    ∃ w, instantiate ρ t = .ok w ∧ HasSupport canon Pi Γ CertOk w C O := by
  rw [instantiate_eq_aux hn]
  exact instantiateAux_hasSupport h hρ


theorem eraseList_length (ts : List Template) : (eraseList ts).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [eraseList, ih]

/-- Erasure moves each named slot from the discharge side to the open side
of the same CQ partition, without losing or duplicating a question key. -/
theorem eraseDis_keys_perm (D : List (QuestionId × AnswerTemplate)) :
    ((eraseDis D).map Prod.fst ++ holeKeys D).Perm (D.map Prod.fst) := by
  induction D with
  | nil => exact .refl _
  | cons p rest ih =>
    rcases p with ⟨q,a⟩
    cases a with
    | term t => simpa [eraseDis, holeKeys] using ih.cons q
    | hole id =>
      simp only [eraseDis, holeKeys, List.map_cons]
      exact List.perm_middle.trans (ih.cons q)

theorem eraseDis_keys_mem (D : List (QuestionId × AnswerTemplate)) (q : QuestionId) :
    q ∈ D.map Prod.fst ↔ q ∈ (eraseDis D).map Prod.fst ∨ q ∈ holeKeys D := by
  simpa using (eraseDis_keys_perm D).mem_iff.symm

theorem eraseList_supported {ts : List Template} {Cs : List Atom}
    (hC : Cs.length = ts.length)
    (h : ∀ (i : Nat) t A, ts[i]? = some t → Cs[i]? = some A →
      ∃ O, HasSupport canon Pi Γ CertOk (eraseOpen t) A O) :
    ∃ Os : List (List QuestionId), Os.length = ts.length ∧
      ∀ (i : Nat) w A O, (eraseList ts)[i]? = some w → Cs[i]? = some A → Os[i]? = some O →
        HasSupport canon Pi Γ CertOk w A O := by
  induction ts generalizing Cs with
  | nil => exact ⟨[], rfl, by simp [eraseList]⟩
  | cons t ts ih =>
    cases Cs with
    | nil => simp at hC
    | cons A Cs =>
      obtain ⟨O, hs⟩ := h 0 t A (by simp) (by simp)
      obtain ⟨Os, hlen, ht⟩ := ih (by simpa using hC)
        (fun i t A ht hA => h (i+1) t A (by simpa using ht) (by simpa using hA))
      refine ⟨O :: Os, by simp [hlen], ?_⟩
      intro i w B P hi hB hP
      cases i with
      | zero =>
        simp only [eraseList, List.getElem?_cons_zero, Option.some.injEq] at hi hB hP
        cases hi; cases hB; cases hP; exact hs
      | succ i =>
        exact ht i w B P (by simpa [eraseList] using hi) (by simpa using hB) (by simpa using hP)

theorem eraseDis_supported {ds : List (QuestionId × AnswerTemplate)} {Cs : List Atom}
    (hC : Cs.length = ds.length)
    (h : ∀ (i : Nat) q t A, ds[i]? = some (q,.term t) → Cs[i]? = some A →
      ∃ O, HasSupport canon Pi Γ CertOk (eraseOpen t) A O) :
    ∃ (Bs : List Atom) (Os : List (List QuestionId)),
      Bs.length = (eraseDis ds).length ∧ Os.length = (eraseDis ds).length ∧
      (∀ (i : Nat) q w B O, (eraseDis ds)[i]? = some (q,w) → Bs[i]? = some B → Os[i]? = some O →
        HasSupport canon Pi Γ CertOk w B O) ∧
      (∀ (i : Nat) q w B, (eraseDis ds)[i]? = some (q,w) → Bs[i]? = some B →
        ∃ j : Nat, (ds.map Prod.fst)[j]? = some q ∧ Cs[j]? = some B) := by
  induction ds generalizing Cs with
  | nil => exact ⟨[], [], rfl, rfl, by simp [eraseDis], by simp [eraseDis]⟩
  | cons p ds ih =>
    rcases p with ⟨q,a⟩
    cases Cs with
    | nil => simp at hC
    | cons A Cs =>
      obtain ⟨Bs, Os, hBlen, hOlen, hsup, horigin⟩ := ih (by simpa using hC)
        (fun i q t A hd hA => h (i+1) q t A (by simpa using hd) (by simpa using hA))
      cases a with
      | hole id =>
        refine ⟨Bs, Os, hBlen, hOlen, hsup, ?_⟩
        intro i q' w B hd hB
        obtain ⟨j, hj, hCj⟩ := horigin i q' w B hd hB
        exact ⟨j+1, by simpa using hj, by simpa using hCj⟩
      | term t =>
        obtain ⟨O, hs⟩ := h 0 q t A (by simp) (by simp)
        refine ⟨A :: Bs, O :: Os, by simp [eraseDis, hBlen], by simp [eraseDis, hOlen], ?_, ?_⟩
        · intro i q' w B P hd hB hP
          cases i with
          | zero =>
            simp only [eraseDis, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hd hB hP
            rcases hd with ⟨rfl,rfl⟩; cases hB; cases hP; exact hs
          | succ i =>
            exact hsup i q' w B P (by simpa [eraseDis] using hd)
              (by simpa using hB) (by simpa using hP)
        · intro i q' w B hd hB
          cases i with
          | zero =>
            simp only [eraseDis, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hd hB
            rcases hd with ⟨rfl,rfl⟩; cases hB
            exact ⟨0, by simp, by simp⟩
          | succ i =>
            obtain ⟨j, hj, hCj⟩ := horigin i q' w B (by simpa [eraseDis] using hd) (by simpa using hB)
            exact ⟨j+1, by simpa using hj, by simpa using hCj⟩


/-- Reconstruct the original open rule after moving named answer slots into H. -/
theorem InstMeta.eraseOpen {ts : List Template} {ds : List (QuestionId × AnswerTemplate)}
    {Os' DOs' : List (List QuestionId)} {Bs : List Atom}
    (h : InstMeta canon Pi CertOk rn θ r ts.length (ds.map Prod.fst)
      H α As Cs Os DCs DOs C)
    (hOs : Os'.length = ts.length)
    (hBs : Bs.length = (eraseDis ds).length)
    (hDOs : DOs'.length = (eraseDis ds).length)
    (horigin : ∀ (i : Nat) q w B, (eraseDis ds)[i]? = some (q,w) → Bs[i]? = some B →
      ∃ j : Nat, (ds.map Prod.fst)[j]? = some q ∧ DCs[j]? = some B) :
    InstSide canon Pi CertOk rn θ r (eraseList ts) (eraseDis ds) (H ++ holeKeys ds)
      α As Cs Os' Bs DOs' C := by
  have hpart := eraseDis_keys_mem ds
  have hn := (eraseDis_keys_perm ds).nodup_iff.mpr h.dNodup
  obtain ⟨hnd, hnh, hcross⟩ := List.nodup_append.mp hn
  have hdisOld : ∀ q, q ∈ (eraseDis ds).map Prod.fst → q ∈ ds.map Prod.fst :=
    fun q hq => (hpart q).mpr (.inl hq)
  have hholeOld : ∀ q, q ∈ holeKeys ds → q ∈ ds.map Prod.fst :=
    fun q hq => (hpart q).mpr (.inr hq)
  exact {
    rule := h.rule
    θNodup := h.θNodup
    θDom := h.θDom
    prems := h.prems
    concl := h.concl
    lenAs := by simpa [eraseList_length] using h.lenAs
    lenCs := by simpa [eraseList_length] using h.lenCs
    lenOs := by simpa [eraseList_length] using hOs
    premEq := h.premEq
    lenDCs := hBs
    lenDOs := hDOs
    ans := by
      intro i q w B hi hB
      obtain ⟨j, hj, hBj⟩ := horigin i q w B hi hB
      exact h.ans j q B hj hBj
    qNodup := h.qNodup
    dNodup := hnd
    hNodup := List.nodup_append.mpr ⟨h.hNodup, hnh, by
      intro a ha b hb hab
      subst b
      exact h.disj a (hholeOld a hb) ha⟩
    cover := by
      intro qd hqd
      rcases h.cover qd hqd with hd | hh
      · rcases (hpart qd.name).mp hd with hd | hh
        · exact .inl hd
        · exact .inr (List.mem_append_right _ hh)
      · exact .inr (List.mem_append_left _ hh)
    disj := by
      intro n hd hh
      rcases List.mem_append.mp hh with hh | hh
      · exact h.disj n (hdisOld n hd) hh
      · exact hcross n hd n hh rfl
    keysD := fun n hn => h.keysD n (hdisOld n hn)
    keysH := by
      intro n hn
      rcases List.mem_append.mp hn with hn | hn
      · exact h.keysH n hn
      · exact h.keysD n (hholeOld n hn)
    strictNoQ := by
      intro hm
      obtain ⟨hd, hh⟩ := h.strictNoQ hm
      have hds : ds = [] := List.map_eq_nil_iff.mp hd
      simp [hds, hh, eraseDis, holeKeys]
    assur := h.assur }

/-- An independently typed template already denotes a genuinely typed open
source term. Named answers become ordinary H entries before any context is
supplied; the returned obligations are those of that original judgment. -/
theorem eraseOpen_hasSupport {Δ : HoleSignature} {t : Template} {C : Atom} {O : List QuestionId}
    (h : HasTemplate canon Pi Γ CertOk Δ t C O) :
    ∃ Oopen, HasSupport canon Pi Γ CertOk (eraseOpen t) C Oopen := by
  induction h using HasTemplate.rec
      (motive_2 := fun a C _ _ => ∀ t, a = .term t →
        ∃ Oopen, HasSupport canon Pi Γ CertOk (eraseOpen t) C Oopen) with
  | core h => exact ⟨_, h⟩
  | @inst rn θ ws D H α r As Cs DCs Os DOs C hm hp hd ihp ihd =>
    obtain ⟨Os', hOs', hps⟩ := eraseList_supported hm.lenCs (by
      intro i t A ht hA
      obtain ⟨O, hO⟩ := getElem?_some_of_lt Os i
        (by have := lt_of_getElem?_some ht; have := hm.lenOs; omega)
      exact ihp i t A O ht hA hO)
    obtain ⟨Bs, DOs', hBs, hDOs', hds, horigin⟩ :=
      eraseDis_supported (by simpa using hm.lenDCs) (by
        intro i q t A ht hA
        obtain ⟨O, hO⟩ := getElem?_some_of_lt DOs i
          (by have := lt_of_getElem?_some ht; have := hm.lenDOs; simp only [List.length_map] at *; omega)
        exact ihd i q (.term t) A O ht hA hO t rfl)
    exact ⟨_, .inst (hm.eraseOpen hOs' hBs hDOs' horigin) hps hds⟩
  | term h ih t ht => cases ht; exact ih
  | hole h t ht => cases ht

end Lara.Context.Holes
