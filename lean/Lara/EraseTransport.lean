/-
# Result 9 — backend replacement: well-checkedness transport

Strengthens `Lara.Erase` (Theorem 2, Model A) by proving that a uniform
injective certificate relabel `mapAssur f` *preserves well-checkedness*: it
maps a `CheckedProgram` over one backend acceptance predicate to a
`CheckedProgram` over another, given only that the relabel preserves the
`AssuranceOk` acceptance side condition (`hpres`) — the formal content of
Theorem 2's "accept the same strict instances" hypothesis.

This makes `Erase.backend_replacement` non-vacuous **by construction**:
`mapCertProg` exhibits a genuine second `CheckedProgram` (over `CertOk₂`) whose
every claim status agrees with the first, rather than assuming such a program
exists. It is a purely additive, Lean-only result.

The transport is a structural induction over `HasSupport`/`HasAttack`: the
certificate payload enters typing only through the `AssuranceOk` premise, so
every other side condition (conclusions, obligations, positions, discharge
keys, lengths) is preserved verbatim, and `hpres` discharges the one premise
that moves.
-/

import Lara.Erase

namespace Lara.Erase

open Lara.Support Lara.Attack Lara.Compile Lara.Grounded

section Transport
variable {f : Assurance → Assurance}

/-! ### Discharge-map plumbing (re-exported / re-added helpers) -/

/-- The discharge helper maps values, keeping keys. -/
theorem mapAssurDis_eq (D : List (QuestionId × SupportTerm)) :
    mapAssurDis f D = D.map (fun p => (p.1, mapAssur f p.2)) := by
  induction D with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨q, w⟩ := p
    simp only [mapAssurDis, List.map_cons, ih]

/-- Relabel keeps the attack's target term (its `mapAssur f` image). -/
theorem mapAssurAtt_target (k : Attack) :
    (mapAssurAtt f k).target = mapAssur f k.target := by
  cases k <;> rfl

theorem mapAssurList_length (ws : List SupportTerm) :
    (mapAssurList f ws).length = ws.length := by
  rw [mapAssurList_eq, List.length_map]

theorem mapAssurDis_length (D : List (QuestionId × SupportTerm)) :
    (mapAssurDis f D).length = D.length := by
  rw [mapAssurDis_eq, List.length_map]

/-- Relabel preserves discharge keys. -/
theorem mapAssurDis_keys (D : List (QuestionId × SupportTerm)) :
    (mapAssurDis f D).map Prod.fst = D.map Prod.fst := by
  rw [mapAssurDis_eq, List.map_map]; rfl

/-- Decompose a hit in a relabeled premise list. -/
theorem mapAssurList_getElem?_some {ws : List SupportTerm} {i : Nat}
    {w' : SupportTerm} (h : (mapAssurList f ws)[i]? = some w') :
    ∃ w₀, ws[i]? = some w₀ ∧ w' = mapAssur f w₀ := by
  rw [mapAssurList_eq, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨w₀, hw, hw'⟩ := h
  exact ⟨w₀, hw, hw'.symm⟩

/-- Decompose a hit in a relabeled discharge list (keys preserved). -/
theorem mapAssurDis_getElem?_some {D : List (QuestionId × SupportTerm)} {j : Nat}
    {q : QuestionId} {w' : SupportTerm}
    (h : (mapAssurDis f D)[j]? = some (q, w')) :
    ∃ w₀, D[j]? = some (q, w₀) ∧ w' = mapAssur f w₀ := by
  rw [mapAssurDis_eq, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨⟨q₀, w₀⟩, hD, hqw⟩ := h
  simp only [Prod.mk.injEq] at hqw
  obtain ⟨hq, hw'⟩ := hqw
  subst hq
  exact ⟨w₀, hD, hw'.symm⟩

/-! ### Typing transport -/

variable {canon : String → String} {Pi : RuleId → Option Rule}
  {Gamma : LeafId → Option Atom}
  {CertOk₁ CertOk₂ : BackendId → Digest → CertRef → List Atom → Atom → Prop}
  {dp : DefeatPolicy}

/-- **`HasSupport` transports along a uniform relabel** given acceptance
preservation. The conclusion `C` and obligation set `O` are unchanged — the
certificate payload never enters them. -/
theorem hasSupport_mapAssur
    (hpres : ∀ (r : Rule) (As : List Atom) (C : Atom) (α : Assurance),
      AssuranceOk CertOk₁ r As C α → AssuranceOk CertOk₂ r As C (f α)) :
    ∀ {w : SupportTerm} {C : Atom} {O : List QuestionId},
      HasSupport canon Pi Gamma CertOk₁ w C O →
      HasSupport canon Pi Gamma CertOk₂ (mapAssur f w) C O := by
  intro w C O h
  induction h with
  | leaf hΓ => exact .leaf hΓ
  | @inst rn θ ws D H α r As Cs Os DCs DOs C hside hprems hdis ihprems ihdis =>
    have hside' : InstSide canon Pi CertOk₂ rn θ r
        (mapAssurList f ws) (mapAssurDis f D) H (f α) As Cs Os DCs DOs C :=
      { rule := hside.rule
        θNodup := hside.θNodup
        θDom := hside.θDom
        prems := hside.prems
        concl := hside.concl
        lenAs := by rw [mapAssurList_length]; exact hside.lenAs
        lenCs := by rw [mapAssurList_length]; exact hside.lenCs
        lenOs := by rw [mapAssurList_length]; exact hside.lenOs
        premEq := hside.premEq
        lenDCs := by rw [mapAssurDis_length]; exact hside.lenDCs
        lenDOs := by rw [mapAssurDis_length]; exact hside.lenDOs
        ans := by
          intro j q w' A hj hA
          obtain ⟨w₀, hD, _⟩ := mapAssurDis_getElem?_some hj
          exact hside.ans j q w₀ A hD hA
        qNodup := hside.qNodup
        dNodup := by rw [mapAssurDis_keys]; exact hside.dNodup
        hNodup := hside.hNodup
        cover := by
          intro qd hqd; rw [mapAssurDis_keys]; exact hside.cover qd hqd
        disj := by
          intro n hn; rw [mapAssurDis_keys] at hn; exact hside.disj n hn
        keysD := by
          intro n hn; rw [mapAssurDis_keys] at hn; exact hside.keysD n hn
        keysH := hside.keysH
        strictNoQ := by
          intro hstrict
          obtain ⟨hDnil, hHnil⟩ := hside.strictNoQ hstrict
          exact ⟨by rw [hDnil]; rfl, hHnil⟩
        assur := hpres r As C α hside.assur }
    refine HasSupport.inst hside' ?_ ?_
    · intro i w' A O hi hA hO
      obtain ⟨w₀, hw, hw'⟩ := mapAssurList_getElem?_some hi
      rw [hw']; exact ihprems i w₀ A O hw hA hO
    · intro j q w' A O hj hA hO
      obtain ⟨w₀, hD, hw'⟩ := mapAssurDis_getElem?_some hj
      rw [hw']; exact ihdis j q w₀ A O hD hA hO

/-- **`HasAttack` transports along a uniform relabel.** Each attack's source
typing transports by `hasSupport_mapAssur`; the target occurrence tracks
`mapAssur_subterm`; every occurrence-local `Pi`/`Gamma`/pattern premise is
assurance-independent. -/
theorem hasAttack_mapAssur
    (hpres : ∀ (r : Rule) (As : List Atom) (C : Atom) (α : Assurance),
      AssuranceOk CertOk₁ r As C α → AssuranceOk CertOk₂ r As C (f α))
    {k : Attack} (hk : HasAttack canon Pi Gamma CertOk₁ dp k) :
    HasAttack canon Pi Gamma CertOk₂ dp (mapAssurAtt f k) := by
  cases hk with
  | rebut hw hrule hdef hconcl hcon =>
    simp only [mapAssurAtt, mapAssur]
    exact .rebut (hasSupport_mapAssur hpres hw) hrule hdef hconcl hcon
  | undercut hw hocc hrule hdef hexc hinst heq =>
    simp only [mapAssurAtt]
    exact .undercut (hasSupport_mapAssur hpres hw)
      (by rw [mapAssur_subterm, hocc]; rfl) hrule hdef hexc hinst heq
  | undermine hw hocc hl hcon =>
    simp only [mapAssurAtt]
    exact .undermine (hasSupport_mapAssur hpres hw)
      (by rw [mapAssur_subterm, hocc]; rfl) hl hcon

/-! ### CheckedProgram transport and constructive non-vacuity -/

/-- **A uniform injective relabel maps a `CheckedProgram` to a `CheckedProgram`**
over the second backend, given acceptance preservation. The witness that
`Erase.backend_replacement`'s hypotheses are satisfiable for any well-checked
program. -/
def mapCertProg (P₁ : CheckedProgram canon Pi Gamma CertOk₁ dp)
    (hf : Function.Injective f)
    (hpres : ∀ (r : Rule) (As : List Atom) (C : Atom) (α : Assurance),
      AssuranceOk CertOk₁ r As C α → AssuranceOk CertOk₂ r As C (f α)) :
    CheckedProgram canon Pi Gamma CertOk₂ dp where
  args := P₁.args.map (mapAssur f)
  nodup := P₁.nodup.map (mapAssur f)
    (fun _ _ hab habeq => hab (mapAssur_injective hf habeq))
  complete := by
    intro w' hw'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
    obtain ⟨C, hC⟩ := P₁.complete w hw
    exact ⟨C, hasSupport_mapAssur hpres hC⟩
  atts := P₁.atts.map (mapAssurAtt f)
  typed := by
    intro k' hk'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hk'
    exact hasAttack_mapAssur hpres (P₁.typed k hk)
  source_declared := by
    intro k' hk'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hk'
    rw [mapAssurAtt_source]
    exact List.mem_map.mpr ⟨k.source, P₁.source_declared k hk, rfl⟩
  target_declared := by
    intro k' hk'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hk'
    rw [mapAssurAtt_target]
    exact List.mem_map.mpr ⟨k.target, P₁.target_declared k hk, rfl⟩

@[simp] theorem mapCertProg_args (P₁ : CheckedProgram canon Pi Gamma CertOk₁ dp)
    (hf : Function.Injective f)
    (hpres : ∀ (r : Rule) (As : List Atom) (C : Atom) (α : Assurance),
      AssuranceOk CertOk₁ r As C α → AssuranceOk CertOk₂ r As C (f α)) :
    (mapCertProg P₁ hf hpres).args = P₁.args.map (mapAssur f) := rfl

@[simp] theorem mapCertProg_atts (P₁ : CheckedProgram canon Pi Gamma CertOk₁ dp)
    (hf : Function.Injective f)
    (hpres : ∀ (r : Rule) (As : List Atom) (C : Atom) (α : Assurance),
      AssuranceOk CertOk₁ r As C α → AssuranceOk CertOk₂ r As C (f α)) :
    (mapCertProg P₁ hf hpres).atts = P₁.atts.map (mapAssurAtt f) := rfl

/-- **Backend replacement, non-vacuous by construction.** For any well-checked
program `P₁` and any injective, acceptance-preserving relabel `f`, the relabeled
program `mapCertProg P₁ …` is a genuine `CheckedProgram` over the second backend
and every claim gets the same four-state status. -/
theorem backend_replacement_transport
    (P₁ : CheckedProgram canon Pi Gamma CertOk₁ dp)
    (hf : Function.Injective f)
    (hpres : ∀ (r : Rule) (As : List Atom) (C : Atom) (α : Assurance),
      AssuranceOk CertOk₁ r As C α → AssuranceOk CertOk₂ r As C (f α))
    (c : Claim) :
    statusC (checkedAF P₁) c
      = statusC (checkedAF (mapCertProg P₁ hf hpres)) c :=
  backend_replacement hf (mapCertProg_args P₁ hf hpres).symm
    (mapCertProg_atts P₁ hf hpres).symm c

end Transport

end Lara.Erase
