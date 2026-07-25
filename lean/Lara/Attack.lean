/-
Mechanized typed positional attacks (`Lara.Attack`) — the Lean port of the
v0.1-frozen attack judgment `Sigma; Pi; Gamma; R |- k : attacks(w, u@π)`
(spec §7.1, frozen in the M1 lock pass). Ports the figure the moment it froze,
per the mechanization discipline (CLAUDE.md).

What this file discharges, against the exact §7.1 figure:

* `attack_source_checked` — every typed attack has a checked source (§1
  guarantee 4, the "checked, not complete" design point: no `O_w = ∅`
  requirement here; completeness gates AF entry at compile time).
* `rebut_top_defeasible`, `undercut_pos_defeasible` — **strict occurrences are
  unattackable**: the rule at a rebutted root or an undercut position is
  defeasible. §7's load-bearing property, now an inversion theorem.
* `undercut_target_rule`, `undermine_target_leaf` — the position-kind
  partition: an undercut lands on a rule occurrence, an undermine on a leaf
  occurrence (rebut's root shape is carried in its index).
* `rebut_concl_coherent` — the locality design point: [A-Rebut] reads the
  target conclusion off the root instance without typing `u`; if `u` *is*
  typed, the contrary match is against its typed conclusion. Uses
  `hasSupport_unique`-style inversion, so local checking and global typing
  agree.

`Lara.Check.Attack` now supplies the executable attack decision procedure and
exact adequacy for result 1. Compile-facing edge soundness is discharged by
the relational compile layer (`Lara.Compile`, result 4); only construction of
the general executable closure-edge oracle remains.

Design notes:

* Positions are element lists consumed left-to-right; the spec's `π.i`/`π.q`
  right-extension is the same data read from the root. Premise indices are
  0-based here (`ws[i]?`), 1-based in the presentation syntax.
* The defeat-relevant policy content (`contrary` pairs, `exception`
  declarations, spec §4) rides in a `DefeatPolicy` alongside the rule lookup
  `Pi` — parameters carry exactly what the metatheory needs (the
  `Lara.Strict` convention).
* `ContraryMatch` is §4.1's implicitly-universally-quantified `contrary`
  declaration: one ground `rho` instantiates a declared pair to the two ground
  propositions, up to `≡` (§3.2).
-/

import Lara.Support

namespace Lara.Attack

open Lara.Support

/-! ### Positions (spec §7: `π ::= ε | π.i | π.q`) -/

inductive PosElem where
  | prem : Nat → PosElem
  | ques : QuestionId → PosElem
deriving DecidableEq

abbrev Pos := List PosElem

def lookupDis : List (QuestionId × SupportTerm) → QuestionId → Option SupportTerm
  | [], _ => none
  | (q', w) :: rest, q => if q' = q then some w else lookupDis rest q

/-- `u@π`: the subterm occurrence at `π`, partial (spec §7.1). -/
def subterm : SupportTerm → Pos → Option SupportTerm
  | u, [] => some u
  | .leaf _, _ :: _ => none
  | .inst _ _ ws _ _ _, .prem i :: π =>
    match ws[i]? with
    | some w => subterm w π
    | none => none
  | .inst _ _ _ D _ _, .ques q :: π =>
    match lookupDis D q with
    | some w => subterm w π
    | none => none

/-! ### Defeat-relevant policy content (spec §4) -/

/-- The `contrary`/`exception` declarations of the selected policy.
`exceptions` entries are keyed by rule id (`exception r : E`). -/
structure DefeatPolicy where
  contraries : List (APat × APat)
  exceptions : List (RuleId × APat)

/-- §4.1 contrary instantiation: some declared `contrary A B` and one ground
`rho` have `A rho ≡ p` and `B rho ≡ q`. -/
def ContraryMatch (canon : String → String) (dp : DefeatPolicy)
    (p q : Atom) : Prop :=
  ∃ ab ∈ dp.contraries, ∃ (ρ : Subst) (pa pb : Atom),
    instAPat ρ ab.1 = some pa ∧ instAPat ρ ab.2 = some pb ∧
    equiv canon pa p ∧ equiv canon pb q

/-! ### Exact executable contrary matching

Bindings retain the ground term as it occurred in the proposition.  The
canonicalizer is applied only at an equality boundary (a literal or a repeated
variable), once to each side.  In particular no idempotence property of
`canon` is needed. -/

mutual
  def matchPat (canon : String → String) (ρ : Subst) :
      Pat → Term → Option Subst
    | .var x, t =>
        match lookupSubst ρ x with
        | none => some ((x, t) :: ρ)
        | some u =>
            if nfTerm canon u = nfTerm canon t then some ρ else none
    | .num s, t =>
        if nfTerm canon (.num s) = nfTerm canon t then some ρ else none
    | .str s, t =>
        if nfTerm canon (.str s) = nfTerm canon t then some ρ else none
    | .con k ps, .con k' ts =>
        if k.name = k' then matchPats canon ρ ps ts else none
    | .con _ _, _ => none

  def matchPats (canon : String → String) (ρ : Subst) :
      Pats → Terms → Option Subst
    | .nil, .nil => some ρ
    | .cons p ps, .cons t ts =>
        match matchPat canon ρ p t with
        | none => none
        | some ρ' => matchPats canon ρ' ps ts
    | _, _ => none
end

def matchAPat (canon : String → String) (ρ : Subst)
    (ap : APat) (a : Atom) : Option Subst :=
  match a with
  | .atom pred args =>
      if ap.pred.name = pred then matchPats canon ρ ap.args args else none

def contraryMatchDecl (canon : String → String) (p q : Atom)
    (ab : APat × APat) : Bool :=
  match matchAPat canon [] ab.1 p with
  | none => false
  | some ρ =>
      match matchAPat canon ρ ab.2 q with
      | none => false
      | some _ => true

def contraryMatchB (canon : String → String) (dp : DefeatPolicy)
    (p q : Atom) : Bool :=
  dp.contraries.any (contraryMatchDecl canon p q)

def SubstExtends (ρ ρ' : Subst) : Prop :=
  ∀ x t, lookupSubst ρ x = some t → lookupSubst ρ' x = some t

def SubstCanonAgrees (canon : String → String) (ρ ρ₀ : Subst) : Prop :=
  ∀ x t, lookupSubst ρ x = some t →
    ∃ t₀, lookupSubst ρ₀ x = some t₀ ∧
      nfTerm canon t = nfTerm canon t₀

theorem SubstExtends.refl (ρ : Subst) : SubstExtends ρ ρ :=
  fun _ _ h => h

theorem SubstExtends.trans {ρ₁ ρ₂ ρ₃ : Subst}
    (h₁₂ : SubstExtends ρ₁ ρ₂) (h₂₃ : SubstExtends ρ₂ ρ₃) :
    SubstExtends ρ₁ ρ₃ :=
  fun x t h => h₂₃ x t (h₁₂ x t h)

mutual
  theorem instPat_of_extends {ρ ρ' : Subst} (hext : SubstExtends ρ ρ') :
      ∀ {p : Pat} {t : Term}, instPat ρ p = some t →
        instPat ρ' p = some t := by
    intro p t h
    cases p with
    | var x => exact hext x t h
    | num s => simpa [instPat] using h
    | str s => simpa [instPat] using h
    | con k ps =>
        simp only [instPat] at h ⊢
        cases hs : instPats ρ ps with
        | none => simp [hs] at h
        | some ts =>
            have hi := instPats_of_extends hext hs
            simp [hs] at h
            subst t
            simp [hi]

  theorem instPats_of_extends {ρ ρ' : Subst} (hext : SubstExtends ρ ρ') :
      ∀ {ps : Pats} {ts : Terms}, instPats ρ ps = some ts →
        instPats ρ' ps = some ts := by
    intro ps ts h
    cases ps with
    | nil => simpa [instPats] using h
    | cons p ps =>
        simp only [instPats] at h ⊢
        cases hp : instPat ρ p with
        | none => simp [hp] at h
        | some t =>
            cases hps : instPats ρ ps with
            | none => simp [hp, hps] at h
            | some us =>
                simp [hp, hps] at h
                subst ts
                simp [instPat_of_extends hext hp,
                  instPats_of_extends hext hps]
end

theorem instAPat_of_extends {ρ ρ' : Subst} (hext : SubstExtends ρ ρ')
    {ap : APat} {a : Atom} (h : instAPat ρ ap = some a) :
    instAPat ρ' ap = some a := by
  cases ap with
  | mk pred args =>
      cases a with
      | atom p ts =>
          simp only [instAPat] at h ⊢
          cases hi : instPats ρ args with
          | none => simp [hi] at h
          | some us =>
              simp [hi] at h
              rcases h with ⟨hp, hts⟩
              subst p
              subst ts
              simp [instPats_of_extends hext hi]

mutual
  theorem matchPat_sound (canon : String → String) (ρ : Subst)
      (p : Pat) (t : Term) (ρ' : Subst)
      (h : matchPat canon ρ p t = some ρ') :
      SubstExtends ρ ρ' ∧
        ∃ u, instPat ρ' p = some u ∧
          nfTerm canon u = nfTerm canon t := by
    cases p with
    | var x =>
        simp only [matchPat] at h
        cases hx : lookupSubst ρ x with
        | none =>
            simp [hx] at h
            subst ρ'
            refine ⟨?_, t, ?_, rfl⟩
            · intro y v hyv
              simp only [lookupSubst]
              split
              · rename_i hyx
                subst y
                rw [hx] at hyv
                contradiction
              · exact hyv
            · simp [instPat, lookupSubst]
        | some u =>
            simp [hx] at h
            rcases h with ⟨heq, hrho⟩
            subst ρ'
            exact ⟨SubstExtends.refl ρ, u, by simp [instPat, hx], heq⟩
    | num s =>
        simp only [matchPat] at h
        split at h
        · rename_i heq
          have := Option.some.inj h
          subst ρ'
          exact ⟨SubstExtends.refl ρ, .num s, rfl, heq⟩
        · contradiction
    | str s =>
        simp only [matchPat] at h
        split at h
        · rename_i heq
          have := Option.some.inj h
          subst ρ'
          exact ⟨SubstExtends.refl ρ, .str s, rfl, heq⟩
        · contradiction
    | con k ps =>
        cases t with
        | num s => simp [matchPat] at h
        | str s => simp [matchPat] at h
        | con k' ts =>
            simp only [matchPat] at h
            split at h
            · rename_i hk
              have hs := matchPats_sound canon ρ ps ts ρ' h
              rcases hs with ⟨hext, us, hi, hnf⟩
              refine ⟨hext, .con k.name us, ?_, ?_⟩
              · simp [instPat, hi]
              · simp [nfTerm, hk, hnf]
            · contradiction

  theorem matchPats_sound (canon : String → String) (ρ : Subst)
      (ps : Pats) (ts : Terms) (ρ' : Subst)
      (h : matchPats canon ρ ps ts = some ρ') :
      SubstExtends ρ ρ' ∧
        ∃ us, instPats ρ' ps = some us ∧
          nfTerms canon us = nfTerms canon ts := by
    cases ps with
    | nil =>
        cases ts with
        | nil =>
            simp [matchPats] at h
            subst ρ'
            exact ⟨SubstExtends.refl ρ, .nil, rfl, rfl⟩
        | cons t ts => simp [matchPats] at h
    | cons p ps =>
        cases ts with
        | nil => simp [matchPats] at h
        | cons t ts =>
            simp only [matchPats] at h
            cases hm : matchPat canon ρ p t with
            | none => simp [hm] at h
            | some ρ₁ =>
                rw [hm] at h
                have hp := matchPat_sound canon ρ p t ρ₁ hm
                have hps := matchPats_sound canon ρ₁ ps ts ρ' h
                rcases hp with ⟨hext₁, u, hu, hnfu⟩
                rcases hps with ⟨hext₂, us, hus, hnfus⟩
                refine ⟨hext₁.trans hext₂, .cons u us, ?_, ?_⟩
                · have hu' : instPat ρ' p = some u :=
                    instPat_of_extends hext₂ hu
                  simp [instPats, hu', hus]
                · simp [nfTerms, hnfu, hnfus]
end

theorem matchAPat_sound (canon : String → String) (ρ : Subst)
    (ap : APat) (a : Atom) (ρ' : Subst)
    (h : matchAPat canon ρ ap a = some ρ') :
    SubstExtends ρ ρ' ∧
      ∃ a', instAPat ρ' ap = some a' ∧ equiv canon a' a := by
  cases a with
  | atom pred args =>
      simp only [matchAPat] at h
      split at h
      · rename_i hp
        rcases matchPats_sound canon ρ ap.args args ρ' h with
          ⟨hext, ts, hts, hnfts⟩
        exact ⟨hext, .atom ap.pred.name ts, by simp [instAPat, hts],
          by simp [equiv, nf, hp, hnfts]⟩
      · contradiction

mutual
  theorem matchPat_complete (canon : String → String) (ρ ρ₀ : Subst)
      (hagree : SubstCanonAgrees canon ρ ρ₀)
      (p : Pat) (t u : Term)
      (hinst : instPat ρ₀ p = some u)
      (hnf : nfTerm canon u = nfTerm canon t) :
      ∃ ρ', matchPat canon ρ p t = some ρ' ∧
        SubstCanonAgrees canon ρ' ρ₀ := by
    cases p with
    | var x =>
        simp only [instPat] at hinst
        cases hx : lookupSubst ρ x with
        | none =>
            refine ⟨(x, t) :: ρ, by simp [matchPat, hx], ?_⟩
            intro y v hyv
            simp only [lookupSubst] at hyv
            split at hyv
            · rename_i hyx
              subst y
              simp only [Option.some.injEq] at hyv
              subst v
              exact ⟨u, hinst, hnf.symm⟩
            · exact hagree y v hyv
        | some v =>
            rcases hagree x v hx with ⟨v₀, hv₀, hvnf⟩
            rw [hinst] at hv₀
            have hvu : v₀ = u := (Option.some.inj hv₀).symm
            subst v₀
            have heq : nfTerm canon v = nfTerm canon t :=
              hvnf.trans hnf
            exact ⟨ρ, by simp [matchPat, hx, heq],
              hagree⟩
    | num s =>
        have hu : u = .num s := by
          simpa [instPat] using hinst.symm
        subst u
        exact ⟨ρ, by simp [matchPat, hnf], hagree⟩
    | str s =>
        have hu : u = .str s := by
          simpa [instPat] using hinst.symm
        subst u
        exact ⟨ρ, by simp [matchPat, hnf], hagree⟩
    | con k ps =>
        simp only [instPat] at hinst
        cases his : instPats ρ₀ ps with
        | none => simp [his] at hinst
        | some us =>
            simp [his] at hinst
            subst u
            cases t with
            | num s => simp [nfTerm] at hnf
            | str s => simp [nfTerm] at hnf
            | con k' ts =>
                simp only [nfTerm] at hnf
                have hk : k.name = k' := by
                  injection hnf
                have hts : nfTerms canon us = nfTerms canon ts := by
                  injection hnf
                rcases matchPats_complete canon ρ ρ₀ hagree ps ts us his hts
                  with ⟨ρ', hm, hagree'⟩
                exact ⟨ρ', by simp [matchPat, hk, hm], hagree'⟩

  theorem matchPats_complete (canon : String → String) (ρ ρ₀ : Subst)
      (hagree : SubstCanonAgrees canon ρ ρ₀)
      (ps : Pats) (ts us : Terms)
      (hinst : instPats ρ₀ ps = some us)
      (hnf : nfTerms canon us = nfTerms canon ts) :
      ∃ ρ', matchPats canon ρ ps ts = some ρ' ∧
        SubstCanonAgrees canon ρ' ρ₀ := by
    cases ps with
    | nil =>
        simp only [instPats] at hinst
        have hus : us = .nil := Option.some.inj hinst.symm
        subst us
        cases ts with
        | nil => exact ⟨ρ, rfl, hagree⟩
        | cons t ts => simp [nfTerms] at hnf
    | cons p ps =>
        simp only [instPats] at hinst
        cases hp : instPat ρ₀ p with
        | none => simp [hp] at hinst
        | some u =>
            cases hps : instPats ρ₀ ps with
            | none => simp [hp, hps] at hinst
            | some us' =>
                simp [hp, hps] at hinst
                subst us
                cases ts with
                | nil => simp [nfTerms] at hnf
                | cons t ts =>
                    simp only [nfTerms] at hnf
                    have hu : nfTerm canon u = nfTerm canon t := by
                      injection hnf
                    have hus : nfTerms canon us' = nfTerms canon ts := by
                      injection hnf
                    rcases matchPat_complete canon ρ ρ₀ hagree p t u hp hu
                      with ⟨ρ₁, hm₁, hagree₁⟩
                    rcases matchPats_complete canon ρ₁ ρ₀ hagree₁ ps ts us'
                        hps hus with ⟨ρ', hm₂, hagree₂⟩
                    exact ⟨ρ', by simp [matchPats, hm₁, hm₂], hagree₂⟩
end

theorem matchAPat_complete (canon : String → String) (ρ ρ₀ : Subst)
    (hagree : SubstCanonAgrees canon ρ ρ₀)
    (ap : APat) (a a₀ : Atom)
    (hinst : instAPat ρ₀ ap = some a₀)
    (heq : equiv canon a₀ a) :
    ∃ ρ', matchAPat canon ρ ap a = some ρ' ∧
      SubstCanonAgrees canon ρ' ρ₀ := by
  cases a with
  | atom pred ts =>
      cases a₀ with
      | atom pred₀ us =>
          simp only [instAPat] at hinst
          cases hi : instPats ρ₀ ap.args with
          | none => simp [hi] at hinst
          | some us₀ =>
              simp [hi] at hinst
              rcases hinst with ⟨hpred, hus⟩
              subst pred₀
              subst us
              simp only [equiv, nf] at heq
              have hp : ap.pred.name = pred := by injection heq
              have hts : nfTerms canon us₀ = nfTerms canon ts := by
                injection heq
              rcases matchPats_complete canon ρ ρ₀ hagree ap.args ts us₀
                  hi hts with ⟨ρ', hm, hagree'⟩
              exact ⟨ρ', by simp [matchAPat, hp, hm], hagree'⟩

theorem emptySubstCanonAgrees (canon : String → String) (ρ : Subst) :
    SubstCanonAgrees canon [] ρ := by
  intro x t h
  simp [lookupSubst] at h

theorem contraryMatchDecl_iff (canon : String → String) (p q : Atom)
    (ab : APat × APat) :
    contraryMatchDecl canon p q ab = true ↔
      ∃ (ρ : Subst) (pa pb : Atom),
        instAPat ρ ab.1 = some pa ∧ instAPat ρ ab.2 = some pb ∧
          equiv canon pa p ∧ equiv canon pb q := by
  constructor
  · intro h
    simp only [contraryMatchDecl] at h
    cases h₁ : matchAPat canon [] ab.1 p with
    | none => simp [h₁] at h
    | some ρ₁ =>
        rw [h₁] at h
        cases h₂ : matchAPat canon ρ₁ ab.2 q with
        | none => simp [h₂] at h
        | some ρ₂ =>
            rcases matchAPat_sound canon [] ab.1 p ρ₁ h₁ with
              ⟨_, pa, hpa, heqp⟩
            rcases matchAPat_sound canon ρ₁ ab.2 q ρ₂ h₂ with
              ⟨hext, pb, hpb, heqq⟩
            exact ⟨ρ₂, pa, pb, instAPat_of_extends hext hpa, hpb,
              heqp, heqq⟩
  · rintro ⟨ρ₀, pa, pb, hpa, hpb, heqp, heqq⟩
    rcases matchAPat_complete canon [] ρ₀
        (emptySubstCanonAgrees canon ρ₀) ab.1 p pa hpa heqp with
      ⟨ρ₁, h₁, hagree₁⟩
    rcases matchAPat_complete canon ρ₁ ρ₀ hagree₁ ab.2 q pb hpb heqq with
      ⟨ρ₂, h₂, _⟩
    simp [contraryMatchDecl, h₁, h₂]

theorem contraryMatchB_iff (canon : String → String) (dp : DefeatPolicy)
    (p q : Atom) :
    contraryMatchB canon dp p q = true ↔ ContraryMatch canon dp p q := by
  simp only [contraryMatchB, List.any_eq_true, ContraryMatch]
  constructor
  · rintro ⟨ab, hab, hm⟩
    exact ⟨ab, hab, (contraryMatchDecl_iff canon p q ab).mp hm⟩
  · rintro ⟨ab, hab, hm⟩
    exact ⟨ab, hab, (contraryMatchDecl_iff canon p q ab).mpr hm⟩

/-! ### The attack judgment (spec §7.1, v0.1-frozen) -/

/-- `k ::= rebut w u | undercut w u@π | undermine w u@π`. -/
inductive Attack where
  | rebut     : SupportTerm → SupportTerm → Attack
  | undercut  : SupportTerm → SupportTerm → Pos → Attack
  | undermine : SupportTerm → SupportTerm → Pos → Attack

def Attack.source : Attack → SupportTerm
  | .rebut w _ => w
  | .undercut w _ _ => w
  | .undermine w _ _ => w

/-- The attacked declared argument `u` (the whole term the position addresses
into). -/
def Attack.target : Attack → SupportTerm
  | .rebut _ u => u
  | .undercut _ u _ => u
  | .undermine _ u _ => u

/-- The three §7.1 rules. The source premise is a full typing (checked, not
complete); target-side premises are occurrence-local (`Pi`/`Gamma` lookups),
never a typing of `u` — the locality design point. -/
inductive HasAttack (canon : String → String) (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom)
    (CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop)
    (dp : DefeatPolicy) : Attack → Prop where
  | rebut {w : SupportTerm} {rn : RuleId} {θ : Subst}
      {ws : List SupportTerm} {D : List (QuestionId × SupportTerm)}
      {H : List QuestionId} {a : Assurance} {r : Rule} {Cw Cu : Atom}
      {Ow : List QuestionId}
      (hw : HasSupport canon Pi Gamma CertOk w Cw Ow)
      (hrule : Pi rn = some r)
      (hdef : r.mode = .defeasible)
      (hconcl : instAPat θ r.concl = some Cu)
      (hcon : ContraryMatch canon dp Cw Cu) :
      HasAttack canon Pi Gamma CertOk dp (.rebut w (.inst rn θ ws D H a))
  | undercut {w u : SupportTerm} {π : Pos} {rn : RuleId} {θ : Subst}
      {ws : List SupportTerm} {D : List (QuestionId × SupportTerm)}
      {H : List QuestionId} {a : Assurance} {r : Rule} {E : APat} {e Cw : Atom}
      {Ow : List QuestionId}
      (hw : HasSupport canon Pi Gamma CertOk w Cw Ow)
      (hocc : subterm u π = some (.inst rn θ ws D H a))
      (hrule : Pi rn = some r)
      (hdef : r.mode = .defeasible)
      (hexc : (rn, E) ∈ dp.exceptions)
      (hinst : instAPat θ E = some e)
      (heq : equiv canon Cw e) :
      HasAttack canon Pi Gamma CertOk dp (.undercut w u π)
  | undermine {w u : SupportTerm} {π : Pos} {l : LeafId} {pl Cw : Atom}
      {Ow : List QuestionId}
      (hw : HasSupport canon Pi Gamma CertOk w Cw Ow)
      (hocc : subterm u π = some (.leaf l))
      (hl : Gamma l = some pl)
      (hcon : ContraryMatch canon dp Cw pl) :
      HasAttack canon Pi Gamma CertOk dp (.undermine w u π)

/-! ### §1 guarantee 4: checked source -/

/-- Every typed attack's source term type-checks. (Nothing requires its
obligation set to be empty — completeness is the compile step's gate.) -/
theorem attack_source_checked {canon Pi Gamma CertOk dp} {k : Attack}
    (hk : HasAttack canon Pi Gamma CertOk dp k) :
    ∃ Cw Ow, HasSupport canon Pi Gamma CertOk k.source Cw Ow := by
  cases hk with
  | rebut hw _ _ _ _ => exact ⟨_, _, hw⟩
  | undercut hw _ _ _ _ _ _ => exact ⟨_, _, hw⟩
  | undermine hw _ _ _ => exact ⟨_, _, hw⟩

/-! ### Strict occurrences are unattackable (spec §7) -/

/-- The rule at a rebutted root is defeasible — a strict-topped instance
cannot be rebutted. -/
theorem rebut_top_defeasible {canon Pi Gamma CertOk dp}
    {w : SupportTerm} {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {a : Assurance}
    (hk : HasAttack canon Pi Gamma CertOk dp (.rebut w (.inst rn θ ws D H a)))
    {r : Rule} (hr : Pi rn = some r) : r.mode = .defeasible := by
  cases hk with
  | rebut hw hrule hdef hconcl hcon =>
    rw [Option.some.inj (hrule.symm.trans hr)] at hdef
    exact hdef

/-- The rule at an undercut position is defeasible — a strict occurrence
cannot be undercut. Together with `rebut_top_defeasible`: strict inferences
are unattackable (ASPIC+, spec §7). -/
theorem undercut_pos_defeasible {canon Pi Gamma CertOk dp}
    {w u : SupportTerm} {π : Pos}
    (hk : HasAttack canon Pi Gamma CertOk dp (.undercut w u π))
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId} {a : Assurance}
    (hocc : subterm u π = some (.inst rn θ ws D H a))
    {r : Rule} (hr : Pi rn = some r) : r.mode = .defeasible := by
  cases hk with
  | undercut hw hocc' hrule hdef hexc hinst heq =>
    rw [hocc] at hocc'
    have hinj := Option.some.inj hocc'
    injection hinj with hrn hθ hws hD hH ha
    subst hrn
    rw [Option.some.inj (hrule.symm.trans hr)] at hdef
    exact hdef

/-! ### The position-kind partition (spec §7: three attacks, three positions) -/

/-- An undercut's target occurrence is a defeasible rule instance. -/
theorem undercut_target_rule {canon Pi Gamma CertOk dp}
    {w u : SupportTerm} {π : Pos}
    (hk : HasAttack canon Pi Gamma CertOk dp (.undercut w u π)) :
    ∃ rn θ ws D H a r, subterm u π = some (.inst rn θ ws D H a) ∧
      Pi rn = some r ∧ r.mode = .defeasible := by
  cases hk with
  | undercut hw hocc hrule hdef hexc hinst heq =>
    exact ⟨_, _, _, _, _, _, _, hocc, hrule, hdef⟩

/-- An undermine's target occurrence is a declared leaf. -/
theorem undermine_target_leaf {canon Pi Gamma CertOk dp}
    {w u : SupportTerm} {π : Pos}
    (hk : HasAttack canon Pi Gamma CertOk dp (.undermine w u π)) :
    ∃ l pl, subterm u π = some (.leaf l) ∧ Gamma l = some pl := by
  cases hk with
  | undermine hw hocc hl hcon => exact ⟨_, _, hocc, hl⟩

/-! ### Locality is coherent with global typing -/

/-- [A-Rebut] reads the target conclusion off the root instance without
typing `u`. If `u` *is* typed, that local read-off agrees: the contrary match
holds against `u`'s typed conclusion. Local attack checking and global
support typing cannot disagree. -/
theorem rebut_concl_coherent {canon Pi Gamma CertOk dp}
    {w u : SupportTerm}
    (hk : HasAttack canon Pi Gamma CertOk dp (.rebut w u))
    {Cu : Atom} {Ou : List QuestionId}
    (hu : HasSupport canon Pi Gamma CertOk u Cu Ou) :
    ∃ Cw Ow, HasSupport canon Pi Gamma CertOk w Cw Ow ∧
      ContraryMatch canon dp Cw Cu := by
  cases hk with
  | @rebut _ _ _ _ _ _ _ r Cw₀ Cu₀ Ow₀ hw hrule hdef hconcl hcon =>
    cases hu with
    | @inst _ _ _ _ _ _ r' As' Cs' Os' DCs' DOs' _ hside' _ _ =>
      have hrr : r' = r := Option.some.inj (hside'.rule.symm.trans hrule)
      rw [hrr] at hside'
      have hCu : Cu₀ = Cu := Option.some.inj (hconcl.symm.trans hside'.concl)
      exact ⟨Cw₀, Ow₀, hw, hCu ▸ hcon⟩

end Lara.Attack
