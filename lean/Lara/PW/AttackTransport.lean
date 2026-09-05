/-
Declared-attack transport (issue #238, tracker #189).

T8's `StatusBridge.forth`/`back` are index-level clauses on the compiled edge
decider `Compile.edgeB`. This module derives them from a correspondence
between the two programs' *declared* attacks: `trAttack`/`trAttackList`
translate a declared attack (both stored terms translated, kind and position
carried verbatim), `AttackBridge.atts_eq` states that the target's declared
attacks are exactly the transports of the source's, and
`AttackBridge.toStatusBridge` derives the index-level clauses from that
source-language contract.

The commutation ladder mirrors `Lara/Erase.lean` lemma-for-lemma
(`mapAssur_subterm`, `containsB_mapAssur`, `attackClosureB_mapAssur`,
`coveredB_relabel`), replacing the total `mapAssur f` with the partial
`trSupport m lm`: every lemma threads `trSupport … = some …` hypotheses, and
partiality forces two inversion helpers (`trSupport_inst_inv`,
`trSupport_subterm_some`) and the `_some_of_mem` lemmas that have no total-map
analogue. Everything stays at the `Bool` level (`containsB` →
`attackClosureB` → `coveredB` → `edgeB`), exactly as `Erase.lean` does, which
avoids any `DisNodup` side condition; the Prop faces `Contains`/`AttackOcc`
named by the issue are recovered as corollaries at the end.

**Injectivity is load-bearing** (T8 limitation 1 is *narrowed*, not
discharged): `containsB` compares subterms by `decide (v = t)`
(`Lara/Compile.lean:120-123`), so the ladder needs both `SymMap.Injective`
(for substitutions, via `trTerm_inj`) and `Function.Injective lm` (for
leaves). A collapsing leaf map makes two distinct source subterms translate
equal and breaks the `decide` component — witnessed negatively in
`Lara/Examples/PWAttack.lean`. The frozen `StatusBridge` contract itself does
not require leaf-map injectivity, so the general injectivity-free statement
of limitation 1 still stands.

**Forced duplication, do not "fix".** `AttackBridge.admits`/`matched` repeat
`StatusBridge`'s first two field statements verbatim. No shared parent can be
introduced: `Lara/PW/Status.lean` is frozen T8 record under empty-diff
discipline. The duplication is forced, not chosen.

`trAttackList`'s cons step goes through the #234 seam (`zipOpt` /
`trAttackList_cons`) — the seam's first use outside the eight traversals it
was extracted from.
-/

import Lara.PW.Status

namespace Lara.PW

open Lara.Support Lara.Compile Lara.PW.Instance

/-! ### Translating declared attacks -/

/-- Structural translation of a declared attack: both stored terms are
translated, the kind and the position are carried verbatim. -/
def trAttack (m : SymMap) (lm : LeafId → LeafId) :
    Lara.Attack.Attack → Option Lara.Attack.Attack
  | .rebut s u =>
      match trSupport m lm s, trSupport m lm u with
      | some s', some u' => some (.rebut s' u')
      | _, _ => none
  | .undercut s u π =>
      match trSupport m lm s, trSupport m lm u with
      | some s', some u' => some (.undercut s' u' π)
      | _, _ => none
  | .undermine s u π =>
      match trSupport m lm s, trSupport m lm u with
      | some s', some u' => some (.undermine s' u' π)
      | _, _ => none

/-- Elementwise, all-or-nothing attack-list translation. -/
def trAttackList (m : SymMap) (lm : LeafId → LeafId) :
    List Lara.Attack.Attack → Option (List Lara.Attack.Attack)
  | [] => some []
  | k :: ks =>
      match trAttack m lm k, trAttackList m lm ks with
      | some k', some ks' => some (k' :: ks')
      | _, _ => none

/-- The cons step of `trAttackList` as `zipOpt` (issue #234's seam, reused
per eng review decision 3A). -/
theorem trAttackList_cons (m : SymMap) (lm : LeafId → LeafId)
    (k : Lara.Attack.Attack) (ks : List Lara.Attack.Attack) :
    trAttackList m lm (k :: ks) =
      zipOpt (· :: ·) (trAttack m lm k) (trAttackList m lm ks) := by
  cases h : trAttack m lm k <;> cases h' : trAttackList m lm ks <;>
    simp [trAttackList, zipOpt, h, h']

/-! ### Inversion and injectivity -/

/-- `trSupport` on a leaf is total. -/
theorem trSupport_leaf (m : SymMap) (lm : LeafId → LeafId) (l : LeafId) :
    trSupport m lm (.leaf l) = some (.leaf (lm l)) := rfl

/-- Inversion on `inst`: a translated instance node decomposes into
translated substitution, premise list, and discharge map. -/
theorem trSupport_inst_inv {m : SymMap} {lm : LeafId → LeafId}
    {rn θ ws D H α} {u' : SupportTerm}
    (h : trSupport m lm (.inst rn θ ws D H α) = some u') :
    ∃ θ' ws' D', trSubst m θ = some θ' ∧ trSupportList m lm ws = some ws' ∧
      trSupportDis m lm D = some D' ∧ u' = .inst rn θ' ws' D' H α := by
  simp only [trSupport] at h
  split at h
  · next θ' ws' D' hθ hws hD =>
    cases h
    exact ⟨θ', ws', D', hθ, hws, hD, rfl⟩
  · cases h

/-- Substitution injectivity from term injectivity: elementwise, keys
preserved. Helper consumed by `trSupport_inj`'s `inst` case. -/
theorem trSubst_inj {m : SymMap} (hm : m.Injective)
    {θ ρ θ' : Subst} (hθ : trSubst m θ = some θ')
    (hρ : trSubst m ρ = some θ') : θ = ρ := by
  induction θ generalizing ρ θ' with
  | nil =>
    cases hθ
    cases ρ with
    | nil => rfl
    | cons xu ρ =>
      obtain ⟨x, u⟩ := xu
      simp only [trSubst] at hρ
      split at hρ <;> cases hρ
  | cons xt θ ih =>
    obtain ⟨x, t⟩ := xt
    simp only [trSubst] at hθ
    split at hθ
    · next t' θ₁' ht hθ₁ =>
      cases hθ
      cases ρ with
      | nil => simp only [trSubst] at hρ; cases hρ
      | cons yu ρ =>
        obtain ⟨y, u⟩ := yu
        simp only [trSubst] at hρ
        split at hρ
        · next u' ρ₁' hu hρ₁ =>
          cases hρ
          rw [trTerm_inj hm t u ht hu, ih hθ₁ hρ₁]
        · cases hρ
    · cases hθ

mutual
  /-- An injective translation is injective on support terms wherever it is
  defined. Mirrors `mapAssur_inj` (`Lara/Erase.lean:76`). -/
  theorem trSupport_inj {m : SymMap} {lm : LeafId → LeafId}
      (hsym : m.Injective) (hlm : Function.Injective lm) :
      ∀ {a b a' : SupportTerm}, trSupport m lm a = some a' →
        trSupport m lm b = some a' → a = b
    | .leaf la, b, _, ha, hb => by
        simp only [trSupport] at ha
        cases ha
        cases b with
        | leaf lb =>
          simp only [trSupport, Option.some.injEq,
            SupportTerm.leaf.injEq] at hb
          rw [hlm hb]
        | inst rn θ ws D H α =>
          simp only [trSupport] at hb
          split at hb
          · next θ' ws' D' hθ hws hD => cases hb
          · cases hb
    | .inst rn θ ws D H α, b, _, ha, hb => by
        obtain ⟨θ', ws', D', hθ, hws, hD, rfl⟩ := trSupport_inst_inv ha
        cases b with
        | leaf lb => simp only [trSupport] at hb; cases hb
        | inst rn₂ θ₂ ws₂ D₂ H₂ α₂ =>
          obtain ⟨θ₂', ws₂', D₂', hθ₂, hws₂, hD₂, hbe⟩ :=
            trSupport_inst_inv hb
          cases hbe
          rw [trSubst_inj hsym hθ hθ₂,
            trSupportList_inj hsym hlm hws hws₂,
            trSupportDis_inj hsym hlm hD hD₂]
  theorem trSupportList_inj {m : SymMap} {lm : LeafId → LeafId}
      (hsym : m.Injective) (hlm : Function.Injective lm) :
      ∀ {xs ys xs' : List SupportTerm}, trSupportList m lm xs = some xs' →
        trSupportList m lm ys = some xs' → xs = ys
    | [], ys, _, hx, hy => by
        cases hx
        cases ys with
        | nil => rfl
        | cons w ys =>
          simp only [trSupportList] at hy
          split at hy <;> cases hy
    | x :: xs, ys, _, hx, hy => by
        simp only [trSupportList] at hx
        split at hx
        · next x' xs₁' hx₁ hxs =>
          cases hx
          cases ys with
          | nil => simp only [trSupportList] at hy; cases hy
          | cons y ys =>
            simp only [trSupportList] at hy
            split at hy
            · next y' ys₁' hy₁ hys =>
              cases hy
              rw [trSupport_inj hsym hlm hx₁ hy₁,
                trSupportList_inj hsym hlm hxs hys]
            · cases hy
        · cases hx
  theorem trSupportDis_inj {m : SymMap} {lm : LeafId → LeafId}
      (hsym : m.Injective) (hlm : Function.Injective lm) :
      ∀ {xs ys xs' : List (QuestionId × SupportTerm)},
        trSupportDis m lm xs = some xs' →
        trSupportDis m lm ys = some xs' → xs = ys
    | [], ys, _, hx, hy => by
        cases hx
        cases ys with
        | nil => rfl
        | cons qw ys =>
          obtain ⟨q, w⟩ := qw
          simp only [trSupportDis] at hy
          split at hy <;> cases hy
    | qw :: xs, ys, _, hx, hy => by
        obtain ⟨q, w⟩ := qw
        simp only [trSupportDis] at hx
        split at hx
        · next w' xs₁' hw hxs =>
          cases hx
          cases ys with
          | nil => simp only [trSupportDis] at hy; cases hy
          | cons qw₂ ys =>
            obtain ⟨q₂, w₂⟩ := qw₂
            simp only [trSupportDis] at hy
            split at hy
            · next w₂' ys₁' hw₂ hys =>
              cases hy
              rw [trSupport_inj hsym hlm hw hw₂,
                trSupportDis_inj hsym hlm hxs hys]
            · cases hy
        · cases hx
end

/-- Translated terms are equal iff their sources are — the `decide`
component of `containsB` rewritten through translation. Mirrors
`mapAssur_eq_iff` (`Lara/Erase.lean:110`). -/
theorem trSupport_eq_iff {m : SymMap} {lm : LeafId → LeafId}
    (hsym : m.Injective) (hlm : Function.Injective lm)
    {a b a' b' : SupportTerm} (ha : trSupport m lm a = some a')
    (hb : trSupport m lm b = some b') : (a' = b') ↔ (a = b) := by
  constructor
  · intro h
    subst h
    exact trSupport_inj hsym hlm ha hb
  · intro h
    subst h
    rw [ha] at hb
    exact Option.some.inj hb

/-! ### Positional navigation commutes with translation -/

/-- A first-match lookup hit is a member of the discharge map. -/
theorem lookupDis_mem {D : List (QuestionId × SupportTerm)} {q : QuestionId}
    {w : SupportTerm} (h : Lara.Attack.lookupDis D q = some w) :
    (q, w) ∈ D := by
  induction D with
  | nil => cases h
  | cons qw D ih =>
    obtain ⟨q', w'⟩ := qw
    simp only [Lara.Attack.lookupDis] at h
    split at h
    · next heq =>
      cases h
      subst heq
      exact List.mem_cons_self
    · next hne =>
      exact List.mem_cons.mpr (.inr (ih h))

/-- First-match lookup commutes with translation because `trSupportDis`
carries keys verbatim in order. Mirrors `lookupDis_mapAssurDis`
(`Lara/Erase.lean:116`). -/
theorem lookupDis_trSupportDis {m : SymMap} {lm : LeafId → LeafId}
    {D D' : List (QuestionId × SupportTerm)}
    (h : trSupportDis m lm D = some D') (q : QuestionId) :
    Lara.Attack.lookupDis D' q =
      (Lara.Attack.lookupDis D q).bind (trSupport m lm) := by
  induction D generalizing D' with
  | nil => cases h; rfl
  | cons qw D ih =>
    obtain ⟨q', w⟩ := qw
    simp only [trSupportDis] at h
    split at h
    · next w' D₁' hw hD =>
      cases h
      simp only [Lara.Attack.lookupDis]
      split
      · next heq => exact hw.symm
      · next hne => exact ih hD
    · cases h

/-- Every member of a translated premise list translates. -/
theorem trSupportList_some_of_mem {m : SymMap} {lm : LeafId → LeafId}
    {ws ws' : List SupportTerm} (h : trSupportList m lm ws = some ws')
    {w : SupportTerm} (hmem : w ∈ ws) :
    ∃ w', trSupport m lm w = some w' := by
  induction ws generalizing ws' with
  | nil => cases hmem
  | cons x xs ih =>
    simp only [trSupportList] at h
    split at h
    · next x' xs₁' hx hxs =>
      cases hmem with
      | head => exact ⟨x', hx⟩
      | tail _ hmem => exact ih hxs hmem
    · cases h

/-- Every member of a translated discharge map translates. -/
theorem trSupportDis_some_of_mem {m : SymMap} {lm : LeafId → LeafId}
    {D D' : List (QuestionId × SupportTerm)}
    (h : trSupportDis m lm D = some D')
    {q : QuestionId} {w : SupportTerm} (hmem : (q, w) ∈ D) :
    ∃ w', trSupport m lm w = some w' := by
  induction D generalizing D' with
  | nil => cases hmem
  | cons qw D ih =>
    obtain ⟨q₀, w₀⟩ := qw
    simp only [trSupportDis] at h
    split at h
    · next w₀' D₁' hw₀ hD =>
      cases hmem with
      | head => exact ⟨w₀', hw₀⟩
      | tail _ hmem => exact ih hD hmem
    · cases h

/-- Subterm navigation commutes with translation — on the nose, because
`trSupportList` preserves order and length (`prem i`) and `trSupportDis`
carries question keys verbatim in order (`ques q`). Mirrors
`mapAssur_subterm` (`Lara/Erase.lean:125`); no injectivity needed. -/
theorem trSupport_subterm {m : SymMap} {lm : LeafId → LeafId} :
    ∀ {u u' : SupportTerm}, trSupport m lm u = some u' →
    ∀ π : Lara.Attack.Pos,
      Lara.Attack.subterm u' π =
        (Lara.Attack.subterm u π).bind (trSupport m lm) := by
  intro u u' h π
  induction π generalizing u u' with
  | nil => exact h.symm
  | cons pe π ih =>
    cases u with
    | leaf l =>
      simp only [trSupport] at h
      cases h
      rfl
    | inst rn θ ws D H α =>
      obtain ⟨θ', ws', D', hθ, hws, hD, rfl⟩ := trSupport_inst_inv h
      cases pe with
      | prem i =>
        simp only [Lara.Attack.subterm, trSupportList_getElem? hws i]
        cases hwi : ws[i]? with
        | none => rfl
        | some w =>
          rw [Option.bind_some]
          obtain ⟨w', hw⟩ :=
            trSupportList_some_of_mem hws (List.mem_of_getElem? hwi)
          rw [hw]
          exact ih hw
      | ques q =>
        simp only [Lara.Attack.subterm, lookupDis_trSupportDis hD q]
        cases hq : Lara.Attack.lookupDis D q with
        | none => rfl
        | some w =>
          rw [Option.bind_some]
          obtain ⟨w', hw⟩ := trSupportDis_some_of_mem hD (lookupDis_mem hq)
          rw [hw]
          exact ih hw

/-- Partiality inversion with no total-map analogue: a subterm of a
translated term translates. Consumed by `attackClosureB_trAttack`'s
undercut/undermine arms. -/
theorem trSupport_subterm_some {m : SymMap} {lm : LeafId → LeafId}
    {u u' x : SupportTerm} (h : trSupport m lm u = some u')
    {π : Lara.Attack.Pos} (hx : Lara.Attack.subterm u π = some x) :
    ∃ x', trSupport m lm x = some x' := by
  induction π generalizing u u' x with
  | nil =>
    simp only [Lara.Attack.subterm] at hx
    cases hx
    exact ⟨u', h⟩
  | cons pe π ih =>
    cases u with
    | leaf l => cases hx
    | inst rn θ ws D H α =>
      obtain ⟨θ', ws', D', hθ, hws, hD, rfl⟩ := trSupport_inst_inv h
      cases pe with
      | prem i =>
        simp only [Lara.Attack.subterm] at hx
        cases hwi : ws[i]? with
        | none => rw [hwi] at hx; cases hx
        | some w =>
          rw [hwi] at hx
          obtain ⟨w', hw⟩ :=
            trSupportList_some_of_mem hws (List.mem_of_getElem? hwi)
          exact ih hw hx
      | ques q =>
        simp only [Lara.Attack.subterm] at hx
        cases hq : Lara.Attack.lookupDis D q with
        | none => rw [hq] at hx; cases hx
        | some w =>
          rw [hq] at hx
          obtain ⟨w', hw⟩ := trSupportDis_some_of_mem hD (lookupDis_mem hq)
          exact ih hw hx

/-! ### Containment and coverage commute with translation -/

mutual
  /-- Structural containment is translation-invariant under injectivity —
  the `decide (v = t)` component is where injectivity is consumed. Mirrors
  `containsB_mapAssur` (`Lara/Erase.lean:150`). -/
  theorem containsB_trSupport {m : SymMap} {lm : LeafId → LeafId}
      (hsym : m.Injective) (hlm : Function.Injective lm) :
      ∀ {v v' t t' : SupportTerm}, trSupport m lm v = some v' →
        trSupport m lm t = some t' → containsB v' t' = containsB v t
    | .leaf l, _, t, t', hv, ht => by
        simp only [trSupport] at hv
        cases hv
        exact decide_eq_decide.mpr (trSupport_eq_iff hsym hlm rfl ht)
    | .inst rn θ ws D H α, _, t, t', hv, ht => by
        obtain ⟨θ', ws', D', hθ, hws, hD, rfl⟩ := trSupport_inst_inv hv
        show (decide (.inst rn θ' ws' D' H α = t')
              || containsBList ws' t' || containsBDis D' t')
            = (decide (.inst rn θ ws D H α = t)
              || containsBList ws t || containsBDis D t)
        rw [decide_eq_decide.mpr (trSupport_eq_iff hsym hlm hv ht),
          containsBList_trSupport hsym hlm hws ht,
          containsBDis_trSupport hsym hlm hD ht]
  theorem containsBList_trSupport {m : SymMap} {lm : LeafId → LeafId}
      (hsym : m.Injective) (hlm : Function.Injective lm) :
      ∀ {ws ws' : List SupportTerm} {t t' : SupportTerm},
        trSupportList m lm ws = some ws' → trSupport m lm t = some t' →
        containsBList ws' t' = containsBList ws t
    | [], _, _, _, hws, _ => by cases hws; rfl
    | w :: ws, _, t, t', hws, ht => by
        simp only [trSupportList] at hws
        split at hws
        · next w' ws₁' hw hws₁ =>
          cases hws
          simp only [containsBList]
          rw [containsB_trSupport hsym hlm hw ht,
            containsBList_trSupport hsym hlm hws₁ ht]
        · cases hws
  theorem containsBDis_trSupport {m : SymMap} {lm : LeafId → LeafId}
      (hsym : m.Injective) (hlm : Function.Injective lm) :
      ∀ {D D' : List (QuestionId × SupportTerm)} {t t' : SupportTerm},
        trSupportDis m lm D = some D' → trSupport m lm t = some t' →
        containsBDis D' t' = containsBDis D t
    | [], _, _, _, hD, _ => by cases hD; rfl
    | qw :: D, _, t, t', hD, ht => by
        obtain ⟨q, w⟩ := qw
        simp only [trSupportDis] at hD
        split at hD
        · next w' D₁' hw hD₁ =>
          cases hD
          simp only [containsBDis]
          rw [containsB_trSupport hsym hlm hw ht,
            containsBDis_trSupport hsym hlm hD₁ ht]
        · cases hD
end

/-- The translated attack's source is the translated source. Mirrors
`mapAssurAtt_source` (`Lara/Erase.lean:69`). -/
theorem trAttack_source {m : SymMap} {lm : LeafId → LeafId}
    {k k' : Lara.Attack.Attack} (h : trAttack m lm k = some k') :
    trSupport m lm k.source = some k'.source := by
  cases k with
  | rebut s u =>
    simp only [trAttack] at h
    split at h
    · next s' u' hs hu => cases h; exact hs
    · cases h
  | undercut s u π =>
    simp only [trAttack] at h
    split at h
    · next s' u' hs hu => cases h; exact hs
    · cases h
  | undermine s u π =>
    simp only [trAttack] at h
    split at h
    · next s' u' hs hu => cases h; exact hs
    · cases h

/-- The attack-closure test is translation-invariant. Mirrors
`attackClosureB_mapAssur` (`Lara/Erase.lean:179`). -/
theorem attackClosureB_trAttack {m : SymMap} {lm : LeafId → LeafId}
    (hsym : m.Injective) (hlm : Function.Injective lm)
    {k k' : Lara.Attack.Attack} {t t' : SupportTerm}
    (hk : trAttack m lm k = some k') (ht : trSupport m lm t = some t') :
    attackClosureB k' t' = attackClosureB k t := by
  cases k with
  | rebut s u =>
    simp only [trAttack] at hk
    split at hk
    · next s' u' hs hu =>
      cases hk
      simp only [attackClosureB]
      exact containsB_trSupport hsym hlm ht hu
    · cases hk
  | undercut s u π =>
    simp only [trAttack] at hk
    split at hk
    · next s' u' hs hu =>
      cases hk
      simp only [attackClosureB, trSupport_subterm hu π]
      cases hsub : Lara.Attack.subterm u π with
      | none => rfl
      | some x =>
        obtain ⟨x', hx'⟩ := trSupport_subterm_some hu hsub
        rw [Option.bind_some, hx']
        exact containsB_trSupport hsym hlm ht hx'
    · cases hk
  | undermine s u π =>
    simp only [trAttack] at hk
    split at hk
    · next s' u' hs hu =>
      cases hk
      simp only [attackClosureB, trSupport_subterm hu π]
      cases hsub : Lara.Attack.subterm u π with
      | none => rfl
      | some x =>
        obtain ⟨x', hx'⟩ := trSupport_subterm_some hu hsub
        rw [Option.bind_some, hx']
        exact containsB_trSupport hsym hlm ht hx'
    · cases hk

/-- Declared-edge coverage is translation-invariant. Mirrors
`coveredB_relabel` (`Lara/Erase.lean:198`). -/
theorem coveredB_trAttack {m : SymMap} {lm : LeafId → LeafId}
    (hsym : m.Injective) (hlm : Function.Injective lm)
    {atts atts' : List Lara.Attack.Attack} {s s' t t' : SupportTerm}
    (hatts : trAttackList m lm atts = some atts')
    (hs : trSupport m lm s = some s') (ht : trSupport m lm t = some t') :
    coveredB atts' s' t' = coveredB atts s t := by
  simp only [coveredB]
  induction atts generalizing atts' with
  | nil => cases hatts; rfl
  | cons k rest ih =>
    rw [trAttackList_cons] at hatts
    cases hk : trAttack m lm k with
    | none =>
      cases hrest : trAttackList m lm rest with
      | none => rw [hk, hrest] at hatts; simp only [zipOpt] at hatts; cases hatts
      | some rest' =>
        rw [hk, hrest] at hatts; simp only [zipOpt] at hatts; cases hatts
    | some k' =>
      cases hrest : trAttackList m lm rest with
      | none => rw [hk, hrest] at hatts; simp only [zipOpt] at hatts; cases hatts
      | some rest' =>
        rw [hk, hrest] at hatts
        simp only [zipOpt] at hatts
        cases hatts
        simp only [List.any_cons]
        rw [ih hrest, attackClosureB_trAttack hsym hlm hk ht,
          decide_eq_decide.mpr
            (trSupport_eq_iff hsym hlm (trAttack_source hk) hs)]

/-! ### Prop-level corollaries (the faces #238 names) -/

/-- `Contains` commutes with translation. The `DisNodup` side conditions
come from the checked programs' `complete` field via `hasSupport_disNodup`
at use sites, exactly as `edgeB_iff` discharges them
(`Lara/Compile.lean:632-634`). -/
theorem Contains_trSupport {m : SymMap} {lm : LeafId → LeafId}
    (hsym : m.Injective) (hlm : Function.Injective lm)
    {v v' t t' : SupportTerm} (hdn : DisNodup v) (hdn' : DisNodup v')
    (hv : trSupport m lm v = some v') (ht : trSupport m lm t = some t') :
    Contains v' t' ↔ Contains v t := by
  rw [← containsB_iff hdn t, ← containsB_iff hdn' t',
    containsB_trSupport hsym hlm hv ht]

/-- `AttackOcc` occurrence-in-target commutes with translation. -/
theorem AttackOcc_trSupport {m : SymMap} {lm : LeafId → LeafId}
    (hsym : m.Injective) (hlm : Function.Injective lm)
    {k k' : Lara.Attack.Attack} {t t' : SupportTerm}
    (hdn : DisNodup t) (hdn' : DisNodup t')
    (hk : trAttack m lm k = some k') (ht : trSupport m lm t = some t') :
    (∃ u, AttackOcc k' u ∧ Contains t' u) ↔
      (∃ u, AttackOcc k u ∧ Contains t u) := by
  rw [← attackClosureB_iff hdn k, ← attackClosureB_iff hdn' k',
    attackClosureB_trAttack hsym hlm hk ht]

/-! ### The bridge-level restatement -/

section Bridge
variable {κ lam : Instance.Context}

/-- T8's attack hypotheses restated on the source language: the target's
declared attacks are exactly the transports of the source's. This is the
bridge-contract-level `AttackBridge` of T8 limitation 1 (#238): its clauses
mention programs' `args`/`atts`, never compiled edge indices. -/
structure AttackBridge (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Prop where
  admits : Admits m lm w v
  matched : ∀ t', t' ∈ v.unit.program.args →
    ∃ t, t ∈ w.unit.program.args ∧ trSupport m lm t = some t'
  atts_eq : trAttackList m lm w.unit.program.atts = some v.unit.program.atts

/-- The index-level attack clauses follow: an `AttackBridge` between
injectively translated worlds is a `StatusBridge`. -/
theorem AttackBridge.toStatusBridge {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} (hsym : m.Injective)
    (hlm : Function.Injective lm) (h : AttackBridge m lm w v) :
    StatusBridge m lm w v := by
  refine ⟨h.admits, h.matched, ?_, ?_⟩
  · intro i j k hC hE
    obtain ⟨ti, tj, hti, htj, htr⟩ := hC
    have hk := ((edgeB_faithful w.unit.program).ranged k i hE).1
    obtain ⟨tk, htk⟩ : ∃ tk, w.unit.program.args[k]? = some tk :=
      ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨tk', htktr, hmem⟩ := h.admits tk (List.mem_of_getElem? htk)
    obtain ⟨k', htk'⟩ := List.mem_iff_getElem?.mp hmem
    refine ⟨k', ⟨tk, tk', htk, htk', htktr⟩, ?_⟩
    have hw : coveredB w.unit.program.atts tk ti = true := by
      unfold edgeB at hE
      rw [htk, hti] at hE
      exact hE
    have hv : edgeB v.unit.program k' j =
        coveredB v.unit.program.atts tk' tj := by
      unfold edgeB
      rw [htk', htj]
    rw [hv, coveredB_trAttack hsym hlm h.atts_eq htktr htr]
    exact hw
  · intro i j k' hC hE
    obtain ⟨ti, tj, hti, htj, htr⟩ := hC
    have hk' := ((edgeB_faithful v.unit.program).ranged k' j hE).1
    obtain ⟨tk', htk'⟩ : ∃ tk', v.unit.program.args[k']? = some tk' :=
      ⟨_, List.getElem?_eq_getElem hk'⟩
    obtain ⟨tk, hmem, htktr⟩ := h.matched tk' (List.mem_of_getElem? htk')
    obtain ⟨k, htk⟩ := List.mem_iff_getElem?.mp hmem
    refine ⟨k, ⟨tk, tk', htk, htk', htktr⟩, ?_⟩
    have hv : coveredB v.unit.program.atts tk' tj = true := by
      unfold edgeB at hE
      rw [htk', htj] at hE
      exact hE
    have hw : edgeB w.unit.program k i =
        coveredB w.unit.program.atts tk ti := by
      unfold edgeB
      rw [htk, hti]
    rw [hw, ← coveredB_trAttack hsym hlm h.atts_eq htktr htr]
    exact hv

end Bridge
end Lara.PW
