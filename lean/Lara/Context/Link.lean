/-
# Theory M4, phase F1 — the linking calculus

The theorems of the fragment/linking carrier frozen in `Lara.Context.Fragment`:
the guard's characterization lemmas, the conclusion cache's soundness and
completeness, the saturation's coverage and typing, and the two results the
milestone's headline rests on —

* `link_attackComplete`: the linked attack list satisfies `Compile.AttackComplete`,
  the all-pairs condition `Check.Unit.checkUnit_complete` demands; and
* `link_checked`: a well-linked composition of two well-formed sides is accepted
  by the executable checker.

The structural merge's semantic inertness (D3) is proved separately, in
`Lara.Context.Merge`, because it needs an argumentation-framework morphism and
not linking vocabulary.
-/

import Lara.Context.Fragment

namespace Lara.Context

open Lara.Support Lara.Attack Lara.Compile

/-! ### The structural merge -/

variable {α : Type} [DecidableEq α]

/-- The merge keeps exactly the declared elements. -/
theorem mem_dedupList {x : α} : ∀ {xs : List α}, x ∈ dedupList xs ↔ x ∈ xs
  | [] => by simp [dedupList]
  | v :: vs => by
      simp only [dedupList, List.mem_cons]
      by_cases h : v ∈ dedupList vs
      · rw [if_pos h]
        constructor
        · exact fun hx => Or.inr (mem_dedupList.mp hx)
        · rintro (rfl | hx)
          · exact h
          · exact mem_dedupList.mpr hx
      · rw [if_neg h]
        simp only [List.mem_cons]
        exact or_congr_right mem_dedupList

/-- The merge is a set: `Compile.CheckedProgram.nodup` is `Args(P)`-as-a-set,
and `Check.Unit.checkUnit_complete` takes that `Nodup` as a premise. -/
theorem dedupList_nodup : ∀ (xs : List α), (dedupList xs).Nodup
  | [] => by simp [dedupList]
  | v :: vs => by
      simp only [dedupList]
      by_cases h : v ∈ dedupList vs
      · rw [if_pos h]; exact dedupList_nodup vs
      · rw [if_neg h]; exact List.nodup_cons.mpr ⟨h, dedupList_nodup vs⟩

/-- A merge over an already duplicate-free list is the identity: the merge is
active only on a genuine cross-boundary collision. -/
theorem dedupList_eq_self : ∀ {xs : List α}, xs.Nodup → dedupList xs = xs
  | [], _ => rfl
  | v :: vs, h => by
      obtain ⟨hv, hvs⟩ := List.nodup_cons.mp h
      have hrest : dedupList vs = vs := dedupList_eq_self hvs
      simp only [dedupList, hrest, if_neg hv]

/-! ### The conclusion cache

`inferSupport_sound` and `inferSupport_complete` make the cache exactly the
graph of `HasSupport … w C []` on the declared terms — the two inverses every
saturation proof below consumes. -/

/-- **The inferred conclusion is the derivable one.** -/
theorem conclusionOf_eq_some_iff {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {w : SupportTerm} {C : Atom} :
    conclusionOf Pi Gamma reg w = some C ↔
      HasSupport canon Pi Gamma (certOkOf reg) w C [] := by
  constructor
  · intro h
    rw [conclusionOf] at h
    cases hinf : Check.inferSupport Pi Gamma reg .root w with
    | error e => rw [hinf] at h; exact absurd h (by simp)
    | ok result =>
        rw [hinf] at h; dsimp only at h
        by_cases hob : result.obligations = []
        · rw [if_pos hob] at h
          have hsound := Check.inferSupport_sound hinf
          rw [Option.some.inj h, hob] at hsound
          exact hsound
        · rw [if_neg hob] at h; exact absurd h (by simp)
  · intro h
    rw [conclusionOf, Check.inferSupport_complete h .root]
    simp

/-- **The cache is exactly the complete-support graph.** -/
theorem mem_conclusionCache {canon : String → String} {Pi : RuleId → Option Rule}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {args : List SupportTerm} {w : SupportTerm} {C : Atom} :
    (w, C) ∈ conclusionCache Pi Gamma reg args ↔
      w ∈ args ∧ HasSupport canon Pi Gamma (certOkOf reg) w C [] := by
  rw [conclusionCache, List.mem_filterMap]
  constructor
  · rintro ⟨v, hv, hres⟩
    cases hc : conclusionOf Pi Gamma reg v with
    | none => rw [hc] at hres; exact absurd hres (by simp)
    | some C' =>
        rw [hc] at hres
        have heq := Option.some.inj hres
        have hw : v = w := congrArg Prod.fst heq
        have hC : C' = C := congrArg Prod.snd heq
        subst hw; subst hC
        exact ⟨hv, conclusionOf_eq_some_iff.mp hc⟩
  · rintro ⟨hw, hsup⟩
    exact ⟨w, hw, by rw [conclusionOf_eq_some_iff.mpr hsup]; rfl⟩

/-- Cache soundness: a cached entry is a complete checked support term with
that conclusion. -/
theorem conclusionCache_sound {canon : String → String} {Pi : RuleId → Option Rule}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {args : List SupportTerm} {w : SupportTerm} {C : Atom}
    (h : (w, C) ∈ conclusionCache Pi Gamma reg args) :
    HasSupport canon Pi Gamma (certOkOf reg) w C [] :=
  (mem_conclusionCache.mp h).2

/-- Cache terms are declared terms. -/
theorem conclusionCache_terms {canon : String → String} {Pi : RuleId → Option Rule}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {args : List SupportTerm} {w : SupportTerm} {C : Atom}
    (h : (w, C) ∈ conclusionCache Pi Gamma reg args) : w ∈ args :=
  (mem_conclusionCache.mp h).1

/-! ### The guard, class by class (D3)

One characterization lemma per fault constructor, so that a proof obligation
about the guard discharges by lemma rather than by `decide` over a quadratic
scan (`native_decide` is banned). Small concrete witnesses may still use
`decide`; the lemmas are what a proof about an arbitrary link needs. -/

theorem firstDup?_none_iff : ∀ {ls : List LeafId}, firstDup? ls = none ↔ ls.Nodup
  | [] => by simp [firstDup?]
  | l :: ls => by
      simp only [firstDup?, List.nodup_cons]
      by_cases h : l ∈ ls
      · rw [if_pos h]
        exact ⟨fun hc => absurd hc (by simp), fun hnd => absurd h hnd.1⟩
      · rw [if_neg h]
        exact ⟨fun hc => ⟨h, firstDup?_none_iff.mp hc⟩,
          fun hnd => firstDup?_none_iff.mpr hnd.2⟩

theorem firstMissing?_none_iff {needed declared : List LeafId} :
    firstMissing? needed declared = none ↔ ∀ l ∈ needed, l ∈ declared := by
  rw [firstMissing?, List.find?_eq_none]
  simp

theorem firstShared?_none_iff {xs ys : List LeafId} :
    firstShared? xs ys = none ↔ ∀ l ∈ xs, l ∉ ys := by
  rw [firstShared?, List.find?_eq_none]
  simp

/-- R-L1, characterized: no side repeats an identifier and the two sides are
disjoint. -/
theorem idHygieneFault_none_iff {F G : Fragment} :
    idHygieneFault F G = none ↔
      F.declared.Nodup ∧ G.declared.Nodup ∧ ∀ l ∈ F.declared, l ∉ G.declared := by
  rw [idHygieneFault]
  cases hF : firstDup? F.declared with
  | some l =>
      simp only [reduceCtorEq, false_iff, not_and]
      intro hnd
      exact absurd (firstDup?_none_iff.mpr hnd) (by rw [hF]; simp)
  | none =>
      cases hG : firstDup? G.declared with
      | some l =>
          simp only [reduceCtorEq, false_iff, not_and]
          intro _ hnd
          exact absurd (firstDup?_none_iff.mpr hnd) (by rw [hG]; simp)
      | none =>
          cases hS : firstShared? F.declared G.declared with
          | some l =>
              simp only [reduceCtorEq, false_iff, not_and]
              intro _ _ hdisj
              exact absurd (firstShared?_none_iff.mpr hdisj) (by rw [hS]; simp)
          | none =>
              simp only [true_iff]
              exact ⟨firstDup?_none_iff.mp hF, firstDup?_none_iff.mp hG,
                firstShared?_none_iff.mp hS⟩

/-- R-L3, characterized. -/
theorem sigmaPolicyFault_none_iff {F G : Fragment} :
    sigmaPolicyFault F G = none ↔ F.sigma = G.sigma ∧ F.policy = G.policy := by
  rw [sigmaPolicyFault]
  by_cases hs : F.sigma = G.sigma
  · rw [if_neg (by simpa using hs)]
    by_cases hp : F.policy = G.policy
    · rw [if_neg (by simpa using hp)]; simp [hs, hp]
    · rw [if_pos (by simpa using hp)]; simp [hp]
  · rw [if_pos (by simpa using hs)]; simp [hs]

/-- **The guard, characterized.** Each conjunct is a named rejection class:
R-L1 (the two `Nodup` clauses and the disjointness clause), R-L2 (the two
import clauses), R-L3 (Σ and policy). -/
theorem linkOk_eq_true_iff {C : Context} {F : Fragment} :
    linkOk C F = true ↔
      C.frame.declared.Nodup ∧ F.declared.Nodup ∧
      (∀ l ∈ C.frame.declared, l ∉ F.declared) ∧
      (∀ l ∈ F.imports.leaves, l ∈ C.frame.declared) ∧
      (∀ l ∈ C.frame.imports.leaves, l ∈ F.declared) ∧
      C.frame.sigma = F.sigma ∧ C.frame.policy = F.policy := by
  rw [linkOk, Option.isNone_iff_eq_none, linkFault]
  cases hH : idHygieneFault C.frame F with
  | some fault =>
      simp only [reduceCtorEq, false_iff, not_and]
      intro hnd1 hnd2 hdisj
      exact absurd (idHygieneFault_none_iff.mpr ⟨hnd1, hnd2, hdisj⟩) (by rw [hH]; simp)
  | none =>
      obtain ⟨hnd1, hnd2, hdisj⟩ := idHygieneFault_none_iff.mp hH
      cases hI : firstMissing? F.imports.leaves C.frame.declared with
      | some l =>
          simp only [reduceCtorEq, false_iff, not_and]
          intro _ _ _ himp
          exact absurd (firstMissing?_none_iff.mpr himp) (by rw [hI]; simp)
      | none =>
          cases hI2 : firstMissing? C.frame.imports.leaves F.declared with
          | some l =>
              simp only [reduceCtorEq, false_iff, not_and]
              intro _ _ _ _ himp
              exact absurd (firstMissing?_none_iff.mpr himp) (by rw [hI2]; simp)
          | none =>
              rw [sigmaPolicyFault_none_iff]
              constructor
              · rintro ⟨hs, hp⟩
                exact ⟨hnd1, hnd2, hdisj, firstMissing?_none_iff.mp hI,
                  firstMissing?_none_iff.mp hI2, hs, hp⟩
              · rintro ⟨-, -, -, -, -, hs, hp⟩
                exact ⟨hs, hp⟩

/-- The unit and Γ a successful link produces. -/
theorem link_eq_some {canon : String → String} {reg : BackendRegistry canon}
    {C : Context} {F : Fragment} (h : linkOk C F = true) :
    link reg C F = some (linkedUnit reg C F, linkGamma C F) := by
  simp only [link, if_pos h]

/-- A link the guard rejects produces nothing, and the fault says which class
rejected it. -/
theorem link_eq_none {canon : String → String} {reg : BackendRegistry canon}
    {C : Context} {F : Fragment} (h : linkOk C F = false) :
    link reg C F = none := by
  simp only [link, h, Bool.false_eq_true, if_false]

/-- A rejected link carries a fault witness. -/
theorem exists_fault_of_not_linkOk {C : Context} {F : Fragment}
    (h : linkOk C F = false) : ∃ fault, linkFault C F = some fault := by
  rw [linkOk, Bool.eq_false_iff, Ne, Option.isNone_iff_eq_none] at h
  exact Option.ne_none_iff_exists'.mp h

/-! ### The cache bridge

`conclusionCache` infers conclusions *before* checking, under the hypothetical
linked Γ; `Check.conflictCache` reads them off `Unit.CheckedUnit.nodes` *after*
acceptance. They are the same idea computed at two different times, and the
saturation `link` performs is the one the checker would have computed exactly
when the two agree. They do, and on the nose: on any accepted unit the inferred
cache over the program's arguments *is* the `(term, conclusion)` projection of
the conflict cache, because `conclusionOf_eq_some_iff` makes the inferred
conclusion the derivable one and every checked node carries its derivation.
Nothing in the saturation proofs consumes this — they use the two inverses
above — so it is a statement about the calculus rather than about any one
proof. -/

/-- The inferred cache over the terms of checked nodes is those nodes'
`(term, conclusion)` pairs. -/
theorem conclusionCache_of_nodes {canon : String → String} {Pi : RuleId → Option Rule}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    (nodes : List (Compile.CheckedNode canon Pi Gamma (certOkOf reg))) :
    conclusionCache Pi Gamma reg (nodes.map (·.term))
      = nodes.map (fun n => (n.term, n.conclusion)) := by
  induction nodes with
  | nil => rfl
  | cons n rest ih =>
      have hf : conclusionOf Pi Gamma reg n.term = some n.conclusion :=
        conclusionOf_eq_some_iff.mpr n.valid
      simp only [conclusionCache] at ih
      simp [conclusionCache, List.filterMap_cons, hf, ih]

/-- **The bridge on an accepted unit.** The conclusions `conclusionCache`
infers for the program's arguments are exactly the ones `Check.conflictCache`
records for its checked nodes, whatever attack list the scan is run against. -/
theorem conclusionCache_eq_conflictCache {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    (checked : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)) (atts : List Attack) :
    conclusionCache checked.policy.ruleLookup Gamma reg checked.program.args
      = (Check.conflictCache checked.policy.ruleLookup atts checked.nodes).map
          (fun n => (n.term, n.conclusion)) := by
  rw [Check.conflictCache_conclusions, ← checked.nodes_terms, conclusionCache_of_nodes]

/-- A successful link is the guarded pair: the guard held, and the result is
`linkedUnit` with `linkGamma`. -/
theorem link_some_inv {canon : String → String} {reg : BackendRegistry canon}
    {C : Context} {F : Fragment} {unit : Lara.Unit} {Gamma : LeafId → Option Atom}
    (hlink : link reg C F = some (unit, Gamma)) :
    linkOk C F = true ∧ unit = linkedUnit reg C F ∧ Gamma = linkGamma C F := by
  by_cases hok : linkOk C F = true
  · rw [link_eq_some hok] at hlink
    have hpair := Option.some.inj hlink
    exact ⟨hok, (congrArg Prod.fst hpair).symm, (congrArg Prod.snd hpair).symm⟩
  · rw [Bool.not_eq_true] at hok
    rw [link_eq_none hok] at hlink
    exact absurd hlink (by simp)

/-- A side's inferred cache is the restriction of the cache over any superset
of its terms. -/
theorem mem_conclusionCache_of_sub {canon : String → String} {Pi : RuleId → Option Rule}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {side args : List SupportTerm} (hsub : ∀ w ∈ side, w ∈ args)
    {w : SupportTerm} {A : Atom} :
    (w, A) ∈ conclusionCache Pi Gamma reg side ↔
      w ∈ side ∧ (w, A) ∈ conclusionCache Pi Gamma reg args := by
  rw [mem_conclusionCache, mem_conclusionCache]
  constructor
  · rintro ⟨hw, hsup⟩; exact ⟨hw, hsub w hw, hsup⟩
  · rintro ⟨hw, -, hsup⟩; exact ⟨hw, hsup⟩

/-- **The bridge on a linked program.** For a link the checker accepts, each
side's saturation cache — built under the linked Γ before checking — is the
restriction of the checker's conflict cache to that side's arguments: `(w, A)`
is in the side's inferred cache exactly when `w` is one of that side's
arguments and the accepted unit carries a checked node for `w` whose recorded
conclusion is `A`. -/
theorem link_cache_bridge {canon : String → String} {reg : BackendRegistry canon}
    {C : Context} {F : Fragment} {unit : Lara.Unit} {Gamma : LeafId → Option Atom}
    {ground : List Atom} {checked : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (hlink : link reg C F = some (unit, Gamma))
    (hcheck : Check.Unit.checkUnit Gamma reg ground unit = .ok checked)
    {side : List SupportTerm} (hside : side = C.frame.args ∨ side = F.args)
    {w : SupportTerm} {A : Atom} :
    (w, A) ∈ conclusionCache F.policy.ruleLookup Gamma reg side ↔
      w ∈ side ∧ ∃ n ∈ Check.conflictCache checked.policy.ruleLookup unit.atts checked.nodes,
        n.term = w ∧ n.conclusion = A := by
  obtain ⟨-, hunit, -⟩ := link_some_inv hlink
  have hsound := Check.Unit.checkUnit_sound hcheck
  have hpol : checked.policy = F.policy := by
    rw [hsound.policy_eq, hunit]; rfl
  have hargs : checked.program.args = dedupList (C.frame.args ++ F.args) := by
    rw [hsound.args_eq, hunit]; rfl
  have hsub : ∀ v ∈ side, v ∈ checked.program.args := by
    intro v hv
    rw [hargs, mem_dedupList, List.mem_append]
    rcases hside with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr hv
  rw [← hpol, mem_conclusionCache_of_sub hsub,
    conclusionCache_eq_conflictCache checked unit.atts, List.mem_map]
  constructor
  · rintro ⟨hw, n, hn, hpair⟩
    exact ⟨hw, n, hn, congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  · rintro ⟨hw, n, hn, hterm, hconcl⟩
    exact ⟨hw, n, hn, by rw [hterm, hconcl]⟩

/-! ### Saturation -/

theorem mem_crossAttsFrom {canon : String → String} {dp : DefeatPolicy}
    {Pi : RuleId → Option Rule} {srcs tgts : List (SupportTerm × Atom)}
    {k : Attack} :
    k ∈ crossAttsFrom canon dp Pi srcs tgts ↔
      ∃ s ∈ srcs, ∃ t ∈ tgts,
        contraryMatchB canon dp s.2 t.2 = true ∧
        conflictAttackableB Pi t.1 = true ∧ k = attackFor s.1 t.1 := by
  simp only [crossAttsFrom, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, t, ht, hres⟩
    by_cases hcond : contraryMatchB canon dp s.2 t.2 && conflictAttackableB Pi t.1
    · rw [if_pos hcond] at hres
      rw [Bool.and_eq_true] at hcond
      exact ⟨s, hs, t, ht, hcond.1, hcond.2, (Option.some.inj hres).symm⟩
    · rw [if_neg hcond] at hres; exact absurd hres (by simp)
  · rintro ⟨s, hs, t, ht, hcm, hca, rfl⟩
    refine ⟨s, hs, t, ht, ?_⟩
    rw [if_pos (by rw [Bool.and_eq_true]; exact ⟨hcm, hca⟩)]

/-- The emitted attack is sourced where the pair says. -/
theorem attackFor_source (s t : SupportTerm) : (attackFor s t).source = s := by
  cases t <;> rfl

/-- The emitted attack's target is the pair's target. -/
theorem attackFor_target (s t : SupportTerm) : (attackFor s t).target = t := by
  cases t <;> rfl

/-- The emitted attack's attacked occurrence is the target itself, so
`Compile.Covered` holds through `Compile.contains_refl`. -/
theorem attackOcc_attackFor (s t : SupportTerm) : AttackOcc (attackFor s t) t := by
  cases t with
  | leaf l => exact rfl
  | inst rn θ ws D H α => exact rfl

/-- One emitted attack covers its pair, inside any attack list containing it. -/
theorem covered_of_mem_attackFor {atts : List Attack} {s t : SupportTerm}
    (h : attackFor s t ∈ atts) : Covered atts s t :=
  ⟨attackFor s t, h, attackFor_source s t, t, attackOcc_attackFor s t,
    contains_refl t⟩

/-- Coverage is monotone in the attack list: a link never loses a side's own
declared coverage by appending the other side's attacks and the saturation. -/
theorem covered_mono {atts atts' : List Attack} {s t : SupportTerm}
    (hsub : ∀ k ∈ atts, k ∈ atts') (h : Covered atts s t) : Covered atts' s t := by
  obtain ⟨k, hk, hsrc, occ, hocc, hcont⟩ := h
  exact ⟨k, hsub k hk, hsrc, occ, hocc, hcont⟩

/-! ### The typing of an emitted attack

`HasAttack` is the premise `Check.Unit.checkUnit_complete` takes for every
declared attack, so saturation is sound only if every attack it emits types.
Both shapes read their target-side premise off the target's own support
derivation — `Support.hasSupport_inst_root` for a rebut, the
`Support.hasSupport_leaf_gamma` Γ lookup for an undermine. -/

/-- **Every emitted cross-boundary attack types.** -/
theorem hasAttack_attackFor {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {dp : DefeatPolicy} {s t : SupportTerm} {Cs Ct : Atom}
    {Os : List QuestionId}
    (hs : HasSupport canon Pi Gamma CertOk s Cs Os)
    (ht : HasSupport canon Pi Gamma CertOk t Ct [])
    (hcm : ContraryMatch canon dp Cs Ct)
    (hca : ConflictAttackable Pi t) :
    HasAttack canon Pi Gamma CertOk dp (attackFor s t) := by
  cases t with
  | leaf l =>
      exact HasAttack.undermine hs rfl (hasSupport_leaf_gamma ht) hcm
  | inst rn θ ws D H α =>
      obtain ⟨r, hrule, hconcl⟩ := hasSupport_inst_root ht
      obtain ⟨r', hrule', hdef⟩ := hca
      rw [Option.some.inj (hrule'.symm.trans hrule)] at hdef
      exact HasAttack.rebut hs hrule hdef hconcl hcm

section Linked

variable {canon : String → String} {reg : BackendRegistry canon}
  {C : Context} {F : Fragment}

/-- Abbreviation for the linked Γ under discussion. -/
local notation "Γ" => linkGamma C F

/-- Every saturation attack types, and is sourced and targeted at a declared
argument of the link. -/
theorem crossAttsFrom_spec
    {srcs tgts : List (SupportTerm × Atom)} {args : List SupportTerm}
    (hsrcs : ∀ p ∈ srcs, p.1 ∈ args ∧
      HasSupport canon F.policy.ruleLookup Γ (certOkOf reg) p.1 p.2 [])
    (htgts : ∀ p ∈ tgts, p.1 ∈ args ∧
      HasSupport canon F.policy.ruleLookup Γ (certOkOf reg) p.1 p.2 [])
    {k : Attack}
    (hk : k ∈ crossAttsFrom canon F.policy.defeat F.policy.ruleLookup srcs tgts) :
    HasAttack canon F.policy.ruleLookup Γ (certOkOf reg) F.policy.defeat k ∧
      k.source ∈ args ∧ k.target ∈ args := by
  obtain ⟨s, hs, t, ht, hcm, hca, rfl⟩ := mem_crossAttsFrom.mp hk
  obtain ⟨hsArgs, hsSup⟩ := hsrcs s hs
  obtain ⟨htArgs, htSup⟩ := htgts t ht
  refine ⟨hasAttack_attackFor hsSup htSup
      ((contraryMatchB_iff canon F.policy.defeat s.2 t.2).mp hcm)
      ((conflictAttackableB_iff F.policy.ruleLookup t.1).mp hca), ?_, ?_⟩
  · rw [attackFor_source]; exact hsArgs
  · rw [attackFor_target]; exact htArgs

/-- The two caches a link saturates over sit inside the linked argument list. -/
theorem cache_spec_left :
    ∀ p ∈ conclusionCache F.policy.ruleLookup Γ reg C.frame.args,
      p.1 ∈ dedupList (C.frame.args ++ F.args) ∧
        HasSupport canon F.policy.ruleLookup Γ (certOkOf reg) p.1 p.2 [] := by
  intro p hp
  obtain ⟨hmem, hsup⟩ := mem_conclusionCache.mp (by simpa using hp)
  exact ⟨mem_dedupList.mpr (List.mem_append_left _ hmem), hsup⟩

theorem cache_spec_right :
    ∀ p ∈ conclusionCache F.policy.ruleLookup Γ reg F.args,
      p.1 ∈ dedupList (C.frame.args ++ F.args) ∧
        HasSupport canon F.policy.ruleLookup Γ (certOkOf reg) p.1 p.2 [] := by
  intro p hp
  obtain ⟨hmem, hsup⟩ := mem_conclusionCache.mp (by simpa using hp)
  exact ⟨mem_dedupList.mpr (List.mem_append_right _ hmem), hsup⟩

/-- **Every attack the saturation emits types**, and both its endpoints are
declared arguments of the link. -/
theorem crossAtts_spec {k : Attack} (hk : k ∈ crossAtts reg Γ C F) :
    HasAttack canon F.policy.ruleLookup Γ (certOkOf reg) F.policy.defeat k ∧
      k.source ∈ dedupList (C.frame.args ++ F.args) ∧
      k.target ∈ dedupList (C.frame.args ++ F.args) := by
  rw [crossAtts, List.mem_append] at hk
  rcases hk with h | h
  · exact crossAttsFrom_spec cache_spec_left cache_spec_right h
  · exact crossAttsFrom_spec cache_spec_right cache_spec_left h

/-- **Saturation covers every cross-boundary conflict.** The pair whose
conclusions contrary-match onto an attackable target is covered by the attack
the link emits for it. -/
theorem crossAtts_covers
    {source target : SupportTerm} {Cs Ct : Atom}
    (hsrc : source ∈ C.frame.args) (htgt : target ∈ F.args)
    (hsSup : HasSupport canon F.policy.ruleLookup Γ (certOkOf reg) source Cs [])
    (htSup : HasSupport canon F.policy.ruleLookup Γ (certOkOf reg) target Ct [])
    (hcm : ContraryMatch canon F.policy.defeat Cs Ct)
    (hca : ConflictAttackable F.policy.ruleLookup target) :
    Covered (crossAtts reg Γ C F) source target := by
  refine covered_of_mem_attackFor ?_
  rw [crossAtts, List.mem_append]
  refine Or.inl (mem_crossAttsFrom.mpr ⟨(source, Cs), ?_, (target, Ct), ?_, ?_, ?_, rfl⟩)
  · exact mem_conclusionCache.mpr ⟨hsrc, hsSup⟩
  · exact mem_conclusionCache.mpr ⟨htgt, htSup⟩
  · exact (contraryMatchB_iff canon F.policy.defeat Cs Ct).mpr hcm
  · exact (conflictAttackableB_iff F.policy.ruleLookup target).mpr hca

/-- The mirror direction: a fragment argument attacking a context argument. -/
theorem crossAtts_covers' {source target : SupportTerm} {Cs Ct : Atom}
    (hsrc : source ∈ F.args) (htgt : target ∈ C.frame.args)
    (hsSup : HasSupport canon F.policy.ruleLookup Γ (certOkOf reg) source Cs [])
    (htSup : HasSupport canon F.policy.ruleLookup Γ (certOkOf reg) target Ct [])
    (hcm : ContraryMatch canon F.policy.defeat Cs Ct)
    (hca : ConflictAttackable F.policy.ruleLookup target) :
    Covered (crossAtts reg Γ C F) source target := by
  refine covered_of_mem_attackFor ?_
  rw [crossAtts, List.mem_append]
  refine Or.inr (mem_crossAttsFrom.mpr ⟨(source, Cs), ?_, (target, Ct), ?_, ?_, ?_, rfl⟩)
  · exact mem_conclusionCache.mpr ⟨hsrc, hsSup⟩
  · exact mem_conclusionCache.mpr ⟨htgt, htSup⟩
  · exact (contraryMatchB_iff canon F.policy.defeat Cs Ct).mpr hcm
  · exact (conflictAttackableB_iff F.policy.ruleLookup target).mpr hca

end Linked

/-! ### Γ transport

Γ is what the two sides contribute, so every judgment about a side has to move
from the side's own environment into the linked one. The transport itself is
generic: `Support.hasSupport_mono_gamma` and `Attack.hasAttack_mono_gamma`
carry derivations across a Γ extension, `Support.hasSupport_unique`
(`Support.lean`) is the uniqueness fact several proofs below consume, and the
`Admission.buildGamma_*` facts say how the linked environment extends each
side's own. All of them are public at their owning modules;
nothing here re-proves them. -/

/-- The linked Γ extends the context's own environment. -/
theorem linkGamma_extends_left {C : Context} {F : Fragment} :
    ∀ l p, Admission.buildGamma C.frame.gammaFrag l = some p → linkGamma C F l = some p :=
  fun _ _ h => Admission.buildGamma_append_of_some _ _ h

/-- The linked Γ extends the fragment's own environment. Hygiene is what makes
this direction true: `buildGamma` is first-wins, and R-L1 has ruled out a leaf
declared by both sides. -/
theorem linkGamma_extends_right {C : Context} {F : Fragment}
    (hok : linkOk C F = true) :
    ∀ l p, Admission.buildGamma F.gammaFrag l = some p → linkGamma C F l = some p := by
  intro l p h
  obtain ⟨-, -, hdisj, -, -, -, -⟩ := linkOk_eq_true_iff.mp hok
  have hmem : l ∈ F.declared := Admission.buildGamma_some_mem h
  have hfresh : l ∉ C.frame.declared := fun hc => hdisj l hc hmem
  rw [linkGamma, Admission.buildGamma_append_fresh _ _ hfresh]
  exact h

/-! ### The signature stage of a link

`Check.Unit.signatureStage` is four independent guards and every one of them
decomposes over a link: Σ and the policy are shared (R-L3 saw to that), the
ground list is the concatenation of the two sides', and the argument list is
their structural merge. So `link_checked`'s stage-2 premise is per-side data
after all. -/

theorem groundWellSorted_append (sg : Sigma.Sigma) (a b : List Atom) :
    Lara.groundWellSorted sg (a ++ b)
      = (Lara.groundWellSorted sg a && Lara.groundWellSorted sg b) := by
  simp [Lara.groundWellSorted, List.all_append]

theorem termsWellSorted_iff_mem (sg : Sigma.Sigma) (P : Policy.Policy) :
    ∀ l : List SupportTerm,
      Lara.termsWellSorted sg P l = true ↔ ∀ w ∈ l, Lara.termWellSorted sg P w = true
  | [] => by simp [Lara.termsWellSorted]
  | w :: ws => by
      simp only [Lara.termsWellSorted, Bool.and_eq_true, List.mem_cons,
        termsWellSorted_iff_mem sg P ws]
      constructor
      · rintro ⟨hw, hws⟩ v (rfl | hv)
        · exact hw
        · exact hws v hv
      · intro h
        exact ⟨h w (Or.inl rfl), fun v hv => h v (Or.inr hv)⟩

/-- **The linked argument list is well-sorted when both sides are.** The merge
only removes terms, so nothing new has to be checked. -/
theorem argsWellSorted_link {sg : Sigma.Sigma} {P : Policy.Policy}
    {C : Context} {F : Fragment}
    (hC : Lara.argsWellSorted sg P C.frame.args = true)
    (hF : Lara.argsWellSorted sg P F.args = true) :
    Lara.argsWellSorted sg P (dedupList (C.frame.args ++ F.args)) = true := by
  rw [Lara.argsWellSorted, termsWellSorted_iff_mem]
  intro w hw
  rcases List.mem_append.mp (mem_dedupList.mp hw) with h | h
  · exact (termsWellSorted_iff_mem sg P C.frame.args).mp hC w h
  · exact (termsWellSorted_iff_mem sg P F.args).mp hF w h

/-- **The signature stage of a link, from per-side data.** -/
theorem signatureStage_link {canon : String → String} {reg : BackendRegistry canon}
    {C : Context} {F : Fragment}
    (hsigma : Sigma.sigmaWellFormed F.sigma = true)
    (hpolicy : Lara.policyWellSorted F.sigma F.policy = true)
    (hgroundC : Lara.groundWellSorted F.sigma C.frame.ground = true)
    (hgroundF : Lara.groundWellSorted F.sigma F.ground = true)
    (hargsC : Lara.argsWellSorted F.sigma F.policy C.frame.args = true)
    (hargsF : Lara.argsWellSorted F.sigma F.policy F.args = true) :
    Check.Unit.signatureStage (linkGround C F) (linkedUnit reg C F) = none := by
  show Check.Unit.signatureStage (C.frame.ground ++ F.ground) _ = none
  rw [Check.Unit.signatureStage, if_neg (by simp [linkedUnit, hsigma]),
    if_neg (by simp [linkedUnit, hpolicy]),
    if_neg (by simp [groundWellSorted_append, hgroundC, hgroundF, linkedUnit]),
    if_neg (by simp [linkedUnit, argsWellSorted_link hargsC hargsF])]

/-! ### Attack completeness of a link -/

/-- **A side is linkable**: its declared material is well-formed *relative to
the linked Γ*. Γ is what the two sides contribute, so every judgment about a
side has to be read under the extended environment;
`hasSupport_mono_gamma`/`hasAttack_mono_gamma` above are what carry a side's own
derivations into this form. -/
structure SideOk (canon : String → String) (reg : BackendRegistry canon)
    (Gamma : LeafId → Option Atom) (P : Policy.Policy)
    (args : List SupportTerm) (atts : List Attack) : Prop where
  /-- every declared argument is complete checked support -/
  support : ∀ w ∈ args, ∃ C, HasSupport canon P.ruleLookup Gamma (certOkOf reg) w C []
  /-- every declared attack types -/
  typed : ∀ k ∈ atts, HasAttack canon P.ruleLookup Gamma (certOkOf reg) P.defeat k
  /-- attack endpoints are declared -/
  source_declared : ∀ k ∈ atts, k.source ∈ args
  target_declared : ∀ k ∈ atts, k.target ∈ args
  /-- the side's own conflicts are covered by the side's own attacks -/
  attack_complete :
    Compile.AttackComplete canon P.ruleLookup Gamma (certOkOf reg) P.defeat args atts

/-- **A side's well-formedness transports into the linked environment.** The
four structural fields move by monotonicity; attack completeness moves because
a checked term has one conclusion (`hasSupport_unique`), so the conflicts
visible under the extended Γ are the conflicts the side already covered. -/
theorem SideOk.mono_gamma {canon : String → String} {reg : BackendRegistry canon}
    {Gamma Gamma' : LeafId → Option Atom} {P : Policy.Policy}
    {args : List SupportTerm} {atts : List Attack}
    (hext : ∀ l p, Gamma l = some p → Gamma' l = some p)
    (h : SideOk canon reg Gamma P args atts) :
    SideOk canon reg Gamma' P args atts where
  support := by
    intro w hw
    obtain ⟨C, hC⟩ := h.support w hw
    exact ⟨C, hasSupport_mono_gamma hext hC⟩
  typed := fun k hk => hasAttack_mono_gamma hext (h.typed k hk)
  source_declared := h.source_declared
  target_declared := h.target_declared
  attack_complete := by
    intro source hs target ht Cs Ct hsSup htSup hcm hca
    obtain ⟨Cs', hCs'⟩ := h.support source hs
    obtain ⟨Ct', hCt'⟩ := h.support target ht
    have hCsEq : Cs' = Cs :=
      (hasSupport_unique (hasSupport_mono_gamma hext hCs') hsSup).1
    have hCtEq : Ct' = Ct :=
      (hasSupport_unique (hasSupport_mono_gamma hext hCt') htSup).1
    exact h.attack_complete source hs target ht Cs' Ct' hCs' hCt'
      (by rw [hCsEq, hCtEq]; exact hcm) hca

/-! ### The fragment-relative carrier (D10) -/

/-- **The fragment's own framework is the compiled AF of its own accepted
program.** `fragmentCarrier` keeps the conclusion labelling so that a
fragment's exports can be read off it; forgetting the labelling recovers
exactly `Compile.checkedAF`. -/
theorem fragmentAF_eq {canon : String → String} {reg : BackendRegistry canon}
    {F : Fragment} {env : ImportEnv}
    {accepted : Lara.Unit.CheckedUnit canon (fragmentGamma F env) (certOkOf reg)}
    (hfault : fragmentEnvFault F env = none)
    (h : Check.Unit.checkUnit (fragmentGamma F env) reg (fragmentGround F env)
      (fragmentUnit F) = .ok accepted) :
    fragmentAF reg F env = some (Compile.checkedAF accepted.program) := by
  rw [fragmentAF, fragmentCarrier, hfault, h]
  exact congrArg some (Invariants.erase_compileUnit accepted)

section Linked

variable {canon : String → String} {reg : BackendRegistry canon}
  {C : Context} {F : Fragment}

/-- **Attack completeness of a link (T1).** `Compile.AttackComplete` is an
all-pairs condition and a premise of `Check.Unit.checkUnit_complete`, so a link
that merely concatenated the two attack lists could not be checked. With the
saturation it holds: within-side pairs are covered by the side's own attacks,
cross-boundary pairs by `crossAtts`. -/
theorem link_attackComplete
    (hC : SideOk canon reg (linkGamma C F) F.policy C.frame.args C.frame.atts)
    (hF : SideOk canon reg (linkGamma C F) F.policy F.args F.atts) :
    Compile.AttackComplete canon F.policy.ruleLookup (linkGamma C F) (certOkOf reg)
      F.policy.defeat (dedupList (C.frame.args ++ F.args))
      (C.frame.atts ++ F.atts ++ crossAtts reg (linkGamma C F) C F) := by
  intro source hsource target htarget Cs Ct hsSup htSup hcm hca
  have hleft : ∀ k ∈ C.frame.atts,
      k ∈ C.frame.atts ++ F.atts ++ crossAtts reg (linkGamma C F) C F := by
    intro k hk; exact List.mem_append_left _ (List.mem_append_left _ hk)
  have hmid : ∀ k ∈ F.atts,
      k ∈ C.frame.atts ++ F.atts ++ crossAtts reg (linkGamma C F) C F := by
    intro k hk; exact List.mem_append_left _ (List.mem_append_right _ hk)
  have hcross : ∀ k ∈ crossAtts reg (linkGamma C F) C F,
      k ∈ C.frame.atts ++ F.atts ++ crossAtts reg (linkGamma C F) C F := by
    intro k hk; exact List.mem_append_right _ hk
  rcases List.mem_append.mp (mem_dedupList.mp hsource) with hs | hs <;>
    rcases List.mem_append.mp (mem_dedupList.mp htarget) with ht | ht
  · exact covered_mono hleft
      (hC.attack_complete source hs target ht Cs Ct hsSup htSup hcm hca)
  · exact covered_mono hcross (crossAtts_covers hs ht hsSup htSup hcm hca)
  · exact covered_mono hcross (crossAtts_covers' hs ht hsSup htSup hcm hca)
  · exact covered_mono hmid
      (hF.attack_complete source hs target ht Cs Ct hsSup htSup hcm hca)

/-- **A well-linked composition is accepted (T1/T2).** Every premise of
`Check.Unit.checkUnit_complete` is discharged from the two sides' linkability
plus the guard except four explicit checker premises. `hargs` comes from the
merge's `Nodup`, `hattackComplete` from `link_attackComplete`, and the
saturation's typing from `crossAtts_spec`.

The signature-stage result and three policy premises stay hypotheses:
`hsignature` covers Σ/policy/ground/argument sorting; `hscope`, `hruleIds`, and
`hpolicy` cover scope, rule-identifier uniqueness, and policy well-formedness.
No structural property of linking can supply them. -/
theorem link_checked {unit : Lara.Unit} {Gamma : LeafId → Option Atom}
    (hlink : link reg C F = some (unit, Gamma))
    (hsignature : Check.Unit.signatureStage (linkGround C F) unit = none)
    (hscope : Policy.firstOutOfScope? F.policy = none)
    (hruleIds : (F.policy.rules.map (·.id)).Nodup)
    (hpolicy : Policy.WellFormed canon F.policy)
    (hC : SideOk canon reg (linkGamma C F) F.policy C.frame.args C.frame.atts)
    (hF : SideOk canon reg (linkGamma C F) F.policy F.args F.atts) :
    ∃ accepted, Check.Unit.checkUnit Gamma reg (linkGround C F) unit = .ok accepted := by
  by_cases hok : linkOk C F = true
  · rw [link_eq_some hok] at hlink
    have hpair := Option.some.inj hlink
    have hunit : unit = linkedUnit reg C F := (congrArg Prod.fst hpair).symm
    have hgamma : Gamma = linkGamma C F := (congrArg Prod.snd hpair).symm
    subst hunit; subst hgamma
    refine Check.Unit.checkUnit_complete hsignature hscope hruleIds hpolicy
      (dedupList_nodup _) ?_ ?_ ?_ ?_ (link_attackComplete hC hF)
    · intro w hw
      rcases List.mem_append.mp (mem_dedupList.mp hw) with h | h
      · exact hC.support w h
      · exact hF.support w h
    · intro k hk
      rcases List.mem_append.mp hk with h | h
      · rcases List.mem_append.mp h with h' | h'
        · exact hC.typed k h'
        · exact hF.typed k h'
      · exact (crossAtts_spec h).1
    · intro k hk
      rcases List.mem_append.mp hk with h | h
      · rcases List.mem_append.mp h with h' | h'
        · exact mem_dedupList.mpr (List.mem_append_left _ (hC.source_declared k h'))
        · exact mem_dedupList.mpr (List.mem_append_right _ (hF.source_declared k h'))
      · exact (crossAtts_spec h).2.1
    · intro k hk
      rcases List.mem_append.mp hk with h | h
      · rcases List.mem_append.mp h with h' | h'
        · exact mem_dedupList.mpr (List.mem_append_left _ (hC.target_declared k h'))
        · exact mem_dedupList.mpr (List.mem_append_right _ (hF.target_declared k h'))
      · exact (crossAtts_spec h).2.2
  · rw [Bool.not_eq_true] at hok
    rw [link_eq_none hok] at hlink
    exact absurd hlink (by simp)

end Linked

end Lara.Context
