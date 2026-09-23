/-
# Multi-artifact maps, part 2b — the batch link the drivers run

`Lara.Map.Link` proves the linking results for the N-member **fold**: each
`linkStep` merges one member into the side accumulated so far and saturates only
the boundary between the two. Neither driver builds a map that way. Both merge
every member's arguments into one list and then saturate **all pairs at once**,
over one conclusion cache computed under the fully merged Γ — `crossMemberAttacks`
on the Haskell side, and on the Lean side `Lara.Map.Driver.generatedAttacksOf`,
which calls `crossPairs` below. This module is that construction and its
acceptance theorem, so the mechanization is about the unit the drivers check
rather than about a neighbouring one.

## The construction

A member is an `(alias, Fragment)` pair. `crossPairs` is the one saturation
function: for every ordered pair of cached `(term, conclusion)` entries that the
`cross` predicate admits, whose conclusions contrary-match, and whose target is
conflict-attackable, it emits `Lara.Context.attackFor`. `cross` is a parameter
because the two drivers decide "these two arguments come from different
members" from their own bookkeeping; `ownedApart` is the reference predicate —
some member declared the source and a member with a *different alias* declared
the target — and `Lara.Map.Driver.crossMember_ownersOf_iff` shows the Lean
driver's owner lists decide exactly that.

## What is proved

* `batch_checked` — the batch unit is accepted by the executable checker. It is
  stated for **any** argument list and attack list with the right *members*,
  not for one spelling of them: the drivers merge terms in first-occurrence order
  and deduplicate attacks, `Lara.Context.dedupList` keeps last occurrences, and
  every premise of `Check.Unit.checkUnit_complete` is membership-based, so a
  statement up to membership is the one that applies to the drivers' exact unit.
  The premises are `linkMembers_checked`'s, adapted: each member well-formed
  under its own Γ, pairwise-distinct aliases, duplicate-free declared leaves
  across the whole map, a `cross` predicate that admits every differently-owned
  pair, and the four checker premises no structural property of linking can
  supply.
* `mem_crossPairs_iff_emits` — the batch saturation emits exactly the attacks
  `Emits` describes. `Emits` is stated once, for both constructions, and
  `Lara.Map.Link.linkMembers_emits` shows the fold emits the same set: that is
  the fold/batch agreement the issue asks for.

The cross-member restriction is what makes the "same member" case safe: a pair
whose two terms are both declared by one member is covered by that member's own
`SideOk.attack_complete`, so the saturation never has to emit it.
-/

import Lara.Context.Link

namespace Lara.Map

open Lara.Support Lara.Attack Lara.Compile
open Lara.Context

/-! ### The batch saturation -/

/-- **The batch saturation.** Every attack a conflict forces between two cached
arguments the `cross` predicate admits, in the drivers' order: sources outer,
targets inner, both in cache order. -/
def crossPairs (canon : String → String) (dp : DefeatPolicy)
    (Pi : RuleId → Option Rule) (cross : SupportTerm → SupportTerm → Bool)
    (cache : List (SupportTerm × Atom)) : List Attack :=
  cache.flatMap fun s =>
    cache.filterMap fun t =>
      if cross s.1 t.1 && contraryMatchB canon dp s.2 t.2 && conflictAttackableB Pi t.1 then
        some (attackFor s.1 t.1)
      else none

theorem mem_crossPairs {canon : String → String} {dp : DefeatPolicy}
    {Pi : RuleId → Option Rule} {cross : SupportTerm → SupportTerm → Bool}
    {cache : List (SupportTerm × Atom)} {k : Attack} :
    k ∈ crossPairs canon dp Pi cross cache ↔
      ∃ s ∈ cache, ∃ t ∈ cache, cross s.1 t.1 = true ∧
        contraryMatchB canon dp s.2 t.2 = true ∧
        conflictAttackableB Pi t.1 = true ∧ k = attackFor s.1 t.1 := by
  simp only [crossPairs, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, t, ht, hres⟩
    by_cases hcond :
        (cross s.1 t.1 && contraryMatchB canon dp s.2 t.2 && conflictAttackableB Pi t.1) = true
    · rw [if_pos hcond] at hres
      simp only [Bool.and_eq_true] at hcond
      exact ⟨s, hs, t, ht, hcond.1.1, hcond.1.2, hcond.2, (Option.some.inj hres).symm⟩
    · rw [if_neg hcond] at hres; exact absurd hres (by simp)
  · rintro ⟨s, hs, t, ht, hc, hcm, hca, rfl⟩
    refine ⟨s, hs, t, ht, ?_⟩
    rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨⟨hc, hcm⟩, hca⟩)]

section Spec

variable {canon : String → String} {reg : BackendRegistry canon} {P : Policy.Policy}
  {Γ : LeafId → Option Atom} {cross : SupportTerm → SupportTerm → Bool}
  {args : List SupportTerm}

/-- **Every attack the batch saturation emits types**, and both of its endpoints
are arguments of the list the cache was built over. -/
theorem crossPairs_spec {k : Attack}
    (hk : k ∈ crossPairs canon P.defeat P.ruleLookup cross
      (conclusionCache P.ruleLookup Γ reg args)) :
    HasAttack canon P.ruleLookup Γ (certOkOf reg) P.defeat k ∧
      k.source ∈ args ∧ k.target ∈ args := by
  obtain ⟨s, hs, t, ht, -, hcm, hca, rfl⟩ := mem_crossPairs.mp hk
  obtain ⟨hsArgs, hsSup⟩ := mem_conclusionCache.mp (show (s.1, s.2) ∈ _ from hs)
  obtain ⟨htArgs, htSup⟩ := mem_conclusionCache.mp (show (t.1, t.2) ∈ _ from ht)
  refine ⟨hasAttack_attackFor hsSup htSup
      ((contraryMatchB_iff canon P.defeat s.2 t.2).mp hcm)
      ((conflictAttackableB_iff P.ruleLookup t.1).mp hca), ?_, ?_⟩
  · rw [attackFor_source]; exact hsArgs
  · rw [attackFor_target]; exact htArgs

/-- **The batch saturation emits the attack for every admitted conflict.** -/
theorem crossPairs_emits {source target : SupportTerm} {Cs Ct : Atom}
    (hs : source ∈ args) (ht : target ∈ args)
    (hsSup : HasSupport canon P.ruleLookup Γ (certOkOf reg) source Cs [])
    (htSup : HasSupport canon P.ruleLookup Γ (certOkOf reg) target Ct [])
    (hcm : ContraryMatch canon P.defeat Cs Ct)
    (hca : ConflictAttackable P.ruleLookup target)
    (hcross : cross source target = true) :
    attackFor source target ∈ crossPairs canon P.defeat P.ruleLookup cross
      (conclusionCache P.ruleLookup Γ reg args) :=
  mem_crossPairs.mpr
    ⟨(source, Cs), mem_conclusionCache.mpr ⟨hs, hsSup⟩,
     (target, Ct), mem_conclusionCache.mpr ⟨ht, htSup⟩, hcross,
     (contraryMatchB_iff canon P.defeat Cs Ct).mpr hcm,
     (conflictAttackableB_iff P.ruleLookup target).mpr hca, rfl⟩

end Spec

/-! ### Members, their environment, and who owns what -/

/-- The batch's leaf environment: every member's declarations, in member order.
`Admission.buildGamma` is first-wins, so this is only the right environment when
no identifier is declared twice across the map — `batchGamma_extends`. -/
def batchGamma (pairs : List (String × Fragment)) : LeafId → Option Atom :=
  Admission.buildGamma (pairs.flatMap (·.2.gammaFrag))

/-- **The batch environment extends every member's own**, given that no leaf
identifier is declared twice across the map. This is where hygiene is consumed:
a leaf an earlier member already declared would shadow a later member's own. -/
theorem batchGamma_extends :
    ∀ {pairs : List (String × Fragment)},
      (pairs.flatMap (·.2.declared)).Nodup →
      ∀ {p : String × Fragment}, p ∈ pairs →
        ∀ l a, Admission.buildGamma p.2.gammaFrag l = some a → batchGamma pairs l = some a
  | [], _, _, hp, _, _, _ => by simp at hp
  | r :: rest, hdecl, p, hp, l, a, h => by
      rw [List.flatMap_cons] at hdecl
      have hsplit := List.nodup_append.mp hdecl
      unfold batchGamma
      rw [List.flatMap_cons]
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact Admission.buildGamma_append_of_some _ _ h
      · have hl : l ∈ p.2.declared := Admission.buildGamma_some_mem h
        have hfresh : l ∉ r.2.gammaFrag.map (·.1) := by
          intro hr
          exact hsplit.2.2 l hr l (List.mem_flatMap.mpr ⟨p, hp', hl⟩) rfl
        rw [Admission.buildGamma_append_fresh _ _ hfresh]
        exact batchGamma_extends hsplit.2.1 hp' l a h

/-- Two members with the same alias are the same member, when aliases are
pairwise distinct. -/
private theorem pair_eq_of_fst_eq {α β : Type} :
    ∀ {pairs : List (α × β)}, (pairs.map Prod.fst).Nodup →
      ∀ {p q : α × β}, p ∈ pairs → q ∈ pairs → p.1 = q.1 → p = q
  | [], _, _, _, hp, _, _ => by simp at hp
  | r :: rest, h, p, q, hp, hq, he => by
      rw [List.map_cons, List.nodup_cons] at h
      rcases List.mem_cons.mp hp with hpr | hp' <;>
        rcases List.mem_cons.mp hq with hqr | hq'
      · rw [hpr, hqr]
      · subst hpr; exact absurd (List.mem_map.mpr ⟨q, hq', he.symm⟩) h.1
      · subst hqr; exact absurd (List.mem_map.mpr ⟨p, hp', he⟩) h.1
      · exact pair_eq_of_fst_eq h.2 hp' hq' he

/-- **The reference cross-member predicate**: some member declared `s`, and a
member with a different alias declared `t`. -/
def ownedApart (pairs : List (String × Fragment)) (s t : SupportTerm) : Bool :=
  pairs.any fun p => pairs.any fun q =>
    p.1 != q.1 && p.2.args.contains s && q.2.args.contains t

theorem ownedApart_iff {pairs : List (String × Fragment)} {s t : SupportTerm} :
    ownedApart pairs s t = true ↔
      ∃ p ∈ pairs, ∃ q ∈ pairs, p.1 ≠ q.1 ∧ s ∈ p.2.args ∧ t ∈ q.2.args := by
  simp only [ownedApart, List.any_eq_true, Bool.and_eq_true, bne_iff_ne,
    List.contains_iff_mem]
  constructor
  · rintro ⟨p, hp, q, hq, ⟨hne, hs⟩, ht⟩; exact ⟨p, hp, q, hq, hne, hs, ht⟩
  · rintro ⟨p, hp, q, hq, hne, hs, ht⟩; exact ⟨p, hp, q, hq, ⟨hne, hs⟩, ht⟩

/-! ### Acceptance of the batch unit -/

/-- **The batch unit is accepted by the executable checker.**

The construction the drivers run, at the level of its members: `args` is any
duplicate-free list holding exactly the members' arguments, and `atts` any list
holding exactly the members' own attacks plus the batch saturation over the
cache of `args` under `batchGamma`. Nothing is assumed about order, which is
what lets the statement apply to both drivers' units as they are built.

The premises are the ones a map supplies. `hmembers` is each member checked on
its own, under its *own* environment. `haliases` and `hdecl` are what alias
qualification buys (`Lara.Map.Link.declared_nodup_of_qualified` discharges
`hdecl` from distinct aliases plus each member's own duplicate-freedom).
`hcross` says the cross-member predicate admits every pair two differently
aliased members declared, which `ownedApart_iff` and
`Lara.Map.Driver.crossMember_ownersOf_iff` establish for the reference predicate
and for the Lean driver's. The last four are `Lara.Context.link_checked`'s
checker premises, open here for the same reason they are open there.

Read with the members' solo acceptance, this is the mechanized reason no map of
well-formed members reaches `MRLinkRejected`: the linked unit the drivers build
is accepted. -/
theorem batch_checked {canon : String → String} {reg : BackendRegistry canon}
    {sg : Sigma.Sigma} {P : Policy.Policy}
    (pairs : List (String × Fragment)) (cross : SupportTerm → SupportTerm → Bool)
    (args : List SupportTerm) (atts : List Attack) (ground : List Atom)
    (haliases : (pairs.map Prod.fst).Nodup)
    (hdecl : (pairs.flatMap (·.2.declared)).Nodup)
    (hmembers : ∀ p ∈ pairs,
      SideOk canon reg (Admission.buildGamma p.2.gammaFrag) P p.2.args p.2.atts)
    (hcross : ∀ p ∈ pairs, ∀ q ∈ pairs, p.1 ≠ q.1 →
      ∀ s ∈ p.2.args, ∀ t ∈ q.2.args, cross s t = true)
    (hnodup : args.Nodup)
    (hargs : ∀ w, w ∈ args ↔ ∃ p ∈ pairs, w ∈ p.2.args)
    (hatts : ∀ k, k ∈ atts ↔ (∃ p ∈ pairs, k ∈ p.2.atts) ∨
      k ∈ crossPairs canon P.defeat P.ruleLookup cross
        (conclusionCache P.ruleLookup (batchGamma pairs) reg args))
    (hsignature : Check.Unit.signatureStage ground
      { sigma := sg, policy := P, args := args, atts := atts } = none)
    (hscope : Policy.firstOutOfScope? P = none)
    (hruleIds : (P.rules.map (·.id)).Nodup)
    (hpolicyWf : Policy.WellFormed canon P) :
    ∃ accepted, Check.Unit.checkUnit (batchGamma pairs) reg ground
      { sigma := sg, policy := P, args := args, atts := atts } = .ok accepted := by
  have hside : ∀ p ∈ pairs, SideOk canon reg (batchGamma pairs) P p.2.args p.2.atts :=
    fun p hp => SideOk.mono_gamma (batchGamma_extends hdecl hp) (hmembers p hp)
  refine Check.Unit.checkUnit_complete hsignature hscope hruleIds hpolicyWf hnodup
    ?_ ?_ ?_ ?_ ?_
  · intro w hw
    obtain ⟨p, hp, hwp⟩ := (hargs w).mp hw
    exact (hside p hp).support w hwp
  · intro k hk
    rcases (hatts k).mp hk with ⟨p, hp, hkp⟩ | hgen
    · exact (hside p hp).typed k hkp
    · exact (crossPairs_spec hgen).1
  · intro k hk
    rcases (hatts k).mp hk with ⟨p, hp, hkp⟩ | hgen
    · exact (hargs _).mpr ⟨p, hp, (hside p hp).source_declared k hkp⟩
    · exact (crossPairs_spec hgen).2.1
  · intro k hk
    rcases (hatts k).mp hk with ⟨p, hp, hkp⟩ | hgen
    · exact (hargs _).mpr ⟨p, hp, (hside p hp).target_declared k hkp⟩
    · exact (crossPairs_spec hgen).2.2
  · intro source hsource target htarget Cs Ct hsSup htSup hcm hca
    obtain ⟨p, hp, hsp⟩ := (hargs source).mp hsource
    obtain ⟨q, hq, htq⟩ := (hargs target).mp htarget
    by_cases hpq : p.1 = q.1
    · -- One member declares both: its own declarations cover the conflict.
      have heq : p = q := pair_eq_of_fst_eq haliases hp hq hpq
      subst heq
      exact covered_mono (fun k hk => (hatts k).mpr (Or.inl ⟨p, hp, hk⟩))
        ((hside p hp).attack_complete source hsp target htq Cs Ct hsSup htSup hcm hca)
    · -- Two members: the batch saturation emits the attack.
      exact covered_of_mem_attackFor ((hatts _).mpr (Or.inr
        (crossPairs_emits hsource htarget hsSup htSup hcm hca
          (hcross p hp q hq hpq source hsp target htq))))

/-! ### One concrete spelling of the batch unit -/

/-- The batch's arguments: every member's, structurally merged. -/
def batchArgs (pairs : List (String × Fragment)) : List SupportTerm :=
  dedupList (pairs.flatMap (·.2.args))

/-- The batch's attacks: every member's own, then the batch saturation. -/
def batchAtts {canon : String → String} (reg : BackendRegistry canon) (P : Policy.Policy)
    (cross : SupportTerm → SupportTerm → Bool) (pairs : List (String × Fragment)) :
    List Attack :=
  pairs.flatMap (·.2.atts) ++
    crossPairs canon P.defeat P.ruleLookup cross
      (conclusionCache P.ruleLookup (batchGamma pairs) reg (batchArgs pairs))

/-- The batch unit, spelled with `batchArgs` and `batchAtts`. -/
def batchUnit {canon : String → String} (reg : BackendRegistry canon) (sg : Sigma.Sigma)
    (P : Policy.Policy) (cross : SupportTerm → SupportTerm → Bool)
    (pairs : List (String × Fragment)) : Lara.Unit :=
  { sigma := sg, policy := P, args := batchArgs pairs, atts := batchAtts reg P cross pairs }

theorem mem_batchArgs {pairs : List (String × Fragment)} {w : SupportTerm} :
    w ∈ batchArgs pairs ↔ ∃ p ∈ pairs, w ∈ p.2.args := by
  rw [batchArgs, mem_dedupList, List.mem_flatMap]

theorem mem_batchAtts {canon : String → String} {reg : BackendRegistry canon}
    {P : Policy.Policy} {cross : SupportTerm → SupportTerm → Bool}
    {pairs : List (String × Fragment)} {k : Attack} :
    k ∈ batchAtts reg P cross pairs ↔ (∃ p ∈ pairs, k ∈ p.2.atts) ∨
      k ∈ crossPairs canon P.defeat P.ruleLookup cross
        (conclusionCache P.ruleLookup (batchGamma pairs) reg (batchArgs pairs)) := by
  rw [batchAtts, List.mem_append, List.mem_flatMap]

/-- `batch_checked` at the concrete spelling. -/
theorem batchUnit_checked {canon : String → String} {reg : BackendRegistry canon}
    {sg : Sigma.Sigma} {P : Policy.Policy}
    (pairs : List (String × Fragment)) (cross : SupportTerm → SupportTerm → Bool)
    (ground : List Atom)
    (haliases : (pairs.map Prod.fst).Nodup)
    (hdecl : (pairs.flatMap (·.2.declared)).Nodup)
    (hmembers : ∀ p ∈ pairs,
      SideOk canon reg (Admission.buildGamma p.2.gammaFrag) P p.2.args p.2.atts)
    (hcross : ∀ p ∈ pairs, ∀ q ∈ pairs, p.1 ≠ q.1 →
      ∀ s ∈ p.2.args, ∀ t ∈ q.2.args, cross s t = true)
    (hsignature : Check.Unit.signatureStage ground (batchUnit reg sg P cross pairs) = none)
    (hscope : Policy.firstOutOfScope? P = none)
    (hruleIds : (P.rules.map (·.id)).Nodup)
    (hpolicyWf : Policy.WellFormed canon P) :
    ∃ accepted, Check.Unit.checkUnit (batchGamma pairs) reg ground
      (batchUnit reg sg P cross pairs) = .ok accepted :=
  batch_checked pairs cross (batchArgs pairs) (batchAtts reg P cross pairs) ground
    haliases hdecl hmembers hcross (dedupList_nodup _) (fun _ => mem_batchArgs)
    (fun _ => mem_batchAtts) hsignature hscope hruleIds hpolicyWf

/-! ### What the batch saturation emits

Stated once, for both constructions, so that the fold/batch agreement
(`Lara.Map.Link.batch_atts_mem_iff_fold`) is two characterizations meeting
rather than one construction unfolded into the other. -/

/-- **What a map's saturation emits**: `attackFor s t` for a source and target
declared by two differently aliased members, whose conclusions under Γ
contrary-match onto a conflict-attackable target. -/
def Emits {canon : String → String} (reg : BackendRegistry canon) (P : Policy.Policy)
    (Γ : LeafId → Option Atom) (pairs : List (String × Fragment)) (k : Attack) : Prop :=
  ∃ p ∈ pairs, ∃ q ∈ pairs, p.1 ≠ q.1 ∧ ∃ s ∈ p.2.args, ∃ t ∈ q.2.args, ∃ Cs Ct,
    HasSupport canon P.ruleLookup Γ (certOkOf reg) s Cs [] ∧
    HasSupport canon P.ruleLookup Γ (certOkOf reg) t Ct [] ∧
    contraryMatchB canon P.defeat Cs Ct = true ∧
    conflictAttackableB P.ruleLookup t = true ∧ k = attackFor s t

/-- Emission is monotone in the member list. -/
theorem Emits.mono {canon : String → String} {reg : BackendRegistry canon}
    {P : Policy.Policy} {Γ : LeafId → Option Atom} {pairs pairs' : List (String × Fragment)}
    (hsub : ∀ p ∈ pairs, p ∈ pairs') {k : Attack} (h : Emits reg P Γ pairs k) :
    Emits reg P Γ pairs' k := by
  obtain ⟨p, hp, q, hq, hne, rest⟩ := h
  exact ⟨p, hsub p hp, q, hsub q hq, hne, rest⟩

/-- **The batch saturation emits exactly `Emits`**, for any cross-member
predicate that decides "declared by two differently aliased members" and any
argument list holding exactly the members' arguments. -/
theorem mem_crossPairs_iff_emits {canon : String → String} {reg : BackendRegistry canon}
    {P : Policy.Policy} {Γ : LeafId → Option Atom} {pairs : List (String × Fragment)}
    {cross : SupportTerm → SupportTerm → Bool} {args : List SupportTerm}
    (hcross : ∀ s t, cross s t = true ↔
      ∃ p ∈ pairs, ∃ q ∈ pairs, p.1 ≠ q.1 ∧ s ∈ p.2.args ∧ t ∈ q.2.args)
    (hargs : ∀ w, w ∈ args ↔ ∃ p ∈ pairs, w ∈ p.2.args) {k : Attack} :
    k ∈ crossPairs canon P.defeat P.ruleLookup cross (conclusionCache P.ruleLookup Γ reg args) ↔
      Emits reg P Γ pairs k := by
  constructor
  · intro hk
    obtain ⟨s, hs, t, ht, hc, hcm, hca, rfl⟩ := mem_crossPairs.mp hk
    obtain ⟨-, hsSup⟩ := mem_conclusionCache.mp (show (s.1, s.2) ∈ _ from hs)
    obtain ⟨-, htSup⟩ := mem_conclusionCache.mp (show (t.1, t.2) ∈ _ from ht)
    obtain ⟨p, hp, q, hq, hne, hsp, htq⟩ := (hcross s.1 t.1).mp hc
    exact ⟨p, hp, q, hq, hne, s.1, hsp, t.1, htq, s.2, t.2, hsSup, htSup, hcm, hca, rfl⟩
  · rintro ⟨p, hp, q, hq, hne, s, hsp, t, htq, Cs, Ct, hsSup, htSup, hcm, hca, rfl⟩
    exact mem_crossPairs.mpr
      ⟨(s, Cs), mem_conclusionCache.mpr ⟨(hargs s).mpr ⟨p, hp, hsp⟩, hsSup⟩,
       (t, Ct), mem_conclusionCache.mpr ⟨(hargs t).mpr ⟨q, hq, htq⟩, htSup⟩,
       (hcross s t).mpr ⟨p, hp, q, hq, hne, hsp, htq⟩, hcm, hca, rfl⟩

end Lara.Map
