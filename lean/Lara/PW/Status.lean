/-
# PW-T8 — conditional status preservation at structural bridges


Instantiates `Lara.PW.AFBisim` at the compiled frameworks of two Lara worlds
related by a structural bridge (`Lara.PW.Structural`). Four sections:

1. **Translation injectivity.** `SymMap.Injective` and the reflection of `≡`
   along an injective translation (`equiv_tr_reflect`). T6 gives the forward
   direction (`equiv_tr`); status needs the backward one, because a target
   argument concluding `≡ τ(c)` must come from a source argument concluding
   `≡ c` — which fails when the translation merges predicates.
2. **The T8 hypotheses.** `Corr m lm w v i j`: the `i`-th source argument
   transports to the `j`-th target argument. `StatusBridge`: T6's `Admits`
   (left-total), *matched* (every target argument is a transport —
   right-total; the clause T7 violates), and attack *forth*/*back* on the
   compiled edge decider `Compile.edgeB`. `StatusBridge.bisim` shows this is
   an `AttackBisim` of the two `checkedAF`s, and `claimSupport_corr` derives
   the complete-support correspondence for every translatable query through
   T6 transport, `hasSupport_unique`, `equiv_tr` and `equiv_tr_reflect`.
3. **T8 and its corollaries.** `status_transport`: `cmpStatus v c' =
   cmpStatus w c`. The modal reading `sat_status_iff_box`/`_dia`: under the
   hypotheses at every accepted successor, the design's guarded
   `RobustlyJustified`/`PossiblyJustified` both collapse to the local status.
4. **Composition.** `StatusBridge.comp`: the hypotheses compose along T9's
   composite bridge, through a chosen intermediate world. Statuses are values,
   so status along a path is `Eq.trans` of per-edge `status_transport`s — no
   path-indexed status theorem is needed. Note the argument order:
   `StatusBridge.comp h₁ h₂` and `SymMap.Injective.comp h₁ h₂` take the legs
   in *path* order (first leg first), while T9's `StructuralBridge.comp B₂ B₁`
   and `SymMap.comp m₂ m₁` take them in *function-composition* order.

Neither T6 nor T9 is strengthened: every theorem here takes `StatusBridge`
(or an explicit `SupportCorr`) as an extra hypothesis, and `t7_t6_boundary`
(`Lara.Examples.PWStructural`) remains the proof that `Admits` alone cannot
give any of these conclusions. The executable checker is one module up, in
`Lara.PW.StatusCheck`. This module only imports.
-/

import Lara.PW.Structural
import Lara.PW.Compose
import Lara.PW.AFBisim

namespace Lara.PW

open Lara.Support Lara.Grounded Lara.Compile Lara.PW.Instance

/-! ### §1 Translation injectivity and `≡`-reflection -/

/-- Both symbol maps are injective where defined — deliberately *not*
`Function.Injective` on the fields. `predMap`/`conMap` are partial
(`String → Option String`), so total injectivity would additionally force any
two out-of-vocabulary symbols to be equal, forbidding a translation from
leaving more than one symbol undefined. Injectivity-where-defined is what the
reflection argument actually consumes. -/
def SymMap.Injective (m : SymMap) : Prop :=
  (∀ x y z, m.predMap x = some z → m.predMap y = some z → x = y) ∧
  (∀ x y z, m.conMap x = some z → m.conMap y = some z → x = y)

/-- The identity translation is injective: every symbol is in vocabulary and
unchanged. -/
theorem SymMap.id_injective : SymMap.id.Injective :=
  ⟨fun _ _ _ hx hy => Option.some.inj (hx.trans hy.symm),
   fun _ _ _ hx hy => Option.some.inj (hx.trans hy.symm)⟩

mutual
  /-- An injective translation is injective on ground terms. -/
  theorem trTerm_inj {m : SymMap} (hm : m.Injective) :
      ∀ (t u : Term) {t' : Term}, trTerm m t = some t' → trTerm m u = some t' →
        t = u
    | .num s, u, t', ht, hu => by
        simp only [trTerm] at ht
        cases ht
        cases u with
        | num s₂ => simp only [trTerm] at hu; cases hu; rfl
        | str s₂ => simp only [trTerm] at hu; cases hu
        | con k ts => simp only [trTerm] at hu; split at hu <;> cases hu
    | .str s, u, t', ht, hu => by
        simp only [trTerm] at ht
        cases ht
        cases u with
        | num s₂ => simp only [trTerm] at hu; cases hu
        | str s₂ => simp only [trTerm] at hu; cases hu; rfl
        | con k ts => simp only [trTerm] at hu; split at hu <;> cases hu
    | .con k ts, u, t', ht, hu => by
        simp only [trTerm] at ht
        split at ht
        · next k' ts' hk hts =>
          cases ht
          cases u with
          | num s₂ => simp only [trTerm] at hu; cases hu
          | str s₂ => simp only [trTerm] at hu; cases hu
          | con k₂ ts₂ =>
            simp only [trTerm] at hu
            split at hu
            · next k₂' ts₂' hk₂ hts₂ =>
              cases hu
              have hk_eq : k = k₂ := hm.2 k k₂ k' hk hk₂
              have hts_eq : ts = ts₂ := trTerms_inj hm ts ts₂ hts hts₂
              rw [hk_eq, hts_eq]
            · cases hu
        · cases ht
  theorem trTerms_inj {m : SymMap} (hm : m.Injective) :
      ∀ (ts us : Terms) {ts' : Terms}, trTerms m ts = some ts' →
        trTerms m us = some ts' → ts = us
    | .nil, us, ts', ht, hu => by
        simp only [trTerms] at ht
        cases ht
        cases us with
        | nil => rfl
        | cons u us => simp only [trTerms] at hu; split at hu <;> cases hu
    | .cons t ts, us, ts', ht, hu => by
        simp only [trTerms] at ht
        split at ht
        · next t' ts₁' ht₁ hts₁ =>
          cases ht
          cases us with
          | nil => simp only [trTerms] at hu; cases hu
          | cons u us =>
            simp only [trTerms] at hu
            split at hu
            · next u' us' hu₁ hus =>
              cases hu
              rw [trTerm_inj hm t u ht₁ hu₁, trTerms_inj hm ts us hts₁ hus]
            · cases hu
        · cases ht
end

/-- An injective translation is injective on atoms. -/
theorem trAtom_inj {m : SymMap} (hm : m.Injective) {a b c : Atom}
    (ha : trAtom m a = some c) (hb : trAtom m b = some c) : a = b := by
  obtain ⟨p, ts⟩ := a
  obtain ⟨q, us⟩ := b
  simp only [trAtom] at ha hb
  split at ha
  · next p' ts' hp hts =>
    cases ha
    split at hb
    · next q' us' hq hus =>
      cases hb
      rw [hm.1 p q p' hp hq, trTerms_inj hm ts us hts hus]
    · cases hb
  · cases ha

/-- **`≡` reflects along an injective translation.** The converse of T6's
`equiv_tr`. `nf` commutes with translation (`trAtom_nf`), so equal target
normal forms are translations of the two source normal forms, and injectivity
identifies those. -/
theorem equiv_tr_reflect {m : SymMap} (hm : m.Injective)
    {canon : String → String} {a b a' b' : Atom}
    (ha : trAtom m a = some a') (hb : trAtom m b = some b')
    (h : equiv canon a' b') : equiv canon a b := by
  unfold equiv at h ⊢
  have h1 := trAtom_nf canon ha
  have h2 := trAtom_nf canon hb
  rw [h] at h1
  exact trAtom_inj hm h1 h2

/-! ### §2 The T8 hypotheses at a structural bridge -/

section Bridge
variable {κ lam : Instance.Context}

/-- The index relation a translation induces between two worlds' compiled
arguments: the `i`-th source argument transports to the `j`-th target
argument. Compiled arguments are list positions (`Compile.toAF`), so this is
the relation on `Grounded.Arg` the bisimulation lives on. -/
def Corr (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) (i j : Nat) : Prop :=
  ∃ t t', w.unit.program.args[i]? = some t ∧
    v.unit.program.args[j]? = some t' ∧ trSupport m lm t = some t'

/-- A `Corr`-related index pair is in range on both sides — both components
are `getElem?` hits, so each bounds its own list. -/
theorem corr_lt {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} {i j : Nat}
    (h : Corr m lm w v i j) :
    i < w.unit.program.args.length ∧ j < v.unit.program.args.length := by
  obtain ⟨t, t', ht, ht', _⟩ := h
  exact ⟨(List.getElem?_eq_some_iff.mp ht).1, (List.getElem?_eq_some_iff.mp ht').1⟩

/-- Right-totality of the translation on program arguments: every target
argument *is* a transport. The converse of T6's `Admits`, and the clause the
T7 target violates at `leaf l2` (`Lara.Examples.PW.Status.t7_unmatched`). -/
def Matched (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Prop :=
  ∀ t', t' ∈ v.unit.program.args →
    ∃ t, t ∈ w.unit.program.args ∧ trSupport m lm t = some t'

/-- **The T8 hypotheses** between two worlds under a translation `(m, lm)`.
`admits` is T6's checker-tied applicability (every source argument
transports into the target program — left-totality of `Corr`). `matched` is
its converse: every target argument *is* a transport — right-totality, the
clause that excludes unmatched target supports and attackers, and the one the
T7 target violates at `leaf l2`. `forth`/`back` are the attack conditions on
the compiled edge decider: a source attacker is matched by a target attacker
of the corresponding argument, and conversely. Nothing here is implied by the
`StructuralBridge` contract; that is the point.

**Scope, deliberately.** `forth`/`back` are *index-level* conditions on
`Compile.edgeB`. They are **not** derived from any correspondence between the
two programs' declared `atts`: doing that needs `trSupport` to commute with
`Attack.subterm`, `Compile.Contains`, `Compile.AttackOcc` and `coveredB`, an
`Erase.lean`-scale lemma set over a partial map, and is deferred to a
follow-up issue. T8's statement per the design is the AF-level
correspondence, so the clauses are stated where the design states them. A
reader should not mistake these for structural conditions on the source
language.

**Consequence when discharging the fields.** Unlike `AttackBisim.forth`/
`back`, these clauses carry no `b ∈ F.args` premise — `StatusBridge.bisim`
discards it. An instance must therefore recover in-rangeness of the attacker
index itself, via `(Compile.edgeB_faithful P).ranged`. -/
structure StatusBridge (m : SymMap) (lm : LeafId → LeafId)
    (w : World κ) (v : World lam) : Prop where
  admits : Admits m lm w v
  matched : Matched m lm w v
  forth : ∀ i j k, Corr m lm w v i j → edgeB w.unit.program k i = true →
    ∃ k', Corr m lm w v k k' ∧ edgeB v.unit.program k' j = true
  back : ∀ i j k', Corr m lm w v i j → edgeB v.unit.program k' j = true →
    ∃ k, Corr m lm w v k k' ∧ edgeB w.unit.program k i = true

/-- The hypotheses are a total attack bisimulation of the two compiled
frameworks. `checkedAF`'s carrier is `List.range` of the argument count and
its attack is `edgeB`, both by `rfl`. -/
theorem StatusBridge.bisim {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} (h : StatusBridge m lm w v) :
    AttackBisim (checkedAF w.unit.program) (checkedAF v.unit.program)
      (Corr m lm w v) where
  dom := fun i j hC =>
    ⟨List.mem_range.mpr (corr_lt hC).1, List.mem_range.mpr (corr_lt hC).2⟩
  left_total := fun i hi => by
    have hi' : i < w.unit.program.args.length := List.mem_range.mp hi
    obtain ⟨t, ht⟩ : ∃ t, w.unit.program.args[i]? = some t :=
      ⟨_, List.getElem?_eq_getElem hi'⟩
    obtain ⟨t', htr, hmem⟩ := h.admits t (List.mem_of_getElem? ht)
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
    exact ⟨j, t, t', ht, hj, htr⟩
  right_total := fun j hj => by
    have hj' : j < v.unit.program.args.length := List.mem_range.mp hj
    obtain ⟨t', ht'⟩ : ∃ t', v.unit.program.args[j]? = some t' :=
      ⟨_, List.getElem?_eq_getElem hj'⟩
    obtain ⟨t, hmem, htr⟩ := h.matched t' (List.mem_of_getElem? ht')
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
    exact ⟨i, t, t', hi, ht', htr⟩
  forth := fun i j k hC _ hE => h.forth i j k hC hE
  back := fun i j k' hC _ hE => h.back i j k' hC hE

/-- At a `Corr`-related index pair, the target node's conclusion is the
translation of the source node's. T6 transport gives *a* checked conclusion
for the transported term; `hasSupport_unique` identifies it with the target
node's own. `hcanon` is the shared-canonicalizer commitment T6 records. -/
theorem corr_conclusion (hcanon : lam.canon = κ.canon)
    (B : StructuralBridge κ.canon κ.policy.ruleLookup lam.policy.ruleLookup
      κ.Gamma lam.Gamma κ.CertOk lam.CertOk)
    {w : World κ} {v : World lam} {i j : Nat}
    (hC : Corr B.sym B.leafMap w v i j)
    {n : CheckedNode κ.canon w.unit.policy.ruleLookup κ.Gamma κ.CertOk}
    {n' : CheckedNode lam.canon v.unit.policy.ruleLookup lam.Gamma lam.CertOk}
    (hn : w.unit.nodes[i]? = some n) (hn' : v.unit.nodes[j]? = some n') :
    trAtom B.sym n.conclusion = some n'.conclusion := by
  obtain ⟨t, t', ht, ht', htr⟩ := hC
  -- the node terms are the program arguments at the same positions
  have hterm : n.term = t := by
    have := congrArg (fun l => l[i]?) w.unit.nodes_terms
    simp only [List.getElem?_map, hn] at this
    rw [ht] at this
    exact Option.some.inj this
  have hterm' : n'.term = t' := by
    have := congrArg (fun l => l[j]?) v.unit.nodes_terms
    simp only [List.getElem?_map, hn'] at this
    rw [ht'] at this
    exact Option.some.inj this
  -- Source judgment, with the policy rewritten to the context's. The
  -- `generalize` is load-bearing: `n.conclusion`'s type mentions the very
  -- `w.unit.policy` the next line rewrites (through `CheckedNode κ.canon
  -- w.unit.policy.ruleLookup …`), so rewriting first fails with a
  -- not-type-correct motive. Replacing it by an opaque `C` breaks that
  -- dependency. Do not inline these away.
  have hv : HasSupport κ.canon w.unit.policy.ruleLookup κ.Gamma κ.CertOk
      t n.conclusion [] := hterm ▸ n.valid
  generalize hcn : n.conclusion = C at hv ⊢
  rw [w.policy_eq] at hv
  -- Target judgment, likewise — here the generalize is what lets the
  -- `hcanon` rewrite through `n'`'s type succeed.
  have hv' : HasSupport lam.canon v.unit.policy.ruleLookup lam.Gamma lam.CertOk
      t' n'.conclusion [] := hterm' ▸ n'.valid
  generalize hcn' : n'.conclusion = C' at hv' ⊢
  rw [v.policy_eq, hcanon] at hv'
  obtain ⟨C'', hC'', hHS''⟩ := support_transport B hv htr
  rw [(hasSupport_unique hHS'' hv').1] at hC''
  exact hC''

/-- **Complete-support correspondence for every translatable query.**
Forward: a source support argument's conclusion `≡ c` translates to one
`≡ c'` (`equiv_tr`). Backward: a target support argument is a transport
(`matched`), and its conclusion `≡ c'` reflects to `≡ c` (`equiv_tr_reflect`,
which is where injectivity is needed). -/
theorem claimSupport_corr (hcanon : lam.canon = κ.canon)
    (B : StructuralBridge κ.canon κ.policy.ruleLookup lam.policy.ruleLookup
      κ.Gamma lam.Gamma κ.CertOk lam.CertOk)
    {w : World κ} {v : World lam}
    (hSB : StatusBridge B.sym B.leafMap w v) (hinj : B.sym.Injective)
    {c c' : Atom} (hc : trAtom B.sym c = some c') :
    SupportCorr (Corr B.sym B.leafMap w v) (claimAt w c) (claimAt v c') := by
  have hbis := hSB.bisim
  constructor
  · intro i hi
    obtain ⟨n, hn, heq⟩ :=
      Lara.Consistency.mem_claimSupportFor_iff.mp
        (by simpa only [claimAt, Lara.Consistency.completeClaimFor] using hi)
    have hi' : i < w.unit.program.args.length := by
      rw [← w.unit.nodes_terms, List.length_map]
      exact (List.getElem?_eq_some_iff.mp hn).1
    obtain ⟨j, hC⟩ := hbis.left_total i (List.mem_range.mpr hi')
    have hj' : j < v.unit.nodes.length := by
      have := (corr_lt hC).2
      rwa [← v.unit.nodes_terms, List.length_map] at this
    obtain ⟨n', hn'⟩ : ∃ n', v.unit.nodes[j]? = some n' :=
      ⟨_, List.getElem?_eq_getElem hj'⟩
    refine ⟨j, ?_, hC⟩
    apply Lara.Consistency.mem_claimSupportFor_iff.mpr
    refine ⟨n', hn', ?_⟩
    -- Rewrite in the hypothesis, not the goal: `lam.canon` occurs inside
    -- `n'`'s type, so abstracting it in the goal is not type correct, while
    -- `κ.canon` does not occur there and this direction is safe.
    have key : equiv κ.canon n'.conclusion c' :=
      equiv_tr (corr_conclusion hcanon B hC hn hn') hc heq
    rw [← hcanon] at key
    exact key
  · intro j hj
    obtain ⟨n', hn', heq'⟩ :=
      Lara.Consistency.mem_claimSupportFor_iff.mp
        (by simpa only [claimAt, Lara.Consistency.completeClaimFor] using hj)
    have hj' : j < v.unit.program.args.length := by
      rw [← v.unit.nodes_terms, List.length_map]
      exact (List.getElem?_eq_some_iff.mp hn').1
    obtain ⟨i, hC⟩ := hbis.right_total j (List.mem_range.mpr hj')
    have hi' : i < w.unit.nodes.length := by
      have := (corr_lt hC).1
      rwa [← w.unit.nodes_terms, List.length_map] at this
    obtain ⟨n, hn⟩ : ∃ n, w.unit.nodes[i]? = some n :=
      ⟨_, List.getElem?_eq_getElem hi'⟩
    refine ⟨i, ?_, hC⟩
    apply Lara.Consistency.mem_claimSupportFor_iff.mpr
    refine ⟨n, hn, ?_⟩
    -- Symmetrically: `lam.canon` does not occur in `n`'s type, so the
    -- forward rewrite is the safe direction here.
    have key : equiv lam.canon n.conclusion c :=
      equiv_tr_reflect hinj (corr_conclusion hcanon B hC hn hn') hc heq'
    rw [hcanon] at key
    exact key

/-! ### §3 T8 -/

/-- Status preservation from an explicit support correspondence — for bridges
whose translation is not injective but whose support sets are known to
correspond by other means. -/
theorem status_transport_of_corr {m : SymMap} {lm : LeafId → LeafId}
    {w : World κ} {v : World lam} (hSB : StatusBridge m lm w v)
    {c c' : Atom}
    (hcorr : SupportCorr (Corr m lm w v) (claimAt w c) (claimAt v c')) :
    cmpStatus v c' = cmpStatus w c :=
  (statusC_of_bisim hSB.bisim hcorr).symm

/-- **T8 — conditional status preservation.** Under the structural-bridge
contract, the `StatusBridge` attack-and-support hypotheses, and an injective
translation, the translated claim has at the target world exactly the status
the claim has at the source world — all four aggregated statuses at once,
none of them read as an argument label. The hypotheses exclude unmatched
target attackers and supports (`matched`, `back`); nothing is derived from
`Admits` alone (`Examples.PW.t7_t6_boundary`). -/
theorem status_transport (hcanon : lam.canon = κ.canon)
    (B : StructuralBridge κ.canon κ.policy.ruleLookup lam.policy.ruleLookup
      κ.Gamma lam.Gamma κ.CertOk lam.CertOk)
    {w : World κ} {v : World lam}
    (hSB : StatusBridge B.sym B.leafMap w v) (hinj : B.sym.Injective)
    {c c' : Atom} (hc : trAtom B.sym c = some c') :
    cmpStatus v c' = cmpStatus w c :=
  status_transport_of_corr hSB (claimSupport_corr hcanon B hSB hinj hc)

/-- T8 read at the independently defined source observation, through T1 on
both sides. -/
theorem srcStatus_transport (hcanon : lam.canon = κ.canon)
    (B : StructuralBridge κ.canon κ.policy.ruleLookup lam.policy.ruleLookup
      κ.Gamma lam.Gamma κ.CertOk lam.CertOk)
    {w : World κ} {v : World lam}
    (hSB : StatusBridge B.sym B.leafMap w v) (hinj : B.sym.Injective)
    {c c' : Atom} (hc : trAtom B.sym c = some c') (s : Status) :
    srcStatus v c' s ↔ srcStatus w c s := by
  rw [srcStatus_iff_cmpStatus, srcStatus_iff_cmpStatus,
    status_transport hcanon B hSB hinj hc]

end Bridge

/-! ### The modal reading

The design's `RobustlyJustified_b(w,c) := Comparable_b(w,c) ∧ w ⊨ [b]Justified(τ_b c)`
and `PossiblyJustified_b(w,c) := Translatable_b(c) ∧ w ⊨ ⟨b⟩Justified(τ_b c)`.
When every accepted successor of `w` is T8-related to `w`, both collapse to
the local status atom — for every status, not only `justified`. `hc` is
`Translatable`, `hreach` is `Reachable`. -/

section Modal
variable (D : BridgeData) (b : D.B)

theorem sat_status_iff_box {w : D.frame.World (D.frame.src b)} {c c' : Atom}
    {s : Status}
    (hcanon : (D.ctx (D.btgt b)).canon = (D.ctx (D.bsrc b)).canon)
    (B : StructuralBridge (D.ctx (D.bsrc b)).canon
      (D.ctx (D.bsrc b)).policy.ruleLookup (D.ctx (D.btgt b)).policy.ruleLookup
      (D.ctx (D.bsrc b)).Gamma (D.ctx (D.btgt b)).Gamma
      (D.ctx (D.bsrc b)).CertOk (D.ctx (D.btgt b)).CertOk)
    (hinj : B.sym.Injective) (hc : trAtom B.sym c = some c')
    (hall : ∀ v, D.frame.A b w v → StatusBridge B.sym B.leafMap w v)
    (hreach : ∃ v, D.frame.A b w v) :
    Sat D.frame (cmpVal D) (.status s c) w ↔
      Sat D.frame (cmpVal D) (.box b (.status s c')) w := by
  constructor
  · intro hs v hA
    show cmpStatus v c' = s
    exact (status_transport hcanon B (hall v hA) hinj hc).trans hs
  · intro hbox
    obtain ⟨v, hA⟩ := hreach
    have hv : cmpStatus v c' = s := hbox v hA
    show cmpStatus w c = s
    exact (status_transport hcanon B (hall v hA) hinj hc).symm.trans hv

theorem sat_status_iff_dia {w : D.frame.World (D.frame.src b)} {c c' : Atom}
    {s : Status}
    (hcanon : (D.ctx (D.btgt b)).canon = (D.ctx (D.bsrc b)).canon)
    (B : StructuralBridge (D.ctx (D.bsrc b)).canon
      (D.ctx (D.bsrc b)).policy.ruleLookup (D.ctx (D.btgt b)).policy.ruleLookup
      (D.ctx (D.bsrc b)).Gamma (D.ctx (D.btgt b)).Gamma
      (D.ctx (D.bsrc b)).CertOk (D.ctx (D.btgt b)).CertOk)
    (hinj : B.sym.Injective) (hc : trAtom B.sym c = some c')
    (hall : ∀ v, D.frame.A b w v → StatusBridge B.sym B.leafMap w v)
    (hreach : ∃ v, D.frame.A b w v) :
    Sat D.frame (cmpVal D) (.status s c) w ↔
      Sat D.frame (cmpVal D) (.dia b (.status s c')) w := by
  constructor
  · intro hs
    obtain ⟨v, hA⟩ := hreach
    refine ⟨v, hA, ?_⟩
    show cmpStatus v c' = s
    exact (status_transport hcanon B (hall v hA) hinj hc).trans hs
  · rintro ⟨v, hA, hv⟩
    have hv' : cmpStatus v c' = s := hv
    show cmpStatus w c = s
    exact (status_transport hcanon B (hall v hA) hinj hc).symm.trans hv'

/-- The same, under the source valuation — T4 (`sat_src_iff_cmp`) applied on
both sides. -/
theorem sat_status_iff_box_src {w : D.frame.World (D.frame.src b)} {c c' : Atom}
    {s : Status}
    (hcanon : (D.ctx (D.btgt b)).canon = (D.ctx (D.bsrc b)).canon)
    (B : StructuralBridge (D.ctx (D.bsrc b)).canon
      (D.ctx (D.bsrc b)).policy.ruleLookup (D.ctx (D.btgt b)).policy.ruleLookup
      (D.ctx (D.bsrc b)).Gamma (D.ctx (D.btgt b)).Gamma
      (D.ctx (D.bsrc b)).CertOk (D.ctx (D.btgt b)).CertOk)
    (hinj : B.sym.Injective) (hc : trAtom B.sym c = some c')
    (hall : ∀ v, D.frame.A b w v → StatusBridge B.sym B.leafMap w v)
    (hreach : ∃ v, D.frame.A b w v) :
    Sat D.frame (srcVal D) (.status s c) w ↔
      Sat D.frame (srcVal D) (.box b (.status s c')) w := by
  rw [sat_src_iff_cmp, sat_src_iff_cmp]
  exact sat_status_iff_box D b hcanon B hinj hc hall hreach

end Modal

/-! ### §4 Composition along T9's composite

Statuses are values, so preservation along a path is `Eq.trans` of the
per-edge T8 instances. What needs proving is that the *hypotheses* compose:
the T9 composite bridge of two status bridges is a status bridge, through
the chosen intermediate world (T9's intermediate-world dependence, kept). -/

section Compose
variable {κ μ lam : Instance.Context}

/-- Injectivity-where-defined is closed under Kleisli composition: a symbol
reaching the same image through both legs is identified leg by leg. -/
theorem SymMap.Injective.comp {m₁ m₂ : SymMap}
    (h₁ : m₁.Injective) (h₂ : m₂.Injective) : (m₂.comp m₁).Injective := by
  constructor
  · intro x y z hx hy
    simp only [SymMap.comp, Option.bind_eq_some_iff] at hx hy
    obtain ⟨x₁, hx₁, hx₂⟩ := hx
    obtain ⟨y₁, hy₁, hy₂⟩ := hy
    have := h₂.1 x₁ y₁ z hx₂ hy₂
    subst this
    exact h₁.1 x y x₁ hx₁ hy₁
  · intro x y z hx hy
    simp only [SymMap.comp, Option.bind_eq_some_iff] at hx hy
    obtain ⟨x₁, hx₁, hx₂⟩ := hx
    obtain ⟨y₁, hy₁, hy₂⟩ := hy
    have := h₂.2 x₁ y₁ z hx₂ hy₂
    subst this
    exact h₁.2 x y x₁ hx₁ hy₁

/-- `Corr` along the composite factors through the intermediate world,
provided the first leg is admitted (so the intermediate term is an
intermediate *argument*). -/
theorem corr_comp_iff {m₁ m₂ : SymMap} {lm₁ lm₂ : LeafId → LeafId}
    {w : World κ} {u : World μ} {v : World lam}
    (h₁ : Admits m₁ lm₁ w u) (i k : Nat) :
    Corr (m₂.comp m₁) (lm₂ ∘ lm₁) w v i k ↔
      ∃ j, Corr m₁ lm₁ w u i j ∧ Corr m₂ lm₂ u v j k := by
  constructor
  · rintro ⟨t, t'', ht, ht'', htr⟩
    rw [trSupport_comp, Option.bind_eq_some_iff] at htr
    obtain ⟨t', htr₁, htr₂⟩ := htr
    obtain ⟨t'₀, htr₁', hmem⟩ := h₁ t (List.mem_of_getElem? ht)
    rw [htr₁] at htr₁'
    cases htr₁'
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
    exact ⟨j, ⟨t, t', ht, hj, htr₁⟩, ⟨t', t'', hj, ht'', htr₂⟩⟩
  · rintro ⟨j, ⟨t, t', ht, hj, htr₁⟩, ⟨t'₁, t'', hj', ht'', htr₂⟩⟩
    rw [hj] at hj'
    cases hj'
    refine ⟨t, t'', ht, ht'', ?_⟩
    rw [trSupport_comp, Option.bind_eq_some_iff]
    exact ⟨t', htr₁, htr₂⟩

/-- **Status bridges compose** along the T9 composite, through a chosen
intermediate world. -/
theorem StatusBridge.comp {m₁ m₂ : SymMap} {lm₁ lm₂ : LeafId → LeafId}
    {w : World κ} {u : World μ} {v : World lam}
    (h₁ : StatusBridge m₁ lm₁ w u) (h₂ : StatusBridge m₂ lm₂ u v) :
    StatusBridge (m₂.comp m₁) (lm₂ ∘ lm₁) w v where
  admits := fun t ht => by
    obtain ⟨t', htr₁, hmem'⟩ := h₁.admits t ht
    obtain ⟨t'', htr₂, hmem''⟩ := h₂.admits t' hmem'
    refine ⟨t'', ?_, hmem''⟩
    rw [trSupport_comp, Option.bind_eq_some_iff]
    exact ⟨t', htr₁, htr₂⟩
  matched := fun t'' ht'' => by
    obtain ⟨t', hmem', htr₂⟩ := h₂.matched t'' ht''
    obtain ⟨t, hmem, htr₁⟩ := h₁.matched t' hmem'
    refine ⟨t, hmem, ?_⟩
    rw [trSupport_comp, Option.bind_eq_some_iff]
    exact ⟨t', htr₁, htr₂⟩
  forth := fun i k k₀ hC hE => by
    obtain ⟨j, hC₁, hC₂⟩ := (corr_comp_iff h₁.admits i k).mp hC
    obtain ⟨k₁, hC₁', hE₁⟩ := h₁.forth i j k₀ hC₁ hE
    obtain ⟨k₂, hC₂', hE₂⟩ := h₂.forth j k k₁ hC₂ hE₁
    exact ⟨k₂, (corr_comp_iff h₁.admits k₀ k₂).mpr ⟨k₁, hC₁', hC₂'⟩, hE₂⟩
  back := fun i k k₂ hC hE => by
    obtain ⟨j, hC₁, hC₂⟩ := (corr_comp_iff h₁.admits i k).mp hC
    obtain ⟨k₁, hC₂', hE₁⟩ := h₂.back j k k₂ hC₂ hE
    obtain ⟨k₀, hC₁', hE₀⟩ := h₁.back i j k₁ hC₁ hE₁
    exact ⟨k₀, (corr_comp_iff h₁.admits k₀ k₂).mpr ⟨k₁, hC₁', hC₂'⟩, hE₀⟩

end Compose

end Lara.PW
