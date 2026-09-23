import Lara.Grounded

/-
Conservative public reporting for quarantine-affected claims (spec §4.3).


**The hazard.** §4.3 quarantine removes a leaf, every argument whose support
term uses it, and every attack with a removed endpoint, and then checks the
*smaller* program. Grounded semantics is non-monotonic across graph changes, so
deletion does not only weaken: if the quarantined leaf backed an *attacker*, its
target loses a defeater and its label can move `contested`/`defeated` →
`justified`. Publishing the smaller graph's label as the claim status therefore
lets **missing evidence make a claim look stronger**. The §4.3 sentence "a data
conflict … can never make a claim `justified`" reasons only about the claim whose
own support was quarantined; it is false in the attacker case.

**The fix.** Do not publish the label of a graph that was edited. Compute the
set of arguments whose grounded label *could* have depended on removed material
and report every claim supported by one of them as `evidence-blocked`, retaining
the smaller graph's label only as a conditional diagnostic. Claims provably out
of reach of the edit keep their ordinary four-state status.

**What is mechanized here.** This module is the abstract, corpus-independent
half: it knows nothing about leaves, policies, support terms, or checkers, and
quantifies over an arbitrary pair of finite frameworks `F` (checked, post-prune)
and `G` (declared, pre-prune).

* `Blocking F G B` — the four conditions making `B` an adequate blocked set.
* `blockedSet` — the executable forward closure both drivers compute, and
  `blocking_of_seed`, which discharges `Blocking` from three seed conditions the
  drivers satisfy by construction.
* `directIn_transfer` / `directIn_reflect` — the **locality lemma**: on arguments
  outside `B`, the declarative grounded judgment cannot tell `F` from `G`.
  Everything else follows from it.
* `justified_nonpromotion` — the safety result. A publicly `justified` claim is
  justified in the declared framework too: the deletion did not manufacture it.
* `statusC_agree` — the preservation companion: an unblocked claim whose
  complete-support set is the *same* in both frameworks keeps its status. The
  equal-support premise is load-bearing: a claim whose own support the prune
  removed can move (`justified` → `gap`) without being blocked, so blocking is
  conservative against promotion, not a guarantee that nothing changed.

The directed rule matters. Blocking the whole undirected component touching a
removed node is also sound but blocks nearly every claim in a connected program;
grounded labelling reads only a node's transitive *attackers*, so forward
attack-reachability from the removed material is the tight rule.

No Mathlib: the finite-closure argument reuses `Lara.Grounded`'s deficit
machinery.
-/

namespace Lara.Blocked

open Lara.Grounded

/-! ### The blocked-set contract -/

/-- `Blocking F G B`: the checked framework `F` is the declared framework `G`
minus quarantined material, and `B` covers every argument that edit could have
reached.

* `args_sub` — `F` removes arguments, never invents them.
* `missing_mem` — every removed argument is blocked.
* `closed` — `B` is closed under declared attack edges going *forward*: if a
  blocked argument attacks `y`, then `y`'s label may have moved too.
* `edge_agree` — outside `B`, the two frameworks have the same incoming edges.
  This is what makes lost *edges* (an attack dropped because one endpoint was
  removed, which under subargument closure could also have carried an edge onto
  a retained argument) as safe as lost nodes: any retained argument whose
  incoming edges changed must be in `B`. -/
structure Blocking (F G : AF) (B : List Arg) : Prop where
  /-- the checked carrier is part of the declared carrier -/
  args_sub : ∀ a, a ∈ F.args → a ∈ G.args
  /-- every removed argument is blocked -/
  missing_mem : ∀ x, x ∈ G.args → x ∉ F.args → x ∈ B
  /-- blocked-ness propagates along declared attack edges -/
  closed : ∀ x, x ∈ B → ∀ y, y ∈ G.args → G.attack x y = true → y ∈ B
  /-- unblocked retained arguments kept all their incoming edges -/
  edge_agree : ∀ y, y ∈ F.args → y ∉ B → ∀ x, x ∈ F.args → F.attack x y = G.attack x y

/-! ### The locality lemma

The declarative grounded judgment at `a` reads only `a`'s transitive attackers.
`Blocking` says the two frameworks agree there whenever `a ∉ B`, so the two
judgments agree at `a`. Both directions are proved by mutual structural
recursion on the derivation, exactly as `Grounded.directIn_sound` is. -/

mutual
  /-- Locality, checked → declared: a directly-`in` unblocked argument of the
  checked framework is directly `in` in the declared framework. Deleting the
  quarantined material did not create this acceptance. -/
  theorem directIn_transfer {F G : AF} {B : List Arg} (hb : Blocking F G B) :
      ∀ {a : Arg}, DirectIn F a → a ∉ B → DirectIn G a
    | a, .intro ha h, hnb =>
      DirectIn.intro (hb.args_sub a ha) (by
        intro b hbG hba
        by_cases hbF : b ∈ F.args
        · have hFba : F.attack b a = true := by
            rw [hb.edge_agree a ha hnb b hbF]; exact hba
          have hbB : b ∉ B := fun hmem =>
            hnb (hb.closed b hmem a (hb.args_sub a ha) hba)
          exact directOut_transfer hb (h b hbF hFba) hbF hbB
        · exact absurd
            (hb.closed b (hb.missing_mem b hbG hbF) a (hb.args_sub a ha) hba) hnb)
  /-- The `DirectOut` companion of `directIn_transfer`. -/
  theorem directOut_transfer {F G : AF} {B : List Arg} (hb : Blocking F G B) :
      ∀ {b : Arg}, DirectOut F b → b ∈ F.args → b ∉ B → DirectOut G b
    | b, .intro (c := c) hc hcb, hbF, hnb =>
      have hcF : c ∈ F.args := directIn_mem_args hc
      have hGcb : G.attack c b = true := by
        rw [← hb.edge_agree b hbF hnb c hcF]; exact hcb
      have hcB : c ∉ B := fun hmem =>
        hnb (hb.closed c hmem b (hb.args_sub b hbF) hGcb)
      DirectOut.intro (directIn_transfer hb hc hcB) hGcb
end

mutual
  /-- Locality, declared → checked: an unblocked argument that is directly `in`
  in the declared framework stays directly `in` after the prune. -/
  theorem directIn_reflect {F G : AF} {B : List Arg} (hb : Blocking F G B) :
      ∀ {a : Arg}, DirectIn G a → a ∈ F.args → a ∉ B → DirectIn F a
    | a, .intro _ h, haF, hnb =>
      DirectIn.intro haF (by
        intro b hbF hba
        have hGba : G.attack b a = true := by
          rw [← hb.edge_agree a haF hnb b hbF]; exact hba
        have hbB : b ∉ B := fun hmem =>
          hnb (hb.closed b hmem a (hb.args_sub a haF) hGba)
        exact directOut_reflect hb (h b (hb.args_sub b hbF) hGba) hbF hbB)
  /-- The `DirectOut` companion of `directIn_reflect`. -/
  theorem directOut_reflect {F G : AF} {B : List Arg} (hb : Blocking F G B) :
      ∀ {b : Arg}, DirectOut G b → b ∈ F.args → b ∉ B → DirectOut F b
    | b, .intro (c := c) hc hcb, hbF, hnb =>
      have hcG : c ∈ G.args := directIn_mem_args hc
      have hcB : c ∉ B := fun hmem =>
        hnb (hb.closed c hmem b (hb.args_sub b hbF) hcb)
      have hcF : c ∈ F.args :=
        Classical.byContradiction (fun hc' => hcB (hb.missing_mem c hcG hc'))
      have hFcb : F.attack c b = true := by
        rw [hb.edge_agree b hbF hnb c hcF]; exact hcb
      DirectOut.intro (directIn_reflect hb hc hcF hcB) hFcb
end

/-- Locality, packaged: outside `B` the two frameworks accept the same
arguments. -/
theorem directIn_iff_of_unblocked {F G : AF} {B : List Arg} (hb : Blocking F G B)
    {a : Arg} (haF : a ∈ F.args) (hnb : a ∉ B) : DirectIn F a ↔ DirectIn G a :=
  ⟨fun h => directIn_transfer hb h hnb, fun h => directIn_reflect hb h haF hnb⟩

/-- Locality for defeat: outside `B` the two frameworks defeat the same
arguments. -/
theorem directOut_iff_of_unblocked {F G : AF} {B : List Arg} (hb : Blocking F G B)
    {a : Arg} (haF : a ∈ F.args) (hnb : a ∉ B) : DirectOut F a ↔ DirectOut G a :=
  ⟨fun h => directOut_transfer hb h haF hnb, fun h => directOut_reflect hb h haF hnb⟩

/-- The compiled labels agree outside `B`. -/
theorem labelC_agree {F G : AF} {B : List Arg} (hb : Blocking F G B)
    {a : Arg} (haF : a ∈ F.args) (hnb : a ∉ B) : labelC F a = labelC G a := by
  have hin := directIn_iff_of_unblocked hb haF hnb
  have hout := directOut_iff_of_unblocked hb haF hnb
  cases hFa : labelC F a
  case inn =>
    exact ((labelC_inn_iff a).mpr (hin.mp ((labelC_inn_iff a).mp hFa))).symm
  case out =>
    obtain ⟨hni, ho⟩ := (labelC_out_iff a).mp hFa
    exact ((labelC_out_iff a).mpr ⟨fun h => hni (hin.mpr h), hout.mp ho⟩).symm
  case undec =>
    obtain ⟨hni, hno⟩ := (labelC_undec_iff a).mp hFa
    exact ((labelC_undec_iff a).mpr
      ⟨fun h => hni (hin.mpr h), fun h => hno (hout.mpr h)⟩).symm

/-! ### Four-state status: non-promotion and preservation -/

/-- `List.any` respects pointwise agreement on the list's members. -/
theorem any_congr {l : List Arg} {p q : Arg → Bool} (h : ∀ a, a ∈ l → p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : p x = q x := h x List.mem_cons_self
    have ih' := ih (fun a ha => h a (List.mem_cons_of_mem x ha))
    simp [List.any_cons, hx, ih']

/-- **The safety result.** If every complete-support argument of the
checked claim is unblocked, then a `justified` verdict on the *checked* (pruned)
framework is also `justified` on the *declared* framework — with the quarantined
arguments and attacks reinstated.

So a published `justified` was never manufactured by deletion. The support
hypothesis is `⊆`: reinstating removed material can only add support, never take
it away. This is the property that makes it sound to publish an unblocked
`justified`; blocked claims are reported `evidence-blocked` precisely because
this argument is unavailable for them. -/
theorem justified_nonpromotion {F G : AF} {B : List Arg} (hb : Blocking F G B)
    {cF cG : Claim}
    (hmem : ∀ a, a ∈ cF.support → a ∈ F.args)
    (hnb : ∀ a, a ∈ cF.support → a ∉ B)
    (hsub : ∀ a, a ∈ cF.support → a ∈ cG.support)
    (h : statusC F cF = Status.justified) : statusC G cG = Status.justified := by
  obtain ⟨i, hi, hin⟩ := (statusC_justified_iff F cF).mp h
  refine (statusC_justified_iff G cG).mpr ⟨i, hsub i hi, ?_⟩
  rw [← labelC_agree hb (hmem i hi) (hnb i hi)]
  exact hin

/-- **Preservation.** With the same complete-support set, an unblocked claim has
the same four-state status in both frameworks: blocking never hides a status the
declared framework would have given. Together with `justified_nonpromotion` this
says the reporting rule is conservative *and* not vacuous. -/
theorem statusC_agree {F G : AF} {B : List Arg} (hb : Blocking F G B)
    {cF cG : Claim}
    (hmem : ∀ a, a ∈ cF.support → a ∈ F.args)
    (hnb : ∀ a, a ∈ cF.support → a ∉ B)
    (hsupp : cF.support = cG.support) : statusC F cF = statusC G cG := by
  have hlab : ∀ a, a ∈ cF.support → labelC F a = labelC G a :=
    fun a ha => labelC_agree hb (hmem a ha) (hnb a ha)
  unfold statusC
  rw [← hsupp]
  have hinn : cF.support.any (fun a => labelC F a == Label.inn)
      = cF.support.any (fun a => labelC G a == Label.inn) :=
    any_congr (fun a ha => by rw [hlab a ha])
  have hund : cF.support.any (fun a => labelC F a == Label.undec)
      = cF.support.any (fun a => labelC G a == Label.undec) :=
    any_congr (fun a ha => by rw [hlab a ha])
  rw [hinn, hund]

/-! ### The executable blocked set

Both drivers compute the blocked set as a bounded forward closure of a seed. The
seed is the material the prune touched: the removed arguments, plus every
retained argument that lost an incoming edge. `blocking_of_seed` turns the three
conditions the drivers establish by construction into the `Blocking` contract the
theorems above consume. -/

/-- One round of forward closure, kept inside the declared carrier. Reflexive by
construction, so the iteration is ascending. -/
def closureStep (G : AF) (B : List Arg) : List Arg :=
  G.args.filter (fun y => memB y B || B.any (fun x => G.attack x y))

/-- The bounded closure iteration from a seed (intersected with the carrier). -/
def closureIter (G : AF) (S : List Arg) : Nat → List Arg
  | 0 => G.args.filter (fun x => memB x S)
  | k + 1 => closureStep G (closureIter G S k)

/-- The blocked set: iterate `|args|` times, which `closure_stable` shows is
already a fixed point. -/
def blockedSet (G : AF) (S : List Arg) : List Arg := closureIter G S G.args.length

theorem closureIter_subset_args {G : AF} {S : List Arg} :
    ∀ k a, a ∈ closureIter G S k → a ∈ G.args
  | 0, _, h => (List.mem_filter.mp h).1
  | _ + 1, _, h => (List.mem_filter.mp h).1

theorem closureIter_mono {G : AF} {S : List Arg} :
    ∀ k a, a ∈ closureIter G S k → a ∈ closureIter G S (k + 1) := by
  intro k a h
  have hargs : a ∈ G.args := closureIter_subset_args k a h
  refine List.mem_filter.mpr ⟨hargs, ?_⟩
  simp [memB_iff.mpr h]

/-- `stable k`: the closure has reached a fixed point at step `k`. -/
def cstable (G : AF) (S : List Arg) (k : Nat) : Prop :=
  ∀ a, a ∈ closureIter G S (k + 1) → a ∈ closureIter G S k

theorem cstable_succ {G : AF} {S : List Arg} {k : Nat} (h : cstable G S k) :
    cstable G S (k + 1) := by
  intro a ha
  have ha' : a ∈ closureStep G (closureIter G S (k + 1)) := ha
  obtain ⟨hargs, hstep⟩ := List.mem_filter.mp ha'
  refine List.mem_filter.mpr ⟨hargs, ?_⟩
  rw [Bool.or_eq_true]
  rcases Bool.or_eq_true _ _ |>.mp hstep with hmem | hedge
  · exact Or.inl (memB_iff.mpr (h a (memB_iff.mp hmem)))
  · obtain ⟨x, hx, hxa⟩ := List.any_eq_true.mp hedge
    exact Or.inr (List.any_eq_true.mpr ⟨x, h x hx, hxa⟩)

theorem cstable_add {G : AF} {S : List Arg} {k : Nat} (h : cstable G S k) :
    ∀ j, cstable G S (k + j)
  | 0 => h
  | j + 1 => cstable_succ (cstable_add h j)

theorem cdeficit_lt {G : AF} {S : List Arg} {k : Nat} (h : ¬ cstable G S k) :
    deficit G (closureIter G S (k + 1)) < deficit G (closureIter G S k) := by
  have hex : ∃ a, a ∈ closureIter G S (k + 1) ∧ ¬ a ∈ closureIter G S k :=
    Classical.byContradiction (fun hcon =>
      h (fun a hain => Classical.byContradiction (fun hnotin => hcon ⟨a, hain, hnotin⟩)))
  obtain ⟨a, ha1, ha0⟩ := hex
  unfold deficit
  apply filter_length_lt (w := a)
  · intro x _ hx
    have hnx : ¬ x ∈ closureIter G S (k + 1) := by
      cases hh : memB x (closureIter G S (k + 1)) with
      | false => simp only [memB, decide_eq_false_iff_not] at hh; exact hh
      | true => rw [hh] at hx; simp at hx
    have hb0 : memB x (closureIter G S k) = false := by
      simp only [memB, decide_eq_false_iff_not]
      intro hc; exact hnx (closureIter_mono k x hc)
    simp [hb0]
  · exact closureIter_subset_args (k + 1) a ha1
  · have : memB a (closureIter G S k) = false := by
      simp only [memB, decide_eq_false_iff_not]; exact ha0
    simp [this]
  · have : memB a (closureIter G S (k + 1)) = true := by
      simp only [memB, decide_eq_true_eq]; exact ha1
    simp [this]

theorem cdeficit_bound {G : AF} {S : List Arg} :
    ∀ k, (∀ j, j < k → ¬ cstable G S j) →
      deficit G (closureIter G S k) + k ≤ G.args.length
  | 0, _ => by
      have h : deficit G (closureIter G S 0) ≤ G.args.length := by
        unfold deficit
        exact List.length_filter_le _ _
      omega
  | k + 1, h => by
    have hk : ¬ cstable G S k := h k (Nat.lt_succ_self k)
    have IH : deficit G (closureIter G S k) + k ≤ G.args.length :=
      cdeficit_bound k (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hlt := cdeficit_lt hk
    omega

/-- The closure reaches a fixed point within `|args|` steps. -/
theorem closure_stable {G : AF} {S : List Arg} : cstable G S G.args.length := by
  by_cases hs : ∃ j, j < G.args.length ∧ cstable G S j
  · obtain ⟨j, hj, hjs⟩ := hs
    have := cstable_add hjs (G.args.length - j)
    rwa [Nat.add_sub_cancel' (Nat.le_of_lt hj)] at this
  · have hs : ∀ j, j < G.args.length → ¬ cstable G S j := fun j hj hst => hs ⟨j, hj, hst⟩
    have hb := cdeficit_bound G.args.length (fun j hj => hs j hj)
    have hdef : deficit G (closureIter G S G.args.length) = 0 := by omega
    have hall : ∀ a, a ∈ G.args → a ∈ closureIter G S G.args.length := by
      intro a ha
      apply Classical.byContradiction
      intro hna
      have hmem : a ∈ G.args.filter (fun a => ! memB a (closureIter G S G.args.length)) := by
        rw [List.mem_filter]
        refine ⟨ha, ?_⟩
        have : memB a (closureIter G S G.args.length) = false := by
          simp only [memB, decide_eq_false_iff_not]; exact hna
        simp [this]
      have : 0 < deficit G (closureIter G S G.args.length) := by
        unfold deficit; exact List.length_pos_of_mem hmem
      omega
    intro a ha
    exact hall a (closureIter_subset_args (G.args.length + 1) a ha)

/-- The seed (inside the carrier) is blocked. -/
theorem seed_subset_blocked {G : AF} {S : List Arg} {x : Arg}
    (hx : x ∈ G.args) (hs : x ∈ S) : x ∈ blockedSet G S := by
  have h0 : x ∈ closureIter G S 0 := List.mem_filter.mpr ⟨hx, by simp [memB_iff.mpr hs]⟩
  unfold blockedSet
  induction G.args.length with
  | zero => exact h0
  | succ n ih => exact closureIter_mono n x ih

/-- The blocked set is closed under declared attack edges. -/
theorem blocked_closed {G : AF} {S : List Arg} {x : Arg} (hx : x ∈ blockedSet G S)
    {y : Arg} (hy : y ∈ G.args) (hxy : G.attack x y = true) : y ∈ blockedSet G S := by
  have hstep : y ∈ closureIter G S (G.args.length + 1) := by
    refine List.mem_filter.mpr ⟨hy, ?_⟩
    have : (blockedSet G S).any (fun z => G.attack z y) = true :=
      List.any_eq_true.mpr ⟨x, hx, hxy⟩
    simp [blockedSet] at this ⊢
    simp [this]
  exact closure_stable y hstep

/-- **The drivers' entry point.** The three seed conditions each driver
establishes by construction — the prune only removes arguments, every removed
argument is seeded, and every retained argument whose incoming edges changed is
seeded — make the computed `blockedSet` an adequate blocked set. -/
theorem blocking_of_seed {F G : AF} {S : List Arg}
    (hargs : ∀ a, a ∈ F.args → a ∈ G.args)
    (hmissing : ∀ x, x ∈ G.args → x ∉ F.args → x ∈ S)
    (hedge : ∀ y, y ∈ F.args → y ∉ S → ∀ x, x ∈ F.args → F.attack x y = G.attack x y) :
    Blocking F G (blockedSet G S) where
  args_sub := hargs
  missing_mem := fun x hxG hxF => seed_subset_blocked hxG (hmissing x hxG hxF)
  closed := fun _ hx _ hy hxy => blocked_closed hx hy hxy
  edge_agree := fun y hyF hnb x hxF =>
    hedge y hyF (fun hs => hnb (seed_subset_blocked (hargs y hyF) hs)) x hxF

end Lara.Blocked
