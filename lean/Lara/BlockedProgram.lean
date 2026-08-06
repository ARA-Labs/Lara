import Lara.Blocked
import Lara.Consistency
import Lara.RawAttack

/-
The program-level instance of conservative reporting for quarantine-affected
claims (spec §4.3, issue #76).

`Lara.Blocked` proves the metatheory over an arbitrary pair of frameworks. This
module builds a declared-index pair matching the drivers' seed computation —
the declared framework `G` over all declared arguments, and a sub-carrier `F`
over the retained ones — and **discharges the three obligations** `Blocking`
requires for that pair.

The definitions here are executable and both drivers mirror them. The
compact-to-declared `AFEmbedding`, lifted complete-support claim, and exact
blocked-query predicate connect the framework below to the
`Compile.checkedAF` / `completeClaimFor` pair production labels.
`production_justified_nonpromotion_of_not_blocked` closes that bridge: a
published `justified` query remains justified with the declared material
reinstated. Differential tests remain conformance evidence that Haskell mirrors
these proved definitions.

The load-bearing fact is `coveredB_mono`: the retained resolved attacks are an
aligned *filter* of the declared resolved list, so `F.attack ≤ G.attack` holds
by construction and the seed only has to cover the other direction. Filtering
in raw-declaration lockstep preserves endpoint identity even when a removed and
retained declaration have equal support terms.
-/

namespace Lara.BlockedProgram

open Lara Lara.Support Lara.Attack Lara.RawAttack Lara.Compile
open Lara.Blocked Lara.Consistency

/-! ### The two frameworks in declared index space -/

/-- The retained declarations paired with their original declaration-order
indices. Keeping the value and index in one list makes the compact-to-declared
embedding structural: its two projections cannot drift. -/
def retainedView (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm)) :
    List ((String × SupportTerm) × Nat) :=
  declared.zipIdx.filter (fun entry => keep entry.1)

/-- The post-quarantine argument declarations, in their original relative
order. This is `Groups.quarantineArgs` specialized to the supplied keep
predicate. -/
def retainedArguments (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm)) :
    List (String × SupportTerm) :=
  (retainedView keep declared).map (fun entry => entry.1)

/-- Declaration-order indices of the arguments quarantine retained. Both
declared-index frameworks use these indices, while production's compact index
`k` embeds as `retainedIndices keep declared[k]?`. -/
def retainedIndices (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm)) : List Nat :=
  (retainedView keep declared).map (fun entry => entry.2)

/-- The structural subargument-closure edge rule (`coveredB`, the same
relation `edgeB` compiles) over declared argument terms. It needs no leaf
context, so it is defined on the declared program even though that program no
longer type-checks once its quarantined leaves leave `Γ`. -/
def edgeIn (declared : List (String × SupportTerm)) (atts : List Attack)
    (i j : Nat) : Bool :=
  match declared[i]?, declared[j]? with
  | some s, some t => coveredB atts s.2 t.2
  | _, _ => false

/-- The declared (pre-quarantine) framework — `Blocking`'s `G`. -/
def declaredAF (declared : List (String × SupportTerm)) (declAtts : List Attack) :
    Grounded.AF :=
  { args := List.range declared.length, attack := edgeIn declared declAtts }

/-- The checked (post-quarantine) framework in declared index space —
`Blocking`'s `F`. -/
def checkedAF (declared : List (String × SupportTerm)) (keptAtts : List Attack)
    (retained : List Nat) : Grounded.AF :=
  { args := retained, attack := edgeIn declared keptAtts }

/-- The material the prune touched: every removed argument, plus every retained
argument that lost an incoming edge. -/
def blockedSeed (declared : List (String × SupportTerm))
    (declAtts keptAtts : List Attack) (retained : List Nat) : List Nat :=
  ((List.range declared.length).filter (fun i => ! Grounded.memB i retained)) ++
  (retained.filter (fun j =>
    retained.any (fun i => edgeIn declared declAtts i j && ! edgeIn declared keptAtts i j)))

/-- Lift compact checked-program support indices into declared index space. -/
def liftSupport (retained support : List Nat) : List Nat :=
  support.filterMap (fun i => retained[i]?)

/-- The production claim after lifting its compact support indices. Holes are
unchanged; `completeClaimFor` supplies `[]` in the shipped path. -/
def liftClaim (retained : List Nat) (c : Grounded.Claim) : Grounded.Claim :=
  { support := liftSupport retained c.support, holes := c.holes }

/-- Does a compact support set contain an argument whose declared-index image
is in the proved blocked set? A missing image fails closed. -/
def supportBlocked (retained blocked support : List Nat) : Bool :=
  support.any (fun k =>
    match retained[k]? with
    | some i => blocked.contains i
    | none => true)

/-- The non-fast-path query filter used by the driver after a quarantine edit.
Factoring it here lets the soundness theorem consume the exact public decision
predicate rather than a parallel logical restatement. -/
def blockedQueriesFor (retained blocked : List Nat)
    (support : Atom → List Nat) (queries : List Atom) : List Atom :=
  queries.filter (fun p => supportBlocked retained blocked (support p))

/-- The exact production blocked-query computation, including its no-prune
fast path. -/
def blockedQueries (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm))
    (declAtts keptAtts : List Attack) (support : Atom → List Nat)
    (queries : List Atom) : List Atom :=
  let kept := retainedArguments keep declared
  if declared.length == kept.length then []
  else
    let retained := retainedIndices keep declared
    let blocked := blockedSet (declaredAF declared declAtts)
      (blockedSeed declared declAtts keptAtts retained)
    blockedQueriesFor retained blocked support queries

/-! ### Discharging the `Blocking` obligations -/

/-- `coveredB` is monotone in its attack list: adding attacks only adds edges.
This is the fact that makes a *dropped* attack the only way an edge can vanish,
so the seed's one-directional test is equivalent to `Blocking.edge_agree`'s
equality. -/
theorem coveredB_mono {atts₁ atts₂ : List Attack}
    (h : ∀ k, k ∈ atts₁ → k ∈ atts₂) {source target : SupportTerm}
    (hc : coveredB atts₁ source target = true) :
    coveredB atts₂ source target = true := by
  unfold coveredB at hc ⊢
  obtain ⟨k, hk, hkc⟩ := List.any_eq_true.mp hc
  exact List.any_eq_true.mpr ⟨k, h k hk, hkc⟩

/-- `edgeIn` unfolded: an edge needs both endpoints in range and a covering
attack. -/
theorem edgeIn_eq {declared : List (String × SupportTerm)} {atts : List Attack}
    {i j : Nat} :
    edgeIn declared atts i j = true ↔
      ∃ s t, declared[i]? = some s ∧ declared[j]? = some t ∧ coveredB atts s.2 t.2 = true := by
  unfold edgeIn
  cases hi : declared[i]? <;> cases hj : declared[j]? <;> simp

/-- The edge relation inherits `coveredB`'s monotonicity. -/
theorem edgeIn_mono {declared : List (String × SupportTerm)}
    {atts₁ atts₂ : List Attack} (h : ∀ k, k ∈ atts₁ → k ∈ atts₂) {i j : Nat}
    (hc : edgeIn declared atts₁ i j = true) : edgeIn declared atts₂ i j = true := by
  obtain ⟨s, t, hi, hj, hcov⟩ := edgeIn_eq.mp hc
  exact edgeIn_eq.mpr ⟨s, t, hi, hj, coveredB_mono h hcov⟩

/-- Aligned selection only removes resolved values. It therefore supplies the
attack-subset premise used by the production blocking theorem independently of
support-term identity or duplicate removed declarations. -/
theorem selectAligned_subset (keep : α → Bool) :
    ∀ (keys : List α) (values : List β) x,
      x ∈ selectAligned keep keys values → x ∈ values := by
  intro keys
  induction keys with
  | nil => intro values x hx; simp [selectAligned] at hx
  | cons key keys ih =>
      intro values x hx
      cases values with
      | nil => simp [selectAligned] at hx
      | cons value values =>
          by_cases hkeep : keep key = true
          · simp only [selectAligned, hkeep, if_true, List.mem_cons] at hx ⊢
            rcases hx with rfl | hx
            · exact Or.inl rfl
            · exact Or.inr (ih values x hx)
          · simp only [selectAligned, hkeep] at hx
            exact List.mem_cons_of_mem value (ih values x hx)

/-- **Obligation 1 (`hargs`).** The retained indices are declared indices. -/
theorem retainedIndices_subset {keep : (String × SupportTerm) → Bool}
    {declared : List (String × SupportTerm)} :
    ∀ i, i ∈ retainedIndices keep declared → i ∈ List.range declared.length := by
  intro i hi
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hi
  have hzip : entry ∈ declared.zipIdx := (List.mem_filter.mp hentry).1
  exact List.mem_range.mpr (List.snd_lt_of_mem_zipIdx hzip)

/-- The compact retained-argument list and its declared-index projection have
the same length because they are projections of one `retainedView`. -/
theorem retained_lengths_eq {keep : (String × SupportTerm) → Bool}
    {declared : List (String × SupportTerm)} :
    (retainedArguments keep declared).length =
      (retainedIndices keep declared).length := by
  simp [retainedArguments, retainedIndices]

/-- The paired retained view projects to the ordinary stable filter used by
`Groups.quarantineArgs`. -/
theorem retainedArguments_eq_filter (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm)) :
    retainedArguments keep declared = declared.filter keep := by
  have aux : ∀ (xs : List (String × SupportTerm)) (n : Nat),
      ((xs.zipIdx n).filter (fun entry => keep entry.1)).map (·.1) =
        xs.filter keep := by
    intro xs
    induction xs with
    | nil => intro n; rfl
    | cons a rest ih =>
        intro n
        simp only [List.zipIdx, List.filter_cons]
        cases h : keep a <;> simp [ih]
  exact aux declared 0

/-- Looking up a compact retained index returns the declaration and original
index from the same retained-view row. -/
theorem retained_lookup {keep : (String × SupportTerm) → Bool}
    {declared : List (String × SupportTerm)} {k i : Nat}
    (hi : (retainedIndices keep declared)[k]? = some i) :
    ∃ a, (retainedArguments keep declared)[k]? = some a ∧
      declared[i]? = some a := by
  simp only [retainedIndices, retainedArguments, List.getElem?_map] at hi ⊢
  cases hv : (retainedView keep declared)[k]? with
  | none => simp [hv] at hi
  | some entry =>
      rcases entry with ⟨a, j⟩
      simp [hv] at hi ⊢
      subst j
      have hview : (a, i) ∈ retainedView keep declared :=
        List.mem_of_getElem? hv
      have hzip : (a, i) ∈ declared.zipIdx :=
        (List.mem_filter.mp hview).1
      exact (List.mem_zipIdx_iff_getElem?).mp hzip

/-- Every retained declared index has a compact preimage. -/
theorem retained_lookup_of_mem {keep : (String × SupportTerm) → Bool}
    {declared : List (String × SupportTerm)} {i : Nat}
    (hi : i ∈ retainedIndices keep declared) :
    ∃ k : Nat, (retainedIndices keep declared)[k]? = some i :=
  (List.mem_iff_getElem? (l := retainedIndices keep declared) (a := i)).mp hi

/-! ### Reindexing a compact framework into declared index space -/

/-- A structure-preserving embedding between two finite AF presentations. The
map is optional only because production represents it by list lookup; `total`
proves it is defined on the compact carrier and `onto` proves every retained
declared index comes from a compact index. -/
structure AFEmbedding (C F : Grounded.AF) (lift : Nat → Option Nat) : Prop where
  total : ∀ a, a ∈ C.args → ∃ A, lift a = some A
  target_mem : ∀ a, a ∈ C.args → ∀ A, lift a = some A → A ∈ F.args
  onto : ∀ A, A ∈ F.args → ∃ a, a ∈ C.args ∧ lift a = some A
  attack_agree : ∀ a, a ∈ C.args → ∀ b, b ∈ C.args →
    ∀ A B, lift a = some A → lift b = some B →
      C.attack a b = F.attack A B

mutual
  /-- Direct acceptance transports from compact indices to retained declared
  indices along an `AFEmbedding`. -/
  theorem directIn_embed {C F : Grounded.AF} {lift : Nat → Option Nat}
      (he : AFEmbedding C F lift) :
      ∀ {a A}, Grounded.DirectIn C a → lift a = some A → Grounded.DirectIn F A
    | a, A, .intro ha h, hA =>
      .intro (he.target_mem a ha A hA) (by
        intro B hBF hBA
        obtain ⟨b, hbC, hB⟩ := he.onto B hBF
        have hba : C.attack b a = true := by
          rw [he.attack_agree b hbC a ha B A hB hA]
          exact hBA
        exact directOut_embed he (h b hbC hba) hbC hB)
  /-- The direct-defeat companion of `directIn_embed`. -/
  theorem directOut_embed {C F : Grounded.AF} {lift : Nat → Option Nat}
      (he : AFEmbedding C F lift) :
      ∀ {b B}, Grounded.DirectOut C b → b ∈ C.args →
        lift b = some B → Grounded.DirectOut F B
    | b, B, .intro (c := c) hc hcb, hbC, hB => by
      have hcC := Grounded.directIn_mem_args hc
      obtain ⟨C', hC'⟩ := he.total c hcC
      refine .intro (directIn_embed he hc hC') ?_
      rw [← he.attack_agree c hcC b hbC C' B hC' hB]
      exact hcb
end

/-- A compact `in` label remains `in` after embedding into retained declared
index space. -/
theorem labelC_inn_embed {C F : Grounded.AF} {lift : Nat → Option Nat}
    (he : AFEmbedding C F lift) {a A : Nat} (hA : lift a = some A)
    (h : Grounded.labelC C a = .inn) : Grounded.labelC F A = .inn := by
  exact (Grounded.labelC_inn_iff A).mpr
    (directIn_embed he ((Grounded.labelC_inn_iff a).mp h) hA)

/-- `justified` status transports through the compact-to-declared embedding
when the target claim contains the lifted complete support. -/
theorem statusC_justified_embed {C F : Grounded.AF} {lift : Nat → Option Nat}
    (he : AFEmbedding C F lift) {cC cF : Grounded.Claim}
    (hsupport : ∀ a, a ∈ cC.support → ∃ A, lift a = some A ∧ A ∈ cF.support)
    (h : Grounded.statusC C cC = .justified) :
    Grounded.statusC F cF = .justified := by
  obtain ⟨a, ha, hin⟩ := (Grounded.statusC_justified_iff C cC).mp h
  obtain ⟨A, hA, hAc⟩ := hsupport a ha
  exact (Grounded.statusC_justified_iff F cF).mpr
    ⟨A, hAc, labelC_inn_embed he hA hin⟩

/-- The production compact AF embeds into the proved declared-index checked AF.
The hypotheses are exactly the successful checker's two list equalities: it
checked the retained argument projection and the filtered declared attacks. -/
theorem compile_checkedAF_embedding
    (P : Compile.CheckedProgram canon Pi Gamma CertOk dp)
    (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm)) (keptAtts : List Attack)
    (hargs : P.args = (retainedArguments keep declared).map (·.2))
    (hatts : P.atts = keptAtts) :
    AFEmbedding (Compile.checkedAF P)
      (checkedAF declared keptAtts (retainedIndices keep declared))
      (fun k => (retainedIndices keep declared)[k]?) := by
  let retained := retainedIndices keep declared
  let kept := retainedArguments keep declared
  have hlen : P.args.length = retained.length := by
    rw [hargs, List.length_map]
    exact retained_lengths_eq
  refine
    { total := ?_
      target_mem := ?_
      onto := ?_
      attack_agree := ?_ }
  · intro a ha
    have halt : a < P.args.length := List.mem_range.mp ha
    obtain ⟨A, hA⟩ := getElem?_some_of_lt retained a (by simpa [hlen] using halt)
    exact ⟨A, hA⟩
  · intro a ha A hA
    exact List.mem_of_getElem? hA
  · intro A hA
    obtain ⟨a, ha⟩ := retained_lookup_of_mem hA
    refine ⟨a, List.mem_range.mpr ?_, ha⟩
    have : a < retained.length := lt_of_getElem?_some ha
    simpa [hlen] using this
  · intro a ha b hb A B hA hB
    obtain ⟨source, hsourceKept, hsourceDecl⟩ := retained_lookup hA
    obtain ⟨target, htargetKept, htargetDecl⟩ := retained_lookup hB
    have hsourceP : P.args[a]? = some source.2 := by
      rw [hargs, List.getElem?_map, hsourceKept]
      rfl
    have htargetP : P.args[b]? = some target.2 := by
      rw [hargs, List.getElem?_map, htargetKept]
      rfl
    simp only [Compile.checkedAF, Compile.toAF, Compile.edgeB, checkedAF, edgeIn]
    rw [hsourceP, htargetP, hsourceDecl, htargetDecl, hatts]

/-- **Obligation 2 (`hmissing`).** Every declared argument the prune removed is
seeded. -/
theorem blockedSeed_hmissing {declared : List (String × SupportTerm)}
    {declAtts keptAtts : List Attack} {retained : List Nat} :
    ∀ i, i ∈ List.range declared.length → i ∉ retained →
      i ∈ blockedSeed declared declAtts keptAtts retained := by
  intro i hi hni
  refine List.mem_append_left _ (List.mem_filter.mpr ⟨hi, ?_⟩)
  have : Grounded.memB i retained = false := by
    simp only [Grounded.memB, decide_eq_false_iff_not]; exact hni
  simp [this]

/-- **Obligation 3 (`hedge`).** An unseeded retained argument kept all of its
incoming edges — as an *equality*: `≥` is the seed's own test, and `≤` is
`coveredB_mono` over the filtered attack list. -/
theorem blockedSeed_hedge {declared : List (String × SupportTerm)}
    {declAtts keptAtts : List Attack}
    {retained : List Nat} :
    (∀ k, k ∈ keptAtts → k ∈ declAtts) →
    ∀ j, j ∈ retained →
      j ∉ blockedSeed declared declAtts keptAtts retained →
      ∀ i, i ∈ retained →
        edgeIn declared keptAtts i j = edgeIn declared declAtts i j := by
  intro hsub j hj hns i hi
  have hnotSeeded :
      ¬ (retained.any (fun x =>
          edgeIn declared declAtts x j
            && ! edgeIn declared keptAtts x j) = true) := by
    intro hany
    exact hns (List.mem_append_right _ (List.mem_filter.mpr ⟨hj, hany⟩))
  have hpair :
      ¬ (edgeIn declared declAtts i j
          && ! edgeIn declared keptAtts i j) = true := by
    intro hp
    exact hnotSeeded (List.any_eq_true.mpr ⟨i, hi, hp⟩)
  cases hk : edgeIn declared keptAtts i j with
  | true =>
      have := edgeIn_mono (declared := declared) hsub hk
      rw [this]
  | false =>
      cases hd : edgeIn declared declAtts i j with
      | true => exact absurd (by simp [hd, hk]) hpair
      | false => rfl

/-- **The driver's instance.** The pair of declared-index frameworks both
drivers compute, together with the blocked set they compute, satisfies
`Blocking`, so `Lara.Blocked.justified_nonpromotion` and `statusC_agree` apply
to *these* frameworks. The three obligations are discharged above, not
asserted. The section below transports this result through production's compact
checked-program indices and computed complete-support sets. -/
theorem blocking_of_blockedSeed (declared : List (String × SupportTerm))
    (declAtts keptAtts : List Attack) (retained : List Nat)
    (hret : ∀ i, i ∈ retained → i ∈ List.range declared.length)
    (hsub : ∀ k, k ∈ keptAtts → k ∈ declAtts) :
    Blocking
      (checkedAF declared keptAtts retained)
      (declaredAF declared declAtts)
      (blockedSet (declaredAF declared declAtts)
        (blockedSeed declared declAtts keptAtts retained)) := by
  exact
    blocking_of_seed
      hret
      (fun x hx hnx => blockedSeed_hmissing x hx hnx)
      (fun y hy hns x hx => blockedSeed_hedge hsub y hy hns x hx)

/-! ### The shipped compact-AF safety theorem -/

/-- Membership in lifted support exposes the compact source index and its
declared-index image. -/
theorem mem_liftSupport_iff {retained support : List Nat} {A : Nat} :
    A ∈ liftSupport retained support ↔
      ∃ a, a ∈ support ∧ retained[a]? = some A := by
  unfold liftSupport
  rw [List.mem_filterMap]

/-- A false public blocking predicate means every successfully lifted support
index lies outside the blocked set. -/
theorem supportBlocked_false_unblocked {retained blocked support : List Nat}
    (hfalse : supportBlocked retained blocked support = false) :
    ∀ A, A ∈ liftSupport retained support → A ∉ blocked := by
  intro A hA hAB
  obtain ⟨a, ha, hmap⟩ := mem_liftSupport_iff.mp hA
  have hany : supportBlocked retained blocked support = true := by
    unfold supportBlocked
    apply List.any_eq_true.mpr
    refine ⟨a, ha, ?_⟩
    rw [hmap]
    simp [hAB]
  rw [hfalse] at hany
  contradiction

/-- If a requested query is absent from the driver's exact blocked-query
filter, its support predicate is false. This is the bridge from the public
`p ∉ blocked` branch to `justified_nonpromotion`'s per-support premise. -/
theorem supportBlocked_false_of_not_mem {retained blocked : List Nat}
    {support : Atom → List Nat} {queries : List Atom} {p : Atom}
    (hp : p ∈ queries)
    (hnot : p ∉ blockedQueriesFor retained blocked support queries) :
    supportBlocked retained blocked (support p) = false := by
  cases h : supportBlocked retained blocked (support p) with
  | false => rfl
  | true =>
      exact False.elim (hnot (List.mem_filter.mpr ⟨hp, h⟩))

/-- Absence from the exact production list yields the unblocked support
predicate whenever quarantine actually removed an argument (the non-fast-path
branch). -/
theorem supportBlocked_false_of_not_mem_blockedQueries
    {keep : (String × SupportTerm) → Bool}
    {declared : List (String × SupportTerm)} {declAtts keptAtts : List Attack}
    {support : Atom → List Nat} {queries : List Atom} {p : Atom}
    (hpruned : declared.length ≠ (retainedArguments keep declared).length)
    (hp : p ∈ queries)
    (hnot : p ∉ blockedQueries keep declared declAtts keptAtts support queries) :
    let retained := retainedIndices keep declared
    let blocked := blockedSet (declaredAF declared declAtts)
      (blockedSeed declared declAtts keptAtts retained)
    supportBlocked retained blocked (support p) = false := by
  simp only [blockedQueries, hpruned, BEq.beq, decide_false,
    Bool.false_eq_true, if_false] at hnot
  exact supportBlocked_false_of_not_mem hp hnot

/-- Every index selected by `completeClaimFor` belongs to the compact compiled
AF. This uses the accepted unit's retained-node alignment, not a driver-side
length assertion. -/
theorem claimSupportFor_mem_checkedAF
    {accepted : Lara.Unit.CheckedUnit canon Gamma CertOk} {p : Atom} :
    ∀ i, i ∈ claimSupportFor accepted p →
      i ∈ (Compile.checkedAF accepted.program).args := by
  intro i hi
  obtain ⟨node, hnode, _⟩ := mem_claimSupportFor_iff.mp hi
  apply List.mem_range.mpr
  have hinodes : i < accepted.nodes.length := lt_of_getElem?_some hnode
  have hlen : accepted.nodes.length = accepted.program.args.length := by
    simpa using congrArg List.length accepted.nodes_terms
  exact hlen ▸ hinodes

/-- **Production non-promotion (issue #80).** For the exact compact AF and
`completeClaimFor` that `Driver.buildAccept` labels, an unblocked `justified`
status remains `justified` in the declared framework after all quarantined
arguments and attacks are reinstated.

`hargs` and `hatts` are the successful checker's exact input equalities. The
driver now supplies the retained projections in those hypotheses by
construction. `hunblocked` is the predicate behind absence from
`blockedQueriesFor`; `supportBlocked_false_of_not_mem` derives it from the
public list membership test. -/
theorem production_justified_nonpromotion
    (accepted : Lara.Unit.CheckedUnit canon Gamma CertOk)
    (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm)) (declAtts keptAtts : List Attack)
    (p : Atom)
    (hargs : accepted.program.args =
      (retainedArguments keep declared).map (·.2))
    (hatts : accepted.program.atts = keptAtts)
    (hsub : ∀ k, k ∈ keptAtts → k ∈ declAtts)
    (hunblocked :
      let retained := retainedIndices keep declared
      let blocked := blockedSet (declaredAF declared declAtts)
        (blockedSeed declared declAtts keptAtts retained)
      supportBlocked retained blocked (claimSupportFor accepted p) = false)
    (hstatus : Grounded.statusC (Compile.checkedAF accepted.program)
      (completeClaimFor accepted p) = .justified) :
    Grounded.statusC (declaredAF declared declAtts)
      (liftClaim (retainedIndices keep declared) (completeClaimFor accepted p)) =
        .justified := by
  let retained := retainedIndices keep declared
  let F := checkedAF declared keptAtts retained
  let G := declaredAF declared declAtts
  let B := blockedSet G (blockedSeed declared declAtts keptAtts retained)
  let cC := completeClaimFor accepted p
  let cF := liftClaim retained cC
  have he : AFEmbedding (Compile.checkedAF accepted.program) F
      (fun k => retained[k]?) := by
    exact compile_checkedAF_embedding accepted.program keep declared keptAtts hargs hatts
  have hcompact : Grounded.statusC (Compile.checkedAF accepted.program) cC =
      .justified := hstatus
  have hF : Grounded.statusC F cF = .justified := by
    apply statusC_justified_embed (cC := cC) (cF := cF) he
    · intro a ha
      change a ∈ claimSupportFor accepted p at ha
      have haC : a ∈ (Compile.checkedAF accepted.program).args :=
        claimSupportFor_mem_checkedAF a ha
      obtain ⟨A, hA⟩ := he.total a haC
      refine ⟨A, hA, ?_⟩
      change A ∈ liftSupport retained (claimSupportFor accepted p)
      exact mem_liftSupport_iff.mpr ⟨a, ha, hA⟩
    · exact hcompact
  have hb : Blocking F G B := by
    exact blocking_of_blockedSeed declared declAtts keptAtts retained
      (fun _ hi => retainedIndices_subset _ hi) hsub
  apply justified_nonpromotion (cF := cF) (cG := cF) hb
  · intro A hA
    change A ∈ liftSupport retained (claimSupportFor accepted p) at hA
    obtain ⟨a, ha, hmap⟩ := mem_liftSupport_iff.mp hA
    exact he.target_mem a (claimSupportFor_mem_checkedAF a ha) A hmap
  · intro A hA
    change A ∈ liftSupport retained (claimSupportFor accepted p) at hA
    exact supportBlocked_false_unblocked hunblocked A hA
  · intro A hA
    exact hA
  · exact hF

/-- Driver-facing form of `production_justified_nonpromotion`: a requested
query that is absent from the exact `blockedQueries` output supplies the
unblocked premise automatically. -/
theorem production_justified_nonpromotion_of_not_blocked
    (accepted : Lara.Unit.CheckedUnit canon Gamma CertOk)
    (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm)) (declAtts keptAtts : List Attack)
    (queries : List Atom) (p : Atom)
    (hargs : accepted.program.args =
      (retainedArguments keep declared).map (·.2))
    (hatts : accepted.program.atts = keptAtts)
    (hsub : ∀ k, k ∈ keptAtts → k ∈ declAtts)
    (hpruned : declared.length ≠ (retainedArguments keep declared).length)
    (hp : p ∈ queries)
    (hnot : p ∉ blockedQueries keep declared declAtts keptAtts
      (fun q => claimSupportFor accepted q) queries)
    (hstatus : Grounded.statusC (Compile.checkedAF accepted.program)
      (completeClaimFor accepted p) = .justified) :
    Grounded.statusC (declaredAF declared declAtts)
      (liftClaim (retainedIndices keep declared) (completeClaimFor accepted p)) =
        .justified := by
  apply production_justified_nonpromotion accepted keep declared declAtts keptAtts p
      hargs hatts hsub ?_ hstatus
  exact supportBlocked_false_of_not_mem_blockedQueries hpruned hp hnot

/-- Fully checker-instantiated shipped-path theorem. A successful `checkUnit`
call supplies `hargs` and `hatts`; callers cannot assert a parallel compact AF.
This is the proof boundary used by the driver branch after it constructs the
retained arguments and filtered declared attacks. -/
theorem checked_production_justified_nonpromotion_of_not_blocked
    {RawAttack : Type}
    (reg : Lara.Support.BackendRegistry canon)
    (policy : Lara.Policy.Policy)
    (accepted : Lara.Unit.CheckedUnit canon Gamma (Lara.Support.certOkOf reg))
    (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm)) (declAtts : List Attack)
    (keepAttack : RawAttack → Bool) (rawAtts : List RawAttack)
    (queries : List Atom) (p : Atom)
    (hcheck : Lara.Check.Unit.checkUnit Gamma reg
      ({ policy := policy
       , args := (retainedArguments keep declared).map (·.2)
       , atts := selectAligned keepAttack rawAtts declAtts } : Lara.Unit) =
        .ok accepted)
    (hpruned : declared.length ≠ (retainedArguments keep declared).length)
    (hp : p ∈ queries)
    (hnot : p ∉ blockedQueries keep declared declAtts
      (selectAligned keepAttack rawAtts declAtts)
      (fun q => claimSupportFor accepted q) queries)
    (hstatus : Grounded.statusC (Compile.checkedAF accepted.program)
      (completeClaimFor accepted p) = .justified) :
    Grounded.statusC (declaredAF declared declAtts)
      (liftClaim (retainedIndices keep declared) (completeClaimFor accepted p)) =
        .justified := by
  obtain ⟨_, _, _, hargs, hatts, _, _⟩ :=
    Lara.Check.Unit.checkUnit_sound hcheck
  exact production_justified_nonpromotion_of_not_blocked
    accepted keep declared declAtts (selectAligned keepAttack rawAtts declAtts)
      queries p hargs hatts
      (fun k hk => selectAligned_subset keepAttack rawAtts declAtts k hk)
      hpruned hp hnot hstatus

end Lara.BlockedProgram
