import Lara.Blocked
import Lara.Consistency
import Lara.RawAttack

/-
The program-level instance of conservative reporting for quarantine-affected
claims (spec §4.3, `docs/theory-core.md#conservative-reporting-with-holes`).

`Lara.Blocked` proves the metatheory over an arbitrary pair of frameworks. This
module builds a declared-index pair matching the drivers' seed computation and
**discharges the three obligations** `Blocking` requires for that pair. Both
frameworks live in original declaration index space:

* the reference carrier `D` is `retainedIndices live declared` for a reference
  mask `live`. The production mask `referenceLive` reads the checked cache on
  retained declarations and classifies each quarantined declaration once under
  the full declared `Γ`: it is a node unless it is a successfully typed hole,
  so an unclassified (ill-typed) quarantined term stays a conservative node;
* the checked carrier `K` is `retainedIndices (keepComplete keep done) declared`:
  the retained declarations the checker made AF nodes. Raw retention `keep`
  stays separate, so retained holes keep their raw ids and attack endpoints;
* `declaredAF` (`G`) carries `D` with the closure edges of the declared
  attacks, `checkedAF` (`F`) carries `K` with those of the retained attacks;
* the seed is `(D \ K) ∪ {j ∈ K | ∃ i ∈ K, G.attack i j ∧ ¬ F.attack i j}`,
  closed forward along `G` over `D` only. Holes are not in `D`, so neither they
  nor the attacks they source can seed or propagate blocking; a dropped attack
  onto an occurrence inside a removed hole still seeds a retained complete
  argument containing that occurrence, because `G` has the closure edge and
  `F` lost it.

`Blocking` holds for every reference carrier containing `K`, so the abstract
results only need `K ⊆ D`; `referenceLive_eq_notHole` identifies the executable
carrier with the specification carrier `D` (complete or unclassified under the
full declared `Γ`) by obligation transport on the supported retained terms.

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

/-- Declaration-order indices of the declarations a mask selects. Under the raw
keep predicate these are the arguments quarantine retained; under
`keepComplete` they are `K`, and production's compact index `k` embeds as
`(retainedIndices (keepComplete keep done) declared)[k]?`; under a reference
mask they are `D`. -/
def retainedIndices (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm)) : List Nat :=
  (retainedView keep declared).map (fun entry => entry.2)

/-- Complete retention: the declaration survives the raw prune and the checked
cache made it an AF node. `done` is that cache's completeness test
(`checkedDone` in production). Raw retention `keep` is kept separate because
retained holes still need their raw ids and attack endpoints. -/
def keepComplete (keep : (String × SupportTerm) → Bool)
    (done : SupportTerm → Bool) (a : String × SupportTerm) : Bool :=
  keep a && done a.2

/-- The specification reference mask (spec §4.3): a declaration is a reference
node unless it is a successfully typed hole under `Gamma`. A term whose
inference fails is a node: it is not `argHole`. This is not `argComplete`. -/
def notHole {canon : String → String} (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom) (reg : BackendRegistry canon)
    (a : String × SupportTerm) : Bool :=
  ! Check.argHole Pi Gamma reg a.2

/-- The production reference mask. A retained declaration reuses the checked
cache (`done`), so no retained term is re-inferred; a quarantined declaration
is classified by one inference under the full declared `Gamma`.
`referenceLive_eq_notHole` proves it equals `notHole` on every declaration. -/
def referenceLive {canon : String → String}
    (keep : (String × SupportTerm) → Bool) (done : SupportTerm → Bool)
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (a : String × SupportTerm) : Bool :=
  if keep a then done a.2 else notHole Pi Gamma reg a

/-- The checked cache's completeness test: a retained term is complete exactly
when it is one of the accepted program's AF arguments. -/
def checkedDone {canon : String → String} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (accepted : Lara.Unit.CheckedUnit canon Gamma CertOk)
    (w : SupportTerm) : Bool :=
  decide (w ∈ accepted.program.args)

/-- `K` for an accepted unit: the declared indices of its AF nodes, read off
its cache. `checkedCarrier_eq` unfolds it. -/
abbrev checkedCarrier {canon : String → String} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (accepted : Lara.Unit.CheckedUnit canon Gamma CertOk)
    (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm)) : List Nat :=
  retainedIndices (keepComplete keep (checkedDone accepted)) declared

/-- `D` for an accepted unit: the production reference carrier under the full
declared context `GammaDecl`. `referenceCarrier_eq` unfolds it. -/
abbrev referenceCarrier {canon : String → String} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (accepted : Lara.Unit.CheckedUnit canon Gamma CertOk)
    (keep : (String × SupportTerm) → Bool) (Pi : RuleId → Option Rule)
    (GammaDecl : LeafId → Option Atom) (reg : BackendRegistry canon)
    (declared : List (String × SupportTerm)) : List Nat :=
  retainedIndices (referenceLive keep (checkedDone accepted) Pi GammaDecl reg)
    declared

theorem checkedCarrier_eq {canon : String → String}
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (accepted : Lara.Unit.CheckedUnit canon Gamma CertOk)
    (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm)) :
    checkedCarrier accepted keep declared =
      retainedIndices (keepComplete keep (checkedDone accepted)) declared := rfl

theorem referenceCarrier_eq {canon : String → String}
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (accepted : Lara.Unit.CheckedUnit canon Gamma CertOk)
    (keep : (String × SupportTerm) → Bool) (Pi : RuleId → Option Rule)
    (GammaDecl : LeafId → Option Atom) (reg : BackendRegistry canon)
    (declared : List (String × SupportTerm)) :
    referenceCarrier accepted keep Pi GammaDecl reg declared =
      retainedIndices (referenceLive keep (checkedDone accepted) Pi GammaDecl reg)
        declared := rfl

/-- The structural subargument-closure edge rule (`coveredB`, the same
relation `edgeB` compiles) over declared argument terms. It needs no leaf
context, so it is defined on the declared program even though that program no
longer type-checks once its quarantined leaves leave `Γ`. -/
def edgeIn (declared : List (String × SupportTerm)) (atts : List Attack)
    (i j : Nat) : Bool :=
  match declared[i]?, declared[j]? with
  | some s, some t => coveredB atts s.2 t.2
  | _, _ => false

/-- The declared (pre-quarantine) reference framework over carrier `D` —
`Blocking`'s `G`. The carrier is passed as a list so the driver classifies
each declaration once. -/
def declaredAF (declared : List (String × SupportTerm)) (declAtts : List Attack)
    (reference : List Nat) : Grounded.AF :=
  { args := reference, attack := edgeIn declared declAtts }

/-- The checked (post-quarantine) framework in declared index space over
carrier `K` — `Blocking`'s `F`. -/
def checkedAF (declared : List (String × SupportTerm)) (keptAtts : List Attack)
    (retained : List Nat) : Grounded.AF :=
  { args := retained, attack := edgeIn declared keptAtts }

/-- The material the prune touched: every removed reference node
(`D \ K`), plus every retained complete node that lost an incoming edge from
another one. -/
def blockedSeed (declared : List (String × SupportTerm))
    (declAtts keptAtts : List Attack) (reference retained : List Nat) :
    List Nat :=
  (reference.filter (fun i => ! Grounded.memB i retained)) ++
  (retained.filter (fun j =>
    retained.any (fun i => edgeIn declared declAtts i j && ! edgeIn declared keptAtts i j)))

/-- Lift compact checked-program support indices into declared index space. -/
def liftSupport (retained support : List Nat) : List Nat :=
  support.filterMap (fun i => retained[i]?)

/-- The production claim after lifting its compact support indices along `K`.
With holes present `K` is not an initial segment of the declared indices, so
this is not the identity even when nothing is quarantined. Holes are
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
fast path. The fast path tests raw retention: a unit whose holes are all
retained quarantines nothing, so hole filtering alone never blocks. The
reference carrier is computed once and shared by the seed and the closure. -/
def blockedQueries (keep : (String × SupportTerm) → Bool)
    (done : SupportTerm → Bool) (live : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm))
    (declAtts keptAtts : List Attack) (support : Atom → List Nat)
    (queries : List Atom) : List Atom :=
  let kept := retainedArguments keep declared
  if declared.length == kept.length then []
  else
    let retained := retainedIndices (keepComplete keep done) declared
    let reference := retainedIndices live declared
    let blocked := blockedSet (declaredAF declared declAtts reference)
      (blockedSeed declared declAtts keptAtts reference retained)
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

/-- Retained indices are declared indices. -/
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

/-- Membership in `retainedIndices`: the mask selects the declaration at that
index. -/
theorem mem_retainedIndices_iff {keep : (String × SupportTerm) → Bool}
    {declared : List (String × SupportTerm)} {i : Nat} :
    i ∈ retainedIndices keep declared ↔
      ∃ a, declared[i]? = some a ∧ keep a = true := by
  simp only [retainedIndices, retainedView, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨a, j⟩, ⟨hzip, hkeep⟩, rfl⟩
    exact ⟨a, (List.mem_zipIdx_iff_getElem?).mp hzip, hkeep⟩
  · rintro ⟨a, ha, hkeep⟩
    exact ⟨(a, i), ⟨(List.mem_zipIdx_iff_getElem?).mpr ha, hkeep⟩, rfl⟩

/-- A mask that selects more declarations selects more indices. -/
theorem retainedIndices_mono {keep keep' : (String × SupportTerm) → Bool}
    {declared : List (String × SupportTerm)}
    (h : ∀ a, a ∈ declared → keep a = true → keep' a = true) :
    ∀ i, i ∈ retainedIndices keep declared →
      i ∈ retainedIndices keep' declared := by
  intro i hi
  obtain ⟨a, ha, hkeep⟩ := mem_retainedIndices_iff.mp hi
  exact mem_retainedIndices_iff.mpr ⟨a, ha, h a (List.mem_of_getElem? ha) hkeep⟩

/-- Masks that agree on the declarations select the same index list. -/
theorem retainedIndices_congr {keep keep' : (String × SupportTerm) → Bool}
    {declared : List (String × SupportTerm)}
    (h : ∀ a, a ∈ declared → keep a = keep' a) :
    retainedIndices keep declared = retainedIndices keep' declared := by
  unfold retainedIndices retainedView
  congr 1
  apply List.filter_congr
  intro entry hentry
  apply h entry.1
  have hget := (List.mem_zipIdx_iff_getElem? (x := entry)).mp hentry
  exact List.mem_of_getElem? hget

/-- **Filter composition for complete retention.** Retaining the complete
declarations is retaining the raw survivors and then keeping the complete
ones. -/
theorem retainedArguments_keepComplete (keep : (String × SupportTerm) → Bool)
    (done : SupportTerm → Bool) (declared : List (String × SupportTerm)) :
    retainedArguments (keepComplete keep done) declared =
      (retainedArguments keep declared).filter (fun a => done a.2) := by
  rw [retainedArguments_eq_filter, retainedArguments_eq_filter,
    List.filter_filter]
  apply List.filter_congr
  intro a _
  simp [keepComplete, Bool.and_comm]

/-- The term projection of complete retention filters the retained terms. -/
theorem keepComplete_terms (keep : (String × SupportTerm) → Bool)
    (done : SupportTerm → Bool) (declared : List (String × SupportTerm)) :
    (retainedArguments (keepComplete keep done) declared).map (·.2) =
      ((retainedArguments keep declared).map (·.2)).filter done := by
  rw [retainedArguments_keepComplete, List.filter_map]
  rfl

/-- Coverage from a live source reads the same edges before and after live
filtering. -/
theorem coveredB_liveAttacks {live : List SupportTerm} {atts : List Attack}
    {source target : SupportTerm} (hsource : source ∈ live) :
    coveredB (Check.liveAttacks live atts) source target =
      coveredB atts source target := by
  unfold coveredB Check.liveAttacks
  rw [List.any_filter]
  congr 1
  funext k
  by_cases hk : k.source = source
  · simp [hk, hsource]
  · simp [hk]

/-- `K ⊆ D` for the production mask, by construction: a retained complete
declaration is a reference node because the mask reads the same cache. -/
theorem referenceLive_of_keepComplete {canon : String → String}
    {keep : (String × SupportTerm) → Bool} {done : SupportTerm → Bool}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {a : String × SupportTerm}
    (h : keepComplete keep done a = true) :
    referenceLive keep done Pi Gamma reg a = true := by
  simp only [keepComplete, Bool.and_eq_true] at h
  simp [referenceLive, h.1, h.2]

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

mutual
  /-- Direct acceptance also reflects from the declared-index presentation back
  to its compact isomorphic presentation. -/
  theorem directIn_reflect_embedding {C F : Grounded.AF}
      {lift : Nat → Option Nat} (he : AFEmbedding C F lift) :
      ∀ {a A}, a ∈ C.args → lift a = some A →
        Grounded.DirectIn F A → Grounded.DirectIn C a
    | a, A, ha, hA, .intro _ defended => by
        apply Grounded.DirectIn.intro ha
        intro b hb hba
        obtain ⟨B, hB⟩ := he.total b hb
        apply directOut_reflect_embedding he hb hB
        apply defended B (he.target_mem b hb B hB)
        rw [← he.attack_agree b hb a ha B A hB hA]
        exact hba
  /-- Direct defeat reflects across the same embedding. -/
  theorem directOut_reflect_embedding {C F : Grounded.AF}
      {lift : Nat → Option Nat} (he : AFEmbedding C F lift) :
      ∀ {a A}, a ∈ C.args → lift a = some A →
        Grounded.DirectOut F A → Grounded.DirectOut C a
    | a, A, ha, hA, .intro (c := B) hBIn hBA => by
        have hBF := Grounded.directIn_mem_args hBIn
        obtain ⟨b, hb, hB⟩ := he.onto B hBF
        apply Grounded.DirectOut.intro
          (directIn_reflect_embedding he hb hB hBIn)
        rw [he.attack_agree b hb a ha B A hB hA]
        exact hBA
end

/-- A mapped compact argument and its retained declared-index image have exactly
the same grounded label. -/
theorem labelC_eq_of_embedding {C F : Grounded.AF}
    {lift : Nat → Option Nat} (he : AFEmbedding C F lift)
    {a A : Nat} (ha : a ∈ C.args) (hA : lift a = some A) :
    Grounded.labelC C a = Grounded.labelC F A := by
  have hin : Grounded.DirectIn C a ↔ Grounded.DirectIn F A :=
    ⟨fun h => directIn_embed he h hA,
      fun h => directIn_reflect_embedding he ha hA h⟩
  have hout : Grounded.DirectOut C a ↔ Grounded.DirectOut F A :=
    ⟨fun h => directOut_embed he h ha hA,
      fun h => directOut_reflect_embedding he ha hA h⟩
  rw [Grounded.labelC_spec, Grounded.labelC_spec]
  simp only [hin, hout]

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
The hypotheses are exactly the successful checker's two list equalities: its AF
arguments are the projection of the declarations `keep` selects (production
passes `keepComplete`), and its compiled attacks are the live filter of the
retained declared attacks. Live filtering loses no edge between AF arguments
(`coveredB_liveAttacks`), so `F` may use the retained attacks themselves. -/
theorem compile_checkedAF_embedding
    (P : Compile.CheckedProgram canon Pi Gamma CertOk dp)
    (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm)) (keptAtts : List Attack)
    (hargs : P.args = (retainedArguments keep declared).map (·.2))
    (hatts : P.atts = Check.liveAttacks P.args keptAtts) :
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
    exact coveredB_liveAttacks (List.mem_of_getElem? hsourceP)

/-- **Obligation 1 (`hargs`).** `K ⊆ D` whenever the reference mask holds of
every retained complete declaration. For the production mask this is
`referenceLive_of_keepComplete`; for the specification mask it is obligation
transport (`checked_complete_subset_notHole`). -/
theorem complete_subset_reference {keep live : (String × SupportTerm) → Bool}
    {done : SupportTerm → Bool} {declared : List (String × SupportTerm)}
    (hlive : ∀ a, a ∈ declared → keepComplete keep done a = true → live a = true) :
    ∀ i, i ∈ retainedIndices (keepComplete keep done) declared →
      i ∈ retainedIndices live declared :=
  retainedIndices_mono hlive

/-- **Obligation 2 (`hmissing`).** Every reference node outside the checked
carrier is seeded. -/
theorem blockedSeed_hmissing {declared : List (String × SupportTerm)}
    {declAtts keptAtts : List Attack} {reference retained : List Nat} :
    ∀ i, i ∈ reference → i ∉ retained →
      i ∈ blockedSeed declared declAtts keptAtts reference retained := by
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
    {reference retained : List Nat} :
    (∀ k, k ∈ keptAtts → k ∈ declAtts) →
    ∀ j, j ∈ retained →
      j ∉ blockedSeed declared declAtts keptAtts reference retained →
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
asserted; the only premise on the carriers is `K ⊆ D`. The section below
transports this result through production's compact checked-program indices and
computed complete-support sets. -/
theorem blocking_of_blockedSeed (declared : List (String × SupportTerm))
    (declAtts keptAtts : List Attack) (reference retained : List Nat)
    (hret : ∀ i, i ∈ retained → i ∈ reference)
    (hsub : ∀ k, k ∈ keptAtts → k ∈ declAtts) :
    Blocking
      (checkedAF declared keptAtts retained)
      (declaredAF declared declAtts reference)
      (blockedSet (declaredAF declared declAtts reference)
        (blockedSeed declared declAtts keptAtts reference retained)) := by
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
    {keep live : (String × SupportTerm) → Bool} {done : SupportTerm → Bool}
    {declared : List (String × SupportTerm)} {declAtts keptAtts : List Attack}
    {support : Atom → List Nat} {queries : List Atom} {p : Atom}
    (hpruned : declared.length ≠ (retainedArguments keep declared).length)
    (hp : p ∈ queries)
    (hnot : p ∉ blockedQueries keep done live declared declAtts keptAtts
      support queries) :
    let retained := retainedIndices (keepComplete keep done) declared
    let reference := retainedIndices live declared
    let blocked := blockedSet (declaredAF declared declAtts reference)
      (blockedSeed declared declAtts keptAtts reference retained)
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

/-- **Production non-promotion.** For the exact compact AF and
`completeClaimFor` that `Driver.buildAccept` labels, an unblocked `justified`
status remains `justified` in the declared reference framework after the
quarantined arguments and attacks are reinstated.

`hargs` and `hatts` are the successful checker's exact output equalities: its
AF arguments are the complete retention of the declarations, and its compiled
attacks are the live filter of the retained declared attacks. `hlive` is
`K ⊆ D`. `hunblocked` is the predicate behind absence from
`blockedQueriesFor`; `supportBlocked_false_of_not_mem` derives it from the
public list membership test. -/
theorem production_justified_nonpromotion
    (accepted : Lara.Unit.CheckedUnit canon Gamma CertOk)
    (keep live : (String × SupportTerm) → Bool) (done : SupportTerm → Bool)
    (declared : List (String × SupportTerm)) (declAtts keptAtts : List Attack)
    (p : Atom)
    (hargs : accepted.program.args =
      (retainedArguments (keepComplete keep done) declared).map (·.2))
    (hatts : accepted.program.atts =
      Check.liveAttacks accepted.program.args keptAtts)
    (hsub : ∀ k, k ∈ keptAtts → k ∈ declAtts)
    (hlive : ∀ a, a ∈ declared → keepComplete keep done a = true →
      live a = true)
    (hunblocked :
      let retained := retainedIndices (keepComplete keep done) declared
      let reference := retainedIndices live declared
      let blocked := blockedSet (declaredAF declared declAtts reference)
        (blockedSeed declared declAtts keptAtts reference retained)
      supportBlocked retained blocked (claimSupportFor accepted p) = false)
    (hstatus : Grounded.statusC (Compile.checkedAF accepted.program)
      (completeClaimFor accepted p) = .justified) :
    Grounded.statusC
      (declaredAF declared declAtts (retainedIndices live declared))
      (liftClaim (retainedIndices (keepComplete keep done) declared)
        (completeClaimFor accepted p)) = .justified := by
  let retained := retainedIndices (keepComplete keep done) declared
  let reference := retainedIndices live declared
  let F := checkedAF declared keptAtts retained
  let G := declaredAF declared declAtts reference
  let B := blockedSet G (blockedSeed declared declAtts keptAtts reference retained)
  let cC := completeClaimFor accepted p
  let cF := liftClaim retained cC
  have he : AFEmbedding (Compile.checkedAF accepted.program) F
      (fun k => retained[k]?) := by
    exact compile_checkedAF_embedding accepted.program _ declared keptAtts
      hargs hatts
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
    exact blocking_of_blockedSeed declared declAtts keptAtts reference retained
      (complete_subset_reference hlive) hsub
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

/-- Every unblocked complete-support argument has the same label in the compact
checked framework and the declared reference framework. This is the
per-argument bridge needed by the five-valued tighten row, including its
defeated-to-contested impossibility. -/
theorem production_unblocked_label_agree
    (accepted : Lara.Unit.CheckedUnit canon Gamma CertOk)
    (keep live : (String × SupportTerm) → Bool) (done : SupportTerm → Bool)
    (declared : List (String × SupportTerm)) (declAtts keptAtts : List Attack)
    (p : Atom)
    (hargs : accepted.program.args =
      (retainedArguments (keepComplete keep done) declared).map (·.2))
    (hatts : accepted.program.atts =
      Check.liveAttacks accepted.program.args keptAtts)
    (hsub : ∀ k, k ∈ keptAtts → k ∈ declAtts)
    (hlive : ∀ a, a ∈ declared → keepComplete keep done a = true →
      live a = true)
    (hunblocked :
      let retained := retainedIndices (keepComplete keep done) declared
      let reference := retainedIndices live declared
      let blocked := blockedSet (declaredAF declared declAtts reference)
        (blockedSeed declared declAtts keptAtts reference retained)
      supportBlocked retained blocked (claimSupportFor accepted p) = false)
    {a A : Nat} (ha : a ∈ claimSupportFor accepted p)
    (hA : (retainedIndices (keepComplete keep done) declared)[a]? = some A) :
    Grounded.labelC (Compile.checkedAF accepted.program) a =
      Grounded.labelC
        (declaredAF declared declAtts (retainedIndices live declared)) A := by
  let retained := retainedIndices (keepComplete keep done) declared
  let reference := retainedIndices live declared
  let F := checkedAF declared keptAtts retained
  let G := declaredAF declared declAtts reference
  let B := blockedSet G (blockedSeed declared declAtts keptAtts reference retained)
  have he : AFEmbedding (Compile.checkedAF accepted.program) F
      (fun k => retained[k]?) :=
    compile_checkedAF_embedding accepted.program _ declared keptAtts
      hargs hatts
  have haC : a ∈ (Compile.checkedAF accepted.program).args :=
    claimSupportFor_mem_checkedAF a ha
  have hAF : A ∈ F.args := he.target_mem a haC A hA
  have hAlift :
      A ∈ liftSupport retained (claimSupportFor accepted p) :=
    mem_liftSupport_iff.mpr ⟨a, ha, hA⟩
  have hAB : A ∉ B :=
    supportBlocked_false_unblocked hunblocked A hAlift
  exact (labelC_eq_of_embedding he haC hA).trans
    (Blocked.labelC_agree
      (blocking_of_blockedSeed declared declAtts keptAtts reference retained
        (complete_subset_reference hlive) hsub)
      hAF hAB)

/-- Driver-facing form of `production_justified_nonpromotion`: a requested
query that is absent from the exact `blockedQueries` output supplies the
unblocked premise automatically. -/
theorem production_justified_nonpromotion_of_not_blocked
    (accepted : Lara.Unit.CheckedUnit canon Gamma CertOk)
    (keep live : (String × SupportTerm) → Bool) (done : SupportTerm → Bool)
    (declared : List (String × SupportTerm)) (declAtts keptAtts : List Attack)
    (queries : List Atom) (p : Atom)
    (hargs : accepted.program.args =
      (retainedArguments (keepComplete keep done) declared).map (·.2))
    (hatts : accepted.program.atts =
      Check.liveAttacks accepted.program.args keptAtts)
    (hsub : ∀ k, k ∈ keptAtts → k ∈ declAtts)
    (hlive : ∀ a, a ∈ declared → keepComplete keep done a = true →
      live a = true)
    (hpruned : declared.length ≠ (retainedArguments keep declared).length)
    (hp : p ∈ queries)
    (hnot : p ∉ blockedQueries keep done live declared declAtts keptAtts
      (fun q => claimSupportFor accepted q) queries)
    (hstatus : Grounded.statusC (Compile.checkedAF accepted.program)
      (completeClaimFor accepted p) = .justified) :
    Grounded.statusC
      (declaredAF declared declAtts (retainedIndices live declared))
      (liftClaim (retainedIndices (keepComplete keep done) declared)
        (completeClaimFor accepted p)) = .justified := by
  apply production_justified_nonpromotion accepted keep live done declared
      declAtts keptAtts p hargs hatts hsub hlive ?_ hstatus
  exact supportBlocked_false_of_not_mem_blockedQueries hpruned hp hnot

/-! ### The no-prune fast path

When raw retention keeps every declaration, `blockedQueries` returns `[]`
without computing anything. The general rule agrees: with the production mask
the reference carrier is exactly `K` and no edge is lost, so the seed is empty.
A clean accepted unit with holes therefore reports no `evidence-blocked`;
filtering holes out of the AF is not quarantine. -/

/-- The fast path: a unit that quarantines nothing blocks no query. -/
theorem blockedQueries_eq_nil_of_keep_all
    {keep live : (String × SupportTerm) → Bool} {done : SupportTerm → Bool}
    {declared : List (String × SupportTerm)} {declAtts keptAtts : List Attack}
    {support : Atom → List Nat} {queries : List Atom}
    (hall : ∀ a, a ∈ declared → keep a = true) :
    blockedQueries keep done live declared declAtts keptAtts support queries =
      [] := by
  have hkept : retainedArguments keep declared = declared := by
    rw [retainedArguments_eq_filter]
    exact List.filter_eq_self.mpr hall
  simp [blockedQueries, hkept]

/-- With nothing quarantined, the production reference carrier is `K`. -/
theorem referenceLive_indices_of_keep_all {canon : String → String}
    {keep : (String × SupportTerm) → Bool} {done : SupportTerm → Bool}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {declared : List (String × SupportTerm)}
    (hall : ∀ a, a ∈ declared → keep a = true) :
    retainedIndices (referenceLive keep done Pi Gamma reg) declared =
      retainedIndices (keepComplete keep done) declared := by
  apply retainedIndices_congr
  intro a ha
  simp [referenceLive, keepComplete, hall a ha]

/-- **Hole filtering alone is not quarantine.** With nothing quarantined and
the retained attacks equal to the declared ones, the general seed is empty, so
the fast path loses nothing. -/
theorem blockedSeed_eq_nil_of_keep_all {canon : String → String}
    {keep : (String × SupportTerm) → Bool} {done : SupportTerm → Bool}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {declared : List (String × SupportTerm)}
    {declAtts keptAtts : List Attack}
    (hall : ∀ a, a ∈ declared → keep a = true)
    (hatts : keptAtts = declAtts) :
    blockedSeed declared declAtts keptAtts
      (retainedIndices (referenceLive keep done Pi Gamma reg) declared)
      (retainedIndices (keepComplete keep done) declared) = [] := by
  rw [referenceLive_indices_of_keep_all hall, hatts]
  unfold blockedSeed
  apply List.append_eq_nil_iff.mpr
  constructor
  · apply List.filter_eq_nil_iff.mpr
    intro i hi
    simp [Grounded.memB, hi]
  · apply List.filter_eq_nil_iff.mpr
    intro j _
    simp

/-- The closure of an empty seed is empty. -/
theorem blockedSet_nil (G : Grounded.AF) : blockedSet G [] = [] := by
  have h : ∀ k, closureIter G [] k = [] := by
    intro k
    induction k with
    | zero => simp [closureIter, Grounded.memB]
    | succ k ih => simp [closureIter, closureStep, ih, Grounded.memB]
  exact h _

/-- With nothing blocked, a support set whose indices all lift is unblocked. -/
theorem supportBlocked_nil {retained support : List Nat}
    (hlt : ∀ k, k ∈ support → k < retained.length) :
    supportBlocked retained [] support = false := by
  unfold supportBlocked
  apply Bool.eq_false_iff.mpr
  intro hany
  obtain ⟨k, hk, hblocked⟩ := List.any_eq_true.mp hany
  obtain ⟨i, hi⟩ := getElem?_some_of_lt retained k (hlt k hk)
  rw [hi] at hblocked
  simp at hblocked

/-- **No-prune non-promotion.** When raw retention keeps everything and the
retained attacks are the declared ones, a compact `justified` status is
`justified` in the declared reference framework. The compact AF is an onto
embedding into it, not equal to it: with holes present `K` skips their
indices, so `liftClaim` is not the identity. -/
theorem production_justified_nonpromotion_of_keep_all {canon : String → String}
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (accepted : Lara.Unit.CheckedUnit canon Gamma CertOk)
    (keep : (String × SupportTerm) → Bool) (done : SupportTerm → Bool)
    (Pi : RuleId → Option Rule) (GammaDecl : LeafId → Option Atom)
    (reg : BackendRegistry canon)
    (declared : List (String × SupportTerm)) (declAtts keptAtts : List Attack)
    (p : Atom)
    (hargs : accepted.program.args =
      (retainedArguments (keepComplete keep done) declared).map (·.2))
    (hatts : accepted.program.atts =
      Check.liveAttacks accepted.program.args keptAtts)
    (hall : ∀ a, a ∈ declared → keep a = true)
    (hkept : keptAtts = declAtts)
    (hstatus : Grounded.statusC (Compile.checkedAF accepted.program)
      (completeClaimFor accepted p) = .justified) :
    Grounded.statusC
      (declaredAF declared declAtts
        (retainedIndices (referenceLive keep done Pi GammaDecl reg) declared))
      (liftClaim (retainedIndices (keepComplete keep done) declared)
        (completeClaimFor accepted p)) = .justified := by
  apply production_justified_nonpromotion accepted keep _ done declared
      declAtts keptAtts p hargs hatts (fun k hk => hkept ▸ hk)
      (fun a _ h => referenceLive_of_keepComplete h) ?_ hstatus
  dsimp only
  rw [blockedSeed_eq_nil_of_keep_all hall hkept, blockedSet_nil]
  apply supportBlocked_nil
  intro k hk
  have hkC := claimSupportFor_mem_checkedAF (accepted := accepted) k hk
  have hlt := List.mem_range.mp hkC
  rw [hargs, List.length_map, retained_lengths_eq] at hlt
  exact hlt

/-! ### Checker-instantiated masks

A successful `checkUnit` call fixes `done` to its cache (`checkedDone`) and the
reference mask to `referenceLive`. On supported retained terms the checked and
declared contexts agree leafwise, so obligations transport exactly and the
production mask is the specification mask `notHole`. Full-declared inference
can fail only on pruned terms, which `referenceLive` keeps as nodes. -/

/-- The checker's AF arguments are the complete retention of the declarations
under its own cache: no support inference is rerun. -/
theorem checked_args_keepComplete {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {ground : List Atom} {sigma : Lara.Sigma.Sigma}
    {policy : Lara.Policy.Policy}
    {accepted : Lara.Unit.CheckedUnit canon Gamma (Lara.Support.certOkOf reg)}
    {keep : (String × SupportTerm) → Bool}
    {declared : List (String × SupportTerm)} {atts : List Attack}
    (hcheck : Lara.Check.Unit.checkUnit Gamma reg ground
      ({ sigma := sigma
       , policy := policy
       , args := (retainedArguments keep declared).map (·.2)
       , atts := atts } : Lara.Unit) = .ok accepted) :
    accepted.program.args =
      (retainedArguments (keepComplete keep (checkedDone accepted))
        declared).map (·.2) := by
  have hargs := (Lara.Check.Unit.checkUnit_sound hcheck).args_eq
  rw [keepComplete_terms]
  have hfilter :
      ((retainedArguments keep declared).map (·.2)).filter
          (checkedDone accepted) =
        Check.completeArgs policy.ruleLookup Gamma reg
          ((retainedArguments keep declared).map (·.2)) := by
    unfold Check.completeArgs
    apply List.filter_congr
    intro w hw
    simp only [checkedDone]
    rw [hargs]
    simp [Check.completeArgs, List.mem_filter, hw]
  rw [hfilter]
  exact hargs

/-- The checker's compiled attacks are the live filter of the attacks it was
given. -/
theorem checked_atts_live {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {ground : List Atom} {unit : Lara.Unit}
    {accepted : Lara.Unit.CheckedUnit canon Gamma (Lara.Support.certOkOf reg)}
    (hcheck : Lara.Check.Unit.checkUnit Gamma reg ground unit = .ok accepted) :
    accepted.program.atts =
      Check.liveAttacks accepted.program.args unit.atts :=
  (Lara.Check.Unit.checkUnit_sound hcheck).atts_eq

/-- **Obligation transport.** On every declaration the production reference
mask equals the specification mask `notHole` under the full declared context,
provided the checked context agrees with it on the leaves of every retained
term. A retained term types under the checked context (`raw_support`), so its
cached completeness is its obligation set's emptiness, which transports to the
declared context; a quarantined term is classified by `notHole` itself. -/
theorem referenceLive_eq_notHole {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {ground : List Atom} {sigma : Lara.Sigma.Sigma}
    {policy : Lara.Policy.Policy}
    {accepted : Lara.Unit.CheckedUnit canon Gamma (Lara.Support.certOkOf reg)}
    {keep : (String × SupportTerm) → Bool}
    {declared : List (String × SupportTerm)} {atts : List Attack}
    (GammaDecl : LeafId → Option Atom)
    (hcheck : Lara.Check.Unit.checkUnit Gamma reg ground
      ({ sigma := sigma
       , policy := policy
       , args := (retainedArguments keep declared).map (·.2)
       , atts := atts } : Lara.Unit) = .ok accepted)
    (hgamma : ∀ a, a ∈ declared → keep a = true →
      ∀ l ∈ leaves a.2, Gamma l = GammaDecl l) :
    ∀ a, a ∈ declared →
      referenceLive keep (checkedDone accepted) policy.ruleLookup GammaDecl reg a =
        notHole policy.ruleLookup GammaDecl reg a := by
  intro a ha
  cases hkeep : keep a with
  | false => simp [referenceLive, hkeep]
  | true =>
      have hsound := Lara.Check.Unit.checkUnit_sound hcheck
      have hmem : a.2 ∈ (retainedArguments keep declared).map (·.2) := by
        rw [retainedArguments_eq_filter]
        exact List.mem_map_of_mem (List.mem_filter.mpr ⟨ha, hkeep⟩)
      obtain ⟨C, O, hC⟩ := hsound.raw_support a.2 hmem
      have hdecl := hasSupport_congr_gamma_on hC (hgamma a ha hkeep)
      have hdone : checkedDone accepted a.2 = O.isEmpty := by
        simp only [checkedDone]
        rw [hsound.args_eq]
        simp only [Check.completeArgs, List.mem_filter, hmem, true_and,
          Bool.decide_eq_true]
        exact Check.argComplete_of_hasSupport hC
      simp only [referenceLive, hkeep, if_true, notHole,
        Check.argHole_of_hasSupport hdecl, hdone, Bool.not_not]

/-- `K ⊆ D` for the specification carrier: every retained complete declaration
is not a typed hole under the full declared context. -/
theorem checked_complete_subset_notHole {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {ground : List Atom} {sigma : Lara.Sigma.Sigma}
    {policy : Lara.Policy.Policy}
    {accepted : Lara.Unit.CheckedUnit canon Gamma (Lara.Support.certOkOf reg)}
    {keep : (String × SupportTerm) → Bool}
    {declared : List (String × SupportTerm)} {atts : List Attack}
    (GammaDecl : LeafId → Option Atom)
    (hcheck : Lara.Check.Unit.checkUnit Gamma reg ground
      ({ sigma := sigma
       , policy := policy
       , args := (retainedArguments keep declared).map (·.2)
       , atts := atts } : Lara.Unit) = .ok accepted)
    (hgamma : ∀ a, a ∈ declared → keep a = true →
      ∀ l ∈ leaves a.2, Gamma l = GammaDecl l) :
    ∀ i, i ∈ checkedCarrier accepted keep declared →
      i ∈ retainedIndices (notHole policy.ruleLookup GammaDecl reg) declared :=
  complete_subset_reference (fun a ha h =>
    (referenceLive_eq_notHole GammaDecl hcheck hgamma a ha) ▸
      referenceLive_of_keepComplete h)

/-- The executable reference carrier is the specification carrier. -/
theorem referenceLive_indices_eq_notHole {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {ground : List Atom} {sigma : Lara.Sigma.Sigma}
    {policy : Lara.Policy.Policy}
    {accepted : Lara.Unit.CheckedUnit canon Gamma (Lara.Support.certOkOf reg)}
    {keep : (String × SupportTerm) → Bool}
    {declared : List (String × SupportTerm)} {atts : List Attack}
    (GammaDecl : LeafId → Option Atom)
    (hcheck : Lara.Check.Unit.checkUnit Gamma reg ground
      ({ sigma := sigma
       , policy := policy
       , args := (retainedArguments keep declared).map (·.2)
       , atts := atts } : Lara.Unit) = .ok accepted)
    (hgamma : ∀ a, a ∈ declared → keep a = true →
      ∀ l ∈ leaves a.2, Gamma l = GammaDecl l) :
    referenceCarrier accepted keep policy.ruleLookup GammaDecl reg declared =
      retainedIndices (notHole policy.ruleLookup GammaDecl reg) declared :=
  retainedIndices_congr (referenceLive_eq_notHole GammaDecl hcheck hgamma)

/-- **Reference nodes are the complete declarations, under full typing.** If
every declaration types under the declared context, no reference node is
unclassified, and `D` is exactly the complete declared arguments. Without the
typing premise this fails: an ill-typed quarantined term is a node of `D` but
not complete. -/
theorem notHole_indices_eq_complete_of_typed {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {declared : List (String × SupportTerm)}
    (htyped : ∀ a, a ∈ declared →
      ∃ C O, HasSupport canon Pi Gamma (certOkOf reg) a.2 C O) :
    retainedIndices (notHole Pi Gamma reg) declared =
      retainedIndices (fun a => Check.argComplete Pi Gamma reg a.2) declared := by
  apply retainedIndices_congr
  intro a ha
  obtain ⟨C, O, hC⟩ := htyped a ha
  simp [notHole, Check.argHole_of_hasSupport hC,
    Check.argComplete_of_hasSupport hC]

/-- Fully checker-instantiated shipped-path theorem. A successful `checkUnit`
call supplies `hargs` and `hatts` and fixes the masks to its cache; callers
cannot assert a parallel compact AF. `K ⊆ D` holds by construction of
`referenceLive`, so this form needs no context premise. -/
theorem checked_production_justified_nonpromotion_of_not_blocked
    {RawAttack : Type}
    (reg : Lara.Support.BackendRegistry canon)
    (policy : Lara.Policy.Policy)
    (accepted : Lara.Unit.CheckedUnit canon Gamma (Lara.Support.certOkOf reg))
    (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm)) (declAtts : List Attack)
    (keepAttack : RawAttack → Bool) (rawAtts : List RawAttack)
    (queries : List Atom) (p : Atom) (sigma : Lara.Sigma.Sigma)
    (ground : List Atom) (GammaDecl : LeafId → Option Atom)
    (hcheck : Lara.Check.Unit.checkUnit Gamma reg ground
      ({ sigma := sigma
       , policy := policy
       , args := (retainedArguments keep declared).map (·.2)
       , atts := selectAligned keepAttack rawAtts declAtts } : Lara.Unit) =
        .ok accepted)
    (hpruned : declared.length ≠ (retainedArguments keep declared).length)
    (hp : p ∈ queries)
    (hnot : p ∉ blockedQueries keep (checkedDone accepted)
      (referenceLive keep (checkedDone accepted) policy.ruleLookup GammaDecl reg)
      declared declAtts (selectAligned keepAttack rawAtts declAtts)
      (fun q => claimSupportFor accepted q) queries)
    (hstatus : Grounded.statusC (Compile.checkedAF accepted.program)
      (completeClaimFor accepted p) = .justified) :
    Grounded.statusC
      (declaredAF declared declAtts
        (referenceCarrier accepted keep policy.ruleLookup GammaDecl reg declared))
      (liftClaim (checkedCarrier accepted keep declared)
        (completeClaimFor accepted p)) = .justified :=
  production_justified_nonpromotion_of_not_blocked
    accepted keep _ (checkedDone accepted) declared declAtts
      (selectAligned keepAttack rawAtts declAtts) queries p
      (checked_args_keepComplete hcheck) (checked_atts_live hcheck)
      (fun k hk => selectAligned_subset keepAttack rawAtts declAtts k hk)
      (fun _ _ h => referenceLive_of_keepComplete h)
      hpruned hp hnot hstatus

/-- The shipped-path theorem with the specification reference carrier: a
published `justified` query is `justified` in the framework whose nodes are
the declarations that are complete or unclassified under the full declared
context. `hgamma` is the leafwise agreement admission establishes for retained
terms. -/
theorem checked_production_justified_nonpromotion_notHole
    {RawAttack : Type}
    (reg : Lara.Support.BackendRegistry canon)
    (policy : Lara.Policy.Policy)
    (accepted : Lara.Unit.CheckedUnit canon Gamma (Lara.Support.certOkOf reg))
    (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm)) (declAtts : List Attack)
    (keepAttack : RawAttack → Bool) (rawAtts : List RawAttack)
    (queries : List Atom) (p : Atom) (sigma : Lara.Sigma.Sigma)
    (ground : List Atom) (GammaDecl : LeafId → Option Atom)
    (hcheck : Lara.Check.Unit.checkUnit Gamma reg ground
      ({ sigma := sigma
       , policy := policy
       , args := (retainedArguments keep declared).map (·.2)
       , atts := selectAligned keepAttack rawAtts declAtts } : Lara.Unit) =
        .ok accepted)
    (hgamma : ∀ a, a ∈ declared → keep a = true →
      ∀ l ∈ leaves a.2, Gamma l = GammaDecl l)
    (hpruned : declared.length ≠ (retainedArguments keep declared).length)
    (hp : p ∈ queries)
    (hnot : p ∉ blockedQueries keep (checkedDone accepted)
      (referenceLive keep (checkedDone accepted) policy.ruleLookup GammaDecl reg)
      declared declAtts (selectAligned keepAttack rawAtts declAtts)
      (fun q => claimSupportFor accepted q) queries)
    (hstatus : Grounded.statusC (Compile.checkedAF accepted.program)
      (completeClaimFor accepted p) = .justified) :
    Grounded.statusC
      (declaredAF declared declAtts
        (retainedIndices (notHole policy.ruleLookup GammaDecl reg) declared))
      (liftClaim (checkedCarrier accepted keep declared)
        (completeClaimFor accepted p)) = .justified := by
  rw [← referenceLive_indices_eq_notHole GammaDecl hcheck hgamma]
  exact checked_production_justified_nonpromotion_of_not_blocked reg policy
    accepted keep declared declAtts keepAttack rawAtts queries p sigma ground
    GammaDecl hcheck hpruned hp hnot hstatus

end Lara.BlockedProgram
