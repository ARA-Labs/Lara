/-
Certified source and full public-status impact (issue #22, plan P5).

**What this module adds.** P1 supplies the checked source observer
(`Lara.Process.Source.checkSource`) and the accepted observation; P4 supplies
checked graph-difference locality (`Lara.Process.Locality`). P5 records the
*impact* of swapping one complete source input for another:

* a **typed** read layer: the closed `ReadKey` sum is indexed by its exact value
  type (`ReadKey.Val`, with `ReadKey.decode` inverting the recorded shape), the
  recorded **read set covers every key the accompanied status calculation
  reads** (the compiled carrier and the ancestry attack rows), and the coverage
  is a theorem (`impactReads_covers_status`, `recorded_status_determined`), not
  a doc comment. The recorded reads are **side-tagged**, so one key carries
  exactly one value per endpoint (`impactReads_functional`).
* an `ImpactCertificate` data record: both complete input snapshots, replay
  identities and **per-endpoint outcome reports** (the exact `SourceRejection`
  payload, or the accepted run's reference/checked/compiled carriers, blocked
  closure and per-query support map), the exact four-way transition, the
  per-query full `Driver.PublicStatus` rows, the changed/unchanged partition,
  the node/support maps, the checked graph difference and checked locality facts,
  and the recorded reads;
* an executable `verifyImpact` that reruns the shared observer and recomputes
  every field, with a closed `VerificationResult`, and a proved **fault
  identity**: for every closed fault `f`, `firstFault c = some f` holds exactly
  when the earlier checks hold and `f`'s own condition fails
  (`firstFault_some_iff`);
* composition of P4's grounded locality with complete support equality and
  blocking equality into a `BHL.ordinaryStatus` preservation theorem. The
  conditional label inside `Driver.PublicStatus.evidenceBlocked` is retained:
  two blocked results with different labels are *different* statuses and land in
  the changed partition;
* the entitlement separation: public-status equality never transports
  entitlement, so impact records the failed-sibling graph/status/audit
  distinction instead of substituting a status certificate for an entitlement
  certificate.

**Scope.** Everything below is about `BHL.ordinaryStatus`, i.e. the grounded
four-state status of `Grounded.statusC` for the complete claim
`Consistency.completeClaimFor`. No equality of `Update.PublicReport` is
substituted for a full public status, and no stable-semantics claim is made.

**Read footprint honesty.** The keys the module *individually resolves and
consumes* are: the compiled carrier and its attack rows (read by
`Grounded.labelC`/`Grounded.statusC`), the reference/checked/compiled carriers,
the blocked closure and per-query blocked flag, and complete support/hole
membership (read by the run reconstruction). For these the exact footprint is
proved complete (`recordsReads_labelC`, `recordsReads_statusC`,
`statusC_reconstruct_of_reads`).

The material-inventory keys (leaf contents and metadata; rule and admission
lookups including the absent lookup; duplicate-group membership and conflicting
values; raw endpoint resolution and retention maps; signature, policy contraries
and substitution; backend theory/digest/certificate inputs; premise and
discharge subterms; normalized conclusion-to-query equivalence) are read by the
audit phase of `Source.checkSource`, for which **no smaller-than-whole footprint
is proved here**. Following the plan's conservative fallback, their recorded
value is the *whole `SourceInput` that supplies them*: `ReadKey.Val` gives them
`Source.SourceInput` and `inputReading` resolves every one of them to
`.source i`. `inputReading_accepts` proves each is well-typed, and the whole-input
binding is complete for the reused run-level calculations over the finite
two-key `Side` space (`recordsReads_transitionOf_input`,
`recordsReads_blockedQueries_input`, `recordsReads_statusRow_input`,
`recordsReads_outcomeRecord_input`), so each is instantiated. `RecordsReads.whole`
is instantiated at that space (`recordsReads_whole_input`); it is *not* claimed
at `ReadKey`, which is not finite.

`Support.certDeps` reports backend acceptance dependencies and is **not** a
complete dependency footprint for source status; this module never uses it as
one.
-/

import Lara.Process.Locality
import Lara.Blocked

namespace Lara.Process.Impact

open Lara.Grounded

/-! ### Endpoints and the closed read keys -/

/-- The endpoint of a source comparison. Every recorded read is tagged by its
side, so one `ReadKey` carries at most one value per endpoint. -/
inductive Side where
  | before
  | after
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The material a source status calculation reads. Each constructor names one
kind of read; the indexed identity is the declaration/rule/leaf it applies to.
`supportMember`/`holeMember` are indexed by the query and the checked node, so
membership is per-query and typed rather than flat.

The material-inventory constructors (leaf contents through conclusion
equivalence) are whole-input bound: no smaller-than-whole footprint is proved
for the audit phase, so their recorded value is the entire `SourceInput` (see
`ReadKey.Val` and the module note). The compiled-graph reads
(`compiledCarrier`, `attackEdge`) are the grounded label/status reads, and
`referenceCarrier`/`checkedCarrier` keep the reference/checked distinction of
`Update.referenceCarrierForRun`/`Update.checkedCarrierForRun`.

`Support.certDeps` (the strict-certificate backend dependency report) is **not**
an element of this inventory and is never used as a footprint for source
status. -/
inductive ReadKey where
  /- material inventory: whole-input bound -/
  | leafContent : Support.LeafId → ReadKey
  | leafMeta : Support.LeafId → ReadKey
  | ruleLookup : Presentation.ArgId → ReadKey
  | admissionLookup : Presentation.ArgId → ReadKey
  | absentLookup : Presentation.ArgId → ReadKey
  | groupMember : Presentation.ArgId → ReadKey
  | groupConflict : Presentation.ArgId → ReadKey
  | rawEndpoint : Nat → ReadKey
  | retention : Nat → ReadKey
  | signature : Presentation.ArgId → ReadKey
  | policyContrary : Presentation.ArgId → ReadKey
  | substitution : Presentation.ArgId → ReadKey
  | backendTheory : Support.BackendId → ReadKey
  | backendDigest : Support.BackendId → ReadKey
  | certificateInput : Support.BackendId → ReadKey
  | premiseSubterm : Nat → ReadKey
  | dischargeSubterm : Nat → ReadKey
  | conclusionEquiv : Presentation.ArgId → ReadKey
  /- run-level reads, individually resolved from the checked run -/
  | supportMember : Atom → Nat → ReadKey
  | holeMember : Atom → Nat → ReadKey
  | referenceCarrier : ReadKey
  | checkedCarrier : ReadKey
  | compiledCarrier : ReadKey
  | blockedClosure : ReadKey
  | blockedQuery : Atom → ReadKey
  | supportNodes : Atom → ReadKey
  | holeNodes : Atom → ReadKey
  /- compiled-graph reads consumed by the grounded label/status calculation -/
  | attackEdge : Grounded.Arg → Grounded.Arg → ReadKey
  /- the conservative whole-input read -/
  | wholeInput : ReadKey
  deriving DecidableEq

/-- The exact value of a read. A closed sum of value shapes; each `ReadKey`
resolves to the constructor matching its kind. `absent` records an *absent
lookup* result. `source` is the whole-input shape of the conservative fallback. -/
inductive ReadVal where
  | absent : ReadVal
  | atom : Atom → ReadVal
  | atoms : List Atom → ReadVal
  | nat : Nat → ReadVal
  | nats : List Nat → ReadVal
  | bool : Bool → ReadVal
  | name : Presentation.ArgId → ReadVal
  | names : List Presentation.ArgId → ReadVal
  | text : String → ReadVal
  | texts : List String → ReadVal
  /-- the whole input that supplies a whole-input-bound material read -/
  | source : Source.SourceInput → ReadVal
  deriving DecidableEq

/-- Read a boolean out of a value, falling back to the supplied default. -/
def ReadVal.boolD : ReadVal → Bool → Bool
  | .bool v, _ => v
  | _, d => d

/-- The direct attack-row value recorded in a read environment, defaulting to
`false` for a non-boolean entry. -/
def ReadVal.attackD (v : ReadVal) : Bool := v.boolD false

/-- **The value type of a read key.** Every key is indexed by the exact shape of
its recorded value: the compiled/run-level keys by their concrete carrier,
closure and membership types, the material inventory by the whole `SourceInput`
that supplies it (the plan's conservative fallback), and `wholeInput` by the
whole input itself. -/
def ReadKey.Val : ReadKey → Type
  | .referenceCarrier => List Nat
  | .checkedCarrier => List Nat
  | .compiledCarrier => List Grounded.Arg
  | .blockedClosure => List Atom
  | .blockedQuery _ => Bool
  | .supportNodes _ => List Nat
  | .holeNodes _ => List Nat
  | .supportMember _ _ => Bool
  | .holeMember _ _ => Bool
  | .attackEdge _ _ => Bool
  | .wholeInput => Source.SourceInput
  | _ => Source.SourceInput

/-- Decode a uniform recorded value into the value type of its key. Each key
kind accepts exactly the shape it names; the material inventory decodes the
whole-input shape it is bound to. -/
def ReadKey.decode : (k : ReadKey) → ReadVal → Option (ReadKey.Val k)
  | .referenceCarrier, .nats l => some l
  | .checkedCarrier, .nats l => some l
  | .compiledCarrier, .nats l => some l
  | .blockedClosure, .atoms l => some l
  | .blockedQuery _, .bool b => some b
  | .supportNodes _, .nats l => some l
  | .holeNodes _, .nats l => some l
  | .supportMember _ _, .bool b => some b
  | .holeMember _ _, .bool b => some b
  | .attackEdge _ _, .bool b => some b
  | .wholeInput, .source i => some i
  | .leafContent _, .source i => some i
  | .leafMeta _, .source i => some i
  | .ruleLookup _, .source i => some i
  | .admissionLookup _, .source i => some i
  | .absentLookup _, .source i => some i
  | .groupMember _, .source i => some i
  | .groupConflict _, .source i => some i
  | .rawEndpoint _, .source i => some i
  | .retention _, .source i => some i
  | .signature _, .source i => some i
  | .policyContrary _, .source i => some i
  | .substitution _, .source i => some i
  | .backendTheory _, .source i => some i
  | .backendDigest _, .source i => some i
  | .certificateInput _, .source i => some i
  | .premiseSubterm _, .source i => some i
  | .dischargeSubterm _, .source i => some i
  | .conclusionEquiv _, .source i => some i
  | _, _ => none

/-- A recorded value is admitted for a key exactly when it decodes. -/
def ReadKey.accepts (k : ReadKey) (v : ReadVal) : Bool := (k.decode v).isSome

/-! ### The grounded read footprint

The grounded label at `a` reads the carrier and the incoming attack rows of
`a`'s ancestry; the four-state status additionally reads each support member's
ancestry. These are the *small* footprints the locality layer justifies. -/

/-- The attack rows of a region: for every region member `y` and every carrier
member `x`, the row `x ↦ y`. -/
def regionRows (F : Grounded.AF) (region : List Grounded.Arg) : List ReadKey :=
  region.flatMap fun y => F.args.map fun x => ReadKey.attackEdge x y

/-- The attack-row read of a region: the carrier plus every region attack row. -/
def regionReads (F : Grounded.AF) (region : List Grounded.Arg) : Finset ReadKey :=
  (ReadKey.compiledCarrier :: regionRows F region).toFinset

theorem mem_regionRows {F : Grounded.AF} {region : List Grounded.Arg}
    {x y : Grounded.Arg} :
    ReadKey.attackEdge x y ∈ regionRows F region ↔ x ∈ F.args ∧ y ∈ region := by
  unfold regionRows
  simp only [List.mem_flatMap, List.mem_map, ReadKey.attackEdge.injEq]
  constructor
  · rintro ⟨b, hb, a, ha, he⟩
    exact ⟨he.1 ▸ ha, he.2 ▸ hb⟩
  · rintro ⟨hx, hy⟩
    exact ⟨y, hy, x, hx, ⟨rfl, rfl⟩⟩

/-- Every attack-row member is an `attackEdge` key. -/
theorem exists_attackEdge_of_mem_regionRows {F : Grounded.AF} {region : List Grounded.Arg}
    {k : ReadKey} (hk : k ∈ regionRows F region) :
    ∃ x y, k = ReadKey.attackEdge x y := by
  unfold regionRows at hk
  obtain ⟨y, _, hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨x, _, hx⟩ := List.mem_map.mp hk
  exact ⟨x, y, hx.symm⟩

/-- The read footprint of the grounded label at `a`. -/
def labelReads (F : Grounded.AF) (a : Grounded.Arg) : Finset ReadKey :=
  regionReads F (Ancestry.ancestors F [a])

/-- The read footprint of the four-state status of a complete claim. -/
def statusReads (F : Grounded.AF) (c : Grounded.Claim) : Finset ReadKey :=
  insert ReadKey.compiledCarrier
    ((c.support.toFinset.product F.args.toFinset).image fun p =>
      ReadKey.attackEdge p.2 p.1) ∪
    (c.support.toFinset.biUnion fun i => labelReads F i)

theorem mem_regionReads_attack {F : Grounded.AF} {region : List Grounded.Arg}
    {x y : Grounded.Arg} :
    ReadKey.attackEdge x y ∈ regionReads F region ↔
      x ∈ F.args ∧ y ∈ region := by
  unfold regionReads
  rw [List.mem_toFinset, List.mem_cons, mem_regionRows]
  constructor
  · rintro (h | h)
    · exact absurd h (fun hc => by cases hc)
    · exact h
  · exact Or.inr

theorem mem_labelReads_attack {F : Grounded.AF} {a x y : Grounded.Arg} :
    ReadKey.attackEdge x y ∈ labelReads F a ↔
      x ∈ F.args ∧ y ∈ Ancestry.ancestors F [a] :=
  mem_regionReads_attack

/-- Every member of a status footprint is the compiled carrier or an attack row:
the status calculation reads nothing else. -/
theorem mem_statusReads_shape {F : Grounded.AF} {c : Grounded.Claim} {k : ReadKey}
    (hk : k ∈ statusReads F c) :
    k = ReadKey.compiledCarrier ∨ ∃ x y, k = ReadKey.attackEdge x y := by
  have h' : k ∈ statusReads F c := hk
  rw [statusReads] at h'
  rw [Finset.mem_union] at h'
  rcases h' with h | h
  · rw [Finset.mem_insert] at h
    rcases h with h | h
    · exact Or.inl h
    · obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨p.2, p.1, hp.symm⟩
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
    rw [labelReads, regionReads, List.mem_toFinset, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact Or.inl rfl
    · obtain ⟨x, y, hxy⟩ := exists_attackEdge_of_mem_regionRows hi
      exact Or.inr ⟨x, y, hxy⟩

/-- A read environment: the value recorded for every read key. -/
abbrev ReadEnv := ReadKey → ReadVal

/-- A side-tagged read environment: the value recorded for every key on every
endpoint. One key has one value per side by construction. -/
abbrev SReadEnv := Side × ReadKey → ReadVal

/-- The read environment of one side of a side-tagged environment. -/
def sideEnv (e : SReadEnv) (s : Side) : ReadEnv := fun k => e (s, k)

/-- The environment that records `F`'s own material. -/
def reading (F : Grounded.AF) : ReadEnv := fun k =>
  match k with
  | .compiledCarrier => .nats F.args
  | .attackEdge x y => .bool (F.attack x y)
  | _ => .absent

/-- Rebuild a framework from an environment, but only through the recorded
read set: an unrecorded attack row falls back to the basis framework's row, so
two environments agreeing on the read set decode to the same framework. -/
def decodeAgainst (F : Grounded.AF) (reads : Finset ReadKey) (e : ReadEnv) : Grounded.AF :=
  ⟨F.args, fun x y =>
    if ReadKey.attackEdge x y ∈ reads then (e (ReadKey.attackEdge x y)).boolD (F.attack x y)
    else F.attack x y⟩

theorem decodeAgainst_args (F : Grounded.AF) (reads : Finset ReadKey) (e : ReadEnv) :
    (decodeAgainst F reads e).args = F.args := rfl

theorem decodeAgainst_attack (F : Grounded.AF) (reads : Finset ReadKey) (e : ReadEnv)
    (x y : Grounded.Arg) :
    (decodeAgainst F reads e).attack x y =
      if ReadKey.attackEdge x y ∈ reads then (e (ReadKey.attackEdge x y)).boolD (F.attack x y)
      else F.attack x y := rfl

theorem decodeAgainst_ext {F : Grounded.AF} {reads : Finset ReadKey} {e₁ e₂ : ReadEnv}
    (agree : ∀ k ∈ reads, e₁ k = e₂ k) :
    decodeAgainst F reads e₁ = decodeAgainst F reads e₂ := by
  apply congrArg (Grounded.AF.mk F.args)
  funext x y
  by_cases hk : ReadKey.attackEdge x y ∈ reads
  · simp only [hk, if_true, agree _ hk]
  · simp only [hk, if_false]

/-! ### RecordsReads for the reused grounded calculations -/

/-- **Conservative whole-table read.** Any check is recorded by the complete
table: if two environments agree everywhere, they are equal, so the check
cannot separate them. This is the honest fallback used for the opaque run-level
calculations; it is instantiated below at the finite two-key `Side` space
(`recordsReads_whole_input`), never at the infinite `ReadKey`. -/
theorem RecordsReads.whole {K V : Type} [Fintype K] [DecidableEq K]
    (check : (K → V) → Bool) : RecordsReads check Finset.univ := by
  intro e₁ e₂ agree
  rw [funext fun k => agree k (Finset.mem_univ k)]

/-- A recorded footprint is closed under extension: larger footprints are still
complete. -/
theorem RecordsReads.mono {K V : Type} {check : (K → V) → Bool} {s t : Finset K}
    (sub : s ⊆ t) (recorded : RecordsReads check s) : RecordsReads check t :=
  fun e₁ e₂ agree => recorded e₁ e₂ fun k hk => agree k (sub hk)

/-- **`RecordsReads` for the grounded label** with the ancestry footprint. The
decoded label is a function of the recorded read set alone. -/
theorem recordsReads_labelC (F : Grounded.AF) (a : Grounded.Arg) :
    RecordsReads (fun e => decide (labelC (decodeAgainst F (labelReads F a) e) a =
      labelC F a)) (labelReads F a) := by
  intro e₁ e₂ agree
  have hAF := decodeAgainst_ext (F := F)
    (reads := labelReads F a) (e₁ := e₁) (e₂ := e₂) agree
  simp only [hAF]

/-- **`RecordsReads` for the four-state status** with the support footprint. -/
theorem recordsReads_statusC (F : Grounded.AF) (c : Grounded.Claim) :
    RecordsReads (fun e => decide (statusC (decodeAgainst F (statusReads F c) e) c =
      statusC F c)) (statusReads F c) := by
  intro e₁ e₂ agree
  have hAF := decodeAgainst_ext (F := F)
    (reads := statusReads F c) (e₁ := e₁) (e₂ := e₂) agree
  simp only [hAF]

/-- **Complete-read preservation for the grounded label.** Reading the carrier
and the ancestry attack rows faithfully reproduces `F`'s own label: the recorded
footprint is complete, so it may be used as a smaller-than-whole read. -/
theorem labelC_reuse_of_reads {F : Grounded.AF} {a : Grounded.Arg} (ha : a ∈ F.args)
    {reads : Finset ReadKey}
    (covers : ∀ x y, x ∈ F.args → y ∈ Ancestry.ancestors F [a] →
      ReadKey.attackEdge x y ∈ reads)
    {e : ReadEnv} (faithful : ∀ k ∈ reads, e k = reading F k) :
    labelC (decodeAgainst F reads e) a = labelC F a := by
  have hseed : ∀ b ∈ [a], b ∈ F.args := by
    intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact ha
  have hmem : ∀ y, Ancestor F a y → y ∈ Ancestry.ancestors F [a] :=
    fun y hanc => (Ancestry.mem_ancestors_iff hseed).mpr ⟨a, List.mem_singleton_self a, hanc⟩
  have hrow : ∀ y, Ancestor F a y → ∀ x,
      (x ∈ F.args ∧ F.attack x y = true) ↔
        (x ∈ (decodeAgainst F reads e).args ∧
          (decodeAgainst F reads e).attack x y = true) := by
    intro y hy x
    have hyanc : y ∈ Ancestry.ancestors F [a] := hmem y hy
    constructor
    · rintro ⟨hx, hatt⟩
      have hr : (decodeAgainst F reads e).attack x y = F.attack x y := by
        simp only [decodeAgainst]
        rw [if_pos (covers x y hx hyanc), faithful _ (covers x y hx hyanc)]
        rfl
      exact ⟨hx, by rw [hr]; exact hatt⟩
    · rintro ⟨hx, hatt⟩
      have hr : (decodeAgainst F reads e).attack x y = F.attack x y := by
        simp only [decodeAgainst]
        rw [if_pos (covers x y hx hyanc), faithful _ (covers x y hx hyanc)]
        rfl
      rw [hr] at hatt
      exact ⟨hx, hatt⟩
  exact (grounded_directional_locality (F := F) (G := decodeAgainst F reads e) (t := a) ha
    (fun y hy => Ancestry.ancestors_subset_args (F := F) (S := [a]) (hmem y hy)) hrow).symm

/-- The ancestry-footprint specialization of complete-read preservation. -/
theorem labelC_reuse_labelReads {F : Grounded.AF} {a : Grounded.Arg} (ha : a ∈ F.args)
    {e : ReadEnv} (faithful : ∀ k ∈ labelReads F a, e k = reading F k) :
    labelC (decodeAgainst F (labelReads F a) e) a = labelC F a :=
  labelC_reuse_of_reads ha (fun _ _ hx hy => mem_labelReads_attack.mpr ⟨hx, hy⟩) faithful

/-- **Complete-read preservation for the four-state status.** With exact support
membership, faithfully reading each support member's ancestry reproduces the
status. -/
theorem statusC_reuse_of_reads {F : Grounded.AF} {c : Grounded.Claim}
    (hsub : ∀ i ∈ c.support, i ∈ F.args)
    {reads : Finset ReadKey}
    (covers : ∀ i ∈ c.support, ∀ x y, x ∈ F.args → y ∈ Ancestry.ancestors F [i] →
      ReadKey.attackEdge x y ∈ reads)
    {e : ReadEnv} (faithful : ∀ k ∈ reads, e k = reading F k) :
    statusC (decodeAgainst F reads e) c = statusC F c := by
  have labels : ∀ i ∈ c.support,
      labelC F i = labelC (decodeAgainst F reads e) i :=
    fun i hi => (labelC_reuse_of_reads (hsub i hi) (covers i hi) faithful).symm
  exact (Locality.statusC_of_support_labels
    (F := F) (G := decodeAgainst F reads e) (cF := c) (cG := c)
    (fun _ => Iff.rfl) labels).symm

/-! ### Reconstructing a framework from reads alone

`decodeAgainst` keeps the basis framework's rows outside the recorded set, so its
`RecordsReads` law is about the recorded set being *stable* under the decode.
To read a framework out of an environment with no basis, `reconstruct` takes the
carrier and every attack row straight from the environment (absent means
`false`). Two environments that differ outside the recorded footprint now really
do reconstruct different graphs; locality is what shows the footprint still
suffices for the label and the status. -/

/-- Reconstruct a framework from an environment alone. -/
def reconstruct (e : ReadEnv) : Grounded.AF :=
  ⟨(match e ReadKey.compiledCarrier with | .nats l => l | _ => []),
   fun x y => (e (ReadKey.attackEdge x y)).attackD⟩

theorem reconstruct_args (e : ReadEnv) :
    (reconstruct e).args =
      (match e ReadKey.compiledCarrier with | .nats l => l | _ => []) := rfl

theorem reconstruct_attack (e : ReadEnv) (x y : Grounded.Arg) :
    (reconstruct e).attack x y = (e (ReadKey.attackEdge x y)).attackD := rfl

/-- Reading a framework's own material reconstructs that framework. -/
theorem reconstruct_reading (F : Grounded.AF) : reconstruct (reading F) = F := by
  apply congrArg (Grounded.AF.mk F.args)
  funext x y
  simp [reading, ReadVal.attackD, ReadVal.boolD]

/-- **Ancestry containment for a reconstruction.** If an environment agrees with
`F`'s carrier and with `F`'s ancestry rows, every ancestor it reconstructs was
already an ancestor of `F`. -/
theorem ancestor_reconstruct_mem {F : Grounded.AF} {a y : Grounded.Arg} {e : ReadEnv}
    (ha : a ∈ F.args)
    (hcar : e ReadKey.compiledCarrier = .nats F.args)
    (hrows : ∀ x y, x ∈ F.args → y ∈ Ancestry.ancestors F [a] →
      e (ReadKey.attackEdge x y) = .bool (F.attack x y))
    (h : Ancestor (reconstruct e) a y) : y ∈ Ancestry.ancestors F [a] := by
  induction h with
  | self => exact Ancestry.ancestors_seed ha (List.mem_singleton_self a)
  | attacker hanc hx hatt ih =>
      rename_i x y
      have hxargs : x ∈ F.args := by
        rw [reconstruct_args, hcar] at hx
        exact hx
      have hxy : F.attack x y = true := by
        rw [reconstruct_attack, hrows x y hxargs ih] at hatt
        simpa [ReadVal.attackD, ReadVal.boolD] using hatt
      exact Ancestry.ancestors_closed ih hxargs hxy

/-- **Complete-read preservation for the grounded label, genuinely locality-based.**
An environment faithful on `a`'s ancestry footprint — with no basis fallback —
reconstructs a framework with the same grounded label at `a`. The proof is
`grounded_directional_locality` on the reconstructed ancestor region. -/
theorem labelC_reconstruct_of_reads {F : Grounded.AF} {a : Grounded.Arg} (ha : a ∈ F.args)
    {e : ReadEnv} (hcar : e ReadKey.compiledCarrier = .nats F.args)
    (hrows : ∀ x y, x ∈ F.args → y ∈ Ancestry.ancestors F [a] →
      e (ReadKey.attackEdge x y) = .bool (F.attack x y)) :
    labelC (reconstruct e) a = labelC F a := by
  refine grounded_directional_locality (F := reconstruct e) (G := F) (t := a) ?_ ?_ ?_
  · rw [reconstruct_args, hcar]
    exact ha
  · intro y hy
    exact Ancestry.ancestors_subset_args (ancestor_reconstruct_mem ha hcar hrows hy)
  · intro y hy x
    have hyR := ancestor_reconstruct_mem ha hcar hrows hy
    have hxargs : x ∈ (reconstruct e).args ↔ x ∈ F.args := by
      rw [reconstruct_args, hcar]
    constructor
    · rintro ⟨hx, hatt⟩
      refine ⟨hxargs.mp hx, ?_⟩
      rw [reconstruct_attack, hrows x y (hxargs.mp hx) hyR] at hatt
      simpa [ReadVal.attackD, ReadVal.boolD] using hatt
    · rintro ⟨hx, hatt⟩
      refine ⟨hxargs.mpr hx, ?_⟩
      rw [reconstruct_attack, hrows x y hx hyR]
      simp [ReadVal.attackD, ReadVal.boolD, hatt]

/-- The ancestry-footprint form of `labelC_reconstruct_of_reads`. -/
theorem labelC_reconstruct_labelReads {F : Grounded.AF} {a : Grounded.Arg} (ha : a ∈ F.args)
    {e : ReadEnv} (faithful : ∀ k ∈ labelReads F a, e k = reading F k) :
    labelC (reconstruct e) a = labelC F a := by
  have hcar : e ReadKey.compiledCarrier = .nats F.args := by
    have hm : ReadKey.compiledCarrier ∈ labelReads F a := by
      unfold labelReads regionReads
      rw [List.mem_toFinset, List.mem_cons]
      exact Or.inl rfl
    rw [faithful _ hm, reading]
  refine labelC_reconstruct_of_reads ha hcar ?_
  intro x y hx hy
  have hm : ReadKey.attackEdge x y ∈ labelReads F a := mem_labelReads_attack.mpr ⟨hx, hy⟩
  rw [faithful _ hm, reading]

/-- A support member's ancestry reads are contained in the status footprint. -/
theorem mem_statusReads_of_labelReads {F : Grounded.AF} {c : Grounded.Claim}
    {i : Grounded.Arg} (hi : i ∈ c.support) {k : ReadKey} (hk : k ∈ labelReads F i) :
    k ∈ statusReads F c := by
  unfold statusReads
  exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
    ⟨i, List.mem_toFinset.mpr hi, hk⟩))

/-- **Complete-read preservation for the four-state status, genuinely
locality-based.** -/
theorem statusC_reconstruct_of_reads {F : Grounded.AF} {c : Grounded.Claim}
    (hsub : ∀ i ∈ c.support, i ∈ F.args)
    {e : ReadEnv} (faithful : ∀ k ∈ statusReads F c, e k = reading F k) :
    statusC (reconstruct e) c = statusC F c := by
  have hcar : e ReadKey.compiledCarrier = .nats F.args := by
    have hm : ReadKey.compiledCarrier ∈ statusReads F c := by
      unfold statusReads
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_insert_self _ _))
    rw [faithful _ hm, reading]
  have labels : ∀ i ∈ c.support, labelC F i = labelC (reconstruct e) i := by
    intro i hi
    have hrows : ∀ x y, x ∈ F.args → y ∈ Ancestry.ancestors F [i] →
        e (ReadKey.attackEdge x y) = .bool (F.attack x y) := by
      intro x y hx hy
      have hm : ReadKey.attackEdge x y ∈ statusReads F c :=
        mem_statusReads_of_labelReads hi (mem_labelReads_attack.mpr ⟨hx, hy⟩)
      rw [faithful _ hm, reading]
    exact (labelC_reconstruct_of_reads (hsub i hi) hcar hrows).symm
  exact (Locality.statusC_of_support_labels (F := F) (G := reconstruct e)
    (cF := c) (cG := c) (fun _ => Iff.rfl) labels).symm

/-- The side-tagged lift of grounded status preservation: the reads recorded
under one side determine that endpoint's four-state status. -/
theorem statusC_reconstruct_of_reads_side {F : Grounded.AF} {c : Grounded.Claim}
    (hsub : ∀ i ∈ c.support, i ∈ F.args) (s : Side) {e : SReadEnv}
    (faithful : ∀ k ∈ statusReads F c, sideEnv e s k = reading F k) :
    statusC (reconstruct (sideEnv e s)) c = statusC F c :=
  statusC_reconstruct_of_reads hsub faithful

/-! ### The checked run of a source input

These definitions resolve the run-level keys from the source input's checked
run. They are the bridge between the read layer and the reused observer. -/

/-- The compiled grounded carrier of a source input (empty when rejected). -/
def carrierOf (i : Source.SourceInput) : List Grounded.Arg :=
  match Source.checkSource i with
  | .ok o => (Compile.checkedAF o.run.checked.program).args
  | .error _ => []

/-- The compiled grounded attack relation of a source input (empty when
rejected). -/
def attackOf (i : Source.SourceInput) (x y : Grounded.Arg) : Bool :=
  match Source.checkSource i with
  | .ok o => (Compile.checkedAF o.run.checked.program).attack x y
  | .error _ => false

/-- The compiled grounded framework of a source input. -/
def compiledAF (i : Source.SourceInput) : Grounded.AF := ⟨carrierOf i, attackOf i⟩

/-- The complete checked claim of one query (the empty claim when rejected). -/
def claimOfInput (i : Source.SourceInput) (q : Atom) : Grounded.Claim :=
  match Source.checkSource i with
  | .ok o => Consistency.completeClaimFor o.run.checked q
  | .error _ => ⟨[], []⟩

/-- The complete-support names of one query (empty when rejected). -/
def supportsOf (i : Source.SourceInput) (q : Atom) : List Presentation.ArgId :=
  match Source.checkSource i with
  | .ok o => Source.Coordinates.supports o.run q
  | .error _ => []

/-- The stable presentation names of a source input's checked carrier (empty
when rejected). -/
def namesOf (i : Source.SourceInput) : List Presentation.ArgId :=
  match Source.checkSource i with
  | .ok o => Source.Coordinates.names o.run
  | .error _ => []

/-- The reference carrier read of a source input. -/
def referenceCarrierOf (i : Source.SourceInput) : List Nat :=
  match Source.checkSource i with
  | .ok o => Update.referenceCarrierForRun o.run
  | .error _ => []

/-- The checked carrier read of a source input. -/
def checkedCarrierOf (i : Source.SourceInput) : List Nat :=
  match Source.checkSource i with
  | .ok o => Update.checkedCarrierForRun o.run
  | .error _ => []

/-- The production blocked-query decision on one endpoint. -/
def blockedQueriesOf (i : Source.SourceInput) (queries : List Atom) : List Atom :=
  match Source.checkSource i with
  | .ok o => Update.blockedQueriesForRun o.run queries
  | .error _ => []

/-- The single-query blocked flag `BHL.ordinaryStatus` reads. -/
def blockedQueryOf (i : Source.SourceInput) (q : Atom) : Bool :=
  match Source.checkSource i with
  | .ok o => decide (q ∈ Update.blockedQueriesForRun o.run [q])
  | .error _ => false

/-- The exact checker outcome as a decidable record: the rejection payload, or
`none` when accepted. -/
def outcomeRecord (i : Source.SourceInput) : Option Source.SourceRejection :=
  match Source.checkSource i with
  | .ok _ => none
  | .error r => some r

/-- One query's full public status using `BHL.ordinaryStatus` (`none` when the
endpoint is rejected — a rejection never fabricates a status). -/
def statusRowOf (i : Source.SourceInput) (q : Atom) : Option Driver.PublicStatus :=
  match Source.checkSource i with
  | .ok o => some (BHL.ordinaryStatus o.run q)
  | .error _ => none

/-- All requested queries' full public-status rows for one endpoint. -/
def statusRowsOf (i : Source.SourceInput) (queries : List Atom) :
    List (Atom × Option Driver.PublicStatus) :=
  queries.map fun q => (q, statusRowOf i q)

/-! ### The canonical reading of one source

`inputReading` resolves every key from the source input and its checked run.
Every individually-resolved key is consumed by a reused calculation; the
material-inventory keys are whole-input bound and resolve to `.source i`. -/

/-- The canonical reading of one source over a fixed query list. -/
def inputReading (i : Source.SourceInput) (queries : List Atom) : ReadEnv := fun k =>
  match k with
  | .wholeInput => .source i
  | .compiledCarrier => .nats (carrierOf i)
  | .attackEdge x y => .bool (attackOf i x y)
  | .referenceCarrier => .nats (referenceCarrierOf i)
  | .checkedCarrier => .nats (checkedCarrierOf i)
  | .blockedClosure => .atoms (blockedQueriesOf i queries)
  | .blockedQuery q => .bool (blockedQueryOf i q)
  | .supportNodes q => .nats (claimOfInput i q).support
  | .holeNodes q => .nats (claimOfInput i q).holes
  | .supportMember q n => .bool (decide (n ∈ (claimOfInput i q).support))
  | .holeMember q n => .bool (decide (n ∈ (claimOfInput i q).holes))
  | _ => .source i

/-- **Every key is well-typed under the canonical reading.** The material
inventory decodes the whole input that supplies it; the resolved keys decode
their concrete shapes. -/
theorem inputReading_accepts (i : Source.SourceInput) (queries : List Atom) (k : ReadKey) :
    ReadKey.accepts k (inputReading i queries k) = true := by
  cases k <;> rfl

theorem inputReading_compiledCarrier (i queries) :
    inputReading i queries ReadKey.compiledCarrier = ReadVal.nats (carrierOf i) := rfl

theorem inputReading_attack (i queries) (x y : Grounded.Arg) :
    inputReading i queries (ReadKey.attackEdge x y) = ReadVal.bool (attackOf i x y) := rfl

theorem inputReading_wholeInput (i queries) :
    inputReading i queries ReadKey.wholeInput = ReadVal.source i := rfl

/-- The material-inventory keys: read only through the whole-input-bound audit
phase, so their recorded value is the whole input that supplies them. -/
def ReadKey.material : ReadKey → Bool
  | .leafContent _ | .leafMeta _ | .ruleLookup _ | .admissionLookup _ | .absentLookup _
  | .groupMember _ | .groupConflict _ | .rawEndpoint _ | .retention _ | .signature _
  | .policyContrary _ | .substitution _ | .backendTheory _ | .backendDigest _
  | .certificateInput _ | .premiseSubterm _ | .dischargeSubterm _ | .conclusionEquiv _ => true
  | _ => false

/-- **The whole-input read determines every material-inventory key.** No material
key has a smaller-than-whole footprint: agreeing on the `wholeInput` read agrees
on every material read, so the conservative binding is complete for them. -/
theorem materialReads_determined_by_wholeInput (i i' : Source.SourceInput)
    (queries : List Atom)
    (h : inputReading i queries ReadKey.wholeInput =
      inputReading i' queries ReadKey.wholeInput) :
    ∀ k : ReadKey, ReadKey.material k = true →
      inputReading i queries k = inputReading i' queries k := by
  have h' : ReadVal.source i = ReadVal.source i' := by
    simpa only [inputReading] using h
  have hii : i = i' := by cases h'; rfl
  subst hii
  intro k _
  rfl

/-- On the grounded footprint, the canonical reading is the grounded reading of
the compiled framework. -/
theorem inputReading_eq_reading_of_grounded {i : Source.SourceInput} {queries : List Atom}
    {k : ReadKey}
    (hk : k = ReadKey.compiledCarrier ∨ ∃ x y, k = ReadKey.attackEdge x y) :
    inputReading i queries k = reading (compiledAF i) k := by
  rcases hk with rfl | ⟨x, y, rfl⟩
  · rfl
  · rfl

/-- The canonical reading reconstructs the compiled framework. -/
theorem reconstruct_inputReading (i : Source.SourceInput) (queries : List Atom) :
    reconstruct (inputReading i queries) = compiledAF i := by
  have hA : (match inputReading i queries ReadKey.compiledCarrier with
      | ReadVal.nats l => l | _ => []) = carrierOf i := rfl
  have hB : (fun x y => (inputReading i queries (ReadKey.attackEdge x y)).attackD) =
      attackOf i := by
    funext x y
    rfl
  unfold reconstruct compiledAF
  rw [hA, hB]

/-- The compiled complete support lies in the compiled carrier. -/
theorem claimOfInput_support_mem (i : Source.SourceInput) (q : Atom) :
    ∀ n ∈ (claimOfInput i q).support, n ∈ (compiledAF i).args := by
  intro n hn
  have hcompiled : (compiledAF i).args = carrierOf i := rfl
  rw [claimOfInput] at hn
  split at hn
  · rename_i o ho
    rw [hcompiled, carrierOf, ho]
    dsimp only
    obtain ⟨node, hnode, _⟩ := Consistency.mem_claimSupportFor_iff.mp hn
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hnode
    rw [Locality.args_checkedAF, List.mem_range,
      ← congrArg List.length o.run.checked.nodes_terms, List.length_map]
    exact hlt
  · simp at hn

/-- **The recorded grounded footprint determines the status it accompanies.**
Any environment agreeing with the canonical reading on the status footprint
reproduces the four-state status of the complete checked claim. -/
theorem recorded_status_determined {i : Source.SourceInput} {queries : List Atom}
    {q : Atom} {e : ReadEnv}
    (agree : ∀ k ∈ statusReads (compiledAF i) (claimOfInput i q),
      e k = inputReading i queries k) :
    statusC (reconstruct e) (claimOfInput i q) = statusC (compiledAF i) (claimOfInput i q) :=
  statusC_reconstruct_of_reads (claimOfInput_support_mem i q) (fun k hk => by
    rw [agree k hk]
    exact inputReading_eq_reading_of_grounded (mem_statusReads_shape hk))

/-! ### RecordsReads for the reused run-level calculations

The whole-input fallback. The key space is the finite two-element `Side`, whose
value at a side is the complete `SourceInput` of that endpoint; this is exactly
"bind the recorded read to the whole `SourceInput`". -/

/-- The whole-input key space of one comparison: one key per endpoint. -/
abbrev InputKey := Side

/-- `RecordsReads.whole` instantiated at the finite endpoint key space. -/
theorem recordsReads_whole_input (check : (InputKey → Source.SourceInput) → Bool) :
    RecordsReads check Finset.univ :=
  RecordsReads.whole check

/-- **`RecordsReads` for `Source.checkSource`'s outcome record**: the exact
rejection payload / acceptance is a function of the whole input. -/
theorem recordsReads_outcomeRecord_input (i : Source.SourceInput) :
    RecordsReads (fun e : InputKey → Source.SourceInput =>
      decide (outcomeRecord (e Side.before) = outcomeRecord i)) Finset.univ := by
  intro e₁ e₂ agree
  have h1 := agree Side.before (Finset.mem_univ _)
  simp only [h1]

/-- **`RecordsReads` for `Update.blockedQueriesForRun`** through the whole
input. -/
theorem recordsReads_blockedQueries_input (i : Source.SourceInput) (queries : List Atom) :
    RecordsReads (fun e : InputKey → Source.SourceInput =>
      decide (blockedQueriesOf (e Side.before) queries = blockedQueriesOf i queries))
      Finset.univ := by
  intro e₁ e₂ agree
  have h1 := agree Side.before (Finset.mem_univ _)
  simp only [h1]

/-- **`RecordsReads` for `BHL.ordinaryStatus`'s public-status row** through the
whole input. -/
theorem recordsReads_statusRow_input (i : Source.SourceInput) (q : Atom) :
    RecordsReads (fun e : InputKey → Source.SourceInput =>
      decide (statusRowOf (e Side.before) q = statusRowOf i q)) Finset.univ := by
  intro e₁ e₂ agree
  have h1 := agree Side.before (Finset.mem_univ _)
  simp only [h1]

/-! ### The recorded read set of a source comparison

The certificate records, for each endpoint, the keys of its complete status
footprint plus its run-level carriers, closure and memberships, all side-tagged.
`impactReads` stores, per side, the image of that endpoint's read keys under the
canonical reading, so a key never appears with two values under one side. -/

/-- The read keys of one endpoint's status rows and per-endpoint reports. -/
def endpointReadKeys (i : Source.SourceInput) (queries : List Atom) : Finset ReadKey :=
  insert ReadKey.wholeInput
    (insert ReadKey.referenceCarrier
      (insert ReadKey.checkedCarrier
        (insert ReadKey.compiledCarrier
          (insert ReadKey.blockedClosure
            ((queries.toFinset.biUnion fun q =>
                insert (ReadKey.supportNodes q)
                  (insert (ReadKey.holeNodes q)
                    (insert (ReadKey.blockedQuery q)
                      (statusReads (compiledAF i) (claimOfInput i q)))))
              ∪ (queries.toFinset.biUnion fun q =>
                  (((claimOfInput i q).support.toFinset).image
                      (fun n => ReadKey.supportMember q n))
                    ∪ (((claimOfInput i q).holes.toFinset).image
                      (fun n => ReadKey.holeMember q n))))))))

/-- **The recorded read set covers what a status calculation reads.** Every key
of a queried status footprint (the compiled carrier and the complete ancestry
attack rows) is a recorded key of that endpoint. -/
theorem statusReads_subset_endpointReadKeys {i : Source.SourceInput}
    {queries : List Atom} {q : Atom} (hq : q ∈ queries) :
    statusReads (compiledAF i) (claimOfInput i q) ⊆ endpointReadKeys i queries := by
  intro k hk
  unfold endpointReadKeys
  refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_))))
  refine Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr
    ⟨q, List.mem_toFinset.mpr hq,
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hk))⟩))

/-- **The recorded reads of a comparison.** One entry per `(side, key)`, each
carrying the canonical value of that key at that endpoint. It is a `Finset`, so
the value recorded for a `(side, key)` is unique by construction. -/
def impactReads (bi ai : Source.SourceInput) (queries : List Atom) :
    Finset (Side × ReadKey × ReadVal) :=
  (endpointReadKeys bi queries).image
      (fun k => (Side.before, k, inputReading bi queries k))
    ∪ (endpointReadKeys ai queries).image
      (fun k => (Side.after, k, inputReading ai queries k))

/-- Every recorded before-side key appears with its canonical value. -/
theorem mem_impactReads_before {bi ai : Source.SourceInput} {queries : List Atom}
    {k : ReadKey} (hk : k ∈ endpointReadKeys bi queries) :
    (Side.before, k, inputReading bi queries k) ∈ impactReads bi ai queries :=
  Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨k, hk, rfl⟩))

/-- Every recorded after-side key appears with its canonical value. -/
theorem mem_impactReads_after {bi ai : Source.SourceInput} {queries : List Atom}
    {k : ReadKey} (hk : k ∈ endpointReadKeys ai queries) :
    (Side.after, k, inputReading ai queries k) ∈ impactReads bi ai queries :=
  Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨k, hk, rfl⟩))

/-- **One key has one value per side.** The recorded reads are functional in
`(side, key)`. -/
theorem impactReads_functional {bi ai : Source.SourceInput} {queries : List Atom}
    {s : Side} {k : ReadKey} {v v' : ReadVal}
    (h : (s, k, v) ∈ impactReads bi ai queries)
    (h' : (s, k, v') ∈ impactReads bi ai queries) : v = v' := by
  have key : ∀ {s : Side} {k : ReadKey} {v : ReadVal},
      (s, k, v) ∈ impactReads bi ai queries →
      (s = Side.before ∧ k ∈ endpointReadKeys bi queries ∧ v = inputReading bi queries k) ∨
      (s = Side.after ∧ k ∈ endpointReadKeys ai queries ∧ v = inputReading ai queries k) := by
    intro s k v h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨k', hk', he⟩ := Finset.mem_image.mp h
      simp only [Prod.mk.injEq] at he
      exact Or.inl ⟨he.1.symm, he.2.1 ▸ hk', by rw [← he.2.2, he.2.1]⟩
    · obtain ⟨k', hk', he⟩ := Finset.mem_image.mp h
      simp only [Prod.mk.injEq] at he
      exact Or.inr ⟨he.1.symm, he.2.1 ▸ hk', by rw [← he.2.2, he.2.1]⟩
  rcases key h with ⟨hs, _, hv⟩ | ⟨hs, _, hv⟩ <;>
    rcases key h' with ⟨hs', _, hv'⟩ | ⟨hs', _, hv'⟩
  · rw [hv, hv']
  · exact absurd (hs.symm.trans hs') (by decide)
  · exact absurd (hs.symm.trans hs') (by decide)
  · rw [hv, hv']

/-- The whole-input read of the before endpoint is recorded with its value. -/
theorem impactReads_records_wholeInput_before (bi ai : Source.SourceInput)
    (queries : List Atom) :
    (Side.before, ReadKey.wholeInput, ReadVal.source bi) ∈ impactReads bi ai queries :=
  mem_impactReads_before (by simp [endpointReadKeys])

/-- The whole-input read of the after endpoint is recorded with its value. -/
theorem impactReads_records_wholeInput_after (bi ai : Source.SourceInput)
    (queries : List Atom) :
    (Side.after, ReadKey.wholeInput, ReadVal.source ai) ∈ impactReads bi ai queries :=
  mem_impactReads_after (by simp [endpointReadKeys])

/-- The endpoint's public-status row read out of a side-tagged environment's
whole-input read: the reused run-level calculation is rerun on the recorded
whole input (the conservative fallback). -/
def statusRowOfReads (e : SReadEnv) (s : Side) (q : Atom) : Option Driver.PublicStatus :=
  match e (s, ReadKey.wholeInput) with
  | .source i => statusRowOf i q
  | _ => none

theorem statusRowOfReads_of_source {e : SReadEnv} {s : Side} {i : Source.SourceInput}
    {q : Atom} (h : e (s, ReadKey.wholeInput) = ReadVal.source i) :
    statusRowOfReads e s q = statusRowOf i q := by
  unfold statusRowOfReads
  rw [h]

/-- **The recorded reads determine the accompanied public-status rows.** Any
side-tagged environment agreeing with the recorded reads has, on each side, that
endpoint's whole input, and the reused `BHL.ordinaryStatus` row is reproduced. -/
theorem impactReads_determines_statusRow {bi ai : Source.SourceInput} {queries : List Atom}
    {e : SReadEnv} {q : Atom}
    (agree : ∀ x : Side × ReadKey × ReadVal,
      x ∈ impactReads bi ai queries → e (x.1, x.2.1) = x.2.2) :
    statusRowOfReads e Side.before q = statusRowOf bi q ∧
    statusRowOfReads e Side.after q = statusRowOf ai q :=
  ⟨statusRowOfReads_of_source (agree _ (impactReads_records_wholeInput_before bi ai queries)),
   statusRowOfReads_of_source (agree _ (impactReads_records_wholeInput_after bi ai queries))⟩

/-- **The certificate's recorded reads cover the accompanied statuses.** Every
key of every queried status footprint is recorded under its endpoint side, so no
unrecorded attack row can flip the recorded status. -/
theorem impactReads_covers_status {bi ai : Source.SourceInput} {queries : List Atom}
    {q : Atom} (hq : q ∈ queries) {k : ReadKey}
    (hk : k ∈ statusReads (compiledAF bi) (claimOfInput bi q)) :
    (Side.before, k, inputReading bi queries k) ∈ impactReads bi ai queries :=
  mem_impactReads_before (statusReads_subset_endpointReadKeys hq hk)

/-- The same coverage on the after endpoint. -/
theorem impactReads_covers_status_after {bi ai : Source.SourceInput} {queries : List Atom}
    {q : Atom} (hq : q ∈ queries) {k : ReadKey}
    (hk : k ∈ statusReads (compiledAF ai) (claimOfInput ai q)) :
    (Side.after, k, inputReading ai queries k) ∈ impactReads bi ai queries :=
  mem_impactReads_after (statusReads_subset_endpointReadKeys hq hk)

/-! ### Impact transitions and the comparison record -/

/-- The four first-class source transitions. A rejected endpoint is an outcome,
never an error: rejection is recorded as a transition, not a refusal. -/
inductive ImpactTransition where
  | rejectedToRejected
  | rejectedToAccepted
  | acceptedToRejected
  | acceptedToAccepted
  deriving DecidableEq, Repr

/-- The exact transition of a source pair. -/
def transitionOf (bi ai : Source.SourceInput) : ImpactTransition :=
  match Source.checkSource bi, Source.checkSource ai with
  | .error _, .error _ => .rejectedToRejected
  | .error _, .ok _ => .rejectedToAccepted
  | .ok _, .error _ => .acceptedToRejected
  | .ok _, .ok _ => .acceptedToAccepted

theorem transitionOf_rejectedToRejected {bi ai : Source.SourceInput}
    {rb : Source.SourceRejection} {ra : Source.SourceRejection}
    (hb : Source.checkSource bi = .error rb) (ha : Source.checkSource ai = .error ra) :
    transitionOf bi ai = .rejectedToRejected := by
  unfold transitionOf; rw [hb, ha]

theorem transitionOf_rejectedToAccepted {bi ai : Source.SourceInput}
    {rb : Source.SourceRejection} {oa : Source.AcceptedObservation ai}
    (hb : Source.checkSource bi = .error rb) (ha : Source.checkSource ai = .ok oa) :
    transitionOf bi ai = .rejectedToAccepted := by
  unfold transitionOf; rw [hb, ha]

theorem transitionOf_acceptedToRejected {bi ai : Source.SourceInput}
    {ob : Source.AcceptedObservation bi} {ra : Source.SourceRejection}
    (hb : Source.checkSource bi = .ok ob) (ha : Source.checkSource ai = .error ra) :
    transitionOf bi ai = .acceptedToRejected := by
  unfold transitionOf; rw [hb, ha]

theorem transitionOf_acceptedToAccepted {bi ai : Source.SourceInput}
    {ob : Source.AcceptedObservation bi} {oa : Source.AcceptedObservation ai}
    (hb : Source.checkSource bi = .ok ob) (ha : Source.checkSource ai = .ok oa) :
    transitionOf bi ai = .acceptedToAccepted := by
  unfold transitionOf; rw [hb, ha]

/-- **`RecordsReads` for the transition** over the finite whole-input key space:
the transition is a function of the two complete inputs. -/
theorem recordsReads_transitionOf_input (b a : Source.SourceInput) :
    RecordsReads (fun e : InputKey → Source.SourceInput =>
      decide (transitionOf (e Side.before) (e Side.after) = transitionOf b a)) Finset.univ := by
  intro e₁ e₂ agree
  have h1 := agree Side.before (Finset.mem_univ _)
  have h2 := agree Side.after (Finset.mem_univ _)
  simp only [h1, h2]

/-- **One endpoint's exact checker outcome.** A rejected endpoint carries its
exact `SourceRejection` payload; an accepted endpoint carries its reference and
checked carriers, its compiled carrier, its blocked closure and its per-query
complete-support map. Nothing is invented: a rejected endpoint records no status
and an empty carrier, and an accepted endpoint records no rejection. -/
structure EndpointReport where
  accepted : Bool
  rejection : Option Source.SourceRejection
  referenceCarrier : List Nat
  checkedCarrier : List Nat
  compiledCarrier : List Grounded.Arg
  blocked : List Atom
  supports : List (Atom × List Presentation.ArgId)
  deriving DecidableEq

/-- The rerun observer's per-endpoint report. -/
def endpointReport (i : Source.SourceInput) (queries : List Atom) : EndpointReport :=
  match Source.checkSource i with
  | .ok o =>
      { accepted := true
        rejection := none
        referenceCarrier := Update.referenceCarrierForRun o.run
        checkedCarrier := Update.checkedCarrierForRun o.run
        compiledCarrier := (Compile.checkedAF o.run.checked.program).args
        blocked := Update.blockedQueriesForRun o.run queries
        supports := queries.map fun q => (q, Source.Coordinates.supports o.run q) }
  | .error r =>
      { accepted := false
        rejection := some r
        referenceCarrier := []
        checkedCarrier := []
        compiledCarrier := []
        blocked := []
        supports := queries.map fun q => (q, []) }

/-- One query's full public-status comparison. Both statuses are recomputed by
the observer; a rejected endpoint contributes `none`, never an invented status.
The `changed` flag is exact public-status inequality on the `Option` values, so
a rejection-to-acceptance (or the reverse) is a change. -/
structure QueryImpact where
  query : Atom
  beforeStatus : Option Driver.PublicStatus
  afterStatus : Option Driver.PublicStatus
  changed : Bool
  localityAccepted : Bool
  deriving DecidableEq

/-- The shared stable-identity comparison carrier; when only one endpoint is
accepted it is that endpoint's carrier, and when neither is accepted it is
empty. A pairwise graph difference exists only for two accepted endpoints. -/
def impactCarrier (bi ai : Source.SourceInput) : List Presentation.ArgId :=
  match Source.checkSource bi, Source.checkSource ai with
  | .ok ob, .ok oa =>
      Locality.sharedCarrier (Source.Coordinates.names ob.run) (Source.Coordinates.names oa.run)
  | .ok ob, .error _ => (Source.Coordinates.names ob.run).dedup
  | .error _, .ok oa => (Source.Coordinates.names oa.run).dedup
  | .error _, .error _ => []

/-- The compiled node symmetric difference of the lifted graphs. It is defined
only for two accepted endpoints; a mixed transition has no second graph and
records the empty difference, while the accepted endpoint's carrier is recorded
in its `EndpointReport`. -/
def impactNodeDiff (bi ai : Source.SourceInput) : List Grounded.Arg :=
  match Source.checkSource bi, Source.checkSource ai with
  | .ok ob, .ok oa =>
      Locality.nodeDiff (Source.Coordinates.graph ob.run (impactCarrier bi ai))
        (Source.Coordinates.graph oa.run (impactCarrier bi ai))
  | _, _ => []

/-- The compiled-edge symmetric difference of the lifted graphs; two accepted
endpoints only, as `impactNodeDiff`. -/
def impactEdgeDiff (bi ai : Source.SourceInput) :
    List (Grounded.Arg × Grounded.Arg) :=
  match Source.checkSource bi, Source.checkSource ai with
  | .ok ob, .ok oa =>
      Locality.edgeDiff (Source.Coordinates.graph ob.run (impactCarrier bi ai))
        (Source.Coordinates.graph oa.run (impactCarrier bi ai))
  | _, _ => []

/-- The checked locality test of one query; only two accepted endpoints have a
pair to compare. -/
def localityAccepted (bi ai : Source.SourceInput) (q : Atom) : Bool :=
  match Source.checkSource bi, Source.checkSource ai with
  | .ok ob, .ok oa =>
      let carrier := impactCarrier bi ai
      (Locality.checkLocality (Source.Coordinates.graph ob.run carrier)
        (Source.Coordinates.graph oa.run carrier)
        (Locality.querySupport ob.run carrier q)
        (Locality.querySupport oa.run carrier q)).accepted
  | _, _ => false

/-- Every requested query's full public status, using `BHL.ordinaryStatus` on
each accepted endpoint. -/
def queryImpacts (bi ai : Source.SourceInput) (queries : List Atom) : List QueryImpact :=
  queries.map fun q =>
    let sb := statusRowOf bi q
    let sa := statusRowOf ai q
    { query := q
      beforeStatus := sb
      afterStatus := sa
      changed := decide (sb ≠ sa)
      localityAccepted := localityAccepted bi ai q }

/-- Queries whose full public status changed between the two endpoints. -/
def changedQueries (bi ai : Source.SourceInput) (queries : List Atom) : List Atom :=
  (queryImpacts bi ai queries).filterMap fun r =>
    if r.changed then some r.query else none

/-- Queries whose full public status is defined on both endpoints and
unchanged. Rejected endpoints contribute to neither partition. -/
def unchangedQueries (bi ai : Source.SourceInput) (queries : List Atom) : List Atom :=
  (queryImpacts bi ai queries).filterMap fun r =>
    if r.beforeStatus.isSome && r.afterStatus.isSome && !r.changed then some r.query
    else none

/-- The recomputed impact result: the rerun observer's transition, full
public-status rows and changed/unchanged partition. This is what `verifyImpact`
recomputes; `ImpactCertificate` is the claim checked against it. -/
structure ImpactResult where
  transition : ImpactTransition
  rows : List QueryImpact
  changed : List Atom
  unchanged : List Atom
  deriving DecidableEq

/-- The impact result of one source pair over a fixed query list. -/
def impactResult (bi ai : Source.SourceInput) (queries : List Atom) : ImpactResult :=
  { transition := transitionOf bi ai
    rows := queryImpacts bi ai queries
    changed := changedQueries bi ai queries
    unchanged := unchangedQueries bi ai queries }

/-! ### The impact certificate and its data constructor -/

/-- The impact of one source against another over a fixed query list. Every
field is *data*; the verifier reruns the observer and recomputes each field. The
per-endpoint outcome reports make rejected-to-accepted, accepted-to-rejected and
rejected-to-rejected first-class: each endpoint carries its exact rejection
payload or its accepted carriers/supports, and no rejected endpoint invents a
status. -/
structure ImpactCertificate where
  beforeInput : Source.SourceInput
  afterInput : Source.SourceInput
  queries : List Atom
  beforeSnapshot : Evidence.Snapshot
  afterSnapshot : Evidence.Snapshot
  beforeIdentity : Source.ReplayIdentity
  afterIdentity : Source.ReplayIdentity
  beforeReport : EndpointReport
  afterReport : EndpointReport
  transition : ImpactTransition
  rows : List QueryImpact
  changed : List Atom
  unchanged : List Atom
  blockedBefore : List Atom
  blockedAfter : List Atom
  carrier : List Presentation.ArgId
  nodeDiff : List Grounded.Arg
  edgeDiff : List (Grounded.Arg × Grounded.Arg)
  locality : List (Atom × Bool)
  reads : Finset (Side × ReadKey × ReadVal)
  deriving DecidableEq

/-- The honest certificate: every field is the recomputed value. -/
def impactCertificate (bi ai : Source.SourceInput) (queries : List Atom) :
    ImpactCertificate :=
  { beforeInput := bi
    afterInput := ai
    queries := queries
    beforeSnapshot := bi.snapshot
    afterSnapshot := ai.snapshot
    beforeIdentity := bi.replay
    afterIdentity := ai.replay
    beforeReport := endpointReport bi queries
    afterReport := endpointReport ai queries
    transition := transitionOf bi ai
    rows := queryImpacts bi ai queries
    changed := changedQueries bi ai queries
    unchanged := unchangedQueries bi ai queries
    blockedBefore := blockedQueriesOf bi queries
    blockedAfter := blockedQueriesOf ai queries
    carrier := impactCarrier bi ai
    nodeDiff := impactNodeDiff bi ai
    edgeDiff := impactEdgeDiff bi ai
    locality := (queryImpacts bi ai queries).map fun r => (r.query, r.localityAccepted)
    reads := impactReads bi ai queries }

/-- The result a certificate claims. -/
def ImpactCertificate.result (c : ImpactCertificate) : ImpactResult :=
  { transition := c.transition
    rows := c.rows
    changed := c.changed
    unchanged := c.unchanged }

/-! ### Verification: faults, result and the recomputing verifier -/

/-- The closed fault of an `ImpactCertificate`. A well-formed but false
certificate yields a fault, not a refusal. -/
inductive VerificationFault where
  | mismatchedSnapshots
  | mismatchedIdentities
  | outcomeMismatch
  | statusMismatch
  | invalidSupports
  | invalidGraph
  | falseLocality
  | falseReadEvidence
  deriving DecidableEq, Repr

/-- The closed verification result. -/
inductive VerificationResult where
  | verified
  | invalidCertificate : VerificationFault → VerificationResult
  deriving DecidableEq, Repr

def snapshotOk (c : ImpactCertificate) : Bool :=
  decide (c.beforeSnapshot = c.beforeInput.snapshot)
    && decide (c.afterSnapshot = c.afterInput.snapshot)

def identityOk (c : ImpactCertificate) : Bool :=
  decide (c.beforeIdentity = c.beforeInput.replay)
    && decide (c.afterIdentity = c.afterInput.replay)

/-- The outcome check: the exact four-way transition, both blocked decisions and
both per-endpoint outcome reports (the rejection payload or the accepted
carriers/supports). -/
def outcomeOk (c : ImpactCertificate) : Bool :=
  decide (c.transition = transitionOf c.beforeInput c.afterInput)
    && decide (c.blockedBefore = blockedQueriesOf c.beforeInput c.queries)
    && decide (c.blockedAfter = blockedQueriesOf c.afterInput c.queries)
    && decide (c.beforeReport = endpointReport c.beforeInput c.queries)
    && decide (c.afterReport = endpointReport c.afterInput c.queries)

def rowsOk (c : ImpactCertificate) : Bool :=
  decide (c.rows = queryImpacts c.beforeInput c.afterInput c.queries)

def supportOk (c : ImpactCertificate) : Bool :=
  decide (c.changed = changedQueries c.beforeInput c.afterInput c.queries)
    && decide (c.unchanged = unchangedQueries c.beforeInput c.afterInput c.queries)

def graphOk (c : ImpactCertificate) : Bool :=
  decide (c.carrier = impactCarrier c.beforeInput c.afterInput)
    && decide (c.nodeDiff = impactNodeDiff c.beforeInput c.afterInput)
    && decide (c.edgeDiff = impactEdgeDiff c.beforeInput c.afterInput)

def localityOk (c : ImpactCertificate) : Bool :=
  decide (c.locality =
    (queryImpacts c.beforeInput c.afterInput c.queries).map
      (fun r => (r.query, r.localityAccepted)))

def readsOk (c : ImpactCertificate) : Bool :=
  decide (c.reads = impactReads c.beforeInput c.afterInput c.queries)

/-- Every check of the verifier, in order. -/
def allChecks (c : ImpactCertificate) : Bool :=
  snapshotOk c && identityOk c && outcomeOk c && rowsOk c && supportOk c
    && graphOk c && localityOk c && readsOk c

/-- The first failing check as a closed fault. Written in positive form, so the
fault identity `firstFault_some_iff` case-splits it directly. -/
def firstFault (c : ImpactCertificate) : Option VerificationFault :=
  if snapshotOk c then
    if identityOk c then
      if outcomeOk c then
        if rowsOk c then
          if supportOk c then
            if graphOk c then
              if localityOk c then
                if readsOk c then none else some .falseReadEvidence
              else some .falseLocality
            else some .invalidGraph
          else some .invalidSupports
        else some .statusMismatch
      else some .outcomeMismatch
    else some .mismatchedIdentities
  else some .mismatchedSnapshots

/-- Rerun the shared observer on both supplied sources, recompute every
certificate field and return the closed verification result. -/
def verifyImpact (c : ImpactCertificate) : VerificationResult :=
  match firstFault c with
  | none => .verified
  | some fault => .invalidCertificate fault

/-- The Boolean decision the interactive path reads; `verified` is exactly this
proposition. -/
def verifyImpactBool (c : ImpactCertificate) : Bool :=
  decide (verifyImpact c = .verified)

/-! ### Verification laws -/

theorem snapshotOk_eq_true (c : ImpactCertificate) :
    snapshotOk c = true ↔
      c.beforeSnapshot = c.beforeInput.snapshot ∧ c.afterSnapshot = c.afterInput.snapshot := by
  simp [snapshotOk, Bool.and_eq_true, decide_eq_true_eq]

theorem identityOk_eq_true (c : ImpactCertificate) :
    identityOk c = true ↔
      c.beforeIdentity = c.beforeInput.replay ∧ c.afterIdentity = c.afterInput.replay := by
  simp [identityOk, Bool.and_eq_true, decide_eq_true_eq]

theorem outcomeOk_eq_true (c : ImpactCertificate) :
    outcomeOk c = true ↔
      c.transition = transitionOf c.beforeInput c.afterInput ∧
      c.blockedBefore = blockedQueriesOf c.beforeInput c.queries ∧
      c.blockedAfter = blockedQueriesOf c.afterInput c.queries ∧
      c.beforeReport = endpointReport c.beforeInput c.queries ∧
      c.afterReport = endpointReport c.afterInput c.queries := by
  simp [outcomeOk, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem rowsOk_eq_true (c : ImpactCertificate) :
    rowsOk c = true ↔ c.rows = queryImpacts c.beforeInput c.afterInput c.queries := by
  simp [rowsOk, decide_eq_true_eq]

theorem supportOk_eq_true (c : ImpactCertificate) :
    supportOk c = true ↔
      c.changed = changedQueries c.beforeInput c.afterInput c.queries ∧
      c.unchanged = unchangedQueries c.beforeInput c.afterInput c.queries := by
  simp [supportOk, Bool.and_eq_true, decide_eq_true_eq]

theorem graphOk_eq_true (c : ImpactCertificate) :
    graphOk c = true ↔
      c.carrier = impactCarrier c.beforeInput c.afterInput ∧
      c.nodeDiff = impactNodeDiff c.beforeInput c.afterInput ∧
      c.edgeDiff = impactEdgeDiff c.beforeInput c.afterInput := by
  simp [graphOk, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem localityOk_eq_true (c : ImpactCertificate) :
    localityOk c = true ↔
      c.locality = (queryImpacts c.beforeInput c.afterInput c.queries).map
        (fun r => (r.query, r.localityAccepted)) := by
  simp [localityOk, decide_eq_true_eq]

theorem readsOk_eq_true (c : ImpactCertificate) :
    readsOk c = true ↔ c.reads = impactReads c.beforeInput c.afterInput c.queries := by
  simp [readsOk, decide_eq_true_eq]

theorem allChecks_eq_true (c : ImpactCertificate) :
    allChecks c = true ↔
      snapshotOk c = true ∧ identityOk c = true ∧ outcomeOk c = true ∧ rowsOk c = true ∧
      supportOk c = true ∧ graphOk c = true ∧ localityOk c = true ∧ readsOk c = true := by
  simp [allChecks, Bool.and_eq_true, and_assoc]

theorem firstFault_eq_none (c : ImpactCertificate) :
    firstFault c = none ↔ allChecks c = true := by
  rw [allChecks_eq_true]
  unfold firstFault
  cases hs : snapshotOk c <;> cases hi : identityOk c <;> cases ho : outcomeOk c <;>
    cases hr : rowsOk c <;> cases hsu : supportOk c <;> cases hg : graphOk c <;>
    cases hl : localityOk c <;> cases hrd : readsOk c <;> simp_all

/-- **`verified` is exactly the Boolean decision.** -/
theorem verifyImpact_eq_verified_iff (c : ImpactCertificate) :
    verifyImpact c = .verified ↔ allChecks c = true := by
  unfold verifyImpact
  constructor
  · intro h
    cases hf : firstFault c with
    | none => exact (firstFault_eq_none c).mp hf
    | some fault => rw [hf] at h; exact absurd h (by simp)
  · intro h
    rw [show firstFault c = none from (firstFault_eq_none c).mpr h]

theorem verified_iff_verifyImpact_true (c : ImpactCertificate) :
    verifyImpact c = .verified ↔ verifyImpactBool c = true := by
  unfold verifyImpactBool
  rw [decide_eq_true_eq]

/-- The exact checks a `verified` certificate passed. -/
theorem verifyImpact_verified_fields (c : ImpactCertificate)
    (h : verifyImpact c = .verified) :
    snapshotOk c = true ∧ identityOk c = true ∧ outcomeOk c = true ∧ rowsOk c = true ∧
    supportOk c = true ∧ graphOk c = true ∧ localityOk c = true ∧ readsOk c = true :=
  (allChecks_eq_true c).mp ((verifyImpact_eq_verified_iff c).mp h)

/-- **Acceptance binds the claimed snapshots and replay/backend identities to the
supplied inputs.** -/
theorem verifyImpact_verified_binding (c : ImpactCertificate)
    (h : verifyImpact c = .verified) :
    c.beforeSnapshot = c.beforeInput.snapshot ∧ c.afterSnapshot = c.afterInput.snapshot ∧
    c.beforeIdentity = c.beforeInput.replay ∧ c.afterIdentity = c.afterInput.replay := by
  have hf := verifyImpact_verified_fields c h
  have hs := (snapshotOk_eq_true c).mp hf.1
  have hi := (identityOk_eq_true c).mp hf.2.1
  exact ⟨hs.1, hs.2, hi.1, hi.2⟩

/-- **Acceptance implies the claimed transition, blocking decisions and
per-endpoint outcome reports.** -/
theorem verifyImpact_verified_outcome (c : ImpactCertificate)
    (h : verifyImpact c = .verified) :
    c.transition = transitionOf c.beforeInput c.afterInput ∧
    c.blockedBefore = blockedQueriesOf c.beforeInput c.queries ∧
    c.blockedAfter = blockedQueriesOf c.afterInput c.queries ∧
    c.beforeReport = endpointReport c.beforeInput c.queries ∧
    c.afterReport = endpointReport c.afterInput c.queries :=
  (outcomeOk_eq_true c).mp (verifyImpact_verified_fields c h).2.2.1

/-- The transition half of `verifyImpact_verified_outcome`. -/
theorem verifyImpact_verified_transition (c : ImpactCertificate)
    (h : verifyImpact c = .verified) :
    c.transition = transitionOf c.beforeInput c.afterInput ∧
    c.blockedBefore = blockedQueriesOf c.beforeInput c.queries ∧
    c.blockedAfter = blockedQueriesOf c.afterInput c.queries := by
  obtain ⟨ht, hb, ha, _, _⟩ := verifyImpact_verified_outcome c h
  exact ⟨ht, hb, ha⟩

/-- **Acceptance implies the claimed full public-status rows.** -/
theorem verifyImpact_verified_rows (c : ImpactCertificate)
    (h : verifyImpact c = .verified) :
    c.rows = queryImpacts c.beforeInput c.afterInput c.queries :=
  (rowsOk_eq_true c).mp (verifyImpact_verified_fields c h).2.2.2.1

/-- **Acceptance implies the claimed changed/unchanged partition.** -/
theorem verifyImpact_verified_partition (c : ImpactCertificate)
    (h : verifyImpact c = .verified) :
    c.changed = changedQueries c.beforeInput c.afterInput c.queries ∧
    c.unchanged = unchangedQueries c.beforeInput c.afterInput c.queries :=
  (supportOk_eq_true c).mp (verifyImpact_verified_fields c h).2.2.2.2.1

/-- **Acceptance implies the claimed node/support maps and graph difference.** -/
theorem verifyImpact_verified_graph (c : ImpactCertificate)
    (h : verifyImpact c = .verified) :
    c.carrier = impactCarrier c.beforeInput c.afterInput ∧
    c.nodeDiff = impactNodeDiff c.beforeInput c.afterInput ∧
    c.edgeDiff = impactEdgeDiff c.beforeInput c.afterInput :=
  (graphOk_eq_true c).mp (verifyImpact_verified_fields c h).2.2.2.2.2.1

/-- **Acceptance implies the claimed checked locality facts.** -/
theorem verifyImpact_verified_locality (c : ImpactCertificate)
    (h : verifyImpact c = .verified) :
    c.locality = (queryImpacts c.beforeInput c.afterInput c.queries).map
      (fun r => (r.query, r.localityAccepted)) :=
  (localityOk_eq_true c).mp (verifyImpact_verified_fields c h).2.2.2.2.2.2.1

/-- **Acceptance implies the claimed exact read keys and values.** -/
theorem verifyImpact_verified_reads (c : ImpactCertificate)
    (h : verifyImpact c = .verified) :
    c.reads = impactReads c.beforeInput c.afterInput c.queries :=
  (readsOk_eq_true c).mp (verifyImpact_verified_fields c h).2.2.2.2.2.2.2

/-- **Acceptance implies the whole claimed impact.** The transition, the public
status rows, the partition, the graph difference and the locality facts all hold
of the rerun observer. -/
theorem verifyImpact_verified_impact (c : ImpactCertificate)
    (h : verifyImpact c = .verified) :
    c.transition = transitionOf c.beforeInput c.afterInput ∧
    c.rows = queryImpacts c.beforeInput c.afterInput c.queries ∧
    c.changed = changedQueries c.beforeInput c.afterInput c.queries ∧
    c.unchanged = unchangedQueries c.beforeInput c.afterInput c.queries ∧
    c.carrier = impactCarrier c.beforeInput c.afterInput ∧
    c.nodeDiff = impactNodeDiff c.beforeInput c.afterInput ∧
    c.locality = (queryImpacts c.beforeInput c.afterInput c.queries).map
      (fun r => (r.query, r.localityAccepted)) := by
  obtain ⟨ht, _, _⟩ := verifyImpact_verified_transition c h
  obtain ⟨hp, hu⟩ := verifyImpact_verified_partition c h
  obtain ⟨hc, hn, he⟩ := verifyImpact_verified_graph c h
  exact ⟨ht, verifyImpact_verified_rows c h, hp, hu, hc, hn,
    verifyImpact_verified_locality c h⟩

/-- **Acceptance implies the claimed result.** -/
theorem verifyImpact_verified_result (c : ImpactCertificate)
    (h : verifyImpact c = .verified) :
    c.result = impactResult c.beforeInput c.afterInput c.queries := by
  obtain ⟨ht, _, _⟩ := verifyImpact_verified_transition c h
  obtain ⟨hp, hu⟩ := verifyImpact_verified_partition c h
  simp [ImpactCertificate.result, impactResult, ht, verifyImpact_verified_rows c h, hp, hu]

/-! ### The honest certificate verifies -/

/-- The computed certificate passes its own verifier: `verifyImpact` is not
vacuous. -/
theorem impactCertificate_verified (bi ai : Source.SourceInput) (queries : List Atom) :
    verifyImpact (impactCertificate bi ai queries) = .verified := by
  rw [verifyImpact_eq_verified_iff, allChecks_eq_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [snapshotOk, identityOk, outcomeOk, rowsOk, supportOk, graphOk, localityOk,
      readsOk, impactCertificate]

/-! ### Closed faults for each field mutation

`verifyImpact` reports the *first* failing check, so each fault theorem is
stated with the preceding checks passing: mutating exactly one field of an
otherwise honest certificate yields that field's fault. -/

theorem snapshotOk_eq_false_of (c : ImpactCertificate)
    (h : c.beforeSnapshot ≠ c.beforeInput.snapshot ∨
      c.afterSnapshot ≠ c.afterInput.snapshot) : snapshotOk c = false := by
  rcases h with h | h
  · have hd : decide (c.beforeSnapshot = c.beforeInput.snapshot) = false :=
      decide_eq_false_iff_not.mpr h
    simp [snapshotOk, hd]
  · have hd : decide (c.afterSnapshot = c.afterInput.snapshot) = false :=
      decide_eq_false_iff_not.mpr h
    simp [snapshotOk, hd]

theorem identityOk_eq_false_of (c : ImpactCertificate)
    (h : c.beforeIdentity ≠ c.beforeInput.replay ∨
      c.afterIdentity ≠ c.afterInput.replay) : identityOk c = false := by
  rcases h with h | h
  · have hd : decide (c.beforeIdentity = c.beforeInput.replay) = false :=
      decide_eq_false_iff_not.mpr h
    simp [identityOk, hd]
  · have hd : decide (c.afterIdentity = c.afterInput.replay) = false :=
      decide_eq_false_iff_not.mpr h
    simp [identityOk, hd]

theorem outcomeOk_eq_false_of (c : ImpactCertificate)
    (h : c.transition ≠ transitionOf c.beforeInput c.afterInput ∨
      c.blockedBefore ≠ blockedQueriesOf c.beforeInput c.queries ∨
      c.blockedAfter ≠ blockedQueriesOf c.afterInput c.queries ∨
      c.beforeReport ≠ endpointReport c.beforeInput c.queries ∨
      c.afterReport ≠ endpointReport c.afterInput c.queries) : outcomeOk c = false := by
  rcases h with h | h | h | h | h
  · have hd : decide (c.transition = transitionOf c.beforeInput c.afterInput) = false :=
      decide_eq_false_iff_not.mpr h
    simp [outcomeOk, hd]
  · have hd : decide (c.blockedBefore = blockedQueriesOf c.beforeInput c.queries) = false :=
      decide_eq_false_iff_not.mpr h
    simp [outcomeOk, hd]
  · have hd : decide (c.blockedAfter = blockedQueriesOf c.afterInput c.queries) = false :=
      decide_eq_false_iff_not.mpr h
    simp [outcomeOk, hd]
  · have hd : decide (c.beforeReport = endpointReport c.beforeInput c.queries) = false :=
      decide_eq_false_iff_not.mpr h
    simp [outcomeOk, hd]
  · have hd : decide (c.afterReport = endpointReport c.afterInput c.queries) = false :=
      decide_eq_false_iff_not.mpr h
    simp [outcomeOk, hd]

theorem rowsOk_eq_false_of (c : ImpactCertificate)
    (h : c.rows ≠ queryImpacts c.beforeInput c.afterInput c.queries) : rowsOk c = false := by
  have hd : decide (c.rows = queryImpacts c.beforeInput c.afterInput c.queries) = false :=
    decide_eq_false_iff_not.mpr h
  simp [rowsOk, hd]

theorem supportOk_eq_false_of (c : ImpactCertificate)
    (h : c.changed ≠ changedQueries c.beforeInput c.afterInput c.queries ∨
      c.unchanged ≠ unchangedQueries c.beforeInput c.afterInput c.queries) :
    supportOk c = false := by
  rcases h with h | h
  · have hd : decide (c.changed = changedQueries c.beforeInput c.afterInput c.queries) = false :=
      decide_eq_false_iff_not.mpr h
    simp [supportOk, hd]
  · have hd : decide (c.unchanged = unchangedQueries c.beforeInput c.afterInput c.queries) = false :=
      decide_eq_false_iff_not.mpr h
    simp [supportOk, hd]

theorem graphOk_eq_false_of (c : ImpactCertificate)
    (h : c.carrier ≠ impactCarrier c.beforeInput c.afterInput ∨
      c.nodeDiff ≠ impactNodeDiff c.beforeInput c.afterInput ∨
      c.edgeDiff ≠ impactEdgeDiff c.beforeInput c.afterInput) : graphOk c = false := by
  rcases h with h | h | h
  · have hd : decide (c.carrier = impactCarrier c.beforeInput c.afterInput) = false :=
      decide_eq_false_iff_not.mpr h
    simp [graphOk, hd]
  · have hd : decide (c.nodeDiff = impactNodeDiff c.beforeInput c.afterInput) = false :=
      decide_eq_false_iff_not.mpr h
    simp [graphOk, hd]
  · have hd : decide (c.edgeDiff = impactEdgeDiff c.beforeInput c.afterInput) = false :=
      decide_eq_false_iff_not.mpr h
    simp [graphOk, hd]

theorem localityOk_eq_false_of (c : ImpactCertificate)
    (h : c.locality ≠ (queryImpacts c.beforeInput c.afterInput c.queries).map
      (fun r => (r.query, r.localityAccepted))) : localityOk c = false := by
  have hd : decide (c.locality = (queryImpacts c.beforeInput c.afterInput c.queries).map
      (fun r => (r.query, r.localityAccepted))) = false := decide_eq_false_iff_not.mpr h
  simp [localityOk, hd]

theorem readsOk_eq_false_of (c : ImpactCertificate)
    (h : c.reads ≠ impactReads c.beforeInput c.afterInput c.queries) : readsOk c = false := by
  have hd : decide (c.reads = impactReads c.beforeInput c.afterInput c.queries) = false :=
    decide_eq_false_iff_not.mpr h
  simp [readsOk, hd]

theorem verifyImpact_staleSnapshot (c : ImpactCertificate) (h : snapshotOk c = false) :
    verifyImpact c = .invalidCertificate .mismatchedSnapshots := by
  simp [verifyImpact, firstFault, h]

theorem verifyImpact_staleIdentity (c : ImpactCertificate) (hs : snapshotOk c = true)
    (h : identityOk c = false) :
    verifyImpact c = .invalidCertificate .mismatchedIdentities := by
  simp [verifyImpact, firstFault, hs, h]

theorem verifyImpact_falseTransition (c : ImpactCertificate) (hs : snapshotOk c = true)
    (hi : identityOk c = true) (h : outcomeOk c = false) :
    verifyImpact c = .invalidCertificate .outcomeMismatch := by
  simp [verifyImpact, firstFault, hs, hi, h]

theorem verifyImpact_falseRows (c : ImpactCertificate) (hs : snapshotOk c = true)
    (hi : identityOk c = true) (ho : outcomeOk c = true) (h : rowsOk c = false) :
    verifyImpact c = .invalidCertificate .statusMismatch := by
  simp [verifyImpact, firstFault, hs, hi, ho, h]

theorem verifyImpact_falseSupports (c : ImpactCertificate) (hs : snapshotOk c = true)
    (hi : identityOk c = true) (ho : outcomeOk c = true) (hr : rowsOk c = true)
    (h : supportOk c = false) :
    verifyImpact c = .invalidCertificate .invalidSupports := by
  simp [verifyImpact, firstFault, hs, hi, ho, hr, h]

theorem verifyImpact_falseGraph (c : ImpactCertificate) (hs : snapshotOk c = true)
    (hi : identityOk c = true) (ho : outcomeOk c = true) (hr : rowsOk c = true)
    (hsu : supportOk c = true) (h : graphOk c = false) :
    verifyImpact c = .invalidCertificate .invalidGraph := by
  simp [verifyImpact, firstFault, hs, hi, ho, hr, hsu, h]

theorem verifyImpact_falseLocality (c : ImpactCertificate) (hs : snapshotOk c = true)
    (hi : identityOk c = true) (ho : outcomeOk c = true) (hr : rowsOk c = true)
    (hsu : supportOk c = true) (hg : graphOk c = true) (h : localityOk c = false) :
    verifyImpact c = .invalidCertificate .falseLocality := by
  simp [verifyImpact, firstFault, hs, hi, ho, hr, hsu, hg, h]

theorem verifyImpact_falseReads (c : ImpactCertificate) (hs : snapshotOk c = true)
    (hi : identityOk c = true) (ho : outcomeOk c = true) (hr : rowsOk c = true)
    (hsu : supportOk c = true) (hg : graphOk c = true) (hl : localityOk c = true)
    (h : readsOk c = false) :
    verifyImpact c = .invalidCertificate .falseReadEvidence := by
  simp [verifyImpact, firstFault, hs, hi, ho, hr, hsu, hg, hl, h]

/-! ### Fault identity

The condition a fault *fires exactly for*: the earlier checks hold and that
fault's own condition fails. This is the converse of the `verifyImpact_false*`
theorems and the separation `outcomeMismatch` does not itself make. -/

/-- The exact condition under which the verifier reports each fault: all earlier
checks hold and the named check fails. -/
def faultCondition (c : ImpactCertificate) : VerificationFault → Prop
  | .mismatchedSnapshots => snapshotOk c = false
  | .mismatchedIdentities => snapshotOk c = true ∧ identityOk c = false
  | .outcomeMismatch =>
      snapshotOk c = true ∧ identityOk c = true ∧ outcomeOk c = false
  | .statusMismatch =>
      snapshotOk c = true ∧ identityOk c = true ∧ outcomeOk c = true ∧ rowsOk c = false
  | .invalidSupports =>
      snapshotOk c = true ∧ identityOk c = true ∧ outcomeOk c = true ∧ rowsOk c = true ∧
      supportOk c = false
  | .invalidGraph =>
      snapshotOk c = true ∧ identityOk c = true ∧ outcomeOk c = true ∧ rowsOk c = true ∧
      supportOk c = true ∧ graphOk c = false
  | .falseLocality =>
      snapshotOk c = true ∧ identityOk c = true ∧ outcomeOk c = true ∧ rowsOk c = true ∧
      supportOk c = true ∧ graphOk c = true ∧ localityOk c = false
  | .falseReadEvidence =>
      snapshotOk c = true ∧ identityOk c = true ∧ outcomeOk c = true ∧ rowsOk c = true ∧
      supportOk c = true ∧ graphOk c = true ∧ localityOk c = true ∧ readsOk c = false

/-- **Fault identity.** The verifier reports the closed fault `f` exactly when
every earlier check holds and `f`'s own condition fails. -/
theorem firstFault_some_iff (c : ImpactCertificate) (f : VerificationFault) :
    firstFault c = some f ↔ faultCondition c f := by
  cases f <;>
    (cases hs : snapshotOk c <;> cases hi : identityOk c <;> cases ho : outcomeOk c <;>
     cases hr : rowsOk c <;> cases hsu : supportOk c <;> cases hg : graphOk c <;>
     cases hl : localityOk c <;> cases hrd : readsOk c <;>
     simp_all [firstFault, faultCondition])

/-- The fault-identity theorem at each fault, stated directly. -/
theorem firstFault_eq_some_mismatchedSnapshots (c : ImpactCertificate) :
    firstFault c = some .mismatchedSnapshots ↔ snapshotOk c = false :=
  (firstFault_some_iff c _).trans (by simp [faultCondition])

theorem firstFault_eq_some_mismatchedIdentities (c : ImpactCertificate) :
    firstFault c = some .mismatchedIdentities ↔
      snapshotOk c = true ∧ identityOk c = false :=
  (firstFault_some_iff c _).trans (by simp [faultCondition])

theorem firstFault_eq_some_outcomeMismatch (c : ImpactCertificate) :
    firstFault c = some .outcomeMismatch ↔
      snapshotOk c = true ∧ identityOk c = true ∧ outcomeOk c = false :=
  (firstFault_some_iff c _).trans (by simp [faultCondition])

theorem firstFault_eq_some_statusMismatch (c : ImpactCertificate) :
    firstFault c = some .statusMismatch ↔
      snapshotOk c = true ∧ identityOk c = true ∧ outcomeOk c = true ∧ rowsOk c = false :=
  (firstFault_some_iff c _).trans (by simp [faultCondition])

theorem firstFault_eq_some_invalidSupports (c : ImpactCertificate) :
    firstFault c = some .invalidSupports ↔
      snapshotOk c = true ∧ identityOk c = true ∧ outcomeOk c = true ∧ rowsOk c = true ∧
      supportOk c = false :=
  (firstFault_some_iff c _).trans (by simp [faultCondition])

theorem firstFault_eq_some_invalidGraph (c : ImpactCertificate) :
    firstFault c = some .invalidGraph ↔
      snapshotOk c = true ∧ identityOk c = true ∧ outcomeOk c = true ∧ rowsOk c = true ∧
      supportOk c = true ∧ graphOk c = false :=
  (firstFault_some_iff c _).trans (by simp [faultCondition])

theorem firstFault_eq_some_falseLocality (c : ImpactCertificate) :
    firstFault c = some .falseLocality ↔
      snapshotOk c = true ∧ identityOk c = true ∧ outcomeOk c = true ∧ rowsOk c = true ∧
      supportOk c = true ∧ graphOk c = true ∧ localityOk c = false :=
  (firstFault_some_iff c _).trans (by simp [faultCondition])

theorem firstFault_eq_some_falseReadEvidence (c : ImpactCertificate) :
    firstFault c = some .falseReadEvidence ↔
      snapshotOk c = true ∧ identityOk c = true ∧ outcomeOk c = true ∧ rowsOk c = true ∧
      supportOk c = true ∧ graphOk c = true ∧ localityOk c = true ∧ readsOk c = false :=
  (firstFault_some_iff c _).trans (by simp [faultCondition])

/-! ### Full public-status preservation

P4's grounded locality gives equality of the checked complete-claim status for
corresponding supports; complete support equality is built into the comparison
through `Locality.querySupport`; blocking equality is the second conjunct. The
result is equality of `BHL.ordinaryStatus`, i.e. the full `Driver.PublicStatus`,
conditional label included. -/

/-- **`BHL.ordinaryStatus` congruence.** Status equality plus blocking equality
give full public-status equality, retaining the conditional diagnostic inside
`evidenceBlocked`. -/
theorem ordinaryStatus_congr {canon : String → String}
    {regA : Support.BackendRegistry canon} {regB : Support.BackendRegistry canon}
    {stateA stateB : Update.SourceState} (runA : Update.AcceptedRun regA stateA)
    (runB : Update.AcceptedRun regB stateB) (query : Atom)
    (status : statusC (Compile.checkedAF runA.checked.program)
        (Consistency.completeClaimFor runA.checked query) =
      statusC (Compile.checkedAF runB.checked.program)
        (Consistency.completeClaimFor runB.checked query))
    (blocked : (query ∈ Update.blockedQueriesForRun runA [query]) ↔
      (query ∈ Update.blockedQueriesForRun runB [query])) :
    BHL.ordinaryStatus runA query = BHL.ordinaryStatus runB query := by
  unfold BHL.ordinaryStatus
  dsimp only
  rw [status]
  by_cases h : query ∈ Update.blockedQueriesForRun runA [query]
  · rw [if_pos h, if_pos (blocked.mp h)]
  · rw [if_neg h, if_neg fun hb => h (blocked.mpr hb)]

/-- **P4 locality + complete support equality give checked status equality.** The
certificate is over the lifted shared carrier, and `claimOf_status_eq_checked`
transports the lifted statuses back to the checked sources. -/
theorem checked_status_eq_of_certificate {first second : Source.SourceInput}
    (before : Source.AcceptedObservation first) (after : Source.AcceptedObservation second)
    (carrier : List Presentation.ArgId) (query : Atom)
    (cert : Locality.Certificate (Source.Coordinates.graph before.run carrier)
      (Source.Coordinates.graph after.run carrier)
      (Locality.querySupport before.run carrier query)
      (Locality.querySupport after.run carrier query))
    (coverBefore : ∀ n ∈ Source.Coordinates.names before.run, n ∈ carrier)
    (coverAfter : ∀ n ∈ Source.Coordinates.names after.run, n ∈ carrier) :
    statusC (Compile.checkedAF before.run.checked.program)
        (Consistency.completeClaimFor before.run.checked query) =
      statusC (Compile.checkedAF after.run.checked.program)
        (Consistency.completeClaimFor after.run.checked query) := by
  have hb := Locality.claimOf_status_eq_checked before.run carrier coverBefore query
  have ha := Locality.claimOf_status_eq_checked after.run carrier coverAfter query
  have hm : statusC (Source.Coordinates.graph before.run carrier)
        (Locality.claimOf before.run carrier query) =
      statusC (Source.Coordinates.graph after.run carrier)
        (Locality.claimOf after.run carrier query) :=
    cert.status_eq (cF := Locality.claimOf before.run carrier query)
      (cG := Locality.claimOf after.run carrier query) rfl rfl
  rw [← hb, ← ha]
  exact hm

/-- **Full public-status preservation from a locality certificate.** -/
theorem ordinaryStatus_eq_of_certificate {first second : Source.SourceInput}
    (before : Source.AcceptedObservation first) (after : Source.AcceptedObservation second)
    (carrier : List Presentation.ArgId) (query : Atom)
    (cert : Locality.Certificate (Source.Coordinates.graph before.run carrier)
      (Source.Coordinates.graph after.run carrier)
      (Locality.querySupport before.run carrier query)
      (Locality.querySupport after.run carrier query))
    (coverBefore : ∀ n ∈ Source.Coordinates.names before.run, n ∈ carrier)
    (coverAfter : ∀ n ∈ Source.Coordinates.names after.run, n ∈ carrier)
    (blocked : (query ∈ Update.blockedQueriesForRun before.run [query]) ↔
      (query ∈ Update.blockedQueriesForRun after.run [query])) :
    BHL.ordinaryStatus before.run query = BHL.ordinaryStatus after.run query :=
  ordinaryStatus_congr before.run after.run query
    (checked_status_eq_of_certificate before after carrier query cert coverBefore coverAfter)
    blocked

/-- **Full public-status preservation from the executable locality test.** -/
theorem publicStatus_eq_of_accepts {first second : Source.SourceInput}
    (before : Source.AcceptedObservation first) (after : Source.AcceptedObservation second)
    (carrier : List Presentation.ArgId) (query : Atom)
    (coverBefore : ∀ n ∈ Source.Coordinates.names before.run, n ∈ carrier)
    (coverAfter : ∀ n ∈ Source.Coordinates.names after.run, n ∈ carrier)
    (accepts : (Locality.checkLocality (Source.Coordinates.graph before.run carrier)
      (Source.Coordinates.graph after.run carrier)
      (Locality.querySupport before.run carrier query)
      (Locality.querySupport after.run carrier query)).accepted = true)
    (blocked : (query ∈ Update.blockedQueriesForRun before.run [query]) ↔
      (query ∈ Update.blockedQueriesForRun after.run [query])) :
    BHL.ordinaryStatus before.run query = BHL.ordinaryStatus after.run query :=
  ordinaryStatus_eq_of_certificate before after carrier query
    (Locality.checked_certificate_of_accepts before after carrier query accepts)
    coverBefore coverAfter blocked

/-- The public-status preservation restated at the accepted observation. -/
theorem observation_publicStatus_eq_of_accepts {first second : Source.SourceInput}
    (before : Source.AcceptedObservation first) (after : Source.AcceptedObservation second)
    (carrier : List Presentation.ArgId) (query : Atom)
    (coverBefore : ∀ n ∈ Source.Coordinates.names before.run, n ∈ carrier)
    (coverAfter : ∀ n ∈ Source.Coordinates.names after.run, n ∈ carrier)
    (accepts : (Locality.checkLocality (Source.Coordinates.graph before.run carrier)
      (Source.Coordinates.graph after.run carrier)
      (Locality.querySupport before.run carrier query)
      (Locality.querySupport after.run carrier query)).accepted = true)
    (blocked : (query ∈ Update.blockedQueriesForRun before.run [query]) ↔
      (query ∈ Update.blockedQueriesForRun after.run [query])) :
    Source.AcceptedObservation.publicStatus before query =
      Source.AcceptedObservation.publicStatus after query :=
  publicStatus_eq_of_accepts before after carrier query coverBefore coverAfter accepts blocked

/-! ### Changed conditional diagnostics under equal outer tags

`Driver.PublicStatus.evidenceBlocked` carries the conditional four-state label
*inside* the constructor, so two blocked results with different conditional
labels are different statuses: the changed partition retains them. An unchanged
checked graph, an argument's displayed name, or unchanged text at one support
does not protect this. -/

theorem evidenceBlocked_conditional_changed {s t : Grounded.Status} (h : s ≠ t) :
    Driver.PublicStatus.evidenceBlocked s ≠ Driver.PublicStatus.evidenceBlocked t := by
  intro he
  exact h (Driver.PublicStatus.evidenceBlocked.inj he)

theorem conditional_diagnostic_recorded {sb sa : Grounded.Status} (h : sb ≠ sa) :
    decide (Driver.PublicStatus.evidenceBlocked sb ≠
      Driver.PublicStatus.evidenceBlocked sa) = true :=
  decide_eq_true_eq.mpr (evidenceBlocked_conditional_changed h)

/-! ### Entitlement is never transported from public-status equality

Public-status equality says nothing about entitlement. Impact therefore records
the failed-sibling distinction — equal graph and equal public status, different
audit count/guarantee — instead of substituting a source/public-status
certificate for an entitlement certificate. -/

/-- **No theorem transports entitlement from public-status equality.** Given one
pair whose public statuses agree while entitlement differs, the implication
"equal public status ⇒ equal entitlement" is refuted. -/
theorem no_entitlement_from_public_status {α : Type} (status : α → Driver.PublicStatus)
    (entitled : α → Prop)
    (witness : ∃ x y, status x = status y ∧ entitled x ∧ ¬ entitled y) :
    ¬ (∀ x y, status x = status y → (entitled x ↔ entitled y)) := by
  obtain ⟨x, y, hst, hx, hy⟩ := witness
  intro h
  exact hy ((h x y hst).mp hx)

/-- The recorded shape of the failed-sibling distinction an impact certificate
must carry: graph and public status may agree while the audit count/guarantee
changes. Impact records this distinction and never uses a source/public-status
certificate as an entitlement certificate. -/
structure EntitlementDistinction (α : Type) where
  before : α
  after : α
  graphSame : Prop
  publicStatusSame : Prop
  auditCountChanged : Prop

/-- Impact keeps the distinction: a pair with equal public status but a changed
audit guarantee is exactly a witness that refutes entitlement transport. -/
theorem impact_records_distinction {α : Type} (status : α → Driver.PublicStatus)
    (entitled : α → Prop) (x y : α)
    (same : status x = status y) (entitledX : entitled x) (notEntitledY : ¬ entitled y) :
    (∃ u v, status u = status v) ∧
      ¬ (∀ u v, status u = status v → (entitled u ↔ entitled v)) :=
  ⟨⟨x, y, same⟩, no_entitlement_from_public_status status entitled ⟨x, y, same, entitledX, notEntitledY⟩⟩

end Lara.Process.Impact
