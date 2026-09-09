/-
Policy admission at the trusted source boundary (runtime plan §2; metatheory
plan Task 2).

Mirrors, in the executable Lean core, the semantic source judgment that
`Lara.Admission.Internal` (Haskell) computes for the `.lara` pipeline:

    declared leaves -> validate table -> first reject? -> quarantine seed
                    -> union inconsistent groups -> one prune -> audit

The Lean model is the *semantic* judgment only: it consumes the declared leaf
metadata, the admission table, the declared leaf/argument/attack tables, and
the duplicate-report groups, and produces either a source invalidity, an R8
rejection, or the accepted carrier (policy seed, group seed, one combined
prune, and the canonical audit).  The concrete `.lara` parser, the structural
elaborator, and the replay identity are validated by Haskell tests; Lean
proves the judgment the runtime computes (verified-versus-validated caveat).

## Two context layers (metatheory plan §2.1)

    Gamma_policy  = declared leaves whose policy decision is admit
    Gamma_checked = Gamma_policy minus group-quarantined members

Policy `quarantine` and `reject` both keep a leaf out of `Gamma_policy`;
`reject` additionally stops the whole source at the first such leaf (R8).
`Gamma_checked` is exactly the leaf table the checker sees after the single
policy/group prune.

## Raw and semantic attacks (metatheory plan §2.3)

Filtering is endpoint-safe: the kept attacks are the `selectAligned`
projection of the declared resolved attacks under a raw-endpoint keep
predicate, never a re-resolution or a support-term equality.  The alignment
commutation is `Lara.RawAttack.resolve_filter_commute`; theorem
`retained_attacks_selectAligned` states it in admission terms.
-/
import Lara.Presentation
import Lara.RawAttack
import Lara.Groups
import Lara.BlockedProgram
import Lara.Compile
import Lara.Check.Unit

namespace Lara.Admission

open Lara Lara.Support
open Lara.Presentation (LeafKind Provenance Admission)
open Lara.RawAttack
open Lara.Attack
open Lara.Groups Lara.BlockedProgram Lara.Compile Lara.Consistency

/-! ### Source-boundary vocabulary (closed constructors) -/

/-- Declared leaf metadata: one entry per declared leaf, aligned to the
declared leaf table by `id`.  Duplicate ids are source-invalid. -/
structure LeafMeta where
  id : LeafId
  kind : Lara.Presentation.LeafKind
  provenance : Lara.Presentation.Provenance
deriving DecidableEq

/-- One admission-table row: a `(LeafKind, Provenance)` key and its decision.
Omitted and unmatched keys default to admit. -/
structure AdmissionRow where
  key : Lara.Presentation.LeafKind × Lara.Presentation.Provenance
  decision : Lara.Presentation.Admission
deriving DecidableEq

/-- Why a leaf left the checking context.  Canonical cause order: policy
first, then every inconsistent containing group in group declaration order. -/
inductive AdmissionCause where
  | policy
  | group : String → AdmissionCause
deriving DecidableEq

/-- The canonical source audit: removed leaf rows with their causes (leaf
declaration order, every row non-empty, policy cause first, then one cause
per inconsistent containing group in group declaration order), removed
argument ids (declaration order), and removed raw attacks (declaration
order, with multiplicity). -/
structure AdmissionAudit where
  leaves : List (LeafId × List AdmissionCause)
  args : List String
  attacks : List RawAttack
deriving DecidableEq

/-- A located R8 decision: the first rejected leaf in declaration order and
its matched `(key, reject)` row. -/
structure AdmissionRejection where
  leaf : LeafId
  kind : Lara.Presentation.LeafKind
  provenance : Lara.Presentation.Provenance
  matched : AdmissionRow
deriving DecidableEq

/-- Source invalidity that precedes any admission decision (mirrors the
`prepareSource` precedence: duplicate admission keys, then duplicate leaf
ids.  The Lean semantic carrier additionally rejects metadata and leaf tables
whose identifiers are not equal position-by-position). -/
inductive SourceInvalid where
  | duplicateAdmissionKey : Lara.Presentation.LeafKind × Lara.Presentation.Provenance → SourceInvalid
  | duplicateLeafId : LeafId → SourceInvalid
  | metadataLeafMisalignment : SourceInvalid
deriving DecidableEq

/-- Raw attack declarations paired with the unique semantic list produced by
endpoint resolution, over a declared argument table whose ids are unique. An
admission evaluator can only be called with this validated carrier, so
`selectAligned` never receives an unrelated or truncated resolved list.

`ids_nodup` is the R14 well-formedness both front doors already enforce (the
wire decoder's `Lara.Driver.decodeUnit`, the `.lara` elaborator's
`DuplicateArgId`), carried here as a proof because the prune *needs* it:
retention is decided per argument row but attacks are filtered by endpoint
*id*, so with two rows sharing an id a kept id no longer implies the resolved
row survived — the prune would retain an attack whose semantic source it had
just removed. With unique ids the two coincide
(`Lara.RawAttack.lookupArg_of_mem_nodup`, `retained_attack_source_retained`). -/
structure AlignedAttacks (argsRaw : List (String × SupportTerm))
    (rawAtts : List RawAttack) where
  resolved : List Attack
  resolve_eq : resolveAttacks argsRaw rawAtts = .ok resolved
  ids_nodup : (argsRaw.map (·.1)).Nodup

/-- The policy/group prune: the one ordered quarantine computation the
runtime performs — policy seed unioned with inconsistent-group members, then
a single leaf/argument/attack filter (mirrors
`Lara.Blocked.pruneWithPolicySeed`). -/
structure AdmissionPrune where
  policySeed : List LeafId
  groupSeed : List LeafId
  removedSeed : List LeafId
  removedLeaves : List LeafId
  checkedLeaves : List (LeafId × Atom)
  keptArgs : List (String × SupportTerm)
  keptIds : List String
  removedArgs : List String
  keptAttacks : List Attack
  removedAttacks : List RawAttack
  keep : (String × SupportTerm) → Bool
  keepAttack : RawAttack → Bool

/-- The accepted source carrier: the combined prune plus the declared
resolved attacks it was aligned with and the canonical audit. -/
structure AdmissionResult where
  prune : AdmissionPrune
  declaredResolved : List Attack
  audit : AdmissionAudit

/-- The source admission outcome.  A `rejected` outcome carries an R8
decision and **no checked unit** (the outcome type has no unit-carrying
branch); `accepted` carries the full carrier. -/
inductive SourceAdmission where
  | invalid : SourceInvalid → SourceAdmission
  | rejected : AdmissionRejection → SourceAdmission
  | accepted : AdmissionResult → SourceAdmission

/-! ### Total lookup, validation, and the first rejection -/

/-- Total admission decision: omitted and unmatched keys default to admit.
Duplicate keys are rejected by validation before any decision is made, so
the first-row `find?` agrees with the runtime's `Map` lookup on every
observable input. -/
def decisionFor (table : List AdmissionRow) (kind : Lara.Presentation.LeafKind)
    (provenance : Lara.Presentation.Provenance) : Lara.Presentation.Admission :=
  match table.find? (fun r => r.key = (kind, provenance)) with
  | some r => r.decision
  | none => .admit

/-- The first duplicate admission key in declaration order. -/
def firstDuplicateKeyAux : List (Lara.Presentation.LeafKind × Lara.Presentation.Provenance) →
    List (Lara.Presentation.LeafKind × Lara.Presentation.Provenance) →
    Option (Lara.Presentation.LeafKind × Lara.Presentation.Provenance)
  | [], _ => none
  | k :: ks, seen => if k ∈ seen then some k else firstDuplicateKeyAux ks (k :: seen)

/-- The first duplicate admission key in declaration order (none = valid). -/
def firstDuplicateKey (table : List AdmissionRow) :
    Option (Lara.Presentation.LeafKind × Lara.Presentation.Provenance) :=
  firstDuplicateKeyAux (table.map (·.key)) []

/-- The first duplicate leaf id in declaration order (metadata alignment). -/
def firstDuplicateLeafIdAux : List LeafId → List LeafId → Option LeafId
  | [], _ => none
  | l :: ls, seen => if l ∈ seen then some l else firstDuplicateLeafIdAux ls (l :: seen)

/-- The first duplicate declared leaf id (none = valid metadata). -/
def firstDuplicateLeafId (metas : List LeafMeta) : Option LeafId :=
  firstDuplicateLeafIdAux (metas.map (·.id)) []

private theorem firstDuplicateLeafIdAux_none_no_seen (ids seen : List LeafId)
    (h : firstDuplicateLeafIdAux ids seen = none) :
    ∀ l ∈ ids, l ∉ seen := by
  intro l hl
  induction ids generalizing seen with
  | nil => simp at hl
  | cons head tail ih =>
      by_cases hhead : head ∈ seen
      · simp [firstDuplicateLeafIdAux, hhead] at h
      · have htail : firstDuplicateLeafIdAux tail (head :: seen) = none := by
          simpa [firstDuplicateLeafIdAux, hhead] using h
        rcases List.mem_cons.mp hl with rfl | hl
        · exact hhead
        · have hnot := ih (head :: seen) htail hl
          exact fun hin => hnot (by simp [hin])

private theorem firstDuplicateLeafIdAux_none_nodup (ids seen : List LeafId)
    (h : firstDuplicateLeafIdAux ids seen = none) : ids.Nodup := by
  induction ids generalizing seen with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      by_cases hhead : head ∈ seen
      · simp [firstDuplicateLeafIdAux, hhead] at h
      · have htail : firstDuplicateLeafIdAux tail (head :: seen) = none := by
          simpa [firstDuplicateLeafIdAux, hhead] using h
        apply List.nodup_cons.mpr
        refine ⟨?_, ih (head :: seen) htail⟩
        intro hmem
        exact
          (firstDuplicateLeafIdAux_none_no_seen tail (head :: seen)
            htail head hmem) (by simp)

private theorem firstDuplicateLeafIdAux_none_of_nodup
    (ids seen : List LeafId) (hnodup : ids.Nodup)
    (hdisjoint : ∀ l ∈ ids, l ∉ seen) :
    firstDuplicateLeafIdAux ids seen = none := by
  induction ids generalizing seen with
  | nil => rfl
  | cons head tail ih =>
      have hhead : head ∉ seen := hdisjoint head (by simp)
      have htailNodup := (List.nodup_cons.mp hnodup).2
      have htailDisjoint : ∀ l ∈ tail, l ∉ head :: seen := by
        intro l hl hmem
        rcases List.mem_cons.mp hmem with heq | hseen
        · exact (List.nodup_cons.mp hnodup).1 (heq ▸ hl)
        · exact hdisjoint l (by simp [hl]) hseen
      simp [firstDuplicateLeafIdAux, hhead,
        ih (head :: seen) htailNodup htailDisjoint]

/-- The leaf-id duplicate detector succeeds exactly when declared metadata
identifiers are pairwise distinct. -/
theorem firstDuplicateLeafId_none_iff_nodup (metas : List LeafMeta) :
    firstDuplicateLeafId metas = none ↔ (metas.map (·.id)).Nodup := by
  constructor
  · intro h
    apply firstDuplicateLeafIdAux_none_nodup
    simpa [firstDuplicateLeafId] using h
  · intro h
    apply firstDuplicateLeafIdAux_none_of_nodup _ [] h
    simp

/-- Metadata and semantic leaf rows describe one declaration-ordered source
exactly when their identifier lists are equal position-by-position. -/
def metadataLeafAligned (metas : List LeafMeta) (leaves : List (LeafId × Atom)) : Prop :=
  metas.map (·.id) = leaves.map (·.1)

instance metadataLeafAlignedDecidable (metas : List LeafMeta)
    (leaves : List (LeafId × Atom)) : Decidable (metadataLeafAligned metas leaves) := by
  unfold metadataLeafAligned
  infer_instance

/-- The first rejected leaf in declaration order, with its matched
`(key, reject)` row. -/
def firstAdmissionRejection (table : List AdmissionRow) (metas : List LeafMeta) :
    Option AdmissionRejection :=
  go table metas
where
  go : List AdmissionRow → List LeafMeta → Option AdmissionRejection
  | _, [] => none
  | table, m :: ms =>
      if decisionFor table m.kind m.provenance = .reject then
        some
          { leaf := m.id
          , kind := m.kind
          , provenance := m.provenance
          , matched := { key := (m.kind, m.provenance), decision := .reject } }
      else go table ms

/-- Policy-quarantined leaf ids in source declaration order. -/
def policyQuarantineSeed (table : List AdmissionRow) (metas : List LeafMeta) : List LeafId :=
  metas.filterMap (fun m =>
    if decisionFor table m.kind m.provenance = .quarantine then some m.id else none)

/-! ### The two context layers -/

/-- The policy-admitted context: declared leaves whose decision is admit
(`Gamma_policy`). -/
def policyAdmitted (table : List AdmissionRow) (metas : List LeafMeta) : List LeafMeta :=
  metas.filter (fun m => decide (decisionFor table m.kind m.provenance = .admit))

/-- The ids of `Gamma_policy`. -/
def policyAdmittedIds (table : List AdmissionRow) (metas : List LeafMeta) : List LeafId :=
  (policyAdmitted table metas).map (·.id)

/-- The final checker leaf table after the one policy/group prune.  Both the
named `Gamma_checked` view and `AdmissionPrune.checkedLeaves` project this
single declaration-ordered definition. -/
def checkedLeafTable (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (groups : List Groups.DupGroup) : List (LeafId × Atom) :=
  Groups.quarantineLeaves
    (policyQuarantineSeed table metas ++ Groups.quarantined canon leaves groups)
    leaves

/-- The ids of the actual checker context (`Gamma_checked`). -/
def checkedAdmittedIds (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (groups : List Groups.DupGroup) : List LeafId :=
  (checkedLeafTable canon table metas leaves groups).map (·.1)

/-! ### The single combined prune -/

/-- The inconsistent groups in group declaration order (the group seed and
the audit's group causes both read these). -/
def inconsistentGroups (canon : String → String) (leaves : List (LeafId × Atom))
    (groups : List Groups.DupGroup) : List Groups.DupGroup :=
  groups.filter (fun g => ! Groups.consistentB canon leaves g)

/-- The leaf table the checker sees after the prune. -/
def buildGamma (leaves : List (LeafId × Atom)) : LeafId → Option Atom :=
  fun l => (leaves.find? (fun e => decide (e.1 = l))).map (·.2)

/-! `buildGamma` is first-wins over the declaration list. The four facts below
are the whole of what its consumers (`Lara.Update`'s Γ transport,
`Lara.Context`'s linked environment) need, and they are public here rather
than re-proved privately downstream (issue #220). -/

/-- Appending declarations never loses an existing entry. -/
theorem buildGamma_append_of_some
    (leaves extra : List (LeafId × Atom)) {l : LeafId} {p : Atom}
    (h : buildGamma leaves l = some p) :
    buildGamma (leaves ++ extra) l = some p := by
  unfold buildGamma at h ⊢
  obtain ⟨row, hfind, hterm⟩ := Option.map_eq_some_iff.mp h
  rw [List.find?_append, hfind]
  simp [hterm]

/-- Appending one declaration leaves every *other* identifier's entry alone. -/
theorem buildGamma_append_ne
    (leaves : List (LeafId × Atom)) (fresh : LeafId) (a : Atom)
    {l : LeafId} (hne : l ≠ fresh) :
    buildGamma (leaves ++ [(fresh, a)]) l = buildGamma leaves l := by
  unfold buildGamma
  rw [List.find?_append]
  cases leaves.find? (fun e => decide (e.1 = l)) <;>
    simp [Ne.symm hne]

/-- An identifier the prefix does not declare is read from the suffix. -/
theorem buildGamma_append_fresh (leaves extra : List (LeafId × Atom)) {l : LeafId}
    (hfresh : l ∉ leaves.map (·.1)) :
    buildGamma (leaves ++ extra) l = buildGamma extra l := by
  unfold buildGamma
  rw [List.find?_append,
    List.find?_eq_none.mpr (by
      intro row hrow hdec
      exact hfresh (List.mem_map.mpr ⟨row, hrow, of_decide_eq_true hdec⟩))]
  rfl

/-- An entry comes from a declaration. -/
theorem buildGamma_some_mem {leaves : List (LeafId × Atom)}
    {l : LeafId} {p : Atom}
    (h : buildGamma leaves l = some p) :
    l ∈ leaves.map (·.1) := by
  unfold buildGamma at h
  obtain ⟨row, hfind, -⟩ := Option.map_eq_some_iff.mp h
  exact List.mem_map.mpr
    ⟨row, List.mem_of_find?_eq_some hfind,
      of_decide_eq_true (List.find?_eq_some_iff_getElem.mp hfind).1⟩

/-- The single leaf/argument/attack prune with the policy seed unioned once
with the inconsistent-group members.  The kept attacks are the `selectAligned`
projection of the declared resolved attacks under the raw-endpoint keep. -/
def buildPrune (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declaredResolved : List Attack) : AdmissionPrune :=
  let policySeed := policyQuarantineSeed table metas
  let groupSeed := Groups.quarantined canon leaves groups
  let removedSeed := policySeed ++ groupSeed
  let removedLeaves := leaves.filterMap (fun e =>
    if e.1 ∈ removedSeed then some e.1 else none)
  let keep := fun a : String × SupportTerm => ! Groups.usesLeaf removedSeed a.2
  let keptArgs := argsRaw.filter keep
  let keptIds := keptArgs.map (·.1)
  let keepAttack := fun ra : RawAttack =>
    let (s, t) := ra.endpoints
    decide (s ∈ keptIds) && decide (t ∈ keptIds)
  let removedArgs := argsRaw.filterMap (fun a =>
    if keep a then none else some a.1)
  let removedAttacks := rawAtts.filter (fun ra => ! keepAttack ra)
  let keptAttacks := selectAligned keepAttack rawAtts declaredResolved
  { policySeed := policySeed
  , groupSeed := groupSeed
  , removedSeed := removedSeed
  , removedLeaves := removedLeaves
  , checkedLeaves := checkedLeafTable canon table metas leaves groups
  , keptArgs := keptArgs
  , keptIds := keptIds
  , removedArgs := removedArgs
  , keptAttacks := keptAttacks
  , removedAttacks := removedAttacks
  , keep := keep
  , keepAttack := keepAttack }

/-! ### The canonical audit -/

/-- The canonical leaf rows: for each removed leaf, the policy cause first,
then one cause per inconsistent group containing the leaf, in group
declaration order. -/
def auditLeaves (policySeed : List LeafId) (inconsistent : List Groups.DupGroup)
    (removedLeaves : List LeafId) : List (LeafId × List AdmissionCause) :=
  removedLeaves.map (fun l =>
    let policyCauses := if l ∈ policySeed then [.policy] else []
    let groupCauses := inconsistent.filterMap (fun g =>
      if l ∈ g.members then some (.group g.id) else none)
    (l, policyCauses ++ groupCauses))

/-- Project the canonical audit from the combined prune.  No support or
endpoint removal decision is repeated here. -/
def buildAdmissionAudit (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declaredResolved : List Attack) : AdmissionAudit :=
  let p := buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved
  { leaves := auditLeaves p.policySeed (inconsistentGroups canon leaves groups) p.removedLeaves
  , args := p.removedArgs
  , attacks := p.removedAttacks }

/-! ### The executable evaluator -/

/-- The executable source admission judgment, mirroring the `prepareSource`
precedence: duplicate admission keys, then duplicate leaf ids, then ordered
metadata/leaf alignment, then the first R8 rejection, then the single prune
and canonical audit. Raw and resolved attacks enter only through
`AlignedAttacks`; the `.lara` front door and wire decoder establish that
endpoint-resolution proof before admission. -/
def evaluateAdmission (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declared : AlignedAttacks argsRaw rawAtts) :
    SourceAdmission :=
  match firstDuplicateKey table with
  | some k => .invalid (.duplicateAdmissionKey k)
  | none =>
    match firstDuplicateLeafId metas with
    | some l => .invalid (.duplicateLeafId l)
    | none =>
      if metadataLeafAligned metas leaves then
        match firstAdmissionRejection table metas with
        | some r => .rejected r
        | none =>
          .accepted
            { prune := buildPrune canon table metas leaves argsRaw rawAtts groups declared.resolved
            , declaredResolved := declared.resolved
            , audit := buildAdmissionAudit canon table metas leaves argsRaw rawAtts groups
                declared.resolved }
      else .invalid .metadataLeafMisalignment

/-! ### The declarative judgment -/

/-- The declarative source-admission relation. A rejected outcome is related
exactly when the first rejected leaf is `r`; an accepted outcome only when the
table has no duplicate keys, the metadata has no duplicate leaf ids, metadata
and leaf rows are ordered-aligned, no declared leaf is rejected, the raw and
resolved attacks are carried by `AlignedAttacks`, and the result is canonical. -/
inductive AdmissionJudgment (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declared : AlignedAttacks argsRaw rawAtts) :
    SourceAdmission → Prop where
  | invalid_key : (hk : firstDuplicateKey table = some k) →
      AdmissionJudgment canon table metas leaves argsRaw rawAtts groups declared
        (.invalid (.duplicateAdmissionKey k))
  | invalid_id : (hk : firstDuplicateKey table = none) →
      (hl : firstDuplicateLeafId metas = some l) →
      AdmissionJudgment canon table metas leaves argsRaw rawAtts groups declared
        (.invalid (.duplicateLeafId l))
  | invalid_alignment : (hk : firstDuplicateKey table = none) →
      (hl : firstDuplicateLeafId metas = none) →
      (ha : ¬ metadataLeafAligned metas leaves) →
      AdmissionJudgment canon table metas leaves argsRaw rawAtts groups declared
        (.invalid .metadataLeafMisalignment)
  | rejected : (hk : firstDuplicateKey table = none) →
      (hl : firstDuplicateLeafId metas = none) →
      (ha : metadataLeafAligned metas leaves) →
      (hr : firstAdmissionRejection table metas = some r) →
      AdmissionJudgment canon table metas leaves argsRaw rawAtts groups declared
        (.rejected r)
  | accepted : (hk : firstDuplicateKey table = none) →
      (hl : firstDuplicateLeafId metas = none) →
      (ha : metadataLeafAligned metas leaves) →
      (hn : firstAdmissionRejection table metas = none) →
      (hcar : carrier =
        { prune := buildPrune canon table metas leaves argsRaw rawAtts groups declared.resolved
        , declaredResolved := declared.resolved
        , audit := buildAdmissionAudit canon table metas leaves argsRaw rawAtts groups
            declared.resolved }) →
      AdmissionJudgment canon table metas leaves argsRaw rawAtts groups declared
        (.accepted carrier)

/-! ### Evaluator/judgment correspondence -/

/-- The evaluator returns an outcome exactly when the declarative judgment
relates the same validated input and outcome. -/
theorem evaluateAdmission_iff_judgment (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declared : AlignedAttacks argsRaw rawAtts)
    (o : SourceAdmission) :
    AdmissionJudgment canon table metas leaves argsRaw rawAtts groups declared o ↔
      evaluateAdmission canon table metas leaves argsRaw rawAtts groups declared = o := by
  constructor
  · intro hj
    cases hj with
    | invalid_key hk => simp [evaluateAdmission, hk]
    | invalid_id hk hl => simp [evaluateAdmission, hk, hl]
    | invalid_alignment hk hl ha => simp [evaluateAdmission, hk, hl, ha]
    | rejected hk hl ha hr => simp [evaluateAdmission, hk, hl, ha, hr]
    | accepted hk hl ha hn hcar =>
        simp [evaluateAdmission, hk, hl, ha, hn]
        rw [hcar]
  · intro h
    cases hk : firstDuplicateKey table with
    | some k =>
        rw [evaluateAdmission, hk] at h
        rw [← h]
        exact AdmissionJudgment.invalid_key hk
    | none =>
        cases hl : firstDuplicateLeafId metas with
        | some l =>
            rw [evaluateAdmission, hk, hl] at h
            rw [← h]
            exact AdmissionJudgment.invalid_id hk hl
        | none =>
            by_cases ha : metadataLeafAligned metas leaves
            · cases hf : firstAdmissionRejection table metas with
              | some r' =>
                  simp [evaluateAdmission, hk, hl, ha, hf] at h
                  rw [← h]
                  exact AdmissionJudgment.rejected hk hl ha hf
              | none =>
                  simp [evaluateAdmission, hk, hl, ha, hf] at h
                  rw [← h]
                  exact AdmissionJudgment.accepted hk hl ha hf rfl
            · simp [evaluateAdmission, hk, hl, ha] at h
              rw [← h]
              exact AdmissionJudgment.invalid_alignment hk hl ha

/-- Every accepted evaluator result certifies all source-validation checks:
the admission table and metadata identifiers are duplicate-free, metadata and
semantic leaf rows are aligned, and no policy rejection remains. -/
theorem evaluateAdmission_accepted_conditions {canon : String → String}
    {table : List AdmissionRow} {metas : List LeafMeta}
    {leaves : List (LeafId × Atom)}
    {argsRaw : List (String × SupportTerm)} {rawAtts : List RawAttack}
    {groups : List Groups.DupGroup} {declared : AlignedAttacks argsRaw rawAtts}
    {admission : AdmissionResult}
    (haccepted :
      evaluateAdmission canon table metas leaves argsRaw rawAtts groups declared =
        .accepted admission) :
    firstDuplicateKey table = none ∧
      firstDuplicateLeafId metas = none ∧
      metadataLeafAligned metas leaves ∧
      firstAdmissionRejection table metas = none := by
  have hj :
      AdmissionJudgment canon table metas leaves argsRaw rawAtts groups declared
        (.accepted admission) :=
    (evaluateAdmission_iff_judgment canon table metas leaves argsRaw rawAtts
      groups declared (.accepted admission)).mpr haccepted
  cases hj with
  | accepted hk hl ha hn _ => exact ⟨hk, hl, ha, hn⟩

/-- **The admission judgment is functional.** Two derivable outcomes for the
same validated input coincide. -/
theorem admission_deterministic (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declared : AlignedAttacks argsRaw rawAtts)
    {o1 o2 : SourceAdmission}
    (h1 : AdmissionJudgment canon table metas leaves argsRaw rawAtts groups declared o1)
    (h2 : AdmissionJudgment canon table metas leaves argsRaw rawAtts groups declared o2) :
    o1 = o2 := by
  have h1' :=
    (evaluateAdmission_iff_judgment canon table metas leaves argsRaw rawAtts groups declared o1).mp h1
  have h2' :=
    (evaluateAdmission_iff_judgment canon table metas leaves argsRaw rawAtts groups declared o2).mp h2
  exact h1'.symm.trans h2'

/-! ### The two context layers -/

/-- **`Gamma_policy`, exact.**  A leaf id is policy-admitted exactly when it
is declared and its decision is admit. -/
theorem policy_admitted_iff (table : List AdmissionRow) (metas : List LeafMeta) (l : LeafId) :
    l ∈ policyAdmittedIds table metas ↔
      ∃ m ∈ metas, m.id = l ∧ decisionFor table m.kind m.provenance = .admit := by
  constructor
  · intro hl
    rw [policyAdmittedIds, policyAdmitted] at hl
    obtain ⟨m, hmem, rfl⟩ := List.mem_map.mp hl
    have hmf := List.mem_filter.mp hmem
    exact ⟨m, hmf.1, rfl, by simpa using (of_decide_eq_true hmf.2)⟩
  · rintro ⟨m, hm, rfl, hdec⟩
    rw [policyAdmittedIds, policyAdmitted]
    exact List.mem_map.mpr ⟨m, List.mem_filter.mpr ⟨hm, by simp [hdec]⟩, rfl⟩

/-- **`Gamma_checked`, exact.**  A leaf id is in the final checker context
exactly when its declared row survives both the policy and group seeds. -/
theorem checked_admitted_iff (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (groups : List Groups.DupGroup) (l : LeafId) :
    l ∈ checkedAdmittedIds canon table metas leaves groups ↔
      ∃ e ∈ leaves, e.1 = l ∧
        l ∉ policyQuarantineSeed table metas ∧
        l ∉ Groups.quarantined canon leaves groups := by
  rw [checkedAdmittedIds, checkedLeafTable, Groups.quarantineLeaves]
  constructor
  · intro hl
    obtain ⟨e, he, hid⟩ := List.mem_map.mp hl
    subst l
    have hfilter := List.mem_filter.mp he
    have hnot : e.1 ∉
        policyQuarantineSeed table metas ++ Groups.quarantined canon leaves groups := by
      have hfalse : decide (e.1 ∈
          policyQuarantineSeed table metas ++ Groups.quarantined canon leaves groups) = false := by
        simpa using hfilter.2
      exact decide_eq_false_iff_not.mp hfalse
    refine ⟨e, hfilter.1, rfl, ?_, ?_⟩
    · intro hp
      exact hnot (List.mem_append.mpr (Or.inl hp))
    · intro hg
      exact hnot (List.mem_append.mpr (Or.inr hg))
  · rintro ⟨e, he, hid, hp, hg⟩
    apply List.mem_map.mpr
    refine ⟨e, List.mem_filter.mpr ⟨he, ?_⟩, hid⟩
    have hnot : e.1 ∉
        policyQuarantineSeed table metas ++ Groups.quarantined canon leaves groups := by
      intro hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · apply hp
        rwa [← hid]
      · apply hg
        rwa [← hid]
    have hfalse : decide (e.1 ∈
        policyQuarantineSeed table metas ++ Groups.quarantined canon leaves groups) = false :=
      decide_eq_false_iff_not.mpr hnot
    rw [hfalse]
    rfl

/-- The named checked-context ids are definitionally the ids in the prune
passed to `checkUnit`. -/
theorem checked_admitted_ids_eq_prune (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declaredResolved : List Attack) :
    checkedAdmittedIds canon table metas leaves groups =
      (buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved).checkedLeaves.map (·.1) := by
  rfl

/-- Unique leaf ids make the id-to-meta map functional: two metas with the
same id are equal. -/
theorem nodup_ids_eq_of_mem {metas : List LeafMeta} (hn : (metas.map (·.id)).Nodup)
    {m1 m2 : LeafMeta} (h1 : m1 ∈ metas) (h2 : m2 ∈ metas)
    (hid : m1.id = m2.id) : m1 = m2 := by
  obtain ⟨i1, hi1⟩ := List.mem_iff_getElem?.mp h1
  obtain ⟨i2, hi2⟩ := List.mem_iff_getElem?.mp h2
  have hi1map : (metas.map (·.id))[i1]? = some m1.id := by
    rw [List.getElem?_map]
    simpa [hi1]
  have hi2map : (metas.map (·.id))[i2]? = some m2.id := by
    rw [List.getElem?_map]
    simpa [hi2]
  have hlen : i1 < (metas.map (·.id)).length := lt_of_getElem?_some hi1map
  have hij : i1 = i2 := by
    apply (List.getElem?_inj hlen hn).mp
    rw [hi1map, hi2map, hid]
  subst i2
  have : some m1 = some m2 := by
    rw [← hi1, hi2]
  exact Option.some.inj this

/-- **Policy-quarantined leaves are absent from `Gamma_checked`.** -/
theorem policy_quarantined_absent (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (groups : List Groups.DupGroup)
    {m : LeafMeta} (hm : m ∈ metas)
    (hdec : decisionFor table m.kind m.provenance = .quarantine) :
    m.id ∉ checkedAdmittedIds canon table metas leaves groups := by
  intro hmem
  obtain ⟨_, _, _, hnot, _⟩ :=
    (checked_admitted_iff canon table metas leaves groups m.id).mp hmem
  apply hnot
  rw [policyQuarantineSeed, List.mem_filterMap]
  exact ⟨m, hm, by simp [hdec]⟩

/-! ### The prune exclusions -/

/-- **Policy-quarantined arguments are excluded.**  An argument whose
support term uses a policy-quarantined leaf is not retained by the combined
prune. -/
theorem policy_quarantined_arg_excluded (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declaredResolved : List Attack)
    {a : String × SupportTerm}
    (huses : Groups.usesLeaf (policyQuarantineSeed table metas) a.2 = true) :
    a ∉ (buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved).keptArgs := by
  intro hmem
  have hkeep : (buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved).keep a = true :=
    (List.mem_filter.mp hmem).2
  have hkeep' : ! Groups.usesLeaf
      (policyQuarantineSeed table metas ++ Groups.quarantined canon leaves groups) a.2 = true := by
    simpa [buildPrune] using hkeep
  have hfalse : Groups.usesLeaf
      (policyQuarantineSeed table metas ++ Groups.quarantined canon leaves groups) a.2 = false := by
    simpa using hkeep'
  have htrue : Groups.usesLeaf
      (policyQuarantineSeed table metas ++ Groups.quarantined canon leaves groups) a.2 = true :=
    Groups.usesLeaf_mono (fun l hl => List.mem_append.mpr (Or.inl hl)) a.2 huses
  rw [htrue] at hfalse
  cases hfalse

/-- **Retained raw attacks name retained endpoints.**  The endpoint-safe
keep holds exactly when both raw endpoints survive in the retained argument
ids. -/
theorem retained_attack_endpoints (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declaredResolved : List Attack)
    {ra : RawAttack}
    (hkeep : (buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved).keepAttack ra = true) :
    ra.endpoints.1 ∈ (buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved).keptIds ∧
    ra.endpoints.2 ∈ (buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved).keptIds := by
  have hk : decide (ra.endpoints.1 ∈
      (buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved).keptIds) &&
      decide (ra.endpoints.2 ∈
        (buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved).keptIds) = true := by
    simpa [buildPrune] using hkeep
  have hk' : decide (ra.endpoints.1 ∈
      (buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved).keptIds) = true ∧
      decide (ra.endpoints.2 ∈
        (buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved).keptIds) = true := by
    simpa using hk
  exact ⟨of_decide_eq_true hk'.1, of_decide_eq_true hk'.2⟩

/-- **A retained attack's resolved endpoints are retained arguments.**  The
prune decides retention per argument row but filters attacks by endpoint id.
Unique declared ids (`AlignedAttacks.ids_nodup`) make the two agree: each
endpoint of a kept attack names a row the prune kept, and that row is exactly
the one the endpoint resolves to.  Without the uniqueness this fails — a second
row sharing the id could keep the endpoint "present" after the resolved row was
pruned, retaining an attack whose semantic source is gone. -/
theorem retained_attack_source_retained (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declared : AlignedAttacks argsRaw rawAtts)
    {ra : RawAttack}
    (hkeep : (buildPrune canon table metas leaves argsRaw rawAtts groups declared.resolved).keepAttack ra = true) :
    (∃ a ∈ (buildPrune canon table metas leaves argsRaw rawAtts groups declared.resolved).keptArgs,
      a.1 = ra.endpoints.1 ∧ lookupArg argsRaw ra.endpoints.1 = some a.2) ∧
    (∃ a ∈ (buildPrune canon table metas leaves argsRaw rawAtts groups declared.resolved).keptArgs,
      a.1 = ra.endpoints.2 ∧ lookupArg argsRaw ra.endpoints.2 = some a.2) := by
  obtain ⟨hsrc, htgt⟩ :=
    retained_attack_endpoints canon table metas leaves argsRaw rawAtts groups
      declared.resolved hkeep
  have hkept : ∀ id,
      id ∈ (buildPrune canon table metas leaves argsRaw rawAtts groups declared.resolved).keptIds →
      ∃ a ∈ (buildPrune canon table metas leaves argsRaw rawAtts groups declared.resolved).keptArgs,
        a.1 = id ∧ lookupArg argsRaw id = some a.2 := by
    intro id hid
    have hid' : id ∈ (buildPrune canon table metas leaves argsRaw rawAtts groups
        declared.resolved).keptArgs.map (·.1) := by
      simpa [buildPrune] using hid
    obtain ⟨a, ha, hida⟩ := List.mem_map.mp hid'
    have hmem : a ∈ argsRaw := by
      have : a ∈ argsRaw.filter (fun a : String × SupportTerm =>
          ! Groups.usesLeaf (policyQuarantineSeed table metas ++
            Groups.quarantined canon leaves groups) a.2) := by
        simpa [buildPrune] using ha
      exact (List.mem_filter.mp this).1
    refine ⟨a, ha, hida, ?_⟩
    rw [← hida]
    exact lookupArg_of_mem_nodup declared.ids_nodup hmem
  exact ⟨hkept _ hsrc, hkept _ htgt⟩

/-- **The retained resolution is the aligned projection.**  When the
declared attacks resolve (the front-door precondition), resolving the
endpoint-kept raw attacks yields exactly the `selectAligned` projection the
combined prune carries — so the checker and the blocking proof consume the
same filtered sublist, with identity by raw endpoint id, never by support
term. -/
theorem retained_attacks_selectAligned (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup)
    {declaredResolved : List Attack}
    (hres : resolveAttacks argsRaw rawAtts = .ok declaredResolved) :
    resolveAttacks argsRaw
        (rawAtts.filter (buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved).keepAttack) =
      .ok (buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved).keptAttacks := by
  rw [resolve_filter_commute argsRaw
    (buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved).keepAttack hres]
  rfl

/-- Every semantic attack retained by the canonical prune has both semantic
endpoints among the retained argument terms.  This packages the raw-id
filter, aligned resolution, and unique-id lookup into the endpoint fact used
by whole-unit checking. -/
theorem retained_semantic_attack_endpoints (canon : String → String)
    (table : List AdmissionRow) (metas : List LeafMeta)
    (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declared : AlignedAttacks argsRaw rawAtts) :
    ∀ k ∈ (buildPrune canon table metas leaves argsRaw rawAtts groups
        declared.resolved).keptAttacks,
      k.source ∈ (buildPrune canon table metas leaves argsRaw rawAtts groups
        declared.resolved).keptArgs.map (·.2) ∧
      k.target ∈ (buildPrune canon table metas leaves argsRaw rawAtts groups
        declared.resolved).keptArgs.map (·.2) := by
  intro k hk
  have hresolved :=
    retained_attacks_selectAligned canon table metas leaves argsRaw rawAtts
      groups declared.resolve_eq
  obtain ⟨ra, hra, hsourceLookup, htargetLookup⟩ :=
    RawAttack.resolveAttacks_attack_lookup argsRaw hresolved k hk
  have hkeep :
      (buildPrune canon table metas leaves argsRaw rawAtts groups
        declared.resolved).keepAttack ra = true :=
    (List.mem_filter.mp hra).2
  obtain ⟨⟨source, hsource, _, hsourceRow⟩,
      ⟨target, htarget, _, htargetRow⟩⟩ :=
    retained_attack_source_retained canon table metas leaves argsRaw rawAtts
      groups declared hkeep
  have hsourceEq : source.2 = k.source :=
    Option.some.inj (hsourceRow.symm.trans hsourceLookup)
  have htargetEq : target.2 = k.target :=
    Option.some.inj (htargetRow.symm.trans htargetLookup)
  exact ⟨List.mem_map.mpr ⟨source, hsource, hsourceEq⟩,
    List.mem_map.mpr ⟨target, htarget, htargetEq⟩⟩

/-! ### The canonical audit -/

/-- **The audit is the combined prune's exact projection.**  Leaf causes,
removed arguments, and removed attacks equal the prune's projections with
canonical multiplicity and order (leaf declaration order, policy cause
first, then one cause per inconsistent containing group in group
declaration order). -/
theorem admission_audit_exact (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declaredResolved : List Attack) :
    let p := buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved
    buildAdmissionAudit canon table metas leaves argsRaw rawAtts groups declaredResolved =
      { leaves := auditLeaves p.policySeed (inconsistentGroups canon leaves groups) p.removedLeaves
      , args := p.removedArgs
      , attacks := p.removedAttacks } := by
  rfl

/-- **Every audit leaf row has a non-empty cause list.**  A leaf is removed
only when the policy or an inconsistent group quarantines it, so no row is
empty (the runtime's `NonEmpty` invariant). -/
theorem audit_leaves_nonempty (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declaredResolved : List Attack) :
    ∀ row ∈ (buildAdmissionAudit canon table metas leaves argsRaw rawAtts groups declaredResolved).leaves,
      row.2 ≠ [] := by
  intro row hrow
  have hrow' : row ∈ auditLeaves (buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved).policySeed
      (inconsistentGroups canon leaves groups)
      (buildPrune canon table metas leaves argsRaw rawAtts groups declaredResolved).removedLeaves := by
    simpa [buildAdmissionAudit] using hrow
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hrow'
  have hrem : ∃ x, x ∈ leaves ∧
      (if x.1 ∈ policyQuarantineSeed table metas ++ Groups.quarantined canon leaves groups
        then some x.1 else none) = some e := by
    simpa [buildPrune] using (List.mem_filterMap.mp he)
  obtain ⟨x, hx, hf⟩ := hrem
  have hin : e ∈ policyQuarantineSeed table metas ++ Groups.quarantined canon leaves groups := by
    by_cases hc : x.1 ∈ policyQuarantineSeed table metas ++ Groups.quarantined canon leaves groups
    · have : x.1 = e := by
        simp [hc] at hf
        exact hf
      rw [← this]
      exact hc
    · simp [hc] at hf
  by_cases hp : e ∈ policyQuarantineSeed table metas
  · simp [auditLeaves, buildPrune, hp]
  · have hg : e ∈ Groups.quarantined canon leaves groups := by
      rcases List.mem_append.mp hin with hin | hg
      · exact absurd hin hp
      · exact hg
    obtain ⟨g, hgmem, hgcon, hmemg⟩ := (Groups.mem_quarantined_iff canon leaves groups e).mp hg
    have hgin : g ∈ inconsistentGroups canon leaves groups := by
      exact List.mem_filter.mpr ⟨hgmem, by simp [inconsistentGroups, hgcon]⟩
    have hsome : (.group g.id) ∈
        (inconsistentGroups canon leaves groups).filterMap (fun g' =>
          if e ∈ g'.members then some ((.group g'.id) : AdmissionCause) else none) := by
      exact List.mem_filterMap.mpr ⟨g, hgin, by simp [hmemg]⟩
    intro hnil
    have hgempty : (inconsistentGroups canon leaves groups).filterMap (fun g' =>
        if e ∈ g'.members then some ((.group g'.id) : AdmissionCause) else none) = [] := by
      simpa [auditLeaves, buildPrune, hp] using hnil
    rw [hgempty] at hsome
    simpa using hsome

/-! ### All-admit identity and restrictiveness -/

/-- **All-admit policy equals the group-only pipeline, structurally.**  With
every decision admit, the policy seed is empty, the combined prune collapses to
the existing §4.3 group quarantine, the keep predicates coincide, and the
blocked-query computation is identical.

Scope, exactly: this theorem states the equalities listed in its conclusion —
the prune's components and `blockedQueries`.  Equality of the *checker's* own
accept/reject result is the separate `policy_all_admit_checkUnit_identity`.
Neither covers the driver stages that sit outside this model: the R13 replay
preflight, the R9 group-conflict boundary, and the assembly of the final public
verdict (grounded labels, per-query statuses, the evidence-blocked overlay).
Identity of the emitted verdict is Haskell conformance evidence
(`test/AdmissionSpec.hs`, `prop_allAdmitSourceVerdictIdentity` — all-admit
source verdict bytes equal the raw checker's), not a Lean proof; do not cite
these two theorems for it. -/
theorem policy_all_admit_group_identity (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declared : AlignedAttacks argsRaw rawAtts)
    (hall : ∀ m ∈ metas, decisionFor table m.kind m.provenance = .admit) :
    let p := buildPrune canon table metas leaves argsRaw rawAtts groups declared.resolved
    let qs := Groups.quarantined canon leaves groups
    p.policySeed = [] ∧
    p.removedSeed = qs ∧
    p.removedLeaves = leaves.filterMap (fun e => if e.1 ∈ qs then some e.1 else none) ∧
    p.checkedLeaves = Groups.quarantineLeaves qs leaves ∧
    p.keptArgs = Groups.quarantineArgs qs argsRaw ∧
    p.keptIds = (Groups.quarantineArgs qs argsRaw).map (·.1) ∧
    p.keep = Groups.keepArg qs ∧
    p.keptAttacks = selectAligned (fun ra : RawAttack =>
      decide (ra.endpoints.1 ∈ (Groups.quarantineArgs qs argsRaw).map (·.1)) &&
      decide (ra.endpoints.2 ∈ (Groups.quarantineArgs qs argsRaw).map (·.1))) rawAtts declared.resolved ∧
    p.removedAttacks = rawAtts.filter (fun ra => ! p.keepAttack ra) ∧
    BlockedProgram.blockedQueries p.keep argsRaw declared.resolved p.keptAttacks =
      BlockedProgram.blockedQueries (Groups.keepArg qs) argsRaw declared.resolved
        (selectAligned (fun ra : RawAttack =>
          decide (ra.endpoints.1 ∈ (Groups.quarantineArgs qs argsRaw).map (·.1)) &&
          decide (ra.endpoints.2 ∈ (Groups.quarantineArgs qs argsRaw).map (·.1))) rawAtts declared.resolved) := by
  have hseed : policyQuarantineSeed table metas = [] := by
    induction metas with
    | nil => rfl
    | cons m ms ih =>
        have hd : decisionFor table m.kind m.provenance = .admit := hall m (by simp)
        have ih' : policyQuarantineSeed table ms = [] :=
          ih (fun m hm => hall m (by simp [hm]))
        unfold policyQuarantineSeed
        simp only [List.filterMap, hd]
        exact ih'
  dsimp
  simp only [buildPrune]
  rw [hseed]
  simp only [checkedLeafTable, hseed, List.nil_append]
  simp [Groups.quarantineArgs, Groups.keepArg]
  repeat (first | constructor | rfl)

/-- The nondependent public outcome of `checkUnit`: exact rejection payload or
successful acceptance. The proof-bearing accepted carrier remains inside the
checker; this projection permits equality across propositionally equal
contexts. -/
def checkUnitOutcome {canon : String → String} (Gamma : LeafId → Option Atom)
    (reg : Lara.Support.BackendRegistry canon) (ground : List Atom)
    (unit : Lara.Unit) :
    Except Lara.Check.Unit.UnitError _root_.Unit :=
  match Lara.Check.Unit.checkUnit Gamma reg ground unit with
  | .error err => .error err
  | .ok _ => .ok ()

/-- **All-admit checked-unit identity.** The actual proof-bearing checker sees
the same `Gamma`, argument list, and endpoint-aligned attack list as the
pre-admission group-only pipeline, so its complete result (accept or reject)
is identical. -/
theorem policy_all_admit_checkUnit_identity (canon : String → String)
    (table : List AdmissionRow) (metas : List LeafMeta)
    (leaves : List (LeafId × Atom)) (argsRaw : List (String × SupportTerm))
    (rawAtts : List RawAttack) (groups : List Groups.DupGroup)
    (declared : AlignedAttacks argsRaw rawAtts)
    (hall : ∀ m ∈ metas, decisionFor table m.kind m.provenance = .admit)
    (reg : Lara.Support.BackendRegistry canon) (policy : Lara.Policy.Policy)
    (sigma : Lara.Sigma.Sigma) (ground : List Atom) :
    let p := buildPrune canon table metas leaves argsRaw rawAtts groups declared.resolved
    let qs := Groups.quarantined canon leaves groups
    checkUnitOutcome (buildGamma p.checkedLeaves) reg ground
        ({ sigma := sigma, policy := policy, args := p.keptArgs.map (·.2), atts := p.keptAttacks } : Lara.Unit) =
      checkUnitOutcome (buildGamma (Groups.quarantineLeaves qs leaves)) reg ground
        ({ sigma := sigma
         , policy := policy
         , args := (Groups.quarantineArgs qs argsRaw).map (·.2)
         , atts := selectAligned (fun ra : RawAttack =>
             decide (ra.endpoints.1 ∈ (Groups.quarantineArgs qs argsRaw).map (·.1)) &&
             decide (ra.endpoints.2 ∈ (Groups.quarantineArgs qs argsRaw).map (·.1)))
             rawAtts declared.resolved } : Lara.Unit) := by
  have hident := policy_all_admit_group_identity canon table metas leaves argsRaw
    rawAtts groups declared hall
  dsimp only at hident ⊢
  rcases hident with ⟨_, _, _, hleaves, hargs, _, _, hatts, _, _⟩
  rw [hleaves, hargs, hatts]

/-- A table `t2` is at least as restrictive as `t1` when it keeps every
non-admit decision and only ever tightens admit rows (admit → quarantine). -/
def AtLeastAsRestrictive (t1 t2 : List AdmissionRow) : Prop :=
  ∀ (k : Lara.Presentation.LeafKind) (p : Lara.Presentation.Provenance),
    decisionFor t1 k p ≠ .admit → decisionFor t2 k p = decisionFor t1 k p

/-- Membership in the policy quarantine seed, exactly. -/
theorem mem_policyQuarantineSeed_iff (table : List AdmissionRow) (metas : List LeafMeta) (l : LeafId) :
    l ∈ policyQuarantineSeed table metas ↔
      ∃ m ∈ metas, m.id = l ∧ decisionFor table m.kind m.provenance = .quarantine := by
  rw [policyQuarantineSeed]
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨m, hm, hsome⟩
    by_cases hd : decisionFor table m.kind m.provenance = .quarantine
    · simp [hd] at hsome
      exact ⟨m, hm, hsome, hd⟩
    · simp [hd] at hsome
  · rintro ⟨m, hm, hid, hq⟩
    rw [← hid]
    exact ⟨m, hm, by simp [hq]⟩

/-- The policy seed grows with restrictiveness. -/
theorem policyQuarantineSeed_subset_of_restrictive {t1 t2 : List AdmissionRow}
    (hrestr : AtLeastAsRestrictive t1 t2) (metas : List LeafMeta) :
    ∀ l, l ∈ policyQuarantineSeed t1 metas → l ∈ policyQuarantineSeed t2 metas := by
  intro l hl
  obtain ⟨m, hm, hid, hq⟩ := (mem_policyQuarantineSeed_iff t1 metas l).mp hl
  apply (mem_policyQuarantineSeed_iff t2 metas l).mpr
  refine ⟨m, hm, hid, ?_⟩
  have hne : decisionFor t1 m.kind m.provenance ≠ .admit := by
    intro hadmit
    rw [hq] at hadmit
    cases hadmit
  have ht2 : decisionFor t2 m.kind m.provenance = decisionFor t1 m.kind m.provenance :=
    hrestr m.kind m.provenance hne
  rw [ht2, hq]

/-- The removed seed (policy ++ groups) grows with restrictiveness. -/
theorem removedSeed_subset_of_restrictive {t1 t2 : List AdmissionRow}
    (hrestr : AtLeastAsRestrictive t1 t2) (canon : String → String)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (groups : List Groups.DupGroup) :
    ∀ l, l ∈ policyQuarantineSeed t1 metas ++ Groups.quarantined canon leaves groups →
      l ∈ policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups := by
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · exact List.mem_append.mpr (Or.inl (policyQuarantineSeed_subset_of_restrictive hrestr metas l hl))
  · exact List.mem_append.mpr (Or.inr hl)

private theorem decision_ne_reject_of_first_none (table : List AdmissionRow)
    (metas : List LeafMeta)
    (hn : firstAdmissionRejection table metas = none) :
    ∀ m ∈ metas, decisionFor table m.kind m.provenance ≠ .reject := by
  intro m hm
  induction metas with
  | nil => simp at hm
  | cons head tail ih =>
      by_cases hd : decisionFor table head.kind head.provenance = .reject
      · simp [firstAdmissionRejection, firstAdmissionRejection.go, hd] at hn
      · have htail : firstAdmissionRejection table tail = none := by
          simpa [firstAdmissionRejection, firstAdmissionRejection.go, hd] using hn
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hd
        · exact ih htail hm

/-- Accepted admission carries the exact ordered metadata/leaf alignment that
the checker-context theorems rely on. -/
theorem accepted_metadata_aligned (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declared : AlignedAttacks argsRaw rawAtts)
    (hacc : evaluateAdmission canon table metas leaves argsRaw rawAtts groups declared =
      .accepted r) :
    metadataLeafAligned metas leaves := by
  exact
    (evaluateAdmission_accepted_conditions hacc).2.2.1

/-- The accepted carrier's prune is the canonical combined prune. -/
theorem accepted_prune_eq (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declared : AlignedAttacks argsRaw rawAtts)
    (hacc : evaluateAdmission canon table metas leaves argsRaw rawAtts groups declared =
      .accepted r) :
    r.prune = buildPrune canon table metas leaves argsRaw rawAtts groups declared.resolved := by
  cases hk : firstDuplicateKey table with
  | some k => simp [evaluateAdmission, hk] at hacc
  | none =>
      cases hl : firstDuplicateLeafId metas with
      | some l => simp [evaluateAdmission, hk, hl] at hacc
      | none =>
          by_cases ha : metadataLeafAligned metas leaves
          · cases hf : firstAdmissionRejection table metas with
            | some r' => simp [evaluateAdmission, hk, hl, ha, hf] at hacc
            | none =>
                simp [evaluateAdmission, hk, hl, ha, hf] at hacc
                rw [← hacc]
          · simp [evaluateAdmission, hk, hl, ha] at hacc

/-- Every accepted carrier preserves the validated raw/resolved attack
alignment; acceptance cannot be constructed from an independently supplied,
truncated, or same-length-unrelated semantic attack list. -/
theorem accepted_resolved_aligned (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declared : AlignedAttacks argsRaw rawAtts)
    (hacc : evaluateAdmission canon table metas leaves argsRaw rawAtts groups declared =
      .accepted r) :
    resolveAttacks argsRaw rawAtts = .ok r.declaredResolved := by
  cases hk : firstDuplicateKey table with
  | some k => simp [evaluateAdmission, hk] at hacc
  | none =>
      cases hl : firstDuplicateLeafId metas with
      | some l => simp [evaluateAdmission, hk, hl] at hacc
      | none =>
          by_cases ha : metadataLeafAligned metas leaves
          · cases hf : firstAdmissionRejection table metas with
            | some r' => simp [evaluateAdmission, hk, hl, ha, hf] at hacc
            | none =>
                simp [evaluateAdmission, hk, hl, ha, hf] at hacc
                rw [← hacc]
                exact declared.resolve_eq
          · simp [evaluateAdmission, hk, hl, ha] at hacc

private theorem checked_iff_policy_no_reject (canon : String → String)
    (table : List AdmissionRow) (metas : List LeafMeta)
    (leaves : List (LeafId × Atom)) (groups : List Groups.DupGroup)
    (ha : metadataLeafAligned metas leaves)
    (hdup : firstDuplicateLeafId metas = none)
    (hn : firstAdmissionRejection table metas = none) (l : LeafId) :
    l ∈ checkedAdmittedIds canon table metas leaves groups ↔
      l ∈ policyAdmittedIds table metas ∧
      l ∉ Groups.quarantined canon leaves groups := by
  have hnodup := (firstDuplicateLeafId_none_iff_nodup metas).mp hdup
  constructor
  · intro hchecked
    obtain ⟨e, he, hid, hnotPolicy, hnotGroup⟩ :=
      (checked_admitted_iff canon table metas leaves groups l).mp hchecked
    have hlLeaves : l ∈ leaves.map (·.1) :=
      List.mem_map.mpr ⟨e, he, hid⟩
    have hlMetas : l ∈ metas.map (·.id) := by
      rw [ha]
      exact hlLeaves
    obtain ⟨m, hm, hmid⟩ := List.mem_map.mp hlMetas
    have hnotReject := decision_ne_reject_of_first_none table metas hn m hm
    have hnotQuarantine : decisionFor table m.kind m.provenance ≠ .quarantine := by
      intro hq
      apply hnotPolicy
      apply (mem_policyQuarantineSeed_iff table metas l).mpr
      exact ⟨m, hm, hmid, hq⟩
    have hadmit : decisionFor table m.kind m.provenance = .admit := by
      cases hdec : decisionFor table m.kind m.provenance with
      | admit => rfl
      | quarantine => exact False.elim (hnotQuarantine hdec)
      | reject => exact False.elim (hnotReject hdec)
    refine ⟨(policy_admitted_iff table metas l).mpr ?_, hnotGroup⟩
    exact ⟨m, hm, hmid, hadmit⟩
  · rintro ⟨hpolicy, hnotGroup⟩
    obtain ⟨m, hm, hmid, hadmit⟩ :=
      (policy_admitted_iff table metas l).mp hpolicy
    have hlMetas : l ∈ metas.map (·.id) := List.mem_map.mpr ⟨m, hm, hmid⟩
    have hlLeaves : l ∈ leaves.map (·.1) := by
      rw [← ha]
      exact hlMetas
    obtain ⟨e, he, hid⟩ := List.mem_map.mp hlLeaves
    apply (checked_admitted_iff canon table metas leaves groups l).mpr
    refine ⟨e, he, hid, ?_, hnotGroup⟩
    intro hseed
    obtain ⟨m', hm', hmid', hquarantine⟩ :=
      (mem_policyQuarantineSeed_iff table metas l).mp hseed
    have hsame : m' = m :=
      nodup_ids_eq_of_mem hnodup hm' hm (hmid'.trans hmid.symm)
    subst m'
    rw [hadmit] at hquarantine
    cases hquarantine

/-- An accepted carrier's checker context is exactly `Gamma_policy` minus the
inconsistent-group seed, and it is the same leaf-id list passed to
`checkUnit`. -/
theorem accepted_checked_context_exact (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declared : AlignedAttacks argsRaw rawAtts)
    (hacc : evaluateAdmission canon table metas leaves argsRaw rawAtts groups declared =
      .accepted r) :
    metadataLeafAligned metas leaves ∧
      r.prune.checkedLeaves.map (·.1) =
        checkedAdmittedIds canon table metas leaves groups ∧
      ∀ l, l ∈ r.prune.checkedLeaves.map (·.1) ↔
        l ∈ policyAdmittedIds table metas ∧
        l ∉ Groups.quarantined canon leaves groups := by
  have hconditions := evaluateAdmission_accepted_conditions hacc
  have ha := hconditions.2.2.1
  have hdup := hconditions.2.1
  have hn := hconditions.2.2.2
  have hp :=
    accepted_prune_eq canon table metas leaves argsRaw rawAtts groups declared hacc
  refine ⟨ha, ?_, ?_⟩
  · rw [hp]
    exact (checked_admitted_ids_eq_prune canon table metas leaves argsRaw rawAtts groups
      declared.resolved).symm
  · intro l
    rw [hp]
    exact checked_iff_policy_no_reject canon table metas leaves groups ha hdup hn l

/-- **More restrictive policies cannot add structure.**  An
admit-to-quarantine tightening can only remove leaves, arguments, and
attacks from the checked source, and can only shrink `Gamma_policy`.  (Claim
*statuses* are deliberately non-monotonic — that is the hazard the
`Lara.Blocked` non-promotion theorem manages, so no monotonicity is claimed
here.) -/
theorem more_restrictive_cannot_add_structure (canon : String → String) {t1 t2 : List AdmissionRow}
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declared : AlignedAttacks argsRaw rawAtts)
    (hrestr : AtLeastAsRestrictive t1 t2)
    (hacc1 : evaluateAdmission canon t1 metas leaves argsRaw rawAtts groups declared = .accepted r1)
    (hacc2 : evaluateAdmission canon t2 metas leaves argsRaw rawAtts groups declared = .accepted r2) :
    (∀ a : String × SupportTerm, a ∈ r2.prune.keptArgs → a ∈ r1.prune.keptArgs) ∧
    (∀ ra : RawAttack, r2.prune.keepAttack ra = true → r1.prune.keepAttack ra = true) ∧
    (∀ att : Attack, att ∈ r2.prune.keptAttacks → att ∈ r1.prune.keptAttacks) ∧
    (∀ l : LeafId, l ∈ r2.prune.checkedLeaves.map (·.1) → l ∈ r1.prune.checkedLeaves.map (·.1)) ∧
    (∀ m : LeafMeta, m ∈ policyAdmitted t2 metas → m ∈ policyAdmitted t1 metas) := by
  have hp1 : r1.prune = buildPrune canon t1 metas leaves argsRaw rawAtts groups declared.resolved :=
    accepted_prune_eq canon t1 metas leaves argsRaw rawAtts groups declared hacc1
  have hp2 : r2.prune = buildPrune canon t2 metas leaves argsRaw rawAtts groups declared.resolved :=
    accepted_prune_eq canon t2 metas leaves argsRaw rawAtts groups declared hacc2
  have hseeds : ∀ l, l ∈ policyQuarantineSeed t1 metas ++ Groups.quarantined canon leaves groups →
      l ∈ policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups :=
    removedSeed_subset_of_restrictive hrestr canon metas leaves groups
  rw [hp1, hp2]
  have hargs_subset : ∀ a : String × SupportTerm,
      a ∈ argsRaw.filter (fun a => ! Groups.usesLeaf
        (policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups) a.2) →
      a ∈ argsRaw.filter (fun a => ! Groups.usesLeaf
        (policyQuarantineSeed t1 metas ++ Groups.quarantined canon leaves groups) a.2) := by
    intro a ha
    have hkeep2 : (! Groups.usesLeaf
        (policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups) a.2) = true :=
      (List.mem_filter.mp ha).2
    have huse2 : Groups.usesLeaf
        (policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups) a.2 = false := by
      simpa using hkeep2
    have huse1 : Groups.usesLeaf
        (policyQuarantineSeed t1 metas ++ Groups.quarantined canon leaves groups) a.2 = false := by
      cases h : Groups.usesLeaf
        (policyQuarantineSeed t1 metas ++ Groups.quarantined canon leaves groups) a.2 with
      | true =>
          have h2 : Groups.usesLeaf
              (policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups) a.2 = true :=
            Groups.usesLeaf_mono hseeds a.2 h
          rw [h2] at huse2
          cases huse2
      | false => rfl
    exact List.mem_filter.mpr ⟨(List.mem_filter.mp ha).1, by simp [huse1]⟩
  have hatts_subset : ∀ ra : RawAttack,
      (decide (ra.endpoints.1 ∈ (argsRaw.filter (fun a => ! Groups.usesLeaf
          (policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups) a.2)).map (·.1)) &&
        decide (ra.endpoints.2 ∈ (argsRaw.filter (fun a => ! Groups.usesLeaf
          (policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups) a.2)).map (·.1))) = true →
      (decide (ra.endpoints.1 ∈ (argsRaw.filter (fun a => ! Groups.usesLeaf
          (policyQuarantineSeed t1 metas ++ Groups.quarantined canon leaves groups) a.2)).map (·.1)) &&
        decide (ra.endpoints.2 ∈ (argsRaw.filter (fun a => ! Groups.usesLeaf
          (policyQuarantineSeed t1 metas ++ Groups.quarantined canon leaves groups) a.2)).map (·.1))) = true := by
    intro ra hk2
    have hk2' : decide (ra.endpoints.1 ∈
        (argsRaw.filter (fun a => ! Groups.usesLeaf
          (policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups) a.2)).map (·.1)) = true ∧
        decide (ra.endpoints.2 ∈
          (argsRaw.filter (fun a => ! Groups.usesLeaf
            (policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups) a.2)).map (·.1)) = true := by
      simpa using hk2
    have hs1 : ra.endpoints.1 ∈
        (argsRaw.filter (fun a => ! Groups.usesLeaf
          (policyQuarantineSeed t1 metas ++ Groups.quarantined canon leaves groups) a.2)).map (·.1) := by
      have hmem2 : ra.endpoints.1 ∈
          (argsRaw.filter (fun a => ! Groups.usesLeaf
            (policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups) a.2)).map (·.1) :=
        of_decide_eq_true hk2'.1
      obtain ⟨a, ha, hid⟩ := List.mem_map.mp hmem2
      exact List.mem_map.mpr ⟨a, hargs_subset a ha, hid⟩
    have ht1 : ra.endpoints.2 ∈
        (argsRaw.filter (fun a => ! Groups.usesLeaf
          (policyQuarantineSeed t1 metas ++ Groups.quarantined canon leaves groups) a.2)).map (·.1) := by
      have hmem2 : ra.endpoints.2 ∈
          (argsRaw.filter (fun a => ! Groups.usesLeaf
            (policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups) a.2)).map (·.1) :=
        of_decide_eq_true hk2'.2
      obtain ⟨a, ha, hid⟩ := List.mem_map.mp hmem2
      exact List.mem_map.mpr ⟨a, hargs_subset a ha, hid⟩
    simp [show decide (ra.endpoints.1 ∈
        (argsRaw.filter (fun a => ! Groups.usesLeaf
          (policyQuarantineSeed t1 metas ++ Groups.quarantined canon leaves groups) a.2)).map (·.1)) = true from
        decide_eq_true hs1,
      show decide (ra.endpoints.2 ∈
        (argsRaw.filter (fun a => ! Groups.usesLeaf
          (policyQuarantineSeed t1 metas ++ Groups.quarantined canon leaves groups) a.2)).map (·.1)) = true from
        decide_eq_true ht1]
  have hleaves_subset : ∀ l : LeafId,
      l ∈ (Groups.quarantineLeaves
        (policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups) leaves).map (·.1) →
      l ∈ (Groups.quarantineLeaves
        (policyQuarantineSeed t1 metas ++ Groups.quarantined canon leaves groups) leaves).map (·.1) := by
    intro l hl
    obtain ⟨e, he, hid⟩ := List.mem_map.mp hl
    have hef := List.mem_filter.mp he
    have hnot2 : e.1 ∉ policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups := by
      have hd : (! decide (e.1 ∈ policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups)) = true := hef.2
      have hf : decide (e.1 ∈ policyQuarantineSeed t2 metas ++ Groups.quarantined canon leaves groups) = false := by
        simpa using hd
      exact decide_eq_false_iff_not.mp hf
    have hnot1 : e.1 ∉ policyQuarantineSeed t1 metas ++ Groups.quarantined canon leaves groups := by
      intro hmem1
      exact hnot2 (hseeds e.1 hmem1)
    exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨hef.1, by
      rw [show decide (e.1 ∈ policyQuarantineSeed t1 metas ++ Groups.quarantined canon leaves groups) = false from
        decide_eq_false_iff_not.mpr hnot1]
      rfl⟩, hid⟩
  have hpol_subset : ∀ m : LeafMeta, m ∈ policyAdmitted t2 metas → m ∈ policyAdmitted t1 metas := by
    intro m hm
    have hmf := List.mem_filter.mp hm
    have hadmit2 : decisionFor t2 m.kind m.provenance = .admit := by
      simpa using (of_decide_eq_true hmf.2)
    have hadmit1 : decisionFor t1 m.kind m.provenance = .admit := by
      by_cases h1 : decisionFor t1 m.kind m.provenance = .admit
      · exact h1
      · have : decisionFor t2 m.kind m.provenance = decisionFor t1 m.kind m.provenance :=
          hrestr m.kind m.provenance h1
        rw [this] at hadmit2
        exact False.elim (h1 hadmit2)
    exact List.mem_filter.mpr ⟨hmf.1, by simp [hadmit1]⟩
  have hsemantic_atts_subset : ∀ att : Attack,
      att ∈ selectAligned
        (buildPrune canon t2 metas leaves argsRaw rawAtts groups declared.resolved).keepAttack
        rawAtts declared.resolved →
      att ∈ selectAligned
        (buildPrune canon t1 metas leaves argsRaw rawAtts groups declared.resolved).keepAttack
        rawAtts declared.resolved :=
    fun att hatt => selectAligned_mono hatts_subset rawAtts declared.resolved att hatt
  exact ⟨hargs_subset, hatts_subset, hsemantic_atts_subset, hleaves_subset, hpol_subset⟩

/-! ### Rejection carries no checked unit -/

/-- **An R8 outcome carries no checked unit and has no core-check branch.**
The rejection names the first rejected leaf, and no accepted carrier exists
for the same input. -/
theorem source_reject_no_checked_unit (canon : String → String) (table : List AdmissionRow)
    (metas : List LeafMeta) (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack)
    (groups : List Groups.DupGroup) (declared : AlignedAttacks argsRaw rawAtts)
    (h : evaluateAdmission canon table metas leaves argsRaw rawAtts groups declared = .rejected r) :
    firstAdmissionRejection table metas = some r ∧
      ∀ res : AdmissionResult,
        evaluateAdmission canon table metas leaves argsRaw rawAtts groups declared = .accepted res → False := by
  cases hk : firstDuplicateKey table with
  | some k => simp [evaluateAdmission, hk] at h
  | none =>
      cases hl : firstDuplicateLeafId metas with
      | some l => simp [evaluateAdmission, hk, hl] at h
      | none =>
          by_cases ha : metadataLeafAligned metas leaves
          · cases hf : firstAdmissionRejection table metas with
            | none => simp [evaluateAdmission, hk, hl, ha, hf] at h
            | some r' =>
                simp [evaluateAdmission, hk, hl, ha, hf] at h
                have heval : evaluateAdmission canon table metas leaves argsRaw rawAtts groups declared =
                    .rejected r' := by
                  simp [evaluateAdmission, hk, hl, ha, hf]
                refine ⟨?_, ?_⟩
                · simpa [h] using hf
                · intro res hacc
                  rw [heval] at hacc
                  cases hacc
          · simp [evaluateAdmission, hk, hl, ha] at h

/-! ### Source non-promotion -/
theorem retained_identity_of_length_eq
    (keep : (String × SupportTerm) → Bool)
    (declared : List (String × SupportTerm))
    (hlen : declared.length = (retainedArguments keep declared).length) :
    retainedArguments keep declared = declared ∧
      retainedIndices keep declared = List.range declared.length := by
  have hfilterLen : (declared.filter keep).length = declared.length := by
    rw [← retainedArguments_eq_filter]
    exact hlen.symm
  have hfilter : declared.filter keep = declared :=
    List.filter_sublist.eq_of_length hfilterLen
  have hkeep : ∀ a, a ∈ declared → keep a = true :=
    List.filter_eq_self.mp hfilter
  have hview : retainedView keep declared = declared.zipIdx := by
    unfold retainedView
    apply List.filter_eq_self.mpr
    intro entry hentry
    apply hkeep entry.1
    rw [← List.zipIdx_map_fst 0 declared]
    exact List.mem_map_of_mem hentry
  constructor
  · rw [retainedArguments_eq_filter, hfilter]
  · unfold retainedIndices
    rw [hview]
    rw [List.zipIdx_map_snd, List.range_eq_range']

theorem liftSupport_range_eq_of_mem {n : Nat} {support : List Nat}
    (hmem : ∀ i, i ∈ support → i < n) :
    liftSupport (List.range n) support = support := by
  induction support with
  | nil => rfl
  | cons head rest ih =>
      have hhead : head < n := hmem head (by simp)
      have hrest : ∀ i, i ∈ rest → i < n := by
        intro i hi
        exact hmem i (by simp [hi])
      unfold liftSupport
      rw [List.filterMap_cons, List.getElem?_range hhead]
      change head :: liftSupport (List.range n) rest = head :: rest
      rw [ih hrest]

theorem checkedAF_eq_declaredAF
    (P : CheckedProgram canon Pi Gamma CertOk dp)
    (argsRaw : List (String × SupportTerm)) (atts : List Attack)
    (hargs : P.args = argsRaw.map (·.2)) (hatts : P.atts = atts) :
    Compile.checkedAF P = BlockedProgram.declaredAF argsRaw atts := by
  have hlen : P.args.length = argsRaw.length := by
    rw [hargs, List.length_map]
  have hedge : Compile.edgeB P = BlockedProgram.edgeIn argsRaw atts := by
    funext i j
    simp only [Compile.edgeB, BlockedProgram.edgeIn, hargs, hatts,
      List.getElem?_map]
    cases hsi : argsRaw[i]? <;> cases htj : argsRaw[j]? <;> simp_all
  change ({ args := List.range P.args.length, attack := Compile.edgeB P } : Lara.Grounded.AF) =
    { args := List.range argsRaw.length, attack := BlockedProgram.edgeIn argsRaw atts }
  rw [hlen, hedge]



/-- **Source `justified` non-promotion.**  Compose admission with the exact
production blocking theorem: a query published `justified` by the checked
source result — with the admission prune's exact keep predicates, retained
arguments, and aligned attacks — remains `justified` in the declared
framework with the policy- and group-quarantined material reinstated.

The no-argument-prune fast path is discharged by identity: equal retained and
declared lengths force every argument and every endpoint-valid raw attack to
survive, so the checked and declared AFs coincide. -/
theorem source_justified_nonpromotion
    {canon : String → String}
    (reg : Lara.Support.BackendRegistry canon) (policy : Lara.Policy.Policy)
    (table : List AdmissionRow) (metas : List LeafMeta)
    (leaves : List (LeafId × Atom)) (argsRaw : List (String × SupportTerm))
    (rawAtts : List RawAttack) (groups : List Groups.DupGroup)
    (declared : AlignedAttacks argsRaw rawAtts)
    (queries : List Atom) (p : Atom)
    (sigma : Lara.Sigma.Sigma) (ground : List Atom)
    (hacc : evaluateAdmission canon table metas leaves argsRaw rawAtts groups declared = .accepted r)
    (accepted : Lara.Unit.CheckedUnit canon (buildGamma r.prune.checkedLeaves)
      (Lara.Support.certOkOf reg))
    (hcheck : Lara.Check.Unit.checkUnit (buildGamma r.prune.checkedLeaves) reg ground
      ({ sigma := sigma, policy := policy, args := r.prune.keptArgs.map (·.2), atts := r.prune.keptAttacks } : Lara.Unit) =
        .ok accepted)
    (hp : p ∈ queries)
    (hnot : p ∉ BlockedProgram.blockedQueries r.prune.keep argsRaw declared.resolved
      r.prune.keptAttacks (fun q => claimSupportFor accepted q) queries)
    (hstatus : Grounded.statusC (Compile.checkedAF accepted.program)
      (completeClaimFor accepted p) = .justified) :
    Grounded.statusC (BlockedProgram.declaredAF argsRaw declared.resolved)
      (BlockedProgram.liftClaim (retainedIndices r.prune.keep argsRaw) (completeClaimFor accepted p)) =
        .justified := by
  have hp_eq : r.prune =
      buildPrune canon table metas leaves argsRaw rawAtts groups declared.resolved :=
    accepted_prune_eq canon table metas leaves argsRaw rawAtts groups declared hacc
  have hkeep : r.prune.keptArgs = retainedArguments r.prune.keep argsRaw := by
    rw [hp_eq]
    rw [retainedArguments_eq_filter]
    rfl
  have hatts : r.prune.keptAttacks =
      selectAligned r.prune.keepAttack rawAtts declared.resolved := by
    rw [hp_eq]
    rfl
  by_cases hpruned : argsRaw.length = r.prune.keptArgs.length
  · have hretainedLen : argsRaw.length =
        (retainedArguments r.prune.keep argsRaw).length := by
      exact hpruned.trans (congrArg List.length hkeep)
    obtain ⟨hretained, hindices⟩ :=
      retained_identity_of_length_eq r.prune.keep argsRaw hretainedLen
    have hpruneArgs : r.prune.keptArgs = argsRaw := hkeep.trans hretained
    have hidsDef : r.prune.keptIds = r.prune.keptArgs.map (·.1) := by
      rw [hp_eq]
      rfl
    have hids : r.prune.keptIds = argsRaw.map (·.1) := by
      rw [hidsDef, hpruneArgs]
    have hkeepAttackDef : ∀ ra, r.prune.keepAttack ra =
        (decide (ra.endpoints.1 ∈ r.prune.keptIds) &&
          decide (ra.endpoints.2 ∈ r.prune.keptIds)) := by
      intro ra
      rw [hp_eq]
      rfl
    have hkeepRaw : ∀ ra, ra ∈ rawAtts → r.prune.keepAttack ra = true := by
      intro ra hra
      have hendpoints := resolveAttacks_endpoints_mem argsRaw declared.resolve_eq ra hra
      rw [hkeepAttackDef, hids]
      simp [hendpoints.1, hendpoints.2]
    have hrawFilter : rawAtts.filter r.prune.keepAttack = rawAtts :=
      List.filter_eq_self.mpr hkeepRaw
    have hselected : selectAligned r.prune.keepAttack rawAtts declared.resolved =
        declared.resolved := by
      have hcommute :=
        resolve_filter_commute argsRaw r.prune.keepAttack declared.resolve_eq
      rw [hrawFilter, declared.resolve_eq] at hcommute
      injection hcommute with heq
      exact heq.symm
    have hpruneAtts : r.prune.keptAttacks = declared.resolved :=
      hatts.trans hselected
    have hsound := Lara.Check.Unit.checkUnit_sound hcheck
    have hprogramArgs := hsound.args_eq
    have hprogramAtts := hsound.atts_eq
    rw [hpruneArgs] at hprogramArgs
    rw [hpruneAtts] at hprogramAtts
    have haf : Compile.checkedAF accepted.program =
        BlockedProgram.declaredAF argsRaw declared.resolved :=
      checkedAF_eq_declaredAF accepted.program argsRaw declared.resolved
        hprogramArgs hprogramAtts
    have hsupport : ∀ i, i ∈ (completeClaimFor accepted p).support →
        i < argsRaw.length := by
      intro i hi
      have hi' : i ∈ claimSupportFor accepted p := hi
      have himem := claimSupportFor_mem_checkedAF (accepted := accepted) i hi'
      have hlt := List.mem_range.mp himem
      rw [hprogramArgs, List.length_map] at hlt
      exact hlt
    have hlift :
        liftClaim (List.range argsRaw.length) (completeClaimFor accepted p) =
          completeClaimFor accepted p := by
      unfold liftClaim
      rw [liftSupport_range_eq_of_mem hsupport]
    rw [hindices, hlift, ← haf]
    exact hstatus
  · rw [hkeep] at hcheck hpruned
    rw [hatts] at hcheck hnot
    exact checked_production_justified_nonpromotion_of_not_blocked
      (RawAttack := Lara.RawAttack.RawAttack)
      reg policy accepted r.prune.keep argsRaw declared.resolved r.prune.keepAttack rawAtts queries p
      sigma ground hcheck hpruned hp hnot hstatus

end Lara.Admission
