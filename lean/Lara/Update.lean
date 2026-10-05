/-
Source-level updates for theory M3.

An update edits only raw source material.  Successful application always reruns
source admission and whole-unit checking; no checked carrier is retained across
an edit.
-/
import Lara.Admission
import Lara.Consistency
import Lara.Semantics
import Lara.Update.Discharge

namespace Lara.Update

open Lara Lara.Support
open Lara.Presentation (LeafKind Provenance Admission)

/-- Raw source material from which admission and unit acceptance are derived.
A `SourceState` deliberately contains no `CheckedUnit`: edits must be checked
against the material they actually produce. -/
structure SourceState where
  sigma    : Sigma.Sigma
  policy   : Policy.Policy
  table    : List Admission.AdmissionRow
  metas    : List Admission.LeafMeta
  leaves   : List (LeafId × Atom)
  argsRaw  : List (String × SupportTerm)
  rawAtts  : List RawAttack.RawAttack
  groups   : List Groups.DupGroup
  ground   : List Atom

/-- Run source admission on exactly the raw carriers in `σ`. -/
private def admissionFor (canon : String → String) (σ : SourceState)
    (declared : Admission.AlignedAttacks σ.argsRaw σ.rawAtts) :
    Admission.SourceAdmission :=
  Admission.evaluateAdmission canon σ.table σ.metas σ.leaves
    σ.argsRaw σ.rawAtts σ.groups declared

/-- The checker context derived by admission. -/
private def checkedGamma (result : Admission.AdmissionResult) : LeafId → Option Atom :=
  Admission.buildGamma result.prune.checkedLeaves

/-- The exact pruned unit passed from admission to `checkUnit`. -/
private def prunedUnit (σ : SourceState) (result : Admission.AdmissionResult) : Lara.Unit :=
  { sigma := σ.sigma
  , policy := σ.policy
  , args := result.prune.keptArgs.map (·.2)
  , atts := result.prune.keptAttacks }

/-- Run whole-unit checking on the exact context and unit derived by admission. -/
private def checkAccepted {canon : String → String} (reg : BackendRegistry canon)
    (σ : SourceState) (result : Admission.AdmissionResult) :
    Except Check.Unit.UnitError
      (Lara.Unit.CheckedUnit canon (checkedGamma result) (certOkOf reg)) :=
  Check.Unit.checkUnit (checkedGamma result) reg σ.ground (prunedUnit σ result)

/-- Acceptance of the current raw state, witnessed by the exact admission
carrier and proof-bearing checked unit returned by the executable pipeline. -/
def Accepted {canon : String → String} (reg : BackendRegistry canon)
    (σ : SourceState) : Prop :=
  ∃ (declared : Admission.AlignedAttacks σ.argsRaw σ.rawAtts)
    (admission : Admission.AdmissionResult)
    (checked : Lara.Unit.CheckedUnit canon (checkedGamma admission) (certOkOf reg)),
    admissionFor canon σ declared = .accepted admission ∧
    checkAccepted reg σ admission = .ok checked

/-- One exact successful source admission/checker run.  Unlike `Accepted`, this
proof-relevant carrier keeps the declared attacks, canonical prune, and checked
unit available to transition theorems. -/
structure AcceptedRun {canon : String → String} (reg : BackendRegistry canon)
    (state : SourceState) where
  declared : Admission.AlignedAttacks state.argsRaw state.rawAtts
  admission : Admission.AdmissionResult
  checked : Lara.Unit.CheckedUnit canon
    (Admission.buildGamma admission.prune.checkedLeaves) (certOkOf reg)
  admission_ok :
    Admission.evaluateAdmission canon state.table state.metas state.leaves
      state.argsRaw state.rawAtts state.groups declared = .accepted admission
  check_ok :
    Check.Unit.checkUnit
      (Admission.buildGamma admission.prune.checkedLeaves) reg state.ground
      { sigma := state.sigma
      , policy := state.policy
      , args := admission.prune.keptArgs.map (·.2)
      , atts := admission.prune.keptAttacks } = .ok checked

/-- An exact successful run supplies the existential acceptance predicate. -/
theorem AcceptedRun.accepted (run : AcceptedRun reg state) :
    Accepted reg state :=
  ⟨run.declared, run.admission, run.checked, run.admission_ok, run.check_ok⟩

/-- Closed diagnostics for update application.  No free-form string crosses
this symbolic boundary. -/
inductive UpdateRejection where
  | leafNotFresh : LeafId → UpdateRejection
  | keyNotAdmitted : LeafKind × Provenance → UpdateRejection
  | endpointNotDeclared : RawAttack.RawAttack → UpdateRejection
  | instanceNotFresh : String → SupportTerm → UpdateRejection
  | notDischargeable : String → Attack.Pos → QuestionId → UpdateRejection
  | batchEdit : Nat → UpdateRejection → UpdateRejection
  | argumentIdsNotUnique
  | attackResolutionFailed
  | sourceInvalid : Admission.SourceInvalid → UpdateRejection
  | sourceRejected : Admission.AdmissionRejection → UpdateRejection
  | unitRejected : Check.Unit.UnitError → UpdateRejection
deriving DecidableEq

/-- One raw edit of an atomic batch (D14).  The vocabulary is the additive
constructors plus in-place discharge: an atomic batch completes a gap, so it
carries no `tighten`.  It is a separate type, not a nested `SourceUpdate`, so a
batch cannot contain a batch. -/
inductive AtomicEdit where
  | addLeaf       (id : LeafId) (a : Atom) (m : Admission.LeafMeta)
  | addInstance   (name : String) (w : SupportTerm)
  | addAttack     (k : RawAttack.RawAttack)
  | dischargeOpen (name : String) (π : Attack.Pos) (q : QuestionId) (v : SupportTerm)

/-- A source edit that may preserve acceptance after the full pipeline is
rerun.  An admit-to-reject constructor is deliberately absent:
`Admission.source_reject_no_checked_unit` proves that source rejection has no
checked-unit target.

`addInstance` and `dischargeOpen` are the deliberate wire-carrier exception:
their `name : String` mirrors the pre-parse `argsRaw` representation rather
than introducing a second identifier type. -/
inductive SourceUpdate where
  | addLeaf     (id : LeafId) (a : Atom) (m : Admission.LeafMeta)
  | tighten     (key : LeafKind × Provenance)
  | addAttack   (k : RawAttack.RawAttack)
  | addInstance (name : String) (w : SupportTerm)
  /-- Answer the open question `q` of the rule occurrence at `π` inside the
  declared argument `name`, with the discharge `v` (D13). -/
  | dischargeOpen (name : String) (π : Attack.Pos) (q : QuestionId) (v : SupportTerm)
  /-- Apply a batch of raw edits, then admit and check once (D14). -/
  | atomic      (edits : List AtomicEdit)

/-! ### Constructor side conditions -/

/-- A new leaf id is absent from both declaration carriers and from every
pre-existing duplicate-group member list. -/
def AddLeafFresh (σ : SourceState) (id : LeafId) : Prop :=
  (∀ e ∈ σ.leaves, e.1 ≠ id) ∧
  (∀ m ∈ σ.metas, m.id ≠ id) ∧
  ∀ g ∈ σ.groups, ∀ member ∈ g.members, member ≠ id

/-- Executable decider for `AddLeafFresh`. -/
def addLeafFreshB (σ : SourceState) (id : LeafId) : Bool :=
  !σ.leaves.any (fun e => decide (e.1 = id)) &&
    (!σ.metas.any (fun m => decide (m.id = id)) &&
      σ.groups.all (fun g => !g.members.any (fun member => decide (member = id))))

/-- `addLeafFreshB` decides freshness in all three leaf-id carriers. -/
theorem addLeafFreshB_iff (σ : SourceState) (id : LeafId) :
    addLeafFreshB σ id = true ↔ AddLeafFresh σ id := by
  simp [addLeafFreshB, AddLeafFresh, List.all_eq_true]

/-- The admission decision at a table key is currently `admit` (including the
default for an omitted key). -/
def AdmittedAt (σ : SourceState) (key : LeafKind × Provenance) : Prop :=
  Admission.decisionFor σ.table key.1 key.2 = .admit

/-- Executable decider for the `tighten` precondition. -/
def admittedAtB (σ : SourceState) (key : LeafKind × Provenance) : Bool :=
  decide (Admission.decisionFor σ.table key.1 key.2 = .admit)

/-- `admittedAtB` decides the exact admission-table precondition. -/
theorem admittedAtB_iff (σ : SourceState) (key : LeafKind × Provenance) :
    admittedAtB σ key = true ↔ AdmittedAt σ key := by
  simp [admittedAtB, AdmittedAt]

/-- Both raw endpoints of a proposed attack name declared arguments. -/
def EndpointDeclared (σ : SourceState) (k : RawAttack.RawAttack) : Prop :=
  let endpoints := k.endpoints
  endpoints.1 ∈ σ.argsRaw.map (·.1) ∧ endpoints.2 ∈ σ.argsRaw.map (·.1)

/-- Executable decider for raw attack endpoint declaration. -/
def endpointDeclaredB (σ : SourceState) (k : RawAttack.RawAttack) : Bool :=
  let endpoints := k.endpoints
  σ.argsRaw.any (fun a => decide (a.1 = endpoints.1)) &&
  σ.argsRaw.any (fun a => decide (a.1 = endpoints.2))

/-- `endpointDeclaredB` decides declaration of both raw endpoints. -/
theorem endpointDeclaredB_iff (σ : SourceState) (k : RawAttack.RawAttack) :
    endpointDeclaredB σ k = true ↔ EndpointDeclared σ k := by
  simp [endpointDeclaredB, EndpointDeclared]

/-- A proposed argument row is fresh in both the pre-parse name carrier and
the semantic support-term carrier. -/
def InstanceFresh (σ : SourceState) (name : String) (w : SupportTerm) : Prop :=
  (∀ a ∈ σ.argsRaw, a.1 ≠ name) ∧
  ∀ a ∈ σ.argsRaw, a.2 ≠ w

/-- Executable decider for argument name-and-term freshness. -/
def instanceFreshB (σ : SourceState) (name : String) (w : SupportTerm) : Bool :=
  !σ.argsRaw.any (fun a => decide (a.1 = name)) &&
  !σ.argsRaw.any (fun a => decide (a.2 = w))

/-- `instanceFreshB` decides both components of argument freshness. -/
theorem instanceFreshB_iff (σ : SourceState) (name : String) (w : SupportTerm) :
    instanceFreshB σ name w = true ↔ InstanceFresh σ name w := by
  simp [instanceFreshB, InstanceFresh]

/-- The `dischargeOpen` site precondition: the declared argument `name` exists
and its occurrence at `π` is a rule instance whose open set contains `q`.
The argument is the row raw endpoint resolution reads (`RawAttack.lookupArg`). -/
def DischargeOpen (σ : SourceState) (name : String) (π : Attack.Pos)
    (q : QuestionId) : Prop :=
  ∃ w, RawAttack.lookupArg σ.argsRaw name = some w ∧ Discharge.OpenAt w π q

/-- Executable decider for `DischargeOpen`. -/
def dischargeOpenB (σ : SourceState) (name : String) (π : Attack.Pos)
    (q : QuestionId) : Bool :=
  match RawAttack.lookupArg σ.argsRaw name with
  | some w => Discharge.openAtB w π q
  | none => false

/-- `dischargeOpenB` decides the exact discharge-site precondition. -/
theorem dischargeOpenB_iff (σ : SourceState) (name : String) (π : Attack.Pos)
    (q : QuestionId) :
    dischargeOpenB σ name π q = true ↔ DischargeOpen σ name π q := by
  unfold dischargeOpenB DischargeOpen
  cases h : RawAttack.lookupArg σ.argsRaw name with
  | none => simp
  | some w =>
      simp only [Option.some.injEq, exists_eq_left']
      exact Discharge.openAtB_iff w π q

/-- Rewrite the raw argument rows named `name` in place: each keeps its name
and its position, and its term is discharged at `π`.  Raw names are unique on
every source that reaches admission, so exactly one row changes there. -/
def dischargeRows (argsRaw : List (String × SupportTerm)) (name : String)
    (π : Attack.Pos) (q : QuestionId) (v : SupportTerm) :
    List (String × SupportTerm) :=
  argsRaw.map fun row =>
    if row.1 = name then (row.1, (Discharge.dischargeAt q v π row.2).getD row.2)
    else row

/-! ### Editing and executable revalidation -/

/-- Apply one raw edit of a batch, checking its syntactic side condition
against the state the earlier edits of the batch produced.  No admission or
checking happens here. -/
def AtomicEdit.applyRaw (σ : SourceState) : AtomicEdit → Except UpdateRejection SourceState
  | .addLeaf id a m =>
      if addLeafFreshB σ id then
        .ok { σ with metas := σ.metas ++ [{ m with id := id }]
                     leaves := σ.leaves ++ [(id, a)] }
      else .error (.leafNotFresh id)
  | .addInstance name w =>
      if instanceFreshB σ name w then
        .ok { σ with argsRaw := σ.argsRaw ++ [(name, w)] }
      else .error (.instanceNotFresh name w)
  | .addAttack k =>
      if endpointDeclaredB σ k then
        .ok { σ with rawAtts := σ.rawAtts ++ [k] }
      else .error (.endpointNotDeclared k)
  | .dischargeOpen name π q v =>
      if dischargeOpenB σ name π q then
        .ok { σ with argsRaw := dischargeRows σ.argsRaw name π q v }
      else .error (.notDischargeable name π q)

/-- Apply a batch's raw edits in order, numbering them from `index`.  The first
failing edit rejects the whole batch, tagged with its position. -/
def applyBatchFrom (σ : SourceState) (index : Nat) :
    List AtomicEdit → Except UpdateRejection SourceState
  | [] => .ok σ
  | e :: es =>
      match e.applyRaw σ with
      | .error reason => .error (.batchEdit index reason)
      | .ok σ' => applyBatchFrom σ' (index + 1) es

/-- The raw final state of a batch, or the first edit rejection. -/
def applyBatch (σ : SourceState) (edits : List AtomicEdit) :
    Except UpdateRejection SourceState :=
  applyBatchFrom σ 0 edits

/-- Change an existing key to quarantine, or append an explicit quarantine row
when the key was previously admitted by the default. -/
private def tightenTable (table : List Admission.AdmissionRow)
    (key : LeafKind × Provenance) : List Admission.AdmissionRow :=
  if table.any (fun row => decide (row.key = key)) then
    table.map (fun row =>
      if row.key = key then { row with decision := .quarantine } else row)
  else
    table ++ [{ key := key, decision := .quarantine }]

/-- Run admission and whole-unit checking on one already-edited raw state. -/
private def acceptEdited {canon : String → String} (reg : BackendRegistry canon)
    (σ : SourceState) : Except UpdateRejection SourceState :=
  if hids : (σ.argsRaw.map (·.1)).Nodup then
    match hresolve : RawAttack.resolveAttacks σ.argsRaw σ.rawAtts with
    | .error _ => .error .attackResolutionFailed
    | .ok resolved =>
        let declared : Admission.AlignedAttacks σ.argsRaw σ.rawAtts :=
          { resolved := resolved
          , resolve_eq := hresolve
          , ids_nodup := hids }
        match admissionFor canon σ declared with
        | .invalid reason => .error (.sourceInvalid reason)
        | .rejected reason => .error (.sourceRejected reason)
        | .accepted result =>
            match checkAccepted reg σ result with
            | .error reason => .error (.unitRejected reason)
            | .ok _ => .ok σ
  else
    .error .argumentIdsNotUnique

/-- Apply one raw source edit.  Constructor-specific syntactic conditions are
checked first; the edited source is returned only after real admission and
`checkUnit` acceptance.  No acceptance witness is asserted or carried by the
edit itself. -/
def applyUpdate {canon : String → String} (reg : BackendRegistry canon)
    (σ : SourceState) (u : SourceUpdate) : Except UpdateRejection SourceState :=
  match u with
  | .addLeaf id a m =>
      if addLeafFreshB σ id then
        acceptEdited reg
          { σ with metas := σ.metas ++ [{ m with id := id }]
                   leaves := σ.leaves ++ [(id, a)] }
      else
        .error (.leafNotFresh id)
  | .tighten key =>
      if admittedAtB σ key then
        acceptEdited reg { σ with table := tightenTable σ.table key }
      else
        .error (.keyNotAdmitted key)
  | .addAttack k =>
      if endpointDeclaredB σ k then
        acceptEdited reg { σ with rawAtts := σ.rawAtts ++ [k] }
      else
        .error (.endpointNotDeclared k)
  | .addInstance name w =>
      if instanceFreshB σ name w then
        acceptEdited reg { σ with argsRaw := σ.argsRaw ++ [(name, w)] }
      else
        .error (.instanceNotFresh name w)
  | .dischargeOpen name π q v =>
      if dischargeOpenB σ name π q then
        acceptEdited reg
          { σ with argsRaw := dischargeRows σ.argsRaw name π q v }
      else
        .error (.notDischargeable name π q)
  | .atomic edits =>
      match applyBatch σ edits with
      | .error reason => .error reason
      | .ok edited => acceptEdited reg edited

/-- A failed leaf-freshness check selects the constructor-specific rejection. -/
theorem applyUpdate_addLeaf_notFresh {canon : String → String}
    (reg : BackendRegistry canon) (σ : SourceState)
    (id : LeafId) (a : Atom) (m : Admission.LeafMeta)
    (h : addLeafFreshB σ id = false) :
    applyUpdate reg σ (.addLeaf id a m) = .error (.leafNotFresh id) := by
  simp [applyUpdate, h]

/-- A failed admitted-key check selects the constructor-specific rejection. -/
theorem applyUpdate_tighten_notAdmitted {canon : String → String}
    (reg : BackendRegistry canon) (σ : SourceState)
    (key : LeafKind × Provenance)
    (h : admittedAtB σ key = false) :
    applyUpdate reg σ (.tighten key) = .error (.keyNotAdmitted key) := by
  simp [applyUpdate, h]

/-- A failed endpoint check selects the constructor-specific rejection. -/
theorem applyUpdate_addAttack_endpointNotDeclared {canon : String → String}
    (reg : BackendRegistry canon) (σ : SourceState)
    (raw : RawAttack.RawAttack)
    (h : endpointDeclaredB σ raw = false) :
    applyUpdate reg σ (.addAttack raw) = .error (.endpointNotDeclared raw) := by
  simp [applyUpdate, h]

/-- A failed instance-freshness check selects the constructor rejection. -/
theorem applyUpdate_addInstance_notFresh {canon : String → String}
    (reg : BackendRegistry canon) (σ : SourceState)
    (name : String) (w : SupportTerm)
    (h : instanceFreshB σ name w = false) :
    applyUpdate reg σ (.addInstance name w) = .error (.instanceNotFresh name w) := by
  simp [applyUpdate, h]

/-- A failed discharge-site check selects the constructor rejection. -/
theorem applyUpdate_dischargeOpen_notDischargeable {canon : String → String}
    (reg : BackendRegistry canon) (σ : SourceState)
    (name : String) (π : Attack.Pos) (q : QuestionId) (v : SupportTerm)
    (h : dischargeOpenB σ name π q = false) :
    applyUpdate reg σ (.dischargeOpen name π q v) =
      .error (.notDischargeable name π q) := by
  simp [applyUpdate, h]

/-- A batch whose raw edits fail is rejected with the first edit failure,
before admission runs. -/
theorem applyUpdate_atomic_batchRejected {canon : String → String}
    (reg : BackendRegistry canon) (σ : SourceState) (edits : List AtomicEdit)
    {reason : UpdateRejection} (h : applyBatch σ edits = .error reason) :
    applyUpdate reg σ (.atomic edits) = .error reason := by
  simp [applyUpdate, h]


/-! ### Sufficient-condition preservation

The Γ-weakening lemmas this section rests on — `Support.hasSupport_mono_gamma`,
`Attack.hasAttack_mono_gamma` — and the `Admission.buildGamma_*` facts live at
their owning modules. -/

private theorem mem_leavesList_of_mem {child : SupportTerm}
    {children : List SupportTerm} (hchild : child ∈ children)
    {l : LeafId} (hl : l ∈ Support.leaves child) :
    l ∈ Support.leavesList children := by
  induction children with
  | nil => simp at hchild
  | cons head tail ih =>
      rcases List.mem_cons.mp hchild with rfl | htail
      · simp [Support.leavesList, hl]
      · simp [Support.leavesList, ih htail]

private theorem mem_leavesDis_of_mem {q : QuestionId} {child : SupportTerm}
    {discharges : List (QuestionId × SupportTerm)}
    (hchild : (q, child) ∈ discharges)
    {l : LeafId} (hl : l ∈ Support.leaves child) :
    l ∈ Support.leavesDis discharges := by
  induction discharges with
  | nil => simp at hchild
  | cons head tail ih =>
      rcases List.mem_cons.mp hchild with hhead | htail
      · subst head
        simp [Support.leavesDis, hl]
      · simp [Support.leavesDis, ih htail]

private theorem firstAdmissionRejection_append_none
    (table : List Admission.AdmissionRow)
    (metas : List Admission.LeafMeta) (m : Admission.LeafMeta)
    (hold : Admission.firstAdmissionRejection table metas = none)
    (hnew : Admission.decisionFor table m.kind m.provenance ≠ .reject) :
    Admission.firstAdmissionRejection table (metas ++ [m]) = none := by
  induction metas with
  | nil =>
      simp [Admission.firstAdmissionRejection,
        Admission.firstAdmissionRejection.go, hnew]
  | cons head tail ih =>
      by_cases hhead :
          Admission.decisionFor table head.kind head.provenance = .reject
      · simp [Admission.firstAdmissionRejection,
          Admission.firstAdmissionRejection.go, hhead] at hold
      · have htail :
            Admission.firstAdmissionRejection table tail = none := by
          simpa [Admission.firstAdmissionRejection,
            Admission.firstAdmissionRejection.go, hhead] using hold
        simpa [Admission.firstAdmissionRejection,
          Admission.firstAdmissionRejection.go, hhead] using ih htail

private theorem leafProp_append_ne (leaves : List (LeafId × Atom))
    {fresh member : LeafId} (a : Atom) (hne : member ≠ fresh) :
    Groups.leafProp (leaves ++ [(fresh, a)]) member =
    Groups.leafProp leaves member := by
  simp [Groups.leafProp, Ne.symm hne]

private theorem memberProps_append_fresh (leaves : List (LeafId × Atom))
    (fresh : LeafId) (a : Atom) (g : Groups.DupGroup)
    (hfresh : ∀ member ∈ g.members, member ≠ fresh) :
    Groups.memberProps (leaves ++ [(fresh, a)]) g =
      Groups.memberProps leaves g := by
  unfold Groups.memberProps
  have go : ∀ members : List LeafId,
      (∀ member ∈ members, member ≠ fresh) →
      List.mapM (Groups.leafProp (leaves ++ [(fresh, a)])) members =
        List.mapM (Groups.leafProp leaves) members := by
    intro members
    induction members with
    | nil => intro _; rfl
    | cons member rest ih =>
        intro hmembers
        simp only [List.mapM_cons]
        rw [leafProp_append_ne leaves a (hmembers member (by simp))]
        rw [ih (by
          intro x hx
          exact hmembers x (by simp [hx]))]
  exact go g.members hfresh

private theorem quarantined_append_fresh (canon : String → String)
    (leaves : List (LeafId × Atom)) (fresh : LeafId) (a : Atom)
    (groups : List Groups.DupGroup)
    (hfresh : ∀ g ∈ groups, ∀ member ∈ g.members, member ≠ fresh) :
    Groups.quarantined canon (leaves ++ [(fresh, a)]) groups =
      Groups.quarantined canon leaves groups := by
  unfold Groups.quarantined
  congr 1
  apply List.filter_congr
  intro g hg

  unfold Groups.consistentB
  rw [memberProps_append_fresh leaves fresh a g (hfresh g hg)]

/-- A term uses a listed leaf exactly when one of its leaves is listed. -/
theorem usesLeaf_true_iff (qs : List LeafId) (w : SupportTerm) :
    Groups.usesLeaf qs w = true ↔
      ∃ l, l ∈ Support.leaves w ∧ l ∈ qs := by
  revert qs
  refine SupportTerm.rec
    (motive_1 := fun w => ∀ qs, Groups.usesLeaf qs w = true ↔
      ∃ l, l ∈ Support.leaves w ∧ l ∈ qs)
    (motive_2 := fun ws => ∀ qs, Groups.usesLeafList qs ws = true ↔
      ∃ l, l ∈ Support.leavesList ws ∧ l ∈ qs)
    (motive_3 := fun ds => ∀ qs, Groups.usesLeafDisch qs ds = true ↔
      ∃ l, l ∈ Support.leavesDis ds ∧ l ∈ qs)
    (motive_4 := fun p => ∀ qs, Groups.usesLeaf qs p.2 = true ↔
      ∃ l, l ∈ Support.leaves p.2 ∧ l ∈ qs)
    ?leaf ?inst ?nilL ?consL ?nilD ?consD ?pair w
  case leaf =>
    intro l qs
    simp [Groups.usesLeaf, Support.leaves]
  case inst =>
    intro rn theta premises discharges holes assurance ihPremises
      ihDischarges qs
    simp only [Groups.usesLeaf, Bool.or_eq_true, Support.leaves,
      List.mem_append]
    rw [ihPremises qs, ihDischarges qs]
    constructor
    · rintro (⟨l, hl, hq⟩ | ⟨l, hl, hq⟩)
      · exact ⟨l, Or.inl hl, hq⟩
      · exact ⟨l, Or.inr hl, hq⟩
    · rintro ⟨l, hl | hl, hq⟩
      · exact Or.inl ⟨l, hl, hq⟩
      · exact Or.inr ⟨l, hl, hq⟩
  case nilL =>
    intro qs
    simp [Groups.usesLeafList, Support.leavesList]
  case consL =>
    intro head tail ihHead ihTail qs
    simp only [Groups.usesLeafList, Bool.or_eq_true, Support.leavesList,
      List.mem_append]
    rw [ihHead qs, ihTail qs]
    constructor
    · rintro (⟨l, hl, hq⟩ | ⟨l, hl, hq⟩)
      · exact ⟨l, Or.inl hl, hq⟩
      · exact ⟨l, Or.inr hl, hq⟩
    · rintro ⟨l, hl | hl, hq⟩
      · exact Or.inl ⟨l, hl, hq⟩
      · exact Or.inr ⟨l, hl, hq⟩
  case nilD =>
    intro qs
    simp [Groups.usesLeafDisch, Support.leavesDis]
  case consD =>
    intro head tail ihHead ihTail qs
    simp only [Groups.usesLeafDisch, Bool.or_eq_true, Support.leavesDis,
      List.mem_append]
    rw [ihHead qs, ihTail qs]
    constructor
    · rintro (⟨l, hl, hq⟩ | ⟨l, hl, hq⟩)
      · exact ⟨l, Or.inl hl, hq⟩
      · exact ⟨l, Or.inr hl, hq⟩
    · rintro ⟨l, hl | hl, hq⟩
      · exact Or.inl ⟨l, hl, hq⟩
      · exact Or.inr ⟨l, hl, hq⟩
  case pair =>
    intro q child ih qs
    exact ih qs



private theorem termsWellSorted_append_singleton
    (sg : Sigma.Sigma) (policy : Policy.Policy)
    (terms : List SupportTerm) (w : SupportTerm)
    (hold : Lara.termsWellSorted sg policy terms = true)
    (hnew : Lara.termWellSorted sg policy w = true) :
    Lara.termsWellSorted sg policy (terms ++ [w]) = true := by
  induction terms with
  | nil => simpa [Lara.termsWellSorted] using hnew
  | cons head rest ih =>
      have hparts :
          Lara.termWellSorted sg policy head = true ∧
            Lara.termsWellSorted sg policy rest = true := by
        simpa [Lara.termsWellSorted] using hold
      simp [Lara.termsWellSorted, hparts.1, ih hparts.2]

private theorem hasSupport_not_uses_prune_seed {canon : String → String}
    {Pi : RuleId → Option Rule}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (table : List Admission.AdmissionRow) (metas : List Admission.LeafMeta)
    (leaves : List (LeafId × Atom))
    (argsRaw : List (String × SupportTerm)) (rawAtts : List RawAttack.RawAttack)
    (groups : List Groups.DupGroup) (resolved : List Attack.Attack)
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi
      (Admission.buildGamma
        (Admission.buildPrune canon table metas leaves argsRaw rawAtts groups
          resolved).checkedLeaves)

      CertOk w C O) :
    Groups.usesLeaf
      (Admission.policyQuarantineSeed table metas ++
        Groups.quarantined canon leaves groups) w = false := by
  cases huses : Groups.usesLeaf
      (Admission.policyQuarantineSeed table metas ++
        Groups.quarantined canon leaves groups) w with
  | false => rfl
  | true =>
      obtain ⟨l, hl, hremoved⟩ :=
        (usesLeaf_true_iff
          (Admission.policyQuarantineSeed table metas ++
            Groups.quarantined canon leaves groups) w).mp huses
      obtain ⟨p, hgamma⟩ := Support.leaves_declared h l hl
      have hchecked :
          l ∈ Admission.checkedAdmittedIds canon table metas leaves groups := by
        have := Admission.buildGamma_some_mem hgamma
        simpa [Admission.buildPrune, Admission.checkedAdmittedIds] using this
      obtain ⟨_, _, _, hnotPolicy, hnotGroup⟩ :=
        (Admission.checked_admitted_iff canon table metas leaves groups l).mp
          hchecked
      rcases List.mem_append.mp hremoved with hpolicy | hgroup
      · exact False.elim (hnotPolicy hpolicy)
      · exact False.elim (hnotGroup hgroup)
private theorem lookupDis_some_pair_mem {discharges : List (QuestionId × SupportTerm)}
    {q : QuestionId} {w : SupportTerm}
    (h : Attack.lookupDis discharges q = some w) :
    (q, w) ∈ discharges := by
  induction discharges with
  | nil => simp [Attack.lookupDis] at h
  | cons head rest ih =>
      by_cases heq : head.1 = q
      · simp [Attack.lookupDis, heq] at h
        exact List.mem_cons.mpr (Or.inl (by
          apply Prod.ext
          · exact heq.symm
          · exact h.symm))
      · simp [Attack.lookupDis, heq] at h
        exact List.mem_cons.mpr (Or.inr (ih h))

private theorem leaf_mem_leaves_of_subterm_leaf {u : SupportTerm}
    {pos : Attack.Pos} {l : LeafId}
    (h : Attack.subterm u pos = some (.leaf l)) :
    l ∈ Support.leaves u := by
  induction pos generalizing u with
  | nil =>
      simp [Attack.subterm] at h
      subst u
      simp [Support.leaves]
  | cons step rest ih =>
      cases u with
      | leaf old =>
          simp [Attack.subterm] at h
      | inst rule subst premises discharges holes assurance =>
          cases step with
          | prem index =>
              cases hchild : premises[index]? with
              | none => simp [Attack.subterm, hchild] at h
              | some child =>
                  have hl := ih (by simpa [Attack.subterm, hchild] using h)
                  simp only [Support.leaves, List.mem_append]
                  exact Or.inl
                    (mem_leavesList_of_mem (List.mem_of_getElem? hchild) hl)
          | ques q =>
              cases hchild : Attack.lookupDis discharges q with
              | none => simp [Attack.subterm, hchild] at h
              | some child =>
                  have hl := ih (by simpa [Attack.subterm, hchild] using h)
                  simp only [Support.leaves, List.mem_append]
                  exact Or.inr
                    (mem_leavesDis_of_mem (lookupDis_some_pair_mem hchild) hl)

private theorem hasAttack_congr_gamma_on_endpoints {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma Gamma' : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {dp : Attack.DefeatPolicy} {k : Attack.Attack}
    (h : Attack.HasAttack canon Pi Gamma CertOk dp k)
    (hsource : ∀ l, l ∈ Support.leaves k.source → Gamma l = Gamma' l)
    (htarget : ∀ l, l ∈ Support.leaves k.target → Gamma l = Gamma' l) :
    Attack.HasAttack canon Pi Gamma' CertOk dp k := by
  cases h with
  | rebut hw hrule hdef hconcl hcon =>
      exact .rebut (hasSupport_congr_gamma_on hw hsource)
        hrule hdef hconcl hcon
  | undercut hw hocc hrule hdef hexc hinst heq =>
      exact .undercut (hasSupport_congr_gamma_on hw hsource)
        hocc hrule hdef hexc hinst heq
  | undermine hw hocc hGamma hcon =>
      exact .undermine (hasSupport_congr_gamma_on hw hsource) hocc
        (by rw [← htarget _ (leaf_mem_leaves_of_subterm_leaf hocc)]
            exact hGamma)
        hcon

private theorem termWellSorted_of_mem {sg : Sigma.Sigma}
    {policy : Policy.Policy} {terms : List SupportTerm}
    (h : Lara.termsWellSorted sg policy terms = true)
    {w : SupportTerm} (hw : w ∈ terms) :
    Lara.termWellSorted sg policy w = true := by
  induction terms with
  | nil => simp at hw
  | cons head rest ih =>
      have hparts :
          Lara.termWellSorted sg policy head = true ∧
            Lara.termsWellSorted sg policy rest = true := by
        simpa [Lara.termsWellSorted] using h
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hparts.1
      · exact ih hparts.2 hw

private theorem termsWellSorted_of_subset {sg : Sigma.Sigma}
    {policy : Policy.Policy} {oldTerms newTerms : List SupportTerm}
    (hold : Lara.termsWellSorted sg policy oldTerms = true)
    (hsubset : ∀ w ∈ newTerms, w ∈ oldTerms) :
    Lara.termsWellSorted sg policy newTerms = true := by
  induction newTerms with
  | nil => rfl
  | cons head rest ih =>
      simp only [Lara.termsWellSorted, Bool.and_eq_true]
      exact ⟨termWellSorted_of_mem hold (hsubset head (by simp)),
        ih (by
          intro w hw
          exact hsubset w (by simp [hw]))⟩

private theorem filter_sublist_filter_of_imp (xs : List α)
    (p q : α → Bool)
    (himp : ∀ x ∈ xs, p x = true → q x = true) :
    (xs.filter p).Sublist (xs.filter q) := by
  induction xs with
  | nil => exact .slnil
  | cons head rest ih =>
      have ih' := ih (fun x hx => himp x (by simp [hx]))
      by_cases hp : p head = true
      · have hq := himp head (by simp) hp
        simpa [hp, hq] using List.Sublist.cons_cons head ih'
      · by_cases hq : q head = true
        · simpa [hp, hq] using List.Sublist.cons head ih'
        · simpa [hp, hq] using ih'
private theorem acceptEdited_of_results {canon : String → String}
    (reg : BackendRegistry canon) (edited : SourceState)
    (hids : (edited.argsRaw.map (·.1)).Nodup)
    (declared : Admission.AlignedAttacks edited.argsRaw edited.rawAtts)
    (admission : Admission.AdmissionResult)
    (checked : Lara.Unit.CheckedUnit canon
      (Admission.buildGamma admission.prune.checkedLeaves) (certOkOf reg))
    (hadmission :
      Admission.evaluateAdmission canon edited.table edited.metas edited.leaves
        edited.argsRaw edited.rawAtts edited.groups declared = .accepted admission)
    (hcheck :
      Check.Unit.checkUnit
        (Admission.buildGamma admission.prune.checkedLeaves) reg edited.ground
        { sigma := edited.sigma
        , policy := edited.policy
        , args := admission.prune.keptArgs.map (·.2)
        , atts := admission.prune.keptAttacks } = .ok checked) :
    acceptEdited reg edited = .ok edited ∧ Accepted reg edited := by
  constructor
  · unfold acceptEdited
    split
    · rename_i hids'
      split
      · rename_i error hresolve
        rw [declared.resolve_eq] at hresolve
        contradiction
      · rename_i resolved hresolve
        have hresolved : resolved = declared.resolved :=
          Except.ok.inj (hresolve.symm.trans declared.resolve_eq)
        subst resolved
        simp only [admissionFor]
        rw [show
          Admission.evaluateAdmission canon edited.table edited.metas edited.leaves
              edited.argsRaw edited.rawAtts edited.groups
                { resolved := declared.resolved
                , resolve_eq := hresolve
                , ids_nodup := hids' } =
            .accepted admission by simpa only using hadmission]
        simp only [checkAccepted, checkedGamma, prunedUnit]
        rw [show
          Check.Unit.checkUnit
              (Admission.buildGamma admission.prune.checkedLeaves) reg edited.ground
              { sigma := edited.sigma
              , policy := edited.policy
              , args := admission.prune.keptArgs.map (·.2)
              , atts := admission.prune.keptAttacks } =
            .ok checked by simpa only using hcheck]
    · contradiction
  · exact ⟨declared, admission, checked, hadmission, hcheck⟩

private theorem prune_eq_of_acceptance {canon : String → String}
    {source : SourceState}
    {declared : Admission.AlignedAttacks source.argsRaw source.rawAtts}
    {admission : Admission.AdmissionResult}
    (hadmission :
      admissionFor canon source declared = .accepted admission) :
    admission.prune =
      Admission.buildPrune canon source.table source.metas source.leaves
        source.argsRaw source.rawAtts source.groups declared.resolved := by
  apply Admission.accepted_prune_eq canon source.table source.metas source.leaves
    source.argsRaw source.rawAtts source.groups declared
  simpa only [admissionFor] using hadmission

/-- The policy-stage facts a successful check established about its unit's
policy, in the form `Check.Unit.checkUnit_complete_holes` consumes. -/
private theorem policy_facts_of_check {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    {ground : List Atom} {unit : Lara.Unit}
    {accepted : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (h : Check.Unit.checkUnit Gamma reg ground unit = .ok accepted) :
    Policy.firstOutOfScope? unit.policy = none ∧
      (unit.policy.rules.map (·.id)).Nodup ∧
      Policy.WellFormed canon unit.policy := by
  have hs := Check.Unit.checkUnit_sound h
  rw [← hs.policy_eq]
  exact ⟨accepted.scopes_wf, hs.ruleIds_nodup, hs.policy_wf⟩

private theorem attackComplete_mono_attacks {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {dp : Attack.DefeatPolicy} {args : List SupportTerm}
    {oldAttacks newAttacks : List Attack.Attack}
    (hsubset : ∀ k ∈ oldAttacks, k ∈ newAttacks)
    (hcomplete :
      Compile.AttackComplete canon Pi Gamma CertOk dp args oldAttacks) :
    Compile.AttackComplete canon Pi Gamma CertOk dp args newAttacks := by
  intro source hsource target htarget sourceConclusion targetConclusion
    hsourceSupport htargetSupport hcontrary hattackable
  rcases hcomplete source hsource target htarget sourceConclusion
      targetConclusion hsourceSupport htargetSupport hcontrary hattackable with
    ⟨k, hk, hksource, witness, hocc, hcontains⟩
  exact ⟨k, hsubset k hk, hksource, witness, hocc, hcontains⟩

/-- Adding one resolved, typed attack preserves acceptance.  The two
`usesLeaf = false` premises are the constructor-local endpoint-retention
facts: the raw endpoint lookups resolve to terms that survive the existing
admission prune.  Resolution of the appended raw row, retention of every old
attack, and monotone conflict coverage are derived in the proof. -/
theorem applyUpdate_addAttack_ok {canon : String → String}
    (reg : BackendRegistry canon) (σ : SourceState)
    (raw : RawAttack.RawAttack) (attack : Attack.Attack)
    (haccepted : Accepted reg σ)
    (hresolved :
      RawAttack.resolveAttacks σ.argsRaw [raw] = .ok [attack])
    (htyped :
      Attack.HasAttack canon σ.policy.ruleLookup
        (Admission.buildGamma
          (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
            σ.rawAtts σ.groups []).checkedLeaves)
        (certOkOf reg) σ.policy.defeat attack)
    (hsourceRetained :
      Groups.usesLeaf
        (Admission.policyQuarantineSeed σ.table σ.metas ++
          Groups.quarantined canon σ.leaves σ.groups) attack.source = false)
    (htargetRetained :
      Groups.usesLeaf
        (Admission.policyQuarantineSeed σ.table σ.metas ++
          Groups.quarantined canon σ.leaves σ.groups) attack.target = false) :
    ∃ σ', applyUpdate reg σ (.addAttack raw) = .ok σ' ∧ Accepted reg σ' := by
  rcases haccepted with ⟨oldDeclared, oldAdmission, oldChecked,
    holdAdmission, holdCheck⟩
  have holdAdmission' :
      Admission.evaluateAdmission canon σ.table σ.metas σ.leaves
        σ.argsRaw σ.rawAtts σ.groups oldDeclared = .accepted oldAdmission := by
    simpa [admissionFor] using holdAdmission
  have holdPrune :
      oldAdmission.prune =
        Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
          σ.rawAtts σ.groups oldDeclared.resolved :=
    Admission.accepted_prune_eq canon σ.table σ.metas σ.leaves σ.argsRaw
      σ.rawAtts σ.groups oldDeclared holdAdmission'
  have htyped' :
      Attack.HasAttack canon σ.policy.ruleLookup
        (Admission.buildGamma oldAdmission.prune.checkedLeaves)
        (certOkOf reg) σ.policy.defeat attack := by
    simpa [holdPrune, Admission.buildPrune] using htyped
  obtain ⟨resolvedRaw, hrawMem, hsourceLookup, htargetLookup⟩ :=
    RawAttack.resolveAttacks_attack_lookup σ.argsRaw hresolved attack (by simp)
  have hrawEq : resolvedRaw = raw := by simpa using hrawMem
  subst resolvedRaw
  obtain ⟨sourceRow, hsourceRaw, hsourceId, hsourceTerm⟩ :=
    RawAttack.lookupArg_some_row σ.argsRaw hsourceLookup
  obtain ⟨targetRow, htargetRaw, htargetId, htargetTerm⟩ :=
    RawAttack.lookupArg_some_row σ.argsRaw htargetLookup
  have hsourceKept : sourceRow ∈ oldAdmission.prune.keptArgs := by
    rw [holdPrune]
    apply List.mem_filter.mpr
    exact ⟨hsourceRaw, by
      simpa [Admission.buildPrune, hsourceTerm] using hsourceRetained⟩
  have htargetKept : targetRow ∈ oldAdmission.prune.keptArgs := by
    rw [holdPrune]
    apply List.mem_filter.mpr
    exact ⟨htargetRaw, by
      simpa [Admission.buildPrune, htargetTerm] using htargetRetained⟩
  have hsourceIdKept : raw.endpoints.1 ∈ oldAdmission.prune.keptIds := by
    rw [holdPrune] at hsourceKept ⊢
    exact List.mem_map.mpr ⟨sourceRow, hsourceKept, hsourceId⟩
  have htargetIdKept : raw.endpoints.2 ∈ oldAdmission.prune.keptIds := by
    rw [holdPrune] at htargetKept ⊢
    exact List.mem_map.mpr ⟨targetRow, htargetKept, htargetId⟩
  let declared : Admission.AlignedAttacks σ.argsRaw (σ.rawAtts ++ [raw]) :=
    { resolved := oldDeclared.resolved ++ [attack]
    , resolve_eq :=
        RawAttack.resolveAttacks_append σ.argsRaw oldDeclared.resolve_eq hresolved
    , ids_nodup := oldDeclared.ids_nodup }
  let admission : Admission.AdmissionResult :=
    { prune := Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
        (σ.rawAtts ++ [raw]) σ.groups declared.resolved
    , declaredResolved := declared.resolved
    , audit := Admission.buildAdmissionAudit canon σ.table σ.metas σ.leaves
        σ.argsRaw (σ.rawAtts ++ [raw]) σ.groups declared.resolved }
  have hconditions :=
    Admission.evaluateAdmission_accepted_conditions holdAdmission'
  have hadmission :
      Admission.evaluateAdmission canon σ.table σ.metas σ.leaves σ.argsRaw
        (σ.rawAtts ++ [raw]) σ.groups declared = .accepted admission := by
    apply
      (Admission.evaluateAdmission_iff_judgment canon σ.table σ.metas σ.leaves
        σ.argsRaw (σ.rawAtts ++ [raw]) σ.groups declared
        (.accepted admission)).mp
    exact Admission.AdmissionJudgment.accepted hconditions.1 hconditions.2.1
      hconditions.2.2.1 hconditions.2.2.2 rfl
  have hargsEq : admission.prune.keptArgs = oldAdmission.prune.keptArgs := by
    rw [holdPrune]
    rfl
  have hgammaEq :
      Admission.buildGamma admission.prune.checkedLeaves =
        Admission.buildGamma oldAdmission.prune.checkedLeaves := by
    rw [holdPrune]
    rfl
  have hkeptIdsEq :
      admission.prune.keptIds = oldAdmission.prune.keptIds := by
    rw [holdPrune]
    rfl
  have hkeepRaw : admission.prune.keepAttack raw = true := by
    change (decide (raw.endpoints.1 ∈ admission.prune.keptIds) &&
      decide (raw.endpoints.2 ∈ admission.prune.keptIds)) = true
    rw [hkeptIdsEq]
    simp [hsourceIdKept, htargetIdKept]
  have hattsEq :
      admission.prune.keptAttacks =
        oldAdmission.prune.keptAttacks ++ [attack] := by
    rw [holdPrune]
    change
      RawAttack.selectAligned admission.prune.keepAttack
          (σ.rawAtts ++ [raw]) (oldDeclared.resolved ++ [attack]) =
        RawAttack.selectAligned admission.prune.keepAttack σ.rawAtts
          oldDeclared.resolved ++ [attack]
    rw [RawAttack.selectAligned_append_of_length_eq _ _ _ _ _
      (RawAttack.resolveAttacks_length σ.argsRaw oldDeclared.resolve_eq)]
    simp [RawAttack.selectAligned, hkeepRaw]
  have holdSound := Check.Unit.checkUnit_sound holdCheck
  have hpolicyFacts := policy_facts_of_check holdCheck
  have hsignature :
      Check.Unit.signatureStage σ.ground
        { sigma := σ.sigma, policy := σ.policy
        , args := admission.prune.keptArgs.map (·.2)
        , atts := admission.prune.keptAttacks } = none := by
    have hold := holdSound.signature_ok
    simp only [Check.Unit.signatureStage] at hold ⊢
    rw [hargsEq]
    exact hold
  have hargs : (admission.prune.keptArgs.map (·.2)).Nodup := by
    rw [hargsEq]
    exact holdSound.raw_nodup
  have hsupport : ∀ w ∈ admission.prune.keptArgs.map (·.2), ∃ C O,
      HasSupport canon σ.policy.ruleLookup
        (Admission.buildGamma admission.prune.checkedLeaves)
        (certOkOf reg) w C O := by
    intro w hw
    rw [hgammaEq]
    rw [hargsEq] at hw
    exact holdSound.raw_support w hw
  have hattackTyping : ∀ k ∈ admission.prune.keptAttacks,
      Attack.HasAttack canon σ.policy.ruleLookup
        (Admission.buildGamma admission.prune.checkedLeaves)
        (certOkOf reg) σ.policy.defeat k := by
    intro current hcurrent
    rw [hattsEq] at hcurrent
    rw [hgammaEq]
    rcases List.mem_append.mp hcurrent with hold | hnew
    · exact holdSound.raw_typed current hold
    · simp at hnew
      subst current
      exact htyped'
  have hendpoints : ∀ current ∈ admission.prune.keptAttacks,
      current.source ∈ admission.prune.keptArgs.map (·.2) ∧
      current.target ∈ admission.prune.keptArgs.map (·.2) := by
    intro current hcurrent
    exact Admission.retained_semantic_attack_endpoints canon σ.table σ.metas
      σ.leaves σ.argsRaw (σ.rawAtts ++ [raw]) σ.groups declared current hcurrent
  have hpriorCoverage :
      Compile.AttackComplete canon σ.policy.ruleLookup
        (Admission.buildGamma admission.prune.checkedLeaves)
        (certOkOf reg) σ.policy.defeat
        (admission.prune.keptArgs.map (·.2))
        oldAdmission.prune.keptAttacks := by
    rw [hgammaEq, hargsEq]
    exact holdSound.raw_attack_complete
  have hnewCoverage :
      Compile.AttackComplete canon σ.policy.ruleLookup
        (Admission.buildGamma admission.prune.checkedLeaves)
        (certOkOf reg) σ.policy.defeat
        (admission.prune.keptArgs.map (·.2))
        admission.prune.keptAttacks :=
    attackComplete_mono_attacks (by
      intro old hold
      rw [hattsEq]
      exact List.mem_append.mpr (Or.inl hold)) hpriorCoverage
  obtain ⟨checked, hcheck⟩ :=
    Check.Unit.checkUnit_complete_holes hsignature
      hpolicyFacts.1 hpolicyFacts.2.1 hpolicyFacts.2.2
      hargs hsupport hattackTyping
      (fun current hcurrent => (hendpoints current hcurrent).1)
      (fun current hcurrent => (hendpoints current hcurrent).2)
      hnewCoverage
  let edited : SourceState := { σ with rawAtts := σ.rawAtts ++ [raw] }
  have hfinished := acceptEdited_of_results reg edited oldDeclared.ids_nodup
    declared admission checked hadmission hcheck
  refine ⟨edited, ?_, hfinished.2⟩
  simp only [applyUpdate]
  have hdeclared : EndpointDeclared σ raw := by
    exact RawAttack.resolveAttacks_endpoints_mem σ.argsRaw hresolved raw (by simp)
  rw [(endpointDeclaredB_iff σ raw).mpr hdeclared]
  exact hfinished.1

/-- The shared `addInstance` preservation argument: the new term only has to
type, complete or not. Callers supply its typing and conflict coverage for the
old retained arguments extended by it. -/
private theorem applyUpdate_addInstance_typed_ok {canon : String → String}
    (reg : BackendRegistry canon) (σ : SourceState)
    (name : String) (w : SupportTerm)
    (haccepted : Accepted reg σ)
    (hfresh : InstanceFresh σ name w)
    (hnewWellSorted : Lara.termWellSorted σ.sigma σ.policy w = true)
    (hnewTyped :
      ∃ C O, HasSupport canon σ.policy.ruleLookup
        (Admission.buildGamma
          (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
            σ.rawAtts σ.groups []).checkedLeaves)
        (certOkOf reg) w C O)
    (hcoverage : ∀ resolved,
      RawAttack.resolveAttacks σ.argsRaw σ.rawAtts = .ok resolved →
      Compile.AttackComplete canon σ.policy.ruleLookup
        (Admission.buildGamma
          (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
            σ.rawAtts σ.groups resolved).checkedLeaves)
        (certOkOf reg) σ.policy.defeat
        ((Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
          σ.rawAtts σ.groups resolved).keptArgs.map (·.2) ++ [w])
        (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
          σ.rawAtts σ.groups resolved).keptAttacks) :
    ∃ σ', applyUpdate reg σ (.addInstance name w) = .ok σ' ∧
      Accepted reg σ' := by
  rcases haccepted with ⟨oldDeclared, oldAdmission, oldChecked,
    holdAdmission, holdCheck⟩
  have holdAdmission' :
      Admission.evaluateAdmission canon σ.table σ.metas σ.leaves
        σ.argsRaw σ.rawAtts σ.groups oldDeclared = .accepted oldAdmission := by
    simpa [admissionFor] using holdAdmission
  have holdPrune :
      oldAdmission.prune =
        Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
          σ.rawAtts σ.groups oldDeclared.resolved :=
    Admission.accepted_prune_eq canon σ.table σ.metas σ.leaves σ.argsRaw
      σ.rawAtts σ.groups oldDeclared holdAdmission'
  obtain ⟨newConclusion, newObligations, hnewTyped'⟩ := hnewTyped
  have hnewKeep :
      Groups.usesLeaf
        (Admission.policyQuarantineSeed σ.table σ.metas ++
          Groups.quarantined canon σ.leaves σ.groups) w = false :=
    hasSupport_not_uses_prune_seed σ.table σ.metas σ.leaves σ.argsRaw
      σ.rawAtts σ.groups [] hnewTyped'
  have hnewTypedOld :
      HasSupport canon σ.policy.ruleLookup
        (Admission.buildGamma oldAdmission.prune.checkedLeaves)
        (certOkOf reg) w newConclusion newObligations := by
    simpa [holdPrune, Admission.buildPrune] using hnewTyped'
  have hresolveExtended :
      RawAttack.resolveAttacks (σ.argsRaw ++ [(name, w)]) σ.rawAtts =
        .ok oldDeclared.resolved :=
    RawAttack.resolveAttacks_mono_lookup σ.argsRaw
      (σ.argsRaw ++ [(name, w)])
      (fun _ _ h => RawAttack.lookupArg_append_of_some σ.argsRaw [(name, w)] h)
      oldDeclared.resolve_eq
  have hids :
      ((σ.argsRaw ++ [(name, w)]).map (·.1)).Nodup := by
    rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨oldDeclared.ids_nodup, by simp, ?_⟩
    intro id hidOld newId hnewId
    have hnewIdEq : newId = name := by simpa using hnewId
    obtain ⟨row, hrow, hname⟩ := List.mem_map.mp hidOld
    intro heq
    exact hfresh.1 row hrow (hname.trans (heq.trans hnewIdEq))
  let declared :
      Admission.AlignedAttacks (σ.argsRaw ++ [(name, w)]) σ.rawAtts :=
    { resolved := oldDeclared.resolved
    , resolve_eq := hresolveExtended
    , ids_nodup := hids }
  let admission : Admission.AdmissionResult :=
    { prune := Admission.buildPrune canon σ.table σ.metas σ.leaves
        (σ.argsRaw ++ [(name, w)]) σ.rawAtts σ.groups declared.resolved
    , declaredResolved := declared.resolved
    , audit := Admission.buildAdmissionAudit canon σ.table σ.metas σ.leaves
        (σ.argsRaw ++ [(name, w)]) σ.rawAtts σ.groups declared.resolved }
  have hconditions :=
    Admission.evaluateAdmission_accepted_conditions holdAdmission'
  have hadmission :
      Admission.evaluateAdmission canon σ.table σ.metas σ.leaves
        (σ.argsRaw ++ [(name, w)]) σ.rawAtts σ.groups declared =
          .accepted admission := by
    apply
      (Admission.evaluateAdmission_iff_judgment canon σ.table σ.metas σ.leaves
        (σ.argsRaw ++ [(name, w)]) σ.rawAtts σ.groups declared
        (.accepted admission)).mp
    exact Admission.AdmissionJudgment.accepted hconditions.1 hconditions.2.1
      hconditions.2.2.1 hconditions.2.2.2 rfl
  have hgammaEq :
      Admission.buildGamma admission.prune.checkedLeaves =
        Admission.buildGamma oldAdmission.prune.checkedLeaves := by
    rw [holdPrune]
    rfl
  have hargsEq :
      admission.prune.keptArgs =
        oldAdmission.prune.keptArgs ++ [(name, w)] := by
    rw [holdPrune]
    change
      (σ.argsRaw ++ [(name, w)]).filter
          (fun row => !Groups.usesLeaf
            (Admission.policyQuarantineSeed σ.table σ.metas ++
              Groups.quarantined canon σ.leaves σ.groups) row.2) =
        σ.argsRaw.filter
            (fun row => !Groups.usesLeaf
              (Admission.policyQuarantineSeed σ.table σ.metas ++
                Groups.quarantined canon σ.leaves σ.groups) row.2) ++
          [(name, w)]
    simp [List.filter_append, hnewKeep]
  have hkeptIdsEq :
      admission.prune.keptIds = oldAdmission.prune.keptIds ++ [name] := by
    have hadmissionIds :
        admission.prune.keptIds = admission.prune.keptArgs.map (·.1) := rfl
    have holdIds :
        oldAdmission.prune.keptIds =
          oldAdmission.prune.keptArgs.map (·.1) := by
      rw [holdPrune]
      rfl
    rw [hadmissionIds, holdIds, hargsEq, List.map_append]
    rfl
  have hattsEq :
      admission.prune.keptAttacks = oldAdmission.prune.keptAttacks := by
    rw [holdPrune]
    apply RawAttack.selectAligned_congr_on
    intro current hcurrent
    have hendpointNames :=
      RawAttack.resolveAttacks_endpoints_mem σ.argsRaw oldDeclared.resolve_eq
        current hcurrent
    have hsourceNe : current.endpoints.1 ≠ name := by
      intro heq
      obtain ⟨row, hrow, hid⟩ := List.mem_map.mp hendpointNames.1
      exact hfresh.1 row hrow (hid.trans heq)
    have htargetNe : current.endpoints.2 ≠ name := by
      intro heq
      obtain ⟨row, hrow, hid⟩ := List.mem_map.mp hendpointNames.2
      exact hfresh.1 row hrow (hid.trans heq)
    change
      (decide (current.endpoints.1 ∈ admission.prune.keptIds) &&
        decide (current.endpoints.2 ∈ admission.prune.keptIds)) =
      (decide (current.endpoints.1 ∈
          (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
            σ.rawAtts σ.groups oldDeclared.resolved).keptIds) &&
        decide (current.endpoints.2 ∈
          (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
            σ.rawAtts σ.groups oldDeclared.resolved).keptIds))
    rw [hkeptIdsEq, ← holdPrune]
    simp [hsourceNe, htargetNe]
  have holdSound := Check.Unit.checkUnit_sound holdCheck
  have hpolicyFacts := policy_facts_of_check holdCheck
  have hnewArgs :
      admission.prune.keptArgs.map (·.2) =
        oldAdmission.prune.keptArgs.map (·.2) ++ [w] := by
    simp [hargsEq, List.map_append]
  have hsignature :
      Check.Unit.signatureStage σ.ground
        { sigma := σ.sigma, policy := σ.policy
        , args := admission.prune.keptArgs.map (·.2)
        , atts := admission.prune.keptAttacks } = none := by
    have hold := holdSound.signature_ok
    have holdArgsSorted :
        Lara.termsWellSorted σ.sigma σ.policy
          (oldAdmission.prune.keptArgs.map (·.2)) = true :=
      holdSound.raw_sorted
    have hnewArgsSorted :
        Lara.argsWellSorted σ.sigma σ.policy
          (admission.prune.keptArgs.map (·.2)) = true := by
      rw [Lara.argsWellSorted, hnewArgs]
      exact termsWellSorted_append_singleton σ.sigma σ.policy
        (oldAdmission.prune.keptArgs.map (·.2)) w holdArgsSorted
        hnewWellSorted
    have hsigmaWf : Sigma.sigmaWellFormed σ.sigma = true :=
      Check.Unit.signatureStage_sigma_wf hold
    have hpolicySorted : Lara.policyWellSorted σ.sigma σ.policy = true :=
      Check.Unit.signatureStage_policy hold
    have hgroundSorted : Lara.groundWellSorted σ.sigma σ.ground = true :=
      Check.Unit.signatureStage_ground hold
    simp [Check.Unit.signatureStage, hsigmaWf, hpolicySorted,
      hgroundSorted, hnewArgsSorted]
  have hargs : (admission.prune.keptArgs.map (·.2)).Nodup := by
    rw [hnewArgs]
    apply List.nodup_append.mpr
    refine ⟨holdSound.raw_nodup, by simp, ?_⟩
    intro term htermOld newTerm htermNew
    have hnewTermEq : newTerm = w := by simpa using htermNew
    obtain ⟨row, hrow, hterm⟩ := List.mem_map.mp htermOld
    have hrowRaw : row ∈ σ.argsRaw := by
      rw [holdPrune] at hrow
      exact (List.mem_filter.mp hrow).1
    intro heq
    exact hfresh.2 row hrowRaw (hterm.trans (heq.trans hnewTermEq))
  have hsupport : ∀ term ∈ admission.prune.keptArgs.map (·.2), ∃ C O,
      HasSupport canon σ.policy.ruleLookup
        (Admission.buildGamma admission.prune.checkedLeaves)
        (certOkOf reg) term C O := by
    intro term hterm
    rw [hnewArgs] at hterm
    rw [hgammaEq]
    rcases List.mem_append.mp hterm with hold | hnew
    · exact holdSound.raw_support term hold
    · simp only [List.mem_singleton] at hnew
      subst term
      exact ⟨newConclusion, newObligations, hnewTypedOld⟩
  have hattackTyping : ∀ current ∈ admission.prune.keptAttacks,
      Attack.HasAttack canon σ.policy.ruleLookup
        (Admission.buildGamma admission.prune.checkedLeaves)
        (certOkOf reg) σ.policy.defeat current := by
    intro current hcurrent
    rw [hattsEq] at hcurrent
    rw [hgammaEq]
    exact holdSound.raw_typed current hcurrent
  have hendpoints : ∀ current ∈ admission.prune.keptAttacks,
      current.source ∈ admission.prune.keptArgs.map (·.2) ∧
      current.target ∈ admission.prune.keptArgs.map (·.2) := by
    intro current hcurrent
    exact Admission.retained_semantic_attack_endpoints canon σ.table σ.metas
      σ.leaves (σ.argsRaw ++ [(name, w)]) σ.rawAtts σ.groups declared
      current hcurrent
  have hcoverageOld :=
    hcoverage oldDeclared.resolved oldDeclared.resolve_eq
  rw [← holdPrune] at hcoverageOld
  have hcoverage' :
      Compile.AttackComplete canon σ.policy.ruleLookup
        (Admission.buildGamma admission.prune.checkedLeaves)
        (certOkOf reg) σ.policy.defeat
        (admission.prune.keptArgs.map (·.2))
        admission.prune.keptAttacks := by
    rw [hgammaEq, hnewArgs, hattsEq]
    exact hcoverageOld
  obtain ⟨checked, hcheck⟩ :=
    Check.Unit.checkUnit_complete_holes hsignature
      hpolicyFacts.1 hpolicyFacts.2.1 hpolicyFacts.2.2
      hargs hsupport hattackTyping
      (fun current hcurrent => (hendpoints current hcurrent).1)
      (fun current hcurrent => (hendpoints current hcurrent).2)
      hcoverage'
  let edited : SourceState :=
    { σ with argsRaw := σ.argsRaw ++ [(name, w)] }
  have hfinished := acceptEdited_of_results reg edited hids declared admission
    checked hadmission hcheck
  refine ⟨edited, ?_, hfinished.2⟩
  simp only [applyUpdate]
  rw [(instanceFreshB_iff σ name w).mpr hfresh]
  exact hfinished.1

/-- Adding a fresh argument instance preserves acceptance from the new
term's own sorting and complete-support derivation.  The final premise is the
sharp constructor delta: conflict coverage must hold for the old retained
argument list extended by the new term.  Resolution, support, attack typing,
and endpoints for every old declaration are transported from `Accepted`.
This is the completion case: the old holes stay declared (D11). -/
theorem applyUpdate_addInstance_ok {canon : String → String}
    (reg : BackendRegistry canon) (σ : SourceState)
    (name : String) (w : SupportTerm)
    (haccepted : Accepted reg σ)
    (hfresh : InstanceFresh σ name w)
    (hnewWellSorted : Lara.termWellSorted σ.sigma σ.policy w = true)
    (hnewComplete :
      ∃ C, HasSupport canon σ.policy.ruleLookup
        (Admission.buildGamma
          (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
            σ.rawAtts σ.groups []).checkedLeaves)
        (certOkOf reg) w C [])
    (hcoverage : ∀ resolved,
      RawAttack.resolveAttacks σ.argsRaw σ.rawAtts = .ok resolved →
      Compile.AttackComplete canon σ.policy.ruleLookup
        (Admission.buildGamma
          (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
            σ.rawAtts σ.groups resolved).checkedLeaves)
        (certOkOf reg) σ.policy.defeat
        ((Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
          σ.rawAtts σ.groups resolved).keptArgs.map (·.2) ++ [w])
        (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
          σ.rawAtts σ.groups resolved).keptAttacks) :
    ∃ σ', applyUpdate reg σ (.addInstance name w) = .ok σ' ∧
      Accepted reg σ' :=
  let ⟨C, hC⟩ := hnewComplete
  applyUpdate_addInstance_typed_ok reg σ name w haccepted hfresh
    hnewWellSorted ⟨C, [], hC⟩ hcoverage

/-- **Adding a fresh hole preserves acceptance.** A fresh, well-sorted term
that types with a nonempty mandatory obligation set never needs a conflict
premise: attack completeness constrains complete arguments only, so the old
coverage carries over unchanged. -/
theorem applyUpdate_addInstance_hole_ok {canon : String → String}
    (reg : BackendRegistry canon) (σ : SourceState)
    (name : String) (w : SupportTerm)
    (haccepted : Accepted reg σ)
    (hfresh : InstanceFresh σ name w)
    (hnewWellSorted : Lara.termWellSorted σ.sigma σ.policy w = true)
    (hnewHole :
      ∃ C O, HasSupport canon σ.policy.ruleLookup
        (Admission.buildGamma
          (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
            σ.rawAtts σ.groups []).checkedLeaves)
        (certOkOf reg) w C O ∧ O ≠ []) :
    ∃ σ', applyUpdate reg σ (.addInstance name w) = .ok σ' ∧
      Accepted reg σ' := by
  obtain ⟨C, O, hC, hO⟩ := hnewHole
  apply applyUpdate_addInstance_typed_ok reg σ name w haccepted hfresh
    hnewWellSorted ⟨C, O, hC⟩
  intro resolved hresolved
  rcases haccepted with ⟨oldDeclared, oldAdmission, oldChecked,
    holdAdmission, holdCheck⟩
  have hresolvedEq : resolved = oldDeclared.resolved :=
    Except.ok.inj (hresolved.symm.trans oldDeclared.resolve_eq)
  subst resolved
  have holdPrune := prune_eq_of_acceptance holdAdmission
  have hold :
      Compile.AttackComplete canon σ.policy.ruleLookup
        (Admission.buildGamma oldAdmission.prune.checkedLeaves) (certOkOf reg)
        σ.policy.defeat (oldAdmission.prune.keptArgs.map (·.2))
        oldAdmission.prune.keptAttacks :=
    (Check.Unit.checkUnit_sound holdCheck).raw_attack_complete
  have hholeGamma :
      HasSupport canon σ.policy.ruleLookup
        (Admission.buildGamma
          (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
            σ.rawAtts σ.groups oldDeclared.resolved).checkedLeaves)
        (certOkOf reg) w C O := by
    simpa [Admission.buildPrune] using hC
  rw [holdPrune] at hold
  intro source hsource target htarget Cs Ct hCs hCt hcontrary hattackable
  have hnotHole : ∀ {term C'},
      term ∈ (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
        σ.rawAtts σ.groups oldDeclared.resolved).keptArgs.map (·.2) ++ [w] →
      HasSupport canon σ.policy.ruleLookup
        (Admission.buildGamma
          (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
            σ.rawAtts σ.groups oldDeclared.resolved).checkedLeaves)
        (certOkOf reg) term C' [] →
      term ∈ (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
        σ.rawAtts σ.groups oldDeclared.resolved).keptArgs.map (·.2) := by
    intro term C' hterm hcomplete
    rcases List.mem_append.mp hterm with hold | hnew
    · exact hold
    · simp only [List.mem_singleton] at hnew
      subst term
      exact absurd (hasSupport_unique hholeGamma hcomplete).2 hO
  exact hold source (hnotHole hsource hCs) target (hnotHole htarget hCt)
    Cs Ct hCs hCt hcontrary hattackable

/-- Adding a fresh admitted leaf preserves acceptance.  Freshness is checked
in the semantic leaf rows, metadata rows, and every duplicate-group member
list.  The sole admission premise allows both the default and an explicit
`admit` row; all old support, attack, endpoint, and coverage obligations are
transported to the checker context extended by the new leaf. -/
theorem applyUpdate_addLeaf_ok {canon : String → String}
    (reg : BackendRegistry canon) (σ : SourceState)
    (id : LeafId) (a : Atom) (m : Admission.LeafMeta)
    (haccepted : Accepted reg σ)
    (hfresh : AddLeafFresh σ id)
    (hnewAdmitted :
      Admission.decisionFor σ.table m.kind m.provenance = .admit) :
    ∃ σ', applyUpdate reg σ (.addLeaf id a m) = .ok σ' ∧
      Accepted reg σ' := by
  rcases haccepted with ⟨declared, oldAdmission, oldChecked,
    holdAdmission, holdCheck⟩
  have holdAdmission' :
      Admission.evaluateAdmission canon σ.table σ.metas σ.leaves
        σ.argsRaw σ.rawAtts σ.groups declared = .accepted oldAdmission := by
    simpa [admissionFor] using holdAdmission
  have holdPrune :
      oldAdmission.prune =
        Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
          σ.rawAtts σ.groups declared.resolved :=
    Admission.accepted_prune_eq canon σ.table σ.metas σ.leaves σ.argsRaw
      σ.rawAtts σ.groups declared holdAdmission'
  have hconditions :=
    Admission.evaluateAdmission_accepted_conditions holdAdmission'
  have hmetaNodup :
      ((σ.metas ++ [{ m with id := id }]).map
        (fun oldMeta : Admission.LeafMeta => oldMeta.id)).Nodup := by
    rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨(Admission.firstDuplicateLeafId_none_iff_nodup σ.metas).mp
      hconditions.2.1,
      by simp, ?_⟩
    intro oldId holdId newId hnewId
    have hnewIdEq : newId = id := by simpa using hnewId
    obtain ⟨oldMeta, hmeta, hmetaId⟩ := List.mem_map.mp holdId
    intro heq
    exact hfresh.2.1 oldMeta hmeta (hmetaId.trans (heq.trans hnewIdEq))
  have hduplicateNone :
      Admission.firstDuplicateLeafId
        (σ.metas ++ [{ m with id := id }]) = none :=
    (Admission.firstDuplicateLeafId_none_iff_nodup _).mpr hmetaNodup
  have haligned :
      Admission.metadataLeafAligned
        (σ.metas ++ [{ m with id := id }])
        (σ.leaves ++ [(id, a)]) := by
    unfold Admission.metadataLeafAligned at hconditions ⊢
    simpa [List.map_append] using congrArg (· ++ [id]) hconditions.2.2.1
  have hrejectionNone :
      Admission.firstAdmissionRejection σ.table
        (σ.metas ++ [{ m with id := id }]) = none :=
    firstAdmissionRejection_append_none σ.table σ.metas
      { m with id := id } hconditions.2.2.2 (by
        rw [hnewAdmitted]
        decide)
  have hpolicySeed :
      Admission.policyQuarantineSeed σ.table
          (σ.metas ++ [{ m with id := id }]) =
        Admission.policyQuarantineSeed σ.table σ.metas := by
    simp [Admission.policyQuarantineSeed, List.filterMap_append, hnewAdmitted]
  have hgroupSeed :
      Groups.quarantined canon (σ.leaves ++ [(id, a)]) σ.groups =
        Groups.quarantined canon σ.leaves σ.groups :=
    quarantined_append_fresh canon σ.leaves id a σ.groups hfresh.2.2
  have hnotPolicy :
      id ∉ Admission.policyQuarantineSeed σ.table σ.metas := by
    intro hmem
    obtain ⟨oldMeta, hmeta, hmetaId, _⟩ :=
      (Admission.mem_policyQuarantineSeed_iff σ.table σ.metas id).mp hmem
    exact hfresh.2.1 oldMeta hmeta hmetaId
  have hnotGroup : id ∉ Groups.quarantined canon σ.leaves σ.groups := by
    intro hmem
    obtain ⟨group, hgroup, _, hmember⟩ :=
      (Groups.mem_quarantined_iff canon σ.leaves σ.groups id).mp hmem
    exact hfresh.2.2 group hgroup id hmember rfl
  let admission : Admission.AdmissionResult :=
    { prune := Admission.buildPrune canon σ.table
        (σ.metas ++ [{ m with id := id }]) (σ.leaves ++ [(id, a)])
        σ.argsRaw σ.rawAtts σ.groups declared.resolved
    , declaredResolved := declared.resolved
    , audit := Admission.buildAdmissionAudit canon σ.table
        (σ.metas ++ [{ m with id := id }]) (σ.leaves ++ [(id, a)])
        σ.argsRaw σ.rawAtts σ.groups declared.resolved }
  have hadmission :
      Admission.evaluateAdmission canon σ.table
        (σ.metas ++ [{ m with id := id }]) (σ.leaves ++ [(id, a)])
        σ.argsRaw σ.rawAtts σ.groups declared = .accepted admission := by
    apply
      (Admission.evaluateAdmission_iff_judgment canon σ.table
        (σ.metas ++ [({ m with id := id } : Admission.LeafMeta)])
        (σ.leaves ++ [(id, a)])
        σ.argsRaw σ.rawAtts σ.groups declared (.accepted admission)).mp
    exact Admission.AdmissionJudgment.accepted hconditions.1 hduplicateNone
      haligned hrejectionNone rfl
  have hcheckedEq :
      admission.prune.checkedLeaves =
        oldAdmission.prune.checkedLeaves ++ [(id, a)] := by
    rw [holdPrune]
    change
      Admission.checkedLeafTable canon σ.table
          (σ.metas ++ [{ m with id := id }]) (σ.leaves ++ [(id, a)])
          σ.groups =
        Admission.checkedLeafTable canon σ.table σ.metas σ.leaves σ.groups ++
          [(id, a)]
    unfold Admission.checkedLeafTable
    rw [hpolicySeed, hgroupSeed]
    simp [Groups.quarantineLeaves, List.filter_append, hnotPolicy, hnotGroup]
  have hargsEq : admission.prune.keptArgs = oldAdmission.prune.keptArgs := by
    rw [holdPrune]
    change
      σ.argsRaw.filter (fun row => !Groups.usesLeaf
        (Admission.policyQuarantineSeed σ.table
            (σ.metas ++ [{ m with id := id }]) ++
          Groups.quarantined canon (σ.leaves ++ [(id, a)]) σ.groups) row.2) =
      σ.argsRaw.filter (fun row => !Groups.usesLeaf
        (Admission.policyQuarantineSeed σ.table σ.metas ++
          Groups.quarantined canon σ.leaves σ.groups) row.2)
    rw [hpolicySeed, hgroupSeed]
  have hattsEq :
      admission.prune.keptAttacks = oldAdmission.prune.keptAttacks := by
    rw [holdPrune]
    dsimp [admission]
    simp only [Admission.buildPrune]
    rw [hpolicySeed, hgroupSeed]
  have holdSound := Check.Unit.checkUnit_sound holdCheck
  have hpolicyFacts := policy_facts_of_check holdCheck
  have holdNoFresh : ∀ term ∈ oldAdmission.prune.keptArgs.map (·.2),
      id ∉ Support.leaves term := by
    intro term hterm hid
    obtain ⟨C, O, hsupport⟩ := holdSound.raw_support term hterm
    obtain ⟨p, hgamma⟩ := Support.leaves_declared hsupport id hid
    have hcheckedId := Admission.buildGamma_some_mem hgamma
    rw [holdPrune] at hcheckedId
    have hleafId : id ∈ σ.leaves.map (·.1) := by
      exact List.mem_map.mpr
        (let ⟨row, hrow, hrowId⟩ := List.mem_map.mp hcheckedId
         ⟨row, (List.mem_filter.mp hrow).1, hrowId⟩)
    obtain ⟨row, hrow, hrowId⟩ := List.mem_map.mp hleafId
    exact hfresh.1 row hrow hrowId
  have hgammaExt : ∀ l p,
      Admission.buildGamma oldAdmission.prune.checkedLeaves l = some p →
      Admission.buildGamma admission.prune.checkedLeaves l = some p := by
    intro l p h
    rw [hcheckedEq]
    exact Admission.buildGamma_append_of_some oldAdmission.prune.checkedLeaves [(id, a)] h
  have hgammaOn : ∀ term ∈ admission.prune.keptArgs.map (·.2),
      ∀ l, l ∈ Support.leaves term →
        Admission.buildGamma admission.prune.checkedLeaves l =
          Admission.buildGamma oldAdmission.prune.checkedLeaves l := by
    intro term hterm l hl
    rw [hcheckedEq]
    apply Admission.buildGamma_append_ne
    intro heq
    subst l
    exact holdNoFresh term (by simpa [hargsEq] using hterm) hl
  have hsignature :
      Check.Unit.signatureStage σ.ground
        { sigma := σ.sigma, policy := σ.policy
        , args := admission.prune.keptArgs.map (·.2)
        , atts := admission.prune.keptAttacks } = none := by
    have hold := holdSound.signature_ok
    simp only [Check.Unit.signatureStage] at hold ⊢
    rw [hargsEq]
    exact hold
  have hargs : (admission.prune.keptArgs.map (·.2)).Nodup := by
    rw [hargsEq]
    exact holdSound.raw_nodup
  have hsupport : ∀ term ∈ admission.prune.keptArgs.map (·.2), ∃ C O,
      HasSupport canon σ.policy.ruleLookup
        (Admission.buildGamma admission.prune.checkedLeaves)
        (certOkOf reg) term C O := by
    intro term hterm
    rw [hargsEq] at hterm
    obtain ⟨C, O, hold⟩ := holdSound.raw_support term hterm
    exact ⟨C, O, hasSupport_mono_gamma hgammaExt hold⟩
  have hattackTyping : ∀ current ∈ admission.prune.keptAttacks,
      Attack.HasAttack canon σ.policy.ruleLookup
        (Admission.buildGamma admission.prune.checkedLeaves)
        (certOkOf reg) σ.policy.defeat current := by
    intro current hcurrent
    rw [hattsEq] at hcurrent
    exact Attack.hasAttack_mono_gamma hgammaExt
      (holdSound.raw_typed current hcurrent)
  have hendpoints : ∀ current ∈ admission.prune.keptAttacks,
      current.source ∈ admission.prune.keptArgs.map (·.2) ∧
      current.target ∈ admission.prune.keptArgs.map (·.2) := by
    intro current hcurrent
    rw [hattsEq] at hcurrent
    rw [hargsEq]
    exact ⟨holdSound.raw_source current hcurrent,
      holdSound.raw_target current hcurrent⟩
  have hcoverage :
      Compile.AttackComplete canon σ.policy.ruleLookup
        (Admission.buildGamma admission.prune.checkedLeaves)
        (certOkOf reg) σ.policy.defeat
        (admission.prune.keptArgs.map (·.2))
        admission.prune.keptAttacks := by
    intro source hsource target htarget sourceConclusion targetConclusion
      hsourceSupport htargetSupport hcontrary hattackable
    have holdCoverage : Compile.AttackComplete canon σ.policy.ruleLookup
        (Admission.buildGamma oldAdmission.prune.checkedLeaves)
        (certOkOf reg) σ.policy.defeat
        (oldAdmission.prune.keptArgs.map (·.2))
        oldAdmission.prune.keptAttacks :=
      holdSound.raw_attack_complete
    have hsourceOld := hasSupport_congr_gamma_on hsourceSupport
      (hgammaOn source hsource)
    have htargetOld := hasSupport_congr_gamma_on htargetSupport
      (hgammaOn target htarget)
    rw [hattsEq]
    exact holdCoverage source (by simpa [hargsEq] using hsource)
      target (by simpa [hargsEq] using htarget)
      sourceConclusion targetConclusion hsourceOld htargetOld hcontrary
      hattackable
  obtain ⟨checked, hcheck⟩ :=
    Check.Unit.checkUnit_complete_holes hsignature
      hpolicyFacts.1 hpolicyFacts.2.1 hpolicyFacts.2.2
      hargs hsupport hattackTyping
      (fun current hcurrent => (hendpoints current hcurrent).1)
      (fun current hcurrent => (hendpoints current hcurrent).2)
      hcoverage
  let edited : SourceState :=
    { σ with metas := σ.metas ++ [{ m with id := id }]
             leaves := σ.leaves ++ [(id, a)] }
  have hfinished := acceptEdited_of_results reg edited declared.ids_nodup
    declared admission checked hadmission hcheck
  refine ⟨edited, ?_, hfinished.2⟩
  simp only [applyUpdate]
  rw [(addLeafFreshB_iff σ id).mpr hfresh]
  exact hfinished.1

/-- Admit-to-quarantine tightening preserves acceptance when the edited table
remains valid and rejection-free.  `AtLeastAsRestrictive` and
`more_restrictive_cannot_add_structure` transport the retained rows and
attacks.  The final two premises are the irreducible local facts not implied
by mere subset membership: checker-Gamma agreement on leaves of retained
terms, and resolution-guarded survival of canonical old coverage witnesses
between retained endpoints. -/
theorem applyUpdate_tighten_ok {canon : String → String}
    (reg : BackendRegistry canon) (σ : SourceState)
    (key : LeafKind × Provenance)
    (haccepted : Accepted reg σ)
    (hadmitted : AdmittedAt σ key)
    (hrestrictive :
      Admission.AtLeastAsRestrictive σ.table (tightenTable σ.table key))
    (hrows :
      Admission.firstDuplicateKey (tightenTable σ.table key) = none ∧
      Admission.firstAdmissionRejection (tightenTable σ.table key) σ.metas =
        none)
    (hgammaRetained : ∀ (row : String × SupportTerm),
      row ∈ (Admission.buildPrune canon (tightenTable σ.table key) σ.metas
        σ.leaves σ.argsRaw σ.rawAtts σ.groups []).keptArgs →
      ∀ l, l ∈ Support.leaves row.2 →
        Admission.buildGamma
            (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
              σ.rawAtts σ.groups []).checkedLeaves l =
          Admission.buildGamma
            (Admission.buildPrune canon (tightenTable σ.table key) σ.metas
              σ.leaves σ.argsRaw σ.rawAtts σ.groups []).checkedLeaves l)
    (hcoveredRetained : ∀ resolved,
      RawAttack.resolveAttacks σ.argsRaw σ.rawAtts = .ok resolved →
      ∀ source,
      source ∈ (Admission.buildPrune canon (tightenTable σ.table key) σ.metas
        σ.leaves σ.argsRaw σ.rawAtts σ.groups resolved).keptArgs.map (·.2) →
      ∀ target,
      target ∈ (Admission.buildPrune canon (tightenTable σ.table key) σ.metas
        σ.leaves σ.argsRaw σ.rawAtts σ.groups resolved).keptArgs.map (·.2) →
      Compile.Covered
          (Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
            σ.rawAtts σ.groups resolved).keptAttacks source target →
        Compile.Covered
          (Admission.buildPrune canon (tightenTable σ.table key) σ.metas
            σ.leaves σ.argsRaw σ.rawAtts σ.groups resolved).keptAttacks
          source target) :
    ∃ σ', applyUpdate reg σ (.tighten key) = .ok σ' ∧ Accepted reg σ' := by
  rcases haccepted with ⟨declared, oldAdmission, oldChecked,
    holdAdmission, holdCheck⟩
  have holdAdmission' :
      Admission.evaluateAdmission canon σ.table σ.metas σ.leaves
        σ.argsRaw σ.rawAtts σ.groups declared = .accepted oldAdmission := by
    simpa [admissionFor] using holdAdmission
  have holdPrune :
      oldAdmission.prune =
        Admission.buildPrune canon σ.table σ.metas σ.leaves σ.argsRaw
          σ.rawAtts σ.groups declared.resolved :=
    Admission.accepted_prune_eq canon σ.table σ.metas σ.leaves σ.argsRaw
      σ.rawAtts σ.groups declared holdAdmission'
  have holdConditions :=
    Admission.evaluateAdmission_accepted_conditions holdAdmission'
  let admission : Admission.AdmissionResult :=
    { prune := Admission.buildPrune canon (tightenTable σ.table key) σ.metas
        σ.leaves σ.argsRaw σ.rawAtts σ.groups declared.resolved
    , declaredResolved := declared.resolved
    , audit := Admission.buildAdmissionAudit canon (tightenTable σ.table key)
        σ.metas σ.leaves σ.argsRaw σ.rawAtts σ.groups declared.resolved }
  have hadmission :
      Admission.evaluateAdmission canon (tightenTable σ.table key) σ.metas
        σ.leaves σ.argsRaw σ.rawAtts σ.groups declared =
          .accepted admission := by
    apply
      (Admission.evaluateAdmission_iff_judgment canon
        (tightenTable σ.table key) σ.metas σ.leaves σ.argsRaw σ.rawAtts
        σ.groups declared (.accepted admission)).mp
    exact Admission.AdmissionJudgment.accepted hrows.1 holdConditions.2.1
      holdConditions.2.2.1 hrows.2 rfl
  have hstructure :=
    Admission.more_restrictive_cannot_add_structure canon σ.metas σ.leaves
      σ.argsRaw σ.rawAtts σ.groups declared hrestrictive holdAdmission'
      hadmission
  have hargRowsSubset : ∀ row ∈ admission.prune.keptArgs,
      row ∈ oldAdmission.prune.keptArgs := hstructure.1
  have hattsSubset : ∀ current ∈ admission.prune.keptAttacks,
      current ∈ oldAdmission.prune.keptAttacks := hstructure.2.2.1
  have hargTermsSubset : ∀ term ∈ admission.prune.keptArgs.map (·.2),
      term ∈ oldAdmission.prune.keptArgs.map (·.2) := by
    intro term hterm
    obtain ⟨row, hrow, hrowTerm⟩ := List.mem_map.mp hterm
    exact List.mem_map.mpr ⟨row, hargRowsSubset row hrow, hrowTerm⟩
  have hargsSublist :
      admission.prune.keptArgs.Sublist oldAdmission.prune.keptArgs := by
    rw [holdPrune]
    change
      (σ.argsRaw.filter (Admission.buildPrune canon
        (tightenTable σ.table key) σ.metas σ.leaves σ.argsRaw σ.rawAtts
        σ.groups declared.resolved).keep).Sublist
      (σ.argsRaw.filter (Admission.buildPrune canon
        σ.table σ.metas σ.leaves σ.argsRaw σ.rawAtts σ.groups
        declared.resolved).keep)
    apply filter_sublist_filter_of_imp
    intro row hrow hkeep
    have hnewMem :
        row ∈ admission.prune.keptArgs := by
      exact List.mem_filter.mpr ⟨hrow, hkeep⟩
    have holdMem := hargRowsSubset row hnewMem
    rw [holdPrune] at holdMem
    exact (List.mem_filter.mp holdMem).2
  have hgammaTerm : ∀ term ∈ admission.prune.keptArgs.map (·.2),
      ∀ l, l ∈ Support.leaves term →
        Admission.buildGamma oldAdmission.prune.checkedLeaves l =
          Admission.buildGamma admission.prune.checkedLeaves l := by
    intro term hterm
    obtain ⟨row, hrow, hrowTerm⟩ := List.mem_map.mp hterm
    subst term
    intro l hl
    have hrowResolved :
        row ∈ (Admission.buildPrune canon (tightenTable σ.table key) σ.metas
          σ.leaves σ.argsRaw σ.rawAtts σ.groups
          declared.resolved).keptArgs := by
      simpa [admission] using hrow
    have hrowZero :
        row ∈ (Admission.buildPrune canon (tightenTable σ.table key) σ.metas
          σ.leaves σ.argsRaw σ.rawAtts σ.groups []).keptArgs := by
      simpa [Admission.buildPrune] using hrowResolved
    simpa [admission, holdPrune, Admission.buildPrune] using
      hgammaRetained row hrowZero l hl
  have holdSound := Check.Unit.checkUnit_sound holdCheck
  have hpolicyFacts := policy_facts_of_check holdCheck
  have hsignature :
      Check.Unit.signatureStage σ.ground
        { sigma := σ.sigma, policy := σ.policy
        , args := admission.prune.keptArgs.map (·.2)
        , atts := admission.prune.keptAttacks } = none := by
    have hold := holdSound.signature_ok
    have holdSorted :
        Lara.termsWellSorted σ.sigma σ.policy
          (oldAdmission.prune.keptArgs.map (·.2)) = true :=
      holdSound.raw_sorted
    have hnewSorted :
        Lara.argsWellSorted σ.sigma σ.policy
          (admission.prune.keptArgs.map (·.2)) = true := by
      unfold Lara.argsWellSorted
      exact termsWellSorted_of_subset holdSorted hargTermsSubset
    have hsigmaWf : Sigma.sigmaWellFormed σ.sigma = true :=
      Check.Unit.signatureStage_sigma_wf hold
    have hpolicySorted : Lara.policyWellSorted σ.sigma σ.policy = true :=
      Check.Unit.signatureStage_policy hold
    have hgroundSorted : Lara.groundWellSorted σ.sigma σ.ground = true :=
      Check.Unit.signatureStage_ground hold
    simp [Check.Unit.signatureStage, hsigmaWf, hpolicySorted,
      hgroundSorted, hnewSorted]
  have hargs : (admission.prune.keptArgs.map (·.2)).Nodup :=
    List.Nodup.sublist (List.Sublist.map (·.2) hargsSublist)
      holdSound.raw_nodup
  have hsupport : ∀ term ∈ admission.prune.keptArgs.map (·.2), ∃ C O,
      HasSupport canon σ.policy.ruleLookup
        (Admission.buildGamma admission.prune.checkedLeaves)
        (certOkOf reg) term C O := by
    intro term hterm
    obtain ⟨C, O, hold⟩ :=
      holdSound.raw_support term (hargTermsSubset term hterm)
    exact ⟨C, O, hasSupport_congr_gamma_on hold (hgammaTerm term hterm)⟩
  have hendpoints : ∀ current ∈ admission.prune.keptAttacks,
      current.source ∈ admission.prune.keptArgs.map (·.2) ∧
      current.target ∈ admission.prune.keptArgs.map (·.2) := by
    intro current hcurrent
    exact Admission.retained_semantic_attack_endpoints canon
      (tightenTable σ.table key) σ.metas σ.leaves σ.argsRaw σ.rawAtts
      σ.groups declared current hcurrent
  have hattackTyping : ∀ current ∈ admission.prune.keptAttacks,
      Attack.HasAttack canon σ.policy.ruleLookup
        (Admission.buildGamma admission.prune.checkedLeaves)
        (certOkOf reg) σ.policy.defeat current := by
    intro current hcurrent
    have hold := holdSound.raw_typed current (hattsSubset current hcurrent)
    have he := hendpoints current hcurrent
    exact hasAttack_congr_gamma_on_endpoints hold
      (hgammaTerm current.source he.1) (hgammaTerm current.target he.2)
  have hcoverage :
      Compile.AttackComplete canon σ.policy.ruleLookup
        (Admission.buildGamma admission.prune.checkedLeaves)
        (certOkOf reg) σ.policy.defeat
        (admission.prune.keptArgs.map (·.2))
        admission.prune.keptAttacks := by
    intro source hsource target htarget sourceConclusion targetConclusion
      hsourceSupport htargetSupport hcontrary hattackable
    have holdCoverage : Compile.AttackComplete canon σ.policy.ruleLookup
        (Admission.buildGamma oldAdmission.prune.checkedLeaves)
        (certOkOf reg) σ.policy.defeat
        (oldAdmission.prune.keptArgs.map (·.2))
        oldAdmission.prune.keptAttacks :=
      holdSound.raw_attack_complete
    have hsourceOld := hasSupport_congr_gamma_on hsourceSupport
      (fun l hl => (hgammaTerm source hsource l hl).symm)
    have htargetOld := hasSupport_congr_gamma_on htargetSupport
      (fun l hl => (hgammaTerm target htarget l hl).symm)
    have holdCovered :=
      holdCoverage source (hargTermsSubset source hsource)
        target (hargTermsSubset target htarget)
        sourceConclusion targetConclusion hsourceOld htargetOld hcontrary
        hattackable
    rw [holdPrune] at holdCovered
    exact hcoveredRetained declared.resolved declared.resolve_eq source hsource
      target htarget holdCovered
  obtain ⟨checked, hcheck⟩ :=
    Check.Unit.checkUnit_complete_holes hsignature
      hpolicyFacts.1 hpolicyFacts.2.1 hpolicyFacts.2.2
      hargs hsupport hattackTyping
      (fun current hcurrent => (hendpoints current hcurrent).1)
      (fun current hcurrent => (hendpoints current hcurrent).2)
      hcoverage
  let edited : SourceState :=
    { σ with table := tightenTable σ.table key }
  have hfinished := acceptEdited_of_results reg edited declared.ids_nodup
    declared admission checked hadmission hcheck
  refine ⟨edited, ?_, hfinished.2⟩
  simp only [applyUpdate]
  rw [(admittedAtB_iff σ key).mpr hadmitted]
  exact hfinished.1

private theorem acceptEdited_ok_target {canon : String → String}
    {reg : BackendRegistry canon} {edited target : SourceState}
    (h : acceptEdited reg edited = .ok target) :
    target = edited := by
  unfold acceptEdited at h
  split at h
  · split at h
    · contradiction
    · simp only at h
      split at h
      · contradiction
      · contradiction
      · split at h
        · contradiction
        · exact (Except.ok.inj h).symm
  · contradiction

private theorem applyUpdate_addLeaf_target {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {id : LeafId} {a : Atom} {m : Admission.LeafMeta}
    (h : applyUpdate reg source (.addLeaf id a m) = .ok target) :
    target =
      { source with metas := source.metas ++ [{ m with id := id }]
                    leaves := source.leaves ++ [(id, a)] } := by
  simp only [applyUpdate] at h
  split at h
  · exact acceptEdited_ok_target h
  · contradiction

private theorem applyUpdate_tighten_target {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {key : LeafKind × Provenance}
    (h : applyUpdate reg source (.tighten key) = .ok target) :
    target = { source with table := tightenTable source.table key } := by
  simp only [applyUpdate] at h
  split at h
  · exact acceptEdited_ok_target h
  · contradiction

private theorem applyUpdate_addAttack_target {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {raw : RawAttack.RawAttack}
    (h : applyUpdate reg source (.addAttack raw) = .ok target) :
    target = { source with rawAtts := source.rawAtts ++ [raw] } := by
  simp only [applyUpdate] at h
  split at h
  · exact acceptEdited_ok_target h
  · contradiction

private theorem applyUpdate_addInstance_target {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {name : String} {w : SupportTerm}
    (h : applyUpdate reg source (.addInstance name w) = .ok target) :
    target = { source with argsRaw := source.argsRaw ++ [(name, w)] } := by
  simp only [applyUpdate] at h
  split at h
  · exact acceptEdited_ok_target h
  · contradiction

/-- A successful revalidation is exactly an accepted run of the edited
state. -/
private theorem accepted_of_acceptEdited {canon : String → String}
    {reg : BackendRegistry canon} {edited target : SourceState}
    (h : acceptEdited reg edited = .ok target) :
    Accepted reg edited := by
  unfold acceptEdited at h
  split at h
  · rename_i hids
    split at h
    · contradiction
    · rename_i resolved hresolve
      simp only at h
      split at h
      · contradiction
      · contradiction
      · rename_i result hadmission
        split at h
        · contradiction
        · rename_i checked hcheck
          exact ⟨{ resolved := resolved, resolve_eq := hresolve, ids_nodup := hids },
            result, checked, hadmission, hcheck⟩
  · contradiction

private theorem acceptEdited_of_accepted {canon : String → String}
    {reg : BackendRegistry canon} {edited : SourceState}
    (h : Accepted reg edited) : acceptEdited reg edited = .ok edited := by
  obtain ⟨declared, admission, checked, hadmission, hcheck⟩ := h
  exact (acceptEdited_of_results reg edited declared.ids_nodup declared
    admission checked hadmission hcheck).1

/-- Revalidation returns the edited state exactly when it is accepted. -/
private theorem acceptEdited_ok_iff {canon : String → String}
    {reg : BackendRegistry canon} {edited target : SourceState} :
    acceptEdited reg edited = .ok target ↔ target = edited ∧ Accepted reg edited :=
  ⟨fun h => ⟨acceptEdited_ok_target h, accepted_of_acceptEdited h⟩,
    fun ⟨htarget, haccepted⟩ => by subst htarget; exact acceptEdited_of_accepted haccepted⟩

/-- **In-place discharge is a site check plus acceptance.** `dischargeOpen`
succeeds exactly when the site precondition holds and the source with the
discharged argument rewritten in place is `Accepted`; it then returns that
source. -/
theorem applyUpdate_dischargeOpen_ok_iff {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {name : String} {π : Attack.Pos} {q : QuestionId} {v : SupportTerm} :
    applyUpdate reg source (.dischargeOpen name π q v) = .ok target ↔
      DischargeOpen source name π q ∧
      target = { source with argsRaw := dischargeRows source.argsRaw name π q v } ∧
      Accepted reg { source with argsRaw := dischargeRows source.argsRaw name π q v } := by
  simp only [applyUpdate]
  by_cases hsite : dischargeOpenB source name π q = true
  · rw [if_pos hsite, acceptEdited_ok_iff]
    exact ⟨fun ⟨ht, ha⟩ => ⟨(dischargeOpenB_iff _ _ _ _).mp hsite, ht, ha⟩,
      fun ⟨_, ht, ha⟩ => ⟨ht, ha⟩⟩
  · rw [if_neg hsite]
    constructor
    · intro h; cases h
    · rintro ⟨hopen, _⟩
      exact absurd ((dischargeOpenB_iff _ _ _ _).mpr hopen) hsite

theorem applyUpdate_dischargeOpen_target {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {name : String} {π : Attack.Pos} {q : QuestionId} {v : SupportTerm}
    (h : applyUpdate reg source (.dischargeOpen name π q v) = .ok target) :
    target = { source with argsRaw := dischargeRows source.argsRaw name π q v } :=
  (applyUpdate_dischargeOpen_ok_iff.mp h).2.1

/-- **A batch is accepted iff its raw final state is.** An atomic batch
succeeds exactly when every raw edit's syntactic side condition holds against
the state the earlier edits produced and the final raw state is `Accepted`; it
then returns that final state. -/
theorem applyUpdate_atomic_ok_iff {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {edits : List AtomicEdit} :
    applyUpdate reg source (.atomic edits) = .ok target ↔
      applyBatch source edits = .ok target ∧ Accepted reg target := by
  simp only [applyUpdate]
  cases hbatch : applyBatch source edits with
  | error reason =>
      simp only
      constructor
      · intro h; cases h
      · rintro ⟨h, _⟩; cases h
  | ok edited =>
      simp only [acceptEdited_ok_iff, Except.ok.injEq]
      constructor
      · rintro ⟨rfl, ha⟩; exact ⟨rfl, ha⟩
      · rintro ⟨rfl, ha⟩; exact ⟨rfl, ha⟩

theorem applyUpdate_atomic_target {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {edits : List AtomicEdit}
    (h : applyUpdate reg source (.atomic edits) = .ok target) :
    applyBatch source edits = .ok target :=
  (applyUpdate_atomic_ok_iff.mp h).1

/-! ### Core observations and successful transitions -/

/-- Recompute the complete claim for `p` from an accepted checked unit and
observe its compiled framework under `sem`.  The atom is held fixed across an
update, rather than any support index: adding or pruning arguments shifts
declaration-order positions, so retaining old indices would observe the wrong
claim. -/
def coreObs (sem : Semantics.ExtensionSemantics)
    (unit : Lara.Unit.CheckedUnit canon Gamma CertOk) (p : Atom) :
    Semantics.ClaimObservation :=
  Semantics.observe sem (Compile.checkedAF unit.program)
    (Consistency.completeClaimFor unit p)

/-- The only belief-set projection used by the AGM probe.  It holds the atom
fixed and recomputes its support through `coreObs`; an atom belongs exactly
when the selected extension semantics observes it as justified. -/
def beliefSet (sem : Semantics.ExtensionSemantics)
    (unit : Lara.Unit.CheckedUnit canon Gamma CertOk) : Atom → Prop :=
  fun p => coreObs sem unit p = .observed .justified

/-- The semantics-indexed pair of core observations before and after an
update.  The checked units are explicit: theorems relating this pair to source
editing must supply the admission, checking, and successful-`applyUpdate`
witnesses that produced them, so no proof-dependent or stale checked value is
hidden in this computation. -/
def CoreTransition (sem : Semantics.ExtensionSemantics)
    (before : Lara.Unit.CheckedUnit canon Gamma₁ CertOk)
    (after : Lara.Unit.CheckedUnit canon Gamma₂ CertOk)
    (p : Atom) :
    Semantics.ClaimObservation × Semantics.ClaimObservation :=
  (coreObs sem before p, coreObs sem after p)

/-- Closed five-valued public report for M3.  `evidenceBlocked` deliberately
does not expose the conditional four-state diagnostic as a sixth public value. -/
inductive PublicReport where
  | gap
  | justified
  | contested
  | defeated
  | evidenceBlocked
deriving DecidableEq, Repr

/-- Embed an ordinary grounded status into the four non-blocked public values. -/
def PublicReport.ofStatus : Grounded.Status → PublicReport
  | .gap => .gap
  | .justified => .justified
  | .contested => .contested
  | .defeated => .defeated

/-- The four grounded public constructors remain distinct. -/
theorem PublicReport.ofStatus_injective :
    Function.Injective PublicReport.ofStatus := by
  intro left right equal
  cases left <;> cases right <;> simp_all [PublicReport.ofStatus]

/-- Stable wire spelling for the closed public report vocabulary. -/
def PublicReport.render : PublicReport → String
  | .gap => "gap"
  | .justified => "justified"
  | .contested => "contested"
  | .defeated => "defeated"
  | .evidenceBlocked => "evidence-blocked"

/-- Publication spelling for public-matrix axes.  This deliberately reuses the
paper vocabulary while `render` retains the stable wire spelling. -/
def PublicReport.publicationLabel : PublicReport → String
  | .gap => "gap"
  | .justified => "justified"
  | .contested => "both"
  | .defeated => "refuted"
  | .evidenceBlocked => "evidence-blocked"

/-- `K` for an accepted run: the declaration-order indices of its AF nodes,
read off the checked cache. Compact support index `k` names the declaration at
`(checkedCarrierForRun run)[k]?`; with holes present this is not the identity
even when nothing is quarantined. -/
abbrev checkedCarrierForRun (run : AcceptedRun reg state) : List Nat :=
  BlockedProgram.checkedCarrier run.checked run.admission.prune.keep
    state.argsRaw

/-- `D` for an accepted run: the production reference carrier under the full
declared leaf table, as `Driver` computes it. Retained declarations reuse the
checked cache; each quarantined declaration is classified once. -/
abbrev referenceCarrierForRun (run : AcceptedRun reg state) : List Nat :=
  BlockedProgram.referenceCarrier run.checked run.admission.prune.keep
    state.policy.ruleLookup (Admission.buildGamma state.leaves) reg
    state.argsRaw

/-- The specification reference carrier of a raw state: every declaration
except the typed holes under the full declared leaf table
(`BlockedProgram.notHole`). It reads the source material alone, so the two
ends of a `tighten` share it. -/
def declaredCarrier {canon : String → String} (reg : BackendRegistry canon)
    (state : SourceState) : List Nat :=
  BlockedProgram.retainedIndices
    (BlockedProgram.notHole state.policy.ruleLookup
      (Admission.buildGamma state.leaves) reg)
    state.argsRaw

/-- The exact production blocked-query computation for one accepted run, with
the checked cache as `done` and the production reference mask as `live`. -/
def blockedQueriesForRun (run : AcceptedRun reg state)
    (queries : List Atom) : List Atom :=
  let done := BlockedProgram.checkedDone run.checked
  BlockedProgram.blockedQueries run.admission.prune.keep done
    (BlockedProgram.referenceLive run.admission.prune.keep done
      state.policy.ruleLookup (Admission.buildGamma state.leaves) reg)
    state.argsRaw run.declared.resolved run.admission.prune.keptAttacks
    (fun p => Consistency.claimSupportFor run.checked p) queries

/-- The exact declared-index blocking seed for one accepted run.  Keeping this
run-specific helper explicit lets additive updates expose the seed independently
of the query fast path. -/
def blockedSeedForRun (run : AcceptedRun reg state) : List Nat :=
  BlockedProgram.blockedSeed state.argsRaw run.declared.resolved
    run.admission.prune.keptAttacks (referenceCarrierForRun run)
    (checkedCarrierForRun run)

/-- The exact declared-index blocked closure used by the non-fast public path
for one accepted run. -/
def blockedSetForRun (run : AcceptedRun reg state) : List Nat :=
  Blocked.blockedSet
    (BlockedProgram.declaredAF state.argsRaw run.declared.resolved
      (referenceCarrierForRun run))
    (blockedSeedForRun run)

/-- Conservative public report for a fixed atom.  The complete claim is
recomputed from the accepted checked unit; the blocking branch is the production
`BlockedProgram.blockedQueries` calculation, not a parallel approximation. -/
def publicReport (run : AcceptedRun reg state) (p : Atom) : PublicReport :=
  if p ∈ blockedQueriesForRun run [p] then
    .evidenceBlocked
  else
    .ofStatus (Grounded.statusC (Compile.checkedAF run.checked.program)
      (Consistency.completeClaimFor run.checked p))

/-- Empty recomputed complete support always publishes `gap`: the production
blocked-query predicate is false on an empty support list. -/
theorem publicReport_gap_of_empty_support (run : AcceptedRun reg state)
    (p : Atom)
    (hempty : Consistency.claimSupportFor run.checked p = []) :
    publicReport run p = .gap := by
  have hnot : p ∉ blockedQueriesForRun run [p] := by
    simp [blockedQueriesForRun, BlockedProgram.blockedQueries,
      BlockedProgram.blockedQueriesFor, BlockedProgram.supportBlocked, hempty]
  unfold publicReport
  rw [if_neg hnot]
  change PublicReport.ofStatus
      (Grounded.statusC (Compile.checkedAF run.checked.program)
        (Consistency.completeClaimFor run.checked p)) = .gap
  rw [(Grounded.statusC_gap_iff _ _).mpr hempty]
  rfl

/-- The public report pair for real accepted source and target runs.  Both sides
recompute the complete claim from the same atom, so neither support indices nor
`Grounded.Claim.holes` are transported across the update. -/
def PublicTransition (before : AcceptedRun reg source)
    (after : AcceptedRun reg target) (p : Atom) :
    PublicReport × PublicReport :=
  (publicReport before p, publicReport after p)

/-- The exact accepted source run is clean when its admission prune has no
policy- or group-quarantine seed.  This is stronger than a raw-state slogan and
is independent of any desired observation equality. -/
def CleanBase (run : AcceptedRun reg state) : Prop :=
  run.admission.prune.removedSeed = []


/-- The prune stored by an exact run is the canonical prune of that same source
state and declared attack alignment. -/
theorem AcceptedRun.prune_eq {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) :
    run.admission.prune =
      Admission.buildPrune canon state.table state.metas state.leaves
        state.argsRaw state.rawAtts state.groups run.declared.resolved :=
  Admission.accepted_prune_eq canon state.table state.metas state.leaves
    state.argsRaw state.rawAtts state.groups run.declared run.admission_ok

/-! #### Run-level views of the production blocking computation -/

/-- The kept arguments of a run are its raw-retained declarations. -/
private theorem AcceptedRun.keptArgs_eq {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) :
    run.admission.prune.keptArgs =
      BlockedProgram.retainedArguments run.admission.prune.keep
        state.argsRaw := by
  rw [run.prune_eq, BlockedProgram.retainedArguments_eq_filter]
  rfl

/-- The kept attacks of a run are the aligned selection of its resolved ones. -/
private theorem AcceptedRun.keptAttacks_eq {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) :
    run.admission.prune.keptAttacks =
      RawAttack.selectAligned run.admission.prune.keepAttack state.rawAtts
        run.declared.resolved := by
  rw [run.prune_eq]
  rfl

private theorem AcceptedRun.keptAttacks_subset {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) :
    ∀ k, k ∈ run.admission.prune.keptAttacks → k ∈ run.declared.resolved := by
  intro k hk
  rw [run.keptAttacks_eq] at hk
  exact BlockedProgram.selectAligned_subset _ _ _ k hk

/-- The run's checker call, with its argument list in retained-view form. -/
private theorem AcceptedRun.check_retained {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) :
    Check.Unit.checkUnit
      (Admission.buildGamma run.admission.prune.checkedLeaves) reg state.ground
      ({ sigma := state.sigma
       , policy := state.policy
       , args := (BlockedProgram.retainedArguments run.admission.prune.keep
           state.argsRaw).map (·.2)
       , atts := run.admission.prune.keptAttacks } : Lara.Unit) =
        .ok run.checked := by
  rw [← run.keptArgs_eq]
  exact run.check_ok

/-- The checked context agrees with the full declared one on every leaf of a
raw-retained declaration (`Admission.prune_gamma_agree`). -/
private theorem AcceptedRun.gamma_agree {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) :
    ∀ a, a ∈ state.argsRaw → run.admission.prune.keep a = true →
      ∀ l ∈ Support.leaves a.2,
        Admission.buildGamma run.admission.prune.checkedLeaves l =
          Admission.buildGamma state.leaves l := by
  intro a _ ha
  rw [run.prune_eq] at ha ⊢
  exact Admission.prune_gamma_agree canon state.table state.metas state.leaves
    state.argsRaw state.rawAtts state.groups run.declared.resolved a ha

/-- The production reference carrier is the specification carrier. -/
private theorem referenceCarrierForRun_eq {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) :
    referenceCarrierForRun run = declaredCarrier reg state :=
  BlockedProgram.referenceLive_indices_eq_notHole
    (Admission.buildGamma state.leaves) run.check_retained run.gamma_agree

/-- `K` has one entry per AF node. -/
private theorem checkedCarrierForRun_length {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) :
    (checkedCarrierForRun run).length = run.checked.program.args.length := by
  rw [BlockedProgram.checked_args_keepComplete run.check_retained,
    List.length_map, BlockedProgram.retained_lengths_eq]

/-- Every complete-support index of a run lifts along `K`. -/
private theorem claimSupportFor_lt_checkedCarrier {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) (p : Atom) :
    ∀ k, k ∈ Consistency.claimSupportFor run.checked p →
      k < (checkedCarrierForRun run).length := by
  intro k hk
  have hkC := BlockedProgram.claimSupportFor_mem_checkedAF
    (accepted := run.checked) k hk
  rw [checkedCarrierForRun_length]
  exact List.mem_range.mp hkC

/-- The facts a run with no argument prune supplies: raw retention keeps every
declaration and every resolved attack, so the production reference carrier is
`K`, the blocking seed is empty, and the compact AF embeds onto the declared
framework over `K`. With holes the embedding is not an equality: `K` skips the
holes' indices. -/
private structure NoPruneTransport {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) : Prop where
  keepAll : ∀ a, a ∈ state.argsRaw → run.admission.prune.keep a = true
  retainedArgs : run.admission.prune.keptArgs = state.argsRaw
  retainedIndices :
    BlockedProgram.retainedIndices run.admission.prune.keep state.argsRaw =
      List.range state.argsRaw.length
  retainedAttacks :
    run.admission.prune.keptAttacks = run.declared.resolved
  referenceCarrier : referenceCarrierForRun run = checkedCarrierForRun run
  blockedSeed : blockedSeedForRun run = []
  embedding :
    BlockedProgram.AFEmbedding (Compile.checkedAF run.checked.program)
      (BlockedProgram.declaredAF state.argsRaw run.declared.resolved
        (checkedCarrierForRun run))
      (fun k => (checkedCarrierForRun run)[k]?)

/-- The authoritative transport from no argument pruning to retained
declarations, endpoint-aligned attacks, the empty seed, and the onto embedding
of the checked framework. -/
private theorem noPruneTransport {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state)
    (hlen : state.argsRaw.length = run.admission.prune.keptArgs.length) :
    NoPruneTransport run := by
  have hkeep := run.keptArgs_eq
  have hretainedLen : state.argsRaw.length =
      (BlockedProgram.retainedArguments run.admission.prune.keep
        state.argsRaw).length :=
    hlen.trans (congrArg List.length hkeep)
  obtain ⟨hretained, hindices⟩ :=
    Admission.retained_identity_of_length_eq run.admission.prune.keep
      state.argsRaw hretainedLen
  have hall : ∀ a, a ∈ state.argsRaw → run.admission.prune.keep a = true := by
    rw [BlockedProgram.retainedArguments_eq_filter] at hretained
    exact List.filter_eq_self.mp hretained
  have hpruneArgs : run.admission.prune.keptArgs = state.argsRaw :=
    hkeep.trans hretained
  have hidsDef :
      run.admission.prune.keptIds =
        run.admission.prune.keptArgs.map (·.1) := by
    rw [run.prune_eq]
    rfl
  have hids :
      run.admission.prune.keptIds = state.argsRaw.map (·.1) := by
    rw [hidsDef, hpruneArgs]
  have hkeepAttackDef : ∀ raw, run.admission.prune.keepAttack raw =
      (decide (raw.endpoints.1 ∈ run.admission.prune.keptIds) &&
        decide (raw.endpoints.2 ∈ run.admission.prune.keptIds)) := by
    intro raw
    rw [run.prune_eq]
    rfl
  have hkeepRaw : ∀ raw, raw ∈ state.rawAtts →
      run.admission.prune.keepAttack raw = true := by
    intro raw hraw
    have hendpoints :=
      RawAttack.resolveAttacks_endpoints_mem state.argsRaw
        run.declared.resolve_eq raw hraw
    rw [hkeepAttackDef, hids]
    simp [hendpoints.1, hendpoints.2]
  have hrawFilter :
      state.rawAtts.filter run.admission.prune.keepAttack = state.rawAtts :=
    List.filter_eq_self.mpr hkeepRaw
  have hselected :
      RawAttack.selectAligned run.admission.prune.keepAttack state.rawAtts
          run.declared.resolved =
        run.declared.resolved := by
    have hcommute :=
      RawAttack.resolve_filter_commute state.argsRaw
        run.admission.prune.keepAttack run.declared.resolve_eq
    rw [hrawFilter, run.declared.resolve_eq] at hcommute
    injection hcommute with heq
    exact heq.symm
  have hpruneAtts :
      run.admission.prune.keptAttacks = run.declared.resolved :=
    run.keptAttacks_eq.trans hselected
  have hembedding :=
    BlockedProgram.compile_checkedAF_embedding run.checked.program
      (BlockedProgram.keepComplete run.admission.prune.keep
        (BlockedProgram.checkedDone run.checked))
      state.argsRaw run.admission.prune.keptAttacks
      (BlockedProgram.checked_args_keepComplete run.check_retained)
      (BlockedProgram.checked_atts_live run.check_ok)
  rw [hpruneAtts] at hembedding
  exact
    { keepAll := hall
    , retainedArgs := hpruneArgs
    , retainedIndices := hindices
    , retainedAttacks := hpruneAtts
    , referenceCarrier := BlockedProgram.referenceLive_indices_of_keep_all hall
    , blockedSeed := BlockedProgram.blockedSeed_eq_nil_of_keep_all hall hpruneAtts
    , embedding := hembedding }

/-- Absence from the production blocked-query list is the unblocked support
predicate over the run's own carriers, on both branches: with no argument
pruned the seed is empty, and otherwise the predicate is what the filter
tested. -/
private theorem unblocked_of_not_mem_blockedQueriesForRun
    {canon : String → String} {reg : BackendRegistry canon}
    {state : SourceState} (run : AcceptedRun reg state) (p : Atom)
    (hnot : p ∉ blockedQueriesForRun run [p]) :
    BlockedProgram.supportBlocked (checkedCarrierForRun run)
      (blockedSetForRun run) (Consistency.claimSupportFor run.checked p) =
        false := by
  by_cases hpruned : state.argsRaw.length = run.admission.prune.keptArgs.length
  · have transport := noPruneTransport run hpruned
    unfold blockedSetForRun
    rw [transport.blockedSeed, BlockedProgram.blockedSet_nil]
    exact BlockedProgram.supportBlocked_nil
      (claimSupportFor_lt_checkedCarrier run p)
  · rw [run.keptArgs_eq] at hpruned
    exact BlockedProgram.supportBlocked_false_of_not_mem_blockedQueries
      hpruned (List.mem_singleton_self p) hnot

/-- **Per-argument label agreement for an accepted run.** An unblocked
complete-support argument has the same grounded label in the compact checked
framework and, at its declared index, in the declared framework over the
specification carrier. -/
private theorem run_label_agree {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) (p : Atom)
    (hnot : p ∉ blockedQueriesForRun run [p])
    {a A : Nat} (ha : a ∈ Consistency.claimSupportFor run.checked p)
    (hA : (checkedCarrierForRun run)[a]? = some A) :
    Grounded.labelC (Compile.checkedAF run.checked.program) a =
      Grounded.labelC
        (BlockedProgram.declaredAF state.argsRaw run.declared.resolved
          (declaredCarrier reg state)) A := by
  rw [← referenceCarrierForRun_eq run]
  exact BlockedProgram.production_unblocked_label_agree run.checked
    run.admission.prune.keep _ (BlockedProgram.checkedDone run.checked)
    state.argsRaw run.declared.resolved run.admission.prune.keptAttacks p
    (BlockedProgram.checked_args_keepComplete run.check_retained)
    (BlockedProgram.checked_atts_live run.check_ok)
    run.keptAttacks_subset
    (fun _ _ h => BlockedProgram.referenceLive_of_keepComplete h)
    (unblocked_of_not_mem_blockedQueriesForRun run p hnot) ha hA

/-- **Run-level `justified` non-promotion.** A query that the run does not
block and whose compact status is `justified` stays `justified` in the
declared framework over the specification carrier. -/
private theorem checked_row_justified_nonpromotion
    {canon : String → String} {reg : BackendRegistry canon}
    {state : SourceState}
    (run : AcceptedRun reg state) (p : Atom)
    (hnot : p ∉ blockedQueriesForRun run [p])
    (hstatus : Grounded.statusC (Compile.checkedAF run.checked.program)
      (Consistency.completeClaimFor run.checked p) = .justified) :
    Grounded.statusC
      (BlockedProgram.declaredAF state.argsRaw run.declared.resolved
        (declaredCarrier reg state))
      (BlockedProgram.liftClaim (checkedCarrierForRun run)
        (Consistency.completeClaimFor run.checked p)) = .justified := by
  rw [← referenceCarrierForRun_eq run]
  exact BlockedProgram.production_justified_nonpromotion run.checked
    run.admission.prune.keep _ (BlockedProgram.checkedDone run.checked)
    state.argsRaw run.declared.resolved run.admission.prune.keptAttacks p
    (BlockedProgram.checked_args_keepComplete run.check_retained)
    (BlockedProgram.checked_atts_live run.check_ok)
    run.keptAttacks_subset
    (fun _ _ h => BlockedProgram.referenceLive_of_keepComplete h)
    (unblocked_of_not_mem_blockedQueriesForRun run p hnot) hstatus

/-! #### Clean runs -/

/-- A clean accepted run retains every raw argument in declaration order. -/
theorem keptArgs_eq_raw_of_clean {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) (hclean : CleanBase run) :
    run.admission.prune.keptArgs = state.argsRaw := by
  have hseed := hclean
  change run.admission.prune.removedSeed = [] at hseed
  rw [run.prune_eq] at hseed
  change
    Admission.policyQuarantineSeed state.table state.metas ++
      Groups.quarantined canon state.leaves state.groups = [] at hseed
  rw [run.prune_eq]
  change state.argsRaw.filter (fun row =>
    ! Groups.usesLeaf
      (Admission.policyQuarantineSeed state.table state.metas ++
        Groups.quarantined canon state.leaves state.groups) row.2) =
      state.argsRaw
  apply List.filter_eq_self.mpr
  intro row _
  rw [hseed]
  have hunused : Groups.usesLeaf [] row.2 = false := by
    apply Bool.eq_false_iff.mpr
    intro huses
    obtain ⟨leaf, _, impossible⟩ :=
      (usesLeaf_true_iff [] row.2).mp huses
    simp at impossible
  simp [hunused]

private theorem noPruneTransportOfClean {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) (hclean : CleanBase run) :
    NoPruneTransport run := by
  apply noPruneTransport run
  rw [keptArgs_eq_raw_of_clean run hclean]


/-- A clean accepted run takes the production no-prune fast path, so no query is
reported blocked. -/
theorem blockedQueriesForRun_eq_nil_of_clean {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) (hclean : CleanBase run)
    (queries : List Atom) :
    blockedQueriesForRun run queries = [] :=
  BlockedProgram.blockedQueries_eq_nil_of_keep_all
    (noPruneTransportOfClean run hclean).keepAll

/-- Under a clean exact run, conservative public reporting is definitionally the
embedded grounded core status. -/
theorem publicReport_eq_core_of_clean {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) (hclean : CleanBase run) (p : Atom) :
    publicReport run p =
      PublicReport.ofStatus
        (Grounded.statusC (Compile.checkedAF run.checked.program)
          (Consistency.completeClaimFor run.checked p)) := by
  have hblocked := blockedQueriesForRun_eq_nil_of_clean run hclean [p]
  unfold publicReport
  rw [hblocked]
  simp

/-- A clean run blocks no query. -/
private theorem not_mem_blockedQueriesForRun_of_clean {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) (hclean : CleanBase run) (p : Atom) :
    p ∉ blockedQueriesForRun run [p] := by
  rw [blockedQueriesForRun_eq_nil_of_clean run hclean]
  simp

/-- A clean accepted run retains every declaration index in canonical order. -/
theorem retainedIndices_eq_range_of_clean {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) (hclean : CleanBase run) :
    BlockedProgram.retainedIndices run.admission.prune.keep state.argsRaw =
      List.range state.argsRaw.length :=
  (noPruneTransportOfClean run hclean).retainedIndices

/-- A clean accepted run retains every resolved attack. -/
theorem keptAttacks_eq_resolved_of_clean {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) (hclean : CleanBase run) :
    run.admission.prune.keptAttacks = run.declared.resolved :=
  (noPruneTransportOfClean run hclean).retainedAttacks

/-- The checked program of a clean run has exactly the complete arguments of
the raw declarations, in declaration order, classified under the full declared
leaf table. The holes are the remaining declarations. -/
theorem checkedArgs_eq_raw_of_clean {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) (hclean : CleanBase run) :
    run.checked.program.args =
      Check.completeArgs state.policy.ruleLookup
        (Admission.buildGamma state.leaves) reg (state.argsRaw.map (·.2)) := by
  have transport := noPruneTransportOfClean run hclean
  have hargs : run.checked.program.args =
      Check.completeArgs state.policy.ruleLookup
        (Admission.buildGamma run.admission.prune.checkedLeaves) reg
        (run.admission.prune.keptArgs.map (·.2)) :=
    (Check.Unit.checkUnit_sound run.check_ok).args_eq
  rw [hargs, transport.retainedArgs]
  apply Check.completeArgs_congr
  intro w hw
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hw
  exact Check.argComplete_congr_gamma_on
    (run.gamma_agree row hrow (transport.keepAll row hrow))

/-- A clean accepted run's compiled framework is an onto embedding into its
declared framework over the specification carrier: nothing was pruned, and the
compact indices land on the complete declarations. With holes this is not an
equality, since the holes' indices are not nodes. -/
theorem checkedAF_embedding_of_clean {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) (hclean : CleanBase run) :
    BlockedProgram.AFEmbedding (Compile.checkedAF run.checked.program)
      (BlockedProgram.declaredAF state.argsRaw run.declared.resolved
        (declaredCarrier reg state))
      (fun k => (checkedCarrierForRun run)[k]?) := by
  have transport := noPruneTransportOfClean run hclean
  rw [← referenceCarrierForRun_eq run, transport.referenceCarrier]
  exact transport.embedding

/-- A clean accepted run has an empty declared-index blocking seed. -/
theorem blockedSeedForRun_eq_nil_of_clean {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) (hclean : CleanBase run) :
    blockedSeedForRun run = [] :=
  (noPruneTransportOfClean run hclean).blockedSeed

/-- Forward closure of an empty blocking seed remains empty. -/
theorem blockedSet_eq_nil_of_seed_nil (G : Grounded.AF) (seed : List Nat)
    (hseed : seed = []) :
    Blocked.blockedSet G seed = [] := by
  subst seed
  unfold Blocked.blockedSet
  generalize G.args.length = steps
  induction steps with
  | zero => simp [Blocked.closureIter]
  | succ steps ih =>
      simp [Blocked.closureIter, Blocked.closureStep, ih]

/-- A clean accepted run has an empty exact declared-index blocked closure. -/
theorem blockedSetForRun_eq_nil_of_clean {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state) (hclean : CleanBase run) :
    blockedSetForRun run = [] := by
  apply blockedSet_eq_nil_of_seed_nil
  exact blockedSeedForRun_eq_nil_of_clean run hclean

/-! #### Empty closures, checker accessors, and the no-prune embedding -/

/-- If the exact declared-index closure is empty, production cannot classify any
query as blocked.  Unlike the no-prune shortcut, the non-fast branch is
discharged from the explicit closure and the bound of every complete-support
index by the checked carrier `K`. -/
theorem blockedQueriesForRun_eq_nil_of_empty_closure {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state)
    (hclosure : blockedSetForRun run = []) (queries : List Atom) :
    blockedQueriesForRun run queries = [] := by
  unfold blockedQueriesForRun BlockedProgram.blockedQueries
  by_cases hfast :
      state.argsRaw.length ==
        (BlockedProgram.retainedArguments run.admission.prune.keep
          state.argsRaw).length
  · simp [hfast]
  · simp only [hfast, Bool.false_eq_true, if_false]
    change BlockedProgram.blockedQueriesFor (checkedCarrierForRun run)
      (blockedSetForRun run)
      (fun p => Consistency.claimSupportFor run.checked p) queries = []
    rw [hclosure]
    apply List.filter_eq_nil_iff.mpr
    intro p _
    simp [BlockedProgram.supportBlocked_nil
      (claimSupportFor_lt_checkedCarrier run p)]

/-- Empty exact closure is sufficient to identify public and core reports. -/
theorem publicReport_eq_core_of_empty_closure {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state)
    (hclosure : blockedSetForRun run = []) (p : Atom) :
    publicReport run p =
      PublicReport.ofStatus
        (Grounded.statusC (Compile.checkedAF run.checked.program)
          (Consistency.completeClaimFor run.checked p)) := by
  have hblocked :=
    blockedQueriesForRun_eq_nil_of_empty_closure run hclosure [p]
  unfold publicReport
  rw [hblocked]
  simp

/-- The checker's policy, and its AF arguments as the complete view of the
kept declarations. -/
private theorem checked_policy_args_of_acceptance {canon : String → String}
    {reg : BackendRegistry canon} {source : SourceState}
    {admission : Admission.AdmissionResult}
    {checked : Lara.Unit.CheckedUnit canon
      (checkedGamma admission) (certOkOf reg)}
    (hcheck : checkAccepted reg source admission = .ok checked) :
    checked.policy = source.policy ∧
      checked.program.args =
        Check.completeArgs source.policy.ruleLookup
          (Admission.buildGamma admission.prune.checkedLeaves) reg
          (admission.prune.keptArgs.map (·.2)) := by
  have hcheckSound := Check.Unit.checkUnit_sound hcheck
  exact ⟨hcheckSound.policy_eq, hcheckSound.args_eq⟩

/-- The checker's compiled attacks: the kept attacks whose source is one of its
AF arguments. -/
private theorem checked_atts_of_acceptance {canon : String → String}
    {reg : BackendRegistry canon} {source : SourceState}
    {admission : Admission.AdmissionResult}
    {checked : Lara.Unit.CheckedUnit canon
      (checkedGamma admission) (certOkOf reg)}
    (hcheck : checkAccepted reg source admission = .ok checked) :
    checked.program.atts =
      Check.liveAttacks checked.program.args admission.prune.keptAttacks :=
  (Check.Unit.checkUnit_sound hcheck).atts_eq

/-- The checker's AF arguments and holes: the complete and the hole views of the
kept declarations under the checked context. -/
private theorem checked_args_holes_of_acceptance {canon : String → String}
    {reg : BackendRegistry canon} {source : SourceState}
    {admission : Admission.AdmissionResult}
    {checked : Lara.Unit.CheckedUnit canon
      (checkedGamma admission) (certOkOf reg)}
    (hcheck : checkAccepted reg source admission = .ok checked) :
    checked.program.args =
        Check.completeArgs source.policy.ruleLookup (checkedGamma admission)
          reg (admission.prune.keptArgs.map (·.2)) ∧
      checked.program.holes =
        Check.holeArgs source.policy.ruleLookup (checkedGamma admission)
          reg (admission.prune.keptArgs.map (·.2)) :=
  let hs := Check.Unit.checkUnit_sound hcheck
  ⟨hs.args_eq, hs.holes_eq⟩

/-- If an exact admission run prunes no arguments, endpoint alignment also
prunes no attacks and the checked framework embeds onto the declared framework
over the specification carrier. -/
theorem checkedAF_embedding_of_no_arg_prune {canon : String → String}
    {reg : BackendRegistry canon} {state : SourceState}
    (run : AcceptedRun reg state)
    (hlen : state.argsRaw.length = run.admission.prune.keptArgs.length) :
    BlockedProgram.AFEmbedding (Compile.checkedAF run.checked.program)
      (BlockedProgram.declaredAF state.argsRaw run.declared.resolved
        (declaredCarrier reg state))
      (fun k => (checkedCarrierForRun run)[k]?) := by
  have transport := noPruneTransport run hlen
  rw [← referenceCarrierForRun_eq run, transport.referenceCarrier]
  exact transport.embedding

/-! #### Constructor transitions: support transport, gap rows, and public rows -/

private theorem claimSupportFor_nonempty_mono
    (source : Lara.Unit.CheckedUnit canon Gamma₁ CertOk)
    (target : Lara.Unit.CheckedUnit canon Gamma₂ CertOk)

    (hpolicy : source.policy = target.policy)
    (hterms : ∀ w ∈ source.program.args, w ∈ target.program.args)
    (hsupport : ∀ {w C}, w ∈ source.program.args →
      HasSupport canon source.policy.ruleLookup Gamma₁ CertOk w C [] →
      HasSupport canon source.policy.ruleLookup Gamma₂ CertOk w C [])
    (p : Atom)
    (hsource : Consistency.claimSupportFor source p ≠ []) :
    Consistency.claimSupportFor target p ≠ [] := by
  obtain ⟨i, hi⟩ :=
    List.exists_mem_of_ne_nil (Consistency.claimSupportFor source p) hsource
  obtain ⟨sourceNode, hsourceNode, hsourceConclusion⟩ :=
    (Consistency.mem_claimSupportFor_iff).mp hi
  obtain ⟨hiBound, hsourceAt⟩ := (List.getElem?_eq_some_iff).mp hsourceNode
  have hsourceMem : sourceNode ∈ source.nodes := by
    rw [← hsourceAt]
    exact List.getElem_mem hiBound
  have hsourceTerm : sourceNode.term ∈ source.program.args := by
    rw [← source.nodes_terms]
    exact List.mem_map.mpr ⟨sourceNode, hsourceMem, rfl⟩
  have htargetTerm := hterms sourceNode.term hsourceTerm
  rw [← target.nodes_terms] at htargetTerm
  obtain ⟨targetNode, htargetMem, htargetTermEq⟩ :=
    List.mem_map.mp htargetTerm
  have htargetValid :
      HasSupport canon source.policy.ruleLookup Gamma₂ CertOk
        targetNode.term targetNode.conclusion [] := by
    simpa only [hpolicy] using targetNode.valid
  have hsourceValid := hsupport hsourceTerm sourceNode.valid
  have hconclusion : sourceNode.conclusion = targetNode.conclusion := by
    exact (hasSupport_unique hsourceValid
      (by simpa [htargetTermEq] using htargetValid)).1
  obtain ⟨j, hjBound, htargetAt⟩ :=
    (List.mem_iff_getElem).mp htargetMem
  intro hempty
  have hj : j ∈ Consistency.claimSupportFor target p := by
    apply (Consistency.mem_claimSupportFor_iff).mpr
    refine ⟨targetNode, (List.getElem?_eq_some_iff).mpr
      ⟨hjBound, htargetAt⟩, ?_⟩
    exact hconclusion ▸ hsourceConclusion
  rw [hempty] at hj
  contradiction


/-- Adding an attack leaves the compiled argument carrier unchanged.  Hence an
unsupported source claim remains unsupported, and `gap` is fixed under every
extension semantics. -/
theorem addAttack_gap_fixed {canon : String → String}
    (sem : Semantics.ExtensionSemantics) (reg : BackendRegistry canon)
    (source target : SourceState) (p : Atom) (raw : RawAttack.RawAttack)
    (sourceDeclared :
      Admission.AlignedAttacks source.argsRaw source.rawAtts)
    (sourceAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetDeclared :
      Admission.AlignedAttacks target.argsRaw target.rawAtts)
    (targetAdmission : Admission.AdmissionResult)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg))
    (hsourceAdmission :
      admissionFor canon source sourceDeclared = .accepted sourceAdmission)
    (hsourceCheck :
      checkAccepted reg source sourceAdmission = .ok sourceChecked)
    (happly : applyUpdate reg source (.addAttack raw) = .ok target)
    (htargetAdmission :
      admissionFor canon target targetDeclared = .accepted targetAdmission)
    (htargetCheck :
      checkAccepted reg target targetAdmission = .ok targetChecked)
    (hgap :
      (CoreTransition sem sourceChecked targetChecked p).1 =
        .observed Grounded.Status.gap) :
    (CoreTransition sem sourceChecked targetChecked p).2 =
      .observed Grounded.Status.gap := by
  have htargetState := applyUpdate_addAttack_target happly
  subst target
  have hsourceSupport :
      Consistency.claimSupportFor sourceChecked p = [] := by
    apply (Semantics.observe_gap_iff sem
      (Compile.checkedAF sourceChecked.program)
      (Consistency.completeClaimFor sourceChecked p)).mp
    simpa only [CoreTransition, coreObs] using hgap
  have hsourcePrune := prune_eq_of_acceptance hsourceAdmission
  have htargetPrune := prune_eq_of_acceptance htargetAdmission
  have hsourceFields :=
    checked_policy_args_of_acceptance hsourceCheck
  have htargetFields :=
    checked_policy_args_of_acceptance htargetCheck
  have hpolicy : targetChecked.policy = sourceChecked.policy := by
    exact htargetFields.1.trans hsourceFields.1.symm
  have hargs : targetChecked.program.args = sourceChecked.program.args := by
    rw [htargetFields.2, hsourceFields.2, htargetPrune, hsourcePrune]
    rfl
  have hgamma : checkedGamma targetAdmission = checkedGamma sourceAdmission := by
    funext l
    simp only [checkedGamma, htargetPrune, hsourcePrune]
    rfl
  have htargetSupport :
      Consistency.claimSupportFor targetChecked p = [] := by
    by_cases hempty :
        Consistency.claimSupportFor targetChecked p = []
    · exact hempty
    · have hsourceNonempty :=
        claimSupportFor_nonempty_mono targetChecked sourceChecked hpolicy
          (fun w hw => by simpa only [hargs] using hw)
          (fun _ h => by simpa only [hgamma] using h) p hempty
      exact False.elim (hsourceNonempty hsourceSupport)
  simp only [CoreTransition]
  unfold coreObs
  apply Semantics.observe_gap
  exact htargetSupport


private theorem applyUpdate_addInstance_fresh {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {name : String} {w : SupportTerm}
    (h : applyUpdate reg source (.addInstance name w) = .ok target) :
    InstanceFresh source name w := by
  simp only [applyUpdate] at h
  split at h
  · rename_i hfresh
    exact (instanceFreshB_iff source name w).mp hfresh
  · contradiction

/-- Filtering the appended row through the prune and then through a test that
only typed terms pass is filtering `[w]` alone: a term the prune drops uses a
removed leaf, so it does not type under the checked context. -/
private theorem filter_keep_singleton {canon : String → String}
    {reg : BackendRegistry canon} {source : SourceState}
    {declared : Admission.AlignedAttacks source.argsRaw source.rawAtts}
    {admission : Admission.AdmissionResult}
    (hadmission : admissionFor canon source declared = .accepted admission)
    (name : String) (w : SupportTerm) (f : SupportTerm → Bool)
    (hf : f w = true → ∃ C O, HasSupport canon source.policy.ruleLookup
      (Admission.buildGamma admission.prune.checkedLeaves) (certOkOf reg)
      w C O) :
    (([(name, w)].filter admission.prune.keep).map (·.2)).filter f =
      [w].filter f := by
  cases hkeep : admission.prune.keep (name, w) with
  | true => simp [hkeep]
  | false =>
      cases hfw : f w with
      | false => simp [hkeep, hfw]
      | true =>
          exfalso
          obtain ⟨C, O, hC⟩ := hf hfw
          have hprune := prune_eq_of_acceptance hadmission
          rw [hprune] at hC hkeep
          have huses := hasSupport_not_uses_prune_seed source.table
            source.metas source.leaves source.argsRaw source.rawAtts
            source.groups declared.resolved hC
          simp [Admission.buildPrune, huses] at hkeep

/-- What a successful `addInstance` changes in the checked unit: the AF
arguments and the holes each gain at most the new term, classified under the
unchanged checked context, and the compiled attacks are unchanged because the
new name and term are fresh. -/
private structure AddInstanceTransport {canon : String → String}
    (reg : BackendRegistry canon) (source : SourceState) (w : SupportTerm)
    (sourceAdmission targetAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg)) : Prop where
  policy_eq : targetChecked.policy = sourceChecked.policy
  gamma_eq : checkedGamma targetAdmission = checkedGamma sourceAdmission
  args_eq : targetChecked.program.args = sourceChecked.program.args ++
    Check.completeArgs source.policy.ruleLookup (checkedGamma sourceAdmission)
      reg [w]
  holes_eq : targetChecked.program.holes = sourceChecked.program.holes ++
    Check.holeArgs source.policy.ruleLookup (checkedGamma sourceAdmission)
      reg [w]
  atts_eq : targetChecked.program.atts = sourceChecked.program.atts
  fresh : w ∉ sourceChecked.program.args

private theorem addInstance_transport {canon : String → String}
    (reg : BackendRegistry canon) (source target : SourceState)
    (name : String) (w : SupportTerm)
    (sourceDeclared :
      Admission.AlignedAttacks source.argsRaw source.rawAtts)
    (sourceAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetDeclared :
      Admission.AlignedAttacks target.argsRaw target.rawAtts)
    (targetAdmission : Admission.AdmissionResult)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg))
    (hsourceAdmission :
      admissionFor canon source sourceDeclared = .accepted sourceAdmission)
    (hsourceCheck :
      checkAccepted reg source sourceAdmission = .ok sourceChecked)
    (happly : applyUpdate reg source (.addInstance name w) = .ok target)
    (htargetAdmission :
      admissionFor canon target targetDeclared = .accepted targetAdmission)
    (htargetCheck :
      checkAccepted reg target targetAdmission = .ok targetChecked)
    (hfresh : InstanceFresh source name w) :
    AddInstanceTransport reg source w sourceAdmission targetAdmission
      sourceChecked targetChecked := by
  have htargetState := applyUpdate_addInstance_target happly
  subst target
  have hsourcePrune := prune_eq_of_acceptance hsourceAdmission
  have htargetPrune := prune_eq_of_acceptance htargetAdmission
  have hsourceSound := Check.Unit.checkUnit_sound hsourceCheck
  have htargetSound := Check.Unit.checkUnit_sound htargetCheck
  have hresolved :
      targetDeclared.resolved = sourceDeclared.resolved := by
    have hextended :
        RawAttack.resolveAttacks (source.argsRaw ++ [(name, w)])
          source.rawAtts = .ok sourceDeclared.resolved :=
      RawAttack.resolveAttacks_mono_lookup source.argsRaw
        (source.argsRaw ++ [(name, w)])
        (fun _ _ h => RawAttack.lookupArg_append_of_some
          source.argsRaw [(name, w)] h)
        sourceDeclared.resolve_eq
    exact Except.ok.inj (targetDeclared.resolve_eq.symm.trans hextended)
  have hgamma :
      checkedGamma targetAdmission = checkedGamma sourceAdmission := by
    funext l
    simp only [checkedGamma, htargetPrune, hsourcePrune, Admission.buildPrune]
  have hkept :
      targetAdmission.prune.keptArgs.map (·.2) =
        sourceAdmission.prune.keptArgs.map (·.2) ++
          ([(name, w)].filter sourceAdmission.prune.keep).map (·.2) := by
    rw [htargetPrune, hsourcePrune]
    simp only [Admission.buildPrune, List.filter_append, List.map_append]
  have hkeptRaw : ∀ term ∈ sourceAdmission.prune.keptArgs.map (·.2),
      term ≠ w := by
    intro term hterm heq
    obtain ⟨row, hrow, hrowTerm⟩ := List.mem_map.mp hterm
    rw [hsourcePrune] at hrow
    exact hfresh.2 row (List.mem_filter.mp hrow).1 (hrowTerm.trans heq)
  have hkeptIds : ∀ x, x ≠ name →
      (x ∈ (Admission.buildPrune canon source.table source.metas
          source.leaves (source.argsRaw ++ [(name, w)]) source.rawAtts
          source.groups sourceDeclared.resolved).keptIds ↔
        x ∈ (Admission.buildPrune canon source.table source.metas
          source.leaves source.argsRaw source.rawAtts source.groups
          sourceDeclared.resolved).keptIds) := by
    intro x hx
    simp only [Admission.buildPrune, List.filter_append, List.map_append,
      List.mem_append]
    constructor
    · rintro (h | h)
      · exact h
      · exfalso
        obtain ⟨row, hrow, hrowId⟩ := List.mem_map.mp h
        have hrowEq : row = (name, w) := by
          simpa using (List.mem_filter.mp hrow).1
        subst row
        exact hx hrowId.symm
    · exact Or.inl
  have hprunedAtts :
      (Admission.buildPrune canon source.table source.metas source.leaves
        (source.argsRaw ++ [(name, w)]) source.rawAtts source.groups
        sourceDeclared.resolved).keptAttacks =
      (Admission.buildPrune canon source.table source.metas source.leaves
        source.argsRaw source.rawAtts source.groups
        sourceDeclared.resolved).keptAttacks := by
    apply RawAttack.selectAligned_congr_on
    intro current hcurrent
    have hendpointNames :=
      RawAttack.resolveAttacks_endpoints_mem source.argsRaw
        sourceDeclared.resolve_eq current hcurrent
    have hsourceNe : current.endpoints.1 ≠ name := by
      intro heq
      obtain ⟨row, hrow, hid⟩ := List.mem_map.mp hendpointNames.1
      exact hfresh.1 row hrow (hid.trans heq)
    have htargetNe : current.endpoints.2 ≠ name := by
      intro heq
      obtain ⟨row, hrow, hid⟩ := List.mem_map.mp hendpointNames.2
      exact hfresh.1 row hrow (hid.trans heq)
    change
      (decide (current.endpoints.1 ∈
          (Admission.buildPrune canon source.table source.metas source.leaves
            (source.argsRaw ++ [(name, w)]) source.rawAtts source.groups
            sourceDeclared.resolved).keptIds) &&
        decide (current.endpoints.2 ∈
          (Admission.buildPrune canon source.table source.metas source.leaves
            (source.argsRaw ++ [(name, w)]) source.rawAtts source.groups
            sourceDeclared.resolved).keptIds)) =
      (decide (current.endpoints.1 ∈
          (Admission.buildPrune canon source.table source.metas source.leaves
            source.argsRaw source.rawAtts source.groups
            sourceDeclared.resolved).keptIds) &&
        decide (current.endpoints.2 ∈
          (Admission.buildPrune canon source.table source.metas source.leaves
            source.argsRaw source.rawAtts source.groups
            sourceDeclared.resolved).keptIds))
    simp only [hkeptIds _ hsourceNe, hkeptIds _ htargetNe]
  have hkeptAtts :
      targetAdmission.prune.keptAttacks = sourceAdmission.prune.keptAttacks := by
    rw [htargetPrune, hsourcePrune, hresolved]
    exact hprunedAtts
  obtain ⟨hsourceArgs, hsourceHoles⟩ :=
    checked_args_holes_of_acceptance hsourceCheck
  obtain ⟨htargetArgs, htargetHoles⟩ :=
    checked_args_holes_of_acceptance htargetCheck
  dsimp only at htargetArgs htargetHoles
  have hargs : targetChecked.program.args = sourceChecked.program.args ++
      Check.completeArgs source.policy.ruleLookup
        (checkedGamma sourceAdmission) reg [w] := by
    rw [htargetArgs, hgamma, hkept, Check.completeArgs_append, ← hsourceArgs]
    congr 1
    exact filter_keep_singleton hsourceAdmission name w _ (fun h =>
      let ⟨C, hC⟩ := Check.argComplete_iff.mp h; ⟨C, [], hC⟩)
  have hholes : targetChecked.program.holes = sourceChecked.program.holes ++
      Check.holeArgs source.policy.ruleLookup
        (checkedGamma sourceAdmission) reg [w] := by
    rw [htargetHoles, hgamma, hkept, Check.holeArgs_append, ← hsourceHoles]
    congr 1
    exact filter_keep_singleton hsourceAdmission name w _ (fun h =>
      let ⟨C, O, hC, _⟩ := Check.argHole_iff.mp h; ⟨C, O, hC⟩)
  have hnotSource : w ∉ sourceChecked.program.args := by
    intro hw
    rw [hsourceArgs] at hw
    exact hkeptRaw w (Check.completeArgs_subset hw) rfl
  have hatts : targetChecked.program.atts = sourceChecked.program.atts := by
    rw [htargetSound.atts_eq, hsourceSound.atts_eq]
    change Check.liveAttacks targetChecked.program.args
        targetAdmission.prune.keptAttacks =
      Check.liveAttacks sourceChecked.program.args
        sourceAdmission.prune.keptAttacks
    rw [hkeptAtts, hargs]
    apply Check.liveAttacks_congr
    intro k hk
    have hkSource : k.source ∈ sourceAdmission.prune.keptArgs.map (·.2) :=
      hsourceSound.raw_source k hk
    constructor
    · intro hmem
      rcases List.mem_append.mp hmem with hold | hnew
      · exact hold
      · exact absurd (List.mem_singleton.mp (Check.completeArgs_subset hnew))
          (hkeptRaw k.source hkSource)
    · exact fun hmem => List.mem_append.mpr (Or.inl hmem)
  exact
    { policy_eq := htargetSound.policy_eq.trans hsourceSound.policy_eq.symm
    , gamma_eq := hgamma
    , args_eq := hargs
    , holes_eq := hholes
    , atts_eq := hatts
    , fresh := hnotSource }

private theorem addInstance_no_gap_entry {canon : String → String}
    (sem : Semantics.ExtensionSemantics) (reg : BackendRegistry canon)
    (source target : SourceState) (p : Atom) (name : String) (w : SupportTerm)
    (sourceDeclared :
      Admission.AlignedAttacks source.argsRaw source.rawAtts)
    (sourceAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetDeclared :
      Admission.AlignedAttacks target.argsRaw target.rawAtts)
    (targetAdmission : Admission.AdmissionResult)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg))
    (hsourceAdmission :
      admissionFor canon source sourceDeclared = .accepted sourceAdmission)
    (hsourceCheck :
      checkAccepted reg source sourceAdmission = .ok sourceChecked)
    (happly : applyUpdate reg source (.addInstance name w) = .ok target)
    (htargetAdmission :
      admissionFor canon target targetDeclared = .accepted targetAdmission)
    (htargetCheck :
      checkAccepted reg target targetAdmission = .ok targetChecked)
    (hsourceNotGap :
      (CoreTransition sem sourceChecked targetChecked p).1 ≠
        .observed Grounded.Status.gap) :
    (CoreTransition sem sourceChecked targetChecked p).2 ≠
      .observed Grounded.Status.gap := by
  have htransport :=
    addInstance_transport reg source target name w sourceDeclared
      sourceAdmission sourceChecked targetDeclared targetAdmission
      targetChecked hsourceAdmission hsourceCheck happly htargetAdmission
      htargetCheck (applyUpdate_addInstance_fresh happly)
  have hsourceSupport :
      Consistency.claimSupportFor sourceChecked p ≠ [] := by
    intro hempty
    apply hsourceNotGap
    simp only [CoreTransition]
    unfold coreObs
    exact Semantics.observe_gap sem (Compile.checkedAF sourceChecked.program)
      (Consistency.completeClaimFor sourceChecked p) hempty
  have hpolicy := htransport.policy_eq.symm
  have hterms :
      ∀ term ∈ sourceChecked.program.args,
        term ∈ targetChecked.program.args := by
    intro term hterm
    rw [htransport.args_eq]
    exact List.mem_append.mpr (Or.inl hterm)
  have hgamma := htransport.gamma_eq.symm
  have htargetSupport :=
    claimSupportFor_nonempty_mono sourceChecked targetChecked hpolicy hterms
      (fun _ h => by simpa only [hgamma] using h) p hsourceSupport
  intro htargetGap
  have hempty :
      Consistency.claimSupportFor targetChecked p = [] := by
    apply (Semantics.observe_gap_iff sem
      (Compile.checkedAF targetChecked.program)
      (Consistency.completeClaimFor targetChecked p)).mp
    simpa only [CoreTransition, coreObs] using htargetGap
  exact htargetSupport hempty


private structure AddLeafTransport {canon : String → String}
    (sourceAdmission targetAdmission : Admission.AdmissionResult)
    (id : LeafId) (a : Atom)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) CertOk)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) CertOk) : Prop where
  policy_eq : sourceChecked.policy = targetChecked.policy
  args_eq : sourceChecked.program.args = targetChecked.program.args
  checkedLeaves_eq :
    targetAdmission.prune.checkedLeaves =
      sourceAdmission.prune.checkedLeaves ++ [(id, a)]
  gamma_mono : ∀ l q,
    checkedGamma sourceAdmission l = some q →
    checkedGamma targetAdmission l = some q
  atts_eq : sourceChecked.program.atts = targetChecked.program.atts
  kept_eq : targetAdmission.prune.keptArgs = sourceAdmission.prune.keptArgs
  gamma_on : ∀ w ∈ sourceAdmission.prune.keptArgs.map (·.2),
    ∀ l ∈ Support.leaves w,
      checkedGamma sourceAdmission l = checkedGamma targetAdmission l
  holes_eq : sourceChecked.program.holes = targetChecked.program.holes


private theorem addLeaf_transport {canon : String → String}
    (reg : BackendRegistry canon) (source target : SourceState)
    (id : LeafId) (a : Atom) (m : Admission.LeafMeta)
    (sourceDeclared :
      Admission.AlignedAttacks source.argsRaw source.rawAtts)
    (sourceAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetDeclared :
      Admission.AlignedAttacks target.argsRaw target.rawAtts)
    (targetAdmission : Admission.AdmissionResult)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg))
    (hsourceAdmission :
      admissionFor canon source sourceDeclared = .accepted sourceAdmission)
    (hsourceCheck :
      checkAccepted reg source sourceAdmission = .ok sourceChecked)
    (happly : applyUpdate reg source (.addLeaf id a m) = .ok target)
    (htargetAdmission :
      admissionFor canon target targetDeclared = .accepted targetAdmission)
    (htargetCheck :
      checkAccepted reg target targetAdmission = .ok targetChecked)
    (hfresh : AddLeafFresh source id)
    (hadmit :
      Admission.decisionFor source.table m.kind m.provenance = .admit) :
    AddLeafTransport sourceAdmission targetAdmission id a sourceChecked
      targetChecked := by
  have htargetState := applyUpdate_addLeaf_target happly
  subst target
  have hsourcePrune := prune_eq_of_acceptance hsourceAdmission
  have htargetPrune := prune_eq_of_acceptance htargetAdmission
  have hpolicySeed :
      Admission.policyQuarantineSeed source.table
          (source.metas ++ [{ m with id := id }]) =
        Admission.policyQuarantineSeed source.table source.metas := by
    simp [Admission.policyQuarantineSeed, List.filterMap_append, hadmit]
  have hgroupSeed :
      Groups.quarantined canon (source.leaves ++ [(id, a)]) source.groups =
        Groups.quarantined canon source.leaves source.groups :=
    quarantined_append_fresh canon source.leaves id a source.groups hfresh.2.2
  have hsourceSound := Check.Unit.checkUnit_sound hsourceCheck
  have htargetSound := Check.Unit.checkUnit_sound htargetCheck
  have hkept :
      targetAdmission.prune.keptArgs = sourceAdmission.prune.keptArgs := by
    rw [hsourcePrune, htargetPrune]
    change
      (source.argsRaw.filter (fun row => !Groups.usesLeaf
        (Admission.policyQuarantineSeed source.table
            (source.metas ++ [{ m with id := id }]) ++
          Groups.quarantined canon (source.leaves ++ [(id, a)])
            source.groups) row.2)) =
      source.argsRaw.filter (fun row => !Groups.usesLeaf
        (Admission.policyQuarantineSeed source.table source.metas ++
          Groups.quarantined canon source.leaves source.groups) row.2)
    rw [hpolicySeed, hgroupSeed]
  have hchecked :
      targetAdmission.prune.checkedLeaves =
        sourceAdmission.prune.checkedLeaves ++ [(id, a)] := by
    rw [hsourcePrune, htargetPrune]
    change
      Admission.checkedLeafTable canon source.table
          (source.metas ++ [{ m with id := id }])
          (source.leaves ++ [(id, a)]) source.groups =
        Admission.checkedLeafTable canon source.table source.metas
            source.leaves source.groups ++ [(id, a)]
    have hnotPolicy :
        id ∉ Admission.policyQuarantineSeed source.table source.metas := by
      intro hmem
      obtain ⟨oldMeta, hmeta, hmetaId, _⟩ :=
        (Admission.mem_policyQuarantineSeed_iff source.table source.metas id).mp
          hmem
      exact hfresh.2.1 oldMeta hmeta hmetaId
    have hnotGroup :
        id ∉ Groups.quarantined canon source.leaves source.groups := by
      intro hmem
      obtain ⟨group, hgroup, _, hmember⟩ :=
        (Groups.mem_quarantined_iff canon source.leaves source.groups id).mp
          hmem
      exact hfresh.2.2 group hgroup id hmember rfl
    unfold Admission.checkedLeafTable
    rw [hpolicySeed, hgroupSeed]
    simp [Groups.quarantineLeaves, List.filter_append, hnotPolicy, hnotGroup]
  have hgammaExt : ∀ l q,
      checkedGamma sourceAdmission l = some q →
      checkedGamma targetAdmission l = some q := by
    intro l q hq
    simp only [checkedGamma] at hq ⊢
    rw [hchecked]
    exact Admission.buildGamma_append_of_some sourceAdmission.prune.checkedLeaves
      [(id, a)] hq
  have hgammaOn : ∀ w ∈ sourceAdmission.prune.keptArgs.map (·.2),
      ∀ l ∈ Support.leaves w,
        checkedGamma sourceAdmission l = checkedGamma targetAdmission l := by
    intro w hw l hl
    obtain ⟨C, O, hsupport⟩ := hsourceSound.raw_support w hw
    obtain ⟨q, hq⟩ := Support.leaves_declared hsupport l hl
    rw [hq, hgammaExt l q hq]
  obtain ⟨hsourceArgs, hsourceHoles⟩ :=
    checked_args_holes_of_acceptance hsourceCheck
  obtain ⟨htargetArgs, htargetHoles⟩ :=
    checked_args_holes_of_acceptance htargetCheck
  dsimp only at htargetArgs htargetHoles
  have hargs : sourceChecked.program.args = targetChecked.program.args := by
    rw [hsourceArgs, htargetArgs, hkept]
    exact Check.completeArgs_congr fun w hw =>
      Check.argComplete_congr_gamma_on (hgammaOn w hw)
  have hholes : sourceChecked.program.holes = targetChecked.program.holes := by
    rw [hsourceHoles, htargetHoles, hkept]
    exact List.filter_congr fun w hw =>
      Check.argHole_congr_gamma_on (hgammaOn w hw)
  have hresolved :
      sourceDeclared.resolved = targetDeclared.resolved :=
    Except.ok.inj
      (sourceDeclared.resolve_eq.symm.trans targetDeclared.resolve_eq)
  have hkeptAtts :
      sourceAdmission.prune.keptAttacks = targetAdmission.prune.keptAttacks := by
    rw [hsourcePrune, htargetPrune]
    simp only [Admission.buildPrune]
    rw [hpolicySeed, hgroupSeed, hresolved]
  have hatts : sourceChecked.program.atts = targetChecked.program.atts := by
    rw [checked_atts_of_acceptance hsourceCheck,
      checked_atts_of_acceptance htargetCheck, hargs, hkeptAtts]
  exact
    { policy_eq := hsourceSound.policy_eq.trans htargetSound.policy_eq.symm
    , args_eq := hargs
    , checkedLeaves_eq := hchecked
    , gamma_mono := hgammaExt
    , atts_eq := hatts
    , kept_eq := hkept
    , gamma_on := hgammaOn
    , holes_eq := hholes }

private theorem addLeaf_no_gap_entry {canon : String → String}
    (sem : Semantics.ExtensionSemantics) (reg : BackendRegistry canon)
    (source target : SourceState) (p : Atom)
    (id : LeafId) (a : Atom) (m : Admission.LeafMeta)
    (sourceDeclared :
      Admission.AlignedAttacks source.argsRaw source.rawAtts)
    (sourceAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetDeclared :
      Admission.AlignedAttacks target.argsRaw target.rawAtts)
    (targetAdmission : Admission.AdmissionResult)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg))
    (hsourceAdmission :
      admissionFor canon source sourceDeclared = .accepted sourceAdmission)
    (hsourceCheck :
      checkAccepted reg source sourceAdmission = .ok sourceChecked)
    (happly : applyUpdate reg source (.addLeaf id a m) = .ok target)
    (htargetAdmission :
      admissionFor canon target targetDeclared = .accepted targetAdmission)
    (htargetCheck :
      checkAccepted reg target targetAdmission = .ok targetChecked)
    (hfresh : AddLeafFresh source id)
    (hadmit :
      Admission.decisionFor source.table m.kind m.provenance = .admit)
    (hsourceNotGap :
      (CoreTransition sem sourceChecked targetChecked p).1 ≠
        .observed Grounded.Status.gap) :
    (CoreTransition sem sourceChecked targetChecked p).2 ≠
      .observed Grounded.Status.gap := by
  have htransport :=
    addLeaf_transport reg source target id a m sourceDeclared sourceAdmission
      sourceChecked targetDeclared targetAdmission targetChecked
      hsourceAdmission hsourceCheck happly htargetAdmission htargetCheck hfresh
      hadmit
  have hsourceSupport :
      Consistency.claimSupportFor sourceChecked p ≠ [] := by
    intro hempty
    apply hsourceNotGap
    simp only [CoreTransition]
    unfold coreObs
    exact Semantics.observe_gap sem (Compile.checkedAF sourceChecked.program)
      (Consistency.completeClaimFor sourceChecked p) hempty
  have htargetSupport :=
    claimSupportFor_nonempty_mono sourceChecked targetChecked
      htransport.policy_eq
      (fun term hterm => by simpa only [htransport.args_eq] using hterm)
      (fun _ h => hasSupport_mono_gamma htransport.gamma_mono h) p hsourceSupport
  intro htargetGap
  have hempty :
      Consistency.claimSupportFor targetChecked p = [] := by
    apply (Semantics.observe_gap_iff sem
      (Compile.checkedAF targetChecked.program)
      (Consistency.completeClaimFor targetChecked p)).mp
    simpa only [CoreTransition, coreObs] using htargetGap
  exact htargetSupport hempty


private theorem addAttack_no_gap_entry {canon : String → String}
    (sem : Semantics.ExtensionSemantics) (reg : BackendRegistry canon)
    (source target : SourceState) (p : Atom) (raw : RawAttack.RawAttack)
    (sourceDeclared :
      Admission.AlignedAttacks source.argsRaw source.rawAtts)
    (sourceAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetDeclared :
      Admission.AlignedAttacks target.argsRaw target.rawAtts)
    (targetAdmission : Admission.AdmissionResult)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg))
    (hsourceAdmission :
      admissionFor canon source sourceDeclared = .accepted sourceAdmission)
    (hsourceCheck :
      checkAccepted reg source sourceAdmission = .ok sourceChecked)
    (happly : applyUpdate reg source (.addAttack raw) = .ok target)
    (htargetAdmission :
      admissionFor canon target targetDeclared = .accepted targetAdmission)
    (htargetCheck :
      checkAccepted reg target targetAdmission = .ok targetChecked)
    (hsourceNotGap :
      (CoreTransition sem sourceChecked targetChecked p).1 ≠
        .observed Grounded.Status.gap) :
    (CoreTransition sem sourceChecked targetChecked p).2 ≠
      .observed Grounded.Status.gap := by
  have htargetState := applyUpdate_addAttack_target happly
  subst target
  have hsourcePrune := prune_eq_of_acceptance hsourceAdmission
  have htargetPrune := prune_eq_of_acceptance htargetAdmission
  have hsourceFields :=
    checked_policy_args_of_acceptance hsourceCheck
  have htargetFields :=
    checked_policy_args_of_acceptance htargetCheck
  have hpolicy : sourceChecked.policy = targetChecked.policy := by
    exact hsourceFields.1.trans htargetFields.1.symm
  have hargs : sourceChecked.program.args = targetChecked.program.args := by
    rw [hsourceFields.2, htargetFields.2, hsourcePrune, htargetPrune]
    rfl
  have hgamma : checkedGamma sourceAdmission = checkedGamma targetAdmission := by
    funext l
    simp only [checkedGamma, hsourcePrune, htargetPrune]
    rfl
  have hsourceSupport :
      Consistency.claimSupportFor sourceChecked p ≠ [] := by
    intro hempty
    apply hsourceNotGap
    simp only [CoreTransition]
    unfold coreObs
    exact Semantics.observe_gap sem (Compile.checkedAF sourceChecked.program)
      (Consistency.completeClaimFor sourceChecked p) hempty
  have htargetSupport :=
    claimSupportFor_nonempty_mono sourceChecked targetChecked hpolicy
      (fun term hterm => by simpa only [hargs] using hterm)
      (fun _ h => by simpa only [hgamma] using h) p hsourceSupport
  intro htargetGap
  have hempty :
      Consistency.claimSupportFor targetChecked p = [] := by
    apply (Semantics.observe_gap_iff sem
      (Compile.checkedAF targetChecked.program)
      (Consistency.completeClaimFor targetChecked p)).mp
    simpa only [CoreTransition, coreObs] using htargetGap
  exact htargetSupport hempty

/-- Constructor-local side conditions for an additive update.  `addLeaf`
records the same full three-carrier freshness and admitted-leaf conditions used
by its acceptance-preservation theorem; attacks and instances need no extra
condition here because successful `applyUpdate` already checks their guards. -/
inductive AdditiveUpdate (source : SourceState) : SourceUpdate → Prop where
  | addLeaf (id : LeafId) (a : Atom) (m : Admission.LeafMeta)
      (fresh : AddLeafFresh source id)
      (admitted :
        Admission.decisionFor source.table m.kind m.provenance = .admit) :
      AdditiveUpdate source (.addLeaf id a m)
  | addAttack (raw : RawAttack.RawAttack) :
      AdditiveUpdate source (.addAttack raw)
  | addInstance (name : String) (w : SupportTerm) :
      AdditiveUpdate source (.addInstance name w)


/-- A clean exact source run remains clean after each of the three additive
constructors.  The `addLeaf` case uses its admitted/fresh side conditions to
show that neither the policy seed nor any duplicate-group seed grows. -/
theorem additive_clean_target {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {u : SourceUpdate} (sourceRun : AcceptedRun reg source)
    (targetRun : AcceptedRun reg target)
    (happly : applyUpdate reg source u = .ok target)
    (hadditive : AdditiveUpdate source u)
    (hclean : CleanBase sourceRun) :
    CleanBase targetRun := by
  have hsourceSeed := hclean
  change sourceRun.admission.prune.removedSeed = [] at hsourceSeed
  rw [sourceRun.prune_eq] at hsourceSeed
  change
    Admission.policyQuarantineSeed source.table source.metas ++
      Groups.quarantined canon source.leaves source.groups = [] at hsourceSeed
  cases hadditive with
  | addLeaf id a m hfresh hadmitted =>
      have htargetState := applyUpdate_addLeaf_target happly
      subst target
      have hpolicy :
          Admission.policyQuarantineSeed source.table
              (source.metas ++ [{ m with id := id }]) =
            Admission.policyQuarantineSeed source.table source.metas := by
        simp [Admission.policyQuarantineSeed, List.filterMap_append, hadmitted]
      have hgroup :
          Groups.quarantined canon (source.leaves ++ [(id, a)]) source.groups =
            Groups.quarantined canon source.leaves source.groups :=
        quarantined_append_fresh canon source.leaves id a source.groups
          hfresh.2.2
      change targetRun.admission.prune.removedSeed = []
      rw [targetRun.prune_eq]
      change
        Admission.policyQuarantineSeed source.table
            (source.metas ++ [{ m with id := id }]) ++
          Groups.quarantined canon (source.leaves ++ [(id, a)])
            source.groups = []
      rw [hpolicy, hgroup]
      exact hsourceSeed
  | addAttack raw =>
      have htargetState := applyUpdate_addAttack_target happly
      subst target
      change targetRun.admission.prune.removedSeed = []
      rw [targetRun.prune_eq]
      exact hsourceSeed
  | addInstance name w =>
      have htargetState := applyUpdate_addInstance_target happly
      subst target
      change targetRun.admission.prune.removedSeed = []

      rw [targetRun.prune_eq]
      exact hsourceSeed

/-- **M3 additive seed fact.** A successful `addLeaf`, `addAttack`, or
`addInstance` from an exact clean source has an empty target blocking seed. -/
theorem additive_target_blockedSeed_eq_nil {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {u : SourceUpdate} (sourceRun : AcceptedRun reg source)
    (targetRun : AcceptedRun reg target)
    (happly : applyUpdate reg source u = .ok target)
    (hadditive : AdditiveUpdate source u)
    (hclean : CleanBase sourceRun) :
    blockedSeedForRun targetRun = [] := by
  apply blockedSeedForRun_eq_nil_of_clean
  exact additive_clean_target sourceRun targetRun happly hadditive hclean

/-- **M3 additive closure fact.** The exact target declared-index blocked set is
empty for the three successful additive constructors from a clean source. -/
theorem additive_target_blockedSet_eq_nil {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {u : SourceUpdate} (sourceRun : AcceptedRun reg source)
    (targetRun : AcceptedRun reg target)
    (happly : applyUpdate reg source u = .ok target)
    (hadditive : AdditiveUpdate source u)
    (hclean : CleanBase sourceRun) :
    blockedSetForRun targetRun = [] := by
  apply blockedSet_eq_nil_of_seed_nil
  exact additive_target_blockedSeed_eq_nil sourceRun targetRun happly
    hadditive hclean

/-- **Clean-base additive equality.** For exactly `addLeaf`, `addAttack`, and
`addInstance`, the explicit empty target seed has an empty forward closure, so
the target public report is its embedded core report. -/
theorem additive_public_eq_core {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {u : SourceUpdate} (sourceRun : AcceptedRun reg source)
    (targetRun : AcceptedRun reg target)
    (happly : applyUpdate reg source u = .ok target)
    (hadditive : AdditiveUpdate source u)
    (hclean : CleanBase sourceRun) (p : Atom) :
    publicReport targetRun p =
      PublicReport.ofStatus
        (Grounded.statusC (Compile.checkedAF targetRun.checked.program)
          (Consistency.completeClaimFor targetRun.checked p)) :=
  publicReport_eq_core_of_empty_closure targetRun
    (additive_target_blockedSet_eq_nil sourceRun targetRun happly hadditive
      hclean) p

/-- No clean-base additive target can enter the blocked public column. -/
theorem additive_public_ne_evidenceBlocked {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {u : SourceUpdate} (sourceRun : AcceptedRun reg source)
    (targetRun : AcceptedRun reg target)
    (happly : applyUpdate reg source u = .ok target)
    (hadditive : AdditiveUpdate source u)
    (hclean : CleanBase sourceRun) (p : Atom) :
    publicReport targetRun p ≠ .evidenceBlocked := by
  rw [additive_public_eq_core sourceRun targetRun happly hadditive hclean p]
  cases Grounded.statusC (Compile.checkedAF targetRun.checked.program)
    (Consistency.completeClaimFor targetRun.checked p) <;> decide

/-- Successful non-instance updates used by the gap-row boundary.  The
tightening constructor records exactly the restrictiveness and retained-Gamma
premises of `applyUpdate_tighten_ok`; `addInstance` is deliberately absent. -/
inductive NonInstanceUpdate (canon : String → String)
    (source : SourceState) : SourceUpdate → Prop where
  | addLeaf (id : LeafId) (a : Atom) (m : Admission.LeafMeta)
      (fresh : AddLeafFresh source id)
      (admitted :
        Admission.decisionFor source.table m.kind m.provenance = .admit) :
      NonInstanceUpdate canon source (.addLeaf id a m)
  | addAttack (raw : RawAttack.RawAttack) :
      NonInstanceUpdate canon source (.addAttack raw)
  | tighten (key : LeafKind × Provenance)
      (restrictive :
        Admission.AtLeastAsRestrictive source.table
          (tightenTable source.table key))
      (gammaRetained : ∀ term,
        term ∈ (Admission.buildPrune canon
          (tightenTable source.table key) source.metas source.leaves
          source.argsRaw source.rawAtts source.groups []).keptArgs.map (·.2) →
        ∀ l, l ∈ Support.leaves term →
          Admission.buildGamma
              (Admission.buildPrune canon source.table source.metas
                source.leaves source.argsRaw source.rawAtts source.groups
                []).checkedLeaves l =
            Admission.buildGamma
              (Admission.buildPrune canon (tightenTable source.table key)
                source.metas source.leaves source.argsRaw source.rawAtts
                source.groups []).checkedLeaves l) :
      NonInstanceUpdate canon source (.tighten key)


/-- A real successful tighten maps every target complete-support index to a
declared index that the clean source claim also supports: the target's lifted
support is contained in the source's.  Both sides lift along their own checked
carrier `K`, since with holes a compact index is not a declared one.  This is
the support half of the five-valued public-row transport; label transport is
supplied by `BlockedProgram.production_unblocked_label_agree`. -/
theorem tighten_lifted_support_subset {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {key : LeafKind × Provenance}
    (sourceRun : AcceptedRun reg source)
    (targetRun : AcceptedRun reg target)
    (happly : applyUpdate reg source (.tighten key) = .ok target)
    (hnon : NonInstanceUpdate canon source (.tighten key))
    (hclean : CleanBase sourceRun) (p : Atom) :
    ∀ a, a ∈ Consistency.claimSupportFor targetRun.checked p →
      ∀ A, (checkedCarrierForRun targetRun)[a]? = some A →
        A ∈ BlockedProgram.liftSupport (checkedCarrierForRun sourceRun)
          (Consistency.claimSupportFor sourceRun.checked p) := by
  cases hnon with
  | tighten key hrestrictive hgammaRetained =>
      have htargetState := applyUpdate_tighten_target happly
      subst target
      have hsourceSound := Check.Unit.checkUnit_sound sourceRun.check_ok
      have htargetSound := Check.Unit.checkUnit_sound targetRun.check_ok
      have hsourceArgs :=
        BlockedProgram.checked_args_keepComplete sourceRun.check_retained
      have htargetArgs :=
        BlockedProgram.checked_args_keepComplete targetRun.check_retained
      have hsourceComplete := checkedArgs_eq_raw_of_clean sourceRun hclean
      have hkeepAll := (noPruneTransportOfClean sourceRun hclean).keepAll
      intro a ha A hA
      obtain ⟨targetNode, htargetNode, htargetConclusion⟩ :=
        (Consistency.mem_claimSupportFor_iff).mp ha
      obtain ⟨row, hrowRetained, hrowRaw⟩ :=
        BlockedProgram.retained_lookup hA
      have hrowMem : row ∈ source.argsRaw := List.mem_of_getElem? hrowRaw
      have htargetTermAt :
          targetRun.checked.program.args[a]? = some row.2 := by
        rw [htargetArgs, List.getElem?_map, hrowRetained]
        rfl
      have htargetNodeTerm : targetNode.term = row.2 := by
        have hmapped :
            (targetRun.checked.nodes.map (·.term))[a]? = some row.2 := by
          rw [targetRun.checked.nodes_terms, htargetTermAt]
        rw [List.getElem?_map, htargetNode] at hmapped
        exact Option.some.inj hmapped
      have hrowKeep : targetRun.admission.prune.keep row = true := by
        have hcomplete :=
          (List.mem_filter.mp (by
            rw [← BlockedProgram.retainedArguments_eq_filter]
            exact List.mem_of_getElem? hrowRetained)).2
        simp only [BlockedProgram.keepComplete, Bool.and_eq_true] at hcomplete
        exact hcomplete.1
      have htermPrune :
          row.2 ∈
            (Admission.buildPrune canon
              (tightenTable source.table key) source.metas source.leaves
              source.argsRaw source.rawAtts source.groups []).keptArgs.map
                (·.2) := by
        have hrowKept : row ∈ targetRun.admission.prune.keptArgs := by
          rw [targetRun.keptArgs_eq, BlockedProgram.retainedArguments_eq_filter]
          exact List.mem_filter.mpr ⟨hrowMem, hrowKeep⟩
        have htermKept :
            row.2 ∈ targetRun.admission.prune.keptArgs.map (·.2) :=
          List.mem_map_of_mem hrowKept
        simpa [targetRun.prune_eq, Admission.buildPrune] using htermKept
      have htargetValidInSource :
          HasSupport canon source.policy.ruleLookup
            (Admission.buildGamma sourceRun.admission.prune.checkedLeaves)
            (certOkOf reg) row.2 targetNode.conclusion [] := by
        have hpol : targetRun.checked.policy = source.policy :=
          htargetSound.policy_eq
        have hrule : targetRun.checked.policy.ruleLookup =
            source.policy.ruleLookup := congrArg Policy.Policy.ruleLookup hpol
        rw [← hrule, ← htargetNodeTerm]
        apply hasSupport_congr_gamma_on targetNode.valid
        intro leaf hleaf
        rw [htargetNodeTerm] at hleaf
        have hgamma := hgammaRetained row.2 htermPrune leaf hleaf
        simpa only [sourceRun.prune_eq, targetRun.prune_eq,
          Admission.buildPrune] using hgamma.symm
      have hrowDone :
          BlockedProgram.checkedDone sourceRun.checked row.2 = true := by
        simp only [BlockedProgram.checkedDone, decide_eq_true_eq]
        rw [hsourceComplete]
        apply Check.mem_completeArgs_iff.mpr
        refine ⟨List.mem_map_of_mem hrowMem, targetNode.conclusion, ?_⟩
        apply hasSupport_congr_gamma_on htargetValidInSource
        exact sourceRun.gamma_agree row hrowMem (hkeepAll row hrowMem)
      have hAsource : A ∈ checkedCarrierForRun sourceRun :=
        BlockedProgram.mem_retainedIndices_iff.mpr ⟨row, hrowRaw, by
          simp [BlockedProgram.keepComplete, hkeepAll row hrowMem, hrowDone]⟩
      obtain ⟨a', ha'⟩ := BlockedProgram.retained_lookup_of_mem hAsource
      obtain ⟨row', hrow'Retained, hrow'Raw⟩ :=
        BlockedProgram.retained_lookup ha'
      have hrowEq : row' = row :=
        Option.some.inj (hrow'Raw.symm.trans hrowRaw)
      subst row'
      have hsourceTermAt :
          sourceRun.checked.program.args[a']? = some row.2 := by
        rw [hsourceArgs, List.getElem?_map, hrow'Retained]
        rfl
      have hsourceNodeMap :
          (sourceRun.checked.nodes[a']?).map (·.term) = some row.2 := by
        rw [← List.getElem?_map, sourceRun.checked.nodes_terms]
        exact hsourceTermAt
      cases hsourceNodeAt : sourceRun.checked.nodes[a']? with
      | none => simp [hsourceNodeAt] at hsourceNodeMap
      | some sourceNode =>
          have hsourceNodeTerm : sourceNode.term = row.2 := by
            simpa [hsourceNodeAt] using hsourceNodeMap
          have hsourceValid :
              HasSupport canon source.policy.ruleLookup
                (Admission.buildGamma sourceRun.admission.prune.checkedLeaves)
                (certOkOf reg) row.2 sourceNode.conclusion [] := by
            have hpol : sourceRun.checked.policy = source.policy :=
              hsourceSound.policy_eq
            rw [← hpol, ← hsourceNodeTerm]
            exact sourceNode.valid
          have hconclusion :
              sourceNode.conclusion = targetNode.conclusion :=
            (hasSupport_unique hsourceValid htargetValidInSource).1
          apply BlockedProgram.mem_liftSupport_iff.mpr
          refine ⟨a', ?_, ha'⟩
          apply (Consistency.mem_claimSupportFor_iff).mpr
          refine ⟨sourceNode, hsourceNodeAt, ?_⟩
          simpa [hconclusion] using htargetConclusion

/-- No additive source update enters the `gap` column from a non-`gap` row.
Both observations recompute support from the same atom; adding a leaf, attack,
or argument instance preserves or extends the support available to that atom.
Tightening is excluded because it may prune arguments. -/
theorem additive_no_gap_entry {canon : String → String}
    (sem : Semantics.ExtensionSemantics) (reg : BackendRegistry canon)
    (source target : SourceState) (p : Atom) (u : SourceUpdate)
    (sourceDeclared :
      Admission.AlignedAttacks source.argsRaw source.rawAtts)
    (sourceAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetDeclared :
      Admission.AlignedAttacks target.argsRaw target.rawAtts)
    (targetAdmission : Admission.AdmissionResult)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg))
    (hsourceAdmission :
      admissionFor canon source sourceDeclared = .accepted sourceAdmission)
    (hsourceCheck :
      checkAccepted reg source sourceAdmission = .ok sourceChecked)
    (happly : applyUpdate reg source u = .ok target)
    (htargetAdmission :
      admissionFor canon target targetDeclared = .accepted targetAdmission)
    (htargetCheck :
      checkAccepted reg target targetAdmission = .ok targetChecked)
    (hadditive : AdditiveUpdate source u)
    (hsourceNotGap :
      (CoreTransition sem sourceChecked targetChecked p).1 ≠
        .observed Grounded.Status.gap) :
    (CoreTransition sem sourceChecked targetChecked p).2 ≠
      .observed Grounded.Status.gap := by
  cases hadditive with
  | addLeaf id a m hfresh hadmit =>
      exact addLeaf_no_gap_entry sem reg source target p id a m
        sourceDeclared sourceAdmission sourceChecked targetDeclared
        targetAdmission targetChecked hsourceAdmission hsourceCheck happly
        htargetAdmission htargetCheck hfresh hadmit hsourceNotGap
  | addAttack raw =>
      exact addAttack_no_gap_entry sem reg source target p raw
        sourceDeclared sourceAdmission sourceChecked targetDeclared
        targetAdmission targetChecked hsourceAdmission hsourceCheck happly

        htargetAdmission htargetCheck hsourceNotGap
  | addInstance name w =>
      exact addInstance_no_gap_entry sem reg source target p name w
        sourceDeclared sourceAdmission sourceChecked targetDeclared
        targetAdmission targetChecked hsourceAdmission hsourceCheck happly
        htargetAdmission htargetCheck hsourceNotGap
/-- Under a clean base, a successful tighten cannot publicly move a defeated
claim to `contested`: every target support lifts to a declared index the source
also supports, and an unblocked label agrees with the label at that declared
index in the shared declared framework, on both sides. -/
theorem tighten_public_defeated_not_contested {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {key : LeafKind × Provenance}
    (sourceRun : AcceptedRun reg source)
    (targetRun : AcceptedRun reg target)
    (happly : applyUpdate reg source (.tighten key) = .ok target)
    (hnon : NonInstanceUpdate canon source (.tighten key))
    (hclean : CleanBase sourceRun) (p : Atom)
    (htransition :
      PublicTransition sourceRun targetRun p = (.defeated, .contested)) :
    False := by
  have hliftSubset :=
    tighten_lifted_support_subset sourceRun targetRun happly hnon hclean p
  have htargetState := applyUpdate_tighten_target happly
  subst target
  have hsourcePublic :
      publicReport sourceRun p = .defeated := by
    simpa [PublicTransition] using congrArg Prod.fst htransition
  have hsourceCore :
      Grounded.statusC (Compile.checkedAF sourceRun.checked.program)
          (Consistency.completeClaimFor sourceRun.checked p) = .defeated := by
    have heq := publicReport_eq_core_of_clean sourceRun hclean p
    rw [heq] at hsourcePublic
    exact PublicReport.ofStatus_injective hsourcePublic
  have htargetPublic :
      publicReport targetRun p = .contested := by
    simpa [PublicTransition] using congrArg Prod.snd htransition
  have htargetNotBlocked :
      p ∉ blockedQueriesForRun targetRun [p] := by
    intro hblocked
    have hblockedReport : publicReport targetRun p = .evidenceBlocked := by
      simp [publicReport, hblocked]
    rw [hblockedReport] at htargetPublic
    contradiction
  have hsourceNotBlocked :=
    not_mem_blockedQueriesForRun_of_clean sourceRun hclean p
  have htargetCore :
      Grounded.statusC (Compile.checkedAF targetRun.checked.program)
          (Consistency.completeClaimFor targetRun.checked p) = .contested := by
    unfold publicReport at htargetPublic
    rw [if_neg htargetNotBlocked] at htargetPublic
    exact PublicReport.ofStatus_injective htargetPublic
  obtain ⟨a, ha, haUndec⟩ :=
    Grounded.statusC_contested_has_undec htargetCore
  obtain ⟨A, hA⟩ := Support.getElem?_some_of_lt (checkedCarrierForRun targetRun)
    a (claimSupportFor_lt_checkedCarrier targetRun p a ha)
  obtain ⟨a', ha', hA'⟩ :=
    BlockedProgram.mem_liftSupport_iff.mp (hliftSubset a ha A hA)
  have hresolved :
      targetRun.declared.resolved = sourceRun.declared.resolved :=
    Except.ok.inj
      (targetRun.declared.resolve_eq.symm.trans sourceRun.declared.resolve_eq)
  have htargetLabel := run_label_agree targetRun p htargetNotBlocked ha hA
  have hsourceLabel := run_label_agree sourceRun p hsourceNotBlocked ha' hA'
  have hsourceOut :=
    (Grounded.statusC_defeated_all_out hsourceCore).2 a' ha'
  rw [htargetLabel, hresolved] at haUndec
  change Grounded.labelC
      (BlockedProgram.declaredAF source.argsRaw sourceRun.declared.resolved
        (declaredCarrier reg source)) A = _ at haUndec
  rw [hsourceLabel] at hsourceOut
  rw [hsourceOut] at haUndec
  contradiction

/-- The `justified` public cell of the tighten/quarantine row is conservative
on an exact `CleanBase` run: a compact `justified` claim, lifted along `K`, is
`justified` in the declared framework over the specification carrier.  The
proof compares the checked and declared frameworks directly and does not
appeal to `Admission.source_justified_nonpromotion`. -/
theorem tighten_public_row_justified_nonpromotion
    {canon : String → String} {reg : BackendRegistry canon}
    {state : SourceState}
    (run : AcceptedRun reg state) (hclean : CleanBase run) (p : Atom)
    (hstatus : Grounded.statusC (Compile.checkedAF run.checked.program)
      (Consistency.completeClaimFor run.checked p) = .justified) :
    Grounded.statusC
      (BlockedProgram.declaredAF state.argsRaw run.declared.resolved
        (declaredCarrier reg state))
      (BlockedProgram.liftClaim (checkedCarrierForRun run)
        (Consistency.completeClaimFor run.checked p)) = .justified :=
  checked_row_justified_nonpromotion run p
    (not_mem_blockedQueriesForRun_of_clean run hclean p) hstatus

/-- A grounded public `justified` target in the tighten row was already
justified in the clean source.  This is the exact transition-level form used by
the public matrix's refuted/both-to-justified blockers. -/
theorem tighten_public_justified_source_justified
    {canon : String → String} {reg : BackendRegistry canon}
    {source target : SourceState} {key : LeafKind × Provenance}
    (sourceRun : AcceptedRun reg source)
    (targetRun : AcceptedRun reg target)
    (happly : applyUpdate reg source (.tighten key) = .ok target)
    (hnon : NonInstanceUpdate canon source (.tighten key))
    (hclean : CleanBase sourceRun) (p : Atom)
    (htargetPublic : publicReport targetRun p = .justified) :
    Grounded.statusC (Compile.checkedAF sourceRun.checked.program)
      (Consistency.completeClaimFor sourceRun.checked p) = .justified := by
  have hliftSubset :=
    tighten_lifted_support_subset sourceRun targetRun happly hnon hclean p
  have htargetState := applyUpdate_tighten_target happly
  subst target
  have hnot : p ∉ blockedQueriesForRun targetRun [p] := by
    intro hblocked
    have hblockedReport : publicReport targetRun p = .evidenceBlocked := by
      simp [publicReport, hblocked]
    rw [hblockedReport] at htargetPublic
    contradiction
  have hsourceNotBlocked :=
    not_mem_blockedQueriesForRun_of_clean sourceRun hclean p
  have htargetCore :
      Grounded.statusC (Compile.checkedAF targetRun.checked.program)
          (Consistency.completeClaimFor targetRun.checked p) = .justified := by
    unfold publicReport at htargetPublic
    rw [if_neg hnot] at htargetPublic
    exact PublicReport.ofStatus_injective htargetPublic
  have hdeclared :=
    checked_row_justified_nonpromotion targetRun p hnot htargetCore
  obtain ⟨A, hAlift, hAIn⟩ :=
    (Grounded.statusC_justified_iff _ _).mp hdeclared
  obtain ⟨a, ha, hA⟩ :=
    BlockedProgram.mem_liftSupport_iff.mp hAlift
  obtain ⟨a', ha', hA'⟩ :=
    BlockedProgram.mem_liftSupport_iff.mp (hliftSubset a ha A hA)
  have hresolved :
      targetRun.declared.resolved = sourceRun.declared.resolved :=
    Except.ok.inj
      (targetRun.declared.resolve_eq.symm.trans sourceRun.declared.resolve_eq)
  have hsourceLabel := run_label_agree sourceRun p hsourceNotBlocked ha' hA'
  rw [hresolved] at hAIn
  apply (Grounded.statusC_justified_iff _ _).mpr
  refine ⟨a', ha', ?_⟩
  rw [hsourceLabel]
  exact hAIn

/-- A clean-base tighten preserves the public `gap` row exactly. -/
theorem tighten_public_gap_fixed {canon : String → String}
    {reg : BackendRegistry canon} {source target : SourceState}
    {key : LeafKind × Provenance}
    (sourceRun : AcceptedRun reg source)
    (targetRun : AcceptedRun reg target)
    (happly : applyUpdate reg source (.tighten key) = .ok target)
    (hnon : NonInstanceUpdate canon source (.tighten key))
    (hclean : CleanBase sourceRun) (p : Atom)
    (hsourcePublic : publicReport sourceRun p = .gap) :
    publicReport targetRun p = .gap := by
  have hsourceCore :
      Grounded.statusC (Compile.checkedAF sourceRun.checked.program)
          (Consistency.completeClaimFor sourceRun.checked p) = .gap := by
    have heq := publicReport_eq_core_of_clean sourceRun hclean p
    rw [heq] at hsourcePublic
    exact PublicReport.ofStatus_injective hsourcePublic
  have hsourceEmpty :
      Consistency.claimSupportFor sourceRun.checked p = [] :=
    (Grounded.statusC_gap_iff _ _).mp hsourceCore
  have htargetEmpty :
      Consistency.claimSupportFor targetRun.checked p = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    obtain ⟨A, hA⟩ := Support.getElem?_some_of_lt
      (checkedCarrierForRun targetRun) a
      (claimSupportFor_lt_checkedCarrier targetRun p a ha)
    have hsourceSupport :=
      tighten_lifted_support_subset sourceRun targetRun happly hnon hclean p
        a ha A hA
    rw [hsourceEmpty] at hsourceSupport
    simp [BlockedProgram.liftSupport] at hsourceSupport
  exact publicReport_gap_of_empty_support targetRun p htargetEmpty


private theorem any_congr_of_mem {α : Type _} {l₁ l₂ : List α}
    {f g : α → Bool}
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂)
    (hfg : ∀ x, f x = g x) :
    l₁.any f = l₂.any g := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    obtain ⟨x, hx, hfx⟩ := List.any_eq_true.mp h
    exact List.any_eq_true.mpr ⟨x, (hmem x).mp hx, hfg x ▸ hfx⟩
  · intro h
    obtain ⟨x, hx, hgx⟩ := List.any_eq_true.mp h
    exact List.any_eq_true.mpr ⟨x, (hmem x).mpr hx, (hfg x).symm ▸ hgx⟩

private theorem all_congr_of_mem {α : Type _} {l₁ l₂ : List α}
    {f g : α → Bool}
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂)
    (hfg : ∀ x, f x = g x) :
    l₁.all f = l₂.all g := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    apply List.all_eq_true.mpr
    intro x hx
    exact hfg x ▸ List.all_eq_true.mp h x ((hmem x).mpr hx)
  · intro h
    apply List.all_eq_true.mpr
    intro x hx
    exact (hfg x).symm ▸ List.all_eq_true.mp h x ((hmem x).mp hx)

private theorem observe_support_congr
    (sem : Semantics.ExtensionSemantics) (F : Grounded.AF)
    (c d : Grounded.Claim)
    (hmem : ∀ i, i ∈ c.support ↔ i ∈ d.support) :
    Semantics.observe sem F c = Semantics.observe sem F d := by
  have hempty : c.support = [] ↔ d.support = [] := by
    constructor
    · intro hc
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro i hi
      have := (hmem i).mpr hi
      simp [hc] at this
    · intro hd
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro i hi
      have := (hmem i).mp hi
      simp [hd] at this
  have haccepted : ∀ E,
      Semantics.claimAcceptedB E c = Semantics.claimAcceptedB E d := by
    intro E
    unfold Semantics.claimAcceptedB
    exact any_congr_of_mem hmem (fun _ => rfl)
  have hdefeated : ∀ E,
      Semantics.claimDefeatedB F E c =
        Semantics.claimDefeatedB F E d := by
    intro E
    unfold Semantics.claimDefeatedB
    exact all_congr_of_mem hmem (fun _ => rfl)
  unfold Semantics.observe
  by_cases hc : c.support = []
  · rw [if_pos hc, if_pos (hempty.mp hc)]
  · rw [if_neg hc, if_neg (fun hd => hc (hempty.mpr hd))]
    split
    · rfl
    · have hallAccepted :
          (sem.enumerate F).all
              (fun E => Semantics.claimAcceptedB E c) =
            (sem.enumerate F).all
              (fun E => Semantics.claimAcceptedB E d) :=
        List.all_congr rfl haccepted
      rw [hallAccepted]
      split
      · rfl
      · have hallDefeated :
            (sem.enumerate F).all
                (fun E => Semantics.claimDefeatedB F E c) =
              (sem.enumerate F).all
                (fun E => Semantics.claimDefeatedB F E d) :=
          List.all_congr rfl hdefeated
        rw [hallDefeated]


private theorem mem_claimSupportFor_congr
    (source : Lara.Unit.CheckedUnit canon Gamma₁ CertOk)
    (target : Lara.Unit.CheckedUnit canon Gamma₂ CertOk)
    (hpolicy : source.policy = target.policy)
    (hargs : source.program.args = target.program.args)
    (hsupport : ∀ {w C},
      HasSupport canon source.policy.ruleLookup Gamma₁ CertOk w C [] →
      HasSupport canon source.policy.ruleLookup Gamma₂ CertOk w C [])
    (p : Atom) (i : Nat) :
    i ∈ Consistency.claimSupportFor source p ↔
      i ∈ Consistency.claimSupportFor target p := by
  have hlength : source.nodes.length = target.nodes.length := by
    have hs : source.nodes.length = source.program.args.length := by
      simpa only [List.length_map] using
        congrArg List.length source.nodes_terms
    have ht : target.nodes.length = target.program.args.length := by
      simpa only [List.length_map] using
        congrArg List.length target.nodes_terms
    exact hs.trans ((congrArg List.length hargs).trans ht.symm)
  constructor
  · intro hi
    obtain ⟨sourceNode, hsourceNode, hsourceConclusion⟩ :=
      (Consistency.mem_claimSupportFor_iff).mp hi
    have hiSource := (List.getElem?_eq_some_iff.mp hsourceNode).1
    have hiTarget : i < target.nodes.length := hlength ▸ hiSource
    let targetNode := target.nodes[i]
    have htargetNode : target.nodes[i]? = some targetNode := by
      exact List.getElem?_eq_some_iff.mpr ⟨hiTarget, rfl⟩
    have hsourceTerm :
        source.program.args[i]? = some sourceNode.term := by
      rw [← source.nodes_terms]
      simpa using congrArg (Option.map (fun n => n.term)) hsourceNode
    have htargetTerm :
        target.program.args[i]? = some targetNode.term := by
      rw [← target.nodes_terms]
      simpa using congrArg (Option.map (fun n => n.term)) htargetNode
    have htermEq : sourceNode.term = targetNode.term := by
      rw [hargs] at hsourceTerm
      exact Option.some.inj (hsourceTerm.symm.trans htargetTerm)
    have htargetValid :
        HasSupport canon source.policy.ruleLookup Gamma₂ CertOk
          targetNode.term targetNode.conclusion [] := by
      simpa only [hpolicy] using targetNode.valid
    have hconclusion :
        sourceNode.conclusion = targetNode.conclusion := by
      exact (hasSupport_unique (hsupport sourceNode.valid)
        (by simpa only [htermEq] using htargetValid)).1
    apply (Consistency.mem_claimSupportFor_iff).mpr
    exact ⟨targetNode, htargetNode, hconclusion ▸ hsourceConclusion⟩
  · intro hi
    obtain ⟨targetNode, htargetNode, htargetConclusion⟩ :=
      (Consistency.mem_claimSupportFor_iff).mp hi
    have hiTarget := (List.getElem?_eq_some_iff.mp htargetNode).1
    have hiSource : i < source.nodes.length := hlength.symm ▸ hiTarget
    let sourceNode := source.nodes[i]
    have hsourceNode : source.nodes[i]? = some sourceNode := by
      exact List.getElem?_eq_some_iff.mpr ⟨hiSource, rfl⟩
    have hsourceTerm :
        source.program.args[i]? = some sourceNode.term := by
      rw [← source.nodes_terms]
      simpa using congrArg (Option.map (fun n => n.term)) hsourceNode
    have htargetTerm :
        target.program.args[i]? = some targetNode.term := by
      rw [← target.nodes_terms]
      simpa using congrArg (Option.map (fun n => n.term)) htargetNode
    have htermEq : sourceNode.term = targetNode.term := by
      rw [hargs] at hsourceTerm
      exact Option.some.inj (hsourceTerm.symm.trans htargetTerm)
    have htargetValid :
        HasSupport canon source.policy.ruleLookup Gamma₂ CertOk
          targetNode.term targetNode.conclusion [] := by
      simpa only [hpolicy] using targetNode.valid
    have hconclusion :
        sourceNode.conclusion = targetNode.conclusion := by
      exact (hasSupport_unique (hsupport sourceNode.valid)
        (by simpa only [htermEq] using htargetValid)).1
    apply (Consistency.mem_claimSupportFor_iff).mpr
    exact ⟨sourceNode, hsourceNode, hconclusion.symm ▸ htargetConclusion⟩


/-- Under the full add-leaf freshness and admitted-update conditions, the
grounded core observation is fixed.  The edit extends evidence only: retained
arguments and compiled attacks are unchanged, while claims are recomputed from
the same atom rather than from pre-update indices. -/
theorem addLeaf_core_fixed {canon : String → String}
    (reg : BackendRegistry canon) (source target : SourceState) (p : Atom)
    (id : LeafId) (a : Atom) (m : Admission.LeafMeta)
    (sourceDeclared :
      Admission.AlignedAttacks source.argsRaw source.rawAtts)
    (sourceAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetDeclared :
      Admission.AlignedAttacks target.argsRaw target.rawAtts)
    (targetAdmission : Admission.AdmissionResult)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg))
    (hsourceAdmission :
      admissionFor canon source sourceDeclared = .accepted sourceAdmission)
    (hsourceCheck :
      checkAccepted reg source sourceAdmission = .ok sourceChecked)
    (happly : applyUpdate reg source (.addLeaf id a m) = .ok target)
    (htargetAdmission :
      admissionFor canon target targetDeclared = .accepted targetAdmission)
    (htargetCheck :
      checkAccepted reg target targetAdmission = .ok targetChecked)
    (hfresh : AddLeafFresh source id)
    (hadmit :
      Admission.decisionFor source.table m.kind m.provenance = .admit) :
    (CoreTransition Semantics.groundedSem sourceChecked targetChecked p).1 =
      (CoreTransition Semantics.groundedSem sourceChecked targetChecked p).2 := by
  have htransport :=
    addLeaf_transport reg source target id a m sourceDeclared sourceAdmission
      sourceChecked targetDeclared targetAdmission targetChecked
      hsourceAdmission hsourceCheck happly htargetAdmission htargetCheck hfresh
      hadmit
  have hedge :
      Compile.edgeB sourceChecked.program =
        Compile.edgeB targetChecked.program := by
    funext i j
    unfold Compile.edgeB
    rw [htransport.args_eq, htransport.atts_eq]
  have hframework :
      Compile.checkedAF sourceChecked.program =
        Compile.checkedAF targetChecked.program := by
    unfold Compile.checkedAF Compile.toAF
    rw [congrArg List.length htransport.args_eq, hedge]
  have hclaimMem : ∀ i,
      i ∈ (Consistency.completeClaimFor sourceChecked p).support ↔
        i ∈ (Consistency.completeClaimFor targetChecked p).support := by
    intro i
    exact mem_claimSupportFor_congr sourceChecked targetChecked
      htransport.policy_eq htransport.args_eq
      (hasSupport_mono_gamma htransport.gamma_mono) p i
  simp only [CoreTransition]
  unfold coreObs
  rw [hframework]
  exact observe_support_congr Semantics.groundedSem
    (Compile.checkedAF targetChecked.program)
    (Consistency.completeClaimFor sourceChecked p)
    (Consistency.completeClaimFor targetChecked p) hclaimMem


/-- `addInstance` is the sole update kind excluded from the gap-row boundary:
it can introduce the first complete support for the fixed atom.  A fresh
admitted leaf and an added attack preserve empty support, while tightening can
only remove retained arguments under its accepted-update transport premises. -/
theorem nonInstance_gap_fixed {canon : String → String}
    (sem : Semantics.ExtensionSemantics) (reg : BackendRegistry canon)
    (source target : SourceState) (p : Atom) (u : SourceUpdate)
    (sourceDeclared :
      Admission.AlignedAttacks source.argsRaw source.rawAtts)
    (sourceAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetDeclared :
      Admission.AlignedAttacks target.argsRaw target.rawAtts)
    (targetAdmission : Admission.AdmissionResult)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg))
    (hsourceAdmission :
      admissionFor canon source sourceDeclared = .accepted sourceAdmission)
    (hsourceCheck :
      checkAccepted reg source sourceAdmission = .ok sourceChecked)
    (happly : applyUpdate reg source u = .ok target)
    (htargetAdmission :
      admissionFor canon target targetDeclared = .accepted targetAdmission)
    (htargetCheck :
      checkAccepted reg target targetAdmission = .ok targetChecked)
    (hnonInstance : NonInstanceUpdate canon source u)
    (hgap :
      (CoreTransition sem sourceChecked targetChecked p).1 =
        .observed Grounded.Status.gap) :
    (CoreTransition sem sourceChecked targetChecked p).2 =
      .observed Grounded.Status.gap := by
  cases hnonInstance with
  | addLeaf id a m hfresh hadmit =>
      have hsourceEmpty :
          Consistency.claimSupportFor sourceChecked p = [] := by
        apply (Semantics.observe_gap_iff sem
          (Compile.checkedAF sourceChecked.program)
          (Consistency.completeClaimFor sourceChecked p)).mp
        simpa only [CoreTransition, coreObs] using hgap
      have htransport :=
        addLeaf_transport reg source target id a m sourceDeclared sourceAdmission
          sourceChecked targetDeclared targetAdmission targetChecked
          hsourceAdmission hsourceCheck happly htargetAdmission htargetCheck
          hfresh hadmit
      have hclaimMem : ∀ i,
          i ∈ Consistency.claimSupportFor sourceChecked p ↔
            i ∈ Consistency.claimSupportFor targetChecked p := by
        intro i
        exact mem_claimSupportFor_congr sourceChecked targetChecked
          htransport.policy_eq htransport.args_eq
          (hasSupport_mono_gamma htransport.gamma_mono) p i
      have htargetEmpty :
          Consistency.claimSupportFor targetChecked p = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro i hi
        have hsourceMem := (hclaimMem i).mpr hi
        simp [hsourceEmpty] at hsourceMem
      simp only [CoreTransition]
      unfold coreObs
      exact Semantics.observe_gap sem (Compile.checkedAF targetChecked.program)
        (Consistency.completeClaimFor targetChecked p) htargetEmpty
  | addAttack raw =>
      exact addAttack_gap_fixed sem reg source target p raw sourceDeclared
        sourceAdmission sourceChecked targetDeclared targetAdmission
        targetChecked hsourceAdmission hsourceCheck happly htargetAdmission
        htargetCheck hgap
  | tighten key hrestrictive hgammaRetained =>
      have htargetState := applyUpdate_tighten_target happly
      subst target
      have hsourceEmpty :
          Consistency.claimSupportFor sourceChecked p = [] := by
        apply (Semantics.observe_gap_iff sem
          (Compile.checkedAF sourceChecked.program)
          (Consistency.completeClaimFor sourceChecked p)).mp
        simpa only [CoreTransition, coreObs] using hgap
      have hsourcePrune := prune_eq_of_acceptance hsourceAdmission
      have htargetPrune := prune_eq_of_acceptance htargetAdmission
      have hsourceFields :=
        checked_policy_args_of_acceptance hsourceCheck
      have htargetFields :=
        checked_policy_args_of_acceptance htargetCheck
      have hpolicy : targetChecked.policy = sourceChecked.policy := by
        exact htargetFields.1.trans hsourceFields.1.symm
      have hseedSubset :
          ∀ l,
            l ∈ Admission.policyQuarantineSeed source.table source.metas ++
                Groups.quarantined canon source.leaves source.groups →
            l ∈ Admission.policyQuarantineSeed
                  (tightenTable source.table key) source.metas ++
                Groups.quarantined canon source.leaves source.groups :=
        Admission.removedSeed_subset_of_restrictive hrestrictive canon
          source.metas source.leaves source.groups
      have htermPrune : ∀ term ∈ targetChecked.program.args,
          term ∈ (Admission.buildPrune canon
            (tightenTable source.table key) source.metas source.leaves
            source.argsRaw source.rawAtts source.groups []).keptArgs.map
              (·.2) := by
        intro term htermTarget
        rw [htargetFields.2, htargetPrune] at htermTarget
        simpa only [Admission.buildPrune] using
          Check.completeArgs_subset htermTarget
      have hsupportBack : ∀ {term C},
          term ∈ targetChecked.program.args →
          HasSupport canon targetChecked.policy.ruleLookup
            (checkedGamma targetAdmission) (certOkOf reg) term C [] →
          HasSupport canon targetChecked.policy.ruleLookup
            (checkedGamma sourceAdmission) (certOkOf reg) term C [] := by
        intro term C htermTarget hsupport
        apply hasSupport_congr_gamma_on hsupport
        intro l hl
        have hgamma := hgammaRetained term (htermPrune term htermTarget) l hl
        simpa only [checkedGamma, hsourcePrune, htargetPrune,
          Admission.buildPrune] using hgamma.symm
      have hterms :
          ∀ term ∈ targetChecked.program.args,
            term ∈ sourceChecked.program.args := by
        intro term hterm
        obtain ⟨C, hC⟩ :=
          (Check.mem_completeArgs_iff.mp (htargetFields.2 ▸ hterm)).2
        have hsourceC := hsupportBack hterm (by rw [htargetFields.1]; exact hC)
        have hkeptTarget := htermPrune term hterm
        rw [hsourceFields.2]
        apply Check.mem_completeArgs_iff.mpr
        refine ⟨?_, C, by
          rw [htargetFields.1] at hsourceC
          exact hsourceC⟩
        rw [hsourcePrune]
        simp only [Admission.buildPrune] at hkeptTarget ⊢
        obtain ⟨row, hrow, hrowTerm⟩ := List.mem_map.mp hkeptTarget
        apply List.mem_map.mpr
        refine ⟨row, ?_, hrowTerm⟩
        obtain ⟨hraw, hkeepNew⟩ := List.mem_filter.mp hrow
        apply List.mem_filter.mpr
        refine ⟨hraw, ?_⟩
        by_cases holdUse :
            Groups.usesLeaf
              (Admission.policyQuarantineSeed source.table source.metas ++
                Groups.quarantined canon source.leaves source.groups)
              row.2 = true
        · have hnewUse :=
            Groups.usesLeaf_mono hseedSubset row.2 holdUse
          simp [hnewUse] at hkeepNew
        · simp [holdUse]
      have htargetEmpty :
          Consistency.claimSupportFor targetChecked p = [] := by
        by_cases hempty :
            Consistency.claimSupportFor targetChecked p = []
        · exact hempty
        · have hsourceNonempty :=
            claimSupportFor_nonempty_mono targetChecked sourceChecked hpolicy
              hterms hsupportBack p hempty
          exact False.elim (hsourceNonempty hsourceEmpty)
      simp only [CoreTransition]
      unfold coreObs
      exact Semantics.observe_gap sem (Compile.checkedAF targetChecked.program)
        (Consistency.completeClaimFor targetChecked p) htargetEmpty


/-- A successful fresh instance append is a sink extension of the compiled
framework.  Consequently a grounded justified claim stays justified, and a
grounded contested claim cannot become defeated.  Incoming closure edges to the
new argument are allowed; freshness rules out only outgoing edges. -/
theorem addInstance_sink_status_monotone {canon : String → String}
    (reg : BackendRegistry canon) (source target : SourceState)
    (p : Atom) (name : String) (w : SupportTerm)
    (sourceDeclared :
      Admission.AlignedAttacks source.argsRaw source.rawAtts)
    (sourceAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetDeclared :
      Admission.AlignedAttacks target.argsRaw target.rawAtts)
    (targetAdmission : Admission.AdmissionResult)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg))
    (hsourceAdmission :
      admissionFor canon source sourceDeclared = .accepted sourceAdmission)
    (hsourceCheck :
      checkAccepted reg source sourceAdmission = .ok sourceChecked)
    (happly :
      applyUpdate reg source (.addInstance name w) = .ok target)
    (htargetAdmission :
      admissionFor canon target targetDeclared = .accepted targetAdmission)
    (htargetCheck :
      checkAccepted reg target targetAdmission = .ok targetChecked)
    (hfresh : InstanceFresh source name w)
    (hnewComplete : ∃ C, HasSupport canon source.policy.ruleLookup
      (Admission.buildGamma
        (Admission.buildPrune canon source.table source.metas source.leaves
          source.argsRaw source.rawAtts source.groups []).checkedLeaves)
      (certOkOf reg) w C []) :
    ((CoreTransition Semantics.groundedSem sourceChecked targetChecked p).1 =
        .observed Grounded.Status.justified →
      (CoreTransition Semantics.groundedSem sourceChecked targetChecked p).2 =
        .observed Grounded.Status.justified) ∧
    ((CoreTransition Semantics.groundedSem sourceChecked targetChecked p).1 =
        .observed Grounded.Status.contested →
      (CoreTransition Semantics.groundedSem sourceChecked targetChecked p).2 ≠
        .observed Grounded.Status.defeated) := by
  have htransport :=
    addInstance_transport reg source target name w sourceDeclared
      sourceAdmission sourceChecked targetDeclared targetAdmission
      targetChecked hsourceAdmission hsourceCheck happly htargetAdmission
      htargetCheck hfresh
  have hpolicy : targetChecked.policy = sourceChecked.policy :=
    htransport.policy_eq
  obtain ⟨newConclusion, hnewComplete'⟩ := hnewComplete
  have hnewCompleteChecked :
      Check.argComplete source.policy.ruleLookup
        (checkedGamma sourceAdmission) reg w = true := by
    apply Check.argComplete_iff.mpr
    refine ⟨newConclusion, ?_⟩
    simpa only [checkedGamma, prune_eq_of_acceptance hsourceAdmission,
      Admission.buildPrune] using hnewComplete'
  have hargs :
      targetChecked.program.args = sourceChecked.program.args ++ [w] := by
    rw [htransport.args_eq]
    simp [Check.completeArgs, hnewCompleteChecked]
  have hatts := htransport.atts_eq
  have hnotmem := htransport.fresh
  let sourceAF := Compile.checkedAF sourceChecked.program
  let targetAF := Compile.checkedAF targetChecked.program
  let sink := sourceChecked.program.args.length
  have hsink : Grounded.SinkExtension sourceAF targetAF sink := by
    refine { args_eq := ?_, old_attack := ?_, sink_no_out := ?_ }
    · simp [sourceAF, targetAF, Compile.checkedAF, Compile.toAF, sink, hargs,
        List.range_succ]
    · intro i hi j hj
      have hiLt : i < sourceChecked.program.args.length := by
        simpa [sourceAF, Compile.checkedAF, Compile.toAF] using hi
      have hjLt : j < sourceChecked.program.args.length := by
        simpa [sourceAF, Compile.checkedAF, Compile.toAF] using hj
      simp only [sourceAF, targetAF, Compile.checkedAF, Compile.toAF]
      unfold Compile.edgeB
      rw [hargs, hatts]
      simp [List.getElem?_append, hiLt, hjLt]
    · intro j
      simp only [targetAF, Compile.checkedAF, Compile.toAF, sink]
      apply Bool.eq_false_iff.mpr
      intro hedge
      have hrange := (Compile.edgeB_faithful targetChecked.program).ranged
        _ _ hedge
      obtain ⟨targetTerm, htargetTerm⟩ :=
        Support.getElem?_some_of_lt targetChecked.program.args j hrange.2
      have hsinkTerm :
          targetChecked.program.args[sourceChecked.program.args.length]? =
            some w := by
        rw [hargs]
        simp
      have hedgeProp :=
        (Compile.edgeB_iff hsinkTerm htargetTerm).mp hedge
      obtain ⟨_, _, k, hk, hsource, _⟩ := hedgeProp
      have hkSource : k ∈ sourceChecked.program.atts := by
        simpa only [hatts] using hk
      have holdSource := sourceChecked.program.source_declared k hkSource
      exact hnotmem (hsource ▸ holdSource)
  have hsupportCarrier :
      ∀ i ∈ (Consistency.completeClaimFor sourceChecked p).support,
        i ∈ sourceAF.args := by
    intro i hi
    have hnode :=
      (Consistency.mem_claimSupportFor_iff (unit := sourceChecked) (p := p)
        (i := i)).mp hi
    obtain ⟨node, hnodeAt, _⟩ := hnode
    have hiLt : i < sourceChecked.nodes.length :=
      Support.lt_of_getElem?_some hnodeAt
    have hlength :
        sourceChecked.nodes.length = sourceChecked.program.args.length := by
      simpa using congrArg List.length sourceChecked.nodes_terms
    simpa [sourceAF, Compile.checkedAF, Compile.toAF, hlength] using hiLt
  have hgamma := htransport.gamma_eq
  have hsupport :
      ∀ i ∈ (Consistency.completeClaimFor sourceChecked p).support,
        i ∈ (Consistency.completeClaimFor targetChecked p).support := by
    intro i hi
    obtain ⟨sourceNode, hsourceNode, hsourceConclusion⟩ :=
      (Consistency.mem_claimSupportFor_iff (unit := sourceChecked) (p := p)
        (i := i)).mp hi
    have hsourceTerm :
        sourceChecked.program.args[i]? = some sourceNode.term := by
      rw [← sourceChecked.nodes_terms, List.getElem?_map, hsourceNode]
      rfl
    have htargetTerm :
        targetChecked.program.args[i]? = some sourceNode.term := by
      have hiLt := Support.lt_of_getElem?_some hsourceTerm
      rw [hargs, List.getElem?_append_left hiLt]
      exact hsourceTerm
    have htargetNodeMap :
        (targetChecked.nodes[i]?).map (·.term) = some sourceNode.term := by
      rw [← targetChecked.nodes_terms, List.getElem?_map] at htargetTerm
      exact htargetTerm
    cases htargetNode : targetChecked.nodes[i]? with
    | none => simp [htargetNode] at htargetNodeMap
    | some targetNode =>
        have hterm : targetNode.term = sourceNode.term := by
          simpa [htargetNode] using htargetNodeMap
        have hsourceValid :
            HasSupport canon targetChecked.policy.ruleLookup
              (checkedGamma targetAdmission) (certOkOf reg)
              sourceNode.term sourceNode.conclusion [] := by
          rw [hpolicy, hgamma]
          exact sourceNode.valid
        have hconclusion : targetNode.conclusion = sourceNode.conclusion := by
          exact (hasSupport_unique
            (by simpa only [hterm] using targetNode.valid) hsourceValid).1
        apply (Consistency.mem_claimSupportFor_iff
          (unit := targetChecked) (p := p) (i := i)).mpr
        refine ⟨targetNode, htargetNode, ?_⟩
        simpa only [hconclusion] using hsourceConclusion
  have hsourceNodup : sourceAF.args.Nodup := by
    change (List.range sourceChecked.program.args.length).Nodup
    exact List.nodup_range
  have htargetNodup : targetAF.args.Nodup := by
    change (List.range targetChecked.program.args.length).Nodup
    exact List.nodup_range
  constructor
  · intro hjustified
    have hsourceStatus :
        Grounded.statusC sourceAF
          (Consistency.completeClaimFor sourceChecked p) =
            Grounded.Status.justified := by
      change Semantics.observe Semantics.groundedSem sourceAF
        (Consistency.completeClaimFor sourceChecked p) =
          .observed Grounded.Status.justified at hjustified
      rw [Semantics.observe_grounded hsourceNodup] at hjustified
      exact Semantics.ClaimObservation.observed.inj hjustified
    have htargetStatus :=
      hsink.justified_preserved hsupportCarrier hsupport hsourceStatus
    change Semantics.observe Semantics.groundedSem targetAF
      (Consistency.completeClaimFor targetChecked p) =
        .observed Grounded.Status.justified
    rw [Semantics.observe_grounded htargetNodup]
    exact congrArg Semantics.ClaimObservation.observed htargetStatus
  · intro hcontested hdefeated
    have hsourceStatus :
        Grounded.statusC sourceAF
          (Consistency.completeClaimFor sourceChecked p) =
            Grounded.Status.contested := by
      change Semantics.observe Semantics.groundedSem sourceAF
        (Consistency.completeClaimFor sourceChecked p) =
          .observed Grounded.Status.contested at hcontested
      rw [Semantics.observe_grounded hsourceNodup] at hcontested
      exact Semantics.ClaimObservation.observed.inj hcontested
    have hnotDefeated :=
      hsink.contested_not_defeated hsupportCarrier hsupport hsourceStatus
    apply hnotDefeated
    change Semantics.observe Semantics.groundedSem targetAF
      (Consistency.completeClaimFor targetChecked p) =
        .observed Grounded.Status.defeated at hdefeated
    rw [Semantics.observe_grounded htargetNodup] at hdefeated
    exact Semantics.ClaimObservation.observed.inj hdefeated


/-! ### Obligations and holes across updates

Hole status is a property of a typed term and the leaf context on its leaves.
`addLeaf` and `addAttack` keep that context on every term the source checks, so
the reported holes are invariant; `tighten` keeps it on every surviving term but
may quarantine a hole, so its reported holes only shrink. `addInstance` is the
only update that can add a hole, and it never removes one (D11). -/

/-- **Obligations of a typed term are local to its leaves.** If `w` types under
`Gamma` and `Gamma'` agrees with `Gamma` on the leaves of `w`, then `w` types
under `Gamma'` with the same conclusion and obligation set, and with no other. -/
theorem typed_obligations_preserved {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma Gamma' : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {w : SupportTerm} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk w C O)
    (hagree : ∀ l ∈ Support.leaves w, Gamma l = Gamma' l) :
    HasSupport canon Pi Gamma' CertOk w C O ∧
      ∀ {C' O'}, HasSupport canon Pi Gamma' CertOk w C' O' →
        C' = C ∧ O' = O := by
  have h' := hasSupport_congr_gamma_on h hagree
  exact ⟨h', fun hC' => hasSupport_unique hC' h'⟩

/-- **`addLeaf` preserves obligations and holes.** A fresh admitted leaf is not
a leaf of any term the source checks, so each keeps its exact conclusion and
obligation set; the retained declarations, the AF arguments and the reported
holes are unchanged. -/
theorem addLeaf_obligations_preserved {canon : String → String}
    (reg : BackendRegistry canon) (source target : SourceState)
    (id : LeafId) (a : Atom) (m : Admission.LeafMeta)
    (sourceDeclared :
      Admission.AlignedAttacks source.argsRaw source.rawAtts)
    (sourceAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetDeclared :
      Admission.AlignedAttacks target.argsRaw target.rawAtts)
    (targetAdmission : Admission.AdmissionResult)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg))
    (hsourceAdmission :
      admissionFor canon source sourceDeclared = .accepted sourceAdmission)
    (hsourceCheck :
      checkAccepted reg source sourceAdmission = .ok sourceChecked)
    (happly : applyUpdate reg source (.addLeaf id a m) = .ok target)
    (htargetAdmission :
      admissionFor canon target targetDeclared = .accepted targetAdmission)
    (htargetCheck :
      checkAccepted reg target targetAdmission = .ok targetChecked)
    (hfresh : AddLeafFresh source id)
    (hadmit :
      Admission.decisionFor source.table m.kind m.provenance = .admit) :
    targetAdmission.prune.keptArgs = sourceAdmission.prune.keptArgs ∧
      (∀ w ∈ sourceAdmission.prune.keptArgs.map (·.2), ∀ C O,
        HasSupport canon source.policy.ruleLookup
          (checkedGamma sourceAdmission) (certOkOf reg) w C O →
        HasSupport canon source.policy.ruleLookup
          (checkedGamma targetAdmission) (certOkOf reg) w C O) ∧
      targetChecked.program.args = sourceChecked.program.args ∧
      targetChecked.program.holes = sourceChecked.program.holes := by
  have htransport :=
    addLeaf_transport reg source target id a m sourceDeclared sourceAdmission
      sourceChecked targetDeclared targetAdmission targetChecked
      hsourceAdmission hsourceCheck happly htargetAdmission htargetCheck hfresh
      hadmit
  exact ⟨htransport.kept_eq,
    fun w hw _ _ h => (typed_obligations_preserved h (htransport.gamma_on w hw)).1,
    htransport.args_eq.symm, htransport.holes_eq.symm⟩

/-- **`addAttack` preserves obligations and holes.** Adding a raw attack
changes neither the leaf context nor the retained declarations, so every term
the source checks keeps its obligations and the reported holes are
unchanged; only the compiled attacks can grow. -/
theorem addAttack_obligations_preserved {canon : String → String}
    (reg : BackendRegistry canon) (source target : SourceState)
    (raw : RawAttack.RawAttack)
    (sourceDeclared :
      Admission.AlignedAttacks source.argsRaw source.rawAtts)
    (sourceAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetDeclared :
      Admission.AlignedAttacks target.argsRaw target.rawAtts)
    (targetAdmission : Admission.AdmissionResult)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg))
    (hsourceAdmission :
      admissionFor canon source sourceDeclared = .accepted sourceAdmission)
    (hsourceCheck :
      checkAccepted reg source sourceAdmission = .ok sourceChecked)
    (happly : applyUpdate reg source (.addAttack raw) = .ok target)
    (htargetAdmission :
      admissionFor canon target targetDeclared = .accepted targetAdmission)
    (htargetCheck :
      checkAccepted reg target targetAdmission = .ok targetChecked) :
    targetAdmission.prune.keptArgs = sourceAdmission.prune.keptArgs ∧
      (∀ w ∈ sourceAdmission.prune.keptArgs.map (·.2), ∀ C O,
        HasSupport canon source.policy.ruleLookup
          (checkedGamma sourceAdmission) (certOkOf reg) w C O →
        HasSupport canon source.policy.ruleLookup
          (checkedGamma targetAdmission) (certOkOf reg) w C O) ∧
      targetChecked.program.args = sourceChecked.program.args ∧
      targetChecked.program.holes = sourceChecked.program.holes := by
  have htargetState := applyUpdate_addAttack_target happly
  subst target
  have hsourcePrune := prune_eq_of_acceptance hsourceAdmission
  have htargetPrune := prune_eq_of_acceptance htargetAdmission
  have hkept :
      targetAdmission.prune.keptArgs = sourceAdmission.prune.keptArgs := by
    rw [htargetPrune, hsourcePrune]
    rfl
  have hgamma :
      checkedGamma targetAdmission = checkedGamma sourceAdmission := by
    funext l
    simp only [checkedGamma, htargetPrune, hsourcePrune]
    rfl
  obtain ⟨hsourceArgs, hsourceHoles⟩ :=
    checked_args_holes_of_acceptance hsourceCheck
  obtain ⟨htargetArgs, htargetHoles⟩ :=
    checked_args_holes_of_acceptance htargetCheck
  dsimp only at htargetArgs htargetHoles
  refine ⟨hkept, fun w _ _ _ h => ?_, ?_, ?_⟩
  · rw [hgamma]
    exact h
  · rw [htargetArgs, hsourceArgs, hkept, hgamma]
  · rw [htargetHoles, hsourceHoles, hkept, hgamma]

/-- **`tighten` preserves obligations on surviving terms.** Under the
retained-context premise of `NonInstanceUpdate.tighten`, every declaration the
target still keeps types with the same conclusion and obligations as in the
source.  The kept declarations and the reported holes can only shrink: a
quarantined hole leaves the accepted report, so the hole list is not
invariant. -/
theorem tighten_obligations_preserved {canon : String → String}
    (reg : BackendRegistry canon) (source target : SourceState)
    (key : LeafKind × Provenance)
    (sourceDeclared :
      Admission.AlignedAttacks source.argsRaw source.rawAtts)
    (sourceAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetDeclared :
      Admission.AlignedAttacks target.argsRaw target.rawAtts)
    (targetAdmission : Admission.AdmissionResult)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg))
    (hsourceAdmission :
      admissionFor canon source sourceDeclared = .accepted sourceAdmission)
    (hsourceCheck :
      checkAccepted reg source sourceAdmission = .ok sourceChecked)
    (happly : applyUpdate reg source (.tighten key) = .ok target)
    (htargetAdmission :
      admissionFor canon target targetDeclared = .accepted targetAdmission)
    (htargetCheck :
      checkAccepted reg target targetAdmission = .ok targetChecked)
    (hnon : NonInstanceUpdate canon source (.tighten key)) :
    targetAdmission.prune.keptArgs.Sublist sourceAdmission.prune.keptArgs ∧
      (∀ w ∈ targetAdmission.prune.keptArgs.map (·.2), ∀ C O,
        HasSupport canon source.policy.ruleLookup
          (checkedGamma sourceAdmission) (certOkOf reg) w C O →
        HasSupport canon source.policy.ruleLookup
          (checkedGamma targetAdmission) (certOkOf reg) w C O) ∧
      targetChecked.program.holes.Sublist sourceChecked.program.holes := by
  cases hnon with
  | tighten key hrestrictive hgammaRetained =>
      have htargetState := applyUpdate_tighten_target happly
      subst target
      have hsourcePrune := prune_eq_of_acceptance hsourceAdmission
      have htargetPrune := prune_eq_of_acceptance htargetAdmission
      have hseedSubset :
          ∀ l,
            l ∈ Admission.policyQuarantineSeed source.table source.metas ++
                Groups.quarantined canon source.leaves source.groups →
            l ∈ Admission.policyQuarantineSeed
                  (tightenTable source.table key) source.metas ++
                Groups.quarantined canon source.leaves source.groups :=
        Admission.removedSeed_subset_of_restrictive hrestrictive canon
          source.metas source.leaves source.groups
      have hkeptSub :
          targetAdmission.prune.keptArgs.Sublist
            sourceAdmission.prune.keptArgs := by
        rw [htargetPrune, hsourcePrune]
        simp only [Admission.buildPrune]
        apply filter_sublist_filter_of_imp
        intro row _ hkeepNew
        by_cases holdUse :
            Groups.usesLeaf
              (Admission.policyQuarantineSeed source.table source.metas ++
                Groups.quarantined canon source.leaves source.groups)
              row.2 = true
        · have hnewUse := Groups.usesLeaf_mono hseedSubset row.2 holdUse
          simp [hnewUse] at hkeepNew
        · simp [holdUse]
      have hgammaOn : ∀ w ∈ targetAdmission.prune.keptArgs.map (·.2),
          ∀ l ∈ Support.leaves w,
            checkedGamma sourceAdmission l = checkedGamma targetAdmission l := by
        intro w hw l hl
        have hwPrune :
            w ∈ (Admission.buildPrune canon (tightenTable source.table key)
              source.metas source.leaves source.argsRaw source.rawAtts
              source.groups []).keptArgs.map (·.2) := by
          rw [htargetPrune] at hw
          simpa only [Admission.buildPrune] using hw
        have hgamma := hgammaRetained w hwPrune l hl
        simpa only [checkedGamma, hsourcePrune, htargetPrune,
          Admission.buildPrune] using hgamma
      obtain ⟨_, hsourceHoles⟩ :=
        checked_args_holes_of_acceptance hsourceCheck
      obtain ⟨_, htargetHoles⟩ :=
        checked_args_holes_of_acceptance htargetCheck
      dsimp only at htargetHoles
      refine ⟨hkeptSub,
        fun w hw _ _ h => (typed_obligations_preserved h (hgammaOn w hw)).1, ?_⟩
      rw [htargetHoles, hsourceHoles]
      have hcongr :
          Check.holeArgs source.policy.ruleLookup
              (checkedGamma targetAdmission) reg
              (targetAdmission.prune.keptArgs.map (·.2)) =
            Check.holeArgs source.policy.ruleLookup
              (checkedGamma sourceAdmission) reg
              (targetAdmission.prune.keptArgs.map (·.2)) :=
        List.filter_congr fun w hw =>
          (Check.argHole_congr_gamma_on (hgammaOn w hw)).symm
      rw [hcongr]
      exact (hkeptSub.map (·.2)).filter _

/-- **Old holes persist under `addInstance` (D11).** Every successful
`addInstance` keeps the source's reported holes as a prefix of the target's;
the new term is appended exactly when it is itself a hole under the unchanged
checked context.  In particular a fresh complete alternative leaves the old
hole reported. -/
theorem addInstance_holes_persist {canon : String → String}
    (reg : BackendRegistry canon) (source target : SourceState)
    (name : String) (w : SupportTerm)
    (sourceDeclared :
      Admission.AlignedAttacks source.argsRaw source.rawAtts)
    (sourceAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetDeclared :
      Admission.AlignedAttacks target.argsRaw target.rawAtts)
    (targetAdmission : Admission.AdmissionResult)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg))
    (hsourceAdmission :
      admissionFor canon source sourceDeclared = .accepted sourceAdmission)
    (hsourceCheck :
      checkAccepted reg source sourceAdmission = .ok sourceChecked)
    (happly : applyUpdate reg source (.addInstance name w) = .ok target)
    (htargetAdmission :
      admissionFor canon target targetDeclared = .accepted targetAdmission)
    (htargetCheck :
      checkAccepted reg target targetAdmission = .ok targetChecked) :
    targetChecked.program.holes = sourceChecked.program.holes ++
      Check.holeArgs source.policy.ruleLookup (checkedGamma sourceAdmission)
        reg [w] :=
  (addInstance_transport reg source target name w sourceDeclared
    sourceAdmission sourceChecked targetDeclared targetAdmission targetChecked
    hsourceAdmission hsourceCheck happly htargetAdmission htargetCheck
    (applyUpdate_addInstance_fresh happly)).holes_eq

/-- **A fresh hole is inert.** A successful `addInstance` whose term is a hole
— it types with a nonempty mandatory obligation set — leaves the AF arguments,
the compiled attacks and the checked context unchanged, so every core
observation is unchanged under every extension semantics.  The only new output
is the hole itself, appended to the reported holes.  This is the conditional
form of inertness; adding an attack onto a hole is not inert (D6). -/
theorem addInstance_hole_core_fixed {canon : String → String}
    (sem : Semantics.ExtensionSemantics) (reg : BackendRegistry canon)
    (source target : SourceState) (p : Atom) (name : String) (w : SupportTerm)
    (sourceDeclared :
      Admission.AlignedAttacks source.argsRaw source.rawAtts)
    (sourceAdmission : Admission.AdmissionResult)
    (sourceChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma sourceAdmission) (certOkOf reg))
    (targetDeclared :
      Admission.AlignedAttacks target.argsRaw target.rawAtts)
    (targetAdmission : Admission.AdmissionResult)
    (targetChecked : Lara.Unit.CheckedUnit canon
      (checkedGamma targetAdmission) (certOkOf reg))
    (hsourceAdmission :
      admissionFor canon source sourceDeclared = .accepted sourceAdmission)
    (hsourceCheck :
      checkAccepted reg source sourceAdmission = .ok sourceChecked)
    (happly : applyUpdate reg source (.addInstance name w) = .ok target)
    (htargetAdmission :
      admissionFor canon target targetDeclared = .accepted targetAdmission)
    (htargetCheck :
      checkAccepted reg target targetAdmission = .ok targetChecked)
    (hnewHole :
      ∃ C O, HasSupport canon source.policy.ruleLookup
        (Admission.buildGamma
          (Admission.buildPrune canon source.table source.metas source.leaves
            source.argsRaw source.rawAtts source.groups []).checkedLeaves)
        (certOkOf reg) w C O ∧ O ≠ []) :
    (CoreTransition sem sourceChecked targetChecked p).1 =
        (CoreTransition sem sourceChecked targetChecked p).2 ∧
      targetChecked.program.holes = sourceChecked.program.holes ++ [w] := by
  have htransport :=
    addInstance_transport reg source target name w sourceDeclared
      sourceAdmission sourceChecked targetDeclared targetAdmission
      targetChecked hsourceAdmission hsourceCheck happly htargetAdmission
      htargetCheck (applyUpdate_addInstance_fresh happly)
  obtain ⟨C, O, hC, hO⟩ := hnewHole
  have hCchecked :
      HasSupport canon source.policy.ruleLookup
        (checkedGamma sourceAdmission) (certOkOf reg) w C O := by
    simpa only [checkedGamma, prune_eq_of_acceptance hsourceAdmission,
      Admission.buildPrune] using hC
  have hhole :
      Check.argHole source.policy.ruleLookup (checkedGamma sourceAdmission)
        reg w = true := Check.argHole_iff.mpr ⟨C, O, hCchecked, hO⟩
  have hnotComplete :
      Check.argComplete source.policy.ruleLookup
        (checkedGamma sourceAdmission) reg w = false := by
    rw [Check.argComplete_of_hasSupport hCchecked]
    cases O with
    | nil => exact absurd rfl hO
    | cons q qs => rfl
  have hargs : sourceChecked.program.args = targetChecked.program.args := by
    rw [htransport.args_eq]
    simp [Check.completeArgs, hnotComplete]
  have hedge :
      Compile.edgeB sourceChecked.program =
        Compile.edgeB targetChecked.program := by
    funext i j
    unfold Compile.edgeB
    rw [hargs, htransport.atts_eq]
  have hframework :
      Compile.checkedAF sourceChecked.program =
        Compile.checkedAF targetChecked.program := by
    unfold Compile.checkedAF Compile.toAF
    rw [congrArg List.length hargs, hedge]
  have hclaimMem : ∀ i,
      i ∈ (Consistency.completeClaimFor sourceChecked p).support ↔
        i ∈ (Consistency.completeClaimFor targetChecked p).support := by
    intro i
    exact mem_claimSupportFor_congr sourceChecked targetChecked
      htransport.policy_eq.symm hargs
      (fun h => by rw [htransport.gamma_eq]; exact h) p i
  refine ⟨?_, ?_⟩
  · simp only [CoreTransition]
    unfold coreObs
    rw [hframework]
    exact observe_support_congr sem
      (Compile.checkedAF targetChecked.program)
      (Consistency.completeClaimFor sourceChecked p)
      (Consistency.completeClaimFor targetChecked p) hclaimMem
  · rw [htransport.holes_eq]
    simp [Check.holeArgs, hhole]


/-! ### Public-row safety and the legacy quarantine corollary -/


/-- An exact successful tighten cannot promote an atom into a justified public
target unless its lifted claim was justified in the clean source's declared
framework.  The transition theorem supplies source checked justification; the
clean-run row theorem then lifts it along the source's checked carrier into
the declared framework over the specification carrier, which is the
conclusion shape of `Admission.source_justified_nonpromotion`. -/
theorem quarantine_nonpromotion_corollary
    {canon : String → String} {reg : BackendRegistry canon}
    {source target : SourceState} {key : LeafKind × Provenance}
    (sourceRun : AcceptedRun reg source)
    (targetRun : AcceptedRun reg target)
    (happly : applyUpdate reg source (.tighten key) = .ok target)
    (hnon : NonInstanceUpdate canon source (.tighten key))
    (hclean : CleanBase sourceRun) (p : Atom)
    (htargetPublic : publicReport targetRun p = .justified) :
    Grounded.statusC
      (BlockedProgram.declaredAF source.argsRaw sourceRun.declared.resolved
        (declaredCarrier reg source))
      (BlockedProgram.liftClaim (checkedCarrierForRun sourceRun)
        (Consistency.completeClaimFor sourceRun.checked p)) = .justified :=
  tighten_public_row_justified_nonpromotion sourceRun hclean p
    (tighten_public_justified_source_justified sourceRun targetRun happly hnon
      hclean p htargetPublic)

end Lara.Update
