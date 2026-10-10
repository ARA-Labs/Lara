import Lara.Process.Order
import Lara.Process.Coverage

/-!
R6: the ARA decoded-record bridge.

An ARA record is decoded, at the boundary, into a symbolic `DecodedRecord`:
identified events, explicit precedence constraints and scoped coverage
assertions, each carrying the ARA file/entry reference and source span it came
from, plus the submitted claims and witnesses. Source references are decode-
boundary evidence, not semantic identifiers; nothing in the theory reads them
except to report them.

The ARA-side input is modeled as an `AraSource`: a list of entries (events,
including failed and sibling trials that lower to no attack edge, ordering
evidence, and coverage attestations with their admission basis). `extract`
keeps every event and ordering entry and admits exactly the attestations whose
basis the reader admits. It never invents an order from file position and never
replaces a missing attestation by a closed-world default.

* `extraction_preserves_compatibility`: a modeled history that satisfies the
  source relation under the admitted bases remains compatible with the
  extracted record.
* `extraction_overapprox_safe`: an extraction admitting a superset of the
  source-compatible histories can lose certainty but never invents it.
* `encode_extract`: encoding a decoded record as ARA entries and extracting it
  is the identity (a section/retraction pair). It is representation
  consistency only; no round trip reconstructs a unique history.
* `verdict_invariant`, `verdictQ`: verdicts respect the representation's
  equivalence and lift to the quotient.
-/

namespace Lara.Process

/-! ### Decode-boundary evidence -/

/-- Where a decoded fact came from: an ARA file, an entry within it and, when
available, a source span. Plain strings are correct here: this is the decode
boundary, and the theory never interprets them. -/
structure SourceRef where
  file : String
  entry : String
  span : Option (Nat × Nat)
  deriving DecidableEq, Repr

/-- Why a coverage attestation may be admitted. An attestation labeled
complete does not prove its own reliability; a reader states which bases it
admits. -/
inductive AdmissionBasis where
  | instrumentedLog
  | signedAttestation
  | authorDeclaration
  deriving DecidableEq, Repr

/-- The one spelling table for admission bases. -/
def AdmissionBasis.label : AdmissionBasis → String
  | .instrumentedLog => "instrumented log"
  | .signedAttestation => "signed attestation"
  | .authorDeclaration => "author declaration"

/-- A coverage assertion with its evidence reference and admission basis. -/
structure CoverageAssertion (Policy : Type) where
  coverage : RecordCoverage Policy
  evidence : SourceRef
  basis : AdmissionBasis
  deriving DecidableEq, Repr

/-- A decoded event with its source reference. -/
structure DecodedEvent where
  event : Stamped
  source : SourceRef
  deriving DecidableEq, Repr

/-- A decoded precedence constraint with its source reference. -/
structure DecodedOrder where
  first : EventId
  second : EventId
  source : SourceRef
  deriving DecidableEq, Repr

/-- The symbolic decoded record. -/
structure DecodedRecord (Policy : Type) where
  events : List DecodedEvent
  order : List DecodedOrder
  coverage : List (CoverageAssertion Policy)
  submitted : List (ClaimId × WitnessId)
  cutoff : Nat
  deriving DecidableEq, Repr

namespace DecodedRecord

variable {Policy : Type}

/-- The partial-order record a decoded record states. -/
def toOrderRecord (d : DecodedRecord Policy) : OrderRecord :=
  ⟨d.events.map DecodedEvent.event, d.order.map fun o => (o.first, o.second), d.cutoff⟩

/-- A complete history is compatible with a decoded record when it is
compatible with its partial order and satisfies every coverage assertion,
reading the record's events as the reported ones. -/
def Compatible (policy : Policy → ProcessHistory → List Stamped → Prop)
    (d : DecodedRecord Policy) (h : ProcessHistory) : Prop :=
  OrderCompatible d.toOrderRecord h ∧
    ∀ c ∈ d.coverage, c.coverage.Allowed policy h (d.events.map DecodedEvent.event)

instance (policy : Policy → ProcessHistory → List Stamped → Prop)
    [∀ p h r, Decidable (policy p h r)] (d : DecodedRecord Policy) (h : ProcessHistory) :
    Decidable (d.Compatible policy h) :=
  inferInstanceAs (Decidable (_ ∧ _))

end DecodedRecord

/-! ### The ARA side and extraction -/

/-- One ARA entry, as the bridge sees it. Event entries include failed and
sibling trials. -/
inductive AraEntry (Policy : Type) where
  | event (event : Stamped) (source : SourceRef)
  | ordering (first second : EventId) (source : SourceRef)
  | coverage (assertion : CoverageAssertion Policy)
  | submission (claim : ClaimId) (witness : WitnessId)
  deriving DecidableEq, Repr

/-- An ARA record as a list of entries and its submission cutoff. Entry order
is file order and carries no meaning. -/
structure AraSource (Policy : Type) where
  entries : List (AraEntry Policy)
  cutoff : Nat
  deriving DecidableEq, Repr

variable {Policy : Type}

def AraEntry.event? : AraEntry Policy → Option DecodedEvent
  | .event e s => some ⟨e, s⟩
  | _ => none

def AraEntry.ordering? : AraEntry Policy → Option DecodedOrder
  | .ordering a b s => some ⟨a, b, s⟩
  | _ => none

def AraEntry.coverage? : AraEntry Policy → Option (CoverageAssertion Policy)
  | .coverage c => some c
  | _ => none

def AraEntry.submission? : AraEntry Policy → Option (ClaimId × WitnessId)
  | .submission c w => some (c, w)
  | _ => none

/-- Extraction: keep every event, ordering and submission entry, and admit
exactly the coverage attestations whose basis is admitted. Several submissions
stay several; none is preferred by file position. -/
def extract (admitted : AdmissionBasis → Bool) (src : AraSource Policy) : DecodedRecord Policy where
  events := src.entries.filterMap AraEntry.event?
  order := src.entries.filterMap AraEntry.ordering?
  coverage := (src.entries.filterMap AraEntry.coverage?).filter fun c => admitted c.basis
  submitted := src.entries.filterMap AraEntry.submission?
  cutoff := src.cutoff

/-- The source relation: what it means for a modeled history to be faithfully
described by the ARA source under the admitted bases. The history is valid
through the cutoff, contains every event entry, respects every ordering entry,
and satisfies every admitted coverage attestation. This is the trust boundary:
it is an assumption about the source, not something the theory checks. -/
def SourceRel (policy : Policy → ProcessHistory → List Stamped → Prop)
    (admitted : AdmissionBasis → Bool) (src : AraSource Policy) (h : ProcessHistory) : Prop :=
  ValidThrough src.cutoff h ∧
    (∀ e s, AraEntry.event e s ∈ src.entries → e ∈ h) ∧
    (∀ a b s, AraEntry.ordering a b s ∈ src.entries → h.Precedes a b) ∧
    ∀ c, AraEntry.coverage c ∈ src.entries → admitted c.basis = true →
      c.coverage.Allowed policy h ((src.entries.filterMap AraEntry.event?).map DecodedEvent.event)

/-- Extraction preserves compatibility: every modeled history the source
faithfully describes is compatible with the extracted record. Together with
`verdict_sound`, a certain verdict on the extracted record holds at the
generating history, conditional on source fidelity and the admitted bases. -/
theorem extraction_preserves_compatibility (policy : Policy → ProcessHistory → List Stamped → Prop)
    (admitted : AdmissionBasis → Bool) (src : AraSource Policy) {h : ProcessHistory}
    (rel : SourceRel policy admitted src h) : (extract admitted src).Compatible policy h := by
  obtain ⟨valid, events, order, coverage⟩ := rel
  refine ⟨⟨valid, ?_, ?_⟩, ?_⟩
  · intro e he
    simp only [DecodedRecord.toOrderRecord, extract, List.mem_map, List.mem_filterMap] at he
    obtain ⟨d, ⟨entry, mem, hentry⟩, rfl⟩ := he
    cases entry with
    | event e s => cases hentry; exact events e s mem
    | _ => cases hentry
  · intro c hc
    simp only [DecodedRecord.toOrderRecord, extract, List.mem_map, List.mem_filterMap] at hc
    obtain ⟨o, ⟨entry, mem, hentry⟩, rfl⟩ := hc
    cases entry with
    | ordering a b s => cases hentry; exact order a b s mem
    | _ => cases hentry
  · intro c hc
    simp only [extract, List.mem_filter, List.mem_filterMap] at hc
    obtain ⟨⟨entry, mem, hentry⟩, adm⟩ := hc
    cases entry with
    | coverage a =>
      simp only [AraEntry.coverage?, Option.some.injEq] at hentry
      subst hentry
      exact coverage _ mem adm
    | _ => cases hentry

/-- A determinate verdict on the extracted record holds for every history the
source faithfully describes. -/
theorem extraction_verdict_sound (policy : Policy → ProcessHistory → List Stamped → Prop)
    (admitted : AdmissionBasis → Bool) (src : AraSource Policy) {φ : ProcessHistory → Prop}
    (certain : verdictOf ((extract admitted src).Compatible policy) φ = .certainTrue)
    {h : ProcessHistory} (rel : SourceRel policy admitted src h) : φ h :=
  verdict_sound certain h (extraction_preserves_compatibility policy admitted src rel)

/-- Conservative overapproximation is safe: if an extraction admits every
history the source admits, and the source admits one, a determinate extracted
verdict transfers to the source. Extra possibilities can lose certainty, never
invent it. -/
theorem extraction_overapprox_safe {X : Type} {sourceCompat extracted : X → Prop}
    (over : ∀ x, sourceCompat x → extracted x) (nonempty : ∃ x, sourceCompat x)
    {φ : X → Prop} {v : Verdict} (hv : verdictOf extracted φ = v) (det : Determinate v) :
    verdictOf sourceCompat φ = v :=
  certain_refine over nonempty hv det

/-- The bridge instance: extraction admits every history the source faithfully
describes, so a determinate verdict on the extracted record is the verdict on
the source-described histories whenever there is one. -/
theorem extraction_safe_for_source (policy : Policy → ProcessHistory → List Stamped → Prop)
    (admitted : AdmissionBasis → Bool) (src : AraSource Policy)
    (described : ∃ h, SourceRel policy admitted src h) {φ : ProcessHistory → Prop} {v : Verdict}
    (hv : verdictOf ((extract admitted src).Compatible policy) φ = v) (det : Determinate v) :
    verdictOf (SourceRel policy admitted src) φ = v :=
  extraction_overapprox_safe (fun _ rel => extraction_preserves_compatibility policy admitted src rel)
    described hv det

/-! ### Encoding: a section/retraction pair -/

/-- Encode a decoded record as ARA entries. -/
def encode (d : DecodedRecord Policy) : AraSource Policy where
  entries := d.events.map (fun e => .event e.event e.source) ++
    d.order.map (fun o => .ordering o.first o.second o.source) ++
    d.coverage.map .coverage ++ d.submitted.map fun s => .submission s.1 s.2
  cutoff := d.cutoff

/-- Extraction retracts encoding when every attestation is admitted. This is
representation consistency only: it reconstructs the decoded record, never a
unique complete history. -/
theorem encode_extract (d : DecodedRecord Policy) : extract (fun _ => true) (encode d) = d := by
  obtain ⟨events, order, coverage, submitted, cutoff⟩ := d
  simp only [extract, encode, List.filterMap_append, List.filterMap_map, List.filter_true]
  congr 1 <;> simp [AraEntry.event?, AraEntry.ordering?, AraEntry.coverage?, AraEntry.submission?]

/-! ### Invariance -/

/-- Two decoded records are equivalent when they admit the same complete
histories. -/
def recordSetoid (policy : Policy → ProcessHistory → List Stamped → Prop) :
    Setoid (DecodedRecord Policy) where
  r d d' := ∀ h, d.Compatible policy h ↔ d'.Compatible policy h
  iseqv := ⟨fun _ _ => Iff.rfl, fun e h => (e h).symm, fun e e' h => (e h).trans (e' h)⟩

/-- Verdicts respect the representation's equivalence. -/
theorem verdict_invariant (policy : Policy → ProcessHistory → List Stamped → Prop)
    {d d' : DecodedRecord Policy} (equiv : (recordSetoid policy).r d d') (φ : ProcessHistory → Prop) :
    verdictOf (d.Compatible policy) φ = verdictOf (d'.Compatible policy) φ := by
  have : d.Compatible policy = d'.Compatible policy := funext fun h => propext (equiv h)
  rw [this]

/-- The verdict on the quotient of decoded records by equivalence. -/
noncomputable def verdictQ (policy : Policy → ProcessHistory → List Stamped → Prop)
    (φ : ProcessHistory → Prop) : Quotient (recordSetoid policy) → Verdict :=
  Quotient.lift (fun d => verdictOf (d.Compatible policy) φ) fun _ _ e => verdict_invariant policy e φ

/-- Coverage assertions read the reported events as a set, as long as the
declared policies do. -/
theorem RecordCoverage.allowed_perm (policy : Policy → ProcessHistory → List Stamped → Prop)
    (policyPerm : ∀ p h r r', r.Perm r' → (policy p h r ↔ policy p h r'))
    (c : RecordCoverage Policy) (h : ProcessHistory) {r r' : List Stamped} (perm : r.Perm r') :
    c.Allowed policy h r ↔ c.Allowed policy h r' := by
  cases c with
  | complete scope => exact forall₂_congr fun e _ => perm.mem_iff
  | countBounded => exact Iff.rfl
  | declaredPolicy _ p => exact policyPerm p h r r' perm
  | openWorld => exact Iff.rfl

/-- Reordering a record's events or constraints yields an equivalent record. -/
theorem perm_equivalent (policy : Policy → ProcessHistory → List Stamped → Prop)
    {d d' : DecodedRecord Policy} (events : (d.events.map DecodedEvent.event).Perm
      (d'.events.map DecodedEvent.event))
    (order : ∀ c, c ∈ d.order.map (fun o => (o.first, o.second)) ↔
      c ∈ d'.order.map (fun o => (o.first, o.second)))
    (coverage : ∀ c, c ∈ d.coverage.map CoverageAssertion.coverage ↔
      c ∈ d'.coverage.map CoverageAssertion.coverage)
    (cutoff : d.cutoff = d'.cutoff) (allowedPerm : ∀ c h r r', r.Perm r' →
      (RecordCoverage.Allowed policy c h r ↔ RecordCoverage.Allowed policy c h r')) :
    (recordSetoid policy).r d d' := by
  intro h
  unfold DecodedRecord.Compatible OrderCompatible DecodedRecord.toOrderRecord
  simp only
  rw [cutoff]
  constructor
  · rintro ⟨⟨v, mem, before⟩, cov⟩
    refine ⟨⟨v, fun e he => mem e (events.mem_iff.mpr he), fun c hc => before c ((order c).mpr hc)⟩,
      fun c hc => ?_⟩
    obtain ⟨c₀, hc₀, eq⟩ := List.mem_map.mp ((coverage c.coverage).mpr (List.mem_map_of_mem hc))
    have := cov c₀ hc₀
    rw [eq] at this
    exact (allowedPerm _ _ _ _ events).mp this
  · rintro ⟨⟨v, mem, before⟩, cov⟩
    refine ⟨⟨v, fun e he => mem e (events.mem_iff.mp he), fun c hc => before c ((order c).mp hc)⟩,
      fun c hc => ?_⟩
    obtain ⟨c₀, hc₀, eq⟩ := List.mem_map.mp ((coverage c.coverage).mp (List.mem_map_of_mem hc))
    have := cov c₀ hc₀
    rw [eq] at this
    exact (allowedPerm _ _ _ _ events).mpr this

/-! ### Separation -/

/-- A coarsening `π` separates a property `φ` when two complete histories with
the same projection disagree on it. -/
def Separates {H P : Type} (π : H → P) (φ : H → Prop) : Prop :=
  ∃ h₁ h₂, π h₁ = π h₂ ∧ φ h₁ ∧ ¬ φ h₂

/-- The shared coarse record of a separating pair has one verdict, `unknown`:
never two contradictory entitlements. -/
theorem separation_unknown {H P : Type} {π : H → P} {φ : H → Prop}
    {h₁ h₂ : H} (same : π h₁ = π h₂) (yes : φ h₁) (no : ¬ φ h₂) :
    verdictOf (fun h => π h = π h₁) φ = .unknown :=
  (verdictOf_unknown_iff _ _).mpr ⟨h₁, h₂, rfl, same.symm, yes, no⟩

/-- A coarsening that separates `φ` cannot support an exact evaluator for it. -/
theorem separates_not_factors {H P : Type} {π : H → P} {φ : H → Prop}
    (sep : Separates π φ) : ¬ Factors (fun _ => True) π φ := by
  obtain ⟨h₁, h₂, same, yes, no⟩ := sep
  exact fun fac => no ((fac h₁ h₂ trivial trivial same).mp yes)

end Lara.Process
