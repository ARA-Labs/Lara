import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Rat.Defs

/-!
The frozen vocabulary of the research-process layer (`Lara.Process`).

This layer is an outer layer over the core calculus and BHL and changes
neither. It talks
about *research processes*: who committed which analysis plan, which data was
read for which purpose, which runs produced which results, which claims were
asserted on which justification, and which sources were later retracted or
updated. Every fixed vocabulary is a closed sum type and every identifier is a
distinct newtype, so the process layer manipulates symbols, never strings
whose meaning depends on a surface syntax or an ARA file layout.

Nothing here asserts that a physical logger observed every action. A process
history is a modeled object; the coverage vocabulary below states, with an
explicit scope, how much of it a record claims to contain.
-/

namespace Lara.Process

/-! ### Identifiers

Separate namespaces get separate types so that, for example, a plan identity
can never be silently used as a dataset identity. -/

structure EventId where
  index : Nat
  deriving DecidableEq, Repr

structure ActorId where
  index : Nat
  deriving DecidableEq, Repr

structure PlanId where
  index : Nat
  deriving DecidableEq, Repr

structure RunId where
  index : Nat
  deriving DecidableEq, Repr

structure ClaimId where
  index : Nat
  deriving DecidableEq, Repr

structure SourceId where
  index : Nat
  deriving DecidableEq, Repr

/-- A dataset identity. Distinct from `Lara.BHL.DatasetId`, whose values are
BHL program names; equal identities here are a modeling decision, and distinct
identities never imply statistically independent samples. -/
structure DataId where
  index : Nat
  deriving DecidableEq, Repr

structure VersionId where
  index : Nat
  deriving DecidableEq, Repr

/-- A statistical family: the set of tests whose multiplicity a guarantee must
account for. Membership is declared by the run event, not inferred from which
results were reported. -/
structure FamilyId where
  index : Nat
  deriving DecidableEq, Repr

/-- A justification witness: one particular submitted argument for a claim. -/
structure WitnessId where
  index : Nat
  deriving DecidableEq, Repr

/-! ### Events -/

/-- Why a dataset was read. Selection reads choose an analysis; evaluation
reads feed the test whose guarantee is claimed. -/
inductive AccessPurpose where
  | selection
  | evaluation
  deriving DecidableEq, Repr

/-- The closed vocabulary of event kinds. -/
inductive EventKind where
  | planCommit
  | dataAccess
  | analysisRun
  | resultProduced
  | claimAsserted
  | sourceRetracted
  | dataUpdated
  deriving DecidableEq, Repr

/-- One modeled research event. A plan commitment fixes one plan version. A run
names the plan version and the input dataset versions it actually used and the
statistical family it belongs to; a result refers to a run. -/
inductive Event where
  | commitPlan (actor : ActorId) (plan : PlanId) (version : VersionId)
  | access (actor : ActorId) (data : DataId) (purpose : AccessPurpose)
  | run (run : RunId) (plan : PlanId) (version : VersionId) (inputs : List (DataId × VersionId))
      (family : FamilyId)
  | result (run : RunId) (outcome : Nat)
  | assert (claim : ClaimId) (witness : WitnessId)
  | retract (source : SourceId)
  | updateData (data : DataId) (version : VersionId)
  deriving DecidableEq, Repr

def Event.kind : Event → EventKind
  | .commitPlan .. => .planCommit
  | .access .. => .dataAccess
  | .run .. => .analysisRun
  | .result .. => .resultProduced
  | .assert .. => .claimAsserted
  | .retract .. => .sourceRetracted
  | .updateData .. => .dataUpdated

/-- The acting party of an event, when the event has one. -/
def Event.actor? : Event → Option ActorId
  | .commitPlan actor _ _ => some actor
  | .access actor _ _ => some actor
  | _ => none

/-- The datasets an event touches. -/
def Event.data : Event → List DataId
  | .access _ data _ => [data]
  | .run _ _ _ inputs _ => inputs.map Prod.fst
  | .updateData data _ => [data]
  | _ => []

/-- The statistical family of a run event. -/
def Event.family? : Event → Option FamilyId
  | .run _ _ _ _ family => some family
  | _ => none

/-- An event with its identity. Records cite events by identity; neither file
order nor display order is evidence of temporal order. -/
structure Stamped where
  id : EventId
  event : Event
  deriving DecidableEq, Repr

/-- A complete modeled process history: the events in their actual order.
Unlike `Lara.BHL.History`, which is a multiset of test occurrences, the list
order is part of the history. -/
abbrev ProcessHistory := List Stamped

/-! ### Coverage

Coverage assumptions are scoped compatibility predicates, not rungs of a
universal strength ladder. Strength is compared by inclusion of compatible
sets on one model and scope (`Lara.Process.Assumptions.Stronger`). -/

/-- The part of a history a coverage assertion speaks about: event kinds, an
optional statistical family, optional actor and dataset restrictions (`none`
means unrestricted; a restricted scope excludes events that carry no actor or
no dataset) and a submission cutoff on history positions. -/
structure CoverageScope where
  kinds : List EventKind
  family : Option FamilyId
  actors : Option (List ActorId)
  data : Option (List DataId)
  cutoff : Nat
  deriving DecidableEq, Repr

/-- A scoped coverage assumption. `Policy` is the closed vocabulary of declared
reporting policies a particular model interprets. -/
inductive RecordCoverage (Policy : Type) where
  | complete (scope : CoverageScope)
  | countBounded (scope : CoverageScope) (bound : Nat)
  | declaredPolicy (scope : CoverageScope) (policy : Policy)
  | openWorld (scope : CoverageScope)
  deriving DecidableEq, Repr

/-- The one spelling table for coverage kinds; a declared policy is spelled by
the model that interprets it. -/
def RecordCoverage.label {Policy : Type} (policyLabel : Policy → String) :
    RecordCoverage Policy → String
  | .complete _ => "complete"
  | .countBounded _ bound => s!"at most {bound}"
  | .declaredPolicy _ p => policyLabel p
  | .openWorld _ => "open world"

def RecordCoverage.scope {Policy : Type} : RecordCoverage Policy → CoverageScope
  | .complete scope | .countBounded scope _ | .declaredPolicy scope _ | .openWorld scope => scope

/-! ### Verdicts -/

/-- The four verdicts of a record on a property of complete histories.
`inconsistent` is the verdict of a record with no compatible history; it is
never a positive answer. -/
inductive Verdict where
  | inconsistent
  | certainTrue
  | certainFalse
  | unknown
  deriving DecidableEq, Repr

/-- The one spelling table for verdicts. -/
def Verdict.label : Verdict → String
  | .inconsistent => "inconsistent"
  | .certainTrue => "certainTrue"
  | .certainFalse => "certainFalse"
  | .unknown => "unknown"

/-! ### Evidence kinds and profiles -/

/-- The evidence-kind lattice `hypothetical < conditional < supported <
observed`. This ordering is this layer's own construction; existing ARA
provenance labels are not silently read as members of it. -/
inductive EvidenceKind where
  | hypothetical
  | conditional
  | supported
  | observed
  deriving DecidableEq, Repr, Fintype

def EvidenceKind.rank : EvidenceKind → Fin 4
  | .hypothetical => 0
  | .conditional => 1
  | .supported => 2
  | .observed => 3

theorem EvidenceKind.rank_injective : Function.Injective EvidenceKind.rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

instance : LinearOrder EvidenceKind :=
  LinearOrder.lift' EvidenceKind.rank EvidenceKind.rank_injective

instance : Lattice EvidenceKind := inferInstance

instance : BoundedOrder EvidenceKind where
  top := .observed
  le_top a := by cases a <;> decide
  bot := .hypothetical
  bot_le a := by cases a <;> decide

theorem EvidenceKind.le_iff_rank {a b : EvidenceKind} : a ≤ b ↔ a.rank ≤ b.rank := by rfl

/-- Every evidence kind, in lattice order. -/
def EvidenceKind.all : List EvidenceKind := [.hypothetical, .conditional, .supported, .observed]

theorem EvidenceKind.mem_all (k : EvidenceKind) : k ∈ EvidenceKind.all := by
  cases k <;> simp [EvidenceKind.all]

def EvidenceKind.label : EvidenceKind → String
  | .hypothetical => "hypothetical"
  | .conditional => "conditional"
  | .supported => "supported"
  | .observed => "observed"

/-- Named error sources a method can be required to have probed. -/
inductive ErrorKind where
  | sampling
  | selection
  | optionalStopping
  | misspecification
  | measurement
  deriving DecidableEq, Repr

/-- Every error kind. -/
def ErrorKind.all : List ErrorKind :=
  [.sampling, .selection, .optionalStopping, .misspecification, .measurement]

theorem ErrorKind.mem_all (k : ErrorKind) : k ∈ ErrorKind.all := by
  cases k <;> simp [ErrorKind.all]

def ErrorKind.label : ErrorKind → String
  | .sampling => "sampling"
  | .selection => "selection"
  | .optionalStopping => "optional stopping"
  | .misspecification => "misspecification"
  | .measurement => "measurement"

/-- The guarantee class of a statistical claim. FDR and mFDR are different
classes: a procedure controlling one need not control the other. -/
inductive GuaranteeClass where
  | fwer
  | fdr
  | mfdr
  deriving DecidableEq, Repr

def GuaranteeClass.label : GuaranteeClass → String
  | .fwer => "FWER"
  | .fdr => "FDR"
  | .mfdr => "mFDR"

/-- The acceptance standard a profile requires of the justification witness.
The only standard defined here is grounded `justified`. -/
inductive Acceptance where
  | groundedJustified
  deriving DecidableEq, Repr

def Acceptance.label : Acceptance → String
  | .groundedJustified => "grounded justified"

/-- An explicit inductive-risk profile. The coverage policy is a decidable
predicate over scoped assumptions, never an order on `RecordCoverage`
constructors. -/
structure Profile (Policy : Type) where
  admissible : Finset EvidenceKind
  acceptsCoverage : RecordCoverage Policy → Bool
  guarantee : GuaranteeClass × ℚ
  requiredProbes : Finset ErrorKind
  acceptance : Acceptance

end Lara.Process
