import Lara.Process.Analysis
import Lara.Process.AnalysisWire
import Lara.Examples.ProcessSource
import Lara.Examples.ProcessSourceProfiles

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 1024

/-!
Kernel-checked fixtures for the P3 analyses (issue #22).

Structural shape. Each fixture family is materialized and checked by the landed
source observer *once*, through `Source.checkFamily family config completions`;
that single `CheckedFamily` is the only place a checker runs. The family's
already-prepared rows are projected once into an observation table
(`statusObservations`), and that one table is then pinned to a concrete literal
list (`*_table`) with a single kernel reduction. Every other declaration reads
the family through a `tableRead` over that table (`*Read`, proved equal to
`tableRead (statusObservations …)` by `*Read_eq`), so no later proof re-runs a
checker, re-derives a status, or re-reads a row pairwise. The observable-specific
entry points (`statusStability`, `statusSensitivity`, `statusAssumptions`) are
linked to the generic records by `*_…_eq`, and every count, status, minimal set
and witness is asserted as concrete data (counts, statuses, completions and
deletion witnesses), never as a bare boolean.

Reduction-cost note (for the next fixture author): an accepted `checkSource` over
a small program reduces in fractions of a second, but a *rejected* one forces the
whole nested `Surface.SourceDiagnostic` payload, and that cost grows with the
program — minutes over a five-rule graph with contraries and attacks, still only
fractions of a second over the minimal two-leaf program. So the rejected-only
fixtures are built on a minimal two-leaf program (`minSource`), the deep
`duplicateLeafId` diagnostic is named once as `minRejection`, and it is reduced
only on that program (the `minMixed` and `minAllRej` tables and the dedicated
`duplicateLeaf_exact_rejection` fixture). Do not put a large program behind a
rejected row unless every such row is bound once as an abstract `def`.

The five fixture families are the empty one, a uniformly accepted one, the
all-accepted but status-varying joint one, a mixed-rejection one and an
all-rejected one.

The joint family is the two-independent-defender graph: the target is attacked
by `a1` and `a2`; `d1` rebuts `a1` and `d2` rebuts `a2`. At reference
`(absent, absent)` the target is defeated, either single defender still leaves
it defeated, and both make it justified — so the only minimal joint change set
is the pair, and neither singleton flips.
-/

namespace Lara.Examples.ProcessAnalysis

open Lara
open Lara.Process
open Lara.Process.Source
open Lara.Process.Family
open Lara.Process.Analysis
open Lara.Process.Analysis.AnalysisWire

/-! ### Vocabulary -/

def atom (name : String) : Lara.Atom := .atom name .nil

def rule (name premise conclusion : String) : Presentation.Rule :=
  { id := ⟨name⟩, params := [], mode := .defeasible
    premises := [⟨premise, .nil⟩], premiseLabels := [], conclusion := ⟨conclusion, .nil⟩
    allowTrusted := false, certifiers := [], questions := [] }

def claimDecl : Presentation.Decl :=
  .claim ⟨⟨"claim"⟩, "Target", atom "t", ⟨"reader", "target interpretation", .reviewed⟩⟩

def argument (name method premise : String) (target : Presentation.ArgConcl) : Presentation.Decl :=
  .arg ⟨⟨name⟩, target, .inferTheta ⟨method⟩ [⟨premise⟩] [] [] .none⟩

def seedLeaf : Presentation.Decl :=
  .leaf ⟨⟨"seed"⟩, atom "seed", .observed, .user, [], none⟩

/-! ### The graph-bearing (joint) source -/

def policy : Presentation.Policy :=
  { Lara.Examples.ProcessSource.ordinaryInput.policy with
    sigma := ⟨[], [], [⟨⟨"seed"⟩, []⟩, ⟨⟨"s1"⟩, []⟩, ⟨⟨"s2"⟩, []⟩,
      ⟨⟨"u1"⟩, []⟩, ⟨⟨"u2"⟩, []⟩, ⟨⟨"t"⟩, []⟩]⟩
    rules := [rule "r-t" "seed" "t", rule "r-a1" "seed" "s1", rule "r-a2" "seed" "s2",
      rule "r-d1" "seed" "u1", rule "r-d2" "seed" "u2"]
    contraries := [⟨⟨"s1", .nil⟩, ⟨"t", .nil⟩⟩, ⟨⟨"s2", .nil⟩, ⟨"t", .nil⟩⟩,
      ⟨⟨"u1", .nil⟩, ⟨"s1", .nil⟩⟩, ⟨⟨"u2", .nil⟩, ⟨"s2", .nil⟩⟩]
    theories := [] }

def baseDecls : List Presentation.Decl :=
  [seedLeaf, claimDecl,
   argument "w" "r-t" "seed" (.supportsClaim ⟨"claim"⟩),
   argument "a1" "r-a1" "seed" (.supportsDerived ⟨"attack1"⟩),
   argument "a2" "r-a2" "seed" (.supportsDerived ⟨"attack2"⟩),
   .attack (.rebut ⟨"a1"⟩ ⟨"w"⟩), .attack (.rebut ⟨"a2"⟩ ⟨"w"⟩)]

def fragD1 : List Presentation.Decl :=
  [argument "d1" "r-d1" "seed" (.supportsDerived ⟨"defense1"⟩),
   .attack (.rebut ⟨"d1"⟩ ⟨"a1"⟩)]

def fragD2 : List Presentation.Decl :=
  [argument "d2" "r-d2" "seed" (.supportsDerived ⟨"defense2"⟩),
   .attack (.rebut ⟨"d2"⟩ ⟨"a2"⟩)]

/-- The base checked source, with whatever extra declarations a choice adds. -/
def source (extra : List Presentation.Decl) : SourceInput :=
  let surface : Surface.Input :=
    { policy
      program := { Lara.Examples.ProcessSource.ordinaryInput.program with
        policy := policy.id, backends := [], decls := baseDecls ++ extra } }
  { surface, replay := ⟨⟨Driver.coreVersionText⟩, policy.id, [], [], surface.program.digest⟩
    capture := none }

/-- A minimal accepted program: just the seed leaf and the target claim. -/
def minPolicy : Presentation.Policy :=
  { Lara.Examples.ProcessSource.ordinaryInput.policy with
    sigma := ⟨[], [], [⟨⟨"seed"⟩, []⟩]⟩, rules := [], contraries := [], theories := [] }

def minSource (extra : List Presentation.Decl) : SourceInput :=
  let surface : Surface.Input :=
    { policy := minPolicy
      program := { Lara.Examples.ProcessSource.ordinaryInput.program with
        policy := minPolicy.id, backends := [], decls := [seedLeaf, claimDecl] ++ extra } }
  { surface, replay := ⟨⟨Driver.coreVersionText⟩, minPolicy.id, [], [], surface.program.digest⟩
    capture := none }

def problem : Universe.Problem := { record := ⟨[], [], [], [], 10⟩, unrecorded := [] }

def absent : Choice := ⟨⟨0⟩, .truth, []⟩
def defend1 : Choice := ⟨⟨1⟩, .truth, fragD1⟩
def defend2 : Choice := ⟨⟨1⟩, .truth, fragD2⟩
/-- A choice that re-declares the seed leaf: the materialized source is rejected. -/
def duplicate : Choice := ⟨⟨1⟩, .truth, [seedLeaf]⟩
def duplicate2 : Choice := ⟨⟨2⟩, .truth, [seedLeaf]⟩

def joint : FamilySpec :=
  { problem := problem, base := source [],
    slots := [⟨⟨0⟩, [absent, defend1]⟩, ⟨⟨1⟩, [absent, defend2]⟩] }

/-- One accepted and one rejected alternative over the minimal program. -/
def minMixed : FamilySpec :=
  { problem := problem, base := minSource [], slots := [⟨⟨0⟩, [absent, duplicate]⟩] }

/-- Every alternative re-declares the seed leaf. -/
def minAllRej : FamilySpec :=
  { problem := problem, base := minSource [], slots := [⟨⟨0⟩, [duplicate, duplicate2]⟩] }

/-- A single-completion, uniformly accepted family: the target is neither
attacked nor supported, so every row reads the same gap. -/
def uniform : FamilySpec :=
  { problem := problem, base := minSource [], slots := [⟨⟨0⟩, [absent]⟩] }

/-- The empty family: contradictory precedence leaves no completion. -/
def deadEvent : Stamped := ⟨⟨0⟩, .commitPlan ⟨0⟩ ⟨0⟩ ⟨0⟩⟩
def deadEvent2 : Stamped := ⟨⟨1⟩, .retract ⟨0⟩⟩
def deadRef : SourceRef := ⟨"analysis", "dead", none⟩
def deadProblem : Universe.Problem :=
  { record := ⟨[⟨deadEvent, deadRef⟩, ⟨deadEvent2, deadRef⟩],
      [⟨deadEvent.id, deadEvent2.id, deadRef⟩, ⟨deadEvent2.id, deadEvent.id, deadRef⟩],
      [], [], 10⟩,
    unrecorded := [] }

def emptyFamily : FamilySpec := { problem := deadProblem, base := source [], slots := [] }

/-! ### Completions -/

def c00 : Family.Completion := ⟨[], [⟨⟨0⟩, absent⟩, ⟨⟨1⟩, absent⟩]⟩
def c01 : Family.Completion := ⟨[], [⟨⟨0⟩, absent⟩, ⟨⟨1⟩, defend2⟩]⟩
def c10 : Family.Completion := ⟨[], [⟨⟨0⟩, defend1⟩, ⟨⟨1⟩, absent⟩]⟩
def c11 : Family.Completion := ⟨[], [⟨⟨0⟩, defend1⟩, ⟨⟨1⟩, defend2⟩]⟩
def m00 : Family.Completion := ⟨[], [⟨⟨0⟩, absent⟩]⟩
def m01 : Family.Completion := ⟨[], [⟨⟨0⟩, duplicate⟩]⟩
def a00 : Family.Completion := ⟨[], [⟨⟨0⟩, duplicate⟩]⟩
def a10 : Family.Completion := ⟨[], [⟨⟨0⟩, duplicate2⟩]⟩
def u0 : Family.Completion := ⟨[], [⟨⟨0⟩, absent⟩]⟩

def jointComps : List Family.Completion := [c00, c01, c10, c11]
def minMixedComps : List Family.Completion := [m00, m01]
def minAllRejComps : List Family.Completion := [a00, a10]
def uniformComps : List Family.Completion := [u0]

theorem joint_reference : referenceFamily joint = jointComps := by decide +kernel
theorem minMixed_reference : referenceFamily minMixed = minMixedComps := by decide +kernel
theorem minAllRej_reference : referenceFamily minAllRej = minAllRejComps := by decide +kernel
theorem empty_reference : referenceFamily emptyFamily = [] := by decide +kernel
theorem uniform_reference : referenceFamily uniform = uniformComps := by decide +kernel
theorem joint_wellFormed : wellFormed joint = true := by decide +kernel
theorem minMixed_wellFormed : wellFormed minMixed = true := by decide +kernel
theorem minAllRej_wellFormed : wellFormed minAllRej = true := by decide +kernel

/-! ### The single checked family view

Each family is checked exactly once, here; everything below is a projection of
these values' already-prepared rows. -/

/-- The fixed inquiry context: one claim binding at the target atom, no
witnesses or kinds. -/
def config : AuditConfig :=
  { claims := [⟨⟨0⟩, ⟨"claim"⟩, atom "t"⟩], witnesses := [], kinds := [], assumptions := [] }

def jointChecked : CheckedFamily joint config jointComps := checkFamily joint config jointComps
def minMixedChecked : CheckedFamily minMixed config minMixedComps :=
  checkFamily minMixed config minMixedComps
def minAllRejChecked : CheckedFamily minAllRej config minAllRejComps :=
  checkFamily minAllRej config minAllRejComps
def uniformChecked : CheckedFamily uniform config uniformComps :=
  checkFamily uniform config uniformComps
def emptyChecked : CheckedFamily emptyFamily config [] := checkFamily emptyFamily config []

/-- The single deep rejection of the minimal duplicate-leaf program, bound once
and reused by every exact-rejection statement. -/
def minRejection : SourceRejection :=
  .source (.source (.structural (.duplicateLeafId ⟨"seed"⟩)))

/-! ### The observation tables (one precomputed pass each)

Each table is the family's own `statusObservations` at the fixed claim, pinned
to concrete data by one kernel reduction. Nothing below re-runs the checker. -/

theorem joint_table :
    statusObservations jointChecked ⟨0⟩ =
      [(c00, .ok (some (.published .defeated))), (c01, .ok (some (.published .defeated))),
       (c10, .ok (some (.published .defeated))), (c11, .ok (some (.published .justified)))] := by
  decide +kernel

theorem minMixed_table :
    statusObservations minMixedChecked ⟨0⟩ =
      [(m00, .ok (some (.published .gap))), (m01, .error minRejection)] := by decide +kernel

theorem minAllRej_table :
    statusObservations minAllRejChecked ⟨0⟩ =
      [(a00, .error minRejection), (a10, .error minRejection)] := by decide +kernel

theorem uniform_table :
    statusObservations uniformChecked ⟨0⟩ = [(u0, .ok (some (.published .gap)))] := by
  decide +kernel

theorem empty_table : statusObservations emptyChecked ⟨0⟩ = [] := rfl

/-- The dedicated exact-rejection fixture: the minimal duplicate-leaf source
reduces, at full strength, to its single structural diagnostic. `SourceOutcome`'s
accepted branch carries no `DecidableEq`, so the rejection is projected through
`rejectionOf` rather than compared directly. -/
private def rejectionOf {input : SourceInput} : SourceOutcome input → Option SourceRejection
  | .error reason => some reason
  | .ok _ => none

theorem duplicateLeaf_exact_rejection :
    rejectionOf (checkSource (minSource [seedLeaf])) = some minRejection := by decide +kernel

/-- The keys of each table are exactly the family's completions, in order. -/
theorem joint_table_keys : (statusObservations jointChecked ⟨0⟩).map Prod.fst = jointComps := by
  rw [joint_table]; rfl

theorem minMixed_table_keys :
    (statusObservations minMixedChecked ⟨0⟩).map Prod.fst = minMixedComps := by
  rw [minMixed_table]; rfl

theorem minAllRej_table_keys :
    (statusObservations minAllRejChecked ⟨0⟩).map Prod.fst = minAllRejComps := by
  rw [minAllRej_table]; rfl

/-! ### The reads: literal tables, proved equal to the family projection -/

def jointRead : Family.Completion → Except SourceRejection (Option Driver.PublicStatus) :=
  tableRead [(c00, .ok (some (.published .defeated))), (c01, .ok (some (.published .defeated))),
    (c10, .ok (some (.published .defeated))), (c11, .ok (some (.published .justified)))]

def minMixedRead : Family.Completion → Except SourceRejection (Option Driver.PublicStatus) :=
  tableRead [(m00, .ok (some (.published .gap))), (m01, .error minRejection)]

def minAllRejRead : Family.Completion → Except SourceRejection (Option Driver.PublicStatus) :=
  tableRead [(a00, .error minRejection), (a10, .error minRejection)]

def uniformRead : Family.Completion → Except SourceRejection (Option Driver.PublicStatus) :=
  tableRead [(u0, .ok (some (.published .gap)))]

def emptyRead : Family.Completion → Except SourceRejection (Option Driver.PublicStatus) :=
  tableRead ([] : List (Family.Completion × Except SourceRejection (Option Driver.PublicStatus)))

theorem jointRead_eq : jointRead = tableRead (statusObservations jointChecked ⟨0⟩) := by
  simp only [jointRead, joint_table]

theorem minMixedRead_eq : minMixedRead = tableRead (statusObservations minMixedChecked ⟨0⟩) := by
  simp only [minMixedRead, minMixed_table]

theorem minAllRejRead_eq :
    minAllRejRead = tableRead (statusObservations minAllRejChecked ⟨0⟩) := by
  simp only [minAllRejRead, minAllRej_table]

theorem uniformRead_eq : uniformRead = tableRead (statusObservations uniformChecked ⟨0⟩) := by
  simp only [uniformRead, uniform_table]

theorem emptyRead_eq : emptyRead = tableRead (statusObservations emptyChecked ⟨0⟩) := by
  simp only [emptyRead, empty_table]

/-! ### Per-completion readings -/

theorem jointRead_c00 : jointRead c00 = .ok (some (.published .defeated)) := by decide
theorem jointRead_c01 : jointRead c01 = .ok (some (.published .defeated)) := by decide
theorem jointRead_c10 : jointRead c10 = .ok (some (.published .defeated)) := by decide
theorem jointRead_c11 : jointRead c11 = .ok (some (.published .justified)) := by decide

theorem minMixedRead_m00 : minMixedRead m00 = .ok (some (.published .gap)) := by decide
theorem minMixedRead_m01 : minMixedRead m01 = .error minRejection := by decide

theorem minAllRejRead_a00 : minAllRejRead a00 = .error minRejection := by decide
theorem minAllRejRead_a10 : minAllRejRead a10 = .error minRejection := by decide

theorem uniformRead_u0 : uniformRead u0 = .ok (some (.published .gap)) := by decide

/-! ### Stability: empty, all-accepted, mixed-rejection, all-rejected

Each observable-specific entry point is first linked to the generic record over
the family's own table, and every count below is read from that link. -/

theorem joint_statusStability :
    statusStability jointChecked ⟨0⟩ = stabilityResult (.status ⟨0⟩) jointComps jointRead := by
  unfold statusStability
  rw [checkedCompletions_eq, ← jointRead_eq]

theorem minMixed_statusStability :
    statusStability minMixedChecked ⟨0⟩ =
      stabilityResult (.status ⟨0⟩) minMixedComps minMixedRead := by
  unfold statusStability
  rw [checkedCompletions_eq, ← minMixedRead_eq]

theorem minAllRej_statusStability :
    statusStability minAllRejChecked ⟨0⟩ =
      stabilityResult (.status ⟨0⟩) minAllRejComps minAllRejRead := by
  unfold statusStability
  rw [checkedCompletions_eq, ← minAllRejRead_eq]

theorem uniform_statusStability :
    statusStability uniformChecked ⟨0⟩ =
      stabilityResult (.status ⟨0⟩) uniformComps uniformRead := by
  unfold statusStability
  rw [checkedCompletions_eq, ← uniformRead_eq]

theorem empty_statusStability :
    statusStability emptyChecked ⟨0⟩ =
      stabilityResult (.status ⟨0⟩) ([] : List Family.Completion) emptyRead := by
  unfold statusStability
  rw [checkedCompletions_eq, ← emptyRead_eq]

/-- All-accepted and status-varying: four accepted rows, no rejection, and
neither whole-outcome nor accepted-only stability — the joint conjunction is
what moves the target. -/
theorem joint_stability :
    (statusStability jointChecked ⟨0⟩).total = 4 ∧
      (statusStability jointChecked ⟨0⟩).accepted = 4 ∧
      (statusStability jointChecked ⟨0⟩).rejected = 0 ∧
      (statusStability jointChecked ⟨0⟩).wholeStable = false ∧
      (statusStability jointChecked ⟨0⟩).acceptedDomainStable = false ∧
      acceptedRows jointComps jointRead = [c00, c01, c10, c11] ∧
      rejectedRows jointComps jointRead = [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [joint_statusStability]; decide
  · rw [joint_statusStability]; decide
  · rw [joint_statusStability]; decide
  · rw [joint_statusStability]; decide
  · rw [joint_statusStability]; decide
  · decide
  · decide

/-- The joint family is not outcome-stable, and the exact witness is `c00`/`c11`:
only the conjunction of both defenders moves the target. -/
theorem joint_not_wholeStable : ¬ WholeStable jointComps jointRead := by
  rw [← wholeStableB_iff]; decide

theorem joint_not_acceptedStable : ¬ AcceptedStable jointComps jointRead := by
  rw [← acceptedStableB_iff]; decide

/-- The complete partition of the joint family: three defeated rows in one
bucket, the both-defenders row in the justified one. -/
theorem joint_buckets :
    buckets jointComps jointRead =
      [(.ok (some (.published .defeated)), [c00, c01, c10]),
       (.ok (some (.published .justified)), [c11])] := by decide

/-- All-accepted and outcome-stable, with an exact count of one. -/
theorem uniform_stability :
    (statusStability uniformChecked ⟨0⟩).total = 1 ∧
      (statusStability uniformChecked ⟨0⟩).accepted = 1 ∧
      (statusStability uniformChecked ⟨0⟩).rejected = 0 ∧
      (statusStability uniformChecked ⟨0⟩).wholeStable = true ∧
      (statusStability uniformChecked ⟨0⟩).acceptedDomainStable = true ∧
      WholeStable uniformComps uniformRead := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [uniform_statusStability]; decide
  · rw [uniform_statusStability]; decide
  · rw [uniform_statusStability]; decide
  · rw [uniform_statusStability]; decide
  · rw [uniform_statusStability]; decide
  · rw [← wholeStableB_iff]; decide

/-- Mixed rejection: whole-outcome stability fails on the rejected row while the
accepted-only domain is stable, with exact counts, and the family is partitioned
by rejected reason or accepted value. -/
theorem minMixed_stability :
    (statusStability minMixedChecked ⟨0⟩).total = 2 ∧
      (statusStability minMixedChecked ⟨0⟩).accepted = 1 ∧
      (statusStability minMixedChecked ⟨0⟩).rejected = 1 ∧
      (statusStability minMixedChecked ⟨0⟩).wholeStable = false ∧
      (statusStability minMixedChecked ⟨0⟩).acceptedDomainStable = true ∧
      acceptedRows minMixedComps minMixedRead = [m00] ∧
      rejectedRows minMixedComps minMixedRead = [m01] ∧
      buckets minMixedComps minMixedRead =
        [(.ok (some (.published .gap)), [m00]), (.error minRejection, [m01])] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [minMixed_statusStability]; decide
  · rw [minMixed_statusStability]; decide
  · rw [minMixed_statusStability]; decide
  · rw [minMixed_statusStability]; decide
  · rw [minMixed_statusStability]; decide
  · decide
  · decide
  · decide

/-- The accepted-only domain carries its rejection count explicitly, so no
reader has to infer it. -/
def minMixedDomain : AcceptedDomain minMixedComps minMixedRead :=
  { rows := [m00], rows_eq := by decide, rejections := 1, rejections_eq := by decide }

/-- All-rejected: every row carries the same rejection, so the *outcome* is
stable, but there is no accepted status and no positive audit. -/
theorem minAllRej_stability :
    (statusStability minAllRejChecked ⟨0⟩).total = 2 ∧
      (statusStability minAllRejChecked ⟨0⟩).accepted = 0 ∧
      (statusStability minAllRejChecked ⟨0⟩).rejected = 2 ∧
      (statusStability minAllRejChecked ⟨0⟩).wholeStable = true ∧
      (statusStability minAllRejChecked ⟨0⟩).acceptedDomainStable = false ∧
      acceptedRows minAllRejComps minAllRejRead = [] ∧
      rejectedRows minAllRejComps minAllRejRead = [a00, a10] ∧
      buckets minAllRejComps minAllRejRead = [(.error minRejection, [a00, a10])] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [minAllRej_statusStability]; decide
  · rw [minAllRej_statusStability]; decide
  · rw [minAllRej_statusStability]; decide
  · rw [minAllRej_statusStability]; decide
  · rw [minAllRej_statusStability]; decide
  · decide
  · decide
  · decide

/-- The all-rejected family is outcome-stable, and the missing accepted domain is
explained by `acceptedStableB_of_all_rejected`. -/
theorem minAllRej_wholeStable : WholeStable minAllRejComps minAllRejRead := by
  rw [← wholeStableB_iff]; decide

theorem minAllRej_no_accepted :
    acceptedStableB minAllRejComps minAllRejRead = false :=
  acceptedStableB_of_all_rejected (by
    intro c hc
    simp only [minAllRejComps, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · rw [minAllRejRead_a00]; rfl
    · rw [minAllRejRead_a10]; rfl)

/-- The empty family: no rows at all, so neither whole nor accepted-only
stability, and the only restriction available is empty. -/
theorem empty_stability :
    (statusStability emptyChecked ⟨0⟩).total = 0 ∧
      (statusStability emptyChecked ⟨0⟩).accepted = 0 ∧
      (statusStability emptyChecked ⟨0⟩).rejected = 0 ∧
      (statusStability emptyChecked ⟨0⟩).wholeStable = false ∧
      (statusStability emptyChecked ⟨0⟩).acceptedDomainStable = false ∧
      acceptedRows ([] : List Family.Completion) emptyRead = [] ∧
      rejectedRows ([] : List Family.Completion) emptyRead = [] ∧
      buckets ([] : List Family.Completion) emptyRead = [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [empty_statusStability]; decide
  · rw [empty_statusStability]; decide
  · rw [empty_statusStability]; decide
  · rw [empty_statusStability]; decide
  · rw [empty_statusStability]; decide
  · decide
  · decide
  · decide

theorem empty_not_stable :
    ¬ WholeStable ([] : List Family.Completion) emptyRead ∧
      acceptedStableB ([] : List Family.Completion) emptyRead = false :=
  ⟨not_wholeStable_nil _, by decide⟩

/-! ### Reference and changed-slot sensitivity

Reference `(absent, absent)`: the only flipping row is the both-defenders row,
whose exact changed-slot set is the pair — neither singleton flips. -/

theorem joint_statusSensitivity :
    statusSensitivity jointChecked ⟨0⟩ c00 =
      sensitivityResult (.status ⟨0⟩) joint jointComps jointRead c00 := by
  unfold statusSensitivity
  rw [checkedCompletions_eq, ← jointRead_eq]

theorem joint_sensitivity :
    (statusSensitivity jointChecked ⟨0⟩ c00).total = 4 ∧
      (statusSensitivity jointChecked ⟨0⟩ c00).sensitive = 1 ∧
      (statusSensitivity jointChecked ⟨0⟩ c00).reference = c00 ∧
      (statusSensitivity jointChecked ⟨0⟩ c00).differing = [⟨c11, [⟨0⟩, ⟨1⟩]⟩] ∧
      (statusSensitivity jointChecked ⟨0⟩ c00).minimalSlotSets = [[⟨0⟩, ⟨1⟩]] ∧
      (statusSensitivity jointChecked ⟨0⟩ c00).realizing = [([⟨0⟩, ⟨1⟩], c11)] ∧
      Sensitivity jointComps jointRead c00 = [c11] ∧
      differingRows joint jointComps jointRead c00 = [⟨c11, [⟨0⟩, ⟨1⟩]⟩] ∧
      changedSlots joint c00 c11 = [⟨0⟩, ⟨1⟩] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [joint_statusSensitivity]; decide
  · rw [joint_statusSensitivity]; decide
  · rw [joint_statusSensitivity]; rfl
  · rw [joint_statusSensitivity]; decide
  · rw [joint_statusSensitivity]; decide
  · rw [joint_statusSensitivity]; decide
  · decide
  · decide
  · decide

/-- The pair is the unique inclusion-minimal change set, and — via the soundness
law on `minimalSlotSets` — it really is minimal. -/
theorem joint_minimal_sets :
    minimalSlotSets joint jointComps jointRead c00 = [[⟨0⟩, ⟨1⟩]] := by decide

theorem joint_pair_minimal :
    SlotMinimal joint jointComps jointRead c00 [⟨0⟩, ⟨1⟩] :=
  minimalSlotSets_sound (spec := joint) (cs := jointComps) (read := jointRead)
    (reference := c00) (S := [⟨0⟩, ⟨1⟩]) (by decide)

theorem joint_pair_minimal_complete :
    [⟨0⟩, ⟨1⟩] ∈ minimalSlotSets joint jointComps jointRead c00 :=
  minimalSlotSets_complete (spec := joint) (cs := jointComps) (read := jointRead)
    (reference := c00) (S := [⟨0⟩, ⟨1⟩])
    (List.mem_sublists.mp (by decide)) joint_pair_minimal

/-- No singleton flips from the reference, so neither singleton is minimal. -/
theorem joint_no_singleton_flip :
    ¬ AdmitsFlip joint jointComps jointRead c00 [⟨0⟩] ∧
      ¬ AdmitsFlip joint jointComps jointRead c00 [⟨1⟩] :=
  ⟨by rw [← admitsFlipB_iff]; decide, by rw [← admitsFlipB_iff]; decide⟩

theorem joint_singletons_not_minimal :
    [⟨0⟩] ∉ minimalSlotSets joint jointComps jointRead c00 ∧
      [⟨1⟩] ∉ minimalSlotSets joint jointComps jointRead c00 := by
  constructor
  · rw [singleton_minimal_iff (mem_slotUniverse.mpr (by decide))]
    rw [← admitsFlipB_iff]
    decide
  · rw [singleton_minimal_iff (mem_slotUniverse.mpr (by decide))]
    rw [← admitsFlipB_iff]
    decide

/-- The conjunction of both defenders admits a flip, and a realizing row exists
for it. -/
theorem joint_only :
    AdmitsFlip joint jointComps jointRead c00 [⟨0⟩, ⟨1⟩] ∧
      realizing joint jointComps jointRead c00 [⟨0⟩, ⟨1⟩] = some c11 :=
  ⟨by rw [← admitsFlipB_iff]; decide, by decide⟩

/-! ### Minimal conditional assumptions -/

def litP : Literal := .slotEq ⟨0⟩ ⟨1⟩
def litQ : Literal := .slotEq ⟨1⟩ ⟨1⟩
def litPne : Literal := .slotNe ⟨0⟩ ⟨1⟩
def litQne : Literal := .slotNe ⟨1⟩ ⟨1⟩
def presentSeed : Literal := .present deadEvent
def absentSeed : Literal := .absent deadEvent

/-- Target `justified`: the unique minimal assumption set is the pair, and every
immediate deletion has an exact surviving family and countercompletion. -/
theorem joint_assumptions_justified :
    minimalAssumptions jointComps jointRead (some (.published .justified))
        [litQ, litP, litP] = [[litQ, litP]] ∧
      restrict jointComps [litQ, litP] = [c11] ∧
      restrict jointComps (removeLit [litQ, litP] litP) = [c01, c11] ∧
      restrict jointComps (removeLit [litQ, litP] litQ) = [c10, c11] ∧
      deletionCounter jointComps jointRead (some (.published .justified)) [litQ, litP] litP =
        some c01 ∧
      deletionCounter jointComps jointRead (some (.published .justified)) [litQ, litP] litQ =
        some c10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The pair is a genuine subset-minimal assumption set (soundness law), and the
per-literal deletion witness law applies to it. -/
theorem joint_pair_assumption_minimal :
    MinimalAssumption jointComps jointRead (some (.published .justified)) [litQ, litP] :=
  minimalAssumptions_sound (cs := jointComps) (read := jointRead)
    (target := some (.published .justified)) (catalog := [litQ, litP]) (L := [litQ, litP])
    (by decide)

theorem joint_deletion_witness :
    restrict jointComps (removeLit [litQ, litP] litP) = [] ∨
      ∃ c, deletionCounter jointComps jointRead (some (.published .justified)) [litQ, litP] litP =
          some c ∧ c ∈ jointComps ∧ jointRead c ≠ .ok (some (.published .justified)) :=
  deletion_witness (cs := jointComps) (read := jointRead)
    (target := some (.published .justified)) (L := [litQ, litP]) (lit := litP)
    joint_pair_assumption_minimal (by decide)

/-- The deletion countercompletion really is a surviving non-target row. -/
theorem joint_deletion_counter_spec :
    c01 ∈ restrict jointComps (removeLit [litQ, litP] litP) ∧
      jointRead c01 ≠ .ok (some (.published .justified)) :=
  deletionCounter_spec (by decide : deletionCounter jointComps jointRead
    (some (.published .justified)) [litQ, litP] litP = some c01)

/-- Duplicate/equivalent literals are deduplicated and the two incomparable
size-one minimal sets are both returned, not one minimum-cardinality set. -/
theorem joint_incomparable :
    minimalAssumptions jointComps jointRead (some (.published .defeated))
        [litPne, litQne, litPne] = [[litQne], [litPne]] ∧
      minimalAssumptions jointComps jointRead (some (.published .defeated)) [litPne] =
        [[litPne]] ∧
      minimalAssumptions jointComps jointRead (some (.published .justified)) [litP, litQ] =
        [[litP, litQ]] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- A shorter (size one) and a longer (size two) inclusion-minimal set, both
minimal by the Boolean specialization's soundness. -/
theorem joint_short_length :
    minimalAssumptionB jointComps jointRead (some (.published .defeated)) [litPne] = true ∧
      minimalAssumptionB jointComps jointRead (some (.published .justified)) [litP, litQ] =
        true := by
  refine ⟨?_, ?_⟩ <;> decide

theorem joint_short_minimal :
    MinimalAssumption jointComps jointRead (some (.published .defeated)) [litPne] :=
  (minimalAssumptionB_iff jointComps jointRead (some (.published .defeated)) [litPne]).mp
    (by decide)

theorem joint_long_minimal :
    MinimalAssumption jointComps jointRead (some (.published .justified)) [litP, litQ] :=
  (minimalAssumptionB_iff jointComps jointRead (some (.published .justified)) [litP, litQ]).mp
    (by decide)

/-- Contradictory literals and an infeasible guard combination each leave an
empty restriction, so neither can satisfy any target and neither is returned. -/
theorem joint_infeasible :
    restrict jointComps [presentSeed, absentSeed] = [] ∧
      restrict jointComps [litP, litPne] = [] ∧
      ¬ Satisfies jointComps jointRead (some (.published .defeated)) [presentSeed, absentSeed] ∧
      ¬ Satisfies jointComps jointRead (some (.published .justified)) [presentSeed, absentSeed] ∧
      satisfiesB jointComps jointRead (some (.published .justified)) [litP, litPne] = false ∧
      minimalAssumptions jointComps jointRead (some (.published .defeated))
        [presentSeed, absentSeed] = [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · unfold Satisfies; decide
  · unfold Satisfies; decide
  · decide
  · decide

/-- A restriction leaving only rejections never satisfies; in particular the
empty literal set is not minimal there, because the family is not uniformly the
target. -/
theorem minMixed_rejection_only :
    restrict minMixedComps [.slotEq ⟨0⟩ ⟨1⟩] = [m01] ∧
      ¬ Satisfies minMixedComps minMixedRead (some (.published .gap)) [.slotEq ⟨0⟩ ⟨1⟩] ∧
      ¬ Satisfies minMixedComps minMixedRead (some (.published .gap)) [] ∧
      [] ∉ minimalAssumptions minMixedComps minMixedRead (some (.published .gap))
        [.slotEq ⟨0⟩ ⟨1⟩] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · unfold Satisfies; decide
  · unfold Satisfies; decide
  · decide

/-- An empty *literal set* is returned exactly when the whole family already
carries the target — false here for the joint family at `defeated` (the pair row
reads `justified`), and true for the uniformly accepted family. -/
theorem uniform_empty_satisfies :
    Satisfies uniformComps uniformRead (some (.published .gap)) [] := by
  unfold Satisfies; decide

theorem empty_set_minimal_iff :
    ¬ Satisfies jointComps jointRead (some (.published .defeated)) [] ∧
      (Satisfies minMixedComps minMixedRead (some (.published .gap)) [] ↔
        [] ∈ minimalAssumptions minMixedComps minMixedRead (some (.published .gap))
          [.slotEq ⟨0⟩ ⟨1⟩]) ∧
      [] ∈ minimalAssumptions uniformComps uniformRead (some (.published .gap)) [litP] ∧
      minimalAssumptions uniformComps uniformRead (some (.published .gap)) [litP] = [[]] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Satisfies; decide
  · exact ⟨minimalAssumptions_empty_mem, fun h => (minimalAssumptions_sound h).1⟩
  · exact minimalAssumptions_empty_mem uniform_empty_satisfies
  · decide

/-- The assumption record for the pair, with both deletion witnesses, read
through the observable-specific entry point. -/
theorem joint_statusAssumptions :
    statusAssumptions jointChecked ⟨0⟩ (.published .justified) [litQ, litP] =
      assumptionResult (.status ⟨0⟩ (.published .justified)) jointComps jointRead
        (some (.published .justified)) [litQ, litP] := by
  unfold statusAssumptions
  rw [checkedCompletions_eq, ← jointRead_eq]

theorem joint_assumption_result :
    (statusAssumptions jointChecked ⟨0⟩ (.published .justified) [litQ, litP]).total = 4 ∧
      (statusAssumptions jointChecked ⟨0⟩ (.published .justified) [litQ, litP]).target =
        .status ⟨0⟩ (.published .justified) ∧
      (statusAssumptions jointChecked ⟨0⟩ (.published .justified) [litQ, litP]).minimal.map
        MinimalSet.literals = [[litQ, litP]] ∧
      (statusAssumptions jointChecked ⟨0⟩ (.published .justified) [litQ, litP]).minimal.map
        (fun s => s.surviving) = [[c11]] ∧
      (statusAssumptions jointChecked ⟨0⟩ (.published .justified) [litQ, litP]).minimal.map
        (fun s => s.deletions.map Deletion.counter) = [[some c10, some c01]] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [joint_statusAssumptions]; decide
  · rw [joint_statusAssumptions]; rfl
  · rw [joint_statusAssumptions]; decide
  · rw [joint_statusAssumptions]; decide
  · rw [joint_statusAssumptions]; decide

/-! ### Wire codecs -/

def names : Process.Wire.Names :=
  { event := [], actor := [], plan := [], run := [], claim := ["c0"], source := [],
    data := [], family := [], witness := ["w0"] }

theorem names_unique : UniqueNames names := by
  simp only [UniqueNames, InquiryProcessWire.UniqueNames]
  decide

theorem completion_wellNamed_of_truth {c : Family.Completion} (hh : c.history = [])
    (hg : ∀ s ∈ c.assignment, s.choice.guard = .truth) : CompletionWellNamed names c := by
  unfold CompletionWellNamed
  refine ⟨?_, ?_⟩
  · intro e he
    rw [hh] at he
    simp at he
  · intro s hs
    unfold Family.Wire.SelectionWellNamed Family.Wire.ChoiceWellNamed Family.Wire.GuardWellNamed
    simp [hg s hs]

theorem c00_wellNamed : CompletionWellNamed names c00 :=
  completion_wellNamed_of_truth rfl (by
    intro s hs
    simp only [c00, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl <;> rfl)

theorem c01_wellNamed : CompletionWellNamed names c01 :=
  completion_wellNamed_of_truth rfl (by
    intro s hs
    simp only [c01, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl <;> rfl)

theorem c10_wellNamed : CompletionWellNamed names c10 :=
  completion_wellNamed_of_truth rfl (by
    intro s hs
    simp only [c10, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl <;> rfl)

theorem c11_wellNamed : CompletionWellNamed names c11 :=
  completion_wellNamed_of_truth rfl (by
    intro s hs
    simp only [c11, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl <;> rfl)

theorem litQ_wellNamed : LiteralWellNamed names litQ := by unfold LiteralWellNamed litQ; decide
theorem litP_wellNamed : LiteralWellNamed names litP := by unfold LiteralWellNamed litP; decide
theorem litPne_wellNamed : LiteralWellNamed names litPne := by
  unfold LiteralWellNamed litPne; decide

def profileSpec : Process.Wire.ProfileSpec :=
  ⟨[.observed], [.complete], .fwer, 1, 20, [.sampling], .groundedJustified⟩

def obsStatusSpec : ObservableSpec := .status ⟨0⟩
def obsAuditSpec : ObservableSpec := .audit ⟨0⟩ ⟨0⟩ profileSpec
def tgtStatusSpec : TargetSpec := .status ⟨0⟩ (.published .justified)
def tgtAuditSpec : TargetSpec := .audit ⟨0⟩ ⟨0⟩ profileSpec

theorem obsStatusSpec_wellNamed : ObservableWellNamed names obsStatusSpec := by
  unfold ObservableWellNamed obsStatusSpec; decide
theorem obsAuditSpec_wellNamed : ObservableWellNamed names obsAuditSpec := by
  unfold ObservableWellNamed obsAuditSpec; decide
theorem tgtStatusSpec_wellNamed : TargetWellNamed names tgtStatusSpec := by
  unfold TargetWellNamed tgtStatusSpec; decide
theorem tgtAuditSpec_wellNamed : TargetWellNamed names tgtAuditSpec := by
  unfold TargetWellNamed tgtAuditSpec; decide

theorem observable_roundtrip :
    decodeObservableSpec names (encodeObservableSpec names obsAuditSpec) = some obsAuditSpec ∧
      decodeObservableSpec names (encodeObservableSpec names obsStatusSpec) = some obsStatusSpec :=
  ⟨decode_encodeObservableSpec names names_unique _ obsAuditSpec_wellNamed,
   decode_encodeObservableSpec names names_unique _ obsStatusSpec_wellNamed⟩

theorem target_roundtrip :
    decodeTargetSpec names (encodeTargetSpec names tgtStatusSpec) = some tgtStatusSpec ∧
      decodeTargetSpec names (encodeTargetSpec names tgtAuditSpec) = some tgtAuditSpec :=
  ⟨decode_encodeTargetSpec names names_unique _ tgtStatusSpec_wellNamed,
   decode_encodeTargetSpec names names_unique _ tgtAuditSpec_wellNamed⟩

theorem literal_roundtrip :
    decodeLiteral names (encodeLiteral names litQ) = some litQ ∧
      decodeLiteral names (encodeLiteral names litPne) = some litPne :=
  ⟨decode_encodeLiteral names names_unique _ litQ_wellNamed,
   decode_encodeLiteral names names_unique _ litPne_wellNamed⟩

theorem row_wellNamed : SensitivityRowWellNamed names ⟨c11, [⟨0⟩, ⟨1⟩]⟩ := by
  unfold SensitivityRowWellNamed
  exact c11_wellNamed

theorem sensitivityRow_roundtrip :
    decodeSensitivityRow names (encodeSensitivityRow names ⟨c11, [⟨0⟩, ⟨1⟩]⟩) =
      some ⟨c11, [⟨0⟩, ⟨1⟩]⟩ :=
  decode_encodeSensitivityRow names names_unique _ row_wellNamed

def stabilityResultSpec : StabilityResult ObservableSpec :=
  { observable := obsStatusSpec, total := 4, accepted := 4, rejected := 0
    wholeStable := false, acceptedDomainStable := false }

theorem stabilityResultSpec_wellNamed : StabilityResultWellNamed names stabilityResultSpec := by
  unfold StabilityResultWellNamed
  exact obsStatusSpec_wellNamed

def deletionSpecQ : Deletion := ⟨litQ, [c10, c11], some c10⟩
def deletionSpecP : Deletion := ⟨litP, [c01, c11], some c01⟩

theorem deletionSpecQ_wellNamed : DeletionWellNamed names deletionSpecQ := by
  unfold DeletionWellNamed
  dsimp only [deletionSpecQ]
  refine ⟨?_, ?_, ?_⟩
  · exact litQ_wellNamed
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact c10_wellNamed
    · exact c11_wellNamed
  · intro c hc
    simp at hc
    subst hc
    exact c10_wellNamed

theorem deletionSpecP_wellNamed : DeletionWellNamed names deletionSpecP := by
  unfold DeletionWellNamed
  dsimp only [deletionSpecP]
  refine ⟨?_, ?_, ?_⟩
  · exact litP_wellNamed
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact c01_wellNamed
    · exact c11_wellNamed
  · intro c hc
    simp at hc
    subst hc
    exact c01_wellNamed

def minSetSpec : MinimalSet :=
  { literals := [litQ, litP], surviving := [c11], deletions := [deletionSpecQ, deletionSpecP] }

theorem minSetSpec_wellNamed : MinimalSetWellNamed names minSetSpec := by
  unfold MinimalSetWellNamed
  dsimp only [minSetSpec]
  refine ⟨?_, ?_, ?_⟩
  · intro lit hlit
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlit
    rcases hlit with rfl | rfl
    · exact litQ_wellNamed
    · exact litP_wellNamed
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    exact c11_wellNamed
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl
    · exact deletionSpecQ_wellNamed
    · exact deletionSpecP_wellNamed

def sensResultSpec : SensitivityResult ObservableSpec :=
  { observable := obsStatusSpec, reference := c00, total := 4, sensitive := 1
    differing := [⟨c11, [⟨0⟩, ⟨1⟩]⟩], minimalSlotSets := [[⟨0⟩, ⟨1⟩]]
    realizing := [([⟨0⟩, ⟨1⟩], c11)] }

theorem sensResultSpec_wellNamed : SensitivityResultWellNamed names sensResultSpec := by
  unfold SensitivityResultWellNamed
  dsimp only [sensResultSpec]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact obsStatusSpec_wellNamed
  · exact c00_wellNamed
  · intro row hrow
    simp only [List.mem_singleton] at hrow
    subst hrow
    exact row_wellNamed
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact c11_wellNamed

def assumeResultSpec : AssumptionResult TargetSpec :=
  { target := tgtStatusSpec, catalog := [litQ, litP], total := 4, minimal := [minSetSpec] }

theorem assumeResultSpec_wellNamed : AssumptionResultWellNamed names assumeResultSpec := by
  unfold AssumptionResultWellNamed
  dsimp only [assumeResultSpec]
  refine ⟨?_, ?_, ?_⟩
  · exact tgtStatusSpec_wellNamed
  · intro lit hlit
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hlit
    rcases hlit with rfl | rfl
    · exact litQ_wellNamed
    · exact litP_wellNamed
  · intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact minSetSpec_wellNamed

theorem deletion_roundtrip :
    decodeDeletion names (encodeDeletion names deletionSpecP) = some deletionSpecP :=
  decode_encodeDeletion names names_unique _ deletionSpecP_wellNamed

theorem minimalSet_roundtrip :
    decodeMinimalSet names (encodeMinimalSet names minSetSpec) = some minSetSpec :=
  decode_encodeMinimalSet names names_unique _ minSetSpec_wellNamed

theorem result_roundtrips :
    decodeStabilityResult names (encodeStabilityResult names stabilityResultSpec) =
        some stabilityResultSpec ∧
      decodeSensitivityResult names (encodeSensitivityResult names sensResultSpec) =
        some sensResultSpec ∧
      decodeAssumptionResult names (encodeAssumptionResult names assumeResultSpec) =
        some assumeResultSpec :=
  ⟨decode_encodeStabilityResult names names_unique _ stabilityResultSpec_wellNamed,
   decode_encodeSensitivityResult names names_unique _ sensResultSpec_wellNamed,
   decode_encodeAssumptionResult names names_unique _ assumeResultSpec_wellNamed⟩

theorem tag_laws :
    Function.Injective Tag.text ∧ (∀ t : Tag, t ∈ Tag.spelling.all) ∧
      (Tag.spelling.all.map Tag.spelling.text).Nodup :=
  ⟨Tag.text_injective, Tag.spelling_complete, Tag.spelling_nodup⟩

/-! ### Audit-observable fixtures (real submitted witness and strict profile)

The audit observable path is exercised below through the same checked-source
pipeline as every status fixture: each family is materialized and checked once
by `checkFamily`, and the audit analyses read the single landed `CheckedFamily`
through `auditObservations`/`tableRead`. The witness and profile are the real
submitted ones from `Lara.Examples.ProcessSourceProfiles` (its `config` carries
the submitted witness and full kind metadata, its `strict` profile is the one
its positive audit uses), so no second checker run or re-derived warrant
appears. -/

namespace PSP
abbrev family := Lara.Examples.ProcessSourceProfiles.family
abbrev completion := Lara.Examples.ProcessSourceProfiles.completion
abbrev config := Lara.Examples.ProcessSourceProfiles.config
abbrev strict := Lara.Examples.ProcessSourceProfiles.strict
abbrev claim := Lara.Examples.ProcessSourceProfiles.claim
end PSP

/-- The positive-audit checked family: a single completion whose submitted
witness warrants under the strict profile. -/
def auditChecked : CheckedFamily (PSP.family false) (PSP.config false) [PSP.completion] :=
  checkFamily (PSP.family false) (PSP.config false) [PSP.completion]

/-- The fixed-witness audit reading of the single positive completion, through
the general bridge (`auditObservations_tableRead`): the observable table's entry
is the per-completion `auditRead` at `rowAt`, here the positive warrant. -/
theorem auditObservation_positive_read :
    tableRead (auditObservations auditChecked PSP.claim.claim ⟨0⟩ PSP.strict) PSP.completion =
      .ok true := by
  rw [auditObservations_tableRead auditChecked PSP.claim.claim ⟨0⟩ PSP.strict
    (c := PSP.completion) (by simp)]
  decide +kernel

def auditStabilityPositive : StabilityResult Observable :=
  auditStability auditChecked PSP.claim.claim ⟨0⟩ PSP.strict

/-- The single positive completion is accepted and warrants, so the audit
observable is whole-outcome stable on its labelled domain: one accepted row, no
rejection, and both whole-outcome and accepted-only stability hold. -/
theorem audit_stability_concrete :
    auditStabilityPositive.total = 1 ∧
      auditStabilityPositive.accepted = 1 ∧
      auditStabilityPositive.rejected = 0 ∧
      auditStabilityPositive.wholeStable = true ∧
      auditStabilityPositive.acceptedDomainStable = true ∧
      auditStabilityPositive.observable = .audit PSP.claim.claim ⟨0⟩ PSP.strict := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩
  all_goals decide +kernel

def auditSensitivityPositive : SensitivityResult Observable :=
  auditSensitivity auditChecked PSP.claim.claim ⟨0⟩ PSP.strict PSP.completion

/-- With one completion there is no other row to differ from the reference, so
the audit sensitivity count is zero and no differing row, minimal change set or
realizing completion is returned. -/
theorem audit_sensitivity_concrete :
    auditSensitivityPositive.total = 1 ∧
      auditSensitivityPositive.sensitive = 0 ∧
      auditSensitivityPositive.differing = [] ∧
      auditSensitivityPositive.minimalSlotSets = [] ∧
      auditSensitivityPositive.realizing = [] ∧
      auditSensitivityPositive.reference = PSP.completion ∧
      auditSensitivityPositive.observable = .audit PSP.claim.claim ⟨0⟩ PSP.strict := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  all_goals decide +kernel

def auditAssumptionsPositive : AssumptionResult Target :=
  auditAssumptions auditChecked PSP.claim.claim ⟨0⟩ PSP.strict ([] : List Literal)

/-- The positive completion keeps its warrant on every surviving row, so the
empty catalog subset already satisfies the audit target, is the unique
subset-minimal set, and its surviving family is the whole single-completion
family with no deletion. -/
theorem audit_assumptions_concrete :
    auditAssumptionsPositive.total = 1 ∧
      auditAssumptionsPositive.target = .audit PSP.claim.claim ⟨0⟩ PSP.strict ∧
      auditAssumptionsPositive.minimal.map MinimalSet.literals = [[]] ∧
      auditAssumptionsPositive.minimal.map MinimalSet.surviving = [[PSP.completion]] ∧
      auditAssumptionsPositive.minimal.map
        (fun s => s.deletions.map Deletion.literal) = [[]] := by
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  all_goals decide +kernel

/-! ### A real `evidenceBlocked` status retaining its conditional label

The base policy quarantines the `(.attested, .user)` leaf kind. The `aux` leaf
is only used by the defender `d1`, so the prune removes `d1`, the attacker `a1`
loses the incoming edge from `d1` and is retained, and the blocking closure marks
the target's support `w` as blocked: the fixed target query reads
`evidenceBlocked .defeated`, with the conditional `.defeated` label preserved
inside the constructor rather than degraded to a published status. -/

def auxLeaf : Presentation.Decl :=
  .leaf ⟨⟨"aux"⟩, atom "aux", .attested, .user, [], none⟩

def blockedPolicy : Presentation.Policy :=
  { Lara.Examples.ProcessSource.ordinaryInput.policy with
    sigma := ⟨[], [], [⟨⟨"seed"⟩, []⟩, ⟨⟨"aux"⟩, []⟩, ⟨⟨"t"⟩, []⟩,
      ⟨⟨"s1"⟩, []⟩, ⟨⟨"u1"⟩, []⟩]⟩
    rules := [rule "r-t" "seed" "t", rule "r-a1" "seed" "s1", rule "r-d1" "aux" "u1"]
    contraries := [⟨⟨"s1", .nil⟩, ⟨"t", .nil⟩⟩, ⟨⟨"u1", .nil⟩, ⟨"s1", .nil⟩⟩]
    admission := [((.attested, .user), .quarantine)]
    theories := [] }

def blockedSource : SourceInput :=
  let surface : Surface.Input :=
    { policy := blockedPolicy
      program := { Lara.Examples.ProcessSource.ordinaryInput.program with
        policy := blockedPolicy.id, backends := [],
        decls := [seedLeaf, auxLeaf, claimDecl,
          argument "w" "r-t" "seed" (.supportsClaim ⟨"claim"⟩),
          argument "a1" "r-a1" "seed" (.supportsDerived ⟨"attack1"⟩),
          argument "d1" "r-d1" "aux" (.supportsDerived ⟨"defense1"⟩),
          .attack (.rebut ⟨"a1"⟩ ⟨"w"⟩), .attack (.rebut ⟨"d1"⟩ ⟨"a1"⟩)] } }
  { surface, replay := ⟨⟨Driver.coreVersionText⟩, blockedPolicy.id, [], [], surface.program.digest⟩
    capture := none }

def blockedFamily : FamilySpec := { problem := problem, base := blockedSource, slots := [] }
def blockedCompletion : Family.Completion := ⟨[], []⟩

def blockedConfig : AuditConfig :=
  { claims := [⟨⟨0⟩, ⟨"claim"⟩, atom "t"⟩], witnesses := [], kinds := [], assumptions := [] }

def blockedChecked : CheckedFamily blockedFamily blockedConfig [blockedCompletion] :=
  checkFamily blockedFamily blockedConfig [blockedCompletion]

theorem blocked_reference : referenceFamily blockedFamily = [blockedCompletion] := by
  decide +kernel

/-- The checked source's one completion reads a real `evidenceBlocked` status
whose conditional label is `.defeated`. -/
theorem blocked_table :
    statusObservations blockedChecked ⟨0⟩ =
      [(blockedCompletion, .ok (some (.evidenceBlocked .defeated)))] := by
  decide +kernel

/-- The reference per-completion reading retains the conditional label inside
the blocked constructor. -/
theorem evidenceBlocked_retains_conditional_label :
    statusRead (rowAt blockedFamily blockedChecked.context blockedCompletion) ⟨0⟩ =
      .ok (some (.evidenceBlocked .defeated)) := by
  decide +kernel

/-- The same retained label through the observation table's `tableRead`. -/
theorem evidenceBlocked_tableRead :
    tableRead (statusObservations blockedChecked ⟨0⟩) blockedCompletion =
      .ok (some (.evidenceBlocked .defeated)) := by
  decide +kernel

/-- Retention is not a degradation: the blocked status is not the published
status with the same core label. -/
theorem evidenceBlocked_label_distinct :
    (some (.evidenceBlocked .defeated) : Option Driver.PublicStatus) ≠
      some (.published .defeated) := by
  decide

/-! ### Silent runtime checks

A few evaluated cross-checks on the literal reads: the same data the kernel
proofs above pin, evaluated instead of kernel-reduced. -/

#guard (decide (jointRead c00 = .ok (some (.published .defeated))))
#guard (decide (jointRead c11 = .ok (some (.published .justified))))
#guard (decide (minMixedRead m01 = .error minRejection))
#guard (decide (minimalSlotSets joint jointComps jointRead c00 = [[⟨0⟩, ⟨1⟩]]))
#guard (decide (minimalAssumptions jointComps jointRead (some (.published .defeated))
  [litPne, litQne, litPne] = [[litQne], [litPne]]))
#guard ((restrict jointComps [presentSeed, absentSeed]).isEmpty)

end Lara.Examples.ProcessAnalysis
