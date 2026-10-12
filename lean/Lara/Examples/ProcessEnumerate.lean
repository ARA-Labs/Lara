import Lara.Process.Enumerate
import Lara.Examples.ProcessSource

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-! Kernel-decidable fixtures for the exact bounded enumerator.

Every history fixture compares the generated `Enumerate.search` with the
reference `Universe.Problem.completions`, covering contradictory orders,
repeated record entries, base/universe overlap, an empty universe, an optional
event with a valid extension, an optional event whose extension is invalid, an
invalid current dataset version and search exhaustion. The family fixtures
exercise guarded slot products, powerset growth with one accepted history and
all-rejected source alternatives, including exact-at-cap and cap-plus-one rows.
The last section ties the untouched version-1 runner to the reference answer and
prints one runtime smoke envelope. -/

namespace Lara.Examples.ProcessEnumerate

open Lara.Process
open Lara.Process.Universe
open Lara.Process.Enumerate

/-! ### Shared events -/

def actor : ActorId := ⟨0⟩
def plan : PlanId := ⟨0⟩
def version : VersionId := ⟨0⟩
def data : DataId := ⟨0⟩
def runId : RunId := ⟨0⟩
def fam : FamilyId := ⟨0⟩

def commit : Stamped := ⟨⟨0⟩, .commitPlan actor plan version⟩
def read : Stamped := ⟨⟨1⟩, .access actor data .evaluation⟩
def run : Stamped := ⟨⟨2⟩, .run runId plan version [(data, version)] fam⟩
def earlyRead : Stamped := ⟨⟨3⟩, .access actor data .evaluation⟩
def update : Stamped := ⟨⟨8⟩, .updateData data ⟨1⟩⟩
def resultOk : Stamped := ⟨⟨9⟩, .result runId 1⟩
def retract : Stamped := ⟨⟨10⟩, .retract ⟨0⟩⟩

def oref : SourceRef := ⟨"enumerate", "fixture", none⟩
def ev (e : Stamped) : DecodedEvent := ⟨e, oref⟩
def ord (a b : Stamped) : DecodedOrder := ⟨a.id, b.id, oref⟩

/-! ### History fixtures -/

/-- Empty universe, three reported events. -/
def pBase : Problem :=
  { record := ⟨[ev commit, ev read, ev run], [], [], [], 10⟩, unrecorded := [] }

/-- Contradictory precedence constraints: no completion at all. -/
def pContra : Problem :=
  { record := ⟨[ev commit, ev read, ev run], [ord commit read, ord read commit], [], [], 10⟩,
    unrecorded := [] }

/-- The same event reported twice, plus one optional universe event. -/
def pRepeat : Problem :=
  { record := ⟨[ev commit, ev commit, ev run], [], [], [], 10⟩, unrecorded := [read] }

/-- A universe event that repeats a reported event, plus a fresh one. -/
def pOverlap : Problem :=
  { record := ⟨[ev commit], [], [], [], 10⟩, unrecorded := [commit, read] }

/-- An optional dataset update; appending it before the run invalidates the run. -/
def pVersion : Problem :=
  { record := ⟨[ev commit, ev read, ev run], [], [], [], 10⟩, unrecorded := [update] }

/-- The omitted-read record of the version-1 fixture, with its reported order. -/
def pOmitted : Problem :=
  { record := ⟨[ev commit, ev read, ev run], [ord commit read], [], [⟨⟨0⟩, ⟨0⟩⟩], 10⟩,
    unrecorded := [earlyRead] }

/-- A contradictory record over seven events: the search exhausts many prefixes
and emits nothing. -/
def pSeven : Problem :=
  { record := ⟨[ev commit, ev read, ev run, ev earlyRead, ev update, ev resultOk, ev retract],
      [ord commit read, ord read commit], [], [], 10⟩,
    unrecorded := [] }

/-- A problem with no events: the single empty history. -/
def pEmpty : Problem := { record := ⟨[], [], [], [], 10⟩, unrecorded := [] }

/-! ### Source family fixtures -/

def sourceBase : Source.SourceInput :=
  let surface := Lara.Examples.ProcessSource.ordinaryInput
  { surface
    replay := {
      core := ⟨Lara.Driver.coreVersionText⟩
      policy := surface.policy.id
      backends := surface.program.backends.map fun pair => ⟨pair.1, ⟨pair.2⟩⟩
      theories := surface.policy.theories.map Prod.fst
      artifact := surface.program.digest }
    capture := none }

def truthChoice (n : Nat) : Family.Choice := ⟨⟨n⟩, .truth, []⟩

def truthSlot (n : Nat) : Family.Slot := ⟨⟨n⟩, [truthChoice 0, truthChoice 1]⟩

/-- Three free binary slots: one accepted history, eight source rows. -/
def powersetSpec : Family.FamilySpec :=
  { problem := pEmpty, base := sourceBase, slots := [truthSlot 0, truthSlot 1, truthSlot 2] }

/-- A slot whose guards partition on the optional universe event. -/
def presentChoice : Family.Choice := ⟨⟨0⟩, .present read, []⟩
def absentChoice : Family.Choice := ⟨⟨1⟩, .not (.present read), []⟩

def guardedSpec : Family.FamilySpec :=
  { problem := pOverlap, base := sourceBase,
    slots := [⟨⟨0⟩, [presentChoice, absentChoice]⟩] }

/-- Every alternative appends a second declaration of the base leaf, so every
materialized source is rejected. -/
def duplicateChoice (n : Nat) : Family.Choice :=
  ⟨⟨n⟩, .truth, [.leaf Lara.Examples.ProcessSource.ordinaryLeaf]⟩

def allRejectedSpec : Family.FamilySpec :=
  { problem := pEmpty, base := sourceBase,
    slots := [⟨⟨0⟩, [duplicateChoice 0, duplicateChoice 1]⟩] }

/-! ### Histories: generated against reference -/

/-- Empty universe: the generated order is exactly the DFS order. -/
theorem base_generated :
    search pBase = [[commit, read, run], [commit, run, read], [read, commit, run]] ∧
      searchSteps pBase = 9 ∧ pBase.completions.length = 3 := by decide +kernel

/-- The reference finite set is recovered. -/
theorem base_reference_recovered :
    (search pBase).Perm pBase.completions ∧ (search pBase).Nodup ∧
      (search pBase).length = pBase.completions.length :=
  ⟨search_perm_completions pBase, search_nodup pBase, search_length pBase⟩

/-- Contradictory precedence constraints: no history, but the search still runs. -/
theorem contradictory_orders :
    search pContra = [] ∧ pContra.completions = [] ∧ searchSteps pContra = 9 := by
  decide +kernel

/-- A twice-reported event is recorded once, so the base is deduplicated and the
optional event is the only branch. -/
theorem repeated_record_entries :
    pRepeat.base = [commit, run] ∧ (search pRepeat).length = 4 ∧
      pRepeat.completions.length = 4 := by decide +kernel

/-- A universe event that repeats a reported event does not add a second
occurrence: the pool is the deduplicated union. -/
theorem base_universe_overlap :
    (pool pOverlap).length = 2 ∧
      search pOverlap = [[commit], [commit, read], [read, commit]] := by decide +kernel

/-- The optional event is emitted both by omission and by a valid extension. -/
theorem optional_event_omission_and_extension :
    [commit] ∈ pOverlap.completions ∧ [commit, read] ∈ pOverlap.completions ∧
      [read, commit] ∈ pOverlap.completions := by decide +kernel

/-- An invalid current dataset version excludes the extension, while the short
history is emitted and still extended in the search. -/
theorem invalid_version_excludes_extension :
    [commit, read, run] ∈ pVersion.completions ∧
      [commit, read, update, run] ∉ pVersion.completions ∧
      (search pVersion).length = 7 ∧ searchSteps pVersion = 25 := by decide +kernel

/-- Search exhaustion: many visited prefixes, no accepted history. -/
theorem search_exhaustion_without_histories :
    search pSeven = [] ∧ pSeven.completions = [] ∧ searchSteps pSeven = 1450 := by
  decide +kernel

/-- Clamping only tightens: the effective cap never exceeds the declared one. -/
theorem clamped_only_tightens :
    (⟨3, 9, 0⟩ : Limits).clamped.histories ≤ 3 ∧
      (⟨3, 9, 0⟩ : Limits).clamped.steps ≤ 9 ∧
        (⟨3, 9, 0⟩ : Limits).clamped.products ≤ 0 :=
  clamped_le_self ⟨3, 9, 0⟩

/-- A huge declared limit cannot raise the ceilings: the run still succeeds and
its counts stay bounded. -/
theorem huge_declared_cap_is_clamped :
    enumerateProblem pBase ⟨1000000000, 1000000000, 0⟩ = .ok (search pBase) :=
  enumerateProblem_eq_ok pBase ⟨1000000000, 1000000000, 0⟩ (by decide) (by decide)

/-! ### Boundaries at and above the limits -/

/-- Exactly at both caps is legal: the complete search finishes. -/
theorem base_exact_at_cap :
    enumerateProblem pBase ⟨3, 9, 0⟩ = .ok (search pBase) :=
  enumerateProblem_eq_ok pBase ⟨3, 9, 0⟩ (by decide) (by decide)

/-- One step above the step cap refuses. -/
theorem base_steps_cap_plus_one :
    enumerateProblem pBase ⟨3, 8, 0⟩ = .error (.steps 9 8) :=
  enumerateProblem_cap_plus_one_steps pBase ⟨3, 8, 0⟩ (by decide)

/-- One history above the history cap refuses. -/
theorem base_histories_cap_plus_one :
    enumerateProblem pBase ⟨2, 9, 0⟩ = .error (.histories 3 2) :=
  enumerateProblem_cap_plus_one_histories pBase ⟨2, 9, 0⟩ (by decide) (by decide)

/-- Exhaustion still refuses over the step cap, even with no history. -/
theorem exhaustion_steps_cap_plus_one :
    enumerateProblem pSeven ⟨0, 1449, 0⟩ = .error (.steps 1450 1449) :=
  enumerateProblem_cap_plus_one_steps pSeven ⟨0, 1449, 0⟩ (by decide)

/-- A refusal carries no rows at all. -/
theorem base_refusal_no_rows : ¬ ∃ hs, enumerateProblem pBase ⟨2, 9, 0⟩ = .ok hs :=
  enumerateProblem_refusal_no_rows pBase ⟨2, 9, 0⟩ (.histories 3 2) (by decide)

/-- The accepted result's counts are bounded by the frozen ceilings. -/
theorem base_within_ceilings :
    searchSteps pBase ≤ maxSearchSteps ∧ (search pBase).length ≤ maxSearchHistories :=
  (enumerateProblem_within_ceilings pBase ⟨3, 9, 0⟩ base_exact_at_cap).2

/-! ### Family products -/

theorem powerset_wellformed : Family.wellFormed powersetSpec = true := by decide +kernel

theorem guarded_wellformed : Family.wellFormed guardedSpec = true := by decide +kernel

theorem allRejected_wellformed : Family.wellFormed allRejectedSpec = true := by decide +kernel

/-- Powerset growth: one accepted history gives eight source rows. -/
theorem powerset_growth :
    (search pEmpty).length = 1 ∧ (searchFamily powersetSpec).length = 8 ∧
      (Family.referenceFamily powersetSpec).length = 8 := by decide +kernel

theorem powerset_family_reference_recovered :
    (searchFamily powersetSpec).Perm (Family.referenceFamily powersetSpec) ∧
      (searchFamily powersetSpec).Nodup :=
  ⟨searchFamily_perm powersetSpec, searchFamily_nodup powersetSpec powerset_wellformed⟩

/-- Every history has exactly one guarded assignment here: three rows. -/
theorem guarded_partition :
    (searchFamily guardedSpec).length = 3 ∧
      (Family.referenceFamily guardedSpec).length = 3 := by decide +kernel

/-- Guard pruning recovers the reference slot product. -/
theorem guarded_family_reference_recovered :
    (searchFamily guardedSpec).Perm (Family.referenceFamily guardedSpec) ∧
      (searchFamily guardedSpec).Nodup :=
  ⟨searchFamily_perm guardedSpec, searchFamily_nodup guardedSpec guarded_wellformed⟩

/-- All-rejected source alternatives: both rows survive the product and both
materializations are rejected with the same typed reason. -/
theorem all_rejected_alternatives :
    (searchFamily allRejectedSpec).length = 2 ∧
      (searchFamily allRejectedSpec).all (fun completion => decide
        (Lara.Examples.ProcessSource.ordinaryError
          (Family.materialize allRejectedSpec completion).surface =
          some (.structural
            (.duplicateLeafId Lara.Examples.ProcessSource.ordinaryLeaf.id)))) = true := by
  decide +kernel

theorem allRejected_family_reference_recovered :
    (searchFamily allRejectedSpec).Perm (Family.referenceFamily allRejectedSpec) :=
  searchFamily_perm allRejectedSpec

/-- Exactly at the product cap is legal. -/
theorem powerset_exact_at_cap :
    enumerateFamily powersetSpec ⟨1, 1, 8⟩ = .ok (searchFamily powersetSpec) :=
  enumerateFamily_eq_ok powersetSpec ⟨1, 1, 8⟩ (by decide) (by decide) (by decide)

/-- One row above the product cap refuses. -/
theorem powerset_products_cap_plus_one :
    enumerateFamily powersetSpec ⟨1, 1, 7⟩ = .error (.products 8 7) :=
  enumerateFamily_cap_plus_one_products powersetSpec ⟨1, 1, 7⟩ (by decide) (by decide)
    (by decide)

/-- A refused family carries no rows at all. -/
theorem powerset_refusal_no_rows :
    ¬ ∃ cs, enumerateFamily powersetSpec ⟨1, 1, 7⟩ = .ok cs :=
  enumerateFamily_refusal_no_rows powersetSpec ⟨1, 1, 7⟩ (.products 8 7) (by decide)

/-- The accepted family result's row count is bounded by the frozen ceiling. -/
theorem powerset_within_ceilings :
    (searchFamily powersetSpec).length ≤ maxSearchProducts :=
  (enumerateFamily_within_ceilings powersetSpec ⟨1, 1, 8⟩ powerset_exact_at_cap).2.2.2

/-! ### Count/verdict invariance and deterministic witness selection -/

/-- Verdict and count are permutation invariant, so the generated list reports
the reference verdict and count. -/
theorem version_verdict_invariance :
    (searchAnswer pVersion (.atom .predictable)).verdict =
      (answer pVersion (.atom .predictable)).verdict ∧
    (searchAnswer pVersion (.atom .predictable)).count =
      (answer pVersion (.atom .predictable)).count :=
  ⟨searchAnswer_verdict pVersion (.atom .predictable),
    searchAnswer_count pVersion (.atom .predictable)⟩

theorem version_answer_shape :
    (searchAnswer pVersion (.atom .predictable)).verdict = .unknown ∧
      (searchAnswer pVersion (.atom .predictable)).count = 7 := by decide +kernel

/-- The new runner's witness is exactly the first match of the documented DFS
order, and it is a reference completion satisfying the query. -/
theorem version_witness_holds :
    (searchAnswer pVersion (.atom .predictable)).holds = some [commit, read, run] := by
  decide +kernel

theorem version_witness_selected :
    (search pVersion).find? (fun x => decide (Predictable x)) = some [commit, read, run] :=
  searchAnswer_holds_is_find pVersion (.atom .predictable) [commit, read, run]
    version_witness_holds

theorem version_witness_mem :
    [commit, read, run] ∈ pVersion.completions ∧ Predictable [commit, read, run] :=
  searchAnswer_holds_mem pVersion (.atom .predictable) [commit, read, run]
    version_witness_holds

/-- A known verdict carries no witness on either side, so the encoded answer
bytes agree. -/
def overlapNames : Wire.Names :=
  { event := [], actor := [], plan := [], run := [], claim := [],
    source := [], data := [], family := [], witness := [] }

theorem overlap_verdict_certain :
    (searchAnswer pOverlap (.atom (.runPrecommitted ⟨0⟩))).verdict = .certainTrue := by
  decide +kernel

theorem overlap_answer_bytes_unchanged :
    Wire.encodeAnswer overlapNames
        ("q", searchAnswer pOverlap (.atom (.runPrecommitted ⟨0⟩))) =
      Wire.encodeAnswer overlapNames
        ("q", answer pOverlap (.atom (.runPrecommitted ⟨0⟩))) :=
  searchAnswer_bytes_eq_of_known overlapNames pOverlap "q" _
    (by decide)

/-! ### Version-1 compatibility -/

/-- The decoded document of `fixtures/process/run/omitted-read.sexp`. -/
def fixtureDoc : Wire.Document :=
  { names :=
      ⟨["commit", "read", "run", "early-read"], ["alice"], ["plan"], ["run0"],
        ["c0"], [], ["test"], ["fam"], ["w0"]⟩
    source :=
      ⟨[.event commit oref, .event read oref, .event run oref,
        .ordering commit.id read.id oref, .submission ⟨0⟩ ⟨0⟩], 10⟩
    admits := [.instrumentedLog, .signedAttestation]
    unrecorded := [earlyRead]
    limits := ⟨8, 1000⟩
    queries :=
      [.verdict "precommitted" (.atom (.runPrecommitted ⟨0⟩)),
        .verdict "predictable" (.atom .predictable)] }

/-- The version-1 runner sees exactly the reference problem. -/
theorem fixture_problem_is_reference : fixtureDoc.problem = pOmitted := by decide +kernel

/-- The reference answer's witnesses are the checked-in bytes: the first
completion where precommitment holds and the first where it fails. -/
theorem fixture_reference_witnesses :
    (answer pOmitted (.atom (.runPrecommitted ⟨0⟩))).verdict = .unknown ∧
      (answer pOmitted (.atom (.runPrecommitted ⟨0⟩))).count = 10 ∧
      (answer pOmitted (.atom (.runPrecommitted ⟨0⟩))).holds = some [commit, read, run] ∧
      (answer pOmitted (.atom (.runPrecommitted ⟨0⟩))).fails =
        some [earlyRead, commit, read, run] := by decide +kernel

/-- Version 1 still prints `Universe.answer` of its own problem, unchanged. -/
theorem v1_witness_bytes_unchanged {r : Wire.Result} (h : Wire.run fixtureDoc = .ok r) :
    r.answers = fixtureDoc.queries.filterMap (fun
      | .verdict name q => some (name, answer fixtureDoc.problem q)
      | .audit .. => none) ∧ fixtureDoc.problem = pOmitted :=
  ⟨run_answers_unchanged h, fixture_problem_is_reference⟩

theorem event_ceiling_unchanged : Wire.maxProcessEvents = 8 := maxProcessEvents_unchanged

/-! ### Silent runtime checks -/

/- The fixture document is accepted by the untouched version-1 runner. -/
#guard (Wire.run fixtureDoc).isOk

/- The reference answer the runner prints has ten completions and names the
first hold and the first failure. -/
#guard ((answer pOmitted (.atom (.runPrecommitted ⟨0⟩))).count == 10)
#guard ((answer pOmitted (.atom (.runPrecommitted ⟨0⟩))).holds ==
  some [commit, read, run])

/- The generated enumerator agrees with the reference on the same problem. -/
#guard ((search pBase).length == 3)
#guard ((searchFamily powersetSpec).length == 8)

end Lara.Examples.ProcessEnumerate
