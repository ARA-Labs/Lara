/-
The reference semantics and the bounded runner for `inquiry-input 1`
(issue #22, shared protocol / delivery).

This module is the *only* interpreter of a decoded `InquiryWire.InquiryInput`.
It has two layers:

* the **reference semantics** (`analyzeWith`) — pure entry points that take an
  already-enumerated family of source completions and produce one
  `InquiryWire.ResultBody` per emitted result. It builds one shared projection
  (`projectionOf`: a single `Source.checkFamily` pass over the enumerated
  completions) and reads it for every embedded query and every wrapper request;
  it never re-runs a checker or a stage. `projectionOf_checkedCompletions`
  records that the projection enumerates the family once, and
  `analyzeWith_eq_perRequest` proves the one-pass semantics equals the
  per-request re-run semantics. Every request form of `InquiryWire.RequestSpec`
  has a body, and source-rejected completions remain family rows inside a
  completed result — they are never filtered out and never an execution
  refusal.

* the **bounded runner** (`runBounded`) — threads one shared budget through the
  P2 enumeration, the shared observation and every dispatched request, and
  returns `Except RunRefusal (List InquiryResult)`. Each declared bound is
  additionally capped by a fixed checker ceiling (`ceilingOf`). Exactly at a cap
  is legal if the whole computation finishes there; discovering one additional
  output refuses the entire document (`runBounded_refusal_no_result`). The
  whole-document counters apply once per document: `sources` counts every
  observed family row plus two endpoints per impact/verification request,
  `declarations` counts every family materialization plus both endpoints'
  declarations, `pairs` counts the per-request observation, graph node/edge and
  read-value comparisons, and `searchSteps` counts the history prefix-DFS plus
  every attempted slot extension (`actualOf_sources_eq`,
  `actualOf_declarations_eq`, `actualOf_pairs_eq`, `actualOf_searchSteps_eq`);
  `checkBudgets` enforces each one, including the `sources` and `search-steps`
  branches. Product upper bounds are allocation guards only: the runner
  uses the guarded bounded traversal `Enumerate.enumerateFamily`, never the
  materialized upper-bound product. No partial rows escape a refusal.
  `runBounded_eq_reference` proves a successful bounded result equals the
  reference result.

Emission order is fixed: the embedded `process` document's queries first, in
their original order, then the wrapper requests in theirs. Labels must be unique
across both lists. History-verdict results (`ResultBody.histories`) carry the
*distinct unguarded history count*; source-family results carry the *guarded
source count*. Embedded verdicts retain P0 semantics (they reuse
`Universe.answer` of `Wire.Document.problem`); embedded audits use the new
checked-source product semantics.
-/
import Lara.Process.InquiryWire

namespace Lara.Process.InquiryRun

open Lara.Process
open Lara.Process.InquiryWire

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-! ## Small aliases -/

abbrev ObservableSpec := Analysis.AnalysisWire.ObservableSpec
abbrev TargetSpec := Analysis.AnalysisWire.TargetSpec
abbrev Literal := Analysis.Literal
abbrev Query := Universe.Query
abbrev Completion := Family.Completion
abbrev FamilySpec := Family.FamilySpec
abbrev Selection := Family.Selection
abbrev SlotId := Family.SlotId
abbrev ChoiceId := Family.ChoiceId
abbrev AuditConfig := Source.AuditConfig
abbrev SourceInput := Source.SourceInput
abbrev Snapshot := Source.Snapshot
abbrev CheckedFamily {family : FamilySpec} {config : AuditConfig} (completions : List Completion) :=
  Source.CheckedFamily family config completions

/-! ## Document projection -/

/-- The problem embedded in the wrapper's `process` document. Constructed
through `Wire.Document.problem` (the shared problem definition), never through
`Wire.run`. -/
def embeddedProblem (input : InquiryInput) : Universe.Problem :=
  Wire.Document.problem input.process

/-- The declared source-choice family. -/
def familyOf (input : InquiryInput) : FamilySpec :=
  ⟨embeddedProblem input, input.base, input.slots⟩

/-- The audit configuration declared by the wrapper. -/
def configOf (input : InquiryInput) : AuditConfig :=
  { claims := input.claims, witnesses := input.witnesses, kinds := input.kinds,
    assumptions := input.assumptions }

/-! ## Reference resolution -/

/-- Resolve one declared `(slot, choice)` pair against the family's slots. -/
def resolveSlot (spec : FamilySpec) (s : SlotId) (c : ChoiceId) : Option Selection :=
  (spec.slots.find? (fun slot => slot.id = s)).bind fun slot =>
    (slot.choices.find? (fun ch => ch.id = c)).map fun ch => ⟨s, ch⟩

/-- Resolve a whole reference assignment, in order. -/
def resolveAssignment (spec : FamilySpec) (a : List (SlotId × ChoiceId)) :
    Option (List Selection) :=
  a.mapM fun p => resolveSlot spec p.1 p.2

/-- Resolve a `ReferenceSpec` into a family completion. -/
def resolveCompletion (spec : FamilySpec) (r : ReferenceSpec) : Option Completion :=
  (resolveAssignment spec r.assignment).map fun sel => ⟨r.history, sel⟩

/-- The reference completion used by the pure semantics. Well-formed documents
resolve before this is read (`referencesResolve`); the fallback is a placeholder
that only a refused document could reach. -/
def referenceCompletion (spec : FamilySpec) (r : ReferenceSpec) : Completion :=
  (resolveCompletion spec r).getD ⟨r.history, []⟩

/-- The fixed atom a claim binding pins a `ClaimId` to. The fallback is inert:
well-formed documents resolve every queried claim before this is read
(`impactClaimsResolve`). -/
def claimAtom (input : InquiryInput) (c : ClaimId) : Atom :=
  ((input.claims.find? (fun b => b.claim = c)).map (fun b => b.query)).getD (Atom.atom "" .nil)
/-! ## Labels -/

/-- The report label of a P0 query spec. -/
def Wire.QuerySpec.label : Wire.QuerySpec → String
  | .verdict name _ => name
  | .audit name _ _ _ => name

/-- The report label of a wrapper request. -/
def RequestSpec.label : RequestSpec → String
  | .status l _ => l
  | .audit l _ _ _ => l
  | .stable l _ => l
  | .sensitivity l _ _ => l
  | .slotsSensitive l _ _ => l
  | .minimalAssumptions l _ => l
  | .impact l _ _ _ => l
  | .verifyImpact l _ _ _ => l

/-- Every emitted label: embedded `process` queries first, then wrapper requests. -/
def labelsOf (input : InquiryInput) : List String :=
  (input.process.queries.map Wire.QuerySpec.label) ++ (input.requests.map RequestSpec.label)

/-- Labels must be unique across the embedded and wrapper lists. -/
def labelsDistinct (input : InquiryInput) : Bool := decide (labelsOf input).Nodup

/-! ## Reference-semantics body builders -/

/-- The assignment of a completion as its declared slot/choice identity pairs. -/
def assignmentOf (c : Completion) : List (SlotId × ChoiceId) :=
  c.assignment.map fun s => (s.slot, s.choice.id)

/-- The row of one completion through the landed checked-source pipeline. -/
def rowAt (family : FamilySpec) {config : AuditConfig} {completions : List Completion}
    (checked : Source.CheckedFamily family config completions) (c : Completion) :=
  Analysis.rowAt family checked.context c

/-- Complete ordered family rows for a status request: every completion, its
rejection or its accepted public status. Rejected rows are retained. -/
def statusBody {family : FamilySpec} {config : AuditConfig} {completions : List Completion}
    (checked : Source.CheckedFamily family config completions) (claim : ClaimId) : ResultBody :=
  let rows : List FamilyStatusRow := (Analysis.checkedCompletions checked).map fun c =>
    let row := rowAt family checked c
    { history := c.history
      assignment := assignmentOf c
      rejection := match row.view with
        | .error r => some r
        | .ok _ => none
      status := row.claimStatus claim }
  .status
    { rows := rows
      total := rows.length
      accepted := (rows.filter fun r => r.rejection.isNone).length
      rejected := (rows.filter fun r => r.rejection.isSome).length
      verdict := Analysis.wholeStableB (Analysis.checkedCompletions checked)
        (Analysis.tableRead (Analysis.statusObservations checked claim)) }

/-- Complete ordered family rows for an audit request, with the fixed-witness
aggregate verdict. Rejected rows are retained and never carry a warrant. -/
def auditBody {family : FamilySpec} {config : AuditConfig} {completions : List Completion}
    (checked : Source.CheckedFamily family config completions) (claim : ClaimId)
    (witness : WitnessId) (profile : Profile Empty) : ResultBody :=
  let rows : List FamilyAuditRow := (Analysis.checkedCompletions checked).map fun c =>
    let row := rowAt family checked c
    { history := c.history
      assignment := assignmentOf c
      rejection := match row.view with
        | .error r => some r
        | .ok _ => none
      audit := match row.view with
        | .error _ => none
        | .ok _ => some (Source.warranted checked.context row profile claim witness) }
  .audit
    { rows := rows
      total := rows.length
      accepted := (rows.filter fun r => r.rejection.isNone).length
      rejected := (rows.filter fun r => r.rejection.isSome).length
      verdict := Source.audit checked profile claim witness }

/-- The stability result for a status or audit observable. -/
def stabilityBody {family : FamilySpec} {config : AuditConfig} {completions : List Completion}
    (checked : Source.CheckedFamily family config completions) (obs : ObservableSpec) : ResultBody :=
  match obs with
  | .status claim =>
      .stability (Analysis.stabilityResult obs (Analysis.checkedCompletions checked)
        (Analysis.tableRead (Analysis.statusObservations checked claim)))
  | .audit claim witness profile =>
      .stability (Analysis.stabilityResult obs (Analysis.checkedCompletions checked)
        (Analysis.tableRead (Analysis.auditObservations checked claim witness profile.toProfile)))

/-- The reference-sensitivity result. -/
def sensitivityBody {family : FamilySpec} {config : AuditConfig} {completions : List Completion}
    (checked : Source.CheckedFamily family config completions) (obs : ObservableSpec)
    (reference : Completion) : ResultBody :=
  match obs with
  | .status claim =>
      .sensitivity (Analysis.sensitivityResult obs family (Analysis.checkedCompletions checked)
        (Analysis.tableRead (Analysis.statusObservations checked claim)) reference)
  | .audit claim witness profile =>
      .sensitivity (Analysis.sensitivityResult obs family (Analysis.checkedCompletions checked)
        (Analysis.tableRead (Analysis.auditObservations checked claim witness profile.toProfile))
        reference)

/-- The changed-slot sensitivity result. -/
def slotsSensitiveBody {family : FamilySpec} {config : AuditConfig}
    {completions : List Completion}
    (checked : Source.CheckedFamily family config completions) (obs : ObservableSpec)
    (reference : Completion) : ResultBody :=
  match obs with
  | .status claim =>
      .slotsSensitive (Analysis.sensitivityResult obs family (Analysis.checkedCompletions checked)
        (Analysis.tableRead (Analysis.statusObservations checked claim)) reference)
  | .audit claim witness profile =>
      .slotsSensitive (Analysis.sensitivityResult obs family (Analysis.checkedCompletions checked)
        (Analysis.tableRead (Analysis.auditObservations checked claim witness profile.toProfile))
        reference)

/-- The minimal-assumptions result over the declared catalog. -/
def assumptionsBody {family : FamilySpec} {config : AuditConfig} {completions : List Completion}
    (checked : Source.CheckedFamily family config completions) (catalog : List Literal)
    (target : TargetSpec) : ResultBody :=
  match target with
  | .status claim expected =>
      .minimalAssumptions (Analysis.assumptionResult target (Analysis.checkedCompletions checked)
        (Analysis.tableRead (Analysis.statusObservations checked claim)) (some expected) catalog)
  | .audit claim witness profile =>
      .minimalAssumptions (Analysis.assumptionResult target (Analysis.checkedCompletions checked)
        (Analysis.tableRead (Analysis.auditObservations checked claim witness profile.toProfile))
        true catalog)

/-! ## P5 impact and verification -/

/-- The wrapper's `verify-impact` semantics: rerun the shared observer on the two
supplied sources, recompute every claimed certificate field and return the closed
verification result. The supplied endpoints replace the certificate's own inputs,
so a certificate bound to other inputs is refused with `mismatchedSnapshots`. -/
def verifyCertificate (before after : SourceInput) (c : Impact.ImpactCertificate) :
    Impact.VerificationResult :=
  Impact.verifyImpact { c with beforeInput := before, afterInput := after }

/-- The wire form of a semantic certificate with an explicit read enumeration.
The read log is the only field whose shape differs (ordered list vs set). -/
def wireOfCertificateList (reads : List (Impact.Side × Impact.ReadKey × Impact.ReadVal))
    (c : Impact.ImpactCertificate) : ImpactCertificateWire :=
  { beforeInput := c.beforeInput, afterInput := c.afterInput, queries := c.queries,
    beforeSnapshot := c.beforeSnapshot, afterSnapshot := c.afterSnapshot,
    beforeIdentity := c.beforeIdentity, afterIdentity := c.afterIdentity,
    beforeReport := c.beforeReport, afterReport := c.afterReport, transition := c.transition,
    rows := c.rows, changed := c.changed, unchanged := c.unchanged,
    blockedBefore := c.blockedBefore, blockedAfter := c.blockedAfter, carrier := c.carrier,
    nodeDiff := c.nodeDiff, edgeDiff := c.edgeDiff, locality := c.locality,
    reads := reads }

/-- Recover the wire form of a semantic certificate (the ordered enumeration of
its read set). The inverse of `ImpactCertificateWire.toCertificate`. -/
noncomputable def wireOfCertificate (c : Impact.ImpactCertificate) : ImpactCertificateWire :=
  wireOfCertificateList c.reads.toList c

/-! ## Reference semantics -/

/-- The embedded `process` document's results: each embedded query becomes one
labelled result, in the embedded order. Verdict queries reuse the P0 answer of
the complete unguarded history family; audit queries use the new checked-source
product semantics. -/
def embeddedResult {family : FamilySpec} {config : AuditConfig} {completions : List Completion}
    (checked : Source.CheckedFamily family config completions) (input : InquiryInput)
    (q : Wire.QuerySpec) : InquiryResult :=
  match q with
  | .verdict name f =>
      ⟨name, .histories (embeddedProblem input).completions.length
        (OutcomeAnswer.ofAnswer (Universe.answer (embeddedProblem input) f))⟩
  | .audit name claim witness profile =>
      ⟨name, auditBody checked claim witness profile.toProfile⟩

/-- The body of one wrapper request. Every request form has a body. -/
def requestBody {family : FamilySpec} {config : AuditConfig} {completions : List Completion}
    (checked : Source.CheckedFamily family config completions) (input : InquiryInput)
    (r : RequestSpec) : ResultBody :=
  match r with
  | .status _ claim => statusBody checked claim
  | .audit _ claim witness profile => auditBody checked claim witness profile.toProfile
  | .stable _ obs => stabilityBody checked obs
  | .sensitivity _ reference obs => sensitivityBody checked obs (referenceCompletion family reference)
  | .slotsSensitive _ reference obs =>
      slotsSensitiveBody checked obs (referenceCompletion family reference)
  | .minimalAssumptions _ target => assumptionsBody checked input.catalog target
  | .impact _ before after queries => .impact (Impact.impactResult before after (queries.map (claimAtom input)))
  | .verifyImpact _ before after certificate =>
      .verification (verifyCertificate before after certificate.toCertificate)

/-- Every declared sensitivity reference resolves to a family member. -/
def referenceResolves (cs : List Completion) (input : InquiryInput) (r : ReferenceSpec) : Bool :=
  match resolveCompletion (familyOf input) r with
  | some c => decide (c ∈ cs)
  | none => false

/-- All references of a document resolve inside the enumerated family. -/
def referencesResolve (cs : List Completion) (input : InquiryInput) : Bool :=
  input.requests.all fun r =>
    match r with
    | .sensitivity _ reference _ => referenceResolves cs input reference
    | .slotsSensitive _ reference _ => referenceResolves cs input reference
    | _ => true


/-- A claim identifier resolves if it is bound in the document's claim bindings. -/
def claimResolves (input : InquiryInput) (c : ClaimId) : Bool :=
  input.claims.any fun b => b.claim = c

/-- Every claim referenced in an impact request resolves in the document's bindings. -/
def impactClaimsResolve (input : InquiryInput) : Bool :=
  input.requests.all fun r =>
    match r with
    | .impact _ _ _ queries => queries.all (claimResolves input)
    | _ => true
/-- The document's single observer projection: one `Source.checkFamily` pass over
the enumerated completions. Every embedded query and wrapper request reads this
same value, so the checker runs once per completion per family, not once per
emitted result. `projectionOf_eq_checkFamily` records that the shared value is
exactly the checker application each result would otherwise re-run, and
`projectionOf_checkedCompletions` records that it enumerates the family once. -/
def projectionOf (input : InquiryInput) (cs : List Completion) :
    Source.CheckedFamily (familyOf input) (configOf input) cs :=
  Source.checkFamily (familyOf input) (configOf input) cs

/-- The observer application a result builder would re-run for itself. It names
the per-request behavior the runner replaced with `projectionOf`; the sharing
theorem `perRequestProjection_eq_projectionOf` proves the two coincide. -/
def perRequestProjection (input : InquiryInput) (cs : List Completion) :
    Source.CheckedFamily (familyOf input) (configOf input) cs :=
  Source.checkFamily (familyOf input) (configOf input) cs

/-- The embedded results of a document: one labelled result per embedded query,
in the embedded order, all read from the one shared projection. -/
def embeddedResults {family : FamilySpec} {config : AuditConfig}
    {completions : List Completion} (checked : Source.CheckedFamily family config completions)
    (input : InquiryInput) : List InquiryResult :=
  input.process.queries.map fun q => embeddedResult checked input q

/-- The wrapper request results of a document, in request order, all read from
the one shared projection. -/
def requestResults {family : FamilySpec} {config : AuditConfig}
    {completions : List Completion} (checked : Source.CheckedFamily family config completions)
    (input : InquiryInput) : List InquiryResult :=
  input.requests.map fun r => ⟨RequestSpec.label r, requestBody checked input r⟩

/-- The reference semantics over an already-enumerated family: validate the
labels and references, then project one shared `CheckedFamily` once and read it
for both the embedded results and every request. Rejected sources stay family
rows. -/
def analyzeWith (cs : List Completion) (input : InquiryInput) :
    Except RunRefusal (List InquiryResult) :=
  if labelsDistinct input then
    if referencesResolve cs input then
      if impactClaimsResolve input then
        let checked := projectionOf input cs
        .ok (embeddedResults checked input ++ requestResults checked input)
      else .error (.malformed "unresolved claim in impact request")
    else .error (.malformed "unresolved or out-of-family source reference")
  else .error (.malformed "duplicate result labels")
/-! ### The shared projection is the per-request observer -/

/-- The pre-sharing reference semantics: every embedded query and wrapper
request re-runs the checker for itself (`perRequestProjection`). Its equality
with `analyzeWith` is the observer-sharing theorem: factoring the one-pass
projection out changes no emitted result. -/
def analyzeWithPerRequest (cs : List Completion) (input : InquiryInput) :
    Except RunRefusal (List InquiryResult) :=
  if labelsDistinct input then
    if referencesResolve cs input then
      if impactClaimsResolve input then
        .ok ((input.process.queries.map fun q =>
                embeddedResult (perRequestProjection input cs) input q) ++
              (input.requests.map fun r =>
                ⟨RequestSpec.label r,
                  requestBody (perRequestProjection input cs) input r⟩))
      else .error (.malformed "unresolved claim in impact request")
    else .error (.malformed "unresolved or out-of-family source reference")
  else .error (.malformed "duplicate result labels")
/-- **Observer sharing.** The shared one-pass projection is exactly the checker
application a result would re-run for itself. -/
theorem projectionOf_eq_checkFamily (input : InquiryInput) (cs : List Completion) :
    projectionOf input cs = Source.checkFamily (familyOf input) (configOf input) cs := rfl

/-- The per-request observer application coincides with the shared projection. -/
theorem perRequestProjection_eq_projectionOf (input : InquiryInput) (cs : List Completion) :
    perRequestProjection input cs = projectionOf input cs := rfl

/-- **One pass over the family.** The shared projection enumerates exactly the
enumerated completions, so no request re-runs enumeration or checking. -/
theorem projectionOf_checkedCompletions (input : InquiryInput) (cs : List Completion) :
    Analysis.checkedCompletions (projectionOf input cs) = cs :=
  Analysis.checkedCompletions_eq (projectionOf input cs)

/-- The shared projection's snapshots are the single map over the family that
`Source.checkFamily` performs — one observer pass per completion, shared. -/
theorem projectionOf_snapshots (input : InquiryInput) (cs : List Completion) :
    (projectionOf input cs).snapshots = cs.map (Source.takeSnapshot (familyOf input)) :=
  (projectionOf input cs).snapshots_eq

/-- The shared projection's rows are the single prepared map over those
snapshots: the checker work is done once and read by every result, not once per
emitted result. -/
theorem projectionOf_rows (input : InquiryInput) (cs : List Completion) :
    (projectionOf input cs).rows =
      (cs.map (Source.takeSnapshot (familyOf input))).map
        (Source.prepareRow (projectionOf input cs).context) := by
  rw [(projectionOf input cs).rows_eq, projectionOf_snapshots]

/-- Every embedded result read from the shared projection equals the embedded
result the same query would compute from its own re-run checker. -/
theorem embeddedResult_shared_eq_perRequest (input : InquiryInput) (cs : List Completion)
    (q : Wire.QuerySpec) :
    embeddedResult (projectionOf input cs) input q =
      embeddedResult (perRequestProjection input cs) input q := rfl

/-- Every wrapper request body read from the shared projection equals the body
the same request would compute from its own re-run checker. -/
theorem requestBody_shared_eq_perRequest (input : InquiryInput) (cs : List Completion)
    (r : RequestSpec) :
    requestBody (projectionOf input cs) input r =
      requestBody (perRequestProjection input cs) input r := rfl

/-- **The sharing changes no result.** The one-pass `analyzeWith` agrees with
the semantics that re-runs the checker per request. -/
theorem analyzeWith_eq_perRequest (cs : List Completion) (input : InquiryInput) :
    analyzeWith cs input = analyzeWithPerRequest cs input := by
  unfold analyzeWith analyzeWithPerRequest
  split
  · split
    · split <;> rfl
    · rfl
  · rfl
/-- The reference semantics of a whole document. It enumerates the *reference*
family (the declared product filtered by the guards, in the documented order)
and analyses it. -/
def reference (input : InquiryInput) : Except RunRefusal (List InquiryResult) :=
  analyzeWith (Enumerate.searchFamily (familyOf input)) input

/-! ## The bounded runner -/

/-- Frozen checker ceiling for the whole-document source-byte bound. -/
def maxInquirySourceBytes : Nat := 1048576

/-- Frozen checker ceiling for the aggregate declaration bound. -/
def maxInquiryDeclarations : Nat := 10000

/-- Frozen checker ceiling for the differential-pair bound. -/
def maxInquiryPairs : Nat := 4096

/-- Frozen checker ceiling for the assumption-subset bound. -/
def maxInquirySubsets : Nat := 4096

/-- The fixed checker ceiling of each counter. The P2 enumeration counters reuse
the frozen P2 ceilings. -/
def ceilingOf : LimitCounter → Nat
  | .histories => Enumerate.maxSearchHistories
  | .sources => Enumerate.maxSearchProducts
  | .sourceBytes => maxInquirySourceBytes
  | .declarations => maxInquiryDeclarations
  | .searchSteps => Enumerate.maxSearchSteps
  | .pairs => maxInquiryPairs
  | .subsets => maxInquirySubsets

/-- The whole-document declared bounds. -/
def declaredCap (l : InquiryLimits) : LimitCounter → Nat
  | .histories => l.histories
  | .sources => l.sources
  | .sourceBytes => l.sourceBytes
  | .declarations => l.declarations
  | .searchSteps => l.searchSteps
  | .pairs => l.pairs
  | .subsets => l.subsets

/-- Refuse the whole document when a declared-and-ceiling-capped bound is below
the actual count. Exactly at the effective cap is legal. -/
def checkBudgets (l : InquiryLimits) (actual : LimitCounter → Nat) :
    Except RunRefusal _root_.Unit :=
  if min l.sourceBytes maxInquirySourceBytes < actual .sourceBytes then
    .error (.limit .sourceBytes (actual .sourceBytes) (min l.sourceBytes maxInquirySourceBytes))
  else if min l.declarations maxInquiryDeclarations < actual .declarations then
    .error (.limit .declarations (actual .declarations) (min l.declarations maxInquiryDeclarations))
  else if min l.pairs maxInquiryPairs < actual .pairs then
    .error (.limit .pairs (actual .pairs) (min l.pairs maxInquiryPairs))
  else if min l.subsets maxInquirySubsets < actual .subsets then
    .error (.limit .subsets (actual .subsets) (min l.subsets maxInquirySubsets))
  else if min l.sources Enumerate.maxSearchProducts < actual .sources then
    .error (.limit .sources (actual .sources) (min l.sources Enumerate.maxSearchProducts))
  else if min l.searchSteps Enumerate.maxSearchSteps < actual .searchSteps then
    .error (.limit .searchSteps (actual .searchSteps) (min l.searchSteps Enumerate.maxSearchSteps))
  else .ok ()

/-- The P2 limits the runner hands to `Enumerate.enumerateFamily`. The history
bound is the minimum of the embedded completion bound and the inquiry history
bound; the source bound is the declared `sources` row bound. -/
def limitsOf (input : InquiryInput) : Enumerate.Limits :=
  { histories := min input.limits.histories (Wire.Document.completionLimit input.process)
    steps := input.limits.searchSteps
    products := input.limits.sources }

/-- Sum of a list of naturals. -/
def sumNat (l : List Nat) : Nat := l.foldr (· + ·) 0

/-- A sum of only zeros is zero. -/
theorem sumNat_replicate_zero (n : Nat) : sumNat (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [sumNat, List.replicate_succ] using ih

/-- The number of completions in the document's guarded family: the rows the
whole-document observers compare. -/
def familySize (input : InquiryInput) : Nat := (Enumerate.searchFamily (familyOf input)).length

/-- The declaration count of one source input's surface program. -/
def declarationsOf (input : SourceInput) : Nat := input.surface.program.decls.length

/-- The endpoints a request checks: two for every impact or verification
request (its before and after sources), none otherwise. -/
def endpointsOf : RequestSpec → Nat
  | .impact .. => 2
  | .verifyImpact .. => 2
  | _ => 0

/-- The endpoint declarations a request passes to source checking: both
endpoints of an impact or verification request, none otherwise. -/
def endpointDeclarationsOf : RequestSpec → Nat
  | .impact _ before after _ => declarationsOf before + declarationsOf after
  | .verifyImpact _ before after _ => declarationsOf before + declarationsOf after
  | _ => 0

/-- The differential-pair cost of one impact or verification comparison: one
public-status comparison and one graph node/edge comparison per query, plus
every read value in the comparison's recorded read set. -/
def impactPairs (before after : SourceInput) (queries : List Atom) : Nat :=
  queries.length + queries.length + (Impact.impactReads before after queries).card

/-- The observation-comparison cost of a minimal-assumptions request: the
assumption analysis visits every sublist of the deduplicated catalog
(`Analysis.minimalAssumptions`) and evaluates `Analysis.satisfiesB` on each,
reading the surviving restriction rows once per completion. Each visited subset
therefore makes one observation comparison per surviving row it reads; the
immediate-deletion re-tests read smaller sub-restrictions and are not
double-counted here. -/
def assumptionPairs (cs : List Completion) (catalog : List Literal) : Nat :=
  sumNat ((catalog.dedup.sublists).map fun L => (Analysis.restrict cs L).length)

/-- The differential-pair cost of one request. The observation-comparison
counters charge one comparison per family row: `status`/`audit` project and
compare the whole guarded family's rows, `stable` makes the pairwise
comparisons its single-pass stability report is decided from, and
`sensitivity`/`slots-sensitive` compare the reference observation against every
row. A `minimal-assumptions` request charges one observation comparison per
surviving restriction row of every visited catalog subset (`assumptionPairs`).
Impact and verification requests charge the per-query status, graph node/edge
and read-value comparisons. -/
def pairsFor (input : InquiryInput) (cs : List Completion) : RequestSpec → Nat
  | .status .. => cs.length
  | .audit .. => cs.length
  | .stable .. => cs.length
  | .sensitivity .. => cs.length
  | .slotsSensitive .. => cs.length
  | .minimalAssumptions .. => assumptionPairs cs input.catalog
  | .impact _ before after queries => impactPairs before after (queries.map (claimAtom input))
  | .verifyImpact _ before after certificate => impactPairs before after certificate.queries

/-- Reference comparison costs; the executable supplies its already bounded
family to `pairsFor` instead of enumerating it again. -/
def pairsOf (input : InquiryInput) : RequestSpec → Nat :=
  pairsFor input (Enumerate.searchFamily (familyOf input))

/-- The assumption-subset cost of one request: the number of catalog subsets
the minimal-assumptions analysis visits, `catalog.dedup.sublists`. -/
def subsetsOf (input : InquiryInput) : RequestSpec → Nat
  | .minimalAssumptions .. => 2 ^ input.catalog.dedup.length
  | _ => 0

/-- The number of a slot's choices whose guard holds at a fixed history: the
extensions the guarded traversal attempts at that slot. Guards depend only on
the history, so this count is the same at every partial assignment. -/
def slotChoiceCount (history : ProcessHistory) (slot : Family.Slot) : Nat :=
  (slot.choices.filter fun choice => choice.guard.eval history).length

/-- The number of nodes the guarded slot traversal (`Enumerate.guarded`) visits
for one history: the root plus, for each slot, every surviving partial
assignment. Its closed form is `Σ_k ∏_{j≤k} f_j`; the recurrence below is exactly
that sum, so it counts the traversal's nodes without materializing any
assignment. -/
def slotTraversalNodes (history : ProcessHistory) : List Family.Slot → Nat
  | [] => 1
  | slot :: rest => 1 + slotChoiceCount history slot * slotTraversalNodes history rest

/-- The attempted slot extensions over the enumerated histories: every non-root
guarded-traversal node is one attempted extension by one choice, so this is
`Σ_history (slotTraversalNodes history slots - 1)`, the slot half of the
`search-steps` counter that the frozen P2 `Enumerate.searchSteps` omits. -/
def slotExtensions (input : InquiryInput) : Nat :=
  sumNat ((Enumerate.search (embeddedProblem input)).map fun history =>
    slotTraversalNodes history input.slots - 1)

/-- Every counter's actual value for a document, computed deterministically from
the decoded input. `sourceBytes` measures UTF-8 bytes in the canonical encoding
for typed callers; the executable supplies the original file's byte count.
`sources` counts every observed family row, rejected rows included, plus each endpoint checked for
every impact or verification request; `declarations` counts the aggregate
declarations passed to source checking, including repeated materializations and
pairwise endpoints; both charge repeated requests again. `searchSteps` counts
the history prefix-DFS (`Enumerate.searchSteps`) plus every attempted slot
extension (`slotExtensions`). -/
def actualFor (input : InquiryInput) (cs : List Completion) (sourceBytes : Nat) :
    LimitCounter → Nat
  | .histories => (Enumerate.search (embeddedProblem input)).length
  | .searchSteps => Enumerate.searchSteps (embeddedProblem input) + slotExtensions input
  | .sources => cs.length + sumNat (input.requests.map endpointsOf)
  | .sourceBytes => sourceBytes
  | .declarations =>
      sumNat (cs.map fun c =>
        (Family.materialize (familyOf input) c).surface.program.decls.length)
      + sumNat (input.requests.map endpointDeclarationsOf)
  | .pairs => sumNat (input.requests.map (pairsFor input cs))
  | .subsets => sumNat (input.requests.map (subsetsOf input))

/-- Reference counters. Runtime accounting uses `actualFor` on the bounded
enumerator's returned rows, never a second reference enumeration. -/
def actualOf (input : InquiryInput) : LimitCounter → Nat :=
  actualFor input (Enumerate.searchFamily (familyOf input))
    (Lara.Driver.printSx (encodeInquiryInput input)).utf8ByteSize

/-! ### Counter characterizations -/

/-- The guarded family row count the source-budget and observation counters use. -/
theorem familySize_eq (input : InquiryInput) :
    familySize input = (Enumerate.searchFamily (familyOf input)).length := rfl

/-- **`sources` counts family rows plus endpoints.** Every observed family row,
rejected rows included, plus two endpoints per impact or verification request. -/
theorem actualOf_sources_eq (input : InquiryInput) :
    actualOf input .sources = familySize input + sumNat (input.requests.map endpointsOf) := rfl

/-- **`declarations` counts materializations plus endpoint declarations.** The
aggregate declarations passed to source checking: every family materialization
plus both endpoints of every impact or verification request. -/
theorem actualOf_declarations_eq (input : InquiryInput) :
    actualOf input .declarations =
      sumNat ((Enumerate.searchFamily (familyOf input)).map fun c =>
        (Family.materialize (familyOf input) c).surface.program.decls.length)
      + sumNat (input.requests.map endpointDeclarationsOf) := rfl

/-- **`pairs` sums the per-request comparison costs.** -/
theorem actualOf_pairs_eq (input : InquiryInput) :
    actualOf input .pairs = sumNat (input.requests.map (pairsOf input)) := rfl

/-- **`searchSteps` counts history nodes plus slot extensions.** -/
theorem actualOf_searchSteps_eq (input : InquiryInput) :
    actualOf input .searchSteps =
      Enumerate.searchSteps (embeddedProblem input) + slotExtensions input := rfl

/-- The slot-extension charge: the sum over every enumerated history of its
guarded-traversal nodes minus the root. -/
theorem slotExtensions_eq (input : InquiryInput) :
    slotExtensions input =
      sumNat ((Enumerate.search (embeddedProblem input)).map fun history =>
        slotTraversalNodes history input.slots - 1) := rfl

/-- The traversal-node recurrence: a node plus one subtree per surviving choice. -/
theorem slotTraversalNodes_cons (history : ProcessHistory) (slot : Family.Slot)
    (rest : List Family.Slot) :
    slotTraversalNodes history (slot :: rest) =
      1 + slotChoiceCount history slot * slotTraversalNodes history rest := rfl

/-- With no slots the guarded traversal is the single root: no extensions. -/
theorem slotTraversalNodes_nil (history : ProcessHistory) :
    slotTraversalNodes history [] = 1 := rfl

/-- A history with no slots and no choices makes no slot extension. -/
theorem slotExtensions_no_slots (input : InquiryInput) (h : input.slots = []) :
    slotExtensions input = 0 := by
  unfold slotExtensions
  simp [h, slotTraversalNodes_nil, sumNat_replicate_zero]

/-- An impact request checks both endpoints. -/
theorem endpointsOf_impact (label : String) (before after : SourceInput)
    (queries : List ClaimId) :
    endpointsOf (.impact label before after queries) = 2 := rfl

/-- A verification request checks both endpoints. -/
theorem endpointsOf_verifyImpact (label : String) (before after : SourceInput)
    (certificate : ImpactCertificateWire) :
    endpointsOf (.verifyImpact label before after certificate) = 2 := rfl

/-- A family status request compares every guarded family row. -/
theorem pairsOf_status (input : InquiryInput) (label : String) (claim : ClaimId) :
    pairsOf input (.status label claim) = familySize input := rfl

/-- A family audit request compares every guarded family row. -/
theorem pairsOf_audit (input : InquiryInput) (label : String) (claim : ClaimId)
    (witness : WitnessId) (profile : Process.Wire.ProfileSpec) :
    pairsOf input (.audit label claim witness profile) = familySize input := rfl

/-- A stability request makes one pairwise comparison per family row. -/
theorem pairsOf_stable (input : InquiryInput) (label : String) (obs : ObservableSpec) :
    pairsOf input (.stable label obs) = familySize input := rfl

/-- A sensitivity request compares the reference against every family row. -/
theorem pairsOf_sensitivity (input : InquiryInput) (label : String) (reference : ReferenceSpec)
    (obs : ObservableSpec) :
    pairsOf input (.sensitivity label reference obs) = familySize input := rfl

/-- An impact request charges its per-query status, graph node/edge and recorded
read-value comparisons. -/
theorem pairsOf_impact (input : InquiryInput) (label : String) (before after : SourceInput)
    (queries : List ClaimId) :
    pairsOf input (.impact label before after queries) =
      impactPairs before after (queries.map (claimAtom input)) := rfl

/-- A verification request charges its per-query status, graph node/edge and
recorded read-value comparisons. -/
theorem pairsOf_verifyImpact (input : InquiryInput) (label : String) (before after : SourceInput)
    (certificate : ImpactCertificateWire) :
    pairsOf input (.verifyImpact label before after certificate) =
      impactPairs before after certificate.queries := rfl

/-- The `assumptionPairs` reading: the sum, over the sublists of the deduplicated
catalog, of the surviving restriction rows read (one observation comparison
per row). -/
theorem assumptionPairs_eq (cs : List Completion) (catalog : List Literal) :
    assumptionPairs cs catalog =
      sumNat ((catalog.dedup.sublists).map fun L => (Analysis.restrict cs L).length) := rfl

/-- A minimal-assumptions request charges one observation comparison per
surviving restriction row of every visited catalog subset. -/
theorem pairsOf_minimalAssumptions (input : InquiryInput) (label : String)
    (target : TargetSpec) :
    pairsOf input (.minimalAssumptions label target) =
      assumptionPairs (Enumerate.searchFamily (familyOf input)) input.catalog := rfl

/-- The subset charge of a minimal-assumptions request is the deduplicated
powerset size, not the raw catalog size. -/
theorem subsetsOf_minimalAssumptions (input : InquiryInput) (label : String)
    (target : TargetSpec) :
    subsetsOf input (.minimalAssumptions label target) = 2 ^ input.catalog.dedup.length := rfl

/-- The charged subset count is exactly the number of catalog subsets the
analysis visits (`catalog.dedup.sublists`). -/
theorem subsetsOf_minimalAssumptions_eq_length (input : InquiryInput) (label : String)
    (target : TargetSpec) :
    subsetsOf input (.minimalAssumptions label target) =
      (input.catalog.dedup.sublists).length := by
  rw [subsetsOf_minimalAssumptions, List.length_sublists]

/-- Translate a P2 refusal into the wire refusal. -/
def ofRefusal : Enumerate.Refusal → RunRefusal
  | .histories actual cap => .limit .histories actual cap
  | .steps actual cap => .limit .searchSteps actual cap
  | .products actual cap => .limit .sources actual cap

/-- The embedded `process` document's event bound, retained from P0: the
deduplicated recorded/universe carrier may not exceed the document's effective
event limit (`Wire.Document.eventLimit`, i.e. the declared bound capped by the
frozen `Wire.maxProcessEvents`). The inquiry wire has no separate `events`
counter, so the refusal is reported through the `histories` counter, which
bounds the same search. -/
def checkEmbeddedEvents (input : InquiryInput) : Except RunRefusal _root_.Unit :=
  if Wire.Document.eventLimit input.process < (embeddedProblem input).eventCount then
    .error (.limit .histories (embeddedProblem input).eventCount
      (Wire.Document.eventLimit input.process))
  else .ok ()

/-- Replace the typed input's canonical byte count with the wire input's exact
UTF-8 size. Whitespace and noncanonical spelling remain charged. -/
def actualWithSourceBytes (input : InquiryInput) (sourceBytes : Nat) : LimitCounter → Nat
  | .sourceBytes => sourceBytes
  | counter => actualOf input counter

/-- Runtime counts agree with the reference when bounded enumeration succeeds. -/
theorem actualFor_reference (input : InquiryInput) (sourceBytes : Nat) :
    actualFor input (Enumerate.searchFamily (familyOf input)) sourceBytes =
      actualWithSourceBytes input sourceBytes := by
  funext counter
  cases counter <;> rfl

/-- Bounds that must precede materialization and subset comparisons. The supplied
counter function must count sources and subsets without constructing either. -/
def checkAllocationBudgets (l : InquiryLimits) (actual : LimitCounter → Nat) :
    Except RunRefusal _root_.Unit :=
  if min l.sources Enumerate.maxSearchProducts < actual .sources then
    .error (.limit .sources (actual .sources) (min l.sources Enumerate.maxSearchProducts))
  else if min l.subsets maxInquirySubsets < actual .subsets then
    .error (.limit .subsets (actual .subsets) (min l.subsets maxInquirySubsets))
  else .ok ()

/-- The bounded runner checks raw bytes before traversal, bounds the family
before materializing sources, and bounds subsets before comparison accounting.
Only then can observation and result dispatch begin. -/
def runBounded (input : InquiryInput) (sourceBytes : Nat) :
    Except RunRefusal (List InquiryResult) :=
  match checkEmbeddedEvents input with
  | .error e => .error e
  | .ok _ =>
    if min input.limits.sourceBytes maxInquirySourceBytes < sourceBytes then
      .error (.limit .sourceBytes sourceBytes
        (min input.limits.sourceBytes maxInquirySourceBytes))
    else
      match Enumerate.enumerateFamily (familyOf input) (limitsOf input) with
      | .error e => .error (ofRefusal e)
      | .ok cs =>
        let actual := actualFor input cs sourceBytes
        match checkAllocationBudgets input.limits actual with
        | .error e => .error e
        | .ok _ =>
          match checkBudgets input.limits actual with
          | .error e => .error e
          | .ok _ => analyzeWith cs input

/-- The raw byte count is enforced before enumeration or source checking. -/
theorem runBounded_sourceBytes_limit (input : InquiryInput) (sourceBytes : Nat)
    (hevents : checkEmbeddedEvents input = .ok ())
    (overshoot : min input.limits.sourceBytes maxInquirySourceBytes < sourceBytes) :
    runBounded input sourceBytes =
      .error (.limit .sourceBytes sourceBytes
        (min input.limits.sourceBytes maxInquirySourceBytes)) := by
  simp [runBounded, hevents, overshoot]

/-- The process exit code of a refusal: `unsupported` and `limit` are 1, every
other refusal 2. -/
def exitCodeOf : RunRefusal → UInt32
  | .unsupported _ => 1
  | .limit _ _ _ => 1
  | _ => 2

/-! ## Budget-check laws (exact-at-cap and cap-plus-one fixtures) -/

theorem checkBudgets_eq_ok (l : InquiryLimits) (actual : LimitCounter → Nat)
    (h₁ : actual .sourceBytes ≤ min l.sourceBytes maxInquirySourceBytes)
    (h₂ : actual .declarations ≤ min l.declarations maxInquiryDeclarations)
    (h₃ : actual .pairs ≤ min l.pairs maxInquiryPairs)
    (h₄ : actual .subsets ≤ min l.subsets maxInquirySubsets)
    (h₅ : actual .sources ≤ min l.sources Enumerate.maxSearchProducts)
    (h₆ : actual .searchSteps ≤ min l.searchSteps Enumerate.maxSearchSteps) :
    checkBudgets l actual = .ok () := by
  unfold checkBudgets
  rw [if_neg (Nat.not_lt_of_ge h₁), if_neg (Nat.not_lt_of_ge h₂),
    if_neg (Nat.not_lt_of_ge h₃), if_neg (Nat.not_lt_of_ge h₄),
    if_neg (Nat.not_lt_of_ge h₅), if_neg (Nat.not_lt_of_ge h₆)]

/-- A successful full budget check implies the cheap allocation prerequisites. -/
theorem checkBudgets_allocation_bounds (l : InquiryLimits) (actual : LimitCounter → Nat)
    (h : checkBudgets l actual = .ok ()) :
    actual .sourceBytes ≤ min l.sourceBytes maxInquirySourceBytes ∧
      actual .sources ≤ min l.sources Enumerate.maxSearchProducts ∧
      actual .subsets ≤ min l.subsets maxInquirySubsets := by
  unfold checkBudgets at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  omega

theorem checkAllocationBudgets_of_fits (l : InquiryLimits) (actual : LimitCounter → Nat)
    (h : checkBudgets l actual = .ok ()) :
    checkAllocationBudgets l actual = .ok () := by
  obtain ⟨_, hsources, hsubsets⟩ := checkBudgets_allocation_bounds l actual h
  simp [checkAllocationBudgets, Nat.not_lt_of_ge hsources, Nat.not_lt_of_ge hsubsets]

/-- Exactly at the source-byte cap is legal (given the whole computation fits). -/
theorem checkBudgets_at_cap_sourceBytes (l : InquiryLimits) (actual : LimitCounter → Nat)
    (h₁ : actual .sourceBytes = min l.sourceBytes maxInquirySourceBytes)
    (h₂ : actual .declarations ≤ min l.declarations maxInquiryDeclarations)
    (h₃ : actual .pairs ≤ min l.pairs maxInquiryPairs)
    (h₄ : actual .subsets ≤ min l.subsets maxInquirySubsets)
    (h₅ : actual .sources ≤ min l.sources Enumerate.maxSearchProducts)
    (h₆ : actual .searchSteps ≤ min l.searchSteps Enumerate.maxSearchSteps) :
    checkBudgets l actual = .ok () :=
  checkBudgets_eq_ok l actual (le_of_eq h₁) h₂ h₃ h₄ h₅ h₆

/-- One over the source-byte cap refuses the whole document. -/
theorem checkBudgets_cap_plus_one_sourceBytes (l : InquiryLimits)
    (actual : LimitCounter → Nat)
    (overshoot : actual .sourceBytes = min l.sourceBytes maxInquirySourceBytes + 1) :
    checkBudgets l actual =
      .error (.limit .sourceBytes (actual .sourceBytes)
        (min l.sourceBytes maxInquirySourceBytes)) := by
  unfold checkBudgets
  rw [if_pos (by omega), overshoot]

/-- Exactly at the declaration cap is legal. -/
theorem checkBudgets_at_cap_declarations (l : InquiryLimits) (actual : LimitCounter → Nat)
    (h₁ : actual .sourceBytes ≤ min l.sourceBytes maxInquirySourceBytes)
    (h₂ : actual .declarations = min l.declarations maxInquiryDeclarations)
    (h₃ : actual .pairs ≤ min l.pairs maxInquiryPairs)
    (h₄ : actual .subsets ≤ min l.subsets maxInquirySubsets)
    (h₅ : actual .sources ≤ min l.sources Enumerate.maxSearchProducts)
    (h₆ : actual .searchSteps ≤ min l.searchSteps Enumerate.maxSearchSteps) :
    checkBudgets l actual = .ok () :=
  checkBudgets_eq_ok l actual h₁ (le_of_eq h₂) h₃ h₄ h₅ h₆

/-- One over the declaration cap refuses the whole document. -/
theorem checkBudgets_cap_plus_one_declarations (l : InquiryLimits)
    (actual : LimitCounter → Nat)
    (h₁ : actual .sourceBytes ≤ min l.sourceBytes maxInquirySourceBytes)
    (overshoot : actual .declarations = min l.declarations maxInquiryDeclarations + 1) :
    checkBudgets l actual =
      .error (.limit .declarations (actual .declarations)
        (min l.declarations maxInquiryDeclarations)) := by
  unfold checkBudgets
  rw [if_neg (Nat.not_lt_of_ge h₁), if_pos (by omega), overshoot]

/-- Exactly at the pair cap is legal. -/
theorem checkBudgets_at_cap_pairs (l : InquiryLimits) (actual : LimitCounter → Nat)
    (h₁ : actual .sourceBytes ≤ min l.sourceBytes maxInquirySourceBytes)
    (h₂ : actual .declarations ≤ min l.declarations maxInquiryDeclarations)
    (h₃ : actual .pairs = min l.pairs maxInquiryPairs)
    (h₄ : actual .subsets ≤ min l.subsets maxInquirySubsets)
    (h₅ : actual .sources ≤ min l.sources Enumerate.maxSearchProducts)
    (h₆ : actual .searchSteps ≤ min l.searchSteps Enumerate.maxSearchSteps) :
    checkBudgets l actual = .ok () :=
  checkBudgets_eq_ok l actual h₁ h₂ (le_of_eq h₃) h₄ h₅ h₆

/-- One over the pair cap refuses the whole document. -/
theorem checkBudgets_cap_plus_one_pairs (l : InquiryLimits) (actual : LimitCounter → Nat)
    (h₁ : actual .sourceBytes ≤ min l.sourceBytes maxInquirySourceBytes)
    (h₂ : actual .declarations ≤ min l.declarations maxInquiryDeclarations)
    (overshoot : actual .pairs = min l.pairs maxInquiryPairs + 1) :
    checkBudgets l actual =
      .error (.limit .pairs (actual .pairs) (min l.pairs maxInquiryPairs)) := by
  unfold checkBudgets
  rw [if_neg (Nat.not_lt_of_ge h₁), if_neg (Nat.not_lt_of_ge h₂),
    if_pos (by omega), overshoot]

/-- Exactly at the subset cap is legal. -/
theorem checkBudgets_at_cap_subsets (l : InquiryLimits) (actual : LimitCounter → Nat)
    (h₁ : actual .sourceBytes ≤ min l.sourceBytes maxInquirySourceBytes)
    (h₂ : actual .declarations ≤ min l.declarations maxInquiryDeclarations)
    (h₃ : actual .pairs ≤ min l.pairs maxInquiryPairs)
    (h₄ : actual .subsets = min l.subsets maxInquirySubsets)
    (h₅ : actual .sources ≤ min l.sources Enumerate.maxSearchProducts)
    (h₆ : actual .searchSteps ≤ min l.searchSteps Enumerate.maxSearchSteps) :
    checkBudgets l actual = .ok () :=
  checkBudgets_eq_ok l actual h₁ h₂ h₃ (le_of_eq h₄) h₅ h₆

/-- One over the subset cap refuses the whole document. -/
theorem checkBudgets_cap_plus_one_subsets (l : InquiryLimits) (actual : LimitCounter → Nat)
    (h₁ : actual .sourceBytes ≤ min l.sourceBytes maxInquirySourceBytes)
    (h₂ : actual .declarations ≤ min l.declarations maxInquiryDeclarations)
    (h₃ : actual .pairs ≤ min l.pairs maxInquiryPairs)
    (overshoot : actual .subsets = min l.subsets maxInquirySubsets + 1) :
    checkBudgets l actual =
      .error (.limit .subsets (actual .subsets) (min l.subsets maxInquirySubsets)) := by
  unfold checkBudgets
  rw [if_neg (Nat.not_lt_of_ge h₁), if_neg (Nat.not_lt_of_ge h₂),
    if_neg (Nat.not_lt_of_ge h₃), if_pos (by omega), overshoot]

/-- Exactly at the source cap is legal: every observed family row plus every
impact/verification endpoint fits the shared budget. -/
theorem checkBudgets_at_cap_sources (l : InquiryLimits) (actual : LimitCounter → Nat)
    (h₁ : actual .sourceBytes ≤ min l.sourceBytes maxInquirySourceBytes)
    (h₂ : actual .declarations ≤ min l.declarations maxInquiryDeclarations)
    (h₃ : actual .pairs ≤ min l.pairs maxInquiryPairs)
    (h₄ : actual .subsets ≤ min l.subsets maxInquirySubsets)
    (h₅ : actual .sources = min l.sources Enumerate.maxSearchProducts)
    (h₆ : actual .searchSteps ≤ min l.searchSteps Enumerate.maxSearchSteps) :
    checkBudgets l actual = .ok () :=
  checkBudgets_eq_ok l actual h₁ h₂ h₃ h₄ (le_of_eq h₅) h₆

/-- One over the source cap refuses the whole document before any dispatch. -/
theorem checkBudgets_cap_plus_one_sources (l : InquiryLimits) (actual : LimitCounter → Nat)
    (h₁ : actual .sourceBytes ≤ min l.sourceBytes maxInquirySourceBytes)
    (h₂ : actual .declarations ≤ min l.declarations maxInquiryDeclarations)
    (h₃ : actual .pairs ≤ min l.pairs maxInquiryPairs)
    (h₄ : actual .subsets ≤ min l.subsets maxInquirySubsets)
    (overshoot : actual .sources = min l.sources Enumerate.maxSearchProducts + 1) :
    checkBudgets l actual =
      .error (.limit .sources (actual .sources) (min l.sources Enumerate.maxSearchProducts)) := by
  unfold checkBudgets
  rw [if_neg (Nat.not_lt_of_ge h₁), if_neg (Nat.not_lt_of_ge h₂),
    if_neg (Nat.not_lt_of_ge h₃), if_neg (Nat.not_lt_of_ge h₄),
    if_pos (by omega), overshoot]

/-- Exactly at the search-step cap is legal: the history prefix-DFS plus every
attempted slot extension fits the shared budget. -/
theorem checkBudgets_at_cap_searchSteps (l : InquiryLimits) (actual : LimitCounter → Nat)
    (h₁ : actual .sourceBytes ≤ min l.sourceBytes maxInquirySourceBytes)
    (h₂ : actual .declarations ≤ min l.declarations maxInquiryDeclarations)
    (h₃ : actual .pairs ≤ min l.pairs maxInquiryPairs)
    (h₄ : actual .subsets ≤ min l.subsets maxInquirySubsets)
    (h₅ : actual .sources ≤ min l.sources Enumerate.maxSearchProducts)
    (h₆ : actual .searchSteps = min l.searchSteps Enumerate.maxSearchSteps) :
    checkBudgets l actual = .ok () :=
  checkBudgets_eq_ok l actual h₁ h₂ h₃ h₄ h₅ (le_of_eq h₆)

/-- One over the search-step cap refuses the whole document before any
enumeration or dispatch. -/
theorem checkBudgets_cap_plus_one_searchSteps (l : InquiryLimits) (actual : LimitCounter → Nat)
    (h₁ : actual .sourceBytes ≤ min l.sourceBytes maxInquirySourceBytes)
    (h₂ : actual .declarations ≤ min l.declarations maxInquiryDeclarations)
    (h₃ : actual .pairs ≤ min l.pairs maxInquiryPairs)
    (h₄ : actual .subsets ≤ min l.subsets maxInquirySubsets)
    (h₅ : actual .sources ≤ min l.sources Enumerate.maxSearchProducts)
    (overshoot : actual .searchSteps = min l.searchSteps Enumerate.maxSearchSteps + 1) :
    checkBudgets l actual =
      .error (.limit .searchSteps (actual .searchSteps)
        (min l.searchSteps Enumerate.maxSearchSteps)) := by
  unfold checkBudgets
  rw [if_neg (Nat.not_lt_of_ge h₁), if_neg (Nat.not_lt_of_ge h₂),
    if_neg (Nat.not_lt_of_ge h₃), if_neg (Nat.not_lt_of_ge h₄),
    if_neg (Nat.not_lt_of_ge h₅), if_pos (by omega), overshoot]

/-! ## Enumeration cap fixtures (histories, steps, sources) -/

/-- Exactly at every enumeration cap is legal when the whole search finishes. -/
theorem family_at_cap (spec : FamilySpec) (lim : Enumerate.Limits)
    (hsteps : Enumerate.searchSteps spec.problem ≤ lim.clamped.steps)
    (hlen : (Enumerate.search spec.problem).length ≤ lim.clamped.histories)
    (hprod : (Enumerate.searchFamily spec).length ≤ lim.clamped.products) :
    Enumerate.enumerateFamily spec lim = .ok (Enumerate.searchFamily spec) :=
  Enumerate.enumerateFamily_eq_ok spec lim hsteps hlen hprod

/-- One over the distinct-history cap refuses the whole document. -/
theorem family_histories_cap_plus_one (spec : FamilySpec) (lim : Enumerate.Limits)
    (hsteps : Enumerate.searchSteps spec.problem ≤ lim.clamped.steps)
    (overshoot : (Enumerate.search spec.problem).length = lim.clamped.histories + 1) :
    Enumerate.enumerateFamily spec lim =
      .error (.histories (lim.clamped.histories + 1) lim.clamped.histories) := by
  simp only [Enumerate.enumerateFamily,
    Enumerate.enumerateProblem_cap_plus_one_histories spec.problem lim hsteps overshoot]

/-- One over the search-step cap refuses the whole document. -/
theorem family_steps_cap_plus_one (spec : FamilySpec) (lim : Enumerate.Limits)
    (overshoot : Enumerate.searchSteps spec.problem = lim.clamped.steps + 1) :
    Enumerate.enumerateFamily spec lim =
      .error (.steps (lim.clamped.steps + 1) lim.clamped.steps) := by
  simp only [Enumerate.enumerateFamily,
    Enumerate.enumerateProblem_cap_plus_one_steps spec.problem lim overshoot]

/-- One over the source-product cap refuses the whole document. -/
theorem family_sources_cap_plus_one (spec : FamilySpec) (lim : Enumerate.Limits)
    (hsteps : Enumerate.searchSteps spec.problem ≤ lim.clamped.steps)
    (hlen : (Enumerate.search spec.problem).length ≤ lim.clamped.histories)
    (overshoot : (Enumerate.searchFamily spec).length = lim.clamped.products + 1) :
    Enumerate.enumerateFamily spec lim =
      .error (.products (lim.clamped.products + 1) lim.clamped.products) :=
  Enumerate.enumerateFamily_cap_plus_one_products spec lim hsteps hlen overshoot

/-! ## Bounded runner equals the reference -/

/-- A successful bounded result equals the reference result. The bounded
enumeration returns the reference family exactly when it fits the caps
(`enumerateFamily_ok`), and both then run the same `analyzeWith`. -/
theorem runBounded_eq_reference (input : InquiryInput) (sourceBytes : Nat)
    {rs : List InquiryResult}
    (h : runBounded input sourceBytes = .ok rs) : reference input = .ok rs := by
  unfold runBounded at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i cs hcs
        have hcs' : cs = Enumerate.searchFamily (familyOf input) :=
          (Enumerate.enumerateFamily_ok (familyOf input) (limitsOf input) hcs).1
        dsimp only at h
        split at h
        · cases h
        · split at h
          · cases h
          · rw [hcs'] at h
            simpa [reference] using h

/-- A refused document yields no result at all: no partial rows escape. -/
theorem runBounded_refusal_no_result (input : InquiryInput) (sourceBytes : Nat)
    {r : RunRefusal} (h : runBounded input sourceBytes = .error r) :
    ¬ ∃ rs, runBounded input sourceBytes = .ok rs := by
  rintro ⟨rs, hok⟩
  rw [h] at hok
  exact absurd hok (by simp)

/-- The bounded runner is `reference` whenever the document fits its budget. -/
theorem runBounded_eq_reference_of_fits (input : InquiryInput) (sourceBytes : Nat)
    (hevents : checkEmbeddedEvents input = .ok ())
    (hbudget : checkBudgets input.limits (actualWithSourceBytes input sourceBytes) = .ok ())
    (hsteps : Enumerate.searchSteps (embeddedProblem input) ≤ (limitsOf input).clamped.steps)
    (hlen : (Enumerate.search (embeddedProblem input)).length ≤ (limitsOf input).clamped.histories)
    (hprod : (Enumerate.searchFamily (familyOf input)).length ≤ (limitsOf input).clamped.products) :
    runBounded input sourceBytes = reference input := by
  have hbytes := (checkBudgets_allocation_bounds _ _ hbudget).1
  have halloc := checkAllocationBudgets_of_fits _ _ hbudget
  change sourceBytes ≤ _ at hbytes
  unfold runBounded
  rw [hevents]
  simp only [if_neg (Nat.not_lt_of_ge hbytes)]
  rw [Enumerate.enumerateFamily_eq_ok (familyOf input) (limitsOf input) hsteps hlen hprod]
  simp only [actualFor_reference, halloc, hbudget]
  rfl

/-! ### The embedded event-bound fixtures -/

/-- Exactly at the embedded event bound is legal. -/
theorem embeddedEvents_at_cap (input : InquiryInput)
    (h : (embeddedProblem input).eventCount = Wire.Document.eventLimit input.process) :
    checkEmbeddedEvents input = .ok () := by
  unfold checkEmbeddedEvents
  rw [if_neg (Nat.not_lt_of_le (le_of_eq h))]

/-- One over the embedded event bound refuses the whole document. -/
theorem embeddedEvents_cap_plus_one (input : InquiryInput)
    (h : (embeddedProblem input).eventCount = Wire.Document.eventLimit input.process + 1) :
    checkEmbeddedEvents input =
      .error (.limit .histories (embeddedProblem input).eventCount
        (Wire.Document.eventLimit input.process)) := by
  unfold checkEmbeddedEvents
  rw [if_pos (by omega), h]

/-! ## P0 compatibility -/

/-- The embedded verdicts of a P0 document, as `(label, history count, answer)`
triples in the document's query order. The history count is the distinct
unguarded completion count. -/
def embeddedVerdicts (d : Wire.Document) : List (String × Nat × OutcomeAnswer) :=
  (d.queries.filterMap fun q =>
    match q with
    | .verdict name f => some (name, Universe.answer d.problem f)
    | .audit .. => none).map fun p =>
      (p.1, d.problem.completions.length, OutcomeAnswer.ofAnswer p.2)

/-- P0 verdict/count agreement: for any document the P0 runner accepts, the
embedded verdict results agree with P0's own `answer` verdicts and counts, in
order. -/
theorem embeddedVerdicts_eq_p0 {d : Wire.Document} {r : Wire.Result} (h : Wire.run d = .ok r) :
    embeddedVerdicts d =
      r.answers.map fun p =>
        (p.1, d.problem.completions.length, OutcomeAnswer.ofAnswer p.2) := by
  rw [(Wire.run_answers h).2]
  rfl

/-- Byte-level P0 agreement: the encoded embedded verdict answers are exactly the
P0 `process-result` answer bytes (`encodeOutcomeAnswer_ofAnswer`). -/
theorem embedded_verdict_bytes_eq_p0 {d : Wire.Document} {r : Wire.Result}
    (h : Wire.run d = .ok r) :
    (embeddedVerdicts d).map (fun p => encodeOutcomeAnswer d.names p.1 p.2.2) =
      r.answers.map fun p => Wire.encodeAnswer d.names p := by
  rw [embeddedVerdicts_eq_p0 h]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro p _
  exact encodeOutcomeAnswer_ofAnswer d.names p.1 p.2

/-- The old `run_answers` theorem is preserved at the old entry point. -/
theorem p0_run_answers_preserved (d : Wire.Document) (r : Wire.Result) (h : Wire.run d = .ok r) :
    r.problem = d.problem := (Wire.run_answers h).1

/-- The old `run_answers` answer list is preserved at the old entry point. -/
theorem p0_run_answers_list_preserved (d : Wire.Document) (r : Wire.Result)
    (h : Wire.run d = .ok r) :
    r.answers = d.queries.filterMap fun q =>
      match q with
      | .verdict name f => some (name, Universe.answer d.problem f)
      | .audit .. => none := (Wire.run_answers h).2

/-- The old `run_audit` refusal theorem is preserved at the old entry point. -/
theorem p0_run_audit_preserved (d : Wire.Document) (name : String) (c : ClaimId)
    (w : WitnessId) (p : Wire.ProfileSpec) (mem : Wire.QuerySpec.audit name c w p ∈ d.queries)
    (r : Wire.Result) : Wire.run d ≠ .ok r :=
  Wire.run_audit mem r

/-- The no-slot projection: with no source slots, the reference family's
histories are exactly P0's completions, in order. -/
theorem referenceFamily_no_slots (problem : Universe.Problem) (base : SourceInput) :
    (Family.referenceFamily ⟨problem, base, []⟩).map Family.Completion.history =
      problem.completions :=
  Family.referenceFamily_no_slots_projection problem base

/-- With no source slots, the generated family's histories are a permutation of
P0's completions (the runner's documented witness order is not P0's byte order). -/
theorem searchFamily_no_slots_perm (problem : Universe.Problem) (base : SourceInput) :
    ((Enumerate.searchFamily ⟨problem, base, []⟩).map Family.Completion.history).Perm
      problem.completions :=
  ((Enumerate.searchFamily_perm ⟨problem, base, []⟩).map Family.Completion.history).trans
    (by rw [referenceFamily_no_slots problem base])

/-- The membership guarantee of the new runner's source witnesses: a completion
is a generated family row exactly when it is a reference-family row. -/
theorem new_witness_mem_iff_reference (spec : FamilySpec) (c : Completion) :
    c ∈ Enumerate.searchFamily spec ↔ c ∈ Family.referenceFamily spec :=
  (Enumerate.searchFamily_perm spec).mem_iff

/-- The membership guarantee agrees with P0's: a completion is a generated row
exactly when its history is a P0 completion selecting the declared guards. -/
theorem new_witness_mem_iff_p0 (spec : FamilySpec) (c : Completion) :
    c ∈ Enumerate.searchFamily spec ↔
      c.history ∈ spec.problem.completions ∧
        Family.Chooses c.history spec.slots c.assignment :=
  Enumerate.mem_searchFamily spec c

/-- Validation splitting: a well-formed analysis is exactly the embedded results
followed by the request results. -/
theorem analyzeWith_ok_split (cs : List Completion) (input : InquiryInput)
    {xs : List InquiryResult} (h : analyzeWith cs input = .ok xs) :
    labelsDistinct input = true ∧ referencesResolve cs input = true ∧
      impactClaimsResolve input = true ∧
      xs = embeddedResults (projectionOf input cs) input
        ++ requestResults (projectionOf input cs) input := by
  unfold analyzeWith at h
  split at h
  · rename_i hlabels
    split at h
    · rename_i hrefs
      split at h
      · rename_i hclaims
        refine ⟨hlabels, hrefs, hclaims, ?_⟩
        dsimp only at h
        exact (Except.ok.inj h).symm
      · cases h
    · cases h
  · cases h
/-- The emitted verdict result for an embedded verdict query is exactly the P0
answer, placed in the embedded order. -/
theorem analyzeWith_embedded_verdict_mem (input : InquiryInput) (cs : List Completion)
    {name : String} {f : Query}
    (mem : Wire.QuerySpec.verdict name f ∈ input.process.queries)
    {xs : List InquiryResult} (h : analyzeWith cs input = .ok xs) :
    ⟨name, .histories (embeddedProblem input).completions.length
      (OutcomeAnswer.ofAnswer (Universe.answer (embeddedProblem input) f))⟩ ∈ xs := by
  obtain ⟨-, -, -, rfl⟩ := analyzeWith_ok_split cs input h
  refine List.mem_append_left _ ?_
  rw [embeddedResults]
  exact List.mem_map.mpr ⟨.verdict name f, mem, rfl⟩

/-- The wrapper request bodies appear after the embedded results, in request
order, all read from the shared projection `projectionOf`. -/
theorem analyzeWith_request_mem (input : InquiryInput) (cs : List Completion)
    {r : RequestSpec} (mem : r ∈ input.requests)
    {xs : List InquiryResult} (h : analyzeWith cs input = .ok xs) :
    ⟨RequestSpec.label r, requestBody (projectionOf input cs) input r⟩ ∈ xs := by
  obtain ⟨-, -, -, rfl⟩ := analyzeWith_ok_split cs input h
  refine List.mem_append_right _ ?_
  rw [requestResults]
  exact List.mem_map.mpr ⟨r, mem, rfl⟩

/-! ## P5 verification laws -/

/-- The wrapper's `verified` case is exactly the Boolean decision of the shared
verifier on the certificate bound to the supplied sources. -/
theorem verifyCertificate_verified_iff (before after : SourceInput)
    (c : Impact.ImpactCertificate) :
    verifyCertificate before after c = .verified ↔
      Impact.verifyImpactBool { c with beforeInput := before, afterInput := after } = true :=
  Impact.verified_iff_verifyImpact_true _

/-- A false claim returns the closed fault of the first failing check. -/
theorem verifyCertificate_invalid (before after : SourceInput) (c : Impact.ImpactCertificate)
    {f : Impact.VerificationFault}
    (h : Impact.firstFault { c with beforeInput := before, afterInput := after } = some f) :
    verifyCertificate before after c = .invalidCertificate f := by
  unfold verifyCertificate
  simp [Impact.verifyImpact, h]

/-- The honest certificate verifies against its own endpoints. -/
theorem verifyCertificate_honest (before after : SourceInput) (queries : List Atom) :
    verifyCertificate before after (Impact.impactCertificate before after queries) = .verified := by
  have hid : ({ Impact.impactCertificate before after queries with
      beforeInput := before, afterInput := after } : Impact.ImpactCertificate)
      = Impact.impactCertificate before after queries := rfl
  unfold verifyCertificate
  rw [hid]
  exact Impact.impactCertificate_verified before after queries

/-! ## Malformed certificates are outer refusals -/

/-- A `verify-impact` request whose certificate payload does not decode is
rejected by the request decoder. -/
theorem decodeRequestRaw_verify_malformed (n : Wire.Names) (label : String)
    (x y z : Lara.Driver.Sx) (h : decodeImpactCertificate z = none) :
    decodeRequestRaw n (.list [.atom (Tag.text .reqVerifyImpact), .atom label, x, y, z]) = none := by
  cases hx : decodeSource x <;> cases hy : decodeSource y <;>
    simp [decodeRequestRaw, Tag.parse_text, h, hx, hy]

/-- A malformed wire certificate therefore makes the whole `inquiry-input`
malformed, and `parseInquiryInput` returns the outer `malformed` refusal. -/
theorem parseInquiryInput_malformed {e : Lara.Driver.Sx}
    (he : decodeInquiryInput e = none)
    {rest : List Lara.Driver.Sx}
    (head : head e = some (.inquiryInput, .atom version :: rest)) :
    parseInquiryInput e = .error (.malformed "malformed inquiry-input") := by
  simp [parseInquiryInput, head, he]

/-! ## Exit-code fixtures -/

theorem exitCode_unsupported (detail : String) :
    exitCodeOf (RunRefusal.unsupported detail) = 1 := rfl

theorem exitCode_limit (counter : LimitCounter) (actual cap : Nat) :
    exitCodeOf (RunRefusal.limit counter actual cap) = 1 := rfl

theorem exitCode_malformed (detail : String) :
    exitCodeOf (RunRefusal.malformed detail) = 2 := rfl

theorem exitCode_syntax (detail : String) :
    exitCodeOf (RunRefusal.syntaxError detail) = 2 := rfl

theorem exitCode_usage (detail : String) :
    exitCodeOf (RunRefusal.usage detail) = 2 := rfl

end Lara.Process.InquiryRun
