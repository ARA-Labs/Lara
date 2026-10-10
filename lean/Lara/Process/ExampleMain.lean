import Lara.Examples.ProcessFalseLaws
import Lara.Examples.ProcessCore
import Lara.Examples.ProcessEntitlement
import Lara.Examples.ProcessOrder
import Lara.Examples.ProcessStatistics
import Lara.Examples.ProcessRevision
import Lara.Examples.ProcessARA
import Lara.Examples.ProcessAdequacy
import Lara.Examples.ProcessInquiry

/-!
The `process-examples` runner: computes every research-process fixture through
the shared executable definitions and fails on the first disagreement. The
proofs carry soundness; this runner is the executable smoke check that the
definitions the theorems are about actually compute the stated values.
-/

namespace Lara.Process.ExampleRuntime

open Lara.Process

private def expect {α : Type} [DecidableEq α] [Repr α]
    (label : String) (actual expected : α) : IO _root_.Unit := do
  if actual = expected then pure ()
  else throw (IO.userError s!"{label}: got {reprStr actual}, expected {reprStr expected}")

private def require (label : String) (actual : Bool) : IO _root_.Unit := expect label actual true

/-- The fields of a profile, read from the profile itself. -/
def profileLines (P : Profile Empty) : List String :=
  let scope : CoverageScope := ⟨[], none, none, none, 0⟩
  let samples : List (RecordCoverage Empty) := [.complete scope, .countBounded scope 0, .openWorld scope]
  let accepts := (samples.filter P.acceptsCoverage).map (·.label Empty.elim)
  [s!"admissible evidence: {(EvidenceKind.all.filter (· ∈ P.admissible)).map EvidenceKind.label}",
   s!"accepted coverage kinds: {accepts}",
   s!"guarantee: {P.guarantee.1.label} at {P.guarantee.2}",
   s!"required probes: {(ErrorKind.all.filter (· ∈ P.requiredProbes)).map ErrorKind.label}",
   s!"acceptance: {P.acceptance.label}"]

/-- Report one contract fixture: its verdict or computed value and everything it
depends on. -/
def fixture (label value model query assumptions : String) (profile : List String)
    (claim sources : String) : IO _root_.Unit := do
  IO.println s!"  {label}: {value}"
  IO.println s!"    model: {model}"
  IO.println s!"    query: {query}"
  IO.println s!"    assumptions: {assumptions}"
  match profile with
  | [] => IO.println "    profile: none (not an entitlement query)"
  | lines => do
      IO.println "    profile:"
      for line in lines do IO.println s!"      {line}"
  IO.println s!"    claim and witness: {claim}"
  IO.println s!"    sources: {sources}"

private def handModeled : String := "hand-modeled finite fixture, no ARA source"

namespace FalseLaws
open Lara.Examples.ProcessFalseLaws
open Lara.Grounded

def checks : IO _root_.Unit := do
  expect "lax profile defeats the claim" (statusC (underKinds kindedAF laxKinds) claim) .defeated
  expect "strict profile reinstates the claim" (statusC (underKinds kindedAF strictKinds) claim) .justified
  expect "quarantine baseline defeats the claim" (statusC kindedAF claim) .defeated
  expect "justified before the defender swap" (statusC beforeAF claim) .justified
  expect "justified after the defender swap" (statusC afterAF claim) .justified
  expect "quarantine reinstates the claim" (statusC (quarantine kindedAF [7]) claim) .justified
  expect "old defender basis survives removal of 2" (statusC (removeArg beforeAF 2) claim) .justified
  expect "new defender basis falls without 2" (statusC (removeArg afterAF 2) claim) .defeated
  expect "empty compatible set" (verdict noCompat (fun x => x = true)) .inconsistent
  expect "past completions certify" (verdict pastCompat (fun x => warranted x.history)) .certainTrue
  require "future retraction defeats" (!decide (warranted Candidate.later.history))
  require "commit-first order" (decide (commitPrecedesRead committedFirst))
  require "read-first order" (!decide (commitPrecedesRead readFirst))
  IO.println "False laws: stricter profile reinstates, quarantine reinstates, equal status with different basis, empty set inconsistent, past vs future, multiset forgets order"

end FalseLaws

namespace Core
open Lara.Examples.ProcessCore

def checks : IO _root_.Unit := do
  expect "coarse record certain" (verdict (fun _ : Bool => True) (fun _ => True)) .certainTrue
  expect "empty refinement inconsistent" (verdict (fun _ : Bool => False) (fun _ => True)) .inconsistent
  expect "Kleene gives up on p ∨ ¬p"
    (kleeneVerdictFinite (fun _ : Bool => True) (finiteAtoms (fun _ => True) pVal) excludedMiddle) .unknown
  expect "supervaluation certifies p ∨ ¬p"
    (verdict (fun _ : Bool => True) (excludedMiddle.holds pVal)) .certainTrue
  require "complete coverage allows full reporting" (decide (completeRuns.Allowed .bothReported ()))
  require "complete coverage forbids omission" (!decide (completeRuns.Allowed .oneOmitted ()))
  require "count bound forbids two runs" (!decide (atMostOneRun.Allowed .bothReported ()))
  require "count bound allows the omission" (decide (atMostOneRun.Allowed .oneOmitted ()))
  expect "stronger assumptions empty the set"
    (verdict (Compatible silentModel bothCoverages ()) (fun _ => True)) .inconsistent
  -- The process model of `partialRecord_unknown`, with the finite evaluator that
  -- `BHLPartialRecord.checkConclusion_correct` ties to `conclusionHolds`.
  let partialVerdict := verdict (Compatible partialModel Assumptions.trivial
    Lara.Examples.BHLPartialRecord.record)
    (fun x => Lara.Examples.BHLPartialRecord.checkConclusion x.1 = true)
  expect "BHL partial record leaves the conclusion unknown" partialVerdict .unknown
  IO.println s!"Compatible-history core: refinement needs nonempty, Kleene incomplete on p ∨ ¬p, coverage incomparable, BHL partial record verdict={partialVerdict.label}"

end Core

namespace Entitlement
open Lara.Examples.ProcessEntitlement

def checks : IO _root_.Unit := do
  require "claim entitled" (decide (Entitled model strict reporting admitted () claimC))
  for w in [Wit.w1, Wit.w2] do
    require s!"{reprStr w} not argument-entitled"
      (!decide (ArgumentEntitled model strict reporting admitted () claimC w))
  require "w1 warrants in left" (decide (Warranted model strict .left claimC .w1))
  require "w2 warrants in right" (decide (Warranted model strict .right claimC .w2))
  require "defeated w2 not warranted in left" (!decide (Warranted model strict .left claimC .w2))
  require "conditional w3 not strictly warranted" (!decide (Warranted model strict .left claimC .w3))
  require "conditional w3 warranted by the lax profile" (decide (Warranted model lax .left claimC .w3))
  require "warranted claim false in right" (!decide (model.truth .right claimC))
  require "entitled claim not known at left" (!decide (Known model sameReport .left claimC))
  require "promoting rule is not well-kinded"
    (!decide (KindDerivation.unary .observed (.leaf .hypothetical)).WellKinded)
  IO.println "Entitlement: entitled without a single submitted argument; defeated, conditional, warranted-but-false and entitled-but-not-known separations"

end Entitlement

namespace Order
open Lara.Examples.ProcessOrder

def checks : IO _root_.Unit := do
  expect "stated order alone leaves an earlier read possible" (verdict openCompat precommitted) .unknown
  expect "complete access coverage certifies precommitment" (verdict coveredCompat precommitted) .certainTrue
  expect "unordered record" (verdict (unorderedCompat unordered) precommitted) .unknown
  expect "shuffled record listing" (verdict (unorderedCompat unorderedShuffled) precommitted) .unknown
  expect "contradictory constraints"
    (verdict (fun x : Candidate => OrderCompatible contradictory x.trace) precommitted) .inconsistent
  expect "family count with a failed sibling" (familyCount withSibling family) 2
  expect "family count without it" (familyCount withoutSibling family) 1
  require "failed sibling yields no argument"
    (decide (successfulRuns withSibling = successfulRuns withoutSibling))
  require "stale input version invalid" (!decide (ValidHistory [commit, update, read, run]))
  require "cutoff excludes the longer history"
    (!decide (OrderCompatible { ordered with cutoff := 3 } Candidate.earlierRead.trace))
  expect "refusing evaluator keeps inconsistency"
    (refuse (verdict (fun x : Candidate => OrderCompatible contradictory x.trace) precommitted))
    .inconsistent
  require "commit-first precommitted" (decide (RunPrecommitted Candidate.committedFirst.trace run0))
  require "read-first not precommitted" (!decide (RunPrecommitted Candidate.readFirst.trace run0))
  require "split selection" (decide (SplitSelection [selectRead, commit, read, run] [selectData] [testData]))
  require "same-data selection is not split"
    (!decide (SplitSelection [selectOnTest, commit, read, run] [selectData] [testData]))
  IO.println "Order: omitted read unknown, access coverage certain, record order irrelevant, contradictory constraints inconsistent, failed sibling counted, multiset forgets precommitment"

end Order

namespace Stats
open Lara.Examples.ProcessStatistics
open Lara.BHL.FiniteProbability
open Lara.Process.Statistics (stoppedHitProb onlineLevel fdp eBH warrantedLevel)

def checks : IO _root_.Unit := do
  expect "e-value null expectation" (Statistics.expect evLaw evalue) 1
  expect "count bound two certifies" (verdict (boundedCompat 2) warrantsRejection) .certainTrue
  expect "count bound four leaves a failing completion"
    (verdict (boundedCompat 4) warrantsRejection) .unknown
  expect "fixed-time p-value" (stoppedHitProb coin crossed (fun _ => false) 2 []) (1 / 2)
  expect "optional stopping" (stoppedHitProb coin crossed crossed 2 []) (3 / 4)
  let ville := stoppedHitProb coin (fun p => decide (1 / (1 / 4 : ℚ) ≤ likelihoodRatio p))
    (fun p => decide (1 / (1 / 4 : ℚ) ≤ likelihoodRatio p)) 4 []
  expect "likelihood-ratio crossing probability" ville (1 / 16)
  expect "same-data selection" (eventMass (product fair fair) (fun ω => analysis (!ω.1) ω)) (3 / 4)
  expect "dependent split" (eventMass correlated (fun ω => matchTest ω.1 ω.2)) 1
  expect "replay with the non-rejection" (onlineLevel (1 / 20) (1 / 20) [false]) (1 / 80)
  expect "replay without it" (onlineLevel (1 / 20) (1 / 20) []) (1 / 40)
  expect "FDR of the mFDR fixture"
    (fdr fair (fun ω => if ω then 1 else 0) (fun ω => if ω then 1 else 9)) (1 / 2)
  expect "alpha-investing mFDR" investMfdr (183 / 2033)
  expect "alpha-investing FDR" investFdr (2663 / 24000)
  require "alpha-investing levels respect the wealth rule"
    ([true, false].all fun a => [true, false].all fun b =>
      [(0 : Fin 3), 1, 2].all fun c => (investAt (a, b, c)).lawful)
  expect "e-BH at the reported count"
    (Statistics.expect (product fair fair) (fun ω => fdp (eBH 1 (1 / 2) fun i => pair i ω) {0})) (3 / 4)
  expect "e-BH at the bound"
    (Statistics.expect (product fair fair) (fun ω => fdp (eBH 2 (1 / 2) fun i => pair i ω) {0})) 0
  expect "warranted level" (warrantedLevel ⟨some .eValue, some 60, some 2, some .fwer⟩)
    ((1 / 30 : ℚ) : WithTop ℚ)
  expect "zero bound fails closed for a p-value"
    (warrantedLevel ⟨some .pValue, some (1 / 40), some 0, some .fwer⟩) ⊤
  expect "missing bound fails closed" (warrantedLevel ⟨some .eValue, some 60, none, some .fwer⟩) ⊤
  IO.println s!"Statistics: Ville crossing {ville} ≤ 1/4; e-value 60 certain under bound 2 and unknown under bound 4; optional stopping 3/4, same-data selection 3/4, dependent split 1, replay 1/40 > 1/80, FDR 1/2 under mFDR, alpha-investing FDR 2663/24000 > 1/10 with mFDR 183/2033, e-BH at reported count 3/4"

end Stats

namespace Revision
open Lara.Examples.ProcessRevision
open Lara.Grounded

def checks : IO _root_.Unit := do
  expect "claim defeated although its support avoids the quarantine" (labelC attacked 0) .out
  require "stable credulous before the unrelated edit" (decide (StableCredulous single 0))
  require "no stable extension after the unrelated edit" (!decide (StableCredulous withSelfAttack 0))
  expect "grounded label unchanged by the unrelated edit" (labelC withSelfAttack 0) (labelC single 0)
  require "warrant without the failed sibling" (decide (bonferroniWarrant Lara.Examples.ProcessOrder.withoutSibling))
  require "no warrant with it" (!decide (bonferroniWarrant Lara.Examples.ProcessOrder.withSibling))
  expect "corroboration before merging" (corroboration twoSources .a) 2
  expect "corroboration after merging" (corroboration (renameSupplies (fun _ : Nat => (0 : Nat)) twoSources) .a) 1
  require "stale reuse" (check (fun k => k == 0) != check (fun _ => true))
  require "new version keeps the old warrant" (decide (VersionWarranted [newV, oldV] [oldV] []))
  require "defect withdraws it" (!decide (VersionWarranted [newV, oldV] [oldV] [oldV]))
  IO.println "Revision: support-only quarantine, attacked support defeated, stable not directional, failed sibling flips warrant, merge halves corroboration, incomplete reads stale, update keeps and revision withdraws"

end Revision

namespace Ara
open Lara.Examples.ProcessARA
open Lara.Examples.ProcessOrder (Candidate precommitted siblingRun failure noPolicy)

/-- Report a decoded-record verdict with everything it depends on: model,
query, coverage scope and admitted assumptions, profile, submitted claims and
witnesses, and the ARA source reference of every decoded fact. -/
def report (label : String) (src : AraSource Empty) (v : Verdict) : IO _root_.Unit := do
  let d := extract admits src
  let cite (r : SourceRef) : String :=
    let span := match r.span with
      | some (a, b) => s!":{a}-{b}"
      | none => ""
    s!"{r.file}#{r.entry}{span}"
  let bases := [AdmissionBasis.instrumentedLog, .signedAttestation, .authorDeclaration]
  let attestations := src.entries.filterMap AraEntry.coverage?
  IO.println s!"  {label}: {v.label}"
  IO.println s!"    model: ProcessOrder.Candidate, 3 complete histories, cutoff {d.cutoff}"
  IO.println "    query: RunPrecommitted run0 (an order query; no profile applies)"
  IO.println s!"    admitted bases: {(bases.filter admits).map AdmissionBasis.label}"
  IO.println s!"    admitted coverage: {d.coverage.map fun c => s!"{c.coverage.label Empty.elim} from {cite c.evidence}"}"
  IO.println s!"    unadmitted attestations: {(attestations.filter fun c => !admits c.basis).map fun c => s!"{cite c.evidence} ({c.basis.label})"}"
  IO.println s!"    submitted: {d.submitted.map fun (c, w) => s!"claim {c.index} by witness {w.index}"}"
  IO.println s!"    events: {d.events.map fun e => cite e.source}"
  IO.println s!"    ordering: {d.order.map fun o => cite o.source}"

def checks : IO _root_.Unit := do
  let omitted := verdict (decodedCompat withoutCoverage) precommitted
  let logged := verdict (decodedCompat withLogCoverage) precommitted
  let declared := verdict (decodedCompat withDeclaredCoverage) precommitted
  let contradictory := verdict (decodedCompat contradictorySource) precommitted
  expect "ordering evidence alone" omitted .unknown
  expect "admitted access coverage" logged .certainTrue
  expect "author declaration not admitted" declared .unknown
  expect "contradictory ordering entries" contradictory .inconsistent
  require "generating history compatible"
    (decide ((extract admits withLogCoverage).Compatible noPolicy Candidate.committedFirst.trace))
  require "failed trial preserved"
    (decide (siblingRun ∈ (extract admits withSiblingSource).toOrderRecord.events))
  expect "reordered source, same verdict"
    (verdict (fun x : Candidate => (extract admits reorderedSource).Compatible noPolicy x.trace) precommitted)
    logged
  IO.println "ARA bridge:"
  report "ordering evidence only" withoutCoverage omitted
  report "instrumented-log access coverage" withLogCoverage logged
  report "author-declared access coverage" withDeclaredCoverage declared
  report "contradictory ordering" contradictorySource contradictory

end Ara

namespace Adequacy
open Lara.Examples.ProcessAdequacy
open Lara.Examples.ProcessOrder

def checks : IO _root_.Unit := do
  require "dropping failed analyses collapses the pair" (decide (dropFailed withoutSibling = dropFailed withSibling))
  require "dropping selection provenance collapses the pair"
    (decide (dropSelectionProvenance [selectRead, commit, read, run] =
      dropSelectionProvenance [selectOnTest, commit, read, run]))
  require "collapsing sources collapses the pair"
    (decide (renameSupplies (fun _ : Nat => (0 : Nat)) Lara.Examples.ProcessRevision.twoSources =
      renameSupplies (fun _ : Nat => (0 : Nat)) ({(1, .a)} : Finset (Nat × Lara.Examples.ProcessRevision.Atom))))
  require "dropping retractions collapses the pair"
    (decide (dropRetractions Lara.Examples.ProcessFalseLaws.asserted =
      dropRetractions Lara.Examples.ProcessFalseLaws.retracted))
  require "the multiset collapses the pair"
    (decide ((Candidate.committedFirst.trace : Multiset Stamped) = Candidate.readFirst.trace))
  require "the pairs disagree on their warrants"
    (decide (Lara.Examples.ProcessRevision.bonferroniWarrant withoutSibling) &&
      !decide (Lara.Examples.ProcessRevision.bonferroniWarrant withSibling) &&
      decide (SplitSelection [selectRead, commit, read, run] [selectData] [testData]) &&
      !decide (SplitSelection [selectOnTest, commit, read, run] [selectData] [testData]) &&
      decide (corroborated Lara.Examples.ProcessRevision.twoSources) &&
      !decide (corroborated {(1, .a)}) &&
      decide (Lara.Examples.ProcessFalseLaws.warranted Lara.Examples.ProcessFalseLaws.asserted) &&
      !decide (Lara.Examples.ProcessFalseLaws.warranted Lara.Examples.ProcessFalseLaws.retracted) &&
      decide (RunPrecommitted Candidate.committedFirst.trace run0) &&
      !decide (RunPrecommitted Candidate.readFirst.trace run0))
  IO.println "Adequacy: multiset, failed-analysis, selection-provenance, source-identity and retraction pairs computed here; the latest-test and PROV separations are proved in Lean (latestTest_separates, prov_separates)"

end Adequacy

namespace Inquiry
open Lara.Examples.ProcessInquiry
open Lara.Examples.ProcessEntitlement

/-- Report the entitlement verdict of the contract's different-witness fixture,
reading the profile and coverage from the fixture's values. -/
def entitlementReport : IO _root_.Unit := do
  let entitled := decide (Entitled model strict reporting admitted () claimC)
  let audits := [(Wit.w1, "w1"), (Wit.w2, "w2"), (Wit.w3, "w3")].map fun (w, name) =>
    s!"{name}={decide (ArgumentEntitled model strict reporting admitted () claimC w)}"
  let coverage := s!"{admitted.coverage.label Empty.elim} coverage, cutoff {admitted.coverage.scope.cutoff}"
  fixture "claim supported by a different witness in each history"
    s!"Entitled={entitled}, ArgumentEntitled {audits}"
    "ProcessEntitlement.Hist, 2 complete histories reporting the same record"
    s!"Entitled and ArgumentEntitled of claim {claimC.index}"
    s!"{coverage}; accepted by the profile: {strict.acceptsCoverage admitted.coverage}"
    (profileLines strict) s!"claim {claimC.index}; witnesses w1, w2, w3" handModeled

def checks : IO _root_.Unit := do
  require "w1 audit unstable over both histories"
    (!decide (both.Stable (fun h => Warranted model strict h claimC .w1)))
  require "right flips the w1 audit"
    (decide (both.sensitivity (fun h => Warranted model strict h claimC .w1) .left = {.right}))
  require "stable truth" (decide (leftOnly.Stable (fun x => model.truth x.1 unargued)))
  require "stable claim not entitled" (!decide (Entitled model strict exact admitted .left unargued))
  expect "status justified at left" (claimStatus .left) .justified
  expect "status justified at right" (claimStatus .right) .justified
  require "w1 audit on the left record" (decide (ArgumentEntitled model strict exact admitted .left claimC .w1))
  require "no w1 audit on the right record" (!decide (ArgumentEntitled model strict exact admitted .right claimC .w1))
  IO.println "Inquiry: sensitivity, stable-but-not-entitled, equal status without transported entitlement"

end Inquiry

namespace Contract
open Lara.Examples.ProcessStatistics (boundedCompat warrantsRejection correlated matchTest ledgerBoundTwo)
open Lara.Examples.ProcessOrder (withSibling withoutSibling family)
open Lara.Examples.ProcessRevision (bonferroniWarrant newV oldV)
open Lara.Examples.ProcessFalseLaws (pastCompat warranted)

def checks : IO _root_.Unit := do
  IO.println "ARA-contract fixtures:"
  let partialBound := verdict (Compatible Lara.Examples.ProcessCore.partialModel ledgerBoundTwo
    Lara.Examples.BHLPartialRecord.record)
    (fun x => Lara.Examples.BHLPartialRecord.checkConclusion x.1 = true)
  expect "BHL conclusion under a count bound of two" partialBound .unknown
  fixture "one-test and two-test BHL histories" partialBound.label
    "BHLPartialRecord: the single and hidden-earlier complete binary runs"
    "the 1/4 single-test statistical belief (checkConclusion, equal to its satisfaction)"
    "latest-test report; complete ledger has at most two tests" [] "no submitted argument"
    handModeled
  let bound2 := verdict (boundedCompat 2) warrantsRejection
  let bound4 := verdict (boundedCompat 4) warrantsRejection
  expect "count bound two" bound2 .certainTrue
  expect "count bound four" bound4 .unknown
  fixture "calibrated e-value 60, count bound two" bound2.label
    "4 completions with 1 to 4 family runs, one run reported"
    "e-Bonferroni rejection at the admitted bound 2 (threshold 2/α = 40)"
    "count bound 2 on the family; e-value null mass 1/60; α = 1/20" [] "the reported run" handModeled
  fixture "calibrated e-value 60, count bound four" bound4.label
    "4 completions with 1 to 4 family runs, one run reported"
    "e-Bonferroni rejection at bound 2; the four-test threshold 4/α = 80 exceeds 60"
    "count bound 4 on the family" [] "the reported run" handModeled
  Inquiry.entitlementReport
  let dependent := Lara.BHL.FiniteProbability.eventMass correlated fun ω => matchTest ω.1 ω.2
  expect "dependent samples" dependent 1
  fixture "distinct dataset identities with dependent samples" s!"selected test level {dependent} > 1/2"
    "selection sample and test sample, fair marginals, perfectly dependent"
    "probability the selected calibrated test rejects"
    "structural split selection holds; the product-law premise fails" [] "none" handModeled
  let countWith := familyCount withSibling family
  let countWithout := familyCount withoutSibling family
  let warrantWith := decide (bonferroniWarrant withSibling)
  let warrantWithout := decide (bonferroniWarrant withoutSibling)
  expect "failed sibling" (countWith, countWithout, warrantWith, warrantWithout) (2, 1, false, true)
  fixture "failed sibling trial with no attack"
    s!"family count {countWith} (without it {countWithout}); e-Bonferroni warrant {warrantWith} (without it {warrantWithout})"
    "two valid process histories with the same successful runs"
    "family count and the e-Bonferroni warrant of a reported e-value 30 at α = 1/20"
    "complete histories" [] "none" handModeled
  let past := verdict pastCompat fun x => warranted x.history
  let after := decide (warranted Lara.Examples.ProcessFalseLaws.Candidate.later.history)
  expect "retraction" (past, after) (.certainTrue, false)
  fixture "later retraction" s!"past completions {past.label}; after retraction warranted={after}"
    "the asserted history and its continuation with a retraction"
    "the claim's source is unretracted" "past completions only; the retraction is a future continuation"
    [] "claim 0 by witness 0" handModeled
  let keeps := decide (VersionWarranted [newV, oldV] [oldV] [])
  let withdrawn := !decide (VersionWarranted [newV, oldV] [oldV] [oldV])
  expect "version change and defect" (keeps, withdrawn) (true, true)
  fixture "dataset version change and defect"
    s!"new version keeps the old warrant: {keeps}; defect withdraws it: {withdrawn}"
    "a warrant reading dataset 1 at version 0" "VersionWarranted"
    "published versions 0 and 1" [] "none" handModeled

end Contract

def run : IO _root_.Unit := do
  FalseLaws.checks
  Core.checks
  Entitlement.checks
  Order.checks
  Stats.checks
  Revision.checks
  Ara.checks
  Adequacy.checks
  Inquiry.checks
  Contract.checks
  IO.println "process examples: all research-process checks passed"

end Lara.Process.ExampleRuntime

def main : IO Unit := Lara.Process.ExampleRuntime.run
