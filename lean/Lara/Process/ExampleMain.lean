import Lara.Examples.ProcessFalseLaws
import Lara.Examples.ProcessCore
import Lara.Examples.ProcessEntitlement
import Lara.Examples.ProcessOrder

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
  IO.println "R0 false laws: stricter profile reinstates, quarantine reinstates, equal status with different basis, empty set inconsistent, past vs future, multiset forgets order"

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
  IO.println s!"R1 core: refinement needs nonempty, Kleene incomplete on p ∨ ¬p, coverage incomparable, BHL partial record verdict={reprStr partialVerdict}"

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
  IO.println "R2 entitlement: entitled without a single submitted argument; defeated, conditional, warranted-but-false and entitled-but-not-known separations"

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
  IO.println "R3 order: omitted read unknown, access coverage certain, record order irrelevant, contradictory constraints inconsistent, failed sibling counted, multiset forgets precommitment"

end Order

def run : IO _root_.Unit := do
  FalseLaws.checks
  Core.checks
  Entitlement.checks
  Order.checks
  IO.println "process examples: all research-process checks passed"

end Lara.Process.ExampleRuntime

def main : IO Unit := Lara.Process.ExampleRuntime.run
