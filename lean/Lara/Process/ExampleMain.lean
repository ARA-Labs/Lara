import Lara.Examples.ProcessFalseLaws

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

def run : IO _root_.Unit := do
  FalseLaws.checks
  IO.println "process examples: all research-process checks passed"

end Lara.Process.ExampleRuntime

def main : IO Unit := Lara.Process.ExampleRuntime.run
