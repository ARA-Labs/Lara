/-
The `inquiry-examples` runner: recomputes a small built-in suite through the
shared reference semantics and the bounded runner, and fails on the first
disagreement. No IO happens at library load; `main` is the only effectful entry.

The suite checks, on one embedded `process-input 1` document and a couple of
wrapper requests:

* the bounded runner and the reference semantics render the same canonical
  results (the P2/P3 equality, re-executed rather than merely trusted);
* the emitted result count equals the embedded query count plus the request
  count, and the embedded verdict rows carry P0's distinct unguarded count;
* a document whose declared source-byte bound is below the actual count refuses
  the whole document with `limit source-bytes`, and the exit code is 1;
* a `verify-impact` request carrying a certificate whose read log is empty is
  refused with the closed `false-read-evidence` fault.
-/
import Lara.Process.InquiryRun
import Lara.Examples.ProcessSource

namespace Lara.Process.InquiryExampleMain

open Lara.Process
open Lara.Process.InquiryRun
open Lara.Process.InquiryWire

/-- The landed `empty-universe` `process-input 1` fixture, embedded verbatim. -/
def processText : String := r#";; process-input 1 fixture
(process-input 1
  (names (event commit read run early-read) (actor alice) (plan plan) (run run0) (claim c0) (source) (data test) (family fam) (witness w0))
  (record (cutoff 10)
    (event commit (commit-plan alice plan 0) (at "experiments/plan.md" commit-v0))
    (event read (access alice test evaluation) (at "logs/access.md" read-test 12 18))
    (event run (run run0 plan 0 (inputs (input test 0)) fam) (at "experiments/run0.md" run0))
    (order commit read (at "logs/access.md" after-commit 20 21))
    (submit c0 w0))
  (reader instrumented-log signed-attestation)
  (universe)
  (limits (events 8) (completions 1000))
  (queries (verdict precommitted (run-precommitted run0)) (verdict predictable (predictable))))
"#

/-- A production-runnable source built from the shared example surface, exactly
as the landed P1 examples do. -/
def baseSource : Source.SourceInput :=
  let surface := Lara.Examples.ProcessSource.ordinaryInput
  { surface
    replay :=
      { core := ⟨Lara.Driver.coreVersionText⟩
        policy := surface.policy.id
        backends := surface.program.backends.map fun pair => ⟨pair.1, ⟨pair.2⟩⟩
        theories := surface.policy.theories.map Prod.fst
        artifact := surface.program.digest }
    capture := none }

/-- A certificate whose read log is empty: every other field is the honest
recomputed value, so the verifier reports exactly `false-read-evidence`. -/
def stubCertificate : ImpactCertificateWire :=
  wireOfCertificateList [] (Impact.impactCertificate baseSource baseSource [])

/-- The built-in suite's document. -/
def builtinDocument : Except String InquiryInput := do
  let process ← match Wire.parse processText with
    | .ok d => pure d
    | .error e => throw s!"embedded process document failed: {e.detail}"
  pure
    { process := process
      base := baseSource
      slots := []
      claims := []
      witnesses := []
      kinds := []
      assumptions := []
      catalog := []
      limits :=
        { histories := 1000, sources := 1000, sourceBytes := 1000000, declarations := 1000,
          searchSteps := 100000, pairs := 1000, subsets := 1000 }
      requests :=
        [ RequestSpec.impact "impact" baseSource baseSource []
        , RequestSpec.stable "stable" (.status ⟨0⟩)
        , RequestSpec.verifyImpact "verify" baseSource baseSource stubCertificate ] }

/-- Render one result envelope as its canonical output lines. -/
def renderResult (input : InquiryInput) (result : Except RunRefusal (List InquiryResult)) :
    Except String (List String) :=
  match result with
  | .error refusal => .error (Lara.Driver.printSx (encodeInquiryError ⟨none, refusal⟩))
  | .ok results =>
      .ok (results.map fun r => Lara.Driver.printSx (encodeInquiryResult input.process.names r))

private def expect {α : Type} [BEq α] [Repr α] (label : String) (actual expected : α) :
    IO _root_.Unit := do
  if actual == expected then pure ()
  else throw (IO.userError s!"{label}: got {repr actual}, expected {repr expected}")

private def require (label : String) (actual : Bool) : IO _root_.Unit :=
  expect label actual true

/-- Every computed fact the suite asserts. -/
def checks (doc : InquiryInput) : IO _root_.Unit := do
  let bounded := runBounded doc (actualOf doc .sourceBytes)
  let referenceResults := reference doc
  expect "bounded equals reference" (renderResult doc bounded) (renderResult doc referenceResults)
  require "bounded is a result" bounded.isOk
  expect "exit code on success"
    (match bounded with | .ok _ => (0 : UInt32) | .error r => exitCodeOf r) (0 : UInt32)
  expect "emitted count"
    ((embeddedVerdicts doc.process).length + doc.requests.length)
    (match bounded with | .ok results => results.length | .error _ => 0)
  -- Over the declared source-byte budget: the whole document is refused.
  let overBudget := { doc with limits := { doc.limits with sourceBytes := 0 } }
  let expectedRefusal : RunRefusal :=
    .limit .sourceBytes (actualOf overBudget .sourceBytes) (min 0 maxInquirySourceBytes)
  expect "over budget refuses"
    (renderResult overBudget (runBounded overBudget (actualOf overBudget .sourceBytes)))
    (.error (Lara.Driver.printSx (encodeInquiryError ⟨none, expectedRefusal⟩)))
  expect "limit exit code" (exitCodeOf expectedRefusal) 1
  -- The empty-read certificate is refused with the closed fault.
  require "stub certificate faults"
    (match bounded with
     | .ok results => results.any fun r =>
         match r.body with
         | .verification (.invalidCertificate .falseReadEvidence) => true
         | _ => false
     | .error _ => false)
  IO.println s!"inquiry examples: bounded equals reference, {doc.requests.length} requests, \
embedded count {(embeddedVerdicts doc.process).length}"

def main (_args : List String) : IO UInt32 := do
  match builtinDocument with
  | .error message => do
      IO.eprintln s!"inquiry examples: {message}"
      pure 1
  | .ok doc => do
      try
        checks doc
        pure 0
      catch e => do
        IO.eprintln s!"inquiry examples failed: {e.toString}"
        pure 1

end Lara.Process.InquiryExampleMain

def main (args : List String) : IO UInt32 := Lara.Process.InquiryExampleMain.main args
