import Lara.BHL.CheckedMethods
import Lara.BHL.FiniteModel

namespace Lara.BHL.ExampleRuntime

open Lara.BHL
open Lara.Examples.BHLBinaryModel

namespace E
export Lara.Examples.BHLExecution (report oldReport x y dataId aliasId)
end E

private def expect {α : Type} [DecidableEq α] [Repr α]
    (label : String) (actual expected : α) : IO Unit := do
  if actual = expected then pure ()
  else throw (IO.userError s!"{label}: got {reprStr actual}, expected {reprStr expected}")

private def require (label : String) (actual : Bool) : IO Unit := expect label actual true

private def expectError {ε α : Type} [DecidableEq ε] [Repr ε]
    (label : String) (actual : Except ε α) (expected : ε) : IO Unit := do
  match actual with
  | .error error => expect label error expected
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted")

private def numericChecks : IO Unit := do
  for sample in [false, true] do
    let p := Tests.Binary.pvalue sample
    let expected : ℚ := if sample then 1 / 4 else 1
    expect "inclusive p-value" p expected
    let nullMass := Tests.Binary.null.mass sample
    let alternativeMass := Tests.Binary.alternative.mass sample
    expect "informative null mass" nullMass (if sample then 1 / 4 else 3 / 4)
    expect "informative alternative mass" alternativeMass (if sample then 3 / 4 else 1 / 4)
    IO.println s!"sample={sample}: p={p}, null atom={nullMass}, alternative atom={alternativeMass}"
  for (threshold, expected) in ([(0, 0), (1 / 8, 0), (1 / 4, 1 / 4),
      (1 / 2, 1 / 4), (1, 1), (5 / 4, 1)] : List (ℚ × ℚ)) do
    let mass := FiniteProbability.eventMass Tests.Binary.null
      (fun sample => decide (Tests.Binary.pvalue sample ≤ threshold))
    expect "null calibration event" mass expected
    require "exercised superuniform bound" (decide (mass ≤ threshold))
    IO.println s!"Pr(p≤{threshold})={mass}"
  for first in [false, true] do
    for second in [false, true] do
      let union := Lara.Examples.BHLFiniteBelief.eventMass .disj first second
      let intersection := Lara.Examples.BHLFiniteBelief.eventMass .conj first second
      let p := Tests.Binary.pvalue first
      let q := Tests.Binary.pvalue second
      expect "actual product union" union (p + q - p * q)
      expect "actual product intersection" intersection (p * q)
      require "unclamped union bound" (decide (union ≤ p + q))
      require "intersection bound" (decide (intersection ≤ min p q))
      IO.println s!"pair=({first},{second}): union={union}≤{p + q}, intersection={intersection}≤{min p q}"

private def executionChecks : IO Unit := do
  let aliases := FiniteExecution.Smoke.aliases
  expect "aliases complete" aliases.status .completed
  require "alias updates the actual dataset" (aliases.state.datasets E.aliasId)
  require "full repeated ledger" (decide (aliases.state.ledger =
    ({(true, firstId), (true, firstId)} : History Bool)))
  expect "protected report" (aliases.state.rationals E.oldReport.id) (some (7 / 11 : ℚ))
  IO.println s!"alias/repeated: H card={aliases.state.ledger.card}, shared test count={aliases.state.ledger.count true firstId}, report={reprStr (aliases.state.rationals E.report.id)}"
  let reporting := FiniteExecution.Smoke.report
  expect "p-value assignment complete" reporting.status .completed
  require "p-value-only has no test delta" (decide (reporting.state.ledger = 0))
  expect "p-value-only is calibrated" (reporting.state.rationals E.report.id) (some (1 / 4 : ℚ))
  for (name, outcome) in [("single", FiniteExecution.Smoke.single),
      ("accounted", FiniteExecution.Smoke.accounted), ("hidden", FiniteExecution.Smoke.hidden)] do
    expect s!"{name} completes" outcome.status .completed
    expect s!"{name} report" (outcome.state.rationals E.report.id) (some (1 / 4 : ℚ))
    expect s!"{name} protected" (outcome.state.rationals E.oldReport.id) (some (7 / 11 : ℚ))
    IO.println s!"{name}: H card={outcome.state.ledger.card}, emitted={outcome.commandCodes}"
  let loop := FiniteExecution.Smoke.loop
  expect "terminating loop" loop.status .completed
  expect "loop final x" (loop.state.integers E.x.id) (some 3)
  expect "loop reference step count" loop.events.length 7
  for (name, outcome) in [("left-first", FiniteExecution.Smoke.left),
      ("right-first", FiniteExecution.Smoke.right)] do
    expect s!"{name} completes" outcome.status .completed
    expect s!"{name} x" (outcome.state.integers E.x.id) (some 1)
    expect s!"{name} y" (outcome.state.integers E.y.id) (some 2)
    IO.println s!"parallel {name}: emitted={outcome.commandCodes}"
  let orders := FiniteExecution.Smoke.nestedAll.map FiniteExecution.Outcome.commandCodes
  let permutations := [[110, 111, 0], [110, 0, 111], [111, 110, 0],
    [111, 0, 110], [0, 110, 111], [0, 111, 110]]
  require "all nested-parallel interleavings" (decide (orders.Perm permutations))
  require "all nested outcomes complete" (FiniteExecution.Smoke.nestedAll.all
    (fun outcome => decide (outcome.status = .completed)))
  expect "mixed root-left/child-right choice" FiniteExecution.Smoke.mixed.commandCodes [111, 110, 0]
  IO.println s!"nested parallel: all emitted orders={orders}"
  expect "empty schedule is incomplete" FiniteExecution.Smoke.exhausted.status .incomplete
  expect "bounded loop remains incomplete" (FiniteExecution.Smoke.boundedLoop.map FiniteExecution.Outcome.status) [.incomplete]
  expect "undefined guard" FiniteExecution.Smoke.undefined.status (.failed .undefinedStep)
  expect "non-NI source malformed" FiniteExecution.Smoke.malformed.status (.failed .malformedSource)
  expect "invalid schedule index" (FiniteExecution.scheduledRun [99]
    FiniteExecution.Smoke.nested FiniteExecution.Smoke.initial).status (.failed (.scheduleChoice 99))
  expect "terminal zero fuel" (FiniteExecution.replay [] none FiniteExecution.Smoke.initial).status .completed
  IO.println s!"loop: x={reprStr (loop.state.integers E.x.id)}, steps={loop.events.length}; bounded={reprStr (FiniteExecution.Smoke.boundedLoop.map FiniteExecution.Outcome.status)}; undefined={reprStr FiniteExecution.Smoke.undefined.status}"

private def satisfactionChecks : IO Unit := do
  let run := Lara.Examples.BHLFiniteBelief.RunKind.single firstId
  let quantified := FiniteModel.evalFinite FiniteModel.Examples.rigidDatasetSupport GhostEnv.empty run 0 true true
  let allKnown := FiniteModel.evalFinite FiniteModel.Examples.allDatasetsKnownSupport GhostEnv.empty run 0 true true
  let reflexive := FiniteModel.evalFinite FiniteModel.Examples.allBooleansReflexiveSupport GhostEnv.empty run 0 true true
  expect "rigid existential dataset outside K" quantified true
  expect "not every dataset ghost equals the input" allKnown false
  expect "all Boolean ghosts remain rigid" reflexive true
  expect "lower alternative possible" (FiniteModel.evalFinite FiniteModel.Examples.lowerPossibleSupport GhostEnv.empty run 0 true true) true
  expect "belief true while alternative false" (FiniteModel.evalFinite FiniteModel.Examples.beliefWithoutTruthSupport GhostEnv.empty run 0 true true) true
  expect "accounted union post" (FiniteModel.checkSatisfaction (Γ := []) .postcondition
    (.modal (.belief .disj .lessEqual (1 / 2))) GhostEnv.empty .pair 0 true true) .satisfied
  expect "accounted intersection post" (FiniteModel.checkSatisfaction (Γ := []) .postcondition
    (.modal (.belief .conj .lessEqual (1 / 4))) GhostEnv.empty .pair 0 true true) .satisfied
  expect "hidden single post is false, not incomplete" (FiniteModel.checkSatisfaction (Γ := []) .postcondition
    (.modal (.belief (.single firstId) .equal (1 / 4))) GhostEnv.empty .hidden 0 true true) .falsePostcondition
  expect "false precondition remains distinct" (FiniteModel.checkSatisfaction .precondition
    FiniteModel.Examples.allDatasetsKnownSupport GhostEnv.empty run 0 true true) .failedPrecondition
  expect "out-of-frame hidden parameter" (FiniteModel.checkSatisfaction .postcondition
    FiniteModel.Examples.allBooleansReflexiveSupport GhostEnv.empty run 2 true true) .outsideDeclaredFrame
  IO.println s!"finite ghosts: ∃dataset K equality={quantified}, ∀dataset={allKnown}, ∀Bool reflexivity={reflexive}; accounted posts true, hidden post false, B without truth true"

private theorem truth_not_falsity : ¬ AssertionEntails (context .two) CheckedMethods.truth CheckedMethods.falsity := by
  intro implication
  have admitted := Lara.Examples.BHLBinaryModel.sampled_admitted .two 0 true true (by simp [Lara.Examples.BHLSoundnessScience.allowed])
  have initial : satisfies interpretation (context .two).model GhostEnv.empty (sampledWorld 0 true true) CheckedMethods.truth := by
    refine ⟨admitted, ?_⟩
    simp [CheckedMethods.truth, referenceAssertionSatisfaction, referenceModalSatisfaction, atomMeaning, evalTerm]
  exact CheckedMethods.conditional_false_not_applicable (CheckedMethods.Method.two.request 0 true true)
    (implication GhostEnv.empty _ initial)

private def checkerChecks : IO Unit := do
  let post := CheckedMethods.truth
  require "proof-backed consequence accepted" (checkDerivation (DerivationCheckExamples.reflexiveConsequence (context .two) post)).isAccepted
  require "assignment rule accepted" (checkDerivation (DerivationCheckExamples.assignment (context .two) E.x (.integer 1) post)).isAccepted
  require "sequence rule accepted" (checkDerivation (DerivationCheckExamples.skipSequence (context .two) post)).isAccepted
  require "conditional rule accepted" (checkDerivation (DerivationCheckExamples.skipConditional (context .two) post (.boolean true))).isAccepted
  require "loop rule accepted" (checkDerivation (DerivationCheckExamples.skipLoop (context .two) post (.boolean false))).isAccepted
  require "parallel rule accepted" (checkDerivation (DerivationCheckExamples.skipParallel (context .two) post)).isAccepted
  expectError "missing implication" (checkDerivation (DerivationCheckExamples.missingImplication (context .two) post)) (.missingImplication .initial)
  expectError "missing recursive premise" (checkDerivation (DerivationCheckExamples.missingPremise (context .two) post)) (.missingPremise .seqFirst)
  expectError "refuted universal implication" (checkDerivation (DerivationCheckExamples.invalidImplication (context .two) post CheckedMethods.falsity truth_not_falsity)) (.invalidImplication .initial)
  expectError "skip is not assignment" (checkDerivation (DerivationCheckExamples.invalidAssignment (context .two) post)) .assignmentNotPure
  expectError "test cannot masquerade as assignment" (checkDerivation (DerivationCheckExamples.testViaAssign (context .two) E.report
    Lara.Examples.BHLBelief.hypothesisId (.read E.dataId) firstId Lara.Examples.BHLBelief.populationId post)) .assignmentNotPure
  expectError "recursive invalid premise path" (checkDerivation (DerivationCheckExamples.invalidRecursivePremise (context .two) post)) (.inPremise .seqFirst .assignmentNotPure)
  expectError "invalid parallel side condition" (checkDerivation (DerivationCheckExamples.noninterferingFailure (context .two) E.x (.integer 1) post)) .noninterferingFailure
  IO.println "checker: exact recursive rules accepted; missing/refuted implication, invalid recursive premise, assignment misuse and non-NI rejected"

private def applicationChecks : IO Unit := do
  for method in ([.two, .low, .up, .disjunction, .conjunction] : List CheckedMethods.Method) do
    require "actual scientific test/consequence tree" (checkDerivation method.evidence).isAccepted
    let request := method.request 0 true true
    match CheckedMethods.checkApplication method request with
    | .error error => throw (IO.userError s!"{reprStr method}: {reprStr error}")
    | .ok certificate =>
        expect "bound actual run completes" certificate.computed.status .completed
        expect "bound computed report" (certificate.computed.state.rationals E.report.id) (some (1 / 4 : ℚ))
        IO.println s!"modeled {reprStr method}: emitted={certificate.computed.commandCodes}, H card={certificate.computed.state.ledger.card}, report={reprStr (certificate.computed.state.rationals E.report.id)}"
  let request := CheckedMethods.Method.two.request 0 true true
  expectError "different actual model" (CheckedMethods.checkApplication .two
    { request with binding := { request.binding with model := .dirac } }) .modelMismatch
  expectError "different actual premise" (CheckedMethods.checkApplication .two
    { request with binding := { request.binding with pre := .falsity } }) .premiseMismatch
  expectError "different actual program" (CheckedMethods.checkApplication .two
    { request with binding := { request.binding with program := .skip } }) .programMismatch
  expectError "different actual postcondition" (CheckedMethods.checkApplication .two
    { request with binding := { request.binding with post := .falsity } }) .postconditionMismatch
  expectError "different initial run world" (CheckedMethods.checkApplication .two
    { request with before := .hidden }) .runMismatch
  expectError "different final run world" (CheckedMethods.checkApplication .two
    { request with after := .hidden }) .runMismatch
  let conditional := CheckedMethods.Method.conditionalFalse
  require "conditional theorem remains available" (checkDerivation conditional.evidence).isAccepted
  expectError "false P cannot become modeled application" (CheckedMethods.checkApplication conditional
    (conditional.request 0 true true)) .failedPrecondition
  expectError "unadmitted parameter cannot become application" (CheckedMethods.checkApplication .two
    (CheckedMethods.Method.two.request 2 true true)) .failedPrecondition
  IO.println "exact model/P/C/Q/run mismatches rejected; conditional validity with false P retained, modeled application rejected"

def run : IO Unit := do
  numericChecks
  executionChecks
  satisfactionChecks
  checkerChecks
  applicationChecks
  IO.println "BHL examples: all computed checker, semantic, execution and application checks passed"

end Lara.BHL.ExampleRuntime

def main : IO Unit := Lara.BHL.ExampleRuntime.run
