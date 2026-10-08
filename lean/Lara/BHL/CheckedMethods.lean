import Lara.BHL.Check
import Lara.BHL.FiniteExecution
import Lara.Examples.BHLStatistical

/-!
Checked scientific methods for the fixed binary interpretation. Closed binding
codes decode to actual contexts and canonical P/C/Q, not caller approval tags.
A conditional certificate is separate from an application: the latter checks
all bindings, proves the initial assertion and retains the actual computed run.
Physical sampling and external capture adequacy are not supplied by either.
-/

namespace Lara.BHL.CheckedMethods

open Lara.BHL
open Lara.Examples.BHLBinaryModel
open Lara.Examples.BHLBinaryScience
open Lara.Examples.BHLSoundnessScience
  (Prior allowed ψ lower upper alternative singleTest pairId secondReport)
open Lara.Examples.BHLBelief (hypothesisId populationId)

namespace E
export Lara.Examples.BHLExecution
  (Snapshot Source Command report oldReport dataId aliasId Reifies eventWorld eventsWorld)
end E

inductive ModelRef where
  | binary (prior : Prior)
  | dirac
  deriving DecidableEq

inductive PreRef where
  | single (prior : Prior)
  | multiple
  | falsity
  deriving DecidableEq

inductive ProgramRef where
  | single (name : TestId)
  | second
  | skip
  deriving DecidableEq

inductive PostRef where
  | single (prior : Prior) (name : TestId)
  | disjunction
  | conjunction
  | falsity
  deriving DecidableEq

structure Binding where
  model : ModelRef
  pre : PreRef
  program : ProgramRef
  post : PostRef
  deriving DecidableEq

inductive Method where
  | two | low | up | disjunction | conjunction | conditionalFalse
  deriving DecidableEq, Repr

def falsity : Assertion [] := .modal (.atom (.equal (.boolean true) (.boolean false)))
def truth : Assertion [] := .modal (.atom (.equal (.boolean true) (.boolean true)))

def selectedAlternative : Prior → ModalFormula []
  | .two => lower.disj upper
  | .low => lower
  | .up => upper

noncomputable def ModelRef.context : ModelRef → ProgramContext Bool
  | .binary prior => Lara.Examples.BHLBinaryModel.context prior
  | .dirac => Lara.Examples.BHLExecution.context

def PreRef.assertion : PreRef → Assertion []
  | .single prior => singlePre (ψ prior)
  | .multiple => multiPre (ψ .two) E.report firstTest alternative
  | .falsity => Lara.BHL.CheckedMethods.falsity

def ProgramRef.source : ProgramRef → E.Source
  | .single name => Lara.Examples.BHLBinaryRuns.singleSource name
  | .second => .command (.test secondReport E.aliasId secondId)
  | .skip => .command .skip

def ProgramRef.program (reference : ProgramRef) : Program := reference.source.quote

def PostRef.assertion : PostRef → Assertion []
  | .single prior name => singlePost (ψ prior) E.report (singleTest name) (selectedAlternative prior)
  | .disjunction => multiDisjPost (ψ .two) E.report secondReport firstTest secondTest pairId alternative alternative
  | .conjunction => multiConjPost (ψ .two) E.report secondReport firstTest secondTest pairId alternative alternative
  | .falsity => Lara.BHL.CheckedMethods.falsity

def Method.binding : Method → Binding
  | .two => ⟨.binary .two, .single .two, .single firstId, .single .two firstId⟩
  | .low => ⟨.binary .low, .single .low, .single lowId, .single .low lowId⟩
  | .up => ⟨.binary .up, .single .up, .single upId, .single .up upId⟩
  | .disjunction => ⟨.binary .two, .multiple, .second, .disjunction⟩
  | .conjunction => ⟨.binary .two, .multiple, .second, .conjunction⟩
  | .conditionalFalse => ⟨.binary .two, .falsity, .skip, .falsity⟩

def Method.prior : Method → Prior
  | .low => .low
  | .up => .up
  | _ => .two

/-- This is the actual test/consequence tree, not a trusted derivation leaf. -/
@[macro_inline]
def singleEvidence (prior : Prior) (name : TestId) :
    DerivationEvidence (context prior) (singlePre (ψ prior : Assertion []))
      (.command (.test E.report hypothesisId (.read E.dataId) name populationId))
      (singlePost (ψ prior) E.report (singleTest name) (selectedAlternative prior)) :=
  .consequence
    (.proved (single_pre_entails_book_preimage (context prior) (ψ prior) E.report hypothesisId
      (.read E.dataId) name populationId (singleConditions (Γ := []) prior name).frameψ
      (singleConditions (Γ := []) prior name).data_fresh (singleConditions (Γ := []) prior name).inputs))
    (.present (.test E.report hypothesisId (.read E.dataId) name populationId
      (singleBook (ψ prior) E.report (singleTest name))))
    (.proved (single_book_entails_post (context prior) (ψ prior) E.report hypothesisId
      (.read E.dataId) name populationId (selectedAlternative prior)))

@[macro_inline]
def disjunctionEvidence : DerivationEvidence (context .two)
    (multiPre (ψ .two : Assertion []) E.report firstTest alternative)
    (.command (.test secondReport hypothesisId (.read E.aliasId) secondId populationId))
    (multiDisjPost (ψ .two) E.report secondReport firstTest secondTest pairId alternative alternative) :=
  .consequence
    (.proved (multi_pre_entails_book_preimage (context .two) (ψ .two) alternative .disj
      E.report secondReport hypothesisId hypothesisId (.read E.dataId) (.read E.aliasId)
      firstId secondId populationId populationId pairId
      (multiConditions (Γ := []) .disj).frameψ2 (multiConditions (Γ := []) .disj).outputs_ne
      (multiConditions (Γ := []) .disj).dataset_fresh (multiConditions (Γ := []) .disj).inputs))
    (.present (.test secondReport hypothesisId (.read E.aliasId) secondId populationId
      (multiBook (ψ .two) E.report secondReport firstTest secondTest (.disj pairId firstTest secondTest))))
    (.proved (multiDisj_book_entails_post (context .two) (ψ .two) alternative alternative
      E.report secondReport hypothesisId hypothesisId (.read E.dataId) (.read E.aliasId)
      firstId secondId populationId populationId pairId (multiConditions .disj)))

@[macro_inline]
def conjunctionEvidence : DerivationEvidence (context .two)
    (multiPre (ψ .two : Assertion []) E.report firstTest alternative)
    (.command (.test secondReport hypothesisId (.read E.aliasId) secondId populationId))
    (multiConjPost (ψ .two) E.report secondReport firstTest secondTest pairId alternative alternative) :=
  .consequence
    (.proved (multi_pre_entails_book_preimage (context .two) (ψ .two) alternative .conj
      E.report secondReport hypothesisId hypothesisId (.read E.dataId) (.read E.aliasId)
      firstId secondId populationId populationId pairId
      (multiConditions (Γ := []) .conj).frameψ2 (multiConditions (Γ := []) .conj).outputs_ne
      (multiConditions (Γ := []) .conj).dataset_fresh (multiConditions (Γ := []) .conj).inputs))
    (.present (.test secondReport hypothesisId (.read E.aliasId) secondId populationId
      (multiBook (ψ .two) E.report secondReport firstTest secondTest (.conj pairId firstTest secondTest))))
    (.proved (multiConj_book_entails_post (context .two) (ψ .two) alternative alternative
      E.report secondReport hypothesisId hypothesisId (.read E.dataId) (.read E.aliasId)
      firstId secondId populationId populationId pairId (multiConditions .conj)))

@[macro_inline]
def Method.evidence (method : Method) : DerivationEvidence method.binding.model.context
    method.binding.pre.assertion method.binding.program.program method.binding.post.assertion :=
  match method with
  | .two => singleEvidence .two firstId
  | .low => singleEvidence .low lowId
  | .up => singleEvidence .up upId
  | .disjunction => disjunctionEvidence
  | .conjunction => conjunctionEvidence
  | .conditionalFalse => .skip falsity

theorem method_checked (method : Method) : (checkDerivation method.evidence).isAccepted = true := by
  cases method <;> rfl

theorem method_derivation (method : Method) : Derivation method.binding.model.context
    method.binding.pre.assertion method.binding.program.program method.binding.post.assertion :=
  checkDerivation_derivation method.evidence (method_checked method)

theorem method_valid (method : Method) : ValidTriple method.binding.model.context
    method.binding.pre.assertion method.binding.program.program method.binding.post.assertion :=
  checkDerivation_sound method.evidence (method_checked method)

inductive Point where
  | sampled
  | single (name : TestId)
  | pair
  | hidden
  | skipped
  deriving DecidableEq

def Point.snapshot (point : Point) (first second : Bool) : E.Snapshot :=
  match point with
  | .sampled | .skipped => initialSnapshot first second
  | .single name => Lara.Examples.BHLBinaryRuns.singleFinal first second name
  | .pair => Lara.Examples.BHLBinaryRuns.pairFinal first second
  | .hidden => Lara.Examples.BHLBinaryRuns.hiddenFinal first second

noncomputable def Point.world (point : Point) (n : Int) (first second : Bool) : World Bool Primitive :=
  match point with
  | .sampled => sampledWorld n first second
  | .single name => Lara.Examples.BHLBinaryRuns.singleWorld n first second name
  | .pair => Lara.Examples.BHLBinaryRuns.pairWorld n first second
  | .hidden => Lara.Examples.BHLBinaryRuns.hiddenWorld n first second
  | .skipped => E.eventWorld (sampledWorld n first second) ⟨some .skip, initialSnapshot first second⟩

def Method.before : Method → Point
  | .disjunction | .conjunction => .single firstId
  | _ => .sampled

def Method.after : Method → Point
  | .two => .single firstId
  | .low => .single lowId
  | .up => .single upId
  | .disjunction | .conjunction => .pair
  | .conditionalFalse => .skipped

structure Request where
  binding : Binding
  before : Point
  after : Point
  parameter : Int
  first : Bool
  second : Bool

def Method.request (method : Method) (n : Int) (first second : Bool) : Request :=
  ⟨method.binding, method.before, method.after, n, first, second⟩

inductive ApplicationError where
  | modelMismatch | premiseMismatch | programMismatch | postconditionMismatch | runMismatch
  | failedPrecondition
  deriving DecidableEq, Repr

structure BindingCertificate (expected actual : Binding) : Type where
  exact : actual = expected

def checkBinding (expected actual : Binding) : Except ApplicationError (BindingCertificate expected actual) :=
  if hm : actual.model = expected.model then
    if hp : actual.pre = expected.pre then
      if hc : actual.program = expected.program then
        if hq : actual.post = expected.post then
          .ok ⟨by cases actual; cases expected; simp_all⟩
        else .error .postconditionMismatch
      else .error .programMismatch
    else .error .premiseMismatch
  else .error .modelMismatch

def Method.run (method : Method) (n : Int) (first second : Bool) : FiniteExecution.Outcome :=
  FiniteExecution.scheduledRun [0] method.binding.program.source (method.before.snapshot first second)

theorem method_run_completed (method : Method) (n : Int) (first second : Bool) :
    (method.run n first second).status = .completed := by cases method <;> rfl

theorem point_reifies (point : Point) (n : Int) (first second : Bool) :
    E.Reifies (point.world n first second) (point.snapshot first second) := by
  cases point with
  | sampled => exact Lara.Examples.BHLBinaryRuns.sampled_reifies n first second
  | single name => simp [Point.world, Point.snapshot, E.Reifies, Lara.Examples.BHLBinaryRuns.singleWorld,
      E.eventWorld, State.visible, Lara.Examples.BHLExecution.Snapshot.visible]
  | pair => simp [Point.world, Point.snapshot, E.Reifies, Lara.Examples.BHLBinaryRuns.pairWorld,
      E.eventWorld, State.visible, Lara.Examples.BHLExecution.Snapshot.visible]
  | hidden => simp [Point.world, Point.snapshot, E.Reifies, Lara.Examples.BHLBinaryRuns.hiddenWorld,
      E.eventWorld, State.visible, Lara.Examples.BHLExecution.Snapshot.visible]
  | skipped => simp [Point.world, Point.snapshot, E.Reifies, E.eventWorld, State.visible,
      Lara.Examples.BHLExecution.Snapshot.visible]

theorem method_run_endpoint (method : Method) (n : Int) (first second : Bool) :
    E.eventsWorld (method.before.world n first second) (method.run n first second).events =
      method.after.world n first second := by cases method <;> rfl

theorem method_initial (method : Method) (notFalse : method ≠ .conditionalFalse)
    (n : Int) (first second : Bool) (permitted : allowed method.prior n) :
    satisfies method.binding.model.context.interpretation method.binding.model.context.model
      GhostEnv.empty (method.before.world n first second) method.binding.pre.assertion := by
  cases method with
  | two => exact Lara.Examples.BHLStatistical.initial_pre .two GhostEnv.empty n first second permitted
  | low => exact Lara.Examples.BHLStatistical.initial_pre .low GhostEnv.empty n first second permitted
  | up => exact Lara.Examples.BHLStatistical.initial_pre .up GhostEnv.empty n first second permitted
  | disjunction => exact Lara.Examples.BHLStatistical.multi_pre n first second permitted
  | conjunction => exact Lara.Examples.BHLStatistical.multi_pre n first second permitted
  | conditionalFalse => exact False.elim (notFalse rfl)

theorem method_execution (method : Method) (n : Int) (first second : Bool)
    (admitted : Admitted method.binding.model.context.model.dynamics (method.before.world n first second)) :
    executes method.binding.model.context method.binding.program.program
      (method.before.world n first second) (method.after.world n first second) := by
  have computed := FiniteExecution.scheduledRun_executes method.prior [0]
    method.binding.program.source (method.before.snapshot first second)
    (method.before.world n first second) (point_reifies method.before n first second)
  have model : method.binding.model.context = context method.prior := by cases method <;> rfl
  rw [model] at admitted ⊢
  have execution := computed admitted (method_run_completed method n first second)
  change executes (context method.prior) method.binding.program.program
    (method.before.world n first second)
    (E.eventsWorld (method.before.world n first second) (method.run n first second).events) at execution
  rw [method_run_endpoint method n first second] at execution
  exact execution

structure ApplicationCertificate (method : Method) (request : Request) : Type where
  binding : request.binding = method.binding
  before : request.before = method.before
  after : request.after = method.after
  computed : FiniteExecution.Outcome
  computed_exact : computed = method.run request.parameter request.first request.second
  computed_completed : computed.status = .completed
  computed_endpoint : E.eventsWorld
    (request.before.world request.parameter request.first request.second) computed.events =
      request.after.world request.parameter request.first request.second
  initial : satisfies method.binding.model.context.interpretation method.binding.model.context.model
    GhostEnv.empty (request.before.world request.parameter request.first request.second)
    method.binding.pre.assertion
  execution : executes method.binding.model.context method.binding.program.program
    (request.before.world request.parameter request.first request.second)
    (request.after.world request.parameter request.first request.second)
  post : satisfies method.binding.model.context.interpretation method.binding.model.context.model
    GhostEnv.empty (request.after.world request.parameter request.first request.second)
    method.binding.post.assertion

def checkApplication (method : Method) (request : Request) :
    Except ApplicationError (ApplicationCertificate method request) := do
  let bound ← checkBinding method.binding request.binding
  if hb : request.before = method.before then
    if ha : request.after = method.after then
      if hn : allowed method.prior request.parameter then
        if hf : method = .conditionalFalse then .error .failedPrecondition
        else
          let initial := method_initial method hf request.parameter request.first request.second hn
          let execution := method_execution method request.parameter request.first request.second initial.1
          let post := checkDerivation_application method.evidence (method_checked method)
            GhostEnv.empty _ _ initial execution
          let computed := method.run request.parameter request.first request.second
          return ⟨bound.exact, hb, ha, computed, rfl,
            method_run_completed method request.parameter request.first request.second,
            by simpa [hb, ha] using method_run_endpoint method request.parameter request.first request.second,
            by simpa [hb] using initial, by simpa [hb, ha] using execution, by simpa [ha] using post⟩
      else .error .failedPrecondition
    else .error .runMismatch
  else .error .runMismatch

theorem conditional_false_not_applicable (request : Request) :
    ¬ satisfies (context .two).interpretation (context .two).model GhostEnv.empty
      (request.before.world request.parameter request.first request.second) falsity := by
  simp [falsity, satisfies, referenceAssertionSatisfaction, referenceModalSatisfaction,
    atomMeaning, evalTerm]

theorem application_post (method : Method) (request : Request)
    (certificate : ApplicationCertificate method request) :
    satisfies method.binding.model.context.interpretation method.binding.model.context.model
      GhostEnv.empty (request.after.world request.parameter request.first request.second)
      method.binding.post.assertion := certificate.post

end Lara.BHL.CheckedMethods
