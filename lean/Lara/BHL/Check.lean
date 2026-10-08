import Lara.BHL.RuleCode

namespace Lara.BHL

variable {D : Type} [MeasurableSpace D] {Γ : List GhostSort}

inductive EntailmentEvidence (ctx : ProgramContext D) (pre post : Assertion Γ) : Type where
  | missing
  | proved : AssertionEntails ctx pre post → EntailmentEvidence ctx pre post
  | refuted : (¬ AssertionEntails ctx pre post) → EntailmentEvidence ctx pre post

structure EntailmentCertificate (ctx : ProgramContext D) (pre post : Assertion Γ) : Type where
  proof : AssertionEntails ctx pre post

def checkEntailment {ctx : ProgramContext D} {pre post : Assertion Γ}
    (side : ImplicationSide) (evidence : EntailmentEvidence ctx pre post) :
    Except DerivationCheckError (EntailmentCertificate ctx pre post) :=
  match evidence with
  | .missing => .error (.missingImplication side)
  | .proved proof => .ok ⟨proof⟩
  | .refuted _ => .error (.invalidImplication side)

@[macro_inline]
def EntailmentEvidence.code {ctx : ProgramContext D} {pre post : Assertion Γ} :
    EntailmentEvidence ctx pre post → EntailmentCode
  | .missing => .missing
  | .proved _ => .proved
  | .refuted _ => .refuted

theorem EntailmentEvidence.bound {ctx : ProgramContext D} {pre post : Assertion Γ}
    (evidence : EntailmentEvidence ctx pre post) : EntailmentBinding ctx pre post evidence.code := by
  cases evidence with
  | missing => exact .missing
  | proved proof => exact .proved proof
  | refuted proof => exact .refuted proof

/-- The executable code is paired with its exact descriptive kernel binding.
The proof is erased; the code has no live mathematical context parameter. -/
structure DerivationEvidence (ctx : ProgramContext D) (pre : Assertion Γ)
    (program : Program) (post : Assertion Γ) : Type where
  code : DerivationCode
  bound : DerivationCodeBinding ctx code pre program post

structure DerivationPremiseEvidence (ctx : ProgramContext D) (pre : Assertion Γ)
    (program : Program) (post : Assertion Γ) : Type where
  code : Option DerivationCode
  bound : DerivationSlotBinding ctx code pre program post

namespace DerivationPremiseEvidence
variable {ctx : ProgramContext D} {pre post : Assertion Γ} {program : Program}

@[macro_inline]
def missing : DerivationPremiseEvidence ctx pre program post := ⟨none, .missing⟩

@[macro_inline]
def present (evidence : DerivationEvidence ctx pre program post) :
    DerivationPremiseEvidence ctx pre program post := ⟨some evidence.code, .present evidence.bound⟩
end DerivationPremiseEvidence

namespace DerivationEvidence
variable {ctx : ProgramContext D}

@[macro_inline]
def skip (pre : Assertion Γ) : DerivationEvidence ctx pre Program.skip pre :=
  ⟨.skip, .skip pre⟩

@[macro_inline]
def assign (primitive : Primitive) (post : Assertion Γ) :
    DerivationEvidence ctx (primitive.preimage post) (.command primitive) post :=
  ⟨.assign primitive, .assign primitive post⟩

@[macro_inline]
def seq {pre intermediate post : Assertion Γ} {left right : Program}
    (first : DerivationPremiseEvidence ctx pre left intermediate)
    (second : DerivationPremiseEvidence ctx intermediate right post) :
    DerivationEvidence ctx pre (.seq left right) post :=
  ⟨.seq first.code second.code, .seq first.bound second.bound⟩

@[macro_inline]
def ite {pre post : Assertion Γ} {guard : ProgramExpr .boolean} {left right : Program}
    (yes : DerivationPremiseEvidence ctx (.conj pre (guardAssertion guard true)) left post)
    (no : DerivationPremiseEvidence ctx (.conj pre (guardAssertion guard false)) right post) :
    DerivationEvidence ctx pre (.ite guard left right) post :=
  ⟨.ite yes.code no.code, .ite yes.bound no.bound⟩

@[macro_inline]
def loop {invariant : Assertion Γ} {guard : ProgramExpr .boolean} {body : Program}
    (preserves : DerivationPremiseEvidence ctx (.conj invariant (guardAssertion guard true)) body invariant) :
    DerivationEvidence ctx invariant (.loop guard body) (.conj invariant (guardAssertion guard false)) :=
  ⟨.loop preserves.code, .loop preserves.bound⟩

@[macro_inline]
def consequence {pre strengthened weakened post : Assertion Γ} {program : Program}
    (initial : EntailmentEvidence ctx pre strengthened)
    (body : DerivationPremiseEvidence ctx strengthened program weakened)
    (final : EntailmentEvidence ctx weakened post) : DerivationEvidence ctx pre program post :=
  ⟨.consequence initial.code body.code final.code, .consequence initial.bound body.bound final.bound⟩

@[macro_inline]
def test (result : Variable .real .observable) (hypothesis : HypothesisId)
    (data : DatasetExpr) (testName : TestId) (population : PopulationId) (post : Assertion Γ) :
    DerivationEvidence ctx ((Primitive.test result hypothesis data testName population).preimage post)
      (.command (.test result hypothesis data testName population)) post :=
  ⟨.test, .test result hypothesis data testName population post⟩

@[macro_inline]
def parallel {pre post : Assertion Γ} {left right : Program}
    (sequential : DerivationPremiseEvidence ctx pre (.seq left right) post) :
    DerivationEvidence ctx pre (.par left right) post :=
  ⟨.parallel left right sequential.code, .parallel sequential.bound⟩
end DerivationEvidence

structure DerivationCertificate (ctx : ProgramContext D) (pre : Assertion Γ)
    (program : Program) (post : Assertion Γ) : Type where
  derivation : Derivation ctx pre program post

abbrev DerivationCheckResult (ctx : ProgramContext D) (pre : Assertion Γ)
    (program : Program) (post : Assertion Γ) :=
  Except DerivationCheckError (DerivationCertificate ctx pre program post)

@[macro_inline]
def DerivationCheckResult.isAccepted {ctx : ProgramContext D} {pre post : Assertion Γ}
    {program : Program} : DerivationCheckResult ctx pre program post → Bool
  | .ok _ => true
  | .error _ => false

/-- All recursion runs on context-free rule codes. The exact binding decodes a
successful code to the independent derivation; it is never a supplied approval. -/
@[macro_inline]
def checkDerivation {ctx : ProgramContext D} {pre post : Assertion Γ} {program : Program}
    (evidence : DerivationEvidence ctx pre program post) : DerivationCheckResult ctx pre program post :=
  match checked : checkDerivationCode evidence.code with
  | .error error => .error error
  | .ok value => .ok ⟨evidence.bound.derivation (by cases value; exact checked)⟩

/-- Acceptance recovers the exact derivation independently of Hoare soundness. -/
theorem checkDerivation_derivation {ctx : ProgramContext D} {pre post : Assertion Γ}
    {program : Program} (evidence : DerivationEvidence ctx pre program post)
    (accepted : (checkDerivation evidence).isAccepted = true) :
    Derivation ctx pre program post := by
  cases checked : checkDerivation evidence with
  | error error => simp [DerivationCheckResult.isAccepted, checked] at accepted
  | ok certificate => exact certificate.derivation

/-- Conditional partial correctness, obtained only after derivation recovery. -/
theorem checkDerivation_sound {ctx : ProgramContext D} {pre post : Assertion Γ}
    {program : Program} (evidence : DerivationEvidence ctx pre program post)
    (accepted : (checkDerivation evidence).isAccepted = true) :
    ValidTriple ctx pre program post :=
  derivation_sound (checkDerivation_derivation evidence accepted)

/-- Application additionally needs independent initial satisfaction and an actual
execution in the very same context/program. Acceptance alone supplies neither. -/
theorem checkDerivation_application {ctx : ProgramContext D} {pre post : Assertion Γ}
    {program : Program} (evidence : DerivationEvidence ctx pre program post)
    (accepted : (checkDerivation evidence).isAccepted = true)
    (env : GhostEnv D Primitive Γ) (before after : World D Primitive)
    (initial : satisfies ctx.interpretation ctx.model env before pre)
    (execution : executes ctx program before after) :
    satisfies ctx.interpretation ctx.model env after post :=
  checkDerivation_sound evidence accepted env before after initial execution

/-- Computed evidence acceptance also recovers the source well-formedness proof. -/
theorem checkDerivation_wellFormed {ctx : ProgramContext D} {pre post : Assertion Γ}
    {program : Program} (evidence : DerivationEvidence ctx pre program post)
    (accepted : (checkDerivation evidence).isAccepted = true) : program.WellFormed :=
  (checkDerivation_derivation evidence accepted).wellFormed

namespace DerivationCheckExamples

variable (ctx : ProgramContext D)

/-- A genuine inference with proof-backed implication premises. -/
@[macro_inline]
def reflexiveConsequence (assertion : Assertion Γ) :
    DerivationEvidence ctx assertion Program.skip assertion :=
  .consequence (.proved (AssertionEntails.refl ctx assertion)) (.present (.skip assertion))
    (.proved (AssertionEntails.refl ctx assertion))

@[simp] theorem reflexiveConsequence_accepted (assertion : Assertion Γ) :
    (checkDerivation (reflexiveConsequence ctx assertion)).isAccepted = true := rfl

@[macro_inline]
def assignment (x : Variable sort .observable) (rhs : ProgramExpr sort)
    (post : Assertion Γ) :
    DerivationEvidence ctx ((Primitive.assign x rhs).preimage post)
      (.command (.assign x rhs)) post :=
  .assign (.assign x rhs) post

@[simp] theorem assignment_accepted (x : Variable sort .observable) (rhs : ProgramExpr sort)
    (post : Assertion Γ) :
    (checkDerivation (assignment ctx x rhs post)).isAccepted = true := rfl

@[macro_inline]
def testRule (result : Variable .real .observable) (hypothesis : HypothesisId)
    (data : DatasetExpr) (testName : TestId) (population : PopulationId) (post : Assertion Γ) :
    DerivationEvidence ctx ((Primitive.test result hypothesis data testName population).preimage post)
      (.command (.test result hypothesis data testName population)) post :=
  .test result hypothesis data testName population post

@[simp] theorem testRule_accepted (result : Variable .real .observable)
    (hypothesis : HypothesisId) (data : DatasetExpr) (testName : TestId)
    (population : PopulationId) (post : Assertion Γ) :
    (checkDerivation (testRule ctx result hypothesis data testName population post)).isAccepted =
      true := rfl

@[macro_inline]
def skipSequence (assertion : Assertion Γ) :
    DerivationEvidence ctx assertion (.seq Program.skip Program.skip) assertion :=
  .seq (.present (.skip assertion)) (.present (.skip assertion))

@[simp] theorem skipSequence_accepted (assertion : Assertion Γ) :
    (checkDerivation (skipSequence ctx assertion)).isAccepted = true := rfl

/-- Removing the guard conjunct requires genuine universal entailment evidence. -/
@[macro_inline]
def guardedSkip (assertion : Assertion Γ) (guard : ProgramExpr .boolean) (choice : Bool) :
    DerivationEvidence ctx (.conj assertion (guardAssertion guard choice))
      Program.skip assertion :=
  .consequence (.proved (AssertionEntails.conj_left ctx assertion (guardAssertion guard choice)))
    (.present (.skip assertion)) (.proved (AssertionEntails.refl ctx assertion))

@[macro_inline]
def skipConditional (assertion : Assertion Γ) (guard : ProgramExpr .boolean) :
    DerivationEvidence ctx assertion (.ite guard Program.skip Program.skip) assertion :=
  .ite (.present (guardedSkip ctx assertion guard true)) (.present (guardedSkip ctx assertion guard false))

@[simp] theorem skipConditional_accepted (assertion : Assertion Γ)
    (guard : ProgramExpr .boolean) :
    (checkDerivation (skipConditional ctx assertion guard)).isAccepted = true := rfl

/-- This checks partial correctness only, including when the loop never exits. -/
@[macro_inline]
def skipLoop (invariant : Assertion Γ) (guard : ProgramExpr .boolean) :
    DerivationEvidence ctx invariant (.loop guard Program.skip)
      (.conj invariant (guardAssertion guard false)) :=
  .loop (.present (guardedSkip ctx invariant guard true))

@[simp] theorem skipLoop_accepted (invariant : Assertion Γ) (guard : ProgramExpr .boolean) :
    (checkDerivation (skipLoop ctx invariant guard)).isAccepted = true := rfl

@[macro_inline]
def skipParallel (assertion : Assertion Γ) :
    DerivationEvidence ctx assertion (.par Program.skip Program.skip) assertion :=
  .parallel (.present (skipSequence ctx assertion))

@[simp] theorem skipParallel_accepted (assertion : Assertion Γ) :
    (checkDerivation (skipParallel ctx assertion)).isAccepted = true := rfl

@[macro_inline]
def missingImplication (assertion : Assertion Γ) :
    DerivationEvidence ctx assertion Program.skip assertion :=
  .consequence .missing (.present (.skip assertion)) (.proved (AssertionEntails.refl ctx assertion))

@[simp] theorem missingImplication_rejected (assertion : Assertion Γ) :
    checkDerivation (missingImplication ctx assertion) =
      .error (.missingImplication .initial) := rfl

@[macro_inline]
def missingFinalImplication (assertion : Assertion Γ) :
    DerivationEvidence ctx assertion Program.skip assertion :=
  .consequence (.proved (AssertionEntails.refl ctx assertion)) (.present (.skip assertion)) .missing

@[simp] theorem missingFinalImplication_rejected (assertion : Assertion Γ) :
    checkDerivation (missingFinalImplication ctx assertion) =
      .error (.missingImplication .final) := rfl

@[macro_inline]
def invalidImplication (pre post : Assertion Γ) (refuted : ¬ AssertionEntails ctx pre post) :
    DerivationEvidence ctx pre Program.skip post :=
  .consequence (.refuted refuted) (.present (.skip post)) (.proved (AssertionEntails.refl ctx post))

@[simp] theorem invalidImplication_rejected (pre post : Assertion Γ)
    (refuted : ¬ AssertionEntails ctx pre post) :
    checkDerivation (invalidImplication ctx pre post refuted) =
      .error (.invalidImplication .initial) := rfl

@[macro_inline]
def missingPremise (assertion : Assertion Γ) :
    DerivationEvidence ctx assertion (.seq Program.skip Program.skip) assertion :=
  .seq (intermediate := assertion) .missing (.present (.skip assertion))

@[simp] theorem missingPremise_rejected (assertion : Assertion Γ) :
    checkDerivation (missingPremise ctx assertion) = .error (.missingPremise .seqFirst) := rfl

/-- Skip is not an assignment, even though it is a valid primitive command. -/
@[macro_inline]
def invalidAssignment (post : Assertion Γ) :
    DerivationEvidence ctx (Primitive.skip.preimage post) Program.skip post :=
  .assign .skip post

@[simp] theorem invalidAssignment_rejected (post : Assertion Γ) :
    checkDerivation (invalidAssignment ctx post) = .error .assignmentNotPure := rfl

/-- Tests must use their dedicated rule rather than smuggling ledger writes
through assignment evidence. -/
@[macro_inline]
def testViaAssign (result : Variable .real .observable) (hypothesis : HypothesisId)
    (data : DatasetExpr) (testName : TestId) (population : PopulationId) (post : Assertion Γ) :
    DerivationEvidence ctx ((Primitive.test result hypothesis data testName population).preimage post)
      (.command (.test result hypothesis data testName population)) post :=
  .assign (.test result hypothesis data testName population) post

@[simp] theorem testViaAssign_rejected (result : Variable .real .observable)
    (hypothesis : HypothesisId) (data : DatasetExpr) (testName : TestId)
    (population : PopulationId) (post : Assertion Γ) :
    checkDerivation (testViaAssign ctx result hypothesis data testName population post) =
      .error .assignmentNotPure := rfl

/-- The invalid recursive assignment is actually visited and its path retained. -/
@[macro_inline]
def invalidRecursivePremise (post : Assertion Γ) :
    DerivationEvidence ctx (Primitive.skip.preimage post)
      (.seq Program.skip Program.skip) post :=
  .seq (.present (invalidAssignment ctx post)) (.present (.skip post))

@[simp] theorem invalidRecursivePremise_rejected (post : Assertion Γ) :
    checkDerivation (invalidRecursivePremise ctx post) =
      .error (.inPremise .seqFirst .assignmentNotPure) := rfl

/-- The sequential premise is fully populated with valid assignment evidence,
but writing the same cell on both parallel sides fails computed NI. -/
@[macro_inline]
def noninterferingFailure (x : Variable sort .observable) (rhs : ProgramExpr sort)
    (post : Assertion Γ) :
    DerivationEvidence ctx ((Primitive.assign x rhs).preimage
      ((Primitive.assign x rhs).preimage post))
      (.par (.command (.assign x rhs)) (.command (.assign x rhs))) post :=
  .parallel (.present (.seq
    (.present (.assign (.assign x rhs) ((Primitive.assign x rhs).preimage post)))
    (.present (.assign (.assign x rhs) post))))

@[simp] theorem noninterferingFailure_rejected (x : Variable sort .observable)
    (rhs : ProgramExpr sort) (post : Assertion Γ) :
    checkDerivation (noninterferingFailure ctx x rhs post) =
      .error .noninterferingFailure := by
  have failed : noninterferingCheck (.command (.assign x rhs))
      (.command (.assign x rhs)) = false := by
    simp [noninterferingCheck, Program.writes, Program.used, Program.reads,
      Primitive.writes, Primitive.reads]
  have rejected : checkDerivationCode (noninterferingFailure ctx x rhs post).code =
      .error .noninterferingFailure := by
    simp [noninterferingFailure, DerivationEvidence.parallel, checkDerivationCode, failed]
  unfold checkDerivation
  split <;> simp_all

end DerivationCheckExamples

end Lara.BHL
