import Lara.BHL.Soundness

namespace Lara.BHL

variable {D : Type} [MeasurableSpace D] {Γ : List GhostSort}

inductive DerivationPremise where
  | seqFirst | seqSecond | ifTrue | ifFalse | loopBody | consequenceBody | parallelSequential
  deriving DecidableEq, Repr

inductive ImplicationSide where
  | initial | final
  deriving DecidableEq, Repr

inductive DerivationCheckError where
  | assignmentNotPure
  | missingPremise : DerivationPremise → DerivationCheckError
  | inPremise : DerivationPremise → DerivationCheckError → DerivationCheckError
  | missingImplication : ImplicationSide → DerivationCheckError
  | invalidImplication : ImplicationSide → DerivationCheckError
  | noninterferingFailure
  deriving DecidableEq, Repr

/-- Only the evidence status is executable; binding a proved status below requires
an actual universal implication proof in the exact mathematical context. -/
inductive EntailmentCode where
  | missing | proved | refuted
  deriving DecidableEq, Repr

/-- Runtime rule data contains only what validation inspects. Mathematical
contexts and assertion indices live in the independent binding relation below. -/
inductive DerivationCode where
  | skip
  | assign : Primitive → DerivationCode
  | seq : Option DerivationCode → Option DerivationCode → DerivationCode
  | ite : Option DerivationCode → Option DerivationCode → DerivationCode
  | loop : Option DerivationCode → DerivationCode
  | consequence : EntailmentCode → Option DerivationCode → EntailmentCode → DerivationCode
  | test
  | parallel : Program → Program → Option DerivationCode → DerivationCode

def Primitive.pureAssignmentCheck : Primitive → Bool
  | .assign _ _ | .assignDataset _ _ => true
  | .skip | .test _ _ _ _ _ => false

@[simp] theorem Primitive.pureAssignmentCheck_iff (primitive : Primitive) :
    primitive.pureAssignmentCheck = true ↔ primitive.IsPureAssignment := by
  cases primitive <;> simp [Primitive.pureAssignmentCheck, Primitive.IsPureAssignment]

def checkEntailmentCode (side : ImplicationSide) : EntailmentCode → Except DerivationCheckError Unit
  | .missing => .error (.missingImplication side)
  | .proved => .ok ()
  | .refuted => .error (.invalidImplication side)

mutual
def checkDerivationCode : DerivationCode → Except DerivationCheckError Unit
  | .skip | .test => .ok ()
  | .assign primitive =>
      if primitive.pureAssignmentCheck then .ok () else .error .assignmentNotPure
  | .seq first second => do
      checkDerivationSlot .seqFirst first
      checkDerivationSlot .seqSecond second
  | .ite yes no => do
      checkDerivationSlot .ifTrue yes
      checkDerivationSlot .ifFalse no
  | .loop body => checkDerivationSlot .loopBody body
  | .consequence initial body final => do
      checkEntailmentCode .initial initial
      checkDerivationSlot .consequenceBody body
      checkEntailmentCode .final final
  | .parallel left right sequential =>
      if noninterferingCheck left right then checkDerivationSlot .parallelSequential sequential
      else .error .noninterferingFailure

def checkDerivationSlot (location : DerivationPremise) :
    Option DerivationCode → Except DerivationCheckError Unit
  | none => .error (.missingPremise location)
  | some code => (checkDerivationCode code).mapError (.inPremise location)
end

inductive EntailmentBinding (ctx : ProgramContext D) (pre post : Assertion Γ) :
    EntailmentCode → Prop where
  | missing : EntailmentBinding ctx pre post .missing
  | proved : AssertionEntails ctx pre post → EntailmentBinding ctx pre post .proved
  | refuted : (¬ AssertionEntails ctx pre post) → EntailmentBinding ctx pre post .refuted

mutual
/-- Exact descriptive binding of every runtime rule. Neither this relation nor
any constructor assumes the desired derivation or triple validity. -/
inductive DerivationCodeBinding (ctx : ProgramContext D) :
    DerivationCode → Assertion Γ → Program → Assertion Γ → Prop where
  | skip (pre : Assertion Γ) : DerivationCodeBinding ctx .skip pre Program.skip pre
  | assign (primitive : Primitive) (post : Assertion Γ) :
      DerivationCodeBinding ctx (.assign primitive) (primitive.preimage post) (.command primitive) post
  | seq {pre intermediate post : Assertion Γ} {left right : Program} {first second}
      (firstBound : DerivationSlotBinding ctx first pre left intermediate)
      (secondBound : DerivationSlotBinding ctx second intermediate right post) :
      DerivationCodeBinding ctx (.seq first second) pre (.seq left right) post
  | ite {pre post : Assertion Γ} {guard : ProgramExpr .boolean} {left right : Program} {yes no}
      (yesBound : DerivationSlotBinding ctx yes (.conj pre (guardAssertion guard true)) left post)
      (noBound : DerivationSlotBinding ctx no (.conj pre (guardAssertion guard false)) right post) :
      DerivationCodeBinding ctx (.ite yes no) pre (.ite guard left right) post
  | loop {invariant : Assertion Γ} {guard : ProgramExpr .boolean} {body : Program} {preserves}
      (bodyBound : DerivationSlotBinding ctx preserves
        (.conj invariant (guardAssertion guard true)) body invariant) :
      DerivationCodeBinding ctx (.loop preserves) invariant (.loop guard body)
        (.conj invariant (guardAssertion guard false))
  | consequence {pre strengthened weakened post : Assertion Γ} {program : Program} {initial body final}
      (initialBound : EntailmentBinding ctx pre strengthened initial)
      (bodyBound : DerivationSlotBinding ctx body strengthened program weakened)
      (finalBound : EntailmentBinding ctx weakened post final) :
      DerivationCodeBinding ctx (.consequence initial body final) pre program post
  | test (result : Variable .real .observable) (hypothesis : HypothesisId)
      (data : DatasetExpr) (testName : TestId) (population : PopulationId) (post : Assertion Γ) :
      DerivationCodeBinding ctx .test
        ((Primitive.test result hypothesis data testName population).preimage post)
        (.command (.test result hypothesis data testName population)) post
  | parallel {pre post : Assertion Γ} {left right : Program} {sequential}
      (sequentialBound : DerivationSlotBinding ctx sequential pre (.seq left right) post) :
      DerivationCodeBinding ctx (.parallel left right sequential) pre (.par left right) post

inductive DerivationSlotBinding (ctx : ProgramContext D) :
    Option DerivationCode → Assertion Γ → Program → Assertion Γ → Prop where
  | missing : DerivationSlotBinding ctx none pre program post
  | present : DerivationCodeBinding ctx code pre program post →
      DerivationSlotBinding ctx (some code) pre program post
end

private theorem bind_ok_parts {ε : Type} (first second : Except ε Unit)
    (checked : (first >>= fun _ => second) = .ok ()) : first = .ok () ∧ second = .ok () := by
  cases first with
  | error error => simp [bind, Except.bind] at checked
  | ok value => cases value; exact ⟨rfl, checked⟩

private theorem map_error_ok (value : Except DerivationCheckError Unit) (location : DerivationPremise)
    (checked : value.mapError (DerivationCheckError.inPremise location) = .ok ()) : value = .ok () := by
  cases value with
  | error error => simp [Except.mapError] at checked
  | ok value => cases value; rfl

theorem EntailmentBinding.entails {ctx : ProgramContext D} {pre post : Assertion Γ}
    {code : EntailmentCode} (bound : EntailmentBinding ctx pre post code) (side : ImplicationSide)
    (checked : checkEntailmentCode side code = .ok ()) : AssertionEntails ctx pre post := by
  cases bound with
  | missing => simp [checkEntailmentCode] at checked
  | proved proof => exact proof
  | refuted proof => simp [checkEntailmentCode] at checked

mutual
/-- Executable acceptance decodes to the independent exact derivation before
soundness is used. The binding proof is erased, but cannot be replaced by a flag. -/
theorem DerivationCodeBinding.derivation {ctx : ProgramContext D} {pre post : Assertion Γ}
    {program : Program} {code : DerivationCode} (bound : DerivationCodeBinding ctx code pre program post)
    (checked : checkDerivationCode code = .ok ()) : Derivation ctx pre program post := by
  cases bound with
  | skip pre => exact .skip pre
  | assign primitive post =>
      by_cases pure : primitive.pureAssignmentCheck = true
      · exact .assign primitive ((Primitive.pureAssignmentCheck_iff primitive).mp pure) post
      · simp [checkDerivationCode, pure] at checked
  | seq firstBound secondBound =>
      have parts := bind_ok_parts _ _ checked
      exact .seq (DerivationSlotBinding.derivation firstBound .seqFirst parts.1)
        (DerivationSlotBinding.derivation secondBound .seqSecond parts.2)
  | ite yesBound noBound =>
      have parts := bind_ok_parts _ _ checked
      exact .ite (DerivationSlotBinding.derivation yesBound .ifTrue parts.1)
        (DerivationSlotBinding.derivation noBound .ifFalse parts.2)
  | loop bodyBound => exact .loop (DerivationSlotBinding.derivation bodyBound .loopBody checked)
  | consequence initialBound bodyBound finalBound =>
      have first := bind_ok_parts _ _ checked
      have tail := bind_ok_parts _ _ first.2
      exact .consequence (initialBound.entails .initial first.1)
        (DerivationSlotBinding.derivation bodyBound .consequenceBody tail.1)
        (finalBound.entails .final tail.2)
  | @parallel pre post left right sequential sequentialBound =>
      by_cases independent : noninterferingCheck left right = true
      · exact .parallel ((noninterferingCheck_iff left right).mp independent)
          (DerivationSlotBinding.derivation sequentialBound .parallelSequential
            (by simpa [checkDerivationCode, independent] using checked))
      · simp [checkDerivationCode, independent] at checked
  | test result hypothesis data testName population post =>
      exact .test result hypothesis data testName population post

theorem DerivationSlotBinding.derivation {ctx : ProgramContext D} {pre post : Assertion Γ}
    {program : Program} {code : Option DerivationCode}
    (bound : DerivationSlotBinding ctx code pre program post) (location : DerivationPremise)
    (checked : checkDerivationSlot location code = .ok ()) : Derivation ctx pre program post := by
  cases bound with
  | missing => simp [checkDerivationSlot] at checked
  | present bound =>
      exact bound.derivation (map_error_ok _ location checked)
end

end Lara.BHL
