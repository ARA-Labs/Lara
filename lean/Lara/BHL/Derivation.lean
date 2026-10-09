import Lara.BHL.Parallel

namespace Lara.BHL

variable {D : Type} [MeasurableSpace D] {Γ : List GhostSort}

/-- Pure assignment rules cannot execute a test or update the canonical ledger. -/
def Primitive.IsPureAssignment : Primitive → Prop
  | .assign _ _ => True
  | .assignDataset _ _ => True
  | _ => False

/-- A guard assertion denotes successful evaluation to the specified Boolean.
Undefined guards denote neither branch, matching the independent execution. -/
def guardAssertion (guard : ProgramExpr .boolean) (choice : Bool) : Assertion Γ :=
  .modal (.atom (.equal (guard.toAssertionTerm Γ) (.boolean choice)))

noncomputable section

/-- True assertion-theory implication in one exact interpretation/model/context.
The evidence quantifies over every rigid environment and admitted source world. -/
def AssertionEntails (ctx : ProgramContext D) (pre post : Assertion Γ) : Prop :=
  ∀ (env : GhostEnv D Primitive Γ) (world : World D Primitive),
    satisfies ctx.interpretation ctx.model env world pre →
      satisfies ctx.interpretation ctx.model env world post

/-- Independent partial correctness over every terminating reference execution.
This neither proves termination nor supplies empirical model applicability. -/
def ValidTriple (ctx : ProgramContext D) (pre : Assertion Γ) (program : Program)
    (post : Assertion Γ) : Prop :=
  ∀ (env : GhostEnv D Primitive Γ) (before after : World D Primitive),
    satisfies ctx.interpretation ctx.model env before pre →
      executes ctx program before after →
        satisfies ctx.interpretation ctx.model env after post

/-- The eight source-mapped Hoare rules. Statistical rules are derived from test
and consequence; no constructor contains the desired whole-triple validity. -/
inductive Derivation (ctx : ProgramContext D) : Assertion Γ → Program → Assertion Γ → Prop
  | skip (pre : Assertion Γ) : Derivation ctx pre Program.skip pre
  | assign (primitive : Primitive) (pure : primitive.IsPureAssignment)
      (post : Assertion Γ) :
      Derivation ctx (primitive.preimage post) (.command primitive) post
  | seq {pre intermediate post : Assertion Γ} {left right : Program}
      (first : Derivation ctx pre left intermediate)
      (second : Derivation ctx intermediate right post) :
      Derivation ctx pre (.seq left right) post
  | ite {pre post : Assertion Γ} {guard : ProgramExpr .boolean} {left right : Program}
      (yes : Derivation ctx (.conj pre (guardAssertion guard true)) left post)
      (no : Derivation ctx (.conj pre (guardAssertion guard false)) right post) :
      Derivation ctx pre (.ite guard left right) post
  | loop {invariant : Assertion Γ} {guard : ProgramExpr .boolean} {body : Program}
      (preserves : Derivation ctx (.conj invariant (guardAssertion guard true)) body invariant) :
      Derivation ctx invariant (.loop guard body) (.conj invariant (guardAssertion guard false))
  | consequence {pre strengthened weakened post : Assertion Γ} {program : Program}
      (initial : AssertionEntails ctx pre strengthened)
      (derivation : Derivation ctx strengthened program weakened)
      (final : AssertionEntails ctx weakened post) :
      Derivation ctx pre program post
  | test (result : Variable .real .observable) (hypothesis : HypothesisId)
      (data : DatasetExpr) (testName : TestId) (population : PopulationId)
      (post : Assertion Γ) :
      Derivation ctx ((Primitive.test result hypothesis data testName population).preimage post)
        (.command (.test result hypothesis data testName population)) post
  | parallel {pre post : Assertion Γ} {left right : Program}
      (noninterfering : Noninterfering left right)
      (sequential : Derivation ctx pre (.seq left right) post) :
      Derivation ctx pre (.par left right) post

@[simp] theorem Primitive.assign_isPureAssignment (x : Variable sort .observable)
    (rhs : ProgramExpr sort) : (Primitive.assign x rhs).IsPureAssignment := True.intro

@[simp] theorem Primitive.assignDataset_isPureAssignment (name : DatasetId)
    (rhs : DatasetExpr) : (Primitive.assignDataset name rhs).IsPureAssignment := True.intro

@[simp] theorem Primitive.skip_not_isPureAssignment : ¬ Primitive.skip.IsPureAssignment :=
  fun impossible => impossible

@[simp] theorem Primitive.test_not_isPureAssignment (result : Variable .real .observable)
    (hypothesis : HypothesisId) (data : DatasetExpr) (testName : TestId)
    (population : PopulationId) :
    ¬ (Primitive.test result hypothesis data testName population).IsPureAssignment :=
  fun impossible => impossible

namespace AssertionEntails

theorem refl (ctx : ProgramContext D) (assertion : Assertion Γ) :
    AssertionEntails ctx assertion assertion := fun _ _ h => h

theorem trans {ctx : ProgramContext D} {first second third : Assertion Γ}
    (left : AssertionEntails ctx first second) (right : AssertionEntails ctx second third) :
    AssertionEntails ctx first third := fun env world h => right env world (left env world h)

theorem conj_left (ctx : ProgramContext D) (left right : Assertion Γ) :
    AssertionEntails ctx (.conj left right) left := by
  intro env world h
  exact ⟨h.1, h.2.1⟩

theorem conj_right (ctx : ProgramContext D) (left right : Assertion Γ) :
    AssertionEntails ctx (.conj left right) right := by
  intro env world h
  exact ⟨h.1, h.2.2⟩

theorem conj {ctx : ProgramContext D} {pre left right : Assertion Γ}
    (hl : AssertionEntails ctx pre left) (hr : AssertionEntails ctx pre right) :
    AssertionEntails ctx pre (.conj left right) := by
  intro env world h
  exact ⟨h.1, (hl env world h).2, (hr env world h).2⟩

end AssertionEntails

namespace Derivation

/-- Derivations prove the source noninterference discipline at every occurrence. -/
theorem wellFormed {ctx : ProgramContext D} {pre post : Assertion Γ} {program : Program}
    (derivation : Derivation ctx pre program post) : program.WellFormed := by
  induction derivation with
  | skip => trivial
  | assign => trivial
  | seq _ _ first second => exact ⟨first, second⟩
  | ite _ _ yes no => exact ⟨yes, no⟩
  | loop _ body => exact body
  | consequence _ _ _ ih => exact ih
  | test => trivial
  | parallel noninterfering _ sequential =>
      exact ⟨sequential.1, sequential.2, noninterfering⟩

end Derivation

end
end Lara.BHL
