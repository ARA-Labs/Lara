import Lara.BHL.ControlLogBinders
import Lara.BHL.ControlLogLaws
import Lara.BHL.CompletenessCore

namespace Lara.BHL

variable {D : Type} [MeasurableSpace D] {Γ : List GhostSort}

noncomputable section

/-- The actual legal finite four-ghost representative, not an assumed
expressiveness oracle. Arbitrary quantified/modal posts keep the original Γ. -/
theorem control_log_represents_wlp (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (before : World D Primitive) (program : Program)
    (post : Assertion Γ) (legal : program.WellFormed)
    (initial : Admitted ctx.model.dynamics before) :
    satisfies ctx.interpretation ctx.model env before
      (ControlLogSyntax.representative program post) ↔
        weakestLiberalPrecondition ctx env program post before := by
  constructor
  · intro represented after execution
    obtain ⟨log, source, terminal, valid⟩ := ControlLog.encode ctx program execution
    have sourceView : semanticView ctx.model.dynamics log.source =
        semanticView ctx.model.dynamics before := by rw [source]
    have result := (ControlLogSyntax.representative_reference_iff ctx env before program post).mp
      represented.2 log valid sourceView
    simpa only [terminal] using result
  · intro outcomes
    refine ⟨initial,
      (ControlLogSyntax.representative_reference_iff ctx env before program post).mpr ?_⟩
    intro log valid sourceView
    obtain ⟨after, execution, view⟩ :=
      ControlLog.decode ctx program log initial valid sourceView.symm legal
    exact (satisfies_congr ctx.interpretation ctx.model env
      (exec_admitted execution) (log.terminal_admitted ctx program valid) view post).mp
        (outcomes after execution)

/-- Public execution requires source well-formedness. An illegal program's
liberal condition is true, while it still cannot acquire a BHL derivation. -/
def weakestLiberalAssertion (program : Program) (post : Assertion Γ) : Assertion Γ := by
  classical
  exact if program.WellFormed then ControlLogSyntax.representative program post
    else .modal ControlLogSyntax.trueFormula

 theorem weakest_liberal_assertion_represents (ctx : ProgramContext D)
    (env : GhostEnv D Primitive Γ) (before : World D Primitive) (program : Program)
    (post : Assertion Γ) (initial : Admitted ctx.model.dynamics before) :
    satisfies ctx.interpretation ctx.model env before (weakestLiberalAssertion program post) ↔
      weakestLiberalPrecondition ctx env program post before := by
  classical
  by_cases legal : program.WellFormed
  · simp only [weakestLiberalAssertion, if_pos legal]
    exact control_log_represents_wlp ctx env before program post legal initial
  · simp only [weakestLiberalAssertion, if_neg legal]
    constructor
    · intro _ after execution
      exact False.elim (legal execution.1)
    · intro _
      refine ⟨initial, ?_⟩
      simp [referenceAssertionSatisfaction, referenceModalSatisfaction,
        ControlLogSyntax.trueFormula, atomMeaning, evalTerm]

/-- Concrete instantiation discharges the independent representation contract;
no representation premise is left in the final completeness theorem. -/
def controlLogWlpFamily (ctx : ProgramContext D) : WlpAssertionFamily ctx where
  formula := weakestLiberalAssertion
  represents := fun env before program post initial =>
    weakest_liberal_assertion_represents ctx env before program post initial

 theorem weakest_liberal_assertion_derivation (ctx : ProgramContext D)
    (program : Program) (legal : program.WellFormed) (post : Assertion Γ) :
    Derivation ctx (weakestLiberalAssertion program post) program post :=
  canonical_derivation ctx (controlLogWlpFamily ctx) program legal post

/-- Relative to the frozen consequence rule's exact-model assertion entailment,
semantic validity reconstructs a derivation for every well-formed source tree.
This neither decides implication nor promises termination or proof search. -/
theorem relative_completeness (ctx : ProgramContext D) (pre post : Assertion Γ)
    (program : Program) (legal : program.WellFormed)
    (valid : ValidTriple ctx pre program post) : Derivation ctx pre program post :=
  relative_completeness_of_family ctx (controlLogWlpFamily ctx) pre post program legal valid

 theorem derivation_iff_valid (ctx : ProgramContext D) (pre post : Assertion Γ)
    (program : Program) (legal : program.WellFormed) :
    Derivation ctx pre program post ↔ ValidTriple ctx pre program post :=
  derivation_iff_valid_of_family ctx (controlLogWlpFamily ctx) pre post program legal

 theorem malformed_program_not_derivable (ctx : ProgramContext D) (pre post : Assertion Γ)
    (program : Program) (illegal : ¬ program.WellFormed) :
    ¬ Derivation ctx pre program post := fun derivation => illegal derivation.wellFormed

 theorem malformed_program_vacuously_valid (ctx : ProgramContext D) (pre post : Assertion Γ)
    (program : Program) (illegal : ¬ program.WellFormed) :
    ValidTriple ctx pre program post := by
  intro env before after _ execution
  exact False.elim (illegal execution.1)

end
end Lara.BHL
