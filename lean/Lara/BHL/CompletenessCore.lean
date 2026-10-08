import Lara.BHL.WlpRepresentation

namespace Lara.BHL

variable {D : Type} [MeasurableSpace D] {Γ : List GhostSort}

noncomputable section

private theorem family_seq_entails (ctx : ProgramContext D) (family : WlpAssertionFamily ctx)
    (left right : Program) (post : Assertion Γ) :
    AssertionEntails ctx (family.formula (.seq left right) post)
      (family.formula left (family.formula right post)) := by
  intro env before satisfied
  apply (family.represents env before left (family.formula right post) satisfied.1).mpr
  intro middle first
  apply (family.represents env middle right post (exec_admitted first)).mpr
  exact (wlp_seq_iff ctx env before left right post).mp
    ((family.represents env before (.seq left right) post satisfied.1).mp satisfied)
    middle first

/-- Structural reconstruction from independently represented liberal outcomes.
The family contract supplies assertion expressiveness, not a derivation rule. -/
theorem canonical_derivation (ctx : ProgramContext D) (family : WlpAssertionFamily ctx)
    (program : Program) (legal : program.WellFormed) (post : Assertion Γ) :
    Derivation ctx (family.formula program post) program post := by
  induction program generalizing post with
  | command primitive =>
      cases primitive with
      | skip =>
          refine Derivation.consequence ?_ (Derivation.skip post) (AssertionEntails.refl ctx post)
          intro env before satisfied
          exact (wlp_skip_iff ctx env before satisfied.1 post).mp
            ((family.represents env before Program.skip post satisfied.1).mp satisfied)
      | assign x rhs =>
          refine Derivation.consequence ?_
            (Derivation.assign (.assign x rhs) True.intro post) (AssertionEntails.refl ctx post)
          intro env before satisfied
          exact (wlp_command_iff ctx env before satisfied.1 (.assign x rhs) post).mp
            ((family.represents env before (.command (.assign x rhs)) post satisfied.1).mp satisfied)
      | assignDataset name rhs =>
          refine Derivation.consequence ?_
            (Derivation.assign (.assignDataset name rhs) True.intro post)
            (AssertionEntails.refl ctx post)
          intro env before satisfied
          exact (wlp_command_iff ctx env before satisfied.1 (.assignDataset name rhs) post).mp
            ((family.represents env before (.command (.assignDataset name rhs)) post
              satisfied.1).mp satisfied)
      | test result hypothesis data testName population =>
          refine Derivation.consequence ?_
            (Derivation.test result hypothesis data testName population post)
            (AssertionEntails.refl ctx post)
          intro env before satisfied
          exact (wlp_command_iff ctx env before satisfied.1
            (.test result hypothesis data testName population) post).mp
            ((family.represents env before
              (.command (.test result hypothesis data testName population)) post
              satisfied.1).mp satisfied)
  | seq left right ihLeft ihRight =>
      exact Derivation.consequence (family_seq_entails ctx family left right post)
        (Derivation.seq (ihLeft legal.1 (family.formula right post))
          (ihRight legal.2 post)) (AssertionEntails.refl ctx post)
  | ite guard left right ihLeft ihRight =>
      apply Derivation.ite
      · refine Derivation.consequence ?_ (ihLeft legal.1 post) (AssertionEntails.refl ctx post)
        intro env before satisfied
        obtain ⟨pre, enabled⟩ := (satisfies_conj ctx env before _ _).mp satisfied
        apply (family.represents env before left post pre.1).mpr
        exact ((wlp_ite_iff ctx env before guard left right post legal.1 legal.2).mp
          ((family.represents env before (.ite guard left right) post pre.1).mp pre)).1
          ((satisfies_guardAssertion_iff ctx env before guard true).mp enabled).2
      · refine Derivation.consequence ?_ (ihRight legal.2 post) (AssertionEntails.refl ctx post)
        intro env before satisfied
        obtain ⟨pre, enabled⟩ := (satisfies_conj ctx env before _ _).mp satisfied
        apply (family.represents env before right post pre.1).mpr
        exact ((wlp_ite_iff ctx env before guard left right post legal.1 legal.2).mp
          ((family.represents env before (.ite guard left right) post pre.1).mp pre)).2
          ((satisfies_guardAssertion_iff ctx env before guard false).mp enabled).2
  | loop guard body ih =>
      let invariant := family.formula (.loop guard body) post
      have preserves : Derivation ctx (.conj invariant (guardAssertion guard true)) body invariant := by
        refine Derivation.consequence ?_ (ih legal invariant) (AssertionEntails.refl ctx invariant)
        intro env before satisfied
        obtain ⟨pre, enabled⟩ := (satisfies_conj ctx env before _ _).mp satisfied
        apply (family.represents env before body invariant pre.1).mpr
        intro middle first
        apply (family.represents env middle (.loop guard body) post (exec_admitted first)).mpr
        exact wlp_loop_body
          ((satisfies_guardAssertion_iff ctx env before guard true).mp enabled).2
          ((family.represents env before (.loop guard body) post pre.1).mp pre)
          middle first
      refine Derivation.consequence (AssertionEntails.refl ctx invariant)
        (Derivation.loop preserves) ?_
      intro env before satisfied
      obtain ⟨pre, enabled⟩ := (satisfies_conj ctx env before _ _).mp satisfied
      exact wlp_loop_exit ctx env before guard body post legal pre.1
        ((satisfies_guardAssertion_iff ctx env before guard false).mp enabled).2
        ((family.represents env before (.loop guard body) post pre.1).mp pre)
  | par left right ihLeft ihRight =>
      apply Derivation.parallel legal.2.2
      refine Derivation.consequence ?_
        (Derivation.seq (ihLeft legal.1 (family.formula right post))
          (ihRight legal.2.1 post)) (AssertionEntails.refl ctx post)
      intro env before satisfied
      apply family_seq_entails ctx family left right post env before
      apply (family.represents env before (.seq left right) post satisfied.1).mpr
      exact (wlp_parallel_iff ctx env before left right post legal.2.2).mp
        ((family.represents env before (.par left right) post satisfied.1).mp satisfied)

/-- Supporting relative completeness, conditional on a proved assertion family.
Well-formedness is essential: malformed parallel programs have no executions,
so their vacuous semantic validity cannot supply the parallel rule's premise. -/
theorem relative_completeness_of_family (ctx : ProgramContext D)
    (family : WlpAssertionFamily ctx) (pre post : Assertion Γ) (program : Program)
    (legal : program.WellFormed) (valid : ValidTriple ctx pre program post) :
    Derivation ctx pre program post := by
  refine Derivation.consequence ?_ (canonical_derivation ctx family program legal post)
    (AssertionEntails.refl ctx post)
  intro env before satisfied
  apply (family.represents env before program post satisfied.1).mpr
  intro after execution
  exact valid env before after satisfied execution

/-- This equivalence asserts partial correctness, not termination or proof search. -/
theorem derivation_iff_valid_of_family (ctx : ProgramContext D)
    (family : WlpAssertionFamily ctx) (pre post : Assertion Γ) (program : Program)
    (legal : program.WellFormed) :
    Derivation ctx pre program post ↔ ValidTriple ctx pre program post :=
  ⟨derivation_sound, relative_completeness_of_family ctx family pre post program legal⟩

end
end Lara.BHL
