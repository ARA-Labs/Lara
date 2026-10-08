import Lara.Examples.BHLBinaryRuns

/-!
Nonvacuous calibrated finite statistical applications and negative witnesses.

Each positive conclusion has both actual initial-precondition satisfaction and
an actual reference execution. The hidden-test witness keeps the same reported
number but falsifies the proposed single-test conclusion through the complete
ledger. At a true-null exceptional sample, statistical belief is true while the
alternative and knowledge of that alternative are false.
-/

namespace Lara.Examples.BHLStatistical

open Lara.BHL
open Lara.Examples.BHLBinaryModel
open Lara.Examples.BHLBinaryScience
open Lara.Examples.BHLBinaryRuns
open Lara.Examples.BHLSoundnessScience
  (Prior allowed theta hiddenMemory lower upper alternative priorFormula sample protectedOld ψ
    singleTest pairId secondReport)
open Lara.Examples.BHLExecution (report oldReport dataId aliasId)

noncomputable section

 theorem initial_pre (prior : Prior) (env : GhostEnv Bool Primitive Γ) (n : Int)
    (first second : Bool) (hn : allowed prior n) :
    satisfies interpretation (context prior).model env (sampledWorld n first second)
      (singlePre (ψ prior)) := by
  refine ⟨sampled_admitted prior n first second hn, ?_, ?_⟩
  · change referenceModalSatisfaction interpretation (context prior).model env (sampledWorld n first second)
      ((sample dataId).conj ((sample aliasId).conj (protectedOld.conj (priorFormula prior))))
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [sample, referenceModalSatisfaction, atomMeaning, evalTerm, semanticView,
        sampledWorld, firstSample, startWorld, World.samplingProvenance, World.extend,
        World.current, World.trace, World.start, initialSnapshot, State.visible, dataId, aliasId]
    · simp [sample, referenceModalSatisfaction, atomMeaning, evalTerm, semanticView,
        sampledWorld, firstSample, startWorld, World.samplingProvenance, World.extend,
        World.current, World.trace, World.start, initialSnapshot, State.visible, aliasId]
    · simp [protectedOld, referenceModalSatisfaction, atomMeaning, evalTerm, semanticView,
        sampledWorld, firstSample, startWorld, initialSnapshot,
        Lara.Examples.BHLExecution.initialSnapshot, Lara.Examples.BHLExecution.Snapshot.memory,
        Memory.read, Memory.assemble, State.visible]
    · cases prior with
      | two => exact ⟨sampled_lower_possible .two env n first second (by simp [allowed]),
          sampled_upper_possible .two env n first second (by simp [allowed])⟩
      | low => exact ⟨sampled_lower_possible .low env n first second (by simp [allowed]),
          low_upper_impossible env _⟩
      | up => exact ⟨up_lower_impossible env _,
          sampled_upper_possible .up env n first second (by simp [allowed])⟩
  · simp [referenceAssertionSatisfaction, referenceModalSatisfaction,
      atomMeaning, evalTerm, semanticView, sampledWorld]

 theorem two_final (n : Int) (first second : Bool) (hn : allowed .two n) :
    satisfies interpretation (context .two).model GhostEnv.empty (singleWorld n first second firstId)
      (singlePost (ψ .two : Assertion []) report (singleTest firstId) (lower.disj upper)) :=
  derivation_sound twoDerivation _ _ _ (initial_pre .two GhostEnv.empty n first second hn)
    (single_executes .two n first second firstId hn)

 theorem low_final (n : Int) (first second : Bool) (hn : allowed .low n) :
    satisfies interpretation (context .low).model GhostEnv.empty (singleWorld n first second lowId)
      (singlePost (ψ .low : Assertion []) report (singleTest lowId) lower) :=
  derivation_sound lowDerivation _ _ _ (initial_pre .low GhostEnv.empty n first second hn)
    (single_executes .low n first second lowId hn)

 theorem up_final (n : Int) (first second : Bool) (hn : allowed .up n) :
    satisfies interpretation (context .up).model GhostEnv.empty (singleWorld n first second upId)
      (singlePost (ψ .up : Assertion []) report (singleTest upId) upper) :=
  derivation_sound upDerivation _ _ _ (initial_pre .up GhostEnv.empty n first second hn)
    (single_executes .up n first second upId hn)

 theorem single_stored (env : GhostEnv Bool Primitive Γ) (n : Int) (first second : Bool) (name : TestId) :
    referenceAssertionSatisfaction interpretation (context .two).model env (singleWorld n first second name)
      (stored report (singleTest name)) := by
  change ∃ v, evalTerm interpretation (context .two).model env
      (semanticView (context .two).model.dynamics (singleWorld n first second name))
      (Lara.BHL.report Γ report) = some v ∧
    evalTerm interpretation (context .two).model env
      (semanticView (context .two).model.dynamics (singleWorld n first second name))
      (.pvalue (singleTest name)) = some v
  refine ⟨(Tests.Binary.pvalue first : ℝ), ?_, ?_⟩
  · simpa [Lara.BHL.report, evalTerm, semanticView, Memory.read, Memory.assemble,
      Memory.observable, State.visible] using single_report n first second name
  · simp [singleTest, leaf, DatasetExpr.toAssertionTerm, evalTerm, evalNumericalEvent,
      interpretation, semanticView, State.visible, single_data]

 theorem single_range (env : GhostEnv Bool Primitive Γ) (n : Int) (first second : Bool) (name : TestId) :
    referenceAssertionSatisfaction interpretation (context .two).model env (singleWorld n first second name)
      (reportRange Γ report) := by
  cases first <;>
    norm_num [referenceAssertionSatisfaction, referenceModalSatisfaction, atomMeaning,
      evalTerm, semanticView, State.visible, compareReal, Memory.read, Memory.assemble,
      singleWorld, Lara.Examples.BHLExecution.eventWorld, singleFinal, runTest,
      initialSnapshot, Lara.Examples.BHLExecution.Snapshot.memory, Lara.Examples.BHLExecution.report,
      dataId, aliasId]

/-- The first statistical belief is established by its own actual run. -/
 theorem multi_pre (n : Int) (first second : Bool) (hn : allowed .two n) :
    satisfies interpretation (context .two).model GhostEnv.empty (singleWorld n first second firstId)
      (multiPre (ψ .two : Assertion []) report firstTest alternative) := by
  rcases two_final n first second hn with ⟨had, hψ, hh, hb⟩
  exact ⟨had, hψ, hh, hb, single_stored GhostEnv.empty n first second firstId,
    single_range GhostEnv.empty n first second firstId⟩

 theorem multDisj_final (n : Int) (first second : Bool) (hn : allowed .two n) :
    satisfies interpretation (context .two).model GhostEnv.empty (pairWorld n first second)
      (multiDisjPost (ψ .two : Assertion []) report secondReport firstTest secondTest
        pairId alternative alternative) :=
  derivation_sound multDisjDerivation _ _ _ (multi_pre n first second hn)
    (second_executes n first second hn)

 theorem multConj_final (n : Int) (first second : Bool) (hn : allowed .two n) :
    satisfies interpretation (context .two).model GhostEnv.empty (pairWorld n first second)
      (multiConjPost (ψ .two : Assertion []) report secondReport firstTest secondTest
        pairId alternative alternative) :=
  derivation_sound multConjDerivation _ _ _ (multi_pre n first second hn)
    (second_executes n first second hn)

 theorem single_alternative_false :
    ¬ referenceModalSatisfaction interpretation (context .two).model GhostEnv.empty
      (singleWorld 0 true true firstId) (alternative : ModalFormula []) := by
  simp [alternative, referenceModalSatisfaction_disj, lower_iff, upper_iff,
    singleWorld, Lara.Examples.BHLExecution.eventWorld, singleFinal, runTest,
    sampledWorld, firstSample, startWorld, initialSnapshot,
    Lara.Examples.BHLSoundnessScience.theta_hiddenMemory]

/-- The actual null-world witness uses the exceptional branch, not model failure. -/
 theorem exceptional_belief_false_alternative :
    satisfies interpretation (context .two).model GhostEnv.empty (singleWorld 0 true true firstId)
      (.modal (statisticalBelief .equal (Lara.BHL.report [] report)
        (singleTest firstId) (alternative : ModalFormula []))) ∧
    ¬ referenceModalSatisfaction interpretation (context .two).model GhostEnv.empty
      (singleWorld 0 true true firstId) (alternative : ModalFormula []) := by
  rcases two_final 0 true true (by simp [allowed]) with ⟨had, _, _, hb⟩
  exact ⟨⟨had, hb⟩, single_alternative_false⟩

 theorem exceptional_requirements_hold :
    referenceModalSatisfaction interpretation (context .two).model GhostEnv.empty
      (singleWorld 0 true true firstId) (modelRequirementsFormula (singleTest firstId)) := by
  rcases two_final 0 true true (by simp [allowed]) with ⟨_, hψ, _, _⟩
  exact requirements_of_sample .two GhostEnv.empty _ dataId firstId hψ.1

 theorem exceptional_only_branch :
    referenceModalSatisfaction interpretation (context .two).model GhostEnv.empty
      (singleWorld 0 true true firstId)
      (exception .equal (Lara.BHL.report [] report) (singleTest firstId)) ∧
    referenceModalSatisfaction interpretation (context .two).model GhostEnv.empty
      (singleWorld 0 true true firstId) (modelRequirementsFormula (singleTest firstId)) := by
  rcases two_final 0 true true (by simp [allowed]) with ⟨_, _, hh, _⟩
  refine ⟨⟨?_, hh⟩, exceptional_requirements_hold⟩
  simp [pvalueAtom, referenceModalSatisfaction, atomMeaning, evalTerm,
    evalNumericalEvent, singleTest, leaf, DatasetExpr.toAssertionTerm, interpretation,
    semanticView, State.visible, Lara.BHL.report, compareReal, singleWorld,
    Lara.Examples.BHLExecution.eventWorld, singleFinal, runTest, initialSnapshot,
    Lara.Examples.BHLExecution.Snapshot.memory, Memory.read, Memory.assemble,
    Lara.Examples.BHLExecution.report, dataId, aliasId]

 theorem alternative_not_known :
    ¬ referenceModalSatisfaction interpretation (context .two).model GhostEnv.empty
      (singleWorld 0 true true firstId) (.knows (alternative : ModalFormula [])) := by
  intro known
  exact single_alternative_false
    (known _ (exec_admitted (single_executes .two 0 true true firstId (by simp [allowed])))
      (accessible_refl _))

 theorem hidden_exact_history_false :
    ¬ referenceModalSatisfaction interpretation (context .two).model GhostEnv.empty
      (hiddenWorld 0 true true) (exactHistory (singleTest firstId)) := by
  have notLedger : (hiddenWorld 0 true true).current.history ≠ {(true, firstId)} := by
    rw [hidden_ledger]
    intro equal
    have cards := congrArg Multiset.card equal
    norm_num at cards
  simpa [exactHistory, referenceModalSatisfaction, atomMeaning, evalTerm,
    testHistoryTerm, singleTest, leaf, DatasetExpr.toAssertionTerm, semanticView,
    State.visible, hiddenWorld, Lara.Examples.BHLExecution.eventWorld, hiddenFinal,
    singleFinal, runTest, initialSnapshot, dataId, aliasId] using notLedger

 theorem hidden_single_post_false :
    ¬ satisfies interpretation (context .two).model GhostEnv.empty (hiddenWorld 0 true true)
      (singlePost (ψ .two : Assertion []) report (singleTest firstId) alternative) := by
  intro proposed
  exact hidden_exact_history_false proposed.2.2.1

 theorem hidden_alternative_false :
    ¬ referenceModalSatisfaction interpretation (context .two).model GhostEnv.empty
      (hiddenWorld 0 true true) (alternative : ModalFormula []) := by
  simp [alternative, referenceModalSatisfaction_disj, lower_iff, upper_iff,
    hiddenWorld, singleWorld, Lara.Examples.BHLExecution.eventWorld, hiddenFinal, singleFinal, runTest,
    sampledWorld, firstSample, startWorld, initialSnapshot,
    Lara.Examples.BHLSoundnessScience.theta_hiddenMemory]

 theorem hidden_requirements_hold :
    referenceModalSatisfaction interpretation (context .two).model GhostEnv.empty
      (hiddenWorld 0 true true) (modelRequirementsFormula (singleTest firstId)) := by
  apply requirements_of_sample .two GhostEnv.empty _ dataId firstId
  simp [sample, referenceModalSatisfaction, atomMeaning, evalTerm, semanticView,
    hiddenWorld, singleWorld, Lara.Examples.BHLExecution.eventWorld, hiddenFinal,
    singleFinal, runTest, sampledWorld, firstSample, startWorld, initialSnapshot,
    World.samplingProvenance, World.extend, World.current, World.trace, World.start, State.visible, dataId, aliasId]

/-- A hidden test is not rescued by the three-way model-failure escape. -/
 theorem hidden_single_belief_false :
    ¬ referenceModalSatisfaction interpretation (context .two).model GhostEnv.empty
      (hiddenWorld 0 true true)
      (statisticalBelief .equal (Lara.BHL.report [] report)
        (singleTest firstId) (alternative : ModalFormula [])) := by
  intro belief
  have here := belief _ (exec_admitted (hidden_executes 0 true true (by simp [allowed])))
    (accessible_refl _)
  simp only [referenceModalSatisfaction_disj] at here
  rcases here with alternative | exceptional | failed
  · exact hidden_alternative_false alternative
  · exact hidden_exact_history_false exceptional.2
  · exact failed hidden_requirements_hold

/-- This is a counterexample to the proposed triple, not just a false state row. -/
 theorem hidden_procedure_invalid :
    ¬ ValidTriple (context .two) (singlePre (ψ .two : Assertion [])) hiddenSource.quote
      (singlePost (ψ .two) report (singleTest firstId) alternative) := by
  intro valid
  exact hidden_single_post_false
    (valid GhostEnv.empty _ _ (initial_pre .two GhostEnv.empty 0 true true (by simp [allowed]))
      (hidden_executes 0 true true (by simp [allowed])))

end
end Lara.Examples.BHLStatistical
