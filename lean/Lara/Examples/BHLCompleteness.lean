import Lara.BHL.Completeness
import Lara.Examples.BHLSoundness

namespace Lara.Examples.BHLCompleteness

open Lara.BHL

namespace E
export Lara.Examples.BHLExecution (context interpretation terminatingLoop incrementX incrementY
  parallel badParallel good_ni bad_ni sampledWorld sampled_admitted loop_executes
  loopEvents eventsWorld loop_final_x x y report oldReport)
end E

namespace S
export Lara.Examples.BHLSoundness (stateAssertion stateAssertion_iff loopInvariant
  loop_body_entails state_entails_loop sampled_state guard_less_iff parallelΓ parallelEnv
  parallelPre parallelIntermediate parallelPost)
end S

noncomputable section

variable {Γ : List GhostSort}

/-- Semantic preservation is obtained from successful local preimages and the
finite arithmetic invariant, not by assuming any syntactic derivation. -/
theorem loop_body_semantically_preserves : ValidTriple E.context
    (.conj (S.loopInvariant Γ)
      (guardAssertion (.intLess (.read E.x) (.integer 3)) true))
    E.incrementX.quote (S.loopInvariant Γ) := by
  intro env before after pre execution
  exact primitive_preimage_valid E.context
    (.assign E.x (.intAdd (.read E.x) (.integer 1))) (S.loopInvariant Γ)
      env before after (S.loop_body_entails env before pre) execution

private theorem false_guard_below_three (env : GhostEnv Bool Primitive Γ)
    (world : World Bool Primitive) (n : Int) (below : n < 3)
    (state : referenceAssertionSatisfaction E.interpretation E.context.model env world
      (S.stateAssertion Γ n 0))
    (guard : referenceAssertionSatisfaction E.interpretation E.context.model env world
      (guardAssertion (.intLess (.read E.x) (.integer 3)) false)) : False := by
  obtain ⟨value, read, negative⟩ := (S.guard_less_iff env world 3 false).mp guard
  have actual := (S.stateAssertion_iff env world n 0).mp state
  have equal : value = n := Option.some.inj (read.symm.trans actual.1)
  subst value
  simp only [below, decide_true] at negative
  cases negative

 theorem loop_exit_entails_three : AssertionEntails E.context
    (.conj (S.loopInvariant Γ)
      (guardAssertion (.intLess (.read E.x) (.integer 3)) false))
    (S.stateAssertion Γ 3 0) := by
  intro env world pre
  have invariant := pre.2.1
  simp only [S.loopInvariant, referenceAssertionSatisfaction_disj] at invariant
  rcases invariant with zero | one | two | three
  · exact False.elim (false_guard_below_three env world 0 (by decide) zero pre.2.2)
  · exact False.elim (false_guard_below_three env world 1 (by decide) one pre.2.2)
  · exact False.elim (false_guard_below_three env world 2 (by decide) two pre.2.2)
  · exact ⟨pre.1, three⟩

/-- Meaningful universal loop validity is proved before reconstruction. The
explicit finite invariant establishes the bound and the defined-false exit. -/
theorem loop_semantically_valid : ValidTriple E.context (S.stateAssertion Γ 0 0)
    E.terminatingLoop.quote (S.stateAssertion Γ 3 0) :=
  rule_consequence_sound E.context (S.state_entails_loop 0 (Or.inl rfl))
    (rule_loop_sound E.context loop_body_semantically_preserves) loop_exit_entails_three

 theorem loop_reconstructed : Derivation E.context (S.stateAssertion Γ 0 0)
    E.terminatingLoop.quote (S.stateAssertion Γ 3 0) :=
  relative_completeness E.context _ _ _ (by trivial) loop_semantically_valid

 def canonicalLoopInvariant (Γ : List GhostSort) : Assertion Γ :=
  weakestLiberalAssertion E.terminatingLoop.quote (S.stateAssertion Γ 3 0)

 theorem canonical_loop_inhabited (env : GhostEnv Bool Primitive Γ) (bit : Bool) :
    satisfies E.interpretation E.context.model env (E.sampledWorld bit)
      (canonicalLoopInvariant Γ) := by
  apply (weakest_liberal_assertion_represents E.context env (E.sampledWorld bit)
    E.terminatingLoop.quote (S.stateAssertion Γ 3 0) (E.sampled_admitted bit)).mpr
  intro after execution
  exact loop_semantically_valid env _ after (S.sampled_state env bit) execution

 theorem canonical_loop_preserves : Derivation E.context
    (.conj (canonicalLoopInvariant Γ)
      (guardAssertion (.intLess (.read E.x) (.integer 3)) true))
    E.incrementX.quote (canonicalLoopInvariant Γ) := by
  apply relative_completeness E.context _ _ _ (by trivial)
  intro env before after pre execution
  apply (weakest_liberal_assertion_represents E.context env after E.terminatingLoop.quote
    (S.stateAssertion Γ 3 0) (exec_admitted execution)).mpr
  have outcomes := (weakest_liberal_assertion_represents E.context env before
    E.terminatingLoop.quote (S.stateAssertion Γ 3 0) pre.1).mp ⟨pre.1, pre.2.1⟩
  have enabled := (reference_guardAssertion_iff E.context env before
    (.intLess (.read E.x) (.integer 3)) true).mp pre.2.2
  exact wlp_loop_body enabled outcomes after execution

 theorem canonical_loop_exit : AssertionEntails E.context
    (.conj (canonicalLoopInvariant Γ)
      (guardAssertion (.intLess (.read E.x) (.integer 3)) false))
    (S.stateAssertion Γ 3 0) := by
  intro env before pre
  have outcomes := (weakest_liberal_assertion_represents E.context env before
    E.terminatingLoop.quote (S.stateAssertion Γ 3 0) pre.1).mp ⟨pre.1, pre.2.1⟩
  have enabled := (reference_guardAssertion_iff E.context env before
    (.intLess (.read E.x) (.integer 3)) false).mp pre.2.2
  exact wlp_loop_exit E.context env before _ _ _ (by trivial) pre.1 enabled outcomes

/-- Rich parallel validity is reconstructed from independent local semantics;
its post includes outer ghosts, nested K, a rigid world and a rigid trace. -/
theorem parallel_semantically_valid :
    ValidTriple E.context S.parallelPre E.parallel.quote S.parallelPost :=
  rule_parallel_sound E.context E.good_ni
    (rule_seq_sound E.context
      (primitive_preimage_valid E.context (.assign E.x (.intAdd (.read E.x) (.integer 1)))
        S.parallelIntermediate)
      (primitive_preimage_valid E.context (.assign E.y (.intAdd (.read E.y) (.integer 2)))
        S.parallelPost))

 theorem parallel_reconstructed :
    Derivation E.context S.parallelPre E.parallel.quote S.parallelPost :=
  relative_completeness E.context _ _ _ ⟨trivial, trivial, E.good_ni⟩ parallel_semantically_valid

 def divergentLoop : Program := .loop (.boolean true) Program.skip
 def falsePost (Γ : List GhostSort) : Assertion Γ := .modal ControlLogSyntax.falseFormula

 theorem divergent_loop_precondition (env : GhostEnv Bool Primitive Γ) (bit : Bool) :
    satisfies E.interpretation E.context.model env (E.sampledWorld bit)
      (weakestLiberalAssertion divergentLoop (falsePost Γ)) :=
  (weakest_liberal_assertion_represents E.context env _ _ _ (E.sampled_admitted bit)).mpr
    (wlp_true_loop E.context env _ Program.skip (falsePost Γ))

 theorem divergent_loop_reconstructed :
    Derivation E.context (weakestLiberalAssertion divergentLoop (falsePost Γ))
      divergentLoop (falsePost Γ) :=
  weakest_liberal_assertion_derivation E.context divergentLoop (by trivial) (falsePost Γ)

 theorem incompatible_parallel_vacuously_valid :
    ValidTriple E.context (S.stateAssertion Γ 0 0) E.badParallel.quote (falsePost Γ) := by
  apply malformed_program_vacuously_valid
  intro wellFormed
  exact E.bad_ni wellFormed.2.2

 theorem incompatible_parallel_not_reconstructed :
    ¬ Derivation E.context (S.stateAssertion Γ 0 0) E.badParallel.quote (falsePost Γ) := by
  apply malformed_program_not_derivable
  intro wellFormed
  exact E.bad_ni wellFormed.2.2

end

/-- Counts are computed from real scheduler events: guard transitions do not
append program states, whereas each primitive transition appends exactly one. -/
def transitionCounts (count : Nat) : List BHLExecution.Event → List Nat
  | [] => []
  | event :: rest =>
      let next := count + if event.emission.isSome then 1 else 0
      next :: transitionCounts next rest

def loopCounts := transitionCounts 0 BHLExecution.loopEvents
 def leftCounts := transitionCounts 0 BHLExecution.leftEvents
 def rightCounts := transitionCounts 0 BHLExecution.rightEvents

 theorem loop_counts : loopCounts = [0, 1, 1, 2, 2, 3, 3] := rfl
 theorem left_counts : leftCounts = [1, 2] := rfl
 theorem right_counts : rightCounts = [1, 2] := rfl

end Lara.Examples.BHLCompleteness
