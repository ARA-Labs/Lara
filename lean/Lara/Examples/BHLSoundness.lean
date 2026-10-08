import Lara.BHL.Soundness
import Lara.BHL.StatisticalRules
import Lara.Examples.BHLExecution
import Lara.Examples.BHLSoundnessDataset
import Lara.Examples.BHLSoundnessScience
import Mathlib.Tactic

namespace Lara.Examples.BHLSoundness

open Lara.BHL

noncomputable section

variable {Γ : List GhostSort}

/-- The complete ledger, rather than a named counter, is part of each state assertion. -/
def stateAssertion (Γ : List GhostSort) (n m : Int) : Assertion Γ :=
  .modal (.conj (.atom (.equal (.valueRead .ambient BHLExecution.x) (.integer n)))
    (.conj (.atom (.equal (.valueRead .ambient BHLExecution.y) (.integer m)))
      (.conj (.atom (.equal (.valueRead .ambient BHLExecution.oldReport) (.rational (7 / 11))))
        (.atom (.equal (.historyOf .ambient) .historyEmpty)))))

 theorem stateAssertion_iff (env : GhostEnv Bool Primitive Γ)
    (world : World Bool Primitive) (n m : Int) :
    referenceAssertionSatisfaction BHLExecution.interpretation BHLExecution.context.model env world
      (stateAssertion Γ n m) ↔
    world.current.memory.read BHLExecution.x = some n ∧ world.current.memory.read BHLExecution.y = some m ∧
      world.current.memory.read BHLExecution.oldReport = some ((7 / 11 : ℚ) : ℝ) ∧
      world.current.history = 0 := by
  simp [stateAssertion, referenceAssertionSatisfaction, referenceModalSatisfaction,
    atomMeaning, evalTerm, semanticView, State.visible, Memory.read,
    Memory.assemble, Memory.observable, BHLExecution.x, BHLExecution.y, BHLExecution.oldReport,
    eq_comm]
  constructor <;> rintro ⟨hx, hy, hr, hh⟩ <;>
    exact ⟨hx.symm, hy.symm, hr.symm, hh.symm⟩

/-- This lemma is used backwards only after constructing an actual admitted
command step; synthetic view membership is never assumed. -/
theorem preimage_step_iff {D : Type} [MeasurableSpace D] {ctx : ProgramContext D}
    (env : GhostEnv D Primitive Γ) {before after : World D Primitive}
    {primitive : Primitive} (initial : Admitted ctx.model.dynamics before)
    (step : Step ctx (some (.command primitive)) before none after) (post : Assertion Γ) :
    satisfies ctx.interpretation ctx.model env before (primitive.preimage post) ↔
      satisfies ctx.interpretation ctx.model env after post :=
  primitive_preimage_successor_iff ctx env initial step post
theorem derivation_preimage_mono {D : Type} [MeasurableSpace D]
    {ctx : ProgramContext D} {first second : Assertion Γ} {primitive : Primitive}
    (entails : AssertionEntails ctx first second) :
    AssertionEntails ctx (primitive.preimage first) (primitive.preimage second) := by
  intro env world h
  refine ⟨h.1, ?_⟩
  have liberal := h.2
  rw [Primitive.preimage, reference_liberalPreimage_iff] at liberal ⊢
  intro view evaluated
  have firstSat := liberal view evaluated
  rcases firstSat.1 with ⟨⟨representative, admitted⟩, rfl⟩
  have referenceFirst := (satisfies_view_iff _ _ env representative admitted first).2 firstSat
  exact (satisfies_view_iff _ _ env representative admitted second).1
    (entails env representative referenceFirst)

theorem preimage_exec_iff {D : Type} [MeasurableSpace D] {ctx : ProgramContext D}
    (env : GhostEnv D Primitive Γ) {before after : World D Primitive}
    {primitive : Primitive} (run : executes ctx (.command primitive) before after)
    (post : Assertion Γ) :
    satisfies ctx.interpretation ctx.model env before (primitive.preimage post) ↔
      satisfies ctx.interpretation ctx.model env after post := by
  obtain ⟨_, initial, n, steps⟩ := run
  obtain ⟨_, visible, delta, enabled, equality⟩ := Steps.command_iff.mp steps
  subst after
  exact preimage_step_iff env initial (.command enabled) post

 theorem sampled_state (env : GhostEnv Bool Primitive Γ) (bit : Bool) :
    satisfies BHLExecution.interpretation BHLExecution.context.model env (BHLExecution.sampledWorld bit)
      (stateAssertion Γ 0 0) := by
  refine ⟨BHLExecution.sampled_admitted bit, (stateAssertion_iff env _ _ _).2 ?_⟩
  simp [BHLExecution.sampledWorld, BHLExecution.startWorld, BHLExecution.initialSnapshot, BHLExecution.Snapshot.memory,
    Memory.read, Memory.assemble, BHLExecution.x, BHLExecution.y, BHLExecution.oldReport]

 theorem incrementX_entails (n m : Int) :
    AssertionEntails BHLExecution.context (stateAssertion Γ n m)
      ((Primitive.assign BHLExecution.x (.intAdd (.read BHLExecution.x) (.integer 1))).preimage
        (stateAssertion Γ (n + 1) m)) := by
  intro env before pre
  obtain ⟨hx, hy, old, ledger⟩ := (stateAssertion_iff env before n m).1 pre.2
  simp only [Memory.read] at hx hy old
  let visible := (VisibleWrite.value BHLExecution.x (n + 1)).apply before.current.visible
  let after := before.extend (commandState before.current
    (.assign BHLExecution.x (.intAdd (.read BHLExecution.x) (.integer 1))) visible 0)
  have enabled : primitiveEffect BHLExecution.context.interpretation
      (.assign BHLExecution.x (.intAdd (.read BHLExecution.x) (.integer 1))) before.current.visible =
        some (visible, 0) := by
    simp [primitiveEffect_assign, evalProgramExpr, State.visible, Memory.observable,
      hx, visible]
  have step : Step BHLExecution.context
      (some (.command (.assign BHLExecution.x (.intAdd (.read BHLExecution.x) (.integer 1))))) before none after :=
    .command enabled
  apply (preimage_step_iff env pre.1 step _).2
  refine ⟨step.admitted pre.1, (stateAssertion_iff env after _ _).2 ?_⟩
  simp only [after, World.extend_current]
  simp [visible, commandState, VisibleWrite.apply, State.visible,
    Memory.read, Memory.assemble, Memory.update, Memory.observable,
    BHLExecution.x, BHLExecution.y, BHLExecution.oldReport] at hy old ⊢
  exact ⟨hy, old, ledger⟩

 theorem incrementY_entails (n m : Int) :
    AssertionEntails BHLExecution.context (stateAssertion Γ n m)
      ((Primitive.assign BHLExecution.y (.intAdd (.read BHLExecution.y) (.integer 2))).preimage
        (stateAssertion Γ n (m + 2))) := by
  intro env before pre
  obtain ⟨hx, hy, old, ledger⟩ := (stateAssertion_iff env before n m).1 pre.2
  simp only [Memory.read] at hx hy old
  let visible := (VisibleWrite.value BHLExecution.y (m + 2)).apply before.current.visible
  let after := before.extend (commandState before.current
    (.assign BHLExecution.y (.intAdd (.read BHLExecution.y) (.integer 2))) visible 0)
  have enabled : primitiveEffect BHLExecution.context.interpretation
      (.assign BHLExecution.y (.intAdd (.read BHLExecution.y) (.integer 2))) before.current.visible =
        some (visible, 0) := by
    simp [primitiveEffect_assign, evalProgramExpr, State.visible, Memory.observable,
      hy, visible]
  have step : Step BHLExecution.context
      (some (.command (.assign BHLExecution.y (.intAdd (.read BHLExecution.y) (.integer 2))))) before none after :=
    .command enabled
  apply (preimage_step_iff env pre.1 step _).2
  refine ⟨step.admitted pre.1, (stateAssertion_iff env after _ _).2 ?_⟩
  simp only [after, World.extend_current]
  simp [visible, commandState, VisibleWrite.apply, State.visible,
    Memory.read, Memory.assemble, Memory.update, Memory.observable,
    BHLExecution.x, BHLExecution.y, BHLExecution.oldReport] at hx old ⊢
  exact ⟨hx, old, ledger⟩

 theorem incrementX_derivation (n m : Int) :
    Derivation BHLExecution.context (stateAssertion Γ n m) BHLExecution.incrementX.quote
      (stateAssertion Γ (n + 1) m) :=
  .consequence (incrementX_entails n m)
    (.assign (.assign BHLExecution.x (.intAdd (.read BHLExecution.x) (.integer 1)))
      (Primitive.assign_isPureAssignment _ _) _) (AssertionEntails.refl _ _)

 theorem incrementY_derivation (n m : Int) :
    Derivation BHLExecution.context (stateAssertion Γ n m) BHLExecution.incrementY.quote
      (stateAssertion Γ n (m + 2)) :=
  .consequence (incrementY_entails n m)
    (.assign (.assign BHLExecution.y (.intAdd (.read BHLExecution.y) (.integer 2)))
      (Primitive.assign_isPureAssignment _ _) _) (AssertionEntails.refl _ _)

 theorem skip_derivation : Derivation BHLExecution.context (stateAssertion Γ 0 0)
    Program.skip (stateAssertion Γ 0 0) := .skip _

def skipEvents : List BHLExecution.Event := [⟨some .skip, BHLExecution.initialSnapshot⟩]

 theorem skip_computes : BHLExecution.scheduled [true] (some (.command .skip)) BHLExecution.initialSnapshot =
    some (none, BHLExecution.initialSnapshot, skipEvents) := rfl

 theorem skip_executes (bit : Bool) : executes BHLExecution.context Program.skip
    (BHLExecution.sampledWorld bit) (BHLExecution.eventsWorld (BHLExecution.sampledWorld bit) skipEvents) :=
  ⟨trivial, BHLExecution.sampled_admitted bit, 1,
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _ (BHLExecution.sampled_reifies bit) skip_computes).1⟩

def incrementEvents : List BHLExecution.Event :=
  [⟨some (.assign BHLExecution.x (.add (.read BHLExecution.x) (.literal 1))), BHLExecution.afterX BHLExecution.initialSnapshot 1⟩]

 theorem increment_computes : BHLExecution.scheduled [true] (some BHLExecution.incrementX) BHLExecution.initialSnapshot =
    some (none, BHLExecution.afterX BHLExecution.initialSnapshot 1, incrementEvents) := rfl

def xOneWorld (bit : Bool) := BHLExecution.eventsWorld (BHLExecution.sampledWorld bit) incrementEvents

 theorem increment_executes (bit : Bool) : executes BHLExecution.context BHLExecution.incrementX.quote
    (BHLExecution.sampledWorld bit) (xOneWorld bit) :=
  ⟨trivial, BHLExecution.sampled_admitted bit, 1,
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _ (BHLExecution.sampled_reifies bit) increment_computes).1⟩

 theorem increment_inhabited :
    satisfies BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty (BHLExecution.sampledWorld false)
      (stateAssertion [] 0 0) ∧
    executes BHLExecution.context BHLExecution.incrementX.quote (BHLExecution.sampledWorld false) (xOneWorld false) ∧
    satisfies BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty (xOneWorld false)
      (stateAssertion [] 1 0) := by
  have initial := sampled_state GhostEnv.empty false
  exact ⟨initial, increment_executes false,
    derivation_sound (incrementX_derivation 0 0) _ _ _ initial (increment_executes false)⟩

 theorem entails_disj_left (left right : Assertion Γ) :
    AssertionEntails BHLExecution.context left (left.disj right) := by
  intro env world h
  exact ⟨h.1, (referenceAssertionSatisfaction_disj _ _ _ _ _ _).2 (Or.inl h.2)⟩

 theorem entails_disj_right (left right : Assertion Γ) :
    AssertionEntails BHLExecution.context right (left.disj right) := by
  intro env world h
  exact ⟨h.1, (referenceAssertionSatisfaction_disj _ _ _ _ _ _).2 (Or.inr h.2)⟩

def branchPre (Γ : List GhostSort) := (stateAssertion Γ 0 0).disj (stateAssertion Γ 1 0)
def branchPost (Γ : List GhostSort) := (stateAssertion Γ 1 0).disj (stateAssertion Γ 1 2)
def branchGuard : ProgramExpr .boolean := .intLess (.read BHLExecution.x) (.integer 1)
def variableBranch : BHLExecution.Source := .ite (.less (.read BHLExecution.x) (.literal 1)) BHLExecution.incrementX BHLExecution.incrementY

/-- The evaluated integer comparison reads exactly the world's observable x. -/
theorem eval_intLess_read (world : World Bool Primitive) (bound : Int) :
    evalProgramExpr BHLExecution.interpretation world.current.visible (.intLess (.read BHLExecution.x) (.integer bound)) =
      (world.current.memory.read BHLExecution.x).map (fun n => decide (n < bound)) := by
  change ((world.current.memory.read BHLExecution.x).bind
    (fun n => some (decide (n < bound)))) =
      (world.current.memory.read BHLExecution.x).map (fun n => decide (n < bound))
  cases world.current.memory.read BHLExecution.x <;> rfl

 theorem guard_less_iff (env : GhostEnv Bool Primitive Γ) (world : World Bool Primitive)
    (bound : Int) (choice : Bool) :
    referenceAssertionSatisfaction BHLExecution.interpretation BHLExecution.context.model env world
      (guardAssertion (.intLess (.read BHLExecution.x) (.integer bound)) choice) ↔
    ∃ n, world.current.memory.read BHLExecution.x = some n ∧ decide (n < bound) = choice := by
  change referenceAssertionSatisfaction BHLExecution.context.interpretation
    BHLExecution.context.model env world
      (guardAssertion (.intLess (.read BHLExecution.x) (.integer bound)) choice) ↔ _
  rw [reference_guardAssertion_iff BHLExecution.context]
  change evalProgramExpr BHLExecution.interpretation world.current.visible
    (.intLess (.read BHLExecution.x) (.integer bound)) = some choice ↔ _
  rw [eval_intLess_read]
  cases h : world.current.memory.read BHLExecution.x with
  | none => simp
  | some n => simp

 theorem branch_yes_entails : AssertionEntails BHLExecution.context
    (.conj (branchPre Γ) (guardAssertion branchGuard true)) (stateAssertion Γ 0 0) := by
  intro env world h
  rcases (referenceAssertionSatisfaction_disj _ _ _ _ _ _).1 h.2.1 with zero | one
  · exact ⟨h.1, zero⟩
  · obtain ⟨n, hn, less⟩ := (guard_less_iff env world 1 true).1 h.2.2
    have hx := ((stateAssertion_iff env world 1 0).1 one).1
    rw [hx] at hn
    cases Option.some.inj hn
    simp at less

 theorem branch_no_entails : AssertionEntails BHLExecution.context
    (.conj (branchPre Γ) (guardAssertion branchGuard false)) (stateAssertion Γ 1 0) := by
  intro env world h
  rcases (referenceAssertionSatisfaction_disj _ _ _ _ _ _).1 h.2.1 with zero | one
  · obtain ⟨n, hn, less⟩ := (guard_less_iff env world 1 false).1 h.2.2
    have hx := ((stateAssertion_iff env world 0 0).1 zero).1
    rw [hx] at hn
    cases Option.some.inj hn
    simp at less
  · exact ⟨h.1, one⟩

 theorem branch_derivation : Derivation BHLExecution.context (branchPre Γ)
    variableBranch.quote (branchPost Γ) := by
  exact .ite
    (.consequence branch_yes_entails (incrementX_derivation 0 0)
      (entails_disj_left _ _))
    (.consequence branch_no_entails (incrementY_derivation 1 0)
      (entails_disj_right _ _))

def variableTrueEvents := BHLExecution.trueBranchEvents
def variableFalseFinal := BHLExecution.afterY (BHLExecution.afterX BHLExecution.initialSnapshot 1) 2
def variableFalseEvents : List BHLExecution.Event :=
  [⟨none, BHLExecution.afterX BHLExecution.initialSnapshot 1⟩,
    ⟨some (.assign BHLExecution.y (.add (.read BHLExecution.y) (.literal 2))), variableFalseFinal⟩]

 theorem variable_true_computes :
    BHLExecution.scheduled [true, true] (some variableBranch) BHLExecution.initialSnapshot =
      some (none, BHLExecution.afterX BHLExecution.initialSnapshot 1, variableTrueEvents) := rfl
 theorem variable_false_computes :
    BHLExecution.scheduled [true, true] (some variableBranch) (BHLExecution.afterX BHLExecution.initialSnapshot 1) =
      some (none, variableFalseFinal, variableFalseEvents) := rfl

 theorem variable_true_executes (bit : Bool) : executes BHLExecution.context variableBranch.quote
    (BHLExecution.sampledWorld bit) (BHLExecution.eventsWorld (BHLExecution.sampledWorld bit) variableTrueEvents) :=
  ⟨⟨trivial, trivial⟩, BHLExecution.sampled_admitted bit, 2,
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _ (BHLExecution.sampled_reifies bit)
      variable_true_computes).1⟩
 theorem variable_false_executes (bit : Bool) : executes BHLExecution.context variableBranch.quote
    (xOneWorld bit) (BHLExecution.eventsWorld (xOneWorld bit) variableFalseEvents) :=
  ⟨⟨trivial, trivial⟩, exec_admitted (increment_executes bit), 2,
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _
      (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _ (BHLExecution.sampled_reifies bit) increment_computes).2
      variable_false_computes).1⟩

 theorem both_branch_premises_inhabited :
    satisfies BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty (BHLExecution.sampledWorld false)
      (.conj (branchPre []) (guardAssertion branchGuard true)) ∧
    satisfies BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty (xOneWorld false)
      (.conj (branchPre []) (guardAssertion branchGuard false)) := by
  have zero := sampled_state GhostEnv.empty false
  have one := increment_inhabited.2.2
  refine ⟨⟨zero.1, (entails_disj_left _ _ _ _ zero).2, ?_⟩,
    ⟨one.1, (entails_disj_right _ _ _ _ one).2, ?_⟩⟩
  · apply (guard_less_iff _ _ 1 true).2
    exact ⟨0, ((stateAssertion_iff _ _ _ _).1 zero.2).1, rfl⟩
  · apply (guard_less_iff _ _ 1 false).2
    exact ⟨1, ((stateAssertion_iff _ _ _ _).1 one.2).1, rfl⟩

/-- A finite invariant for the actual three-iteration loop. It does not assert
termination of other programs or add a ranking premise to the loop rule. -/
def loopInvariant (Γ : List GhostSort) : Assertion Γ :=
  (stateAssertion Γ 0 0).disj ((stateAssertion Γ 1 0).disj
    ((stateAssertion Γ 2 0).disj (stateAssertion Γ 3 0)))

 theorem state_entails_loop (n : Int) (hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) :
    AssertionEntails BHLExecution.context (stateAssertion Γ n 0) (loopInvariant Γ) := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact entails_disj_left _ _
  · exact (entails_disj_left _ _).trans (entails_disj_right _ _)
  · exact ((entails_disj_left _ _).trans (entails_disj_right _ _)).trans
      (entails_disj_right _ _)
  · exact ((entails_disj_right _ _).trans (entails_disj_right _ _)).trans
      (entails_disj_right _ _)

 theorem loop_body_entails : AssertionEntails BHLExecution.context
    (.conj (loopInvariant Γ) (guardAssertion (.intLess (.read BHLExecution.x) (.integer 3)) true))
    ((Primitive.assign BHLExecution.x (.intAdd (.read BHLExecution.x) (.integer 1))).preimage
      (loopInvariant Γ)) := by
  intro env before h
  have invariant := h.2.1
  simp only [loopInvariant, referenceAssertionSatisfaction_disj] at invariant
  rcases invariant with zero | one | two | three
  · exact derivation_preimage_mono (state_entails_loop 1 (Or.inr (Or.inl rfl))) env before
      (incrementX_entails 0 0 env before ⟨h.1, zero⟩)
  · exact derivation_preimage_mono (state_entails_loop 2 (Or.inr (Or.inr (Or.inl rfl)))) env before
      (incrementX_entails 1 0 env before ⟨h.1, one⟩)
  · exact derivation_preimage_mono (state_entails_loop 3 (Or.inr (Or.inr (Or.inr rfl)))) env before
      (incrementX_entails 2 0 env before ⟨h.1, two⟩)
  · obtain ⟨n, hn, less⟩ := (guard_less_iff env before 3 true).1 h.2.2
    have hx := ((stateAssertion_iff env before 3 0).1 three).1
    rw [hx] at hn
    cases Option.some.inj hn
    simp at less

 theorem loop_derivation : Derivation BHLExecution.context (loopInvariant Γ)
    BHLExecution.terminatingLoop.quote (.conj (loopInvariant Γ)
      (guardAssertion (.intLess (.read BHLExecution.x) (.integer 3)) false)) :=
  .loop (.consequence loop_body_entails
    (.assign (.assign BHLExecution.x (.intAdd (.read BHLExecution.x) (.integer 1)))
      (Primitive.assign_isPureAssignment _ _) _) (AssertionEntails.refl _ _))

 theorem loop_inhabited :
    satisfies BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty (BHLExecution.sampledWorld false)
      (loopInvariant []) ∧
    executes BHLExecution.context BHLExecution.terminatingLoop.quote (BHLExecution.sampledWorld false)
      (BHLExecution.eventsWorld (BHLExecution.sampledWorld false) BHLExecution.loopEvents) ∧
    satisfies BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty
      (BHLExecution.eventsWorld (BHLExecution.sampledWorld false) BHLExecution.loopEvents)
      (.conj (loopInvariant [])
        (guardAssertion (.intLess (.read BHLExecution.x) (.integer 3)) false)) := by
  have initial := state_entails_loop 0 (Or.inl rfl) _ _ (sampled_state GhostEnv.empty false)
  exact ⟨initial, BHLExecution.loop_executes false,
    derivation_sound loop_derivation _ _ _ initial (BHLExecution.loop_executes false)⟩

/-- A reified snapshot determines the semantic view's visible/history fields. -/
theorem semanticView_eq_of_reifies (world : World Bool Primitive) (state : BHLExecution.Snapshot)
    (r : BHLExecution.Reifies world state) :
    semanticView BHLExecution.context.model.dynamics world =
      ⟨state.visible, state.ledger, world.current.memory.hidden,
        compatibleHidden BHLExecution.context.model.dynamics world, world.samplingProvenance⟩ := by
  obtain ⟨visible, history⟩ := r
  simp only [semanticView, visible, history]

def leafTest (Γ : List GhostSort) (data : DatasetId) (test : TestId) : TestExpression Γ :=
  .leaf BHLBelief.hypothesisId (.datasetRead .ambient data) test BHLBelief.populationId

def reportPost (Γ : List GhostSort) : Assertion Γ :=
  .conj (stateAssertion Γ 0 0)
    (.modal (.atom (.equal (.valueRead .ambient BHLExecution.report)
      (.pvalue (leafTest Γ BHLExecution.dataId BHLBelief.correctId)))))

def reportPre (Γ : List GhostSort) :=
  (Primitive.assign BHLExecution.report (.pvalue BHLBelief.hypothesisId (.read BHLExecution.dataId)
    BHLBelief.correctId BHLBelief.populationId)).preimage (reportPost Γ)

 theorem report_only_derivation : Derivation BHLExecution.context (reportPre Γ)
    BHLExecution.reportOnly.quote (reportPost Γ) :=
  .assign (.assign BHLExecution.report (.pvalue BHLBelief.hypothesisId
    (.read BHLExecution.dataId) BHLBelief.correctId BHLBelief.populationId))
    (Primitive.assign_isPureAssignment _ _) _

 theorem report_only_executes (bit : Bool) : executes BHLExecution.context BHLExecution.reportOnly.quote
    (BHLExecution.sampledWorld bit) (BHLExecution.eventsWorld (BHLExecution.sampledWorld bit) BHLExecution.reportingEvents) :=
  ⟨trivial, BHLExecution.sampled_admitted bit, 1,
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _ (BHLExecution.sampled_reifies bit)
      BHLExecution.reporting_computes).1⟩

 theorem report_only_post (env : GhostEnv Bool Primitive Γ) (bit : Bool) :
    satisfies BHLExecution.interpretation BHLExecution.context.model env
      (BHLExecution.eventsWorld (BHLExecution.sampledWorld bit) BHLExecution.reportingEvents) (reportPost Γ) := by
  refine ⟨exec_admitted (report_only_executes bit), ?_⟩
  have reifies : BHLExecution.Reifies (BHLExecution.eventsWorld (BHLExecution.sampledWorld bit) BHLExecution.reportingEvents)
      BHLExecution.reportingFinal :=
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _
      (BHLExecution.sampled_reifies bit) BHLExecution.reporting_computes).2
  rw [reference_view_assertion_correspondence, semanticView_eq_of_reifies _ _ reifies]
  simp [reportPost, stateAssertion, leafTest, viewAssertionSatisfaction, viewModalSatisfaction,
    atomMeaning, evalTerm, evalNumericalEvent, BHLExecution.interpretation, BHLExecution.reportingFinal,
    BHLExecution.initialSnapshot, BHLExecution.Snapshot.visible, BHLExecution.Snapshot.memory, Memory.read,
    Memory.assemble, Function.update, BHLExecution.x, BHLExecution.y, BHLExecution.report, BHLExecution.oldReport]

 theorem report_only_pre_inhabited :
    satisfies BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty (BHLExecution.sampledWorld false)
      (reportPre []) :=
  (preimage_exec_iff GhostEnv.empty (report_only_executes false) _).2
    (report_only_post GhostEnv.empty false)

def pairHistory (Γ : List GhostSort) : AssertionTerm Γ .history :=
  .historyAdd (.historySingleton (.datasetRead .ambient BHLExecution.dataId) BHLBelief.correctId)
    (.historySingleton (.datasetRead .ambient BHLExecution.aliasId) BHLBelief.correctId)

def twoTestPost (Γ : List GhostSort) : Assertion Γ := .modal
  (.conj (.atom (.equal (.valueRead .ambient BHLExecution.oldReport) (.rational (7 / 11))))
    (.conj (.atom (.equal (.valueRead .ambient BHLExecution.report) (.rational 1)))
      (.conj (.atom (.equal (.historyOf .ambient) (pairHistory Γ)))
        (.conj (.atom (.equal
          (.historyCount (.historyOf .ambient) (.datasetRead .ambient BHLExecution.dataId) BHLBelief.correctId)
          (.integer 2)))
          (.atom (.equal
            (.historyCount (.historyOf .ambient) (.datasetRead .ambient BHLExecution.aliasId) BHLBelief.correctId)
            (.integer 2)))))))

def secondTestPre (Γ : List GhostSort) := (Primitive.test BHLExecution.report BHLBelief.hypothesisId
  (.read BHLExecution.aliasId) BHLBelief.correctId BHLBelief.populationId).preimage (twoTestPost Γ)
def twoTestPre (Γ : List GhostSort) := (Primitive.test BHLExecution.report BHLBelief.hypothesisId
  (.read BHLExecution.dataId) BHLBelief.correctId BHLBelief.populationId).preimage (secondTestPre Γ)
def twoTests : BHLExecution.Source := .seq BHLExecution.testData BHLExecution.testAlias
def firstEvents : List BHLExecution.Event := [⟨some (.test BHLExecution.report BHLExecution.dataId BHLBelief.correctId), BHLExecution.testedSnapshot⟩]
def secondSnapshot : BHLExecution.Snapshot :=
  {BHLExecution.testedSnapshot with
    rationals := Function.update BHLExecution.testedSnapshot.rationals BHLExecution.report.id (some 1)
    ledger := BHLExecution.testedSnapshot.ledger + {(false, BHLBelief.correctId)}}
def secondEvents : List BHLExecution.Event := [⟨some (.test BHLExecution.report BHLExecution.aliasId BHLBelief.correctId), secondSnapshot⟩]
def firstWorld (bit : Bool) := BHLExecution.eventsWorld (BHLExecution.sampledWorld bit) firstEvents
def secondWorld (bit : Bool) := BHLExecution.eventsWorld (firstWorld bit) secondEvents

 theorem first_computes : BHLExecution.scheduled [true] (some BHLExecution.testData) BHLExecution.initialSnapshot =
    some (none, BHLExecution.testedSnapshot, firstEvents) := rfl
 theorem second_computes : BHLExecution.scheduled [true] (some BHLExecution.testAlias) BHLExecution.testedSnapshot =
    some (none, secondSnapshot, secondEvents) := rfl
 theorem first_executes (bit : Bool) : executes BHLExecution.context BHLExecution.testData.quote
    (BHLExecution.sampledWorld bit) (firstWorld bit) :=
  ⟨trivial, BHLExecution.sampled_admitted bit, 1,
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _ (BHLExecution.sampled_reifies bit) first_computes).1⟩
 theorem second_executes (bit : Bool) : executes BHLExecution.context BHLExecution.testAlias.quote
    (firstWorld bit) (secondWorld bit) :=
  ⟨trivial, exec_admitted (first_executes bit), 1,
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _
      (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _ (BHLExecution.sampled_reifies bit) first_computes).2
      second_computes).1⟩

 theorem two_tests_derivation : Derivation BHLExecution.context (twoTestPre Γ)
    twoTests.quote (twoTestPost Γ) :=
  .seq (.test _ _ _ _ _ (secondTestPre Γ)) (.test _ _ _ _ _ (twoTestPost Γ))

 theorem two_tests_executes (bit : Bool) : executes BHLExecution.context twoTests.quote
    (BHLExecution.sampledWorld bit) (secondWorld bit) :=
  exec_seq_iff.mpr ⟨firstWorld bit, first_executes bit, second_executes bit⟩

 theorem two_tests_post (env : GhostEnv Bool Primitive Γ) (bit : Bool) :
    satisfies BHLExecution.interpretation BHLExecution.context.model env (secondWorld bit) (twoTestPost Γ) := by
  refine ⟨exec_admitted (two_tests_executes bit), ?_⟩
  have reifies : BHLExecution.Reifies (secondWorld bit) secondSnapshot :=
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _
      (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _ (BHLExecution.sampled_reifies bit) first_computes).2
      second_computes).2
  unfold twoTestPost referenceAssertionSatisfaction
  rw [reference_view_modal_correspondence, semanticView_eq_of_reifies _ _ reifies]
  simp [pairHistory, viewModalSatisfaction,
    atomMeaning, evalTerm, secondSnapshot, BHLExecution.testedSnapshot, BHLExecution.initialSnapshot,
    BHLExecution.Snapshot.visible, BHLExecution.Snapshot.memory, Memory.read, Memory.assemble,
    History.count, BHLExecution.report, BHLExecution.oldReport, BHLExecution.dataId, BHLExecution.aliasId,
    BHLBelief.correctId, Function.update]

 theorem two_tests_pre_inhabited :
    satisfies BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty (BHLExecution.sampledWorld false)
      (twoTestPre []) :=
  (preimage_exec_iff GhostEnv.empty (first_executes false) _).2
    ((preimage_exec_iff GhostEnv.empty (second_executes false) _).2
      (two_tests_post GhostEnv.empty false))

def parallelΓ : List GhostSort := [.value .integer, .world, .trace, .value .real]
def parallelEnv : GhostEnv Bool Primitive parallelΓ :=
  GhostEnv.push (sort := .value .integer) (1 : Int)
    (GhostEnv.push (sort := .world) (BHLExecution.sampledWorld false)
      (GhostEnv.push (sort := .trace) (BHLExecution.sampledWorld false).trace
        (GhostEnv.push (sort := .value .real) (((7 / 11 : ℚ) : ℝ)) GhostEnv.empty)))

def rigidParallel : Assertion parallelΓ := .modal
  (.conj (.atom (.equal (.ghost (.bound .here)) (.integer 1)))
    (.conj (.atom (.equal
      (.traceLength (.worldTrace (.ghost (.bound (.there .here))))) (.integer 2)))
      (.conj (.atom (.equal
        (.traceLength (.ghost (.bound (.there (.there .here))))) (.integer 2)))
        (.atom (.equal (.valueRead .ambient BHLExecution.oldReport)
          (.ghost (.bound (.there (.there (.there .here))))))))))

def outerNestedKnowledge : Assertion parallelΓ :=
  .all (.value .boolean) (.modal (.knows (.atView .ambient (.knows
    (.conj (.atom (.equal (.valueRead .ambient BHLExecution.x)
      (.ghost (.bound (.there .here)))))
      (.atom (.equal (.ghost (.bound .here)) (.ghost (.bound .here)))))))))

def parallelPost : Assertion parallelΓ :=
  .conj (stateAssertion parallelΓ 1 2) (.conj rigidParallel outerNestedKnowledge)
def parallelIntermediate : Assertion parallelΓ :=
  (Primitive.assign BHLExecution.y (.intAdd (.read BHLExecution.y) (.integer 2))).preimage parallelPost
def parallelPre : Assertion parallelΓ :=
  (Primitive.assign BHLExecution.x (.intAdd (.read BHLExecution.x) (.integer 1))).preimage parallelIntermediate

 theorem parallel_derivation : Derivation BHLExecution.context parallelPre BHLExecution.parallel.quote parallelPost :=
  .parallel BHLExecution.good_ni
    (.seq
      (.assign (.assign BHLExecution.x (.intAdd (.read BHLExecution.x) (.integer 1)))
        (Primitive.assign_isPureAssignment _ _) _)
      (.assign (.assign BHLExecution.y (.intAdd (.read BHLExecution.y) (.integer 2)))
        (Primitive.assign_isPureAssignment _ _) _))

 theorem parallel_post_left : satisfies BHLExecution.interpretation BHLExecution.context.model parallelEnv
    (BHLExecution.leftWorld false) parallelPost := by
  have admitted := exec_admitted (BHLExecution.left_executes false)
  refine ⟨admitted, ?_⟩
  rw [reference_view_assertion_correspondence]
  have reifies : BHLExecution.Reifies (BHLExecution.leftWorld false) BHLExecution.leftFinal :=
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _ (BHLExecution.sampled_reifies false) BHLExecution.left_computes).2
  refine ⟨?_, ?_, ?_⟩
  · rw [semanticView_eq_of_reifies _ _ reifies]
    simp [stateAssertion, viewAssertionSatisfaction, viewModalSatisfaction, atomMeaning,
      evalTerm, BHLExecution.leftFinal, BHLExecution.afterX, BHLExecution.afterY, BHLExecution.initialSnapshot, BHLExecution.Snapshot.visible,
      BHLExecution.Snapshot.memory, Memory.read, Memory.assemble,
      Function.update, BHLExecution.x, BHLExecution.y, BHLExecution.oldReport]
  · rw [semanticView_eq_of_reifies _ _ reifies]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ⟨(1 : Int), rfl, rfl⟩
    · refine ⟨(2 : Int), ?_, rfl⟩
      change some (Int.ofNat (BHLExecution.sampledWorld false).trace.length) = some 2
      simp [World.trace, BHLExecution.sampledWorld, BHLExecution.startWorld,
        World.extend, World.start]
    · refine ⟨(2 : Int), ?_, rfl⟩
      change some (Int.ofNat (BHLExecution.sampledWorld false).trace.length) = some 2
      simp [World.trace, BHLExecution.sampledWorld, BHLExecution.startWorld,
        World.extend, World.start]
    · refine ⟨(((7 / 11 : ℚ) : ℝ)), ?_, rfl⟩
      simp [evalTerm, BHLExecution.leftFinal, BHLExecution.afterX, BHLExecution.afterY,
        BHLExecution.initialSnapshot, BHLExecution.Snapshot.visible,
        BHLExecution.Snapshot.memory, Memory.read, Memory.assemble,
        BHLExecution.x, BHLExecution.y, BHLExecution.oldReport]
  · intro value first member access
    refine ⟨first, rfl, member, ?_⟩
    intro second member2 secondAccess
    have nested := (BHLExecution.parallel_nested_knowledge
      (Γ := .value .boolean :: parallelΓ)
      (GhostEnv.push (sort := .value .boolean) value parallelEnv) false).2
    have xOne := nested first member access second member2 secondAccess
    refine ⟨?_, ?_⟩
    · obtain ⟨v, hread, hone⟩ := xOne
      exact ⟨v, hread, by
        change some (1 : Int) = some v
        exact hone⟩
    · exact ⟨value, rfl, rfl⟩

 theorem parallel_post_right : satisfies BHLExecution.interpretation BHLExecution.context.model parallelEnv
    (BHLExecution.rightWorld false) parallelPost := by
  apply (satisfies_view_iff _ _ _ _ (exec_admitted (BHLExecution.right_executes false)) parallelPost).2
  rw [← BHLExecution.parallel_all_assertions parallelEnv parallelPost false]
  exact (satisfies_view_iff _ _ _ _ (exec_admitted (BHLExecution.left_executes false))
    parallelPost).1 parallel_post_left

 theorem parallel_seq_computes :
    BHLExecution.scheduled [true, true] (some (.seq BHLExecution.incrementX BHLExecution.incrementY)) BHLExecution.initialSnapshot =
      some (none, BHLExecution.leftFinal, BHLExecution.leftEvents) := rfl

 theorem parallel_pre_inhabited :
    satisfies BHLExecution.interpretation BHLExecution.context.model parallelEnv (BHLExecution.sampledWorld false) parallelPre := by
  have sequential : executes BHLExecution.context (.seq BHLExecution.incrementX.quote BHLExecution.incrementY.quote)
      (BHLExecution.sampledWorld false) (BHLExecution.leftWorld false) :=
    ⟨⟨trivial, trivial⟩, BHLExecution.sampled_admitted false, 2,
      (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _ (BHLExecution.sampled_reifies false)
        parallel_seq_computes).1⟩
  obtain ⟨middle, first, second⟩ := exec_seq_iff.mp sequential
  exact (preimage_exec_iff parallelEnv first _).2
    ((preimage_exec_iff parallelEnv second _).2 parallel_post_left)

 theorem parallel_inhabited :
    satisfies BHLExecution.interpretation BHLExecution.context.model parallelEnv (BHLExecution.sampledWorld false) parallelPre ∧
    executes BHLExecution.context BHLExecution.parallel.quote (BHLExecution.sampledWorld false) (BHLExecution.leftWorld false) ∧
    executes BHLExecution.context BHLExecution.parallel.quote (BHLExecution.sampledWorld false) (BHLExecution.rightWorld false) ∧
    satisfies BHLExecution.interpretation BHLExecution.context.model parallelEnv (BHLExecution.leftWorld false) parallelPost ∧
    satisfies BHLExecution.interpretation BHLExecution.context.model parallelEnv (BHLExecution.rightWorld false) parallelPost ∧
    BHLExecution.scheduled [true, true] (some BHLExecution.parallel) BHLExecution.initialSnapshot =
        some (none, BHLExecution.leftFinal, BHLExecution.leftEvents) ∧
    BHLExecution.scheduled [false, true] (some BHLExecution.parallel) BHLExecution.initialSnapshot =
        some (none, BHLExecution.rightFinal, BHLExecution.rightEvents) :=
  ⟨parallel_pre_inhabited, BHLExecution.left_executes false, BHLExecution.right_executes false,
    parallel_post_left, parallel_post_right, BHLExecution.left_computes, BHLExecution.right_computes⟩

 theorem parallel_sound : ValidTriple BHLExecution.context parallelPre BHLExecution.parallel.quote parallelPost :=
  derivation_sound parallel_derivation

/-- The declared alternative of the two-bit fixture: the hidden parameter is true. -/
def alternativeFormula (Γ : List GhostSort) : ModalFormula Γ :=
  .atom (.hypothesis BHLBelief.hypothesisId (.hiddenOf .ambient))

/-- The single-test expression whose exact ledger the extra test destroys. -/
def counterTest (Γ : List GhostSort) : TestExpression Γ :=
  .leaf BHLBelief.hypothesisId (.datasetRead .ambient BHLExecution.dataId) BHLBelief.correctId BHLBelief.populationId

/-- A legal precondition that a correct single test actually establishes. -/
def badFormula (Γ : List GhostSort) : ModalFormula Γ :=
  .conj (modelRequirementsFormula (counterTest Γ))
    (.conj ((alternativeFormula Γ).possible)
      (.conj (.atom (.equal (.valueRead .ambient BHLExecution.oldReport) (.rational (7 / 11))))
        (.conj (.atom (.equal (.valueRead .ambient BHLExecution.report)
            (.pvalue (counterTest Γ))))
          (.conj (exactHistory (counterTest Γ))
            (statisticalBelief .equal (report Γ BHLExecution.report) (counterTest Γ)
              (alternativeFormula Γ))))))

def badPre (Γ : List GhostSort) : Assertion Γ := .modal (badFormula Γ)

/-- The extra audit test is an ordinary well-formed test, not a forbidden
interfering parallel program. -/
def extraFirstSnapshot : BHLExecution.Snapshot :=
  {BHLExecution.testedSnapshot with
    rationals := Function.update BHLExecution.testedSnapshot.rationals BHLExecution.report.id (some 1)
    ledger := BHLExecution.testedSnapshot.ledger + {(false, BHLBelief.extraId)}}

def extraFirstEvents : List BHLExecution.Event :=
  [⟨some (.test BHLExecution.report BHLExecution.dataId BHLBelief.extraId), extraFirstSnapshot⟩]

def afterExtraWorld (bit : Bool) : World Bool Primitive :=
  BHLExecution.eventsWorld (firstWorld bit) extraFirstEvents

 theorem extra_computes : BHLExecution.scheduled [true] (some BHLExecution.extraTest) BHLExecution.testedSnapshot =
    some (none, extraFirstSnapshot, extraFirstEvents) := rfl

 theorem first_ledger (bit : Bool) :
    (firstWorld bit).current.history = ({(false, BHLBelief.correctId)} : History Bool) := by
  have represented : BHLExecution.Reifies (firstWorld bit) BHLExecution.testedSnapshot :=
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _
      (BHLExecution.sampled_reifies bit) first_computes).2
  rw [represented.2]
  simp [BHLExecution.testedSnapshot, BHLExecution.initialSnapshot]

 theorem afterExtra_ledger (bit : Bool) :
    (afterExtraWorld bit).current.history =
      (firstWorld bit).current.history + {(false, BHLBelief.extraId)} := by
  have first : BHLExecution.Reifies (firstWorld bit) BHLExecution.testedSnapshot :=
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _
      (BHLExecution.sampled_reifies bit) first_computes).2
  have second : BHLExecution.Reifies (afterExtraWorld bit) extraFirstSnapshot :=
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _ first extra_computes).2
  rw [second.2, first.2]
  simp [extraFirstSnapshot]

 theorem extra_executes (bit : Bool) : executes BHLExecution.context BHLExecution.extraTest.quote
    (firstWorld bit) (afterExtraWorld bit) := by
  have first : BHLExecution.Reifies (firstWorld bit) BHLExecution.testedSnapshot :=
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _
      (BHLExecution.sampled_reifies bit) first_computes).2
  exact ⟨trivial, exec_admitted (first_executes bit), 1,
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _ first extra_computes).1⟩

/-! ## Observation independence of the two hidden values -/

 theorem observeWorld_sampled (bit : Bool) :
    observeWorld (BHLExecution.sampledWorld bit) = observeWorld (BHLExecution.sampledWorld false) :=
  BHLExecution.sampled_accessible bit false

/-- The observation appended by one event; hidden memory is not observed. -/
def observeEvent (world : World Bool Primitive) (event : BHLExecution.Event) :
    List (Observation Bool Primitive) :=
  match event.emission with
  | none => []
  | some command => [observeState ⟨Memory.assemble event.state.memory
      world.current.memory.hidden, event.state.datasets, event.state.ledger,
        .command command.quote⟩]

 theorem observeEvent_irrel (left right : World Bool Primitive) (event : BHLExecution.Event) :
    observeEvent left event = observeEvent right event := by
  cases event with
  | mk emission state =>
      cases emission with
      | none => rfl
      | some command => simp [observeEvent, observeState, Memory.assemble]

 theorem eventWorld_observe (world : World Bool Primitive) (event : BHLExecution.Event) :
    observeWorld (BHLExecution.eventWorld world event) = observeWorld world ++ observeEvent world event := by
  cases event with
  | mk emission state =>
      cases emission with
      | none => simp [BHLExecution.eventWorld, observeEvent, observeWorld]
      | some command =>
          simp [BHLExecution.eventWorld, observeEvent, observeWorld, World.extend, World.trace]

 theorem eventWorld_observe_congr (left right : World Bool Primitive) (event : BHLExecution.Event)
    (h : observeWorld left = observeWorld right) :
    observeWorld (BHLExecution.eventWorld left event) = observeWorld (BHLExecution.eventWorld right event) :=
  calc observeWorld (BHLExecution.eventWorld left event)
      = observeWorld left ++ observeEvent left event := eventWorld_observe left event
    _ = observeWorld right ++ observeEvent right event := by
        rw [h, observeEvent_irrel left right event]
    _ = observeWorld (BHLExecution.eventWorld right event) := (eventWorld_observe right event).symm

 theorem observeWorld_eventsWorld_irrel (left right : World Bool Primitive)
    (events : List BHLExecution.Event) (h : observeWorld left = observeWorld right) :
    observeWorld (BHLExecution.eventsWorld left events) = observeWorld (BHLExecution.eventsWorld right events) := by
  induction events generalizing left right with
  | nil => simpa [BHLExecution.eventsWorld] using h
  | cons event rest ih =>
      simp only [BHLExecution.eventsWorld, List.foldl_cons]
      exact ih _ _ (eventWorld_observe_congr left right event h)

 theorem hidden_sampled (bit : Bool) :
    (BHLExecution.sampledWorld bit).current.memory.hidden = BHLBelief.hiddenMemory bit := by
  simp only [BHLExecution.sampledWorld, World.extend_current, BHLExecution.startWorld,
    World.start_current, Memory.hidden_assemble]

 theorem hidden_eventsWorld (world : World Bool Primitive) (events : List BHLExecution.Event) :
    (BHLExecution.eventsWorld world events).current.memory.hidden = world.current.memory.hidden := by
  induction events generalizing world with
  | nil => rfl
  | cons event rest ih =>
      rw [show BHLExecution.eventsWorld world (event :: rest) =
        BHLExecution.eventsWorld (BHLExecution.eventWorld world event) rest from rfl, ih]
      cases event with
      | mk emission state =>
          cases emission with
          | none => rfl
          | some command =>
              simp only [BHLExecution.eventWorld, World.extend_current, Memory.hidden_assemble]

 theorem provenance_eventsWorld (world : World Bool Primitive) (events : List BHLExecution.Event) :
    (BHLExecution.eventsWorld world events).samplingProvenance = world.samplingProvenance := by
  induction events generalizing world with
  | nil => rfl
  | cons event rest ih =>
      rw [show BHLExecution.eventsWorld world (event :: rest) =
        BHLExecution.eventsWorld (BHLExecution.eventWorld world event) rest from rfl, ih]
      cases event with
      | mk emission state =>
          cases emission with
          | none => rfl
          | some command =>
              change (world.extend ⟨Memory.assemble state.memory world.current.memory.hidden,
                state.datasets, state.ledger, .command command.quote⟩).samplingProvenance
                = world.samplingProvenance
              exact World.samplingProvenance_extend_command world _ command.quote rfl

 theorem sampled_provenance (bit : Bool) :
    (BHLExecution.sampledWorld bit).samplingProvenance = {(false, BHLBelief.populationId)} := by
  simp [BHLExecution.sampledWorld, BHLExecution.startWorld, World.samplingProvenance, World.extend, World.start,
    List.filterMap]

 theorem first_provenance (bit : Bool) :
    (firstWorld bit).samplingProvenance = {(false, BHLBelief.populationId)} := by
  change (BHLExecution.eventsWorld (BHLExecution.sampledWorld bit) firstEvents).samplingProvenance
    = {(false, BHLBelief.populationId)}
  rw [provenance_eventsWorld]
  exact sampled_provenance bit

 theorem first_accessible (bit : Bool) : Accessible (firstWorld false) (firstWorld bit) :=
  (observeWorld_eventsWorld_irrel (BHLExecution.sampledWorld bit) (BHLExecution.sampledWorld false) firstEvents
    (observeWorld_sampled bit)).symm

 theorem afterExtra_accessible (bit : Bool) :
    Accessible (afterExtraWorld false) (afterExtraWorld bit) := by
  exact (observeWorld_eventsWorld_irrel (firstWorld bit) (firstWorld false) extraFirstEvents
    (first_accessible bit).symm).symm

 theorem first_dataset (bit : Bool) : (firstWorld bit).current.datasets BHLExecution.dataId = false := by
  have represented : BHLExecution.Reifies (firstWorld bit) BHLExecution.testedSnapshot :=
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _
      (BHLExecution.sampled_reifies bit) first_computes).2
  have datasets := congrArg VisibleState.datasets represented.1
  change (firstWorld bit).current.visible.datasets BHLExecution.dataId = false
  rw [datasets]
  simp [BHLExecution.testedSnapshot, BHLExecution.initialSnapshot, BHLExecution.Snapshot.visible]

 theorem first_visible_dataset (bit : Bool) :
    (firstWorld bit).current.visible.datasets BHLExecution.dataId = false :=
  first_dataset bit

 theorem first_datasetEval (bit : Bool) : evalTerm BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty
    (semanticView BHLExecution.context.model.dynamics (firstWorld bit))
    (AssertionTerm.datasetRead .ambient BHLExecution.dataId) = some false := by
  show some ((firstWorld bit).current.visible.datasets BHLExecution.dataId) = some false
  rw [first_visible_dataset bit]

 theorem afterExtra_datasetEval (bit : Bool) :
    evalTerm BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty
    (semanticView BHLExecution.context.model.dynamics (afterExtraWorld bit))
    (AssertionTerm.datasetRead .ambient BHLExecution.dataId) = some false := by
  show some ((afterExtraWorld bit).current.visible.datasets BHLExecution.dataId) = some false
  have first : BHLExecution.Reifies (firstWorld bit) BHLExecution.testedSnapshot :=
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _
      (BHLExecution.sampled_reifies bit) first_computes).2
  have second : BHLExecution.Reifies (afterExtraWorld bit) extraFirstSnapshot :=
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _ first extra_computes).2
  have datasets := congrArg VisibleState.datasets second.1
  rw [datasets]
  simp [extraFirstSnapshot, BHLExecution.testedSnapshot, BHLExecution.initialSnapshot,
    BHLExecution.Snapshot.visible]

 theorem first_report (bit : Bool) : evalTerm BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty
    (semanticView BHLExecution.context.model.dynamics (firstWorld bit)) (report [] BHLExecution.report) =
      some (1 : ℝ) := by
  change evalTerm BHLExecution.context.interpretation BHLExecution.context.model GhostEnv.empty
    (semanticView BHLExecution.context.model.dynamics (firstWorld bit))
    (report [] BHLExecution.report) = some (1 : ℝ)
  rw [evalTerm_report BHLExecution.context GhostEnv.empty _ BHLExecution.report]
  have represented : BHLExecution.Reifies (firstWorld bit) BHLExecution.testedSnapshot :=
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _
      (BHLExecution.sampled_reifies bit) first_computes).2
  change (firstWorld bit).current.visible.memory .real BHLExecution.report.id = some (1 : ℝ)
  rw [represented.1]
  simp [BHLExecution.Snapshot.visible, BHLExecution.Snapshot.memory, BHLExecution.testedSnapshot]

 theorem first_pvalue (bit : Bool) : evalTerm BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty
    (semanticView BHLExecution.context.model.dynamics (firstWorld bit)) (.pvalue (counterTest [])) =
      some (1 : ℝ) := by
  change evalTerm BHLExecution.context.interpretation BHLExecution.context.model GhostEnv.empty
      (semanticView BHLExecution.context.model.dynamics (firstWorld bit))
      (.pvalue (leaf [] BHLBelief.hypothesisId (.read BHLExecution.dataId)
        BHLBelief.correctId BHLBelief.populationId)) = some (1 : ℝ)
  rw [evalTerm_pvalue_leaf_some BHLExecution.context GhostEnv.empty _ BHLBelief.hypothesisId
    (.read BHLExecution.dataId) BHLBelief.correctId BHLBelief.populationId false (first_datasetEval bit)]
  change some ((BHLBelief.testFor BHLBelief.correctId).tailProbability false) = some (1 : ℝ)
  simpa only [Rat.cast_one] using
    congrArg some (BHLExecution.exact_dirac_pvalue BHLBelief.correctId false)

 theorem first_exact_history (bit : Bool) :
    referenceModalSatisfaction BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty (firstWorld bit)
      (exactHistory (counterTest [])) := by
  rw [exactHistory_iff_ledger, first_ledger bit]
  rw [show evalTestHistory BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty
        (semanticView BHLExecution.context.model.dynamics (firstWorld bit)) (counterTest [])
        = some ({(false, BHLBelief.correctId)} : History Bool) from by
      rw [counterTest, evalTestHistory_leaf, first_datasetEval bit]
      rfl]

 theorem first_old (bit : Bool) :
    referenceModalSatisfaction BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty (firstWorld bit)
      (.atom (.equal (.valueRead .ambient BHLExecution.oldReport) (.rational (7 / 11)))) := by
  refine ⟨((7 / 11 : ℚ) : ℝ), ?_, rfl⟩
  change evalTerm BHLExecution.context.interpretation BHLExecution.context.model GhostEnv.empty
    (semanticView BHLExecution.context.model.dynamics (firstWorld bit))
    (report [] BHLExecution.oldReport) = some (((7 / 11 : ℚ) : ℝ))
  rw [evalTerm_report BHLExecution.context GhostEnv.empty _ BHLExecution.oldReport]
  have represented : BHLExecution.Reifies (firstWorld bit) BHLExecution.testedSnapshot :=
    (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _
      (BHLExecution.sampled_reifies bit) first_computes).2
  change (firstWorld bit).current.visible.memory .real BHLExecution.oldReport.id = some (((7 / 11 : ℚ) : ℝ))
  rw [represented.1]
  simp [BHLExecution.Snapshot.visible, BHLExecution.Snapshot.memory, BHLExecution.testedSnapshot,
    BHLExecution.initialSnapshot, Function.update, BHLExecution.report, BHLExecution.oldReport]

 theorem first_report_pvalue (bit : Bool) :
    referenceModalSatisfaction BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty (firstWorld bit)
      (.atom (.equal (.valueRead .ambient BHLExecution.report) (.pvalue (counterTest [])))) :=
  ⟨(1 : ℝ), first_report bit, first_pvalue bit⟩

 theorem first_requirements (bit : Bool) :
    referenceModalSatisfaction BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty (firstWorld bit)
      (modelRequirementsFormula (counterTest [])) := by
  refine ⟨semanticView BHLExecution.context.model.dynamics (firstWorld bit), rfl, ?_⟩
  intro d hd
  have value : d = false := Option.some.inj (hd.symm.trans (first_datasetEval bit))
  rw [value]
  refine ⟨?_, ?_⟩
  · simp [BHLExecution.interpretation, BHLBelief.lawBinding_iff, BHLBelief.correctId, BHLBelief.wrongId]
  · rw [show (semanticView BHLExecution.context.model.dynamics (firstWorld bit)).provenance
        = (firstWorld bit).samplingProvenance from rfl, first_provenance bit]
    simp

 theorem first_possible :
    referenceModalSatisfaction BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty (firstWorld false)
      ((alternativeFormula []).possible) := by
  rw [referenceModalSatisfaction_possible, possible_iff_exists]
  refine ⟨firstWorld true, exec_admitted (first_executes true), first_accessible true, ?_⟩
  refine ⟨(firstWorld true).current.memory.hidden, rfl, ?_⟩
  have hidden : (firstWorld true).current.memory.hidden = BHLBelief.hiddenMemory true :=
    (show (firstWorld true).current.memory.hidden = (BHLExecution.sampledWorld true).current.memory.hidden
      from hidden_eventsWorld _ _).trans (hidden_sampled true)
  rw [hidden]
  exact ⟨rfl, BHLBelief.hiddenMemory_parameter true⟩

 theorem first_belief :
    referenceModalSatisfaction BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty (firstWorld false)
      (statisticalBelief .equal (report [] BHLExecution.report) (counterTest [])
        (alternativeFormula [])) := by
  refine belief_from_observable_exception BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty
    (firstWorld false) .equal (report [] BHLExecution.report) (counterTest []) (alternativeFormula [])
    (observableTest_leaf BHLExecution.context GhostEnv.empty BHLBelief.hypothesisId (.read BHLExecution.dataId)
      BHLBelief.correctId BHLBelief.populationId)
    (observationInvariant_report BHLExecution.context GhostEnv.empty BHLExecution.report) ?_
    (first_exact_history false)
  exact ⟨(1 : ℝ), (1 : ℝ), first_pvalue false, first_report false, rfl⟩

 theorem legal_pre :
    satisfies BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty (firstWorld false) (badPre []) :=
  ⟨exec_admitted (first_executes false),
    ⟨first_requirements false,
      ⟨first_possible,
        ⟨first_old false,
          ⟨first_report_pvalue false,
            ⟨first_exact_history false, first_belief⟩⟩⟩⟩⟩⟩

 theorem afterExtra_exact_history_false (bit : Bool) :
    ¬ referenceModalSatisfaction BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty
      (afterExtraWorld bit) (exactHistory (counterTest [])) := by
  rw [exactHistory_iff_ledger]
  intro h
  have expected : evalTestHistory BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty
      (semanticView BHLExecution.context.model.dynamics (afterExtraWorld bit)) (counterTest []) =
        some ({(false, BHLBelief.correctId)} : History Bool) := by
    rw [counterTest, evalTestHistory_leaf, afterExtra_datasetEval bit]
    rfl
  rw [afterExtra_ledger bit, first_ledger bit, expected] at h
  have cardinality := congrArg Multiset.card (Option.some.inj h)
  simp at cardinality

 theorem not_post :
    ¬ satisfies BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty (afterExtraWorld false)
      (badPre []) := by
  intro h
  exact afterExtra_exact_history_false false h.2.2.2.2.2.1

/-- The extra well-formed test makes the proposed single-test freshness post false
while the visible report value is preserved. -/
 theorem not_valid_freshness : ¬ ValidTriple BHLExecution.context (badPre []) BHLExecution.extraTest.quote (badPre []) :=
  fun valid => not_post (valid GhostEnv.empty (firstWorld false) (afterExtraWorld false)
    legal_pre (extra_executes false))

 theorem visible_report_preserved :
    evalTerm BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty
        (semanticView BHLExecution.context.model.dynamics (firstWorld false)) (report [] BHLExecution.report) =
      some (1 : ℝ) ∧
    evalTerm BHLExecution.interpretation BHLExecution.context.model GhostEnv.empty
        (semanticView BHLExecution.context.model.dynamics (afterExtraWorld false)) (report [] BHLExecution.report) =
      some (1 : ℝ) :=
  ⟨first_report false, by
    change evalTerm BHLExecution.context.interpretation BHLExecution.context.model GhostEnv.empty
      (semanticView BHLExecution.context.model.dynamics (afterExtraWorld false))
      (report [] BHLExecution.report) = some (1 : ℝ)
    rw [evalTerm_report BHLExecution.context GhostEnv.empty _ BHLExecution.report]
    have first : BHLExecution.Reifies (firstWorld false) BHLExecution.testedSnapshot :=
      (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _
        (BHLExecution.sampled_reifies false) first_computes).2
    have second : BHLExecution.Reifies (afterExtraWorld false) extraFirstSnapshot :=
      (BHLExecution.scheduled_correspondence _ _ _ _ _ _ _ first extra_computes).2
    change (afterExtraWorld false).current.visible.memory .real BHLExecution.report.id =
      some (1 : ℝ)
    rw [second.1]
    simp [extraFirstSnapshot, BHLExecution.Snapshot.visible, BHLExecution.Snapshot.memory,
      BHLExecution.testedSnapshot]⟩

/-- Global soundness excludes a derivation of the countermodel's false triple. -/
 theorem extra_not_derivable :
    ¬ Derivation BHLExecution.context (badPre []) BHLExecution.extraTest.quote (badPre []) := by
  intro derivation
  exact not_valid_freshness (derivation_sound derivation)

/-! ## Computable observation rows -/

def observe (result : Option (Option BHLExecution.Source × BHLExecution.Snapshot × List BHLExecution.Event)) :
    Option (Option Int × Option Int × Option ℚ × Option ℚ × List Nat) :=
  result.map fun out =>
    (out.2.1.integers BHLExecution.x.id, out.2.1.integers BHLExecution.y.id, out.2.1.rationals BHLExecution.report.id,
      out.2.1.rationals BHLExecution.oldReport.id,
      out.2.2.filterMap fun event => event.emission.map BHLExecution.Command.code)

def skipRow := observe (BHLExecution.scheduled [true] (some (.command .skip)) BHLExecution.initialSnapshot)
def incrementRow := observe (BHLExecution.scheduled [true] (some BHLExecution.incrementX) BHLExecution.initialSnapshot)
def reportRow := observe (BHLExecution.scheduled [true] (some BHLExecution.reportOnly) BHLExecution.initialSnapshot)
def twoTestRow := observe (BHLExecution.scheduled [true, true] (some twoTests) BHLExecution.initialSnapshot)
def branchTrueRow := observe (BHLExecution.scheduled [true, true] (some variableBranch) BHLExecution.initialSnapshot)
def branchFalseRow := observe (BHLExecution.scheduled [true, true] (some variableBranch)
  (BHLExecution.afterX BHLExecution.initialSnapshot 1))
def loopRow := observe (BHLExecution.scheduled (List.replicate 7 true) (some BHLExecution.terminatingLoop)
  BHLExecution.initialSnapshot)
def parallelLeftRow := observe (BHLExecution.scheduled [true, true] (some BHLExecution.parallel) BHLExecution.initialSnapshot)
def parallelRightRow := observe (BHLExecution.scheduled [false, true] (some BHLExecution.parallel) BHLExecution.initialSnapshot)
def firstRow := observe (BHLExecution.scheduled [true] (some BHLExecution.testData) BHLExecution.initialSnapshot)
def extraRow := observe (BHLExecution.scheduled [true] (some BHLExecution.extraTest) BHLExecution.testedSnapshot)

 theorem skipRow_computes :
    skipRow = some (some 0, some 0, none, some (7 / 11), [0]) := rfl
 theorem incrementRow_computes :
    incrementRow = some (some 1, some 0, none, some (7 / 11), [110]) := rfl
 theorem reportRow_computes :
    reportRow = some (some 0, some 0, some 1, some (7 / 11), [412]) := rfl
 theorem twoTestRow_computes :
    twoTestRow = some (some 0, some 0, some 1, some (7 / 11), [312, 312]) := rfl
 theorem branchTrueRow_computes :
    branchTrueRow = some (some 1, some 0, none, some (7 / 11), [110]) := rfl
 theorem branchFalseRow_computes :
    branchFalseRow = some (some 1, some 2, none, some (7 / 11), [111]) := rfl
 theorem loopRow_computes :
    loopRow = some (some 3, some 0, none, some (7 / 11), [110, 110, 110]) := rfl
 theorem parallelLeftRow_computes :
    parallelLeftRow = some (some 1, some 2, none, some (7 / 11), [110, 111]) := rfl
 theorem parallelRightRow_computes :
    parallelRightRow = some (some 1, some 2, none, some (7 / 11), [111, 110]) := rfl
 theorem firstRow_computes :
    firstRow = some (some 0, some 0, some 1, some (7 / 11), [312]) := rfl
 theorem extraRow_computes :
    extraRow = some (some 0, some 0, some 1, some (7 / 11), [312]) := rfl

def ledgerCounts (state : BHLExecution.Snapshot) : Nat × Nat :=
  (History.count state.ledger false BHLBelief.correctId, History.count state.ledger false BHLBelief.extraId)

 theorem firstLedgerCounts : ledgerCounts BHLExecution.testedSnapshot = (1, 0) := by
  simp [ledgerCounts, BHLExecution.testedSnapshot, BHLExecution.initialSnapshot, History.count,
    BHLBelief.correctId, BHLBelief.extraId]
 theorem extraLedgerCounts : ledgerCounts extraFirstSnapshot = (1, 1) := by
  simp [ledgerCounts, extraFirstSnapshot, BHLExecution.testedSnapshot, BHLExecution.initialSnapshot,
    History.count, BHLBelief.correctId, BHLBelief.extraId]

/-- The full-ledger multiplicities before and after the extra test, evaluated by
rewriting the proved count equations; the semantic failure is `not_valid_freshness`. -/
def freshnessSummary : Nat × Nat × Nat × Nat :=
  ((ledgerCounts BHLExecution.testedSnapshot).1, (ledgerCounts BHLExecution.testedSnapshot).2,
    (ledgerCounts extraFirstSnapshot).1, (ledgerCounts extraFirstSnapshot).2)

 theorem freshnessSummary_computes : freshnessSummary = (1, 0, 1, 1) := by
  rw [freshnessSummary, firstLedgerCounts, extraLedgerCounts]

/-- Executable observations; their semantic content is the public correspondence
theorems above, not the printed list. -/
def rows : List (String × Bool) :=
  [("skip", decide (skipRow = some (some 0, some 0, none, some (7 / 11), [0]))),
   ("increment", decide (incrementRow = some (some 1, some 0, none, some (7 / 11), [110]))),
   ("reportOnly", decide (reportRow = some (some 0, some 0, some 1, some (7 / 11), [412]))),
   ("twoTests", decide (twoTestRow = some (some 0, some 0, some 1, some (7 / 11), [312, 312]))),
   ("branchTrue", decide (branchTrueRow = some (some 1, some 0, none, some (7 / 11), [110]))),
   ("branchFalse", decide (branchFalseRow = some (some 1, some 2, none, some (7 / 11), [111]))),
   ("loop", decide (loopRow = some (some 3, some 0, none, some (7 / 11), [110, 110, 110]))),
   ("parallelLeft",
     decide (parallelLeftRow = some (some 1, some 2, none, some (7 / 11), [110, 111]))),
   ("parallelRight",
     decide (parallelRightRow = some (some 1, some 2, none, some (7 / 11), [111, 110])))]

 theorem rows_compute : rows = [("skip", true), ("increment", true), ("reportOnly", true),
    ("twoTests", true), ("branchTrue", true), ("branchFalse", true), ("loop", true),
    ("parallelLeft", true), ("parallelRight", true)] := by
  simp [rows, skipRow_computes, incrementRow_computes, reportRow_computes, twoTestRow_computes,
    branchTrueRow_computes, branchFalseRow_computes, loopRow_computes,
    parallelLeftRow_computes, parallelRightRow_computes]

/-- Executable observations of the two satellite fixtures. Their own modules
prove these values against the actual assertions and reference runs. -/
def otherChecks : List Bool :=
  Lara.Examples.BHLSoundnessDataset.smokeFlags ++
    [Lara.Examples.BHLSoundnessScience.smokeObservations.1,
     Lara.Examples.BHLSoundnessScience.smokeObservations.2.1,
     Lara.Examples.BHLSoundnessScience.smokeObservations.2.2.1,
     Lara.Examples.BHLSoundnessScience.smokeObservations.2.2.2.1,
     Lara.Examples.BHLSoundnessScience.smokeObservations.2.2.2.2]

 theorem otherChecks_compute : otherChecks.all id = true := by
  simp [otherChecks, Lara.Examples.BHLSoundnessDataset.smoke_flags,
    Lara.Examples.BHLSoundnessScience.smoke_observations]

 theorem rows_all_true : rows.all (fun row => row.2) = true := by
  rw [rows_compute]
  rfl

end
end Lara.Examples.BHLSoundness
