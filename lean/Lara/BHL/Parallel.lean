import Lara.BHL.ProgramLaws
import Lara.BHL.ExecutionLaws

namespace Lara.BHL

variable {D : Type} [MeasurableSpace D]

noncomputable section

/-- Finite support of a genuine source residual; terminal configurations have no support. -/
def residualReads : Option Program → List ProgramCell
  | none => []
  | some program => program.reads

def residualWrites : Option Program → List ProgramCell
  | none => []
  | some program => program.writes

/-- Membership, rather than multiplicity, is the support order. Loop unfolding may
repeat a source subtree, but never introduces a new readable or writable cell. -/
def ResidualBound (residual : Option Program) (program : Program) : Prop :=
  (∀ cell ∈ residualReads residual, cell ∈ program.reads) ∧
  (∀ cell ∈ residualWrites residual, cell ∈ program.writes)

namespace ResidualBound

theorem initial (program : Program) : ResidualBound (some program) program :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem terminal (program : Program) : ResidualBound none program := by
  simp [ResidualBound, residualReads, residualWrites]

end ResidualBound

namespace Step

theorem support_mono {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) :
    (∀ cell ∈ residualReads target, cell ∈ residualReads source) ∧
      (∀ cell ∈ residualWrites target, cell ∈ residualWrites source) := by
  induction step <;>
    simp only [residualReads, residualWrites, Program.reads, Program.writes,
      List.mem_append, List.not_mem_nil, false_implies, implies_true] at * <;>
    constructor <;> intros <;> aesop

theorem residual_bound {context : ProgramContext D} {source target before after program}
    (step : Step context source before target after) (bound : ResidualBound source program) :
    ResidualBound target program :=
  ⟨fun cell member => bound.1 cell (step.support_mono.1 cell member),
    fun cell member => bound.2 cell (step.support_mono.2 cell member)⟩

end Step

namespace Steps

theorem support_mono {context : ProgramContext D} {n source target before after}
    (steps : Steps context n source before target after) :
    (∀ cell ∈ residualReads target, cell ∈ residualReads source) ∧
      (∀ cell ∈ residualWrites target, cell ∈ residualWrites source) := by
  induction steps with
  | refl => exact ⟨fun _ h => h, fun _ h => h⟩
  | cons first rest ih =>
      exact ⟨fun cell h => first.support_mono.1 cell (ih.1 cell h),
        fun cell h => first.support_mono.2 cell (ih.2 cell h)⟩

end Steps

namespace Noninterfering

theorem left_read {left right : Program} (h : Noninterfering left right)
    {cell : ProgramCell} (read : cell ∈ left.reads) : cell ∉ right.writes := by
  intro write
  exact h.2 cell write (by simp [Program.used, read])

theorem right_read {left right : Program} (h : Noninterfering left right)
    {cell : ProgramCell} (read : cell ∈ right.reads) : cell ∉ left.writes :=
  h.symm.left_read read

theorem left_write {left right : Program} (h : Noninterfering left right)
    {cell : ProgramCell} (write : cell ∈ left.writes) : cell ∉ right.writes :=
  h.writes_not_writes cell write

theorem residual_mono {left right nextLeft nextRight : Program}
    (h : Noninterfering left right)
    (leftBound : ResidualBound (some nextLeft) left)
    (rightBound : ResidualBound (some nextRight) right) :
    Noninterfering nextLeft nextRight := by
  refine h.mono leftBound.2 ?_ rightBound.2 ?_
  · intro cell member
    rcases List.mem_append.mp member with read | write
    · exact List.mem_append_left _ (leftBound.1 cell read)
    · exact List.mem_append_right _ (leftBound.2 cell write)
  · intro cell member
    rcases List.mem_append.mp member with read | write
    · exact List.mem_append_left _ (rightBound.1 cell read)
    · exact List.mem_append_right _ (rightBound.2 cell write)

end Noninterfering

def residualWellFormed : Option Program → Prop
  | none => True
  | some program => program.WellFormed

namespace Step

theorem wellFormed {context : ProgramContext D} {source target before after}
    (step : Step context source before target after)
    (wellFormed : residualWellFormed source) : residualWellFormed target := by
  revert wellFormed
  induction step with
  | command enabled => intro _; trivial
  | seqContinue child ih =>
      intro wellFormed
      exact ⟨ih wellFormed.1, wellFormed.2⟩
  | seqFinish child ih => intro wellFormed; exact wellFormed.2
  | ifTrue enabled => intro wellFormed; exact wellFormed.1
  | ifFalse enabled => intro wellFormed; exact wellFormed.2
  | loopTrue enabled => intro wellFormed; exact ⟨wellFormed, wellFormed⟩
  | loopFalse enabled => intro _; trivial
  | @parLeftContinue left right next before after child ih =>
      intro wellFormed
      exact ⟨ih wellFormed.1, wellFormed.2.1,
        wellFormed.2.2.residual_mono (child.residual_bound (ResidualBound.initial left))
          (ResidualBound.initial right)⟩
  | parLeftFinish child ih => intro wellFormed; exact wellFormed.2.1
  | @parRightContinue left right next before after child ih =>
      intro wellFormed
      exact ⟨wellFormed.1, ih wellFormed.2.1,
        wellFormed.2.2.residual_mono (ResidualBound.initial left)
          (child.residual_bound (ResidualBound.initial right))⟩
  | parRightFinish child ih => intro wellFormed; exact wellFormed.1

end Step

namespace Steps

theorem wellFormed {context : ProgramContext D} {n source target before after}
    (steps : Steps context n source before target after)
    (wellFormed : residualWellFormed source) : residualWellFormed target := by
  revert wellFormed
  induction steps with
  | refl => exact id
  | cons first rest ih => exact fun wellFormed => ih (first.wellFormed wellFormed)

end Steps

/-- A proof-local record of one actual source-step effect. Silent guard steps are
not source skip: a command record always extends the world, even for skip. -/
inductive SourceEffect (D : Type) where
  | guard (expression : ProgramExpr .boolean) (value : Bool)
  | command (primitive : Primitive) (payload : VisibleWrite D) (delta : History D)

namespace SourceEffect

def payload : SourceEffect D → VisibleWrite D
  | .guard _ _ => .unchanged
  | .command _ write _ => write

def delta : SourceEffect D → History D
  | .guard _ _ => 0
  | .command _ _ history => history

def reads : SourceEffect D → List ProgramCell
  | .guard expression _ => expression.reads
  | .command primitive _ _ => primitive.reads

/-- Actual evaluator evidence for the recorded guard or payload and ledger delta. -/
def Valid (context : ProgramContext D) (effect : SourceEffect D)
    (before : World D Primitive) : Prop :=
  match effect with
  | .guard expression value =>
      evalProgramExpr context.interpretation before.current.visible expression = some value
  | .command primitive write history =>
      evalPrimitive context.interpretation before.current.visible primitive = some (write, history)

def apply (effect : SourceEffect D) (world : World D Primitive) : World D Primitive :=
  match effect with
  | .guard _ _ => world
  | .command primitive write history => world.extend
      (commandState world.current primitive (write.apply world.current.visible) history)

omit [MeasurableSpace D] in
@[simp] theorem apply_visible (effect : SourceEffect D) (world : World D Primitive) :
    (effect.apply world).current.visible = effect.payload.apply world.current.visible := by
  cases effect <;> simp [apply, payload, VisibleWrite.apply]

omit [MeasurableSpace D] in
@[simp] theorem apply_history (effect : SourceEffect D) (world : World D Primitive) :
    (effect.apply world).current.history = world.current.history + effect.delta := by
  cases effect <;> simp [apply, delta, commandState]

omit [MeasurableSpace D] in
theorem apply_agrees (effect : SourceEffect D) (cell : ProgramCell)
    {left right : World D Primitive} (h : cell.Agrees left.current.visible right.current.visible) :
    cell.Agrees (effect.apply left).current.visible (effect.apply right).current.visible := by
  simp only [apply_visible]
  exact effect.payload.apply_agrees cell h

omit [MeasurableSpace D] in
theorem apply_frame (effect : SourceEffect D) (world : World D Primitive) :
    ProgramFrame effect.payload.cells world.current.visible (effect.apply world).current.visible := by
  rw [apply_visible]
  exact effect.payload.apply_frame _

omit [MeasurableSpace D] in
theorem accessible {effect : SourceEffect D} {left right : World D Primitive}
    (h : Accessible left right) : Accessible (effect.apply left) (effect.apply right) := by
  cases effect with
  | guard expression value => exact h
  | command primitive write history =>
      apply (extend_accessible_iff _ _ _ _).mpr
      refine ⟨h, ?_⟩
      have visible := accessible_current_visible h
      have ledger := accessible_history_eq h
      simp only [observeState, commandState, Memory.assemble]
      rw [visible, ledger]

end SourceEffect

/-- The exact source site of a recorded effect, including the selected branch
and selected nested-parallel component. This relation is proof-local; its
reference theorem produces the existing Step relation. -/
inductive EffectOrigin : Option Program → Option Program → SourceEffect D → Prop where
  | command (primitive : Primitive) (payload : VisibleWrite D) (delta : History D) :
      EffectOrigin (some (.command primitive)) none (.command primitive payload delta)
  | seqContinue {left right next effect}
      (child : EffectOrigin (some left) (some next) effect) :
      EffectOrigin (some (.seq left right)) (some (.seq next right)) effect
  | seqFinish {left right effect} (child : EffectOrigin (some left) none effect) :
      EffectOrigin (some (.seq left right)) (some right) effect
  | ifTrue (guard : ProgramExpr .boolean) (left right : Program) :
      EffectOrigin (some (.ite guard left right)) (some left) (.guard guard true)
  | ifFalse (guard : ProgramExpr .boolean) (left right : Program) :
      EffectOrigin (some (.ite guard left right)) (some right) (.guard guard false)
  | loopTrue (guard : ProgramExpr .boolean) (body : Program) :
      EffectOrigin (some (.loop guard body)) (some (.seq body (.loop guard body))) (.guard guard true)
  | loopFalse (guard : ProgramExpr .boolean) (body : Program) :
      EffectOrigin (some (.loop guard body)) none (.guard guard false)
  | parLeftContinue {left right next effect}
      (child : EffectOrigin (some left) (some next) effect) :
      EffectOrigin (some (.par left right)) (some (.par next right)) effect
  | parLeftFinish {left right effect} (child : EffectOrigin (some left) none effect) :
      EffectOrigin (some (.par left right)) (some right) effect
  | parRightContinue {left right next effect}
      (child : EffectOrigin (some right) (some next) effect) :
      EffectOrigin (some (.par left right)) (some (.par left next)) effect
  | parRightFinish {left right effect} (child : EffectOrigin (some right) none effect) :
      EffectOrigin (some (.par left right)) (some left) effect

namespace EffectOrigin

omit [MeasurableSpace D] in
theorem reads_mono {source target : Option Program} {effect : SourceEffect D}
    (origin : EffectOrigin source target effect) :
    ∀ cell ∈ effect.reads, cell ∈ residualReads source := by
  induction origin <;>
    simp only [SourceEffect.reads, residualReads, Program.reads, List.mem_append] at * <;>
    intros <;> aesop

theorem valid_congr {context : ProgramContext D} {source target : Option Program}
    {effect : SourceEffect D} {before other : World D Primitive}
    (origin : EffectOrigin source target effect) (valid : effect.Valid context before)
    (agreement : ProgramAgreement (residualReads source)
      before.current.visible other.current.visible) : effect.Valid context other := by
  have reads : ProgramAgreement effect.reads before.current.visible other.current.visible :=
    agreement.mono origin.reads_mono
  cases effect with
  | guard expression value =>
      exact (evalProgramExpr_congr context.interpretation _ _ expression reads).symm.trans valid
  | command primitive payload delta =>
      exact (evalPrimitive_congr context.interpretation _ _ primitive reads).symm.trans valid

theorem reference {context : ProgramContext D} {source target : Option Program}
    {effect : SourceEffect D} (origin : EffectOrigin source target effect)
    (before : World D Primitive) (valid : effect.Valid context before) :
    Step context source before target (effect.apply before) := by
  revert valid
  induction origin with
  | command primitive payload delta =>
      intro valid
      change evalPrimitive context.interpretation before.current.visible primitive =
        some (payload, delta) at valid
      exact .command (by simp [primitiveEffect, valid])
  | seqContinue child ih => exact fun valid => .seqContinue (ih valid)
  | seqFinish child ih => exact fun valid => .seqFinish (ih valid)
  | ifTrue guard left right => exact fun valid => .ifTrue valid
  | ifFalse guard left right => exact fun valid => .ifFalse valid
  | loopTrue guard body => exact fun valid => .loopTrue valid
  | loopFalse guard body => exact fun valid => .loopFalse valid
  | parLeftContinue child ih => exact fun valid => .parLeftContinue (ih valid)
  | parLeftFinish child ih => exact fun valid => .parLeftFinish (ih valid)
  | parRightContinue child ih => exact fun valid => .parRightContinue (ih valid)
  | parRightFinish child ih => exact fun valid => .parRightFinish (ih valid)

theorem writes_mono {context : ProgramContext D} {source target : Option Program}
    {effect : SourceEffect D} {before : World D Primitive}
    (origin : EffectOrigin source target effect) (valid : effect.Valid context before) :
    ∀ cell ∈ effect.payload.cells, cell ∈ residualWrites source := by
  revert valid
  induction origin with
  | command primitive payload delta =>
      intro valid cell member
      simpa only [SourceEffect.payload, residualWrites, Program.writes,
        evalPrimitive_cells context.interpretation _ _ _ _ valid] using member
  | seqContinue child ih =>
      intro valid cell member
      exact List.mem_append_left _ (ih valid cell member)
  | seqFinish child ih =>
      intro valid cell member
      exact List.mem_append_left _ (ih valid cell member)
  | ifTrue guard left right => simp [SourceEffect.payload, VisibleWrite.cells]
  | ifFalse guard left right => simp [SourceEffect.payload, VisibleWrite.cells]
  | loopTrue guard body => simp [SourceEffect.payload, VisibleWrite.cells]
  | loopFalse guard body => simp [SourceEffect.payload, VisibleWrite.cells]
  | parLeftContinue child ih =>
      intro valid cell member
      exact List.mem_append_left _ (ih valid cell member)
  | parLeftFinish child ih =>
      intro valid cell member
      exact List.mem_append_left _ (ih valid cell member)
  | parRightContinue child ih =>
      intro valid cell member
      exact List.mem_append_right _ (ih valid cell member)
  | parRightFinish child ih =>
      intro valid cell member
      exact List.mem_append_right _ (ih valid cell member)

end EffectOrigin

namespace Step

theorem recorded_effect {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) :
    ∃ effect : SourceEffect D, after = effect.apply before ∧
      EffectOrigin source target effect ∧ effect.Valid context before := by
  induction step with
  | @command primitive world visible delta enabled =>
      cases evaluated : evalPrimitive context.interpretation world.current.visible primitive with
      | none => simp [primitiveEffect, evaluated] at enabled
      | some out =>
          rcases out with ⟨payload, history⟩
          have equal : (payload.apply world.current.visible, history) = (visible, delta) := by
            simpa [primitiveEffect, evaluated] using enabled
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
          exact ⟨.command primitive payload history, rfl, .command _ _ _, evaluated⟩
  | seqContinue child ih =>
      obtain ⟨effect, actual, origin, valid⟩ := ih
      exact ⟨effect, actual, .seqContinue origin, valid⟩
  | seqFinish child ih =>
      obtain ⟨effect, actual, origin, valid⟩ := ih
      exact ⟨effect, actual, .seqFinish origin, valid⟩
  | ifTrue enabled => exact ⟨.guard _ true, rfl, .ifTrue _ _ _, enabled⟩
  | ifFalse enabled => exact ⟨.guard _ false, rfl, .ifFalse _ _ _, enabled⟩
  | loopTrue enabled => exact ⟨.guard _ true, rfl, .loopTrue _ _, enabled⟩
  | loopFalse enabled => exact ⟨.guard _ false, rfl, .loopFalse _ _, enabled⟩
  | parLeftContinue child ih =>
      obtain ⟨effect, actual, origin, valid⟩ := ih
      exact ⟨effect, actual, .parLeftContinue origin, valid⟩
  | parLeftFinish child ih =>
      obtain ⟨effect, actual, origin, valid⟩ := ih
      exact ⟨effect, actual, .parLeftFinish origin, valid⟩
  | parRightContinue child ih =>
      obtain ⟨effect, actual, origin, valid⟩ := ih
      exact ⟨effect, actual, .parRightContinue origin, valid⟩
  | parRightFinish child ih =>
      obtain ⟨effect, actual, origin, valid⟩ := ih
      exact ⟨effect, actual, .parRightFinish origin, valid⟩

theorem effect_origin_iff {context : ProgramContext D} {source target before after} :
    Step context source before target after ↔
      ∃ effect : SourceEffect D, after = effect.apply before ∧
        EffectOrigin source target effect ∧ effect.Valid context before := by
  constructor
  · exact recorded_effect
  · rintro ⟨effect, rfl, origin, valid⟩
    exact origin.reference before valid

end Step

namespace VisibleWrite

omit [MeasurableSpace D] in
/-- Commutation concerns the evaluated payloads, not symbolic right-hand sides. -/
theorem apply_commute (left right : VisibleWrite D) (visible : VisibleState D)
    (disjoint : ∀ cell ∈ left.cells, cell ∉ right.cells) :
    left.apply (right.apply visible) = right.apply (left.apply visible) := by
  apply ProgramAgreement.visible_eq
  intro cell
  by_cases inLeft : cell ∈ left.cells
  · have outRight := disjoint cell inLeft
    exact (left.apply_agrees cell (right.apply_frame visible cell outRight).symm).trans
      (right.apply_frame (left.apply visible) cell outRight)
  · exact (left.apply_frame (right.apply visible) cell inLeft).symm.trans
      (right.apply_agrees cell (left.apply_frame visible cell inLeft))

end VisibleWrite

/-- A foreign frame preserves the entire optional evaluated payload, including
disabledness and the dataset-value-indexed test delta. -/
theorem primitive_read_enabledness (interpretation : AssertionInterpretation D Primitive)
    (primitive : Primitive) (before after : VisibleState D) (writes : List ProgramCell)
    (frame : ProgramFrame writes before after)
    (disjoint : ∀ cell ∈ primitive.reads, cell ∉ writes) :
    evalPrimitive interpretation after primitive = evalPrimitive interpretation before primitive :=
  (evalPrimitive_congr interpretation before after primitive (frame.agreement disjoint)).symm

theorem primitive_actual_payload_commute
    (interpretation : AssertionInterpretation D Primitive)
    (left right : Primitive) (visible : VisibleState D)
    (leftPayload rightPayload : VisibleWrite D) (leftDelta rightDelta : History D)
    (noninterfering : Noninterfering (.command left) (.command right))
    (leftEnabled : evalPrimitive interpretation visible left = some (leftPayload, leftDelta))
    (rightEnabled : evalPrimitive interpretation visible right = some (rightPayload, rightDelta)) :
    evalPrimitive interpretation (rightPayload.apply visible) left = some (leftPayload, leftDelta) ∧
      evalPrimitive interpretation (leftPayload.apply visible) right = some (rightPayload, rightDelta) ∧
      leftPayload.apply (rightPayload.apply visible) =
        rightPayload.apply (leftPayload.apply visible) ∧
      leftDelta + rightDelta = rightDelta + leftDelta := by
  have leftCells := evalPrimitive_cells interpretation visible left leftPayload leftDelta leftEnabled
  have rightCells := evalPrimitive_cells interpretation visible right rightPayload rightDelta rightEnabled
  refine ⟨?_, ?_, ?_, add_comm _ _⟩
  · rw [primitive_read_enabledness interpretation left visible (rightPayload.apply visible)
      rightPayload.cells (rightPayload.apply_frame visible) (by
        intro cell member
        rw [rightCells]
        exact noninterfering.left_read member)]
    exact leftEnabled
  · rw [primitive_read_enabledness interpretation right visible (leftPayload.apply visible)
      leftPayload.cells (leftPayload.apply_frame visible) (by
        intro cell member
        rw [leftCells]
        exact noninterfering.right_read member)]
    exact rightEnabled
  · apply leftPayload.apply_commute rightPayload visible
    intro cell member
    rw [rightCells]
    exact noninterfering.left_write (by simpa only [leftCells, Program.writes] using member)

/-- All constructors retain the exact source site, evaluated payload, delta and
guard choice when replayed on agreement on the source program's reads. -/
theorem step_effect_replay_origin {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) :
    ∃ effect : SourceEffect D, after = effect.apply before ∧
      (∀ cell ∈ effect.payload.cells, cell ∈ residualWrites source) ∧
      EffectOrigin source target effect ∧ effect.Valid context before ∧
      (∀ other : World D Primitive,
        ProgramAgreement (residualReads source) before.current.visible other.current.visible →
        Step context source other target (effect.apply other) ∧ effect.Valid context other) := by
  obtain ⟨effect, actual, origin, valid⟩ := step.recorded_effect
  refine ⟨effect, actual, origin.writes_mono valid, origin, valid, ?_⟩
  intro other agreement
  have otherValid := origin.valid_congr valid agreement
  exact ⟨origin.reference other otherValid, otherValid⟩

theorem step_effect_replay {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) :
    ∃ effect : SourceEffect D, after = effect.apply before ∧
      (∀ cell ∈ effect.payload.cells, cell ∈ residualWrites source) ∧
      effect.Valid context before ∧
      (∀ other : World D Primitive,
        ProgramAgreement (residualReads source) before.current.visible other.current.visible →
        Step context source other target (effect.apply other) ∧ effect.Valid context other) := by
  obtain ⟨effect, actual, footprint, origin, valid, replay⟩ := step_effect_replay_origin step
  exact ⟨effect, actual, footprint, valid, replay⟩

namespace Step

theorem frame {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) :
    ProgramFrame (residualWrites source) before.current.visible after.current.visible := by
  obtain ⟨effect, rfl, footprint, _⟩ := step_effect_replay step
  intro cell outside
  exact effect.apply_frame before cell (fun member => outside (footprint cell member))

theorem target_enabled_iff {context : ProgramContext D} {source target before otherBefore}
    (agreement : ProgramAgreement (residualReads source)
      before.current.visible otherBefore.current.visible) :
    (∃ after, Step context source before target after) ↔
      ∃ otherAfter, Step context source otherBefore target otherAfter := by
  constructor
  · rintro ⟨after, step⟩
    obtain ⟨effect, actual, footprint, valid, replay⟩ := step_effect_replay step
    exact ⟨effect.apply otherBefore, (replay otherBefore agreement).1⟩
  · rintro ⟨otherAfter, step⟩
    obtain ⟨effect, actual, footprint, valid, replay⟩ := step_effect_replay step
    exact ⟨effect.apply before, (replay before agreement.symm).1⟩

end Step

namespace Steps

theorem frame {context : ProgramContext D} {n source target before after}
    (steps : Steps context n source before target after) :
    ProgramFrame (residualWrites source) before.current.visible after.current.visible := by
  induction steps with
  | refl => exact ProgramFrame.refl _ _
  | cons first rest ih =>
      intro cell outside
      exact (first.frame cell outside).trans
        (ih cell (fun member => outside (first.support_mono.2 cell member)))

end Steps

/-- Lockstep witnesses for two actual executions. Shared effects expose the exact
payloads and ledger deltas; the shared source/target exposes every guard choice. -/
inductive MatchedSteps (context : ProgramContext D) : Nat → Option Program →
    World D Primitive → Option Program → World D Primitive →
    World D Primitive → World D Primitive → Prop where
  | refl (source : Option Program) (left right : World D Primitive) :
      MatchedSteps context 0 source left source left right right
  | cons {n source middle target left leftNext leftFinal right rightNext rightFinal}
      (effect : SourceEffect D)
      (origin : EffectOrigin source middle effect)
      (leftStep : Step context source left middle leftNext)
      (rightStep : Step context source right middle rightNext)
      (leftEffect : leftNext = effect.apply left)
      (rightEffect : rightNext = effect.apply right)
      (leftValid : effect.Valid context left)
      (rightValid : effect.Valid context right)
      (rest : MatchedSteps context n middle leftNext target leftFinal rightNext rightFinal) :
      MatchedSteps context (n + 1) source left target leftFinal right rightFinal

namespace MatchedSteps

theorem left {context : ProgramContext D} {n source target before after otherBefore otherAfter}
    (matched : MatchedSteps context n source before target after otherBefore otherAfter) :
    Steps context n source before target after := by
  induction matched with
  | refl => exact .refl _ _
  | cons effect origin first second actual otherActual firstValid secondValid rest ih => exact .cons first ih

theorem right {context : ProgramContext D} {n source target before after otherBefore otherAfter}
    (matched : MatchedSteps context n source before target after otherBefore otherAfter) :
    Steps context n source otherBefore target otherAfter := by
  induction matched with
  | refl => exact .refl _ _
  | cons effect origin first second actual otherActual firstValid secondValid rest ih => exact .cons second ih

theorem agreement {context : ProgramContext D} {n source target before after otherBefore otherAfter}
    (matched : MatchedSteps context n source before target after otherBefore otherAfter)
    (cell : ProgramCell) (h : cell.Agrees before.current.visible otherBefore.current.visible) :
    cell.Agrees after.current.visible otherAfter.current.visible := by
  induction matched with
  | refl => exact h
  | cons effect origin first second actual otherActual firstValid secondValid rest ih =>
      apply ih
      rw [actual, otherActual]
      exact effect.apply_agrees cell h

theorem ledger {context : ProgramContext D} {n source target before after otherBefore otherAfter}
    (matched : MatchedSteps context n source before target after otherBefore otherAfter) :
    ∃ delta : History D, after.current.history = before.current.history + delta ∧
      otherAfter.current.history = otherBefore.current.history + delta := by
  induction matched with
  | refl => exact ⟨0, by simp, by simp⟩
  | cons effect origin first second actual otherActual firstValid secondValid rest ih =>
      obtain ⟨delta, ledger, otherLedger⟩ := ih
      refine ⟨effect.delta + delta, ?_, ?_⟩
      · simpa [actual, add_assoc] using ledger
      · simpa [otherActual, add_assoc] using otherLedger

theorem accessible {context : ProgramContext D}
    {n source target before after otherBefore otherAfter}
    (matched : MatchedSteps context n source before target after otherBefore otherAfter)
    (h : Accessible before otherBefore) : Accessible after otherAfter := by
  induction matched with
  | refl => exact h
  | cons effect origin first second actual otherActual firstValid secondValid rest ih =>
      apply ih
      rw [actual, otherActual]
      exact effect.accessible h

end MatchedSteps

namespace Steps

/-- Replay uses no fuel and no termination assumption beyond the supplied finite run. -/
theorem replay {context : ProgramContext D} {n source target before after}
    (steps : Steps context n source before target after) (otherBefore : World D Primitive)
    (agreement : ProgramAgreement (residualReads source)
      before.current.visible otherBefore.current.visible) :
    ∃ otherAfter, MatchedSteps context n source before target after otherBefore otherAfter := by
  induction steps generalizing otherBefore with
  | refl => exact ⟨otherBefore, .refl _ _ _⟩
  | @cons count source middle target before intermediate after first rest ih =>
      obtain ⟨effect, actual, footprint, origin, valid, replay⟩ := step_effect_replay_origin first
      obtain ⟨otherStep, otherValid⟩ := replay otherBefore agreement
      have nextAgreement : ProgramAgreement (residualReads middle) intermediate.current.visible
          (effect.apply otherBefore).current.visible := by
        intro cell member
        rw [actual]
        exact effect.apply_agrees cell
          (agreement cell (first.support_mono.1 cell member))
      obtain ⟨otherAfter, matched⟩ := ih (effect.apply otherBefore) nextAgreement
      exact ⟨otherAfter, .cons effect origin first otherStep actual rfl valid otherValid matched⟩

theorem accessible_forth {context : ProgramContext D} {n source target before after otherBefore}
    (steps : Steps context n source before target after)
    (initial : Admitted context.model.dynamics otherBefore)
    (accessible : Accessible before otherBefore) :
    ∃ otherAfter, Steps context n source otherBefore target otherAfter ∧
      Admitted context.model.dynamics otherAfter ∧ Accessible after otherAfter := by
  obtain ⟨otherAfter, matched⟩ := steps.replay otherBefore (by
    rw [accessible_current_visible accessible]
    exact ProgramAgreement.refl _ _)
  exact ⟨otherAfter, matched.right, matched.right.admitted initial,
    matched.accessible accessible⟩

theorem accessible_back {context : ProgramContext D} {n source target before after otherAfter}
    (steps : Steps context n source before target after)
    (alternative : Admitted context.model.dynamics otherAfter)
    (accessible : Accessible after otherAfter) :
    ∃ otherBefore, Admitted context.model.dynamics otherBefore ∧
      Accessible before otherBefore ∧ Steps context n source otherBefore target otherAfter := by
  let otherBefore := before.rebuildHidden otherAfter.current.memory.hidden
  have beforeAccessible : Accessible before otherBefore := rebuildHidden_accessible _ _
  have beforeAdmitted : Admitted context.model.dynamics otherBefore := by
    apply (admitted_rebuildHidden_iff _ _ _).mpr
    have compatible := admitted_hidden_mem_compatible alternative
    rw [← compatibleHidden_eq_of_accessible accessible, steps.information.2.1] at compatible
    exact compatible
  obtain ⟨reconstructed, run, admitted, observed⟩ :=
    steps.accessible_forth beforeAdmitted beforeAccessible
  have equal : otherAfter = reconstructed := by
    apply admitted_eq_of_accessible_hidden alternative admitted
      (accessible.symm.trans observed)
    rw [run.information.1]
    exact (World.rebuildHidden_current_hidden before _).symm
  exact ⟨otherBefore, beforeAdmitted, beforeAccessible, by simpa only [equal] using run⟩

end Steps

/-- The tagged proof configuration collapses to the existing reference residual.
There is no alternative execution semantics: both terminal components mean none. -/
def pairedResidual : Option Program → Option Program → Option Program
  | none, none => none
  | some left, none => some left
  | none, some right => some right
  | some left, some right => some (.par left right)

inductive PairedStep (context : ProgramContext D) : Option Program → Option Program →
    World D Primitive → Option Program → Option Program → World D Primitive → Prop where
  | left {left right next before after} (step : Step context left before next after) :
      PairedStep context left right before next right after
  | right {left right next before after} (step : Step context right before next after) :
      PairedStep context left right before left next after

namespace PairedStep

theorem reference {context : ProgramContext D} {left right nextLeft nextRight before after}
    (step : PairedStep context left right before nextLeft nextRight after) :
    Step context (pairedResidual left right) before (pairedResidual nextLeft nextRight) after := by
  cases step with
  | left child =>
      obtain ⟨program, rfl⟩ := child.source_some
      cases right with
      | none => cases nextLeft <;> simpa only [pairedResidual] using child
      | some right =>
          cases nextLeft with
          | none => exact .parLeftFinish child
          | some next => exact .parLeftContinue child
  | right child =>
      obtain ⟨program, rfl⟩ := child.source_some
      cases left with
      | none => cases nextRight <;> simpa only [pairedResidual] using child
      | some left =>
          cases nextRight with
          | none => exact .parRightFinish child
          | some next => exact .parRightContinue child

theorem of_reference {context : ProgramContext D} {left right target before after}
    (step : Step context (pairedResidual left right) before target after) :
    ∃ nextLeft nextRight, target = pairedResidual nextLeft nextRight ∧
      PairedStep context left right before nextLeft nextRight after := by
  cases left with
  | none =>
      cases right with
      | none => exact False.elim (Step.terminal_impossible step)
      | some right => exact ⟨none, target, by cases target <;> rfl, .right step⟩
  | some left =>
      cases right with
      | none => exact ⟨target, none, by cases target <;> rfl, .left step⟩
      | some right =>
          rcases Step.par_iff.mp step with ⟨next, child, rfl⟩ | ⟨child, rfl⟩ |
            ⟨next, child, rfl⟩ | ⟨child, rfl⟩
          · exact ⟨some next, some right, rfl, .left child⟩
          · exact ⟨none, some right, rfl, .left child⟩
          · exact ⟨some left, some next, rfl, .right child⟩
          · exact ⟨some left, none, rfl, .right child⟩

theorem reference_iff {context : ProgramContext D} {left right target before after} :
    Step context (pairedResidual left right) before target after ↔
      ∃ nextLeft nextRight, target = pairedResidual nextLeft nextRight ∧
        PairedStep context left right before nextLeft nextRight after := by
  constructor
  · exact of_reference
  · rintro ⟨nextLeft, nextRight, rfl, paired⟩
    exact paired.reference

end PairedStep

/-- Separate source-step counters count only the selected component's actual
step, including guards and component-final steps. -/
inductive PairedSteps (context : ProgramContext D) : Nat → Nat →
    Option Program → Option Program → World D Primitive →
    Option Program → Option Program → World D Primitive → Prop where
  | refl (left right : Option Program) (world : World D Primitive) :
      PairedSteps context 0 0 left right world left right world
  | left {m k left right next finalLeft finalRight before intermediate after}
      (first : Step context left before next intermediate)
      (rest : PairedSteps context m k next right intermediate finalLeft finalRight after) :
      PairedSteps context (m + 1) k left right before finalLeft finalRight after
  | right {m k left right next finalLeft finalRight before intermediate after}
      (first : Step context right before next intermediate)
      (rest : PairedSteps context m k left next intermediate finalLeft finalRight after) :
      PairedSteps context m (k + 1) left right before finalLeft finalRight after

namespace PairedSteps

theorem reference {context : ProgramContext D}
    {m k left right finalLeft finalRight before after}
    (steps : PairedSteps context m k left right before finalLeft finalRight after) :
    Steps context (m + k) (pairedResidual left right) before
      (pairedResidual finalLeft finalRight) after := by
  induction steps with
  | refl => exact .refl _ _
  | left first rest ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Steps.cons (PairedStep.reference (.left first)) ih
  | right first rest ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Steps.cons (PairedStep.reference (.right first)) ih

theorem terminal_iff {context : ProgramContext D}
    {m k finalLeft finalRight before after} :
    PairedSteps context m k none none before finalLeft finalRight after ↔
      m = 0 ∧ k = 0 ∧ finalLeft = none ∧ finalRight = none ∧ before = after := by
  constructor
  · intro steps
    cases steps with
    | refl => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | left first rest => exact False.elim (Step.terminal_impossible first)
    | right first rest => exact False.elim (Step.terminal_impossible first)
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact .refl _ _ _

end PairedSteps

namespace Steps

theorem paired {context : ProgramContext D} {n source target before after}
    (steps : Steps context n source before target after)
    (left right : Option Program) (sourceEq : source = pairedResidual left right) :
    ∃ m k finalLeft finalRight, n = m + k ∧
      target = pairedResidual finalLeft finalRight ∧
      PairedSteps context m k left right before finalLeft finalRight after := by
  induction steps generalizing left right with
  | refl => exact ⟨0, 0, left, right, rfl, sourceEq, .refl _ _ _⟩
  | cons first rest ih =>
      obtain ⟨nextLeft, nextRight, targetEq, paired⟩ :=
        PairedStep.of_reference (sourceEq ▸ first)
      obtain ⟨m, k, finalLeft, finalRight, count, finalEq, tail⟩ :=
        ih nextLeft nextRight targetEq
      cases paired with
      | left child => exact ⟨m + 1, k, finalLeft, finalRight, by omega,
          finalEq, .left child tail⟩
      | right child => exact ⟨m, k + 1, finalLeft, finalRight, by omega,
          finalEq, .right child tail⟩

theorem parallel_paired_iff {context : ProgramContext D} {n left right before after} :
    Steps context n (some (.par left right)) before none after ↔
      ∃ m k, n = m + k ∧
        PairedSteps context m k (some left) (some right) before none none after := by
  constructor
  · intro steps
    obtain ⟨m, k, finalLeft, finalRight, count, terminal, paired⟩ :=
      steps.paired (some left) (some right) rfl
    cases finalLeft with
    | none =>
        cases finalRight with
        | none => exact ⟨m, k, count, paired⟩
        | some program => cases terminal
    | some program =>
        cases finalRight <;> cases terminal
  · rintro ⟨m, k, rfl, paired⟩
    exact paired.reference

theorem paired_iff {context : ProgramContext D} {n left right target before after} :
    Steps context n (pairedResidual left right) before target after ↔
      ∃ m k finalLeft finalRight, n = m + k ∧
        target = pairedResidual finalLeft finalRight ∧
        PairedSteps context m k left right before finalLeft finalRight after := by
  constructor
  · intro steps
    exact steps.paired left right rfl
  · rintro ⟨m, k, finalLeft, finalRight, rfl, rfl, paired⟩
    exact paired.reference

end Steps

/-- A tagged schedule and its two isolated replays, retaining the very same
evaluated effect at every selected source step. This is proof evidence over
reference Step, not a replacement for reference execution. -/
inductive ProjectedSchedule (context : ProgramContext D) : Nat → Nat →
    Option Program → Option Program → World D Primitive →
    World D Primitive → World D Primitive → Option Program → Option Program →
    World D Primitive → World D Primitive → World D Primitive → Prop where
  | refl (left right : Option Program) (shared isolatedLeft isolatedRight : World D Primitive) :
      ProjectedSchedule context 0 0 left right shared isolatedLeft isolatedRight
        left right shared isolatedLeft isolatedRight
  | left {m k left right next finalLeft finalRight shared sharedNext sharedFinal
      isolatedLeft isolatedNext isolatedFinal isolatedRight rightFinal}
      (effect : SourceEffect D)
      (origin : EffectOrigin left next effect)
      (sharedStep : Step context left shared next sharedNext)
      (isolatedStep : Step context left isolatedLeft next isolatedNext)
      (sharedEffect : sharedNext = effect.apply shared)
      (isolatedEffect : isolatedNext = effect.apply isolatedLeft)
      (sharedValid : effect.Valid context shared)
      (isolatedValid : effect.Valid context isolatedLeft)
      (rest : ProjectedSchedule context m k next right sharedNext isolatedNext isolatedRight
        finalLeft finalRight sharedFinal isolatedFinal rightFinal) :
      ProjectedSchedule context (m + 1) k left right shared isolatedLeft isolatedRight
        finalLeft finalRight sharedFinal isolatedFinal rightFinal
  | right {m k left right next finalLeft finalRight shared sharedNext sharedFinal
      isolatedLeft leftFinal isolatedRight isolatedNext isolatedFinal}
      (effect : SourceEffect D)
      (origin : EffectOrigin right next effect)
      (sharedStep : Step context right shared next sharedNext)
      (isolatedStep : Step context right isolatedRight next isolatedNext)
      (sharedEffect : sharedNext = effect.apply shared)
      (isolatedEffect : isolatedNext = effect.apply isolatedRight)
      (sharedValid : effect.Valid context shared)
      (isolatedValid : effect.Valid context isolatedRight)
      (rest : ProjectedSchedule context m k left next sharedNext isolatedLeft isolatedNext
        finalLeft finalRight sharedFinal leftFinal isolatedFinal) :
      ProjectedSchedule context m (k + 1) left right shared isolatedLeft isolatedRight
        finalLeft finalRight sharedFinal leftFinal isolatedFinal

namespace ProjectedSchedule

theorem paired {context : ProgramContext D}
    {m k left right shared isolatedLeft isolatedRight finalLeft finalRight
      sharedFinal leftFinal rightFinal}
    (projection : ProjectedSchedule context m k left right shared isolatedLeft isolatedRight
      finalLeft finalRight sharedFinal leftFinal rightFinal) :
    PairedSteps context m k left right shared finalLeft finalRight sharedFinal := by
  induction projection with
  | refl => exact .refl _ _ _
  | left effect origin first second actual isolatedActual sharedValid isolatedValid rest ih => exact .left first ih
  | right effect origin first second actual isolatedActual sharedValid isolatedValid rest ih => exact .right first ih

theorem left_steps {context : ProgramContext D}
    {m k left right shared isolatedLeft isolatedRight finalLeft finalRight
      sharedFinal leftFinal rightFinal}
    (projection : ProjectedSchedule context m k left right shared isolatedLeft isolatedRight
      finalLeft finalRight sharedFinal leftFinal rightFinal) :
    Steps context m left isolatedLeft finalLeft leftFinal := by
  induction projection with
  | refl => exact .refl _ _
  | left effect origin first second actual isolatedActual sharedValid isolatedValid rest ih => exact .cons second ih
  | right effect origin first second actual isolatedActual sharedValid isolatedValid rest ih => exact ih

theorem right_steps {context : ProgramContext D}
    {m k left right shared isolatedLeft isolatedRight finalLeft finalRight
      sharedFinal leftFinal rightFinal}
    (projection : ProjectedSchedule context m k left right shared isolatedLeft isolatedRight
      finalLeft finalRight sharedFinal leftFinal rightFinal) :
    Steps context k right isolatedRight finalRight rightFinal := by
  induction projection with
  | refl => exact .refl _ _
  | left effect origin first second actual isolatedActual sharedValid isolatedValid rest ih => exact ih
  | right effect origin first second actual isolatedActual sharedValid isolatedValid rest ih => exact .cons second ih

end ProjectedSchedule

/-- Each cell outside the other component's write support agrees with its
isolated execution. No equality of schedule-sensitive action traces is assumed. -/
def ParallelMerge (leftWrites rightWrites : List ProgramCell)
    (shared isolatedLeft isolatedRight : VisibleState D) : Prop :=
  (∀ cell, cell ∉ rightWrites → cell.Agrees shared isolatedLeft) ∧
    (∀ cell, cell ∉ leftWrites → cell.Agrees shared isolatedRight)

namespace ParallelMerge

omit [MeasurableSpace D] in
theorem refl (leftWrites rightWrites : List ProgramCell) (visible : VisibleState D) :
    ParallelMerge leftWrites rightWrites visible visible visible :=
  ⟨fun cell _ => ProgramCell.Agrees.refl cell visible,
    fun cell _ => ProgramCell.Agrees.refl cell visible⟩

omit [MeasurableSpace D] in
theorem left_apply {leftWrites rightWrites : List ProgramCell}
    {shared isolatedLeft isolatedRight : World D Primitive}
    (merge : ParallelMerge leftWrites rightWrites shared.current.visible
      isolatedLeft.current.visible isolatedRight.current.visible)
    (effect : SourceEffect D)
    (footprint : ∀ cell ∈ effect.payload.cells, cell ∈ leftWrites) :
    ParallelMerge leftWrites rightWrites (effect.apply shared).current.visible
      (effect.apply isolatedLeft).current.visible isolatedRight.current.visible := by
  constructor
  · intro cell outside
    exact effect.apply_agrees cell (merge.1 cell outside)
  · intro cell outside
    exact (effect.apply_frame shared cell
      (fun member => outside (footprint cell member))).symm.trans (merge.2 cell outside)

omit [MeasurableSpace D] in
theorem right_apply {leftWrites rightWrites : List ProgramCell}
    {shared isolatedLeft isolatedRight : World D Primitive}
    (merge : ParallelMerge leftWrites rightWrites shared.current.visible
      isolatedLeft.current.visible isolatedRight.current.visible)
    (effect : SourceEffect D)
    (footprint : ∀ cell ∈ effect.payload.cells, cell ∈ rightWrites) :
    ParallelMerge leftWrites rightWrites (effect.apply shared).current.visible
      isolatedLeft.current.visible (effect.apply isolatedRight).current.visible := by
  constructor
  · intro cell outside
    exact (effect.apply_frame shared cell
      (fun member => outside (footprint cell member))).symm.trans (merge.1 cell outside)
  · intro cell outside
    exact effect.apply_agrees cell (merge.2 cell outside)

end ParallelMerge

namespace PairedSteps

/-- Projection reconstructs real isolated worlds from their own initial traces.
The shared ledger receives each component delta once, irrespective of the
initial ledger or the interleaving's source-step schedule. -/
theorem project {context : ProgramContext D}
    {m k left right finalLeft finalRight before after originalLeft originalRight}
    (steps : PairedSteps context m k left right before finalLeft finalRight after)
    (noninterfering : Noninterfering originalLeft originalRight)
    (leftBound : ResidualBound left originalLeft)
    (rightBound : ResidualBound right originalRight)
    (isolatedLeft isolatedRight : World D Primitive)
    (merge : ParallelMerge originalLeft.writes originalRight.writes before.current.visible
      isolatedLeft.current.visible isolatedRight.current.visible) :
    ∃ leftAfter rightAfter leftDelta rightDelta,
      Steps context m left isolatedLeft finalLeft leftAfter ∧
      Steps context k right isolatedRight finalRight rightAfter ∧
      ParallelMerge originalLeft.writes originalRight.writes after.current.visible
        leftAfter.current.visible rightAfter.current.visible ∧
      leftAfter.current.history = isolatedLeft.current.history + leftDelta ∧
      rightAfter.current.history = isolatedRight.current.history + rightDelta ∧
      after.current.history = before.current.history + leftDelta + rightDelta ∧
      ProjectedSchedule context m k left right before isolatedLeft isolatedRight
        finalLeft finalRight after leftAfter rightAfter := by
  induction steps generalizing isolatedLeft isolatedRight with
  | refl =>
      exact ⟨isolatedLeft, isolatedRight, 0, 0, .refl _ _, .refl _ _, merge,
        by simp, by simp, by simp, .refl _ _ _ _ _⟩
  | @left m k left right next finalLeft finalRight before intermediate after first rest ih =>
      obtain ⟨effect, actual, footprint, origin, valid, replay⟩ := step_effect_replay_origin first
      have agreement : ProgramAgreement (residualReads left) before.current.visible
          isolatedLeft.current.visible := by
        intro cell member
        exact merge.1 cell (noninterfering.left_read (leftBound.1 cell member))
      obtain ⟨isolatedStep, isolatedValid⟩ := replay isolatedLeft agreement
      have nextMerge := merge.left_apply effect
        (fun cell member => leftBound.2 cell (footprint cell member))
      rw [← actual] at nextMerge
      obtain ⟨leftAfter, rightAfter, leftDelta, rightDelta, leftRun, rightRun,
        finalMerge, leftLedger, rightLedger, sharedLedger, projected⟩ :=
        ih (first.residual_bound leftBound) rightBound (effect.apply isolatedLeft)
          isolatedRight nextMerge
      refine ⟨leftAfter, rightAfter, effect.delta + leftDelta, rightDelta,
        .cons isolatedStep leftRun, rightRun, finalMerge, ?_, rightLedger, ?_,
        .left effect origin first isolatedStep actual rfl valid isolatedValid projected⟩
      · simpa only [SourceEffect.apply_history, add_assoc] using leftLedger
      · simpa only [actual, SourceEffect.apply_history, add_assoc] using sharedLedger
  | @right m k left right next finalLeft finalRight before intermediate after first rest ih =>
      obtain ⟨effect, actual, footprint, origin, valid, replay⟩ := step_effect_replay_origin first
      have agreement : ProgramAgreement (residualReads right) before.current.visible
          isolatedRight.current.visible := by
        intro cell member
        exact merge.2 cell (noninterfering.right_read (rightBound.1 cell member))
      obtain ⟨isolatedStep, isolatedValid⟩ := replay isolatedRight agreement
      have nextMerge := merge.right_apply effect
        (fun cell member => rightBound.2 cell (footprint cell member))
      rw [← actual] at nextMerge
      obtain ⟨leftAfter, rightAfter, leftDelta, rightDelta, leftRun, rightRun,
        finalMerge, leftLedger, rightLedger, sharedLedger, projected⟩ :=
        ih leftBound (first.residual_bound rightBound) isolatedLeft
          (effect.apply isolatedRight) nextMerge
      refine ⟨leftAfter, rightAfter, leftDelta, effect.delta + rightDelta,
        leftRun, .cons isolatedStep rightRun, finalMerge, leftLedger, ?_, ?_,
        .right effect origin first isolatedStep actual rfl valid isolatedValid projected⟩
      · simpa only [SourceEffect.apply_history, add_assoc] using rightLedger
      · simpa only [actual, SourceEffect.apply_history, add_assoc, add_comm,
          add_left_comm] using sharedLedger

end PairedSteps

/-- The source lemma-2 interface: any terminating permitted schedule projects to
actual isolated runs of exactly m and k steps, with n = m + k. -/
theorem parallel_project {context : ProgramContext D} {n left right before after}
    (noninterfering : Noninterfering left right)
    (steps : Steps context n (some (.par left right)) before none after) :
    ∃ m k leftAfter rightAfter leftDelta rightDelta,
      n = m + k ∧
      PairedSteps context m k (some left) (some right) before none none after ∧
      Steps context m (some left) before none leftAfter ∧
      Steps context k (some right) before none rightAfter ∧
      ParallelMerge left.writes right.writes after.current.visible
        leftAfter.current.visible rightAfter.current.visible ∧
      leftAfter.current.history = before.current.history + leftDelta ∧
      rightAfter.current.history = before.current.history + rightDelta ∧
      after.current.history = before.current.history + leftDelta + rightDelta ∧
      ProjectedSchedule context m k (some left) (some right) before before before
        none none after leftAfter rightAfter := by
  obtain ⟨m, k, count, paired⟩ := Steps.parallel_paired_iff.mp steps
  obtain ⟨leftAfter, rightAfter, leftDelta, rightDelta, leftRun, rightRun, merge,
    leftLedger, rightLedger, ledger, projected⟩ := paired.project noninterfering
      (ResidualBound.initial left) (ResidualBound.initial right) before before
      (ParallelMerge.refl _ _ _)
  exact ⟨m, k, leftAfter, rightAfter, leftDelta, rightDelta, count, paired,
    leftRun, rightRun, merge, leftLedger, rightLedger, ledger, projected⟩

/-- Every permitted terminating interleaving has an actual left-then-right
representative. Its traces may differ, but its complete semantic view does not. -/
theorem parallel_sequential_representative {context : ProgramContext D}
    {n left right before after}
    (noninterfering : Noninterfering left right)
    (steps : Steps context n (some (.par left right)) before none after) :
    ∃ m k intermediate isolatedRight sequentialAfter,
      n = m + k ∧
      Steps context m (some left) before none intermediate ∧
      Steps context k (some right) before none isolatedRight ∧
      MatchedSteps context k (some right) before none isolatedRight intermediate sequentialAfter ∧
      Steps context n (some (.seq left right)) before none sequentialAfter ∧
      semanticView context.model.dynamics after =
        semanticView context.model.dynamics sequentialAfter := by
  obtain ⟨m, k, leftAfter, rightAfter, leftDelta, rightDelta, count, paired,
    leftRun, rightRun, merge, leftLedger, rightLedger, ledger, projected⟩ :=
    parallel_project noninterfering steps
  have rightAgreement : ProgramAgreement right.reads before.current.visible
      leftAfter.current.visible :=
    leftRun.frame.agreement (fun cell member => noninterfering.right_read member)
  obtain ⟨sequentialAfter, matched⟩ := rightRun.replay leftAfter rightAgreement
  have sequential : Steps context n (some (.seq left right)) before none sequentialAfter := by
    rw [count]
    exact (leftRun.seq_lift right).trans matched.right
  have visible : after.current.visible = sequentialAfter.current.visible := by
    apply ProgramAgreement.visible_eq
    intro cell
    by_cases rightWrite : cell ∈ right.writes
    · have outsideLeft : cell ∉ left.writes := noninterfering.symm.left_write rightWrite
      exact (merge.2 cell outsideLeft).trans
        (matched.agreement cell (leftRun.frame cell outsideLeft))
    · exact (merge.1 cell rightWrite).trans (matched.right.frame cell rightWrite)
  obtain ⟨actualDelta, isolatedLedger, sequentialLedger⟩ := matched.ledger
  have deltaEq : actualDelta = rightDelta := by
    apply add_left_cancel (a := before.current.history)
    exact isolatedLedger.symm.trans rightLedger
  have history : after.current.history = sequentialAfter.current.history := by
    rw [ledger, sequentialLedger, deltaEq, leftLedger]
  have view : semanticView context.model.dynamics after =
      semanticView context.model.dynamics sequentialAfter := by
    unfold semanticView
    rw [visible, history, steps.information.1, sequential.information.1,
      steps.information.2.1, sequential.information.2.1,
      steps.information.2.2.1, sequential.information.2.2.1]
  exact ⟨m, k, leftAfter, rightAfter, sequentialAfter, count, leftRun, rightRun,
    matched, sequential, view⟩

/-- Recombination is the existing exact-count reference lift, not projected execution. -/
theorem sequential_parallel_recombine {context : ProgramContext D}
    {n left right before after}
    (steps : Steps context n (some (.seq left right)) before none after) :
    Steps context n (some (.par left right)) before none after :=
  steps.seq_to_parallel

/-- Independent isolated terminating runs recombine as an actual reference
parallel run after replaying the right component on the left endpoint. -/
theorem parallel_recombine {context : ProgramContext D}
    {m k left right before leftAfter rightAfter}
    (noninterfering : Noninterfering left right)
    (leftRun : Steps context m (some left) before none leftAfter)
    (rightRun : Steps context k (some right) before none rightAfter) :
    ∃ after, MatchedSteps context k (some right) before none rightAfter leftAfter after ∧
      Steps context (m + k) (some (.seq left right)) before none after ∧
      Steps context (m + k) (some (.par left right)) before none after ∧
      ParallelMerge left.writes right.writes after.current.visible
        leftAfter.current.visible rightAfter.current.visible ∧
      ∃ leftDelta rightDelta,
        leftAfter.current.history = before.current.history + leftDelta ∧
        rightAfter.current.history = before.current.history + rightDelta ∧
        after.current.history = before.current.history + leftDelta + rightDelta := by
  have rightAgreement : ProgramAgreement right.reads before.current.visible
      leftAfter.current.visible :=
    leftRun.frame.agreement (fun cell member => noninterfering.right_read member)
  obtain ⟨after, matched⟩ := rightRun.replay leftAfter rightAgreement
  have sequential := (leftRun.seq_lift right).trans matched.right
  refine ⟨after, matched, sequential, sequential.seq_to_parallel, ?_, ?_⟩
  · constructor
    · intro cell outside
      exact (matched.right.frame cell outside).symm
    · intro cell outside
      exact (matched.agreement cell (leftRun.frame cell outside)).symm
  · obtain ⟨leftDelta, leftLedger⟩ := leftRun.ledger_delta
    obtain ⟨rightDelta, rightLedger, finalLedger⟩ := matched.ledger
    exact ⟨leftDelta, rightDelta, leftLedger, rightLedger,
      by simpa only [leftLedger, add_assoc] using finalLedger⟩

theorem parallel_terminates_iff {context : ProgramContext D} {n left right before}
    (noninterfering : Noninterfering left right) :
    (∃ after, Steps context n (some (.par left right)) before none after) ↔
      ∃ after, Steps context n (some (.seq left right)) before none after := by
  constructor
  · rintro ⟨after, steps⟩
    obtain ⟨m, k, intermediate, isolatedRight, sequentialAfter, count,
      leftRun, rightRun, matched, sequential, view⟩ :=
      parallel_sequential_representative noninterfering steps
    exact ⟨sequentialAfter, sequential⟩
  · rintro ⟨after, steps⟩
    exact ⟨after, steps.seq_to_parallel⟩

/-- View equality includes full memory, datasets, the full ledger, hidden memory,
compatible hidden possibilities, and sampling provenance, but not actions. -/
theorem semanticView_endpoint_fields {context : ProgramContext D}
    {left right : World D Primitive}
    (view : semanticView context.model.dynamics left = semanticView context.model.dynamics right) :
    left.current.memory = right.current.memory ∧
      left.current.datasets = right.current.datasets ∧
      left.current.history = right.current.history ∧
      left.current.memory.hidden = right.current.memory.hidden ∧
      compatibleHidden context.model.dynamics left = compatibleHidden context.model.dynamics right ∧
      left.samplingProvenance = right.samplingProvenance := by
  have visible := congrArg SemanticView.visible view
  have observable := congrArg VisibleState.memory visible
  have hidden := congrArg SemanticView.hidden view
  have memory : left.current.memory = right.current.memory := by
    calc
      _ = Memory.assemble left.current.memory.observable left.current.memory.hidden :=
        (Memory.assemble_projections _).symm
      _ = Memory.assemble right.current.memory.observable right.current.memory.hidden :=
        congrArg₂ Memory.assemble observable hidden
      _ = _ := Memory.assemble_projections _
  exact ⟨memory, congrArg VisibleState.datasets visible, congrArg SemanticView.history view,
    hidden, congrArg SemanticView.compatible view, congrArg SemanticView.provenance view⟩

/-- Public correspondence retains well-formedness, the actual model, admission,
and literal run endpoints. No fairness or total-termination hypothesis is added. -/
theorem exec_parallel_correspondence {context : ProgramContext D} {left right before after}
    (execution : executes context (.par left right) before after) :
    ∃ sequentialAfter, executes context (.seq left right) before sequentialAfter ∧
      semanticView context.model.dynamics after =
        semanticView context.model.dynamics sequentialAfter := by
  obtain ⟨n, steps⟩ := execution.2.2
  obtain ⟨m, k, intermediate, isolatedRight, sequentialAfter, count,
    leftRun, rightRun, matched, sequential, view⟩ :=
    parallel_sequential_representative execution.1.2.2 steps
  exact ⟨sequentialAfter, ⟨⟨execution.1.1, execution.1.2.1⟩,
    execution.2.1, n, sequential⟩, view⟩

theorem exec_parallel_project {context : ProgramContext D}
    {left right before after} (initialLedger : History D)
    (ledger : before.current.history = initialLedger)
    (execution : executes context (.par left right) before after) :
    ∃ n m k leftAfter rightAfter leftDelta rightDelta,
      n = m + k ∧
      Steps context n (some (.par left right)) before none after ∧
      executes context left before leftAfter ∧ executes context right before rightAfter ∧
      Steps context m (some left) before none leftAfter ∧
      Steps context k (some right) before none rightAfter ∧
      ProjectedSchedule context m k (some left) (some right) before before before
        none none after leftAfter rightAfter ∧
      ParallelMerge left.writes right.writes after.current.visible
        leftAfter.current.visible rightAfter.current.visible ∧
      leftAfter.current.history = initialLedger + leftDelta ∧
      rightAfter.current.history = initialLedger + rightDelta ∧
      after.current.history = initialLedger + leftDelta + rightDelta := by
  obtain ⟨n, steps⟩ := execution.2.2
  obtain ⟨m, k, leftAfter, rightAfter, leftDelta, rightDelta, count, paired,
    leftRun, rightRun, merge, leftLedger, rightLedger, finalLedger, projected⟩ :=
    parallel_project execution.1.2.2 steps
  exact ⟨n, m, k, leftAfter, rightAfter, leftDelta, rightDelta, count, steps,
    ⟨execution.1.1, execution.2.1, m, leftRun⟩,
    ⟨execution.1.2.1, execution.2.1, k, rightRun⟩, leftRun, rightRun, projected,
    merge, by simpa only [ledger] using leftLedger,
    by simpa only [ledger] using rightLedger, by simpa only [ledger] using finalLedger⟩

theorem exec_parallel_terminates_iff {context : ProgramContext D} {left right before}
    (noninterfering : Noninterfering left right) :
    (∃ after, executes context (.par left right) before after) ↔
      ∃ after, executes context (.seq left right) before after := by
  constructor
  · rintro ⟨after, execution⟩
    obtain ⟨sequentialAfter, sequential, view⟩ := exec_parallel_correspondence execution
    exact ⟨sequentialAfter, sequential⟩
  · rintro ⟨after, execution⟩
    exact ⟨after, exec_seq_to_parallel noninterfering execution⟩

/-- All legal assertions, including nested knowledge, explicit reference scopes,
and arbitrary outer ghosts, are invariant at the reconstructed endpoint. -/
theorem parallel_assertion_correspondence {context : ProgramContext D}
    {left right before after Γ}
    (execution : executes context (.par left right) before after)
    (env : GhostEnv D Primitive Γ) :
    ∃ sequentialAfter, executes context (.seq left right) before sequentialAfter ∧
      ∀ assertion : Assertion Γ,
        satisfies context.interpretation context.model env after assertion ↔
          satisfies context.interpretation context.model env sequentialAfter assertion := by
  obtain ⟨sequentialAfter, sequential, view⟩ := exec_parallel_correspondence execution
  exact ⟨sequentialAfter, sequential, fun assertion =>
    satisfies_congr context.interpretation context.model env
      (exec_admitted execution) (exec_admitted sequential) view assertion⟩

theorem parallel_satisfying_execution_iff {context : ProgramContext D}
    {left right before Γ}
    (noninterfering : Noninterfering left right)
    (env : GhostEnv D Primitive Γ) (assertion : Assertion Γ) :
    (∃ after, executes context (.par left right) before after ∧
      satisfies context.interpretation context.model env after assertion) ↔
    (∃ after, executes context (.seq left right) before after ∧
      satisfies context.interpretation context.model env after assertion) := by
  constructor
  · rintro ⟨after, execution, satisfaction⟩
    obtain ⟨sequentialAfter, sequential, equivalent⟩ :=
      parallel_assertion_correspondence execution env
    exact ⟨sequentialAfter, sequential, (equivalent assertion).mp satisfaction⟩
  · rintro ⟨after, execution, satisfaction⟩
    exact ⟨after, exec_seq_to_parallel noninterfering execution, satisfaction⟩

/-- An admitted epistemic alternative of an endpoint is reconstructed by replay
from an actual hidden rebuilding of the initial world, with the exact same count. -/
theorem endpoint_hidden_replay {context : ProgramContext D}
    {n source target before after alternative}
    (steps : Steps context n source before target after)
    (admitted : Admitted context.model.dynamics alternative)
    (accessible : Accessible after alternative) :
    ∃ rebuiltBefore, rebuiltBefore = before.rebuildHidden alternative.current.memory.hidden ∧
      Admitted context.model.dynamics rebuiltBefore ∧ Accessible before rebuiltBefore ∧
      Steps context n source rebuiltBefore target alternative := by
  let rebuiltBefore := before.rebuildHidden alternative.current.memory.hidden
  have sourceAccessible : Accessible before rebuiltBefore := rebuildHidden_accessible _ _
  have sourceAdmitted : Admitted context.model.dynamics rebuiltBefore := by
    apply (admitted_rebuildHidden_iff _ _ _).mpr
    have compatible := admitted_hidden_mem_compatible admitted
    rw [← compatibleHidden_eq_of_accessible accessible, steps.information.2.1] at compatible
    exact compatible
  obtain ⟨replayed, replayedSteps, replayedAdmitted, replayedAccessible⟩ :=
    steps.accessible_forth sourceAdmitted sourceAccessible
  have equal : alternative = replayed := by
    apply admitted_eq_of_accessible_hidden admitted replayedAdmitted
      (accessible.symm.trans replayedAccessible)
    rw [replayedSteps.information.1]
    exact (World.rebuildHidden_current_hidden before _).symm
  exact ⟨rebuiltBefore, rfl, sourceAdmitted, sourceAccessible,
    by simpa only [equal] using replayedSteps⟩

/-- Forth between admitted endpoint alternatives of two schedules uses hidden
rebuilding and actual replay. The different schedule traces are never asserted
Accessible to one another. -/
theorem correspondence_epistemic_forth {context : ProgramContext D}
    {n m source target otherSource otherTarget before after otherAfter alternative}
    (run : Steps context n source before target after)
    (otherRun : Steps context m otherSource before otherTarget otherAfter)
    (view : semanticView context.model.dynamics after =
      semanticView context.model.dynamics otherAfter)
    (alternativeAdmitted : Admitted context.model.dynamics alternative)
    (accessible : Accessible after alternative) :
    ∃ rebuiltBefore rebuiltAfter,
      rebuiltBefore = before.rebuildHidden alternative.current.memory.hidden ∧
      Admitted context.model.dynamics rebuiltBefore ∧ Accessible before rebuiltBefore ∧
      Steps context n source rebuiltBefore target alternative ∧
      Steps context m otherSource rebuiltBefore otherTarget rebuiltAfter ∧
      Admitted context.model.dynamics rebuiltAfter ∧ Accessible otherAfter rebuiltAfter ∧
      semanticView context.model.dynamics alternative =
        semanticView context.model.dynamics rebuiltAfter := by
  obtain ⟨rebuiltBefore, rebuiltEq, rebuiltAdmitted, sourceAccessible, alternativeRun⟩ :=
    endpoint_hidden_replay run alternativeAdmitted accessible
  obtain ⟨rebuiltAfter, rebuiltRun, endpointAdmitted, endpointAccessible⟩ :=
    otherRun.accessible_forth rebuiltAdmitted sourceAccessible
  have finalView : semanticView context.model.dynamics alternative =
      semanticView context.model.dynamics rebuiltAfter := by
    have visible : alternative.current.visible = rebuiltAfter.current.visible :=
      (accessible_current_visible accessible).symm.trans
        ((congrArg SemanticView.visible view).trans
          (accessible_current_visible endpointAccessible))
    have history : alternative.current.history = rebuiltAfter.current.history :=
      (accessible_history_eq accessible).symm.trans
        ((congrArg SemanticView.history view).trans
          (accessible_history_eq endpointAccessible))
    unfold semanticView
    rw [visible, history, alternativeRun.information.1, rebuiltRun.information.1,
      alternativeRun.information.2.1, rebuiltRun.information.2.1,
      alternativeRun.information.2.2.1, rebuiltRun.information.2.2.1]
  exact ⟨rebuiltBefore, rebuiltAfter, rebuiltEq, rebuiltAdmitted, sourceAccessible,
    alternativeRun, rebuiltRun, endpointAdmitted, endpointAccessible, finalView⟩

theorem correspondence_epistemic_back {context : ProgramContext D}
    {n m source target otherSource otherTarget before after otherAfter alternative}
    (run : Steps context n source before target after)
    (otherRun : Steps context m otherSource before otherTarget otherAfter)
    (view : semanticView context.model.dynamics after =
      semanticView context.model.dynamics otherAfter)
    (alternativeAdmitted : Admitted context.model.dynamics alternative)
    (accessible : Accessible otherAfter alternative) :
    ∃ rebuiltBefore rebuiltAfter,
      rebuiltBefore = before.rebuildHidden alternative.current.memory.hidden ∧
      Admitted context.model.dynamics rebuiltBefore ∧ Accessible before rebuiltBefore ∧
      Steps context m otherSource rebuiltBefore otherTarget alternative ∧
      Steps context n source rebuiltBefore target rebuiltAfter ∧
      Admitted context.model.dynamics rebuiltAfter ∧ Accessible after rebuiltAfter ∧
      semanticView context.model.dynamics alternative =
        semanticView context.model.dynamics rebuiltAfter :=
  correspondence_epistemic_forth otherRun run view.symm alternativeAdmitted accessible

/-- Specialized admitted forth for the sequential representative reconstructed
from a permitted terminating parallel run. -/
theorem parallel_endpoint_epistemic_forth {context : ProgramContext D}
    {n left right before after alternative}
    (noninterfering : Noninterfering left right)
    (steps : Steps context n (some (.par left right)) before none after)
    (alternativeAdmitted : Admitted context.model.dynamics alternative)
    (accessible : Accessible after alternative) :
    ∃ sequentialAfter rebuiltBefore rebuiltAfter,
      Steps context n (some (.seq left right)) before none sequentialAfter ∧
      semanticView context.model.dynamics after =
        semanticView context.model.dynamics sequentialAfter ∧
      rebuiltBefore = before.rebuildHidden alternative.current.memory.hidden ∧
      Admitted context.model.dynamics rebuiltBefore ∧ Accessible before rebuiltBefore ∧
      Steps context n (some (.par left right)) rebuiltBefore none alternative ∧
      Steps context n (some (.seq left right)) rebuiltBefore none rebuiltAfter ∧
      Admitted context.model.dynamics rebuiltAfter ∧ Accessible sequentialAfter rebuiltAfter ∧
      semanticView context.model.dynamics alternative =
        semanticView context.model.dynamics rebuiltAfter := by
  obtain ⟨m, k, intermediate, isolatedRight, sequentialAfter, count,
    leftRun, rightRun, matched, sequential, view⟩ :=
    parallel_sequential_representative noninterfering steps
  obtain ⟨rebuiltBefore, rebuiltAfter, rebuiltEq, sourceAdmitted, sourceAccessible,
    alternativeRun, rebuiltRun, endpointAdmitted, endpointAccessible, finalView⟩ :=
    correspondence_epistemic_forth steps sequential view alternativeAdmitted accessible
  exact ⟨sequentialAfter, rebuiltBefore, rebuiltAfter, sequential, view, rebuiltEq,
    sourceAdmitted, sourceAccessible, alternativeRun, rebuiltRun,
    endpointAdmitted, endpointAccessible, finalView⟩

/-- Back retains the literal sequential representative and both reference runs. -/
theorem parallel_endpoint_epistemic_back {context : ProgramContext D}
    {n left right before after sequentialAfter alternative}
    (steps : Steps context n (some (.par left right)) before none after)
    (sequential : Steps context n (some (.seq left right)) before none sequentialAfter)
    (view : semanticView context.model.dynamics after =
      semanticView context.model.dynamics sequentialAfter)
    (alternativeAdmitted : Admitted context.model.dynamics alternative)
    (accessible : Accessible sequentialAfter alternative) :
    ∃ rebuiltBefore rebuiltAfter,
      rebuiltBefore = before.rebuildHidden alternative.current.memory.hidden ∧
      Admitted context.model.dynamics rebuiltBefore ∧ Accessible before rebuiltBefore ∧
      Steps context n (some (.seq left right)) rebuiltBefore none alternative ∧
      Steps context n (some (.par left right)) rebuiltBefore none rebuiltAfter ∧
      Admitted context.model.dynamics rebuiltAfter ∧ Accessible after rebuiltAfter ∧
      semanticView context.model.dynamics alternative =
        semanticView context.model.dynamics rebuiltAfter :=
  correspondence_epistemic_back steps sequential view alternativeAdmitted accessible

end
end Lara.BHL
