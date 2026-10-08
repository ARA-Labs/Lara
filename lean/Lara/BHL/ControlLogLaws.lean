import Lara.BHL.ControlLogData

namespace Lara.BHL

noncomputable section

variable {D : Type} [MeasurableSpace D]

/-- A local ghost edge can be realized without identifying its ghost command
state with the literal operational command state. Guards keep the actual world. -/
theorem ControlLabel.viewEffect_replay (ctx : ProgramContext D) (label : ControlLabel)
    {before ghostBefore ghostAfter : World D Primitive}
    (initial : Admitted ctx.model.dynamics before)
    (view : semanticView ctx.model.dynamics before = semanticView ctx.model.dynamics ghostBefore)
    (effect : label.viewEffect ctx ghostBefore ghostAfter) :
    ∃ after, label.effect ctx before after ∧ Admitted ctx.model.dynamics after ∧
      semanticView ctx.model.dynamics after = semanticView ctx.model.dynamics ghostAfter := by
  cases label with
  | command primitive =>
      obtain ⟨visible, delta, enabled, output⟩ := effect
      have evaluated : evalTerm ctx.interpretation ctx.model GhostEnv.empty
          (semanticView ctx.model.dynamics before) (primitive.viewTerm []) =
            some (semanticView ctx.model.dynamics ghostAfter) := by
        rw [view, output]
        exact evalPrimitive_viewTerm_enabled ctx.interpretation ctx.model GhostEnv.empty
          (semanticView ctx.model.dynamics ghostBefore) primitive visible delta enabled
      obtain ⟨after, step, admitted, terminal⟩ :=
        primitive_viewTerm_realized ctx GhostEnv.empty initial evaluated
      obtain ⟨actualLabel, member, actualEffect⟩ := step.control_edge (.command primitive) rfl
      simp only [Program.controlEdges, List.mem_singleton] at member
      rcases Prod.mk.inj member with ⟨_, equal⟩
      cases equal
      exact ⟨after, actualEffect, admitted, terminal⟩
  | guard expression value =>
      obtain ⟨enabled, same⟩ := effect
      have visible := congrArg SemanticView.visible view
      change before.current.visible = ghostBefore.current.visible at visible
      have actualEnabled : evalProgramExpr ctx.interpretation before.current.visible expression =
          some value := by
        rw [visible]
        exact enabled
      exact ⟨before, ⟨actualEnabled, rfl⟩, initial, view.trans same⟩

/-- Literal actions satisfy the full-view local relation used by the finite log. -/
theorem ControlLabel.effect_viewEffect (ctx : ProgramContext D) (label : ControlLabel)
    {before after : World D Primitive} (effect : label.effect ctx before after) :
    label.viewEffect ctx before after := by
  cases label with
  | command primitive =>
      obtain ⟨visible, delta, enabled, rfl⟩ := effect
      have step : Step ctx (some (.command primitive)) before none
          (before.extend (commandState before.current primitive visible delta)) := .command enabled
      have evaluated := primitive_viewTerm_successor ctx GhostEnv.empty step
      rw [evalPrimitive_viewTerm_enabled ctx.interpretation ctx.model GhostEnv.empty
        (semanticView ctx.model.dynamics before) primitive visible delta enabled] at evaluated
      exact ⟨visible, delta, enabled, (Option.some.inj evaluated).symm⟩
  | guard expression value =>
      obtain ⟨enabled, rfl⟩ := effect
      exact ⟨enabled, rfl⟩

namespace ControlLog

/-- The forward invariant before a finite execution has reached its terminal
configuration. The endpoint carries a residual code rather than necessarily zero. -/
def Ready (ctx : ProgramContext D) (program : Program) (log : ControlLog D)
    (node : Option Program) : Prop :=
  Admitted ctx.model.dynamics log.source ∧
    log.readCell 0 .control = some (program.controlCode (some program)) ∧
    log.readCell 0 .commands = some 0 ∧
    log.readCell log.controlStates.length .control = some (program.controlCode node) ∧
    log.readCell log.controlStates.length .commands = some (log.programStates.length : Int) ∧
    ∀ index, index < log.controlStates.length → log.edge ctx program index

/-- Append one metadata row; only command labels append program states. -/
def append (log : ControlLog D) (program : Program) (node : Option Program)
    (states : List (State D Primitive)) : ControlLog D where
  source := log.source
  programStates := log.programStates ++ states
  controlSeed := log.controlSeed
  controlStates := log.controlStates ++
    [ControlMetadata.state log.source.initial (program.controlCode node)
      ((log.programStates.length + states.length : Nat) : Int)]

omit [MeasurableSpace D] in
@[simp] theorem append_source (log : ControlLog D) (program : Program)
    (node : Option Program) (states : List (State D Primitive)) :
    (log.append program node states).source = log.source := rfl

omit [MeasurableSpace D] in
@[simp] theorem append_program_length (log : ControlLog D) (program : Program)
    (node : Option Program) (states : List (State D Primitive)) :
    (log.append program node states).programStates.length =
      log.programStates.length + states.length := by simp [append]

omit [MeasurableSpace D] in
@[simp] theorem append_control_length (log : ControlLog D) (program : Program)
    (node : Option Program) (states : List (State D Primitive)) :
    (log.append program node states).controlStates.length = log.controlStates.length + 1 := by
  simp [append]

omit [MeasurableSpace D] in
 theorem append_programPrefix (log : ControlLog D) (program : Program)
    (node : Option Program) (states : List (State D Primitive)) (count : Nat)
    (bound : count ≤ log.programStates.length) :
    (log.append program node states).programPrefix count = log.programPrefix count := by
  simp [programPrefix, append, List.take_append, Nat.sub_eq_zero_of_le bound]

omit [MeasurableSpace D] in
 theorem append_readCell (log : ControlLog D) (program : Program)
    (node : Option Program) (states : List (State D Primitive)) (index : Nat)
    (bound : index ≤ log.controlStates.length) (cell : LogCell) :
    (log.append program node states).readCell index cell = log.readCell index cell := by
  simp [readCell, metadataPrefix, append, List.take_append, Nat.sub_eq_zero_of_le bound]

omit [MeasurableSpace D] in
 theorem append_readCell_end_control (log : ControlLog D) (program : Program)
    (node : Option Program) (states : List (State D Primitive)) :
    (log.append program node states).readCell (log.controlStates.length + 1) .control =
      some (program.controlCode node) := by
  have bound : (log.append program node states).controlStates.length ≤
      log.controlStates.length + 1 := by simp only [append_control_length, le_refl]
  unfold readCell metadataPrefix
  rw [List.take_of_length_le bound]
  simp only [append]
  rw [← World.appendStates_assoc, World.appendStates_singleton, World.extend_current]
  exact ControlMetadata.state_read_control _ _ _

omit [MeasurableSpace D] in
 theorem append_readCell_end_commands (log : ControlLog D) (program : Program)
    (node : Option Program) (states : List (State D Primitive)) :
    (log.append program node states).readCell (log.controlStates.length + 1) .commands =
      some ((log.programStates.length + states.length : Nat) : Int) := by
  have bound : (log.append program node states).controlStates.length ≤
      log.controlStates.length + 1 := by simp only [append_control_length, le_refl]
  unfold readCell metadataPrefix
  rw [List.take_of_length_le bound]
  simp only [append]
  rw [← World.appendStates_assoc, World.appendStates_singleton, World.extend_current]
  exact ControlMetadata.state_read_commands _ _ _

omit [MeasurableSpace D] in
 theorem append_terminal (log : ControlLog D) (program : Program)
    (node : Option Program) (states : List (State D Primitive)) :
    (log.append program node states).terminal = log.terminal.appendStates states := by
  exact (World.appendStates_assoc _ _ _).symm

omit [MeasurableSpace D] in
@[simp] theorem programPrefix_length (log : ControlLog D) :
    log.programPrefix log.programStates.length = log.terminal := by
  simp [programPrefix, terminal]

omit [MeasurableSpace D] in
@[simp] theorem programPrefix_zero (log : ControlLog D) : log.programPrefix 0 = log.source := by
  simp [programPrefix]

 theorem append_edge_previous (ctx : ProgramContext D) (program : Program)
    (log : ControlLog D) (node : Option Program) (states : List (State D Primitive))
    (index : Nat) (bound : index < log.controlStates.length)
    (edge : log.edge ctx program index) :
    (log.append program node states).edge ctx program index := by
  obtain ⟨current, member, target, label, transition, code, nextCode,
    count, nextCount, countBound, nextBound, readCount, readNext,
    admitted, nextAdmitted, effect, increment⟩ := edge
  refine ⟨current, member, target, label, transition, ?_, ?_, count, nextCount,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, increment⟩
  · rw [append_readCell log program node states index (by omega)]
    exact code
  · rw [append_readCell log program node states (index + 1) (by omega)]
    exact nextCode
  · simp only [append_program_length]
    omega
  · simp only [append_program_length]
    omega
  · rw [append_readCell log program node states index (by omega)]
    exact readCount
  · rw [append_readCell log program node states (index + 1) (by omega)]
    exact readNext
  · rw [append_programPrefix log program node states count countBound]
    exact admitted
  · rw [append_programPrefix log program node states nextCount nextBound]
    exact nextAdmitted
  · rw [append_programPrefix log program node states count countBound,
      append_programPrefix log program node states nextCount nextBound]
    exact effect

 theorem append_ready (ctx : ProgramContext D) (program : Program)
    (log : ControlLog D) {current : Program} {target : Option Program} {label : ControlLabel}
    (ready : log.Ready ctx program (some current))
    (member : current ∈ program.residuals)
    (transition : (target, label) ∈ current.controlEdges)
    (states : List (State D Primitive))
    (admitted : Admitted ctx.model.dynamics log.terminal)
    (nextAdmitted : Admitted ctx.model.dynamics (log.terminal.appendStates states))
    (effect : label.viewEffect ctx log.terminal (log.terminal.appendStates states))
    (increment : match label with
      | .guard _ _ => states.length = 0
      | .command _ => states.length = 1) :
    (log.append program target states).Ready ctx program target := by
  obtain ⟨initial, sourceCode, sourceCount, finalCode, finalCount, edges⟩ := ready
  refine ⟨initial, ?_, ?_, ?_, ?_, ?_⟩
  · rw [append_readCell log program target states 0 (Nat.zero_le _)]
    exact sourceCode
  · rw [append_readCell log program target states 0 (Nat.zero_le _)]
    exact sourceCount
  · rw [append_control_length]
    exact append_readCell_end_control _ _ _ _
  · rw [append_control_length, append_program_length]
    exact append_readCell_end_commands _ _ _ _
  · intro index bound
    rw [append_control_length] at bound
    by_cases previous : index < log.controlStates.length
    · exact append_edge_previous ctx program log target states index previous (edges index previous)
    · have equal : index = log.controlStates.length := by omega
      subst index
      refine ⟨current, member, target, label, transition, ?_, ?_,
        log.programStates.length, log.programStates.length + states.length,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [append_readCell log program target states log.controlStates.length (le_refl _)]
        exact finalCode
      · exact append_readCell_end_control _ _ _ _
      · simp only [append_program_length]
        omega
      · rw [append_program_length]
      · rw [append_readCell log program target states log.controlStates.length (le_refl _)]
        exact finalCount
      · exact append_readCell_end_commands _ _ _ _
      · rw [append_programPrefix log program target states log.programStates.length (le_refl _),
          programPrefix_length]
        exact admitted
      · rw [← append_program_length log program target states, programPrefix_length, append_terminal]
        exact nextAdmitted
      · rw [append_programPrefix log program target states log.programStates.length (le_refl _),
          programPrefix_length, ← append_program_length log program target states,
          programPrefix_length, append_terminal]
        exact effect
      · cases label <;> simp_all

 theorem ready_valid {ctx : ProgramContext D} {program : Program} {log : ControlLog D}
    (ready : log.Ready ctx program none) : log.Valid ctx program := by
  simpa only [Ready, Valid, Program.controlCode_none] using ready

/-- The final program ghost prefix is admitted by the same local checks; no
admission condition is imposed on the independent metadata carriers. -/
theorem terminal_admitted (ctx : ProgramContext D) (program : Program)
    (log : ControlLog D) (valid : log.Valid ctx program) :
    Admitted ctx.model.dynamics log.terminal := by
  obtain ⟨sourceAdmitted, _, initialCount, _, finalCount, edges⟩ := valid
  by_cases empty : log.controlStates = []
  · have controlLength : log.controlStates.length = 0 := by simp only [empty, List.length_nil]
    rw [controlLength] at finalCount
    have lengthInt : (log.programStates.length : Int) = 0 :=
      Option.some.inj (finalCount.symm.trans initialCount)
    have lengthZero : log.programStates.length = 0 := by exact_mod_cast lengthInt
    have statesEmpty : log.programStates = [] := by
      cases states : log.programStates with
      | nil => rfl
      | cons head tail => simp only [states, List.length_cons] at lengthZero; omega
    simpa only [terminal, statesEmpty, World.appendStates_nil] using sourceAdmitted
  · have positive : 0 < log.controlStates.length := List.length_pos_iff.mpr empty
    let index := log.controlStates.length - 1
    have bound : index < log.controlStates.length := by dsimp [index]; omega
    have finalIndex : index + 1 = log.controlStates.length := by dsimp [index]; omega
    obtain ⟨_, _, _, _, _, _, _, _, nextCount, _, _, _, readNext,
      _, nextAdmitted, _, _⟩ := edges index bound
    rw [finalIndex] at readNext
    have countEqual : nextCount = log.programStates.length := by
      exact_mod_cast (Option.some.inj (readNext.symm.trans finalCount))
    simpa only [countEqual, programPrefix_length] using nextAdmitted

/-- Replay the suffix of an arbitrary locally checked log. The induction counts
metadata rows, including guards, and reads primitive counts as typed integers. -/
theorem decode_suffix (ctx : ProgramContext D) (program : Program) (log : ControlLog D)
    (valid : log.Valid ctx program) (remaining : Nat) :
    ∀ (index : Nat) (node : Option Program) (count : Nat) (before : World D Primitive),
      index + remaining = log.controlStates.length →
      node ∈ program.controlNodes → count ≤ log.programStates.length →
      log.readCell index .control = some (program.controlCode node) →
      log.readCell index .commands = some (count : Int) →
      Admitted ctx.model.dynamics before →
      semanticView ctx.model.dynamics before =
        semanticView ctx.model.dynamics (log.programPrefix count) →
      ∃ after, Steps ctx remaining node before none after ∧
        semanticView ctx.model.dynamics after = semanticView ctx.model.dynamics log.terminal := by
  obtain ⟨_, _, _, terminalCode, terminalCount, edges⟩ := valid
  induction remaining with
  | zero =>
      intro index node count before length member countBound code commands initial view
      have indexEqual : index = log.controlStates.length := by omega
      subst index
      have codeEqual : program.controlCode node = 0 := Option.some.inj (code.symm.trans terminalCode)
      have nodeEqual : node = none := (program.controlCode_eq_zero_iff node).mp codeEqual
      subst node
      have countEqual : count = log.programStates.length := by
        have equal := Option.some.inj (commands.symm.trans terminalCount)
        omega
      subst count
      exact ⟨before, .refl _ _, by simpa only [programPrefix_length] using view⟩
  | succ remaining ih =>
      intro index node count before length member countBound code commands initial view
      have indexBound : index < log.controlStates.length := by omega
      obtain ⟨current, currentMember, target, label, transition, currentCode, nextCode,
        currentCount, nextCount, currentBound, nextBound, currentRead, nextRead,
        currentAdmitted, nextAdmitted, effect, increment⟩ := edges index indexBound
      have currentNode : some current ∈ program.controlNodes :=
        Program.some_mem_controlNodes.mpr currentMember
      have nodeEqual : node = some current := program.controlCode_injective member currentNode
        (Option.some.inj (code.symm.trans currentCode))
      subst node
      have countEqual : count = currentCount := by
        have equal := Option.some.inj (commands.symm.trans currentRead)
        omega
      subst currentCount
      obtain ⟨intermediate, actualEffect, admitted, terminalView⟩ :=
        label.viewEffect_replay ctx initial view effect
      have first := current.control_edge_step transition actualEffect
      obtain ⟨after, rest, afterView⟩ := ih (index + 1) target nextCount intermediate
        (by omega) (program.control_edge_target_mem_controlNodes currentNode transition)
        nextBound nextCode nextRead admitted terminalView
      exact ⟨after, .cons first rest, afterView⟩

/-- Every locally valid finite ghost log decodes from every admitted literal
source having its complete source view, for any well-formed source program. -/
theorem decode (ctx : ProgramContext D) (program : Program) (log : ControlLog D)
    {before : World D Primitive} (initial : Admitted ctx.model.dynamics before)
    (valid : log.Valid ctx program)
    (sourceView : semanticView ctx.model.dynamics before = semanticView ctx.model.dynamics log.source)
    (wellFormed : program.WellFormed) :
    ∃ after, executes ctx program before after ∧
      semanticView ctx.model.dynamics after = semanticView ctx.model.dynamics log.terminal := by
  obtain ⟨after, steps, view⟩ := decode_suffix ctx program log valid log.controlStates.length
    0 (some program) 0 before (by omega) program.source_mem_controlNodes (Nat.zero_le _)
    valid.2.1 valid.2.2.1 initial (by simpa only [programPrefix_zero] using sourceView)
  exact ⟨after, ⟨wellFormed, initial, log.controlStates.length, steps⟩, view⟩

end ControlLog

/-- Extend an existing forward log by all actual small steps. This retains the
root residual membership and literal endpoint invariant through loop revisits
and either noninterfering parallel scheduling choice. -/
theorem Steps.controlLog_encode {ctx : ProgramContext D}
    {length : Nat} {source target : Option Program} {before after : World D Primitive}
    (steps : Steps ctx length source before target after) (program : Program)
    (log : ControlLog D) (ready : log.Ready ctx program source)
    (member : source ∈ program.controlNodes)
    (initial : Admitted ctx.model.dynamics before) (endpoint : log.terminal = before) :
    ∃ encoded : ControlLog D, encoded.source = log.source ∧
      encoded.terminal = after ∧ encoded.Ready ctx program target := by
  revert ready member initial endpoint
  induction steps generalizing log with
  | refl =>
      intro ready member initial endpoint
      exact ⟨log, rfl, endpoint, ready⟩
  | @cons length source middle target before intermediate after first rest ih =>
      intro ready member initial endpoint
      obtain ⟨current, sourceEqual⟩ := first.source_some
      subst source
      obtain ⟨label, transition, effect⟩ := first.control_edge current rfl
      have currentMember := Program.some_mem_controlNodes.mp member
      have middleMember := first.controlNodes_closed program member
      have intermediateAdmitted := first.admitted initial
      have viewEffect := label.effect_viewEffect ctx effect
      cases label with
      | command primitive =>
          obtain ⟨visible, delta, enabled, intermediateEqual⟩ := effect
          let states := [commandState before.current primitive visible delta]
          have appendedEndpoint : (log.append program middle states).terminal = intermediate := by
            rw [ControlLog.append_terminal, endpoint]
            exact intermediateEqual.symm
          have appendedReady : (log.append program middle states).Ready ctx program middle := by
            apply ControlLog.append_ready ctx program log ready currentMember transition states
            · simpa only [endpoint] using initial
            · rw [← ControlLog.append_terminal log program middle states, appendedEndpoint]
              exact intermediateAdmitted
            · rfl
            · rw [← ControlLog.append_terminal log program middle states, appendedEndpoint, endpoint]
              exact viewEffect
          obtain ⟨encoded, sourcePreserved, terminal, finalReady⟩ :=
            ih (log.append program middle states) appendedReady middleMember
              intermediateAdmitted appendedEndpoint
          exact ⟨encoded, sourcePreserved, terminal, finalReady⟩
      | guard expression value =>
          obtain ⟨enabled, intermediateEqual⟩ := effect
          have appendedEndpoint : (log.append program middle []).terminal = intermediate := by
            rw [ControlLog.append_terminal, World.appendStates_nil, endpoint]
            exact intermediateEqual
          have appendedReady : (log.append program middle []).Ready ctx program middle := by
            apply ControlLog.append_ready ctx program log ready currentMember transition []
            · simpa only [endpoint] using initial
            · rw [← ControlLog.append_terminal log program middle [], appendedEndpoint]
              exact intermediateAdmitted
            · rfl
            · rw [← ControlLog.append_terminal log program middle [], appendedEndpoint, endpoint]
              exact viewEffect
          obtain ⟨encoded, sourcePreserved, terminal, finalReady⟩ :=
            ih (log.append program middle []) appendedReady middleMember
              intermediateAdmitted appendedEndpoint
          exact ⟨encoded, sourcePreserved, terminal, finalReady⟩

/-- Every public execution has a finite log whose source and terminal are the
literal execution worlds. Administrative guards appear only in control states. -/
theorem ControlLog.encode (ctx : ProgramContext D) (program : Program)
    {before after : World D Primitive} (execution : executes ctx program before after) :
    ∃ log : ControlLog D, log.source = before ∧ log.terminal = after ∧ log.Valid ctx program := by
  let seed : ControlLog D :=
    ⟨before, [], ControlMetadata.seed before.initial (program.controlCode (some program)), []⟩
  have ready : seed.Ready ctx program (some program) := by
    refine ⟨execution.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · exact ControlMetadata.seed_read_control _ _
    · exact ControlMetadata.seed_read_commands _ _
    · exact ControlMetadata.seed_read_control _ _
    · exact ControlMetadata.seed_read_commands _ _
    · intro index bound
      change index < 0 at bound
      omega
  have endpoint : seed.terminal = before := World.appendStates_nil _
  obtain ⟨length, steps⟩ := execution.2.2
  obtain ⟨log, source, terminal, finalReady⟩ := steps.controlLog_encode program seed ready
    program.source_mem_controlNodes execution.2.1 endpoint
  exact ⟨log, source, terminal, ControlLog.ready_valid finalReady⟩

end
end Lara.BHL
