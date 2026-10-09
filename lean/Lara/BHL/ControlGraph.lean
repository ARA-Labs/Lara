import Lara.BHL.ExecutionLaws

namespace Lara.BHL

/-- One source transition has exactly a primitive action or a Boolean guard.
Sequence/parallel propagation belongs to that same transition, not a new action. -/
inductive ControlLabel where
  | command : Primitive → ControlLabel
  | guard : ProgramExpr .boolean → Bool → ControlLabel

/-- Finite symbolic possibilities for one step. No model or assertion decides
which edge is enabled; the independent local effect supplies that condition. -/
def Program.controlEdges : Program → List (Option Program × ControlLabel)
  | .command primitive => [(none, .command primitive)]
  | .seq left right => left.controlEdges.map (fun edge => (seqResidual right edge.1, edge.2))
  | .ite guard left right => [(some left, .guard guard true), (some right, .guard guard false)]
  | .loop guard body =>
      [(some (.seq body (.loop guard body)), .guard guard true), (none, .guard guard false)]
  | .par left right =>
      left.controlEdges.map (fun edge => (parLeftResidual right edge.1, edge.2)) ++
        right.controlEdges.map (fun edge => (parRightResidual left edge.1, edge.2))

/-- A loop revisits a finite family of residual syntax; it does not require a
bound on its iteration count. Parallel control uses the finite Cartesian product. -/
def Program.residuals : Program → List Program
  | .command primitive => [.command primitive]
  | .seq left right => left.residuals.map (fun next => .seq next right) ++ right.residuals
  | .ite guard left right => .ite guard left right :: (left.residuals ++ right.residuals)
  | .loop guard body => .loop guard body :: body.residuals.map (fun next => .seq next (.loop guard body))
  | .par left right =>
      left.residuals.flatMap (fun nextLeft =>
        right.residuals.map (fun nextRight => .par nextLeft nextRight)) ++
          (left.residuals ++ right.residuals)

def Program.controlNodes (program : Program) : List (Option Program) :=
  none :: program.residuals.map some

variable {D : Type} [MeasurableSpace D]

/-- This is one primitive or guard's independently defined effect, not a
predicate interpreting a whole execution, log, Hoare triple or WLP. -/
def ControlLabel.effect (context : ProgramContext D) (label : ControlLabel)
    (before after : World D Primitive) : Prop :=
  match label with
  | .command primitive => ∃ visible delta,
      primitiveEffect context.interpretation primitive before.current.visible = some (visible, delta) ∧
        after = before.extend (commandState before.current primitive visible delta)
  | .guard expression value =>
      evalProgramExpr context.interpretation before.current.visible expression = some value ∧ before = after

theorem Program.mem_residuals (program : Program) : program ∈ program.residuals := by
  induction program with
  | command primitive => simp [residuals]
  | seq left right ihLeft ihRight =>
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨left, ihLeft, rfl⟩))
  | ite guard left right ihLeft ihRight => exact List.mem_cons_self
  | loop guard body ihBody => exact List.mem_cons_self
  | par left right ihLeft ihRight =>
      apply List.mem_append.mpr
      left
      exact List.mem_flatMap.mpr ⟨left, ihLeft, List.mem_map.mpr ⟨right, ihRight, rfl⟩⟩

theorem Program.residuals_closed (program : Program) :
    ∀ member ∈ program.residuals, member.residuals ⊆ program.residuals := by
  induction program with
  | command primitive =>
      intro member hmember next hnext
      simp only [residuals, List.mem_singleton] at hmember
      subst member
      exact hnext
  | seq left right ihLeft ihRight =>
      intro member hmember next hnext
      rcases List.mem_append.mp hmember with hleft | hright
      · rcases List.mem_map.mp hleft with ⟨child, hchild, rfl⟩
        rcases List.mem_append.mp hnext with hchildNext | hrightNext
        · rcases List.mem_map.mp hchildNext with ⟨nextChild, hnextChild, rfl⟩
          exact List.mem_append.mpr (Or.inl (List.mem_map.mpr
            ⟨nextChild, ihLeft child hchild hnextChild, rfl⟩))
        · exact List.mem_append.mpr (Or.inr hrightNext)
      · exact List.mem_append.mpr (Or.inr (ihRight member hright hnext))
  | ite guard left right ihLeft ihRight =>
      intro member hmember next hnext
      rcases List.mem_cons.mp hmember with rfl | hmember
      · exact hnext
      · rcases List.mem_append.mp hmember with hleft | hright
        · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr
            (Or.inl (ihLeft member hleft hnext))))
        · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr
            (Or.inr (ihRight member hright hnext))))
  | loop guard body ihBody =>
      intro member hmember next hnext
      rcases List.mem_cons.mp hmember with rfl | hmember
      · exact hnext
      · rcases List.mem_map.mp hmember with ⟨child, hchild, rfl⟩
        rcases List.mem_append.mp hnext with hchildNext | hloopNext
        · rcases List.mem_map.mp hchildNext with ⟨nextChild, hnextChild, rfl⟩
          exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr
            ⟨nextChild, ihBody child hchild hnextChild, rfl⟩))
        · exact hloopNext
  | par left right ihLeft ihRight =>
      intro member hmember next hnext
      rcases List.mem_append.mp hmember with hpair | hsingle
      · rcases List.mem_flatMap.mp hpair with ⟨childLeft, hchildLeft, hpair⟩
        rcases List.mem_map.mp hpair with ⟨childRight, hchildRight, rfl⟩
        rcases List.mem_append.mp hnext with hpairNext | hsingleNext
        · rcases List.mem_flatMap.mp hpairNext with ⟨nextLeft, hnextLeft, hpairNext⟩
          rcases List.mem_map.mp hpairNext with ⟨nextRight, hnextRight, rfl⟩
          exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
            ⟨nextLeft, ihLeft childLeft hchildLeft hnextLeft,
              List.mem_map.mpr ⟨nextRight, ihRight childRight hchildRight hnextRight, rfl⟩⟩))
        · rcases List.mem_append.mp hsingleNext with hleftNext | hrightNext
          · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr
              (Or.inl (ihLeft childLeft hchildLeft hleftNext))))
          · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr
              (Or.inr (ihRight childRight hchildRight hrightNext))))
      · rcases List.mem_append.mp hsingle with hleft | hright
        · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr
            (Or.inl (ihLeft member hleft hnext))))
        · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr
            (Or.inr (ihRight member hright hnext))))

theorem Program.source_mem_controlNodes (program : Program) :
    some program ∈ program.controlNodes :=
  List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨program, program.mem_residuals, rfl⟩))

theorem Program.terminal_mem_controlNodes (program : Program) : none ∈ program.controlNodes :=
  List.mem_cons_self

theorem Step.control_edge {context : ProgramContext D} {source target before after}
    (step : Step context source before target after) :
    ∀ program, source = some program →
      ∃ label, (target, label) ∈ program.controlEdges ∧ label.effect context before after := by
  induction step with
  | command enabled =>
      intro program heq
      cases heq
      exact ⟨.command _, List.mem_singleton_self _, _, _, enabled, rfl⟩
  | seqContinue child ih =>
      intro program heq
      cases heq
      obtain ⟨label, hlabel, heffect⟩ := ih _ rfl
      exact ⟨label, List.mem_map.mpr ⟨_, hlabel, rfl⟩, heffect⟩
  | seqFinish child ih =>
      intro program heq
      cases heq
      obtain ⟨label, hlabel, heffect⟩ := ih _ rfl
      exact ⟨label, List.mem_map.mpr ⟨_, hlabel, rfl⟩, heffect⟩
  | ifTrue enabled =>
      intro program heq
      cases heq
      exact ⟨_, List.mem_cons_self, enabled, rfl⟩
  | ifFalse enabled =>
      intro program heq
      cases heq
      exact ⟨.guard _ false, List.mem_cons_of_mem _ (List.mem_singleton_self _), enabled, rfl⟩
  | loopTrue enabled =>
      intro program heq
      cases heq
      exact ⟨_, List.mem_cons_self, enabled, rfl⟩
  | loopFalse enabled =>
      intro program heq
      cases heq
      exact ⟨.guard _ false, List.mem_cons_of_mem _ (List.mem_singleton_self _), enabled, rfl⟩
  | parLeftContinue child ih =>
      intro program heq
      cases heq
      obtain ⟨label, hlabel, heffect⟩ := ih _ rfl
      exact ⟨label, List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨_, hlabel, rfl⟩)), heffect⟩
  | parLeftFinish child ih =>
      intro program heq
      cases heq
      obtain ⟨label, hlabel, heffect⟩ := ih _ rfl
      exact ⟨label, List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨_, hlabel, rfl⟩)), heffect⟩
  | parRightContinue child ih =>
      intro program heq
      cases heq
      obtain ⟨label, hlabel, heffect⟩ := ih _ rfl
      exact ⟨label, List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, hlabel, rfl⟩)), heffect⟩
  | parRightFinish child ih =>
      intro program heq
      cases heq
      obtain ⟨label, hlabel, heffect⟩ := ih _ rfl
      exact ⟨label, List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, hlabel, rfl⟩)), heffect⟩

theorem Program.control_edge_step (program : Program) {context : ProgramContext D}
    {target : Option Program} {label : ControlLabel} {before after : World D Primitive}
    (member : (target, label) ∈ program.controlEdges)
    (effect : label.effect context before after) :
    Step context (some program) before target after := by
  induction program generalizing target label with
  | command primitive =>
      simp only [controlEdges, List.mem_singleton] at member
      rcases Prod.mk.inj member with ⟨rfl, rfl⟩
      obtain ⟨visible, delta, enabled, rfl⟩ := effect
      exact .command enabled
  | seq left right ihLeft ihRight =>
      obtain ⟨⟨next, innerLabel⟩, innerMember, equal⟩ := List.mem_map.mp member
      rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
      have child := ihLeft innerMember effect
      cases next with
      | none => exact .seqFinish child
      | some residual => exact .seqContinue child
  | ite guard left right ihLeft ihRight =>
      simp only [controlEdges, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with equal | equal
      · rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
        obtain ⟨enabled, rfl⟩ := effect
        exact .ifTrue enabled
      · rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
        obtain ⟨enabled, rfl⟩ := effect
        exact .ifFalse enabled
  | loop guard body ihBody =>
      simp only [controlEdges, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with equal | equal
      · rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
        obtain ⟨enabled, rfl⟩ := effect
        exact .loopTrue enabled
      · rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
        obtain ⟨enabled, rfl⟩ := effect
        exact .loopFalse enabled
  | par left right ihLeft ihRight =>
      rcases List.mem_append.mp member with leftMember | rightMember
      · obtain ⟨⟨next, innerLabel⟩, innerMember, equal⟩ := List.mem_map.mp leftMember
        rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
        have child := ihLeft innerMember effect
        cases next with
        | none => exact .parLeftFinish child
        | some residual => exact .parLeftContinue child
      · obtain ⟨⟨next, innerLabel⟩, innerMember, equal⟩ := List.mem_map.mp rightMember
        rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
        have child := ihRight innerMember effect
        cases next with
        | none => exact .parRightFinish child
        | some residual => exact .parRightContinue child

theorem Step.control_edge_iff {context : ProgramContext D}
    {program : Program} {target : Option Program} {before after : World D Primitive} :
    Step context (some program) before target after ↔
      ∃ label, (target, label) ∈ program.controlEdges ∧ label.effect context before after :=
  ⟨fun step => step.control_edge program rfl,
    fun ⟨_, member, effect⟩ => program.control_edge_step member effect⟩

@[simp] theorem Program.some_mem_controlNodes {program residual : Program} :
    some residual ∈ program.controlNodes ↔ residual ∈ program.residuals := by
  simp [controlNodes]

/-- Every possible symbolic edge stays inside the finite residual family,
independently of the state values and whether that edge is enabled. -/
theorem Program.control_edge_target (program : Program)
    {target : Option Program} {label : ControlLabel}
    (member : (target, label) ∈ program.controlEdges) :
    target ∈ program.controlNodes := by
  induction program generalizing target label with
  | command primitive =>
      simp only [controlEdges, List.mem_singleton] at member
      rcases Prod.mk.inj member with ⟨rfl, rfl⟩
      exact terminal_mem_controlNodes _
  | seq left right ihLeft ihRight =>
      obtain ⟨⟨next, innerLabel⟩, innerMember, equal⟩ := List.mem_map.mp member
      rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
      have child := ihLeft innerMember
      cases next with
      | none =>
          apply some_mem_controlNodes.mpr
          exact List.mem_append.mpr (Or.inr right.mem_residuals)
      | some residual =>
          apply some_mem_controlNodes.mpr
          exact List.mem_append.mpr (Or.inl (List.mem_map.mpr
            ⟨residual, some_mem_controlNodes.mp child, rfl⟩))
  | ite guard left right ihLeft ihRight =>
      simp only [controlEdges, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with equal | equal
      · rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
        apply some_mem_controlNodes.mpr
        exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl left.mem_residuals)))
      · rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
        apply some_mem_controlNodes.mpr
        exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr right.mem_residuals)))
  | loop guard body ihBody =>
      simp only [controlEdges, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with equal | equal
      · rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
        apply some_mem_controlNodes.mpr
        exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨body, body.mem_residuals, rfl⟩))
      · rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
        exact terminal_mem_controlNodes _
  | par left right ihLeft ihRight =>
      rcases List.mem_append.mp member with leftMember | rightMember
      · obtain ⟨⟨next, innerLabel⟩, innerMember, equal⟩ := List.mem_map.mp leftMember
        rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
        have child := ihLeft innerMember
        cases next with
        | none =>
            apply some_mem_controlNodes.mpr
            exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr right.mem_residuals)))
        | some residual =>
            apply some_mem_controlNodes.mpr
            exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
              ⟨residual, some_mem_controlNodes.mp child,
                List.mem_map.mpr ⟨right, right.mem_residuals, rfl⟩⟩))
      · obtain ⟨⟨next, innerLabel⟩, innerMember, equal⟩ := List.mem_map.mp rightMember
        rcases Prod.mk.inj equal with ⟨rfl, rfl⟩
        have child := ihRight innerMember
        cases next with
        | none =>
            apply some_mem_controlNodes.mpr
            exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl left.mem_residuals)))
        | some residual =>
            apply some_mem_controlNodes.mpr
            exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
              ⟨left, left.mem_residuals,
                List.mem_map.mpr ⟨residual, some_mem_controlNodes.mp child, rfl⟩⟩))

theorem Step.controlNodes_closed {context : ProgramContext D}
    {source target : Option Program} {before after : World D Primitive}
    (step : Step context source before target after) (program : Program)
    (sourceMember : source ∈ program.controlNodes) : target ∈ program.controlNodes := by
  obtain ⟨current, rfl⟩ := step.source_some
  obtain ⟨label, edge, _⟩ := step.control_edge current rfl
  have targetMember := current.control_edge_target edge
  cases target with
  | none => exact program.terminal_mem_controlNodes
  | some residual =>
      apply Program.some_mem_controlNodes.mpr
      exact program.residuals_closed current
        (Program.some_mem_controlNodes.mp sourceMember)
        (Program.some_mem_controlNodes.mp targetMember)

theorem Steps.controlNodes_closed {context : ProgramContext D}
    {n : Nat} {source target : Option Program} {before after : World D Primitive}
    (steps : Steps context n source before target after) (program : Program)
    (sourceMember : source ∈ program.controlNodes) : target ∈ program.controlNodes := by
  induction steps with
  | refl => exact sourceMember
  | cons first rest ih => exact ih (first.controlNodes_closed program sourceMember)

end Lara.BHL
