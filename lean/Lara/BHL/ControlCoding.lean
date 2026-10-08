import Lara.BHL.ControlGraph

namespace Lara.BHL

/-- The first occurrence in the actual finite control graph. Repeated residual
syntax shares a code; a node outside the graph receives its length. -/
noncomputable def Program.controlCode (program : Program) (node : Option Program) : Int := by
  classical
  exact Int.ofNat (program.controlNodes.idxOf node)

/-- Decode a finite control location, rejecting negative and out-of-range codes.
A successful lookup need not be the first occurrence of the decoded node. -/
def Program.controlNode (program : Program) (code : Int) : Option (Option Program) :=
  if code < 0 then none else program.controlNodes[code.toNat]?

@[simp] theorem Program.controlCode_none (program : Program) :
    program.controlCode none = 0 := by
  classical
  simp [controlCode, controlNodes]

theorem Program.controlCode_nonneg (program : Program) (node : Option Program) :
    0 ≤ program.controlCode node := by
  classical
  exact Int.natCast_nonneg _

theorem Program.controlCode_le_length (program : Program) (node : Option Program) :
    program.controlCode node ≤ (program.controlNodes.length : Int) := by
  classical
  change (program.controlNodes.idxOf node : Int) ≤ (program.controlNodes.length : Int)
  exact_mod_cast (List.idxOf_le_length (l := program.controlNodes) (a := node))

theorem Program.controlCode_lt_length (program : Program) {node : Option Program}
    (member : node ∈ program.controlNodes) :
    program.controlCode node < (program.controlNodes.length : Int) := by
  classical
  change (program.controlNodes.idxOf node : Int) < (program.controlNodes.length : Int)
  exact_mod_cast (List.idxOf_lt_length_of_mem member)

theorem Program.controlCode_lt_length_iff (program : Program) (node : Option Program) :
    program.controlCode node < (program.controlNodes.length : Int) ↔
      node ∈ program.controlNodes := by
  classical
  change ((program.controlNodes.idxOf node : Int) < (program.controlNodes.length : Int)) ↔ _
  exact_mod_cast (List.idxOf_lt_length_iff (l := program.controlNodes) (a := node))

theorem Program.controlCode_eq_length_of_not_mem (program : Program) {node : Option Program}
    (notMember : node ∉ program.controlNodes) :
    program.controlCode node = (program.controlNodes.length : Int) := by
  classical
  simp only [controlCode, List.idxOf_eq_length notMember]
  rfl

@[simp] theorem Program.controlNode_natCast (program : Program) (index : Nat) :
    program.controlNode (index : Int) = program.controlNodes[index]? := by
  simp [controlNode]

theorem Program.controlNode_of_nonneg (program : Program) {code : Int}
    (nonneg : 0 ≤ code) :
    program.controlNode code = program.controlNodes[code.toNat]? := by
  simp only [controlNode, if_neg (not_lt_of_ge nonneg)]

theorem Program.controlNode_of_neg (program : Program) {code : Int}
    (negative : code < 0) : program.controlNode code = none := by
  simp only [controlNode, if_pos negative]

theorem Program.controlNode_eq_none_iff (program : Program) (code : Int) :
    program.controlNode code = none ↔
      code < 0 ∨ (program.controlNodes.length : Int) ≤ code := by
  by_cases negative : code < 0
  · simp [controlNode, negative]
  · rw [controlNode, if_neg negative, List.getElem?_eq_none_iff]
    constructor <;> intro bound <;> omega

theorem Program.controlNode_of_ge_length (program : Program) {code : Int}
    (bound : (program.controlNodes.length : Int) ≤ code) :
    program.controlNode code = none :=
  (program.controlNode_eq_none_iff code).mpr (Or.inr bound)

theorem Program.controlNode_eq_some_iff (program : Program) (code : Int)
    (node : Option Program) :
    program.controlNode code = some node ↔
      0 ≤ code ∧ ∃ bound : code.toNat < program.controlNodes.length,
        program.controlNodes[code.toNat]'bound = node := by
  by_cases negative : code < 0
  · have notNonneg : ¬0 ≤ code := by omega
    simp [controlNode, negative, notNonneg]
  · have nonneg : 0 ≤ code := by omega
    simp only [controlNode, if_neg negative, nonneg, true_and]
    exact List.getElem?_eq_some_iff

theorem Program.controlNode_mem (program : Program) {code : Int} {node : Option Program}
    (decoded : program.controlNode code = some node) : node ∈ program.controlNodes := by
  obtain ⟨_, _, equal⟩ := (program.controlNode_eq_some_iff code node).mp decoded
  exact List.mem_of_getElem equal

theorem Program.controlNode_bounds (program : Program) {code : Int} {node : Option Program}
    (decoded : program.controlNode code = some node) :
    0 ≤ code ∧ code < (program.controlNodes.length : Int) := by
  obtain ⟨nonneg, bound, _⟩ := (program.controlNode_eq_some_iff code node).mp decoded
  exact ⟨nonneg, by omega⟩

/-- Any valid finite index decodes. This does not assert that its node's
canonical first-occurrence code equals that index. -/
theorem Program.controlNode_getElem (program : Program) (index : Nat)
    (bound : index < program.controlNodes.length) :
    program.controlNode (index : Int) = some (program.controlNodes[index]'bound) := by
  rw [controlNode_natCast]
  exact List.getElem?_eq_getElem bound

@[simp] theorem Program.controlNode_zero (program : Program) :
    program.controlNode 0 = some none := by
  simp [controlNode, controlNodes]

theorem Program.controlNode_controlCode (program : Program) {node : Option Program}
    (member : node ∈ program.controlNodes) :
    program.controlNode (program.controlCode node) = some node := by
  classical
  rw [controlNode_of_nonneg _ (program.controlCode_nonneg node)]
  change program.controlNodes[(program.controlNodes.idxOf node : Int).toNat]? = some node
  simpa only [Int.toNat_natCast] using (List.getElem?_idxOf member)

theorem Program.controlNode_controlCode_iff (program : Program) (node : Option Program) :
    program.controlNode (program.controlCode node) = some node ↔
      node ∈ program.controlNodes :=
  ⟨program.controlNode_mem, program.controlNode_controlCode⟩

theorem Program.controlCode_injective (program : Program) {left right : Option Program}
    (leftMember : left ∈ program.controlNodes) (rightMember : right ∈ program.controlNodes)
    (equal : program.controlCode left = program.controlCode right) : left = right := by
  have decoded := congrArg program.controlNode equal
  rw [program.controlNode_controlCode leftMember,
    program.controlNode_controlCode rightMember] at decoded
  exact Option.some.inj decoded

theorem Program.controlCode_eq_iff (program : Program) {left right : Option Program}
    (leftMember : left ∈ program.controlNodes) (rightMember : right ∈ program.controlNodes) :
    program.controlCode left = program.controlCode right ↔ left = right :=
  ⟨program.controlCode_injective leftMember rightMember, fun equal => congrArg _ equal⟩

theorem Program.controlCode_some_pos (program residual : Program) :
    0 < program.controlCode (some residual) := by
  classical
  have positive : 0 < program.controlNodes.idxOf (some residual) := by
    simp [controlNodes]
  change (0 : Int) < (program.controlNodes.idxOf (some residual) : Int)
  exact_mod_cast positive

theorem Program.controlCode_some_ne_zero (program residual : Program) :
    program.controlCode (some residual) ≠ 0 :=
  ne_of_gt (program.controlCode_some_pos residual)

@[simp] theorem Program.controlCode_eq_zero_iff (program : Program) (node : Option Program) :
    program.controlCode node = 0 ↔ node = none := by
  cases node with
  | none => simp
  | some residual => simp [program.controlCode_some_ne_zero residual]

theorem Program.controlCode_source_pos (program : Program) :
    0 < program.controlCode (some program) :=
  program.controlCode_some_pos program

theorem Program.controlCode_source_wellFormed (program : Program) :
    0 < program.controlCode (some program) ∧
      program.controlCode (some program) < (program.controlNodes.length : Int) ∧
      program.controlNode (program.controlCode (some program)) = some (some program) :=
  ⟨program.controlCode_source_pos,
    program.controlCode_lt_length program.source_mem_controlNodes,
    program.controlNode_controlCode program.source_mem_controlNodes⟩

theorem Program.controlCode_terminal_wellFormed (program : Program) :
    0 ≤ program.controlCode none ∧
      program.controlCode none < (program.controlNodes.length : Int) ∧
      program.controlNode (program.controlCode none) = some none :=
  ⟨program.controlCode_nonneg none,
    program.controlCode_lt_length program.terminal_mem_controlNodes,
    program.controlNode_controlCode program.terminal_mem_controlNodes⟩

/-- Symbolic edges of every residual stay in the original graph, whether or
not their independent local effects are enabled. -/
theorem Program.control_edge_target_mem_controlNodes (program : Program)
    {residual : Program} {target : Option Program} {label : ControlLabel}
    (sourceMember : some residual ∈ program.controlNodes)
    (edge : (target, label) ∈ residual.controlEdges) : target ∈ program.controlNodes := by
  have targetMember := residual.control_edge_target edge
  cases target with
  | none => exact program.terminal_mem_controlNodes
  | some next =>
      apply Program.some_mem_controlNodes.mpr
      exact program.residuals_closed residual (Program.some_mem_controlNodes.mp sourceMember)
        (Program.some_mem_controlNodes.mp targetMember)

theorem Program.controlCode_edge_target_wellFormed (program : Program)
    {residual : Program} {target : Option Program} {label : ControlLabel}
    (sourceMember : some residual ∈ program.controlNodes)
    (edge : (target, label) ∈ residual.controlEdges) :
    0 ≤ program.controlCode target ∧
      program.controlCode target < (program.controlNodes.length : Int) ∧
      program.controlNode (program.controlCode target) = some target := by
  have targetMember := program.control_edge_target_mem_controlNodes sourceMember edge
  exact ⟨program.controlCode_nonneg target, program.controlCode_lt_length targetMember,
    program.controlNode_controlCode targetMember⟩

end Lara.BHL
