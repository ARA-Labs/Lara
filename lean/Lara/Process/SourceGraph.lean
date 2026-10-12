import Lara.PW.AFBisim
import Mathlib.Data.List.Basic

namespace Lara.Process.Source

open Grounded

/-- Cache compiled edges once before constructing the stable-coordinate graph. -/
def mappedEdges (framework : AF) (identity : Arg → Arg) : List (Arg × Arg) :=
  framework.args.flatMap fun source =>
    (framework.args.filter (framework.attack source)).map fun target =>
      (identity source, identity target)

def liftGraph (framework : AF) (identity : Arg → Arg) : AF :=
  let edges := mappedEdges framework identity
  ⟨framework.args.map identity, fun source target => decide ((source, target) ∈ edges)⟩

theorem mem_mappedEdges (framework : AF) (identity : Arg → Arg) (source target : Arg) :
    (source, target) ∈ mappedEdges framework identity ↔
      ∃ originalSource ∈ framework.args, ∃ originalTarget ∈ framework.args,
        framework.attack originalSource originalTarget = true ∧
          identity originalSource = source ∧ identity originalTarget = target := by
  simp [mappedEdges, List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq,
    and_assoc, and_left_comm, and_comm]

theorem liftGraph_iso (framework : AF) (identity : Arg → Arg)
    (injective : ∀ a b, a ∈ framework.args → b ∈ framework.args →
      identity a = identity b → a = b) : PW.AFIso framework (liftGraph framework identity) identity := by
  constructor
  · intro a member
    exact List.mem_map_of_mem member
  · exact injective
  · intro a member
    exact List.mem_map.mp member
  · intro a b ha hb
    constructor
    · intro edge
      apply decide_eq_true
      exact (mem_mappedEdges framework identity _ _).mpr ⟨a, ha, b, hb, edge, rfl, rfl⟩
    · intro edge
      obtain ⟨x, hx, y, hy, attack, xa, yb⟩ :=
        (mem_mappedEdges framework identity _ _).mp (of_decide_eq_true edge)
      have xa := injective x a hx ha xa
      have yb := injective y b hy hb yb
      simpa [xa, yb] using attack

theorem liftGraph_label (framework : AF) (identity : Arg → Arg)
    (injective : ∀ a b, a ∈ framework.args → b ∈ framework.args →
      identity a = identity b → a = b) {argument : Arg} (member : argument ∈ framework.args) :
    labelC (liftGraph framework identity) (identity argument) = labelC framework argument :=
  (PW.labelC_of_iso (liftGraph_iso framework identity injective) member).symm

theorem liftGraph_status (framework : AF) (identity : Arg → Arg)
    (injective : ∀ a b, a ∈ framework.args → b ∈ framework.args →
      identity a = identity b → a = b) (claim : Claim)
    (supported : ∀ a ∈ claim.support, a ∈ framework.args) :
    statusC (liftGraph framework identity) { claim with support := claim.support.map identity } =
      statusC framework claim := by
  symm
  apply PW.statusC_of_iso (liftGraph_iso framework identity injective)
  apply PW.supportCorr_of_image supported
  intro a
  exact List.mem_map

end Lara.Process.Source
