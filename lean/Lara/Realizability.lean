/-
M1 — structured-framework isomorphism over the frozen M0 carrier.

The node equivalence permutes every `Nat`, not only in-range positions. This is
required because `StructuredAF.attack` is total and the M0 ranged invariant
constrains its out-of-range values.
-/

import Lara.Invariants

namespace Lara.Realizability

universe u v w

/-- A bijection represented by mutually inverse functions. -/
structure Equiv (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

instance {α : Sort u} {β : Sort v} : CoeFun (Equiv α β) (fun _ => α → β) :=
  ⟨Equiv.toFun⟩

namespace Equiv

/-- The identity equivalence. -/
def refl (α : Sort u) : Equiv α α where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Reverse an equivalence. -/
def symm (e : Equiv α β) : Equiv β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- Compose two equivalences. -/
def trans (eAB : Equiv α β) (eBC : Equiv β γ) : Equiv α γ where
  toFun := fun x => eBC (eAB x)
  invFun := fun z => eAB.invFun (eBC.invFun z)
  left_inv := by
    intro x
    calc
      eAB.invFun (eBC.invFun (eBC (eAB x))) = eAB.invFun (eAB x) :=
        congrArg eAB.invFun (eBC.left_inv (eAB x))
      _ = x := eAB.left_inv x
  right_inv := by
    intro z
    calc
      eBC (eAB (eAB.invFun (eBC.invFun z))) = eBC (eBC.invFun z) :=
        congrArg eBC.toFun (eAB.right_inv (eBC.invFun z))
      _ = z := eBC.right_inv z

end Equiv

/-- An isomorphism of structured argumentation frameworks preserving the total
position space, exact optional node labels, and the total attack relation. -/
structure StructuredAFIso (F G : Invariants.StructuredAF) where
  nodeEquiv : Equiv Nat Nat
  labels : ∀ i, F.nodes[i]? = G.nodes[nodeEquiv i]?
  attacks : ∀ i j,
    F.attack i j = G.attack (nodeEquiv i) (nodeEquiv j)

namespace StructuredAFIso

variable {F G H : Invariants.StructuredAF}

/-- Every structured argumentation framework is isomorphic to itself. -/
def refl (F : Invariants.StructuredAF) : StructuredAFIso F F where
  nodeEquiv := Equiv.refl Nat
  labels := by
    intro i
    rfl
  attacks := by
    intro i j
    rfl

/-- Structured-framework isomorphism is symmetric. -/
def symm (h : StructuredAFIso F G) : StructuredAFIso G F where
  nodeEquiv := h.nodeEquiv.symm
  labels := by
    intro i
    calc
      G.nodes[i]? = G.nodes[h.nodeEquiv (h.nodeEquiv.symm i)]? :=
        congrArg (fun k => G.nodes[k]?) (h.nodeEquiv.right_inv i).symm
      _ = F.nodes[h.nodeEquiv.symm i]? := (h.labels (h.nodeEquiv.symm i)).symm
  attacks := by
    intro i j
    calc
      G.attack i j = G.attack (h.nodeEquiv (h.nodeEquiv.symm i)) j :=
        congrArg (fun k => G.attack k j) (h.nodeEquiv.right_inv i).symm
      _ = G.attack (h.nodeEquiv (h.nodeEquiv.symm i))
          (h.nodeEquiv (h.nodeEquiv.symm j)) :=
        congrArg (fun k => G.attack (h.nodeEquiv (h.nodeEquiv.symm i)) k)
          (h.nodeEquiv.right_inv j).symm
      _ = F.attack (h.nodeEquiv.symm i) (h.nodeEquiv.symm j) :=
        (h.attacks (h.nodeEquiv.symm i) (h.nodeEquiv.symm j)).symm

/-- Structured-framework isomorphism is transitive. -/
def trans (hFG : StructuredAFIso F G) (hGH : StructuredAFIso G H) :
    StructuredAFIso F H where
  nodeEquiv := hFG.nodeEquiv.trans hGH.nodeEquiv
  labels := by
    intro i
    calc
      F.nodes[i]? = G.nodes[hFG.nodeEquiv i]? := hFG.labels i
      _ = H.nodes[hGH.nodeEquiv (hFG.nodeEquiv i)]? := hGH.labels (hFG.nodeEquiv i)
  attacks := by
    intro i j
    calc
      F.attack i j = G.attack (hFG.nodeEquiv i) (hFG.nodeEquiv j) := hFG.attacks i j
      _ = H.attack (hGH.nodeEquiv (hFG.nodeEquiv i))
          (hGH.nodeEquiv (hFG.nodeEquiv j)) :=
        hGH.attacks (hFG.nodeEquiv i) (hFG.nodeEquiv j)

end StructuredAFIso

/-! ### Executable realizability -/

/-- A finite executable ground context covers every evidence leaf used by the
raw support declarations. -/
def GroundCoversUsedLeaves
    (Gamma : Support.LeafId → Option Atom)
    (ground : List Atom)
    (args : List Support.SupportTerm) : Prop :=
  ∀ w ∈ args, ∀ l ∈ Support.leaves w, ∀ p,
    Gamma l = some p → p ∈ ground

namespace HasSupport

/-- A support conclusion is well-sorted when every used leaf and every actual
rule instance is well-sorted. -/
theorem conclusion_wellSorted
    (hs : Support.HasSupport canon Pi Gamma CertOk w C O)
    (hleaves : ∀ l ∈ Support.leaves w, ∀ p,
      Gamma l = some p → Sigma.WellSorted sigma p)
    (hinstances : AllInstancesWellSorted sigma Pi w) :
    Sigma.WellSorted sigma C := by
  cases hs with
  | leaf hΓ =>
      exact hleaves _ (by simp [Support.leaves]) _ hΓ
  | inst hside _ _ =>
      exact (hinstances.1 _ hside.rule).2.1 _ hside.concl

end HasSupport

/-- An executable checked-unit witness whose structured compilation is
isomorphic to the target framework. -/
structure Realization
    (canon : String → String)
    (sigma : Sigma.Sigma)
    (policy : Policy.Policy)
    (reg : Support.BackendRegistry canon)
    (F : Invariants.StructuredAF) where
  Gamma : Support.LeafId → Option Atom
  ground : List Atom
  raw : Lara.Unit
  accepted : Lara.Unit.CheckedUnit canon Gamma (Support.certOkOf reg)
  checked : Check.Unit.checkUnit Gamma reg ground raw = .ok accepted
  sigma_eq : accepted.sigma = sigma
  policy_eq : accepted.policy = policy
  ground_covers : GroundCoversUsedLeaves Gamma ground raw.args
  compiled_iso : StructuredAFIso (Invariants.compileUnit accepted) F

namespace Realization

/-- Every retained checked node in a realization has a well-sorted
conclusion under the realization's fixed signature. -/
theorem node_conclusion_wellSorted
    (R : Realization canon sigma policy reg F)
    {node : Compile.CheckedNode canon R.accepted.policy.ruleLookup
      R.Gamma (Support.certOkOf reg)}
    (hnode : node ∈ R.accepted.nodes) :
    Sigma.WellSorted sigma node.conclusion := by
  obtain ⟨_, hground, hinstances⟩ :=
    Check.Unit.checkUnit_wellSorted R.checked
  obtain ⟨_, _, _, _, _, _, _, _, hargs, _, _, _⟩ :=
    Check.Unit.checkUnit_sound R.checked
  have hterm : node.term ∈ R.accepted.program.args := by
    have hmapped : node.term ∈ R.accepted.nodes.map (·.term) :=
      List.mem_map.mpr ⟨node, hnode, rfl⟩
    rwa [R.accepted.nodes_terms] at hmapped
  have hcoverage :
      GroundCoversUsedLeaves R.Gamma R.ground
        R.accepted.program.args := by
    intro w hw l hl p hlookup
    apply R.ground_covers w ?_ l hl p hlookup
    rw [← hargs]
    exact hw
  have hleaves : ∀ l ∈ Support.leaves node.term, ∀ p,
      R.Gamma l = some p → Sigma.WellSorted sigma p := by
    intro l hl p hlookup
    have hp := hground p (hcoverage node.term hterm l hl p hlookup)
    simpa only [R.sigma_eq] using hp
  have hinstancesFixed :
      AllInstancesWellSorted sigma policy.ruleLookup node.term := by
    simpa only [R.sigma_eq, R.policy_eq] using hinstances node.term hterm
  have hvalid :
      Support.HasSupport canon policy.ruleLookup R.Gamma
        (Support.certOkOf reg) node.term node.conclusion [] := by
    simpa only [R.policy_eq] using node.valid
  exact HasSupport.conclusion_wellSorted hvalid hleaves hinstancesFixed

end Realization

/-- A fixed signature, policy, backend registry, and target framework admit an
exhibited raw unit that succeeds through the executable checker. -/
def Realizable
    (canon : String → String)
    (sigma : Sigma.Sigma)
    (policy : Policy.Policy)
    (reg : Support.BackendRegistry canon)
    (F : Invariants.StructuredAF) : Prop :=
  Nonempty (Realization canon sigma policy reg F)

/-! ### Invariant transport -/

/-- The frozen compiler invariant is preserved by all-`Nat` structured
framework isomorphism. -/
theorem compilerInvariant_iso
    (hiso : StructuredAFIso F G)
    (hF : Invariants.CompilerInvariant canon dp F) :
    Invariants.CompilerInvariant canon dp G := by
  have hinv : ∀ k, hiso.nodeEquiv (hiso.nodeEquiv.symm k) = k := by
    intro k
    simpa [Equiv.symm] using hiso.nodeEquiv.right_inv k
  constructor
  · intro i j hij
    have hback :
        F.attack (hiso.nodeEquiv.symm i) (hiso.nodeEquiv.symm j) = true := by
      rw [hiso.attacks, hinv i, hinv j]
      exact hij
    obtain ⟨hi, hj⟩ := hF.ranged _ _ hback
    obtain ⟨ci, hci⟩ := Support.getElem?_some_of_lt F.nodes
      (hiso.nodeEquiv.symm i) hi
    obtain ⟨cj, hcj⟩ := Support.getElem?_some_of_lt F.nodes
      (hiso.nodeEquiv.symm j) hj
    constructor
    · apply Support.lt_of_getElem?_some (a := ci)
      calc
        G.nodes[i]? =
            G.nodes[hiso.nodeEquiv (hiso.nodeEquiv.symm i)]? :=
          congrArg (fun k => G.nodes[k]?) (hinv i).symm
        _ = F.nodes[hiso.nodeEquiv.symm i]? :=
          (hiso.labels (hiso.nodeEquiv.symm i)).symm
        _ = some ci := hci
    · apply Support.lt_of_getElem?_some (a := cj)
      calc
        G.nodes[j]? =
            G.nodes[hiso.nodeEquiv (hiso.nodeEquiv.symm j)]? :=
          congrArg (fun k => G.nodes[k]?) (hinv j).symm
        _ = F.nodes[hiso.nodeEquiv.symm j]? :=
          (hiso.labels (hiso.nodeEquiv.symm j)).symm
        _ = some cj := hcj
  · intro i j ci cj hi hj hcontrary
    have hiBack : F.nodes[hiso.nodeEquiv.symm i]? = some ci := by
      calc
        F.nodes[hiso.nodeEquiv.symm i]? =
            G.nodes[hiso.nodeEquiv (hiso.nodeEquiv.symm i)]? :=
          hiso.labels (hiso.nodeEquiv.symm i)
        _ = G.nodes[i]? := congrArg (fun k => G.nodes[k]?) (hinv i)
        _ = some ci := hi
    have hjBack : F.nodes[hiso.nodeEquiv.symm j]? = some cj := by
      calc
        F.nodes[hiso.nodeEquiv.symm j]? =
            G.nodes[hiso.nodeEquiv (hiso.nodeEquiv.symm j)]? :=
          hiso.labels (hiso.nodeEquiv.symm j)
        _ = G.nodes[j]? := congrArg (fun k => G.nodes[k]?) (hinv j)
        _ = some cj := hj
    have hback := hF.conflictComplete
      (hiso.nodeEquiv.symm i) (hiso.nodeEquiv.symm j)
      ci cj hiBack hjBack hcontrary
    calc
      G.attack i j =
          G.attack (hiso.nodeEquiv (hiso.nodeEquiv.symm i)) j :=
        congrArg (fun k => G.attack k j) (hinv i).symm
      _ = G.attack (hiso.nodeEquiv (hiso.nodeEquiv.symm i))
          (hiso.nodeEquiv (hiso.nodeEquiv.symm j)) :=
        congrArg
          (fun k => G.attack (hiso.nodeEquiv (hiso.nodeEquiv.symm i)) k)
          (hinv j).symm
      _ = F.attack (hiso.nodeEquiv.symm i) (hiso.nodeEquiv.symm j) :=
        (hiso.attacks (hiso.nodeEquiv.symm i)
          (hiso.nodeEquiv.symm j)).symm
      _ = true := hback

example
    (hiso : StructuredAFIso F G)
    (hF : Invariants.CompilerInvariant canon dp F) :
    ∀ i j, G.attack i j = true → i < G.size ∧ j < G.size :=
  (compilerInvariant_iso hiso hF).ranged

example
    (hiso : StructuredAFIso F G)
    (hF : Invariants.CompilerInvariant canon dp F) :
    ∀ (i j : Nat) (ci cj : Atom),
      G.nodes[i]? = some ci → G.nodes[j]? = some cj →
      Attack.ContraryMatch canon dp ci cj → G.attack i j = true :=
  (compilerInvariant_iso hiso hF).conflictComplete

/-! ### Necessity -/

/-- Every executable realization satisfies the frozen M0 compiler invariant,
up to the exhibited structured-framework isomorphism. -/
theorem realizable_invariant
    (h : Realizable canon sigma policy reg F) :
    Invariants.CompilerInvariant canon policy.defeat F := by
  rcases h with ⟨realization⟩
  apply compilerInvariant_iso realization.compiled_iso
  simpa only [realization.policy_eq] using
    Invariants.compileUnit_invariant realization.accepted

end Lara.Realizability
