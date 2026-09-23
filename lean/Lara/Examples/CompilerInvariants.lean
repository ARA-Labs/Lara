/-
M0 rejecting counterexamples.

For each invariant the M0 carrier can express, the smallest structured
framework that violates it, together with the corollary that no accepted unit
compiles to that framework. The corollaries all run through
`Invariants.compileUnit_invariant`: a violated field is exactly a proof of
non-realizability, which is why the invariant record has to be stated before
M1 rather than discovered during it.

Invariants that live in the *source* judgment are rejected by programs, not by
carriers. Subargument closure gets its witness here because the running fixture
already supplies one; positional attack coherence is rejected by the inversion
theorems of `Lara.Attack`, and strict-chain well-formedness waits on B0.
`docs/theory-m0-compilation-invariants.md` names each one.
-/

import Lara.Invariants
import Lara.Examples.GroundedConsistency

namespace Lara.Examples.CompilerInvariants

open Lara.Support Lara.Invariants

/-! ### Endpoint-safe pruning -/

/-- The smallest violation of `ranged`: no declared nodes, yet an edge. A
compiled framework cannot do this, because `Compile.Edge` requires both
endpoints to be declared arguments. -/
def unrangedEx : StructuredAF :=
  { nodes := [], attack := fun _ _ => true }

theorem unrangedEx_not_invariant (canon : String → String)
    (dp : Attack.DefeatPolicy) :
    ¬ CompilerInvariant canon dp unrangedEx := by
  intro h
  have hlt := (h.ranged 0 0 rfl).1
  simp [unrangedEx, StructuredAF.size] at hlt

/-- No accepted unit compiles to it. -/
theorem unrangedEx_not_realizable {canon : String → String}
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (unit : Unit.CheckedUnit canon Gamma CertOk) :
    compileUnit unit ≠ unrangedEx := by
  intro heq
  exact unrangedEx_not_invariant canon unit.policy.defeat
    (heq ▸ compileUnit_invariant unit)

/-! ### Conflict completeness -/

/-- The smallest violation of `conflictComplete`: two nodes whose conclusions
are declared contrary, with no edge between them. This is the invariant that
constrains the *image* of compilation rather than its well-formedness — an
accepted unit's edge relation is forced by its conclusions and the fixed
contrary policy, so a framework may not label its nodes freely and then choose
its edges. -/
def unforcedConflictEx (p q : Atom) : StructuredAF :=
  { nodes := [p, q], attack := fun _ _ => false }

theorem unforcedConflictEx_not_invariant {canon : String → String}
    {dp : Attack.DefeatPolicy} {p q : Atom}
    (hcontrary : Attack.ContraryMatch canon dp p q) :
    ¬ CompilerInvariant canon dp (unforcedConflictEx p q) := by
  intro h
  have hedge := h.conflictComplete 0 1 p q rfl rfl hcontrary
  simp [unforcedConflictEx] at hedge

/-- No accepted unit whose policy declares the two conclusions contrary
compiles to it. -/
theorem unforcedConflictEx_not_realizable {canon : String → String}
    {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (unit : Unit.CheckedUnit canon Gamma CertOk) {p q : Atom}
    (hcontrary : Attack.ContraryMatch canon unit.policy.defeat p q) :
    compileUnit unit ≠ unforcedConflictEx p q := by
  intro heq
  exact unforcedConflictEx_not_invariant hcontrary
    (heq ▸ compileUnit_invariant unit)

/-! ### Non-vacuity, and the self-attack diagonal

The two theorems above are conditional on a contrary match, so they are worth
nothing without one. `GroundedConsistency.selfConflictPolicy` supplies it: it
declares `p` contrary to *itself*, which is also the spec's self-attack
condition. The rejected framework is therefore both the conflict-completeness
counterexample and the self-attack one. -/

theorem selfContrary :
    Attack.ContraryMatch id GroundedConsistency.selfConflictPolicy.defeat
      pA pA :=
  ⟨(apA, apA), by simp [GroundedConsistency.selfConflictPolicy], [], pA, pA,
    by decide, by decide, equiv_refl id pA, equiv_refl id pA⟩

/-- A concrete framework outside the image of compilation: two `p`-concluding
nodes under a policy that makes `p` self-contrary, with no edges at all. -/
theorem unforcedSelfConflict_not_invariant :
    ¬ CompilerInvariant id GroundedConsistency.selfConflictPolicy.defeat
        (unforcedConflictEx pA pA) :=
  unforcedConflictEx_not_invariant selfContrary

/-! ### Non-vacuity off the diagonal

`selfContrary` witnesses the case `p = q`, which is row 3 of the invariant
table — the self-attack diagonal — and would remain available even if
`ContraryMatch` were narrowed to self-contrary pairs only. That would leave
`conflictComplete` a corollary of the diagonal rather than a separate field,
with both conditional theorems above silently vacuous and the axiom audit still
green. The witness below rules that out: `dpShared` declares `p(?x)` contrary to
`q(?x)`, so `pTa` and `qTa` are *distinct* conclusions forced to carry an edge.
This is the case §3.1 describes and the one that makes M1's only-if direction
bite. -/

theorem sharedContrary :
    Attack.ContraryMatch id dpShared pTa qTa :=
  (Attack.contraryMatchB_iff _ _ _ _).mp contrary_shared_substitution

theorem unforcedDistinctConflict_not_invariant :
    ¬ CompilerInvariant id dpShared (unforcedConflictEx pTa qTa) :=
  unforcedConflictEx_not_invariant sharedContrary

/-! ### Subargument closure — a source-level rejection

Closure is an invariant of the source judgment, not of the carrier: it
quantifies over occurrence containment, which erasure discards. Its rejecting
witness is therefore a program, not a framework. In the running fixture the
declared attack `kAtk` has attacked occurrence `l1`, so the wrapper containing
it receives a closure edge (`Examples.checked_edge_fixture`), while node `0`
— in range, and the attack's own source — receives none, because `l2` does not
contain `l1`. Closure adds edges onto containing arguments only; it does not
make an attack universal. -/

theorem closure_rejects_noncontaining_target :
    Compile.edgeB PEx 0 0 = false := by
  decide

/-! ### The positive anchor

The accepted self-conflict unit of `GroundedConsistency` compiles into the
carrier and carries the forced self-edge, so the invariant is not satisfied
only by frameworks nothing compiles to. -/

theorem selfEdgeUnit_nodes :
    (compileUnit GroundedConsistency.acceptedSelfEdgeUnit).nodes = [pA] := by
  decide

theorem selfEdgeUnit_selfEdge :
    (compileUnit GroundedConsistency.acceptedSelfEdgeUnit).attack 0 0 = true := by
  decide

end Lara.Examples.CompilerInvariants
