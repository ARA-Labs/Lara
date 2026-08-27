/-
M0 — the frozen compilation carrier and invariant record (issue #183).

M0's job is not to prove a new metatheorem. It is to answer, once and
irrevocably, the question every downstream item quotes: *what is the formal
object that compilation produces?* M1 characterizes the image of that object,
M2 measures queries on it, M3 moves it, and the possible-world wrapper indexes
a family of them. If the carrier is chosen loosely, each of those items either
becomes unstatable or becomes true by definition.

This module fixes three things:

* `StructuredAF` — the carrier. Nodes are declaration-order positions carrying
  the conclusion their checked support term proves; edges are the compiled
  closure relation over those positions.
* `eraseAF` — the projection to a naked Dung framework (`Grounded.AF`), frozen
  here so M1's erased-AF corollary quantifies over a fixed function.
* `CompilerInvariant` — the conjunction of the invariants that are *visible in
  the carrier* and hold of every compiled accepted unit.

### Why conclusions, and only conclusions

A carrier that keeps whole support terms makes M1 vacuous: "realizable" would
mean "already built from checked terms". A carrier that keeps nothing but the
edge relation makes M1 uninformative in the other direction, because the
interesting constraint on the image — that edges are *forced* by the fixed
contrary policy — is invisible without node labels. Conclusions are the
smallest labelling that separates the two, and `status_compileUnit` below shows
they are also enough: every claim status the system reports factors through
this carrier.

### Why there is no `attackable` node label

The obvious reading of `AttackComplete` needs a per-node "can be attacked at
its root" flag, since `Compile.ConflictAttackable` is a property of a *term*
and terms are gone from the carrier. That label turns out to be redundant:
`Consistency.wellFormed_contrary_target_attackable` proves that in a
well-formed accepted policy a contrary target can never be a strict-rule root,
so conflict attackability is implied by the contrary match itself. The label
was a candidate carrier field and is deliberately absent.

### What is *not* in the invariant record

Subargument closure, positional attack coherence, and strict-chain
well-formedness are invariants of the source judgment, not of the carrier: each
quantifies over term structure that erasure discards. They keep their existing
Lean homes (`Compile.Covered`, `Compile.AttackOcc`, `Support.cert_steps_accounted`)
and are classified as source-level in `docs/theory-m0-compilation-invariants.md`
rather than restated here as carrier predicates they cannot be.
-/

import Lara.Consistency

namespace Lara.Invariants

open Lara.Support Lara.Grounded

/-! ### The carrier -/

/-- **The M1 carrier (M0-frozen).** A finite structured argumentation
framework: node `i` is the `i`-th declared complete argument, labelled with the
conclusion its checked support term proves, and `attack` is the compiled
subargument-closure edge relation over those positions.

Positions, not terms, are the node identity — matching `Compile.toAF`, where
`Grounded.Arg = Nat` indexes `CheckedProgram.args`. -/
structure StructuredAF where
  /-- node conclusions in declaration order; the node count is `nodes.length` -/
  nodes : List Atom
  /-- the compiled closure-edge relation over node positions -/
  attack : Nat → Nat → Bool

namespace StructuredAF

/-- The node count. -/
def size (F : StructuredAF) : Nat := F.nodes.length

end StructuredAF

/-- **The frozen erasure.** Forget the conclusion labelling; keep the positions
and the edge relation. This is the projection M1's erased-AF corollary
quantifies over, and `erase_compileUnit` ties it to the existing pipeline:
erasing a compiled unit gives back exactly `Compile.checkedAF`. -/
def eraseAF (F : StructuredAF) : Grounded.AF :=
  { args := List.range F.size, attack := F.attack }

/-! ### The claim projection over the carrier

The observation side of the carrier: which nodes support a claim, and what
status that claim receives. Both are functions of `StructuredAF` alone — that
is the content of `support_compileUnit` and `status_compileUnit` below. -/

/-- Declaration-order positions whose conclusion is canonically equivalent to
`p`. The carrier-level twin of `Consistency.claimSupportFor`. -/
def support (canon : String → String) (F : StructuredAF) (p : Atom) : List Nat :=
  F.nodes.zipIdx.filterMap fun entry =>
    if equiv canon entry.1 p then some entry.2 else none

/-- The complete-support claim for `p`, read off the carrier. Holes are
definitionally empty, matching `Consistency.completeClaimFor`. -/
def claim (canon : String → String) (F : StructuredAF) (p : Atom) : Grounded.Claim :=
  { support := support canon F p, holes := [] }

/-- The four-state status of `p`, computed entirely inside the carrier. -/
def status (canon : String → String) (F : StructuredAF) (p : Atom) : Grounded.Status :=
  Grounded.statusC (eraseAF F) (claim canon F p)

/-! ### The invariant record -/

/-- **The M0 invariant record.** The conjunction of the compiler invariants
that are visible in the carrier, at a fixed canonicalizer and defeat policy.

`ranged` is endpoint-safe pruning: an edge never names a position outside the
declared arguments, because `Compile.Edge` requires both endpoints declared.

`conflictComplete` is the forced-edge invariant induced by
`Compile.AttackComplete`: the edge relation of a compiled framework is not
freely chosen — every declared-contrary pair of node conclusions *must* carry
an edge. This is the invariant that makes M1's only-if direction bite, since it
rules out frameworks whose edges disagree with their labels. -/
structure CompilerInvariant (canon : String → String)
    (dp : Attack.DefeatPolicy) (F : StructuredAF) : Prop where
  /-- endpoint-safe pruning: no edge escapes the declared node range -/
  ranged : ∀ i j, F.attack i j = true → i < F.size ∧ j < F.size
  /-- conflict completeness: contrary conclusions force an edge -/
  conflictComplete : ∀ (i j : Nat) (ci cj : Atom),
    F.nodes[i]? = some ci → F.nodes[j]? = some cj →
    Attack.ContraryMatch canon dp ci cj → F.attack i j = true

variable {canon : String → String} {Gamma : LeafId → Option Atom}
  {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}

/-! ### Compiling an accepted unit into the carrier -/

/-- **Structured compilation.** An accepted unit's retained checker cache
already holds exactly the carrier data: `nodes` supplies the conclusion
labelling, and the checker-built decider `Compile.edgeB` supplies the edge
relation. No support is re-inferred. -/
def compileUnit (unit : Unit.CheckedUnit canon Gamma CertOk) : StructuredAF :=
  { nodes := unit.nodes.map (·.conclusion)
  , attack := Compile.edgeB unit.program }

/-- The carrier has one node per declared argument. -/
theorem compileUnit_size (unit : Unit.CheckedUnit canon Gamma CertOk) :
    (compileUnit unit).size = unit.program.args.length := by
  have h := congrArg List.length unit.nodes_terms
  simpa [compileUnit, StructuredAF.size] using h

/-- **Erasure coherence.** Erasing the structured compilation of an accepted
unit gives back exactly the AF the existing pipeline compiles to. The carrier
is a refinement of `Compile.checkedAF`, not a parallel construction. -/
theorem erase_compileUnit (unit : Unit.CheckedUnit canon Gamma CertOk) :
    eraseAF (compileUnit unit) = Compile.checkedAF unit.program := by
  have hlen := compileUnit_size unit
  unfold eraseAF Compile.checkedAF Compile.toAF
  rw [hlen]
  rfl

/-! ### Necessity: every compiled accepted unit satisfies the record -/

/-- Endpoint-safe pruning holds of every compiled accepted unit. -/
theorem compileUnit_ranged (unit : Unit.CheckedUnit canon Gamma CertOk) :
    ∀ i j, (compileUnit unit).attack i j = true →
      i < (compileUnit unit).size ∧ j < (compileUnit unit).size := by
  intro i j h
  have hr := (Compile.edgeB_faithful unit.program).ranged i j h
  rw [compileUnit_size]
  exact hr

/-- **Conflict completeness holds of every compiled accepted unit.** Recover
the two retained checked nodes behind the conclusion labels, lift the contrary
match to their conclusions, obtain attackability of the target from policy
well-formedness, and discharge the edge through whole-program attack
completeness and the checker's own edge decider. -/
theorem compileUnit_conflictComplete
    (unit : Unit.CheckedUnit canon Gamma CertOk) :
    ∀ (i j : Nat) (ci cj : Atom),
      (compileUnit unit).nodes[i]? = some ci →
      (compileUnit unit).nodes[j]? = some cj →
      Attack.ContraryMatch canon unit.policy.defeat ci cj →
      (compileUnit unit).attack i j = true := by
  intro i j ci cj hi hj hcontrary
  simp only [compileUnit, List.getElem?_map, Option.map_eq_some_iff] at hi hj
  obtain ⟨source, hsource, hsc⟩ := hi
  obtain ⟨target, htarget, htc⟩ := hj
  have hsourceAt : unit.program.args[i]? = some source.term := by
    rw [← unit.nodes_terms, List.getElem?_map, hsource]; rfl
  have htargetAt : unit.program.args[j]? = some target.term := by
    rw [← unit.nodes_terms, List.getElem?_map, htarget]; rfl
  have hcontrary' :
      Attack.ContraryMatch canon unit.policy.defeat
        source.conclusion target.conclusion := by
    rw [hsc, htc]; exact hcontrary
  have hattackable :
      Compile.ConflictAttackable unit.policy.ruleLookup target.term :=
    Consistency.wellFormed_contrary_target_attackable
      (_source := source.term) unit target.valid hcontrary'
  have hedge : Compile.Edge unit.program source.term target.term :=
    Compile.complete_conflict_edge unit.program unit.attack_complete
      (List.mem_of_getElem? hsourceAt) (List.mem_of_getElem? htargetAt)
      source.valid target.valid hcontrary' hattackable
  have hedgeB := (Compile.edgeB_iff hsourceAt htargetAt).mpr hedge
  simpa [compileUnit] using hedgeB

/-- **M0 necessity.** Every accepted unit compiles to a carrier satisfying the
frozen invariant record. This is the direction M1 inherits as its only-if half,
and the direction every non-realizability corollary below runs through. -/
theorem compileUnit_invariant (unit : Unit.CheckedUnit canon Gamma CertOk) :
    CompilerInvariant canon unit.policy.defeat (compileUnit unit) :=
  { ranged := compileUnit_ranged unit
  , conflictComplete := compileUnit_conflictComplete unit }

/-- **Self-conflict is the diagonal, not an independent invariant.** A node
whose conclusion is contrary to itself carries a self-edge — the `i = j` case
of conflict completeness, recorded separately because the spec lists
self-attack as its own condition. -/
theorem compileUnit_selfConflict (unit : Unit.CheckedUnit canon Gamma CertOk)
    {i : Nat} {ci : Atom} (hi : (compileUnit unit).nodes[i]? = some ci)
    (hcontrary : Attack.ContraryMatch canon unit.policy.defeat ci ci) :
    (compileUnit unit).attack i i = true :=
  compileUnit_conflictComplete unit i i ci ci hi hi hcontrary

/-! ### Observational adequacy of the carrier

The carrier is not merely *a* structured object compilation happens to
produce; it retains everything the system observes. Claim support and claim
status both factor through it, so an M1 characterization of the carrier is a
characterization of everything downstream reads. -/

private theorem support_map_aux (canon : String → String) (p : Atom)
    {Pi : RuleId → Option Rule}
    (nodes : List (Compile.CheckedNode canon Pi Gamma CertOk)) (n : Nat) :
    ((nodes.map (·.conclusion)).zipIdx n).filterMap
        (fun entry => if equiv canon entry.1 p then some entry.2 else none)
      = (nodes.zipIdx n).filterMap
        (fun entry => if equiv canon entry.1.conclusion p then some entry.2
          else none) := by
  induction nodes generalizing n with
  | nil => rfl
  | cons node rest ih =>
    by_cases hequiv : equiv canon node.conclusion p <;>
      simp [List.zipIdx_cons, hequiv, ih]

/-- **Claim support factors through the carrier.** The carrier-level support
projection agrees with the accepted unit's computed complete support. -/
theorem support_compileUnit (unit : Unit.CheckedUnit canon Gamma CertOk)
    (p : Atom) :
    support canon (compileUnit unit) p = Consistency.claimSupportFor unit p := by
  simpa [support, compileUnit, Consistency.claimSupportFor] using
    support_map_aux canon p unit.nodes 0

/-- **Claim status factors through the carrier.** The status computed entirely
inside the carrier equals the status the existing pipeline reports over
`Compile.checkedAF`. Nothing an accepted unit says about a claim survives
outside `StructuredAF`, which is what licenses M1 to quantify over the carrier
instead of over programs. -/
theorem status_compileUnit (unit : Unit.CheckedUnit canon Gamma CertOk)
    (p : Atom) :
    status canon (compileUnit unit) p
      = Grounded.statusC (Compile.checkedAF unit.program)
          (Consistency.completeClaimFor unit p) := by
  rw [status, claim, erase_compileUnit, support_compileUnit,
    Consistency.completeClaimFor]

end Lara.Invariants
