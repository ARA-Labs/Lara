# Theory M1: the compilation-image boundary

_Status: proved for the POPL 2028 theory spine on 2026-08-26 (issue #184,
tracker #180). This document records the fixed-context theorem boundary after
M1 tested and refuted the proposed sufficiency direction._

The intended readers are the paper author and future M2 implementers. They
should cite the declarations below rather than restating the original M1
conjecture.

## 1. Fixed Context and Equality Notion

M1 fixes a canonicalizer `canon`, signature `sigma`, policy `policy`, and
backend registry `reg`. The target is an `Invariants.StructuredAF`, the frozen
M0 carrier of conclusion labels and a total Boolean attack relation.

`Realizability.StructuredAFIso F G` is equality up to node renaming. Its
`nodeEquiv : Realizability.Equiv Nat Nat` renames the total position space, while `labels`
preserves exact optional node labels and `attacks` preserves the total attack
relation. `Realizability.StructuredAFIso.refl`,
`Realizability.StructuredAFIso.symm`, and
`Realizability.StructuredAFIso.trans` prove that this notion is an equivalence
relation.

## 2. Executable Realization

`Realizability.Realization canon sigma policy reg F` exhibits all data needed
to place `F` in the executable compilation image:

- a leaf context `Gamma`, finite `ground` input, and raw `Lara.Unit`;
- an accepted `Unit.CheckedUnit` and an equation showing that
  `Check.Unit.checkUnit Gamma reg ground raw` returns that accepted unit;
- equations fixing the accepted signature and policy to `sigma` and `policy`;
- `GroundCoversUsedLeaves Gamma ground raw.args`; and
- a `StructuredAFIso` from `Invariants.compileUnit accepted` to `F`.

`Realizability.Realizable canon sigma policy reg F` is the proposition that
such a `Realization` exists. This definition requires an executable witness; it
does not identify realizability with a carrier-only predicate.

## 3. Proved Boundary

### Necessity

`Realizability.compilerInvariant_iso` transports the frozen
`Invariants.CompilerInvariant` across `StructuredAFIso`:

```lean
theorem compilerInvariant_iso
    (hiso : StructuredAFIso F G)
    (hF : Invariants.CompilerInvariant canon dp F) :
    Invariants.CompilerInvariant canon dp G
```

`Realizability.realizable_invariant` is the only-if direction:

```lean
theorem realizable_invariant
    (h : Realizable canon sigma policy reg F) :
    Invariants.CompilerInvariant canon policy.defeat F
```

The proof applies `Invariants.compileUnit_invariant` to the exhibited accepted
unit and transports the result through `Realization.compiled_iso`.

### Conclusion Sortedness Under Coverage

`Realizability.Realization.node_conclusion_wellSorted` closes M0's recorded
sortedness obligation at the realization boundary. Its exact hypotheses and
conclusion are:

```lean
theorem node_conclusion_wellSorted
    (R : Realization canon sigma policy reg F)
    {node : Compile.CheckedNode canon R.accepted.policy.ruleLookup
      R.Gamma (Support.certOkOf reg)}
    (hnode : node ∈ R.accepted.nodes) :
    Sigma.WellSorted sigma node.conclusion
```

The theorem uses the successful checker equation and
`R.ground_covers`. Its conclusion therefore applies under used-leaf ground
coverage; it is not an unconditional theorem about every standalone
`Unit.CheckedUnit` value.

### Nonempty Integration Anchor

`Examples.Realizability.nonempty_swapped_realizable` assembles the accepted
two-argument `Examples.rawUnitEx`, its nonempty ground input, explicit used-leaf
coverage, and a two-node swap that fixes every position from two onward.
`Examples.Realizability.nonempty_swapped_node_wellSorted` applies the
realization sortedness theorem to an actual retained node. `lean/AxCheck.lean`
audits both declarations.

### Accepted Empty-Policy Anchor

`Examples.Realizability.emptyUnitCheck_ok` proves that the concrete empty raw
unit under `Examples.PolicyAcceptance.emptyPolicy` succeeds through
`Check.Unit.checkUnit`. The empty defeat context is executable and accepted, so
the negative result below does not exploit an inconsistent checker context.

### Failure of Sufficiency

For any atom `p`, `Examples.Realizability.oneSelfEdge p` has one node and a
self-edge. The following declarations establish the counterexample:

- `Examples.Realizability.oneSelfEdge_invariant` proves that `oneSelfEdge p`
  satisfies `Invariants.CompilerInvariant canon emptyDefeat`.
- `Examples.Realizability.oneSelfEdge_not_realizable` takes any `sigma`,
  `policy`, and `reg` satisfying `policy.defeat = emptyDefeat` and proves that
  `oneSelfEdge p` is not `Realizable canon sigma policy reg`.

Under `emptyDefeat`, every compiled edge is false. The M0 record still accepts
the self-edge because conflict completeness is vacuous and the edge endpoints
are in range. Optional support and typed attack provenance are erased from the
carrier, so the invariant record cannot establish that an arbitrary carrier
edge has a compilable source witness.

Necessity holds for every fixed context. The empty-defeat theorems refute a
converse quantified over all fixed contexts; they do not establish
non-sufficiency for every policy. A `realize` function under the original
universal quantifiers would have to realize the invariant-satisfying self-edge
in the fixed empty-defeat context.

## 4. Carrier Revision Decision

After proving the empty-defeat counterexample, M1 evaluated candidate extensions
to the M0 carrier. Checked support terms, declared attack data, source
blueprints, and search certificates would store the source witness that
`Realizable` already requires, so they would make the converse circular.
Endpoint-label edge licensing is not necessary because undercut, undermine, and
closure edges depend on erased target occurrences or containment. Empty-policy
edge soundness and canonical leaf-only restrictions describe strict subclasses,
not the fixed-context compilation image.

None of these evaluated candidates supplied both an independent
compiler-necessity proof and a constructive checker-success proof. M1 therefore
retains the M0 carrier. This is a decision about the evaluated candidates, not
an exhaustive impossibility theorem for every future carrier extension.

## 5. Paper Claims

The paper may claim that executable realizability implies the frozen compiler
invariant in every fixed context. It may also claim that a converse universal
over fixed contexts is false, citing the accepted empty-policy anchor and the
one-self-edge counterexample.

The paper must not state the original unconditional iff, cite a constructive
`realize` theorem, or imply that every invariant-satisfying framework has a
checked source program. The mechanization contains no such declaration.

M1 omits an erased-AF result. Once conclusion labels and source terms are
removed, the surviving endpoint-range condition is generic finite-framework
well-formedness rather than a Lara-specific image characterization.

## 6. Proposed Follow-up Work

A generated-policy theorem or a realization-kit theorem could use different
quantifiers and retain source witnesses that the frozen carrier erases. That is
proposed follow-up work, not an M1 result. This document does not assign it a
tracker or claim that the present development proves it.
