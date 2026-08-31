# M2b restricted-class realization spike

## Gate decision

**INCONCLUSIVE**

This spike does not establish HARDNESS and does not establish a TRACTABILITY
CANDIDATE. The required family-wide checker equation was not mechanized, so the
compile-image, realizability, and polynomial-size obligations that depend on it
were not attempted after the gate.

## Evidence produced

The spike source is
`lean/Lara/Examples/Complexity/Realization.lean`.

- `checkUnit_path_ok` constructs the closed `d -> b(0) -> a(0)` checker
  fixture, with named output `acceptedPathUnit`. `directedPathIso` is the
  Lean-checked identity-position `StructuredAFIso` to the hand-written
  three-node carrier.
- `checkUnit_cycle_ok` constructs the closed
  `lit(0,0) <-> lit(1,0)` checker fixture, with named output
  `acceptedCycleUnit`. `twoCycleIso` is the Lean-checked identity-position
  `StructuredAFIso` to the hand-written two-cycle carrier.
- `checkUnit_reversedPath_rejected` is the negative control: reversing the
  first path declaration is rejected because `b(0)` is not contrary to `d`.
- `rawUnitOfFormula`, `gammaOfFormula`, and `groundOfFormula` encode the
  intended formula-indexed raw gadget. They allocate two root literal leaves
  for each duplicate-free occurring variable, one fixed-rule clause argument
  with three positional occurrence leaves per clause, one query leaf, mutual
  literal-root attacks, satisfying-literal positional undermines, and
  clause-root undermines of query.

## Implemented API

`Lara.Complexity.Context` exposes the formula-independent `m2bSigma`,
`m2bPolicy`, `m2bRegistry`, the stable `m2bClauseRuleId`, and constructors for
the policy's ground atoms. The policy has one ordinary defeasible clause rule
and six directional contrary schemas; the registry is empty.

`Lara.Complexity.Encoding` exposes `Literal`, `Clause3`, `Formula3`,
`CarrierCode`, `M2bPromise`, `FixedCredComplete`, and
`fixedCredCompleteB`. `CarrierCode.decode` preserves node order and interprets
its square Boolean matrix as the attack relation. `fixedCredCompleteB_iff`
connects the executable complete-semantics profile to the existential
`FixedCredComplete` proposition.

The two size functions have different contracts:

- `Formula3.byteSize` is the exact UTF-8 byte length of
  `Formula3.encode`, its canonical S-expression serializer.
- `CarrierCode.byteSize` is a frozen **carrier accounting measure**: one
  framing unit, the UTF-8 sizes of atom keys and the decimal query index, and
  one unit per Boolean matrix cell. No `CarrierCode` serializer exists, so
  this measure is not a serialized wire length. `matrixByteSize_eq_square`
  proves that a valid square matrix contributes exactly the square of the
  carrier length.


The controller validated the completed closed-fixture spike:

- `lake env lean Lara/Examples/Complexity/Realization.lean` passed with no
  output.
- `lake build` passed all 90 jobs.

These results check the concrete checker equations, negative control,
structured isomorphisms, and raw formula constructor in the source file. They
do not supply or validate the absent general `acceptedUnitOfFormula`,
`checkUnit_formula_ok`, compile-image, realizability, or size results; the gate
therefore remains INCONCLUSIVE.

## Exact obstruction

The missing mandatory theorem is

```lean
theorem checkUnit_formula_ok (φ : Formula3) :
  Check.Unit.checkUnit (gammaOfFormula φ) m2bRegistry
    (groundOfFormula φ) (rawUnitOfFormula φ) =
  .ok (acceptedUnitOfFormula φ)
```

No `acceptedUnitOfFormula` is defined. Closing this equation through
`Check.Unit.checkUnit_complete` requires simultaneous formula-family proofs
of all of the following generated-list invariants:

1. duplicate-freedom of root support terms across literal, indexed clause, and
   query namespaces;
2. recursive `HasSupport` for each `m2bClauseRule` instance, including exact
   substitution domain and three premise-conclusion matches;
3. `HasAttack` for every mutual root and positional undermine declaration;
4. source and target membership for every generated attack; and
5. `Compile.AttackComplete` for exactly the fixed-policy contrary pairs.

The existing checker API exposes these as whole-program obligations; the spike
did not produce the required compositional lifting lemmas for the mapped and
flat-mapped formula lists. Ground coverage is explicit in the data
(`groundOfFormula` is the projection of the same leaf table used by
`gammaOfFormula`) but its universal `GroundCoversUsedLeaves` theorem is also not
closed.

Without the checker equation there is no accepted unit from which to prove
that compilation has exactly the gadget edges and no closure-generated extras.
Consequently the following required surfaces do not exist and are not claimed:

- `reduceCode`;
- the general compile-image `StructuredAFIso` and exact-edge theorem;
- `reduce_realizable`;
- `reduce_nodes`;
- `reduce_byteSize`.

## Fixed-context audit

The attempted raw constructor fixes the fields that `Lara.Unit` stores
definitionally:

- signature: exactly `m2bSigma`;
- policy: exactly `m2bPolicy`.

`rawUnitOfFormula_fixedFields` proves those two facts uniformly for every
formula. Canonicalization and registry selection happen at the checker
boundary, not in a raw unit: the target checker equation fixes the registry to
`m2bRegistry`, whose type fixes the canonicalizer to `id`, and
`m2bRegistry_empty` proves that registry is empty.

Only `Γ`, finite ground atoms, leaf identifiers, substitutions, raw support
terms, and raw attack declarations depend on the input formula. No
formula-specific policy, signature, registry, axiom, `sorry`, or placeholder
was introduced.

## Stop condition

The mandatory realization gate stopped at **INCONCLUSIVE**. Deferred
complexity work must not proceed from this spike, and `lean/Lara.lean` must
not import the incomplete module. A future attempt may resume only by closing the
general checker equation and then all compile-image and size obligations; it
must not reinterpret this record as evidence for hardness or tractability.
