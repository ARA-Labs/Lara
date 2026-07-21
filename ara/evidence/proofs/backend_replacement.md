# Theorem 2: backend replacement preserves claim status

- **Source**: docs/strict-backend-decision.md §5, Theorem 2. Target: Lean 4 mechanization (spec §9
  result 9); currently paper-proved, not machine-checked.
- **Grounds**: C04.
- **Assumptions used**: the six backend obligations (constraints.md; strict_backend.md §2); grounded
  semantics; finite argument set.

## Statement

Let `P_β` and `P_γ` be source-identical programs after erasing strict-certificate payloads. Assume the
corresponding payloads under backends `β` and `γ` accept exactly the same strict instances. Let
`eraseCert` replace each accepted certificate annotation by `certified` while preserving argument
names, rule instances, conclusions, obligations, and positions. Then `compile(P_β) ≅ compile(P_γ)`
under the node bijection induced by equal `eraseCert` argument names/skeletons, and every claim has the
same `justified`/`defeated`/`contested`/`gap` status.

## Proof (from the source, verbatim structure)

1. By structural induction on support terms, the same leaves and rule instances check in both
   programs. The only differing case is `Strict-Cert`, equalized by the acceptance hypothesis.
2. Certificate payloads do not occur in conclusions, positions, obligation sets, or attack typing.
   Therefore `eraseCert` gives a bijection between complete argument nodes and typed attacks.
3. Compilation preserves that bijection, so it is a graph isomorphism between the target Dung
   frameworks.
4. Dung's characteristic function commutes with graph isomorphism. Iteration from the empty set
   therefore yields corresponding unique grounded labels.
5. Claim aggregation is a deterministic function of corresponding support sets, equal holes, and
   corresponding labels. Statuses are equal. QED.

## Why it matters

This is the formal reason not to make any one logic (LP, S4, …) foundational to **claim-status
semantics**: status cannot distinguish LP from another adapter with the same strict acceptance profile.
Replay, certificate size, backend theory, and dependency reports may differ and remain visible for
audit — only *status* is invariant.

## Mechanization plan (docs/mechanization-plan.md §4)

Parametricity over the `Backend` structure + graph isomorphism under `eraseCert` + invariance of the
grounded least fixed point under that isomorphism. "Should"-tier (result 9): high reviewer value;
include if the M2 schedule holds.
