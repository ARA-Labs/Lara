# PW-T9 — exact structural-path composition

## Result

Issue #190 (tracker #189) is implemented as two stacked pull requests. PR #233
freezes the first-leg-first Kleisli laws and adds `StructuralBridge.comp`,
`support_transport_comp`, indexed `BridgePath`, stepwise/folded path coherence,
and `path_support_transport`, without changing the T6 structural contract.
PR #236 adds applicability factorization, `Commutes`/direct-path agreement,
accepted-edge separation, expanded witnesses, durable records, and final audit
wiring.
The reviewed foundation head is `3362f00` (tree-identical to merged `54c2052`);
the synchronized implementation head verified before this ARA closeout is
`43541ca`.

`SymMap.comp m₂ m₁` applies `m₁` first. Every lifted translation used by T6
commutes with this composition, including `trAtom_comp`, `trRule_comp`, and
`trSupport_comp`. Consequently a composite is defined exactly when the first
leg is defined and the second leg accepts its image. `StructuralBridge.comp`
chains the three T6 contract clauses through the intermediate environment;
`support_transport_comp` retains both intermediate and final checked judgments.

`BridgePath` is an indexed path whose constructors carry the intermediate rule,
evidence, and certificate environments. `BridgePath.compose` folds the path to
one structural bridge and `BridgePath.trans` executes the stepwise partial
support translation. `BridgePath.trans_eq_compose` proves those views equal;
`path_support_transport` therefore transports any checked support along any
chosen typed path while preserving its obligation list.

A separately named direct bridge agrees with a chosen arbitrary path only under
`Commutes`, whose atom- and support-translation fields are equivalent to full
symbol-map and leaf-map equality (`Commutes.of_maps_eq`). Support substitutions
make constructor translation observable directly. `direct_transport_agrees`
then gives the common translated conclusion and checked target judgment.

The outer accepted relation is not silently identified with checker
applicability: `Accepted R m lm w u` is literally
`R w u ∧ Admits m lm w u`, and `accepted_iff_of_commutes` requires both
`Commutes` and a caller-supplied equivalence between the direct and path
candidate relations. `t7_accepted_needs_candidate_coherence` keeps commutation
and applicability true while a false path relation makes acceptance fail.

The witness module exercises both sides of the contract. A live renaming route
has two genuine renaming edges, a separately named direct bridge, a three-edge
path with a final reflexive edge, and direct/path agreement. The leaf-map
negative swaps checked evidence leaves and carries source and target
`HasSupport` judgments. The predicate-only negative deliberately uses empty
environments, proves equal leaf and constructor maps plus identical
constructor-bearing support translation, and isolates only atom disagreement.
`gap_admits_comp_fails` uses a checked constructor-bearing support and bridges
whose policy, evidence, and certificate parameters are exactly those of the
checked endpoint context. It shows both `AdmitsSteps` and composite `Admits`
fail when the second edge omits the first edge's image. `gapPath` connects an
atom-translation failure to
`incomparable translationUndefined`; `gapSupportPath` separately shows two
successful support translations followed by a constructor-map gap.
`certComp_two_live_legs` chains two inhabited, non-identity certificate
judgments through the composite bridge.

## Verification (2026-09-03)

PR #233, after its foundation review fixes:

```
$ cd lean && lake build
Build completed successfully (140 jobs).

$ cd lean && python3 ../scripts/check-axcheck-coverage.py AxCheck.lean \
    Lara/PW/Compose.lean Lara/Examples/PWCompose.lean
AxCheck coverage passed (33 declarations).

$ cd lean && (set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
Axiom audit passed.
```

PR #236, after review fixes and synchronization with reviewed PR #233:

```
$ cd lean && lake build
Build completed successfully (140 jobs).

$ cd lean && python3 ../scripts/check-axcheck-coverage.py AxCheck.lean \
    Lara/PW/Compose.lean Lara/Examples/PWCompose.lean
AxCheck coverage passed (67 declarations).

$ cd lean && (set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
Axiom audit passed.
```

The 33- and 67-declaration counts are the targeted PW-T9 two-file scope, not
the repository-wide CI gate, which audits ten source files.

The audit reports no `sorryAx`, no `ofReduceBool`, and no axioms outside
`propext`, `Classical.choice`, and `Quot.sound`. The PR #236 diff against the
synchronized PR #233 head leaves the frozen T6 modules
`Lara/PW/Translation.lean`, `Lara/PW/Structural.lean`, and
`Lara/PW/Support.lean` unchanged.

## Boundary

PW-T9 is exact structural-path composition for the existing bridge-global,
functional partial translation. It does not prove grounded-status preservation;
that requires attack correspondence (T8, #193). It does not define approximation
bridges, their comparison spaces, or error/convergence laws. A failed
intermediate translation remains incomparability at the outer comparison layer,
never a fifth local status.

Full record: `docs/theory-pw-t9-path-composition.md`.
