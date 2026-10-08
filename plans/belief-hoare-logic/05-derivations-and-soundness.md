# PR 05: BHL derivations and soundness
**Date:** 2026-10-07

## TL;DR

Define BHL triples and explicit derivations, then prove every mapped rule and the global soundness theorem. Keep the underlying assertion-theory obligations explicit. This PR completes B4's soundness part and enables the independent relative-completeness and concrete-instance branches.

Plan status: approved by the researcher on 2026-10-07. Implementation status: pending. Original scope: B4, soundness. Dependency: PR 04. Proposed PR title: `theory(bhl): prove derivation soundness`. Read the [shared contract and sequence](README.md) before execution. [Issue #24](https://github.com/ARA-Labs/Lara/issues/24) tracks this work; no definition or theorem below is claimed to exist yet.

## Problem

A checker or derivation tree is trustworthy only if each rule preserves the independent reference meaning. Rule side conditions, especially substitution and parallel noninterference, must survive translation from the paper.

## Constraints

Use the exact assertion and execution semantics merged in PR 03-04. Derivability must be an inductive proof system with the paper's mapped rules, not semantic validity renamed as a constructor. Expose assertion-validity and statistical-model premises as independently justified hypotheses. Relative completeness remains owned by PR 06.

## Proposed approach

### Which files and rules land?

| File | Deliverable |
| --- | --- |
| `lean/Lara/BHL/Derivation.lean` | Explicit proof rules, semantic triple validity and precise premise/side-condition carriers |
| `lean/Lara/BHL/Soundness.lean` | Local rule soundness and the global derivation-to-validity theorem |
| `lean/Lara/Examples/BHLSoundness.lean` | Inhabited assignment, testing, composition, loop and parallel derivations |
| `docs/theory-bhl.md`, `lean/Lara.lean`, `lean/AxCheck.lean` | Per-rule source correspondence, hypotheses and audited proof rows |

Implement the rule inventory frozen in PR 01. Connect assignment rules to PR 03's actual substitution theorem, loop rules to invariant preservation, and parallel rules to PR 04's noninterference/correspondence results. Statistical rules must use the reviewed local test conditions, not a model field that asserts the desired global conclusion.

### How is the soundness proof constructed?

Use the audited published argument, or the compatible checked proof selected in PR 01 with its representation correspondence. For a local reconstruction, prove global soundness by induction on the explicit `Derivation`. Prove each rule case against satisfaction and execution defined independently in PR 03-04.

| Rule family | Semantic proof ingredient |
| --- | --- |
| Assignment | Capture-avoiding substitution and its satisfaction theorem |
| Statistical test | Actual test/history transition and the independently stated primitive test contracts |
| Sequencing and branches | Execution decomposition and the induction hypotheses for the selected subderivations |
| Loop | Invariant initialization and preservation, with induction over the finite terminating execution |
| Parallel composition | The audited read/update side conditions and execution correspondence |
| Consequence | Valid underlying assertion implications, with no automatic arithmetic-oracle claim |

The general proof remains conditional on explicit model/test premises. PR 07 discharges those premises for its concrete distribution and calibration convention. Neither a model field asserting global soundness nor semantic validity stored as the sole derivation constructor counts as this proof.


### What is the required theorem boundary?

```text
Derivation assumptions pre program post
  + valid underlying assertion premises
  + stated model/program side conditions
  => validTriple model pre program post
```

This is a proposed statement shape. The frozen contract decides the exact contexts and hypotheses. Semantic validity quantifies over every terminating reference run from a precondition-satisfying world. It does not prove termination, empirical truth or real-world model applicability.

Keep conditional procedure validity, modeled application and defeasible artifact warrant separate. Applying the theorem to a particular execution requires a run witness for the exact model/program and real satisfaction of `pre` at its initial world. A Lara justification of applicability supplies neither that premise nor BHL knowledge of it. Residual model and interpretation assumptions stay visible. Partial correctness establishes the stated postcondition only for terminating runs satisfying the premises; it proves neither truth of the statistical alternative nor a physical execution record.

The durable theorem inventory must identify which statements mechanize inherited BHL results, which specialize those results to an instance, and which require new Lara bridge proofs. Record each statement's source, hypotheses and proof dependencies. PR 07 supplies concrete instance proofs; PR 09 supplies the dependency-sensitive artifact results. Do not attribute the inherited soundness theorem to the bridge.

### What makes this PR complete?

- Every mapped rule has an audited soundness proof and all side conditions visible.
- The global theorem composes those proofs over the actual derivation system.
- Nonempty examples inhabit the rule interfaces; no false precondition substitutes for a useful proof.
- A negative example shows why dropping a substantive side condition would invalidate a rule, using the independent semantics.
- Execute a throwaway Lean main over concrete derivation-backed runs and evaluate their pre/post observations. Fail if the computed postcondition disagrees; no output-only theorem list counts as a smoke run.
- Run `make local-gates` and record the new proofs and witnessed scope now, not in PR 09.


## Alternatives considered

A derivation constructor containing only a proof of whole-triple semantic validity makes rule soundness tautological. Deferring all rule proofs until completeness would violate the mechanization discipline. Neither approach is allowed.

## Tradeoffs

The rule and soundness inventory is a substantial review by itself. Separating completeness lets reviewers finish this semantic-preservation check without also inspecting invariant expressiveness and proof reconstruction.

## Migration

Do not implement `Completeness.lean` as a placeholder or publish a completeness alias. Both PR 06 and PR 07 consume these merged rules and soundness result independently. Relative completeness remains mandatory, but the concrete branch `07 -> 08 -> 09` does not depend on it. B8 is the required final join: the last-landing PR, either PR 06 or PR 09, must base or rebase on main containing the other branch, record the complete inventory and run all integrated gates on its candidate tree before review. Record workstream completion only after both merge. Keep core checking untouched; retire this plan once its rule proofs and durable records land.

## Recommendations

1. Implement the mapped derivation rules with explicit premises.
2. Prove every rule and global soundness, then execute concrete witnesses.
3. Open both [PR 06](06-relative-completeness.md) and [PR 07](07-finite-statistical-instance.md) after this PR lands; neither branch replaces the other.
