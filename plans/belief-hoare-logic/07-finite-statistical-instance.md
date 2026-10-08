# PR 07: Exact finite statistical instance
**Date:** 2026-10-07

## TL;DR

Construct a concrete finite statistical model with exact rational probabilities and prove that it satisfies the BHL test contracts. Prove the positive single/multiple-test procedures and hidden-test countermodels. These proofs discharge the concrete-instance obligations that abstract model fields leave open.

Plan status: approved by the researcher on 2026-10-07. Implementation status: pending. Original scope: B5. Dependency: PR 05. Proposed PR title: `theory(bhl): instantiate finite statistical tests`. Read the [shared contract and sequence](README.md) before execution. [Issue #24](https://github.com/ARA-Labs/Lara/issues/24) tracks this work; no definition or theorem below is claimed to exist yet.

## Problem

General metatheory can be vacuous if no meaningful test model inhabits its assumptions. An executable test can also compute a tail probability that fails the intended discrete calibration convention.

## Constraints

Use the numeric and statistical contracts frozen in PR 01. The finite instance does not replace general real-valued semantics or silently add a new probability axiom. Test combinations and their dependence assumptions must match the paper's rules. No empirical dataset, workload or experiment protocol is introduced.

Plan approval leaves PR 01's exact paper and numeric decisions to that prerequisite. This concrete branch uses PR 05 soundness and can proceed independently of PR 06 relative completeness. Completeness remains a required deliverable at the final B8 join.

## Proposed approach

### Which concrete method lands?

Construct a finite binary-sample test with rational probabilities, a defined null condition, statistic and tail relation. Prove that its computed p-value agrees with its null-distribution event. Prove the required calibration property for the chosen discrete convention; strict and non-strict tails must be stated explicitly, because discrete ties can change calibration. Instantiate the BHL test rules with that model and an inhabited precondition.

Exercise a valid single-test derivation, a valid accounted multiple-test procedure, and a hidden-test procedure whose proposed single-test postcondition fails in a reference world. Include a positive world where statistical belief holds while the alternative is false through the exceptional-sample branch. This catches an unsound truth-elimination bridge. Any further procedure-level false-assertion bound requires its own distribution and strategy proof; BHL satisfaction alone does not supply one.

Use an explicit finite distribution, sample space and interpretation. A rational probability carrier requires nonnegative mass and normalization proofs. State whether the null is simple or composite and prove the null-model conditions needed by the selected test. The model must contain nonempty worlds satisfying a useful precondition.

### Which files own it?

| File | Deliverable |
| --- | --- |
| `lean/Lara/BHL/FiniteProbability.lean` | Focused finite mass/event and exact arithmetic results needed by the instance |
| `lean/Lara/BHL/Tests/Binary.lean` | Null/alternative, statistic, tail relation, p-value, calibration and test-model instance |
| `lean/Lara/Examples/BHLStatistical.lean` | Valid single/multiple-test derivations, hidden-test and belief-without-truth countermodels |
| `docs/theory-bhl.md`, `lean/Lara.lean`, `lean/AxCheck.lean` | Quantitative source mapping, explicit hypotheses and proof audit |

Reuse PR 02 history identity, PR 03 belief semantics and PR 05 soundness directly. Prove test combination/decomposition assumptions and instantiate the relevant rules; do not add an opaque field that certifies the example output. No proof in this PR may require PR 06 completeness. In the theorem inventory, distinguish inherited BHL rules from their finite specializations and the probability, calibration and concrete countermodel results proved here.

### Which acceptance evidence is required?

- Computed p-values agree with their exact null-distribution events.
- The selected strict/non-strict discrete convention has the required calibration proof, including ties.
- The concrete model satisfies the independently stated primitive model/test obligations.
- Useful single-test and correctly accounted multiple-test derivations are inhabited.
- A hidden-test procedure violates its proposed single-test postcondition in a concrete reference world.
- Statistical belief can hold with a false alternative through the exceptional-sample branch.
- Bind concrete modeled applications to their actual run witnesses and precondition-satisfaction proofs. Retain residual interpretation/model assumptions; supported applicability alone is not a premise proof.
- Execute exact arithmetic and the concrete program/history operations through a throwaway library-based main. Print computed rationals and witnessed postconditions; fail on a mismatch.
- Run `make local-gates`; record the symbolic proofs separately from the finite execution output.


## Alternatives considered

A fixed output table or caller-authored approval flag would not construct the model. Replacing the calibration result with an assumed inequality would hide the statistical obligation. Arbitrary adaptive or repeated procedures are not covered by a single-test theorem.

## Tradeoffs

A small binary test is easier to mechanize and audit than a broad statistics library. Its assumptions and exact coverage must remain visible; it does not justify every continuous test or unaccounted repeated assertion.

## Migration

No corpus regeneration or frozen-data change is needed. PR 08 builds checking/execution over these real definitions, not a duplicated demonstration model. Continue the concrete branch through PR 09 without waiting for PR 06. The last-landing PR, either PR 06 or PR 09, must base or rebase on main containing the other branch and complete B8's inventory and integrated gates on its candidate tree before review. Record workstream completion only after both merge. Move the instance and negative witnesses into the durable theorem record and remove this plan when landed.

## Recommendations

1. Define and prove the finite probability/test model.
2. Prove and execute the valid and invalid procedure witnesses.
3. Land before [PR 08](08-executable-checking.md).
