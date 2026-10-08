# PR 08: Executable proof checking and finite semantics
**Date:** 2026-10-07

## TL;DR

Implement executable BHL derivation checking and exact finite-model satisfaction, with proofs relating both to the reference theory. Add the real `bhl-examples` runner and include it in the local Lean gate. Report incomplete exploration separately from counterexamples or malformed inputs.

Plan status: approved by the researcher on 2026-10-07. Implementation status: pending. Original scope: B6. Dependency: PR 07. Proposed PR title: `feat(bhl): check derivations and execute finite models`. Read the [shared contract and sequence](README.md) before execution. [Issue #24](https://github.com/ARA-Labs/Lara/issues/24) tracks this work; no definition or theorem below is claimed to exist yet.

## Problem

A proof system and mathematical model are not yet an executable checking capability. The checker must verify rule premises, and a bounded execution search must not claim universal assurance when it exhausts fuel.

## Constraints

Use PR 02-05 and PR 07 definitions without a second assertion/program representation unless a checked decode relation is necessary. PR 06 is not a dependency of this concrete branch. No production wire schema, Haskell command or general arithmetic solver is introduced. General assertion-premise proof evidence and finite-model discharge have distinct coverage statements.

## Proposed approach

### What execution boundary must remain explicit?

Executable model checking applies to a named finite instance with decidable primitive interpretations and exact rational test probabilities. Prove that it computes reference satisfaction for that instance. A fuel-limited interpreter reports exhausted exploration separately from a failed precondition, a false postcondition, and malformed input. Parallel execution is nondeterministic; a chosen schedule has deterministic replay, but one successful schedule does not establish a triple for all terminating interleavings.

General derivations may use Lean proofs for underlying assertion implications. The finite checker may discharge a premise by exact satisfaction checking only over its named model. Neither accepts a caller-supplied Boolean as proof. State the decidable model restrictions and prove that their carriers and interpretations preserve the independently defined semantics.

Prepare evidence for PR 09 that retains the exact method/derivation, model, `P/C/Q`, checked premises, actual run, source snapshot and dependency identities specified by PR 01. Keep residual assumptions and declared history coverage explicit. A successful derivation check establishes conditional validity. Modeled application also requires the run witness and satisfaction of `P` in the bound initial world. Neither result is a Boolean artifact approval, a proof of physical log completeness, or a conversion from finite-model validity to general validity. PR 09 owns artifact warrant and its revalidation proofs.

### How do the checker and semantic proofs compose?

Prove checker-to-derivation correspondence first: successful checking produces a derivation of the exact bound triple with checked or proof-backed premises. Then apply PR 05's soundness theorem to obtain semantic triple validity. For a concrete application, separately supply initial-world satisfaction and the reference execution witness to derive the final postcondition. Keep each premise visible so finite-model discharge cannot become unrestricted validity and supported applicability cannot replace satisfaction.

Prove finite satisfaction and bounded execution correspondence directly against their independent reference definitions. Agreement on example outputs is not this proof. Reuse the BHL soundness dependency rather than reproving it inside the checker or assuming checker correctness follows from the paper.


### Which files and build changes land?

| File | Deliverable |
| --- | --- |
| `lean/Lara/BHL/Check.lean` | Executable derivation validation with explicit premise evidence and soundness |
| `lean/Lara/BHL/FiniteModel.lean` | Exact finite satisfaction and bounded execution with correspondence proofs |
| `lean/Lara/BHL/ExampleMain.lean` | Actual checker/semantic runner over the proved examples |
| `lean/lakefile.toml` | Register the `bhl-examples` executable |
| `Makefile` | Add `bhl-theory` and include it in `lean-gate` now |
| `docs/theory-bhl.md`, `lean/Lara.lean`, `lean/AxCheck.lean` | Executable coverage, imports, theorem record and audit |

Use closed error/result types for malformed inputs, invalid derivations, failed preconditions, false postconditions and incomplete execution/search. Reference semantics remains unbounded. A chosen parallel schedule is a witness, not an all-schedules proof; any finite exhaustive claim must establish its declared coverage.

### What proofs and runs finish the PR?

- Accepted derivations satisfy the reference triple under the checked or proof-backed premises.
- Finite satisfaction computes the reference meaning exactly for the declared finite model/fragment.
- Bounded execution results correspond to actual reference runs; exhausted exploration cannot become a completed universal claim.
- The runner exercises dataset aliasing and test multiplicity, valid inference, hidden testing, accounted multiple comparisons, a loop witness, noninterfering parallel runs, fuel exhaustion and belief without truth.
- Include consumer-visible invalid-premise and invalid-side-condition cases rather than testing only that a wrapper forwards values.
- Exercise evidence carrying a conditional theorem with residual assumptions without reporting an established application. Reject a mismatched model, premise or run binding; do not replace missing satisfaction evidence with defeasible support.
- Run `(cd lean && lake exe bhl-examples)` and require a nonzero exit for unexpected results. The runner uses library definitions and computed outputs, never hardcoded approvals or a theorem-name listing.
- Run `make local-gates` with `bhl-theory` included, plus the three ARA gates when research records change.

Permanent tests, if necessary for an uncertain consumer-visible edge, follow repository conventions. Do not introduce source-text, forwarding, mock-echo or bare-not-throw tests. Remove all temporary mains after the permanent runner proves the changed paths.


## Alternatives considered

Executing examples without checker/semantics proofs gives conformance evidence only. Checking one favorable schedule and labeling the program valid ignores nondeterminism. Omitting the runner from local gates postpones the executable contract to an unrelated PR.

## Tradeoffs

Exact finite execution is reproducible but narrower than general BHL semantics. The result types and theorem record must make that restriction visible instead of using a search limit as a hidden model assumption.

## Migration

This PR establishes standalone BHL execution without adding the Lara bridge. Existing verdict bytes, anchor discovery and source/evidence behavior stay unchanged. PR 09 consumes the exact evidence and extends the same runner with bridge outcomes. Every stage PR targets `feat/belief-hoare-logic`; PR 06 has already landed there. PR 09 must execute B8's joined inventory and integrated gates on that integration candidate before review. Record workstream completion only after PR 06 and PR 09 land, then bump the version, merge the completed feature to main with a merge commit, and publish and verify the release. Remove this plan after its executable and proofs land.

## Recommendations

1. Implement and prove checker/finite-semantics correspondence.
2. Register and exercise the real runner in the same PR.
3. Land before [PR 09](09-lara-bridge-and-acceptance.md).
