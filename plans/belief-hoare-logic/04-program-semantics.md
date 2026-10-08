# PR 04: Program execution and parallel correspondence
**Date:** 2026-10-07

## TL;DR

Implement the published testing-program syntax and reference execution relation. Prove typing, test-history updates and the sequencing, branch, loop and noninterfering parallel correspondence results. Keep partial correctness distinct from termination and schedule fairness.

Plan status: approved by the researcher on 2026-10-07. Implementation status: pending. Original scope: B3. Dependency: PR 03. Proposed PR title: `theory(bhl): prove program execution semantics`. Read the [shared contract and sequence](README.md) before execution. [Issue #24](https://github.com/ARA-Labs/Lara/issues/24) tracks this work; no definition or theorem below is claimed to exist yet.

## Problem

Soundness needs the exact operational meaning of a program. Equal final memory does not imply equal trace semantics, and one chosen parallel schedule cannot represent every permitted interleaving.

## Constraints

Use the PR 01 program/model contract and PR 02-03 definitions. Include assignment, test execution, sequencing, conditionals, loops and parallel composition. Enforce the paper's update/read noninterference restrictions for parallel programs. This is general reference execution, not the bounded evaluator planned for PR 08.

## Proposed approach

### Which program files land?

| File | Deliverable |
| --- | --- |
| `lean/Lara/BHL/Program.lean` | Typed expressions/commands/programs, observable-variable restrictions and read/update sets |
| `lean/Lara/BHL/Execution.lean` | Small-step execution, termination relation and test-history updates |
| `lean/Lara/BHL/Parallel.lean` | Interleaving semantics, side conditions and noninterfering parallel correspondence |
| `lean/Lara/Examples/BHLExecution.lean` | Assignment/test, branching, terminating loop and parallel trace witnesses |
| `docs/theory-bhl.md`, `lean/Lara.lean`, `lean/AxCheck.lean` | Operational source mapping, immediate proofs and audit coverage |

Formalize the effect of executing a statistical test on its result variable, history variables and dataset-value-indexed multiset. Preserve the ordered command/world trace; do not quotient distinct histories merely because the final memory matches.

Carry the exact model, program, initial world, terminal world and history in each run witness. A conditional procedure theorem does not establish that a particular run occurred or that its initial world satisfies the precondition. Modeled application requires both an actual run witness and real satisfaction of that precondition in the declared model. Reference execution describes the modeled run; it does not certify physical logging or natural-language interpretation. Use complete modeled histories here; general partial-history reasoning remains in issue #23.

### Which operational results finish the PR?

- Well-typed execution preserves memory and history consistency under the model hypotheses.
- A test execution updates exactly the declared result/history entries and accounts for multiplicity.
- Sequencing and branch equations match the terminating relation.
- Loop unfolding and terminating-run decomposition are proved without assuming all loops terminate.
- Parallel runs decompose/recombine under the exact noninterference restrictions.
- Any final-state equivalence result for noninterfering interleavings retains its hypotheses and does not assert identical action traces.
- Run witnesses retain the bindings needed to apply PR 05's conditional theorem without substituting supported applicability for precondition satisfaction.

### What execution evidence is required?

Use a throwaway Lean main to evaluate concrete library-defined next-step cases and a declared terminating schedule; arbitrary reference execution need not be decidable. Observe both a terminating loop and two permitted parallel schedules, checking the proved common observations while retaining their different traces. Include a side-condition failure witness and equal-memory/different-history cases. Run `make local-gates`, elaborate the examples and update the theorem record. Permanent general finite execution checking remains PR 08.


## Alternatives considered

Replacing parallel execution with one deterministic order would change the reference language. Dropping loops would remove a completeness obligation from the original B3/B4 scope. Neither reduction is part of this split.

## Tradeoffs

Interleaving proofs add review work but make the later soundness rule's assumptions explicit. A concrete scheduled smoke run checks executable local operations; it does not prove universal schedule coverage by itself.

## Migration

No Haskell command, wire schema, source revalidator or production orchestrator changes. PR 05 defines triples and derivations over this exact execution relation. Remove this plan after the operational theorems and witnesses land.

## Recommendations

1. Implement command effects and prove their local invariants.
2. Prove the composite and parallel execution results.
3. Land before [PR 05](05-derivations-and-soundness.md).
