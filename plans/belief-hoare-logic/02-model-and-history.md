# PR 02: Epistemic model and test history
**Date:** 2026-10-07

## TL;DR

Implement typed memory, test history, world histories and observation-based accessibility. Prove the local model laws and history invariants in the same PR. Construct a nonempty model and a same-final-memory/different-history witness before calling the semantic boundary complete.

Plan status: approved by the researcher on 2026-10-07. Implementation status: pending. Original scope: B1. Dependency: PR 01. Proposed PR title: `theory(bhl): formalize worlds and test histories`. Read the [shared contract and sequence](README.md) before execution. [Issue #24](https://github.com/ARA-Labs/Lara/issues/24) tracks this work; no definition or theorem below is claimed to exist yet.

## Problem

BHL observes histories, not just final reported values. Dataset aliasing or deduplicated tests can erase the very distinction that later belief and procedure proofs require.

## Constraints

Use the exact model restrictions frozen in PR 01. The general model must not require a finite universe or execution fuel. Preserve the paper's visible/invisible-variable distinction, explicit action observations, nonempty world histories and initial-history conditions. This PR makes no assertion-language soundness or physical capture claim.

PR 01 must settle the exact paper and numeric contracts before implementation; this plan's approval leaves those decisions open. BHL observation equality induces an equivalence relation and supports its S5 laws. Lara's existing possible-world accepted-context bridges generally provide normal K semantics; they do not supply this equivalence relation. Keep the accessibility relations distinct. Transport between their modalities requires an explicit relation and proof.

## Proposed approach

### Which model definitions and files land?

Use closed sum types for fixed vocabulary and distinct identifier types for program variables, tests, datasets, and hypotheses. Keep model denotations separate from identifiers. In particular, the paper's history is indexed by dataset values and records test multiplicity. Distinct names for equal data must not reset that history; an executable representation must prove its correspondence to the reference indexing. Conversely, the later process layer may need execution lineage beyond equal values. Document the two meanings instead of silently merging them.

| File | Deliverable |
| --- | --- |
| `lean/Lara/BHL/Types.lean` | Extend PR 01's distinct identities, value/sort vocabulary and well-typed memory carriers |
| `lean/Lara/BHL/Model.lean` | States, nonempty worlds, state/world observation and observation-induced accessibility |
| `lean/Lara/BHL/History.lean` | Dataset-value-indexed test multisets, multiplicity and history-variable consistency |
| `lean/Lara/Examples/BHLModel.lean` | Inhabited model, aliasing/multiplicity and snapshot-separation witnesses |
| `docs/theory-bhl.md`, `lean/Lara.lean`, `lean/AxCheck.lean` | Landed model statements, imports and audit rows |

Model denotations must remain separate from symbolic identifiers. Prove that consistent renaming preserves bindings, while equal dataset values retain the same history accounting even through distinct names. Keep any representation relation between history multisets and executable carriers explicit.

### Which proofs are required now?

- Observation equality induces reflexive, symmetric and transitive accessibility on valid worlds.
- World extension preserves the prefix and records the intended action/state observation.
- History update preserves existing entries and increments the relevant test multiplicity.
- History-variable values agree with the underlying dataset-value-indexed multiset.
- The symbolic memory/history operations preserve their typing and consistency invariants.
- A nonempty model inhabits the interface and exhibits equal final memory with different recorded histories.
- State each epistemic law against BHL's observation-induced relation; do not transfer S5 laws to Lara's accepted-context accessibility.

### How is this PR exercised?

Run a throwaway Lean main over the real model/history operations. Observe the test counts before and after a repeated execution, the effect of dataset aliasing, and the different history observations for the same final memory. Fail on a discrepancy. Elaborate the theorem-bearing examples, run `make local-gates`, and update the durable theorem map in this PR. No assertion or BHL derivation result is claimed yet.


### What design should the server continuation preserve?

The following is an unimplemented design from the contract audit, not checked model evidence:

- Separate typed visible bindings from immutable ordinary hidden bindings. Derived history counts are not independently writable hidden variables.
- Keep `RawWorld` as an initial state plus finite later states. Define admitted worlds by empty initial ledger, constant ordinary hidden memory, independent initial-evidence conditions and independently checked adjacent command/sampling edges. Admit every trace satisfying those local conditions, rather than a caller-selected universe.
- A primitive command effect receives only visible memory and yields visible memory plus a finite test-event delta. Sampling is a separate historical action, not a testing-program constructor. History edges compare count denotations, not event-list order.
- Define `TraceAllowed h observations`, derive `compatibleHidden w`, and construct `rebuildHidden w h` for every compatible hidden memory. Prove prefix closure, lawful extension and accessible forth/back; none is a model field asserting the desired modal theorem.
- Derive sampling provenance from actual adjacent sampling transitions, never an initial-state action label.
- Define the assertion view by current visible memory, canonical ledger, actual ordinary hidden memory, exact compatible-hidden set and derived sampling provenance. Its carrier is the image of admitted worlds. Prove the bounded-morphism correspondence to full ordered observation accessibility; do not replace that reference relation with endpoint equality.

## Alternatives considered

A set of tests drops repeated execution. History indexed only by fresh author-chosen dataset names permits an alias to reset accounting. A final-memory-only world representation cannot support the separating witness.

## Tradeoffs

Value-based history identity is faithful to the paper, while later research-process lineage may need more information. State the distinction now; do not add unrelated physical execution tracking to this model PR.

## Migration

The new model is outside Lara's core. Reuse the reviewed types and prepare them for PR 03's satisfaction semantics without declaring satisfaction in this PR. Move the proved model laws to the durable theorem record and remove this executed plan.

## Recommendations

1. Implement the reviewed carriers and observation definitions.
2. Prove and execute the history/alias invariants.
3. Land before [PR 03](03-assertions-and-belief.md) adds assertions.
