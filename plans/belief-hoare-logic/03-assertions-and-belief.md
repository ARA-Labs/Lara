# PR 03: Assertions, substitution and statistical belief
**Date:** 2026-10-07

## TL;DR

Define the BHL assertion language and its satisfaction relation over PR 02's model. Prove capture-avoiding substitution and the applicable epistemic/statistical-belief laws. Include a model where statistical belief holds although its alternative is false.

Plan status: approved by the researcher on 2026-10-07. Implementation status: pending. Original scope: B2. Dependency: PR 02. Proposed PR title: `theory(bhl): formalize assertions and statistical belief`. Read the [shared contract and sequence](README.md) before execution. [Issue #24](https://github.com/ARA-Labs/Lara/issues/24) tracks this work; no definition or theorem below is claimed to exist yet.

## Problem

The postcondition of a BHL triple is an epistemic statistical assertion. Replacing it with truth of a hypothesis or a generic permission flag would change the logic and make the later Lara bridge unsound.

## Constraints

Follow PR 01's exact syntax and binder contract. Satisfaction is independent of the executable checker and has no finite/fuel restriction. Keep population requirements and exceptional-sample alternatives explicit. General assertion validity is not automatically decidable.

Keep Lara's defeasible support judgment separate from BHL satisfaction: `Justified(P)` supplies neither `P` nor BHL `K(P)`. Support for applicability cannot discharge a mathematical premise. PR 01's artifact binding must retain the model, claim interpretation and residual assumptions alongside any conditional theorem. The artifact judgment need not assert that its postcondition is true in the actual world. Plan approval leaves PR 01's exact paper and numeric contracts open.

## Proposed approach

### Which files and definitions land?

| File | Deliverable |
| --- | --- |
| `lean/Lara/BHL/Assertion.lean` | Reviewed assertion AST, free variables, binding and model/world satisfaction |
| `lean/Lara/BHL/Substitution.lean` | Capture-avoiding substitution with the exact scope restrictions needed by rules |
| `lean/Lara/BHL/Belief.lean` | Knowledge/possibility, statistical-belief and history-assertion meanings |
| `lean/Lara/Examples/BHLBelief.lean` | Positive belief, explicit model/exception branches and truth-elimination countermodel |
| `docs/theory-bhl.md`, `lean/Lara.lean`, `lean/AxCheck.lean` | Source mapping, imports and immediate theorem audit |

Define any primitive statistical interpretation required by satisfaction through PR 01's explicit model contract. Do not assert calibration or the final BHL soundness theorem as a primitive field. A later concrete probability instance must discharge its own mathematical obligations.

### Which proofs land with these definitions?

- Type/scope preservation and semantic correctness of substitution, with all freshness and model restrictions exposed.
- Identity/composition or renaming laws where valid under the reviewed binder and modal restrictions.
- The applicable observation-invariance and epistemic/statistical-belief laws mapped in PR 01.
- Correct interpretation of history assertions, including multiplicity and dataset aliases from PR 02.
- A concrete countermodel to eliminating statistical belief into truth of the alternative.
- Exhibit the support/truth boundary without introducing a rule from Lara justification to satisfaction or knowledge. Keep unresolved interpretation and applicability assumptions explicit for PR 09.

Do not use extensional equality of symbols to discharge an interpretation assumption. If a proposed substitution law fails under a modality, prove the correct restricted statement and document the counterexample; do not change the assertion meaning to make a convenient lemma pass.

### What verifies this PR?

Elaborate the countermodel and positive examples. Execute a throwaway Lean main evaluating satisfaction in their concrete decidable submodels using the real definitions; this witness evaluation does not claim a general finite checker. Observe belief=true with alternative=false in the exceptional-sample case and fail if truth elimination slips into the implementation. Run `make local-gates` and add every proved statement to the theorem record and axiom audit.


### What syntax seam should the server continuation preserve?

This design is proposed, not implemented or proved. Use distinct assertion-only ghost sorts, intrinsically scoped bound ghosts, rigid ghost terms and ambient view terms. Arbitrary real/list/distribution values enter through typed ghosts or interpreted symbolic constants, not function-valued AST fields. Keep user functions/predicates restricted to explicit value arguments so they cannot conceal execution or satisfaction.

Use a quantifier-free modal AST and an outer assertion AST with binders; `K` cannot contain the outer AST. A full-world ghost may inspect its own fixed trace. Ambient terms cannot obtain the raw current world/trace, last action or trace length. Scoped `atWorld` targets the same ghost value; an `atView` target is a realized semantic view and is reevaluated at each accessible alternative under `K`, never frozen at the actual hidden value.

Prove full-world/view satisfaction correspondence, identical-ghost-environment schedule invariance, capture-avoiding ghost substitution and primitive memory/history preimages separately. Partial primitive enabledness must remain explicit: a liberal preimage is true when no successor exists. Exact primitive effect formulas expand visible evaluation, typed writes, pre-state ledger updates and preserved information/provenance; they are not whole-execution atoms.

## Alternatives considered

A primitive `Permits` flag would omit the published epistemic meaning. Treating a small decidable example as a complete assertion solver would exceed its checked model. Both alternatives are excluded.

## Tradeoffs

Modal substitution and hypothesis interpretation need more care than propositional rewriting. Keeping their side conditions visible lets PR 05's rule proofs reuse real semantic lemmas instead of hiding assumptions inside a checker.

## Migration

This PR adds no program execution or core support rule. PR 04 consumes the frozen assertion semantics; later PRs reuse it without aliases or a second assertion language. Preserve all source/admission behavior and remove this plan after landing its durable results.

## Recommendations

1. Define satisfaction before proof rules or execution checking.
2. Prove substitution and the non-truth belief boundary.
3. Land before [PR 04](04-program-semantics.md).
