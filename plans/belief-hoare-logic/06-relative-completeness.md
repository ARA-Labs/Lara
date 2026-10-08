# PR 06: Relative completeness
**Date:** 2026-10-07

## TL;DR

Prove relative completeness for the already sound BHL derivation system. State the exact assertion-logic, expressiveness and model premises needed by the paper's proof. Include loop-invariant obligations and a nontrivial reconstructed derivation; do not turn completeness into a claim of automatic proof search.

Plan status: approved by the researcher on 2026-10-07. Implementation status: pending. Original scope: B4, completeness. Dependency: PR 05. Proposed PR title: `theory(bhl): prove relative completeness`. Read the [shared contract and sequence](README.md) before execution. [Issue #24](https://github.com/ARA-Labs/Lara/issues/24) tracks this work; no definition or theorem below is claimed to exist yet.

## Problem

Soundness says derivations are valid. Relative completeness is a different direction: under explicit premises, semantic validity has a derivation in the fixed proof system. Combining the two in one large review can hide an expressiveness assumption or a tautological encoding.

## Constraints

Do not change semantic validity or add a derivation rule saying that any semantically valid triple is derivable. Reuse PR 05's rules and PR 01's completeness contract. Quantification over terminating runs remains partial correctness. Assertion-logic completeness assumptions must be visible and independent of the final BHL conclusion.

PR 06 is mandatory, but it is an independent branch after PR 05. PR 07 also depends on PR 05; neither PR 07 nor PR 08 nor PR 09 requires relative completeness. Approval fixes this obligation and dependency graph, not the paper/numeric decisions still due in PR 01 or the truth of an unproved theorem.

## Proposed approach

### Which proof files land?

| File | Deliverable |
| --- | --- |
| `lean/Lara/BHL/Completeness.lean` | Paper-mapped expressiveness/invariant lemmas and relative-completeness theorem |
| `lean/Lara/BHL/Assertion.lean`, `Substitution.lean`, `Derivation.lean` only if required | Narrow supporting results, without changing the reviewed logic to force completeness |
| `lean/Lara/Examples/BHLCompleteness.lean` | Nontrivial proof reconstruction and loop/parallel coverage witnesses |
| `docs/theory-bhl.md`, `lean/Lara.lean`, `lean/AxCheck.lean` | Complete source-to-proof map, explicit premises and standard-axiom audit |

Follow the reviewed Appendix B argument. Specify any assertion expressiveness, expressible loop invariant or underlying implication-provability premise as a separately named mathematical condition. Prove every supporting result available from the frozen definitions in this PR. Do not assume BHL relative completeness itself under a different name.

Use PR 01's checked-proof reuse decision or reconstruct the published expressiveness and derivation arguments in Lean. Show how the audited weakest-precondition or invariant representation supports the proof for each program constructor. Every imported result must be a checked dependency with any required representation correspondence; citing the paper does not fill a proof hole. This is inherited metatheory, not a new Lara completeness result.

Soundness is the result consumed when applying a checked derivation. Relative completeness instead addresses whether semantic validity has a derivation under the assertion-theory premises. It proves neither automatic proof search nor that the assertion language captures every scientifically relevant distinction. These roles explain the independent dependency branch without weakening this PR's acceptance obligation.

### Which results must reviewers see?

```text
validTriple model pre program post
  + the paper's explicit assertion-theory/expressiveness premises
  => Derivation assumptions pre program post
```

This is a proposed theorem shape, not a claimed Lean signature. The completeness proof must account for all program constructors and the declared restrictions, including loops and noninterfering parallel programs. Where the published theorem is relative to a model or assertion theory, preserve that qualification exactly.

### How is completeness verified?

- Mechanize the reviewed theorem and its supporting expressiveness/invariant obligations.
- Demonstrate a meaningful derived triple, including a loop with a realizable invariant; separate useful termination witnesses from the partial-correctness theorem.
- Supply the applicable parallel/composite coverage from the reviewed proof inventory.
- Execute the concrete program witnesses and compare their reference pre/post observations. Use a throwaway main before PR 08 registers the runner, then remove it; otherwise extend the registered `bhl-examples` runner. Proof elaboration establishes completeness, not this finite run alone.
- Run `make local-gates`, audit every theorem and document what relative completeness leaves to the underlying assertion logic.

If an unexpected gap requires changing the frozen logic or numeric dependency, stop that cutover, record the problem in issue #24, and obtain an explicit scope decision. A finite truth-table check is not a substitute for the required theorem.

### When does this PR own the final join?

Original B8 is a required join of PR 06 and PR 09. If PR 09 has already landed, base or rebase PR 06 on that merged main. Complete integrated acceptance on the candidate tree before review. Use PR 08's registered `bhl-examples` runner, extended by PR 09, rather than creating another runner. Carry the completeness witnesses into that runner and retain the earlier history, statistical, loop, parallel, fuel, non-truth and source-bridge scenarios, including dependency quarantine, snapshot rebinding and the incomplete-record limitation.

Run `(cd lean && lake exe bhl-examples)`, `make local-gates` with the shared macOS GNU-tool PATH, and `make ara-source-spans ara-session-index ara-observations`. Record the full B0-B8 theorem/assumption inventory, all axiom-audit results and the integrated outcomes in `docs/theory-bhl.md`. Distinguish inherited BHL results, finite-instance/checker results and Lara-specific composition; complete the novelty/assumption comparison before making novelty claims. Preserve the wider issue #23 theory gate and its external interpretation, sampling and history-capture limits. Follow [PR 09's B8 acceptance contract](09-lara-bridge-and-acceptance.md#what-finishes-original-b8-acceptance) in full. There is no separate acceptance PR.

If PR 09 remains pending, record relative completeness as complete only after its own proofs and gates pass, leave B8 open, and hand the final join to PR 09. The last-landing PR supplies the integrated record before review; record whole-workstream completion only after both PRs merge. A pending completeness branch prevents PR 09 from calling the whole workstream complete.


### What concrete representation design should the server preserve?

This construction remains unimplemented; it is not an expressiveness proof. Compile each finite program into a finite control graph with explicit guard/epsilon/primitive edges and finite products for parallel control locations. Prove both simulations against independent execution. Administrative transitions do not append world states; primitive skip/assignment/test transitions append their actual actions.

Use a trace ghost of type `List (Nat × World)` plus a terminal world ghost. Expand a finite disjunction of local graph-edge equations, and an outer natural-index binder validating every adjacent log entry. Check entry/exit locations and complete start/end semantic views. Do not require the ghost worlds themselves to extend one another: the decoding proof must replay from the literal starting world, construct the actual prefix-extending run and prove terminal view equality.

The proposed finite representative is `∀ trace, ∀ terminalWorld, validLocalLog → Q at terminalWorld`. It must be constructed from legal AST nodes, not an opaque run/WLP predicate. Prove representation by actual-run encoding and local-log decoding, with modal satisfaction transferred through the proved view correspondence. Run length changes the ghost list value, not formula size or binder count. No quantifier goes underneath `K`.

Build canonical derivations by structural induction generalized over the postcondition. Sequence uses the child's representative as intermediate assertion; loops use the loop representative as the realizable invariant; parallel uses child derivations plus the independent sequential/parallel universal-outcome theorem. Only the named assertion-implication oracle remains relative. None of these design notes discharges a Lean obligation.

## Alternatives considered

A finite model checker may decide examples but does not prove the general relative-completeness theorem. A semantic-validity constructor or an assumption equal to the theorem makes the result circular. The plan rejects both.

## Tradeoffs

This PR requires substantial proof work with little executable behavior. Its smoke runs check the meaning of the examples, while the audited Lean proof establishes completeness. State those two roles separately.

## Migration

The theorem record must distinguish soundness from relative completeness and identify any pending finite-instance, checking or bridge work without treating them as completeness prerequisites. If PR 09 is already complete, perform the B8 join above before closing issue #24 or removing the sequence index. Otherwise retain the pending plans and index. Remove this executed plan only after its durable proof evidence and any final-join record have been retained.

## Recommendations

1. Recheck the Appendix B assumptions against the frozen interfaces.
2. Prove completeness for the existing derivation system without widening its rules.
3. Complete this mandatory branch independently of [PR 07](07-finite-statistical-instance.md); perform B8 if this is the last of PR 06 and PR 09.
