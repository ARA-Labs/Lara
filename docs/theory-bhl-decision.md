# BHL and research-artifact semantics
**Date:** 2026-10-07

## TL;DR

Lara is a lower-level language for expressing the semantics of Agent-Native Research Artifacts (ARA). Belief Hoare Logic (BHL) is approved as its statistical-method component, alongside argumentation and context semantics. The implementation must distinguish conditional procedure validity, application in a mathematical model, and defeasible artifact warrant under residual assumptions. The Lara-specific targets concern dependency-sensitive warrant and revision; the existing BHL metatheory remains attributed to its source.

Decision status: approved by the researcher on 2026-10-07. Implementation status: pending. This record settles the architectural role and acceptance boundaries. The exact mathematical definitions, paper audit and numeric-library decision remain work for PR 01; no new BHL theorem or runtime capability is established here.

## Problem

A research artifact can report a result and give an argument for a claim without specifying whether the procedure warrants that inference. BHL expresses this missing methodological meaning through preconditions, programs, epistemic postconditions and test histories. The reference is Kawamoto, Sato and Suenaga, [Sound and Relatively Complete Belief Hoare Logic for Statistical Hypothesis Testing Programs](https://arxiv.org/html/2208.07074v3). Its history sensitivity, statistical-belief semantics, soundness and relative completeness are prior results.

Lara's purpose is broader than checking statistical programs. It must connect method judgments to claims, interpretations, evidence and source revisions. A bridge that only packages a BHL certificate beside an accepted argument does not establish how those meanings interact. [Issue #24](https://github.com/ARA-Labs/Lara/issues/24) owns the approved implementation and bounded composition results; [issue #23](https://github.com/ARA-Labs/Lara/issues/23) owns the wider research-process theory.

## Constraints

Preserve the existing core, admission, quarantine, evidence and public-status semantics. Neither statistical belief nor Lara support implies empirical truth. Support for an assumption also cannot establish that assumption or knowledge of it in BHL. Keep residual assumptions visible in the artifact even when evidence supports their applicability.

BHL's observation-equivalence relation differs from Lara's accepted-context bridge relation. The former supports its epistemic laws; the latter generally lacks the stronger frame laws, as recorded in [the PW0 theory](theory-pw0-outer-model.md). No modality coercion is approved. A future translation must state and prove the required conditions.

This decision introduces no `.lara` syntax, core/wire migration, corpus regeneration, mutation-base rewrite or freeze-tag bump. It does not add physical history capture, a receipt service or an empirical protocol. Any later need for those changes requires separate approval and explicit costs. Every definition frozen during implementation must land with its available metatheory and axiom audit.

## Proposed approach

### What does the artifact assertion bind?

PR 01 must specify the abstract artifact fragment and its reference interpretation before later semantic interfaces freeze. The binding includes the accepted source snapshot, claim and hypothesis interpretation, model, precondition/program/postcondition, execution, applicability evidence dependencies, residual assumptions and declared history coverage. The reference meaning must be independent of the executable bridge. No parser is needed to specify this fragment.

| Judgment | Required evidence | Conclusion boundary |
| --- | --- | --- |
| Conditional method validity | A checked derivation with valid underlying premises and model side conditions | Every terminating modeled run from a precondition-satisfying world has the stated postcondition |
| Modeled application | Conditional validity, actual initial-world precondition satisfaction and the bound execution | The modeled final world satisfies the postcondition |
| Artifact warrant under residual assumptions | Exact bindings, conditional method evidence, justified unblocked claim support and the required applicability evidence | The artifact has that conditional warrant; residual assumptions are not proved true |

A claim identifier does not prove interpretation fidelity. A modeled execution does not prove that physical sampling occurred as modeled. BHL's complete modeled history does not prove completeness of a submitted log. Each remains an explicit external obligation where the application needs it.

### What must composition prove?

The bridge must use actual accepted source/evidence runs. It must preserve ordinary observations when method metadata is forgotten and characterize warrant under source changes. Its result must not be a theorem obtained solely by projecting fields from a conjunction of two successful checks.

| Required case | Acceptance distinction |
| --- | --- |
| Quarantine of selected applicability evidence | An accepted source loses that dependent warrant while the conditional BHL theorem remains valid |
| Safe source update | An explicitly rebound warrant survives under binding, admission, support and attack preservation hypotheses |
| Stale or incompatible certificate | A copied certificate cannot attest a different source snapshot, hypothesis interpretation, model or dependency binding |
| Supported applicability with a false assumption | Lara support cannot discharge a mathematical precondition or BHL knowledge premise |
| Partial submitted record | A nonempty pair of compatible histories can disagree on the proposed method conclusion; omitted tests cannot certify completeness |

The quarantine theorem concerns a selected dependency witness. Independent alternative support can preserve another warrant for the same claim. Source acceptance, claim status, mathematical theorem validity and applicability warrant must remain distinguishable in the examples.

### Which results belong to this workstream?

The theorem inventory must distinguish inherited BHL metatheory, concrete-instance and executable correspondence results, and Lara-specific composition results. The last category is a candidate contribution until the statements are proved and compared with prior art. No claim that BHL cannot encode arguments or revision is approved.

Issue #24 owns the complete-history BHL baseline, the artifact binding contract, bounded evidence-sensitive revalidation and the partial-record separating witness. Issue #23 retains the general compatible-history calculus, broader claim/model revision, representation adequacy and inquiry/impact composition. Completing BHL does not release empirical experiment design before that wider theory acceptance.

### How are the proofs mechanized?

The researcher approved reusing the BHL paper's mathematics while requiring checked proof dependencies for Lara. PR 01 must audit available mechanizations and record their coverage, hypotheses, toolchain and axiom dependencies. Reuse compatible checked declarations with any necessary representation correspondence; otherwise reconstruct the published arguments in Lean. A citation or a proof checked in another system cannot by itself discharge a Lean obligation. No axiom asserting published soundness or completeness is permitted.

Keep reference BHL metatheory, concrete-instance and checker correspondence, and Lara-specific composition as separate proof layers. Construct local soundness by induction on derivations over independent satisfaction and execution, then compose it with checker correspondence and genuine application premises. Prove revision results from actual source/evidence semantics and negative boundaries with inhabited countermodels. Record each theorem's source or motivation, assumptions, checked dependencies, axiom audit and witness. Tests check executable examples; they do not replace proofs or establish interpretation fidelity.


### How do the implementation dependencies change?

The [living plans](../plans/belief-hoare-logic/README.md) retain their PR identifiers. After soundness in PR 05, relative completeness in PR 06 is independent of the concrete PR 07-09 branch. The latter needs soundness, not relative completeness. Both branches remain mandatory.

Final acceptance B8 belongs to the last-ready PR among PR 06 and PR 09. It must include the other's merged work, reconcile the full theorem inventory and run integrated gates on its candidate tree before review. Workstream completion is recorded only after both merge. This removes an unnecessary dependency without dropping a theorem or creating a separate acceptance-only PR.

## Alternatives considered

| Alternative | Decision |
| --- | --- |
| Make BHL the semantics of all research | Rejected: claim interpretation, defeasible argumentation and incomplete records require additional semantics |
| Keep BHL only as a literature comparison | Rejected: Lara needs a faithful, checked statistical-method component |
| Implement the standalone logic before deciding artifact meaning | Rejected: the binding and assumption contracts constrain the implementation |
| Treat supported assumptions as true preconditions | Rejected: defeasible support cannot discharge mathematical satisfaction |
| Drop relative completeness to reach the bridge sooner | Rejected: retain completeness on an independent required branch |

## Tradeoffs

Early artifact contracts add design work before the paper formalization. They expose errors that would otherwise appear only when connecting the checker to actual source and evidence semantics. The bounded revision and record witnesses add Lean proof and execution work without claiming to complete the wider process calculus.

Keeping physical sampling, interpretation and record completeness as external obligations limits what checking can establish. It also prevents a successful checker result from being reported as empirical truth. The exact real-number and probability-library cost remains unresolved until PR 01 completes its audit.

## Migration

The revised plans are approved; their implementation is pending. No existing runtime or frozen contract changes in this planning revision. PR 01 extends this decision with the audited mathematical and numeric contract, and implementation PRs add only proved results to `docs/theory-bhl.md` as they land. Executed living plans are removed after their durable decisions and theorem evidence have moved into documentation.

## Recommendations

1. Execute PR 01 with the artifact judgment and cross-layer examples included in its contract review.
2. Prove the bounded revalidation and separation results alongside the faithful BHL baseline.
3. Complete both dependency branches and the B8 joined-tree gates before closing issue #24.
