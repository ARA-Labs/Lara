# PR 01: Reference audit and artifact semantic contract
**Date:** 2026-10-07

## TL;DR

Specify how BHL judgments express methodological meaning in a Lara research artifact, then audit the published BHL definitions and proofs. Fix the assumption boundary, cross-layer examples and numeric dependency decision before later semantics freeze. Include the immediate results for any definitions frozen here; approval of this plan is not completion of that audit.

Plan status: approved by the researcher on 2026-10-07. Implementation status: partial, retained for server continuation. The assessment, approved corrected contract, pinned Mathlib carrier, initial vocabulary and source countermodels are implemented; their focused checks and axiom audit passed. Full `make local-gates` remains incomplete after local platform/resource failures and an interrupted larger-memory Linux run. Do not mark PR 01 complete or remove this plan until its full acceptance gate passes. Original scope: B0, extended with the artifact contract and cross-layer witness specifications. Dependency: None. Proposed PR title: `theory(bhl): freeze the reference and artifact contract`. Read the [shared contract and dependency graph](README.md), [architectural decision](../../docs/theory-bhl-decision.md), and [verification/handoff record](../../docs/theory-bhl.md#what-was-verified-before-the-server-handoff). [Issue #24](https://github.com/ARA-Labs/Lara/issues/24) tracks the remaining work.

## Problem

Lara is a lower-level semantic language for research artifacts. A faithful statistical-program library contributes to that goal only when the artifact can state which claim, interpretation, procedure, execution and assumptions it describes. Later soundness and completeness also depend on the exact assertion language, model restrictions and execution semantics. This PR resolves both contracts before proof engineering fixes the interfaces.

## Constraints

Inherit every constraint in the shared index. This PR may establish the minimal symbolic types needed for a reviewed contract, with their immediate proofs; it must not land the later semantics as unproved declarations. The existing no-Mathlib baseline remains until this PR makes an explicit reviewed dependency decision. Any new library must preserve the allowed axiom set and document its build/toolchain cost.

## Proposed approach

### What artifact meaning must be specified first?

Define the abstract artifact fragment and its reference meaning independently of an executable bridge. Bind the exact accepted source snapshot and claim to a hypothesis interpretation, model, precondition `P`, program `C`, postcondition `Q`, execution witness, applicability evidence, residual assumptions and declared history coverage. Distinguish a procedure-wide assertion from an assertion about one modeled execution. Surface syntax and an ARA parser are outside this workstream; the abstract representation and its interpretation are required.

Specify three judgments with separate evidence: conditional method validity, application in a mathematical model, and defeasible artifact warrant under residual assumptions. Derive a modeled postcondition only from a valid triple, genuine satisfaction of its precondition at the initial world, and the bound execution. Lara support for applicability can justify a conditional artifact warrant but cannot discharge that satisfaction premise. Require countermodels to both `Justified(P) => P` and `Justified(P) => K(P)`, as well as the separate statistical-belief-to-truth implication.

State what connects the claim's symbolic interpretation to the BHL hypothesis. Checked identifiers alone do not establish that natural-language prose faithfully expresses that hypothesis. Record interpretation fidelity, sampling fidelity and physical log completeness as external obligations wherever they are needed. Keep BHL observation-equivalence modalities separate from Lara's accepted-context bridge modalities, as documented in [PW0](../../docs/theory-pw0-outer-model.md); do not import S5 laws into arbitrary context bridges.

### Which cross-layer cases constrain the design?

Specify inhabited examples and expected outcomes now, with proofs and executable witnesses in their owning PRs.

| Case | Required distinction | Implementation owner |
| --- | --- | --- |
| Equal reported result with different test histories | A single-test postcondition can fail for unaccounted testing | PR 02, PR 07 |
| Justified applicability with a false modeled assumption | Applicability support cannot establish `P` or `K(P)` | PR 03, PR 09 |
| Quarantine of a selected applicability dependency | The source still accepts and the conditional method theorem stays valid, while that dependent warrant is unavailable | PR 09 |
| Harmless source update | Warrant can be rebound to the new snapshot under explicit interpretation, execution, admission and support/attack preservation conditions | PR 09 |
| Copied or stale certificate | An incompatible hypothesis, model, dependency or snapshot binding cannot supply current warrant | PR 09 |
| Incomplete submitted record | Two compatible histories disagree on the proposed method conclusion, preventing an inference of complete history from missing entries | PR 09 |

Define selected-warrant loss separately from loss of every warrant for a claim; alternative supporting evidence may survive. Keep the last case as a limitation witness over an explicitly defined record projection. The general compatible-history calculus, broader revision and representation-adequacy theory remain tracked in [issue #23](https://github.com/ARA-Labs/Lara/issues/23). This PR must name their required interface without freezing an unproved general extension.

### What source audit must land?

Use `Lara.BHL` for the paper-facing logic. Keep Lara-specific composition outside its base semantics. B0 produces a statement-level inventory covering the model, assertion language, programming language, proof rules, soundness, relative completeness, and the examples needed to exercise them. Record any discrepancy as a research finding; do not silently replace the published judgment with a simpler permission checker.

| Paper component | Formalization obligation | Boundary |
| --- | --- | --- |
| Sections 4.1-4.3: state, worlds and observations | Typed observable/invisible variables, memory, actions, test multisets, nonempty world histories, observation equality and the induced accessibility relation | Complete modeled test history is not proof that a submitted physical record is complete |
| Section 4.4: statistical tests | Null/alternative bindings, statistic, null distribution, tail/likeliness relation, population conditions, test combination and decomposition | Model assumptions remain visible; a test's label supplies no statistical guarantee |
| Section 5: programs | Assignment, test execution, sequential composition, conditionals, loops, and parallel composition with the paper's noninterference restrictions | Terminating-run semantics gives partial correctness, not termination or fair scheduling |
| Sections 6-7: assertions and beliefs | The epistemic assertion language, knowledge/possibility, statistical-belief definitions, history assertions, binding and capture-avoiding substitution | Statistical belief retains the alternative/exceptional-sample/model-failure meaning |
| Section 8 and Appendix B: proof theory | Explicit derivations, each rule's side conditions, soundness, and relative completeness under the actual expressiveness and assertion-logic premises | Relative completeness does not supply decidable proof search or an arithmetic oracle |
| Section 9: procedure examples | Hidden-test and multiple-comparison examples, with valid corrected procedures and semantic countermodels | Failure of one procedure is not a theorem against every adaptive method |
| Section 10: external justification | Separate formal test/model premises from evidence that they apply to a population | Logical checking does not establish sampling fidelity or natural-language interpretation |

Read the corresponding Appendix B proofs, not just the theorem summaries. For every planned Lean statement, record its source definition/rule/theorem, hypotheses, required supporting lemmas, and whether it is inherited BHL metatheory, a concrete-instance or executable correspondence result, or a Lara-specific composition result. Identify real-number, distribution, substitution, loop-invariant expressiveness and parallel noninterference requirements. Relative completeness must name its assertion-logic assumptions and any validity-premise discharge interface. It remains required in PR 06 but is not a dependency of PR 07-09.

### Can existing checked proofs be reused?

Audit the paper's associated artifacts and available mechanizations before choosing to reconstruct its proofs. Record where the search looked, candidate source URLs and revisions, license, proof assistant/toolchain, theorem coverage, exact hypotheses and transitive axiom dependencies in `docs/belief-hoare-logic-assessment.md`. Do not assume a compatible artifact exists or claim none exists beyond the documented search.

For a compatible candidate, specify how its checked declarations enter Lara's Lean proof dependency chain and which representation or semantic-preservation lemmas connect it to Lara's definitions. A result checked by another proof assistant is useful source material, but is not automatically a Lean theorem. If no candidate meets the contract, allocate the published proof arguments and supporting lemmas to PR 02-06 for Lean mechanization. This decision does not authorize an implicit library dependency or waive any theorem.

Extend the statement inventory with the source or motivation, exact assumptions, reuse-or-reconstruction choice, intended Lean declaration, supporting proof dependencies, owning PR, required witness/countermodel, executable correspondence where applicable, and axiom-audit entry. Unimplemented rows are obligations, not proof evidence. Keep reference BHL, implementation correspondence and Lara-specific metatheory separately identifiable.


### Which files own the contract?

| File | Deliverable |
| --- | --- |
| `docs/belief-hoare-logic-assessment.md` | Source inventory, proof assumptions, external statistical conditions and statement-level scope comparison |
| `docs/theory-bhl-decision.md` | Extend the approved architectural decision with the audited model, artifact judgment, syntax, proof and numeric contract |
| `lean/Lara/BHL/Types.lean`, if definitions are frozen here | Minimal symbolic vocabulary with identity/typing lemmas; PR 02 extends the same module |
| `docs/theory-bhl.md` | Initial record of the results actually proved in this PR |
| `lean/Lara.lean`, `lean/AxCheck.lean`, build registration as needed | Imports and audit coverage for every new definition/theorem |

Do not define a placeholder statistical model or admit the intended soundness conclusion as a field. If the paper requires a different numeric library, make that decision here and reconcile the affected PR plans before the next implementation starts.

### What makes PR 01 complete?

- Every paper component in the table has a precise contract and an owning later PR.
- The artifact fragment has an independent reference meaning and an exact binding contract, with conditional, modeled and defeasible judgments distinguished.
- The cross-layer cases have realizable specifications and owners; quarantine cannot be modeled only by a hardcoded acceptance flag.
- Residual assumptions, modality separation and the incomplete-record boundary are explicit. The inventory separates inherited results from candidate Lara contributions.
- The mechanization search and reuse-or-reconstruction decision are recorded, including any required checked translation. No published theorem is introduced as an axiom.
- The numeric representation and dependency decision is approved, with no rational/real equivalence claim left implicit.
- Any frozen definitions have their available identity and typing results, audited under the allowed trio.
- A nonempty typed instance exercises the frozen vocabulary; no all-empty model substitutes for it.
- Execute an actual operation over that instance with a throwaway library-based Lean main. If this remains a pure audit with no new semantic definition, document that limit instead of claiming a BHL runtime check.
- Run the shared gates that apply: `make local-gates` for any Lean/dependency change, and the three ARA gates for research records. Record exact proof and execution coverage.


## Alternatives considered

Freezing the executable checker first would let implementation choices define the reference meaning. Waiting until PR 09 to choose the artifact judgment risks building an unrelated statistics library. Importing Mathlib without checking the required statements would add an unreviewed dependency. The contract audit precedes all three choices.

## Tradeoffs

This PR resolves choices before downstream code depends on them. The paper audit may expose a limitation or proof obstacle; record the finding and obtain an explicit scope decision rather than silently removing the result.

## Migration

No core, wire, receipt or source-checking change is included. Extend the existing architectural decision rather than replacing it with a second convention. Preserve the approved dependency graph, updating proposed signatures only to reflect audited contract decisions. Remove this plan after landing the assessment, completed contract and available proofs.

## Recommendations

1. Specify the artifact judgment, residual assumptions and cross-layer cases alongside the paper audit.
2. Resolve the exact statement inventory and numeric dependency decision.
3. Prove any frozen initial definitions and hand the contract to [PR 02](02-model-and-history.md).
