# ARA records as sets of research histories
**Date:** 2026-10-10

## TL;DR

An ARA record denotes the valid research histories and reporting choices that could have produced it, under explicit model and coverage assumptions. Auditing a submitted argument requires its particular justification to work in every compatible history; establishing that a claim has some justification in every history is a separate judgment. This contract is part of the approved [research-process semantics plan](README.md), not an implemented ARA importer. R0 freezes the interfaces, R1–R5 prove their semantics, and R6–R7 connect decoded ARA fixtures to the executable reference theory.

## Problem

The existing [ARA-to-Lara map](../../docs/corpus-map.md#3-the-field-level-lowering-map) lowers claims, evidence, experiments and exploration branches to support and attack structures. It does not establish event-order or omission guarantees. A branch that contributes no attack edge may still be a trial in the statistical family. Keeping only the successful claim's ancestors would lose that information.

A record must distinguish an observed absence from an unrecorded event. A plan commitment followed by an evaluation does not rule out earlier access to the evaluation data. Likewise, a complete test ledger says nothing about whether data-access events were recorded completely.

## Constraints

Keep the core, BHL, wire and existing corpus unchanged. The implementation in this workstream covers a symbolic decoded-record contract, finite Lean fixtures, proofs and a reference runner. It does not parse arbitrary ARA prose or implement physical event capture. No theorem establishes the honesty of an external log, the faithfulness of a natural-language interpretation, or the adequacy of the model for the real world.

Use closed event and evidence-kind types and distinct identifiers for events, actors, plans, runs, claims, sources, datasets and versions. File paths and source spans identify decode-boundary evidence, not semantic identifiers. Existing ARA provenance labels must not be silently treated as the proposed evidence-kind lattice; any translation needs an explicit admission rule.

## Proposed approach

### What makes a research history valid?

A process model `M` supplies initial states and a labeled transition relation `Step M s e s'`. A history is a finite execution of that relation through a declared submission cutoff. Extend or annotate the existing BHL trace rather than replacing its execution semantics. R3 proves that the test-event projection agrees with the existing multiset `History` for the represented execution.

The state records committed plan versions, data accesses, runs and their inputs, results, claim justifications and source revisions. The event constructors distinguish plan commitment, data access, analysis execution, result production, claim assertion and source retraction. A result refers to an existing run, and the run identifies the plan and input versions actually used. These are modeled preconditions, not evidence that an external logger observed every physical action.

An ARA branch edge is not automatically a temporal edge. Explicit temporal constraints form a partial order; compatible histories include every valid ordering that satisfies it. File order, display order and timestamps without a justified ordering interpretation do not establish precedence. Include relevant failed and sibling branches even if their argumentation lowering is `no edge`.

### What does a record mean?

Fix a process model `M`, coverage/reporting assumptions `A`, a decoded record `r` and a cutoff. Write `x = (h, rho)` for a history and reporting choice. Define:

```text
Compatible M A r (h, rho) :=
  Valid M h ∧ Allowed M A h rho ∧ Report M h rho = r

Completions M A r := { x | Compatible M A r x }
```

`Report` preserves selected values and identities while allowing omissions or field projections specified by `rho`. `Allowed` restricts those choices and the underlying history. If a record format abstracts values rather than preserving them exactly, that abstraction belongs explicitly in `Report`; equality is at the decoded-record boundary.

Coverage assumptions carry a scope: event kinds, test-family membership, relevant actors/data and a cutoff. `complete` means the full relevant observation is present, `countBounded K` limits tests in the declared family, `declaredPolicy` constrains the reporting choice, and `openWorld` adds no completeness assumption. These are compatibility predicates, not a universal strongest-to-weakest enum ordering. Compare assumptions by inclusion of their compatible sets on the same model and scope.

Every coverage assertion carries its evidence reference and admission basis. A profile may accept an attestation as an assumption, but the verdict must retain that dependency. An assertion labeled `complete` does not prove its own reliability. Missing coverage evidence must not be replaced by a closed-world default.

Mathematical compatibility can range over arbitrary histories. The executable instance in this plan uses a declared finite model with decidable compatibility and query predicates. Its horizon, carriers and family bounds remain explicit parameters of the verdict. A smaller enumeration is not a stronger research record: do not silently discard histories merely to make evaluation terminate.

### Which verdict does the record support?

For `C = Completions M A r` and a property `phi`:

| Verdict | Condition |
| --- | --- |
| `inconsistent` | `C` is empty |
| `certainTrue` | `C` is nonempty and every completion satisfies `phi` |
| `certainFalse` | `C` is nonempty and every completion violates `phi` |
| `unknown` | Two compatible completions disagree on `phi` |

Refinement preserves certainty only when the refined compatible set remains nonempty. A finer observation has the same requirement, discharged for an actual observation by its generating history. Determinacy means `certainTrue` or `certainFalse`, so its no-disagreement characterization also requires nonemptiness.

A complete test ledger need not determine data-access order or every warrant input. Conservativity against `ArtifactWarrant` therefore requires a realizable complete observation that determines the queried warrant, not just a coverage constructor named `complete`. Profile checks must be absent or separately satisfied for that agreement theorem.

### Which justification is being audited?

Let `Warranted M P h c w` mean that witness `w` warrants claim `c` in complete history `h` under profile `P`. Keep two judgments:

```text
Entitled M P A r c :=
  Completions M A r ≠ ∅ ∧
  ∀ (h, rho) ∈ Completions M A r, ∃ w, Warranted M P h c w

ArgumentEntitled M P A r c w :=
  Completions M A r ≠ ∅ ∧
  ∀ (h, rho) ∈ Completions M A r, Warranted M P h c w
```

The ARA submitted-argument audit uses `ArgumentEntitled` with the recorded witness and its exact source/run/version bindings. `ArgumentEntitled` implies `Entitled`; the converse fails when different histories need different witnesses. R2 supplies that separating example. Do not claim to have checked the submitted argument merely because some argument exists in each completion.

Warrant includes methodological and probabilistic premises as well as process facts. Disjoint dataset identities do not imply statistical independence. R4 states the product-distribution or appropriate conditional-independence assumption, test calibration and selection measurability explicitly. R3's structural split predicate proves only read separation. Similarly, event order does not establish predictable statistical validity without a complete account of relevant information access and the corresponding model assumptions.

### What crosses the ARA boundary?

The contract augments the existing argumentation map; it does not replace it or require that current ARAs already contain every field.

| Source material | Decoded process information | Missing-information behavior |
| --- | --- | --- |
| Claims and their proof references | Claim identity, exact submitted witness, source and version dependencies | Leave the affected witness unaudited; no substitute argument is silently chosen |
| Experiment setup, run references and evidence | Run identity, plan/input versions, result and statistical family | Leave missing fields unknown; do not infer family size from reported successes |
| Exploration branches, including failed trials | Candidate events and dependencies throughout the declared scope | Preserve relevant trials even when they lower to no attack edge |
| Explicit access/commit records and ordering evidence | Data reads, plan commitments and temporal constraints | Admit all valid orderings not ruled out by evidence |
| Coverage attestations and reporting declarations | Scoped coverage assumptions with evidence and admission basis | No claim of completeness from absence of entries |
| Corrections, withdrawals and dataset updates | Versioned changes and affected dependencies | Distinguish a new dataset version from a defect in an old version |

Every extracted fact retains an ARA file/entry reference and available source span at the boundary. Verdict examples report the model, scope, coverage assumptions, profile, claim and submitted witness alongside the verdict. An `unknown` example exposes two incompatible answers from compatible histories; an `inconsistent` example reports no compatible history without pretending to find a minimal inconsistent subset.

The primary bridge obligation is `extraction_preserves_compatibility`: if a modeled history and reporting choice satisfy the source-record relation and admitted assumptions, decoding that source must keep the pair compatible. Together with `verdict_sound`, this gives warrant for the modeled generating history whenever the decoded record certifies the submitted argument. It is conditional on source fidelity and admitted assumptions, not a proof about physical history.

R6 also proves `extraction_overapprox_safe`: if a conservative extraction admits a superset of the source-compatible completions, its positive verdict transfers to the nonempty source-compatible set. Extra possibilities can lose certainty; excluding a relevant possibility can create false certainty. A round trip proves representation consistency only and cannot replace these preservation obligations. No round trip reconstructs a unique full history from an incomplete record.

### Which examples must demonstrate the contract?

| Fixture | Required result | Owner |
| --- | --- | --- |
| Same recorded plan/evaluation, with or without an omitted earlier read | Precommitment `unknown`; justified complete access evidence excludes the violating history | R3, R6 |
| Same submitted result, one-test and two-test existing BHL histories | Original method conclusion stays `unknown`, even under a count bound of two | R1, R4 |
| New calibrated e-value fixture, score 60, count bound two, alpha 1/20 | Pass the bound-adjusted threshold 40 with a nonempty compatible set; allowing four tests introduces threshold 80 and a failing completion | R4 |
| Claim supported by a different witness in each history | `Entitled` holds but no single submitted witness is `ArgumentEntitled` | R2 |
| Distinct dataset identities with dependent samples | Structural read separation does not supply the statistical independence premise | R4 |
| Failed sibling trial contributes no attack | Trial still affects family membership/count | R3, R6 |
| Contradictory admitted temporal constraints | `inconsistent`, never a positive entitlement | R1, R6 |
| Later retraction or dataset version change | Recompute affected warrants; retain old-version claims only where the update permits | R5 |

The e-value fixture is a new finite calibrated model, not a reinterpretation of the existing p-value witness. Prove its null expectation bound and positive outcome mass before using the reported score. The count bound alone does not make either a weak score or the original BHL conclusion pass.

## Alternatives considered

| Approach | Decision |
| --- | --- |
| Treat the displayed successful path as the execution | Reject: omits relevant sibling trials and earlier reads |
| Treat every missing field as a false event predicate | Reject as reference semantics: missing information permits both possibilities; a conservative evaluator may refuse certification but must agree with the four-verdict contract |
| Require all physical history to be recorded | Reject: completeness must be scoped and its admission basis explicit |
| Infer a probabilistic distribution over hidden histories | Outside this contract: compatible-history certainty needs no prior over reporting choices; statistical calibration still needs a probability model |

## Tradeoffs

Exact enumeration is suitable for finite reference examples, not arbitrary real research logs. Conservative extraction may return `unknown` often. That is preferable to certifying a claim by inventing coverage or order. Statistical family membership and provenance interpretation remain explicit trust boundaries even when the downstream Lean proofs are complete.

## Migration

R0 freezes this contract alongside the main plan. R3 implements the symbolic process view, R6 implements the decoded-record bridge and fixtures, and R7 exposes their verdicts in `process-examples`. Update `docs/corpus-map.md` and `docs/theory-process.md` as those contracts land; describe only implemented behavior there. Move durable content from this file into those subject documents and delete this file when its work is complete. Production capture, arbitrary-prose extraction and runtime importer delivery remain outside this theory workstream, as recorded in issue #23's residual boundary.

## Recommendations

1. Freeze scope, identity, reporting and witness quantifiers in R0 before proving preservation laws.
2. Prove non-vacuity and compatibility preservation before using decoded ARA records to certify arguments.
3. Run all fixtures through the same verdict implementation in R7, retaining their assumptions and source references in the output.
