# Documentation

Lara's design documents are organized by subject. Start with the [project README](../README.md) for the language and CLI, then choose the semantic layer below. The [language specification](spec.md) and [surface grammar](lara-surface-grammar.md) define the concrete contracts; the subject documents explain their design, theorem assumptions and limits.

## Which logic answers which question?

| Subject | Canonical design and theory | What it establishes |
| --- | --- | --- |
| Base language | [Claim support and argumentation](theory-core.md) | Whether declared support terms type-check, how complete arguments compile into an attack graph, and how grounded claim status behaves under observations, updates and contexts |
| Possible worlds | [Checking contexts and transport](theory-pw.md) | When explicitly declared bridges transport support or preserve status between checking contexts; includes sorted queries, wire format and runtime limits |
| Statistical methods | [Belief Hoare Logic](theory-bhl.md) | Conditional validity of statistical methods, modeled application and evidence-dependent artifact warrants under explicit assumptions |
| Strict certificates | [Backend interface and adapters](strict-certificates.md) | What an accepted strict step certifies relative to its premises, backend replacement, and the limits of numerical and inspection adapters |
| Evidence admission | [Evidence and source admission](evidence-admission-design.md) | Which leaves reach the source checker, how certified inputs bind to evidence files, and what remains outside the parser, cryptographic and operating-system models |
| Artifact composition | [Maps of independently checked artifacts](artifact-composition.md) | How manifests qualify and link members, generate cross-member attacks and report composite verdicts |

These layers do not establish empirical truth. A grounded support status, an accepted evidence binding and a valid statistical-method judgment have different premises and conclusions. Possible-world bridges are not automatically BHL epistemic relations. The subject documents retain those boundaries rather than presenting the layers as interchangeable logics.

## Where are the language contracts?

| Reference | Contents |
| --- | --- |
| [Language specification](spec.md) | Frozen v0.1 language, current `lara-core@0.3`, typing, compilation, verdicts and rejection classes |
| [Surface grammar](lara-surface-grammar.md) | Concrete `.lara` syntax and versioned appendices |
| [Rejection reference](rejection-surface.md) | Refused inputs, located diagnostics and runnable examples |
| [Natural-language boundary](naturalness-boundary.md) | Which prose is presentation and which declarations the checker interprets |
| [BHL theorem inventory](bhl-theorem-inventory.jsonl) | Exact kernel types, basis citations and axiom-audit locations |

## Where are examples and evidence?

The [worked-example catalogue](../examples/README.md) lists executable artifacts. The prose walkthroughs cover [rebuttal replay](demos/d1-rebuttal-replay.md), [mechanical review](demos/d2-mechanical-reviewer.md), [cross-paper agreement](demos/d3-agreement-map.md), [philosophical argument](demos/d4-philmath.md), [axiom withdrawal](demos/d5-axiom-withdrawal.md), and [statistical-method support and its limits](demos/d6-bhl-method-support.md).

| Reference | Contents |
| --- | --- |
| [Corpus lowering map](corpus-map.md) | How research-artifact content becomes Lara declarations |
| [Evidence inventory](evidence-admission-inventory.md) | Original-output inventory and evidence admission coverage |
| [Evidence review instructions](certified-evidence-review-instructions.md) | Independent review procedure and acceptance rules |
| [Evidence review record](certified-evidence-human-review-worklist.md) | Accepted independent review and published reviewed bindings |
| [Evaluation](evaluation.md) | Performance, mutation and localization contracts, frozen inputs and historical measurement records |
| [Measured-input freeze](../measurements/frozen/evidence-measured-inputs-v2.md) | Separate certified-evidence evaluation inputs |

## How is the implementation maintained?

[Implementation and verification](implementation.md) owns the architecture, mechanization discipline and CI/local-gate boundary. [Contributing](../CONTRIBUTING.md) covers setup, work tracking and research-record maintenance. [Releasing](releasing.md) covers release binaries and packaging. The [Lean catalogue](../lean/README.md) maps the proof development to its modules.

Per-module API documentation is generated from source comments with `make docs`: Haddock for Haskell and doc-gen4 for Lean. `make doctest` runs the `>>>` examples in Haddock comments. Generated API output is not committed here.

## What prior work does Lara build on?

Read [foundations](foundations.md) for the main sources, [novelty and related work](novelty-and-related-work.md) for the claimed differences, and [prior-art lessons](prior-art-lessons.md) for implementation lessons. The [argumentation-scheme reading note](references/yu-zenker-2020-schemes-cqs-completeness.md) and [bibliography](lara-related-work.bib) retain detailed references.

## How should these documents change?

Update the relevant subject document when a design or theorem contract changes. Keep its assumptions, counterexamples, trust boundaries and source mappings together. Do not create implementation-stage documents, completed plans or standalone decision records. Open work belongs in [GitHub issues](https://github.com/ARA-Labs/Lara/issues); unlanded implementation plans belong in `plans/` and are removed when executed.

Historical verification snapshots are evidence from their recorded revision, not fresh test results. The repository's `main` starts at the v0.1.0 release; older development commits and freeze tags may not resolve in this history. [Evaluation](evaluation.md) retains the frozen content and recorded hashes. Historical research traces in `ara/` and serialized corpus, example and fixture bytes remain unchanged when active documentation is reorganized. Old document paths inside those preserved artifacts refer to their recorded revision; current documentation and source-code comments use the subject references above.
