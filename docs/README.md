# Documentation

Lara's design documents are organized by subject. Start with the [project README](../README.md) for the language and CLI, then choose the semantic layer below. The [language specification](spec.md) and [surface grammar](lara-surface-grammar.md) define the concrete contracts; the subject documents explain their design, theorem assumptions and limits.

## Which logic answers which question?

| Subject | Canonical design and theory | What it establishes |
| --- | --- | --- |
| Base language | [Claim support and argumentation](theory-core.md) | Whether declared support terms type-check, how complete arguments compile into an attack graph, and how grounded claim status behaves under observations, updates and contexts |
| Possible worlds | [Checking contexts and transport](theory-pw.md) | When explicitly declared bridges transport support or preserve status between checking contexts; includes sorted queries, wire format and runtime limits |
| Statistical methods | [Belief Hoare Logic](theory-bhl.md) | Conditional validity of statistical methods, modeled application and evidence-dependent artifact warrants under explicit assumptions |
| Research processes | [Entitlement over incomplete histories](theory-process.md) | When a partial research record entitles a claim: compatible-history verdicts, profiles, ordered process histories, statistical validity under count bounds, revision and the ARA decoded-record bridge |
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
| [Natural language and the trusted boundary](spec.md#natural-language-and-the-trusted-boundary) | Which prose is presentation and which declarations the checker interprets |
| [BHL theorem inventory](bhl-theorem-inventory.jsonl) | Exact kernel types, basis citations and axiom-audit locations |

## Where are examples and evidence?

The [worked-example catalogue](../examples/README.md) lists executable artifacts. The prose walkthroughs cover [rebuttal replay](demos/d1-rebuttal-replay.md), [mechanical review](demos/d2-mechanical-reviewer.md), [cross-paper agreement](demos/d3-agreement-map.md), [philosophical argument](demos/d4-philmath.md), [axiom withdrawal](demos/d5-axiom-withdrawal.md), and [statistical-method support and its limits](demos/d6-bhl-method-support.md).

| Reference | Contents |
| --- | --- |
| [Corpus lowering map](corpus-map.md) | How research-artifact content becomes Lara declarations |
| [Evaluation](evaluation.md) | Performance, mutation and localization contracts and frozen inputs |
| [Measured-input freeze](../measurements/frozen/evidence-measured-inputs-v2.md) | Certified-evidence evaluation inputs |

## How is the implementation maintained?

[Implementation and verification](implementation.md) owns the architecture, mechanization discipline and CI/local-gate boundary. [Contributing](../CONTRIBUTING.md) covers setup, work tracking and research-record maintenance. [Releasing](releasing.md) covers release binaries and packaging. The [Lean catalogue](../lean/README.md) maps the proof development to its modules.

Per-module API documentation is generated from source comments with `make docs`: Haddock for Haskell and doc-gen4 for Lean. `make doctest` runs the `>>>` examples in Haddock comments. Generated API output is not committed here.

## What prior work does Lara build on?

Read [foundations](foundations.md) for the main sources and [novelty and related work](novelty-and-related-work.md) for the claimed differences. The [bibliography](lara-related-work.bib) holds the full references.

## How should these documents change?

These documents describe the current design. When a design or theorem contract changes, update its subject document in place, keeping assumptions, counterexamples, trust boundaries and source mappings together. [Contributing](../CONTRIBUTING.md#how-work-is-tracked) says where decision history, open work and plans live instead.

Frozen measurement records, `ara/` research traces and serialized corpus, example and fixture bytes are never rewritten when these documents change. Document paths cited inside them refer to the revision at which they were recorded.
