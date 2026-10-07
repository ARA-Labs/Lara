# Certified-evidence admission and source composition

**Date:** 2026-10-06

## TL;DR

`lara-evidence@0.1` checks that a certified leaf is the approved checker's output over package-captured evidence. The Lean development proves this guarantee for a finite snapshot and typed selection model, then combines it with the existing source and argument checker. Successful admission preserves the ordinary retained context and located holes; it does not bypass policy quarantine or make a scientific claim true. The concrete byte parsers, SHA-256, operating-system capture and compilers remain trusted. Use [the package contract](evidence-admission-design.md#concrete-package-contract) for runtime details and the theorem map below for proof scope.

## What does successful admission prove?

A snapshot records immutable typed payloads and object metadata. A request names its dependencies, selector payload, checker and version. The pure registry constructs a proposition from those inputs without receiving the leaf's expected proposition; admission compares their normalized forms. The independent `Admitted` judgment requires valid request bindings, capture under the request-declared manifest entry, and replay of all declarations. [Admission.lean](../lean/Lara/Evidence/Admission.lean) proves that this judgment is equivalent to successful executable admission:

```text
admit snapshot policy manifest registry leaves = .ok judgments
  ↔ Admitted snapshot policy manifest registry leaves judgments
```

The scope is every declared certified leaf, including unused leaves and leaves later quarantined by ordinary policy or group handling. `all_declared_certified_witness` supplies an approved bound request, a successful runner result, equal normalized propositions and exact dependency metadata. `retained_certified_witness` carries that witness through any retained-leaf filter. `checked_partition_exact` identifies the successful judgments with precisely the certified declarations in source order; ordinary declared leaves remain possible.

## Where are the selector and runner guarantees proved?

[Extract.lean](../lean/Lara/Evidence/Extract.lean) operates on typed CSV tables, JSON trees and scalar lexemes. Its relations describe unique key-row selection, ordered column selection, pointer resolution and explicitly typed scalar decoding. Exact output construction precedes the admission normal-form comparison. These are claims about typed inputs, not a proof that a concrete UTF-8 decoder constructs the right table or tree.

| Guarantee | Theorems | Scope |
| --- | --- | --- |
| Scalar and ordered selection | `decodeScalar_iff`, `csvSelect_iff`, `jsonColumns_iff` | Executable selection agrees with the corresponding relations |
| Unique row and exact output | `csv_unique_row`, `extract_csv_exact`, `extract_json_exact` | A unique selected row or valid selected JSON scalars construct the ordered proposition |
| Root-zero JSON depth and bounds | `jsonMeasure_empty_object`, `jsonMeasure_empty_array`, `jsonMeasure_every_depth`, `jsonWithinBounds_iff`, `jsonWithinBounds_depth_boundary` | Empty containers count as one node at depth zero; depth 128 is reachable and admitted within the node bound, while depth 129 is rejected |
| Runner-owned dependencies | `run_dependencies`, `run_exact_declared_dependencies`, `run_snapshot_membership` | Reported metadata is exactly the supplied declared-object list |
| Local replay | `run_locality`, `admission_locality` | Equal lookup results on requested objects preserve successes and failures |
| Registry replacement | `run_registry_replacement`, `admission_registry_replacement` | Equal registry results on supplied objects preserve the admission result |

[Runner.lean](../lean/Lara/Evidence/Runner.lean) defines locality using equality of complete lookup results, including errors, payloads and metadata. Equal digest strings alone do not establish this premise. Admission also checks `CapturedValid`: an ID lookup must return an object whose metadata equals the requested manifest entry. The Haskell promotion boundary enforces that requirement through `Admission.captureRejection`; an object captured under another entry with the same ID is not sufficient.

## How are first errors and precedence specified?

The finite admission pass runs binding checks in leaf order, capture checks in requested-manifest order, then replay in leaf order. A capture failure names the failed object and the earliest leaf referencing it. Extraction failures are located at the leaf and carry no object in the typed differential encoding. The runtime's global package capture and ordinary source/policy rejection are earlier boundaries described in the decision record.

```text
binding_stage_first_error
capture_stage_first_error
admission_first_extraction_error
binding_precedes_capture
capture_precedes_extraction
```

These theorems identify the failing declaration or object and the valid prefix before it. `admission_deterministic` fixes the result for fixed inputs. Determinism does not assert that a live filesystem stays unchanged before capture.

## How does admission preserve source checking?

[Composition.lean](../lean/Lara/Evidence/Composition.lean) adds a rejecting evidence check before the existing source continuation. `successful_gate_conservativity` proves that its ordinary output is unchanged when admission succeeds. `package_checked_context_exact` and `package_retained_gamma_agree` reuse the existing policy/group prune and retained-leaf meaning results; evidence success cannot admit a quarantined leaf.

`package_source_preserves` starts from an actual successful `Surface.sourceWithEvidence` equation and derives ordinary elaboration, core checking, complete arguments, typed holes and resolved attacks for that same source. `package_same_source_witness` proves replay witnesses for its semantic certified leaves. `package_holes_iff` and `package_hole_reports_exact` reuse the core checker's exact obligation partition; acceptance does not imply that every argument is complete.

`package_source_justified_nonpromotion` supplies the non-definitional safety connection. It combines evidence admission with ordinary admission and core acceptance, then applies `source_justified_nonpromotion`. Its premises require that the query belongs to the requested query set, is not blocked by the directed quarantine computation, and is justified in the checked framework. The conclusion preserves justified status in the declared reference framework. This is not monotonicity of all statuses under arbitrary evidence deletion, and the status remains conditional on the evidence and policy.

## Which claims remain outside the proof?

`concrete_admission_refinement` explicitly assumes equality between a concrete implementation's result and the finite model's result. It transfers a successful result through that premise; it does not prove the premise. `TypedParserRefinement` similarly states a decoder-to-typed-payload relation rather than verifying the CSV or JSON byte parser. Hash collision resistance, descriptor-relative capture and compiler/runtime correctness remain outside the finite model.

The implementation checks pinned bytes and a selected mapping. It does not rerun an experiment, authenticate its author, prove that a column expresses the intended scientific quantity, or establish that prose matches formal claims. The original-output examples now declare `audit-status = reviewed` after the separately [accepted independent mapping review](certified-evidence-human-review-worklist.md#accepted-independent-review). The [second additive freeze](../measurements/frozen/evidence-measured-inputs-v2.md) records the re-pinned packages; historical raw-core measurements retain their declared-evidence meaning.

## How can the implementation and proofs be checked?

Run the mandatory local proof and conformance gates before review. `lean/AxCheck.lean` covers the new theorems, and the axiom audit restricts proofs to `propext`, `Classical.choice` and `Quot.sound`. The typed Haskell/Lean differential is conformance evidence; byte parsing and OS capture have separate runtime tests.

```sh
make local-gates
cabal test all --test-show-details=direct
make ara-source-spans ara-session-index
cabal run lara -- check-ara examples/certified-evidence/package-a
cabal run lara -- check-ara examples/certified-evidence/package-b
```

The package acceptance gate runs the real binary over copied original packages and mutation cases, including missing or changed evidence, policy precedence, mixed assurance, no-context source paths and transactional publication. The required GitHub Haskell workflow alone does not cover the Lean build or cross-language gates; see [the CI scope decision](ci-scope-decision.md).

## Next Steps

1. Review the runtime contract alongside these theorem premises; do not replace typed-model conformance with a byte-parser soundness claim.
2. Review changed mappings and record a new additive freeze before extending the measured-input scope. The accepted review and current freeze do not satisfy the separate [archival paper-promotion gate](evidence-admission-design.md#archival-paper-promotion-gate).
