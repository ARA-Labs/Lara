# ARA Format Alignment and Strict Validation

Status: approved in conversation on 2026-08-12.

## Goal

Align LARA's research artifact, the published Agent-Native Research Artifact
format, and the official `ara` runtime without deleting research provenance or
hiding valid evidence. The completed work must make both LARA and the canonical
`the-ara-of-ara` example pass `ara check --strict` with zero errors and zero
warnings using the updated runtime.

The migration spans three repositories:

1. `EYH0602/lara`, which owns the 177-node LARA artifact;
2. `ARA-Labs/ara-cli`, which owns parsing, validation, normalized data, and the
   viewer;
3. `ARA-Labs/Agent-Native-Research-Artifact`, which owns the compiler reference,
   canonical examples, and published format documentation.

## Problem

The current strict diagnostics mix genuine LARA drift with runtime/schema
mismatch. LARA initially had malformed YAML scalars. After those syntax errors
were repaired, `ara` 0.1.11 reported 462 warnings:

- 157 `provenance` fields and 157 `timestamp` fields rejected as unknown;
- 114 lifecycle `status` fields rejected as unknown;
- 16 noncanonical `parent` fields;
- two structured `resolution` fields and one each of `caveat` and
  `superseded_by`;
- four redundant ancestor dependencies;
- ten evidence-index rows whose valid bodies live under `status/`, `results/`,
  or `proofs/`, directories that the runtime does not scan.

The published sources establish that most of these warnings are not invalid
ARA data. The canonical `examples/the-ara-of-ara/trace/exploration_tree.yaml`
uses `provenance` and `timestamp` on all 116 nodes and also uses `status` and
additional narrative fields. The compiler directory schema permits
`evidence/results/` and `evidence/proofs/`. The runtime currently accepts none
of those metadata fields and enumerates only `evidence/figures/` and
`evidence/tables/`.

The fix must therefore change the runtime and published contract before
normalizing the LARA-only extensions. Making LARA conform to the runtime's
current narrow field list would discard canonical provenance and suppress
valid evidence.

## Authorities and Compatibility Rule

The accepted format is the union of:

- the field-level compiler references under
  `skills/compiler/references/`;
- fields used by the canonical `examples/the-ara-of-ara` artifact;
- explicit provenance guarantees in the top-level ARA documentation.

`ara check --strict` must reject or warn on fields outside this published union,
not on fields the official repository itself emits. When documentation and an
official example disagree, this work updates the documentation to describe the
example rather than deleting the example's provenance.

The migration does not introduce an `ara_version` or schema-version bump. It
makes the runtime implement the already-published 1.0 artifact surface.

## Non-goals

- Do not change LARA checker behavior, Haskell or Lean source, surface syntax,
  wire formats, replay identity, generated corpus artifacts, or frozen
  measurements.
- Do not rewrite research conclusions, calibrate claims, or refresh historical
  project status. This is a structural migration, not an epistemic review.
- Do not silence diagnostics through a runtime allowlist that discards field
  values.
- Do not remove provenance, timestamps, lifecycle status, dead ends, rejected
  alternatives, or evidence bodies to satisfy the current runtime.
- Do not broaden `ara` into a generic YAML viewer. The accepted fields remain a
  documented format surface.
- Do not make LARA depend on an unreleased global `ara` binary. Cross-repository
  verification runs the locally built runtime explicitly.

## Runtime Design (`ara-cli`)

### Node metadata

Extend the raw schema, normalized manifest, native/WASM serialization, and
viewer node details with optional metadata used by the canonical artifact:

- `provenance`;
- `timestamp`;
- `status`.

`provenance` preserves the format's existing values (`user`, `ai-suggested`,
`ai-executed`, and `user-revised`). Unknown future values remain displayable
strings rather than causing data loss. `timestamp` is preserved as authored
text because official examples contain both full dates and date-time values.
`status` is also preserved as authored text; the runtime does not infer or
rewrite research maturity.

The canonical example also carries type-specific narrative keys not modeled by
the current `RawNode`: `prior_direction`, `new_direction`, `reason`,
`exploration`, and `outcome`. Model and retain those values. The parser may map
`reason` to the existing dead-end failure field only when the existing
canonical fix rule applies; otherwise the normalized node retains the authored
field. No accepted field may be consumed through `IgnoredAny`.

The viewer displays metadata in a compact node-details block and uses the
additional narrative fields in a deterministic fallback order after the
primary type-specific body. Native and WASM builds must expose the same values.

### Evidence categories

Extend evidence discovery and `ExhibitKind` to cover the published directories:

- `figures`;
- `tables`;
- `results`;
- `proofs`.

Each directory is enumerated in that order, with filenames sorted inside the
directory. Index rows continue to match bodies by normalized basename. Results
and proofs render as textual exhibits; they do not acquire figure/table image
requirements. Index rows for a real result or proof body must not produce a
missing-body warning.

LARA's two status ledgers move into `evidence/results/`; `status/` does not
become a fifth runtime category. The published schema already defines results
as the home for run records and empirical status ledgers fit that category.

### Regression fixtures

Add focused tests that prove:

- every published metadata field parses without entering the unknown-field
  map;
- metadata survives normalization and native/WASM serialization;
- viewer node details receive the preserved values;
- result and proof bodies bind to index rows and retain source, description,
  and claim references;
- unknown fields still warn;
- directory and source ordering remain deterministic;
- `ara check --fix` remains idempotent and does not rewrite metadata.

Use a small checked-in fixture derived from the published field set. Do not
copy the entire LARA artifact into `ara-cli`.

## Published Contract Design

Update `skills/compiler/references/exploration-tree-spec.md` and the relevant
section of `ara-schema.md` to document:

- optional `provenance`, `timestamp`, and `status` node metadata;
- the additional narrative fields already used by the canonical example;
- preservation requirements for authored metadata;
- `results` and `proofs` as evidence body categories consumed by the runtime;
- `support_level` and `source_refs` as the grounding fields expected from newly
  compiled artifacts.

The canonical `the-ara-of-ara` example remains the compatibility fixture. Fix
its genuine structural warnings, including redundant ancestor dependencies and
any evidence-index/body mismatch, but do not remove metadata to make it pass.

## LARA Migration

### Preserve identity and content

The migration must preserve:

- the complete set of 177 node IDs;
- every node type and title;
- all provenance values, timestamps, and lifecycle statuses;
- all authored narrative text and alternatives;
- every evidence body and cross-layer claim reference;
- the reachability relation of the research DAG.

Formatting and field placement may change. No historical statement may be
silently shortened or reinterpreted.

### Canonicalize primary-parent edges

Sixteen root-level nodes currently carry a `parent` field that the runtime
ignores. Convert each relation into canonical nesting:

1. remove the node from the root list;
2. append it to the named parent's `children` list;
3. preserve the moved nodes' original relative source order;
4. apply the operation recursively where a moved node is itself a parent.

Before and after migration, compute the graph induced by nesting,
`also_depends_on`, and legacy `parent` edges. The new graph must preserve all
old edges and remain acyclic.

Remove only the four `also_depends_on` entries that the runtime proves are
redundant because the target is already an ancestor. Other cross-edges remain
in source order.

### Canonicalize special legacy fields

N16 and N17 are dead ends with structured `resolution` maps. Preserve each
resolution's status, date, source list, and note in canonical fields:

- append the exact note to `lesson` with its resolution status and date;
- append each `by` entry to `source_refs` without duplication;
- remove `resolution` only after an invariant check confirms every value was
  transferred.

N36 carries `caveat` and `superseded_by: N37`. Append the caveat text to N36's
`result` under an explicit `Caveat:` label. Add N36 to N37's
`also_depends_on`, preserving N37's existing edge order, then remove
`superseded_by`. This records the supersession as a forward DAG dependency
instead of an ignored reverse pointer.

### Complete grounding metadata

Preserve every existing `support_level` and `source_refs` value. For nodes that
lack `support_level`:

- use `inferred` for `ai-suggested` records unless an explicit source directly
  states the decision or result;
- use `explicit` only when an existing source reference, evidence entry,
  session record, issue, commit, run, or document directly grounds the node;
- otherwise use `inferred` rather than inventing a source.

Every newly explicit node receives at least one existing, resolvable source
reference. Evidence values may be reused only when they identify a real claim,
file, run, issue, PR, commit, or session. Free-form explanatory prose is not
promoted into a source locator.

### Normalize evidence paths

Move:

- `evidence/status/mechanization_status.md` to
  `evidence/results/mechanization_status.md`;
- `evidence/status/test_status.md` to
  `evidence/results/test_status.md`.

Update `evidence/README.md`, `PAPER.md`, claims, experiments, trace records, and
any other references through a repository-wide exact-path migration. Remove the
empty `status/` directory. Existing files under `results/` and `proofs/` remain
in place.

## Verification

### Structural invariants

A migration verifier compares the pre-migration and post-migration trees and
fails unless:

- both contain exactly 177 unique node IDs;
- ID, type, title, provenance, timestamp, and status maps are identical;
- every legacy `parent` edge exists as a nesting edge afterward;
- the old and new DAG reachability relations are identical;
- both graphs are acyclic;
- every transferred `resolution`, `caveat`, and `superseded_by` value is present
  in its canonical destination;
- no evidence body or README index row is lost.

The verifier may be a one-off implementation aid if the permanent runtime tests
cover the resulting contract. It must run before the legacy fields are removed
and again against the final artifact.

### Repository gates

`ara-cli`:

- `cargo fmt --check`;
- focused parser, evidence, serialization, and viewer tests;
- `cargo test --workspace`;
- local `ara check --strict` against its regression fixtures.

`Agent-Native-Research-Artifact`:

- the locally built `ara check --strict examples/the-ara-of-ara` reports zero
  errors and zero warnings;
- compiler/schema references agree with the example and runtime field set.

LARA:

- the migration invariant verifier passes;
- the locally built `ara check --strict ara` reports zero errors and zero
  warnings;
- all modified Markdown links and evidence paths resolve;
- the LARA source tree, generated corpus, replay bundles, and frozen artifacts
  are unchanged.

No Haskell or Lean suite is required unless the final diff touches checker or
mechanization files, which this design prohibits.

## Delivery Sequence

1. Implement and test the runtime field/evidence support in `ara-cli`.
2. Update the published schema and canonical example against that runtime.
3. Migrate LARA using the locally built runtime and invariant verifier.
4. Run strict validation across both artifacts.
5. Publish separate, reviewable commits and pull requests per repository.

The LARA migration must not land before the corresponding runtime contract is
available at a pinned commit or release. Until then, LARA's existing non-strict
zero-error result remains the truthful validation status.
