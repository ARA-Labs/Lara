# ARA Format Alignment Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make LARA and `examples/the-ara-of-ara` pass the updated `ara check --strict` with zero errors and zero warnings while preserving canonical provenance, narrative metadata, evidence bodies, and LARA's 177-node research DAG.

**Architecture:** The work is an ordered three-repository cutover. First widen `ara-core`'s explicit schema and manifest and expose the new fields in `ara-viewer`; then publish release `v0.1.14`, document that contract, and repair the canonical example; finally migrate LARA with a baseline-vs-current invariant checker. Downstream repositories pin the immutable `v0.1.14` runtime; no permissive allowlist or metadata-dropping compatibility path is allowed.

**Tech Stack:** Rust 2024, Serde/serde-saphyr, Leptos/WASM, Rust integration and browser tests, YAML/Markdown, Python 3.12 + PyYAML 6.0.2 for the permanent LARA migration verifier, GitHub Actions.

## Global Constraints

- Work in three separate repositories and branches: `ARA-Labs/ara-cli`, `ARA-Labs/Agent-Native-Research-Artifact`, and `EYH0602/lara`; publish one reviewable PR per repository.
- Delivery order is runtime, published format, then LARA. The LARA migration must not land before the runtime contract is available at a pinned commit or release.
- Do not change LARA checker behavior, Haskell or Lean source, surface syntax, wire formats, replay identity, generated corpus artifacts, or frozen measurements.
- Do not add an ARA schema-version field or a generic unknown-field allowlist. Every newly accepted key must be explicitly typed and preserved.
- Preserve metadata exactly as authored. `provenance`, `timestamp`, and `status` remain optional strings; no value validation, date normalization, status inference, or rewriting.
- Preserve deterministic source order. Evidence categories are scanned exactly as `figures`, `tables`, `results`, `proofs`; filenames remain sorted within each category.
- Unknown node fields must continue to produce warnings. `ara check --fix` must remain idempotent and must not rewrite any newly accepted metadata.
- Results and proofs are textual exhibits. They do not inherit image or screenshot requirements.
- LARA migration preserves all 177 node IDs; every ID/type/title/provenance/timestamp/status value; all authored narrative text and alternatives; every evidence body and cross-layer claim reference; and old DAG reachability.
- The permanent LARA invariant verifier compares the pre-migration tree at `7718b1df27916159b8df706876579e781f8c03dc` with the final working tree and requires PyYAML 6.0.2.
- No Haskell or Lean suite is required unless an implementation diff touches checker or mechanization files. Verification must prove those paths remain untouched.

---

## Repository and File Map

### `ARA-Labs/ara-cli`

- `crates/ara-core/src/schema.rs`: explicitly deserialize published node metadata and narrative keys.
- `crates/ara-core/src/manifest.rs`: serialize normalized metadata, narrative values, and the four evidence kinds.
- `crates/ara-core/src/parse.rs`: project every accepted raw value into `Node` without changing genuine unknown-field diagnostics.
- `crates/ara-core/src/lint.rs`, `crates/ara-core/src/fix.rs`: retain the scoped dead-end `reason` canonicalization after `reason` becomes an accepted pivot narrative key.
- `crates/ara-core/src/evidence.rs`: discover result/proof Markdown bodies in canonical order and ignore unrelated Markdown tables.
- `crates/ara-core/tests/fixtures/official/published-fields/`: small published-field artifact fixture.
- `crates/ara-core/tests/fixtures/evidence/published-categories/`: focused four-category evidence fixture.
- `crates/ara-core/tests/parse_fixtures.rs`: native parse/JSON and evidence regressions.
- `crates/ara-cli/tests/cli.rs`: strict/fix preservation regression.
- `crates/ara-viewer/src/detail.rs`: deterministic metadata and narrative detail model/rendering.
- `crates/ara-viewer/public/styles.css`: compact metadata presentation.
- `crates/ara-viewer/tests/web.rs`: browser-visible detail assertions.
- `crates/ara-cli/assets/viewer/`: regenerated embedded viewer output after UI changes.
- `.github/workflows/ci.yml`: dogfood strict checks over the new fixtures.
- `CHANGELOG.md`: record the accepted field and evidence-category contract.

### `ARA-Labs/Agent-Native-Research-Artifact`

- `skills/compiler/references/exploration-tree-spec.md`: canonical metadata and narrative field semantics.
- `skills/compiler/references/ara-schema.md`: evidence-category and preservation requirements.
- `examples/the-ara-of-ara/trace/exploration_tree.yaml`: remove its one genuinely redundant ancestor edge, retaining all metadata.
- `.github/workflows/ara-check.yml`: pin the aligned runtime and enforce strict checking on the canonical example.

### `EYH0602/lara`

- `scripts/verify-ara-migration.py`: permanent baseline-vs-current structural/content/evidence invariant gate.
- `scripts/test_verify_ara_migration.py`: mutation-sensitive tests for every invariant.
- `ara/trace/exploration_tree.yaml`: canonical nesting, legacy-field transfer, support/source completion, and redundant-edge removal.
- `ara/evidence/results/mechanization_status.md`, `ara/evidence/results/test_status.md`: renamed ledgers.
- `ara/evidence/README.md`, `ara/PAPER.md`, and every exact old-path reference: result-ledger path migration.
- `.github/workflows/ci.yml`: run migration verification and strict ARA validation with the pinned aligned runtime.

---

## Phase A — Runtime Contract (`ara-cli`)

### Task 1: Preserve Published Node Metadata and Narrative Fields

**Files:**
- Create: `crates/ara-core/tests/fixtures/official/published-fields/trace/exploration_tree.yaml`
- Create: `crates/ara-core/tests/fixtures/official/published-fields/logic/claims.md`
- Modify: `crates/ara-core/src/schema.rs:32-90`
- Modify: `crates/ara-core/src/manifest.rs:253-324`
- Modify: `crates/ara-core/src/parse.rs:331-515`
- Modify: `crates/ara-core/src/lint.rs:1-13,287-388`
- Modify: `crates/ara-core/src/fix.rs:228-273,383-431`
- Modify: `crates/ara-core/tests/parse_fixtures.rs:15-118`
- Modify: `crates/ara-cli/tests/cli.rs:253-315`
- Modify: every `Node { ... }` test constructor under `crates/ara-core/src/` and `crates/ara-viewer/src/`

**Interfaces:**
- Consumes: existing `parse_sources(&str, Option<&str>) -> Result<(Manifest, ParseReport), ParseReport>`.
- Produces: `NodeMetadata { provenance: Option<String>, timestamp: Option<String>, status: Option<String> }`; `NodeNarrative { prior_direction: Option<String>, new_direction: Option<String>, reason: Option<String>, exploration: Option<String>, outcome: Option<String> }`; `Node.metadata`; `Node.narrative`.
- Invariant: `RawNode.extra` receives only genuinely unknown keys; normalized JSON contains every accepted value.

- [ ] **Step 1: Add the published-field fixture**

Create a three-node YAML fixture that exercises all fields and the dead-end alias boundary:

```yaml
tree:
  - id: N01
    type: pivot
    provenance: user-revised
    timestamp: "2026-03-12"
    status: resolved
    support_level: explicit
    source_refs: ["session S01"]
    title: Direction changed
    prior_direction: Curate twenty papers.
    new_direction: Use PaperBench.
    reason: PaperBench has expert rubrics.
    children:
      - id: N02
        type: experiment
        provenance: ai-executed
        timestamp: "2026-04-23T10:30:00Z"
        title: Explore training signal
        exploration: Treat the artifact as an RL environment.
        outcome: The trace carries preference signal.
  - id: N03
    type: dead_end
    title: Failed run
    reason: The process exhausted memory.
```

- [ ] **Step 2: Write failing parse, JSON, and alias assertions**

Add tests that assert N01/N02 values survive `parse_sources` and `serde_json::to_value`, N03's `reason` is normalized to `NodeFields::DeadEnd.why_failed` without duplication in generic narrative, and a `bogus_field` still emits exactly one unknown-field warning. Assert the fixture has no warnings for the eight newly published keys. Add a CLI fix test proving dead-end `reason` remains ARA002-fixable and rewrites to `why_failed` without changing the normalized manifest.

- [ ] **Step 3: Run the focused tests and confirm red behavior**

Run:

```bash
cargo test -p ara-core --test parse_fixtures published_fields -- --nocapture
```

Expected: FAIL because the metadata/narrative accessors do not exist and the raw parser warns on the published keys.

- [ ] **Step 4: Add explicit raw and normalized types**

In `schema.rs`, deserialize each accepted field as `Option<String>`. In `manifest.rs`, define `NodeMetadata` and `NodeNarrative`, derive `Default`, `Serialize`, and `Deserialize`, apply `#[serde(default, skip_serializing_if = ...)]` at field level, and add both structs to `Node`. Keep authored strings verbatim.

In `parse.rs`, clone the raw values into the two structs. Preserve the contextual alias contract: on a `dead_end`, raw `reason` populates `why_failed` and `NodeNarrative.reason` stays `None`; on every other kind, `reason` remains narrative. The other four narrative keys remain available on any node so no accepted value is dropped.

Update ARA002 lint/fix comments and guards. Detection remains context-scoped to `reason` directly on a `dead_end`. Because pre-fix and post-fix manifests are now semantically equal, accept that exact equality plus the existing error-subset and idempotence checks; do not weaken ARA003/ARA004 guards.

- [ ] **Step 5: Update every synthetic `Node` constructor**

- [ ] **Step 6: Run focused and crate tests**

Run:

```bash
cargo test -p ara-core --test parse_fixtures published_fields -- --nocapture
cargo test -p ara-cli --test cli check_fix -- --nocapture
cargo test -p ara-core
```

Expected: PASS; accepted fields produce zero warnings; dead-end `reason` remains safely canonicalizable; the unknown-field regression still warns.

- [ ] **Step 7: Commit the normalized contract**

```bash
git add crates/ara-core/src/schema.rs crates/ara-core/src/manifest.rs crates/ara-core/src/parse.rs crates/ara-core/src/lint.rs crates/ara-core/src/fix.rs crates/ara-core/tests crates/ara-cli/tests/cli.rs crates/ara-viewer/src
git commit -m "feat(core): preserve published node metadata"
```

### Task 2: Discover Results and Proofs as Textual Exhibits

**Files:**
- Create: `crates/ara-core/tests/fixtures/evidence/published-categories/evidence/README.md`
- Create: `crates/ara-core/tests/fixtures/evidence/published-categories/evidence/figures/f1.md`
- Create: `crates/ara-core/tests/fixtures/evidence/published-categories/evidence/tables/t1.md`
- Create: `crates/ara-core/tests/fixtures/evidence/published-categories/evidence/results/r1.md`
- Create: `crates/ara-core/tests/fixtures/evidence/published-categories/evidence/results/r2.md`
- Create: `crates/ara-core/tests/fixtures/evidence/published-categories/evidence/proofs/p1.md`
- Create: `crates/ara-core/tests/fixtures/evidence/published-categories/logic/claims.md`
- Create: `crates/ara-core/tests/fixtures/evidence/published-categories/trace/exploration_tree.yaml`
- Modify: `crates/ara-core/src/manifest.rs:211-237`
- Modify: `crates/ara-core/src/evidence.rs:1-15,308-423`
- Modify: `crates/ara-core/tests/parse_fixtures.rs:226-281`
- Modify: `crates/ara-viewer/src/detail.rs:328-336`

**Interfaces:**
- Consumes: `IndexRow`, `assemble_exhibit`, and `read_evidence`.
- Produces: `ExhibitKind::{Figure, Table, Result, Proof, Other}` and the ordered exhibit vector `[figures/*, tables/*, results/*, proofs/*]`.

- [ ] **Step 1: Add a four-category fixture**

Index all five Markdown bodies with source, claims, and description columns. Name result bodies `r1.md` and `r2.md` in reverse creation order so the test proves filename sorting, not filesystem order. Link a trace node to the same claims. Include an unrelated `Component | Path` code-reference table and a no-file `Fact | Source turns | Used by` evidence table: the former must be ignored, while the latter must retain the existing column-name-tolerant behavior.

- [ ] **Step 2: Write failing evidence assertions**

Assert the exact exhibit sequence and kinds:

```rust
let actual: Vec<(&str, ExhibitKind)> = manifest
    .exhibits
    .iter()
    .map(|e| (e.id.as_str(), e.kind.clone()))
    .collect();
assert_eq!(
    actual,
    vec![
        ("f1", ExhibitKind::Figure),
        ("t1", ExhibitKind::Table),
        ("r1", ExhibitKind::Result),
        ("r2", ExhibitKind::Result),
        ("p1", ExhibitKind::Proof),
    ]
);
```

Also assert zero missing-body warnings and exact source, description, claims, and body text for `r1` and `p1`.

- [ ] **Step 3: Run the focused test and confirm red behavior**

Run:

```bash
cargo test -p ara-core --test parse_fixtures published_evidence_categories -- --nocapture
```

Expected: FAIL because results/proofs are absent and their index rows warn.

- [ ] **Step 4: Extend exhibit discovery and table eligibility**

Add `Result` and `Proof` enum variants. Replace the two-entry discovery array with:

```rust
[
    ("figures", ExhibitKind::Figure),
    ("tables", ExhibitKind::Table),
    ("results", ExhibitKind::Result),
    ("proofs", ExhibitKind::Proof),
]
```

Keep `sorted_md_files`, basename matching, body fallback, and index precedence unchanged. Extend `exhibit_kind_label` to return `result` and `proof`.

Make `ColumnMap::from_headers` return `None` for unrelated Markdown tables: a table is evidence-index-shaped only when it has an explicit file header or at least one recognized claims/source/description header. Preserve the first-column fallback for recognized no-file shapes such as `Fact | Source turns | Used by`.

- [ ] **Step 5: Run focused and core tests**

Run:

```bash
cargo test -p ara-core --test parse_fixtures published_evidence_categories -- --nocapture
cargo test -p ara-core
```

Expected: PASS with deterministic order and no false missing-body warning.

- [ ] **Step 6: Commit evidence support**

```bash
git add crates/ara-core/src/manifest.rs crates/ara-core/src/evidence.rs crates/ara-core/tests crates/ara-viewer/src/detail.rs
git commit -m "feat(core): index result and proof evidence"
```

### Task 3: Render Metadata and Narrative in Node Details

**Files:**
- Modify: `crates/ara-viewer/src/detail.rs:115-166,274-291,338-470,560-650`
- Modify: `crates/ara-viewer/public/styles.css`
- Modify: `crates/ara-viewer/tests/web.rs:39-120` and detail-pane test section

**Interfaces:**
- Consumes: `Node.metadata`, `Node.narrative`, and the existing `TypedField`/`DetailModel` rendering path.
- Produces: `DetailModel.metadata: Vec<MetadataItem>` ordered `provenance`, `timestamp`, `status`; narrative typed fields ordered `prior direction`, `new direction`, `reason`, `exploration`, `outcome` after the node-kind primary fields.

- [ ] **Step 1: Extend the browser JSON fixture and write failing DOM assertions**

Add all metadata and narrative fields to N01. Mount `DetailPane`, select N01, and assert the rendered text contains each authored value exactly once, metadata labels appear in `provenance → timestamp → status` order, and the node-kind `choice/rationale/alternatives` blocks precede the additional narrative blocks.

- [ ] **Step 2: Add native detail-model tests**

Construct a node with all new values. Assert `detail_model` preserves them and that `is_empty()` returns false for a metadata-only or narrative-only node.

- [ ] **Step 3: Run focused native tests and confirm red behavior**

Run:

```bash
cargo test -p ara-viewer detail::tests -- --nocapture
```

Expected: FAIL because `DetailModel` has no metadata/narrative projection.

- [ ] **Step 4: Implement the deterministic detail model**

Add a small `MetadataItem { label: &'static str, value: String }` display model. Append non-empty metadata in the fixed order. Extend `typed_fields_for` by first emitting the existing kind-specific fields, then appending non-empty narrative values in the fixed fallback order. Do not relabel or merge authored text.

Render metadata as a compact labeled block below the header and before description. Update `is_empty()` to count both vectors. Add only the CSS needed for readable label/value alignment and wrapping.

- [ ] **Step 5: Run native and browser tests**

Run:

```bash
cargo test -p ara-viewer detail::tests -- --nocapture
wasm-pack test --headless --chrome crates/ara-viewer --locked
```

Expected: PASS; browser-visible values and ordering match the model.

- [ ] **Step 6: Regenerate the embedded viewer and check freshness**

Run:

```bash
scripts/embed-viewer.sh
scripts/embed-viewer.sh --check
```

Expected: PASS; generated assets and source hash are fresh.

- [ ] **Step 7: Commit viewer support**

```bash
git add crates/ara-viewer crates/ara-cli/assets/viewer
git commit -m "feat(viewer): show node provenance and narrative"
```

### Task 4: Lock Strict/Fix and CI Compatibility

**Files:**
- Modify: `crates/ara-cli/tests/cli.rs:243-315,505-526`
- Modify: `.github/workflows/ci.yml:141-202`
- Modify: `CHANGELOG.md:7-14`

**Interfaces:**
- Consumes: the published-field fixture and current `ara check`/`--fix` exit contract.
- Produces: a CLI regression proving strict-clean parsing and byte-preserving fix idempotence for accepted metadata.

- [ ] **Step 1: Add a strict/fix preservation test**

Copy the published-field YAML to a temporary artifact, record its bytes, run `ara check <dir> --strict --fix` twice, and assert both invocations succeed with `applied 0 fix(es)` and the file bytes remain identical. Add a sibling unknown-field case and assert strict mode still fails.

- [ ] **Step 2: Run the focused CLI tests**

Run:

```bash
cargo test -p ara-cli --test cli check_published_metadata -- --nocapture
```

Expected: PASS after Tasks 1-3; failure here identifies a fix/lint regression.

- [ ] **Step 3: Extend runtime dogfooding**

Add the `official/published-fields` and `evidence/published-categories` artifact directories to the CI fixture loop, both with `--strict`. Keep the synthetic alias round-trip gate unchanged.

- [ ] **Step 4: Update the changelog**

Under `Unreleased / Added`, state that `ara` now preserves and renders the published metadata/narrative keys and indexes Markdown evidence under `results/` and `proofs/`.

- [ ] **Step 5: Run the full runtime gate**

Run:

```bash
cargo fmt --all --check
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo test --workspace --locked
cargo build --locked
./target/debug/ara check crates/ara-core/tests/fixtures/evidence/published-categories --strict
scripts/embed-viewer.sh --check
```

Expected: every command exits 0.

- [ ] **Step 6: Commit runtime gates and documentation**

```bash
git add crates/ara-cli/tests/cli.rs .github/workflows/ci.yml CHANGELOG.md
git commit -m "test: gate published ARA format fields"
```

- [ ] **Step 7: Publish runtime release `v0.1.14` and record its immutable commit**

Open the `ara-cli` PR and wait for all hosted jobs including `viewer-web-test`. Merge only that reviewed head. Create and push the `v0.1.14` tag only after explicit user approval for the release action, wait for the release workflow, and verify the installer reports `ara 0.1.14`. Record the merge SHA and release URL. Downstream phases pin `v0.1.14`; never point a gate at a moving branch.

---

## Phase B — Published Format Contract (`Agent-Native-Research-Artifact`)

### Task 5: Document the Accepted 1.0 Field and Evidence Surface

**Files:**
- Modify: `skills/compiler/references/exploration-tree-spec.md:6-123`
- Modify: `skills/compiler/references/ara-schema.md:29-44,101-105,418-438,500-538`

**Interfaces:**
- Consumes: the reviewed `ara-cli` `NodeMetadata`, `NodeNarrative`, and `ExhibitKind` contract from Tasks 1-4.
- Produces: one documented field matrix matching the runtime and canonical example.

- [ ] **Step 1: Add the exact optional metadata contract**

Document:

```yaml
provenance: user | ai-suggested | ai-executed | user-revised
timestamp: "authored date or date-time text"
status: "authored lifecycle text"
```

State that the named provenance values are current producer values, not a closed parser enum; all three values are preserved verbatim and never inferred or normalized by the runtime.

- [ ] **Step 2: Add the narrative field matrix**

Document `prior_direction`, `new_direction`, and `reason` for pivots; `exploration` and `outcome` for experiments; and the legacy `reason` → canonical `why_failed` rule only for dead-end nodes. State deterministic viewer fallback order and prohibit consuming these fields as untyped extras.

- [ ] **Step 3: Clarify grounding fields**

Retain `support_level` and `source_refs` as required/recommended compiler output for new artifacts. Explicitly distinguish these grounding fields from lifecycle metadata so `provenance: user` does not itself imply `support_level: explicit`.

- [ ] **Step 4: Document evidence bodies consumed by the runtime**

Add `Results` and `Proofs` index examples alongside Tables/Figures. State canonical discovery order `figures`, `tables`, `results`, `proofs`; sorted filenames within each; textual rendering for results/proofs; and no figure/table screenshot obligation for textual categories.

- [ ] **Step 5: Review documentation field names against runtime source**

Compare the prose list directly with `RawNode`, `NodeMetadata`, `NodeNarrative`, and `ExhibitKind`. Expected: no spelling mismatch and no published field absent from runtime.

- [ ] **Step 6: Commit the format contract**

```bash
git add skills/compiler/references/exploration-tree-spec.md skills/compiler/references/ara-schema.md
git commit -m "docs(format): specify provenance and evidence categories"
```

### Task 6: Make the Canonical Example Strict-Clean
**Files:**
- Modify: `examples/the-ara-of-ara/trace/exploration_tree.yaml` at N68
- Modify: `.github/workflows/ara-check.yml:9-48`

**Interfaces:**
- Consumes: the exact reviewed runtime binary/SHA from Task 4.
- Produces: a canonical example with zero errors and zero warnings under strict validation.

- [ ] **Step 1: Capture the pre-edit canonical inventory**

Use a short PyYAML check to record node count, ordered IDs, and `id → {type,title,provenance,timestamp,status}`. Expected baseline: 116 nodes. Save output as review evidence, not a committed artifact.

- [ ] **Step 2: Remove only the redundant ancestor edge**

Delete N68's `also_depends_on: [N65]` entry because N68 is already nested under N65. Do not move nodes or alter other edges.

- [ ] **Step 3: Confirm the code-reference table is not parsed as evidence**

Do not edit or delete the `Code references` table. The Task 2 eligibility rule must ignore its `Component | Path` rows because it has neither an explicit file header nor an evidence semantic column. This preserves all authored code pointers and eliminates the false `Per-task system prompts` missing-body warning at the runtime boundary.

- [ ] **Step 4: Run the released runtime**

Run:

```bash
ara_version_before=\"$(ara --version 2>/dev/null || true)\"
curl --proto '=https' --tlsv1.2 -LsSf \
  https://github.com/ARA-Labs/ara-cli/releases/download/v0.1.14/ara-cli-installer.sh | sh
test \"$(ara --version)\" = \"ara 0.1.14\"
ara check examples/the-ara-of-ara --strict --json | jq '.summary'
```

Expected:

```json
{"errors":0,"warnings":0,"fixable":0,"strict":true,"write_errors":false,"passed":true}
```

- [ ] **Step 5: Re-run the canonical inventory**

Assert the 116 ordered node IDs and metadata map are byte-for-byte equal to Step 1. Assert the only graph delta is removal of redundant edge `N68 → N65`; all authored metadata remains.

- [ ] **Step 6: Pin and strengthen hosted validation**

Set `ARA_VERSION: v0.1.14` and run `ara check examples/the-ara-of-ara --strict` in the same loop as the other examples. Remove the warning-tolerant exception and stale explanatory comment.

- [ ] **Step 7: Run repository gates**

Run:

```bash
ara check examples/minimal-artifact --strict
ara check examples/resnet-ara-example --strict
ara check examples/the-ara-of-ara --strict
```

Expected: all exit 0 with zero warnings. Hosted `ARA Check` and `Validate Skills` provide the remaining repository workflow gates after the PR opens.

- [ ] **Step 8: Commit and publish the format PR**

```bash
git add examples/the-ara-of-ara/trace/exploration_tree.yaml .github/workflows/ara-check.yml
git commit -m "fix(example): enforce strict ARA conformance"
```

Open the PR, wait for hosted ARA Check and Validate Skills, and record the merge commit or reviewed head SHA for the LARA PR.

---

## Phase C — LARA Artifact Migration (`lara`)

### Task 7: Build a Mutation-Sensitive Migration Verifier

**Files:**
- Create: `scripts/verify-ara-migration.py`
- Create: `scripts/test_verify_ara_migration.py`

**Interfaces:**
- Consumes: baseline Git object `7718b1df27916159b8df706876579e781f8c03dc:ara/trace/exploration_tree.yaml`, current `ara/`, and explicit allowed transfers.
- Produces: exit 0 plus a deterministic summary only when all migration invariants hold; exit 1 with one concrete invariant failure otherwise.
- Command: `uv run --no-project scripts/verify-ara-migration.py --baseline 7718b1df27916159b8df706876579e781f8c03dc --artifact ara`.

- [ ] **Step 1: Write failing unit tests for graph normalization**

Use temporary baseline/current mini-artifacts. Cover: duplicate/missing IDs; type/title/metadata mutation; dropped narrative/alternative text; lost `parent` edge; changed reachability; introduced cycle; lost evidence README row/body; invalid resolution transfer; invalid N36 caveat/supersession transfer; and an expected clean migration.

- [ ] **Step 2: Run tests and confirm red behavior**

Run:

```bash
python3 -m unittest scripts/test_verify_ara_migration.py -v
```

Expected: FAIL because the verifier module does not exist.

- [ ] **Step 3: Implement strict loaders and graph extraction**

Use a PEP 723 header pinned to Python `>=3.12,<3.13` and `pyyaml==6.0.2`. Read baseline bytes with:

```python
subprocess.run(
    ["git", "show", f"{baseline}:ara/trace/exploration_tree.yaml"],
    check=True,
    stdout=subprocess.PIPE,
).stdout
```

Decode both trees as strict UTF-8, reject non-mapping nodes, non-string/duplicate IDs, bad child containers, missing edge targets, and malformed legacy `parent` values. Extract ordered node records and semantic graphs: baseline edges are `children ∪ also_depends_on ∪ parent`; current edges are `children ∪ also_depends_on`. Compare reachability after applying the approved structural projection to the baseline: remove the four redundant ancestor edges and replace the legacy N36 `superseded_by: N37` pointer with the forward semantic edge `N37→N36`. Both the projected baseline and current graph must be acyclic.

- [ ] **Step 4: Implement exact content and transfer checks**

Require exactly 177 IDs and equality of ordered ID set plus `type`, `title`, `provenance`, `timestamp`, and `status` maps. Compare all non-structural authored values after applying only these declared canonicalization projections to the baseline:

1. remove `parent`;
2. remove the four known redundant ancestor edges `N67→N66`, `N71→N69`, `N72→N69`, `N73→N69`;
3. map N16/N17 `resolution.note/status/date/by` into `lesson` and deduplicated `source_refs`;
4. map N36 `caveat` into `result` and `superseded_by: N37` into current edge `N37→N36`;
5. add `support_level` and explicit-node `source_refs` according to the assignment map in Task 9;
6. recursively replace only the two approved `evidence/status/...` strings with their `evidence/results/...` destinations.

Any other scalar, list, map, or path difference fails.


- [ ] **Step 5: Implement reachability, acyclicity, and evidence checks**

Compute transitive closure for both semantic graphs and require equality. Run explicit cycle detection on both. Inventory every baseline evidence body below `ara/evidence/` except the index `README.md` by relative path and SHA-256, applying only the two approved `status/ → results/` renames; require exact current path/hash equality. Compare `ara/evidence/README.md` after only the exact two path replacements and the approved `Status ledgers` → `Result ledgers` heading change. Parse every README Markdown link target, require the same normalized targets after the approved rename, and require each current local target to exist.

- [ ] **Step 6: Make the tests mutation-sensitive**

For each invariant, start from the passing fixture, apply one mutation, invoke the verifier CLI, assert exit 1, and match the diagnostic category. The clean fixture must exit 0 twice with byte-identical stdout.

- [ ] **Step 7: Run the verifier tests**

Run:

```bash
uv run --no-project python -m unittest scripts/test_verify_ara_migration.py -v
```

Expected: all tests pass.

- [ ] **Step 8: Commit the verifier before artifact edits**

```bash
git add scripts/verify-ara-migration.py scripts/test_verify_ara_migration.py
git commit -m "test(ara): add migration invariant verifier"
```

### Task 8: Canonicalize LARA Tree Structure and Legacy Fields

**Files:**
- Modify: `ara/trace/exploration_tree.yaml`

**Interfaces:**
- Consumes: Task 7's exact transfer rules.
- Produces: no `parent`, `resolution`, `caveat`, or `superseded_by` fields; canonical nesting and cross-edges accepted by `ara`.

- [ ] **Step 1: Run the verifier against the unmigrated tree and capture red diagnostics**

Run:

```bash
uv run --no-project scripts/verify-ara-migration.py \
  --baseline 7718b1df27916159b8df706876579e781f8c03dc --artifact ara
```

Expected: FAIL listing the sixteen legacy parent relations and three legacy-field nodes.

- [ ] **Step 2: Canonically nest the sixteen parented nodes**

Move nodes in this exact relation set, preserving source order at each destination and recursively nesting chains:

```text
N69→N74
N114→N115→N116→N117→N118→N119→N120→N121
N122→N123→N125→N126→N129→N130
N122→N124→N127→N128
```

Here `A→B` means B becomes a child of A. Remove each moved root occurrence and its `parent` key. Never duplicate a node.

- [ ] **Step 3: Remove the four proven-redundant edges**

Delete only `N67→N66`, `N71→N69`, `N72→N69`, and `N73→N69` from `also_depends_on`. Preserve every other cross-edge and its order.

- [ ] **Step 4: Transfer N16 and N17 resolution records**

Append to each existing `lesson` exactly:

```text
Resolution (<status>, <YYYY-MM-DD>): <note>
```

Append every `resolution.by` string to `source_refs` in authored order, skipping exact duplicates. Confirm the new lesson contains the full original note and the status/date before deleting `resolution`.

- [ ] **Step 5: Transfer N36 caveat and supersession**

Append `Caveat: <exact caveat text>` to N36's `result`. Append `N36` to N37's `also_depends_on` after any existing targets. Then remove `caveat` and `superseded_by` from N36.

- [ ] **Step 6: Run the verifier and inspect only remaining grounding failures**

Expected: structural, content-transfer, reachability, cycle, and evidence checks pass; only missing support/source assignments remain.

- [ ] **Step 7: Commit structural normalization**

```bash
git add ara/trace/exploration_tree.yaml
git commit -m "refactor(ara): canonicalize exploration graph"
```

### Task 9: Complete Grounding Metadata Without Inventing Sources

**Files:**
- Modify: `ara/trace/exploration_tree.yaml`
- Modify: `scripts/verify-ara-migration.py`
- Modify: `scripts/test_verify_ara_migration.py`

**Interfaces:**
- Consumes: existing node provenance, `source_refs`, and evidence entries.
- Produces: every node has `support_level`; every explicit node has at least one existing source locator.

- [ ] **Step 1: Encode and apply the reviewed assignment map**

Keep the existing 66 explicit nodes unchanged. Assign `inferred` to exactly:

```text
N60 N68 N76 N80 N83 N85 N89 N92 N93 N100
N105 N106 N132 N133 N134 N140 N142 N150 N158 N160
```

Assign `explicit` to the other 91 previously unclassified nodes initially because their existing evidence lists appear to contain a direct file, run, issue, PR, commit, session, or user directive. The source-resolution audit in Step 3 is authoritative: if any candidate has no accepted locator, reclassify it as `inferred` and update the assignment constant and test in the same commit.

- [ ] **Step 2: Promote only locators into `source_refs`**

For each newly explicit node, copy its existing evidence entries into `source_refs` in order only when each entry identifies an existing repository path, URL, issue/PR, commit/tag, Actions run, session/user directive, or named run result. Retain every original evidence entry. Do not copy explanatory prose or bare conclusions. If a node lacks any valid locator, change it to `inferred` rather than inventing a source.

- [ ] **Step 3: Add verifier source-resolution rules**

For `support_level: explicit`, require a non-empty `source_refs`. Resolve repository-relative paths against the repository, accept `ara/`-prefixed paths relative to repository root, validate HTTP(S) syntax without network fetch, and accept the explicitly documented GitHub issue/PR/commit/run, session, or user-directive forms. Reject free-form prose-only entries. Require `support_level` to be exactly `explicit` or `inferred`.

- [ ] **Step 4: Run migration and mutation tests**

Run:

```bash
uv run --no-project python -m unittest scripts/test_verify_ara_migration.py -v
uv run --no-project scripts/verify-ara-migration.py \
  --baseline 7718b1df27916159b8df706876579e781f8c03dc --artifact ara
```

Expected: both pass; summary reports 177 nodes and equal reachability.

- [ ] **Step 5: Run the aligned runtime on the tree before evidence moves**

Run the pinned local binary:

```bash
../ara-cli/target/debug/ara check ara --strict --json | jq '.summary'
```

Expected: only missing-body warnings tied to the two still-unmoved status ledgers may remain; no unknown-field, parent, legacy-field, grounding, cycle, or redundant-edge warning remains.

- [ ] **Step 6: Commit grounding metadata**

```bash
git add ara/trace/exploration_tree.yaml scripts/verify-ara-migration.py scripts/test_verify_ara_migration.py
git commit -m "docs(ara): complete node grounding metadata"
```

### Task 10: Move Status Ledgers into Results and Rewrite Exact References

**Files:**
- Rename: `ara/evidence/status/mechanization_status.md` → `ara/evidence/results/mechanization_status.md`
- Rename: `ara/evidence/status/test_status.md` → `ara/evidence/results/test_status.md`
- Modify: every tracked text file containing `evidence/status/mechanization_status.md` or `evidence/status/test_status.md`, including `ara/PAPER.md`, `ara/evidence/README.md`, logic files, trace/session records, `docs/`, and `lean/README.md`

**Interfaces:**
- Consumes: the two exact old paths.
- Produces: two byte-identical bodies at new result paths and zero old-path references.

- [ ] **Step 1: Record pre-move body hashes and reference inventory**

Run SHA-256 over both files and use repository search to record every exact old-path reference. This is verification evidence, not a committed generated file.

- [ ] **Step 2: Rename both files without content edits**

Use filesystem moves. Verify the new hashes equal Step 1 and `ara/evidence/status/` is empty.

- [ ] **Step 3: Replace both exact paths everywhere**

Perform a literal full-path migration only:

```text
evidence/status/mechanization_status.md → evidence/results/mechanization_status.md
evidence/status/test_status.md          → evidence/results/test_status.md
```

Preserve each file's surrounding prose. In `ara/evidence/README.md`, rename `Status ledgers` to `Result ledgers` and point both table rows to `results/...`.

- [ ] **Step 4: Verify zero stale references and resolved local links**

Search the entire tracked repository for `evidence/status/` and `status/mechanization_status.md` / `status/test_status.md`; expected zero matches. Run the migration verifier; expected evidence inventory and README row checks pass.

- [ ] **Step 5: Run strict ARA validation**

Run:

```bash
../ara-cli/target/debug/ara check ara --strict --json | jq '.summary'
```

Expected:

```json
{"errors":0,"warnings":0,"fixable":0,"strict":true,"write_errors":false,"passed":true}
```

- [ ] **Step 6: Commit the path migration**

```bash
git add -A ara docs lean/README.md scripts
git commit -m "refactor(ara): move status ledgers into results"
```

### Task 11: Gate LARA Against the Pinned Runtime

**Files:**
- Modify: `.github/workflows/ci.yml:9-113`
- Modify: `scripts/verify-ara-migration.py` only if hosted path behavior exposes a real portability defect

**Interfaces:**
- Consumes: the immutable runtime SHA/tag and format PR SHA from Phases A/B.
- Produces: hosted migration-invariant and strict-validation gates independent of any globally installed `ara`.

- [ ] **Step 1: Add the migration invariant gate**

After uv setup, run:

```yaml
- name: ARA migration invariants
  run: |
    uv run --no-project python -m unittest scripts/test_verify_ara_migration.py -v
    uv run --no-project scripts/verify-ara-migration.py \
      --baseline 7718b1df27916159b8df706876579e781f8c03dc --artifact ara
```

The checkout must have enough Git history/object access for `git show <baseline>:...`; set `fetch-depth: 0` on `actions/checkout` if needed.

- [ ] **Step 2: Add strict validation using release `v0.1.14`**

```yaml
- uses: ARA-Labs/ara-cli/.github/actions/check@v0.1.14
  with:
    path: ara
    strict: true
    version: v0.1.14
```

The tag is the immutable released contract from Task 4. Do not use `latest`, `v0`, a global preinstalled binary, or a moving branch.

- [ ] **Step 3: Run local CI-equivalent ARA gates**

Run the unittest, migration verifier, and pinned strict checker exactly as CI will. Expected: all exit 0.

- [ ] **Step 4: Prove checker/mechanization artifacts are untouched**

Compare the migration branch to `7718b1d` and fail the review if any path under `src/`, `test/` Haskell suites, `lean/`, `examples/`, `fixtures/`, `corpus-units/`, `bundles/`, `measurements/`, or generated artifact directories changed, except documentation-only `lean/README.md` path rewrites. Record that no Haskell/Lean suite is required under the approved design.

- [ ] **Step 5: Commit hosted gates**

```bash
git add .github/workflows/ci.yml
git commit -m "ci: enforce strict ARA migration checks"
```

- [ ] **Step 6: Publish the LARA PR with pinned dependencies**

Link the runtime and format PRs/commits in the body. Report the exact strict JSON summary, migration verifier summary, body hashes, node count, and hosted CI result. Do not merge until the pinned runtime contract is available.

---

## Final Cross-Repository Verification

### Task 12: Verify the Coordinated Cutover

**Files:**
- No source changes unless a gate exposes a defect.

**Interfaces:**
- Consumes: final reviewed commits from all three repositories.
- Produces: reproducible evidence that the runtime, published contract, canonical example, and LARA artifact agree.

- [ ] **Step 1: Verify `ara-cli` from a clean checkout**

Run:

```bash
cargo fmt --all --check
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo test --workspace --locked
wasm-pack test --headless --chrome crates/ara-viewer --locked
scripts/embed-viewer.sh --check
```

Expected: all exit 0.

- [ ] **Step 2: Build the exact runtime once**

Run `cargo build -p ara-cli --locked` and record the binary path, version, and source commit SHA. Use this same binary for both downstream strict checks.

- [ ] **Step 3: Verify the published canonical example**

Run:

```bash
$PINNED_ARA check /path/to/Agent-Native-Research-Artifact/examples/the-ara-of-ara --strict --json
```

Expected: 0 errors, 0 warnings, 0 fixable issues, `passed: true`.

- [ ] **Step 4: Verify LARA migration and strict conformance**

Run:

```bash
uv run --no-project python -m unittest scripts/test_verify_ara_migration.py -v
uv run --no-project scripts/verify-ara-migration.py \
  --baseline 7718b1df27916159b8df706876579e781f8c03dc --artifact ara
$PINNED_ARA check ara --strict --json
```

Expected: all pass; strict summary is zero/zero/zero.

- [ ] **Step 5: Verify repository boundaries**

Confirm the format repository changed only schema/example/CI files; LARA changed only artifact/docs/verifier/CI files; runtime changed only parser/manifest/evidence/viewer/tests/assets/docs/CI files. Confirm LARA generated corpus, replay bundles, and frozen artifact hashes match `7718b1d`.

- [ ] **Step 6: Verify hosted checks in dependency order**

Require green hosted CI for the runtime PR first, then the format PR against its immutable runtime, then LARA against the same runtime. Record PR URLs, reviewed head/merge SHAs, runtime tag if released, and check-run URLs in each dependent PR.

- [ ] **Step 7: Merge in dependency order**

Merge `ara-cli`, publish/pin its release if required by downstream CI, merge `Agent-Native-Research-Artifact`, then merge LARA. If any upstream SHA/tag changes during review, rerun both downstream strict checks before merging.
