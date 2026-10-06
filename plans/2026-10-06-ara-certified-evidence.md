# ARA-packaged certified evidence implementation plan

**Date:** 2026-10-06

>For agentic workers: use the `subagent-driven-development` or `executing-plans` skill to execute this plan task by task. The checkboxes below track implementation, not work completed by writing this document.

**Goal:** Resolve [issue #8](https://github.com/ARA-Labs/Lara/issues/8) by admitting a certified leaf only after a policy-approved checker reproduces its proposition from hash-pinned files included in its ARA package.

**Architecture:** Put a separately versioned evidence-admission boundary around the existing source checker. Its sealed result binds package bytes, source and policy, extraction requests, and successful leaf judgments to the same source carrier used for checking and reporting. Preserve the symbolic core, its conditional interpretation of `Gamma`, its located holes, and its four argument statuses.

**Tech stack:** Haskell implementation, Lean metatheory and executable differential model, the existing S-expression codecs and exact numeric normalization, SHA-256 artifact identities, and existing Cabal/Make verification gates.

**Status:** **Partially executed; blocked at Task 0 (2026-10-06).** The approved plan's original-output gate did not pass in the [recorded inventory](../docs/evidence-admission-inventory.md). The corpus was initialized and candidate byte hashes, package sizes, saved notebook outputs and rejected extraction probes were inspected. No evidence runtime was written. Tasks 1 through 7 and the inventory-backed contract review remain unexecuted; issue #8 stays open with the acquisition/portfolio blocker. Approval of the plan is not a gate pass. Keep this living plan while work remains; delete it only after execution, preserving settled contracts in `docs/`.

**Review revisions (2026-10-06):**
- Replaced the dynamic read-program runner with *static* per-request dependencies. Both shipped families read exactly one named object, so an interpreter with data-dependent reads would be machinery no shipped checker uses, and its tests would need a test-only checker. Confinement now holds by construction and is still proved over the runner model.
- The verifier, not only the package author, can supply the policy (`--policy`). A package-supplied allowlist is self-approval; the report now records which policy was used and where it came from.
- Exit codes are now settled per failure class. Capture or integrity failure of the manifest, `PAPER.md`, source, or policy exits 2, matching today's missing-policy behavior. Evidence-object failures, and certified leaves on a door with no evidence context, are R8 (exit 1), matching the spec §10.1 R8 row.
- The manifest must be in canonical form on disk; non-canonical bytes reject, so a package has exactly one identity.
- Made the vague `PAPER.md` requirement concrete and fixed the version naming in Migration (`lara-syntax@0.11` for the syntax, `lara-evidence@0.1` for the layer).
- Migration now lists the seven affected `.lara` fixtures and replaces the blanket "no relabeling" rule, which those fixtures could not satisfy, with a per-fixture rule.
- Task 0 now bounds package size, because Git LFS pointers are rejected by design.

## TL;DR

This adds an evidence-admission judgment and composition proofs while preserving Lara's argumentation semantics. An ARA package must contain the original files used by each certified leaf; an external URL or a copied prose assertion does not substitute for those bytes. The checker must reproduce the proposition. Implementation starts after the existing inventory gate passes, with scientific validity, natural-language faithfulness, and filesystem/cryptographic assumptions kept outside the proved guarantee.

## Problem

The current specification requires a listed checker witness and a replayable reference for certified leaves, but marks the requirement unenforced in `docs/spec.md` §4.3. The separate evidence-admission design deliberately deferred byte checking. Merely adding a witness-name field would close a metadata gap while leaving the claimed value unchecked.

The approved direction is stronger: the result file must be inside the ARA package and the extraction must run. `docs/corpus-map.md` §3 already maps leaf references to ARA evidence paths. The upstream [ARA anatomy](https://github.com/ARA-Labs/Agent-Native-Research-Artifact#under-the-hood--the-artifact-anatomy) describes `PAPER.md`, `logic/`, `src/`, `trace/`, and `evidence/`; it does not by itself define the machine-readable manifest proposed here. This plan introduces a Lara checking profile for that package, not an unannounced change to the upstream ARA standard.

At planning time the checked-out `corpus/ara-paperbench/` directory was empty. Task 0 has now initialized its existing pin and recorded the [inventory result](../docs/evidence-admission-inventory.md): the gate has not passed. Existing lowered Lara corpus units and reconstructed paper tables are not substitutes for original experiment outputs.

## Constraints

- Keep `lara-core@0.3`, its wire codec, strict backends, attack rules, and four-state semantics unchanged. Raw `.sexp` checking stays relative to supplied evidence and never reports package verification.
- Package inclusion is necessary but insufficient: check the object hash, the checker allowlist, the pinned extraction request, and equality of normalized propositions.
- Certification does not validate the experiment, authenticate its author, prove a column's scientific meaning, or prevent attacks on the leaf. The payload-to-proposition mapping remains an explicit reviewed assumption.
- No network access, arbitrary executables, dynamic plugins, or filesystem access from a leaf checker. A checker is a pure function of the captured bytes of the objects its request statically names; the runner, not the checker, looks those objects up in the snapshot.
- Missing, altered, or mismatching certified evidence rejects. No automatic relabeling as observed evidence and no evidence-specific quarantine mechanism in this implementation. Existing policy/group quarantine remains unchanged.
- Source validity and rejection precedence must be deterministic. A successful replay cannot override policy rejection or make a quarantined leaf available.
- Mechanize each frozen corpus-independent definition alongside its implementation. Every new Lean theorem must appear in `lean/AxCheck.lean`, remain `sorry`-free, and use only the standard axiom trio.

## Proposed approach

### What is in the package?

Use an explicitly supplied ARA root, not upward directory discovery. Add `lara-evidence.sexp` at that root as the versioned checking manifest. Require `PAPER.md` to be a regular file at the root, listed in the manifest with its length and digest so the report pins which paper the evidence accompanies. Lara does not parse its contents, and its presence proves nothing about the quality or completeness of the whole ARA. List the artifact `.lara` source, policy source, and every evidence object needed for replay by package-relative path, byte length, and SHA-256 digest. Read existing ARA files without rewriting their schema.

Package membership means a regular file actually captured from inside that root, not a URL, unresolved Git LFS pointer, symlink to outside data, or an entry that exists only in the manifest. Reject absolute paths, empty components, `.`/`..`, duplicate normalized paths, duplicate object identifiers, symlink traversal, and non-regular files. Resolve path components relative to an opened root directory; checking a string prefix or calling `realpath` and later reopening a path is not sufficient. The approved manifest defines the snapshot; a checker must never reopen live paths after capture.

Use canonical manifest bytes for identity, and reject a manifest whose on-disk bytes differ from the canonical encoding of what they decode to. Re-encoding silently would give one package two identities: the bytes a reader hashes and the bytes Lara reports. The manifest must not hash itself or generated reports, and the source's existing declared artifact digest must not be set to the enclosing manifest digest, which would create a hash cycle. Capture each input once; validate its length and digest on the bytes passed to later stages. Source and policy are captured before their semantic checks; evidence objects are captured after earlier policy rejection has been ruled out. Record acquisition origins separately from the certified object bytes. Copying an original output into `evidence/` is permitted; rewriting an output to make the extractor accept it is not original-output evidence.

### How does the source name a witness?

Keep evidence policy and extraction requests in the existing presentation AST: add an evidence allowlist to Haskell `Lara.AST.Policy` and a typed optional request to its source `Leaf`, mirrored in `Lara.Presentation`. This follows the existing presentation-only `policyMeasurands` convention (`src/Lara/AST.hs:469-477`). Haskell's presentation `Policy` is not the Lean core `Lara.Policy.Policy`; only selected fields lower into `Unit`. Do not extend the core policy, core leaf environment, or wire codec, and do not introduce parallel program/policy wrappers merely to carry source-only fields.

The source policy has an exact allowlist of `(LeafCheckerId, CheckerVersion)`. A certified leaf has exactly one extraction request, naming one approved checker, its typed payload, and the manifest objects it depends on. That object list is part of the request: the runner passes the checker exactly those captured objects, so dependencies are known before any extraction runs. Both v1 families take exactly one object. A future multi-object family still declares its whole object list in the request; data-dependent dynamic reads are out of scope until a real family needs them. The request resolves an existing leaf reference to a manifest-listed object and must agree with the leaf's checker provenance. Reject missing or duplicate requests, requests for undeclared leaves, requests attached to non-certified leaves, disallowed/unknown checker versions, and disagreement between request and provenance. Ordinary provenance remains descriptive; neither an author-supplied name nor a receipt can construct a successful judgment.

The policy that holds the allowlist may come from the package, but a package-supplied allowlist is self-approval, so the package cannot be the only possible source. `check-ara` takes an optional verifier policy (`--policy FILE`) that replaces the manifest-listed policy for the whole run, including its admission table and group mode. The verifier policy is read once, hashed, and recorded with origin `verifier`; the package policy is recorded with origin `package`. The report and evidence identity always name the policy digest and its origin, and a report produced under a package policy must not be presented as verifier-approved. The registry is closed and compiled into Lara either way, so an allowlist can only narrow which implemented checkers apply.

Compare extracted output against the expanded semantic leaf produced by the existing value-binding/comparison elaboration, using `Lara.Prop.nf`/`equiv`. Bind it back to the authored leaf identifier, provenance and references. Comparing against an unexpanded `let` name would check a different proposition; independently expanding the program twice risks disagreement between admission and checking.

Use closed sums for fixed keywords and the implemented checker families, distinct newtypes for package paths, object identifiers, column names, JSON keys, checker versions, and digests, and private constructors for validated paths, snapshots, and successful judgments. Raw strings belong only in boundary decoders and diagnostics. The source syntax target is `lara-syntax@0.11`, advancing the currently documented `@0.10`; update the grammar appendix and Haskell/Lean presentation parity together.

### Which extractors ship?

The bounded candidate portfolio is `tsv-row@1` and `json-pointer@1`. Task 0 must demonstrate that both occur in original outputs covering the inventory gate. If it does not, stop and revise the portfolio against observed formats before writing extractor code; do not invent fixtures to pass the gate. Checker family means an independently specified extraction operation, not two versions or two aliases of the same checker.

| Family | Proposed request shape | Acceptance rule | Reject boundaries |
| --- | --- | --- | --- |
| `tsv-row@1` | Object reference, key column/value, ordered column selectors and explicit term encodings, output predicate | Exactly one row matches the key; each selected field decodes under its declared encoding; construct the ordered proposition and compare its normal form with the leaf | Duplicate headers, duplicate or absent matching rows, missing columns, malformed UTF-8, malformed cells, ragged rows, proposition mismatch |
| `json-pointer@1` | Object reference, ordered tokenized JSON pointers and explicit term encodings, output predicate | Every pointer resolves exactly once; selected scalar values decode under their declared encodings; construct the ordered proposition and compare its normal form with the leaf | Duplicate object keys, missing paths, invalid pointer escapes or array indices, wrong scalar types, malformed UTF-8/JSON, proposition mismatch |

Freeze string and exact-decimal field encodings for both families, plus canonical Lara ground-term decoding where original TSV data actually uses it. No inferred types, wildcards, coercion of booleans/null, unit conversion, aggregation, approximate equality, or binary floating-point parsing. Specify scientific-notation and trailing-zero handling through exact normalization before using the existing `Lara.Strict.Cell` decimal representation. Original bytes remain unchanged even when the decoded number normalizes. Freeze numeric size limits before parser implementation so enormous exponents cannot force unbounded allocation. The corpus inventory must reject an unsuitable encoding rather than silently coerce it.

TSV is UTF-8 with one header row, tabs as separators, LF or CRLF record endings, no quoted embedded tabs/newlines, and an optional final newline. Strip a CR only as part of a CRLF record ending. JSON is strict UTF-8 JSON with duplicate keys rejected during parsing, before any last-key-wins object representation could erase them. Selection order is explicit and part of replay identity. Neither checker accepts the declared leaf proposition as its expected extraction output; the runner compares independently constructed output with that proposition afterwards.

### How does it compose with current admission?

After manifest decoding and safe capture of the source/policy inputs, use this proposed semantic precedence and pin it with collision cases before implementation:

```text
source/manifest structural invalidity
  > existing policy-reject R8
  > certified-evidence R8
  > strict replay R13
  > duplicate-report group R9
  > core rejection or accepted result
```

Source/manifest syntax and duplicate declarations are exit 2 with empty stdout. Capture or integrity failure of a package-global input (the manifest, `PAPER.md`, the source, or the package policy) is also exit 2. Today an unreadable policy file is a decode-boundary exit 2 (`app/Main.hs`), and nothing has been checked yet that a rejection could be attributed to. Capture, integrity, or extraction failure of an *evidence object* is R8, exit 1 with empty stdout and one located deterministic diagnostic. On the existing `.lara` doors, which have no evidence context, a certified leaf is R8 at its declaration: this is the spec §10.1 R8 row ("`certified` leaf without a listed checker witness"), now enforced. It is not a source-syntax error. Because source invalidity precedes R8, a fixture that already rejects earlier keeps its current outcome. Keep the existing policy-reject selection in source order. For evidence, first validate all request/provenance and allowlist/registry bindings in leaf order; then capture evidence objects and select any integrity failure in manifest order; then replay requests in leaf order, checking reference membership, extraction and proposition equality. A package-global failure identifies its object instead of inventing a leaf location. No core evaluation or accepted report occurs after an admission failure.

Preserve replay-identity construction errors as source invalidity; they are distinct from runtime strict replay R13. Add an evidence-specific case to the outer source rejection sum instead of inventing a matched policy row to fit today's `SourceRejected AdmissionRejection`. A package cannot parse or check untrusted source bytes before safely capturing them: manifest/source/policy capture failures are package-global prerequisites and precede semantic policy decisions. After those inputs are captured, policy R8 precedes evidence-object integrity and extraction failures. Pin both cases in tests rather than claiming all IO can be postponed until after policy lookup.

Validate every declared certified leaf after the earlier rejecting boundaries, including unused leaves and leaves later quarantined by policy or group handling. This prevents quarantine from hiding a broken certification assertion. After successful evidence validation, reuse the existing policy/group combined prune exactly once. Compute group consistency over full declared leaves as today. Do not treat successful certification as policy admission and do not extend the prune with a new byte-evidence quarantine seed.

The sealed evidence result binds the captured inputs, normalized requests, per-leaf results, and the existing opaque source carrier. `Gamma`, kept arguments, kept attacks, holes, and blocked reporting remain projections of that carrier. A replay receipt loaded from disk is data to compare, never authority to bypass the checker.

The enforcement point is public `prepareSource`, not only `loadSource` or the new CLI command. Separate structurally validated but untrusted input from an exportable accepted carrier. A witness-free call must fail on certified declarations; a checked call must consume a sealed evidence result bound to that exact semantic source and policy. Neither `preparedCheckInput` nor `sourceResultCheckInput` may bypass this check. Raw export intentionally discards evidence assurance and remains labeled declared. Preserve map contract-before-admission precedence by comparing parsed member contracts before promoting a member to an accepted source carrier.

### How is replay reported?

Add a separately versioned evidence identity around the existing core replay identity. Include the evidence format version, manifest digest, source digest, policy digest and origin, checker identities, normalized payloads, and the canonical dependency-report digest. The runner builds the dependency report from each request's declared object list, never from checker-supplied output. It records identifiers, paths, digests, and lengths, without copying file contents into every leaf judgment. Every object passed to a checker is recorded, including objects that only affect row or pointer selection and not the returned value.

Report checked leaf identifiers and declared leaf identifiers separately. A package with both kinds must not be labeled as if every premise were checked. Existing core verdict bytes remain a component of the report, not a rewritten core codec. Reports must distinguish a failed certification from an accepted source whose public claim is `evidence-blocked` because of existing quarantine rules.

Expose `lara check-ara ROOT [--policy FILE] [--out DIR]` as the package entry point. Its `--out` names a report *directory*, unlike `lara check --out <path>`, which writes one verdict file; keep the two documented separately. Existing `.lara` source entry points reject certified declarations without an evidence context; raw `.sexp` inputs still check conditionally and cannot mint evidence assurance. Audit map, possible-world, and library callers so none silently erases the new source requirement. The default command emits a combined report to stdout only after checking finishes. When `--out` is supplied, publish the complete report bundle through a temporary sibling directory and an atomic rename; reject an existing destination instead of overwriting an immutable run.

`src/Lara/ExpectedJson.hs` currently recomputes exportable source results through the raw checker; update it to preserve evidence metadata from the sealed source result. The corpus accounting loaders in `src/Lara/ClaimSupport/Load.hs` and `src/Lara/MechReview/Load.hs` use structural internal elaboration; their raw-core reports remain explicitly evidence-declared, not package-certified. Existing `.Internal` modules and raw `Unit` constructors are low-level escape hatches, so do not advertise whole-library unforgeability. Keep the new successful-evidence constructor out of exposed modules.

## Do we introduce new metatheory?

Yes: an admission calculus and composition results. No new defeat relation, support inference rule, or fifth core status is needed. New theorems must describe a real boundary used by the executable path, not just prove that a record contains a field named `witness`.

Let `S` be a finite immutable object snapshot, `PiE` the evidence policy, `P` the ordered semantic source declarations, `W(l)` the typed extraction request for leaf `l`, and `R` the closed checker registry. Let `deps(W(l))` be the request's declared object list, and let `run(S, R, W(l))` look up exactly `deps(W(l))` in `S`. It then applies the registry's pure checker to those bytes and returns either an error or an independently extracted proposition with its dependency report. Define `EAdmit(S, PiE, R, P) = ok J` to require that every certified leaf has an approved successful run whose normalized proposition equals the declared one. `J` is not an independently supplied premise; prove that the executable admission function constructs it only through those checks.

| Proof obligation | Required statement | Limit |
| --- | --- | --- |
| Admission characterization | Executable admission succeeds iff the declarative evidence judgment holds, with the same normalized propositions and ordered diagnostics | Prove both directions; do not define the judgment as equality with the executable function |
| No unsupported certified leaves | Every declared certified leaf after successful evidence admission has a matching approved request, a successful checker run, and package-member dependencies; retained certified leaves inherit this guarantee | Includes unused and later-quarantined declarations; ordinary declared leaves intentionally remain possible |
| Dependency confinement | The dependency report of every run equals the request's declared objects; every reported object resolves to a snapshot member with the recorded length and digest metadata; a missing declared object yields the located R8 error, not a partial run | Holds for the runner model; the Haskell checker signature (pure bytes in, no IO) is the conformance counterpart |
| Dependency-local replay | With the same source, policy, registry, payload and membership metadata, snapshots equal on the declared objects of every request reproduce the same admission result and dependency report, including failures | Does not say that equal SHA-256 strings imply equal bytes as a Lean theorem |
| Determinism | Fixed snapshot, source, policy and registry yield identical admission outcome, first error and canonical evidence report | Excludes live filesystem changes before capture |
| Successful-check conservativity | If evidence validation succeeds and the ordinary source input is unchanged, the retained core unit, holes, attacks, and conditional verdict equal those obtained by the existing policy/group pipeline | Does not upgrade a conditional verdict to empirical truth |
| Registry replacement | Registries with the same per-request results on this input produce the same evidence result and core observation | Equal propositions alone do not imply equal replay identities, which also name checker versions |
| End-to-end composition | Successful package checking yields both the evidence judgments for retained certified leaves and the existing checked-source/core guarantees | Filesystem capture and concrete byte-decoder refinement assumptions must appear explicitly |

Prove confinement and replay over the modeled runner and the whole admission pass, by induction over the ordered leaf requests, so the statements also cover first-error selection and the leaf-order/manifest-order failure precedence. Hiding a Haskell constructor without modeling the runner does not prove these properties. Static dependencies make the per-request step easy on purpose. The substantive results are admission characterization, conservativity, and end-to-end composition; do not inflate the confinement lemma into a headline. If a later family needs data-dependent reads, it brings a restricted read-program model and a trace-completeness theorem in its own plan.

Reuse existing policy/group prune and conservative reporting theorems instead of reproving argumentation semantics. Keep holes in the statements: accepted programs may contain incomplete source arguments whose mandatory questions are reported as located holes. The historical gated sketch's claim that every accepted argument has an empty obligation set is no longer valid. Likewise, deleting evidence can improve a conditional grounded status by removing an attacker; do not claim status monotonicity. Reuse the directed `evidence-blocked` rule.

| Existing result | Reuse in the new composition proof | Do not claim |
| --- | --- | --- |
| `Lara.Admission.accepted_checked_context_exact` | Identify the retained leaf context from the validated policy/group prune | That it already verifies artifact hashes |
| `Lara.Admission.prune_gamma_agree` | Reuse equality of declared and checked leaf meanings on retained terms | Equality on removed dependencies |
| `Lara.Admission.source_justified_nonpromotion` | Derive unblocked public justified safety in the declared reference framework from actual source/core success | Monotonicity of all four statuses under arbitrary evidence deletion |
| `Lara.Surface.elaborate_preserves` | Preserve checked source elaboration, complete nodes and holes | Complete byte-parser, IO or replay correctness |
| `Lara.Check.Unit.CheckUnitSound.holes_iff` and `hole_reports_exact` | Preserve the exact located-hole partition and reports | That every accepted declaration has discharged all mandatory questions |

Add a named composition corollary applying `source_justified_nonpromotion` to the evidence-checked source result, with its actual query-membership and unblocked-query premises. This supplies the useful non-definitional safety connection; a successful-gate projection identity alone is not a novelty result.

Lean proves the finite snapshot/runner/admission model and composition. SHA-256 collision resistance, safe OS file capture, the compiler/runtime, and any unverified concrete TSV/JSON parser remain in the trusted computing base. Add an independent Lean model of typed row/pointer selection and exact term decoding; Haskell/Lean differential tests are conformance evidence, not a proof that the Haskell byte parsers implement that model. Report this distinction in the theory note and user-facing guarantee.

## Alternatives considered

A documentation-only resolution would make the current limitation explicit but would not implement the approved guarantee. A name-and-reference presence check would accept a fabricated result behind plausible metadata. Putting witnesses into the core `Unit` would force a core-wire migration while giving the argumentation calculus no useful new information. General external-URL resolution, arbitrary extractor plugins, and an evidence-specific quarantine lattice add scope not needed for the approved fail-closed boundary.

## Tradeoffs

Self-contained packages cost storage and may exclude private or unredistributable evidence. Such material can remain declared evidence, but cannot be certified under this checking profile. Hash pinning detects changes relative to an accepted manifest; it does not authenticate who created that manifest. Requiring replay for unused or quarantined certified leaves is stricter than checking only load-bearing evidence, but prevents an accepted package from carrying unchecked certification assertions.

The original inventory and promotion gates still apply. A functional implementation can be useful bounded tooling without being a new paper-level contribution. Claiming a contribution additionally requires the frozen semantic-faithfulness protocol, honest trust accounting, real-package evaluation, and a non-definitional composition theorem used by the implementation.

## Migration

This plan targets a source syntax increment (`lara-syntax@0.11`), a new independently versioned evidence layer (`lara-evidence@0.1`), and a new package-report format, while preserving `lara-core@0.3`. Do not promise byte-identical combined reports or unchanged source acceptance. Test-only synthetic packages may exercise errors but never count toward the original-output gate.

Raw `.sexp` inputs (including `examples/S*/example.core.sexp`, `fixtures/admission/`, and `fixtures/mutants/`) are unaffected. At planning time, exactly seven `.lara` sources declare `kind = certified`, all under `fixtures/surface/`:

| Fixture | Today | After, on a door without evidence context |
| --- | --- | --- |
| `ambiguous-premise-reject.lara`, `attack-path-reject.lara`, `capture-reject.lara` | Source rejection | Unchanged: source invalidity precedes R8 |
| `all-forms.lara`, `nd-alpha-left.lara`, `nd-alpha-right.lara` | Accepted | R8 unless migrated |
| `admission-prune-open.lara` | Accepted, with `(certified, user)` quarantined by policy | R8 unless migrated; certification is its subject |

Re-run this inventory at Task 1, since the list may have grown. Decide each accepting fixture individually and record the decision in the conformance manifest. Where `certified` is incidental to what the fixture tests (the `nd-alpha` pair, and probably `all-forms` apart from its kind coverage), changing the kind is allowed, provided a new evidence fixture covers the certified path the old one exercised. Where certification is the subject (`admission-prune-open`, the quarantined-certified case), give the fixture a synthetic test package so the "validate even when quarantined" rule is exercised. No bulk relabeling, and no relabeling without a recorded rationale. The Lean surface checker must produce the same R8 on the same fixtures.

Keep the old frozen measurements as historical declared-evidence results. Budget an additive evidence-admission evaluation, new R8 rejection anchors, and a freeze update when source expectations or measured inputs change. Do not silently regenerate the existing snapshot or claim its core Haskell/Lean agreement establishes evidence correctness. Any deferred actionable work stays in issue #8 or a linked GitHub issue, not only in this plan.

## Implementation tasks

### Task 0: Establish the original-output inventory and approve the concrete contract

**Read:** `docs/evidence-admission-decision.md`, `docs/evidence-admission-gated-tasks.md`, `docs/corpus-map.md`, `.gitmodules`, and original ARA packages. **Create:** `docs/evidence-admission-inventory.md` as the durable gate result and package/leaf mapping; place the two inventoried packages at `examples/certified-evidence/package-a/` and `examples/certified-evidence/package-b/`, recording their original names and origins. Do not add evidence runtime modules in this task.

- [ ] Initialize the existing corpus submodule, then inspect original outputs rather than only Lara lowerings. Acquire original outputs from documented origins when permitted, keeping the acquired bytes in the candidate ARA package.
- [ ] Record package/revision, package-local file, hash, origin/license, leaf identifier, claim family, checker family, extraction selector, and normalized expected proposition for each candidate. Identify at least two independently produced packages, ten leaves, two claim families, and two deterministic checker families.
- [ ] Record each candidate package's total size and largest object. Committed packages must be ordinary Git blobs, because Git LFS pointers are rejected by design. Prefer outputs that keep each `examples/certified-evidence/` package within a stated budget (proposed: 5 MiB per package), and raise the budget explicitly in the inventory record rather than trimming original bytes.
- [ ] Demonstrate candidate extractions with a throwaway script against original bytes. Check precise values and propositions, not just file counts. If TSV/JSON are not represented, record failure and revise the portfolio against actual data before implementation.
- [ ] Freeze the concrete syntax, numeric bounds, manifest canonicalization, first-error precedence, per-class exit codes, policy-origin semantics, report schema and all public-door behavior in the existing evidence decision record. Obtain review of this contract. If the inventory fails, record the failure on issue #8 and stop implementation without declaring the issue fixed.

```sh
git submodule update --init corpus/ara-paperbench
```

Expected: the source corpus is available for inspection. This command alone does not establish the inventory gate. A valid gate record includes reproducible extraction evidence; no gate pass is claimed by this plan.

**Execution checkpoint (2026-10-06):** The [inventory](../docs/evidence-admission-inventory.md) did not establish the required original-output coverage. The available question JSON is prose, reconstructed evidence is Markdown, and candidate row data is CSV rather than original TSV. No synthetic success package was substituted. Runtime Tasks 1 through 7 are blocked; remaining Task 0 work is original-output acquisition, any inventory-backed portfolio revision, and review of the concrete contract. This checkpoint does not freeze syntax, numeric bounds, manifests or report codecs. The Task 0 checkboxes remain open because none of their full acceptance conditions was met.

### Task 1: Define the source-only contract and its Lean model

**Modify:** `src/Lara/AST.hs`, `src/Lara/Syntax.hs`, `src/Lara/Elaborate.hs`, `src/Lara/Source/Load.hs`, `lean/Lara/Presentation.lean`, `lean/Lara/Surface/Elaborate.lean`, `lean/Lara/Surface/Check.lean`, `lean/Lara/Surface/Correctness.lean`, `test/SyntaxSpec.hs`, `test/SurfaceConformanceSpec.hs`, `scripts/surface-conformance.hs`, and `docs/lara-surface-grammar.md`. **Create:** `src/Lara/Evidence/Types.hs`, `src/Lara/Evidence/Syntax.hs`, `lean/Lara/Evidence/Types.lean`. Extend presentation-only records; keep the core-reachable projection unchanged.

- [ ] Add typed presentation-policy allowlist entries and source-leaf extraction requests. Use language-server references to enumerate constructors and exported-signature callers before editing them. Hide successful-judgment and validated-path constructors; keep fixed tag spellings in one parse/render table per vocabulary.
- [ ] Add focused parser/decoder regressions for duplicate leaf requests, unknown leaves, malformed selectors, duplicate allowlist entries and provenance disagreement. Separate malformed syntax from semantic R8 certification failures.
- [ ] Migrate every presentation constructor and source consumer to the extended records and make omission of evidence context explicit. Do not retain an unchecked source-certification alias.
- [ ] Mirror the symbolic types and source well-formedness judgment in Lean. Prove round-trip/uniqueness properties for the frozen symbolic boundary and register every new theorem in `lean/AxCheck.lean`.
- [ ] Update source grammar, printer, presentation-shape witnesses and source conformance cases together. Preserve old non-certified source behavior.

```sh
make presentation-parity surface-conformance
```

Expected after this task: source representations agree; malformed witness declarations fail at the documented boundary; the raw core schema has not changed.

### Task 2: Capture an immutable ARA package safely

**Create:** `src/Lara/Evidence/Manifest.hs`, `src/Lara/Evidence/Snapshot.hs`, `test/EvidenceSnapshotSpec.hs`, and `fixtures/evidence/` package fixtures. **Modify:** `lara.cabal` and `test/Spec.hs`. Add a maintained raw-byte SHA-256 library dependency; current Git blob hashing in `Lara.BindingAudit` is not raw-file SHA-256.

- [ ] Implement the versioned S-expression manifest decoder, canonical encoder, distinct typed IDs and duplicate/path checks. Keep manifest metadata separate from captured bytes.
- [ ] Implement descriptor-relative package traversal with no symlink following and regular-file checks. Hash and decode the same captured bytes; do not validate a path and later reopen it for extraction.
- [ ] Reuse source-loader error and byte-IO patterns, not `canonicalPathKey` as a security check. Map paths deliberately permit aliases and parent-relative spellings; do not globally tighten unrelated map loading to implement ARA evidence confinement.
- [ ] Add temporary-directory tests for file replacement, changed bytes, missing files, duplicate paths/IDs, traversal, intermediate/final symlinks, directory/device entries and unresolved pointer content. No test depends on a real external file or network.
- [ ] Exercise the actual capture function on a copied candidate ARA, then change a listed file and observe the integrity failure. Remove throwaway capture scripts after recording the result.

### Task 3: Implement the dependency-confined runner and prove replay properties

**Create:** `src/Lara/Evidence/Runner.hs`, `src/Lara/Evidence/Registry.hs`, package-private `src/Lara/Evidence/Internal.hs`, `lean/Lara/Evidence/Runner.lean`, and `test/EvidenceRunnerSpec.hs`. **Modify:** `lean/AxCheck.lean`, `lean/Lara.lean`, `lara.cabal`, `test/Spec.hs`. List the successful-judgment implementation in library `other-modules`, not `exposed-modules`; tests exercise the public smart boundary instead of forging successful receipts.

- [ ] Implement the runner over the captured snapshot. The closed registry maps each checker identity to a pure function from the declared objects' captured bytes and the typed payload to a result, never an IO callback. The runner owns object lookup, the dependency report, the approved-checker check, and normalized output comparison.
- [ ] Create a sealed successful judgment only after every check succeeds. Evidence consumers receive projections, never a public constructor or a constructor accepting an author-supplied success flag.
- [ ] Test dependency locality: changing a declared object's bytes must change its recorded digest and the result (an integrity failure, or a different extraction under a regenerated manifest), while changing an undeclared manifest object must leave every leaf's extraction and dependency report unchanged. Do not confuse stable extraction with stable whole-manifest identity.
- [ ] Prove dependency confinement, snapshot membership, determinism and dependency-local replay over the admission pass. Cover failure paths and first-error selection, not only successful runs.

```sh
make lean-build axiom-audit
```

Expected after this task: the runner's abstract guarantees are mechanized, with no parser/filesystem correctness claim hidden inside them.

### Task 4: Implement the inventory-backed extraction families

**Create:** `src/Lara/Evidence/TSV.hs`, `src/Lara/Evidence/JSON.hs`, `lean/Lara/Evidence/Extract.lean`, `test/EvidenceExtractSpec.hs`. **Reuse:** `src/Lara/Strict/Cell.hs`, proposition normalization and existing term codecs rather than a second numeric semantics.

- [ ] Implement the Task 0-frozen TSV and JSON byte grammars and typed selectors. Construct output independently from the leaf being checked.
- [ ] Keep numbers exact through byte decoding, field mapping, normalization and comparison. Test exponent/trailing-zero normalization, negative zero, declared size bounds, wrong scalar types and unsupported rational spellings.
- [ ] Cover a unique selected row, duplicate matching rows, duplicate JSON keys, missing columns/pointers, swapped selector order and wrong output predicate. Expected outcomes must name the extracted proposition or the precise rejection class.
- [ ] Define and prove the row/pointer selection relations in Lean, including unique-selection and exact construction of the normalized proposition. State explicitly that byte-decoder refinement remains a conformance obligation unless separately proved.
- [ ] Re-run the original-output extractions through the real Haskell runner and compare exact propositions with the gate record. Synthetic success fixtures cannot replace this check.

### Task 5: Integrate admission without a source bypass

**Modify:** `src/Lara/Admission/Internal.hs`, `src/Lara/Elaborate.hs`, `src/Lara/Elaborate/Internal.hs`, `src/Lara/Source/Load.hs`, `src/Lara/Map/Load.hs`, `src/Lara/PW/Run.hs`, `src/Lara/ExpectedJson.hs`, `app/Main.hs`, `test/AdmissionSpec.hs`, `test/ElaborateSpec.hs`, `test/MapLoadSpec.hs`, `test/CliSpec.hs`. **Create:** `src/Lara/Evidence/Admission.hs`, `lean/Lara/Evidence/Admission.lean`, `lean/Lara/Evidence/Composition.lean`, `test/EvidenceAdmissionSpec.hs`. Reuse `src/Lara/Driver/Internal.hs` unchanged unless the sealed source interface requires a signature adjustment; do not add byte IO to the core driver.

- [ ] Add evidence preparation to the source boundary and bind its result to the existing opaque source carrier. Reject certified source declarations on any path that lacks the required context; keep conditional raw-core checking distinct.
- [ ] Implement the frozen precedence. Add collisions for policy reject plus broken evidence, evidence failure plus strict replay failure, evidence failure plus group reject, and malformed source plus all later errors.
- [ ] Check unused and policy-quarantined certified leaves; successful checking must not admit a policy-quarantined leaf. Reuse one existing combined prune and the directed blocked-report computation.
- [ ] Prove executable/declarative admission equivalence, replay coverage for all declared certified leaves, successful-check conservativity, registry replacement and end-to-end composition. Derive public justified safety using `source_justified_nonpromotion`, with its explicit query and unblocked premises; preserve the existing located-hole partition.
- [ ] Update every source-level caller and fixture affected by the fields or capability signature. Map and possible-world `.lara` loaders must explicitly reject certified members when no ARA context is supplied, including paths that call `preparedCheckInput` without `runSourceCheck`. Preserve their current contract-first error ordering. This plan does not add an evidence identity to the composite wire formats; raw exports from successfully checked packages remain conditional declared-evidence inputs.
- [ ] Migrate direct source callers in `src/Lara/RunningExample.hs`, `scripts/check-corpus-unit.hs`, `scripts/gen-corpus-units.hs`, `scripts/gen-worked-examples.hs`, `scripts/surface-conformance.hs`, and all language-server references to `prepareSource`. Cover both raw-export projections and `deps` in actual CLI cases.
- [ ] Keep `src/Lara/ClaimSupport/Load.hs` and `src/Lara/MechReview/Load.hs` explicitly scoped to raw declared-evidence accounting. If a report consumes the new package result, route it through the sealed result renderer rather than its structural elaboration shortcut. Update associated consumer-visible assurance tests; do not relabel existing raw fixtures as byte-verified.

### Task 6: Ship the package command, identity and honest reports

**Create:** `src/Lara/Evidence/Load.hs`, `src/Lara/Evidence/Report.hs`, `test/EvidenceReportSpec.hs`, `test/evidence-cli.sh`. **Modify:** `app/Main.hs`, `src/Lara/ExpectedJson.hs`, `test/ReportingSpec.hs`, `test/CliSpec.hs`, `test/Spec.hs`, `scripts/replay.sh`, and `bundles/README.md` where the package replay mode is exposed.

- [ ] Implement `lara check-ara ROOT [--policy FILE] [--out DIR]`. The source always comes from the checking manifest; the policy comes from the manifest unless `--policy` supplies a verifier policy, and the policy's origin is recorded. Test that both origins appear in the report and evidence identity, and that a verifier policy which drops a checker from the allowlist turns an otherwise-passing package into R8. Pass one sealed evidence/source result to all output renderers; never infer evidence success by rerunning the raw core.
- [ ] Encode evidence identity separately from the unchanged core replay tuple. Include normalized payloads and every logged dependency; never accept an old receipt as proof of a fresh check.
- [ ] Report exact checked/declared leaf partitions and preserve public `evidence-blocked` overlays. Add mixed-evidence and all-declared cases that cannot receive an all-evidence-checked assurance label.
- [ ] Make persisted outputs transactional. Test failure before/after extraction, pre-existing destinations, and replay of a modified input without leaving an accepted partial artifact.
- [ ] Run the actual command on the original-output packages and tampered copies. Check stdout, stderr, exit status and persisted files, not merely a mocked runner return value.

```sh
cabal run lara -- check-ara examples/certified-evidence/package-a
cabal run lara -- check-ara examples/certified-evidence/package-b
```

These package paths are populated from original outputs by Task 0, not by synthetic assertion files. Expected after implementation: success only when every declared certified leaf passes; a changed measured value, missing file or wrong selector produces the frozen R8 behavior and no accepted report.

### Task 7: Cross-check, evaluate and complete the cutover

**Create:** `lean/Lara/EvidenceDriver.lean`, `scripts/evidence-differential.hs`, `scripts/evidence-differential.sh`, `docs/theory-evidence-admission.md`. **Modify:** `lean/lakefile.toml`, `lean/AxCheck.lean`, `Makefile`, `scripts/admission-differential.sh`, `docs/spec.md`, `docs/rejection-surface.md`, `docs/evidence-admission-decision.md`, `docs/evidence-admission-gated-tasks.md`, `docs/m5-freeze-checklist.md`, `docs/README.md`, `README.md` and fixture/measurement manifests affected by the cutover.

- [ ] Add an executable Lean evidence driver over finite snapshots and typed payloads, with a versioned test codec. Compare normalized propositions, first errors, dependency reports and retained source projections byte-for-byte with Haskell. Keep byte-parser tests separate from the typed-model differential.
- [ ] Add `evidence-differential` to `make cross-check`; retain admission/core/map/possible-world gates. Extend the admission differential with composition and precedence fixtures rather than treating the new gate as a replacement.
- [ ] Exercise original-byte mutation, manifest digest/length changes, checker/version changes, payload selectors, duplicate selections, leaf proposition changes, an added declared dependency, and package-versus-verifier policy origin. Every case has a specified consumer-visible rejection or dependency change.
- [ ] Compare the declared baseline with package-checked runs without claiming scientific truth. Reuse existing quarantine examples to ensure no favorable conditional status caused by deletion escapes as an unqualified public status. Record two-annotator faithfulness review and the implementation's trusted base before claiming a paper-level contribution.
- [ ] Add an R8 anchor and budget the measured-input/report freeze change explicitly. Keep prior core measurements readable as historical results; never edit their meaning retroactively.
- [ ] Remove obsolete unchecked source entry points and old certification claims. Update the spec's unenforced-witness note only after the runtime, tests and proofs land. Preserve the historical gated sketch as history with a pointer to the implemented contract.

```sh
cabal build all
cabal test all --test-show-details=direct
make local-gates
bash test/evidence-cli.sh
```

Expected at the final checkpoint: builds, all existing tests, all Lean/axiom/cross-language gates, and the real package-command smoke cases pass. `make local-gates` is mandatory before review because this work changes Lean and versioned source/report contracts. The required GitHub Haskell workflow alone is insufficient.

## Acceptance checklist

- [ ] The recorded original-output inventory passes; all certified evidence bytes are packaged in ARA.
- [ ] Policy-approved, implemented checker/version plus actual matching extraction is required, not a witness string alone.
- [ ] Missing, unsafe, altered or mismatching evidence fails deterministically, with no silent downgrade or source-API bypass.
- [ ] Existing policy/group quarantine and directed public blocking remain intact; successful evidence replay never overrides them.
- [ ] Mixed and raw-core inputs cannot claim stronger assurance than they received.
- [ ] Replay identifies source, policy (with its origin), mappings, registry versions and every declared evidence object.
- [ ] New admission/runner/composition theorems are executable-model-linked, axiom-audited and honest about trusted byte parsers, cryptography and OS capture.
- [ ] Core wire, argumentation semantics, located-hole behavior and existing strict-backend guarantees remain unchanged.
- [ ] Real-package command smoke, tamper regressions, differentials and `make local-gates` pass; docs and freeze records describe the measured scope.

## Next Steps

Resume the remaining Task 0 work from the [inventory](../docs/evidence-admission-inventory.md) and issue #8. Acquire traceable original outputs and review any format-driven portfolio change, then demonstrate the gate and review the concrete contract before runtime edits. Tasks 1 through 7 and the acceptance checklist remain open. Do not close issue #8 or delete this partially executed plan until the certified source path is enforced end to end. The Task 0 outcome is documented; no implementation, Lean or package-command gate pass is claimed.
