# Evidence-admission design (`lara-evidence@0.1`)
**Date:** 2026-10-07

## TL;DR

`lara-evidence@0.1` checks that every declared certified leaf is the exact output of an approved, versioned checker over captured, hash-pinned package bytes and a pinned extraction request. The shipped package door preserves `lara-core@0.3`, existing policy/group quarantine, located holes and conditional argumentation semantics. The additive `evidence-measured-inputs@1` content freeze records package-door behavior; it is not a Git tag or a scientific-validity result. Astra independently judged all ten original-output mappings faithful, and the maintainer accepted that review. Source audit labels remain unreviewed, issue #20 still tracks applying the verdicts, re-pinning sources and publishing the next report/freeze and matching tag, and the accepted review does not satisfy the separate archival paper-promotion protocol.

## Problem

A leaf is a declared piece of evidence that may support a claim. Lara's argument checker decides what a leaf can support through support schemes, their critical questions and typed rebut, undercut and undermine attacks. Its raw core input supplies an evidence context, `Gamma`, without supplying artifact bytes. A core verdict therefore cannot establish that a declared measurement was actually extracted from the referenced output.

Evidence admission checks that earlier boundary. It captures the package bytes, runs a closed checker selected by a typed request and compares the constructed proposition with the declared leaf. The result composes with the existing source and argument checker. A malformed, altered or mismatching certified declaration rejects instead of silently becoming ordinary declared evidence.

## Constraints

The source language is `lara-syntax@0.11`, the evidence layer is independently versioned as `lara-evidence@0.1`, and the core wire remains `lara-core@0.3`. Evidence checking does not change the core codec, strict backends, four argument statuses, located holes or defeat rules. Trust tiers and manifest roles never become attacks. Quarantine means unavailable evidence, not false evidence, and cannot directly assign a core status.

Three limits apply to every assurance label: admission does not prove a proposition true in the world; admission does not prove that the proposition supports a downstream claim; and a justified grounded status does not strengthen extractor soundness or policy adequacy. A justified status remains relative to the supplied evidence context and trusted registry. Neither byte replay nor the accepted mapping review validates the producers' experiments or establishes scientific truth.

This layer does not reproduce RIT's full Claim Flow Graph, replace schemes and attacks with Lean arithmetic, add dynamic checker plugins or arbitrary shell extractors, or infer scientific meaning from column names. Goal/attempt history and registration receipts stay outside the calculus and this versioned layer, as specified in the [registration-receipt contract](registration-receipt-contract.md). Git order and local timestamps do not establish preregistration. A bespoke registration service would require a demonstrated gap in existing systems.

## Proposed approach

The shipped design uses immutable capture, typed request binding and a rejecting evidence check before the existing source continuation. Each request declares its complete dependencies before replay. The runner constructs dependency metadata from that list; extractors receive only the captured objects and cannot perform IO. Existing policy and group quarantine still use their single combined prune and directed public `evidence-blocked` overlay.

### Concrete package contract

`lara check-ara ROOT [--policy FILE] [--out DIR]` checks an explicit package root with a canonical `lara-evidence.sexp` manifest. Result files used to certify a leaf must be package members; a prose assertion or external URL is insufficient. Original files may be copied into `evidence/` with their origins recorded, without claiming that ARA generated them. Capturing `PAPER.md` pins the accompanying document, not the complete upstream ARA or its scientific claims. The [corpus map](corpus-map.md) specifies the ARA-to-Lara mapping.

Every declared certified leaf must pass, including unused leaves and leaves later quarantined by ordinary policy/group handling. Certification requires safe capture, matching length and SHA-256 metadata, an implemented checker/version approved by policy, valid request binding and an independently constructed normalized proposition equal to the leaf. Assumptions and attestations remain declared evidence. Successful certification neither overrides policy rejection nor makes a quarantined leaf available, and it does not protect evidence from attacks.

A verifier policy supplied with `--policy` replaces the entire package policy for the run. It is captured and hashed once. Reports name the policy digest and its origin, `package` or `verifier`, so a package's own allowlist cannot claim verifier approval.

### Source requests and exact extraction

Presentation leaves accept at most one optional `extract` field, and presentation policies accept at most one exact checker/version allowlist field. The shipped forms are:

```text
extract = (csv-row 1 object-id
  (key "column" "exact raw key")
  (select ("column" decimal) ("column" text))
  (predicate pred))

extract = (json-pointer 1 object-id
  (select ("/cells/19/outputs/0/text/0" decimal-line))
  (predicate training_loss))

evidence-checkers = (checkers (csv-row 1) (json-pointer 1))
```

Checker and encoding vocabularies are closed sums. Identifiers, column names, JSON tokens, versions and digests have distinct types. Each v1 request family declares exactly one object. Its request must match the certified leaf's checker provenance, be approved by policy and resolve an existing leaf reference to the manifest object's path. Extraction on a noncertified leaf rejects at R8. Duplicate fields and duplicate allowlist entries are structural errors; unsupported versions and binding disagreements are R8 errors. The checker never receives the expected proposition. It constructs an ordered proposition from selected values, and the runner compares it with the once-expanded semantic leaf using existing normalization.

CSV is strict UTF-8 with comma-separated fields and a unique header row. An empty header name is allowed for the original Pandas index column. Records use LF or CRLF, with an optional final record ending. Quoted commas and record endings are preserved, and doubled quotes escape a quote. Bare CR outside quotes, unquoted quotes, trailing garbage after a quoted field, duplicate headers and ragged rows reject. The entire table is decoded before selecting exactly one row by its raw key field. Zero or multiple matches reject; there is no first-match or aggregation rule.

JSON is strict UTF-8 JSON, with duplicate keys rejected before a last-key-wins representation can erase them. Pointers decode RFC 6901 escapes into typed tokens. Array indices must be canonical nonnegative decimal integers; numeric object keys remain keys. `decimal` selects a JSON number, `text` selects a JSON string, and `decimal-line` selects a JSON string containing a decimal followed by exactly one LF. CSV accepts only `decimal` and `text`. There is no arbitrary whitespace stripping, null/boolean coercion, approximate comparison, aggregation, unit conversion or inferred ground-term decoding.

Decimals use `[+-]?[0-9]+(\.[0-9]+)?([eE][+-]?[0-9]+)?`. The mantissa is bounded at 256 digits. The exponent has at most three digits and absolute value at most 256. These bounds apply before integer parsing, exponentiation or padding. Normalization is exact in Lara's existing decimal representation, including scientific notation, trailing zeros and negative zero; it never uses binary floating point.

The resource bounds are 1 MiB per manifest, 8 MiB per object, 256 manifest objects and 16 MiB per requested snapshot. Both request families accept at most 256 selectors. CSV is bounded at 100000 rows and 256 columns. JSON is bounded at root-zero depth 128 and 100000 nodes: scalars and empty containers have depth zero and count as one node; nonempty containers add one to their deepest child's depth. The original notebook's long image strings remain subject to the same object-byte bound.

### Canonical manifest and immutable capture

The manifest's canonical UTF-8 encoding is `printSExpr` followed by exactly one LF:

```text
(lara-evidence 1
  (paper paper-id)
  (source source-id)
  (policy policy-id)
  (objects (object ID PATH LENGTH SHA256) ...))
```

Lengths are canonical decimal naturals. Digests are `sha256:` followed by 64 lowercase hexadecimal digits. Required global entries have distinct IDs and paths, and the paper path is exactly `PAPER.md`. Unknown, missing or duplicate fields, duplicate IDs/paths, unsafe path components, manifest/report self-references and noncanonical bytes reject. NUL anywhere in a path rejects before POSIX string conversion, with a defensive check in the capture shim. The source artifact's declared digest is independent of the enclosing manifest, avoiding a hash cycle.

Capture traverses paths relative to held directory descriptors without following symlinks, checks regular files and bounds reads. A nonblocking open prevents a FIFO from hanging before the regular-file check. Hashing and decoding use the same immutable bytes; checkers never reopen live paths. Global manifest, paper, source and package-policy capture precedes source parsing. After structural validation and policy rejection, bindings are checked in leaf order and requested evidence objects are captured in manifest order. Only captured dependencies receive byte assurance. Unrequested manifest entries are not certified package members.

A captured object is usable only under the manifest entry it was captured for. Snapshot lookup uses the object ID, so the promotion boundary also compares captured metadata with the request-declared entry through `Admission.captureRejection`. An object captured for different metadata under the same ID is insufficient. The package path builds its snapshot from the manifest's own entries, and recorded dependency metadata must equal the entry validated by binding. `EvidenceAdmissionSpec` pins this requirement at the public `admitSourceEvidence` boundary; the finite model expresses it through `Admitted.capture` and `CapturedValid`.

### Sealed types and source-door guarantees

`PackageResult`, `ObjectMeta`, `Manifest` and `BoundRequest` hide positional constructors and expose ordinary read-only projections. They do not export record labels, because labels would permit public record updates despite hidden constructors. Captured snapshots and successful judgments are sealed in the same way. Callers cannot replace a checked policy origin or leaf partition, exceed the metadata length bound, rewrite validated manifest relationships or change a bound request.

Evidence enforcement includes public `prepareSource`, its exportable projections and every source-level caller. Source doors without an evidence context reject certified declarations at R8, including declarations that policy would quarantine. Map contract comparison still precedes admission. Raw core `.sexp` checks remain conditional on supplied `Gamma` and cannot mint package assurance; raw exports intentionally discard that assurance. Result renderers consume the sealed accepted source result, not a fresh raw-core check.

Accepted source can contain located holes outside the argumentation framework. Admission decides which leaves reach the retained context; the core subsequently decides whether a submitted argument is complete. A quarantined hole is pruned with its dependent argument and is never reported as a hole. Existing policy/group quarantine produces the directed forward-reachability `evidence-blocked` public overlay specified in [the source specification](spec.md) §4.3 and [policy-admission decision](policy-admission-calculus-decision.md). It does not use undirected connected components, create an evidence attack or silently publish a status improved by deletion.

### Error precedence and rejection output

The boundaries run in the following order. An evidence-rejected source never proceeds to the core checker.

1. Global capture, manifest and structural/source invalidity, including replay-identity construction errors: exit 2.
2. Existing policy R8.
3. Evidence binding R8, in leaf order.
4. Requested-object capture/integrity R8, in manifest order.
5. Extraction or proposition-mismatch R8, in leaf order.
6. Strict replay R13, group R9 and core outcomes.

Source and policy capture are prerequisites to semantic policy decisions. Policy R8 therefore wins over broken evidence bytes. An evidence-object failure exits 1 and is located at the earliest referencing leaf. The typed rejection names an artifact only for an artifact-located failure: capture names the object it failed to capture, while extraction is leaf-located and carries `none`. The typed [model corpus](../fixtures/evidence/model/MANIFEST.tsv) fixes that encoding; the CLI rendering reports the leaf and reason, not the offending object ID. Every R8 emits empty stdout and no output bundle. Certified-evidence failure rejects; it does not add an evidence-quarantine outcome.

### Report identity and atomic publication

The canonical `lara-evidence-report 1` envelope carries the unchanged core verdict, separate core and evidence identities, exact checked/declared leaf partitions, normalized requests and checker versions, and runner-owned object metadata. The evidence digest covers format versions, manifest/source hashes, policy hash and origin, the core replay tuple, normalized requests, and the canonical dependency-report digest and metadata. It excludes its own digest. Core replay identity is unchanged and remains separate from evidence identity.

Assurance is `evidence-checked` when the checked partition is nonempty and there are no declared leaves, `mixed` when both partitions are nonempty, and `evidence-declared` when no leaves are checked. Availability remains a separate matter: an evidence-checked leaf can still be quarantined under ordinary policy/group handling. A raw `.sexp` verdict is evidence-declared and relative to its supplied context; it cannot claim full byte-evidence checking.

The command emits an accepted report only after the complete source/core check. Requested output consists of `report.sexp` and `core-verdict.sexp`, written in a temporary sibling directory and published by atomic no-replace rename. Existing or racing destinations reject, and failure removes temporary output. Publication requires Linux `renameat2(RENAME_NOREPLACE)` or an equivalent supported primitive and fails closed if unavailable. There is no check-then-ordinary-rename fallback. Requested output publishes before accepted stdout. No stored receipt authorizes skipping fresh replay.

Source JSON retains ordinary claim support counts, hole counts, incomplete-alternative flags and argument names on grounded labels. These come from the accepted checker cache behind `SourceResult` projections, so rendering does not replay raw core. Replay-preflight rejection resolves argument indices against declarations; checker-stage rejection resolves them against the retained post-prune argument list.

### Verification and trusted assumptions

The finite Lean model proves executable/declarative admission equivalence, coverage of every declared certified leaf, exact checked partitions, typed scalar and ordered selection, unique CSV row selection, dependency confinement/locality, registry replacement, deterministic first errors and successful-check conservativity. The [theory note](theory-evidence-admission.md) maps these guarantees to their theorems and premises. Admission requires capture under the declared manifest entry as well as a successful runner result; equal digest strings alone do not establish locality, which requires equal complete lookup results, including errors, payloads and metadata.

Source composition derives ordinary elaboration, core acceptance, complete arguments, typed holes and resolved attacks for the same accepted source. It preserves the existing retained context and exact hole reports. `package_source_justified_nonpromotion` uses `source_justified_nonpromotion` with its actual query-membership and unblocked-query premises. This proves a conditional justified-status connection to the declared reference framework, not monotonicity of every status under arbitrary deletion. Acceptance does not imply that all submitted arguments are complete.

The proofs live in `lean/Lara/Evidence/` and are audited by `lean/AxCheck.lean`; they are `sorry`-free and restricted to `propext`, `Classical.choice` and `Quot.sound`. `concrete_admission_refinement` assumes agreement with the finite model rather than proving it. `TypedParserRefinement` states a decoder-to-typed-payload relation. Concrete CSV/JSON byte-parser refinement, filesystem capture, SHA-256 assumptions, the POSIX shim and compiler/runtime correctness remain trusted boundaries. The typed differential supplies conformance evidence, not proofs of these byte parsers or scientific interpretation.

The runtime gate is `test/evidence-cli.sh`, covering the real binary over copied original packages, mutations, precedence, no-evidence-context source doors and publication atomicity. `scripts/evidence-differential.sh` compares the typed Haskell/Lean model corpus. They are `evidence-cli` and `evidence-differential` members of `make cross-check` and `make local-gates`. The [theory note's verification section](theory-evidence-admission.md#how-can-the-implementation-and-proofs-be-checked) gives reproduction commands; the [CI scope decision](ci-scope-decision.md) distinguishes the Haskell workflow from required Lean and cross-language gates.

### Additive measurement and accepted independent review

`evidence-measured-inputs@1`, recorded on 2026-10-06, is an additive content freeze keyed by its identifier and corpus identity, not a Git tag. It neither re-measures nor amends `m5-freeze-*` snapshots, whose core results retain their declared-evidence interpretation. Its separate [freeze protocol](../measurements/frozen/evidence-measured-inputs-v1.md), [corpus manifest](../fixtures/evidence/measured/MANIFEST.tsv) and frozen JSON/TSV report hold the input and identity tables; they are not duplicated here.

`scripts/gen-evidence-measured.py` materializes six one-edit rejection packages from the committed quarantine fixture without changing original packages. `scripts/evidence-measure.py` runs the real package door over ten declared inputs: the two original packages, the quarantine fixture, an identical-verifier-policy run and those six rejections. It records observed classes, located leaf/reason, exits and stdout/stderr digests, and independently recomputes accepted report identities, dependencies, requests, partitions and assurance labels from package bytes. Both reported core replay IDs must equal the tuple derived from the source artifact digest and ordered backends, the effective policy ID and sorted theory digests, with `lara-core@0.3` enforced. Its `--check` compares deterministic report blocks and matching TSV, ignoring only the environment block. Generator `--check` checks regeneration of committed bytes. These are `evidence-measured` and `evidence-measured-test` cross-check members. This measures package capture, binding, extraction, identity and the core replay verdict, without rerunning an experiment or supplying a semantic verdict.

On 2026-10-07 the maintainer removed issue #20's human-only review requirement and accepted `openai-codex/gpt-6-astra`'s independent review: ten faithful verdicts, zero unfaithful and zero unclear. The [accepted review record](certified-evidence-human-review-worklist.md#accepted-independent-review) preserves reviewer identity, date, inspected source hashes and per-leaf rationale separately from the [maintainer's agreement](https://github.com/ARA-Labs/Lara/issues/20#issuecomment-6027990904). Independent agents or humans may perform this review under the [review instructions](certified-evidence-review-instructions.md). Agent verdicts are not human-authored verdicts, and the maintainer's acceptance is not a separate ten-leaf human audit.

The inspected sources still carry `author = ai_inventory`, `audit-status = unreviewed`. [Issue #20](https://github.com/ARA-Labs/Lara/issues/20) tracks applying the accepted verdicts, preserving authorship, updating rationales, re-pinning changed source entries, checking both packages and publishing the next additive report/freeze and matching tag. The first snapshot must remain unchanged. The accepted review does not strengthen `evidence-checked`, prove scientific truth or satisfy the archival paper-promotion gate below. The first freeze's historical human-only wording describes the policy at its recording date, not current issue #20 policy.

## Alternatives considered

The earlier design proposed dynamic access-logged checker reads and an `admit < quarantine < reject` outcome join. The shipped families declare their dependencies statically and reject certified-evidence failures. They do not implement that read-program sketch or add a byte-level quarantine outcome. Runner-owned dependency metadata remains required. The original sketch also used independent quarantine/retained-structure arguments and undirected blocking; the opaque source result, existing combined prune and directed public overlay supersede those choices.

Incomplete arguments were a separate core decision. Through `lara-core@0.2`, open mandatory obligations rejected with `PEIncompleteArgument`, and a gap meant no submitted argument. `lara-core@0.3` instead accepts such an argument as a located hole outside the argumentation framework, with a full core refreeze documented in the [located-gap decision](located-gap-decision.md). This was a core scope change, not an evidence-admission soundness requirement. The evidence layer neither restores the former rejection rule nor turns a pruned argument into a reported hole.

### Original-output inventory and portfolio revision

The historical implementation gate required at least two independently produced packages, ten certified leaves across at least two claim families, and two closed, deterministic, byte-addressed checker families. Failure would have left the layer unbuilt. The earlier roadmap closed the extension as not planned on 2026-08-26; issue #8 later authorized an inventory-backed portfolio revision and delivered the feature. That implementation prerequisite is satisfied, not pending work.

The `tsv-row@1` portfolio failed because available measured row outputs were original CSV rather than TSV. Reconstructed Markdown tables, question JSON with expected-result prose and hand-authored assertion files were insufficient witnesses. The revised [original-output inventory](evidence-admission-inventory.md) retains complete pinned CompoNet and Simformer files, original licenses and producer provenance. It supplies ten exact leaf assertions across two independently authored packages, three narrow claim families and the independently specified `csv-row@1` and `json-pointer@1` families. CSV was not converted to TSV, and the explicit `decimal-line` encoding accounts for original notebook output strings rather than an invented fixture. Saved positions from one notebook run are not independent experiments; runtime and loss records do not assert comparative superiority.

The inventory records original revisions, byte counts, hashes, license details and selectors. Each package has a 5 MiB budget and uses ordinary Git blobs, not Git LFS pointers; no original byte was trimmed to fit. Test-only synthetic packages exercise error paths and never count toward this gate. Independent capture/security and semantic/composition contract reviews required NUL rejection and atomic no-replace publication. A later security review closed the borrowed-capture gap with `Admission.captureRejection`, its runtime regression and the corresponding finite-model obligation.

### Archival paper-promotion gate

The historical gate below is preserved as an archival research constraint, not a current implementation plan or issue #20 acceptance policy. It restricted paper-level promotion beyond describing a bounded tooling extension. Astra's accepted mapping review and the additive package-door freeze do not satisfy or retire it. No paper-level promotion is claimed here.

The historical protocol required all of the following:

- Original outputs from at least two independently produced packages, ten certified leaves, two claim families and two closed checker families.
- Every declared tamper and incomplete-dependency mutant rejected or recorded before core checking.
- No quarantine-affected root receiving an unqualified public core status.
- Dependency reports sufficient to reproduce every admitted proposition exactly.
- Payload-to-result and proposition-to-result mappings passing a frozen two-annotator semantic-faithfulness protocol with no LLM judging.
- Byte-exact Haskell/Lean core behavior after admission.
- Honest reporting of the added trusted computing base and separate guarantees.
- At least one non-definitional composition/safety theorem used by implementation and evaluation.

It also required three measured treatments: the declared-leaf baseline with policy-admitted leaves trusted at the world boundary, a naïve-pruned diagnostic measuring label changes after deletion, and the conservative checked treatment blocking every quarantine-affected public root. A favorable label transition caused by naïve pruning was a hazard to detect, not a success. Failure left the contribution classified as bounded tooling or future work. These archival requirements do not imply that such measurements or the two-annotator review have been completed, and even semantic faithfulness would not prove scientific truth.

## Tradeoffs

Closed checkers and explicit dependencies keep replay deterministic and restrict what artifact input can execute. They cover exact CSV row selection and JSON pointer traversal without general aggregation, conversions or experiment reruns. Format strictness and resource limits reject inputs outside that scope. Adding a checker or changing its contract requires an independently versioned evidence-layer decision rather than a silent core-semantics change.

Immutable snapshots and exact metadata binding keep later path changes or borrowed captures from authorizing the wrong bytes. Atomic no-replace publication prevents accepted partial bundles. These guarantees still depend on OS capture, cryptography and runtime behavior. Typed proofs and byte-level runtime tests address different boundaries; neither can stand in for the other. Separate identities and audit records let readers distinguish package-byte checking, conditional argument status and review of a mapping's meaning.

## Migration

The canonical design is this file. `docs/evidence-admission-decision.md` and `docs/evidence-admission-gated-tasks.md` are retired without compatibility redirects. Their filenames may still occur in historical ARA records and must be interpreted at their historical revision. Historical records are not rewritten as new research events. The inventory, theory note, review procedure/record and frozen measurement protocol remain separate data, proof, audit and operational records.

Raw `.sexp` examples and admission/mutant fixtures are unaffected. Six certified declarations remain in surface fixtures whose subjects are rejections: `ambiguous-premise-reject.lara`, `attack-path-reject.lara` and `capture-reject.lara` retain structural failures before R8. The policy-quarantined certified fixture `admission-prune-open.lara` is recorded as `admission-prune-no-context`; its package replay coverage is supplied by `fixtures/evidence/quarantined`. Previously accepting fixtures `all-forms.lara`, `nd-alpha-left.lara` and `nd-alpha-right.lara` now use noncertified kinds (`observed`, `attested`, `assumed`) rather than depending on a missing evidence context. Each decision is recorded in `fixtures/surface/MANIFEST.tsv`, and `make surface-conformance` compares both runtimes with the golden over the whole manifest.

Core checker bytes, wire grammar, fixtures and proof claims retain their versioned meaning. New replay/report evaluations require an explicit additive refreeze instead of borrowing old measured assurance. Audit-label changes must preserve original producer bytes and the first measured snapshot, update the affected source pins and produce a new reproducible report before the next freeze or release tag.

## Next Steps

1. Apply the accepted issue #20 verdicts to source audit metadata, preserving `author = ai_inventory` and identifying the independent reviewer separately; update rationales and re-pin changed source entries.
2. Check both changed packages and reproduce the additive corpus/report before publishing its next freeze and matching tag. Preserve `evidence-measured-inputs@1` and resolve the remaining issue #20 acceptance criteria explicitly.
3. Keep runtime contract checks, typed-model conformance and the axiom audit aligned when evolving the evidence layer. Do not describe those gates or the accepted mapping review as parser soundness, empirical truth or completed paper-level promotion.
