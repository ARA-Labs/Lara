# Evidence and source admission (`lara-evidence@0.1`)

## TL;DR

`lara-evidence@0.1` checks that every declared certified leaf is the exact output of an approved, versioned checker over captured, hash-pinned package bytes and a pinned extraction request, and preserves `lara-core@0.3`, policy/group quarantine, located holes and conditional argumentation semantics. The same `.lara` source boundary applies the policy's `admission` table, deciding which declared leaves reach the core checker; quarantine means unavailable evidence, not false evidence, and never assigns a core status. The finite Lean model proves that a snapshot-and-typed-selection admission is equivalent to the executable runner and that a successful gate preserves ordinary source checking; concrete byte parsers, SHA-256, operating-system capture and compilers remain trusted. External registration receipts annotate provenance only and stay outside the calculus. Astra independently judged all ten original-output mappings faithful, the maintainer accepted that review and applied it to their audit metadata, and the additive `evidence-measured-inputs@2` freeze with its matching `evidence-measured-inputs-v2` tag records the checked packages; the first snapshot remains unchanged. These checks and the accepted review do not establish scientific validity or satisfy the separate archival paper-promotion protocol.

## Problem

A leaf is a declared piece of evidence that may support a claim. Lara's argument checker decides what a leaf can support through support schemes, their critical questions and typed rebut, undercut and undermine attacks. Its raw core input supplies an evidence context, `Gamma`, without supplying artifact bytes. A core verdict therefore cannot establish that a declared measurement was actually extracted from the referenced output.

Evidence admission checks that earlier boundary. It captures the package bytes, runs a closed checker selected by a typed request and compares the constructed proposition with the declared leaf. The result composes with the existing source and argument checker. A malformed, altered or mismatching certified declaration rejects instead of silently becoming ordinary declared evidence.

## Constraints

The source language is `lara-syntax@0.11`, the evidence layer is independently versioned as `lara-evidence@0.1`, and the core wire remains `lara-core@0.3`. Evidence checking does not change the core codec, strict backends, four argument statuses, located holes or defeat rules. Trust tiers and manifest roles never become attacks. Quarantine means unavailable evidence, not false evidence, and cannot directly assign a core status.

Three limits apply to every assurance label: admission does not prove a proposition true in the world; admission does not prove that the proposition supports a downstream claim; and a justified grounded status does not strengthen extractor soundness or policy adequacy. A justified status remains relative to the supplied evidence context and trusted registry. Neither byte replay nor the accepted mapping review validates the producers' experiments or establishes scientific truth.

This layer does not reproduce RIT's full Claim Flow Graph, replace schemes and attacks with Lean arithmetic, add dynamic checker plugins or arbitrary shell extractors, or infer scientific meaning from column names. Goal/attempt history and registration receipts stay outside the calculus and this versioned layer, as specified in [External registration receipts](#external-registration-receipts). Git order and local timestamps do not establish preregistration. A bespoke registration service would require a demonstrated gap in existing systems.

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

Accepted source can contain located holes outside the argumentation framework. Admission decides which leaves reach the retained context; the core subsequently decides whether a submitted argument is complete. A quarantined hole is pruned with its dependent argument and is never reported as a hole. Existing policy/group quarantine produces the directed forward-reachability `evidence-blocked` public overlay specified in [the source specification](spec.md) §4.3 and [Policy admission at the source boundary](#policy-admission-at-the-source-boundary). It does not use undirected connected components, create an evidence attack or silently publish a status improved by deletion.

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

### Additive measurement and accepted independent review

The current additive freeze is [`evidence-measured-inputs@2`](../measurements/frozen/evidence-measured-inputs-v2.md), recorded on 2026-10-07 and tagged `evidence-measured-inputs-v2`. It records the reviewed source bindings and updated source pins. The [first content freeze](../measurements/frozen/evidence-measured-inputs-v1.md), recorded on 2026-10-06 without a Git tag, remains unchanged. Neither freeze amends `m5-freeze-*` snapshots, whose core results retain their declared-evidence interpretation. The freeze records, [corpus manifest](../fixtures/evidence/measured/MANIFEST.tsv) and frozen JSON/TSV reports hold the input and identity tables; they are not duplicated here.

`scripts/gen-evidence-measured.py` materializes six one-edit rejection packages from the committed quarantine fixture without changing original packages. `scripts/evidence-measure.py` runs the real package door over ten declared inputs: the two original packages, the quarantine fixture, an identical-verifier-policy run and those six rejections. It records observed classes, located leaf/reason, exits and stdout/stderr digests, and independently recomputes accepted report identities, dependencies, requests, partitions and assurance labels from package bytes. Both reported core replay IDs must equal the tuple derived from the source artifact digest and ordered backends, the effective policy ID and sorted theory digests, with `lara-core@0.3` enforced. Its `--check` compares deterministic report blocks and matching TSV, ignoring only the environment block. Generator `--check` checks regeneration of committed bytes. These are `evidence-measured` and `evidence-measured-test` cross-check members. This measures package capture, binding, extraction, identity and the core replay verdict, without rerunning an experiment or supplying a semantic verdict.

On 2026-10-07 the maintainer removed issue #20's human-only review requirement and accepted `openai-codex/gpt-6-astra`'s independent review: ten faithful verdicts, zero unfaithful and zero unclear. The [accepted review record](certified-evidence-human-review-worklist.md#accepted-independent-review) preserves reviewer identity, date, inspected source hashes and per-leaf rationale separately from the [maintainer's agreement](https://github.com/ARA-Labs/Lara/issues/20#issuecomment-6027990904). Independent agents or humans may perform this review under the [review instructions](certified-evidence-review-instructions.md). Agent verdicts are not human-authored verdicts, and the maintainer's acceptance is not a separate ten-leaf human audit.

All ten bindings now carry `author = ai_inventory`, `audit-status = reviewed`, and a rationale naming the independent reviewer, review date and accepted review record. Both package manifests pin the changed source bytes. Their formal mappings, original producer/data bytes, core replay identities, verdicts and dependency digests remain unchanged. The [publication record](certified-evidence-human-review-worklist.md#published-reviewed-bindings) identifies the new source hashes separately from the inspected hashes. This completes the implementation and freeze work tracked by [issue #20](https://github.com/ARA-Labs/Lara/issues/20); closure follows merge. The accepted review does not strengthen `evidence-checked`, prove scientific truth or satisfy the archival paper-promotion gate below. The first freeze's human-only wording describes the policy at its recording date.

## What successful admission proves

A snapshot records immutable typed payloads and object metadata. A request names its dependencies, selector payload, checker and version. The pure registry constructs a proposition from those inputs without receiving the leaf's expected proposition; admission compares their normalized forms. The independent `Admitted` judgment requires valid request bindings, capture under the request-declared manifest entry, and replay of all declarations. `lean/Lara/Evidence/Admission.lean` proves that this judgment is equivalent to successful executable admission:

```text
admit snapshot policy manifest registry leaves = .ok judgments
  ↔ Admitted snapshot policy manifest registry leaves judgments
```

The scope is every declared certified leaf, including unused leaves and leaves later quarantined by ordinary policy or group handling. `all_declared_certified_witness` supplies an approved bound request, a successful runner result, equal normalized propositions and exact dependency metadata. `retained_certified_witness` carries that witness through any retained-leaf filter. `checked_partition_exact` identifies the successful judgments with precisely the certified declarations in source order; ordinary declared leaves remain possible.

Admission requires capture under the declared manifest entry as well as a successful runner result, so equal digest strings alone do not establish locality; locality requires equal complete lookup results, including errors, payloads and metadata.

## Where are the selector and runner guarantees proved?

`lean/Lara/Evidence/Extract.lean` operates on typed CSV tables, JSON trees and scalar lexemes. Its relations describe unique key-row selection, ordered column selection, pointer resolution and explicitly typed scalar decoding. Exact output construction precedes the admission normal-form comparison. These are claims about typed inputs, not a proof that a concrete UTF-8 decoder constructs the right table or tree.

| Guarantee | Theorems | Scope |
| --- | --- | --- |
| Scalar and ordered selection | `decodeScalar_iff`, `csvSelect_iff`, `jsonColumns_iff` | Executable selection agrees with the corresponding relations |
| Unique row and exact output | `csv_unique_row`, `extract_csv_exact`, `extract_json_exact` | A unique selected row or valid selected JSON scalars construct the ordered proposition |
| Root-zero JSON depth and bounds | `jsonMeasure_empty_object`, `jsonMeasure_empty_array`, `jsonMeasure_every_depth`, `jsonWithinBounds_iff`, `jsonWithinBounds_depth_boundary` | Empty containers count as one node at depth zero; depth 128 is reachable and admitted within the node bound, while depth 129 is rejected |
| Runner-owned dependencies | `run_dependencies`, `run_exact_declared_dependencies`, `run_snapshot_membership` | Reported metadata is exactly the supplied declared-object list |
| Local replay | `run_locality`, `admission_locality` | Equal lookup results on requested objects preserve successes and failures |
| Registry replacement | `run_registry_replacement`, `admission_registry_replacement` | Equal registry results on supplied objects preserve the admission result |

`lean/Lara/Evidence/Runner.lean` defines locality using equality of complete lookup results, including errors, payloads and metadata. Equal digest strings alone do not establish this premise. Admission also checks `CapturedValid`: an ID lookup must return an object whose metadata equals the requested manifest entry. The Haskell promotion boundary enforces that requirement through `Admission.captureRejection`; an object captured under another entry with the same ID is not sufficient.

## How are first errors and precedence specified?

The finite admission pass runs binding checks in leaf order, capture checks in requested-manifest order, then replay in leaf order. A capture failure names the failed object and the earliest leaf referencing it. Extraction failures are located at the leaf and carry no object in the typed differential encoding. The runtime's global package capture and ordinary source/policy rejection are earlier boundaries described under [Error precedence and rejection output](#error-precedence-and-rejection-output).

```text
binding_stage_first_error
capture_stage_first_error
admission_first_extraction_error
binding_precedes_capture
capture_precedes_extraction
```

These theorems identify the failing declaration or object and the valid prefix before it. `admission_deterministic` fixes the result for fixed inputs. Determinism does not assert that a live filesystem stays unchanged before capture.

## How does admission preserve source checking?

`lean/Lara/Evidence/Composition.lean` adds a rejecting evidence check before the existing source continuation. `successful_gate_conservativity` proves that its ordinary output is unchanged when admission succeeds. `package_checked_context_exact` and `package_retained_gamma_agree` reuse the existing policy/group prune and retained-leaf meaning results; evidence success cannot admit a quarantined leaf.

`package_source_preserves` starts from an actual successful `Surface.sourceWithEvidence` equation and derives ordinary elaboration, core checking, complete arguments, typed holes and resolved attacks for that same source. `package_same_source_witness` proves replay witnesses for its semantic certified leaves. `package_holes_iff` and `package_hole_reports_exact` reuse the core checker's exact obligation partition; acceptance does not imply that every argument is complete.

`package_source_justified_nonpromotion` supplies the non-definitional safety connection. It combines evidence admission with ordinary admission and core acceptance, then applies `source_justified_nonpromotion`. Its premises require that the query belongs to the requested query set, is not blocked by the directed quarantine computation, and is justified in the checked framework. The conclusion preserves justified status in the declared reference framework. This is not monotonicity of all statuses under arbitrary evidence deletion, and the status remains conditional on the evidence and policy.

## Which claims remain outside the proof?

`concrete_admission_refinement` explicitly assumes equality between a concrete implementation's result and the finite model's result. It transfers a successful result through that premise; it does not prove the premise. `TypedParserRefinement` similarly states a decoder-to-typed-payload relation rather than verifying the CSV or JSON byte parser. Hash collision resistance, descriptor-relative capture and compiler/runtime correctness remain outside the finite model. The proofs live in `lean/Lara/Evidence/` and are audited by `lean/AxCheck.lean`; they are `sorry`-free and restricted to `propext`, `Classical.choice` and `Quot.sound`.

The implementation checks pinned bytes and a selected mapping. It does not rerun an experiment, authenticate its author, prove that a column expresses the intended scientific quantity, or establish that prose matches formal claims. The original-output examples declare `audit-status = reviewed` after the separately [accepted independent mapping review](certified-evidence-human-review-worklist.md#accepted-independent-review). The [second additive freeze](../measurements/frozen/evidence-measured-inputs-v2.md) records the re-pinned packages; historical raw-core measurements retain their declared-evidence meaning.

## How can the implementation and proofs be checked?

Run the mandatory local proof and conformance gates before review. `lean/AxCheck.lean` covers the new theorems, and the axiom audit restricts proofs to `propext`, `Classical.choice` and `Quot.sound`. The typed Haskell/Lean differential is conformance evidence; byte parsing and OS capture have separate runtime tests. Review the runtime contract alongside these theorem premises, and do not replace typed-model conformance with a byte-parser soundness claim.

```sh
make local-gates
cabal test all --test-show-details=direct
make ara-source-spans ara-session-index
cabal run lara -- check-ara examples/certified-evidence/package-a
cabal run lara -- check-ara examples/certified-evidence/package-b
```

The package acceptance gate runs the real binary over copied original packages and mutation cases, including missing or changed evidence, policy precedence, mixed assurance, no-context source paths and transactional publication. `test/evidence-cli.sh` is that runtime gate; `scripts/evidence-differential.sh` compares the typed Haskell/Lean model corpus. They are `evidence-cli` and `evidence-differential` members of `make cross-check` and `make local-gates`. The [CI scope decision](implementation.md#ci-and-local-gates) distinguishes the Haskell workflow from the Lean build and cross-language gates.

## Policy admission at the source boundary

Policy admission is a deterministic judgment at the `.lara` source boundary (frozen runtime-source contract, recorded 2026-08-05). Background for cold readers: a *leaf* is a declared piece of evidence, and the policy's admission rows say which kinds of leaf (by kind and provenance) an artifact may rely on. This contract fixes the filtering layer that applies those rows at the `.lara` source boundary: it decides, deterministically, which declared leaves reach the core checker and which are *quarantined* (set aside as inadmissible, which is not the same as declared false). It filters inputs; it changes nothing about the calculus or the four statuses behind it, and it adds no construct to the core calculus.

### Boundary and non-goals

Policy admission is a deterministic judgment at the `.lara` source boundary. It decides which declared leaves and dependent source declarations reach the already-frozen core checker. It is not an alternative support calculus, it does not turn quarantine into falsity, and it does not change the raw core `.sexp` interface, replay identity, frozen corpus, or the four core statuses.

The byte-level `lara-evidence@0.1` layer described above is separately versioned and outside this contract's scope. This policy-admission contract does not make source references byte-checked or add a leaf-certificate format or evidence-checker registry.

### Total policy lookup and source validity

For every declared leaf `l`, the runtime looks up its exact `(LeafKind, Provenance)` key in the policy admission rows:

```text
policyOutcome(Pi, l) =
  Pi.admission[(kind(l), provenance(l))]  when that row is present
  admit                                    otherwise
```

Thus the semantic lookup is total even though the source table is finite and may be omitted. An omitted table, an empty table, and an unmatched key all mean `admit`; there is no wildcard or first-match behavior.

Two ambiguities are source invalidity, before any policy or core judgment:

- two admission rows with the same `(LeafKind, Provenance)` key; and
- two leaf declarations with the same `LeafId`.

These are not R8 or R1. The `.lara` CLI reports source invalidity with exit 2, empty stdout, and one deterministic located diagnostic on stderr.

### Source outcomes and precedence

The source pipeline has this fixed outcome order:

```text
source invalidity > policy R8 > replay R13 > group R9 > core rejection
```

The first applicable outcome is the only public outcome. Policy-reject R8 scans leaves in source declaration order and selects the first leaf whose exact `(LeafKind, Provenance)` key matches a `reject` row. R8 is a valid source judgment, not malformed syntax and not a core R1: it produces CLI exit 1, empty stdout, and exactly one deterministic stderr line. That line identifies the selected leaf, its kind, its provenance, and the matched admission row. This is the deliberate CLI exception to the ordinary verdict path because R8 is outside the frozen core verdict codec.

Replay R13, group R9, accepted programs, and core rejections retain the existing core-verdict stdout contract (with their existing exit status and any canonical stderr diagnostic). Admission `quarantine` is not rejection.

The classes remain disjoint:

- **R8, source admission:** a declared leaf is rejected by policy admission;
- **R9, group integrity:** a declared duplicate-report group is inconsistent and policy escalates group conflict to rejection; and
- **R1, core reference:** a declaration reaching the core refers to an undeclared core identifier.

In particular, quarantine cannot be implemented by deleting only `Gamma(l)` and allowing a surviving dependent term to fail as R1.

### One combined prune

Duplicate-report consistency is evaluated against the full declared leaf sequence, before anything is removed. This ensures that policy quarantine cannot hide a group conflict. The runtime then computes two ordered seed sets:

```text
policySeed = leaves whose policy outcome is quarantine
groupSeed  = leaves in every inconsistent group when group mode is quarantine
removeSeed = policySeed union groupSeed
```

After all earlier rejecting boundaries have passed, policy and group seeds are unioned once and exactly one prune is applied. The prune removes:

1. every leaf in `removeSeed`;
2. every argument whose full support term depends on a removed leaf, including leaves nested in premises and in question discharges; and
3. every attack whose raw source or raw target argument was removed.

The admitted `Gamma`, retained arguments, retained attacks, and blocked-status input are projections of this same prune. The production core therefore never sees a dangling dependent leaf occurrence. A conditional core query can be `gap` because no complete retained support remains, but that result comes from checking the pruned program, not from treating a missing `Gamma(l)` as a typing route to gap. Public `evidence-blocked` reporting is derived from the same prune and retains the conditional four-state result only as a diagnostic.

### Hidden source carrier

The implementation may expose ordinary verdict/report projections, but the value threaded between source checking and reporting is an opaque carrier. Its sole smart constructor binds together:

- the unchanged replay identity;
- the full declared unit, including declaration order;
- the ordered policy-quarantine seed;
- the one combined policy-plus-group prune; and
- the canonical admission audit.

The carrier prevents reporting from recomputing admission against a different unit, constructing a second prune, or deriving blocked status from different removed material. Hiding the constructor is an API invariant, not a new trust or serialization boundary.

### Canonical audit

The audit is deterministic and is rendered in leaf declaration order. For each removed leaf it records causes in this order:

1. `PolicyQuarantine`, if policy caused removal;
2. every causing `GroupQuarantine` value, once each and in group declaration order.

Removed arguments and removed attacks are rendered in their respective source declaration order. The leaf portion contains exactly one row per removed leaf, and every row has a nonempty cause list; a leaf removed by both mechanisms is not duplicated. This canonical audit, the retained source projections, and blocked reporting all describe the same combined prune.

### Compatibility lock

This contract changes only the `.lara` runtime source boundary and its mechanized metatheory. It does not change:

- core judgments, rejection classes, wire grammar, or four-state semantics;
- raw `.sexp` checking relative to a caller-supplied `Gamma`;
- replay identity or the frozen corpus; or
- byte-level evidence verification, which is the separately versioned layer described above.

This contract has landed. The runtime lives in `src/Lara/Admission.hs` and `src/Lara/Admission/`, threaded through `src/Lara/Driver.hs`; the mechanized side is `lean/Lara/Admission.lean` with the executable reference driver `lean/Lara/AdmissionDriver.lean`, and the two are compared byte-for-byte by `scripts/admission-differential.sh` (20 files: 15 semantic, 5 codec rejects). The implementation plans that specified this work were retired once it landed; their content is this contract section plus the code.

## External registration receipts

The registration-receipt contract is a backend-neutral seam for citing externally witnessed registrations (frozen documentation contract, recorded 2026-08-06). It adds no schema, no validator, no Git backend, no network dependency, and no Haskell or Lean code. Registration receipts are process metadata: they never enter `Gamma`, never create an attack, and never change a grounded status or claim status.

Why anyone wants this: a registration receipt proves that specific content existed, unchanged, at a specific time; for example, that a preregistered analysis plan predates the results it governs. The disclaimers above mark where receipts may *not* reach: `Gamma` is the evidence context the checker reasons from, so a receipt can annotate provenance but can never itself become evidence, mount an attack, or move a claim's status.

### The minimal receipt

A registration receipt is a record issued by an external witness that fixed a content digest at a time:

```text
registration-receipt:
  provider
  immutable-record-id
  registered-content-digest
  witness-issued-at
  witness-proof
```

The receipt says exactly one thing: the named provider witnessed `registered-content-digest` as immutable at `witness-issued-at`, and `witness-proof` lets an auditor verify that statement against the provider. It says nothing about the registered content's truth, quality, or relevance. Lara may cite the registered object later only through the ordinary leaf-and-policy path; the receipt itself is never a leaf, a support term, or an attack.

### Temporal-priority labels

Exactly three labels, in decreasing strength:

- **`preregistered`** — the goal or analysis-plan digest is covered by a verified external immutable timestamp that predates the attempt.
- **`prior-in-checkpoint-history`** — the goal is an ancestor of the attempt in a content-addressed history (e.g. Git), but no external time witness was verified.
- **`post-hoc`** — the goal and attempt first appear together, or the goal follows the attempt.

Git ancestry may establish the second label only. Git author or committer timestamps alone must never establish the first: a local Git log proves checkpoint-relative order, not wall-clock priority, and rewriting local history is cheap. OSF-style time-stamped, read-only registrations (a plan posted before data collection or analysis) are the reference model for the first label.

### Build/no-build gate

No Lara event-log schema, receipt validator, or Git backend is built in this paper cycle. A Lara-specific protocol package is reconsidered only if evaluation identifies a workflow that existing registration services plus a content-digest receipt cannot express, and such a package would require its own threat model covering witness authenticity, key rotation, clock semantics, history rewrite, and availability before any code is written.

### Invariants

1. The documentation never equates local Git order with preregistration.
2. Registration receipts remain outside the calculus and the trusted core.
3. No goal or attempt event automatically changes a Lara claim status.
4. This contract adds no module, schema, or runtime dependency.

## Alternatives considered

The shipped families declare their dependencies statically and reject certified-evidence failures, so they add no byte-level quarantine outcome; the earlier design's read-program sketch of dynamic access-logged checker reads and an `admit < quarantine < reject` outcome join is not implemented. Runner-owned dependency metadata remains required. The original sketch also used independent quarantine/retained-structure arguments and undirected blocking; the opaque source result, existing combined prune and directed public overlay supersede those choices.

Incomplete arguments were a separate core decision. Through `lara-core@0.2`, open mandatory obligations rejected with `PEIncompleteArgument`, and a gap meant no submitted argument. `lara-core@0.3` instead accepts such an argument as a located hole outside the argumentation framework, with a full core refreeze documented in the [located-gap decision](theory-core.md#holes-located-gaps-and-term-level-critical-questions). This was a core scope change, not an evidence-admission soundness requirement. The evidence layer neither restores the former rejection rule nor turns a pruned argument into a reported hole.

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

Evidence admission, its finite-model theory, policy source admission and external receipt boundaries share this reference. [Artifact composition](artifact-composition.md) defines the separate map contract. The evidence inventory, independent review procedure and record, and frozen measurement protocol remain separate audit records. Historical research records and frozen artifacts retain their original citations and are read at their recorded revision.

Raw `.sexp` examples and admission/mutant fixtures are unaffected. Six certified declarations remain in surface fixtures whose subjects are rejections: `ambiguous-premise-reject.lara`, `attack-path-reject.lara` and `capture-reject.lara` retain structural failures before R8. The policy-quarantined certified fixture `admission-prune-open.lara` is recorded as `admission-prune-no-context`; its package replay coverage is supplied by `fixtures/evidence/quarantined`. Previously accepting fixtures `all-forms.lara`, `nd-alpha-left.lara` and `nd-alpha-right.lara` now use noncertified kinds (`observed`, `attested`, `assumed`) rather than depending on a missing evidence context. Each decision is recorded in `fixtures/surface/MANIFEST.tsv`, and `make surface-conformance` compares both runtimes with the golden over the whole manifest.

Core checker bytes, wire grammar, fixtures and proof claims retain their versioned meaning. New replay/report evaluations require an explicit additive refreeze instead of borrowing old measured assurance. Audit-label changes must preserve original producer bytes and the first measured snapshot, update the affected source pins and produce a new reproducible report before the next freeze or release tag.

Independently review any changed mapping before applying its verdict, and preserve original authorship while recording reviewer identity separately. Re-pin changed package bytes and record a new additive report/freeze with a matching tag when the measured inputs change, preserving prior snapshots. Keep runtime contract checks, typed-model conformance and the axiom audit aligned when the layer evolves, and do not describe those gates or mapping reviews as parser soundness, empirical truth or completed paper-level promotion.
