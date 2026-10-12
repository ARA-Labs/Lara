# P6-P7 Haskell inquiry door and conformance implementation plan

>For agentic workers: Use `skill://subagent-driven-development` or `skill://executing-plans` to execute this plan after approval. Track the checkbox steps in order and review each dependency boundary before proceeding.

**Date:** 2026-10-12

**Status:** Approved 2026-10-12. Tasks 1–3 passed spec/quality review, the Haskell suite, and decoded-fixture smoke scenarios. Task 2 also passed the existing source/checker differentials. Tasks 4–7 remain.

**Goal:** Deliver an independent Haskell implementation of `inquiry-input 1`, its result and error codecs, and a CLI whose outputs agree with the Lean reference on the full committed inquiry suite and the resource-boundary cases.

**Architecture:** Port the frozen finite process and inquiry definitions to typed Haskell modules. Reuse the existing source elaborator, evidence runner, checker, and grounded evaluator, retaining their accepted checker value for every family row. A thin `lara inquiry FILE` command reads the raw bytes and prints the bounded runner's result lines or one refusal; a separate differential gate runs both implementations independently.

**Tech stack:** Haskell/GHC2021 and Cabal; existing `bytestring`, `containers`, and `text` dependencies; Lean/Lake reference executables; Python standard-library conformance scripts; Make local gates.

## TL;DR

P6 requires an independent Haskell port of the finite inquiry semantics. The current checkout has no Haskell `Lara.Process` modules or process CLI command. This plan includes the embedded process codec, history semantics, checked-source observation, audits, finite analyses, impact verification and document-wide limits. P7 compares the two implementations on unchanged inputs and goldens. The wire versions and legacy checker behavior stay unchanged.

## Problem

[Issue #45](https://github.com/ARA-Labs/Lara/issues/45) requires Haskell consumers to read and write inquiry documents and to obtain the same result or refusal as `inquiry-run`. [Issue #22](https://github.com/ARA-Labs/Lara/issues/22) groups this work as P6-P7. PR #47 delivered the Lean inquiry semantics and executable; it did not deliver the Haskell implementation.

The issue's statement that the old process door already has Haskell P6/P7 support is inconsistent with this checkout. `app/Main.hs:170-199` routes `check`, `deps`, map, PW, and ARA commands; `lara.cabal:25-142` exposes no process modules. `docs/theory-process.md:266` explicitly assigns the Haskell process door to P6. Running `cabal run -v0 exe:lara -- inquiry fixtures/process/inquiry/joint-only.sexp` currently prints the generic usage to stderr and exits 2. Treat the embedded process implementation as required work, without adding an unrelated standalone process command.

The independent Lean reference is executable now. `lean/.lake/build/bin/inquiry-run fixtures/process/inquiry/joint-only.sexp` returns the joint-slot sensitivity result with four completions and one differing row. Its definitions, rather than the fixture contents alone, define the port's supported inputs.

## Constraints

This delivery implements all eight wrapper request constructors and all nine result-body constructors in `lean/Lara/Process/InquiryWire.lean:1309-1320,1738-1755`. Embedded verdict and audit queries are also supported. Preserve rejected source completions as rows, distinguish an inconsistent family from a positive result, keep submitted witnesses fixed, and never turn hypothetical evidence or equal public status into observed assurance or entitlement.

Keep `process-input 1`, `inquiry-input 1`, `inquiry-result 1`, `inquiry-error 1`, and `lara-core@0.3` unchanged. Do not regenerate the semantic corpus, rewrite mutation bases, change the freeze tag, raise a ceiling, or rewrite existing goldens to accommodate the port. Issue #46's search-step proof and issue #39's infinite-horizon statistical extensions remain outside this delivery. P8/P9 evaluation, file-based presentation sources, evidence recapture, a live inquiry loop, and a new standalone Haskell `process-run` command are also outside it.

The executable emits one newline-terminated `inquiry-result 1` per result, in embedded-query order followed by wrapper-request order. A successful document with no results emits no lines. Any refusal emits exactly one `inquiry-error 1`, with no partial results. Exit codes are 0 for success, 1 for `unsupported` or `limit`, and 2 for other refusals; stderr stays empty. Use `lean/Lara/Process/InquiryRunMain.lean:21-49` for the boundary contract. The Haskell usage detail names `lara inquiry FILE`; compare usage envelopes with that explicit command-name difference, not a blanket diagnostic mask. Missing-file detail must match Lean's `cannot read PATH` exactly, with PATH as given on the command line. A file whose bytes are not valid UTF-8 is the same `io` refusal (`cannot read PATH`, exit 2), because Lean's `IO.FS.readFile` fails on invalid UTF-8 before the reader runs; Haskell must not report it as a `syntax` refusal. Reader failures (`syntax`) carry the shared reader's located message, which both runtimes already spell identically (`src/Lara/Wire.hs` and the Lean reader agree on line, column, message and nesting bound).

## Proposed approach

### Which implementation owns each decision?

The Lean definitions remain the semantic specification and soundness argument. Haskell independently computes the result using the production Haskell checker. Port the executable definitions, their ordering, and their refusal precedence; do not copy proof witnesses into runtime state. When a frozen definition is missing in Haskell, implement it in the process layer rather than substituting a weaker existing report.

Use distinct newtypes for process identifiers, slot/choice identifiers, stable graph identities, and provenance identifiers. Model event kinds, access purposes, coverage kinds, request forms, statuses, diagnostics, limit counters, certificate faults, and read keys as closed sum types. Each fixed vocabulary has one spelling owner and one parse table. Reuse existing `Prop`, AST identifiers, evidence values, and `PublicStatus` where they represent the same domain. Authored strings remain at the text or wire boundary and in fields that the contract explicitly treats as report text.

Use `Natural` for wire naturals and nonnegative counters, including authored values larger than a machine word. Convert to bounded machine indices only after checking the relevant bound. Retain list order and duplicates wherever Lean does; do not replace an ordered list with a set because a calculation later deduplicates it. Preserve authored profile fields for re-encoding instead of normalizing their spelling through `Rational`.

### Which files own the port?

These are proposed new module names. Existing files listed in the last rows are integration points, not a request to restructure unrelated code.

| Files | Responsibility | Lean definition owner |
| --- | --- | --- |
| `src/Lara/Process/Types.hs` | Process identities, events, records, scopes, admission bases, profiles, formulas, names, documents | `Vocabulary.lean`, `Bridge.lean`, `Universe.lean`, `Wire.lean` |
| `src/Lara/Process/History.hs` | Record extraction, state transitions, validity, coverage compatibility, formula evaluation and verdict witnesses | `WorldView.lean`, `Order.lean`, `Coverage.lean`, `Contract.lean`, `Universe.lean`, `Verdict.lean` |
| `src/Lara/Process/Wire.hs` | Embedded process codec and its vocabulary | `Wire.lean`, `InquiryProcessWire.lean` |
| `src/Lara/Process/Source/Types.hs` | Typed source envelope, fragments, replay identity, capture data, source failures and stable source coordinates | `SourceInput.lean`, `SourceCoordinates.lean`, `SourceModel.lean` |
| `src/Lara/Process/Source/Wire.hs` | Exact source/fragment presentation-tree codec and conversion to the existing Haskell presentation AST | `SourceWire.lean`, `SourceDiagnosticWire.lean` |
| `src/Lara/Process/Source/Evidence.hs`, `src/Lara/Process/Source/Diagnostic.hs` | Typed capture admission/extraction and full structured source/core failures | `Evidence/Types.lean`, `Evidence/Admission.lean`, `Surface/Source.lean`, `SourceDiagnosticWire.lean`, `SourceResultWire.lean` |
| `src/Lara/Process/Source.hs` | Shared source observer with retained checker result, public graph/status, source kind/provenance | `Source.lean`, `SourceGraph.lean`, `SourceKinds.lean`, `SourceKindTable.lean`, `SourceProvenance.lean` |
| `src/Lara/Process/Audit.hs` | Claims/witness bindings, capture assumptions, ledger obligations, warrant and fixed-witness audits | `SourceAudit*.lean`, `SourceAuditSupport.lean`, `SourceLedger.lean`, `FamilyAudit.lean`, `Entitlement.lean`, `Ledger.lean`, `Prov.lean` |
| `src/Lara/Process/Audit/Types.hs`, `src/Lara/Process/Projection.hs` | Shared audit/configuration data and one checked-family projection consumed by every analysis | `SourceAudit.lean`, `SourceModel.lean`, `FamilyAudit.lean` |
| `src/Lara/Process/CheckedMethods.hs` | Six source-bound BHL methods and conditional/applied binding checks | `BHL/CheckedMethods.lean`, `BHL/LaraBridge.lean` |
| `src/Lara/Process/Family.hs` | Guarded source slots, assignments, materialization and reference resolution | `Family.lean`, `FamilyWire.lean`, `SourceModel.lean` |
| `src/Lara/Process/Enumerate.hs` | Prefix history search, guard-surviving count, bounded family rows and exact search charges | `Enumerate.lean` |
| `src/Lara/Process/Analysis.hs` | Rejection-aware stability, reference/joint sensitivity, subset-minimal assumptions | `Analysis.lean`, `Inquiry.lean` |
| `src/Lara/Process/Locality.hs` | Stable-identity graph differences and sufficient grounded-locality certificates | `Revision.lean`, `Locality.lean` |
| `src/Lara/Process/Impact.hs` | Full public-status transitions, typed read evidence, impact certificates and first-fault verification | `Impact.lean` |
| `src/Lara/Process/Inquiry/Types.hs` | Typed wrapper input, requests, limits, results, refusals and certificate wire records | `InquiryWire.lean` |
| `src/Lara/Process/AuditWire.hs`, `src/Lara/Process/AnalysisWire.hs`, `src/Lara/Process/ResultWire.hs` | Stage-owned codecs for audit/configuration, analysis records and source/impact result data | `SourceAuditWire.lean`, `AnalysisWire.lean`, `SourceResultWire.lean`, nested `InquiryWire.lean` codecs |
| `src/Lara/Process/Inquiry/Wire.hs` | Top-level input/result/error codecs; reuse stage codecs | `InquiryWire.lean` |
| `src/Lara/Process/Inquiry/Run.hs` | Whole-document validation, accounting, shared projection, dispatch and file boundary | `InquiryRun.lean`, `InquiryRunMain.lean` |
| `src/Lara/Driver/Internal.hs`, `src/Lara/Elaborate.hs` | Retain the existing accepted checker result and source admission state without a second checker pass | Existing `runCheckReported`, `runSourceCheck`, opaque `SourceCheckInput`/`SourceResult` |
| `app/Main.hs`, `lara.cabal`, `test/Spec.hs` | CLI routing, module/test registration | Existing PW command and test registration pattern |
| `test/ProcessSpec.hs`, `test/InquirySpec.hs` | Consumer-visible boundary and semantic regression properties | Existing QuickCheck suite conventions |
| `scripts/check-inquiry-conformance.py` | Independent fixture and generated-case differential | Existing `scripts/check-pw-conformance.py` pattern |
| `scripts/check_inquiry_bytes.py`, `scripts/check_inquiry_products.py` | Run existing adversarial scenarios on a supplied command | Existing Lean-only boundary scripts |
| `Makefile` | New `inquiry-conformance` target in `cross-check` | Existing `local-gates = lean-gate + cross-check` |

The source codec must understand the declared wire, not a textual `.lara` substitute. `SourceWire.lean:124-163` distinguishes strings, signed integer constructors, nodes, and cons-spine children. Decode these into typed presentation data before the checker boundary, including policy, support, evidence, and metadata constructors. Keep one vocabulary owner for each constructor family. A raw `SExpr` is permitted while reading the wire; no generic string-tagged tree enters the semantic runtime.

Keep dependencies acyclic. Put audit/configuration records in `Audit/Types.hs`, which depends on process and source boundary types but no runtime observer. `Source.hs` checks one source; `Audit.hs` reads that retained observation. `Projection.hs` composes bounded family rows with source observation, kind/provenance grading and witness preparation. Analysis depends on this projection; neither source checking nor audits depend on inquiry dispatch. Define required records before their consumers, even when the record's codec or calculation is delivered in a later task.

### How does the source observer reuse the checker?

`Source.checkSource` first checks replay compatibility, then the source/evidence boundary, then certificates selected across all authoritative reconstructed declarations, then missing capture (`lean/Lara/Process/Source.lean:117-134`). The order matters. An invalid replay or a rejected source becomes the exact typed source rejection in its family row; it does not become an inquiry execution refusal.

Reuse `prepareSourceStructure` and `runSourceCheck` through a shared source-checking path. Package-only `admitSourceEvidence` cannot directly represent inquiry captures: inquiry snapshots contain typed CSV/JSON payloads and failed lookups, while package snapshots contain bytes. Add `Source/Evidence.hs` with faithful modeled metadata, ordered snapshot entries, capture failures, request admission and extraction results. Share `Lara.Evidence.Registry`'s typed extractors and the `replayTypedEvidence` algorithm, factoring metadata-independent work into a common helper where needed. Keep the path, digest and size restrictions in `src/Lara/Evidence/Manifest.hs:20-56` at the package boundary. Do not use unsafe constructors or roundtrip typed payloads through CSV/JSON text.

Promote successful modeled judgments through the same opaque source admission/prune/checker path as package judgments, using a typed entry point that preserves capture metadata and evidence dependencies. Retain full structural, evidence and core `UnitError` diagnostics before existing human-rendered/class-only projections discard information. Map constructors to Lean source diagnostics in `Source/Diagnostic.hs`; do not parse diagnostic prose back into structure. Inquiry evaluation performs no external capture or package lookup.

Retain the accepted `CheckedUnit`, the declared and pruned source, admission audit, evidence judgments, and stable node coordinates in the same checker pass. Refactor the internal checker report from its current tuple into a named record with an optional accepted checker value, and migrate its consumers together. Add an opaque accepted-source projection from `SourceResult` for the inquiry observer. A rejected result has no accepted cache; callers cannot pair an audit from one source with a checker value from another. Before changing exported helpers, query LSP references, then read every affected caller; known uses include `Driver/Internal.hs` and `Elaborate.hs`, with source-result consumers in `app/Main.hs`, `Lara.Source.Load`, `Lara.Evidence.Load`, `Lara.Map.Load`, `Lara.RunningExample`, and tests.

Do not call `sourceResultCheckInput` and feed its output to `runCheck` as the inquiry implementation. That projection intentionally refuses policy quarantine (`src/Lara/Elaborate.hs:342-362`). Inquiry must retain evidence-blocked conditional status and source admission causes. Likewise, calling `acceptedRawUnit` after `runSourceCheck` would repeat checking and lose the source-boundary state. New cache projections must leave existing CLI bytes, diagnostics, report order, and rejection precedence unchanged.

### What are the public library boundaries?

The proposed exports below state the intended division. Their argument types are owned by the modules above; implementation may move private helpers within those modules without changing the contracts. `Names` is the embedded process namespace table, and result decoders need it to resolve process identifiers.

```haskell
-- Lara.Process.Inquiry.Wire
parseInquiryInputBS :: ByteString -> Either RunRefusal InquiryInput
encodeInquiryInput :: InquiryInput -> SExpr
parseInquiryResult :: Names -> SExpr -> Either RunRefusal InquiryResult
encodeInquiryResult :: Names -> InquiryResult -> SExpr
parseInquiryError :: SExpr -> Either RunRefusal InquiryError
encodeInquiryError :: InquiryError -> SExpr

-- Lara.Process.Enumerate
-- Includes guard-surviving source counts and exact logical search charges.
enumerateFamily :: FamilySpec -> EnumerationLimits
                -> Either EnumerationRefusal EnumeratedFamily

-- Lara.Process.Projection
-- CheckedFamily retains every completion and uses the enumeration's own family.
checkFamily :: AuditConfig -> EnumeratedFamily -> CheckedFamily

-- Lara.Process.Inquiry.Run
-- Raw file byte count is supplied separately from the typed input.
runBounded :: InquiryInput -> Natural -> Either RunRefusal [InquiryResult]
runInquiryFile :: FilePath -> IO (Either RunRefusal (Names, [InquiryResult]))
exitCodeOf :: RunRefusal -> Int
```

`EnumeratedFamily` owns the bounded history list, family rows, and logical enumeration counts. `CheckedFamily` owns the shared snapshots and prepared rows. `AuditConfig` owns claim bindings, witness specifications, kind metadata, and admitted capture assumptions. The result list is completely determined before the CLI starts writing stdout. File errors, parser failures, and typed run refusals use the same error encoder; result decoders do not execute a query.

### Which limits and ordering must match?

Mirror `runBounded` in `InquiryRun.lean:812-830`: embedded event bound first; raw UTF-8 byte bound; bounded family enumeration; allocation guards for source endpoints and assumption subsets; remaining budget checks; label/reference/impact-claim validation; one shared observation projection; result dispatch. Do not move a malformed-reference refusal ahead of a limit refusal, or emit an embedded verdict before discovering a later request failure.

| Counter | Fixed ceiling | Required charge |
| --- | ---: | --- |
| Embedded events | 8 | Deduplicated recorded/universe event carrier; wrapper refusal uses `histories` |
| `histories` | 10000 | Distinct compatible unguarded histories; also clamped by the embedded process completion limit |
| `sources` | 10000 | Guarded family rows, including rejected sources, plus two endpoints per impact/verification request |
| `source-bytes` | 1048576 | Original file bytes, including whitespace and multibyte UTF-8; typed callers may supply canonical input size |
| `declarations` | 10000 | Aggregate materialized family declarations and both endpoints' declarations |
| `search-steps` | 200000 | History prefix search and logical attempted slot extensions, including pruned suffix cases |
| `pairs` | 4096 | Wrapper requests only: family-row comparisons; surviving rows per assumption subset; twice query count plus read-set cardinality for impact/verification |
| `subsets` | 4096 | Sum of deduplicated-catalog powerset sizes over minimal-assumptions requests only; joint-slot sensitivity is not charged here |

Clamp declared bounds with the fixed ceilings. Exact-at-cap success is legal only when the whole computation finishes there. Product counting saturates at effective `sources + 1`; its refusal reports that first excess. Other counts must follow the reference's reported actual value: for example, a late empty guard can yield no rows yet charge a large exact logical step count. Use closed arithmetic/counting over slot cardinalities rather than building the discarded product just to compute that number. Share bounded rows across accounting and checking, and share suffixes across guarded choice expansion.

Preserve DFS stop-before-extension order, event pool order, slot order, choice order, first differing witnesses, first-fault verification order, and minimal-assumption/generated-read output order. Most lists retain order exactly. Certificate wire reads are an ordered list decoded to a semantic finite set: duplicates and reordering are normalized for verification, so do not invent a sorted/unique-list refusal. `Enumerate.lean:15-40,73-103` specifies enumeration order; `InquiryRun.lean:139-143,369-378` specifies labels and validation order.

Impact pair accounting can require endpoint observation before final budget/label checks to compute read-set cardinality. Retain and reuse that observation for dispatch; do not guess a cheaper charge or check the endpoint again. Source/subset allocation guards still run before expensive comparisons.

## Alternatives considered

| Approach | Benefit | Cost or failure |
| --- | --- | --- |
| Independent typed Haskell port using existing checker operations | Gives Haskell consumers a real implementation and makes cross-language comparison meaningful | Requires the missing process, audit and inquiry semantics, not just a codec |
| Haskell command shells out to `inquiry-run` | Reuses the reference behavior immediately | Does not provide independent P7 evidence; makes Lean a runtime dependency |
| New extracted/generated runtime | Could reduce duplicated semantics | Introduces a generator and another trust/build boundary that the repository does not currently use |

Use the independent port. Keep the Lean reference stable unless comparison reveals a real contract defect. A discovered defect needs an explicit reviewed correction and the required proof/fixture changes; changing a golden to agree with Haskell alone is not a fix.

## Tradeoffs

The largest work items are the typed source presentation codec, fixed-witness process/BHL audits, and full impact/read-certificate recomputation. Existing Haskell public verdicts do not supply all those records. The module seams above keep the port readable by domain while sharing the production source checker. File length alone is not a reason to split a coherent stage.

Haskell property tests and differentials establish conformance, not soundness. The existing Lean proofs remain the soundness evidence. A Haskell-only port of an already frozen definition does not require a second Lean theory; if implementation introduces or changes a corpus-independent definition, mechanize it at that stage and add every new theorem to `lean/AxCheck.lean`. Keep proofs sorry-free and within `propext`, `Classical.choice`, and `Quot.sound`.

## Migration

### Task 1: Port the embedded process model and codec

Files: create `Types.hs`, `History.hs`, `Wire.hs` under `src/Lara/Process/`; create `test/ProcessSpec.hs`; modify `lara.cabal` and `test/Spec.hs`.

- [x] Read `Vocabulary.lean`, `WorldView.lean`, `Order.lean`, `Coverage.lean`, `Bridge.lean`, `Contract.lean`, `Universe.lean`, `Verdict.lean`, `Wire.lean`, and `InquiryProcessWire.lean` at their executable declarations. Map each constructor and spelling into the three Haskell modules. Port scoped coverage and default dataset version 0 exactly.
- [x] Add behavioral tests before the port for an omitted earlier evaluation/selection read changing precommitment to unknown, admitted coverage removing that completion, contradictory coverage producing inconsistent, and a data update invalidating the old input version. Use actual decoded process records from `fixtures/process/run/`, not mocked transition results.
- [x] Implement namespace interning, exact arity, ordered optional clauses, canonical decimal naturals, duplicate and undeclared-name refusal, and profile/formula codecs. Preserve the embedded codec's supported/unsupported coverage forms. The inquiry parser must translate an embedded decode failure to its own generic malformed-input result exactly as Lean does.
- [x] Implement extraction under admitted bases, state steps, cutoff validity, compatible histories, formula truth and the four verdicts. Preserve P0 completion order and witness selection for embedded unknown verdicts; its `Universe.answer` path is separate from guarded source-family results.
- [x] Exercise `fixtures/process/run/empty-universe.sexp`, `omitted-read.sexp`, `admitted-coverage.sexp`, `contradictory-order.sexp`, and `renamed-identifiers.sexp`. Construct the data-version transition as typed events, since it has no dedicated process-run fixture. Add valid-name/record roundtrips and refusals for leading-zero naturals and swapped identifier namespaces. No standalone process CLI is part of this task.

Run `cabal test lara-test` after the task is integrated. Expected: existing suites and the new process behavior properties pass. For a commit, use `feat(process): port the embedded process model and codec`.

### Task 2: Decode typed source envelopes and retain the production checker result

Files: create `Source/Types.hs`, `Source/Wire.hs`, `Source/Evidence.hs`, `Source/Diagnostic.hs`, `Source.hs`, and the shared audit/configuration records in `Audit/Types.hs` under `src/Lara/Process/`; modify `src/Lara/Driver/Internal.hs`, `src/Lara/Elaborate.hs`, shared evidence helpers, affected consumers and registrations; add source cases to `test/InquirySpec.hs`.

- [x] Decode the exact source and fragment constructor tree, replay metadata, capture snapshot/manifest, source diagnostics, policy, program declarations, support terms, and evidence values. Reuse existing presentation/core types where equivalent. Keep representation adapters at this boundary and test any differences in declared names, formulas or numeric constructors against the Lean codec.
- [x] Implement modeled capture admission with arbitrary metadata, ordered JSON entries and numeric lexemes, duplicate entries where Lean admits them, failed lookups and typed extraction. Add the source-promotion entry point described above. Test a valid modeled capture that package validation would reject, metadata mismatch and failed capture against the modeled semantics.
- [x] Query LSP references for `runCheckReported`, `runSourceCheck`, and exports whose types change. Read returned and known imported callers. Retain the accepted cache and full source/core failures in the same decision path; migrate tuple destructuring together, leaving no second legacy report implementation.
- [x] Extend opaque `SourceResult` with a typed accepted-source projection carrying its checker value and its own source admission/evidence state. Reuse it to compute the AF and fixed-atom public statuses, including policy/group blocked overlays. Expose no constructor that permits independently replacing the cache or audit.
- [x] Implement `checkSource` replay/error precedence and certificate selection over all declared reconstructed arguments, including pruned arguments and nested discharge/certificate terms. Implement kind aggregation, provenance and stable source graph/hole coordinates from the retained source. Unknown attacker kind remains an explicit unknown, not a default kind.
- [x] Use actual sources for the rejected replay, admission/evidence failure, missing capture, forged observed evidence, blocked conditional status, normalized support, shared discharge, and reindexed hole behaviors. Confirm source-rejected rows retain the appropriate typed failure and never a public status. Test that policy quarantine cannot escape as an ordinary raw checker status.

Run `cabal test lara-test` and the existing source/checker differentials after integration. Expected: the old CLI/report contracts remain unchanged, and source observation uses one retained checker result. Commit: `feat(inquiry): add the checked source observation boundary`.

### Task 3: Port fixed-witness audits and guarded family enumeration

Files: create `Audit.hs`, `AuditWire.hs`, `CheckedMethods.hs`, `Family.hs`, `Enumerate.hs`, and `Projection.hs` under `src/Lara/Process/`; extend `Audit/Types.hs`, `ProcessSpec.hs` and `InquirySpec.hs`; register modules.

- [x] Port claim and witness bindings, process/BHL witness specifications, capture assumptions, kind metadata and their codecs. Implement the source association and ledger predicates used by `Source.warranted`; include retraction/version changes, failed siblings, family selection, submitted-witness identity, conditional/evidence-blocked outcomes, and profile admission/guarantee requirements.
- [x] Port all six checked methods (`two`, `low`, `up`, `disjunction`, `conjunction`, `conditionalFalse`) from `lean/Lara/BHL/CheckedMethods.lean` and source-bound checks from `lean/Lara/BHL/LaraBridge.lean`. Check model/premise/program/postcondition binding, allowed parameters, before/after points and actual modeled application. Conditional interpretation does not assert execution; `conditionalFalse` fails applied preconditions. A matching method name is insufficient.
- [x] Pin each witness to the base source and check claim/alternative association, inferred support, retention and profile-filtered grounded warrant. Check admissible kinds, required probes, guarantee class and attained level. Conditional levels lie in [0,1]; exact ledger formulas include failed trials. Duplicate audit metadata and missing kinds make the modeled audit incomplete where Lean specifies it, not a new wrapper decode error.
- [x] Append every supported fragment declaration in order, including extraction/comparison declarations and generated contribution keys. Preserve base policy, replay identity, artifact digest and capture. Implement guards at the fixed history, fixed claim binding, stable slot/choice identities, assignment resolution and family membership. Keep duplicate/absence cases at their specified semantic-failure or refusal boundary.
- [x] Implement prefix DFS with its empty-prefix stop branch, compatible-history deduplication and deterministic pool order. Preserve full reported history/search counts and the refusal precedence in `Enumerate.enumerateFamily`. Do not silently filter source failures.
- [x] Count guard-surviving products using capped arithmetic before allocation. An empty choice list prunes the final rows, including a late empty guard; logical slot-extension counts still apply. Share each bounded suffix and retain the enumerated history/row/count record for later accounting.
- [x] Implement `Projection.checkFamily`: snapshot each bounded completion once, form the shared node/witness-name carrier, and prepare graph, grades, witnesses and fixed-claim observations from retained source results. Share this record across all requests. Distinguish raw argument occurrence, retained declaration and AF-node coordinates.
- [x] Add transition properties where a different valid witness cannot rescue the submitted witness, observed capture cannot be inferred for hypothetical fragments, a failed ledger sibling remains relevant, and an added attacker defeats the prior warrant. Keep timeout/product tests in the executable gate rather than a flaky QuickCheck timeout property.

Run `cabal test lara-test` after integration. Expected: history/family/audit properties pass without weakening the legacy process audit refusal in Lean. Commit: `feat(inquiry): port audits and bounded source families`.

### Task 4: Port finite analyses, locality and full impact verification

Files: create `Analysis.hs`, `AnalysisWire.hs`, `Locality.hs`, `Impact.hs`, and `ResultWire.hs` under `src/Lara/Process/`; extend `InquirySpec.hs`; register modules.

- [ ] Read the shared checked-family projection and implement observable/target/literal codecs. Implement whole-family and conditional stability with rejected rows retained, reference sensitivity, every joint-sensitive slot set, and all subset-minimal assumption sets. Match catalog deduplication, subset traversal and result ordering; an empty compatible family does not produce a positive stability or assumption result.
- [ ] Preserve full rejection-payload equality: a nonempty family of identical rejections can be whole-stable, but never accepted-domain-stable. Sensitivity counts changed observations across histories; differing rows, minimal changed-slot sets and realizers use the reference history. Return all inclusion-minimal sets, not just minimum-cardinality sets. Assumption restrictions require nonempty accepted rows matching the exact target.
- [ ] Port stable-identity graph differences and the sufficient grounded-locality certificate. Treat graph indices as local serialization positions, not source identity. Preserve hole reindexing, support normalization, new attackers, unrelated self-attack, and dependency changes.
- [ ] Port both endpoint observations and full public-status impact: acceptance/rejection transitions, conditional blocked statuses, query bindings, changed/read key partitions, graph/locality data and resulting impact rows. The conservative whole-input read fallback is part of the port; equal grounded status alone cannot replace it.
- [ ] Implement honest certificate construction and verification by recomputing every field against the supplied endpoints. Port `firstFault` ordering and every verification fault constructor. A structurally valid false certificate returns a verification result, not an inquiry error. A referenced impact claim without a binding returns the explicit malformed refusal; there is no empty-atom fallback.
- [ ] Verify faults in order: snapshots, identities, endpoint/transition/blocked reports, status rows, partitions, graph carrier/diffs, locality, reads. Replace certificate inputs with supplied endpoints. Rejected-to-rejected queries belong to neither changed nor unchanged; mixed endpoint outcomes retain accepted-side names but have no graph differences and false locality.
- [ ] Add behavior tests that a changed read value or query binding invalidates a certificate, an honest certificate verifies, and equal public status with changed entitlement-relevant provenance remains distinguished. Use fixture semantics for normalized support, reindexing holes, backend dependencies and rejected endpoints. Do not test that an encoder merely forwards a mocked field.

Run `cabal test lara-test` after integration. Expected: independent Haskell analyses and certificate recomputation satisfy the behavior properties. Commit: `feat(inquiry): port finite analysis and impact verification`.

### Task 5: Finish the wrapper codecs, shared budgets and real CLI

Files: create `Inquiry/Types.hs`, `Inquiry/Wire.hs`, and `Inquiry/Run.hs` under `src/Lara/Process/`; modify `app/Main.hs`, `lara.cabal`, and `test/InquirySpec.hs`.

- [ ] Implement all input fields, eight request forms, nine result bodies, nested impact certificate records, optional error labels, and structured refusal codecs. Result parsing takes the input's `Names`; error parsing needs no names. Use decode-then-reencode equality where Lean's codec applies `canonical`, and retain the wire's contextual namespace constraints.
- [ ] Implement all allocation and whole-document counters from `actualFor`, `pairsOf`, `subsetsOf`, `declarationsOf`, endpoint charges and `limitsOf`. Count before constructing source products and assumption subsets. Follow the exact execution/refusal sequence in the limits section above, including duplicate labels across embedded and wrapper lists and reference membership checks after budgets.
- [ ] Build one shared `CheckedFamily` for the bounded family and dispatch every embedded query and wrapper request from it. Impact and verification requests charge and observe their own endpoints. Do not rerun the family checker or materializer for each request, and do not use the declared product upper bound as the actual observed row count.
- [ ] Add `lara inquiry FILE`. Route every argument shape beginning with `inquiry` through the inquiry boundary so missing/extra arguments produce an inquiry usage envelope on stdout with empty stderr. Read the file as `ByteString`; map a read failure or invalid UTF-8 to `io "cannot read PATH"`; charge its original byte length; decode with the existing S-expression reader; compute the entire outcome, then emit result/error lines and the required exit code. Keep unrelated CLI argument handling unchanged.
- [ ] Add exact-at-cap, cap-plus-one and precedence properties where two faults coexist: embedded event/byte limits, source/subset allocation guards, remaining budget checks, duplicate labels, reference failures and unresolved impact bindings. Verify no result lines precede a refusal. Smoke the real command against joint sensitivity, reference sensitivity, verified/tampered certificates, and unresolved impact claims.

Run `cabal build exe:lara` and `cabal test lara-test` after integration. Then run:

```bash
cabal run -v0 exe:lara -- inquiry fixtures/process/inquiry/joint-only.sexp
cabal run -v0 exe:lara -- inquiry fixtures/process/inquiry/reference-sensitivity.sexp
cabal run -v0 exe:lara -- inquiry fixtures/process/inquiry/verified-certificate.sexp
cabal run -v0 exe:lara -- inquiry fixtures/process/inquiry/tampered-certificate.sexp
cabal run -v0 exe:lara -- inquiry fixtures/process/inquiry/unresolved-claim-impact.sexp
```

Expected: the first four produce their existing golden result bytes with exit 0 and empty stderr, including an invalid-certificate result for the tampered certificate. The last produces the existing malformed inquiry error with exit 2 and empty stderr. Commit: `feat(cli): expose the bounded inquiry runner`.

### Task 6: Add independent conformance and adversarial CLI coverage

Files: create `scripts/check-inquiry-conformance.py`; modify `scripts/check_inquiry_bytes.py`, `scripts/check_inquiry_products.py`, and `Makefile`; extend focused properties only where the differential leaves an uncertain semantic boundary.

- [ ] Build both drivers once: `cabal build exe:lara`, then `lake build inquiry-run` in `lean/`; resolve Haskell with `cabal list-bin exe:lara`. Discover all `fixtures/process/inquiry/*.sexp` and fail for an empty family or missing golden. Current inventory is 49 document pairs; `scripts/check-inquiry-run.sh` reports 52 because it adds three argument-shape boundary cases. Do not hardcode either count. Run both drivers independently on each original file with a timeout.
- [ ] For each fixture, compare each driver's raw stdout bytes to the unchanged golden and compare exit codes and stderr independently. Preserve final newlines and multi-line results; do not use shell command substitution, text normalization, ignored stderr, or an exit-only comparison. A refusal must be one error envelope and no result envelopes. Successful documents with no requests/queries are valid empty stdout, not an empty fixture suite. Keep that case generated rather than committed: the Lean gate writes goldens with `printf '%s\n'`, compares through command substitution and infers the exit code from the golden's first form, so an empty-output golden would be `\n` and would be classified as exit 2.
- [ ] Exercise the Haskell input/result/error consumer codecs on actual fixture documents and actual driver output, requiring decoded typed values to re-encode to the same parsed S-expression. Add value roundtrips for constructor families not present in the fixtures, so result parsing is part of P6 acceptance rather than an unused encoder-only API.
- [ ] Generalize each existing boundary script to accept a command argument list while preserving its current default Lean command; `scripts/check-inquiry-run.sh` invokes both scripts with no arguments and must keep working unchanged. Run the same six ASCII/whitespace/multibyte byte cases and seven guarded-product cases against both commands. Keep the ten-second timeout on product invocations; timeout, spawn failure or signal termination fails the gate. The huge binary-choice case must refuse at `sources = 2, cap = 1` without materializing its product.
- [ ] Generate malformed section/arity/name/natural/version cases, empty output, duplicate cross-list labels, invalid references/impact bindings, shared-counter exhaustion, ceiling clamps, certificate faults and fault precedence. Include a large deduplicated assumption catalog with a tiny subset cap, proving refusal before powerset allocation. Specify expected outcomes as well as driver agreement. Keep documents temporary and use typed constructors or parsed-tree edits.
- [ ] Exercise zero/extra arguments, missing files, invalid-UTF-8 file bytes (both drivers: `io` refusal, exit 2), syntax/trailing forms, reader-depth boundaries, Unicode escaping and non-ASCII paths under C and non-UTF-8 locales. Check each command's exact usage detail. Require portable syntax cases to match structured refusals and agreed detail; do not copy PW's broad diagnostic masking.
- [ ] Add phony `inquiry-conformance` to `cross-check`, hence `local-gates`; preserve `process-theory`. Keep process-tree exclusions in `scripts/differential.sh` and `scripts/gen-anchor-manifest.sh`; update only ownership comments to name inquiry parity. Check fixture ownership so nested or misplaced inputs cannot silently disappear. Keep anchor manifests and corpus bytes unchanged.

Run:

```bash
python3 scripts/check-inquiry-conformance.py
make inquiry-conformance
make process-theory
cabal test lara-test
make local-gates
```

Expected: both drivers match every committed inquiry golden, all generated comparisons and the two shared boundary suites; the old process runner and every existing cross-language gate still pass. Run the final full gate on the integrated tree, not inside each parallel edit slice. Commit: `test(inquiry): gate Haskell Lean conformance`.

### Task 7: Document the landed contract and resolve delivery tracking

Files: modify `docs/theory-process.md`, `docs/implementation.md`, `docs/spec.md`, and `README.md`; update `ara/` only when recording the implemented feature/design change; delete this executed plan after moving durable details to subject docs.

- [ ] After the executable smoke and differential evidence pass, document the Haskell library codecs, `lara inquiry FILE`, multi-line output/refusal/exit behavior, fixed limits, shared observer and independent conformance target in present tense. Replace the wrapper's Lean-only status; keep the standalone `process-input 1` reference status accurate.
- [ ] Update the implementation command index and CI/local-gate table. Required GitHub workflows still do not run Lean or cross-language gates unless the workflow itself is deliberately changed; this plan adds the local gate, not a CI guarantee. Say `make local-gates` passed in the implementation PR.
- [ ] Run `skill://research-manager` for the implemented feature, record exercised evidence and limitations in the existing ARA subjects/trace, and run its required source-span, session-index and observation checks. Do not describe finite fixture agreement as a performance or scientific-discovery improvement.
- [ ] Update #22's P1-P5 status to reference #47 and mark P6-P7 complete only with this delivery's evidence. Close #45 through the implementation PR's `Closes #45`. Keep #22 open for P8/P9 and keep #39/#46 open. If any required part of this plan is deferred, obtain scope approval, open a GitHub issue stating work/why/cost, and leave this plan with a remaining-work status; do not claim #45 complete.
- [ ] Remove temporary smoke programs and generated-case files; keep only the permanent behavior tests and reusable gate scripts. Move any durable design statement into the matching subject document before deleting this plan. Review all affected callsites, tests and docs before requesting merge review.

Commit: `docs(inquiry): document the Haskell door and conformance gate`.

## Which checks establish acceptance?

| Requirement | Acceptance evidence |
| --- | --- |
| Independent Haskell evaluation | Production Haskell source checker, process/audit/analysis/impact code; no Lean subprocess or golden reads in runtime modules |
| Complete input and consumer codecs | Typed input/result/error roundtrips and actual driver-output decoding, including contextual names and certificates |
| All queries and request/result forms | Full Lean definition inventory implemented; fixtures plus constructor/behavior properties cover gaps |
| Exact public behavior | Every committed inquiry fixture matches raw stdout, empty stderr and its expected exit separately on both drivers |
| Fail-closed resource bounds | All seven counters, effective ceiling clamps, shared charges, exact/cap-plus-one tests, six byte cases and seven timeout-bounded product cases |
| Source rejection and assurance discipline | Rejected rows retained, fixed witness/query identities, capture assumptions explicit, conditional blocked statuses and full read certificates preserved |
| Existing contracts unchanged | `cabal test lara-test`, `make process-theory`, and the full `make local-gates` pass with existing goldens unchanged |
| Honest tracking and documentation | #45 closed by delivery; #22 P6/P7 checked while P8/P9 remain open; docs and ARA describe only exercised behavior |

## Next steps

1. Commit this approved plan (`plans/` is currently untracked) so `/implement` can execute it from the repository.
2. Execute the dependency chain through Task 5. Codec subdomains and generated gate cases can be worked independently once their shared types and command contract are fixed; give shared-file edits one integration owner.
3. Land P6 and P7 together only after the real CLI, complete consumer codecs, adversarial gates, and `make local-gates` satisfy the acceptance table.
