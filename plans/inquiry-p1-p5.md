# Checked inquiry P1-P5 implementation plan

**Date:** 2026-10-11

>Status: APPROVED plan after design and feasibility review. All implementation checkboxes remain unimplemented; proposed interfaces and fixtures are not landed contracts.

>For agentic workers: use the subagent-driven-development or executing-plans skill when implementation is separately assigned. Complete the checkboxes in dependency order. Deliver P1-P5 together in one PR for [issue #22](https://github.com/ARA-Labs/Lara/issues/22). This review authorizes no implementation, commit, push or PR.

Goal: compute exact finite source-completion analyses and dependency-correct impact certificates from the real Lara checker, including rejected sources and evidence-blocked conditional statuses.

Architecture: preserve the landed process history contract and add a separately versioned inquiry envelope containing finite typed source choices. One proof-bearing source observer feeds audit, stability, sensitivity and impact. Recheck both ends before issuing an impact certificate; locality proves which results could not change, without introducing a second checker.

Tech stack: Lean, the existing symbolic Lara checker and S-expression boundary, shell golden gates. Haskell codecs/CLI and full cross-language inquiry conformance remain P6/P7; evaluation remains P8/P9.

## TL;DR

P0 cannot carry this work unchanged: its document has no source, its answers contain only history verdicts, and `run_audit` proves every audit is refused. The approved design leaves those version-1 bytes and theorems true and adds an `inquiry-input 1` wrapper and `inquiry-run` Lean executable in this same P1-P5 PR. The wrapper embeds the P0 document and finite concrete source alternatives; it never accepts a caller-supplied argumentation framework or status function. Plan approval covers this additional outer contract, the finite source-choice semantics and the audit metadata trust boundary. No core wire change, corpus regeneration, mutation-base rewrite or freeze-tag bump is planned.

## Problem

The existing `Inquiry` holds a finite set of completions, with Boolean-property stability and reference sensitivity. `Universe.Problem.completions` supplies compatible ordered histories from recorded and declared unrecorded events. Neither maps a completion to raw Lara source. The old outer result cannot print a family of source rejections, joint sensitivity, minimal assumptions or pairwise impact evidence (`lean/Lara/Process/Inquiry.lean:28-89`, `lean/Lara/Process/Universe.lean:110-145`, `lean/Lara/Process/Run.lean:53-83`).

The integration boundary must retain more than a grounded status. `Update.PublicReport` intentionally collapses blocked diagnostics, whereas `Driver.PublicStatus` and `BHL.ordinaryStatus` retain `evidenceBlocked conditionalStatus`. `Update.AcceptedRun` retains the exact admission result and proof-bearing checked unit needed by `BHL.observeOrdinary`; this is the existing boundary to reuse (`lean/Lara/Update.lean:70-85,2048-2056`, `lean/Lara/BHL/LaraBridge.lean:398-435`).

Lara makes research arguments checkable rather than establishing their empirical truth (`README.md:8-34,64-90`). This extension asks whether those arguments withstand declared alternatives, which missing observations matter jointly, which explicit conditions stabilize an answer, and which edits preserve a claim's public status. These are useful questions about the declared model; this plan claims neither automatic experiment selection nor measured discovery or performance gains.

## Constraints

Keep `process-input 1`, `process-result 1`, `process-error 1`, `lara-core@0.3`, all existing corpus bytes and existing P0 fixtures unchanged. The P0 runner remains a history-only runner and continues refusing audits. The separate wrapper is an approved extension, not a reinterpretation of version 1. A future decision to select a version-2 process contract requires a separately reviewed plan revision budgeting all affected codecs, proofs, goldens and P6/P7 work; do not silently rewrite P0's semantics.

The symbolic layer uses closed constructors and distinct identifiers. Strings are confined to wire names, labels and the existing raw argument-name exception in `Update.SourceState`. Every frozen definition lands with its independent semantics, executable correspondence proofs and explicit `AxCheck.lean` rows. Proofs use no `sorry` or `native_decide`; only `propext`, `Classical.choice` and `Quot.sound` are allowed. No desired result is accepted as a certificate premise.

Exact enumeration is exponential. Limits refuse the entire inquiry before any affirmative result is published; a checker-rejected source remains a member of the completed family, not an execution refusal and not a filtered-out completion. The result distinguishes model assumptions, supplied conditional facts, checked source acceptance and physical observation. A hypothetical source alternative never becomes observed evidence. Equality of public statuses proves no process entitlement transfer (`docs/theory-process.md:205-209`).

## Proposed approach

### Which missing boundary gets added?

Add a proposed `Lara.Process.Source` module over authoritative typed `Surface.Input`, not a separately supplied lowered core unit. It runs the existing surface assembly/admission, evidence replay and core continuation, then retains the exact `Surface.ElaboratedWithAudit` and accepted output. Derive the raw state through `BHL.sourceStateOfAudit`, the exact `Update.AcceptedRun` through `BHL.acceptedRunOfSource`, and certified source evidence through `BHL.certifiedSourceOfSource` (`lean/Lara/BHL/BridgeSource.lean:148-286`). These constructors already retain the actual source/checker successes and prove the full alignment; no raw-certified bridge API or refactor of `Update.acceptEdited` is needed.

Match `Surface.sourceWithEvidence`'s full failure priority (`lean/Lara/Surface/Source.lean:99-109`): first reject a duplicate evidence-checker allowlist as `evidenceSyntax`, even with no evidence leaves; then ordinary structural assembly/admission (including group policy), evidence admission over every semantic declaration, and core checking. Replay certified/extraction leaves even when unused or quarantined, using `Evidence.admit` under the fixed production registry `Evidence.extract`. After the initial syntax guard, a policy rejection wins over an evidence mismatch; after admission succeeds, an evidence mismatch wins over a core rejection. The proof-retaining helper keeps the elaboration audit from the same assembly and proves its `elaborateWithAudit` equation and output agreement, rather than rerunning expansion/inference. Retain typed core errors before `finishAssembled` collapses them to `.unsupported`, and prove the observer projects to the existing result after diagnostic erasure. Add mixed-failure fixtures for all three priorities.

The proposed source record contains typed `Surface.Input`, backend theory/replay declarations and an optional evidence snapshot/manifest. Its policy already owns admission and evidence-checker declarations, and its program owns leaves, arguments, claims, groups and attacks. `Process.SourceWire` composes the existing AST codecs into a source envelope with canonical round-trip laws; it is not a `.lara` parser. Reuse existing atom, support/certificate and evidence codecs where their types match. Build the symbolic environment from the production canonicalizer and closed shipped backend/evidence registries; do not decode function-valued registries. Missing evidence context is legal only when no semantic leaf needs it; otherwise retain a source rejection. No caller-supplied raw source can disagree with the surface: all raw carriers are derived from the elaboration audit. The unchanged `check-input` envelope remains the core parity format, not the authoritative source format. Adding this envelope and its laws is an explicitly budgeted P1 task; no file fetch or Haskell elaborator is added.

Reuse `Presentation.printProgram`/`parseProgram`, `printPolicy`/`parsePolicy`, and their `parse_printProgram`/`parse_printPolicy` laws for `Surface.Input`'s two fields. Reuse `sxDecl`/`unDecl` and `un_sxList_Decl` for fragments (`lean/Lara/Presentation.lean:1487-1525,1559-1588`). The new codec adds the source envelope and capture/backend context, a lossless bridge from `Presentation.Sx` to the runner boundary, and missing strict canonical/injective laws. It must not introduce a second AST spelling convention.

### What is one completion?

Use a declared finite product of source-choice slots paired with a P0 history. A slot has a distinct `SlotId`, a nonempty ordered list of distinct `ChoiceId`s and a typed source declaration fragment for each choice. Fragments use existing `Presentation.Decl` constructors, including leaves with extraction declarations, arguments, claims, attacks and duplicate-report groups. Signature, rule/admission policies and backend theories are common to the family. Append the selected declarations to the base program in declaration order, then elaborate the resulting complete `Surface.Input`; duplicate identifiers, unresolved attacks and missing dependencies are source rejections rather than left-biased overwrites. A pairwise impact request may compare two independent full source inputs, so policy, signature and registry changes are still covered by P5.

A choice can carry a guard made from the existing `Universe.Query` formulas plus explicit event-presence and event-before atoms. Guards are modeling constraints over a history, not observations. The family contains every pair `(h, choices)` where `h` is in `Problem.completions`, exactly one alternative is selected per slot, and every selected guard holds. With no slots and true guards, projection to histories is exactly P0. Declaring a slot's domain explicitly excludes all other alternatives, just as P0's universe excludes undeclared events. Failed runs remain in `h`, even if their alternatives add no argument. Input order never supplies event precedence.

This is a concrete finite source language, not a function parameter `ProcessHistory -> AF`. The executable enumerates choices, builds raw material, and checks every result. A finite table of already computed statuses, an `accepted` flag, a caller-provided graph or a callback choosing arbitrary witnesses is forbidden. Source choices may describe hypothetical outcomes; no automatic inference from an event to a scientific source interpretation is claimed.

### What are the proposed interfaces?

The following signatures are proposed contracts, not compilable code or landed names. Supporting records named here are defined by the field lists below; dependent parameters will follow existing `AcceptedRun` conventions.

```lean
-- Source.lean: reuse the concrete registry and exact admission/checker run.
checkSource (input : SourceInput) : SourceOutcome input
observeSource (input : SourceInput) (queries : List Lara.Atom) : SourceObservation
-- Accepted constructor carries the input-indexed exact run and evidence admission.
-- Rejected constructor carries SourceRejection; neither carries a fabricated AF.

-- Family.lean: Completion holds a history and one choice per declared slot.
referenceFamily (spec : FamilySpec) : List Completion
materialize (spec : FamilySpec) (c : Completion) : SourceInput
observeCompletion (spec : FamilySpec) (c : Completion) : CompletionObservation

-- Enumerate.lean: refusal is outside semantic source outcomes.
generate (limits : InquiryLimits) (spec : FamilySpec) : Except RunRefusal (List Completion)

-- Analysis.lean: analyses project the shared observations, never rerun a new model.
analyze (request : FamilyRequest) (rows : List CompletionObservation) : FamilyResult

-- Locality.lean and Impact.lean: check complete material, not a desired status equality.
checkLocality (before after : AcceptedObservation) (q : Lara.Atom) : LocalityCheck
impact (before after : SourceObservation) (queries : List Lara.Atom) : ImpactResult
verifyImpact (before after : SourceInput) (certificate : ImpactCertificate) : Bool
```

`FamilyRequest` contains only status, audit, stability, reference/slot sensitivity and minimal-assumptions requests. `FamilyResult` is their result sum. `AnalysisRequest` wraps a family request or independent impact/verification inputs; the runner dispatches the latter to `impact`/`verifyImpact`, never through `analyze`. These signatures describe pure reference semantics. The bounded runner threads one shared budget through enumeration, observation and each dispatched analysis, returning `Except RunRefusal AnalysisResult`; prove successful bounded results equal the reference results. Rejected sources remain family rows.

`SourceInput` owns authoritative typed `Surface.Input`, backend/replay declarations and evidence capture inputs. `SourceRejection` is a closed sum distinguishing structural/admission/group errors, replay incompatibility, evidence admission error and core unit rejection, retaining existing typed reasons and locations. Free-form decode text stays in `RunRefusal`. `SourceObservation` contains either that rejection or an accepted snapshot, the exact source/audit successes, `AcceptedRun`, certified evidence, fresh raw/checked coordinate maps, compiled graph, complete support/hole projections, `BHL.observeOrdinary` and `BHL.ordinaryHoleRows`. `AcceptedObservation` is the accepted constructor's payload, not independently forgeable data.

`CompletionObservation` contains its history, slot assignment, source outcome, full public statuses and per-witness audit checks. `AnalysisRequest` selects public status of a fixed atom, submitted-witness audit, stability, reference sensitivity, changed-slot sensitivity, minimal assumptions, impact generation or impact verification. `AnalysisResult` carries the matching result constructor: family analyses include exact total/accepted/rejected counts, reason or disagreement witnesses and requested minimal sets; impact and verification use their dedicated records. Every history/choice witness belongs to the enumerated family. Rejected rows have no public status.

`VerificationResult` is a closed `verified` or `invalid-certificate fault` result. Its faults distinguish mismatched snapshots/identities, outcome/status mismatch, invalid node/support maps and false locality/read evidence. A well-formed but false certificate is an analysis result, not a source rejection or runtime refusal.

### How does a checked source become a submitted-witness audit?

Resolve each process `ClaimId` to a declared symbolic query atom and each `WitnessId` to a stable raw argument identifier. Recompute its checked-node coordinate per completion; `WarrantModel.argOf` is history-independent, but compact checked indices are not. Build the family-wide argument carrier from stable declaration identifiers, lift each checked graph injectively into that carrier, and prove grounded-label preservation. An absent/pruned/incomplete selected argument has no warrant; it never points to whatever now occupies its former index. Two witnesses that alternate support across completions do not certify the one submitted witness.

Freeze the wrapper's `ClaimId -> Atom` bindings before enumeration. Every status and impact query uses that exact atom, even if an alternative removes its declaration or changes a same-named claim's formal proposition. Audits additionally require the authoritative declaration and selected argument to associate with that fixed atom; absence or mismatch fails the audit, not an otherwise successful source check. Never compare different propositions under one claim label.

Compute a kind for every checked node, including every attacker and defender, from all its used leaf and method inputs. Prove the rule/input meet law for this calculation. Build `WarrantModel.underProfile` from this total labeling and check the witness's grounded label there (`lean/Lara/Process/Entitlement.lean:36-72`). Keep ordinary public status separate: removing an inadmissible attacker can reinstate a witness. No transfer to the ordinary graph follows without the existing ancestry premise.

Every slot contribution is hypothetical by construction, with no producer-controlled observed override. Propagate this cap through each dependent support and method derivation. Base-source process kinds are admitted separately from presentation leaf labels and successful replay: a modeled observed kind requires explicitly reader-admitted capture/source-fidelity assumptions and exact source/process bindings. Without that admission its kind is at most conditional; absent required audit metadata still fails the audit. Replay proves pinned-content agreement, not physical observation or calibration.

Require complete kind metadata for every node in an accepted framework before any positive audit of that completion. An unknown kind may have a total placeholder for evaluation, but a separate metadata-completeness check forces every audit on that framework false. An unknown attacker cannot disappear under profile filtering and create an affirmative audit. Ordinary public status is unaffected. Print every reader-admitted modeled-observation assumption in the result; no parser field certifies physical observation.

There is a second missing prerequisite beyond source checking: raw source data alone supplies neither scientific probes, guarantee levels nor the artifact checks in `WarrantModel`. Add an explicit, closed audit specification in the wrapper. Each witness declares its source interpretation, required dependencies, evidence-kind upper bounds, probed error kinds and either a conditional guarantee declaration or an FWER ledger binding. Conditional declarations are reported as assumptions, bound the witness kind by `conditional`, and can never satisfy the strict observed-only profile. Missing metadata yields a failed audit check, never an unconditional `True` artifact field. A ledger binding names the actual run, family, statistic kind/value and a declared count bound; verify run/result association and count every family run in each history, including failed siblings. Reuse `Statistics.warrantedLevel`; missing/nonpositive fields and a violated bound give no warrant. Calibration, interpretation fidelity and capture adequacy remain explicit residual assumptions. Do not claim `warrantedLevel` proves external calibration.

For a checked BHL method binding, reuse `CheckedMethods.Method`, its canonical `binding` and actual `request`, and `BHL.checkSupport`/`checkBridge`. Construct the existing `BridgeCertificate` from the accepted observer: `certifiedSourceOfSource` supplies its evidence field, independently run support inference to prove `RawSupport` for the selected/dependency occurrences, and resolve `ClaimAssociation.declared` from the authoritative surface claim, reconstructed pair and alternative ledger. Validate exact source/claim/method/dependency fields before constructing the certificate; no Boolean `artifact-ok` enters. Add finite codecs and executable construction for these existing obligations in P1. Conditional-only methods remain conditional; `conditionalFalse` cannot manufacture an applied run. Report the method/ledger path and residual assumptions. Evidence-kind computation meets every used leaf and method input; simulated alternatives impose a hypothetical upper bound regardless of successful certificate replay.

Construct the `WarrantModel` over product completions from those computed fields. Define its audit with the existing `ArgumentEntitledBy` quantifier order and `Universe.admittedCoverage`. `Universe.AuditHolds` itself is typed over `ProcessHistory`, so prove a no-slot specialization to that existing predicate instead of claiming a type-invalid direct equality on the product carrier. Accepted source plus false warrant is an ordinary negative audit case. A source rejection is recorded explicitly and prevents a positive all-completions audit. The Boolean warrant projection is false on rejected sources; the richer result retains their rejection reasons.

### What does exact P3 analysis mean?

For a fixed observable, partition the complete family by `rejected reason` or `accepted value`. Public values use `Driver.PublicStatus`, including the conditional label inside a blocked result. Define whole-outcome stability as nonempty and equal observations on every pair. Also report accepted-only stability with an explicit accepted-domain label and rejection count; it is never substituted for whole-family stability. An all-rejected family may be outcome-stable but has no accepted status and no positive audit. An empty family is inconsistent. Prove Boolean-property specialization agrees with `Inquiry.Stable` and `Inquiry.sensitivity`.

Reference sensitivity requires a named reference completion in the family and compares its full observation with every other row. Changed-slot sensitivity uses that same reference and holds its history fixed. For each differing completion compute exactly the slots whose choices differ from the reference; single-slot sensitivity is the singleton case, and joint sensitivity returns every inclusion-minimal nonempty change set admitting a flip. History sensitivity remains visible separately through reference sensitivity and explicit history predicates. The joint-only countermodel uses Boolean conjunction at reference `(absent, absent)`: changing either slot alone keeps the result false, while changing both makes it true. This is reference-relative sensitivity. Global pair sensitivity would also find singleton flips between `(present, absent)` and `(present, present)`, so it must not be used for this countermodel.

Minimal conditional assumptions use a finite user-declared catalog of literals: slot equality/inequality, event presence/absence, event precedence, or an existing process formula and its negation. For every subset, filter the original family, require it to remain nonempty, and require the requested accepted status or positive submitted-witness audit on every remaining row, with no rejections. Return every subset-minimal satisfying set, not merely one minimum-cardinality set. For each literal removed from a returned set, provide a countercompletion showing the immediate smaller set fails; prove upward persistence among consistent restrictions makes these witnesses sufficient for all proper subsets. Inconsistent restrictions never certify anything. Return the empty assumption set exactly when the base family already meets the target. Every result prints the catalog and its hypothetical/conditional assurance; the catalog bounds which conditions the search can express.

### How will P2 enumerate without changing semantics?

Keep `Universe.Problem.completions` as the history reference. Add a prefix depth-first search (DFS) whose state contains `ProcessState`, remaining event identities and satisfied precedence constraints. Extend only with an event whose `ProcessState.step` succeeds; enforce cutoff and already-forced order constraints early. Check complete coverage/count restrictions at each stop candidate unless an explicit prefix-monotonicity lemma licenses earlier pruning. Rejecting a short prefix for omitting a required recorded event would lose valid longer histories. Enumerate source slot products with guard pruning only when the guard is already determined.

DFS starts from the deduplicated union of recorded and universe events. At every executable prefix, including the empty prefix, offer a stop branch: emit it exactly when full compatibility, recorded-event, order and coverage checks pass. Then independently explore its executable extensions. Remaining optional events do not prevent emission; missing required events prevent emission but not extension (`lean/Lara/Process/Universe.lean:130-145`).

Prove history membership, uniqueness and equality of finite sets with the reference, then product-family equivalence. P0 answer witnesses depend on list order (`find?`), so do not replace its runner's list with a permutation-equivalent DFS list. The new runner uses one documented lexicographic history/choice witness order. Prove permutation invariance for verdicts/counts and equivalence of the new witness membership guarantees. Leave P0 ceilings and its enumeration untouched. New inquiry limits include events, process histories, source completions, source bytes/declarations, analysis comparisons and assumption subsets; each is capped by a checker constant. Exceeding any cap aborts the entire result; exactly at a cap remains legal if the complete search finishes there. Stop after cap plus one outputs, and check bounded products/powers before allocating Cartesian products or powersets. A finite search-step cap also bounds searches that produce few valid completions.

### What does graph-difference locality prove?

P4 compares two actually checked graphs after lifting them to a common declaration-identity carrier. Construct the symmetric difference of node membership and compiled incoming edges. Compute backward ancestry of every complete support of the queried atom in both graphs. Check that support membership corresponds and that no changed membership/incoming edge reaches this combined region. Prove that this finite test implies the hypotheses of `grounded_directional_locality`, and derive equality of the complete claim's grounded status. New attackers must be checked in the target graph; old-graph reachability alone is unsound. A successful test is sufficient, not necessary: changes inside the region can cancel without changing a label.

Use `Compile.edgeB`/`checkedAF` closure edges, not just authored raw attacks. Rebut/undermine/undercut can propagate through premise and discharge occurrences (`Compile.containsB` and `attackClosureB`). A fresh declaration name or disjoint leaf set does not establish locality. Capture node deletions, reindexing, holes becoming complete and newly discovered alternative supports. A self-attacking node outside every queried ancestor may change stable-extension existence; it must not change this grounded-only certificate.

### What does a P5 impact certificate contain?

A source comparison records both complete input snapshots, their replay/backend identities, both exact checker outcomes, the query atoms, support membership maps, graph difference and the checked locality facts. Rejected-to-accepted, accepted-to-rejected and rejected-to-rejected outcomes are first-class transitions. For two accepted sources compute every requested full public status using `BHL.ordinaryStatus`, partition queries into changed and unchanged, and retain changed conditional diagnostics even when both outer tags are `evidenceBlocked`. The verifier reruns the shared observer and recomputes all certificate fields; digests identify material but never replace equality or checking.

Source dependency evidence records the material each calculation actually reads: leaf contents and metadata; rule and admission lookups including absent lookups; duplicate-group membership and conflicting values; raw endpoint resolution and retention maps; signature, policy contraries and substitution; backend theory/digest/certificate inputs; all premise and discharge subterms; normalized conclusion-to-query equivalence; complete support/hole membership; and the reference/checked carriers and blocked closure. `Support.certDeps` reports backend acceptance dependencies and is not a complete dependency footprint for source status. Use a closed `ReadKey` sum and exact read values; prove a `RecordsReads` theorem for each reused calculation. Conservative whole-table reads are allowed where a fine dependency theorem is unavailable, and reduce reuse rather than soundness. No claim of maximal locality or incremental speed follows.

Recheck normalization-sensitive equality classes on both sides. An argument's displayed name, unchanged text at one support or unchanged checked graph alone does not protect query equivalence, duplicate-group admission or public blocking. Full public-status preservation needs P4's grounded result plus equal blocking decisions, not equality of `Update.PublicReport` alone. A failed-sibling event can leave the graph and public status unchanged while changing the audit's count/guarantee. Impact records that distinction and never uses a source/public-status certificate as an entitlement certificate.

### Which wire and runner are proposed?

The wrapper has its own closed tag table, strict version check, canonical encoder/decoder laws and `inquiry-result 1` / `inquiry-error 1` envelopes. Proposed grammar outline below names records defined in this plan; implementation must replace each nonterminal with its typed encoder and round-trip theorem in the same task, not accept opaque JSON or caller functions.

```text
(inquiry-input 1
  (process PROCESS-INPUT-1)
  (base SOURCE-INPUT)
  (slots (slot SLOT (choice CHOICE GUARD SOURCE-FRAGMENT)...)...)
  (bindings CLAIM-BINDING... WITNESS-AUDIT-SPEC...)
  (kind-metadata KIND-SPEC...)
  (admitted-assumptions CAPTURE-ASSUMPTION...)
  (assumption-catalog LITERAL...)
  (inquiry-limits (histories N) (sources N) (source-bytes N)
                  (declarations N) (search-steps N) (pairs N) (subsets N))
  (requests REQUEST...))
REQUEST := (status LABEL CLAIM) | (audit LABEL CLAIM WITNESS PROFILE)
         | (stable LABEL OBSERVABLE) | (sensitivity LABEL REFERENCE OBSERVABLE)
         | (slots-sensitive LABEL REFERENCE OBSERVABLE)
         | (minimal-assumptions LABEL TARGET)
         | (impact LABEL SOURCE-INPUT SOURCE-INPUT (queries CLAIM...))
         | (verify-impact LABEL SOURCE-INPUT SOURCE-INPUT IMPACT-CERTIFICATE)
```

`KIND-SPEC` and `CAPTURE-ASSUMPTION` encode the finite typed records below. Resolve their identities against authoritative declarations and process events; require unique keys and reject conflicting entries. Missing required entries fail audit metadata completeness rather than source acceptance. Slot provenance is derived from materialization and imposes its hypothetical cap regardless of these declarations. An admitted assumption records the reader's trust decision, never evidence that the physical observation occurred.

The following records fix the wrapper contract. All identifiers are typed and references must resolve; failures of outer reference validation are malformed input, not source rejections.

| Record/request | Required fields and result |
| --- | --- |
| `FamilySpec` | Embedded process document, base source, ordered slots/choices with guards/fragments, fixed claim bindings, witness audit specifications, reader-admitted kind assumptions and assumption catalog |
| `KindSpec` | Source identity, typed leaf/method/argument identity, evidence-kind upper cap and optional admitted-assumption reference; node kinds are computed from these inputs, not accepted as labels |
| `CaptureAssumption` | Distinct assumption identity, exact source/leaf/method/argument and process event/run bindings, capture and source-fidelity assertions, and reader-admitted `AdmissionBasis`; print the assumption and basis in results |
| `Reference` | Ordered history plus one choice for every slot; membership in the guarded product family is required |
| `Observable` | `status ClaimId` at its fixed atom, or `audit ClaimId WitnessId Profile` |
| `Target` | `status ClaimId PublicStatus`, including a blocked conditional label, or positive `audit ClaimId WitnessId Profile` |
| Status/audit result | Complete ordered family rows with history, assignment and rejected reason or accepted status/audit checks; exact total/accepted/rejected counts, and the fixed-witness aggregate verdict for audit |
| Stability/sensitivity result | Observable, counts, whole/accepted-domain stability or reference and all differing rows; slot sensitivity additionally returns every minimal changed-slot set and a realizing row |
| Minimal-assumptions result | Target, catalog, counts and every minimal literal set with its surviving family and immediate-deletion countercompletions |
| `LocalityCheck` | Checked node/support correspondence, node/compiled-edge differences, both ancestry regions and success/failure of the sufficient test |
| `ImpactResult` / `ImpactCertificate` | Both source snapshots and identities, exact rejection/acceptance transitions, fixed query atoms, before/after full statuses where defined, changed/unchanged partitions, node/support maps, graph differences, locality checks and exact read keys/values |
| `VerificationResult` | Verified or the closed certificate fault described above, preserving the request label |
| `RunRefusal` | Closed malformed, syntax, unsupported, version, usage, I/O and limit cases with typed location/limit details; decode text is diagnostic only |

`InquiryLimits` counters apply to the whole document, not separately to each request. Each declared bound is also capped by a fixed checker ceiling. The embedded event bound limits the deduplicated recorded/universe carrier. The history bound is the minimum of the embedded completion bound and inquiry history bound, and counts all unguarded compatible histories, including those excluded by source guards. `sources` counts every observed family row, rejected rows included, plus each endpoint checked for every impact or verification request; repeated requests consume the same shared budget again. `source-bytes` bounds the UTF-8 input document, including pairwise snapshots and certificates, and `declarations` bounds the aggregate declarations passed to source checking, including repeated materializations and pairwise endpoints. `search-steps` counts each attempted history extension/stop and slot extension. `pairs` counts each observation comparison, graph node/edge comparison and read-value comparison across all requests. `subsets` counts each visited assumption subset across all requests. All counters are checked before the charged operation.

Exactly at a cap is legal if the entire computation finishes there; discovering one additional output or required operation refuses the entire document. Product and powerset upper bounds are allocation guards only: a loose upper bound must not refuse a guarded family that fits the actual counters. Use bounded traversal rather than allocating the upper-bound product. Limits cover pairwise-only documents and certificate verification as well as family analyses; no partial answers escape.

Implementation chooses the new numeric checker ceilings once, documents them as fixed version-1 constants and supplies exact-at-cap and cap-plus-one fixtures for every counter. Increasing a frozen ceiling requires explicit review; a ceiling is never optional.

Emit embedded queries first in their original order, then wrapper requests in their order. Labels must be unique across both lists. Tag history-verdict results separately from source-family results and retain distinct unguarded history and guarded source counts. Embedded verdicts retain P0 semantics and limits; embedded audits intentionally use the new checked-source product semantics. New-runner witnesses need membership proofs, not byte equality with P0 witnesses.

Embedded P0 verdict queries use the complete P0 history family, before source-choice guards; their count never silently shrinks when a source guard excludes a history. Source-family queries report their guarded product count separately. Embedded audits use the product source family and the same fixed submitted witness as wrapper audits. Construct the problem through `Document.problem`; do not call `Wire.run` and discard its audit error. Prove P0 verdict/count agreement, with the new wrapper's documented witness order and the old executable's bytes unchanged. Preserve request order and labels, and validate duplicate labels and unresolved references. A checker-rejected source appears inside a completed inquiry result (exit 0); outer malformed/syntax/version/usage/I/O errors exit 2 and unsupported forms/limits exit 1. Emit one envelope on stdout with empty stderr and no partial result.

The `verify-impact` request decodes a typed `ImpactCertificate`, reruns the shared observer on both supplied sources, and returns a labeled `VerificationResult`. Prove its `verified` case equivalent to `verifyImpact = true`; false claims return `invalid-certificate` with a closed fault. A malformed wire certificate is an outer `malformed` refusal. Field mutations therefore have an executable file-driven path, and no desired status equality is accepted as a premise.

This adds the Lean reference codec and runner required to exercise all P1-P5 results. It does not implement the P6 Haskell door. P6 must support both the unchanged P0 protocol and this wrapper, and P7 must compare each against the corresponding Lean executable. This extra codec burden is an explicit approval cost, not work hidden in a later stage. Old `run_audit` and `run_answers` remain scoped to `Lara.Process.Wire.run` and true; new `inquiry_run_answers` covers every result constructor. If a future choice changes the old runner instead, remove/replace `auditFault`, `verdictQuery`, `run_audit`, `run_answers`, their `AxCheck` rows, affected `ProcessWire` tests, audit goldens and the version-1 prose together; retaining the old theorem statement would be false.

## Alternatives considered

The wrapper is recommended because it preserves the frozen P0 contract while giving source choices and richer results a typed home. It costs a second outer codec and an explicit compatibility theorem. A `process-input 2` cutover would consolidate the protocol but requires version-1 dispatch/support, migration rules, revised documentation and P6/P7 budgeting; it cannot be treated as an optional field in version 1. A Lean-only function API would avoid codec work, but would leave P1 audits and P3/P5 results unreachable from the existing runner, so it does not meet this plan's end-to-end acceptance.

Finite typed declaration fragments give source completions explicit choices while reusing the existing surface semantics. Their product can be large, and each completion needs elaboration and checking. A supplied status/graph oracle would bypass the checker, while automatic natural-language interpretation needs an unprovided scientific mapping. Complete source snapshots are accepted for pairwise impact; using one full snapshot per product row would also be sound after checking but duplicates input material and obscures which slot changed.

## Tradeoffs

The largest proof risks are the stable identity lift from compact checked nodes, exact evidence/source admission ordering, and public blocking after graph locality. The source observer must preserve source rejection distinctions while integrating the existing admission, group and evidence phases. P3's minimality proof is finite but combinatorial; limits must cover the analysis itself, not just the number of histories. P4/P5 recheck both sources, so this PR establishes correctness and explanatory locality, not an incremental performance claim.

The approved audit specification requires conditional declarations to be printed as assumptions and capped at conditional kind; modeled certificate replay cannot become evidence of a real observation. Checked BHL method adapters need finite executable construction and explicit proof obligations for every used binding field. This additional P1 work is included; missing guarantees or artifact checks cannot be replaced by defaults. Source-slot semantics and wrapper version 1 are approved. Numeric ceilings follow the implementation rule above; P0 and core semantics remain unchanged.

## Migration

No existing consumer migrates during this plan review. When implementation lands, add the new reference executable and fixtures while running all legacy gates unchanged. Update `docs/theory-process.md` to describe both entry points and the shared observer, with current-tense contracts only; update `docs/implementation.md`, `lean/README.md` and `docs/spec.md` only where their command/wire indexes require it. Keep alternatives and approval history in this living plan and the research record, not durable documentation. When the unified implementation lands, move durable contracts into those subject documents and delete this executed plan.

When implementation lands, explicitly replace `docs/theory-process.md:213`'s statement that every stage reads and writes `process-input 1` with the two-entry-point contract. Until then the durable document remains unchanged.

### Which files does each task own?

Every new path below is proposed. Existing paths were inspected for the named integration seam. One integration owner owns shared imports, axiom rows, build/gate registration and final documentation. The P1 source contract must settle before P3/P5 code is split among workers.

P1a first settles and implements the shared observer, total kind/provenance calculation, fixed query bindings and stable declaration identity contract. Its source correspondence, kind meet/no-promotion, graph-lift and support-exactness proofs must land in the working tree before P2/P3/P4/P5 implementation is split among workers. P1 audit construction then consumes that boundary; later stages share it rather than inventing adapters. This dependency order changes no acceptance scope: all stages still ship together in one PR.

| Task | Create | Modify | Responsibility |
| --- | --- | --- | --- |
| P1 source/audit boundary | `lean/Lara/Process/Source.lean`, `lean/Lara/Process/SourceWire.lean`, `lean/Lara/Process/SourceAudit.lean`, `lean/Lara/Process/Family.lean`, `lean/Lara/Examples/ProcessSource.lean` | `lean/Lara/Surface/Source.lean` only for a proof-retaining, diagnostic-preserving helper equivalent to the existing door | Typed source codec, exact checker/evidence run, rejection sum, stable witness identity, materialization and existing BHL certificate construction |
| P2 generator | `lean/Lara/Process/Enumerate.lean`, `lean/Lara/Examples/ProcessEnumerate.lean` | none in P0 | Bounded generation and reference equivalence |
| P3 analysis | `lean/Lara/Process/Analysis.lean`, `lean/Lara/Examples/ProcessAnalysis.lean` | `lean/Lara/Process/Inquiry.lean` only for general finite observable lemmas | Rejection-aware stability, reference/single/joint sensitivity, every subset-minimal assumption set |
| P4 locality | `lean/Lara/Process/Locality.lean`, `lean/Lara/Examples/ProcessLocality.lean` | `lean/Lara/Process/Revision.lean` only for reusable finite ancestry lemmas | Checked graph alignment, difference test and grounded locality |
| P5 impact | `lean/Lara/Process/Impact.lean`, `lean/Lara/Examples/ProcessImpact.lean` | none in core | Source reads, complete public status transitions, recomputable certificates |
| Shared protocol/delivery | `lean/Lara/Process/InquiryWire.lean`, `lean/Lara/Process/InquiryRun.lean`, `lean/Lara/Process/InquiryRunMain.lean`, `lean/Lara/Process/InquiryExampleMain.lean`, `scripts/check-inquiry-run.sh`, `fixtures/process/inquiry/` | `lean/Lara.lean`, `lean/AxCheck.lean`, `lean/lakefile.toml`, `Makefile`, `docs/theory-process.md`, `docs/implementation.md`, `docs/spec.md`, `lean/README.md` | All input/output constructors, executable examples, codec laws, goldens and command documentation |

### P1: check every materialized source and audit the submitted witness

- [ ] Add kernel-decidable source examples before implementing the observer: accepted single leaf, policy reject, group quarantine, escalated group reject, duplicate declaration, core rejection, evidence mismatch and a required extraction with no evidence context. Assert typed rejection reasons, including mixed admission/evidence/core failures.
- [ ] Compose the existing presentation codecs into the typed source envelope, then implement the proof-retaining observer with the evidence-policy syntax guard, ordinary assembly/admission, all-declared evidence replay and core finish in that order. Prove projection to `sourceWithEvidence`, exact source/audit output agreement and the `CertifiedSource`/`AcceptedRun` construction using existing BHL helpers. Retain detailed rejection payloads and prove their erasure agrees with existing errors. No core or `applyUpdate` behavior changes.
- [ ] Define typed declaration fragments, deterministic append/materialization, slots and guarded product completions. Prove exact membership and the no-slot P0 specialization. Keep invalid materialized sources in the family as rejected outcomes.
- [ ] Resolve claim/witness names, lift checked graphs to stable declaration identities, and prove label preservation and selected-support exactness. Test an earlier pruned declaration shifting every later checked index.
- [ ] Implement the closed conditional, ledger and BHL audit specifications, constructing every `BridgeCertificate` premise from the authoritative source and existing BHL helpers. Prove computed audit iff the reused warrant/coverage predicate, fixed-witness quantifier order, no hypothetical promotion and fail-closed missing metadata. Test swapped witnesses, false preconditions, failed siblings, stale bindings and mixed admission/evidence/core failures.
- [ ] Add fixed-atom claim-change, forged-observed replay, inadmissible-attacker reinstatement and defender-kind examples; prove every checked node's kind calculation and profile graph agree with the warrant model.
- [ ] Add explicit `AxCheck.lean` rows for every public theorem and countermodel in this task; update the source-boundary portion of the subject document only after definitions are settled.

### P2: enumerate exactly and stop at declared limits

- [ ] Add exhaustive small-model examples comparing reference histories and slot products with generated families, including contradictory orders, repeated record entries, base/universe overlap, empty universe, invalid current dataset versions and all-rejected source alternatives.
- [ ] Add an optional-event fixture emitting both omission and valid extension, and a valid short history whose optional extension is invalid.
- [ ] Implement prefix history DFS and guarded slot traversal with bounded counters. Prove soundness, completeness, no duplicates, finite-set equality to the reference and cap-plus-one refusal correctness. Do not prune partial coverage without the corresponding lemma.
- [ ] Prove count/verdict invariance and deterministic new-runner witness selection. Test that v1 witness bytes stay unchanged because its runner is untouched.
- [ ] Add boundary examples at and above each limit, including search exhaustion with few accepted histories and powerset growth with few source completions. No partial rows or positive result may escape a refusal.
- [ ] Add axiom audit rows and document exactly which limits count histories, source products and analysis work. Do not raise the P0 event ceiling as part of this PR.

### P3: implement all exact inquiry analyses

- [ ] Define full-observation equality, nonempty stability, reference sensitivity and their Boolean specializations. Prove compatibility with the landed `Inquiry` laws; test empty, all-accepted, mixed-rejection and all-rejected families.
- [ ] Enumerate each candidate against the named reference, requiring the same history; compute its exact changed-slot set and observation difference. Prove singleton equivalence and joint-set inclusion minimality; return all minimal sets. Test conjunction at reference `(absent, absent)`, with no singleton flip from that reference, and an infeasible combination excluded by guards.
- [ ] Enumerate the finite assumption catalog's subsets with canonical ordering; require consistency and all-accepted target agreement. Return every subset-minimal set with countercompletion witnesses for deleting each literal. Prove soundness, completeness and minimality, including the empty-set case.
- [ ] Test duplicate/equivalent literals, contradictory literals, multiple incomparable minimal sets, a shorter and a longer inclusion-minimal set, a restriction leaving only rejections and an empty restriction. Assert exact witnesses and exact acceptance/rejection counts.
- [ ] Add axiom rows and result codec cases for every analysis; no single-sensitivity-only substitute for the joint analysis and no one-minimum substitute for all minimal assumptions.

### P4: prove graph-difference locality

- [ ] Add countermodels first: a new attacker outside the old graph; an attack propagated through a shared discharge subterm; a node deletion; new complete support from a hole; and unrelated self-attack. Assert the false raw-name/old-ancestor criteria fail.
- [ ] Implement stable-identity graph alignment, node/edge symmetric differences and finite backwards reachability over both graphs. Prove the checked test implies the existing directional-locality premises without assuming the desired label equality.
- [ ] Lift per-support label equality to complete-claim status equality, requiring exact support correspondence. Prove reindexing and pure declaration permutation invariance with query identities held fixed.
- [ ] Test unchanged status despite a failed locality test to pin its sufficient-only scope. Add all theorem/countermodel axiom rows and grounded-semantics-only scope documentation.

### P5: certify source and full public-status impact

- [ ] Add tests where policy quarantine changes the public tag with unchanged ordinary grounded status, both blocked results have different conditional labels, normalization changes support membership, a fresh attacker reaches an old support, and a backend/discharge dependency changes.
- [ ] Implement the closed source read keys and exact observations above. Prove the complete-read preservation statements before using any smaller recorded footprint; use conservative whole-table reads where necessary.
- [ ] Compose graph locality, complete support equality and blocking equality into a full `Driver.PublicStatus` preservation theorem. Reuse `BHL.ordinaryStatus`; do not substitute `Update.PublicReport`.
- [ ] Generate exact changed/unchanged query partitions and source-rejection transitions. Implement certificate recomputation and prove acceptance implies the claimed input binding, transition and locality facts. Mutate each certificate field, query, snapshot, node map and conditional status in tests; the verifier must reject stale or false claims.
- [ ] Include the existing unchanged-status/different-entitlement and failed-sibling witnesses. Prove no theorem transports entitlement from public-status equality. Add axiom audit rows and the full-public-status contract to the subject documentation.

### Integrate the complete PR

- [ ] Implement all wrapper constructors and strict codecs together with canonical round trips, injective spelling tables and renaming invariance for new slot/choice/argument identities. Keep the embedded process names independently interned and core names in their own namespace.
- [ ] Add `inquiry-run` and `inquiry-examples` Lake targets, run the shared observer once per completion, and make every printed result trace to the corresponding analysis theorem. Prove verdict-only/no-slot agreement with P0, preserving its audit refusal theorem at the old entry point.
- [ ] Add the fixture suite and `scripts/check-inquiry-run.sh`; extend `make process-theory` to run both old process gates and both new inquiry executables/goldens. Assert stdout, stderr and exit codes independently; do not regenerate old goldens.
- [ ] Finish reference docs and run the commands below after all task branches or edits are integrated. Review all P1-P5 code/proofs/fixtures together in one PR. No P1-only or P1-P3 partial delivery satisfies issue #22's group B.

## How will acceptance be checked?

All names in the fixture column below are proposed files under `fixtures/process/inquiry/`, paired with `.expected` goldens. They must be executable input documents, not prose scenarios or hard-coded runner answers. The example modules provide independent kernel-checked facts about the same material. Reuse existing small source fixtures for actual typed supports/attacks instead of constructing graphs directly.

For `joint-only`, build checked source arguments whose compiled graph has `b1 -> target` and `b2 -> target`, with optional unattacked defenders `d1 -> b1` and `d2 -> b2`. Use distinct rule occurrences for the two defender undercuts so neither disables both attackers; include every conflict the checker requires. At reference `(d1 absent, d2 absent)`, the target is defeated, and either single defender still leaves it defeated. Both defenders make it justified. Prove this graph shape from the actual checked source before asserting the sensitivity truth table; the runner does not accept these edges as an oracle.

| Requirement | Fixture / exact construction | Required result |
| --- | --- | --- |
| P0 compatibility | `p0-verdict.sexp`: embed `fixtures/process/run/empty-universe.sexp`, no source slots | P0 history verdict/count agree; all old process fixtures unchanged |
| Strong P0 compatibility | `p0-unknown.sexp`, `p0-guard.sexp`, `p0-rejected.sexp`, `p0-embedded-audit.sexp` | Unknown verdict witnesses remain valid; guards and all-rejected source rows leave embedded verdict/count unchanged; submitted embedded audits execute under the new semantics |
| Checked source family | `source-rejections.sexp`: choices accepted, policy reject, core reject and failed evidence extraction | All choices counted; rejection kind/location retained; no fabricated AF |
| Submitted audit | `fixed-witness.sexp`: two completions with alternating support witnesses | Claim-level existential cannot become a positive fixed-witness audit |
| No promotion | `hypothetical-audit.sexp`: simulated source choice with valid replay | Strict profile never reports observed entitlement |
| Audit metadata | `ledger-sibling.sexp`: ledger bound one, same source graph, second failed family run in one history | Bound check fails only in the two-run completion; public status stays equal, fixed-witness warrant changes |
| Fixed query identity | `fixed-query.sexp`: choices change the formal proposition of the same named claim | Every status still queries the fixed atom; the mismatched declared association fails audit |
| Forged observation | `forged-observed.sexp`: slot leaf declares observed and passes replay | Derived hypothetical cap remains; strict audit fails |
| Unknown attacker metadata | `unknown-attacker-kind.sexp`: otherwise warranting witness has an attacker without kind metadata | Framework metadata check prevents every positive audit; ordinary status is still computed |
| Profile acceptance | `profile-reinstatement.sexp`: fully kinded inadmissible attacker is filtered | Profile witness can become accepted; ordinary public status remains separately reported |
| Optional history prefixes | `optional-prefix.sexp`: optional executable event and a separate invalid extension | Both omission and valid extension occur; valid shorter history survives its invalid extension |
| Empty family | `inconsistent.sexp`: contradictory precedence | Inconsistent; no stability or conditional certificate from an empty domain |
| Stability/rejection | `mixed-stability.sexp`: same accepted status plus one rejected source | Accepted-only result labeled; whole-outcome stability differs |
| Single/joint sensitivity | `joint-only.sexp`: two independent Boolean slots, reference `(absent, absent)`, with observable conjunction | Minimal joint set of both slots relative to that reference; no singleton flip from the reference |
| Minimal conditions | `minimal-conditions.sexp`: alternative supports requiring either one condition or a separate pair | Return both incomparable subset-minimal sets, not only the smaller one |
| Locality | `new-attacker.sexp`, `shared-discharge.sexp`, `unrelated-self-attack.sexp` | New/closure attacker prevents certificate; unrelated grounded component permits it |
| Complete public status | `blocked-conditional.sexp`: both snapshots blocked, conditional status changes | Query appears changed although both five-valued projections are blocked |
| Dependencies | `normalized-support.sexp`, `backend-dependency.sexp`, `reindex-hole.sexp` | Recomputed support/read/identity facts prevent false unchanged certificates |
| Rejections in impact | `impact-rejected.sexp`: accepted/rejected and rejected/rejected pairs | Typed transition, no invented before/after status |
| Certificate verification | `tampered-certificate.sexp`: each tested mutation changes a bound field | Verification fails; no input-status equality supplied as a premise |
| Limits and errors | `limit-sources.sexp`, `limit-subsets.sexp`, `limit-search.sexp`, `bad-version.sexp`, `bad-binding.sexp` | One refusal, correct exit, empty stderr, no partial answers |
| Failure precedence | `allowlist-structure-fail.sexp`, `admission-evidence-fail.sexp`, `evidence-core-fail.sexp`: deliberately pair failures in the named phases | Duplicate allowlist wins before assembly; ordinary admission then wins before evidence; evidence then wins before core |

Commands to run after implementation, from repository root unless shown otherwise:

```bash
# Focused theorem build and executable examples.
(cd lean && lake build)
(cd lean && lake exe inquiry-examples)
# One file-driven smoke, followed by every golden and boundary refusal.
(cd lean && lake exe inquiry-run ../fixtures/process/inquiry/joint-only.sexp)
bash scripts/check-inquiry-run.sh
# Includes unchanged P0 checks plus new inquiry examples/goldens after registration.
make process-theory
# Required before unified PR review; includes all Lean proofs, axiom coverage/audit
# and existing Haskell-Lean gates. P7's new inquiry cross-check is not claimed here.
make local-gates
```

Expected outcome: the theorem build and examples succeed; the joint-only smoke prints an `inquiry-result 1` containing exactly the two-slot minimal witness; each golden gate prints its actual fixture count and no mismatches; `make local-gates` succeeds without updating corpus or old goldens. These are future acceptance commands, not tests run while drafting. The implementation PR must report actual output and any allowed changes, not copy these expectations as evidence.

Document-only checks, authorized for this planning task:

```bash
/home/yfhe/.claude/skills/write-doc/scripts/check-style.sh plans/inquiry-p1-p5.md
# Check every existing cited file/range, distinguish every proposed path,
# inspect stage/acceptance coverage, and scan for unresolved placeholders.
```

Plan review covers the exact source/evidence phase ordering, preservation of `run_audit`, the shared finite family for sensitivity and minimality, and retention of blocking and its conditional label. Implementation must prove these obligations. No expensive code test is required for this document-only change.

## Next Steps

1. The wrapper, source-choice semantics and audit trust boundary are approved as a plan after the corrections above. All implementation checkboxes remain open; approval does not claim that code or proofs exist.
2. On a separately assigned implementation task, settle P1a and its proofs before splitting later work. Resolve any newly discovered contract conflict in this living plan without dropping acceptance requirements or using arbitrary runtime oracles.
3. Deliver the checked boundary, generator, analyses, locality, impact and complete runner together before requesting the single PR review. This review performs and authorizes no implementation, commit, push or PR. Record material design corrections only after review is complete; no empirical utility claim follows.
