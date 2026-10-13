# Corrected checked-inquiry P8 report
**Date:** 2026-10-13

## TL;DR

The single approved corrected P8 measurement completed all 96 documents, with exact oracle agreement for both drivers on all 80 unique input hashes and successful real consumer checks on every capture. The authored cases expose distinctions that a report of public statuses alone omits: equal claim status can accompany a failed fixed-witness audit, and an unchanged status can lack a sufficient locality certificate. The run stayed within its local budget, but its one-shot timings and correlated synthetic inputs do not establish performance advantages or research-workflow benefits. The P9 decision table therefore supports protocol drafting only; researcher review of these results is pending, and no live P9 run, agent call, paid compute or additional measurement is authorized.

## Which evidence and approval does this report cover?

The evidence directory is `20261013T071248Z-317f210-corrected`; its directory timestamp is not the measurement start. [run.json](run.json) records start `2026-10-13T07:13:22.162373+00:00` and internal run ID `20261013T071322.162373Z-317f210ab2f4`. [summary.json](summary.json), [results.jsonl](results.jsonl), [summary.tsv](summary.tsv), [raw captures](raw/) and the [self-contained archive](evidence/) are the sealed measurement record. This report reads those artifacts without another driver or consumer invocation. Numeric diagnostic tables below apply to each driver, whose reported results agree, unless a table names a driver separately.

| Identity or authorization | Exact retained binding |
| --- | --- |
| Original approval | Yifeng He, 2026-10-12; approval commit `a904130af7781fd5b308d049be7f4f43bdf9e256`; approved plan blob `2edd1512d4cb0f242392db14ee7978d38106bf70`; plan SHA256 `42a48cd1f3ccf59ae992c39958b51a4210a216e6c2586fa1c67f5354a9558f27` |
| Corrective runtime | `317f210ab2f4e5ea070dcae75218f056373e142d` |
| Final reviewed candidate | `7a90fca1d679013815f6a31f241af5181f4cbeec` |
| Committed metadata-only input freeze and measurement runner | `1f1f101bc9df6c3e527b93dc911376b3ec57f916` |
| Frozen manifest SHA256 | `01dfe6800964d09f4b87028931337d2be93badae63192e5f4aace80de5f7b9da` |
| Frozen protocol SHA256 | `9b60b965521cdfe0290443d3030fbb2ee6dfbee995934a6947aacaaef98c853c` |
| Final candidate protocol SHA256 | `19e582eb117fba09102072a4b3e0b29dff76d9201f456663baa83a8131585ee0` |
| Final candidate manifest SHA256 | `59225ebd79b1bb6f667f9e73db3fdbce8b2277dbf3499ff31b28c24b6d9c46fd` |
| Approved data-policy SHA256 | `b12df70659359ad7c6da4acd16d127a6d98693b8385c0c99bcae58897bbfe341` |

The [original correction receipt](../../../../evaluation/inquiry-p8-corrected/researcher-approval.json) records “I approved it, forget to mark” on 2026-10-13 without inventing an earlier approval date. It binds candidate `71c1cba9da9863440eaa2873bbd223dbe6ba57b1` and protocol SHA256 `181a5363f8778942dbf00971efe63b0659529f486ecba5acef2a1876bf9bcc10`, including the distinct-T07-support amendment and residual 40-slot timeout risk. The [test-fixture receipt](../../../../evaluation/inquiry-p8-corrected/researcher-approval-test-fixtures.json) binds candidate `bfc6d1ecc538f3456ab3e98df6f314e0611f91b1` and protocol SHA256 `663e6c92823bfce9cfa6dd53920e089c7c717e3a1a20e01f0893f353570a8bec`. The [effective provenance receipt](../../../../evaluation/inquiry-p8-corrected/researcher-approval-provenance.json) binds the final candidate above and retains both prior receipts. The instruction “checkout a new branch and complete the next, finish and pr directly” authorizes the reviewed issue #53 helper/provenance correction and the already-approved single attempt, not another budget. The source-axis clarification counts leaf-root groups, with two AST declarations per group per endpoint. None of these approvals is approval of this result report or of P9.

The [independent input review](evidence/suite/independent-review.json) is explicitly AI-executed, not researcher assent. It retains independent judgments for 91 unchanged cases and fresh inspection of the five T07 repairs, without using production-driver answers as expectations. The [preflight receipts](../preflight-20261013-corrected/) retain successful local gates, both Haskell test suites, all 68 inquiry Python regressions, native/Lean/consumer builds and final [repository preflight](../preflight-20261013-corrected/repository-preflight.json) over 217 suite artifacts. The parent supplied the completed-gate record, including the 7,192-declaration AxCheck axiom audit; this report does not rerun those gates. Earlier [quality-pin preflight failure](../preflight-20261013-corrected/quality-pin-failure.json) and withdrawn initial readiness review remain retained; that failure started no measurement. The original [20261012 incomplete run](../20261012T225824Z-a904130/), [its replay](../20261012T225824Z-a904130-replay/) and [reproduction receipt](../20261012T225824Z-a904130-reproduction.json) remain evidence of the Lean T11 40-slot timeout and original T07 oracle disagreement. The correction neither replaces that attempt nor uses it as a timing baseline.

## What passed, with which denominators?

Oracle agreement, protocol validity, real consumer acceptance and cross-driver agreement are separate checks. Each driver returned a result on 96/96 documents, passed the oracle on 96/96 captures, passed protocol checks on 96/96 captures and passed consumer decoding on 96/96 original-input/output pairs. Cross-driver agreement is 96/96 documents. All 96 pair checkpoints passed their required predicates; there are no missing invocations, unattached captures or semantic discrepancies. Unique-input correctness requires every duplicate capture to agree.

| Stratum | Documents | Unique input hashes | Native oracle / validated correctness | Lean oracle / validated correctness | Captured requests per driver | Distinct captured result-body projections within stratum |
| --- | ---: | ---: | --- | --- | ---: | ---: |
| Development controls | 16 | 16 | 16/16; 16/16 | 16/16; 16/16 | 20 | 17 |
| Authored controls | 16 | 16 | 16/16; 16/16 | 16/16; 16/16 | 37 | 29 |
| Generated variants | 64 | 58 | 58/58; 58/58 | 58/58; 58/58 | 259 | 64 |
| All new inputs, authored plus generated | 80 | 64 | 64/64; 64/64 | 64/64; 64/64 | 296 | Not an additive semantic denominator |
| All documents | 96 | 80 | 80/80; 80/80 | 80/80; 80/80 | 316 | 80 |

Development goldens are disclosed conformance controls, not held-out or newly independent research evidence. The ten duplicate-content groups in `summary.json.duplicate_content_groups` account for 16 repeated documents beyond the 80 unique hashes. Within-stratum counts overlap across strata and must not be added. The 80 diagnostic projections are deduplicated by captured result-body hash, not input hash or submitted-request identity; their equality to the unique-input count is incidental. Repeated work and generated variants do not add independent semantic or research tasks.

| Generated axis | Documents / within-axis unique hashes | Levels | Input-byte range | Observation |
| --- | --- | --- | --- | --- |
| Inert singleton slots | 16/16 | 0, 1, 4, 40 | 2,987–26,184 | Original histories, observations and sensitive slots preserved |
| Inert source declarations | 16/16 | 0, 1, 4, 16 groups | 11,425–92,911 | Adds 0, 2, 8, 32 declarations per endpoint; status/partition preserved |
| Additional assumption literals | 16/16 | 0, 1, 2, 4 | 2,987–22,740 | Adds no new minimal satisfying sets |
| Repeated requests | 16/16 | 1, 2, 4, 8 copies | 6,392–169,183 | Preserves answers under fresh labels; charges repeated work |

Each axis has exact oracle/validated correctness 16/16 within-axis hashes for each driver. There are only 58 distinct hashes across all four generated axes because their unchanged levels overlap. All 64 generated documents returned results, with zero refusals. The axes are separate manipulations of four seeds each, not a factorial or random sample.

## Which family outcomes and witness audits were observed?

The base-case table reports rows within each request. A status and an audit request over the same family do not create two independent families. The ledger retains all 316 requests per driver at `results.jsonl → drivers.DRIVER.diagnostics.requests`, including rows, histories, selections and exact rejection payloads where that request kind exposes them. Stability, verification and impact bodies do not expose every such field. Generated cases preserve the seed's outcomes under the declared manipulation. Empty accepted domains use the frozen false accepted-only-stability rule, including the empty inconsistent family. Rejected rows have no public status.

| Case / observable | Total / accepted / rejected rows | Whole-outcome stability | Accepted-only stability |
| --- | --- | --- | --- |
| `source-rejections`, status | 4 / 1 / 3 | false | true, accepted denominator 1 |
| `mixed-stability`, status | 2 / 1 / 1 | false | true, accepted denominator 1 |
| `inconsistent`, status | 0 / 0 / 0 | false | false, accepted denominator 0 |
| T09, status | 2 / 0 / 2 | true | false, accepted denominator 0 |
| T10, status / fixed-witness audit | 2 / 2 / 0 | true / false | true / false, accepted denominator 2 |
| T11, status | 6 / 6 / 0 | false | false, accepted denominator 6 |
| T12, status | 4 / 4 / 0 | false | false, accepted denominator 4 |
| T13, status | 2 / 2 / 0 | true | true, accepted denominator 2 |
| T14, status | 2 / 2 / 0 | true | true, accepted denominator 2 |
| T15, status / fixed-witness audit | 2 / 2 / 0 | true / false | true / false, accepted denominator 2 |

The three `source-rejections` buckets each contain 1/4 rows: `(source (source (structural (admission-rejected bad))))`, `(source (core (signature (ground-ill-sorted))))` and `(source (evidence (admission-error (extraction) mismatched (absent) mismatch)))`. T09's sole bucket contains 2/2 rows, `(source (source (structural (duplicate-leaf-id seed))))`. `mixed-stability` reports 1 rejected row out of 2 but its stability-only result emits no exact rejection payload. The `inconsistent` history verdict has zero completions; this is neither a source rejection nor an operational failure.

| Fixed-witness request | True / false / rejected rows | Universal fixed-witness audit | Allowed grades in declared profile |
| --- | --- | --- | --- |
| Development `fixed-witness` | 1 / 1 / 0, denominator 2 | false | hypothetical, observed |
| Development `hypothetical-audit` | 0 / 1 / 0, denominator 1 | false | observed only |
| Development `forged-observed` | 0 / 1 / 0, denominator 1 | false | observed only |
| T10 `audit` | 1 / 1 / 0, denominator 2 | false | hypothetical, observed |
| T15 `audit` | 1 / 1 / 0, denominator 2 | false | observed only |

All five requests fix claim `c0` and submitted witness `w0`; each profile accepts `complete` and `count-bounded` coverage, asks for family-wise error rate `1/20`, has empty sampling requirements and requires grounded justification. T10 and T15 independently annotate complete kind metadata, a known provenance ledger for family `fam` and run `run0`, count 1 bounded by 1, result 1 and warranted level `1/40`. Their reader coverage defaults to `open-world` because no coverage admission exists; it is not silently promoted to complete coverage. The annotation explicitly records that not all admitted coverage is accepted by the profile. These component and coverage facts are construction annotations, not extra runtime audit output; the family audit exposes final booleans only. Development controls have declared profiles/bindings but no independent component annotation, which is a reporting coverage limit.

In T10, both rows publish justified status, but only slot-0 choice 0 retains the selected hypothetical argument for `w0`; choice 1 lacks it, so another supporting argument cannot rescue this submitted witness. In T15 both rows also publish justified status. Row 0 binds the modeled capture exactly to source and run `run0`, with observed selected grade and a true audit; row 1's capture names `aux`, fails the exact binding and has conditional selected grade and a false audit. Its argument remains present and grounded-justified. Exact source ASTs, claim/witness bindings, admitted capture assumptions, kind specifications and per-row component tables are retained in `diagnostics.declared_input_annotations` and `diagnostics.construction_annotations.values` for those cases, plus the archived input/oracle bytes. These are modeled admissions, not physical capture observations or independently established empirical guarantees.

## Which choices and conditional assumptions mattered?

Sensitivity is relative to the submitted reference and finite family. T11 and T12 report reference membership as true both from captured family rows and from independent annotations. The two development sensitivity controls do not expose a captured-family membership comparison or an independent membership annotation in the report, so those fields are null rather than claimed verified. Each listed minimum is nonempty and has cardinality 2; no singleton minimum occurs. Every differing row and first realizer, including its complete history and selected fragments, is retained under `differing_rows` and `first_declaration_order_realizers`, not discarded after computing counts.

| Case / requests | Total flips / family rows | Same-history flips / differing rows | All minimal slot sets | First declaration-order realizer |
| --- | --- | --- | --- | --- |
| `reference-sensitivity` / `sens` | 1/4 | 1/1 | `{0,1}` | Empty history; choices `(0=1,1=1)` |
| `joint-only` / `slots` | 1/4 | 1/1 | `{0,1}` | Empty history; choices `(0=1,1=1)` |
| T11 / `sensitivity`, `slots` | 2/6 each | 2/2 each | `{0,1}` once | Empty history; first `(0=1,1=1)`, then differing row `(0=2,1=1)` |
| T12 / `sensitivity`, `slots` | 1/4 each | 1/1 each | `{0,1}` | Empty history; choices `(0=1,1=1)` |

Conditional sets must leave a nonempty, rejection-free family satisfying the accepted target. In the table, `sN=C` means slot N selects choice C; `sN≠C` is the corresponding inequality. Counts of examined subsets are the deduplicated finite catalog's power-set size, derived from construction, not measured internal loop iterations. The full catalog and every surviving completion/deletion countercompletion are retained in each assumptions request's `catalog_before_dedup`, `catalog_after_dedup` and `minimal_sets` fields.

| Case / target | Catalog before / after dedup | Derived subsets | Every minimal set; surviving rows / original family | Deletion countercompletions |
| --- | --- | ---: | --- | --- |
| `minimal-conditions`, published justified | 3 / 3 | 8 | `{s0=1}`: 4/8; `{s1=1,s2=1}`: 2/8 | Delete s0: `(0,0,0)`; delete s1: `(0,0,1)`; delete s2: `(0,1,0)`; all empty history |
| T09, published justified | 2 / 2 | 4 | None, 0 minima / 4 subsets | No returned members, so 0 applicable deletions; all original rows rejected |
| T10, positive `c0`/`w0` audit | 2 / 2 | 4 | `{s0=0}`: 1/2; `{s0≠1}`: 1/2 | Each deletion exposes choice 1 in the retained four-event history |
| T13, published defeated | 2 / 2 | 4 | None, 0 minima / 4 subsets | No returned members; contradictory full catalog leaves 0/2 rows and cannot establish target |
| T14, published justified | 2 / 2 | 4 | Empty set: 2/2 | Empty minimum has 0 members, hence 0 applicable deletions |

For each assumption-axis seed T09/T10/T13/T14, catalog lengths before and after dedup are 2, 3, 4, 6 at added-literal levels 0, 1, 2, 4; derived subset counts are 4, 8, 16, 64. Minima remain respectively none, the two T10 singleton sets, none, and the empty set. Fresh undeclared-slot inequalities evaluate true in every row because `selectionFor` returns no choice; their predicate truth tables are retained construction facts, not evidence observations. There is no exercised catalog duplicate-elimination contrast, different-history flip, singleton minimum or empty-changed-set sensitivity contrast in these reported base sensitivity requests. The positive deletion witnesses are 3/3 returned members in `minimal-conditions` and 2/2 in T10; zero-member cases do not establish deletion coverage.

## What changed across source endpoints?

Across the 80 distinct captured result-body projections, eight impact bodies contribute acceptance classes: accepted-to-accepted 5/8, accepted-to-rejected 1/8, rejected-to-accepted 1/8 and rejected-to-rejected 1/8. The within-stratum counts are development 3/0/1/1 out of 5, authored 4/1/1/1 out of 7, and generated 4/0/0/0 out of 4, in that class order. These are body projections, not counts of separately authored pairs. Equal result bodies collapse, including T06 and T08; their distinct inputs and certificate context remain in the full ledger.

| Case or diagnostic contrast | Before → after full public status | Changed / unchanged query partition | Grounded locality / equal blocking |
| --- | --- | --- | --- |
| T01 identity | published justified → published justified | `[]` / `[t]` | true / true |
| T02 | published justified → absent (rejected) | `[t]` / `[]` | false / false; full-status comparison inapplicable |
| T03 | absent (rejected) → published justified | `[t]` / `[]` | false / false; full-status comparison inapplicable |
| T04 | absent → absent (both rejected) | `[]` / `[]` | false / false; full-status comparison inapplicable |
| `new-attacker`, `shared-discharge` | published justified → published defeated | `[t]` / `[]` | false / true |
| T05 and `blocked-conditional` | evidence-blocked defeated → evidence-blocked justified | `[t]` / `[]` | false / true |
| T06 and `unrelated-self-attack` | published defeated → published defeated | `[]` / `[t]` | true / true |
| Corrected T07 | published defeated → published defeated | `[]` / `[t]` | false / true |
| T08 declaration permutation | published defeated → published defeated | `[]` / `[t]` | true / true |

There are five applicable accepted-to-accepted query rows after body deduplication: 2/5 change full status and 3/5 do not. Grounded locality holds for 2/5; equal blocking holds for both of those 2/2; certified unchanged is therefore 2/5 of eligible queries, or 2/3 of actually unchanged queries. Certified full-status counterexamples are 0/2 certified queries. Blocked conditional changes are 1/5 eligible queries, also 1/2 changed queries. Grounded-local queries with changed blocking are 0/2, so that specific failure contrast has no positive coverage. T07 is the required unchanged-but-not-certified example: failed sufficient locality does not imply a status change. Locality is grounded-semantics preservation and does not transport process entitlement.

Rejected endpoints contribute zero applicable full-status queries: their status denominator is 0, not an invented gap, false value or unknown status. T02/T03/T04 retain duplicate-leaf rejection `(source (source (structural (duplicate-leaf-id seed))))` in the submitted certificate and independent endpoint annotations. Exact rejected-pair comparison uses a separate input-hash/body/verification-and-annotation context denominator of 2: T04 is equal (1/2), the development `impact-rejected` rejected pair is unknown (1/2), and different is 0/2. The latter lacks the bound verification/independent annotation needed to establish exact payload equality; an empty changed partition does not supply it. Complete payloads remain at `requests[].rejection_annotations.bound_certificate_evidence[].submitted_endpoint_rejections`, with their comparison context in `rejected_endpoint_comparison`, separate from public statuses. T01 through T04 and T08 endpoint certificates verify; T16 reports `verified` for its original certificate and `(invalid-certificate (false-read-evidence))` for its same-type changed read value. The development tampered certificate instead reports `(invalid-certificate (mismatched-snapshots))`. Neither invalid-certificate outcome is an inquiry refusal.

## What does the same-capture snapshot comparison omit?

`results.jsonl → drivers.DRIVER.diagnostics.snapshot_only` projects only full public statuses and row/endpoint identity from that exact capture. It deliberately omits family rejection/stability, fixed-witness audit, sensitivity, assumptions and dependency/source-transition diagnostics. No alternate input, query, checker run or agent is involved. T10's two snapshot rows both say `published justified`; the same capture's inquiry audit says true then false for `w0`, and its two alternative minimal assumptions each select the passing row. T15 likewise has two justified snapshot rows but only one exact modeled capture binding. These concrete contrasts show missing diagnostic information, not improved agent behavior.

A full-status snapshot does retain T05's conditional defeated-to-justified change inside `evidence-blocked`; collapsing that status to a bare “blocked” label would be a different, weaker comparison. T06 and T07 have the same defeated-to-defeated snapshot endpoints but different locality results. `source-rejections` shows why one accepted gap row cannot summarize its three rejected alternatives. Matched equal-status/different-audit groups and annotated assumption/capture contrasts are retained in `same_full_status_different_audit` and `same_full_status_different_assumptions_or_capture_annotations`; these groups are descriptive joins, not independent successes. Real capture fidelity, empirical truth and agent use of this information were not measured.

## What were the operational costs and limits?

The runner recorded one direct fresh process per driver per document, sequentially on CPU 0, alternating native-first at even manifest positions and Lean-first at odd positions. It used 192/192 authorized driver calls and 192 consumer calls, 96 for each driver's captures. Driver and consumer timeout, spawn-failure, independent-signal and all-signal counts are each 0/96 attempts per driver or corresponding consumer leg; successful infrastructure completion is 96/96 for all four legs. Aggregate measured evaluation time was 39,246.769306 ms of the 2,700-second budget, including consumer checks and scoring. Every direct driver call was below the 10-second cap. The no-concurrent-benchmark/agent condition is recorded in `run.json.budget`, not inferred from a host-wide workload monitor.

| Stratum | Documents per driver | Original input bytes, min–max (sum) | Native elapsed ms, min / median / max | Lean elapsed ms, min / median / max |
| --- | ---: | --- | --- | --- |
| Development | 16 | 2,169–27,144 (195,479) | 3.041834 / 5.647056 / 17.762016 | 65.217338 / 65.614335 / 65.984491 |
| Authored | 16 | 2,987–34,804 (252,821) | 3.592314 / 8.923589 / 9.749553 | 65.187528 / 65.454947 / 65.853799 |
| Generated | 64 | 2,987–169,183 (1,230,805) | 3.324579 / 9.204178 / 33.054467 | 64.993684 / 65.578459 / 366.435305 |
| All | 96 | 2,169–169,183 (1,679,105) | 3.041834 / 9.080647 / 33.054467 | 64.993684 / 65.574339 / 366.435305 |

Summed driver intervals are 850.147282 ms native and 7,242.666495 ms Lean across 96 calls each. These are descriptors, not a speedup comparison. Intervals include startup, parsing, checking, analyses and output, excluding builds and consumer checks; no internal-phase attribution is possible. T11's 40-singleton variant completed in 16.925060 ms native and 65.438841 ms Lean, one observation each, with no comparison to the failed attempt. Each driver emitted 464,834 stdout bytes in total and zero stderr bytes over its 96 calls. Per-call commands, exit codes, signals, timeouts, raw byte counts and hashes remain in `results.jsonl.drivers.DRIVER.invocation`; the 192-row TSV retains every input size, expected counter vector and elapsed interval, not just these aggregates.

| Counter | Expected construction range over 96 documents | Effective declared cap | Frozen checker ceiling |
| --- | --- | ---: | ---: |
| Histories | 0–9 | 1,000 | 10,000 |
| Sources | 0–33 | 1,000 | 10,000 |
| Source bytes | 2,169–169,183 | 1,000,000 | 1,048,576 |
| Declarations | 0–152 | 1,000 | 10,000 |
| Search steps | 1–406 | 100,000 | 200,000 |
| Pairs | 0–352 | 1,000 | 4,096 |
| Subsets | 0–64 | 1,000 | 4,096 |
| Embedded events | Not a reported runtime counter | 8 | 8 |

Expected logical counters come from the independently reviewed finite construction, not instrumentation. Successful wrapper results do not expose actual internal counters; every `actual_counter_refusal` is null. No case expects a refusal because all constructions stay below every declared cap, at most 352/1,000 pairs. Observed refusals are 0/96 per driver by this design; this run has zero positive refusal-handling or ceiling-exhaustion coverage. Resource refusal, source rejection, invalid certificate and infrastructure failure are distinct outcomes. Repeated requests are charged cumulatively; hard ceilings are not performance targets.

The recorded machine is Linux `7.0.0-28-generic`, glibc 2.43, x86_64, AMD EPYC 9354 32-Core Processor, with 128 visible logical CPUs and allocation restricted to CPU 0. Host memory at capture was 1,580,515,632 kB total and 1,482,350,556 kB available; these are host descriptors, not process usage. Address-space, CPU-time and data resource limits were unlimited (`-1`); recorded effective cpuset was `0-127`. Peak resident set size (RSS), per-invocation memory, allocation counts, phase timings and independent host-load telemetry were not collected. Toolchains were GHC 9.10.3, Lean 4.32.0 commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35` (Release), and Python 3.14.4. `LANG`/`LC_CTYPE` resolved to `en_US.UTF-8`, other recorded locale categories to `C`; `LC_ALL` was unset.

| Binary | Original bytes | Original SHA256 | Retained archive |
| --- | ---: | --- | --- |
| Native | 12,879,344 | `cfa20be69a3d1737790db828a9437987d5dff3146c55ec95359e5e7aaed9a1f8` | `evidence/binaries/native.gz` |
| Lean | 151,613,512 | `07b603e59bd5245d1373db6e21315a0dc46b2f7f7365370dac58aabad46a0c27` | `evidence/binaries/lean.gz` |
| Consumer | 11,296,920 | `5f75a2310315848077ef8a17cc378f05ef5dcd495bd67e691e7b7fd75158989b` | `evidence/binaries/consumer.gz` |

Builds occurred before measurement: `cabal build exe:lara`, `lake build inquiry-run` from `lean/`, and `cabal exec -- ghc -package lara -outputdir /tmp/p8-consumer-build -o /tmp/p8-consumer scripts/inquiry-codec-client.hs`. Exact selected executable paths, archive bytes/hashes and build commands are in `run.json.binaries` and `run.json.build_commands`; the runner built nothing. One sample per document supports neither confidence intervals nor speedup, asymptotic or universal-latency claims.

## Which P9 decision follows, and what remains unmeasured?

The predeclared “correct and complete results with usable costs and diagnostic contrasts” row applies to this bounded suite: no semantic blocker or timeout remained in the corrected attempt, all four acceptance classes were exercised, and fixed-witness/capture/locality contrasts are present. Its permission is **protocol drafting only**. The next design action is to map measured contrasts to fixed claim-revision or evidence-audit tasks and derive finite per-task inquiry bounds, not to borrow the 96 synthetic documents as a live-study sample size. Researcher review of this exact report is pending; independent AI review cannot substitute for that review or provide assent. P9 remains open in [issue #22](https://github.com/ARA-Labs/Lara/issues/22).

P8 measured no agent success, discovery quality, scientific truth, human faithfulness, causal effect, calibration, real origin-sensitive corroboration, physical capture, arbitrary-prose import, statistical-profile selection or infinite-horizon guarantee. It does not resolve the scope of issues #39 or #46. Hypothetical inputs gain no observed assurance; modeled capture assumptions do not prove real acquisition. Rare or absent distinctions, including different rejected payloads, changed blocking under grounded locality, actual refusals and runtime counters, are not established by zero counts. The all-authored, correlated suite estimates neither the prevalence of these situations in real research nor their workflow value.

## Appendix: Reproduction

The parent already ran the following capture-only replay and retained its output at [the sibling replay directory](../20261013T071248Z-317f210-corrected-replay/). [replay-validation.json](replay-validation.json) records PASS, zero driver invocations and byte-for-byte equality of all 1,009 original run files with the replay, followed by equality of the retained copy. Replay used no drivers or consumers, preserved original timing observations and did not create a second measurement. This is an already-executed provenance command, not authorization to repeat measurement or replay into an existing directory.

```sh
python3 scripts/inquiry-evaluate.py \
  --manifest ara/evidence/inquiry-p8/20261013T071248Z-317f210-corrected/evidence/suite/MANIFEST.json \
  --replay ara/evidence/inquiry-p8/20261013T071248Z-317f210-corrected \
  --out /tmp/lara-p8-corrected-final-replay
cp -a /tmp/lara-p8-corrected-final-replay \
  ara/evidence/inquiry-p8/20261013T071248Z-317f210-corrected-replay
```

Deterministic report SHA256 values recorded in `run.json` are `619e3ddd254d3b239d1e9d0d9cb766b2a63f9411f0e6b26ae774bc8564b39f32` for `results.jsonl`, `80adb5d4d05a92c9ca11b74c36770b4706a2b523098682c1f8335134fe0fa89b` for `summary.json`, and `0430111e6c8f998621ac46073c64ba3a1a84c12ba13b680ef6b5fab6bf28c0f8` for `summary.tsv`. The source `run.json` hash in the replay receipt is `249a3dc4fca82a2a02c7b8761b85793d01f91c548ce2c9ff8cf30a5cf1ad57f7`. The report and subsequent review/replay receipts are additions outside those original sealed measurement files.

## Next Steps

1. Obtain and record Yifeng He's review of this exact result report, including any null findings or scope objections; no such review is recorded here.
2. If that review permits drafting, freeze a separate P9 protocol's tasks, comparison, independent scoring, data policy, model/version, per-task limits, full budget and stop rules, then obtain explicit researcher approval before any live pilot or evaluation.
3. Preserve the corrected and failed evidence, and keep P9 open until its separately approved evaluation and report are complete or the researcher explicitly rescopes it. No additional P8 driver/consumer calls or measurements are part of this handoff.
