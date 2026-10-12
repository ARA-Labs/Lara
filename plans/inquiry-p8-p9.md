# Inquiry P8 protocol and P9 follow-on plan

>For agentic workers: this plan is approved; execute it with `subagent-driven-development` or `executing-plans` and track progress with the checkboxes below.

**Goal:** Evaluate the frozen checked-inquiry semantics on bounded families and explicit source transitions, then use the results to design and approve a separate live-loop evaluation.

**Architecture:** P8 invokes the existing native and Lean inquiry executables on a separately frozen evaluation suite. Independent semantic annotations determine correctness; source-transition reports describe the observations and assumptions exposed by the inquiry layer. P9 uses the P8 report to select a feasible workflow and freezes its own task, comparison and compute protocol before any live run.

**Tech stack:** Haskell production checker and consumer codecs, Lean reference semantics, Python standard-library evaluation tooling, versioned S-expression inputs and append-only ARA evidence.

**Status:** Approved by Yifeng He on 2026-10-12 for implementation and for the P8 local measurement budget defined below. Tasks 1–3 are complete; Tasks 4–5 remain. Approval does not authorize P9: any live-loop pilot or evaluation, agent call or paid compute still needs its own approved protocol.

**Date:** 2026-10-12

## TL;DR

P8 measures finite semantic behavior and source transitions on an additive, authored suite. It distinguishes rejected sources, full public statuses and fixed-witness audits, and checks sensitivity and minimal assumptions against independently enumerated expectations. Existing conformance fixtures are disclosed as development controls; they are not held-out evidence or observations of research success. P9 starts only after the P8 results are reviewed and a separate live-loop protocol has explicit researcher approval.

## Problem

P6 and P7 supplied the native `lara inquiry FILE` door, complete consumer codecs and independent Haskell/Lean conformance. Those gates establish agreement on exercised inputs. They do not measure the distribution of source-transition outcomes, the coverage of locality certificates, the assumptions needed to stabilize a bounded family, or the effect of inquiry feedback on a live research workflow.

[Issue #22](https://github.com/ARA-Labs/Lara/issues/22) leaves P8 and P9 open and requires a separately approved protocol for each. [PR #48](https://github.com/ARA-Labs/Lara/pull/48) is merged at the planning baseline `f1af470`. Before executing P8, pin the actual code and evaluation-input commits instead of measuring a moving branch.

## Constraints

Reuse `inquiry-input 1`, `inquiry-result 1`, the production source observer and the existing analyses. Do not add a second checker, completion semantics, evidence grading system or definition of status. The authoritative contracts are [the inquiry interface and analyses](../docs/theory-process.md#what-do-the-exact-inquiry-analyses-compute), [impact](../docs/theory-process.md#how-is-an-edits-impact-certified) and [the wrapper](../docs/theory-process.md#what-does-the-inquiry-wrapper-add). Exact source rejection payloads and conditional labels inside `evidence-blocked` remain visible. A rejected endpoint has no public status. Equal status does not transport process entitlement.

P8 is local, uses authored inputs and performs no agent calls, network acquisition, protected-data access or scientific experiments. Capture assumptions are modeled reader admissions, not proof of physical capture. Hypothetical choices never acquire observed assurance. Statistical-profile selection, real origin-sensitive corroboration, causal identification, infinite-horizon guarantees in issue #39, and the search-step ceiling rationale in issue #46 are outside this protocol. Report these boundaries; do not treat a successful finite run as resolving them.

Do not change `lara-core@0.3`, inquiry version 1, ceilings, legacy fixture/golden bytes, corpus trees, mutation seeds, manifests or freeze tags. Evaluation inputs live outside `fixtures/process/`: `scripts/check-inquiry-conformance.py` rejects a third fixture owner or nested process fixtures. A needed semantic fix pauses final measurement and needs its own reviewed change, Lean metatheory and `AxCheck.lean` coverage where applicable, plus `make local-gates` for proof, wire or golden changes. A contract change also requires an explicit version/regeneration/axis-(c) budget before resuming.

## Proposed approach

Freeze a bounded P8 suite before final execution, run both built drivers directly, retain their raw output and independently score the results. P8 produces exact semantic checks and descriptive measurements over the declared suite. Correctness is a prerequisite for interpreting measurements. Correct results that expose no useful distinction still belong in the report; do not tune cases or thresholds to make the report favorable.

### What questions does P8 answer?

| Question | Required observation | Claim boundary |
| --- | --- | --- |
| Are family answers rejection-aware? | Total, accepted and rejected rows; rejection buckets; whole-outcome and accepted-only stability | No inference from an accepted-only answer to the whole family |
| Does a submitted witness warrant its claim throughout the family? | Per-row fixed-witness audit and universal audit, with the admitted profile and capture assumptions | Alternative claim support cannot rescue the submitted witness |
| Which choices change an observable? | Reference membership, every differing row, same-history single/joint slot minima and first realizers | Relative to the declared reference and family |
| Which conditional facts suffice? | Every subset-minimal satisfying catalog subset and a deletion countercompletion for each member | Restrictions must be nonempty, rejection-free and satisfy the requested accepted target |
| What does a source edit change? | Acceptance transition, exact rejections, before/after full public statuses, changed/unchanged queries and locality checks | Grounded semantics only; failed locality does not entail changed status |
| What can a snapshot-only report hide? | Differences between the same public-status rows alone and the inquiry's family/audit/transition diagnostics | A diagnostic comparison, not an agent-success comparison |
| Are these bounded workloads operationally feasible? | Completion/refusal counts, input size, per-invocation elapsed time and timeouts | Single-machine descriptive costs, not speedup or asymptotic claims |

### Which inputs are included?

Use at most 96 documents, partitioned into 16 existing controls, 16 new semantic/transition controls and 64 deterministic size variants. These are proposed protocol limits, not measured counts. The frozen manifest must contain exactly that partition for a complete run; if a case cannot be authored within the frozen contract, revise and reapprove the protocol before final execution rather than silently dropping it. Duplicate content hashes are disclosed and excluded from any denominator describing unique semantic inputs.

The 16 existing controls are `source-rejections`, `mixed-stability`, `inconsistent`, `fixed-witness`, `hypothetical-audit`, `forged-observed`, `reference-sensitivity`, `joint-only`, `minimal-conditions`, `new-attacker`, `shared-discharge`, `unrelated-self-attack`, `blocked-conditional`, `impact-rejected`, `verified-certificate` and `tampered-certificate`, each read from `fixtures/process/inquiry/NAME.sexp`. The `.expected` partners remain unchanged. Copy their input bytes into the additive suite and record the original input and golden hashes. Existing golden agreement is a control result, not a newly independent semantic oracle.

| New control IDs | Construction and independent acceptance criterion |
| --- | --- |
| T01-T04 | Extract the `dup-plain` pair from `impact-rejected`. T01 compares its accepted endpoint with itself; T02 reverses the original pair for accepted-to-rejected; T03 retains the rejected-to-accepted pair; T04 compares its rejected endpoint with itself. Record rejection payloads, absent statuses and the exact changed partition; an empty changed partition does not imply equal rejection payloads. |
| T05 | Extract the `blocked-conditional` pair. Both endpoints stay blocked while the conditional label changes from defeated to justified; require that the full public-status query is changed. |
| T06 | Extract the `unrelated-self-attack` pair. The queried status stays defeated and locality succeeds despite an unrelated edit. |
| T07 | Author an accepted pair with an edit inside the query's ancestry that leaves its status unchanged but fails the sufficient locality test. Specify its small graph by hand before encoding it. |
| T08 | Pair T07's before source with an authored declaration permutation of it, keeping stable identity correspondence and a fixed query atom. Require equal statuses and a successful locality check; compare certificates structurally under that correspondence, not by raw indices. |
| T09 | Author a nonempty family whose rows all have the same rejection outcome. Require whole-outcome stability without inventing an accepted status; score accepted-only stability using the frozen empty-accepted-domain rule. |
| T10 | Author two accepted family rows with the same claim status but different fixed-witness audit results. Require stable status and unstable audit; record the exact profile and process bindings. |
| T11 | Extend the `reference-sensitivity` family with a third choice producing the same flip set as an existing choice. Require every differing row, deduplicated minima and the first declaration-order realizer. |
| T12 | Use the `joint-only` family to request both reference sensitivity and joint slot sensitivity. Require a joint minimum with no singleton minimum. |
| T13 | Author a family with no row satisfying its requested accepted target and a catalog containing a slot equality and its contradictory inequality. Require no satisfying subset, including the full catalog that eliminates every row; empty restriction cannot establish the unreachable target. |
| T14 | Use a family already satisfying its accepted target and a catalog containing irrelevant literals. Require the empty minimal set and no spurious nonempty minimum. |
| T15 | Bind one modeled observed witness to an exact admitted capture, then alter the source/process binding. In one bounded family require the affirmative only on the correctly bound row; no label alone earns observed assurance. |
| T16 | On the T01 accepted identity pair, generate an impact certificate with the sanctioned impact API and verify it against the supplied endpoints; replace one recorded read value with a different value of the same `ReadKey.Val` type while retaining its key. A wrong-shaped value would test a different fault, so it is out of scope here. Require `verified` for the original and `invalid-certificate` for the altered value, not an inquiry refusal. |

Prepare T07-T15 from the same source vocabulary as the controls, with independently drawn graphs, row observations, histories and assumption truth tables in the oracle annotations. The author must not read a new driver's output to decide the expected result. T16's certificate producer may compute the certificate, but the expected transition, query partition and tamper fault are independently specified. Do not infer correctness merely because a producer and verifier share an implementation.

The 64 size variants are four levels on four axes, applied to four specified seeds per axis. Generate only the listed axis for each variant; no full factorial expansion. Levels with unchanged bytes remain execution controls and cannot inflate unique-case counts. Each request label must remain unique.

| Axis | Levels | Four seed controls | Semantic expectation |
| --- | --- | --- | --- |
| Inert singleton slots | 0, 1, 4, 40 added slots | T09, T10, T11, T12 | Keep histories, row observables and sensitive original slots unchanged; singleton choices add no alternative completions. Record the frozen empty-changed-set rule if applicable. |
| Inert source declarations | 0, 1, 4, 16 added leaf-root groups (0, 2, 8, 32 AST declarations per endpoint) | T01, T05, T06, T07 | Add disconnected accepted leaf-root arguments with fresh identities, fresh atoms and their required signature entries to both endpoints; a repeated leaf is a source rejection (as in `dup-plain`), not an inert addition. Query statuses and changed partitions stay fixed; read inventories can grow. |
| Additional assumption literals | 0, 1, 2, 4 distinct added literals | T09, T10, T13, T14 | Each seed has one explicit `minimal-assumptions` request. Add distinct unused-slot inequalities that are true in every row; record their exact evaluations. They must introduce no new minimal satisfying sets. |
| Repeated query work | 1, 2, 4, 8 copies of the seed's wrapper request list | T01, T05, T11, T12 | Fresh labels preserve each answer's content until the shared budget refuses the whole document. Do not deduplicate repeated work in the runner or multiply cases in semantic success denominators. |

For the catalog-axis seeds, T09 targets `published justified` at its fixed claim atom and has no satisfying restriction because every row is rejected. T10 targets its positive fixed-witness audit and includes slot literals selecting the passing row. T13 uses the unreachable accepted target defined in its annotation; T14 uses the accepted status common to every row. The added literals have fresh, undeclared slot IDs, so `Literal.Holds` interprets their inequalities as true (`selectionFor` returns no choice). Disclose that convention and include the expected predicate values in the oracle; these literals are not evidence observations.

All generated identities must be fresh in their namespace, and all certificates/source pins must match the generated endpoints. Retain any expected limit refusals as refusals rather than shrinking inputs after inspection. A variant unable to express its intended manipulation is an authoring failure, not evidence against the checker. Fix it before the input freeze and rerun its independent annotation review.

### How are expectations established?

For each new input, an independent reviewer receives its semantic specification and source bytes before final driver execution. The reviewer enumerates the bounded histories, guard-surviving selections, endpoint graphs and row outcomes without using either driver's answers or importing `Lara.Process.Analysis`. The reviewer checks the accepted/rejected partition, exact public statuses and fixed-witness audit, then exhaustively compares all reference flips and all catalog subsets. A returned conditional set must leave at least one row, contain no rejected rows and satisfy the accepted target; deleting each member must expose a countercompletion. Joint minima must be complete, nonempty and inclusion-minimal under the frozen rule.

Store the expectations as structured semantic data and cite the relevant definitions/theorems from `docs/theory-process.md`. Input/golden byte checks still run, but the P8 score compares decoded meanings against this independent data. A reviewer disagreement blocks the freeze until the input specification or annotation is corrected. Driver agreement never settles an oracle disagreement. No human faithfulness claim is attached to authored cases; using real research records later requires separate binding review and provenance.

For locality, compute the per-query support correspondence and old-graph ancestry with the small annotated graphs, then compare the relevant attackers in the new graph. Include fresh attackers and propagated premise/discharge edges. Score sufficient preservation separately from actual equality, and retain T07 so a failed locality test cannot be scored as a detected change. Full public status also needs equal blocking; a grounded-label certificate alone cannot certify unchanged blocked status.

### What is frozen and retained?

The additive suite belongs in `evaluation/inquiry-p8/`, not in any existing corpus or process-fixture tree. Every document has a `case_id`, stratum, development/generated classification, source ancestry, content hash, original query order, optional reference, catalog, effective declared limits, expected refusal or result, and independently annotated semantic expectation. `MANIFEST.json` references `inputs/CASE.sexp` and `oracles/CASE.json`; `protocol.json` records the approved protocol text hash, manifest hash, generator recipe/version, deterministic declaration order and budget. Never populate an expected field from a final driver output.

Pin the evaluation-input commit and code commit before measurement, and record both binary hashes, GHC and Lean versions, build commands, OS/architecture, locale, CPU, available memory and the effective inquiry ceilings. Preserve the original input bytes and each driver's stdout, stderr, exit/signal/timeout classification and invocation command. Raw captures belong under `ara/evidence/inquiry-p8/RUN_ID/`; the run ID is the UTC start timestamp plus the code-commit prefix and must not overwrite an existing run. Driver agreement, oracle agreement and consumer-decoder success are separate fields.

The future `scripts/inquiry-evaluate.py` entry point accepts `--manifest`, `--native`, `--lean`, `--consumer` and `--out`, resolves paths, verifies frozen hashes before spawning, and does not build or update inputs. It reuses `scripts/evidence_measured.py` for concrete parsing/canonical encoding and the driver/consumer invocation discipline of `scripts/check-inquiry-conformance.py`. Compile `scripts/inquiry-codec-client.hs` once during preflight and pass that binary as `--consumer`; consume every original input and captured output. Its verification leg is outside the timed driver interval. Keep the evaluation input/oracle logic separate from the existing generated conformance cases so implementation-generated expected output cannot leak into the independent score.

In replay mode, `--manifest`, `--replay` and a fresh `--out` directory replace all executable arguments. `--replay` names a complete saved run; verify its input, binary and capture hashes and recompute deterministic score fields without spawning drivers or consumers. Retain its original timing and invocation records. Incomplete evidence stays incomplete under replay.

### Which measurements are reported?

| Report field | Definition and denominator |
| --- | --- |
| Correctness | Exact oracle agreement per unique semantic input, separately for native and Lean; controls and new cases reported separately |
| Family outcomes | Total/accepted/rejected rows and exact rejection buckets; whole-outcome stability and accepted-only stability with explicit accepted count |
| Audit outcomes | True/false per fixed witness and row, plus universal audit; retain profile, coverage, kind completeness and capture bindings |
| Sensitivity | Reference membership, total flips, same-history flips, all nonempty minimal slot sets, cardinalities and first realizing rows |
| Conditional assumptions | Catalog size before/after deduplication, subsets examined, satisfying minima, surviving-row counts and deletion countercompletions |
| Endpoint transitions | Counts in all four acceptance classes and rejection reasons. Only accepted endpoints contribute status rows; do not treat an absent status as gap, false or unknown |
| Public-status changes | Full before/after values, per-query changed/unchanged partition and separate blocked conditional changes |
| Locality coverage | Certified unchanged / actually unchanged queries among accepted-to-accepted pairs, with equal-blocking checks; report the numerator and denominator, including a zero denominator |
| Locality soundness checks | Every certified unchanged query must actually have equal full public status; fail the semantic run on any counterexample |
| Additional diagnostics | Matched accepted endpoints or family rows with equal full public status but different witness audits or assumption/capture bindings; compare exact rejection payloads separately among rejected endpoints, which have no public status |
| Operational observations | Original byte size, manifest's independently calculated logical counters, result/limit refusal, elapsed milliseconds per direct process call and timeout/signal/spawn failure |

The wrapper does not expose every logical counter on successful runs. Calculate manifest counters from the approved finite construction and label them `expected`, not runtime telemetry; record `actual` only where a refusal prints it. Do not add instrumentation to the checker for this protocol. Elapsed time includes process startup, parsing, checking, analyses and output emission, but excludes builds and consumer checks. One invocation per driver and document gives descriptive elapsed times only, with no confidence interval, speedup claim or attribution to internal phases. Report all timeouts and expected refusals in separate columns rather than assigning a successful value.

The snapshot-only comparison is computed from the same captured public-status rows, so input, query and checker differences cannot confound it. It deliberately lacks family, witness-audit and dependency/transition diagnostics. It is a descriptive visibility comparison; P8 cannot show that an agent uses those diagnostics well or discovers better science.

### What is the execution budget?

Build and run existing local correctness gates before starting the measurement interval. The proposed measurement budget is at most 96 documents, one native and one Lean invocation each, a 10-second timeout per driver invocation, and a 45-minute aggregate evaluation deadline including consumer checks and scoring. That permits at most 192 driver invocations; refusals and failed invocations count against the budget. Run sequentially on one local CPU allocation with no concurrent benchmark or agent workload. Each driver is a new process; alternate which driver runs first by manifest position. No repeats, remote compute or paid API calls are authorized by P8.

Honor all seven frozen inquiry ceilings and the embedded event ceiling, including the per-document cumulative charging of repeated requests. Hard ceilings are not performance targets. A timeout, signal, spawn/consumer failure, resource kill or aggregate deadline exhaustion makes the run incomplete. Retain partial evidence and the missing-case list, stop, and request a protocol/budget revision before rerunning. Do not reclassify infrastructure failures as semantic rejection or keep retrying until a favorable run appears.

### When is P8 complete?

A complete P8 report needs the approved protocol and independently reviewed input freeze, every planned case and raw capture, exact oracle agreement for both drivers, successful real consumer decoding, all four transition classes and the required audit/blocking/locality contrasts, and separate results for controls and new cases. Expected limit refusals are valid observations when their counter, actual/cap and atomic output match the independent expectation. Unexpected semantic discrepancies block completion. A full report may conclude that feasible scope or diagnostic coverage is too narrow for the intended P9 workflow; a favorable conclusion is not an acceptance criterion.

## Alternatives considered

| Approach | Benefit | Reason for the chosen scope |
| --- | --- | --- |
| Additive authored suite, then separately approved live protocol | Exact bounded expectations and preserved legacy freezes | Chosen; supplies interpretable P8 evidence without live acquisition |
| Reuse only existing conformance goldens | Minimal tooling | Gives little new evidence beyond P7 and no independently reviewed transition measurements |
| Start live agent experiments immediately | Direct workflow observations | Leaves task selection, comparison, data handling and compute unapproved; conflates semantic defects with workflow effects |

## Tradeoffs

The authored suite gives a precise finite oracle but does not estimate the prevalence of these cases in real research artifacts. Existing controls disclose their development role. Generated size variants exercise bounded workloads and accounting but are correlated with their seeds; report them by axis, not as independent research tasks. Conservative whole-input dependency reads can make certificates large, and that cost is an observation rather than grounds to claim finer dependency tracking than the proved contract supplies.

P8's operational observations can rule out an impractical P9 scope on the measured machine. They cannot set a universal latency guarantee. Additional calibrated repetition or broader sampling requires an approved protocol amendment before another final measurement run.

## Migration

This plan adds evaluation inputs, an evaluation runner and reports without a runtime cutover. It leaves the public APIs, wire contracts and all current consumers unchanged. New evaluation schema fields belong to the manifest/report boundary; fixed vocabularies are closed in the checker and original S-expression atoms are decoded at the existing boundary. Any future exported-symbol change requires reference inspection and migration of every caller, not an evaluation-only compatibility shim.

After P8 lands, fold its settled protocol and claim limits into `docs/evaluation.md` under a checked-inquiry subject section and link reproduction commands from `docs/implementation.md`. Keep run evidence and interpretations in `ara/`; do not create a milestone or dated review record in `docs/`. Delete an executed P8-only plan. If this combined plan remains while P9 is unexecuted, replace its status banner with the remaining tasks and move durable P8 content to the subject docs.

## How does P9 follow the results?

P8 does not authorize P9. Review the complete P8 report and use the table below to choose the next design action. There is no threshold on discovery improvement because P8 does not measure it. Separate engineering feasibility from workflow effectiveness.

| P8 finding | Required next action | P9 permission |
| --- | --- | --- |
| Oracle disagreement, certificate soundness counterexample or evidence-grade promotion | Diagnose and fix under the frozen contract; open a GitHub issue for actionable work not completed in that change, with proof/regeneration costs; refreeze inputs only for a justified approved correction | No live run |
| Timeout/incomplete run, unexpected refusal or a planned workflow outside feasible bounds | Retain failure evidence; design a smaller finite workflow or separately budget the required implementation/limit change and rerun the relevant P8 protocol | No live run |
| Correct results, but little distinction from snapshot-only reports | Choose a narrow diagnostic/task that actually exercises a measured distinction or explicitly design a null-result feasibility pilot; do not claim general benefit | Protocol drafting only |
| Correct and complete results with usable costs and diagnostic contrasts | Map measured contrasts to a fixed set of research tasks and derive per-task inquiry bounds; prepare the paired live protocol below | Protocol drafting only |
| P9 task needs physical capture, arbitrary-prose importing, real corroboration adapters or an unproved statistical guarantee | Design and budget that dependency separately, with its trust boundary, proofs and evaluation | No dependent live run |

### What must the P9 protocol freeze?

Write a separate `plans/inquiry-p9-live-loop.md` after P8 review. It must cite the immutable P8 report and explicitly state which finding justifies each task and budget. The checklist below is the required protocol content, not permission to leave values unspecified when approving the live run.

- Research question and scope: start with whether checked inquiry feedback improves a bounded claim-revision or evidence-audit workflow. State separately any scientific-discovery question; a workflow result cannot establish discovery quality or empirical truth.
- Task set: exact public or researcher-approved task snapshots, source hashes, expected bindings, allowed observations/actions, task inclusion/exclusion rules, fixed query atoms, declared finite families and profiles. Separate calibration/pilot tasks from evaluation tasks before outcome inspection.
- Comparison: propose two matched arms, the same agent/workflow with ordinary checker/public-status feedback versus the same agent/workflow with added inquiry diagnostics. Hold model/version, task inputs, retrieval access, prompts except the feedback treatment, tool access and total per-task budget fixed. Charge inquiry computation and extra feedback tokens to the treatment arm. Use isolated task copies and fresh conversations; do not share outputs or improvements across arms. Declare randomization/seed policy and order before running.
- Outcome and scoring: name one primary task-level outcome, such as independently scored correct final claim disposition with justified assumptions and no unsupported assurance. Freeze the scoring rubric, treatment-blind review where feasible and resolution of reviewer disagreements. Keep task completion, unsupported claim rate, audit correctness, latency, tokens and cost separate. Do not use checker acceptance alone as an empirical-truth label.
- Design size and analysis: freeze the number of tasks and repetitions, paired analysis, uncertainty reporting, exclusion policy and handling of non-independent repetitions. Pilot estimates may set feasibility budgets but do not enter the final efficacy denominator. If the approved size supports only feasibility, state that explicitly and make no significance or causal/discovery claim.
- Budget and execution: exact model/provider and workflow version, maximum agent steps, inquiry calls, input/family/catalog sizes, token limits, per-task and aggregate timeouts, total currency/compute ceiling, allowed retries and automatic stop rules. Approve all values before enabling tools or credentials. No replenishing a budget in response to an unfavorable result.
- Data policy: classify every input, approve destinations, retention, access and deletion, exclude protected data by default, and forbid sending secrets or private records to an unapproved provider. Public tasks need pinned source provenance too.
- Process record: preserve precommitted protocol and amendments, all selection/calibration/evaluation actions in order, complete trial families including failed or resultless runs, run/model/version identity, edits, exact tool calls/results and missingness. Log inaccessible capture as missing, not observed. Bind each audit's source/process/material explicitly; physical logs do not automatically establish model fidelity.
- Failure policy: score refusals, timeouts and abandoned tasks using the frozen rubric; retain their denominators. A semantic defect stops the affected evaluation and triggers a versioned amendment and a fresh run; do not repair treatment outputs manually. A data-policy breach stops immediately and follows the approved handling policy.
- Approval and claims: name the researcher approving the exact protocol hash, data policy and full budget. Require independent final scoring and a report of all runs, including null/negative results. State exactly which workflow claim the design can support and which soundness, calibration, truth and discovery claims it cannot.

A conservative starting proposal is a public-data paired feasibility pilot on claim revision, with tasks chosen from the measured fresh-attacker, blocked-conditional and fixed-witness contrasts. P8 results may reject that choice. Do not set a model, task count, statistical profile or live budget by borrowing P8's synthetic-case counts. Those are materially different decisions and must be made in the P9 design review.

P9 completes only when its separately approved protocol has been run, the full ledger and budget use are retained, independent scoring is complete and the report states the supported scope. Drafting the protocol or running only a pilot does not complete the issue's P9 evaluation stage. If the researcher declines a live run, record that decision in issue #22; leave P9 open unless they explicitly rescope it.

## What work executes the approved P8 protocol?

### Task 1: Approve the protocol and establish the additive input boundary

Files: create `evaluation/inquiry-p8/protocol.json` and `evaluation/inquiry-p8/MANIFEST.json`. The researcher approved this plan on 2026-10-12. These paths and the commands below are proposed deliverables, not existing executables.

- [x] Review the questions, case matrix, 96-document cap, local execution budget and P9 separation. Record the approving researcher and the Git blob hash of this plan at its approval commit in `protocol.json`; later status-banner edits do not change the approved protocol.
- [x] Pin the code commit and verify the native/Lean/toolchain dependencies are locally available. Record any required setup separately from measurement time.
- [x] Record hashes of the legacy input trees and selected fixture/golden controls. Do not run a regeneration or `UPDATE=1` command.

### Task 2: Author, independently review and freeze all cases

Files: create `evaluation/inquiry-p8/inputs/*.sexp`, `evaluation/inquiry-p8/oracles/*.json` and `scripts/inquiry_evaluation_cases.py`; populate the manifest.

- [x] Copy the 16 development controls unchanged and generate the 16 new controls and 64 variants using the recipes above. Keep source manipulations structural via `parse`/`canonical`, not string replacement.
- [x] Give the independent reviewer the semantic specifications and byte-level inputs. Store their exact row, graph, audit, sensitivity, conditional and transition expectations plus review provenance.
- [x] Confirm all strata and four acceptance classes are present, distinguish expected limit refusals from source rejections, and identify duplicate hashes.
- [x] Freeze the inputs/oracles/manifest in an input commit before the final measurement run. The freeze commits the additive suite only; it creates no legacy freeze tag and changes no existing corpus.

### Task 3: Implement the runner and exercise its failure boundaries

Files: create `scripts/inquiry-evaluate.py`; reuse `scripts/evidence_measured.py` and `scripts/inquiry-codec-client.hs` without changing their existing contract.

- [x] Implement the CLI specified above, hash checks, direct invocation, aggregate deadline and append-only raw captures. Produce `run.json`, `raw/CASE.DRIVER.{stdout,stderr}`, `results.jsonl`, `summary.json` and `summary.tsv` under the supplied output directory.
- [x] Implement semantic scoring from the reviewed oracle data, separate control/unique/generated denominators and a snapshot-only projection from the same captures. The runner exits nonzero for an incomplete run or oracle/consumer disagreement even when both drivers agree with each other.
- [x] Use throwaway runner probes to prove missing/hash-mismatched inputs fail before driver execution, a real timeout/signal is retained as incomplete, an intentionally wrong oracle fails, and an attempted reused output directory does not overwrite evidence. Remove the probes after verification; add permanent tests only for uncertain consumer-visible boundaries.

### Task 4: Run the frozen P8 protocol and retain the observations

Files: create `ara/evidence/inquiry-p8/RUN_ID/` with the run outputs; no fixture/golden edits.

- [ ] Run `make local-gates` and `cabal test all` before measurement, preserving their actual output. These gates are correctness preconditions, not P8 results.
- [ ] Build the native and Lean inquiry executables and the consumer client, and resolve their binary paths exactly as `scripts/check-inquiry-conformance.py` does; record hashes and environment in the run metadata. No builds run inside the measurement interval.
- [ ] Execute the approved runner once on the frozen manifest. Retain every case, including expected refusals and infrastructure failures, and enforce both budgets.
- [ ] Recompute the report from saved captures without rerunning drivers. Require identical deterministic fields and hashes; elapsed times remain original observations.

Proposed final-run command, after Tasks 1-3 supply the files and the two paths are recorded in the shell environment:

```sh
python3 scripts/inquiry-evaluate.py \
  --manifest evaluation/inquiry-p8/MANIFEST.json \
  --native "$NATIVE_INQUIRY_BINARY" \
  --lean "$LEAN_INQUIRY_BINARY" \
  --consumer "$INQUIRY_CONSUMER_BINARY" \
  --out "$P8_EVIDENCE_DIRECTORY"
```

Expected outcome: zero exit only for a complete, oracle-correct, consumer-accepted run with the approved case partition. Exact counts and measurements come from `summary.json`, not from this plan. A nonzero exit preserves the incomplete evidence and blocks interpretation as a completed P8 run.

Proposed capture-only reproduction command:

```sh
python3 scripts/inquiry-evaluate.py \
  --manifest evaluation/inquiry-p8/MANIFEST.json \
  --replay "$P8_EVIDENCE_DIRECTORY" \
  --out "$P8_REPLAY_DIRECTORY"
```

### Task 5: Interpret P8 and choose the P9 design path

Files: create `ara/evidence/inquiry-p8/RUN_ID/report.md`; update `docs/evaluation.md`, `docs/implementation.md`, issue #22 and the ARA research record. Create `plans/inquiry-p9-live-loop.md` only if the P8 review permits protocol drafting.

- [ ] Report every defined field with its denominator, separate authored/development inputs, disclose correlated variants and explain any zero-coverage, refusal or null result.
- [ ] Apply the P9 decision table without changing the interpretation thresholds after seeing results. Record the researcher review and the chosen design path.
- [ ] Open GitHub issues for any actionable deferred defect or dependency, including proof, compute, corpus-regeneration and freeze costs. Issue #22 remains the tracker for the already-planned P9 protocol/run; do not create an in-repo backlog.
- [ ] Move settled P8 contracts to subject docs and keep raw runs/interpretation in ARA. Keep this plan with an updated remaining-work banner while P9 is pending, or replace it with the living P9 plan once the P8 work lands.

## Next Steps

1. Commit this approved plan so its blob hash can be pinned in `protocol.json`.
2. Execute P8 Tasks 1-5 under the approved freeze and local budget.
3. Review the P8 findings and approve a fully specified, separately budgeted P9 protocol before its pilot or evaluation run.
