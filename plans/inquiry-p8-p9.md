# Inquiry P8 review and P9 follow-on plan

**Remaining work:** Researcher review of the completed corrected P8 report, then a separately approved P9 protocol and evaluation. P8 implementation, measurement, capture-only replay and reporting are complete. This plan grants no P9 execution or additional P8 measurement budget.

**Tracker:** [Issue #22](https://github.com/ARA-Labs/Lara/issues/22). The corrected P8 [report](../ara/evidence/inquiry-p8/20261013T071248Z-317f210-corrected/report.md) retains the original failed attempt, full denominators and claim limits. The settled protocol and replay contract live in [evaluation](../docs/evaluation.md#how-is-bounded-checked-inquiry-evaluated) and [implementation](../docs/implementation.md#how-are-bounded-inquiry-results-reproduced).

## Review and approval gates

- [ ] Record the researcher's disposition of the corrected P8 report. Independent engineering/evidence review is not researcher assent to its interpretation.
- [ ] Select a bounded workflow using the decision table below; map measured diagnostic contrasts to task-level outcomes without claiming agent efficacy from P8.
- [ ] Draft `plans/inquiry-p9-live-loop.md` with every protocol field below and the dependency/proof/data/compute costs. Do not select an unapproved model, task count or budget by extrapolating from synthetic cases.
- [ ] Obtain researcher approval of the exact P9 protocol hash, data policy and full budget before any pilot or evaluation call.
- [ ] Execute only that approved protocol, retain all outcomes, complete independent scoring and report the supported scope. Keep issue #22 open until the approved P9 work lands or the researcher explicitly rescopes it.

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

