# P9 checked-inquiry live-loop report
**Date:** 2026-10-13

## TL;DR

The approved paired feasibility run completed all 16 agent runs and all 16 blind scorings within budget: $1.76 of the $150 ceiling, with no timeouts, refusals or missing answers. With inquiry diagnostics, Claude Opus 5.5 reached the correct claim disposition without unsupported assurance on 8/8 tasks; with the public status view alone, on 6/8. The two discordant tasks both favour the diagnostics (exact McNemar p = 0.5, descriptive only). One status-arm miss was an unsupported assurance (P9-07: three rejected alternatives dropped, status reported as settled). The other was a conservative under-claim (P9-06: no locality certificate, so the agent refused to certify an edit that is in fact certified harmless). On the other diagnostic-dependent tasks, the status-only agent derived the decisive fact from the raw document itself. Eight synthetic tasks support feasibility only. They establish no efficacy, significance, generality or discovery claim.

## Which protocol and approvals does this cover?

| Identity | Binding |
| --- | --- |
| P8 report review | `evaluation/inquiry-p8-corrected/researcher-result-review.json`, report SHA256 `23366d69…03eb`, researcher Yifeng He |
| Original P9 protocol | SHA256 `ad2c0b23…aeac9`, commit `0590fe5`, approval `evaluation/inquiry-p9/researcher-approval-original.json` |
| Executed protocol (amendment 1) | `evaluation/inquiry-p9/protocol.json`, SHA256 `b1c9e135dffafbb9b47a54b7671820c76e127d86df4331a884342c1602e24b68`, commit `181812f`, approval `evaluation/inquiry-p9/researcher-approval.json` |
| Run | [run.json](run/run.json): started 2026-10-13T22:23:07Z, finished 22:26:33Z, code commit `49a8d80`, `lara` binary SHA256 `cfa20be6…a1f8` |
| Agent and scorer | `claude-opus-5-5` through Claude Code 2.1.296 `claude -p`, fresh non-persistent session per call |

Amendment 1 was made before any task outcome existed. The first harness-validation call ([smoke](smoke/)) showed that the CLI auto-allows read-only commands inside the workspace. The original wrapper selected its view from an environment variable, so a status-arm agent might have reached the diagnostics. The amendment fixes each arm's view inside its own wrapper. Tasks, answer key, scoring and ceiling are unchanged.

## Deviation: the isolation check was inconclusive

The approved [isolation check](smoke-isolation/) ran in a status-arm workspace. Its agent ran `./lara-view check`, which returned the status view only, and `cat lara-view`. It then declined the remaining probes itself, judging them to be circumvention: the environment-variable override, direct execution of the views script, and `ls -a`. The CLI permission layer therefore never saw those routes in the check. The protocol allows one isolation call, so it was not repeated. The task runs proceeded under two compensating facts:

- The environment-variable route is closed by construction. The wrapper unsets the variable and hardcodes its view; a local test of the status wrapper with `LARA_P9_VIEW=inquiry` printed the status view only.
- A post-hoc [isolation audit](run/isolation-audit.json) (`scripts/inquiry_p9_audit.py`) inspected every tool call and result in all 16 task transcripts. Every executed call was an allowed command: `./lara-view show && ./lara-view check`, or `./lara-view check` alone. No status-arm tool result carries inquiry output. One treatment-arm agent (P9-08) attempted a piped `grep` command, and the CLI refused it. That refusal is direct evidence that unlisted commands are denied. Isolation held.

## What was measured?

Eight tasks, each one P8 case, with expected answers derived from the reviewed P8 oracles and checked by `scripts/inquiry-p9.py check-key`. Primary outcome: every answer field matches the key, and the arm-blind scorer reports no unsupported assurance. The scorer saw the task, the reference answer and the answer with tool names redacted, but not the arm.

| Task | P8 case / contrast | Status view only | With inquiry diagnostics |
| --- | --- | --- | --- |
| P9-01 | T10, fixed-witness audit | correct (2/2 fields) | correct (2/2) |
| P9-02 | T15, capture binding | correct (2/2) | correct (2/2) |
| P9-03 | T05, blocked conditional (null-contrast control) | correct (3/3) | correct (3/3) |
| P9-04 | new-attacker, status-changing edit (null-contrast control) | correct (3/3) | correct (3/3) |
| P9-05 | T07, unchanged without certificate | correct (3/3) | correct (3/3) |
| P9-06 | T06, certified unchanged | **incorrect** (1/3): refused to certify; no unsupported assurance | correct (3/3) |
| P9-07 | source-rejections, rejected alternatives | **incorrect** (2/4): status reported stable and settled; **unsupported assurance** | correct (4/4) |
| P9-08 | minimal-conditions, minimal assumptions | correct (1/1) | correct (1/1) |

| Arm | Primary correct | All fields correct | Unsupported assurance | Timeouts / not run | Agent cost | Agent wall time | Turns |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Status view only | 6/8 | 6/8 | 1/8 | 0/8 | $0.648 | 111.8 s | 16 |
| With inquiry diagnostics | 8/8 | 8/8 | 0/8 | 0/8 | $0.754 | 94.4 s | 18 |

Paired outcomes per task: both correct 6, diagnostics only 2 (P9-06, P9-07), status view only 0, neither 0. Exact two-sided McNemar p = 0.5 over the two discordant pairs; it is reported descriptively and supports no significance claim. No answer was flagged for researcher resolution: every all-fields-correct answer had a scorer verdict of no unsupported assurance and a justification consistent with its fields.

Total spend was $1.758: harness check $0.030, isolation check $0.056, 16 agent runs $1.402 and 16 scorer calls $0.270, as recorded in [spend.jsonl](spend.jsonl). No call approached its cap. The treatment arm's extra cost is charged to it: $0.106 more in total, mostly P9-08, where one refused command cost two extra turns.

## How should the two discordant tasks be read?

**P9-07** is the contrast P8 predicted. The status view lists one accepted completion, `(published gap)`. The agent read all four slot choices from the document and correctly described why the other three are rejected. It then treated the rejected completions as not counting, and reported the status stable and settled. The inquiry arm saw `whole-outcome-stable false` with three rejection reasons, and answered correctly. A status-only report invites exactly this error: an accepted-only summary presented as settled.

**P9-06 and P9-05 together** show what the locality certificate adds. Without a certificate, the status-only agent declined to certify either edit. That is correct for T07, where a new attacker enters the claim's ancestry, and wrong for T06, where the added self-attacking argument is unrelated. Its justification for T06 noted that the new argument "does not seem to touch" the claim, but it would not certify on inspection alone. The inquiry arm certified T06 and refused T07. Caution without a certificate is safe but cannot tell the two cases apart; the certificate can.

## What did the status-only agent manage without diagnostics?

For the fixed-witness audit (P9-01), capture binding (P9-02) and minimal assumptions (P9-08), the status-only agent derived the decisive fact from the raw S-expression document. It traced which slot choice introduces the witness argument, and which capture assumption requires `correct-capture`. It also enumerated the attack structure to find both minimal sets. For these small documents, the extra diagnostics were not needed for a strong model to answer correctly. They supplied the answer directly instead of by derivation. This run does not show whether that derivation scales to larger documents or weaker models.

## What does P9 support, and what not?

Supported: under this harness and model, both feedback conditions complete all eight bounded claim-review tasks quickly and cheaply. The isolation between arms held. On this task set, the observed outcome difference is two tasks, both favouring the diagnostics, one of which is an avoided unsupported assurance.

Not supported:
- agent efficacy in general, statistical significance, or any causal estimate: 8 tasks, 1 repetition, one model;
- generality beyond these authored synthetic cases, which were chosen because they exercise P8's measured contrasts;
- scientific discovery, empirical truth, calibration or soundness: the key encodes the checker's own semantics;
- real capture fidelity.

The scorer is a same-family model shown the reference answer. It is arm-blind, but it is not independent of the agent's model family.

## Reproduction

`python3 scripts/inquiry-p9.py check-key` re-verifies the answer key against the P8 oracles without any agent call. `python3 scripts/inquiry_p9_audit.py ara/evidence/inquiry-p9/run` re-derives the isolation audit, and `python3 scripts/inquiry-p9.py summarize --out ara/evidence/inquiry-p9/run --ledger ara/evidence/inquiry-p9/spend.jsonl` re-derives the summary from retained records and scores. Neither makes a call. Re-running `run` or `score` makes new live calls under a new budget and is not a replay.
