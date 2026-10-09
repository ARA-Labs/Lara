# Certified-evidence independent review record (`evidence-measured-inputs@1`)

Review status: accepted and applied on 2026-10-07. `openai-codex/gpt-6-astra` independently reviewed all ten mappings and returned ten faithful verdicts; the maintainer looked at the review and agreed. The package bindings retain `author = ai_inventory` and now carry `audit-status = reviewed` with the reviewer and accepted review link in their rationales. The [publication record](#published-reviewed-bindings) identifies the re-pinned sources and [second freeze](../../../measurements/frozen/evidence-measured-inputs-v2.md). The [first measured report](../../../measurements/frozen/evidence-measured-inputs-v1.md) remains unchanged and is not semantic-review evidence.


## What a reviewer decides

One question per leaf: **does the original producer's own output mean what the
Lara claim says it means?**

Lara checks the mechanical half: the pinned bytes, the extraction request and
equality with the declared proposition. It does not prove the producer's
scientific interpretation. The reviewer judges the reading of those bytes.

A reviewer therefore answers three things:

1. **Selector.** Is the named original cell the cell the claim intends? (Row
   key, column names, JSON pointer.)
2. **Unit and quantity.** Does the original producer's source say the stored
   number is the quantity the claim names? (Seconds of forward time, seconds of
   training time, mean denoising loss.)
3. **Reading.** Does the claim's natural-language sentence assert no more than
   that record supports? (In particular: a saved record is not a comparison, an
   accuracy, or a replication.)

## What a verdict does **not** establish

A `faithful` verdict is not a result about the producer's experiment. It says
the packaged original output is read as the claim reads it. It does **not**
validate CompoNet's or Simformer's method, their measurements, their
comparisons, their paper, or the upstream ARA reconstruction. Nobody may
publish "human-verified" scientific claims on the strength of this table.

## Recording protocol

An independent agent or human reviewer checks the AI-authored inventory bindings. On 2026-10-07, the maintainer removed issue #20's human-only requirement and accepted Astra's review. Identify the agent model explicitly; an accepted agent verdict is not a human-authored verdict.

1. Read the named original object and the producer source for each leaf.
2. Record `faithful`, `unfaithful`, or `unclear`, with a rationale naming the
   cell, quantity, unit and producer source relied on.
3. Record the reviewer's name or agent model and date with each verdict.
4. Leave `unfaithful` or `unclear` bindings unreviewed until the mapping is
   corrected and independently reviewed again. Preserve the original verdict.
5. A `faithful` verdict permits changing the leaf's audit status to reviewed.
   Keep `author = ai_inventory`: review does not change who authored the
   mapping. Record the reviewer separately and cite this worklist.

Budget: ten leaf reviews, including the original cells and producer code.
Changing an audit status changes the pinned source and package manifest, so
re-pin the affected source entry and re-run the additive evidence report before
cutting its next freeze. Do not rewrite the first measured snapshot.

## The ten leaves

Package paths are relative to `examples/certified-evidence/`. "Raw original
value(s)" are quoted from the committed original bytes, not retyped from a
paper.

| # | Package | Leaf | Claim | Original object and exact selector | Raw original value(s) | Declared formal proposition | Declared natural-language reading |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | A (CompoNet) | `forward-1631` | `c-forward-1631` | `evidence/benchmarking.csv`, row where column `""` (the Pandas index) is `1631` | `""=1631`, `method=ProgressiveNet`, `num prevs=10`, `time=0.0030154159758239985` | `forward_time_s(1631,"ProgressiveNet",10,0.0030154159758239985)` | "The original saved forward-runtime record 1631 has the displayed method, prior-module count and runtime in seconds." |
| 2 | A (CompoNet) | `forward-1632` | `c-forward-1632` | `evidence/benchmarking.csv`, row where column `""` is `1632` | `""=1632`, `method=ProgressiveNet`, `num prevs=10`, `time=0.0030042969156056643` | `forward_time_s(1632,"ProgressiveNet",10,0.0030042969156056643)` | "The original saved forward-runtime record 1632 has the displayed method, prior-module count and runtime in seconds." |
| 3 | B (Simformer) | `train-0` | `c-train-0` | `evidence/summary.csv`, row where `model_id` is `0` | `method=score_transformer`, `task=two_moons_all_cond`, `time_train=977.5672931671144` | `training_time_s("score_transformer","two_moons_all_cond",977.5672931671144)` | "The original saved training-runtime record 0 reports seconds." |
| 4 | B (Simformer) | `train-1` | `c-train-1` | `evidence/summary.csv`, row where `model_id` is `1` | `method=score_transformer_joint`, `task=two_moons_all_cond`, `time_train=1047.1436779499054` | `training_time_s("score_transformer_joint","two_moons_all_cond",1047.1436779499054)` | "The original saved training-runtime record 1 reports seconds." |
| 5 | B (Simformer) | `train-2` | `c-train-2` | `evidence/summary.csv`, row where `model_id` is `2` | `method=score_transformer_undirected`, `task=slcp_all_cond`, `time_train=2717.260816335678` | `training_time_s("score_transformer_undirected","slcp_all_cond",2717.260816335678)` | "The original saved training-runtime record 2 reports seconds." |
| 6 | B (Simformer) | `loss-0` | `c-loss-0` | `evidence/1_minimal_code_example.ipynb`, `/cells/19/outputs/0/text/0` | `46.13004` (one LF) | `training_loss(46.13004)` | "The original saved notebook output 0 reports mean denoising loss for a block of 5000 updates." |
| 7 | B (Simformer) | `loss-1` | `c-loss-1` | `evidence/1_minimal_code_example.ipynb`, `/cells/19/outputs/0/text/1` | `45.541588` (one LF) | `training_loss(45.541588)` | "The original saved notebook output 1 reports mean denoising loss for a block of 5000 updates." |
| 8 | B (Simformer) | `loss-2` | `c-loss-2` | `evidence/1_minimal_code_example.ipynb`, `/cells/19/outputs/0/text/2` | `45.425938` (one LF) | `training_loss(45.425938)` | "The original saved notebook output 2 reports mean denoising loss for a block of 5000 updates." |
| 9 | B (Simformer) | `loss-3` | `c-loss-3` | `evidence/1_minimal_code_example.ipynb`, `/cells/19/outputs/0/text/3` | `45.380486` (one LF) | `training_loss(45.380486)` | "The original saved notebook output 3 reports mean denoising loss for a block of 5000 updates." |
| 10 | B (Simformer) | `loss-4` | `c-loss-4` | `evidence/1_minimal_code_example.ipynb`, `/cells/19/outputs/0/text/4` | `45.31089` (one LF) | `training_loss(45.31089)` | "The original saved notebook output 4 reports mean denoising loss for a block of 5000 updates." |

## Where each reading is checked against the producer

- **Rows 1–2.** `package-a/origin/benchmarking.py` (the producer, pinned at
  `7257a17e…`) writes `torch.utils.benchmark` measurement times and labels
  their unit as seconds. The empty CSV header name is the original Pandas
  index, not a missing column. The two indices each select exactly one row of
  5255; other index values repeat and are not used.
- **Rows 3–5.** `package-b/evidence/summary.csv` stores one row per saved
  training run. The selected rows have `metric = none` and `value` either empty
  or `None`; the runtime mappings use `time_train`, not an accuracy result.
  Review the pinned [`hydra_script.py`](https://github.com/mackelab/simformer/blob/a35055613aaae7c84067416932e5636ef34b2ed2/src/scoresbibm/scoresbibm/scripts/hydra_script.py)
  `score_sbi` timing block (`start_time = time.time()` through
  `time_train = time.time() - start_time`) and its call to `save_summary`.
  The pinned [`data_utils.py`](https://github.com/mackelab/simformer/blob/a35055613aaae7c84067416932e5636ef34b2ed2/src/scoresbibm/scoresbibm/utils/data_utils.py)
  `save_summary` writes `"time_train": str(time_train)` to the CSV.
  These are producer-code pointers used for the review recorded below.
- **Rows 6–10.** Notebook cell 19 prints the mean accumulated denoising loss
  over each block of 5000 updates. The five values are five saved positions
  from the *same* run, not five experiments and not accuracy results.

## Accepted independent review

Review date: 2026-10-07. Reviewer: `openai-codex/gpt-6-astra` (reported runtime configuration: `openai-codex/gpt-6-astra:high`). Maintainer acceptance is recorded separately in the [issue comment](https://github.com/ARA-Labs/Lara/issues/20#issuecomment-6027990904): “I took a look and agree with astra.” This agreement accepts the agent verdicts below; it is not recorded as a separate ten-leaf human audit.

| # | Leaf | Agent reviewer, date | Verdict | Rationale / producer source |
| --- | --- | --- | --- | --- |
| 1 | `forward-1631` | `openai-codex/gpt-6-astra`, 2026-10-07 | faithful | Unique CSV key `"" = 1631`, physical line 1633; selected values match `forward_time_s`. Packaged `origin/benchmarking.py` lines 389–406 record ProgressiveNet forward-call timings, lines 137 and 216 label seconds, and lines 435–436 retain the CSV index. Prose claims only the saved record. |
| 2 | `forward-1632` | `openai-codex/gpt-6-astra`, 2026-10-07 | faithful | Unique CSV key `"" = 1632`, physical line 1634; selected values match `forward_time_s`. The same producer lines support method, prior-module count and forward seconds, without a comparison or replication claim. |
| 3 | `train-0` | `openai-codex/gpt-6-astra`, 2026-10-07 | faithful | Unique `model_id = 0`, CSV line 2; method, task and decimal match `training_time_s`. Pinned `hydra_script.py` lines 85–87 time `method_run` in seconds; line 162 forwards the value to `save_summary`; `data_utils.py` lines 194–208 serialize it. No accuracy assertion. |
| 4 | `train-1` | `openai-codex/gpt-6-astra`, 2026-10-07 | faithful | Unique `model_id = 1`, CSV line 3; selected values match `training_time_s`. The same pinned timing and writer lines support elapsed training-call seconds and the claim's runtime wording. |
| 5 | `train-2` | `openai-codex/gpt-6-astra`, 2026-10-07 | faithful | Unique `model_id = 2`, CSV line 4; selected values match `training_time_s`. The same pinned producer lines support seconds; `metric = none` and literal `value = None` do not supply accuracy. |
| 6 | `loss-0` | `openai-codex/gpt-6-astra`, 2026-10-07 | faithful | `/cells/19/outputs/0/text/0` is `46.13004` plus one LF, matching `training_loss` and `decimal-line`. Cells 15 and 17 compute and device-average denoising loss; cell 19 prints its first 5,000-update block mean. |
| 7 | `loss-1` | `openai-codex/gpt-6-astra`, 2026-10-07 | faithful | `/cells/19/outputs/0/text/1` is `45.541588` plus one LF. Cells 15, 17 and 19 support the second saved 5,000-update block mean, not another independent run. |
| 8 | `loss-2` | `openai-codex/gpt-6-astra`, 2026-10-07 | faithful | `/cells/19/outputs/0/text/2` is `45.425938` plus one LF. The same cells support the third saved block mean, with no accuracy assertion. |
| 9 | `loss-3` | `openai-codex/gpt-6-astra`, 2026-10-07 | faithful | `/cells/19/outputs/0/text/3` is `45.380486` plus one LF. The same cells support the fourth saved block mean in this output stream. |
| 10 | `loss-4` | `openai-codex/gpt-6-astra`, 2026-10-07 | faithful | `/cells/19/outputs/0/text/4` is `45.31089` plus one LF. The same cells support the fifth saved block mean, not a final whole-run loss or a separate experiment. |

Totals: ten faithful, zero unfaithful, zero unclear. The agent found no blocking evidence gaps. This review does not establish historical execution provenance or scientific validity and does not satisfy the separate archival paper-promotion protocol.

Reviewed source revision: `5f094b73a4929fc6a2de1d7d5c8c3d8b291ac77b`. The SHA-256 values below identify the inspected local bytes, including edits not identified by the revision alone. Paths are relative to `examples/certified-evidence/`; the linked issue comment also records the original-data and producer hashes.

```text
c0e186ef3622e67a5f6eef88537b6a9121336ccdf6037d702fe013a8bcba97be  package-a/artifact.lara
49b59354b468a8b3d007c72d223c36704009b017058386ada4bebd635e674283  package-a/lara-evidence.sexp
5c6e1dd40391a18e2d35d073280dc9b3ff41d90bd2adbdb7346ab1d61b94bfa2  package-b/artifact.lara
0959e239d2e7fd075e7626617cb5b0fdb1cd9a1baad72dd13e68ea4f3d338f1f  package-b/lara-evidence.sexp
```

## Published reviewed bindings

Recorded 2026-10-07. All ten accepted verdicts are applied to the source audit
metadata. Only binding annotations changed; prose, formal propositions,
extraction requests, original evidence and producer bytes are unchanged.
Both packages pass `lara check-ara`. Their core replay identities, verdicts
and dependency digests match the first freeze; their evidence identities
change because the source capture and manifest pins change.

The inspected hashes above remain the review's historical input identities.
The published source and manifest SHA-256 values are:

```text
03993eb5e7e20a7c6e86c39ad982358e3690578bdbcdda105cc7ab0b64aa9a64  package-a/artifact.lara
1552b0e5694a6c1ec79f354d06e5db6aa715a4601e2325250168a61cd738b812  package-a/lara-evidence.sexp
5da99d4512aa14a4ac891b50c139271e6b91fca736fc28d64602689590bbdb2d  package-b/artifact.lara
2674c18e630642912b75792b2d41e942cf66cdc056ab035029a678c8a448effe  package-b/lara-evidence.sexp
```

[`evidence-measured-inputs@2`](../../../measurements/frozen/evidence-measured-inputs-v2.md)
records the ten-case rerun and matching `evidence-measured-inputs-v2` Git tag.
Issue #20 closes when the publishing PR merges. This publication does not
relabel the agent review as a human audit or establish scientific validity.
