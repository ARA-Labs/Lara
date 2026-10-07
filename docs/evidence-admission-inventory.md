# Certified-evidence original-output inventory

**Date:** 2026-10-06. **Status:** the revised CSV-row + JSON-pointer portfolio passes the original-output gate and concrete-contract review. This is extraction and contract-review evidence, not a runtime or proof gate pass.

The earlier TSV-row portfolio did not pass. The pinned ARA corpus contains reconstructed Markdown tables, question JSON with expected-result prose, and original CSV rather than original TSV. The approved plan permits an inventory-backed portfolio revision. The user confirmed that the deliverable is the feature, not a documentation-only stop. The revised portfolio preserves author bytes and specifies their actual formats.

## Originals, origins and storage

`package-a` and `package-b` are Lara checking packages for independently authored research outputs. Their `PAPER.md` files are copied unchanged from the corresponding packages in `ara-paperbench` at `62e9b54b2d4efe45b97f25676a16784530dd552a`. The Lara source assertions, policies and checking manifests are newly authored. Neither ARA reconstruction nor the new checking profile is represented as the producer of the measured outputs. Checking `PAPER.md` pins the accompanying document; it does not validate a complete upstream ARA or its scientific claims.

| Package | Original authors and repository | Pinned revision | Redistribution |
| --- | --- | --- | --- |
| A: CompoNet | Mikel Malagón, Josu Ceberio, Jose A. Lozano; [mikelma/componet](https://github.com/mikelma/componet) | `7257a17e9dbb50f81482da65cdae2086c761aaa2` | Original repository GPLv3 license retained in `ORIGINAL-LICENSE`; original producer source and notices retained, not relicensed as Lara data |
| B: Simformer | Manuel Gloeckler, Michael Deistler, Christian Weilbach, Frank Wood, Jakob H. Macke; [mackelab/simformer](https://github.com/mackelab/simformer) | `a35055613aaae7c84067416932e5636ef34b2ed2` | Original MIT license and copyright notice retained in `ORIGINAL-LICENSE` |

Files below are complete original files, not regenerated tables or trimmed rows. Acquisition used pinned raw GitHub URLs; copying the UTF-8 bytes was followed by byte equality with the fetched originals.

| Package object | Package-local path | Bytes | SHA-256 |
| --- | --- | ---: | --- |
| A / `benchmarking` | `evidence/benchmarking.csv` | 298568 | `d346381c8af21c6b51440a181af3bf475edca0ce63c5e95362845a23a30261f6` |
| B / `summary` | `evidence/summary.csv` | 4397 | `9274a5de460f391d6862f256433cb004c7d4356c7e43b34f447f4bcdd5d09297` |
| B / `notebook` | `evidence/1_minimal_code_example.ipynb` | 286082 | `3e0d0055bb4688f6753ccb3a14a313a666a883d3a2b38a3f2a04bc85865a9869` |

CompoNet's CSV is the full `data/benchmarking.csv` member of the pinned [original archive](https://raw.githubusercontent.com/mikelma/componet/7257a17e9dbb50f81482da65cdae2086c761aaa2/experiments/meta-world/data.tar.xz): 4918964 compressed bytes, SHA-256 `4d91703cf10953b4f38818234eea57c2588ab58159943dc4885df1e36bca1059`. Its four expanded members total 83494829 bytes. Selecting one complete original member avoids that storage cost without rewriting the file. The pinned [producer](https://github.com/mikelma/componet/blob/7257a17e9dbb50f81482da65cdae2086c761aaa2/experiments/meta-world/benchmarking.py) stores `torch.utils.benchmark` measurement times and labels them inference time in seconds; a complete copy is retained at `origin/benchmarking.py`.

Simformer's [CSV](https://raw.githubusercontent.com/mackelab/simformer/a35055613aaae7c84067416932e5636ef34b2ed2/results/example_guidance/summary.csv) and [notebook](https://raw.githubusercontent.com/mackelab/simformer/a35055613aaae7c84067416932e5636ef34b2ed2/example/1_minimal_code_example.ipynb) are direct original repository files. The notebook is byte-identical to the pinned corpus copy. Its cell 19 prints the mean accumulated denoising loss over each block of 5000 updates; the five selected saved values are not accuracy results or summaries transcribed from a paper. The CSV has `metric = none`; only its saved training runtimes are used, not its empty metric fields.

Each package has a **5 MiB** budget and uses ordinary Git blobs, not Git LFS pointers. Acquired original files, licenses, producer source and `PAPER.md` total 352790 bytes for A and 298788 bytes for B before the small new checking sources, manifests and origin notes. Largest objects are A's 298568-byte CSV and B's 286082-byte notebook. Final package totals are checked with the implementation evaluation.

## Ten-leaf mapping

Each row names a single deterministic extraction. Object metadata and license are given above; every leaf uses that exact object, original revision and hash. CSV matching compares the raw key field, rejects zero or multiple matches, and selects columns in the stated order. An empty header name is deliberate: it is the original Pandas index column, not a missing header.

| Package / leaf | Claim family | Checker | Object / selector | Ordered encodings | Normalized proposition |
| --- | --- | --- | --- | --- | --- |
| A / `forward-1631` | Forward-runtime record | `csv-row@1` | `benchmarking`; key column `""` = `1631` | `""`: decimal; `method`: text; `num prevs`: decimal; `time`: decimal | `forward_time_s(1631,"ProgressiveNet",10,0.0030154159758239985)` |
| A / `forward-1632` | Forward-runtime record | `csv-row@1` | `benchmarking`; key column `""` = `1632` | same ordered columns | `forward_time_s(1632,"ProgressiveNet",10,0.0030042969156056643)` |
| B / `train-0` | Training-runtime record | `csv-row@1` | `summary`; `model_id` = `0` | `method`: text; `task`: text; `time_train`: decimal | `training_time_s("score_transformer","two_moons_all_cond",977.5672931671144)` |
| B / `train-1` | Training-runtime record | `csv-row@1` | `summary`; `model_id` = `1` | same ordered columns | `training_time_s("score_transformer_joint","two_moons_all_cond",1047.1436779499054)` |
| B / `train-2` | Training-runtime record | `csv-row@1` | `summary`; `model_id` = `2` | same ordered columns | `training_time_s("score_transformer_undirected","slcp_all_cond",2717.260816335678)` |
| B / `loss-0` | Saved denoising-loss record | `json-pointer@1` | `notebook`; `/cells/19/outputs/0/text/0` | decimal-line | `training_loss(46.13004)` |
| B / `loss-1` | Saved denoising-loss record | `json-pointer@1` | `notebook`; `/cells/19/outputs/0/text/1` | decimal-line | `training_loss(45.541588)` |
| B / `loss-2` | Saved denoising-loss record | `json-pointer@1` | `notebook`; `/cells/19/outputs/0/text/2` | decimal-line | `training_loss(45.425938)` |
| B / `loss-3` | Saved denoising-loss record | `json-pointer@1` | `notebook`; `/cells/19/outputs/0/text/3` | decimal-line | `training_loss(45.380486)` |
| B / `loss-4` | Saved denoising-loss record | `json-pointer@1` | `notebook`; `/cells/19/outputs/0/text/4` | decimal-line | `training_loss(45.31089)` |

The two CompoNet index values each select exactly one row among 5255 rows; many other original index values repeat and were not selected. Simformer's three `model_id` values each select exactly one row. The notebook's five values are distinct saved output positions from the same run, not five independently replicated experiments. The gate counts supported leaf assertions, not independent experiment replicates. The runtime and loss families do not assert comparative superiority or validate the producers' scientific interpretation.

## Extraction demonstration

A throwaway probe decoded the acquired CSV bytes with Python's CSV parser, checked unique key matches, traversed the notebook's saved JSON output positions, and rendered exact `Decimal` values without floating point. For `decimal-line`, it required a JSON string ending in exactly one LF and applied the decimal grammar only to the preceding characters. It did not trim arbitrary whitespace, convert CSV to TSV, rerun the notebooks, or edit the original bytes.

Observed output:

```text
PASS: original extraction inventory 10 leaves, 2 independent author packages,
3 claim families, 2 independently specified extraction families
package-a captured original-file bytes 352790
package-b captured original-file bytes 298788
```

All ten printed propositions matched the table above. The explicit decimal-line encoding is an inventory-backed extension for an original producer's numeric printed output; ordinary JSON numeric selection remains separately typed. CSV row selection and JSON pointer traversal are independently specified operations, not aliases or two versions of one checker.

## Contract review and implementation boundary

The concrete contract records comma quoting, JSON duplicate-key rejection, exact numeric bounds, canonical manifest/report encoding, safe descriptor-relative capture, source enforcement, precedence, policy origin and the trusted base in [the evidence-admission design](evidence-admission-design.md#concrete-package-contract). Independent capture/security and semantic/composition reviews completed. Their fixes are incorporated: reject NUL in package paths before POSIX conversion, and require atomic no-replace publication with no check-then-rename fallback. The semantic review confirmed once-expanded source binding and staged whole-source precedence. Runtime implementation has since landed and is in review (see the design). This inventory alone does not claim a passing package command, Lean theorem, cross-check or `make local-gates` run; the landing status of those is recorded in the design.

The earlier negative probe results remain historical evidence for rejecting the TSV portfolio and prose-only witnesses. The source path is now enforced end to end, so the format mismatch is no longer treated as an unavailable prerequisite and issue #8 closes with the feature. The two committed packages hold 352790 and 298788 bytes of original files, comfortably inside the plan's 5 MiB-per-package budget, with the largest single object 298568 bytes (`package-a`'s `evidence/benchmarking.csv`); no original byte was trimmed to fit.

_Update, 2026-10-06: the additive evaluation is now implemented as the independent freeze `evidence-measured-inputs@1` — the corpus is [`../fixtures/evidence/measured/MANIFEST.tsv`](../fixtures/evidence/measured/MANIFEST.tsv), the harness is `scripts/evidence-measure.py` over the real `lara check-ara` door, and the protocol and regeneration budget are [`../measurements/frozen/evidence-measured-inputs-v1.md`](../measurements/frozen/evidence-measured-inputs-v1.md). The remaining [issue #20](https://github.com/ARA-Labs/Lara/issues/20) obligation is the human semantic-faithfulness verdict on the ten leaves, which no tool may record: see [`certified-evidence-human-review-worklist.md`](certified-evidence-human-review-worklist.md)._

_Update, 2026-10-07: the maintainer removed issue #20's human-only review requirement and accepted the independent review by `openai-codex/gpt-6-astra`. All ten mappings received faithful verdicts; the [review record](certified-evidence-human-review-worklist.md#accepted-independent-review) preserves the agent's identity, source hashes and per-leaf rationale separately from the maintainer's agreement. This supersedes the review obligation in the preceding update. Issue #20 still tracks applying the accepted verdicts, preserving `author = ai_inventory`, re-pinning the changed sources, checking the packages and publishing the next additive report/freeze and matching tag. The review does not change the mechanical guarantee or establish scientific validity._

_Publication, 2026-10-07: all ten accepted verdicts are applied to the binding annotations, with `author = ai_inventory` preserved. The package manifests pin the new source bytes; original evidence and producer bytes remain unchanged. Both packages pass `lara check-ara`, and the [second additive freeze](../measurements/frozen/evidence-measured-inputs-v2.md) reproduces all ten declared cases under the matching `evidence-measured-inputs-v2` tag. The [published source identities](certified-evidence-human-review-worklist.md#published-reviewed-bindings) are separate from the inspected review identities. This completes the remaining issue #20 implementation work; the issue closes on merge._
