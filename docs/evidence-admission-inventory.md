# Certified-evidence original-output inventory
**Date:** 2026-10-06

## TL;DR
The original-output gate has not passed. The pinned ARA corpus lacks packaged TSV and JSON measurement files needed to demonstrate the proposed checker portfolio. Its JSON question files contain expected-result prose; selecting that prose would check an assertion without replaying an original measurement. Runtime implementation remains blocked at Task 0 of the [approved plan](../plans/2026-10-06-ara-certified-evidence.md), and [issue #8](https://github.com/ARA-Labs/Lara/issues/8) remains unresolved.

## Which sources were inspected?
The corpus was initialized with `git submodule update --init corpus/ara-paperbench` at the existing pin `62e9b54b2d4efe45b97f25676a16784530dd552a`. No submodule revision changed. The [corpus README](https://github.com/AmberLJC/ara-paperbench/blob/62e9b54b2d4efe45b97f25676a16784530dd552a/README.md#provenance--quality) says: “These artifacts are reconstructions for research and evaluation purposes; consult the original papers and their licenses for authoritative results.” Its CC BY 4.0 license covers the reconstruction, not an automatic grant to redistribute every linked original output.

A recursive regular-file inventory found 32 artifact directories, 2,786 files and 26,736,830 bytes, excluding repository metadata. All 529 files under package `evidence/` directories have the `.md` extension. The corpus contains no `.tsv`, `.jsonl` or `.log` files, two `.json` question files, one `.csv` game-data file and four notebooks. The inspection also covered saved notebook outputs and documented original-code links. These file counts establish format coverage only; they do not establish replay or provenance.

The documented format repository was cloned separately at `e52a925e9d03b4ada3008653e72f99b04116fca2`, without vendoring it or moving the corpus pin. Its ResNet example contains transcribed Markdown paper tables. Its `the-ara-of-ara` example contains CSV analysis outputs, but no TSV files. Converting CSV or Markdown into TSV would change the acquired output bytes and cannot demonstrate that the approved `tsv-row@1` portfolio occurs in originals.

## Why do the available candidates not pass?
The following byte identities were measured directly from the acquired files. Paths in the first three rows are relative to `corpus/ara-paperbench`; paths in the remaining rows are relative to the format repository. None is admitted as a certified leaf, so no successful leaf identifier or normalized proposition is assigned.

| Candidate file | Bytes | SHA-256 | Probe and exclusion |
| --- | ---: | --- | --- |
| `artifacts/extra/andes/questions.json` | 5,759 | `06bd5b6c50b06992c83f03ba0a74937e57e8d829db55543c0a604a2cd898bb5f` | `/questions/0/expected_results` resolves to a prose string beginning `- Andes average QoE: 0.99`; exact-decimal decoding rejects it. This is a reproduction prompt, not original output. |
| `artifacts/extra/venn/questions.json` | 5,186 | `7338e64b06ba750782fa452368a14f13430e123bc2c795aaac28d9fe434c5b14` | `/questions/0/expected_results` resolves to a prose string beginning `- Even: FIFO=1.38×, SRSF=1.69×, Venn=1.87×`; exact-decimal decoding rejects it. This is a reproduction prompt, not original output. |
| `artifacts/paperbench/ftrl/src/code/sf_examples/nethack/utils/reward_shaping/monster_data.csv` | 8,589 | `dbbb2f907910a1f7fc2a14cbedc8df4be363c4ab0ea9d54934a5af4a97351dec` | A tab-separated decoder sees the single header `,Name,Experience,Difficulty,Level`, so a `Name` selector fails. The file describes game monsters, not measured training results. |
| `examples/the-ara-of-ara/src/extension-harness/analysis/all_scores.csv` | 435,413 | `3ebc053afc92abebb349d9561de8185a2cb706ea331fea5cae3343bdba6cc3d7` | A tab-separated decoder sees one comma-separated header. The file is a CSV analysis table, not a TSV output or an independently acquired second package. |
| `examples/the-ara-of-ara/src/extension-harness/analysis/mlm_scores_all.csv` | 69,592 | `1792738a85b1f98b68fb66131debba989ee6720c8d92adb15f17951638f6d4aa` | A tab-separated decoder sees one comma-separated header. Another table in the same analysis package does not supply an independent package or a second checker family. |

The three `all-in-one/src/code/example/` notebooks contain saved outputs: 20 in the minimal example, six in the two-moons example and five in the SLCP example. These are notebook streams, displays and rendered results, not the proposed original TSV rows. The FTRL hub-example notebook has no saved outputs. Treating notebook code literals, execution counts or GPU-installation output as scientific result leaves would substitute a different claim for the task.

## Which original-output acquisition leads were exercised?
Original outputs are available outside the reconstructed corpus, but the inspected formats do not satisfy the proposed portfolio. The public [NanoGPT record log](https://raw.githubusercontent.com/KellerJordan/modded-nanogpt/4ea6b937337a4889b8cfe3f38a93d120048d8f71/records/track_1_short/2024-11-19_FlexAttention/8384493d-dba9-4991-b16b-8696953f5e6d.txt) at revision `4ea6b937337a4889b8cfe3f38a93d120048d8f71` was acquired unchanged: 163,408 bytes, SHA-256 `e934707bf4d5b73b1b4b69ffbe735cb8803b8d30174aea8ce51571f110570677`. A throwaway anchored selector found exactly one final validation row: `step:1875/1875 val_loss:3.2783 train_time:301825ms step_avg:161.84ms`. Exact-decimal extraction produced the candidate propositions `validation_loss(flex_attention_20241119, 3.2783)` and `training_time_ms(flex_attention_20241119, 301825)`. These are inventory notation, not admitted Lara leaves. A training-log extractor would need a reviewed grammar and request contract; converting this log into TSV would not satisfy original-byte replay. The repository's MIT license requires retaining the copyright and permission notice.

The [METR release](https://github.com/METR/RE-Bench/tree/93b98062e55f6945d4a7e213a3226dd419896170) supplies password-protected official-solution archives. The specialized reader cannot extract encrypted members, so Python's ZIP reader was used with the password published in METR's README. Five archives were inspected. Only `ai_rd_fix_embedding` and `ai_rd_rust_codecontests_inference` contained result-log members; the other three inspected official solutions (`ai_rd_restricted_mlm`, `ai_rd_triton_cumsum`, `ai_rd_nanogpt_chat_rl`) contained no members with `.log`, `.json`, `.tsv`, `.csv`, `.jsonl` or `.txt` suffixes. This is an archive-member inventory, not a claim about unpublished runs or arbitrary embedded data.

| Original archive member | Bytes | SHA-256 | Exact content and exclusion |
| --- | ---: | --- | --- |
| `ai_rd_fix_embedding/official_solution.zip:official_solution/score.log` | 33 | `01b1ff653e1297166afd2306c7cc6ae6326ab6e8999dbd9b9c5187cc4f9e0621` | `2024-08-01T01:12:53+00:00 2.8917`; timestamp plus scalar, not TSV or JSON. |
| `ai_rd_rust_codecontests_inference/official_solution.zip:official_solution/score.log` | 48 | `7655fbe1f6eba24c1b4fa8fd8c84dc84c3690d8a3bb795f54ebc075cd25a8f93` | `2024-08-08T01:15:45.525660, 0.12727272727272726`; timestamp plus comma-separated scalar, not TSV or JSON. |

METR licenses the release under MIT and asks users not to publish unprotected solutions or feed evaluation material into training. No decrypted solution or result log was committed. Private MALT transcripts named by the reconstructed ReBench artifacts are separate acquisition leads; their provenance and redistribution permission cannot be inferred from METR's license.

The inspected [speedrunner template JSON](https://raw.githubusercontent.com/facebookresearch/llm-speedrunner/ec3e4afd6dcf7c99f7b0be35898e40df6e1257c9/workspace_templates/nanogpt_speedrun/record_10/results.json) contains numeric metrics, but its scalar `val_loss` is `3.2782` while its prose summary says `3.2785`. Template availability does not establish that those exact bytes are original experiment outputs. This candidate needs file-specific production provenance before it can count. Further source inspection covered [Venn](https://github.com/SymbioticLab/Venn/tree/f8ada37ae94456c839551e077703882b210ee0e2), [EXP-Bench](https://github.com/Just-Curieous/Curie/tree/db1b1f56159b591515f77e03c55bf473d5c1c201/benchmark/exp_bench) and the [Andes project](https://github.com/llm-qoe/llm-qoe.github.io). The inspected Venn tree omits measured simulator logs; EXP-Bench contains task-curation JSON rather than the agent evaluation results needed by its claims; the Andes page labels its GitHub release “Coming soon.” These are bounded acquisition findings, not evidence that authors have no original data.

## Which portfolio revision is supported by original bytes?
The author repositories for [CompoNet](https://github.com/mikelma/componet/tree/7257a17e9dbb50f81482da65cdae2086c761aaa2) and [Simformer](https://github.com/mackelab/simformer/tree/a35055613aaae7c84067416932e5636ef34b2ed2) supply independent, accessible CSV outputs. CompoNet's README calls `experiments/meta-world/data.tar.xz` the “compressed CSV files used for the figures.” The archive was acquired unchanged: 4,918,964 bytes, SHA-256 `4d91703cf10953b4f38818234eea57c2588ab58159943dc4885df1e36bca1059`. Its four regular members expand to 83,494,829 bytes. The smallest two are `data/eval_results.csv` (36,644 bytes) and `data/benchmarking.csv` (298,568 bytes); the other two are 29,271,861 and 53,887,756 bytes. These sizes distinguish the compressed download from package-storage cost. Copying a complete member is possible without trimming rows; shipping the whole expanded archive exceeds the proposed budget.

Actual member inspection found 2,000 rows in `eval_results.csv`, with repeated `(algorithm, test task, train task, seed)` selections. A checker cannot silently aggregate or pick the first match. `benchmarking.csv` contains 5,255 rows with columns `time`, `method`, `total parameters`, `trainable parameters` and `num prevs`, plus an unnamed index column. Its first recorded time is exactly `0.0031176558695733547` for `ProgressiveNet`. Most index values repeat across settings. A revised row checker still needs an inventory-backed key or explicit compound selector and a claim-linked meaning for each selected measurement. CompoNet is GPLv3; its data/notice requirements must be preserved rather than replacing them with the reconstruction's CC BY 4.0 notice.

Simformer's [summary CSV](https://raw.githubusercontent.com/mackelab/simformer/a35055613aaae7c84067416932e5636ef34b2ed2/results/example_guidance/summary.csv) was acquired unchanged: 4,397 bytes, SHA-256 `9274a5de460f391d6862f256433cb004c7d4356c7e43b34f447f4bcdd5d09297`. Its three unique `model_id` rows report `time_train` values `977.5672931671144`, `1047.1436779499054` and `2717.260816335678`. The `cfg` cells contain quoted commas, so a TSV decoder or naive comma split cannot replay these bytes. The rows' `metric` is `none`; their times cannot be relabeled as posterior accuracy. Simformer uses MIT with attribution and notice requirements.

The original [minimal notebook](https://raw.githubusercontent.com/mackelab/simformer/a35055613aaae7c84067416932e5636ef34b2ed2/example/1_minimal_code_example.ipynb) was also acquired: 286,082 bytes, SHA-256 `3e0d0055bb4688f6753ccb3a14a313a666a883d3a2b38a3f2a04bc85865a9869`. Its bytes exactly match the corpus copy. JSON pointers `/cells/19/outputs/0/text/0` through `/4` yield the saved loss strings `46.13004\n`, `45.541588\n`, `45.425938\n`, `45.380486\n` and `45.31089\n`. String extraction can preserve those values exactly. Interpreting them as numeric loss requires an explicit reviewed encoding for the trailing line feed; formatted timing strings require a separate parsing operation. These findings justify considering `csv-row@1` plus a precisely scoped JSON-pointer encoding, but do not approve that replacement or supply the required reviewed ten-leaf mapping.

## What is the storage cost?
The rejected Andes, Venn and FTRL package directories occupy 317,540, 276,796 and 2,431,780 bytes respectively. Their largest files are `trajectory.html` (141,268 bytes), `trajectory.html` (154,520 bytes) and `src/code/sf_examples/nethack/render_utils/Hack-Regular.ttf` (305,316 bytes). Every existing corpus package is below the proposed 5 MiB limit; the largest is `adaptive-pruning` at 2,860,278 bytes. Storage did not block this inventory. Acquired original outputs could still exceed that budget. No success package was committed under `examples/certified-evidence/`, and no original file was trimmed, converted or replaced with synthetic assertions.

## Which gate conditions remain unmet?
[Decision §7](evidence-admission-decision.md#7-inventory-gate) requires original outputs from at least two independently produced packages, at least ten leaves across at least two claim families, and at least two deterministic checker families. This run established no complete original-output package/leaf mapping satisfying those conditions. In particular, the proposed TSV family lacks an original-output demonstration. Hashes of rejected candidates and the existence of reconstructed tables cannot count toward the gate.

No manifest syntax, numeric limit, report codec or new source syntax was frozen. Those choices depend on the inventory-backed contract review required by Task 0. No evidence runtime, source certification enforcement, Lean evidence theorem, package command, golden or measurement freeze was changed. The spec's current unenforced-witness limitation remains accurate; this record does not resolve issue #8.

## Appendix: Reproduction
Initialize the recorded corpus revision, then inspect its provenance and candidates without rewriting the files:

```sh
git submodule update --init corpus/ara-paperbench
git -C corpus/ara-paperbench rev-parse HEAD
sha256sum corpus/ara-paperbench/artifacts/extra/andes/questions.json \
  corpus/ara-paperbench/artifacts/extra/venn/questions.json \
  corpus/ara-paperbench/artifacts/paperbench/ftrl/src/code/sf_examples/nethack/utils/reward_shaping/monster_data.csv
```

The format examples were acquired with:

```sh
git clone https://github.com/ARA-Labs/Agent-Native-Research-Artifact /tmp/lara-evidence-format
git -C /tmp/lara-evidence-format checkout e52a925e9d03b4ada3008653e72f99b04116fca2
```

The original-log probe can be repeated without converting the input:

```python
import hashlib
import re
from decimal import Decimal
from urllib.request import urlopen

url = "https://raw.githubusercontent.com/KellerJordan/modded-nanogpt/4ea6b937337a4889b8cfe3f38a93d120048d8f71/records/track_1_short/2024-11-19_FlexAttention/8384493d-dba9-4991-b16b-8696953f5e6d.txt"
raw = urlopen(url).read()
assert len(raw) == 163408
assert hashlib.sha256(raw).hexdigest() == "e934707bf4d5b73b1b4b69ffbe735cb8803b8d30174aea8ce51571f110570677"
matches = re.findall(
    r"^step:1875/1875 val_loss:([0-9]+\.[0-9]+) train_time:([0-9]+)ms step_avg:([0-9]+\.[0-9]+)ms$",
    raw.decode("utf-8"), re.MULTILINE,
)
assert len(matches) == 1
loss, time_ms, _ = matches[0]
assert Decimal(loss) == Decimal("3.2783")
assert int(time_ms) == 301825
print(loss, time_ms)
```

The acquisition and extraction probes ran against original checked-out bytes with Python's UTF-8 decoder, JSON parser, `decimal.Decimal` and tab-delimited `csv` reader. They were throwaway inventory probes, not a Lara evidence checker or a successful admission run. No generated probe file remains in the repository.

## Next Steps
1. Track original-output acquisition and redistribution permissions in issue #8. Record an immutable revision, byte hash, origin and package-local path for each usable output.
2. Demonstrate exact selectors and normalized propositions for the full gate before runtime edits. If original formats require CSV or notebook extraction, revise and review the checker portfolio rather than relabeling converted data as TSV originals.
3. Resume Task 0's contract review, then Tasks 1 through 7, only after the inventory passes. Budget the additive evaluation, two-annotator faithfulness review and measured-input/report freeze separately from historical declared-evidence measurements.
