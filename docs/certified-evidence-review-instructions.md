# Review the ten certified-evidence mappings
**Date:** 2026-10-07

## TL;DR

Issue [#20](https://github.com/ARA-Labs/Lara/issues/20) accepts independent agent or human review of the ten AI-authored mappings. Lara checks the pinned bytes and declared extraction requests, but those checks do not establish what a measurement means. Inspect the original cells, producer code and Lara claims, then record a verdict for each leaf with the reviewer identity and reviewed source hashes. Astra's ten faithful verdicts and the maintainer's agreement are recorded in the [accepted review](certified-evidence-human-review-worklist.md#accepted-independent-review). Applying them to the source audit labels and publishing the next freeze remain separate work.

## Why does this need an independent review?

The author chooses an object, a row or JSON pointer, selected values and a predicate name. The extractor checks that this request reproduces the declared proposition. It does not establish whether the predicate, unit or prose describes the producer's intended quantity. For example, a mapping that calls a training-runtime number an accuracy could agree with its declared proposition and still misread the original output.

Independent review is an acceptance requirement of issue #20, not a prerequisite for running `check-ara` or obtaining `evidence-checked`. That assurance describes byte and extraction checks. The review records a judgment about the meaning of the mapping; it does not prove that the experiment was correct or that the paper's conclusions are true. A reviewer identity and date make the judgment attributable and identify when it was made. They do not guarantee correctness.

## Who can perform the review?

An independent agent or human who can follow the producer code and understand the quantities can review these mappings. On 2026-10-07, the maintainer removed the issue's human-only requirement and accepted the review by `openai-codex/gpt-6-astra`. Record an agent's model identity explicitly and keep its verdicts separate from maintainer acceptance; do not relabel them as human-authored. No two-human-reviewer requirement, external panel or experiment rerun is needed for issue #20. Its revised review requirement does not replace the separate archival paper-promotion protocol.

## 1. Identify the exact source being reviewed

Run these commands from the repository root. Record the revision and source/manifest hashes with the review so a later reader can identify the bytes you inspected. The hashes identify uncommitted source edits that the revision alone would miss.

```sh
git rev-parse HEAD
sha256sum \
  examples/certified-evidence/package-a/artifact.lara \
  examples/certified-evidence/package-a/lara-evidence.sexp \
  examples/certified-evidence/package-b/artifact.lara \
  examples/certified-evidence/package-b/lara-evidence.sexp
```

Open the [ten-leaf worklist](certified-evidence-human-review-worklist.md#the-ten-leaves), [package A source](../examples/certified-evidence/package-a/artifact.lara) and [package B source](../examples/certified-evidence/package-b/artifact.lara). For each worklist row, locate its claim's `nl`, `formal` and `binding` fields and the corresponding leaf's `extract` request. Check the actual source as well as the worklist, since the worklist itself is AI-authored.

## 2. Display the original values and notebook code

This read-only command uses Python's standard library. It prints the five selected CSV rows, the notebook code that computes and prints the loss, and the five saved output strings. It does not rerun the notebook or issue any review verdict.

```sh
python3 - <<'PY'
import csv
import json
from pathlib import Path

base = Path("examples/certified-evidence")
selections = [
    ("package-a", "benchmarking.csv", "", ("1631", "1632"),
     ("", "method", "num prevs", "time")),
    ("package-b", "summary.csv", "model_id", ("0", "1", "2"),
     ("model_id", "method", "task", "time_train", "metric", "value")),
]
for package, filename, key, values, columns in selections:
    path = base / package / "evidence" / filename
    with path.open(encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle))
    for value in values:
        matches = [row for row in rows if row[key] == value]
        if len(matches) != 1:
            raise SystemExit(f"{path}: key {value!r} has {len(matches)} matches")
        print(f"\n{package}/{filename}, key {key!r} = {value!r}")
        print(json.dumps({column: matches[0][column] for column in columns}, ensure_ascii=False))

path = base / "package-b/evidence/1_minimal_code_example.ipynb"
notebook = json.loads(path.read_text(encoding="utf-8"))
for index in (3, 15, 17, 19):
    print(f"\nNotebook cell {index} (zero-based):")
    print("".join(notebook["cells"][index]["source"]))
for index in range(5):
    pointer = f"/cells/19/outputs/0/text/{index}"
    print(pointer, repr(notebook["cells"][19]["outputs"][0]["text"][index]))
PY
```

Keep numeric CSV fields as strings while comparing them with the declarations. This avoids changing the original decimal spelling through floating-point conversion. The notebook strings each include a final newline; the declared `decimal-line` encoding accounts for it.

## 3. Check what the producer says the values mean

For `forward-1631` and `forward-1632`, inspect the packaged [CompoNet producer](../examples/certified-evidence/package-a/origin/benchmarking.py). Trace how it records the `time`, `method` and `num prevs` columns. Confirm that the claim describes a saved forward-runtime record in seconds and that the empty header column is the row key the request selects.

For `train-0`, `train-1` and `train-2`, inspect the pinned Simformer [`score_sbi` timing code](https://github.com/mackelab/simformer/blob/a35055613aaae7c84067416932e5636ef34b2ed2/src/scoresbibm/scoresbibm/scripts/hydra_script.py) and [`save_summary` writer](https://github.com/mackelab/simformer/blob/a35055613aaae7c84067416932e5636ef34b2ed2/src/scoresbibm/scoresbibm/utils/data_utils.py). Trace `start_time = time.time()`, `time_train = time.time() - start_time`, the call to `save_summary`, and the CSV field `"time_train": str(time_train)`. Decide whether `training_time_s` and the claim's prose accurately describe that stored quantity. The selected rows have `metric = none` and `value` either empty or `None`; those fields provide no accuracy measurement.

For `loss-0` through `loss-4`, inspect the displayed notebook cells. Cell 15 defines `loss_fn` using `denoising_score_matching_loss`; cell 17 computes the update's loss; cell 19 accumulates `loss[0] / 5000` over 5000 updates and prints it. Confirm that each pointer selects the stated saved output and that the claim describes the printed mean loss. These are five positions from one saved run, not five independent experiments.

For each row, answer these questions before choosing a verdict:

- Does the request select the intended original record and the right columns or output position?
- Does the formal proposition preserve the selected values, their order, quantity and unit?
- Does the natural-language claim stay within what that saved record and producer code support?

## 4. Record your verdicts

Record each verdict in the existing [review table](certified-evidence-human-review-worklist.md#accepted-independent-review) or a new dated review section when inspecting changed source bytes. Each row needs the reviewer identity (name or model), date, verdict and a rationale naming the original cell and producer code. Use `faithful` when the mapping and its prose are supported, `unfaithful` when you found a specific mismatch, and `unclear` when the available source does not settle the interpretation. Shared producer code can support several rows, but each selected record still needs its own verdict. Preserve the accepted review of the previous source identities.

Include the source revision and hashes from step 1 with the review. You may instead send the same information in a GitHub issue comment or a message and have it transcribed into the worklist without changing your words. Do not sign off merely because the mechanical checks passed.

```text
Reviewer (human name or agent model):
Review date (YYYY-MM-DD):
Maintainer acceptance, if recorded (separate from the reviewer's verdicts):
Source revision and the four source/manifest SHA-256 values from step 1:

For each leaf:
Leaf ID:
Verdict (faithful / unfaithful / unclear):
Rationale, original cell/pointer and producer-code location:
```

## 5. Hand off the recorded review

Leave the package source, manifest and frozen reports unchanged while reviewing them. A maintainer can then apply each accepted `faithful` verdict to the corresponding claim binding, preserve `author = ai_inventory`, update its outdated rationale and set `audit-status = reviewed` with a pointer to the review record. `unfaithful` or `unclear` rows remain unresolved until a mapping correction and another independent review are recorded.

Those source edits change pinned hashes. The maintainer must re-pin the affected source entries, rerun both package checks and record a new measured-input freeze without overwriting the first snapshot. The existing measurement gate deliberately rejects drift from `evidence-measured-inputs@1`. Release tagging and issue closure remain maintainer actions; review acceptance alone does not complete those steps.

## Next Steps

1. Run the read-only commands and compare all ten mappings with the original outputs and producer code.
2. Record the reviewer identity, date, verdicts and reviewed source identities, keeping any maintainer acceptance separate.
3. Have the maintainer apply supported verdicts, verify the changed packages, record the next freeze and check issue #20's remaining acceptance criteria.
