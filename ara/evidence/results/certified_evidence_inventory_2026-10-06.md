# Certified-evidence inventory probes, 2026-10-06

This records Task 0 acquisition and throwaway probes, not Lara evidence admission. The durable interpretation, source URLs and reproduction command are in [the inventory](../../../docs/evidence-admission-inventory.md). The approved TSV/JSON portfolio did not clear its gate. No runtime implementation or new Lean result was produced.

## Corpus scan output

Pin: `62e9b54b2d4efe45b97f25676a16784530dd552a`.

```text
packages: 32
files: 2786
bytes: 26736830
evidence_files: 529
evidence_suffix_counts: {'.md': 529}
.tsv: 0
.jsonl: 0
.log: 0
.json: 2
.csv: 1
.ipynb: 4
```

The JSON files are reproduction questionnaires. `/questions/0/expected_results` is a prose string in both; `decimal.Decimal` rejects both strings. Tab-delimited decoding of FTRL `monster_data.csv` yields the one-column header `,Name,Experience,Difficulty,Level`, so the `Name` lookup fails. Its rows describe game metadata, not training results.

## Original-output probe output

```text
original log 163408 e934707bf4d5b73b1b4b69ffbe735cb8803b8d30174aea8ce51571f110570677
unique final row [('3.2783', '301825', '161.84')]
exact candidate propositions validation_loss(flex_attention_20241119, 3.2783) training_time_ms(flex_attention_20241119, 301825)
approved TSV family probe: first row columns 1
```

Source: `KellerJordan/modded-nanogpt@4ea6b937337a4889b8cfe3f38a93d120048d8f71`, `records/track_1_short/2024-11-19_FlexAttention/8384493d-dba9-4991-b16b-8696953f5e6d.txt`. Candidate notation is not a certified Lara proposition.

Five METR archives at `93b98062e55f6945d4a7e213a3226dd419896170` were acquired and inventoried with the published password. `fix_embedding` contains a 33-byte score log, SHA-256 `01b1ff653e1297166afd2306c7cc6ae6326ab6e8999dbd9b9c5187cc4f9e0621`; `rust_codecontests_inference` contains a 48-byte score log, SHA-256 `7655fbe1f6eba24c1b4fa8fd8c84dc84c3690d8a3bb795f54ebc075cd25a8f93`. The other three inspected archives contain no members ending in the candidate result suffixes. No decrypted content was committed.

## Alternative-format acquisition output

```text
CompoNet archive 4918964 4d91703cf10953b4f38818234eea57c2588ab58159943dc4885df1e36bca1059 regular members 4 uncompressed bytes 83494829
smallest members [('data/eval_results.csv', 36644), ('data/benchmarking.csv', 298568), ('data/data_transfer_matrix_raw.csv', 29271861), ('data/agg_results.csv', 53887756)]
Simformer CSV 4397 9274a5de460f391d6862f256433cb004c7d4356c7e43b34f447f4bcdd5d09297
Simformer notebook 286082 3e0d0055bb4688f6753ccb3a14a313a666a883d3a2b38a3f2a04bc85865a9869 matches local True
saved loss scalars ['46.13004\n', '45.541588\n', '45.425938\n', '45.380486\n', '45.31089\n']
benchmark headers dict_keys(['', 'time', 'method', 'total parameters', 'trainable parameters', 'num prevs']) rows 5255
unique index values: 1691
eval rows 2000
```

Sources: CompoNet revision `7257a17e9dbb50f81482da65cdae2086c761aaa2`, `experiments/meta-world/data.tar.xz`; Simformer revision `a35055613aaae7c84067416932e5636ef34b2ed2`, `results/example_guidance/summary.csv` and `example/1_minimal_code_example.ipynb`. These bytes support investigating a CSV/JSON encoding revision; no changed checker portfolio was approved or implemented.

## Exercised documentation verification

```text
3.2783 301825
Documented original-log probe: PASS
Changed documentation local links and fence parity: PASS
clean: docs/evidence-admission-inventory.md
```

The original-log reproduction code in the inventory ran against the pinned upstream bytes and asserted length, SHA-256, unique final-row selection and exact loss/time values. Haskell/Lean runtime gates were not run: this change does not touch executable source, Lean, wire contracts, fixtures, goldens or measured-input freezes. The issue blocker and remaining cost were reported at https://github.com/ARA-Labs/Lara/issues/8#issuecomment-6011704289.

## Epilogue consistency checks

```text
ARA session index: PASS (82 sessions, one row each, every row agreeing with its file)
ARA source spans: PASS (66 quotations)
Existing duplicate observation IDs: {'O176': 2, 'O177': 2}
Strict YAML, trace IDs, new O186 uniqueness/bindings and existing claim dependency references: PASS; historical observation duplicates remain
```

The global observation-ID assertion failed on the historical collisions. The new observation and trace references were then checked separately; the failed global assertion is not reported as passing. Append-only-safe repair is tracked in [issue 18](https://github.com/ARA-Labs/Lara/issues/18).
