# Freeze record: `evidence-measured-inputs@2`

Recorded 2026-10-07. The real `lara check-ara` command matched all ten declared
inputs after the accepted independent review was applied to the original
packages. The matching annotated Git tag is `evidence-measured-inputs-v2`.
The [first content freeze](evidence-measured-inputs-v1.md), its JSON/TSV reports
and the historical `m5-freeze-*` measurements remain unchanged.

## What changed from the first freeze?

`openai-codex/gpt-6-astra` independently judged all ten original-output mappings
faithful on 2026-10-07. The maintainer accepted those verdicts. The
[review record](../../docs/certified-evidence-human-review-worklist.md#accepted-independent-review)
keeps the reviewer, inspected hashes and per-leaf rationales separate from the
maintainer's agreement.

All ten source bindings now retain `author = ai_inventory`, carry
`audit-status = reviewed`, and name the reviewer, date and accepted review link
in their rationales. Only binding annotations changed. Both manifests pin the
new source lengths and SHA-256 hashes. The
[publication record](../../docs/certified-evidence-human-review-worklist.md#published-reviewed-bindings)
contains those new identities without replacing the inspected identities.

Original CSV/notebook outputs, packaged producer code, natural-language claims,
formal propositions, extraction requests and generated rejection packages are
unchanged. Both original packages accept. Their core replay identities,
verdicts and dependency digests match the first report. Source capture,
manifest, evidence and corpus identities change. The report's scope wording
now excludes independent mapping review rather than the former human-only
review requirement; the measurement still supplies no semantic verdict.

## What does this freeze measure?

| Field | Value |
| --- | --- |
| Freeze identifier | `evidence-measured-inputs@2` |
| Git tag | `evidence-measured-inputs-v2` |
| Report format | `lara-evidence-measure-report@1` |
| Real command | `lara check-ara ROOT [--policy FILE]` |
| Source language | `lara-syntax@0.11` |
| Evidence layer | `lara-evidence@0.1` |
| Core | `lara-core@0.3`, unchanged |
| Measured | Package capture, request binding, extraction, core replay verdict and evidence-report identities |
| Not measured | Scientific validity, historical experiment execution or independent mapping judgments |

The accepted agent review does not become a human audit. Neither the review
nor this measurement satisfies the separate
[archival paper-promotion gate](../../docs/evidence-admission-design.md#archival-paper-promotion-gate).
The first freeze's human-only wording records its historical policy, not the
current review policy for [issue #20](https://github.com/ARA-Labs/Lara/issues/20).

## Which inputs and results are pinned?

The unchanged [corpus manifest](../../fixtures/evidence/measured/MANIFEST.tsv)
declares ten inputs: four acceptance cases and six one-edit rejection cases.
The real command matched all ten classes. Rejections cover binding, capture,
policy, package invalidity and two extraction failures. Accepted cases account
for 13 checked leaves and one declared leaf: the two original packages, a
second package-A run under an identical verifier policy, and a mixed-assurance
quarantine fixture. The two package-A runs are not separate scientific trials.

| Identity | SHA-256 |
| --- | --- |
| Corpus manifest | `5d1db05a90b588fb417d9667faebb4e05c20dfc71cbabb0845bf390dae8580f6` |
| Corpus identity | `afc0295efc1cabc0790a7716d34ab80e39238efb57141c3e4858ee8e7789650b` |
| [Frozen JSON](evidence-report-v2.json) | `2e33dbbc2c69770bbbaa2843961a6ff89c885765a5b2642394bb69eb53679ecb` |
| [Frozen TSV](evidence-report-v2.tsv) | `fbf112dbdb34308df9140797c04db5ccea854e767ec239d28ee2c54b4aa33d40` |

The JSON records each input's captured bytes, requests, result class, located
failure, exit status, stdout/stderr hashes and accepted-report identities.
The harness independently recomputes accepted-report identities and expected
core replay tuples from the package bytes. `--check` compares every
deterministic report block and the TSV, ignoring only `environment`.

The environment records the actual pre-commit run: revision
`2b9146f25c95e6c83fa231c17799b3c8e32ec3eb` with a dirty worktree, GHC 9.10.3,
Python 3.14.8 and the built binary's hash. The tag pins the subsequent clean
commit containing the reviewed sources and this report. Input and corpus
hashes, not the pre-commit revision alone, identify the measured bytes.

## How can the result be reproduced?

```sh
git checkout evidence-measured-inputs-v2
python3 scripts/gen-evidence-measured.py --check
python3 -m unittest scripts/test_evidence_measure.py -v
cabal build exe:lara
scripts/evidence-measure.py --check
make local-gates
```

The active default snapshot is `measurements/frozen/evidence-report-v2.json`
and its paired TSV. To regenerate live reports without replacing any freeze:

```sh
scripts/evidence-measure.py
```

That command writes `measurements/evidence-report.{json,tsv}` only. To reproduce
the historical first freeze, use its source revision, `2b9146f`, and the
[first freeze protocol](evidence-measured-inputs-v1.md). The first report is not
expected to match the reviewed source capture in the second freeze.

## What does another freeze cost?

One rebuild plus ten package-command invocations reproduces this corpus. The
six generated rejection packages total about 20 KiB. No original experiment,
historical core corpus or Lean proof is regenerated. Changes to measured
inputs require a new freeze identifier, new report files and a matching tag;
prior frozen reports must not be overwritten. Changed mappings also require
an independent review with its own inspected source identities.
