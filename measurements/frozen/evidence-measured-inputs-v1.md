# Freeze record: `evidence-measured-inputs@1` (additive check-ara evaluation)

_Recorded 2026-10-06. **Status: the real package-door run matched all ten declared
inputs; its JSON and TSV snapshots are frozen below.** This freeze is separate
from the historical `m5-freeze-*` evaluation snapshots. It does not re-measure,
replace or amend their core results. `evidence-measured-inputs@1` is a content
freeze rather than a Git tag; see "Git tag" below._

`evidence-measured-inputs@1` measures the certified-evidence **package door**
(`lara check-ara`) on real, committed inputs. It is the additive evaluation
[issue #20](https://github.com/ARA-Labs/Lara/issues/20) budgets, and it is
separate from the typed conformance gates: `scripts/evidence-differential.sh`
pins the finite Lean model's behaviour, `test/evidence-cli.sh` pins the CLI's
acceptance and refusal scenarios, and this freeze records what the real door
does on a declared corpus, with the byte identities that let someone else
reproduce it.

## Scope and versions

| Field | Value |
| --- | --- |
| Freeze identifier | `evidence-measured-inputs@1` |
| Report format | `lara-evidence-measure-report@1` (distinct from the door's own `lara-evidence-report 1`) |
| Door under measurement | `lara check-ara ROOT [--policy FILE]` (the real binary) |
| Source language | `lara-syntax@0.11` |
| Evidence layer | `lara-evidence@0.1` |
| Core | `lara-core@0.3` (unchanged; core semantics are not part of this change) |
| Measured | package manifest/capture, request binding, extraction, the core replay verdict, and the evidence-report identities |
| **Not** measured | scientific interpretation, semantic faithfulness, the producers' experiments, or any human judgment |

## Corpus

The corpus is declared in
[`../../fixtures/evidence/measured/MANIFEST.tsv`](../../fixtures/evidence/measured/MANIFEST.tsv)
and materialized by `scripts/gen-evidence-measured.py`; `--check` fails a tree
that no longer regenerates its own fixture bytes, exactly as
`gen-mutants.hs --check` guards the mutation suite.

| Corpus anchor | Value |
| --- | --- |
| Declared inputs | 10 (4 accepted, 6 rejected) |
| Manifest SHA-256 | `5d1db05a90b588fb417d9667faebb4e05c20dfc71cbabb0845bf390dae8580f6` |
| Generated fixture bytes | `fixtures/evidence/measured/` (20 KiB), six packages each one edit from `fixtures/evidence/quarantined` |
| Accepted inputs | the two real committed packages, measured in place, plus the committed `fixtures/evidence/quarantined` package and one identical-verifier-policy run |
| Corpus identity | `sha256` over the canonical JSON of every row's `(case, root, policy, expectation, located leaf/reason, partitions, input tree digest, policy digest)`; recorded as `corpus.identity` in the frozen report |

Nothing under `examples/certified-evidence/` or `fixtures/evidence/quarantined`
is written by the generator, and no original producer byte is edited.

### Accepted inputs and their checked-leaf assurance

| Input | Held-out identity | Assurance | Checked | Declared |
| --- | --- | --- | ---: | ---: |
| `package-a` (CompoNet) | real package, package policy | `evidence-checked` | 2 | 0 |
| `package-b` (Simformer) | real package, package policy | `evidence-checked` | 8 | 0 |
| `package-a-verifier-policy` | same bytes, identical policy supplied as verifier | `evidence-checked` | 2 | 0 |
| `quarantined-mixed` | committed synthetic quarantine fixture | `mixed` | 1 | 1 |

The verifier-policy row exists to pin the one identity a policy override may
move: the core replay tuple, dependency digest and capture union must be
identical to the package-policy row, while the evidence digest must differ
because the policy origin does.

### Rejected inputs and their failure classes

Class names are the typed model corpus's
(`fixtures/evidence/model/MANIFEST.tsv`), so the measured and model evaluations
name the same boundaries.

| Input | Expected class | Located leaf | Expected reason |
| --- | --- | --- | --- |
| `reject-admission` | `policy` | `drop` | admission row `(certified, checker(csv-row, 1)) = reject` |
| `reject-binding` | `binding` | `drop` | `object does not resolve an existing leaf reference` |
| `reject-capture` | `capture` | `drop` | `object SHA256 mismatch` |
| `reject-extraction` | `extraction` | `drop` | `extracted proposition mismatch` |
| `reject-selection` | `extraction` | `drop` | `missing CSV key row` |
| `invalid-global-digest` | `invalid` | — | `object SHA256 mismatch` (package invalidity, exit 2) |

Every rejected input must exit with its class's code (1, or 2 for `invalid`),
emit no stdout, and locate the failure at the leaf above. The `policy` row's
"reason" is descriptive of the rendered admission row; the harness compares the
class and the located leaf there, and compares an exact reason for the other
five rows (the corpus manifest records `-` where no exact reason is fixed). The
offending object id is **not** compared: `renderEvidenceRejection` renders the
leaf and the reason only, so the door's own diagnostics do not name the object.
The typed model corpus is the artifact that fixes the object.

### Independent verification inside the report

For every accepted input the harness re-derives, from the package bytes and the
reported replay tuples, all of: the canonical re-print of the report, the
manifest/source/policy SHA-256 values, the policy origin, the capture union
(globals plus requested objects, in manifest order, each against its actual
bytes), the dependency-report digest, the evidence digest, the partition
disjointness and assurance label, and the equality between each replay's
normalized request and the source's declared `extract`. A record only counts as
matching its class if every one of those holds. The same independent
recomputations are what `test/evidence-cli.sh` performs; this freeze makes them
a measured record over a declared corpus rather than a pass/fail scenario.

## Outputs and anchors

| Output | Contents |
| --- | --- |
| `measurements/frozen/evidence-report.json` | format/freeze/scope, environment, corpus block (manifest hash, input count, corpus identity), aggregate, and one record per input |
| `measurements/frozen/evidence-report.tsv` | the flat table of the same records |

The committed JSON is the single source of truth for the freeze's hashes: the
corpus identity, each input's tree digest, and each accepted record's report
identities. They are deliberately not copied into this document, so the record
cannot drift from the artifact that the gate re-checks. `scripts/evidence-measure.py
--check` recomputes the whole report and compares every deterministic block
(format, freeze, scope, corpus, aggregate, records) against the frozen snapshot,
ignoring only the per-machine environment block on both sides. It also checks
the matching TSV and refuses a snapshot whose inputs fail their expectations.
A corpus, fixture, generator, door-format or door-version change makes that
gate red; re-freeze rather than adjusting an anchor.

## Environment

The frozen report records, in its `environment` block: the input revision and
dirty flag, the `lara` binary path and its SHA-256, GHC, Python, OS and CPU.
The environment block is excluded from `--check` because it is machine state,
not evidence. The flag is recorded as measured, never asserted clean: the
snapshot is normally taken on the branch that carries the corpus and harness,
just before that commit, so `git-dirty: true` at freeze time is expected and
harmless — the freeze's provenance is the commit that carries the snapshot, and
the deterministic blocks are what `--check` enforces. The version identities
that matter are in the records themselves (`lara-syntax@0.11`,
`lara-evidence@0.1`), not in the environment block.

## Reproduction

```sh
python3 scripts/gen-evidence-measured.py --check   # fixtures byte-identical (10 inputs)
python3 -m unittest scripts/test_evidence_measure.py -v
cabal build exe:lara                                # no Lean build is needed
scripts/evidence-measure.py                         # writes measurements/evidence-report.{json,tsv}
python3 scripts/evidence-measure.py --check         # must reproduce measurements/frozen/
```

To cut the initial snapshot (then commit it), or record a new freeze after a change:

```sh
scripts/gen-evidence-measured.py --check
cabal build exe:lara
scripts/evidence-measure.py
cp measurements/evidence-report.json measurements/evidence-report.tsv measurements/frozen/
git add measurements/frozen/evidence-report.json measurements/frozen/evidence-report.tsv
```

## Regeneration budget

A re-run costs one `cabal build exe:lara` plus ten door invocations.
The six generated rejection packages total about 20 KiB; the two original
packages remain within their inventory budgets. The verifier-policy case
checks package A a second time. No original experiment, historical core corpus
or Lean proof is regenerated by this evaluation.

Adding real packages also costs origin, licence and human mapping review.
Declare additions in the corpus manifest and record a new freeze rather than
silently expanding the first snapshot.

## Git tag

There is **no** git tag for this freeze, and none may be minted against a dirty
tree. The repository carries only `v0.1.0`; the historical `m5-freeze-v1` …
`m5-freeze-v8` tags do not resolve here. `evidence-measured-inputs@1` is
therefore a content freeze keyed by the identifier, the corpus manifest hash,
and the corpus identity in the report. A release tag for it requires a clean
commit (or the release merge) and is a maintainer decision, taken with the
release tag, not silently against the working tree.

## What this freeze still owes a human

The ten certified leaves in `package-a` and `package-b` carry
`author = ai_inventory`, `audit-status = unreviewed`. Their semantic
faithfulness — whether the original producer's bytes mean what the claim says —
is a **human** verdict and is not measured here: no LLM may judge it, and this
report must never be presented as if one had. The worklist and independent
human-review recording protocol are
[`../../docs/certified-evidence-human-review-worklist.md`](../../docs/certified-evidence-human-review-worklist.md);
that table is empty on purpose. Until those verdicts are recorded, the
certified-evidence feature may be described as mechanically checked and
measured, and **not** as human-verified.
