This candidate repairs the added attacker in T07. Its after policy copies the
existing `r-s` rule as `r-s-new`. The new attacker alone uses that rule. Both
rules have the same seed premise and `s` conclusion, while their rule IDs make
the complete support terms distinct. The existing witness, consumer and attacker
keep their original terms. Both attackers defeat the witness and its consumer;
neither attacker is attacked. The queried witness stays defeated, and the new
incoming ancestry makes locality false.

The candidate contains 16 development controls, 16 authored controls and 64
variants. Only T07 and its four source-declaration variants change input bytes.
Every expected result AST stays the same as in the original suite. Source-axis
levels 0, 1, 4 and 16 count leaf-root groups, which add 0, 2, 8 and 32 AST
declarations per endpoint. The original researcher clarification remains in the
protocol. Original inputs, oracles, certificates and review receipts remain
untouched in `evaluation/inquiry-p8/`.

`ground_support_annotations` in the five repaired oracles explicitly records
complete ground terms for every argument on each endpoint. The authoring guard
checks leaf and rule IDs, ordered substitutions, nested premises, discharge
maps, holes and assurance. Argument IDs and derived claim names label rows and
never enter a term key. For these parameter-free sources, the guard checks that
all rules are parameter-free and question-free defeasible rules with nullary
atom premises and conclusions, empty premise labels and certifiers, and false
allow-trusted flags. It resolves only the listed leaf/argument
references to compare the source payload with the explicit annotations. It
rejects equal support keys, missing rows, recursive or unknown references, and
unsupported syntax. It does not infer propositions, establish typing or compute
attacks or acceptance. The real checker remains the semantic authority. The
negative test gives the new attacker the old `r-s` term and requires rejection
by the guard; the repaired `r-s-new` example passes.

Fresh independent input and quality reviews passed. Their exact immutable
receipts are attached to all 96 oracle entries. Supplemental reviews of the
state-only generator change, metadata attachment and proposed data policy
passed. The original and helper-only approval receipts remain immutable.
`approval-provenance-amendment.json` records the transitive metadata scope
required by the corrected test helper. The protocol's `correction_approval`
field selects the effective receipt at freeze.
The prepared audit tool retains finite graph, history, selection, subset, counter and certificate
checks and adds direct source checks for the fresh cloned rule and additive
T07 declarations. Running it without `--reviewer` is an authoring check and
cannot write an independent review receipt. The real consumer has decoded all
96 inputs and encoded authored expected ASTs. This authoring work invoked no
inquiry driver and ran no pilot or measurement.

To reproduce the authoring checks from the repository root:

```sh
python3 scripts/inquiry_evaluation_cases.py --suite evaluation/inquiry-p8-corrected --recipe-version inquiry-p8-recipes@2-candidate --check
python3 scripts/inquiry_evaluation_cases.py --check
python3 test/inquiry_corrected_candidates.py
python3 test/inquiry_approval_receipt.py
python3 test/inquiry_evaluation_boundaries.py
python3 test/inquiry_evaluation_runner.py
python3 evaluation/inquiry-p8-corrected/review/independent_finite_audit.py
python3 scripts/inquiry_corrected_validation.py --suite evaluation/inquiry-p8-corrected --consumer /tmp/p8-consumer --out /tmp/new-p8-corrected-authoring-validation.json
```

The last command needs the retained real consumer and a fresh receipt path.
Its expected AST stream is encoded from each authored oracle, never from a
driver. `authoring-validation.json` attaches the exact selected consumer hash,
build command and per-case commands, inputs, oracle hashes and process results
from `review/authoring-validation-fixture-provenance-raw.json`. That raw receipt
keeps the helper's unconditional PENDING independent-review marker. The
attachment claims successful decoding only; it links existing independent
semantic judgments and the composite quality receipt rather than inventing a
new semantic review. Earlier authoring receipts remain unchanged under `review/`.

The retained independent semantic review binds all 96 input and semantic
identities. `quality-review.json` is an author-attached composite of the
original independent quality judgment and the final independent test-helper
review. Its predecessor is preserved byte-for-byte at
`review/quality-review-before-fixture-amendment.json`.
`review/test-fixture-metadata-attachment.json` records the resulting oracle
provenance hashes. `review/test-fixture-scientific-identity.json` records exact
comparison against committed baseline blobs: inputs, expected ASTs, semantic
specifications, ancestry and counters are unchanged. Only review metadata moves.

`researcher-approval-provenance.json` binds the final reviewed candidate commit
and exact `candidate-protocol-provenance.json` and
`candidate-manifest-provenance.json` snapshots, with user provenance and
metadata-only freeze authorization. Earlier snapshots and approvals remain
immutable. The helper-only freeze failed preflight before measurement because
its quality receipt still pinned the old test source; its failed preflight and
withdrawn readiness clearance remain retained.
The frozen protocol cannot record its own approval, so the T07 amendment and
the data policy carry the status `requires-correction-receipt`. The receipt
approves them. `approved_amendments` holds one entry for `distinct-t07-support`
with the researcher's non-blank approval text and the SHA256 of its
interpretation in UTF-8. `data_policy_sha256` is the SHA256 of the data policy
as `json_bytes` encodes it: sorted keys, compact separators, UTF-8 and one
trailing newline. The loader refuses a receipt that omits either one, repeats
an amendment id, gives a non-string id or binds different text.
The loader permits only changes to protocol `freeze.state`,
`freeze.manifest_sha256`, and the `correction_approval` state/path/hash linkage.
Every other protocol field, including supporting artifacts, the input commit
rule and legacy tag flag, stays exact. The manifest may change only its state;
all case bytes, meanings, ancestry, counters and completed review identities
stay bound to the approved candidate. Preflight verifies both candidate files against that commit and
requires the final input commit to descend from it. The final input commit is
supplied through `--input-commit`, avoiding a hash written into its own commit.
A draft candidate, a freeze marker alone or a changed approved candidate fails
before driver resolution. Replay reads the saved input identity and runs no
processes. There is no approval bypass flag.

The refusal tests construct explicit temporary draft or unapproved suites,
independent of this candidate's current state. The approval-state test first
loads a complete synthetic approved fixture, then changes only that state.
`approval-amendment.json` records the initial helper-only scope.
`approval-provenance-amendment.json` extends its metadata attachment to every
dependent quality, oracle, manifest and authoring receipt hash. Production
code, scientific content, data policy and the single-attempt budget are unchanged.

The runner uses saved-run schema version 2. It publishes `run.json` and its
embedded `metadata_sha256` in one atomic replacement, without a separate
`run.sha256`. Replay still verifies and copies original version-1 evidence
byte-for-byte. An interrupted write leaves a consistent checkpoint, but an
unsealed checkpoint is not a replayable report. The exact runner and regression
test hashes are pinned in `protocol.json`. `review-package.json` retains the
checkpoint reviews against their original source hashes and the later GitHub
review confirming the deadline, raw-inventory and report-binding fixes. The
later review requested a candidate-pin refresh; its CHANGES_REQUESTED verdict
is retained, not relabeled as approval. Helper-only reviews do not replace the
independent input or oracle reviews.

The approved measurement budget is 96 documents, 192 driver invocations,
one invocation per driver per document, a 10-second driver timeout, a 45-minute
aggregate deadline, one CPU and zero repeats. The single corrected attempt is
complete; [its report](../../ara/evidence/inquiry-p8/20261013T071248Z-317f210-corrected/report.md)
links the sealed captures, capture-only replay and preflight evidence.
The approved data policy uses repository fixtures and authored synthetic
inputs only. Capture, replay and preflight evidence are retained under
`ara/evidence/inquiry-p8/`. The original failed attempt is preserved.
The measurement acquired no network data and made no paid calls.
The repeated-request levels stay below every declared limit, so no case expects
a refusal. The consumed budget authorizes no further measurement attempt.
P9, legacy regeneration and freeze-tag changes remain unapproved.
