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
passed. Researcher correction/protocol approval and a fresh budget remain
pending. The prepared audit
tool retains finite graph, history, selection, subset, counter and certificate
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
python3 test/inquiry_evaluation_boundaries.py
python3 test/inquiry_evaluation_runner.py
python3 evaluation/inquiry-p8-corrected/review/independent_finite_audit.py
python3 scripts/inquiry_corrected_validation.py --suite evaluation/inquiry-p8-corrected --consumer /tmp/p8-consumer --out /tmp/new-p8-corrected-authoring-validation.json
```

The last command needs the retained real consumer and a fresh receipt path.
Its expected AST stream is encoded from each authored oracle, never from a
driver. `authoring-validation.json` records the selected consumer hash, build
command, exact per-case commands, inputs, oracle hashes and process results.
The pre-provenance snapshot is retained exactly as
`review/authoring-validation-before-review.json`. The consumer ran again against
the final attached oracle bytes; its exact raw receipt is retained as
`review/authoring-validation-after-review-raw.json`. The canonical receipt
records that run and names the actual spec and quality reviewers and receipt
hashes when correcting the helper's fixed PENDING review-status annotation to
PASS. Every raw command, process result, input/oracle/AST hash and byte field
is preserved. Researcher approval remains pending.

The independent reviewers inspected the actual source bytes and annotations,
and their retained receipts bind all 96 input and semantic identities.
`review/metadata-attachment.json` records the canonical attachment, with the
before/after oracle hashes and unchanged input, semantic, expectation, ancestry
and counter hashes. The named independent spec reviewer has issued the retained semantic receipt;
this author has attached its exact bytes and has not issued an independent
receipt. Any review
must bind the new input hashes, semantic-content hashes, ancestry and helper
bytes; the original suite's reviews do not apply to this candidate.

The researcher must approve the exact candidate protocol hash and committed
candidate identity before measurement. Approval may explicitly authorize the
later metadata-only freeze. The receipt must name the researcher, carry user
provenance, bind saved candidate protocol and manifest copies by SHA256, name
the full reviewed candidate commit, and authorize metadata-only freeze changes.
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

The proposed measurement budget remains 96 documents, 192 driver invocations,
one invocation per driver per document, a 10-second driver timeout, a 45-minute
aggregate deadline, one CPU and zero repeats. No new budget is approved here.
The proposed data policy uses repository fixtures and authored synthetic
inputs only. It requests one fresh local capture directory under
`ara/evidence/inquiry-p8/<fresh-run-id>` and a local replay directory under
`ara/evidence/inquiry-p8/<fresh-run-id>-replay`. The original failed attempt
and every new outcome will be retained for the requested implementation PR.
Measurement will acquire or transfer no data over the network and make no
paid calls. The researcher must approve this proposed policy in the fresh
budget request. P9, legacy regeneration and freeze-tag changes remain unapproved.
