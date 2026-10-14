# D7: a record that omits part of what happened

A paper says its analysis was preregistered. Lara's
[research-process layer](../theory-process.md) asks whether the paper's
research record *entitles* that statement, which is different from asking
whether the statement is true. This demo writes one small research record
three ways and runs each version through `lara inquiry`. The verdict changes
from `unknown` to `certainTrue` only when an admitted source vouches that the
record is complete.

The inputs are in [`examples/process-precommitment/`](../../examples/process-precommitment/).
The demo adds no `.lara` syntax and no CLI command.

## What this demo is

The core checker asks whether a claim's declared support survives every
declared attack. It reads the arguments a paper submits and takes the
record as given. The process layer asks a question one step earlier: when a
record leaves things out, which complete histories could it have come from,
and does a property hold in all of them?

A record denotes every complete history that is consistent with it and uses
only events the reader declares possible. A verdict is `certainTrue` when
the property holds in every such history, `certainFalse` when it fails in
every one, `unknown` when the histories disagree, and `inconsistent` when
there are none. So a missing log entry cannot help a claim. If the record is
silent about an event that would break the claim, the history containing
that event stays possible and the verdict stays `unknown`.

## The case

The following is an **illustrative research record**, not quoted from any
real study. It is written in the four files under
[`record/`](../../examples/process-precommitment/record/).

> **From the paper.** We fixed the analysis plan before touching the
> held-out test set. Plan version 0 was committed first. The test set was
> read once, for evaluation, after that commit, and the evaluation run
> `eval` used plan version 0 on test-set version 0.

The supporting record consists of:

- [`plan.md`](../../examples/process-precommitment/record/plan.md): the
  committed analysis plan, version 0.
- [`access-log.md`](../../examples/process-precommitment/record/access-log.md):
  a hand-kept log with one evaluation read of the test set, a note that the
  read came after the plan commit, and the author's own statement that the
  log lists every access.
- [`eval-run.md`](../../examples/process-precommitment/record/eval-run.md):
  the run, its plan version and its input version.
- [`server-audit.md`](../../examples/process-precommitment/record/server-audit.md):
  an export from the data server, which records every read before returning
  data, saying the logged read was the only one up to submission.

A reviewer asks one question: **was `eval` precommitted?** In the layer's
terms, `run-precommitted eval` holds in a history when the plan version
`eval` used was committed before every evaluation read of its inputs. Every
evaluation read counts, including one that served no reported run.

## How the record is written into Lara

The process layer has no `.lara` syntax. A record is written as a
`process-input 1` document, embedded in the `inquiry-input 1` wrapper that
the shipped `lara` binary reads. Each version of the record is one document:

| Document | Record contents |
| --- | --- |
| [`omitted.sexp`](../../examples/process-precommitment/omitted.sexp) | Plan commit, logged read, run, and the order of commit and read |
| [`declared.sexp`](../../examples/process-precommitment/declared.sexp) | Same, plus the author's completeness note |
| [`instrumented.sexp`](../../examples/process-precommitment/instrumented.sexp) | Same, plus the server's completeness attestation |

Writing a document means making five commitments.

**1. Each sentence the record relies on becomes one entry, with a citation.**
The citation `(at FILE ENTRY)` names the file and anchor it came from. The
semantics never reads the citation; it is there for an auditor to check the
transcription.

```text
(event plan-commit (commit-plan analyst analysis-plan 0) (at record/plan.md plan-v0))
(event test-read (access analyst test-set evaluation) (at record/access-log.md test-read))
(event eval-run (run eval analysis-plan 0 (inputs (input test-set 0)) primary) (at record/eval-run.md eval))
(order plan-commit test-read (at record/access-log.md after-commit))
```

The entries carry no timestamps and their listing order means nothing. The
only ordering evidence is the explicit `order` entry: the commit preceded the
logged read. The transition rules add one more fact: a run needs a committed
plan version, so `eval-run` comes after `plan-commit` in every history.

**2. Completeness statements are entries too, labelled with their basis.**
The note in `access-log.md` and the server export make the same claim, that
every data access up to the cutoff is in the record. They differ in who says
so:

```text
(coverage (complete (scope (kinds data-access) (cutoff 10))) (at record/access-log.md author-coverage) author-declaration)
(coverage (complete (scope (kinds data-access) (cutoff 10))) (at record/server-audit.md server-coverage) instrumented-log)
```

**3. The reader states which bases it trusts.** Here the reader admits
`instrumented-log` and `signed-attestation`, and not `author-declaration`. An
attestation on a basis the reader does not admit stays in the record and is
never applied.

**4. The modeler declares what might have happened off the record.** The
`universe` lists events that could have occurred without being recorded. This
demo declares one: a second evaluation read of the test set, `unlogged-read`.
This is a modeling assumption, and the result is conditional on it. Declaring
an empty universe asserts that nothing unrecorded happened, which would make
every version `certainTrue` (see `fixtures/process/run/empty-universe.sexp`).

**5. The question is a query.** `(verdict precommitted (run-precommitted eval))`.

The wrapper also requires a base checked source. These documents reuse the
one-claim source from the `p0-*` fixtures. A history verdict never reads it.
Checked-source requests such as `status` and `audit` are outside this demo.

## What comes out

From the repository root:

```sh
cabal run -v0 exe:lara -- inquiry examples/process-precommitment/omitted.sexp
cabal run -v0 exe:lara -- inquiry examples/process-precommitment/declared.sexp
cabal run -v0 exe:lara -- inquiry examples/process-precommitment/instrumented.sexp
```

Each command exits 0 with empty stderr and prints one line:

```text
(inquiry-result 1 precommitted (history-verdict (history-count 10) (answer precommitted unknown (completions 10) (holds (history plan-commit test-read eval-run)) (fails (history unlogged-read plan-commit test-read eval-run)))))
(inquiry-result 1 precommitted (history-verdict (history-count 10) (answer precommitted unknown (completions 10) (holds (history plan-commit test-read eval-run)) (fails (history unlogged-read plan-commit test-read eval-run)))))
(inquiry-result 1 precommitted (history-verdict (history-count 2) (answer precommitted certainTrue (completions 2))))
```

| Record version | Completions | Verdict | Why |
| --- | ---: | --- | --- |
| No completeness statement | 10 | `unknown` | An unlogged read before the commit is consistent with the record |
| Author's completeness note | 10 | `unknown` | The note's basis is not admitted, so it removes no history |
| Server's completeness attestation | 2 | `certainTrue` | The admitted attestation rules out every unlogged read |

The counts can be checked by hand. Without the extra read, the run and the
logged read can come in either order after the commit: 2 histories. The
unlogged read can be inserted at any of 4 positions in each: 8 more. It
breaks precommitment only when it comes before the commit, so the histories
disagree. For an `unknown` answer the runner prints one history where the
property holds and one where it fails. The failing one says what the record
would need to rule out: `unlogged-read` before `plan-commit`.

The second row shows what the demo is about. The author's note and the server
export state the same thing. Only the source the reader admits changes the
verdict.

## What this does not show

- `certainTrue` is entitlement relative to the declared universe, the
  reader's admitted bases and the record. It does not show the server log is
  honest, that the transcription from Markdown to entries is faithful, or
  that preregistration made the result true. No theorem in the layer
  establishes any of those.
- The record files are illustrative. Nothing here is an empirical claim
  about a real study.
- The demo exercises history verdicts only. Statistical-family queries,
  submitted-witness audits, sensitivity and edit impact are documented in
  [the theory record](../theory-process.md#what-does-the-inquiry-wrapper-add)
  and exercised by `fixtures/process/inquiry/`.

## Verification

The same records are proved in Lean. `Lara.Examples.ProcessOrder`
(`omitted_read_unknown`, `complete_access_certain`) and
`Lara.Examples.ProcessARA` (`omitted_read_ara`, `admitted_coverage_ara`,
`declared_coverage_not_admitted`) prove the same three verdicts for the same
record shape, with different identifier names. `answerVerdict_eq_verdict` proves
that the reported wire verdict is the model's verdict, and `answer_rename`
proves that renaming identifiers changes no verdict.

`CliSpec.prop_cliProcessPrecommitmentDemo` runs the three documents through
`lara inquiry` and compares stdout, exit code and stderr with the committed
`.expected` goldens. The Lean reference runner gives the same bytes:

```sh
(cd lean && lake build inquiry-run)
for n in omitted declared instrumented; do
  lean/.lake/build/bin/inquiry-run examples/process-precommitment/$n.sexp |
    diff - examples/process-precommitment/$n.expected
done
```
