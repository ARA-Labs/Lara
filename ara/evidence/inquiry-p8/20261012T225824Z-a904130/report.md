# Why this inquiry run is incomplete

The approved local attempt stopped at a Lean timeout and also exposed a wrong
T07 source annotation. It is not a completed P8 evaluation. No production retry
ran. Capture-only replay retained the incomplete outcome and matched the saved
artifacts and deterministic reports byte for byte.

| Observation | Recorded result | Denominator or scope |
| --- | --- | --- |
| Native attempts | 43 | 96 planned native invocations |
| Lean attempts | 44 | 96 planned Lean invocations |
| Completed outputs accepted by the real consumer | 86 | 87 attempted driver invocations |
| Missing invocations | 105 | 192 planned driver invocations |
| Oracle agreement among completed outputs | 42 native; 42 Lean | 43 completed outputs per driver |
| Distinct inputs with completed outputs | 40 per driver | 80 planned distinct input hashes |
| T07 disagreement | Both drivers returned accepted-to-rejected | Frozen oracle requested accepted-to-accepted |
| Timeout | Lean T11-singleton-slots-40 | One invocation; 10-second driver limit |
| Recorded timeout elapsed | 10879.956607 ms | Includes process startup, execution and termination handling |
| Aggregate elapsed | 25761.876774951816 ms | Saved aggregate observation, below the 45-minute deadline |
| Captured locality counterexamples | 0 per driver | Captured accepted-to-accepted comparisons only |

The summary's all-input oracle ratio is 30/80 for each driver. Its rule requires
every planned duplicate capture to agree, so missing duplicate invocations lower
that numerator too. It is a completion bound, not an estimate of semantic
accuracy or a failure rate over observed inputs. Missing and timed-out cases
have no successful semantic observation.

## What caused the failures?

T07 adds a new argument identity while copying the attacker's complete support
term. The program checker rejects duplicate support terms before checking
supports and attacks (`src/Lara/Check.hs`, `checkProgramDetailed`). Changing an
argument name and derived claim name does not make that term distinct. The
independent input review missed this validation boundary. The accepted-to-
accepted graph annotation therefore describes a graph the supplied after-source
never reaches. The frozen input and oracle remain unchanged as evidence; a
correction must retain T07's intended unchanged-status, failed-locality contrast.

The Lean reference computes minimal slot sets by filtering every sublist of the
slot universe (`lean/Lara/Process/Analysis.lean`, `minimalSlotSets`). This case has
two variable slots and forty inert singleton slots, although its family has only
six completions. Static inspection identifies an unbudgeted powerset traversal.
The timeout is one descriptive observation, not a latency estimate or a universal
performance bound. A correction must preserve all minima, ordering, first
realizers and the empty-change rule under the existing semantics.

The runner computed semantic scores after capture execution. T07's oracle
mismatch thus did not stop later invocations before the eventual timeout. A
correction should score each completed pair before advancing while preserving
separate oracle, driver and consumer judgments and the incomplete ledger.

## What evidence is retained?

- [Run metadata](run.json), [per-case results](results.jsonl),
  [all defined summary fields](summary.json) and [tabular summary](summary.tsv)
  retain original times, commands, exits, raw hashes, expected construction
  counters, statuses, audits, sensitivities, conditions and partial coverage.
- `raw/` preserves every attempted driver's stdout and stderr. The timeout's
  streams are empty; the absent response is not a source rejection.
- The sibling replay directory and reproduction receipt retain the exact
  artifact comparison. The sibling preflight directory retains both failed
  setup attempts, successful full local gates, both Haskell suites, selected
  builds and fake-only runner boundary tests. These are correctness/setup
  evidence, not P8 measurements.
- Development controls, authored cases, generated variants and duplicates remain
  separate in the saved reports. Variants are correlated with their seeds.
  Snapshot-only projections use the same captured status rows; this attempt
  cannot establish agent effectiveness or scientific-discovery improvement.

## What work is required before another measurement?

Keep this evidence immutable. Review a genuinely distinct T07 support term and
its small graph; independently re-annotate and refreeze the additive suite.
Implement and prove a finite-row Lean sensitivity procedure equivalent to the
frozen reference, with AxCheck coverage and full local gates. Add fail-fast
semantic scoring to the runner and verify its interruption/replay boundaries.
Then obtain researcher approval for the exact corrected code/input pins and a
fresh local measurement budget. No legacy corpus regeneration, wire/version,
ceiling or freeze-tag change is proposed. P9 live work remains unauthorized.
