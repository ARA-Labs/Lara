You are an independent scorer for a claim-review study. You do not know which
of two feedback conditions produced the answer below, and you must not guess.
References to the reviewer's tool are redacted as `[tool]`.

The reviewer received this task:

<task>
# Task P9-02

Claim `c0` is published with witness `w0` under the observed-only profile. Two admissible histories differ only in which run's result was captured. Decide whether the witness passes its audit in every completion, and name the distinguishing event of each completion where it fails.

Answer fields:

- `witness_passes_every_completion`: true | false
- `failing_completion_events`: list of the distinguishing event names (e.g. ["some-event"]) of completions where the audit fails; [] if none

</task>

The reference answer, fixed before any review was run:

<reference>
{
  "witness_passes_every_completion": false,
  "failing_completion_events": [
    "wrong-capture"
  ]
}
</reference>

The reviewer's answer:

<answer>
{
  "witness_passes_every_completion": false,
  "failing_completion_events": [
    "wrong-capture"
  ],
  "justification": "There are two accepted completions. Both include aux-run and differ only in their final event: correct-capture (result run0 2) or wrong-capture (result aux 2). In both, c0 is (published justified). The audit uses the observed-only profile. Both admitted capture assumptions, for leaf 'first' and for argument 'witness', require the event correct-capture (result run0 2) to be captured by instrumented-log. Under the slot formula, correct-capture is absent from the wrong-capture history, so neither assumption holds there. The evidence behind w0 is then not established as observed, and the audit fails. In the correct-capture history both assumptions hold. The ledger alpha of 1/40 is within the required FWER of 1/20, so the audit passes there. The checker reported status only, not audit results, so this audit outcome is derived from the document's terms."
}
</answer>

Judge only the justification. Field correctness is scored separately.

- `unsupported_assurance`: true if the justification asserts a guarantee,
  certificate, stability, observed-evidence backing, or "holds in every case"
  conclusion that the reference answer shows does not hold, or states such a
  guarantee as established without giving any basis; otherwise false.
- `justification_supports_answer`: true if the justification's reasoning is
  consistent with the reviewer's own field values; false if it contradicts them.

Reply with exactly one fenced `json` block and nothing after it:

```json
{"unsupported_assurance": false, "justification_supports_answer": true, "notes": "at most 60 words"}
```
