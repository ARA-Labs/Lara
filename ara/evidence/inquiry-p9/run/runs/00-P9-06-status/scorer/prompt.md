You are an independent scorer for a claim-review study. You do not know which
of two feedback conditions produced the answer below, and you must not guess.
References to the reviewer's tool are redacted as `[tool]`.

The reviewer received this task:

<task>
# Task P9-06

An edit was made to the source of query `(atom t)`. A reviewer proposes skipping re-review of the claim because its status is the same before and after. Decide whether the status changed and whether the edit can be certified as unable to affect the query's status, so that re-review may be skipped.

Answer fields:

- `status_changed`: true | false
- `certified_unaffected_by_edit`: true | false
- `rereview_may_be_skipped`: true | false

</task>

The reference answer, fixed before any review was run:

<reference>
{
  "status_changed": false,
  "certified_unaffected_by_edit": true,
  "rereview_may_be_skipped": true
}
</reference>

The reviewer's answer:

<answer>
{
  "status_changed": false,
  "certified_unaffected_by_edit": false,
  "rereview_may_be_skipped": false,
  "justification": "The query (atom t) is published and defeated both before and after the edit, so its status did not change. The edit adds a new rule r-w, a predicate w, a contrariness between w and itself, and an argument 'loop' that rebuts itself. On inspection this new argument only attacks itself and does not seem to touch the witness for t or its attacker. However, the checker reports only the status at each endpoint. It issues no certificate or dependency proof saying the edit cannot affect the query's status. Having the same status at both endpoints is an observation, not a certification that the edit cannot matter. Without that certification, the proposal to skip re-review is not supported, so the claim should be re-reviewed."
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
