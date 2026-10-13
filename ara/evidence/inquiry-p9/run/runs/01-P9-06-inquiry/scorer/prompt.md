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
  "certified_unaffected_by_edit": true,
  "rereview_may_be_skipped": true,
  "justification": "Query (atom t) is (published defeated) both before and after the edit, so the status did not change. The edit only adds a new argument 'loop', concluding w from seed through rule r-w, that rebuts itself, plus a self-contrary pair on w. It does not touch the attacker-to-witness rebuttal that defeats t, and it adds nothing that attacks or supports t's ancestry. The checker's impact result for (atom t) gives locality true. That certifies that the query's relevant ancestry and acceptance are unchanged, so the edit cannot affect its grounded status. The transition is accepted-to-accepted, so no completion was rejected. Because the status is certified as unaffected, and not just observed to be the same, skipping re-review is justified."
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
