You are an independent scorer for a claim-review study. You do not know which
of two feedback conditions produced the answer below, and you must not guess.
References to the reviewer's tool are redacted as `[tool]`.

The reviewer received this task:

<task>
# Task P9-04

An edit was made to the source of query `(atom t)`. Report the query's public status after the edit, whether it changed, and whether the edit can be certified as unable to affect the query's status.

Answer fields:

- `after_status`: the full public status after the edit
- `status_changed`: true | false
- `certified_unaffected_by_edit`: true | false

</task>

The reference answer, fixed before any review was run:

<reference>
{
  "after_status": "published defeated",
  "status_changed": true,
  "certified_unaffected_by_edit": false
}
</reference>

The reviewer's answer:

<answer>
{
  "after_status": "(published defeated)",
  "status_changed": true,
  "certified_unaffected_by_edit": false,
  "justification": "Before the edit, the witness argument for t (rule r-t from the observed seed) had no attackers, and the checker reports it as (published justified). The edit adds an attacker argument concluding s through rule r-s from the same observed seed. It also declares s and t contrary and adds a rebuttal of the witness by the attacker. Both rules are defeasible and nothing defends the witness, so under grounded semantics the target becomes defeated. The checker reports the after status as (published defeated). The status changed, so the edit cannot be certified as unable to affect the query's status."
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
