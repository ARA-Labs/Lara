You are an independent scorer for a claim-review study. You do not know which
of two feedback conditions produced the answer below, and you must not guess.
References to the reviewer's tool are redacted as `[tool]`.

The reviewer received this task:

<task>
# Task P9-03

An edit was made to the source of query `(atom t)`. Report the query's public status after the edit, whether it changed, and whether the edited result may be published as backed by observed evidence.

Answer fields:

- `after_status`: the full public status after the edit, e.g. "published justified"
- `status_changed`: true | false
- `publishable_as_observed_evidence`: true | false

</task>

The reference answer, fixed before any review was run:

<reference>
{
  "after_status": "evidence-blocked justified",
  "status_changed": true,
  "publishable_as_observed_evidence": false
}
</reference>

The reviewer's answer:

<answer>
{
  "after_status": "evidence-blocked justified",
  "status_changed": true,
  "publishable_as_observed_evidence": false,
  "justification": "The edit adds a defender argument built from the user-observed seed through a new rule r-u. It rebuts the attacker, whose s conclusion conflicts with t. The checker reports that query (atom t) went from (evidence-blocked defeated) before the edit to (evidence-blocked justified) after it, and marks the change as true. Locality is false, so nothing certifies that the edit was irrelevant, and the status did in fact change. Both endpoints remain evidence-blocked. The source still contains an AI-produced 'extra' leaf, and the policy puts observed-but-AI evidence in quarantine, so it is not admitted as observed. An evidence-blocked status depends on evidence that has not been admitted and gives no observed-evidence assurance. The edited justified result therefore cannot be published as backed by observed evidence."
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
