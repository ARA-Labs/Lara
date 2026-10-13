# Claim-review task

You are reviewing one research claim recorded in a Lara inquiry document. Lara
is a checker for research claims. The document is an S-expression with these
parts:

- `process-input`: the recorded research process (events such as committing a
  plan, reading data, running an analysis and its result), the claims (`c0`, ...)
  and their submitted witnesses (`w0`, ...).
- `checked-source`: the argument source the claim is checked against. An
  argument can be `justified`, `defeated` or a `gap` under grounded semantics.
- `slots`: open observations. Each slot has several allowed choices; a
  *completion* picks one choice for every slot (and, where the process allows
  it, one admissible event history). Some completions may be rejected by the
  checker.
- `bindings`, `kind-metadata`, `admitted-assumptions`: how claims and witnesses
  bind to the source, and which capture assumptions are admitted.
- `assumption-catalog`: conditional facts a reviewer may assume, written as
  literals `slot-eq` (slot N takes choice C, written `sN=C`) and `slot-ne`
  (slot N does not take choice C, written `sN!=C`).
- `impact` documents compare a `before` and an `after` source for the same
  query; an edit has been made between them.
- `requests`: the questions the document asks the checker.

A public status is a pair such as `(published justified)` or
`(evidence-blocked defeated)`. `evidence-blocked` means the status is
conditional on evidence that has not been admitted as observed; it gives no
observed-evidence assurance.

## Your tool

You have one command, run from the current directory:

- `./lara-view show` prints the inquiry document.
- `./lara-view check` runs the real Lara checker on the document and prints its
  feedback.

No other command, file or network access is available. Do not guess at
information the document and the tool do not provide; when they do not
establish something, say so and answer accordingly.

## Your answer

Finish with exactly one fenced `json` block containing the fields the task
asks for, plus `"justification"`: at most 150 words explaining the decision
from what the document and tool show. Do not name the tool output format or
your tool in the justification; describe the facts. Your final message must
contain that block and nothing after it.

## What `./lara-view check` reports

The checker feedback is the **public status view** (the full public status of
every accepted completion, or of each query at the `before` and `after`
endpoints of an impact document), followed by the complete **inquiry
diagnostics** for every request:

- `status-body`: every completion row, including rejected rows and their exact
  rejection reason, then total/accepted/rejected counts and whether the status
  is stable across the whole family.
- `audit-body`: for every completion, whether the submitted fixed witness passes
  its audit under the stated profile, then whether it passes in every row.
- `stability-body`: `(stability-result OBSERVABLE total accepted rejected
  whole-outcome-stable accepted-only-stable)`.
- `assumptions-body`: the catalog, then every *minimal* set of catalog literals
  that leaves a nonempty, rejection-free family in which the target holds, with
  surviving completions and the countercompletion exposed by deleting each
  literal.
- `impact-body`: per query `(query-impact QUERY BEFORE AFTER changed locality)`.
  `locality` true is a certificate that the edit cannot affect the query's
  grounded status (its relevant ancestry and acceptance are unchanged); false
  means no such certificate exists, which does not by itself mean the status
  changed.

# Task P9-06

An edit was made to the source of query `(atom t)`. A reviewer proposes skipping re-review of the claim because its status is the same before and after. Decide whether the status changed and whether the edit can be certified as unable to affect the query's status, so that re-review may be skipped.

Answer fields:

- `status_changed`: true | false
- `certified_unaffected_by_edit`: true | false
- `rereview_may_be_skipped`: true | false
