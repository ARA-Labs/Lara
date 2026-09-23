# External registration-receipt contract (documentation only)

_Status: frozen documentation contract, 2026-08-06, per the evidence-admission
scope decision (plan Task 6, reduced). This document defines a backend-neutral
seam for citing externally witnessed registrations. It adds no schema, no
validator, no Git backend, no network dependency, and no Haskell or Lean
code. Registration receipts are process metadata: they never enter `Gamma`,
never create an attack, and never change a grounded status or claim status._

Why anyone wants this: a registration receipt proves that specific content
existed, unchanged, at a specific time; for example, that a preregistered
analysis plan predates the results it governs. The disclaimers above mark
where receipts may *not* reach: `Gamma` is the evidence context the checker
reasons from, so a receipt can annotate provenance but can never itself
become evidence, mount an attack, or move a claim's status.

## 1. The minimal receipt

A registration receipt is a record issued by an external witness that fixed a
content digest at a time:

```text
registration-receipt:
  provider
  immutable-record-id
  registered-content-digest
  witness-issued-at
  witness-proof
```

The receipt says exactly one thing: the named provider witnessed
`registered-content-digest` as immutable at `witness-issued-at`, and
`witness-proof` lets an auditor verify that statement against the provider.
It says nothing about the registered content's truth, quality, or relevance.
LARA may cite the registered object later only through the ordinary
leaf-and-policy path; the receipt itself is never a leaf, a support term, or
an attack.

## 2. Temporal-priority labels

Exactly three labels, in decreasing strength:

- **`preregistered`** — the goal or analysis-plan digest is covered by a
  verified external immutable timestamp that predates the attempt.
- **`prior-in-checkpoint-history`** — the goal is an ancestor of the attempt
  in a content-addressed history (e.g. Git), but no external time witness
  was verified.
- **`post-hoc`** — the goal and attempt first appear together, or the goal
  follows the attempt.

Git ancestry may establish the second label only. Git author or committer
timestamps alone must never establish the first: a local Git log proves
checkpoint-relative order, not wall-clock priority, and rewriting local
history is cheap. OSF-style time-stamped, read-only registrations — a plan
posted before data collection or analysis — are the reference model for the
first label.

## 3. Build/no-build gate

No LARA event-log schema, receipt validator, or Git backend is built in this
paper cycle. A LARA-specific protocol package is reconsidered only if
evaluation identifies a workflow that existing registration services plus a
content-digest receipt cannot express — and such a package would require its
own threat model covering witness authenticity, key rotation, clock
semantics, history rewrite, and availability before any code is written.

## 4. Invariants

1. The documentation never equates local Git order with preregistration.
2. Registration receipts remain outside the calculus and the trusted core.
3. No goal or attempt event automatically changes a LARA claim status.
4. This contract adds no module, schema, or runtime dependency.

Related record: `docs/evidence-admission-decision.md`
records the gated evidence-admission layer this seam deliberately stays
outside of.
