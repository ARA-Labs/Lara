# TODOS

## Runtime

### Cache grounded adjacency for the M3 production evaluator

**What:** Build a production grounded evaluator that computes adjacency once
and evaluates accepted units without the Lean reference evaluator's repeated
nested edge scans.

**Why:** The proof-oriented `defendedB → step → iter → grounded` path is clear
and executable, but its repeated argument and edge scans are not the intended
runtime architecture for larger policies.

**Pros:** Reduces repeated edge work, gives M3 a deliberate runtime boundary,
and enables differential tests against the Lean reference semantics.

**Cons:** Adds cache invariants, a second evaluator implementation, and
equivalence testing that must remain synchronized with the frozen semantics.

**Context:** Issue #18 retains the Lean evaluator as the reference semantics,
documents its cost, and adds a representative default-heartbeat regression.
Start from `Compile.checkedAF`/the accepted-unit edge surface, build immutable
incoming and outgoing adjacency, and compare every resulting label and status
with `Grounded.grounded` on shared fixtures.

**Effort:** L
**Priority:** P2
**Depends on:** Issue #18 accepted-unit and compiled-edge interfaces; M3
production Haskell checker

## Reporting

### Compute full claim holes and incomplete-alternative diagnostics

**What:** Compute `holes(P,p)` from raw unit inputs and emit the
`incompleteAlternative` diagnostics defined by the language specification.

**Why:** Issue #18 computes exact complete support for result 7, but it does
not retain or aggregate rejected hole-bearing alternatives into a full
language-facing claim report.

**Pros:** Completes claim reporting, preserves unresolved-alternative
provenance, and prevents callers from mistaking `completeClaimFor` for full
claim construction.

**Cons:** Requires a raw reporting path alongside accepted arguments and a
precise link between rejected incomplete terms, root obligations, and accepted
claim status.

**Context:** `Lara.Check.Program.checkArguments` rejects an argument whose
inferred obligations are nonempty. Issue #18 therefore defines
`claimSupportFor` only over accepted complete nodes and wraps it as
`completeClaimFor` with no holes. Begin at the raw `Unit` boundary, retain
located incomplete alternatives without admitting them to the AF, and connect
the resulting diagnostic to spec §8's `holes(P,p)` definition.

**Effort:** M
**Priority:** P2
**Depends on:** Issue #18 `Unit` boundary; M3 raw-program and reporting design

## Completed
