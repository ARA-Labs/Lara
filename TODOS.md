# TODOS

> Tracked in GitHub issue #27 (M3 tracker: production Haskell checker and
> status engine). Plan: `plans/2026-07-26-m3-production-checker.md`.

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

## Performance

### Criterion-grade performance lab for the grounded evaluator

**What:** A proper benchmark suite (criterion) for the production grounded
evaluator with percentile reporting and regression curves.

**Why:** M3 ships a wall-clock smoke guard (absolute ceiling in CI, label
equality as the real assertion — plan-eng-review D10/D16). A real perf lab
becomes valuable when input sizes grow.

**Pros:** Regression curves instead of thresholds; catches gradual degradation
that a ceiling cannot.

**Cons:** New dependency and CI time; pointless at current corpus scale.

**Context:** Revisit when AF sizes exceed ~1k arguments or M4 incremental
checking lands. The M3 smoke guard (test-suite wall-clock assertion on the
ported #18 stress fixture plus a 100+ arg synthetic AF) is the interim guard.

**Effort:** M
**Priority:** P3
**Depends on:** M3 production evaluator; trigger: AF sizes >1k or M4 scope

## Runtime (M4 candidates)

### Production-runtime concerns beyond the frozen core

**What:** Incremental re-checking (re-evaluate only affected claims when a
unit changes), large-graph performance, and diagnostic UX beyond located
rejections.

**Why:** M3 deliberately optimizes for conformance of the frozen symbolic
core; "production" eventually means more than a conformant batch checker
(outside-voice point, plan-eng-review 2026-07-26).

**Pros:** Captured before M4 planning; prevents M3's conformance focus from
becoming the permanent definition of done.

**Cons:** Explicitly out of M3 scope; some items may require spec evolution
(lara-core version bump governance).

**Context:** The frozen spec governs semantics, but incremental checking is a
runtime concern that does not touch semantics. Candidate M4 scope once M3
closes issue #27.

**Effort:** L
**Priority:** P3
**Depends on:** M3 closeout (#27)

## Completed
