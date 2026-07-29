# TODOS

> M3 closed (GitHub issue #27, PR #28). Remaining items below are post-M3
> backlog. M4 is tracked under umbrella issue #29 — split into M4a (#31,
> `plans/2026-07-27-m4a-compiler-worked-examples.md`) and M4b (#32,
> `plans/2026-07-27-m4b-walking-skeleton.md`).

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
runtime concern that does not touch semantics. Candidate M4 scope now that M3
closed issue #27.

**Effort:** L
**Priority:** P3
**Depends on:** M3 closeout (#27)

## Mechanization (split from M4a #31)

### Result-9 backend-replacement: eraseCert + stable argument-id representation

**What:** An argument-id / `eraseCert` compile-boundary representation for the
Lean `CheckedProgram`, then the result-9 (backend replacement) proof: node
bijection transport, graph isomorphism, and grounded-status invariance.

**Why:** `/plan-eng-review` (2026-07-27) split this out of M4a's Task A3. Result
12 (the parser round-trip) needs none of it; the machinery belongs to **result 9**
(`docs/spec.md:1153-1159`). The current `CheckedProgram` "cannot state the required
payload-varying node bijection: nodes are certificate-bearing `SupportTerm`s with
no stable argument id or erased skeleton."

**Pros:** Unblocks the only remaining unmechanized backend-independence result;
already flagged in `ara/evidence/status/mechanization_status.md` as the result-9
statement-model blocker.

**Cons:** A substantial Lean representation refactor; genuine proof risk.

**Context:** `eraseCert` behavioral definition at `docs/spec.md:882` (preserves
argument names, rule instances, conclusions, obligations, positions; replaces
payloads with a `certified` marker). No `eraseCert` exists in Haskell or Lean yet.

**Effort:** L
**Priority:** P3
**Depends on:** the M4a `Lara.AST` / presentation-AST freeze (#31); not blocked by
anything inside M4a.

### Print hole-lines in support terms

**What:** Make `printSupportTerm` preserve `open … as …` hole lines. It currently
drops `srHoles`, so a parsed open obligation does not survive the surface
round-trip.

**Context:** Low priority until an authored example needs `open`; recorded as an
explicit out-of-scope item in the strict-certificate implementation plan.

**Effort:** S
**Priority:** P3

### Theory-line groundness

**What:** Enforce the grammar's requirement that policy `theory` entries are
ground propositions, or revise the grammar to admit variables explicitly.

**Context:** `propP` accepts variable-looking identifiers in theory entries
(harmless in practice because `encodeND` flattens every entry to an atom).
Tighten the parser or update the grammar.

**Effort:** S
**Priority:** P3

## Completed

### Strict-certificate worked example (nd@1 frontend cert path)

S1 lands the full frontend certificate path (`.lara` → elaborate → verdict +
`.core.sexp`); the hypothesis-reuse boundary is recorded in
`examples/S1/strict-v1.policy.lara`.

### Cache grounded adjacency for the M3 production evaluator (PR #28)

Production grounded evaluator (`Lara.Runtime`) computes adjacency once and is
byte-identical to the un-cached `Lara.Compile.checkedAF` path, differential-
tested against `Grounded.grounded` with a 120-argument ≤5 s perf guard.

### Full claim holes and incomplete-alternative diagnostics (PR #28)

`Lara.Reporting` computes `holes(P,p)` from the raw `Unit` boundary and emits
the `incompleteAlternative` diagnostics defined by spec §8 / §10.1.
