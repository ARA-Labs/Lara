# TODOS

> M3 closed (issue #27, PR #28). M4 closed: the walking-skeleton spine
> (research-proposal.md §7) is satisfied — M4a compiler-on-worked-examples
> (#31, PR #33) and M4b untrusted elaborator + replay bundle (#32, PR #34)
> both landed; the strict-certificate `nd@1` worked example (#39) followed.
> Result 9 (backend replacement) is also complete: PR #41 mechanized the
> uniform-injective-relabel theorem and PR #43 added well-checkedness transport,
> making it non-vacuous by construction.
>
> Next milestone: **M5 — evaluation corpus** (research-proposal.md §7). Its
> implementation prerequisites are now both closed: verdict-carried replay
> identity (#36, the audit story) and duplicate-report groups (#38, the
> mutation-suite spine). The LLM/JSON producer (#30) follows when the
> deterministic→LLM flip begins.

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

## M5 prerequisites and language cleanup

### Verdict-carried replay identity (spec §2.1)

**What:** Extend the verdict codec (Haskell `Lara.Wire` + Lean `Lara.Driver`,
byte-identical) to print the frozen `replayId` tuple: `(lara-core@0.1, policy
id @ version, [backend@version*], {theory digests}, artifact digest)` — spec
§2.1's "Reports print the tuple verbatim."

**Why:** The obligation is frozen but unimplemented — no verdict path emits
the tuple (only the `Digest` newtype exists, `AST.hs:387`). M4b works around
it with the bundle manifest (checker-source revision as audit metadata);
that covers bundles, not arbitrary checker runs.

**Pros:** Every checker run carries its replay identity; verdict byte-diffing
catches trusted-input drift for free; fulfills a frozen spec obligation.

**Cons:** Coordinated change to the differential anchor plus every
golden/fixture — wide, shallow, carefully sequenced. Policy id@version and
artifact digest are presentation-layer metadata the `Unit` drops; the carrier
(report-side vs `Unit`) needs a design call.

**Context:** Becomes load-bearing when M5's audit/evaluation story needs
machine-checkable replay identity on arbitrary runs. Discovered in the M4b
plan-eng-review (2026-07-28).

**Issue:** #36.
**Effort:** M
**Priority:** P3
**Depends on:** nothing; natural fit with M5 planning


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

### Duplicate-report groups, spec §4.3 (issue #38)

Groups are carried end-to-end: surface `group g = [l, …]` and the policy
`duplicate-reports = quarantine|reject` setting (`Lara.Syntax`), the `DupGroup`
/ `GroupConflictMode` AST carrier and `unitGroups` / `unitGroupMode` on `Unit`
(`Lara.AST`), the wire `groups` section (`Lara.Wire`, byte-identical Lean
`Lara.Driver`), the elaborator lowering (`Lara.Elaborate`), and the
driver-boundary check (`Lara.Driver.runCheck` / Lean `runOnContents`): a
`≡`-consistent group admits normally; an inconsistent group quarantines its
members so the dependent claim routes to `gap`; an escalated conflict rejects
R9 (a boundary reject like R13). Lean metatheory (`Lara.Groups`, AxCheck-clean):
pairwise-`≡` ⟺ representative, quarantine membership, arg exclusion, the
leaf-rule connection, and the escalation characterization. Differential
fixtures `group-consistent-accept` / `group-conflict-quarantine` / `reject-r9`
pass both drivers byte-exact; R9 negative in `Lara.Negatives` and `CheckSpec`.

### Result-9 backend replacement (PRs #41 and #43)

`lean/Lara/Erase.lean` proves backend replacement under a uniform injective
assurance relabel. `lean/Lara/EraseTransport.lean` transports well-checkedness
under acceptance preservation and constructs the relabeled `CheckedProgram`,
so the theorem is non-vacuous by construction. Both developments are
`sorry`-free and AxCheck-clean within the standard axiom trio.

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
