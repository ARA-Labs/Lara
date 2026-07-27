# M3 Production Checker and Status Engine Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `executing-plans` to implement this plan task by task. Keep checkbox
> state current as each focused test, proof, and gate lands.

**Goal:** Build the M3 production Haskell compiler/checker and status engine,
replacing the proof-oriented Lean reference evaluator as the runtime target.
The Lean reference PL (`checkUnit → Unit.CheckedUnit`) is complete on `main`
(`f33e084`); M3 brings the production runtime online.

**Architecture:** Keep the frozen spec (`docs/spec.md`) as the contract and the
Lean executable semantics as the conformance anchor. Spike the S-expr wire
codec + Lean driver first (the real divergence surface), then build the
Haskell checker spine bottom-up per `docs/engineering-plan.md` §3 layers 3–8,
then add the two deferred M3 production surfaces: a cached-adjacency grounded
evaluator (differential-tested against `Grounded.grounded`) and full
`holes(P,p)` / `incompleteAlternative` reporting over the raw `Unit` boundary.

**Tech Stack:** Haskell/GHC, Cabal, QuickCheck, the existing
`src/Lara/{Prop,Strict}.hs` conformance anchors, the Lean executable semantics
in `lean/`, and the frozen spec.

**Tracker:** GitHub issue #27. Parent: #15 (closed M2 tracker). Predecessors:
#16/#17/#18 (PRs #21/#25/#26).

## Definition of Done

- The Haskell M3 checker spine (`Lara.Policy`, `Lara.SupportTerm`,
  `Lara.Attack`, `Lara.Compile`, `Lara.Check`, `Lara.Grounded`,
  `Lara.Diagnostics`) exists and passes property/golden tests per
  `docs/engineering-plan.md` §5.
- The S-expr wire codec has golden vectors, round-trip properties, and a
  malformed-input rejection matrix; the Lean driver is a thin
  decode→call→encode shim over the theorem-bearing defs.
- `lara check <file.sexp>` runs the full pipeline and prints S-expr verdicts.
- The production grounded evaluator computes adjacency once and agrees with
  the naive Haskell evaluator and with `Grounded.grounded` on shared fixtures
  and on random-AF QuickCheck properties.
- The raw-unit reporting path emits `holes(P,p)` and `incompleteAlternative`
  diagnostics per spec §8.
- Differential tests between the Haskell runtime and the Lean executable
  semantics pass on the ported conformance fixtures.
- Docs/spec/checklist/ARA ledger updated.

## Global Constraints

- The frozen spec and the Lean executable semantics are the conformance
  anchors; the Haskell runtime is production code, not a second semantics.
- The compiler core stays symbolic (CLAUDE.md): closed sum types and
  namespace-specific identifiers; raw strings only at the decode boundary.
- Core types stay in `src/Lara/AST.hs` (review D2). Layer modules hold
  judgments and algorithms only; they do not redefine AST types.
- The Lean `Grounded` evaluator remains the proof reference. The Haskell
  fixpoint algorithm is defined once in `Lara.Grounded`, parameterized over
  an edge-lookup interface (record of functions); `Lara.Runtime` supplies
  the cached-adjacency backend and is the production default (review D5).
- AF edges stay unlabelled: attack reasons are never retained in the Dung AF
  (prior learning `lara_unlabelled_edge_completeness`, 10/10).
- Executable results retain located diagnostics and cache data in the result
  type, never in a side channel (prior learning
  `lean_runtime_cache_not_theorem_output`, 10/10).
- `claimSupportFor`/`completeClaimFor` remain complete-only projections. Full
  `holes(P,p)` lives on the raw-unit reporting path, never admitted to the AF.
- Claim-status aggregation lives in `Lara.Grounded` over a
  `Claim { support, holes }` record (mirroring Lean `statusC`);
  `Lara.Reporting` computes the holes that populate it (review D7).
- Fixture arbitration: the Lean executable semantics is the oracle. Any
  fixture disagreement is a bug (in Haskell or in the fixture annotation),
  fixed with a recorded note; expected values are never silently
  re-annotated (review D16).
- Do not add Path A, preferred/stable/complete semantics, NL claim/edge
  extraction, `Backend.uses`/`certDeps`, certificate-erased identity, or
  `Lara.Json`/`Lara.Syntax` codec round-trip. The S-expr wire codec is the
  differential anchor (exploration-tree N11), not a JSON front end.

## Module Boundaries

```text
Lara.Prop / Lara.Strict          (carve-outs 1–2 — done)
        |
        v
Lara.Policy ---> Lara.SupportTerm ---> Lara.Attack
        |              |                    |
        v              v                    v
        +--------> Lara.Compile ----> Lara.Grounded ----+ (algorithm,
        |              |                    |           |  parameterized
        |              v                    v           |  over edges)
        |        Lara.Check (six-stage      |           v
        |          checkUnit pipeline)  Lara.Runtime (cached adjacency,
        |              |                    |            production default)
        v              v                    v
Lara.Diagnostics <-----+                    |
        |                                   |
        v                                   v
Lara.Reporting (holes / incompleteAlternative; feeds Claim.holes)

Wire lane (spiked first, independent of the spine):
Lara.Wire (S-expr codec over Lara.Strict.SExpr) <---> lean Driver.lean
        |
        v
app/Main.hs = `lara check` CLI (S-expr verdicts on stdout)
```

Layers 1–2 (`Lara.Prop`, `Lara.Strict` + ND adapter) already exist and are
unchanged. `Lara.Runtime` and `Lara.Reporting` are the two M3 production
surfaces deferred from #18. All core types come from `Lara.AST`;
`Lara.Examples` / `Lara.Negatives` are the golden/mutation fixture base.

---

### Task 0: T0 — Wire Codec, Lean Driver, CLI Skeleton (spike first)

**Files:**

- Add: `src/Lara/Wire.hs` — textual read/write over `Lara.Strict.SExpr` for
  core programs and verdicts (the documented N11 differential anchor).
- Add: `lean/Driver.lean` (or `lean/Lara/Driver.lean`) — `def main : IO Unit`,
  a thin decode→call→encode shim calling exactly the theorem-bearing defs
  (`checkUnit`, `grounded`, `statusC`, `edgeB`).
- Modify: `app/Main.hs` — replace the experimental LP-kernel demo with
  `lara check <file.sexp>`.
- Modify: `test/` — codec ground-truth tests.

**Interfaces:**

- Consumes: `Lara.Strict.SExpr`, `Lara.AST`, Lean executable checkers.
- Produces: a shared wire format, both drivers printing byte-identical
  verdict S-expressions.

- [ ] **Step 1: S-expr codec** for programs, units, and verdicts.
- [ ] **Step 2: Codec ground truth** (review D11) — hand-verified golden
  vectors, round-trip property (parse ∘ print = id on ASTs), malformed-input
  rejection matrix; mirror the `StrictSpec` atom-key pattern.
- [ ] **Step 3: Lean driver** — thin shim; no logic beyond decode/call/encode.
- [ ] **Step 4: CLI skeleton** — contract (review D16): stdout = S-expr
  verdicts (same codec, explicit coupling); exit 0 = accept, 1 = rejection,
  2 = codec/usage error.

---

### Task 1: Haskell M3 Checker Spine (Layers 3–8)

**Files:** (chosen per `docs/engineering-plan.md` §3)

- Add: `src/Lara/Policy.hs`
- Add: `src/Lara/SupportTerm.hs`
- Add: `src/Lara/Attack.hs`
- Add: `src/Lara/Compile.hs`
- Add: `src/Lara/Check.hs` (review D3)
- Add: `src/Lara/Grounded.hs`
- Add: `src/Lara/Diagnostics.hs`
- Modify: `test/` (property + golden tests; reuse `Lara.Examples` /
  `Lara.Negatives`)

**Interfaces:**

- Consumes: frozen spec §4/§6/§7/§8, `Lara.Prop`, `Lara.Strict`, `Lara.AST`
  types (review D2 — no parallel type universe).
- Produces: executable policy/support/attack/compile/check/grounded/
  diagnostics layers, property + golden tested.

- [ ] **Step 1: `Lara.Policy`** — rule schemas, `contrary`, `exception`,
  admission table, §8.1 strict-reachable validator (early M3 target).
- [ ] **Step 2: `Lara.SupportTerm`** — `⊢ w : supports(p) ▷ O`, `leaves`,
  `certDeps` over the AST `SupportTerm`.
- [ ] **Step 3: `Lara.Attack`** — positional `w@π`, rebut/undercut/undermine
  typing; strict unattackability as a property test.
- [ ] **Step 4: `Lara.Compile`** — `compile(P) = AF`, subargument closure;
  edges unlabelled.
- [ ] **Step 5: `Lara.Check`** — the six-stage `checkUnit` pipeline in the
  Lean order: duplicate rule IDs → R12 policy-wf → duplicate arguments →
  support → typed attacks → missing conflict (attack completeness, the
  result-7 premise). Returns a detailed result retaining located rejections.
- [ ] **Step 6: `Lara.Grounded`** — least-fixpoint labelling + four-state
  aggregation, defined once and parameterized over an edge-lookup interface;
  status over `Claim { support, holes }`.
- [ ] **Step 7: `Lara.Diagnostics`** — located rejection per rejection class.
- [ ] **Step 8: Property + golden tests** — per `docs/engineering-plan.md`
  §5, building on `Lara.Examples` (accepted) and `Lara.Negatives` (8
  rejection classes).

---

### Task 2: T9 — Cached Grounded Adjacency for the Production Evaluator

**Files:**

- Add: `src/Lara/Runtime.hs`
- Modify: `test/` (equivalence + differential tests)

**Interfaces:**

- Consumes: the Haskell `Lara.Compile` edge surface and the parameterized
  `Lara.Grounded` algorithm.
- Produces: the cached-adjacency backend — the production default.

- [ ] **Step 1: Build immutable incoming/outgoing adjacency** from the
  accepted-unit edge surface (`Data.Map`/`Data.IntMap`; no new deps).
  Compute adjacency once; do not rescan edges per iteration.
- [ ] **Step 2: Wire the cached backend** into the parameterized
  `Lara.Grounded` fixpoint (no second copy of the algorithm, review D5).
- [ ] **Step 3: Random-AF equivalence property** (review D12) — QuickCheck
  generator over arbitrary AFs (cycles, self-loops, disconnected
  components); cached labels ≡ naive labels for every argument.
- [ ] **Step 4: Differential-test every label and status** against
  `Grounded.grounded` on shared fixtures via the Task 0 wire.
- [ ] **Step 5: Perf guard** (review D10/D16) — port the #18 stress fixture
  plus a 100+ arg synthetic AF to the wire; absolute wall-clock ceiling in
  CI as a smoke guard; label equality is the real assertion. No criterion.

---

### Task 3: T10 — Full Claim Holes and Incomplete-Alternative Diagnostics

**Files:**

- Add: `src/Lara/Reporting.hs`
- Modify: `test/` (golden cases)

**Interfaces:**

- Consumes: the raw `Unit` boundary, the Haskell `Lara.Check` pipeline
  (review D3 — replaces the plan's original Lean-only
  `Lara.Check.Program.checkArguments` reference), spec §8's `holes(P,p)`.
- Produces: full claim holes and `incompleteAlternative` diagnostics;
  populates `Claim.holes` for `Lara.Grounded` status aggregation.

- [ ] **Step 1: Retain located incomplete alternatives** at the raw `Unit`
  boundary without admitting them to the AF.
- [ ] **Step 2: Compute `holes(P,p)`** from raw unit inputs, linking rejected
  incomplete terms to root obligations and accepted claim status.
- [ ] **Step 3: Emit `incompleteAlternative` diagnostics** per spec §8 —
  holes never suppress a complete `in` alternative; status never hides holes.
- [ ] **Step 4: Golden cases** — empty support, unresolved alternatives, and
  a complete winning alternative with separate hole diagnostics.
- [ ] **Step 5: Prevent `completeClaimFor` misuse** — the complete-only
  projection and the full reporting path are distinct and never conflated.

---

### Task 4: Differential Tests and Closeout

**Files:**

- Modify: `test/` (differential harness)
- Modify: `docs/spec.md`, `docs/m1-freeze-checklist.md`,
  `docs/engineering-plan.md`, `ara/` ledger

- [ ] **Step 1: Fixture corpus** (review D8) — serialize the Lean
  conformance fixtures (`Examples/PolicyAcceptance`,
  `Examples/GroundedConsistency`, `Examples/AttackCompleteness` incl. the
  stress fixture) plus `Lara.Examples` / `Lara.Negatives` into the wire
  format. Arbitration per Global Constraints.
- [ ] **Step 2: Differential harness** — run every serialized fixture
  through both drivers; byte-exact verdict agreement.
- [ ] **Step 3: Mutation suite** (review D9) — enumerate R1–R14 explicitly:
  map each class to an existing `Negative` or author a new one; every class
  gets ≥1 rejected golden + ≥1 mutation.
- [ ] **Step 4: Docs/ARA ledger** — record build/test commands and pass
  status; update the checklist and mechanization plan.
- [ ] **Step 5: Commit** — close issue #27.

## NOT in scope

- Path A, preferred/stable/complete semantics, NL extraction,
  `Backend.uses`/`certDeps`, certificate-erased identity — frozen out by the
  spec and prior milestone decisions.
- `Lara.Json` / `Lara.Syntax` codec round-trip (r12) — later boundary layer;
  the S-expr wire is the differential anchor, not a user front end.
- criterion perf lab — deferred to TODOS.md (trigger: AF >1k args or M4).
- Incremental re-checking, large-graph work, diagnostic UX — M4 candidates
  in TODOS.md.
- Haskell module restructuring around runtime concerns — rejected (review
  D14); the 1:1 Lean mirror is the audit backbone.

## What already exists (and how the plan reuses it)

- `src/Lara/AST.hs` — all core types; reused as-is (no redefinition).
- `src/Lara/Examples.hs`, `src/Lara/Negatives.hs` — golden/mutation fixture
  base for Tasks 1/4.
- `src/Lara/Strict.hs` `SExpr` — wire anchor for Task 0; ND atom-key codec
  in `Lara.Strict.ND` is the golden-vector test pattern to mirror.
- `lean/Lara/Check/*` — the six-stage pipeline shape ported by `Lara.Check`.
- `lean/Lara/Examples/*` — conformance fixtures ported to the wire in Task 4,
  including the #18 default-heartbeat stress fixture.
- `.github/workflows/ci.yml` — runs `cabal build + test` on PRs; new modules
  are covered automatically once added to `lara.cabal`.

## Failure modes

| Codepath | Realistic failure | Test? | Handling? | User sees |
|---|---|---|---|---|
| S-expr codec | malformed hand-edited fixture | malformed matrix (R14) | located parse error | exit 2 + message |
| Lean driver | heartbeat blowup on big fixture | #18 default-heartbeat guard | fixture size discipline | Lean error |
| Cached adjacency | desync → wrong labels | random-AF prop + differential | two independent oracles | not silent |
| `Lara.Check` stages | wrong stage order → wrong R-class | R1–R14 golden + mutation | closed error sums | located diagnostic |
| Status aggregation | holes not fed → wrong gap/justified | Task 3 golden cases | single owner (Grounded) | correct status |
| CLI | missing file / bad args | CLI golden cases | usage error | exit 2 + usage |
| Fixpoint | non-termination | bound property (≤ \|args\| iters) | same bound as Lean proof | n/a |

Critical gaps (no test AND no handling AND silent): **0**.

## Parallelization strategy

| Step | Modules touched | Depends on |
|------|----------------|------------|
| T0 wire/driver/CLI | `Lara.Wire`, `app/`, `lean/Driver.lean` | — |
| T1 spine | `src/Lara/{Policy,SupportTerm,Attack,Compile,Check,Grounded,Diagnostics}` | — (soft: T0 wire for later steps) |
| T2 runtime | `Lara.Runtime` | T1 (Grounded/Compile) |
| T3 reporting | `Lara.Reporting` | T1 (Check) |
| T4 closeout | `test/`, `docs/` | T0–T3 |

Lane A: T0 (wire lane — independent). Lane B: T1 → T2 / T3 (spine, then its
two dependents in parallel). Lane C: T4.
Execution: launch A and B in parallel worktrees; merge both; then T2+T3 in
parallel; then C.
Conflict flags: Lanes A and B both touch `lara.cabal` and `test/` — land T0
first (small diff) or coordinate the cabal exposed-modules list.

## Plan Review

Completed 2026-07-26 (`/plan-eng-review`, FULL_REVIEW, 14 issues found, all
resolved; outside voice via Claude subagent — Codex CLI usage-limited).
Decisions D1–D18 folded inline above. Prior review artifacts:
`~/.gstack/projects/lara/yfhe-main-eng-review-test-plan-20260726-214949.md`.

## Implementation Tasks

- [ ] **T0 (P1, human: ~2–3d / CC: ~4–8h)** — wire codec + ground-truth
  tests + Lean driver + `lara check` CLI skeleton (spike first)
- [ ] **T1 (P1, human: ~4–6d / CC: ~1–2d)** — Haskell M3 checker spine
  (layers 3–8 incl. `Lara.Check`; types from `Lara.AST`)
- [ ] **T2 (P2, human: ~1–2w / CC: ~1–2d)** — T9 cached grounded adjacency
  (parameterized algorithm, random-AF prop, perf guard)
- [ ] **T3 (P2, human: ~3–5d / CC: ~4–8h)** — T10 holes /
  incompleteAlternative reporting
- [ ] **T4 (P2, human: ~2–3d / CC: ~4–8h)** — differential harness +
  R1–R14 mutation enumeration + closeout

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | `/codex review` | Independent 2nd opinion | 1 | issues_found (via claude subagent) | 12 findings, 6 accepted, 2 tensions rejected, 4 answered by existing structure |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | clean (PLAN) | 14 issues, 0 critical gaps, 0 unresolved |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | — |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | — |

- **CROSS-MODEL:** Outside voice (Claude subagent; Codex CLI usage-limited) raised 12 points. Accepted: codec ground-truth tests, random-AF equivalence property, codec/driver-first sequencing, perf-threshold policy, CLI contract, fixture arbitration. Tensions resolved for the review: 1:1 module mirroring kept (audit backbone), differential testing kept in DoD (conformance anchor). Answered by existing structure: holes semantics (spec §8), Lean driver soundness (thin shim over theorem-bearing defs), divergence governance (frozen-spec version bump), acceptance-path coverage (goldens + differential).
- **VERDICT:** ENG CLEARED — ready to implement.

NO UNRESOLVED DECISIONS
