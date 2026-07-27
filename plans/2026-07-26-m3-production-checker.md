# M3 Production Checker and Status Engine Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `executing-plans` to implement this plan task by task. Keep checkbox
> state current as each focused test, proof, and gate lands.

**Goal:** Build the M3 production Haskell compiler/checker and status engine,
replacing the proof-oriented Lean reference evaluator as the runtime target.
The Lean reference PL (`checkUnit → Unit.CheckedUnit`) is complete on `main`
(`f33e084`); M3 brings the production runtime online.

**Architecture:** Keep the frozen spec (`docs/spec.md`) as the contract and the
Lean executable semantics as the conformance anchor. Build the Haskell checker
spine bottom-up per `docs/engineering-plan.md` §3 layers 3–8, then add the two
deferred M3 production surfaces: a cached-adjacency grounded evaluator
(differential-tested against `Grounded.grounded`) and full `holes(P,p)` /
`incompleteAlternative` reporting over the raw `Unit` boundary.

**Tech Stack:** Haskell/GHC, Cabal, QuickCheck, the existing
`src/Lara/{Prop,Strict}.hs` conformance anchors, the Lean executable semantics
in `lean/`, and the frozen spec.

**Tracker:** GitHub issue #27. Parent: #15 (closed M2 tracker). Predecessors:
#16/#17/#18 (PRs #21/#25/#26).

## Definition of Done

- The Haskell M3 checker spine (`Lara.Policy`, `Lara.SupportTerm`,
  `Lara.Attack`, `Lara.Compile`, `Lara.Grounded`, `Lara.Diagnostics`) exists
  and passes property/golden tests per `docs/engineering-plan.md` §5.
- The production grounded evaluator computes adjacency once and agrees with
  `Grounded.grounded` on shared fixtures.
- The raw-unit reporting path emits `holes(P,p)` and `incompleteAlternative`
  diagnostics per spec §8.
- Differential tests between the Haskell runtime and the Lean executable
  semantics pass.
- Docs/spec/checklist/ARA ledger updated.

## Global Constraints

- The frozen spec and the Lean executable semantics are the conformance
  anchors; the Haskell runtime is production code, not a second semantics.
- The compiler core stays symbolic (CLAUDE.md): closed sum types and
  namespace-specific identifiers; raw strings only at the decode boundary.
- The Lean `Grounded` evaluator remains the proof reference; the production
  evaluator is a separate, differentially tested implementation.
- `claimSupportFor`/`completeClaimFor` remain complete-only projections. Full
  `holes(P,p)` lives on the raw-unit reporting path, never admitted to the AF.
- Do not add Path A, preferred/stable/complete semantics, NL claim/edge
  extraction, `Backend.uses`/`certDeps`, certificate-erased identity, or
  `Lara.Json`/`Lara.Syntax` codec round-trip.

## Module Boundaries

```text
Lara.Prop / Lara.Strict          (carve-outs 1–2 — done)
        |
        v
Lara.Policy ---> Lara.SupportTerm ---> Lara.Attack
        |              |                    |
        v              v                    v
        +--------> Lara.Compile ----> Lara.Grounded
                          |               |
                          v               v
                    Lara.Diagnostics   Lara.Runtime (cached adjacency)
                          |
                          v
                    Lara.Reporting (holes / incompleteAlternative)
```

Layers 1–2 (`Lara.Prop`, `Lara.Strict` + ND adapter) already exist and are
unchanged. `Lara.Runtime` and `Lara.Reporting` are the two M3 production
surfaces deferred from #18.

---

### Task 1: Haskell M3 Checker Spine (Layers 3–8)

**Files:** (chosen per `docs/engineering-plan.md` §3)

- Add: `src/Lara/Policy.hs`
- Add: `src/Lara/SupportTerm.hs`
- Add: `src/Lara/Attack.hs`
- Add: `src/Lara/Compile.hs`
- Add: `src/Lara/Grounded.hs`
- Add: `src/Lara/Diagnostics.hs`
- Modify: `test/` (property + golden tests)

**Interfaces:**

- Consumes: frozen spec §4/§6/§7/§8, `Lara.Prop`, `Lara.Strict`
- Produces: executable policy/support/attack/compile/grounded/diagnostics
  layers, property + golden tested

- [ ] **Step 1: `Lara.Policy`** — rule schemas, `contrary`, `exception`,
  admission table, §8.1 strict-reachable validator (early M3 target).
- [ ] **Step 2: `Lara.SupportTerm`** — `w` AST, `⊢ w : supports(p) ▷ O`,
  `leaves`, `certDeps`.
- [ ] **Step 3: `Lara.Attack`** — positional `w@π`, rebut/undercut/undermine
  typing.
- [ ] **Step 4: `Lara.Compile`** — `compile(P) = AF`, subargument closure.
- [ ] **Step 5: `Lara.Grounded`** — least-fixpoint labelling + four-state
  aggregation.
- [ ] **Step 6: `Lara.Diagnostics`** — located rejection per rejection class.
- [ ] **Step 7: Property + golden tests** — per `docs/engineering-plan.md` §5.

---

### Task 2: T9 — Cached Grounded Adjacency for the Production Evaluator

**Files:** (chosen per M3 implementation)

- Add: `src/Lara/Runtime.hs` (or equivalent)
- Modify: `test/` (differential tests)

**Interfaces:**

- Consumes: `Compile.checkedAF`/the accepted-unit edge surface (Lean) and the
  Haskell `Lara.Compile`/`Lara.Grounded` layers.
- Produces: a production grounded evaluator that computes adjacency once.

- [ ] **Step 1: Build immutable incoming/outgoing adjacency** from the
  accepted-unit edge surface. Compute adjacency once; do not rescan edges per
  iteration.
- [ ] **Step 2: Implement the production grounded evaluator** over the cached
  adjacency, mirroring the reference `defendedB → step → iter → grounded`
  logic.
- [ ] **Step 3: Differential-test every resulting label and status** against
  `Grounded.grounded` on shared fixtures. Compare all four statuses and all
  labels.
- [ ] **Step 4: Pin cache invariants** — the adjacency is immutable, indexed by
  argument, and provably synchronized with the frozen semantics.
- [ ] **Step 5: Benchmark regression** — representative input under default
  heartbeats; the production evaluator must not regress on the #18 stress
  fixture.

---

### Task 3: T10 — Full Claim Holes and Incomplete-Alternative Diagnostics

**Files:** (chosen per M3 implementation)

- Add: `src/Lara/Reporting.hs` (or equivalent)
- Modify: `test/` (golden cases)

**Interfaces:**

- Consumes: raw `Unit` boundary, `Lara.Check.Program.checkArguments`, spec §8's
  `holes(P,p)` definition.
- Produces: full claim holes and `incompleteAlternative` diagnostics.

- [ ] **Step 1: Retain located incomplete alternatives** at the raw `Unit`
  boundary without admitting them to the AF.
- [ ] **Step 2: Compute `holes(P,p)`** from raw unit inputs, linking rejected
  incomplete terms to root obligations and accepted claim status.
- [ ] **Step 3: Emit `incompleteAlternative` diagnostics** per spec §8.
- [ ] **Step 4: Golden cases** — empty support, unresolved alternatives, and a
  complete winning alternative with separate hole diagnostics.
- [ ] **Step 5: Prevent `completeClaimFor` misuse** — the complete-only
  projection and the full reporting path are distinct and never conflated.

---

### Task 4: Differential Tests and Closeout

**Files:**

- Modify: `test/` (differential harness)
- Modify: `docs/spec.md`, `docs/m1-freeze-checklist.md`,
  `docs/engineering-plan.md`, `ara/` ledger

- [ ] **Step 1: Differential harness** — run the same serialized core programs
  and verdicts through both the Haskell runtime and the Lean executable
  semantics.
- [ ] **Step 2: Mutation suite** — per `docs/engineering-plan.md` §5.
- [ ] **Step 3: Docs/ARA ledger** — record build/test commands and pass status;
  update the checklist and mechanismation plan.
- [ ] **Step 4: Commit** — close issue #27.

## Plan Review

TODO: `/plan-eng-review` + `/codex review` before implementation.

## Implementation Tasks

- [ ] **T1 (P1, human: ~3–5d / CC: ~1–2d)** — Haskell M3 checker spine
  (layers 3–8)
- [ ] **T2 (P2, human: ~1–2w / CC: ~1–2d)** — T9 cached grounded adjacency
- [ ] **T3 (P2, human: ~3–5d / CC: ~4–8h)** — T10 holes / incompleteAlternative
  reporting
- [ ] **T4 (P2, human: ~1–2d / CC: ~2–4h)** — differential tests + closeout
