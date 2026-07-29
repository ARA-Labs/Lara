# M4a Implementation Plan — compiler end to end on the worked-examples suite

> **For agentic workers:** REQUIRED SUB-SKILL: Use `executing-plans` to
> implement this plan task by task. Keep checkbox state current as each focused
> test, proof, and gate lands.

> **Revised 2026-07-27 by `/plan-eng-review`.** Eleven decisions locked (see the
> `## GSTACK REVIEW REPORT` at the end). The load-bearing change: `.lara` parses
> to the **presentation AST (`Program` + `Policy`)** and lowers to `Unit` through
> a **new, named elaborator** — not "directly to `Unit`" as the first draft (and
> D1) stated. This reopens D1, which is shared with #32; see the report.

**Tracker:** GitHub #31 (child of #29, the M4 umbrella). Sibling: #32 (M4b,
`plans/2026-07-27-m4b-walking-skeleton.md`). Predecessor: PR #28.

**Milestone spine:** `plans/research-proposal.md` §7, M4. M4 splits into two
tracks because its two clauses have different prerequisites; this plan is the
first:

- **M4a (this plan) — the compiler works end to end on the worked-examples
  suite.** The `Lara.Syntax` frontend + a `Program`→`Unit` elaborator + the M3
  checker + golden verdicts on tiny, self-authored examples that *exhibit the
  calculus's discriminating power*. Compiler-style: start with small self-created
  cases that carry the pathology, not an external corpus. This also produces the
  paper's **motivating examples** and discharges `docs/worked-examples-plan.md`
  §4 (each `.lara` → `.core.sexp` + `expected.json`).
- **M4b (#32) — the walking skeleton with no hand-authored certificate.** The
  *untrusted* elaborator producing a certificate from a real/structured source +
  the replay bundle. Deferred to its own track. (Distinct from M4a's *trusted*
  surface elaborator below — outside-voice #2.)

**Why M4a is its own track.** A tiny `.lara` file *is* a hand-authored
certificate — its typed attacks (`rebut d3 a1`), support terms, and CQ discharges
are the certificate content in surface form. So the worked-examples suite
satisfies the **compiler + type checker** (M4a) but not the "no hand-authored
certificate" clause, which specifically needs a *machine producer* (M4b).
Award-winning papers (PaperBench) are the wrong source: a well-executed paper
never defeats its own headline claim, so it never exhibits
`defeated`/`contested`/`gap`.

**Architecture.** `.lara`, `.sexp`, and (later) JSON are **concrete syntaxes
over one symbolic IR**, but they land at two layers: the **presentation AST**
(`Program`/`Policy`/`Claim`/`Leaf`, which retain artifact identity, claim NL +
bindings, leaf kind/provenance/refs, backend selection) and the **checker anchor**
(`Unit`, which deliberately drops all of that — `Lara.AST` lines 438-440). The
frontend is two maps, not one:

```text
  worked-example .lara ──parse (Lara.Syntax, TCB)──► Program + Policy
         │                                                │
         │ authored to exhibit                            │ elaborate (TCB): Program+Policy
         │ defeated/contested/gap/illegal-attack          │ +TheoryRegistry+Σ ─► Unit
         │                                                 ▼
         │                                        Unit ──encodeUnit──► canonical .core.sexp
         │                                                 │            (replay + Haskell↔Lean anchor)
         │                                                 ▼
         └─ goldens: .core.sexp (both engines)     { Haskell runUnit, Lean driver }  (byte-identical)
            + expected.json (class differential;      │
              located diag Haskell-only)              ▼
                                                   verdict
  result 12 round-trip:  parse ∘ print == id  over (Program, Policy)   [label-preserving printer]
```

`Lara.Syntax` and the elaborator are **inside** the TCB (decode boundary, spec
**§1.1** row 1 — the TCB table; §10.1 is the rejection-class table). Haskell is
solely trusted for `.lara → .core.sexp`; the Lean driver only ever consumes the
derived `.core.sexp`, never `.lara`. The frozen spec (`docs/spec.md`) stays the
contract; the Lean executable semantics stays the verdict oracle.

**Tech Stack:** Haskell/GHC + Cabal + QuickCheck for `Lara.Syntax`; the existing
`Lara.Wire` S-expr codec (`encodeUnit`/`decodeUnit`) as the machine boundary;
the `examples/*.lara` + planned E-series as the golden presentation oracles.
Parser dependency and any JSON dependency for `expected.json` are decided in
Task A0.5 and registered in `lara.cabal` (library exposed-modules +
test other-modules) as part of A1.

## Resolved decisions (shared with #32)

- **D1 (REVISED by eng review) — producer→checker surface.** `Lara.Syntax` parses
  `.lara` to the **presentation AST** `Program` + `Policy`, and a **new named
  elaborator** `Program + Policy + TheoryRegistry + Σ → Either Err Unit` lowers
  to the checker anchor; the canonical `.core.sexp` is *derived* via
  `Lara.Wire.encodeUnit` from the elaborated `Unit`. (The prior "parses directly
  to `Unit`" is rejected: `Unit` cannot hold the surface's metadata, the
  elaboration must happen regardless, and result 12 must be stated over the
  presentation AST.) JSON is the later LLM-producer surface (#30).
  **Ripple:** #32 inherits D1 — its plan must be updated to the two-layer target.
- **D2 — fixtures.** The self-authored **worked-examples suite**
  (`docs/worked-examples-plan.md` E1–E3 / R1–R3 + existing `examples/A`,`B`,
  `empirical-v1.policy.lara`). **PaperBench (`corpus/ara-paperbench`) is dropped
  from the M4 critical path**, demoted to M5 evaluation.
- **D3 — elaborator determinism.** M4a's *trusted surface* elaborator
  (`Program+Policy → Unit`) must be deterministic and total-on-well-formed-input;
  M4b's *untrusted* certificate producer determinism is separate and lives in #32.

### Open cross-plan decisions (D1 ripple — owned by #32/#30, NOT resolved here)

Revising D1 (eng-review decision #2) reopened the producer→checker contract for
producers other than `.lara`. These are **not M4a's to decide**; M4a only keeps
them two-way doors (the elaborator is pure and decoupled — see A1). The M4b plan
(`plans/2026-07-27-m4b-walking-skeleton.md`, not yet written) should open against
the revised D1 and resolve TBD-1/TBD-2 explicitly before it builds anything.

- **TBD-1 — which layer M4b's *untrusted* producer targets.** Presentation
  (`Program`/`Policy`, reusing M4a's trusted elaborator) vs checker-level
  (`Unit`/`.core.sexp` directly, treating the certificate as the checked
  artifact). Lean: presentation, for a single audited lowering — but M4b's call.
- **TBD-2 — one elaborator or two.** Whether M4b's untrusted producer emits a
  `Program` and hands off to M4a's *trusted* `Program→Unit` elaborator (so the
  untrusted code never touches `Unit` directly), or runs a separate path. The word
  "elaborator" now names two distinct things (trusted surface vs untrusted
  producer); #32 must disambiguate.
- **TBD-3 — `TheoryRegistry`/`Σ` provenance + replay pinning.** M4a-facing half is
  settled: closed `nd@1` registry for v0.1. Open: how the M4b replay bundle pins
  exactly which registry/signature was used.
- **TBD-4 — JSON surface (#30) layer.** Revised D1 implies JSON also lands at
  `Program`/`Policy`; but LLM-produced JSON is closer to the machine-producer
  case. Deferred to #30 planning; keep consistent with TBD-1's resolution.

## Global Constraints

- **Keep the core symbolic (CLAUDE.md).** `Lara.Syntax` produces the closed
  `Program`/`Policy` sum types and newtyped identifiers; raw strings live only at
  the parse boundary. The concrete `.lara` spelling of every keyword/tag/mode has
  a single `toString`/`parse` table, never scattered literals.
- **Two layers, one derivation path.** `Lara.Syntax` parses `.lara` to
  `Program`/`Policy`; the elaborator lowers to `Unit`; the canonical `.core.sexp`
  is *derived* from the `Unit`, never a parallel parse route.
- **The Lean executable semantics is the verdict oracle.** Any disagreement is a
  bug fixed with a recorded note; expected values are never silently
  re-annotated (M3 review D16).
- **Do not reopen the frozen M3 verdict format.** Gap-holes and located rejection
  diagnostics stay in the Haskell result types (`Lara.Reporting`,
  `Lara.Check.ProgramError`); goldens that need them are Haskell-only, outside the
  byte-differential (see A2).

---

## Task A0: scope lock + freeze the A/B golden set

**Files:**
- Add: `docs/m4a-checklist.md` freeze note (mirroring `docs/m1-freeze-checklist.md`
  and `docs/m3-closeout-notes.md` — corrected filenames).
- Confirm the E-series design in `docs/worked-examples-plan.md` §1 coverage
  matrix; identify which examples already exist (`examples/A`,`B`,
  `empirical-v1.policy.lara`) vs which E1–E3/R1–R3 files must be authored.

**Work:**
- Freeze `examples/A` and `examples/B` expected verdicts from their inline
  hand-computed oracles NOW (they are the only examples with oracles today):
  four-state claim status + per-argument grounded label.
- **E1–E3/R1–R3 verdicts cannot be oracle-frozen here** — the Lean oracle
  consumes `.core.sexp`, which does not exist until the parser + elaborator (A1)
  produce it (outside-voice #9). A0 records the *intended* verdict for each; the
  oracle freeze happens in A1 once E1 (the vertical slice) can be elaborated.

**Gate:** the A/B golden set and the coverage matrix are committed and reviewed
before frontend code lands.

## Task A0.5: freeze the `.lara` grammar + reconcile A/B (NEW — gates A1)

**Why (outside-voice #5/#6):** the authored examples use surface constructs the
current AST cannot represent, and the grammar is under-specified. A1 must not
invent language semantics inside the parser.

**Files:**
- Add: `docs/lara-surface-grammar.md` — the frozen EBNF for `.lara` (artifact
  grammar) and `.policy.lara` (policy grammar), the two distinct top-level shapes.
- Edit: `src/Lara/AST.hs` — extend where the surface needs it.
- Edit: `examples/A-self-defeating-paper.lara`, `examples/B-two-paper-contested.lara`
  — reconcile to the frozen grammar; re-commit.

**Work — decide and write down, then make A/B conform:**
- **Attack-arguments without a claim.** `arg d1 : challenges(external_validity(a1))
  by leaf(e4)` and `arg d3 : supports(c1_neg) ...` (with `c1_neg` undeclared) do
  not fit `Arg` (which requires a declared `PropId`). Decide the surface + AST for
  attack-supporting arguments and undeclared/derived claim conclusions; extend the
  AST (e.g. an attack-argument node, or a claim-inference desugaring).
- **`challenges(...)`** target syntax and the **`.rule` / `.q.leaf` position
  suffixes** (how a dotted path lowers to `Position = [Step]`).
- **Implicit vs explicit premise selection** in `by <rule>(...)` (A/B omit
  principal premise leaves like `e1`, `e7`).
- **`#` lexing ambiguity:** `#` starts a comment *except* inside a source ref
  token (`refs = [paper_17.pdf#sec=4.1]`). Freeze the tokenizer rule.
- **Policy vs artifact top-level distinction** (two grammars, one file extension).

**Gate:** grammar frozen in `docs/lara-surface-grammar.md`; A/B parse under it
(verified in A1); AST extensions compile.

## Task A1: `Lara.Syntax` parser/printer + `Program`→`Unit` elaborator (result 12)

**Files:**
- Add: `src/Lara/Syntax.hs` — parse `.lara` → `Program`, `.policy.lara` → `Policy`
  (per A0.5 grammar); **label-preserving** canonical print `Program`/`Policy` →
  surface. Located parse-error type (line/col + reason, spec §10.1 R14-aligned).
- Add: `src/Lara/Elaborate.hs` — the **trusted surface elaborator**
  `Program + Policy + TheoryRegistry + Σ → Either ElabError Unit` (outside-voice
  #2/#3): resolve the named policy, validate `Arg.argClaim`, build the leaf
  context Γ, lower `status` requests to `unitQueries`, populate `unitTheories`
  from the registry, resolve attack dotted-positions, apply the admission map.
  **Admission (outside-voice #12):** `empirical-v1.policy.lara` declares no
  admission map; decide the default (total map / all-admit) and record it in the
  policy; keep R1 (undeclared leaf, executable core) distinct from R8 (admission
  reject, *outside* the executable core, `Lara.AST` line 483).
  **Decoupling (D1 ripple, keeps M4b a two-way door — TBD-1/TBD-2 below):**
  `Lara.Elaborate` is a **pure function over already-parsed `Program`/`Policy`
  values** — no `.lara` parsing, no CLI, no filesystem or co-located-policy IO
  *inside* it (that IO lives in `app/Main.hs`, which hands the elaborator parsed
  values). A machine producer (#32) can then build a `Program` in memory and
  reuse this exact trusted lowering, or ignore it — M4a forecloses neither.
- Add: `test/SyntaxSpec.hs` — round-trip properties + negatives + golden tests;
  register in `lara.cabal` (`other-modules`).
- Edit: `app/Main.hs` — `lara check <file>` extension-dispatches (`.lara` vs
  `.sexp`); `.lara` path parses → elaborates → `runUnit` → prints verdict, with
  co-located policy resolution (see below). `Lara.Driver.runUnit` reused unchanged.
- Edit: `lara.cabal` — expose `Lara.Syntax`, `Lara.Elaborate`; add the parser
  dependency chosen in A0.5.

**Work:**
- Parse the reconciled `examples/{A,B}-*.lara` and `empirical-v1.policy.lara` into
  `Program`/`Policy`; author the missing E1–E3/R1–R3 `.lara` files. **E1 is the
  vertical slice:** author E1, land the minimal parse→elaborate→verdict path,
  freeze E1's verdict from the Lean oracle, then expand to E2/E3/R1–R3.
- **E2 gap (outside-voice #7):** author E2 so its verdict `gap` comes from a claim
  with **empty complete support** (`statusC` = Gap iff `null claimSupport`,
  `Grounded.hs:127`) — NOT a declared arg with an open mandatory CQ (that is an
  `IncompleteArgument` *rejection*, `Check.hs:179`). The "incomplete attempt"
  teaching is captured via a separate `Lara.Reporting` `incompleteAlternative`
  golden (Haskell-only, not the differential). Re-word `worked-examples-plan.md`
  §1 E2 to match. `runUnit` stays unchanged.
- **Policy resolution (D-Arch-2):** artifact `policy <name>` resolves to
  `<name>.policy.lara` co-located in the artifact's directory; the elaborator
  asserts the loaded file's `policy <name>` header matches; error on
  absent/duplicate/mismatch. Record the trust note: the adjacent policy is a
  mutable trusted input — its content digest feeds replay identity (outside-voice
  #4); do not silently trust across a version mismatch.
- **Result 12 round-trip:** prove `parse ∘ print == id` over generated `Program`
  and `Policy` (exact structural equality, label-preserving printer — implies the
  spec's "α-equivalent" a fortiori). **Do NOT** claim `print ∘ parse` fixed on the
  authored files (comments/trivia are not in the AST). Authored files are verified
  by parsing to their committed `.core.sexp` golden (A2), not textual round-trip.
- **Negatives suite (D-CQ-1):** malformed surface, unknown keyword, unresolved
  policy name, bad attack-target path, duplicate surface ids → located errors.
- **REGRESSION (CRITICAL, IRON RULE):** `app/Main.hs` moves from `.sexp`-only
  (hardcoded `"usage: lara check <file.sexp>"`) to extension-dispatch. Add a
  `CliSpec` test asserting the existing `.sexp` check still returns the same
  verdict + exit codes (0/1/2) after dispatch lands.

**Gate:** `lara check examples/A-self-defeating-paper.lara` yields the same verdict
as the derived `.core.sexp`, byte-identical between Haskell `runUnit` and the Lean
driver; `parse ∘ print == id` holds; negatives produce located errors; the `.sexp`
regression test passes.

## Task A2: wire the worked-examples suite to goldens + differential

**Files:**
- Add: per-example directory under `examples/` (e.g. `examples/E1/{example.lara,
  example.core.sexp, expected.json, README.md}`) — a **flat `examples/` cannot
  hold one `expected.json` per example** (outside-voice #15). Discharges
  `docs/worked-examples-plan.md` §4.
- Edit: extend the **existing** differential mechanism (`scripts/differential.sh`
  + `test/DifferentialSpec.hs`) — do NOT build a parallel harness (D-Arch-3). Add
  each worked-example `.core.sexp` to the fixture corpus the script + spec already
  sweep; pin verdict bytes.

**Work:**
- Generate each `.core.sexp` by parsing + elaborating the `.lara` (the derivation
  path), commit as the differential anchor.
- **Freshness assertion (outside-voice #13):** a test asserts that re-running
  `parse` + `elaborate` on each committed `.lara` reproduces the committed
  `.core.sexp` bytes exactly (catches drift between surface and anchor).
- **`expected.json` schema (D-OV-3):** `{ verdict-class (compared across Haskell
  + Lean via the differential), located-diagnostic (rendered from Haskell
  `ProgramError`/`Reporting` to JSON, **Haskell-only** golden) }`. The Lean driver
  emits only the wire verdict, so located detail is not differential.
- Assert the coverage matrix: every status (justified/gap/contested/defeated),
  every attack kind (rebut/undercut/undermine), three rejection classes (R1/R12/R7
  per §1). **Honesty note (outside-voice #14):** the suite is defeasible-only —
  `use backends [nd@1]` is inert; the strict-certificate frontend path is NOT
  covered here (TODO captured).

**Gate:** all E1–E3/R1–R3/A/B examples pass Haskell↔Lean differential + `.core.sexp`
freshness + `expected.json` goldens; suite accounting maps §1's six examples plus
A and B explicitly.

## Task A3: mechanize result 12 (parse∘print round-trip) — CLAUDE.md discipline

**Files:**
- Edit: `lean/Lara/` — a Lean representation of the `Program`/`Policy` presentation
  AST and its printer; extend `AxCheck.lean`.

**Work (SCOPED to result 12 only — D-A3):**
- State and prove result 12 as `parse ∘ print == id` over the Lean `Program`/`Policy`
  representation (spec §9 result 12: "presentation codec round-trip to
  alpha-equivalent abstract syntax"; exact equality implies α-equivalence).
- **Explicitly out of A3:** the `eraseCert` / stable-argument-id `CheckedProgram`
  representation and the **result-9** backend-replacement obligations (transport,
  graph isomorphism, grounded-status invariance). Those belong to result 9
  (`docs/spec.md:1153-1159`), NOT result 12 — the first draft crossed the
  citation. Split to TODOS.md (backlog).
- **Caveat (outside-voice #11):** result 12 is a property of the *codec*; a Lean
  copy of the parser does not by itself prove the *Haskell* parser correct.
  `docs/mechanization-plan.md:55` marks result 12 test-only / optional to
  mechanize — confirm the intended strength before investing; the Haskell
  QuickCheck round-trip (A1) is the conformance evidence, the Lean lemma is the
  metatheory anchor for the frozen AST shape.
- Keep proofs `sorry`-free within the `propext` / `Classical.choice` /
  `Quot.sound` trio.

**Gate:** `AxCheck.lean` covers the new theorem; the Lean build is green.

## M4a Definition of Done

- `.lara` parses to `Program`/`Policy`; the trusted elaborator lowers to `Unit`;
  `parse ∘ print == id` holds (result 12), property + golden tested.
- `lara check <file.lara>` yields the S-expr verdict byte-identical to the derived
  `.core.sexp` and the Lean driver; the `.sexp` regression test passes.
- The worked-examples suite (E1–E3, R1–R3, A, B) each has a per-example dir with
  `.core.sexp` + `expected.json` golden; Haskell and Lean agree on the class;
  `.core.sexp` freshness holds.
- Every status, attack kind, and the three rejection classes are covered; the
  defeasible-only limitation (inert `nd@1`) is recorded.
- Result 12 mechanized in Lean (scope: round-trip only); `AxCheck.lean` green.
- Located parse/elaborate errors + a negatives suite exist.
- Docs (grammar, worked-examples-plan, m4a-checklist) / ARA ledger updated.

## Out of scope (→ #32 / M5+ / TODOS)

- The untrusted elaborator and the "no hand-authored certificate" clause → M4b
  (#32). (M4a's *trusted surface* elaborator is in scope.)
- The `eraseCert` / stable-argument-id `CheckedProgram` representation and
  **result-9** backend-replacement mechanization → TODOS.md (split from A3).
- A **strict-certificate worked example** exercising the `nd@1` cert frontend path
  → TODOS.md (the M4a suite is defeasible-only).
- `Lara.Json` LLM-producer surface (#30); PaperBench evaluation (M5); elaborator
  faithfulness measurement (M5).
- Serializing gap-holes / located diagnostics into the frozen wire verdict (would
  reopen M3) — kept Haskell-side.
- Incremental re-checking, large-graph performance, diagnostic UX
  (`TODOS.md` "Runtime (M4 candidates)", P3); preferred/stable/complete
  semantics; the optional LP adapter.

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | `/codex review` | Independent 2nd opinion | 1 | issues_found | 15 raised; 6 confirm our findings, 9 new (feasibility) |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | clean | 9 decisions resolved, 0 critical gaps |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | not applicable (compiler/proof work) |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | — |

Decisions locked (all via AskUserQuestion, user-approved):
1. **A3 scope** → result 12 (round-trip) only; result-9 eraseCert/CheckedProgram refactor split to TODOS.
2. **Parse target** → `.lara` → `Program`/`Policy` + a new named `Program→Unit` elaborator (rejects D1's "direct to Unit"; ripples to #32).
3. **Policy linking** → co-located `<name>.policy.lara` convention, header-match asserted.
4. **Differential** → extend the existing `differential.sh`/`DifferentialSpec` harness, not a new one.
5. **Parse errors** → located error type + negatives suite (R14-aligned).
6. **Round-trip** → label-preserving printer, exact `parse ∘ print == id`; drop the false `print∘parse`-on-authored-files gate.
7. **Grammar** → new A0.5 freeze task (EBNF + `challenges`/anonymous-args/position-suffix/`#`-in-refs) before A1; reconcile A/B.
8. **E2 gap** → gap = empty complete support (keeps `runUnit` unchanged) + a Haskell-only `Reporting` golden.
9. **expected.json** → rejection-class differential + Haskell-only located diagnostic.
10. **TODO** → result-9 machinery added to `TODOS.md`.
11. **TODO** → strict-certificate worked example added to `TODOS.md`.

Folded corrections (no separate decision): citations §1.1-not-§10.1, `m1-freeze-checklist`/`m3-closeout-notes` filenames, result-9-not-12 parenthetical; elaborator needs TheoryRegistry+Σ inputs; admission-map totality + R1-vs-R8; `.core.sexp` freshness assertion; inert `nd@1` honesty note; per-example dirs; cabal/parser-dep/JSON-dep registration; A0 sequencing (E1 vertical slice).

- **CODEX:** 15 findings at high reasoning; 6 independently confirmed our architecture/round-trip/A3 calls (cross-model consensus), 9 were new — 3 became decisions (grammar, E2 gap, expected.json), 6 folded as corrections. No cross-model tension (Codex agreed with every review decision).
- **CROSS-MODEL:** Claude eng review + Codex converged on the same load-bearing defect (the missing `Program→Unit` elaborator / lossy direct-to-Unit). Strong signal the two-layer routing is correct.
- **VERDICT:** ENG CLEARED — plan revised and locked, ready to implement. Sequence: A0 → A0.5 (grammar freeze, gates A1) → A1 (E1 vertical slice first) → A2 → A3.

NO UNRESOLVED DECISIONS
