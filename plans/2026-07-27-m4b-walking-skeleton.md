# M4b Implementation Plan — walking skeleton, no hand-authored certificate

> **For agentic workers:** REQUIRED SUB-SKILL: Use `executing-plans` to
> implement this plan task by task. Keep checkbox state current as each focused
> test and gate lands.

**Tracker:** GitHub #32 (child of #29, the M4 umbrella). Sibling: #31 (M4a,
`plans/2026-07-27-m4a-compiler-worked-examples.md`). **Blocked on #31** (needs
`Lara.Syntax` and the frozen `Unit` IR surface).

**Milestone spine:** `plans/research-proposal.md` §7, M4 — the "no hand-authored
certificate step; all untrusted outputs retained for audit" clause. That clause
needs a *machine producer*, which is why it is split out from M4a.

**Why M4b is its own track.** A tiny `.lara` file *is* a hand-authored
certificate — its typed attacks, support terms, and CQ discharges are the
certificate content in surface form. M4a (#31) proves the compiler + type
checker on those self-authored examples; M4b adds the untrusted **elaborator**
that produces the certificate from a source, so no human writes it.

**Source (D2).** A small self-authored **structured source** (e.g. a hand-built
ARA trace for one worked example) — NOT a clean award paper (PaperBench is
demoted to M5; award papers never exhibit `defeated`/`contested`/`gap`). The
source is self-created; the *certificate* is machine-produced. That keeps the
"no hand-authored certificate" property honest while staying in the motivating
examples, not an external corpus.

**Architecture.** The elaborator emits `.lara`, which flows through the M4a
pipeline. `.lara`, `.sexp`, and (later) JSON are concrete syntaxes over one
symbolic IR (`Unit` = `Lara.AST`):

```text
  structured source ──elaborator (untrusted, §11)──► bundles/<skeleton>/ ──► lara check ──► verdict
  (mini ARA trace,            │                      ├─ source.yaml (input)         ▲
   research-level only:       │                      ├─ empirical-v1.policy.lara    │
   NL claims, evidence,       │                      │  (copied trusted input, 1A)  │
   outcomes, dead ends;       │                      ├─ emitted .lara ◄── golden byte-diff (T5)
   NO certificate-level       │                      ├─ derived .core.sexp ─────────┼─► differential.sh
   content (T6)               └─ provenance log        ├─ frozen verdict              │   (glob extended, 2A;
                                (per §11 task,         └─ manifest.json ──────────────┘    CI-wired, T3)
                                 canonicalized)          trusted-input sha256s +
                                                          checker-rev + lara-core@0.1 (T4)
```

`Lara.Syntax` (from #31) is **inside** the TCB; the elaborator is **outside** it
(spec §11) and may never define policy rules, schemas, or backends at runtime —
it only instantiates the versioned trusted inputs (`Sigma`, `Pi`, `R`, theory
digests) by id.

**Tech Stack:** Python (`uv`) for the elaborator — a single-file PEP 723 script
(`elaborator/elaborate.py`, PyYAML the only dependency; no `pyproject.toml`, no
package scaffold — the #30 LLM stage decides package structure, review 4A); the
`Lara.Syntax` frontend and `Lara.Wire` codec from #31; the Lean executable
semantics as the verdict oracle.

## Resolved decisions (shared with #31)

- **D1 — producer→checker surface.** The elaborator emits `.lara`; `Lara.Syntax`
  lowers it to `Unit`; the canonical `.sexp` is *derived* via
  `Lara.Wire.encodeUnit` as the replay + Haskell↔Lean differential artifact.
  **JSON is deferred** to the LLM-producer stage (#30), gated on the D3 flip.
- **D2 — source.** A self-authored structured source (see above); PaperBench
  dropped from the M4 critical path.
- **D3 — elaborator determinism.** Deterministic harness first (reproducible CI,
  no live model); LLM lowering + JSON (#30) is a later increment.

## Global Constraints

- **`Lara.Syntax` is TCB; the elaborator is not.** A checker verdict may never
  depend on elaborator-only code. The checker always receives the explicit wire
  form and re-derives everything (spec §10.1).
- **The elaborator instantiates, never defines** (spec §4, §5). It loads
  the trusted inputs read-only and references them by id. The trusted inputs
  the checker actually consumes are the **policy file** (rules, contraries,
  exceptions) and the **theory registry** (currently empty; M4a ships all-admit
  admission and ignores `Sigma`, which is grammar-frozen vocabulary — outside-
  voice #3 confirmed). The manifest hashes what the checker consumes, not the
  spec's idealized tuple.
- **Faithfulness is an evaluation axis, not a checker guarantee.** Lowering
  faithfulness of the six §11 tasks is measured against human annotation in M5,
  never asserted by acceptance (spec §11). M4b proves the *plumbing*.
- **The Lean executable semantics is the verdict oracle** (M3 review D16).
- **Bundles are hermetic** (review 1A). A replay bundle contains every trusted
  input it was checked against — the policy file is *copied in*, not referenced
  by path — so replay needs only the bundle directory and the `lara` binary.
- **Bundle artifacts are canonicalized for byte-identity.** The provenance log
  and manifest carry no wall-clock timestamps, no absolute paths, and no
  unordered dumps (sorted keys throughout); replay compares bytes, so every
  byte must be a function of the source and the trusted inputs only.

---

## Task B0: source + replay-bundle format + D3

**Work:**
- Choose the small self-authored structured source (a hand-built ARA trace for
  one worked example, YAML — matching the `ara/trace/*.yaml` convention) that
  the elaborator lowers.
- **Source abstraction ceiling (T6).** The source contains research-level
  objects only: NL claims, evidence cells, experiment outcomes, dead-end
  narratives, artifact refs. It may NOT contain formal propositions, scheme
  ids, discharge decisions, attack declarations, or certificates — those are
  DERIVED by the elaborator and logged in provenance, or the "no hand-authored
  certificate" property is theater.
- **Task coverage, honestly stated (T1/T2).** The frozen frontend has no
  support-term assurance syntax (`Lara.Syntax` forces `AssuranceNone`), and no
  implementation layer carries duplicate-report groups. So the source exercises
  §11 tasks 1–4 and 6 for real; task 5 is spec-conditional ("where a strict
  instance is certified") and N/A here; task 2 is exercised as leaf extraction
  + source binding, with any duplicate-report case logged in provenance only.
  Strict-cert frontend and §4.3 groups are TODOS/issue items, not M4b scope.
- Confirm D3 (deterministic harness first).
- Specify the replay-bundle format (reviews 1A/2A/T4/T8): a hermetic directory
  under `bundles/` containing the elaborator inputs (source trace), the
  *copied* trusted policy file, a per-§11-task provenance log (canonicalized),
  the emitted `.lara`, the derived `.core.sexp`, the frozen verdict, and a
  manifest recording every trusted input's sha256 (policy file, theory
  digests) plus two identities: the **checker-source revision** — last commit
  touching `src/ app/ lean/ lara.cabal cabal.project` (the `lean/` path
  carries the toolchain + lake manifest) — and the **producer toolchain**
  (pinned PyYAML, Python, uv versions). Both are audit metadata, not a full
  binary-reproducibility identity (GHC/dependency-store pinning stays out of
  scope).

**Gate:** the source and bundle format are committed and reviewed before
elaborator code lands.

## Task B1: untrusted elaborator (Phase E, six §11 lowering tasks)

**Files:**
- Add: `elaborator/elaborate.py` (single-file PEP 723 script, PyYAML the only
  runtime dependency — pinned, with `requires-python` (T8)) — reads the B0
  source, performs the six §11 tasks, emits `.lara` + a provenance log into
  the bundle directory, and copies the referenced trusted policy file in (1A).
- Add: `elaborator/test_elaborate.py` (stdlib `unittest`, zero added deps) —
  one test per §11 task (T10, reversing 7A) plus the malformed-source
  negatives (6A).

**Work:**
- Implement the six logged lowering tasks (spec §11): (1) NL proposition
  formalization; (2) evidence-leaf extraction + source binding (duplicate-
  report situations are logged in provenance only — no implementation layer
  carries groups, T2); (3) inference-scheme selection/instantiation; (4)
  critical-question discharge or explicit hole creation; (5) strict-backend /
  theory / certificate selection — N/A for this defeasible source (T1); (6)
  typed-attack extraction over the whole exploration trace, lowering each
  `dead_end` node per its evidential role.
- Enforce the trust boundary in code: load the trusted inputs read-only,
  reference by id, define none.
- **Input-validation contract** (review 6A): a malformed source (unparseable
  YAML, missing node field, unknown node kind) exits nonzero with a located
  stderr message and emits **no** `.lara`.
- **Transactional generation** (T9): all bundle artifacts are written to a
  staging directory and renamed into place only on full success — a failed
  run never leaves partial or stale content that a later check could mistake
  for fresh output.
- **Per-task tests** (T10): one test per §11 task pinning its trace→.lara
  derivation; the malformed-source negatives pin the 6A contract.

**Gate:** the emitted `.lara` is **accepted by the unchanged checker** with no
manual edit — the "no hand-authored certificate" property.

## Task B2: replay bundle

**Files:**
- Add: bundle writer + `scripts/replay.sh` that re-runs a bundle through
  `lara check` and diffs the verdict. (A `lara replay` CLI mode is rejected:
  replay is untrusted audit plumbing and stays out of the trusted binary.)

**Work (reviews D4/T4/5A):**
- Manifest check first: recompute every trusted input's sha256 and compare
  against the manifest — a mismatch is a **hard error** (D4). Checker-source
  revision drift (T4) is a **loud warning**; replay proceeds and the verdict
  byte-diff decides.
- Tamper fixture: a scratch copy of the skeleton bundle with one doctored
  trusted input must hard-fail replay — the only test that observes the
  mismatch path firing (5A).

**Gate:** replaying the committed skeleton bundle reproduces the frozen verdict
byte-for-byte; a trusted-input version mismatch is a hard error (and the tamper
fixture proves the error fires).

## Task B3: end-to-end walking skeleton (golden)

**Files:**
- Add: `test/` walking-skeleton golden — source → elaborator → `.lara` →
  `lara check` → verdict, matching the B0 oracle, zero hand-authored certificate.
- Edit: `.github/workflows/ci.yml` — install `uv` (astral-sh/setup-uv, version
  pinned, T8) and run the elaborator tests, golden, and replay gates; the
  plan's "holds in CI" requirement has no CI step without this (review finding,
  CI gap).
- Edit: `.github/workflows/ci.yml` — run `scripts/differential.sh` in CI
  (neither existing job invokes it today; the 32/32 Haskell↔Lean agreement is
  currently local-only, T3).
- Edit: `scripts/differential.sh` — extend the fixture glob to `bundles/` so
  the machine-produced `.core.sexp` anchor gets the same Haskell↔Lean
  byte-exact differential as every other anchor (review 2A). The `.core.sexp`
  is derived by the existing `scripts/gen-worked-examples.hs` (parse →
  elaborate → `Lara.Wire.encodeUnit`), generalized to bundle inputs.

**Work (reviews T3/T5/T7):**
- **Producer determinism (T5):** the golden also asserts the freshly emitted
  `.lara` and provenance log are byte-identical to the committed bundle's —
  D3's "deterministic harness" becomes a tested property, not a claim.
- **Authenticity check (T7):** CI asserts the bundle's policy copy is
  byte-identical to the canonical policy it was copied from — a
  self-consistent-but-substituted bundle fails even though the tamper fixture
  cannot see it.

**Gate:** the M4 spine definition-of-done "one claim end to end, no
hand-authored certificate" holds in CI (deterministic harness, no live model).

## M4b Definition of Done

- An untrusted elaborator lowers one structured source (research-level content
  only, T6) to a checker-accepted `.lara` via §11 tasks 1–4 and 6, no manual
  edit (task 5 is spec-conditional and N/A for a defeasible source, T1).
- A replay bundle retains every untrusted output and re-runs deterministically
  to the frozen verdict; producer determinism is byte-tested (T5).
- The walking-skeleton run is golden-tested in CI, with the Haskell↔Lean
  differential CI-enforced over its anchor (T3).

## Out of scope (M5+ / TL-1)

- **Strict-certificate frontend (T1, issue #37).** Support-term assurance surface syntax
  (`assurance = cert(…)`), its elaboration, and a theory-registry CLI path —
  TCB work on the frozen frontend that the nd@1 cert path requires. Tracked in
  TODOS + issue #37; spec-conditional §11 task 5 stays N/A until then.
- **Duplicate-report groups, spec §4.3 (T2, issue #38).** No implementation layer (surface
  syntax, `Unit`, wire, Lean) carries groups; the frozen R9 class is spec-only.
  A cross-layer TCB feature of its own. Tracked in TODOS + issue #38.
- **Verdict-carried replay identity (spec §2.1, issue #36).** The spec obligates reports
  to "print the [replayId] tuple verbatim"; the current verdict encoder prints
  no tuple and adding one is a coordinated Haskell+Lean change to the
  differential anchor. M4b gets audit identity from the bundle manifest
  instead (D4/T4). Tracked in TODOS + issue #36.
- **`Lara.Json` — LLM-producer surface (later stage, #30).** A third concrete
  syntax over the same `Unit`, for the machine producer we cannot retrain:
  `decode : JSON → Unit`, routed through the identical checker. JSON Schema
  constrains the *framing*; a small expression sub-grammar carries the *logic*.
  JSON fixes packaging validity, not logical faithfulness. **Trigger:** land it
  alongside the first LLM-driven elaborator run (the D3 flip), not before.
- **PaperBench (`corpus/ara-paperbench`) → M5 evaluation.** Award-winning papers
  are the wrong substrate for the discriminating statuses; a real evaluation
  corpus wants *contested / flawed / retracted* claims.
- **Elaborator lowering faithfulness** measurement against human annotation
  (spec §11) — the M5 evaluation axis, not M4 plumbing.

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | outside voice | Independent 2nd opinion | 1 | issues_found | 14 findings → 11 tensions, all resolved (T1–T11); 1 reversed decision (D3), 1 reversed test skip (7A) |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | CLEAR | 7 issues, 0 critical gaps — arch 3 (1A/2A/3A), quality 1 (4A), test 3 (5A/6A/7A), perf 0; Step-0: D2 skip office-hours, D4 harness-side manifest |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | no UI scope |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | — |

- **CROSS-MODEL:** Codex confirmed 3 P0 plan defects the section review missed (strict-cert frontend impossible, §4.3 groups inexpressible, differential not in CI) — all corrected (T1/T2/T3). Agreement on the overall architecture (untrusted producer → unchanged checker → replay bundle).
- **VERDICT:** ENG CLEARED — ready to implement. Outside-voice findings folded (10 accepted, 1 clarified, 2 held with rationale, 1 cosmetic-noted). Deferred work filed: issues #36 (replayId), #37 (strict-cert frontend), #38 (duplicate-report groups).

NO UNRESOLVED DECISIONS
