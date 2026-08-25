# LARA engineering plan

_How the artifact gets built, in dependency order. This is the engineering companion to the
milestone spine (`../plans/research-proposal.md` §7, M0–M7) and the phased work plan
(`../plans/popl-research-review.md` §5, Phases A–G). Where those describe *what* and *when*, this
describes the *module dependency graph* and the *build discipline*. The spec (`spec.md`) is the
contract every module implements._

## 0. Current state (2026-07-21; M1 update 2026-07-22; M5 update 2026-08-19; surface updates 2026-08-22/23; milestone update 2026-08-24)

**Milestone update (2026-08-24): no milestone is open in this repository.** #60
(M7, the paper package) was closed as completed — paper-writing and
submission-package work is tracked in the paper repository, not here. The
milestone spine in `../plans/research-proposal.md` §7 is now a record rather than
a worklist. Remaining engineering work is the open GitHub issues, chiefly the
`refreeze-batch` evaluation-suite extensions (#125 in #154, #124, and #123),
which landed together and were frozen by the shared refreeze cycle #156 as
**`m5-freeze-v5`** — 541 mutants + 60 corpus units = 601 measured inputs. The
protocol and every anchor are in `docs/m5-freeze-checklist.md`.

**Surface update (2026-08-22):** `lara-syntax@0.9` adds named `nd@1` proof
terms as a presentation-only lowering to the unchanged de Bruijn kernel;
Appendix H and the S8 worked example are the durable specification and witness.
**Surface update (2026-08-23):** `lara-syntax@0.10` adds source-authored
`nd@1` formula annotations — `(prop TEXT)` lowered through the shared
`encodeAtomKey ∘ nf` path — closing #144; Appendix I and the rewritten S8 are
the durable specification and witness.

**M5 update (2026-08-19): M1–M5 are closed and the build order below is fully
implemented.** Since the M3 note, the core moved to **`lara-core@0.2`** (a
declared many-sorted signature carried in `Unit` and enforced in `checkUnit`
stage 2, making R2 a real rejection class — `spec.md` §3.4), the authoring
surface reached **`lara-syntax@0.10`** (`docs/lara-surface-grammar.md`
Appendices A–I; `@0.7` is the surface-strictness release — it removes three
spellings and adds none — and `@0.8` lets a certificate premise reference cite
the citing rule's declared premise label, so the core and the wire are
untouched; `@0.9` adds named `nd@1` proof terms lowered to the same de Bruijn
kernel and `@0.10` adds source-authored formula annotations for them, again
without a core or wire change), and the deterministic evaluation corpus is frozen at tag
`m5-freeze-v5` (`m5-freeze-checklist.md`). Layers added beyond the M3 spine:
`Lara.Admission` (the `.lara` source-boundary admission judgment,
`policy-admission-calculus-decision.md`), the `ord@1` and `ra@1` strict backends
beside `nd@1`, `Lara.Mutate` + `Lara.Measure` (the seeded mutation suite and the
axis-(c) harness), `Lara.ClaimSupport` + `Lara.BindingAudit` (reporting and the
blinded audit pipeline), and the cross-language presentation-parity guard
(`scripts/check-presentation-parity.sh`).

**M1 update (2026-07-22):** M0 exited (PR #8/#9) and the v0.1 language froze — `spec.md` is now
"v0.1 — frozen at M1" with the row-by-row record in `m1-freeze-checklist.md`. The Lean
development additionally mechanizes the frozen §6.1 support-term typing, §7.1 attack typing, and
§8 compilation layers (`lean/Lara/{Support,Attack,Compile}.lean`) plus the executable §8.1
Path-B validator (`lean/Lara/Policy.lean`); the M2 backlog and remaining proof preconditions are
tracked in the checklist. The Haskell state below is unchanged — M3 builds against the frozen spec.

**M3 update (2026-07-27): the production-checker spine has landed.** The §3 build order below is
now implemented in Haskell, each module the executable mirror of the frozen Lean development:

- **Layers 3–8** — `Lara.Policy` (rule schemas, `contrary`/`exception`, §8.1 strict-reachable
  validator), `Lara.SupportTerm` (`inferSupport`), `Lara.Attack` (positional rebut/undercut/
  undermine typing + exact `contraryMatchB`), `Lara.Compile` (subargument-closure AF), and
  `Lara.Grounded` (least-fixpoint labelling + four-state aggregation). The seven-stage whole-unit
  boundary is `Lara.Check.checkUnit`, with located diagnostics in `Lara.Diagnostics`.
- **Runtime** — `Lara.Runtime` is the cached-adjacency production evaluator; its verdict is
  byte-identical to the un-cached `Lara.Compile.checkedAF` path (guarded by `RuntimeSpec`, incl. a
  120-argument ≤5 s perf guard).
- **Reporting** — `Lara.Reporting` implements the M3-deferred `holes(P,p)` / `incompleteAlternative`
  claim diagnostics (spec §8, §10.1), previously listed as a deferral.
- **Wire anchor (N11)** — `Lara.Wire` is the single S-expression codec; the `lara check` CLI
  (`app/Main.hs`) and the Lean driver (`lean/Lara/Driver.lean`, exe `lara-driver`) both print
  verdicts through it, so differential testing is byte comparison.

The differential harness is live: `scripts/differential.sh` runs every `fixtures/**/*.sexp` through
**both** drivers and asserts byte-exact stdout + exit-code agreement (the Lean executable is the
oracle); `test/DifferentialSpec.hs` pins the agreed verdict bytes so `cabal test` catches
regressions without the Lean binary. The conformance corpus lives under `fixtures/corpus/`
(generated by `scripts/gen-corpus.hs`) plus the two committed self-edge fixtures, and includes a
120-argument default-heartbeat stress fixture. **R1–R14 coverage**: `checkUnit` decides
R1, R2, R3, R4, R5, R6, R7, R10, R11, R12, and R13 (certificate replay at the
support stage), plus the four structural outcomes (duplicate-rule, duplicate-argument,
incomplete-argument, and missing-conflict); `CheckSpec` pins each with a rejected golden. The
production driver decides replay-preflight R13 and the escalated data-integrity class R9. R8 is the
source-admission boundary. R14 is the wire-decode
boundary, covered by `WireSpec`'s malformed-input matrix. The mutation and differential corpora
exercise these boundaries. The soundness proofs remain in Lean (`sorry`-free, standard axiom
trio); these tests are conformance evidence.

The Haskell state table below records the pre-M3 snapshot for historical context.

The only code that existed before M3 was an experimental LP adapter seed — ~483 lines of Haskell:

| Module | Role | Status |
| --- | --- | --- |
| `Lara.Term`, `Lara.Formula` | LP proof polynomials `t` and formulas `F` | optional-adapter seed |
| `Lara.Kernel` | checks `d ⇒ t : F`, mints the sealed `Judgment` | optional-adapter seed |
| `Lara.ConstantSpec` | membership check for `(constant, formula)` pairs | **non-conforming adapter** |

Carve-out 1 (`Lara.Prop`, `nf`/`≡`) and carve-out 2 (`Lara.Strict` backend registry +
`Lara.Strict.ND` reference adapter) are now implemented and tested (21 QuickCheck properties pass;
see `../ara/evidence/status/test_status.md`). Everything else in the source calculus — leaves,
policies, support terms, typed attacks, AF compilation, grounded labelling, four-state aggregation,
JSON codec, parser/printer, and the untrusted elaborator — is **spec-only**. No code yet.

Known defect carried in code: `ConstantSpec` accepts arbitrary `(constant, formula)` pairs. The
existing modules are not the LARA core and do not satisfy the strict-backend contract. They become an
eligible LP adapter only after fixed schema recognition and a soundness/conformance argument.

## 1. The dominating constraint: corpus before calculus

`research-proposal.md:454` (the order constraint) and the eight open questions in §8 make the
sequencing non-negotiable:

> Do the corpus study before freezing the calculus, but build one hand-lowered vertical slice while
> specifying it. Do not automate ARA lowering until the source language, policy obligations, and
> trusted base are stable.

**Decision (2026-07-21): M0 corpus study is the true blocker.** No new upper-layer Haskell begins
until the corpus fixes the shapes it can change. The corpus-sensitive open questions are §8 #2
(which rule schemes exist; which are strict vs defeasible), #3 (defeat typing), #5 (leaf
granularity), and #7 (behavioral-vs-empirical routing, which gates TL-1). Open question #1 also
decides which optional strict adapters ship, but does not block the fixed interface or reference
adapter. Building the support-term, policy, and attack layers before these are known would bake
guesses into the frozen v0.1 calculus and the evaluation benchmark.

### The two carve-outs that M0 cannot change

Two pieces are already frozen by recent spec work and are corpus-independent, so they *may* proceed
in parallel with M0 without violating the constraint:

1. **`nf`/`≡` normalizer** (spec §3.2) — literal canonicalization + structural recursion over ground
   atoms; no argument reordering, no binders. Frozen in commit `124f461`.
2. **Strict-backend interface + natural-deduction reference adapter** (spec §5;
   `strict-backend-decision.md`) — the interface, replay/normalization/soundness/dependency
   obligations, and reference rules are corpus-independent. Corpus evidence decides which optional
   adapters ship; it does not change the seam.

These are the only Haskell allowed to start before M0 exits. Everything else waits.

## 2. M0 — semantic corpus study (the current work)

Exit criteria (from `popl-research-review.md` §5 Phase A and `research-proposal.md` M0):

- 50–100 claims sampled across the 30-paper ARA corpus, stratified by claim type (descriptive,
  comparative, causal, generalization, negative-result, implementation/behavioral).
- Each annotated for: proposition shape, evidence/leaf granularity, inference scheme + premises,
  critical questions, rebut/undercut/undermine candidates, unresolved holes, and for every proposed
  strict step the smallest plausible certifier/theory (reference ND, domain checker, LP, or none).
- Double-annotate ≥20–30%; adjudicate disagreements.
- **Exit gate:** a finite set of constructs covers ≥80% of sampled argument shapes without encoding
  whole reasoning steps as opaque leaves.

M0 is a **data/annotation task, not a coding task.** Its deliverable is the answer set for open
questions §8 #2/#3/#5/#7, which unlocks the module backlog below. It has no code dependency and
should start immediately.

## 3. Post-corpus Haskell build order (the M3 spine)

Built bottom-up once M0 exits. Each layer ships as a module plus property + golden tests before the
next begins, keeping the trusted core small and auditable at every step. "Corpus-gated" marks layers
whose shape M0 can change.

| # | Module | Spec | Depends on | Corpus-gated |
| --- | --- | --- | --- | --- |
| 1 | `Lara.Prop` — ground atoms + `nf`/`≡` | §3, §3.2 | — | no (carve-out) |
| 2 | `Lara.Strict` + `Lara.Strict.ND` — closed registry, backend contract, reference natural-deduction adapter | §5 | Prop | no (carve-out) |
| 3 | `Lara.Policy` — rule schemas, `contrary`, `exception`, admission table, **§8.1 strict-reachable validator** | §4, §8.1 | Prop, Strict | which schemes |
| 4 | `Lara.SupportTerm` — `w` AST, `⊢ w : supports(p) ▷ O`, `leaves(w)`, `certDeps(w)` | §6, §4.1–4.3 | Prop, Strict, Policy | granularity |
| 5 | `Lara.Attack` — positional `w@π`, rebut/undercut/undermine typing | §7 | SupportTerm, Policy | taxonomy |
| 6 | `Lara.Compile` — `compile(P)=AF`, subargument closure | §8 | SupportTerm, Attack | no |
| 7 | `Lara.Grounded` — least-fixpoint labelling + four-state aggregation | §8 | Compile | no |
| 8 | `Lara.Diagnostics` — located rejection for every ill-formed construct | §1, §10 | all above | no |

**The §8.1 policy validator is an early M3 target** (`research-proposal.md:447`): compute the
strict-reachable pattern set and reject any policy whose `contrary` sides may overlap it at the
ground-instance level. It lands with `Lara.Policy` (layer 3), not later.

### Boundary layers (after the core AST stabilizes)

These plug the untrusted producer into the checker and must **not** drive the trusted design, so
they come after layers 1–8:

- `Lara.Json` — producer/checker wire codec (spec §1); can track `SupportTerm` early.
- `Lara.Syntax` — presentation parser + canonical printer; codec round-trip to α-equivalent AST
  (spec §9 result 10).
- **Untrusted Python/LLM elaborator** (Phase E) — explicitly last. It performs the six logged
  lowering tasks (spec §11) and may never define policy rules or logical schemas at runtime.

Layers 1–2 plus a hand-authored support term and a stub policy are the **vertical slice**: run one
claim end-to-end through 6→7 to prove the pipeline before the real schemes freeze. Port the existing
LP seed behind `Lara.Strict` only if the corpus justifies a second shipped adapter.

## 4. Mechanization track (parallel, starts at M1 freeze)

`spec.md §9` lists 12 required results; core results 1–9 plus reference-adapter result 10 must be
mechanized (Lean 4 default,
`research-proposal.md:461`; open question §8 #8 decides Lean vs Rocq before M1 freezes). Engineering
implications:

- It is a **separate development sharing one first-order core AST** with the Haskell checker
  (`research-proposal.md:258`) — that shared serialized core is the differential-testing anchor.
- Design `Lara.SupportTerm`'s AST from day one to serialize into the Lean/Rocq model, so the same
  core programs and verdicts cross-check both implementations.
- Do not start mechanizing until M1 freezes the definitions; a theorem about the model does not
  transfer to the Haskell checker without the conformance argument (differential + property +
  golden + mutation tests).

## 5. Test discipline (all layers)

- **Property tests** (QuickCheck, already wired) per layer for the algebraic laws — e.g. `≡`
  reflexive/symmetric/transitive/linear; natural-deduction weakening; backend replacement; grounded
  labelling determinism.
- **Golden tests**: the three complete + three rejected examples the spec requires
  (`popl-research-review.md` §5 Phase B; spec §10 currently has one incomplete example).
- **Mutation suite** (M3/Phase D): wrong formulas, undeclared leaves, hidden policy extension, bad
  attack targets, open obligations, cycles, codec corruption — every rejection class must be caught.
- **Differential tests**: serialized core programs + verdicts run through both Haskell and the
  mechanized executable semantics once the mechanization track is live.

Property/golden/mutation/differential tests are **conformance evidence, not soundness proofs**
(spec §9 closing note); the mechanized theorems carry soundness.

## 6. Decision gates

| Gate | Blocks | Resolved by |
| --- | --- | --- |
| M0 exit (≥80% coverage) | layers 3–5 | corpus study |
| §8 #1 optional adapter portfolio | LP/domain adapters beyond `Lara.Strict.ND` | M0 |
| §8 #2 rule schemes | `Lara.Policy` | M0 |
| §8 #3 defeat typing | `Lara.Attack` | M0 |
| §8 #5 leaf granularity | `Lara.SupportTerm` leaf handling | M0 |
| §8 #8 TCB + Lean/Rocq | mechanization track start | before M1 freeze |
| §8 #7 behavioral routing | TL-1 (optional) | corpus sampling |

Carve-out layers 1–2 clear no gate — they are frozen and may start now.
