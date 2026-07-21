# LARA engineering plan

_How the artifact gets built, in dependency order. This is the engineering companion to the
milestone spine (`../plans/research-proposal.md` §7, M0–M7) and the phased work plan
(`../plans/popl-research-review.md` §5, Phases A–G). Where those describe *what* and *when*, this
describes the *module dependency graph* and the *build discipline*. The spec (`spec.md`) is the
contract every module implements._

## 0. Current state (2026-07-21)

The only code that exists is the innermost strict layer — ~483 lines of Haskell:

| Module | Role | Status |
| --- | --- | --- |
| `Lara.Term`, `Lara.Formula` | LP proof polynomials `t` and formulas `F` | seed |
| `Lara.Kernel` | checks `d ⇒ t : F`, mints the sealed `Judgment` | seed |
| `Lara.ConstantSpec` | membership check for `(constant, formula)` pairs | **TCB hole** |

Everything above the LP kernel — propositions/`nf`, leaves, policies, warrant terms, typed attacks,
AF compilation, grounded labelling, four-state aggregation, JSON codec, parser/printer, and the
untrusted elaborator — is **spec-only**. No code yet.

Known defect carried in code: `ConstantSpec` accepts arbitrary `(constant, formula)` pairs
(spec §5; `research-proposal.md:291`). Until it is a fixed axiom-schema recognizer, `Lara.Kernel` is
not a trusted core and must not be described as one.

## 1. The dominating constraint: corpus before calculus

`research-proposal.md:454` (the order constraint) and the eight open questions in §8 make the
sequencing non-negotiable:

> Do the corpus study before freezing the calculus, but build one hand-lowered vertical slice while
> specifying it. Do not automate ARA lowering until the source language, policy obligations, and
> trusted base are stable.

**Decision (2026-07-21): M0 corpus study is the true blocker.** No new upper-layer Haskell begins
until the corpus fixes the shapes it can change. The corpus-sensitive open questions are §8 #2
(which rule schemes exist; which are strict vs defeasible), #3 (defeat typing), #5 (leaf
granularity), and #7 (behavioral-vs-empirical routing, which gates TL-1). Building the warrant-term,
policy, and attack layers before these are known would bake guesses into the frozen v0.1 calculus
and the evaluation benchmark.

### The two carve-outs that M0 cannot change

Two pieces are already frozen by recent spec work and are corpus-independent, so they *may* proceed
in parallel with M0 without violating the constraint:

1. **`nf`/`≡` normalizer** (spec §3.2) — literal canonicalization + structural recursion over ground
   atoms; no argument reordering, no binders. Frozen in commit `124f461`.
2. **Fixed LP axiom-schema recognizer** (spec §5) — the `ConstantSpec` fix. The A0–A4 schemas are
   the logic itself (Tier 1, `research-proposal.md:268`); the corpus cannot move them.

These are the only Haskell allowed to start before M0 exits. Everything else waits.

## 2. M0 — semantic corpus study (the current work)

Exit criteria (from `popl-research-review.md` §5 Phase A and `research-proposal.md` M0):

- 50–100 claims sampled across the 30-paper ARA corpus, stratified by claim type (descriptive,
  comparative, causal, generalization, negative-result, implementation/behavioral).
- Each annotated for: proposition shape, evidence/leaf granularity, warrant scheme + premises,
  critical questions, rebut/undercut/undermine candidates, and unresolved holes.
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
| 2 | `Lara.Axiom` — fixed A0–A4 recognizer; re-seal `Kernel` on it | §5 | Kernel | no (carve-out) |
| 3 | `Lara.Policy` — rule schemas, `contrary`, `exception`, admission table, **§8.1 strict-reachable validator** | §4, §8.1 | Prop | which schemes |
| 4 | `Lara.WarrantTerm` — `w` AST, `⊢ w : supports(p) ▷ O`, `leaves(w)` | §6, §4.1–4.3 | Prop, Axiom, Policy | granularity |
| 5 | `Lara.Attack` — positional `w@π`, rebut/undercut/undermine typing | §7 | WarrantTerm, Policy | taxonomy |
| 6 | `Lara.Compile` — `compile(P)=AF`, subargument closure | §8 | WarrantTerm, Attack | no |
| 7 | `Lara.Grounded` — least-fixpoint labelling + four-state aggregation | §8 | Compile | no |
| 8 | `Lara.Diagnostics` — located rejection for every ill-formed construct | §1, §10 | all above | no |

**The §8.1 policy validator is an early M3 target** (`research-proposal.md:447`): compute the
strict-reachable proposition set and reject any policy whose `contrary` declarations touch it. It
lands with `Lara.Policy` (layer 3), not later.

### Boundary layers (after the core AST stabilizes)

These plug the untrusted producer into the checker and must **not** drive the trusted design, so
they come after layers 1–8:

- `Lara.Json` — producer/checker wire codec (spec §1); can track `WarrantTerm` early.
- `Lara.Syntax` — presentation parser + canonical printer; codec round-trip to α-equivalent AST
  (spec §9 result 10).
- **Untrusted Python/LLM elaborator** (Phase E) — explicitly last. It performs the five logged
  lowering tasks (spec §11) and may never define policy rules or logical schemas at runtime.

Layers 1–2 plus a hand-authored warrant term and a stub policy are the **vertical slice**: run one
claim end-to-end through 6→7 to prove the pipeline before the real schemes freeze.

## 4. Mechanization track (parallel, starts at M1 freeze)

`spec.md §9` lists 10 required results; results 1–8 must be mechanized (Lean 4 default,
`research-proposal.md:461`; open question §8 #8 decides Lean vs Rocq before M1 freezes). Engineering
implications:

- It is a **separate development sharing one first-order core AST** with the Haskell checker
  (`research-proposal.md:258`) — that shared serialized core is the differential-testing anchor.
- Design `Lara.WarrantTerm`'s AST from day one to serialize into the Lean/Rocq model, so the same
  core programs and verdicts cross-check both implementations.
- Do not start mechanizing until M1 freezes the definitions; a theorem about the model does not
  transfer to the Haskell checker without the conformance argument (differential + property +
  golden + mutation tests).

## 5. Test discipline (all layers)

- **Property tests** (QuickCheck, already wired) per layer for the algebraic laws — e.g. `≡`
  reflexive/symmetric/transitive/linear; grounded labelling determinism.
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
| §8 #2 rule schemes | `Lara.Policy` | M0 |
| §8 #3 defeat typing | `Lara.Attack` | M0 |
| §8 #5 leaf granularity | `Lara.WarrantTerm` leaf handling | M0 |
| §8 #8 TCB + Lean/Rocq | mechanization track start | before M1 freeze |
| §8 #7 behavioral routing | TL-1 (optional) | corpus sampling |

Carve-out layers 1–2 clear no gate — they are frozen and may start now.
