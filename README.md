# LARA

[![CI](https://github.com/EYH0602/lara/actions/workflows/ci.yml/badge.svg)](https://github.com/EYH0602/lara/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)
[![spec](https://img.shields.io/badge/spec-v0.1%20frozen-brightgreen.svg)](docs/spec.md)

LARA is a small language of proof-carrying, policy-relative **claim support** —
a calculus for research claims in the way a proof assistant's kernel is a
calculus for proofs. A LARA program lowers a research artifact into a checkable
**claim-support graph**: for each claim it reports whether the argument from
declared evidence is **justified**, **gap**, **defeated**, or **contested** —
and why. Acceptance is a certificate check against a fixed policy, not a search
for truth: every dependency, open obligation, and attack is explicit, and the
reported status is the grounded result for the compiled graph.

## Why LARA

Research claims — in papers, agent-generated experiment reports,
[ARAs](https://github.com/ARA-Labs/Agent-Native-Research-Artifact) — rest on
*defeasible* empirical arguments: evidence can be undermined, inference rules
undercut, conclusions rebutted, sometimes by the same artifact's own
limitations section. Today that support structure lives in prose, so nothing
can check it, diff it, or replay it — and as more research is produced by LLM
agents, the gap between "claims made" and "claims whose support anyone can
audit" widens.

LARA makes the support structure explicit, typed, and replayable. An untrusted
producer (human or LLM) submits a program; a small trusted checker validates
it. The checker does not establish empirical truth — it establishes that the
argument is well formed, complete relative to the declared policy, and yields
the reported status ([spec §1](docs/spec.md)). When claims, evidence, and dead
ends are explicit objects, the *support* of each claim becomes something a
small trusted kernel can type, compile, and audit — that is how research
knowledge compounds.

## Example

The paper's running example, abridged from
[`examples/running-example/run2/example.lara`](examples/running-example/run2/example.lara)
(CI checks the full version byte-for-byte against its committed verdict). A
paper's headline claim is supported by a controlled experiment — and attacked
by the paper's own limitations section:

```text
artifact paper_17 at sha256:aaaa...
policy empirical-v1
use backends [nd@1]

claim c1
  nl      = "Method M improves accuracy on distribution D"
  formal  = improves(M, accuracy, D)
  binding = { author = alice, audit-status = reviewed }

leaf e1 : reports(exp_3, effect(M, accuracy, D, positive))
  kind       = observed
  provenance = ai-executed
  refs       = [evidence/table_2.csv#row=mean]

# The paper's own limitations section, recorded as evidence.
leaf e4 : distribution_shift(M, accuracy, D)
  kind       = attested
  provenance = user
  refs       = [paper_17.pdf#sec=7-limitations]

# (leaves e2, e3, e6 — the critical-question discharges — elided)

# A defeasible step: the scheme's critical questions must each be
# discharged by a declared leaf, or reported as located holes.
arg a1 : supports(c1) by controlled_experiment(M, accuracy, D, exp_3)
  discharge randomization     with e2
  discharge adequate_power    with e3
  discharge external_validity with e6

# The limitations note lowers to an undercut on a1's rule application.
arg d1 : challenges(external_validity(a1)) by leaf(e4)
undercut d1 a1.rule

status c1
```

Check it:

```sh
cabal run lara -- check examples/running-example/run2/example.lara
```

The verdict is one S-expression carrying the replay identity, the grounded
labelling, and each requested status (wrapped here):

```text
(verdict (replay-id (core lara-core@0.2) (policy empirical-v1)
                    (backends (backend nd 1)) (theories) (artifact sha256:aaaa...))
  accept (labels (0 out) (1 in)) (edges (1 0))
  (statuses (status (atom improves (con M) (con accuracy) (con D)) defeated)))
```

`c1` is **defeated**: the undercut `d1` is *in* and puts `a1` *out* in the
grounded labelling. Run 1 of the same example
([`run1/`](examples/running-example/run1/)) omits the leaf that discharges
external validity: no complete support argument for `c1` can be declared, and
the verdict reports **gap** — honest incompleteness is a located, first-class
outcome, not a rejection.

### Strict steps and named certificate slots (`lara-syntax@0.6`)

Deductive sub-results — arithmetic re-checks, code inspections — enter as
*strict* steps carrying an opaque certificate that a registered backend
replays. From [`examples/S6/example.lara`](examples/S6/example.lara): the
`ord@1` backend re-checks `0.71 < 0.74` in exact arithmetic, and the
certificate cites its premise slots by the *leaf names* that fill them —
`(prem base_cell)`, not `(prem 0)` — the `lara-syntax@0.6` spelling, lowered
at elaboration to the byte-identical numeric payload:

```text
arg a1 : supports(c1) by lt_recheck from [base_cell, new_cell]
  assurance = cert(ord@1, sha256:ord-named-v1-theory-0, (ordcmp (prem base_cell) (prem new_cell)))
```

A name that resolves to no premise, or ambiguously, is a located elaboration
error — never a guess. `examples/S6/` is the standing byte-identity witness
for this lowering (its committed wire bytes are re-proved equal to the numeric
spelling's on every CI run); the feature is specified in
[grammar Appendix E](docs/lara-surface-grammar.md). For the interplay of
certified arithmetic with defeasible claims, see
[`examples/S4/`](examples/S4/) — the arithmetic survives while the claim it
serves is defeated.

More worked examples, each a self-contained directory with its surface
artifact, co-located policy, derived wire anchor, and expected verdict, are
indexed in [`examples/README.md`](examples/README.md). For a prose-first
reading, the demo write-ups reconstruct checked artifacts as a
[paper/review/rebuttal exchange](docs/demos/d1-rebuttal-replay.md),
[mechanical review comments](docs/demos/d2-mechanical-reviewer.md), and
[cross-paper abstract excerpts](docs/demos/d3-agreement-map.md).

## Quick start

Haskell checker (GHC + cabal via [ghcup](https://www.haskell.org/ghcup/);
developed on GHC 9.14.1 / cabal 3.16):

```sh
cabal build all                      # library + CLI
cabal run lara -- check <file.lara>  # check an artifact
cabal test                           # property suite
```

Lean mechanization (elan / lean / lake on `PATH`; toolchain pinned in
[`lean/lean-toolchain`](lean/lean-toolchain)):

```sh
cd lean && lake build
```

CI runs both, including the `AxCheck.lean` axiom audit, on every push.

## Documentation

| Document | What it covers |
| --- | --- |
| [`docs/spec.md`](docs/spec.md) | The **v0.1 language specification** (frozen at M1; current core `lara-core@0.2`): TCB, propositions and `nf`/`≡`, policies, strict backends, support-term and attack typing, compilation and grounded semantics, rejection classes |
| [`docs/lara-surface-grammar.md`](docs/lara-surface-grammar.md) | The `.lara` presentation syntax (current: **`lara-syntax@0.6`**), with per-version appendices — comparison blocks, value bindings, inferred instantiation, named certificate premise slots |
| [`docs/foundations.md`](docs/foundations.md) | The four lines of work LARA builds on: abstract and structured argumentation, argumentation schemes, proof-carrying code / LCF |
| [`docs/novelty-and-related-work.md`](docs/novelty-and-related-work.md) | The novelty claim and the delta table against prior art (Micropublications, AIF, EG-VAR, Pandžić, ASPIC+, Dung, PCC/FPC) |
| [`docs/claim-support-calculus-decision.md`](docs/claim-support-calculus-decision.md) | Why one unified support-term calculus (strict/defeasible as a rule mode) |
| [`docs/strict-backend-decision.md`](docs/strict-backend-decision.md) | The backend-parametric strict-certificate interface and its proof obligations |
| [`docs/substrate-decision.md`](docs/substrate-decision.md) | Why the core is Haskell and the front-end Python |
| [`docs/mechanization-plan.md`](docs/mechanization-plan.md), [`lean/README.md`](lean/README.md) | The Lean 4 development: what is mechanized, per-result pointers |
| [`docs/engineering-plan.md`](docs/engineering-plan.md), [`TODOS.md`](TODOS.md) | Milestone roadmap and the tracked follow-up items |
| [`m0/annotation-summary.md`](m0/annotation-summary.md) | The M0 semantic corpus study that froze the scheme vocabulary, leaf grain, adapter portfolio, and defeat conventions |
| [`examples/README.md`](examples/README.md) | Index of the worked examples (A/B, E-series, R-series, S-series, running example) |

## Repository layout

```
src/, app/, test/   Haskell: parser, elaborator, checker, compiler, grounded
                    evaluator, strict backends, CLI, property suites
lean/               Lean 4 mechanized reference semantics + second driver (spec §9)
examples/           worked .lara examples with co-located policies and verdicts
corpus-units/, fixtures/, measurements/   the frozen M5 evaluation corpus
docs/               spec, surface grammar, design decisions, plans, demos
m0/, corpus/        the M0 semantic corpus study and its sampled ARA corpus
ara/                this project's own Agent-Native Research Artifact
```

## Trust and status

The trusted computing base is deliberately small and enumerated in
[spec §1.1](docs/spec.md). Soundness is carried by the Lean proofs, not the
tests: each definition is ported to Lean 4 and proved as it freezes —
`sorry`-free, within the standard axiom trio — and the Haskell and Lean
drivers are differential-tested byte-for-byte on every example, corpus unit,
and generated mutant. Property, golden, mutation, and differential tests are
conformance evidence for the Haskell checker, never a substitute for the
theorems (spec §9).

Milestones M1–M5 are complete: the frozen core (`lara-core@0.2`), the
mechanized reference semantics, the production compiler/checker, the
walking-skeleton replay pipeline, and the deterministic evaluation corpus
(frozen at tag `m5-freeze-v4`: 504 generated mutants + 60 corpus units,
564/564 rejection-class matches, 564/564 cross-driver agreement, 60/60
replay). Current work is the paper package
([#60](https://github.com/EYH0602/lara/issues/60)); see
[`TODOS.md`](TODOS.md) for the tracked follow-ups.

## License

LARA is released under the [MIT license](LICENSE).
