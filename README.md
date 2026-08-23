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
(CI checks the full version byte-for-byte against its committed verdict). One
artifact carries an empirical headline claim, an independently certified
arithmetic sub-result, and a limitations note that attacks its own headline:

```text
artifact paper_17 at sha256:aaaa...
policy empirical-v3
use backends [nd@1, ord@1]

let base_score = 0.71
let ours_score = 0.74

claim c1
  nl      = "Method M improves accuracy on distribution D"
  formal  = improves(M, accuracy, D)
  binding = { author = alice, audit-status = reviewed }

claim c2
  nl      = "The baseline accuracy {base_score} is strictly below {ours_score}"
  formal  = num_lt(base_score, ours_score)
  binding = { author = alice, audit-status = reviewed }

leaf base : reports(exp_3, score_cell(M0, accuracy, D, base_score))
  kind       = observed
  provenance = ai-executed
  refs       = [evidence/table_2.csv#row=base]

leaf ours : reports(exp_3, score_cell(M, accuracy, D, ours_score))
  kind       = observed
  provenance = ai-executed
  refs       = [evidence/table_2.csv#row=ours]

# The paper's own limitations section, recorded as evidence.
leaf e4 : distribution_shift(M, accuracy, D)
  kind       = attested
  provenance = user
  refs       = [paper_17.pdf#sec=7-limitations]

# (leaves e1, e2, e3, e6 — the effect observation and the three
#  critical-question discharges — elided; see the full file.)

# A strict step: the ord@1 backend re-checks 0.71 < 0.74 exactly. The
# certificate cites its premise slots by leaf NAME — `(prem base)`, not
# `(prem 0)` — and elaboration lowers the names to the byte-identical
# numeric payload (lara-syntax@0.6).
arg s1 : supports(c2) by lt_recheck from [base, ours]
  assurance = cert(ord@1, sha256:empv3-t0, (ordcmp (prem base) (prem ours)))

# A defeasible step: the scheme's critical questions must each be
# discharged by a declared leaf, or reported as located holes.
arg a1 : supports(c1) by controlled_experiment from [e1]
  discharge randomization     with e2
  discharge adequate_power    with e3
  discharge external_validity with e6

# The limitations note lowers to an undercut on a1's rule application.
arg d1 : challenges(external_validity(a1)) by leaf(e4)
undercut d1 a1.rule

status c1
status c2
```

Check it:

```sh
cabal run lara -- check examples/running-example/run2/example.lara
```

The verdict is one S-expression carrying the replay identity, the grounded
labelling, and each requested status (wrapped here):

```text
(verdict (replay-id (core lara-core@0.2) (policy empirical-v3)
                    (backends (backend nd 1) (backend ord 1))
                    (theories sha256:empv3-t0) (artifact sha256:aaaa...))
  accept (labels (0 in) (1 out) (2 in)) (edges (2 1))
  (statuses (status (atom improves (con M) (con accuracy) (con D)) defeated)
            (status (atom num_lt (num 0.71) (num 0.74)) justified)))
```

The certified arithmetic stands on its own (`c2` **justified**: `s1` is strict
and unattacked) while the empirical claim is defeated (`c1`: the undercut `d1`
is *in* and puts `a1` *out* in the grounded labelling). Run 1
of the same example ([`run1/`](examples/running-example/run1/)) omits the leaf
that discharges external validity: no complete support argument for `c1` can
be declared, and the verdict reports **gap** — honest incompleteness is a
located, first-class outcome, not a rejection.

A source name that resolves to no premise, or ambiguously, is a located
error — never a guess. Since `lara-syntax@0.7` that is one policy across all
three places an argument body names a source: inferred θ references,
certificate premise slots, and discharge targets ([grammar
Appendix F](docs/lara-surface-grammar.md)). The `lara-syntax@0.6` named-slot
spelling itself is specified in [grammar Appendix E](docs/lara-surface-grammar.md);
[`examples/S6/`](examples/S6/) is its standing byte-identity witness (the
committed wire bytes are re-proved equal to the numeric spelling's on every CI
run). Since `lara-syntax@0.8` a certificate may also cite the **premise label**
the rule declares for a slot ([grammar Appendix G](docs/lara-surface-grammar.md)),
which names the slot rather than the term filling it and so stays unambiguous
where a leaf name cannot — when one leaf feeds two premises;
[`examples/S7/`](examples/S7/) works that case. For a program where certified
arithmetic genuinely feeds a defeasible
claim — and survives while the claim it serves is defeated — see
[`examples/S4/`](examples/S4/).

Since `lara-syntax@0.9`, an `nd@1` certificate may also use named binders and
premise references while retaining the numeric de Bruijn kernel
([grammar Appendix H](docs/lara-surface-grammar.md));
[`examples/S8/`](examples/S8/) is the byte-identity witness. Formula annotations
remain `(atom KEY)` and source-proposition-to-key authoring is tracked by
[#144](https://github.com/ARA-Labs/lara/issues/144).

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
| [`docs/lara-surface-grammar.md`](docs/lara-surface-grammar.md) | The `.lara` presentation syntax (current: **`lara-syntax@0.9`**), with per-version appendices — comparison blocks, value bindings, inferred instantiation, named certificate premise slots, surface strictness, premise-label citation, and named `nd@1` proof terms |
| [`docs/foundations.md`](docs/foundations.md) | The four lines of work LARA builds on: abstract and structured argumentation, argumentation schemes, proof-carrying code / LCF |
| [`docs/novelty-and-related-work.md`](docs/novelty-and-related-work.md) | The novelty claim and the delta table against prior art (Micropublications, AIF, EG-VAR, Pandžić, ASPIC+, Dung, PCC/FPC) |
| [`docs/claim-support-calculus-decision.md`](docs/claim-support-calculus-decision.md) | Why one unified support-term calculus (strict/defeasible as a rule mode) |
| [`docs/strict-backend-decision.md`](docs/strict-backend-decision.md) | The backend-parametric strict-certificate interface and its proof obligations |
| [`docs/substrate-decision.md`](docs/substrate-decision.md) | Why the core is Haskell and the front-end Python |
| [`docs/mechanization-plan.md`](docs/mechanization-plan.md), [`lean/README.md`](lean/README.md) | The Lean 4 development: what is mechanized, per-result pointers |
| [`docs/engineering-plan.md`](docs/engineering-plan.md) | Milestone roadmap and the module dependency graph (open follow-ups are tracked as GitHub issues) |
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
([#60](https://github.com/EYH0602/lara/issues/60)); open follow-ups are tracked
as [GitHub issues](https://github.com/ARA-Labs/lara/issues).

## License

LARA is released under the [MIT license](LICENSE).
