# LARA

[![Haskell](https://github.com/ARA-Labs/Lara/actions/workflows/haskell.yml/badge.svg)](https://github.com/ARA-Labs/Lara/actions/workflows/haskell.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)
[![spec](https://img.shields.io/badge/spec-v0.1%20frozen-brightgreen.svg)](docs/spec.md)
[![arXiv](https://img.shields.io/badge/arXiv-2609.25421-b31b1b.svg)](https://arxiv.org/abs/2609.25421)

LARA is a small language for writing down the **argument behind a research
claim**: the evidence, the reasoning steps, and the caveats. A program can
then check the argument automatically.

Think of a proof assistant like Lean or Isabelle: you write a mathematical
proof in a formal language, and a small trusted checker confirms every step
follows the rules. LARA plays the same role for the arguments in empirical
research. Those arguments are a different kind of reasoning: evidence can be
undermined, conclusions can be rebutted, sometimes by the paper's own
limitations section. Math proofs are all-or-nothing; research arguments can be
strong, incomplete, or overturned, and LARA's verdicts reflect that. For each
claim the checker reports one of four statuses, and why:

- **justified** — the claim has a complete supporting argument that survives
  every declared attack;
- **gap** — the argument is incomplete, and the checker names exactly which
  piece is missing;
- **defeated** — an argument existed, but something also declared in the file
  knocks it down;
- **contested** — support and attack are in a standoff, so neither side wins.

In more technical terms: LARA is a proof-carrying, policy-relative calculus of
claim support. A LARA program lowers a research artifact into a checkable
claim-support graph; acceptance is a certificate check against a fixed policy,
and the reported status is the grounded result for the compiled graph
([spec](docs/spec.md)).

The language is described in
[*Beyond Natural Language: An Agent-Native Language for Autonomous Science*](https://arxiv.org/abs/2609.25421)
(arXiv:2609.25421); see [Citation](#citation) for the BibTeX entry.

## Why LARA

Behind a claim like "our method improves accuracy" sits a structure: an
experiment produced some numbers, the numbers support the claim through a
reasoning step ("we ran a controlled experiment"), and caveats may weaken it
("but we only tested on one dataset"). Today that structure lives in prose:
in papers, agent-generated experiment reports,
[ARAs](https://github.com/ARA-Labs/Agent-Native-Research-Artifact). A human
reviewer reconstructs it in their head, and no tool can check it, diff it, or
replay it. As more research is produced by LLM agents, the gap between "claims
made" and "claims whose support anyone can audit" widens.

LARA gives that structure a written, machine-readable form. In a `.lara` file
you declare:

- **Claims** — the statements the artifact makes, each in both natural
  language and a formal spelling.
- **Evidence** — the concrete facts you have, each pointing at its source
  (a CSV row, a section of a PDF).
- **Arguments** — which evidence supports which claim, and by what kind of
  reasoning.
- **Attacks** — things that undermine an argument, including the artifact's
  own limitations.

An untrusted producer (human or LLM) writes the file; a small trusted checker
validates it. Two things the checker deliberately does **not** do:

- **It does not judge whether the evidence is true.** If the file says "the
  experiment reported 0.74," LARA takes that as given, while recording where
  the number came from. What it checks is whether the argument built on the
  evidence is well formed, complete relative to the declared policy, and
  actually yields the reported status. It audits reasoning, not reality.
- **It does not search for missing pieces or guess.** Everything is what the
  producer wrote down; the value is that "what you wrote down" is now
  something a machine can check, and honest incompleteness (**gap**) is a
  located, first-class outcome rather than a rejection.

When claims, evidence, and dead ends are explicit objects, the *support* of
each claim becomes something a small trusted kernel can type, compile, and
audit. That is how research knowledge compounds.

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

# A strict step: the ord@1 backend re-checks 0.71 < 0.74 exactly,
# from a certificate that cites its premises by leaf name.
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

Arguments come in two strengths. A *defeasible* step like `a1` ("the
experiment suggests the method works") must answer every critical question its
reasoning scheme requires (was it randomized, was the sample adequate, does
it generalize), either with a declared piece of evidence or by admitting the
answer is missing. A *strict* step like `s1` ("0.71 is less than 0.74") must
instead carry a certificate that a small dedicated backend re-checks from
scratch: the checker does not trust the author's arithmetic, it redoes it.

Check the file:

```sh
cabal run lara -- check examples/running-example/run2/example.lara
```

The verdict is one S-expression carrying the replay identity (the exact
versions and hashes of everything involved, so anyone can re-run the check and
confirm the same result), the argument labelling, and each requested status
(wrapped here):

```text
(verdict (replay-id (core lara-core@0.2) (policy empirical-v3)
                    (backends (backend nd 1) (backend ord 1))
                    (theories sha256:empv3-t0) (artifact sha256:aaaa...))
  accept (labels (0 in) (1 out) (2 in)) (edges (2 1))
  (statuses (status (atom improves (con M) (con accuracy) (con D)) defeated)
            (status (atom num_lt (num 0.71) (num 0.74)) justified)))
```

The certified arithmetic stands on its own (`c2` **justified**: `s1` is strict
and unattacked) while the empirical claim is **defeated** (`c1`: the paper's
own limitations note, `d1`, undermines the experiment argument `a1` and
nothing knocks `d1` down). Run 1 of the same example
([`run1/`](examples/running-example/run1/)) omits the leaf that discharges
external validity: no complete support argument for `c1` can be declared, and
the verdict reports **gap**, naming the missing piece.

One artifact is one paper, and a **map** is several of them. A `.laramap`
manifest names independently authored, independently checkable `.lara` members
by path and alias; `lara check` on it rereads and rechecks every member, links
them into one framework, *generates* the cross-paper attacks their declared
contraries license, and prints one composite verdict with per-member claim
statuses. [`examples/agreement-map-multi/`](examples/agreement-map-multi/) is the
worked case — four "papers" that each stand alone as `justified`, two of which
become `contested` the moment they are read together, and two of which do not
because their experimental settings differ. No member declares an edge; none
could. The contract is in
[`docs/multi-artifact-composition-decision.md`](docs/multi-artifact-composition-decision.md).

More worked examples, each a self-contained directory with its surface
artifact, co-located policy, derived wire anchor, and expected verdict, are
indexed in [`examples/README.md`](examples/README.md). For a prose-first
reading, the demo write-ups reconstruct checked artifacts as a
[paper/review/rebuttal exchange](docs/demos/d1-rebuttal-replay.md),
[mechanical review comments](docs/demos/d2-mechanical-reviewer.md),
[cross-paper abstract excerpts](docs/demos/d3-agreement-map.md), a
[philosophy-of-mathematics debate](docs/demos/d4-philmath.md), and
[withdrawing an assumed axiom](docs/demos/d5-axiom-withdrawal.md).

## How checking works

`lara check` goes through four stages:

1. **Read and translate.** The human-friendly file is parsed and lowered
   (*elaborated*) into a small fixed core format. Every name must resolve to
   exactly one thing; a name that matches nothing, or matches two things, is a
   located error, never a guess.
2. **Check the pieces are well formed.** Each claim, leaf, and argument step
   is checked against the declared **policy**, the rulebook the artifact
   opts into. A policy lists the accepted reasoning schemes and, for each,
   the critical questions that must be answered before the reasoning counts.
   Strict steps have their certificates re-verified by the declared backends.
3. **Build the graph of attacks.** The checker assembles the whole argument:
   nodes are argument steps, edges are attacks (this limitations note
   undercuts that experiment's reasoning, this counter-evidence rebuts that
   conclusion). Attacks are computed from the formal content, not from prose:
   two statements clash only when the policy declares them contraries and
   they are about literally the same things.
4. **Settle who wins.** One fixed, deterministic rule (the *grounded
   semantics*) decides which arguments stand: an unattacked argument stands;
   an argument stands if every attack on it comes from an argument that has
   itself been knocked down; an unbreakable standoff leaves both sides
   unsettled. There is no judgment call: same file, same answer, every
   time, which is what makes verdicts replayable. Each claim then gets its
   status: justified, gap, defeated, or contested.

## More than one paper

The same machinery extends to a set of papers on one topic: write the rival
papers' claims, evidence, and arguments under one shared policy and check
whether they actually attack each other. Because attacks are computed from
formal content, LARA distinguishes a **genuine disagreement** (two papers
measured the same thing and concluded contraries, so both claims come out
contested) from an **apparent one** (the slogans contradict, but the
experiments measured different models, benchmarks, or settings, so no attack
forms, and the checker names the bridging experiment that would connect
them). The worked demo is the
[cross-paper agreement map](docs/demos/d3-agreement-map.md); for papers kept
in separate files, a `.laramap` composes them (see [Example](#example)).

## Quick start

Haskell checker (GHC + cabal via [ghcup](https://www.haskell.org/ghcup/);
developed on GHC 9.14.1 / cabal 3.16):

```sh
cabal build all                          # library + CLI
cabal run lara -- check <file.lara>      # check an artifact
cabal run lara -- check <file.laramap>   # check a map of several artifacts
cabal run lara -- deps <file.lara>       # what evidence an accepted artifact cites
cabal test                               # test suites (property + doctest)
```

`check` takes an optional `--out <path>`, which writes the verdict to a file
instead of stdout — atomically, and only when the check accepts, so a failed run
leaves the previous file intact. `make map-check` is the same thing for a map.

Lean mechanization (elan / lean / lake on `PATH`; toolchain pinned in
[`lean/lean-toolchain`](lean/lean-toolchain)):

```sh
cd lean && lake build
```

The required Haskell workflow gates the checker on every push. The Lean side — the build, the
`AxCheck.lean` axiom audit, and the Haskell-Lean conformance gates — runs with
`make lean-gate` and `make cross-check`, and on a PR in the optional Lean
workflow when a reviewer adds the `lean` label
([why](docs/ci-scope-decision.md)).

## Syntax versions

The `.lara` surface syntax is versioned (current: `lara-syntax@0.10`) and each
version's additions are specified as appendices of the
[surface grammar](docs/lara-surface-grammar.md). The invariant across all of
them: a source name that resolves to no target, or ambiguously, is a located
error, with one policy for inferred references, certificate premise slots,
and discharge targets alike (Appendix F). Certificates may cite premises by leaf
name (Appendix E; [`examples/S6/`](examples/S6/) is the standing
byte-identity witness) or by the rule's declared premise label, which stays
unambiguous when one leaf feeds two premises (Appendix G;
[`examples/S7/`](examples/S7/)). `nd@1` proof terms may use named binders over
the numeric de Bruijn kernel (Appendix H), and their formula annotations may
be authored as source propositions that the elaborator lowers to the frozen
atom encoding (Appendix I; [`examples/S8/`](examples/S8/)). For a program
where certified arithmetic genuinely feeds a defeasible claim — and survives
while the claim it serves is defeated — see [`examples/S4/`](examples/S4/).

## Documentation

Start with the [documentation index](docs/README.md) for reading paths and theory records.

| Document | What it covers |
| --- | --- |
| [`docs/spec.md`](docs/spec.md) | The **v0.1 language specification** (frozen; current core `lara-core@0.2`): TCB, propositions and `nf`/`≡`, policies, strict backends, support-term and attack typing, compilation and grounded semantics, rejection classes |
| [`docs/lara-surface-grammar.md`](docs/lara-surface-grammar.md) | The `.lara` presentation syntax (current: **`lara-syntax@0.10`**), with per-version appendices — comparison blocks, value bindings, inferred instantiation, named certificate premise slots, surface strictness, premise-label citation, named `nd@1` proof terms, and source-authored `nd@1` formula annotations |
| [`docs/foundations.md`](docs/foundations.md) | The four lines of work LARA builds on: abstract and structured argumentation, argumentation schemes, proof-carrying code / LCF |
| [`docs/novelty-and-related-work.md`](docs/novelty-and-related-work.md) | The novelty claim and the delta table against prior art (Micropublications, AIF, EG-VAR, Pandžić, ASPIC+, Dung, PCC/FPC) |
| [`docs/claim-support-calculus-decision.md`](docs/claim-support-calculus-decision.md) | Why one unified support-term calculus (strict/defeasible as a rule mode) |
| [`docs/strict-backend-decision.md`](docs/strict-backend-decision.md) | The backend-parametric strict-certificate interface and its proof obligations |
| [`docs/ord1-corpus-extension-decision.md`](docs/ord1-corpus-extension-decision.md), [`docs/insp1-code-inspection-decision.md`](docs/insp1-code-inspection-decision.md) | What an accepted `ord@1` / `insp@1` step certifies — and, for `insp@1`, why the closed-world step is the certified content and why its family needs a declared contrary pair |
| [`docs/multi-artifact-composition-decision.md`](docs/multi-artifact-composition-decision.md) | The `.laramap` **map**: what composing independently checkable artifacts means, the manifest and composite-verdict grammars, why a map is a recheck rather than a build, and what v1 refuses |
| [`docs/substrate-decision.md`](docs/substrate-decision.md) | Why the core is Haskell and the front-end Python |
| [`docs/mechanization-plan.md`](docs/mechanization-plan.md), [`lean/README.md`](lean/README.md) | The Lean 4 development: what is mechanized, per-result pointers |
| [`docs/performance.md`](docs/performance.md) | What the checker-performance bench measures, how to run it, and a dated snapshot (checking a corpus unit costs ~200 µs; one pass over all 564 harness records, under 200 ms) |
| [`docs/engineering-plan.md`](docs/engineering-plan.md) | The engineering plan: build order and the module dependency graph |
| [`m0/annotation-summary.md`](m0/annotation-summary.md) | The semantic corpus study that froze the scheme vocabulary, leaf grain, adapter portfolio, and defeat conventions |
| [`examples/README.md`](examples/README.md) | Index of the worked examples (A/B, E-series, R-series, S-series, running example, and the D3 agreement map in both its single-file and four-artifact forms) |

### Building the documentation

API documentation is generated, never committed. With the toolchains from
[Quick start](#quick-start) installed:

```sh
make docs           # both halves; each target prints where its index.html landed
make docs-haskell   # Haddock for the Haskell library, with hyperlinked source
make docs-lean      # doc-gen4 for the Lean development (lean/docbuild)
make doctest        # run the >>> examples in Haddock comments
```

The first `make docs-lean` clones doc-gen4 from GitHub and builds it, which
takes a few minutes; later runs are incremental. The doctest examples are a
cabal test-suite, so `make test` runs them too; a doctest run reconfigures the
library in interactive mode, so expect one extra configure step on the next
`cabal build`.

## Repository layout

```
src/, app/, test/   Haskell: parser, elaborator, checker, compiler, grounded
                    evaluator, strict backends, CLI, property suites
lean/               Lean 4 mechanized reference semantics + second driver (spec §9)
examples/           worked .lara examples with co-located policies and verdicts
corpus-units/, fixtures/, measurements/   the frozen evaluation corpus
scripts/            conformance gates, corpus/mutant generators, bench, replay
bundles/, elaborator/   replay bundles and the untrusted Python elaborator
containers/         pinned container for the performance bench
docs/               spec, surface grammar, design decisions, plans, demos
m0/, corpus/        the semantic corpus study and its sampled ARA corpus
ara/                this project's own Agent-Native Research Artifact
```

## Trust

The part of LARA you have to trust (the trusted computing base) is
deliberately small and enumerated in [spec §1.1](docs/spec.md). Soundness is
carried by the Lean proofs, not the tests: each definition is ported to Lean 4
and proved as it freezes, `sorry`-free and within the standard axiom trio, and
the Haskell and Lean drivers are differential-tested byte-for-byte on every
example, corpus unit, and generated mutant. Property, golden, mutation, and
differential tests are conformance evidence for the Haskell checker, never a
substitute for the theorems (spec §9). So the tool that judges arguments has
its own argument for correctness.

## Contributing

Issues and pull requests are both welcome. Read
[CONTRIBUTING.md](CONTRIBUTING.md) for the development setup, the verification
gates a change must pass before review, and how this repository splits work
between the [issue tracker](https://github.com/ARA-Labs/Lara/issues) and
`docs/`.

## Citation

LARA is described in
[*Beyond Natural Language: An Agent-Native Language for Autonomous Science*](https://arxiv.org/abs/2609.25421)
(arXiv:2609.25421). If you use it in your work, please cite:

```bibtex
@misc{he2026lara,
  title={Beyond Natural Language: An Agent-Native Language for Autonomous Science},
  author={Yifeng He and Jiachen Liu},
  year={2026},
  eprint={2609.25421},
  archivePrefix={arXiv},
  primaryClass={cs.PL},
  url={https://arxiv.org/abs/2609.25421}
}
```

GitHub's "Cite this repository" button exports the same reference from
[`CITATION.cff`](CITATION.cff).

## License

LARA is released under the [MIT license](LICENSE).
