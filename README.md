# LARA

[![CI](https://github.com/EYH0602/lara/actions/workflows/ci.yml/badge.svg)](https://github.com/EYH0602/lara/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)
[![spec](https://img.shields.io/badge/spec-v0.1%20frozen-brightgreen.svg)](docs/spec.md)

LARA is a small language of proof-carrying, policy-relative **claim support**.
It lowers a research artifact into a checkable **claim-support graph**: for each
claim it reports whether the argument from declared evidence is **justified**,
**gap**, **defeated**, or **contested** — and why. Acceptance is a certificate
check against a fixed policy, not a search for truth: every dependency, open
obligation, and attack is explicit, and the reported status is the grounded
result for the compiled graph.

The target domain is **research artifacts** — papers, agent-generated
experiment reports, [ARAs](https://github.com/ARA-Labs/Agent-Native-Research-Artifact) —
whose claims rest on *defeasible* empirical arguments: evidence can be
undermined, inference rules undercut, conclusions rebutted, sometimes by the
same artifact's own limitations sections. LARA makes that support structure
explicit, typed, and replayable. An untrusted producer (human or LLM) submits
a program; the small trusted checker validates it. The checker does not
establish empirical truth — it establishes that the argument is well formed,
complete relative to the declared policy, and yields the reported status
([spec §1](docs/spec.md)).

> "The format of research knowledge matters a lot more than you think —
> that is how knowledge compounds."

LARA is the checker side of that thesis: when claims, implementations, results,
and dead ends are explicit, the *support* of each claim becomes an object a
small trusted kernel can type, compile, and audit.

Features:

- **One calculus.** Every argument is a single syntactic category — the
  *support term* — and strict-vs-defeasible is a *rule mode*, not a separate
  logic ([design decision](docs/claim-support-calculus-decision.md)).
- **Pluggable strict certificates.** Strict steps carry an opaque certificate
  checked through a small versioned backend interface (`Lara.Strict`), with
  intuitionistic natural deduction as the implemented reference adapter
  (`Lara.Strict.ND`). The M0 corpus study sized the v0.1 adapter portfolio to
  arithmetic table-recheck + code-inspection checkers, with LP non-shipping
  ([spec §5](docs/spec.md), [design decision](docs/strict-backend-decision.md)).
- **Grounded argumentation semantics.** Typed positional attacks
  (rebut / undercut / undermine) compile, with subargument closure, to a Dung
  framework; a claim's status is its grounded labelling ([spec §7–§8](docs/spec.md)).
- **Small trusted core, mechanized metatheory.** The trusted computing base is
  enumerated in [spec §1.1](docs/spec.md); each definition is ported to Lean 4
  and proved the moment it freezes — `sorry`-free, within the standard axiom
  trio ([`lean/`](lean/README.md)).
- **Untrusted front-end.** A Python/LLM elaborator (a later milestone) only
  *proposes* certificates; the checker is the sole arbiter of structural
  validity ([design decision](docs/substrate-decision.md)).

## A taste of LARA

```text
artifact paper_17 at sha256:...
policy empirical-v1
use backends [nd@1]

claim c1
  nl      = "Method M improves accuracy on distribution D"
  formal  = improves(M, accuracy, D)
  binding = { author = alice, audit-status = reviewed }

leaf e1 : reports(exp_3, effect(M, accuracy, D, +2.1))
  kind       = observed
  provenance = ai-executed
  refs       = [evidence/table_2.csv#row=mean]

arg a1 : supports(c1) by controlled_comparison(e1)
  discharge randomization with e2
  discharge adequate_power with e3
  open external_validity as o1

arg d1 : challenges(external_validity(a1)) by distribution_shift(e4)
undercut d1 a1.rule

status c1
```

This program is intentionally incomplete: the checker reports the located open
obligation `o1` instead of silently accepting or rejecting. Complete worked
examples live in [`examples/`](examples/), answering the design question *"if
one paper cannot rebut itself, what is the unit of argumentation?"* (the
support term, not the paper):

Each example is a self-contained directory `examples/<NAME>/` holding the surface
artifact `example.lara`, its co-located policy, and the derived wire anchor
`example.core.sexp` (the byte-exact Haskell↔Lean differential target):

- [`A/example.lara`](examples/A/example.lara) — one paper attacks its own
  headline claim with all three attack kinds → **defeated**.
- [`B/example.lara`](examples/B/example.lara) — two papers with contrary
  conclusions, a mutual rebut 2-cycle → **contested** ×2, with no new calculus for
  corpus scale.
- [`A/empirical-v1.policy.lara`](examples/A/empirical-v1.policy.lara) — the shared
  trusted policy A, B, and the E-series check against (co-located in each dir).

For a prose-first reading, the demo write-ups reconstruct the checked artifacts
as a [paper/review/rebuttal exchange](docs/demos/d1-rebuttal-replay.md),
[mechanical review comments](docs/demos/d2-mechanical-reviewer.md), and four
[cross-paper abstract excerpts](docs/demos/d3-agreement-map.md) before mapping
them back to LARA.

`Lara.Examples` additionally transcribes real
[ARA-Demo](https://github.com/ARA-Labs/ARA-Demo) claims (nanoGPT-speedrun,
ARC-AGI-3 ls20) into hand-built `Program` values, and `Lara.Negatives` supplies
one minimal ill-formed program per rejection class with the located diagnostic
acceptance must produce.

## Theoretical foundations

LARA sits at the junction of four established lines of work:

- **Abstract argumentation** (Dung 1995) is the *semantic target*: a
  well-formed program compiles to a finite Dung framework, and a claim's
  status is derived from the grounded labelling — the least fixed point of the
  defense operator ([spec §8](docs/spec.md)).
- **Structured argumentation** (ASPIC+, Modgil–Prakken 2014) shapes the inside
  of arguments: strict and defeasible rules in one calculus, subargument
  closure under compilation, and the three attack kinds — rebut, undercut,
  undermine — realized as the three kinds of *positions* in a support term
  ([spec §6–§7](docs/spec.md)).
- **Argumentation schemes with critical questions** are the policy layer: a
  claim-support policy is a versioned vocabulary of inference schemes (the
  nine-family vocabulary was frozen against the M0 corpus) whose critical
  questions generate obligations that must be discharged or reported as
  located holes ([spec §4](docs/spec.md)).
- **Proof-carrying code and the LCF architecture** (Necula 1997; Milner) give
  the trust discipline: untrusted producers, opaque certificates, and a small
  checker whose sealed judgments are the only way to obtain acceptance —
  applied here to defeasible empirical claim support rather than machine
  proofs.

Justification logic (Artemov's LP) informed the early design and survives as a
non-shipping backend seed; factive logics in general are confined behind the
strict-backend interface rather than admitted into the source calculus. The
precise delta over each neighbor (Micropublications, AIF, EG-VAR, Pandžić,
ASPIC+, PCC) is recorded in
[`docs/novelty-and-related-work.md`](docs/novelty-and-related-work.md): LARA is
a proof-carrying *language* whose programs are typed claim-support
certificates, compiled into an argumentation framework with mechanized
accountability and status-preservation theorems.

## Building from source

### Haskell checker

Requires GHC + cabal (via [ghcup](https://www.haskell.org/ghcup/); developed on
GHC 9.14.1 / cabal 3.16):

```sh
cabal build all      # library + demo
cabal run lara       # run the LP-seed demo
cabal test           # run the property suite
```

### Lean mechanization

Requires elan / lean / lake on `PATH` (toolchain pinned in
[`lean/lean-toolchain`](lean/lean-toolchain)):

```sh
cd lean && lake build
```

CI runs both, including the `AxCheck.lean` axiom audit, on every push.

## Documentation

| Document | What it covers |
| --- | --- |
| [`docs/spec.md`](docs/spec.md) | The **v0.1 language specification** (frozen at M1): TCB, propositions and `nf`/`≡`, policies, strict backends, support-term and attack typing, compilation and grounded semantics, rejection classes |
| [`docs/claim-support-calculus-decision.md`](docs/claim-support-calculus-decision.md) | Why one unified support-term calculus (strict/defeasible as a rule mode) |
| [`docs/strict-backend-decision.md`](docs/strict-backend-decision.md) | The backend-parametric strict-certificate interface and its proof obligations |
| [`docs/substrate-decision.md`](docs/substrate-decision.md) | Why the core is Haskell and the front-end Python |
| [`docs/mechanization-plan.md`](docs/mechanization-plan.md), [`lean/README.md`](lean/README.md) | The Lean 4 development: what is mechanized, per-result pointers |
| [`docs/novelty-and-related-work.md`](docs/novelty-and-related-work.md) | The novelty claim and the delta table against prior art (Micropublications, AIF, EG-VAR, Pandžić, ASPIC+, Dung, PCC/FPC) |
| [`docs/engineering-plan.md`](docs/engineering-plan.md) | Milestone roadmap (M0–M5) |
| [`m0/annotation-summary.md`](m0/annotation-summary.md) | The M0 semantic corpus study that froze the scheme vocabulary, leaf grain, adapter portfolio, and defeat conventions |

## Repository layout

```
src/Lara/
  Prop.hs          ground propositions + trusted identity ≡ (nf p = nf q)   [frozen]
  Strict.hs        strict-backend seam: registry + sealed StrictJudgment    [frozen]
  Strict/ND.hs     reference ND adapter (→/⊥, de Bruijn certificates)       [frozen]
  Strict/ND/Internal.hs  unstable test escape hatch (raw AtomId)
  AST.hs           full claim-support language skeleton (spec §2–§8)        [data only]
  Examples.hs      worked ARA-Demo programs (justified / gap / defeated / contested)
  Negatives.hs     one minimal reject per spec rejection class (Axis A)
  Term.hs          LP justification terms  t ::= x | c | s·t | s+t | !t     [non-shipping seed]
  Formula.hs       LP formulas             F ::= p | ⊥ | F→G | t:F
  ConstantSpec.hs  LP constant specification + hypothesis context (leaf sources)
  Kernel.hs        sealed Judgment + the experimental LP t:F checker
app/Main.hs        LP demo: checks (c0 · x) : Q and sum-monotonicity end-to-end
test/PropSpec.hs   QuickCheck properties for Lara.Prop (≡ is a decidable equivalence, etc.)
test/StrictSpec.hs QuickCheck properties for the strict seam + ND adapter
test/Spec.hs       property-suite entry point
examples/          presentation-syntax worked examples (*.lara) + shared policy
lean/              Lean 4 mechanized reference semantics (spec §9)
m0/                semantic corpus study: sampling frame, annotations, coverage gate
corpus/            the sampled ARA corpus the M0 study annotates
docs/              spec.md + design decisions, plans, corpus map, novelty/related work
ara/               this project's own Agent-Native Research Artifact
```

## Trusted computing base

The acceptance verdict is only as good as the TCB, so the boundary is frozen and
enumerated ([spec §1.1](docs/spec.md)). Two pieces are implemented and frozen:

- **`Lara.Prop`** — ground propositions and the trusted identity `≡` as
  `nf p = nf q` (decidable, total, an equivalence; spec §9 result 11). Both
  `supports` and `contrary` matching reduce to it.
- **`Lara.Strict` / `Lara.Strict.ND`** — the strict-certificate seam and the
  required reference adapter. The seam is a closed backend registry behind a
  sealed `StrictJudgment` (LCF-style: the only way to obtain a judgment is to
  have a registered backend accept), and no backend formula or proof term ever
  re-enters the source language — the *factivity firewall*. The ND adapter
  checks intuitionistic natural deduction over `→`/`⊥` with de Bruijn
  certificates, encoding each source proposition as an opaque atom via the
  shared UTF-8 framed atom key of `nf p` (`encodeAtomKey . nf`, spec §5.1).

The rest of the Haskell is deliberately not trusted yet: **`Lara.AST`** is the
datatype skeleton for the whole language (spec §2–§8) with **no checking** —
the judgments, compilation, and grounded labelling land in `Lara.Check`,
`Lara.Compile`, `Lara.Grounded`. **`Lara.Term` / `Formula` / `ConstantSpec` /
`Kernel`** are a non-shipping LP adapter seed: the M0 corpus study found no
observed demand for LP (3 of 60 sampled claims, all speculative), so it stays a
registered-optional seed unless the flip criterion in spec §5.2 is met.

Soundness is carried by the Lean proofs, not the tests: property, golden,
mutation, and differential tests are conformance evidence for the Haskell
checker, never a substitute for the theorems (spec §9).

## Status

The implementation is complete through the M4 walking-skeleton milestone:

- **M1 — frozen core language.** The core is specified in
  [`docs/spec.md`](docs/spec.md); the `.lara` presentation frontend is
  `lara-syntax@0.4`. M1 froze `lara-core@0.1`; the current core is
  **`lara-core@0.2`**, which added the declared many-sorted proposition
  signature and made rejection class R2 executable (issue #89). That is the one
  amendment to the frozen core so far, and it widened a class no implementation
  had ever enforced.
- **M2 — mechanized reference core.** Lean proves the checker, compilation,
  grounded evaluation, strict-backend soundness/isolation, result-7 consistency,
  backend replacement (including constructive well-checkedness transport), the
  ND adapter, the presentation-codec round trip, and dependency accountability
  in both halves (result 3): the source-leaf inversion lemma and backend
  `certDeps` via the `Backend.uses` report laws.
- **M3 — production compiler/checker.** The Haskell parser, elaborator, checker,
  compiler, grounded evaluator, diagnostics, CLI, replay bundle, and canonical
  S-expression wire format are implemented and differential-tested byte-for-byte
  against the Lean driver.
- **M4 — walking skeleton.** The worked-example suite, untrusted deterministic
  elaborator, hermetic replay bundle, and strict `nd@1` certificate example run
  end to end without a hand-authored certificate step.

The next milestone is **M5 — evaluation corpus**. Before freezing evaluation
artifacts, the remaining spec-facing prerequisites are verdict-carried replay
identity ([#36](https://github.com/EYH0602/lara/issues/36)) and duplicate-report
groups/R9 checking ([#38](https://github.com/EYH0602/lara/issues/38)). See
[`TODOS.md`](TODOS.md) for the smaller language-cleanup items.

## License

LARA is released under the [MIT license](LICENSE).
