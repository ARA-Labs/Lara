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

- [`A-self-defeating-paper.lara`](examples/A-self-defeating-paper.lara) — one
  paper attacks its own headline claim with all three attack kinds → **defeated**.
- [`B-two-paper-contested.lara`](examples/B-two-paper-contested.lara) — two
  papers with contrary conclusions, a mutual rebut 2-cycle → **contested** ×2,
  with no new calculus for corpus scale.
- [`empirical-v1.policy.lara`](examples/empirical-v1.policy.lara) — the shared
  trusted policy both check against.

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
  certificates, encoding each source proposition as an opaque atom via
  `show . nf` (spec §5.1).

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

M1 complete: the `lara-core@0.1` language is frozen in
[`docs/spec.md`](docs/spec.md). **Mechanized in Lean 4** (`lean/`, `sorry`-free,
standard axiom trio): results 2, 4, 5, 8, 10, and 11; the leaf half of result 3;
the relational/uniqueness half of result 1; the source-to-compiled bridge for
result 6 modulo the general executable edge decider; and the §8.1
strict-reachable/`wf(Pi)` validator underlying result 7. **Data-only skeleton:**
the full claim-support AST, worked ARA-Demo examples, and rejection-class
negatives. **Non-shipping seed:** the LP adapter that checks explicit LP
derivations (M0 measured no corpus demand; spec §5.2). **Still to come (Haskell
checker):** executable support/attack checking, Dung-framework compilation and
grounded labelling (`Lara.Check`, `Lara.Compile`, `Lara.Grounded`), the leaf
interface and ARA→core mapping, and the Python elaborator. See the roadmap in
[`docs/engineering-plan.md`](docs/engineering-plan.md).

## License

LARA is released under the [MIT license](LICENSE).
