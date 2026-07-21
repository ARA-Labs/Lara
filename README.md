# lara

A language for typed, policy-relative claim-support certificates with pluggable strict certificates
and grounded argumentation semantics.

`lara` lowers a research artifact into a checkable **claim-support graph**: for each
claim it computes whether the argument from declared evidence to the claim is
*justified / gap / defeated / contested*, and why. Every argument is a single
syntactic category — a **support term** — and strict-vs-defeasible is a *rule mode*,
not a separate calculus. Strict steps carry an **opaque backend certificate**
checked through a small versioned backend interface (natural-deduction reference
adapter planned; an LP adapter is optional). A non-monotonic argumentation layer
compiles the terms and typed positional attacks (rebut / undercut / undermine) to a
Dung framework and reports the grounded status. An untrusted LLM front-end (added
later, in Python) proposes certificates; the checker is the sole arbiter of
structural validity.

See [`docs/spec.md`](docs/spec.md) for the core calculus,
[`docs/substrate-decision.md`](docs/substrate-decision.md) for why the core is
Haskell and the front-end Python,
[`docs/claim-support-calculus-decision.md`](docs/claim-support-calculus-decision.md)
for the unified support-term design, and
[`docs/strict-backend-decision.md`](docs/strict-backend-decision.md) for the
backend-parametric strict interface.

## Layout

```
src/Lara/
  Prop.hs          ground propositions + trusted identity ≡ (nf p = nf q)   [frozen]
  AST.hs           full claim-support language skeleton (spec §2–§8)        [data only]
  Examples.hs      worked ARA-Demo programs (justified / gap / defeated / contested)
  Negatives.hs     one minimal reject per spec rejection class (Axis A)
  Term.hs          LP justification terms  t ::= x | c | s·t | s+t | !t     [optional adapter seed]
  Formula.hs       LP formulas             F ::= p | ⊥ | F→G | t:F
  ConstantSpec.hs  LP constant specification + hypothesis context (leaf sources)
  Kernel.hs        sealed Judgment + the experimental LP t:F checker
app/Main.hs        LP demo: checks (c0 · x) : Q and sum-monotonicity end-to-end
test/PropSpec.hs   QuickCheck properties for Lara.Prop (≡ is a decidable equivalence, etc.)
test/Spec.hs       property-suite entry point
examples/          presentation-syntax worked examples (*.lara) + shared policy
lean/              Lean 4 mechanized reference semantics (spec §9)
docs/              spec.md + design decisions, plans, corpus map, novelty/related work
ara/               this project's own Agent-Native Research Artifact
```

### What is trusted vs. skeleton vs. optional

- **`Lara.Prop` is the one implemented piece of the trusted base.** It defines
  ground propositions and the trusted identity relation `≡` as `nf p = nf q`
  (literal canonicalization + structural recursion, no argument reordering). It is
  decidable, total, and an equivalence — and it is the frozen `nf`/`≡` carve-out
  (spec §9 result 11). Both `supports` (spec §3.1) and `contrary` matching (§4.1)
  reduce to it.
- **`Lara.AST` is the datatype skeleton for the whole language** (spec §2–§8):
  names, leaves, claims, policy rules, support terms, positional attacks, programs,
  and the four-state status. It transcribes the spec productions but implements
  **no checking** — the judgments, Dung-framework compilation, and grounded
  labelling land in later modules (`Lara.Check`, `Lara.Compile`, `Lara.Grounded`).
  `Lara.Examples` and `Lara.Negatives` are **data over these types**, so their
  designed statuses/diagnostics are recorded inline, not produced by a runner.
- **`Lara.Term` / `Formula` / `ConstantSpec` / `Kernel` are an optional LP strict-backend
  adapter seed** (spec §5.2). `Kernel.Judgment` has no exported constructor, so
  clients obtain one through `check`, relative to a supplied `ConstantSpec` and
  `Context`. This seed checks explicit LP derivations (Const, Hyp, App, Sum-L/R,
  Check) but does not yet recognize fixed LP axiom schemas, so it does **not** yet
  satisfy the strict-backend contract and is **not** LARA's trusted core. It ships
  only if corpus evidence justifies the optional LP adapter.

## Worked examples

`examples/` holds presentation-syntax (`*.lara`) programs answering the design
question *"if one paper cannot rebut itself, what is the unit of argumentation?"* —
the answer being the **support term**, not the paper:

- `A-self-defeating-paper.lara` — one paper attacks its own headline claim with all
  three attack kinds → **defeated**.
- `B-two-paper-contested.lara` — two papers with contrary conclusions, a mutual
  rebut 2-cycle → **contested** ×2, with no new calculus for corpus scale.
- `empirical-v1.policy.lara` — the shared trusted policy both check against.

`Lara.Examples` additionally transcribes real [ARA-Demo](https://github.com/ARA-Labs/ARA-Demo)
claims (nanoGPT-speedrun, ARC-AGI-3 ls20) into hand-built `Program` values, and
`Lara.Negatives` supplies one minimal ill-formed program per rejection class with
the located diagnostic acceptance must produce.

## Mechanization

`lean/` is the machine-checked companion to the Haskell checker (Lean 4, toolchain
pinned in `lean/lean-toolchain`). `Lara/Prop.lean` mechanizes spec §9 **result 11**
(the `nf`/`≡` support-adequacy carve-out): the equivalence laws, decidability,
idempotence, and no-argument-reordering, with no `sorry` and `propext` as the only
axiom. It mirrors `src/Lara/Prop.hs` and `test/PropSpec.hs`. Remaining results are
gated to the M1 freeze — see [`docs/mechanization-plan.md`](docs/mechanization-plan.md).

## Build & test

Haskell requires GHC + cabal (via [ghcup](https://www.haskell.org/ghcup/); developed
on GHC 9.14.1 / cabal 3.16).

```sh
cabal build all      # library + demo
cabal run lara       # run the LP-seed demo
cabal test           # run the property suite
```

The Lean development needs elan / lean / lake on `PATH`:

```sh
cd lean && lake build
```

## Status

Phase 0/1. **Frozen and mechanized:** the `Lara.Prop` trusted identity relation
(spec §9 result 11). **Data-only skeleton:** the full claim-support AST, worked
ARA-Demo examples, and rejection-class negatives. **Optional seed:** the LP adapter
that checks explicit LP derivations. **Still to come:** the strict-backend registry
and natural-deduction reference adapter, the checker / Dung-framework compilation /
grounded labelling (`Lara.Check`, `Lara.Compile`, `Lara.Grounded`), the leaf
interface and ARA→core mapping, and the Python elaborator. See the roadmap in
[`docs/engineering-plan.md`](docs/engineering-plan.md).
