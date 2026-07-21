# lara

A language for typed, policy-relative research warrants with pluggable strict certificates and
grounded argumentation semantics.

`lara` lowers a research artifact into a checkable **warrant graph**: for each
claim it computes whether the argument from declared evidence to the claim is
*justified / gap / defeated / contested*, and why. Strict steps use a small
backend interface with a natural-deduction reference adapter; LP is optional.
A non-monotonic argumentation layer handles global defeat. An untrusted LLM
front-end (added later, in Python) proposes certificates; the checker is the
sole arbiter of structural validity.

See [`docs/substrate-decision.md`](docs/substrate-decision.md) for why the core
is Haskell and the front-end Python, and [`docs/spec.md`](docs/spec.md) for the
core calculus.

## Layout

```
src/Lara/              current experimental LP adapter seed
  Term.hs          justification terms  t ::= x | c | s·t | s+t | !t
  Formula.hs       formulas             F ::= p | ⊥ | F→G | t:F
  ConstantSpec.hs  constant specification + hypothesis context (leaf sources)
  Kernel.hs        sealed Judgment + the experimental t:F checker
app/Main.hs        demo: checks (c0 · x) : Q end-to-end
test/Spec.hs       QuickCheck properties (eval axis (a): deterministic correctness)
docs/              substrate-decision.md, spec.md
```

`Lara.Kernel` is an experimental LP adapter seed: `Judgment` has no exported
constructor, so ordinary clients obtain one through `check`. Its result is
relative to the supplied `ConstantSpec` and `Context`. The current
`ConstantSpec` does not recognize fixed LP axiom schemas, so this code does not
yet satisfy the strict-backend contract and is not LARA's trusted core. The
backend registry, natural-deduction adapter, and full source calculus described
in `docs/spec.md` are not yet implemented.

## Build & test

Requires GHC + cabal (via [ghcup](https://www.haskell.org/ghcup/); developed on
GHC 9.14.1 / cabal 3.16).

```sh
cabal build all      # library + demo
cabal run lara       # run the demo
cabal test           # run the property suite
```

## Status

Phase 0/1 skeleton: the existing seed checks explicit LP derivations (Const,
Hyp, App, Sum-L/R, Check). Still to come: the strict-backend registry and
natural-deduction reference adapter, leaf interface and ARA→core mapping,
argumentation/defeat layer, and Python elaborator. An S4→LP realizer is built
only if corpus evidence justifies shipping the optional LP adapter. See
[`docs/strict-backend-decision.md`](docs/strict-backend-decision.md) and the
roadmap in `docs/engineering-plan.md`.
