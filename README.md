# lara

A language to verify research claims with formal justification logic and neighborhood semantics.

`lara` lowers a research artifact into a checkable **warrant graph**: for each
claim it computes whether the argument from declared evidence to the claim is
*justified / gap / defeated / contested*, and why. The trusted core is a tiny
Logic-of-Proofs (LP) checker — it decides local validity of a justification
term `t : F` — wrapped by a non-monotonic argumentation layer for global defeat.
An untrusted LLM front-end (added later, in Python) produces candidate
derivations; the kernel is the sole arbiter of validity.

See [`docs/substrate-decision.md`](docs/substrate-decision.md) for why the core
is Haskell and the front-end Python, and [`docs/spec.md`](docs/spec.md) for the
core calculus.

## Layout

```
src/Lara/
  Term.hs          justification terms  t ::= x | c | s·t | s+t | !t
  Formula.hs       formulas             F ::= p | ⊥ | F→G | t:F
  ConstantSpec.hs  constant specification + hypothesis context (leaf sources)
  Kernel.hs        TRUSTED CORE: sealed Judgment + the t:F checker
app/Main.hs        demo: checks (c0 · x) : Q end-to-end
test/Spec.hs       QuickCheck properties (eval axis (a): deterministic correctness)
docs/              substrate-decision.md, spec.md
```

`Lara.Kernel` is the current strict-fragment checker: `Judgment` has no exported
constructor, so ordinary clients obtain one through `check`. Its result is
relative to the supplied `ConstantSpec` and `Context`. The current
`ConstantSpec` does not yet recognize fixed LP axiom schemas, so it remains
trusted input; the full LARA trusted boundary described in `docs/spec.md` is
not yet implemented.

## Build & test

Requires GHC + cabal (via [ghcup](https://www.haskell.org/ghcup/); developed on
GHC 9.14.1 / cabal 3.16).

```sh
cabal build all      # library + demo
cabal run lara       # run the demo
cabal test           # run the property suite
```

## Status

Phase 0/1 skeleton: the kernel checks explicit LP derivations (Const, Hyp, App,
Sum-L/R, Check) and the property suite covers sum-monotonicity, positive
introspection, and rejection of malformed derivations. Still to come: the
Phase-0 leaf-atom interface and ARA→core mapping, the S4→LP realizer, the
argumentation/defeat layer, and the Python elaborator. See the roadmap in
`../ARA-verification-plan.md`.
