# Contributing to LARA

This file is the short version of how changes are made and verified here; the
[README](README.md) covers what LARA is and how to use it.

## Development setup

Two toolchains:

- **Haskell** (checker, CLI, tests): GHC + cabal via
  [ghcup](https://www.haskell.org/ghcup/); developed on GHC 9.14.1 /
  cabal 3.16.
- **Lean 4** (mechanized reference semantics): [elan](https://github.com/leanprover/elan)
  with the toolchain pinned in [`lean/lean-toolchain`](lean/lean-toolchain).

```sh
cabal build all          # library + CLI
cabal test               # property + doctest suites
cd lean && lake build    # proofs
```

## Verification gates

The required `Haskell` CI workflow builds and tests the checker on every
push. The Lean side — the build, the `AxCheck.lean` axiom audit, and the
Haskell–Lean conformance gates — runs with `make lean-gate` and
`make cross-check`, and on a PR in the optional Lean workflow when a reviewer
adds the `lean` label ([scope decision](docs/ci-scope-decision.md)).

Before asking for review on any change that touches `lean/`, a wire contract,
or a golden either side emits, run:

```sh
make local-gates         # lean-gate + cross-check, in that order
```

On macOS this needs GNU sed and coreutils
(`brew install gnu-sed coreutils`) on `PATH` ahead of the BSD tools.

## How work is tracked

- Open work lives in [GitHub issues](https://github.com/ARA-Labs/Lara/issues).
  There is no in-repo backlog file; do not create one.
- [`docs/`](docs/README.md) records *decisions and contracts*: the frozen
  spec, decision records with status headers, and theory notes for mechanized
  results. When a change settles a design question, record it there.
- [`ara/`](ara/) is this project's own research artifact. A session that
  introduces or materially changes a feature, design, or theory — or runs or
  interprets an experiment — updates it; routine fixes, guidance, and review
  cycles do not.

## Code conventions

- Keep the compiler core symbolic: a fixed vocabulary is a closed sum type
  with one `toString`/`parse` table; a domain-meaningful identifier is its own
  newtype, one type per namespace; a value carrying a kernel invariant is
  built only through its sanctioned smart constructor. Plain `String` is
  correct only at the pre-parse wire boundary (`SExpr.SAtom`).
- Byte-exactness is a contract, not a nicety: goldens and cross-driver
  differentials compare bytes, so regenerate them deliberately, never
  casually.
- Module size is a guideline (a hint that a seam may have appeared), not a
  gate; see
  [docs/mutate-module-ownership-decision.md](docs/mutate-module-ownership-decision.md).
- Prefer boring code. Correctness first, then maintainability six months out.

## Mechanization

As soon as a definition freezes and is corpus-independent, port it to the
Lean development in `lean/` and prove its metatheory — do not batch provable
results for later. Every theorem must be covered by `lean/AxCheck.lean`, stay
`sorry`-free, and use only the standard axiom trio (`propext`,
`Classical.choice`, `Quot.sound`); `make lean-gate` audits all of this.
Haskell property tests are conformance evidence, never a substitute for the
theorems.

## Bug reports

Open an [issue](https://github.com/ARA-Labs/Lara/issues) with the `.lara`
file (or `.laramap`), the exact `lara` invocation, the verdict you got, and
what you expected. Include the commit you ran it on, and the `replay-id`
block from the verdict if you have one.
