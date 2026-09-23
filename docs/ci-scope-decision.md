# Decision: what the required CI gates

_Records which checks run on every push and PR in GitHub Actions, which run only
on request, and why. The workflows are `Haskell` (`.github/workflows/haskell.yml`,
required) and `Lean` (`.github/workflows/lean.yml`, optional); the Makefile's
`lean-gate`, `cross-check` and `local-gates` targets are the local entry
points._

## The rule

**The required `Haskell` workflow gates the Haskell compiler only.** That is:
`cabal build`, `cabal test`, the Python unit tests, the ARA checks, the
walking-skeleton golden, replay and tamper gates, and the mutation-suite
freshness check. No step in it installs Lean or runs `lake`.

It was previously the two-job `CI` workflow (`ci.yml`). It is named for what it
gates, next to `Lean`, rather than for a step (`cabal build` undersells the ARA
and replay checks it also runs). The job name, `Haskell (cabal build + test)`,
is unchanged, so a branch-protection rule keyed on it still matches. Runs from
before the rename stay listed under `CI` in the Actions history, and
`scripts/bench_container.py` now looks up `Haskell` runs, so a SHA that only has
an old `CI` run needs a fresh run before a publication bench.

**Everything that needs a Lean build runs outside it:**

| Check | Local | On GitHub |
|---|---|---|
| `lake build`, PW example, `AxCheck.lean` axiom audit, semantics registry | `make lean-gate` | Lean workflow, when a reviewer adds the `lean` label to a PR (or `gh workflow run lean.yml --ref <branch>`) |
| Haskell-Lean cross-checks: presentation parity, surface conformance and its gate test, semantics / certDeps / update-matrix goldens, update differential, wire differential, admission differential, map conformance, PW conformance | `make cross-check` | not run |

`make local-gates` runs both.

## Why

The repository's focus is the compiler. The Lean development carries the
soundness argument, but whether a given PR needs it re-checked is a review
judgment: a PR that changes proofs, or one where review finds something that
should be mechanized, gets the `lean` label. Most PRs do neither, and paying for
a Lean build and the cross-checks on each of them spends Actions minutes on
checks whose outcome the change cannot affect.

Measured on 2026-09-12 by replaying every step of the previous `CI` workflow on a
local 128-core machine, cold build, GHC 9.6.6:

| Previous job | Total | Largest steps |
|---|---|---|
| Lean | 8.4 min | `lake build` 311 s, semantics registry check + tests 191 s |
| Haskell | 5.8 min | Haskell-Lean cross-checks 201 s, `cabal test` 69 s, `cabal build` 67 s |

On GitHub runners the previous workflow took a median 8.0 min wall clock over
its last 100 successful runs (both jobs in parallel), with the Haskell job also
building Lean for its cross-checks. Dropping every Lean-dependent step removes
the Lean install and build from the required job entirely, not only the
cross-check steps themselves.

## What this gives up, and the mitigation

Nothing on GitHub now checks, on every change, that the Haskell and Lean
implementations still agree. A gate that nothing runs drifts silently: when this
decision was taken, `make pw-conformance` was already failing on `main`, because
its fixture-ownership check had not been taught about `fixtures/pw/source/`
while CI was switched off.

The mitigation is procedural, not mechanical:

- A change that touches `lean/`, a wire or envelope contract, or any golden
  that either side emits runs `make local-gates` before review.
- A reviewer adds the `lean` label to a PR that changes proofs or should gain
  some; the Lean workflow then runs on it and on every later push.

## Rejected alternatives

- **Keep everything on every push.** The status quo; rejected for the cost
  above.
- **Heavy tier on a schedule (nightly or weekly).** Catches drift without a
  person remembering to, but still spends minutes on unchanged trees and
  reports failures detached from the PR that caused them. Can be revisited if
  drift of the kind above recurs.
- **Keep the cross-checks in the required job but drop the Lean job.** The
  cross-checks need a Lean build, so this keeps most of the cost.
