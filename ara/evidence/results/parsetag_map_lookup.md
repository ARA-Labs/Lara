# `parseTag` Map Lookup

## Result

Commit `a7b498a` replaces the 97-entry association-list scan in
`Lara.Wire.parseTag` with a top-level `Data.Map.Strict` table. The table remains
derived from `tagToString` over the complete bounded `Tag` range. An exhaustive
public-API property checks every reverse lookup and rejects duplicate spellings.
`Lara.Driver.tagToString_injective` proves the same invariant for the mirrored
Lean vocabulary.

## Performance (2026-08-17)

The same-session runs used Apple M5 Pro, 64 GB RAM, darwin/aarch64, GHC 9.14.1,
and Lean 4.32.0. Each `make bench` result is the median of five sections of 100
batched runs over 60 corpus units and a 564-record harness.

| Median | Association-list baseline | Map lookup | Change |
|---|---:|---:|---:|
| End-to-end | 1459.8 µs | 784.8 µs | -46.24% |
| Parse | 1264.0 µs | 581.2 µs | -54.02% |
| Check + render, pre-decoded | 192.8 µs | 203.5 µs | +5.55% |

The post-change run was repeated because check + render moved by more than a few
percent. The repeated medians were 784.8 µs end-to-end, 581.2 µs parse, and
203.5 µs check + render, close to the first post-change run (783.1, 580.2, and
204.2 µs). The generated `tables/performance.tex` records the repeated run.

The end-to-end improvement exceeded the plan's predicted band. A focused `-O2`
benchmark therefore timed both implementations in one executable over exactly
1052 head keywords from `corpus-units/fre/C01/unit.core.sexp`, using an `IORef`
seed and five sections of 300 runs. The association-list median was 233.56 µs;
the Map median was 38.733 µs, an 83.42% reduction. Absolute values differ from
the issue's earlier microbenchmark, but both measurements support the lookup
change as the source of the parse reduction.

The check + render path did not change in source. Its +5.55% movement is retained
as observed noise; this record makes no causal performance claim for that path.

## Correctness and Integration

- `make build`: Haskell and Lean drivers built successfully.
- `make test`: the complete Haskell unit and property suite passed.
- `scripts/differential.sh`: 581 positive cases passed with zero failures; 56
  negative cases passed with zero failures.
- `scripts/replay.sh bundles/walking-skeleton`: verdict bytes and exit code
  matched the frozen bundle.
- `make presentation-parity`: passed with 73 rows.
- [PR #117](https://github.com/ARA-Labs/lara/pull/117), hosted CI run
  `32107434809`: the Haskell build/test, replay, tamper, presentation parity,
  Haskell-Lean differential, and semantic admission differential gates passed;
  the Lean build and no-`sorry` standard-axiom audit also passed.
- The optimization commit's implementation boundary contained only
  `src/Lara/Wire.hs`, `test/WireSpec.hs`, and generated `tables/performance.tex`.
- A temporary mutation making `parseTag` always return `Nothing` caused the new
  exhaustive property to fail, confirming that the property detects a broken
  reverse table.
- The review follow-up independently counted 97 bounded Haskell tags, built
  `Lara.Driver`, and found no axioms in `tagToString_injective`. It did not
  repeat the behavioral suites or performance experiment because the follow-up
  changes only comments, evidence records, and the Lean invariant.

The Haskell-Lean differential is the independent semantic oracle, so a separate
old-Haskell-versus-new-Haskell fixture run was unnecessary. The focused
microbenchmark still compares the previous and current lookup algorithms in the
same executable.
