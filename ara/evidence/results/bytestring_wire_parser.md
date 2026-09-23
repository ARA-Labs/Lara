# `ByteString` Wire Parser

## Result

Commit `a2904d7` replaces the `String` (`[Char]`) S-expression reader in
`src/Lara/Wire.hs` with one over strict `ByteString`. `parseSExprBS` and
`decodeCheckInputFileBS` are the primitives; `parseSExpr` and
`decodeCheckInputFile` survive as thin `String` wrappers, so only the two paths
the performance table depends on move to `B.readFile` — `app/Main.hs` (the
shipped CLI) and `scripts/bench.hs`. `SExpr` is unchanged and still carries
`String` atoms.

The parser's win comes from `B.span`/`B.break` returning O(1) slices where the
`String` version walked and rebuilt the token, and from bulk whitespace and
comment skipping in place of one cursor step per character.

## The two decisions the issue asked to make explicitly

### Columns count code points, not bytes

`lean/Lara/Driver.lean:164-175` holds `PState.input : List Char` and advances
the column per `Char`. A byte-counting `ByteString` parser would disagree with
the reference driver on any error located after a multi-byte character on the
same line. `fixtures/corpus/strict-cert-unicode-theory.sexp` carries `é` inside
quoted atoms and is a live differential anchor, so this is not hypothetical.

`pCol` therefore counts UTF-8 non-continuation bytes. Bare atoms are ASCII by
construction — `isBareByte` mirrors `isBareChar` on `0x21..0x7e` minus
`();"\` — so they use `B.length` and skip the count entirely. Only quoted-atom
payloads and `;` comments go through the code-point-counting cursor bump, whose
line arithmetic is done in bulk with `B.elemIndexEnd` and `B.count`.

### Invalid UTF-8 becomes a located R14 codec error

Probed on `main` before any code was written, feeding a `.sexp` with a lone
`0xFF` byte inside a quoted atom to both drivers:

| Driver | Exit | Stdout | Stderr |
|---|---|---|---|
| Haskell CLI | 2 | empty | `lara: cannot read …: hGetContents: invalid argument (cannot decode byte sequence starting from 255)` |
| Lean driver | 2 | empty | `lara-driver: cannot read …` |

Both drivers already failed closed with the same outcome class, and neither
substituted U+FFFD. After the switch to `B.readFile` the Haskell side still
exits 2 with empty stdout, but the fault arrives as a located R14 codec error
through the same channel as every other codec fault rather than as an IO-level
read failure. No compared byte moves: `scripts/differential.sh` compares stdout
and exit code, and compares stderr only for the two pinned rejection classes and
the generated mutants, none of which is an invalid-UTF-8 input.

Quoted payloads decode through `Data.Text.Encoding.decodeUtf8'`, never
`decodeUtf8` (partial) and never `decodeUtf8Lenient`, which would make malformed
input accepted with substituted content — a fail-open change inside the trusted
base.

## Performance (2026-08-18)

The machine of record is Apple M5 Pro, 64 GB RAM, darwin/aarch64, GHC 9.14.1,
Lean 4.32.0. Each result is the median of five sections of 100 batched runs over
60 corpus units and a 564-record harness.

**The machine was not idle during this session.** Load average sat between 3.0
and 4.4 throughout, and every row — including rows this change cannot touch —
ran approximately 1.4 times the committed `0aa97ef` table. Those published
numbers are therefore not a valid comparator. What follows is the same-session
pair the protocol requires: both runs at `git_rev 1b2d245`, the same binaries,
a 120-second settle before the timed work, and the rebuild outside the timed
command.

| Median | `String` baseline | `ByteString` | Change |
|---|---:|---:|---:|
| End-to-end | 1115.5 µs | 747.2 µs | −33.0% |
| Parse | 813.0 µs | 442.8 µs | −45.5% |
| Check + render, pre-decoded | 300.0 µs | 309.6 µs | +3.2% |
| 564-record harness, one pass | 545.6 ms | 278.4 ms | −49.0% |

The parse reduction of 45.5% exceeds the plan's predicted 26–43% band and is
far above its 12% failed-hypothesis floor. The code-point counting cost less
than budgeted because the line arithmetic runs in bulk and bare atoms bypass it.

The parse to check + render ratio fell from 2.71× to 1.43×.

### The check + render movement is not attributable to this change

Check + render moved +3.2% on a path whose source was not edited. Because
`printSExpr` and `encodeVerdict` both live in `Lara.Wire` — the module this
change rewrites — "the source is untouched" does not by itself rule out a
codegen shift from recompiling a larger module. The movement was therefore
measured against a noise floor rather than assumed to be noise.

Four `make bench` runs, each the per-unit median over the same 60 corpus units,
two of the `String` binary and two of the `ByteString` binary:

| Run | kernel (check + render) | check | parse |
|---|---:|---:|---:|
| `String`, unsettled | 305.4 µs | 291.5 µs | 834.6 µs |
| `String`, settled (baseline of record) | 299.7 µs | 284.7 µs | 812.5 µs |
| `ByteString`, settled (run of record) | 309.4 µs | 297.0 µs | 441.7 µs |
| `ByteString`, repeat | 314.1 µs | 300.5 µs | 459.2 µs |

Per-unit median deltas:

| Comparison | kernel | check | parse |
|---|---:|---:|---:|
| Same `String` binary, run 1 → run 2 | −2.63% | −2.66% | −1.73% |
| Same `ByteString` binary, run 1 → run 2 | +2.51% | +1.48% | +3.78% |
| `String` → `ByteString` | +2.96% | +3.07% | −46.13% |
| `String` → `ByteString`, repeat run | +5.40% | +5.69% | −44.24% |

Three independent observations rule out a code attribution:

1. Two runs of an *identical* binary differ by 2.51% to 2.63% on the kernel
   row. The attributed effect, +2.96%, is the same magnitude as that floor.
2. `check_ns` tracks `kernel_ns` to within a few tenths of a percent in every
   comparison. `check_ns` times `checkUnitWith` and a derived `Show`, and runs
   no `Lara.Wire` code at all. A codegen shift from recompiling `Lara.Wire`
   would move the kernel row and leave `check` flat; it does not.
3. The movement is not fixed. The kernel median climbs monotonically with
   wall-clock time across the session — 299.7, then 309.4, then 314.1 µs —
   regardless of which binary is running, and the attributed effect inflates to
   +5.40% against the later repeat. A real code effect would be reproducible,
   not time-dependent.

This record therefore makes no causal performance claim for the check + render
path: the movement is ambient machine drift, measured rather than asserted.

The parse reduction is separated from that drift by roughly a factor of
eighteen. Its per-unit median is −46.13% with a range of −52.10% to −39.81%
and **0 of 60 units slower**, and it still measures −44.24% against the slowest
of the four runs.

An earlier baseline taken immediately after a full GHC rebuild read 1136.9,
834.8, and 305.4 µs against the settled baseline's 1115.5, 813.0, and 300.0 µs.
The two agree within 3%, so the ≈1.4× inflation relative to the committed table
is ambient machine load rather than a thermal artifact of the rebuild.

### `tables/performance.tex` was deliberately not regenerated

Under this load the untouched check + render row would move from the committed
203.5 µs to 309.6 µs — a 52% apparent regression that is purely machine state.
Committing that table would move an evaluation number for a reason unrelated to
the change, which is what the freeze protocol exists to prevent. The table needs
one `make bench` on an idle machine. The code change does not depend on it.

## Correctness and Integration

- `make test`: the complete Haskell unit and property suite passed, including
  six new properties.
- The previous `String` reader is copied verbatim into `test/WireSpec.hs` as
  `referenceParseSExpr`, because comparing `parseSExprBS` against `parseSExpr`
  would be tautological once the latter is a wrapper over the former. The
  assertion is equality of the parsed tree and, on failure, of the exact
  `ParseError` line, column, and message, over every committed `.sexp` under
  `fixtures/`, `corpus-units/`, `bundles/`, and `examples/` (581 files,
  malformed envelopes and generated codec mutants included); over `printSExpr`
  output of QuickCheck-generated `SExpr`s; and over QuickCheck-corrupted wire
  text — truncations, deletions, injected delimiters, escapes and multi-byte
  code points, a duplicated top-level form, a multi-byte comment prefix, and
  inputs straddling the `maxDepth` boundary — so the error paths are
  differentially covered, not only the happy path.
- Eleven exact `(line, column, message)` pins cover an error after a multi-byte
  character on the same line (byte columns would report 9 rather than 8), an
  error inside a quoted atom carrying `é`, end of input inside a multi-byte
  comment, a raw newline inside a quoted atom advancing the line, `show` of a
  non-ASCII code point in bare position, every escape fault, and the depth
  bound. `maxDepth = 10000` and its "R14, not stack overflow" contract are
  preserved and pinned both at the parser and at the `decodeCheckInputFileBS`
  boundary.
- `scripts/differential.sh`: 581 positive cases passed with zero failures; 56
  negative cases passed with zero failures.
  `fixtures/corpus/strict-cert-unicode-theory.sexp`, the code-point witness, is
  byte-identical on both drivers.
- `scripts/replay.sh bundles/walking-skeleton`: verdict bytes and exit code
  matched the frozen bundle.
- `make presentation-parity`: passed with 73 rows.
- `make measure`, then `cut -f1-14 measurements/report.tsv | shasum -a 256`:
  `eae0c82e8c1607a4daf74b8dfb8ecab333996f0e213bcbf22f9b81533add3d7a`, matching
  `docs/m5-freeze-checklist.md:194`. `shasum -a 256 measurements/ablation.tsv`:
  `23112189212d4e6e154fafa4a7a2d9425e9d77de2b228702f3bf52b29859cdc3`, also
  matching.
- The frozen hashes match by construction rather than by coincidence.
  `Lara.Measure` computes `detTotalBytes = length bytes` over a `String`, so
  that field counts code points despite its name and is `report.tsv` column 12,
  inside the hashed deterministic projection. Retaining the `String` wrapper
  meant `Lara.Measure`, `scripts/measure.hs`, both loaders,
  `scripts/gen-mutants.hs`, and all nine other test files that call
  `decodeCheckInputFile` compile untouched while still exercising the new parser
  through the wrapper.
- The implementation boundary was `src/Lara/Wire.hs`, `app/Main.hs`,
  `scripts/bench.hs`, `test/WireSpec.hs`, `lara.cabal`, and the plan.
  `lara.cabal` is the one file the plan did not anticipate: the `lara`
  executable had no `bytestring` dependency and now needs one.
- At commit `a2904d7`,
  hosted CI run `32226016340` at head `37781e9`: the Haskell job's build,
  test, presentation parity, replay, tamper, policy-copy authenticity,
  Haskell-Lean differential, and semantic admission differential gates
  passed; the Lean job's build and no-`sorry` standard-axiom audit also
  passed.

The Haskell–Lean differential remains the independent semantic oracle. The
verbatim reference-parser differential is the additional old-versus-new check
that the oracle alone cannot give, because the oracle pins stdout and exit code
but not codec error positions, which live only on stderr.

## Consequence for the table-claim audit

`src/evaluation.tex:77-79` claims decoding consumes "roughly seven eighths" of
end-to-end time. That sentence was written against a 1317 µs parse row. At a
parse to check + render ratio of 1.43×, parse is approximately 59% of end-to-end
rather than 87%, so the sentence is false by a wide margin. The table-claim audit closes as
option A — rewrite the paragraph around measured numbers — rather than option B,
which would have spent a sentence conceding the split is an engineering
artifact. The rewrite is gated on regenerating the table on an idle machine, not
on this change.
