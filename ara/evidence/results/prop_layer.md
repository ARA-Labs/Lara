# Lara.Prop: build + property-suite run record

- **Trace node**: N10
- **Claim**: C01
- **Source**: `cabal build all` + `cabal test` on the LARA repo, GHC 9.14.1 / cabal 3.16.1.0.

| run | target | result | detail |
|-----|--------|--------|--------|
| build | `cabal build all` | OK | library + demo compile clean (`-Wall`, no warnings in `Lara.Prop`) |
| test  | `cabal test` (PropSpec) | PASS | 8/8 `Lara.Prop` properties, 100 cases each |
| test  | `cabal test` (Spec, LP seed) | PASS | 6/6 LP-seed properties, 100 cases each |

## Module under test

`src/Lara/Prop.hs` (162 lines) — transcribed to `src/execution/Prop.hs`. Exposes `Term`, `Prop`, `nf`,
`nfTerm`, `(===)`/`equiv`, `canonNum`, `prettyProp`, `prettyTerm`. `canonId = id` with Unicode NFC
flagged as the single deferred TCB-extension point.

## Interpretation

This is the only checker layer with running code; it grounds C01's claim that `nf`/`≡` is a "trivial
addition to the TCB" — the equivalence laws, idempotence, no-reorder, and literal-canonicalization all
hold under QuickCheck. It also realizes spec §9 result 11 (support adequacy) at the identity level.
Everything above this layer (`Strict`, `Policy`, `SupportTerm`, `Attack`, `Compile`, `Grounded`, codec,
parser, elaborator) is spec-only; see `evidence/status/mechanization_status.md`.

Verbatim runner output: `evidence/status/test_status.md`.
