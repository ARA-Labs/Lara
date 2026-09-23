# Numeric quarantine parity

## Result

The Haskell and Lean production drivers now use the same numeric-literal identity
function. `lean/Lara/Prop.lean` ports Haskell `Lara.Prop.canonNum`, and
`Lara.Driver.dcanon` delegates to it.

The regression fixture
`fixtures/corpus/group-quarantine-numeric-multi-blocked.sexp` contains, for each
of two queried numeric claims, an attacked support with a non-canonical numeral
and an unattacked support with the canonical spelling. Under the former Lean
`canon = id`, only the unattacked support matched and Lean published
`justified`; under `canonNum`, both supports match and both queries are publicly
`evidence-blocked`. An ordinary query between them remains `justified`, pinning
the positional conditional projection.

## Verification (2026-08-05)

- Real Haskell CLI: accept with statuses `evidence-blocked`, `justified`,
  `evidence-blocked` and two ordered conditional `justified` entries.
- Real Lean CLI: byte-identical output.
- `cabal test all --test-show-details=direct`: PASS.
- `cd lean && lake build`: PASS.
- `cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh`: PASS.
- `scripts/differential.sh`: positive 436/436; negative 54/54.
