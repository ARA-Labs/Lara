# Generated mutation suite (M5 tracker #48, T1)

GENERATED — do not edit. Regenerate with:

    cabal exec -- runghc scripts/gen-mutants.hs

Every file is derived from the committed worked-example anchors
(`examples/<NAME>/example.core.sexp`, bases: A B E1 E2 E3 E4 E5 S1)
by the seeded operators of `Lara.Mutate` (seed 20260801), verified
against the production checker at generation time, re-verified on every
`cabal test` run (`test/MutationSpec.hs`: specified outcomes, seeded
reproducibility, class coverage), and held byte-identical across the
Haskell and Lean drivers by `scripts/differential.sh` (`malformed/` is
the negative half: both drivers exit 2 with no verdict AND the
per-operator stderr diagnostic pinned in the manifest's last two
columns, so a deleted codec check cannot stay green via a different
downstream failure).

Total mutants: 148

| expected outcome | mutants |
| --- | --- |
| `accept-all-contested` | 4 |
| `codec-reject` | 45 |
| `reject-R1` | 20 |
| `reject-R10` | 8 |
| `reject-R11` | 7 |
| `reject-R12` | 8 |
| `reject-R13` | 17 |
| `reject-R3` | 7 |
| `reject-R4` | 6 |
| `reject-R5` | 6 |
| `reject-R6` | 6 |
| `reject-R7` | 7 |
| `reject-R9` | 7 |

| mutation family | mutants |
| --- | --- |
| `bad-attack-targets` | 15 |
| `certificate-tampering` | 24 |
| `codec-corruption` | 45 |
| `cycles` | 4 |
| `data-integrity` | 7 |
| `hidden-policy-extension` | 15 |
| `open-obligations` | 12 |
| `undeclared-leaves` | 13 |
| `wrong-formulas` | 13 |
