# Evidence Index

## What the evidence layer is for this artifact

LARA is a **language-design / type-theory** contribution, not an experimental empirical paper, and
benchmarking is out of scope for the first submission (claim C10, decision N13). The source therefore
carries **no numbered tables or figures** — there is nothing to transcribe as `tables/` or `figures/`,
and no such objects are omitted.

Instead, per the project's own decision, the empirical signal that grounds each design claim is:

1. **Mechanization status** — which of the 12 required metatheory results (spec §9) are paper-proved,
   sketched, mechanized, or still open. This is the primary "experiment."
2. **Checker test status** — the Haskell implementation's QuickCheck property results (the only code
   that exists so far is the `Lara.Prop` `nf`/`≡` carve-out plus the LP adapter seed).
3. **Paper proofs** — the metatheory theorems already written in the decision records.

## Status ledgers (the "experiments")
| File | Grounds | Description |
|------|---------|-------------|
| [status/mechanization_status.md](status/mechanization_status.md) | C01–C12 | The 12 required results (spec §9) × proof status — paper-proved / mechanized / open |
| [status/test_status.md](status/test_status.md) | C01 | Verbatim `cabal test` output: 14 properties pass (8 for `Lara.Prop`, 6 for the LP seed) |

## Run records
| File | Source | Claims | Description |
|------|--------|--------|-------------|
| [results/prop_layer.md](results/prop_layer.md) | `cabal build`/`cabal test` on `Lara.Prop` | C01 | Build + property-suite run record for carve-out layer 1 |

## Proofs
| File | Source | Claims | Description |
|------|--------|--------|-------------|
| [proofs/backend_replacement.md](proofs/backend_replacement.md) | strict-backend-decision §5 Thm 2 | C04 | Backend replacement preserves claim status (AF isomorphism + grounded-lfp invariance) |
| [proofs/nd_adapter_soundness.md](proofs/nd_adapter_soundness.md) | strict-backend-decision §5 Thm 4 + Lemma 5 | C03, C05 | Natural-deduction adapter soundness + dependency exactness |
| [proofs/nonfactivity_and_defeat.md](proofs/nonfactivity_and_defeat.md) | strict-backend-decision §5 Thm 3, §6 Prop 8 | C03, C06 | Source non-factivity + monotonic consequence cannot represent defeat |

## Tables
None — the source has no numbered tables (see above).

## Figures
None — the source has no numbered figures (see above). The one presentation-syntax listing in
spec §10 is a worked-example sketch, catalogued as worked example E3 in `docs/worked-examples-plan.md`,
not a data figure.
