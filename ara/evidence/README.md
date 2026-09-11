# Evidence Index

## What the evidence layer is for this artifact

LARA is primarily a **language-design / type-theory** contribution. Mechanized
semantics and checker conformance remain the load-bearing evaluation, while the
generated production-checker table records secondary implementation performance.
The table is printed on demand by `make bench` and is not tracked in this
repository (it is valid only for the machine and commit that produced it); ARA
result records preserve the protocol, the measured numbers, and the claim
boundary.

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
| [results/map_bench_2026-09-11.md](results/map_bench_2026-09-11.md) | `make bench-map` at `ad513b5` (#319) | C56 (context) | First run of the committed map harness: shipped four-member map 2778.2 µs per full pass, 272.9 µs of it linking and the linked check |
| [results/executable_nd_adapter.md](results/executable_nd_adapter.md) | Lean/Haskell ND adapter gates | C03, C05 | Exact replay adequacy, proved Atom codec inverse, shared golden vectors, and full gate results |
| [results/strict_certificate_frontend.md](results/strict_certificate_frontend.md) | S1 `.lara` → elaborate → `nd@1` replay + both-driver differential | C03, C05 | Policy-carried theory and surface assurance reach an accepted, justified verdict; missing theory rejects R13 |
| [results/numeric_quarantine_parity.md](results/numeric_quarantine_parity.md) | Real Haskell/Lean drivers + full regression gates | C12, C25 | Shared `canonNum` closes false-justified numeric divergence; two blocked queries retain positional byte parity |
| [results/parsetag_map_lookup.md](results/parsetag_map_lookup.md) | Same-session `make bench`, focused old/new lookup benchmark, Haskell/Lean differential, replay | C32 | Map-backed tag dispatch cuts median parse latency while preserving the observed wire contract |
| [results/bytestring_wire_parser.md](results/bytestring_wire_parser.md) | Same-session `make bench` pair, verbatim reference-parser differential, Haskell/Lean differential, replay, frozen-hash re-check | C33 | A byte-sliced parser cursor with code-point columns cuts median parse latency again without moving any accepted input, rejected input, or located error position |

## Proofs
| File | Source | Claims | Description |
|------|--------|--------|-------------|
| [proofs/backend_replacement.md](proofs/backend_replacement.md) | strict-backend-decision §5 Thm 2 | C04 | Backend replacement preserves claim status (AF isomorphism + grounded-lfp invariance) |
| [proofs/nd_adapter_soundness.md](proofs/nd_adapter_soundness.md) | strict-backend-decision §5 Thm 4 + Lemma 5 | C03, C05 | Natural-deduction adapter soundness + dependency exactness |
| [proofs/nonfactivity_and_defeat.md](proofs/nonfactivity_and_defeat.md) | strict-backend-decision §5 Thm 3, §6 Prop 8 | C03, C06 | Source non-factivity + monotonic consequence cannot represent defeat |
| [proofs/quarantine_nonpromotion.md](proofs/quarantine_nonpromotion.md) | Production `checkUnit` + compact-to-declared AF embedding | C21, C25 | Checker-instantiated proof that evidence quarantine cannot manufacture an unqualified justified verdict |
| [proofs/pw0_outer_model.md](proofs/pw0_outer_model.md) | PW0 outer-model gate (#192), PR #221 | C47 | Frame + valuation over unchanged local judgments; the T7 pair where support transports and grounded status still flips |
| [proofs/pw_t6_transport.md](proofs/pw_t6_transport.md) | PW-T6 structural transport (#191), PR #223 | C48 | Exact checked-support transport across a structural bridge, obligations verbatim, with the checker-tied applicability judgment |
| [proofs/m4_contextual_adequacy.md](proofs/m4_contextual_adequacy.md) | Theory M4 Part A (#187), PR #218 | C49 | Contextual representation independence: a certificate relabel commutes with linking saturation, so backend replacement is a congruence over admissible contexts |
| [proofs/pw_t9_path_composition.md](proofs/pw_t9_path_composition.md) | PW-T9 exact structural-path composition (#190), PRs #233/#236 | C48 boundary, mechanization §11 | First-leg-first partial translation, composed structural bridges, arbitrary typed paths, direct/path triangles, explicit candidate-relation coherence, and checked positive/negative witnesses |
| [proofs/map_batch_link_321.md](proofs/map_batch_link_321.md) | Batch link mechanization (#321), commit `bf31acc` | C56 | `batch_checked`: the drivers' one-shot linked unit is accepted; `batch_atts_mem_iff_fold`/`batch_args_mem_iff_fold`: it equals the fold; `linkedUnitOf_checked`: applied to the Lean driver's own unit |
| [proofs/pw_t8_status_preservation.md](proofs/pw_t8_status_preservation.md) | PW-T8 conditional status preservation (#193), PR #240 | C50, C47/C48 boundary | Grounded status invariant under a total attack bisimulation; `StatusBridge` hypotheses at a structural bridge; T8 `status_transport`, its modal collapse, and composition along T9; T7 as a forward homomorphism that fails `matched`; all four statuses transported off the identity |

## Tables
The performance table is generated by `make bench` and printed rather than committed, so the durable record of any measured number is the result file that quotes it. [results/parsetag_map_lookup.md](results/parsetag_map_lookup.md) records the issue #114 same-session baseline, post-change run, focused old/new lookup comparison, and semantic gates.

[results/bytestring_wire_parser.md](results/bytestring_wire_parser.md) records the issue #115 same-session baseline and post-change run. That table was deliberately **not** regenerated for #115: the benchmark machine carried a load average of 3.0 to 4.4, inflating every row — including untouched ones — by roughly 1.4x, so regenerating it would have moved an evaluation number for reasons unrelated to the change. The then-committed table therefore stayed at the post-#114 numbers, stale in the conservative direction — the staleness that retired the committed table in favour of printing it on demand.

## Figures
None — the source has no numbered figures (see above). The one presentation-syntax listing in
spec §10 is a worked-example sketch, catalogued as worked example E3 in `docs/worked-examples-plan.md`,
not a data figure.

[proofs/m4_finite_extension_279.md](proofs/m4_finite_extension_279.md) records the finite realization and the unrestricted-extension counterexample correcting C53.

- [Backend mutation v6](results/backend_mutation_v6.md): #266 clean S2/S9 corpus refresh, additive deltas, and measured ablations.
