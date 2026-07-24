# Mechanization status ledger (the primary "experiment")

- **Source**: spec.md §9 (the 12 required results); docs/mechanization-plan.md §1 (the status table);
  docs/strict-backend-decision.md §5 (the paper proofs).
- **As of**: 2026-07-24.
- **Legend**: `paper-proved` = proof written in a decision record; `mechanized` = machine-checked in
  Lean/Rocq (none yet — mechanization gated to M1 freeze); `implemented+tested` = Haskell code + passing
  properties; `spec-only` = defined in the spec, no proof or code yet; `open` = not yet provable /
  definitionally incomplete.

## The 12 required results (spec §9) × status

| # | Result | Status | Grounds | Note |
|---|--------|--------|---------|------|
| 1 | Decidability of program + attack checking | **partially mechanized (relational)** | C02 | `Lara.Support` proves typing uniqueness/invariants and `Lara.Attack` proves positional inversion; executable support/attack checkers still need decidable backend replay |
| 2 | Strict-backend isolation | **mechanized** (+Haskell conformance) | C03 | Theorem 3 (non-factivity, the factivity firewall). `lean/Lara/Strict.lean`: `no_truth_projection` — no uniform map from a checked `StrictJudgment B` to premise-free truth `B.models [] (enc goal)` — proved via the reference ND witness `nd_nonfactive_witness` (the backend accepts `p ⊢ p` yet `⊨_ND p` fails under the all-false valuation), so it bites even against a factive backend; `nd_relative_not_absolute` pairs the relative-consequence projection (`strict_step_sound`) against the failure of absolute truth. No `sorry`, `propext` only. Also enforced structurally in both Haskell (sealed `StrictJudgment`, opaque `SExpr` cert, no backend formula exported) and Lean (`StrictJudgment` carries only source data). |
| 3 | Dependency accountability (`leaves(w)`, `certDeps`) | **partially mechanized** | C08 | `Lara.Support.leaves_declared` proves the leaf half; `certDeps` awaits `Backend.uses` |
| 4 | Compilation soundness + subargument closure | **mechanized (relational)** | C02 | `Lara.Compile.compile_nodes_checked`, `edge_iff`, and `closure_includes_direct`; closed examples exercise direct and strict-superset closure |
| 5 | Grounded determinism + termination | **mechanized** (core) | C07 | `lean/Lara/Grounded.lean`: grounded extension = bounded characteristic-operator iteration; `grounded_stable` proves the ascending chain reaches the least fixed point within `\|Args\|` steps (deficit measure + strict-filter-length), so the labelling is a total, deterministic function and aggregation (`statusC`) is total. Full compiled-AF construction (with concrete support terms) still M1-gated. |
| 6 | **Status preservation (direct vs compiled)** | **mechanized modulo executable edge decider** | C08 | `Lara.Compile.srcIn_iff_grounded` and `srcStatus_iff` compose source status with grounded execution under `Faithful`; `Lara.Examples.edgeBEx_faithful` exercises one concrete closure. The general checker-built decider remains. |
| 7 | Rationality postulates (consistency under §8.1) | **validator mechanized** | C09 | `strictReachable_iff_mem`, `aPatMayOverlap_of_instances`, and `wfB_iff` prove exact decidable Path-B validation over conservative instance overlap; `wellFormed_no_strict_contrary_left/right` connect it to `ContraryMatch`, with an exact regression and located R12 payload. Status consistency awaits attack completeness (O10) |
| 8 | Strict-certificate soundness | **mechanized** (+Haskell conformance) | C03 | Theorem 1, `lean/Lara/Strict.lean`: backend-as-structure carrying obligation 3 as a field; `strict_step_sound` is its projection (needs **no** axioms) and `ndBackend` discharges the field via `nd_sound`. Excludes trusted-policy instances. |
| 9 | Backend replacement | paper-proved; statement-model blocker | C04 | Theorem 2 is written, but Lean `CheckedProgram` needs stable argument ids and `eraseCert` skeletons before payload-varying node bijection/isomorphism can be stated faithfully (O09) |
| 10 | Reference ND adapter soundness + dependency exactness | **mechanized** (+Haskell conformance) | C05 | Theorem 4 + Lemma 5, `lean/Lara/ND.lean`: `nd_sound` (soundness by induction on typing), `nd_relevance` (only free slots matter — the exactness core), `fv_in_range` + `hyp_out_of_range_untypable` (Lemma 5 in-range half / out-of-range rejection). **Layer-C bridge**: `infer` (Lean port of the Haskell `inferType` algorithm) proved sound+complete for the `HasType` relation (`infer_iff`) and to return exactly `fv` (`infer_deps_eq_fv`), so the metatheory transfers to the *decision procedure*, not just the relation. No `sorry`, `propext`/`Quot.sound` only. Also `Lara.Strict.ND` Haskell + 7 QuickCheck properties. |
| 11 | Support adequacy (`w supports c` = normalized identity) | **mechanized** (+implemented+tested) | C01 | `lean/Lara/Prop.lean`: `nf`/`≡`, equivalence laws, decidability, idempotence, no-reorder — no `sorry`, axioms `propext` only. Also `Lara.Prop` Haskell + 8 QuickCheck properties. |
| 12 | Codec round-trip to α-equivalent AST | spec-only | C12 | test-only (not a soundness result); codec not built |

**Summary**: results 2, 4 (relational), 5, 8, 10, and 11 are mechanized; result 6 is
source-to-compiled oracle-parametrically and has one constructive decider residual; results 1 and 3
have mechanized relational/leaf halves; result 7 has its exact executable instance-overlap validator;
result 9 remains
paper-proved with an explicit representation prerequisite; result 12 remains spec-only. Every theorem
is `sorry`-free and audited within the standard axiom trio. Haskell conformance still covers the
implemented lower layers with 22 property groups.

## Methodology grounding (C10, C11, C12 — from the deep-research pass, E02)

| Finding | Status | Grounds | Source |
|---------|--------|---------|--------|
| Mechanized metatheory can BE the evaluation | verified (3-0) | C10 | Two Mechanisations of WebAssembly 1.0, FM 2021 |
| POPL AEC excludes non-mechanized proofs from review | verified | C10 | POPL 2025 AEC page |
| AEC certifies reproducibility, not claim-support | verified (3-0) | C10 | SIGPLAN Checklist Manifesto 2019 |
| Untrusted-producer/checker judged by verified-success + adversarial zero-false-positive | verified (3-0) | C11 | DSP, Baldur, LeanDojo, Clover |
| Anti-memorization via novel-premises split | verified (3-0) | C11 | LeanDojo |
| Differential testing = N+1 (fallible oracle), not Csmith voting | verified (3-0 / 2-1 on Csmith framing) | C12 | JEST ICSE 2021; Csmith PLDI 2011 |
| Executable-oracle-from-mechanized-semantics has precedent | verified (3-0) | C12 | Marmsoler–Brucker TAP 2022 |

Deep-research run: 104 agents, 21 sources fetched, 95 claims extracted, 25 verified, 24 confirmed / 1
refuted. The refuted claim (useful): beating LLM baselines is NOT a required acceptance criterion for
the neural component (failed 1-2) — so LARA need not over-invest in baseline-beating for the producer.

## What this ledger drives (design decisions grounded by status)

- Result 11 `implemented+tested` → C01's "trivial TCB addition" is empirically grounded, so `nf`/`≡`
  is frozen and the carve-out can be ported to Lean early.
- Result 6 `mechanized modulo decider` → **N16 discharged semantically.** Source `SrcStatus` equals
  `grounded(toAF W edgeB)` whenever `Faithful` decides the frozen closure relation, and a concrete
  closure is exercised. The general raw-source checker still must construct that witness.
- Results 2/8/10 `mechanized` → the strict-backend soundness *and* isolation claims (Theorems 1, 3,
  4) are now artifact-checkable, not just paper proofs (C10). Result 9 `paper-proved` stays on the M2
  critical path until the compiled AF layer exists to state backend replacement against.
- Result 7's validator is now executable and proved exact; the status theorem waits on an explicit
  attack-completeness checker invariant. Result 9 waits on certificate-erased argument identity, not
  proof queue order.
