# Mechanization status ledger (the primary "experiment")

- **Source**: spec.md §9 (the 12 required results); docs/mechanization-plan.md §1 (the status table);
  docs/strict-backend-decision.md §5 (the paper proofs).
- **As of**: 2026-07-21.
- **Legend**: `paper-proved` = proof written in a decision record; `mechanized` = machine-checked in
  Lean/Rocq (none yet — mechanization gated to M1 freeze); `implemented+tested` = Haskell code + passing
  properties; `spec-only` = defined in the spec, no proof or code yet; `open` = not yet provable /
  definitionally incomplete.

## The 12 required results (spec §9) × status

| # | Result | Status | Grounds | Note |
|---|--------|--------|---------|------|
| 1 | Decidability of program + attack checking | spec-only | C02 | decidable functions defined; termination theorem pending mechanization |
| 2 | Strict-backend isolation | **mechanized** (+Haskell conformance) | C03 | Theorem 3 (non-factivity, the factivity firewall). `lean/Lara/Strict.lean`: `no_truth_projection` — no uniform map from a checked `StrictJudgment B` to premise-free truth `B.models [] (enc goal)` — proved via the reference ND witness `nd_nonfactive_witness` (the backend accepts `p ⊢ p` yet `⊨_ND p` fails under the all-false valuation), so it bites even against a factive backend; `nd_relative_not_absolute` pairs the relative-consequence projection (`strict_step_sound`) against the failure of absolute truth. No `sorry`, `propext` only. Also enforced structurally in both Haskell (sealed `StrictJudgment`, opaque `SExpr` cert, no backend formula exported) and Lean (`StrictJudgment` carries only source data). |
| 3 | Dependency accountability (`leaves(w)`, `certDeps`) | spec-only | C08 | inversion lemma stated (spec §6); `Lara.SupportTerm` corpus-gated |
| 4 | Compilation soundness + subargument closure | spec-only | C02 | the combinatorially fiddly one (positional attacks × closure) |
| 5 | Grounded determinism + termination | spec-only | C07 | fixed-point argument in spec §8; `Lara.Grounded` not built |
| 6 | **Status preservation (direct vs compiled)** | **open** | C08 | **UNPROVABLE as written — no direct semantics exists (N16); define before M1** |
| 7 | Rationality postulates (consistency under §8.1) | spec-only | C09 | Path-B validator stated; `Lara.Policy` early M3 target |
| 8 | Strict-certificate soundness | **mechanized** (+Haskell conformance) | C03 | Theorem 1, `lean/Lara/Strict.lean`: backend-as-structure carrying obligation 3 as a field; `strict_step_sound` is its projection (needs **no** axioms) and `ndBackend` discharges the field via `nd_sound`. Excludes trusted-policy instances. |
| 9 | Backend replacement | paper-proved | C04 | Theorem 2 (AF isomorphism + grounded-lfp invariance) |
| 10 | Reference ND adapter soundness + dependency exactness | **mechanized** (+Haskell conformance) | C05 | Theorem 4 + Lemma 5, `lean/Lara/ND.lean`: `nd_sound` (soundness by induction on typing), `nd_relevance` (only free slots matter — the exactness core), `fv_in_range` + `hyp_out_of_range_untypable` (Lemma 5 in-range half / out-of-range rejection). **Layer-C bridge**: `infer` (Lean port of the Haskell `inferType` algorithm) proved sound+complete for the `HasType` relation (`infer_iff`) and to return exactly `fv` (`infer_deps_eq_fv`), so the metatheory transfers to the *decision procedure*, not just the relation. No `sorry`, `propext`/`Quot.sound` only. Also `Lara.Strict.ND` Haskell + 7 QuickCheck properties. |
| 11 | Support adequacy (`w supports c` = normalized identity) | **mechanized** (+implemented+tested) | C01 | `lean/Lara/Prop.lean`: `nf`/`≡`, equivalence laws, decidability, idempotence, no-reorder — no `sorry`, axioms `propext` only. Also `Lara.Prop` Haskell + 8 QuickCheck properties. |
| 12 | Codec round-trip to α-equivalent AST | spec-only | C12 | test-only (not a soundness result); codec not built |

**Summary**: 4 **mechanized** in Lean 4 (results 2, 8, 10, 11 — the two frozen carve-outs plus the
factivity firewall); 1 paper-proved (9); 6 spec-only (1, 3, 4, 5, 7, 12); 1 open (6). Results
2/8/10/11 also carry Haskell + property-test conformance. Per the mechanization discipline
(CLAUDE.md), every frozen, corpus-independent result is mechanized as soon as its definitions land —
result 11 was the warm-up, carve-out 2 (results 8, 10) followed immediately, and result 2
(non-factivity) landed once the abstract `Backend`/`StrictJudgment` model existed to state it against.
The remaining core results (1, 3, 4, 5, 9) depend on corpus-gated or compile-gated definitions and
mechanize at/after M1 freeze (docs/mechanization-plan.md §6). Result 9 (backend replacement) stays
paper-proved pending the compiled AF layer.

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
- Result 6 `open` → the highest-priority pre-M1 action: define the direct source semantics (N16).
- Results 2/8/10 `mechanized` → the strict-backend soundness *and* isolation claims (Theorems 1, 3,
  4) are now artifact-checkable, not just paper proofs (C10). Result 9 `paper-proved` stays on the M2
  critical path until the compiled AF layer exists to state backend replacement against.
- Results 3/4/5/7 `spec-only` and corpus-gated (or compile-order-gated) → wait on M0 / M3.
