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
| 5 | Grounded determinism + termination | **mechanized** (core) | C07 | `lean/Lara/Grounded.lean`: grounded extension = bounded characteristic-operator iteration; `grounded_stable` proves the ascending chain reaches the least fixed point within `\|Args\|` steps (deficit measure + strict-filter-length), so the labelling is a total, deterministic function and aggregation (`statusC`) is total. Full compiled-AF construction (with concrete support terms) still M1-gated. |
| 6 | **Status preservation (direct vs compiled)** | **partially mechanized (abstract AF layer)** | C08 | **N16 partially resolved.** `lean/Lara/Grounded.lean` mechanizes the *abstract core*: over an arbitrary framework `F`, the declarative least-fixed-point grounded judgment (`DirectIn`/`DirectOut`) equals the executable bounded-iteration labelling (`labelC`) — `directIn_iff`, `labelC_inn/out/undec_iff`, `status_preservation`. This closes N16's "no independent semantics exists" gap. **NOT yet proven:** the source-vs-compiled preservation itself — every equivalence theorem quantifies over a single `F : AF` and `statusDirect`/`statusC` read the *same* `F.attack`, so `compile : Source → AF` and its subargument closure are only *defined and characterized* (`compile_attack_iff`), never *exercised*. Instantiating at `F := compile W` with a source-level status and proving preservation over the closure edges is M1 work. No `sorry`, trio axioms only. |
| 7 | Rationality postulates (consistency under §8.1) | spec-only | C09 | Path-B validator stated; `Lara.Policy` early M3 target |
| 8 | Strict-certificate soundness | **mechanized** (+Haskell conformance) | C03 | Theorem 1, `lean/Lara/Strict.lean`: backend-as-structure carrying obligation 3 as a field; `strict_step_sound` is its projection (needs **no** axioms) and `ndBackend` discharges the field via `nd_sound`. Excludes trusted-policy instances. |
| 9 | Backend replacement | paper-proved | C04 | Theorem 2 (AF isomorphism + grounded-lfp invariance) |
| 10 | Reference ND adapter soundness + dependency exactness | **mechanized** (+Haskell conformance) | C05 | Theorem 4 + Lemma 5, `lean/Lara/ND.lean`: `nd_sound` (soundness by induction on typing), `nd_relevance` (only free slots matter — the exactness core), `fv_in_range` + `hyp_out_of_range_untypable` (Lemma 5 in-range half / out-of-range rejection). **Layer-C bridge**: `infer` (Lean port of the Haskell `inferType` algorithm) proved sound+complete for the `HasType` relation (`infer_iff`) and to return exactly `fv` (`infer_deps_eq_fv`), so the metatheory transfers to the *decision procedure*, not just the relation. No `sorry`, `propext`/`Quot.sound` only. Also `Lara.Strict.ND` Haskell + 7 QuickCheck properties. |
| 11 | Support adequacy (`w supports c` = normalized identity) | **mechanized** (+implemented+tested) | C01 | `lean/Lara/Prop.lean`: `nf`/`≡`, equivalence laws, decidability, idempotence, no-reorder — no `sorry`, axioms `propext` only. Also `Lara.Prop` Haskell + 8 QuickCheck properties. |
| 12 | Codec round-trip to α-equivalent AST | spec-only | C12 | test-only (not a soundness result); codec not built |

**Summary**: 5 fully **mechanized** in Lean 4 (results 2, 5-core, 8, 10, 11 — the two frozen
carve-outs, the factivity firewall, and grounded determinism/termination) plus 1 **partially
mechanized** (result 6 — the abstract-AF-layer declarative-vs-executable grounded equivalence; the
compile step is defined/characterized but not exercised); 1 paper-proved (9); 4 spec-only (1, 3, 4,
12); 0 open. Results 2/8/10/11 also carry Haskell + property-test conformance; the whole-status layer
(5-core, 6) is a purely mechanized metatheory layer (its Haskell implementation is corpus-gated M3, so
no conformance counterpart exists yet). Per the mechanization discipline (CLAUDE.md), every frozen,
corpus-independent result is mechanized as soon as its definitions land — result 11 was the warm-up,
carve-out 2 (results 8, 10) followed, result 2 (non-factivity) landed once the abstract
`Backend`/`StrictJudgment` model existed, and results 5-core / 6-abstract landed once the direct
semantics was invented (N16) to state the equivalence against. The remaining core results (1, 3, 4)
depend on corpus-gated definitions and mechanize at/after M1 freeze (docs/mechanization-plan.md §6);
the full compiled-AF construction for results 4/5/6/9 (exercising `compile` over concrete support
terms) follows. Result 9 (backend replacement) stays paper-proved pending that layer.

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
- Result 6 `partially mechanized` → **N16 partially discharged.** An independent declarative grounded
  semantics (spec §8.2) exists and provably equals the executable labelling over any AF (C08), so the
  "no semantics to preserve" gap is closed at the abstract layer. The "semantics-preserving
  compilation" *headline* — source status = `grounded(compile(W))` exercising subargument closure — is
  **not** yet machine-checked (M1). N17: the "gap only on empty complete support" half is mechanized
  (`statusC_gap_iff`); the hole diagnostic and SCC provenance are modeled definitions.
- Results 2/8/10 `mechanized` → the strict-backend soundness *and* isolation claims (Theorems 1, 3,
  4) are now artifact-checkable, not just paper proofs (C10). Result 9 `paper-proved` stays on the M2
  critical path until the compiled AF layer exists to state backend replacement against.
- Results 3/4/7 `spec-only` and corpus-gated (or compile-order-gated) → wait on M0 / M3. Result 5's
  core (grounded termination/determinism) is mechanized abstractly; its full instance over concrete
  compiled support terms follows at M1.
