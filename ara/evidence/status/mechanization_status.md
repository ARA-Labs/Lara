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
| 2 | Strict-backend isolation | paper-proved | C03 | Theorem 3 (non-factivity) by inversion; structural |
| 3 | Dependency accountability (`leaves(w)`, `certDeps`) | spec-only | C08 | inversion lemma stated (spec §6); `Lara.SupportTerm` corpus-gated |
| 4 | Compilation soundness + subargument closure | spec-only | C02 | the combinatorially fiddly one (positional attacks × closure) |
| 5 | Grounded determinism + termination | spec-only | C07 | fixed-point argument in spec §8; `Lara.Grounded` not built |
| 6 | **Status preservation (direct vs compiled)** | **open** | C08 | **UNPROVABLE as written — no direct semantics exists (N16); define before M1** |
| 7 | Rationality postulates (consistency under §8.1) | spec-only | C09 | Path-B validator stated; `Lara.Policy` early M3 target |
| 8 | Strict-certificate soundness | paper-proved | C03 | Theorem 1; excludes trusted-policy instances |
| 9 | Backend replacement | paper-proved | C04 | Theorem 2 (AF isomorphism + grounded-lfp invariance) |
| 10 | Reference ND adapter soundness + dependency exactness | paper-proved | C05 | Theorem 4 + Lemma 5, by induction |
| 11 | Support adequacy (`w supports c` = normalized identity) | **mechanized** (+implemented+tested) | C01 | `lean/Lara/Prop.lean`: `nf`/`≡`, equivalence laws, decidability, idempotence, no-reorder — no `sorry`, axioms `propext` only. Also `Lara.Prop` Haskell + 8 QuickCheck properties. |
| 12 | Codec round-trip to α-equivalent AST | spec-only | C12 | test-only (not a soundness result); codec not built |

**Summary**: 1 **mechanized** (result 11, in Lean 4); 4 paper-proved (2, 8, 9, 10); 6 spec-only (1, 3,
4, 5, 7, 12); 1 open (6). Result 11 is the mechanization warm-up (corpus-independent, frozen); the rest
of the mechanization starts at M1 freeze (docs/mechanization-plan.md §6). Core results 1–9 +
reference-adapter 10 must be mechanized for the paper (spec §9 closing note).

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
- Results 8/9/10 `paper-proved` but not mechanized → they stay on the M2 critical path; the paper's
  soundness claim is not artifact-checkable until mechanized (C10).
- Results 3/4/5/7 `spec-only` and corpus-gated (or compile-order-gated) → wait on M0 / M3.
