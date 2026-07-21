---
title: "LARA: A Proof-Carrying Language for Typed, Policy-Relative Claim Support"
authors: ["yfhe"]
year: 2026
venue: "In preparation — target POPL 2028 (main-conference); see popl-research-review §1"
doi: "n/a — unpublished research artifact"
ara_version: "1.0"
domain: "Programming languages / type theory / formal methods (structured argumentation + proof-carrying certificates)"
keywords:
  - claim-support calculus
  - structured argumentation
  - Dung argumentation frameworks
  - grounded semantics
  - proof-carrying certificates
  - backend-parametric strict interface
  - non-monotonic defeat
  - mechanized metatheory
  - untrusted LLM producer
  - scientific claim verification
claims_summary:
  - "A claim is supported iff some checked support term's normalized conclusion is positionally identical to the claim's formal target — no entailment, no solver in the trusted base."
  - "The three ASPIC+ attack types (rebut/undercut/undermine) are exactly the three kinds of positions in a support term, so attack checking is subterm-occurrence lookup plus a contrary-relation check."
  - "Strict deductive steps factor through a backend-parametric certificate interface, so claim-support status is invariant under replacing one backend with another that accepts the same instances (backend replacement)."
  - "The evidence→claim step is defeasible and non-factive: adding a checked attacker can retract a claim's justified status, which no monotonic consequence relation can represent."
  - "For a language-design paper whose contribution is a calculus, the evaluation is mechanized metatheory + worked examples + rejection-class conformance, not benchmarks or user studies."
  - "Compile-time restriction of contrary relations off strict-reachable propositions (Path B) buys direct = indirect consistency by construction under grounded semantics."
abstract: "LARA is a small language of proof-carrying, policy-relative claim support. A program declares artifact-scoped propositions and evidence leaves, instances of strict or defeasible inference schemes, the obligations those instances generate, typed rebut/undercut/undermine relations, and claim roots whose status is requested. A checker validates a submitted certificate and compiles it into a finite Dung argumentation framework whose grounded labelling yields a replayable four-state claim status (justified / gap / defeated / contested). Acceptance means the argument is well-typed and undefeated relative to a versioned policy, admitted leaves, and selected backend theories — never that the claim is empirically true. Strict deductive steps factor through a backend-parametric certificate interface with a required intuitionistic natural-deduction reference adapter (Logic-of-Proofs is an optional adapter); the source calculus knows no backend's formulas or proof terms. An untrusted LLM front-end (added later, in Python) proposes certificates; the Haskell checker is the sole arbiter of structural validity. This artifact records the research trajectory that produced the frozen v0.1 calculus: the pivot from LP-realization-as-lowering-guarantee to a backend-parametric strict seam, the claim-support terminology settlement, the corpus-before-calculus build discipline, and — since the contribution is a calculus rather than an experiment — the use of mechanization and checker-test status as the empirical signal that grounds each design claim."
---

# LARA: A Proof-Carrying Language for Typed, Policy-Relative Claim Support

## Overview

LARA lowers a research artifact into a checkable **claim-support graph**: for each claim it computes
whether the argument from declared evidence to the claim is *justified / gap / defeated / contested*,
and why. It is a POPL-track **language-design / type-theory** contribution, not an experimental
empirical paper — so its "experiments" are **mechanization status** (which of the 12 required
metatheory results in the spec are paper-proved, sketched, mechanized, or still open) plus the
Haskell checker's property / golden / mutation test results. That status is the empirical signal that
grounds each design decision.

The technical contribution is threefold: (1) a typed claim-support **calculus** with
policy-generated critical-question obligations and typed positional attacks; (2) a
**semantics-preserving compilation** into a Dung framework with grounded four-state status; and
(3) **mechanized** accountability, backend-replacement, and status-preservation theorems over an
explicit leaf interface and a backend-parametric strict-certificate seam. The novelty is the checked,
defeasible, replayable claim-support certificate with *located* failure — not the act of formalizing
a claim (Micropublications, AIF, and EG-VAR already do that).

This artifact captures the project as of 2026-07-21: the calculus specification (`docs/spec.md`) is
frozen in the corpus-independent parts (proposition normalization `nf`/`≡`; the strict-backend
interface + natural-deduction adapter) and awaiting a semantic corpus study (M0) for the
corpus-gated parts. Only one carve-out layer is implemented (`Lara.Prop` = `nf`/`≡`, with 8 passing
QuickCheck properties); the rest of the checker is spec-only, and the existing LP code is an
experimental, non-conforming adapter seed.

## Layer Index

### Cognitive Layer (`/logic`)
| File | Description |
|------|-------------|
| [problem.md](logic/problem.md) | Observations (the trust gap in LLM-produced research claims) → gaps → key insight → assumptions |
| [claims.md](logic/claims.md) | 12 falsifiable claims (C01–C12): the calculus's design/metatheory claims, each grounded in mechanization/test status |
| [concepts.md](logic/concepts.md) | 12 core technical terms (claim-support term, positional attack, backend-parametric strict interface, grounded four-state status, …) |
| [experiments.md](logic/experiments.md) | 8 verification plans (E01–E08): mechanization obligations + checker conformance tests, directional only |
| [related_work.md](logic/related_work.md) | Typed dependency graph: Dung, ASPIC+, Pandžić, Micropublications, AIF, EG-VAR, PCC/FPC, DSP/Baldur/LeanDojo/Clover, Csmith/JEST |
| [solution/calculus.md](logic/solution/calculus.md) | The claim-support calculus: syntax, judgments, `nf`/`≡`, support terms, positional attacks, compilation, grounded aggregation |
| [solution/strict_backend.md](logic/solution/strict_backend.md) | The backend-parametric strict-certificate interface + the required natural-deduction reference adapter |
| [solution/mechanization.md](logic/solution/mechanization.md) | The mechanization architecture: Lean 4 default, shared-core differential testing, per-result proof recipes |
| [solution/constraints.md](logic/solution/constraints.md) | Boundary conditions, assumptions, known limitations (the three-way conditional guarantee) |

### Physical Layer (`/src`)
| File | Description | Claims |
|------|-------------|--------|
| [environment.md](src/environment.md) | GHC 9.14.1 / cabal 3.16, QuickCheck; the eventual Lean 4 + Python front-end | — |
| [artifacts.md](src/artifacts.md) | Pointer index to the repo codebase (Lara.Prop, the LP adapter seed, tests, spec, plans) | C01, C05 |
| [execution/Prop.hs](src/execution/Prop.hs) | Transcribed: the implemented `nf`/`≡` normalizer (carve-out layer 1) | C01 |
| [execution/Kernel.hs](src/execution/Kernel.hs) | Transcribed: the LP proof-term checker (non-conforming adapter seed) | C03 |
| `../lean/Lara/Prop.lean` | Lean 4 mechanization of `nf`/`≡` (spec §9 result 11): equivalence laws, decidability, idempotence, no-reorder — no `sorry`, axioms `propext` only | C01 |

### Exploration Graph (`/trace`)
| File | Description |
|------|-------------|
| [exploration_tree.yaml](trace/exploration_tree.yaml) | Research DAG: central questions, the LP→backend-parametric pivot, the terminology rename, the IR decision, the result-6 gap, the corpus-before-calculus constraint, and dead ends |

### Evidence (`/evidence`)
| File | Description |
|------|-------------|
| [README.md](evidence/README.md) | Index; explains that the source carries no numbered tables/figures and that the evidence layer is mechanization + test status |
| [status/mechanization_status.md](evidence/status/mechanization_status.md) | The 12 required results (spec §9) × proof status ledger — the primary "experiment" |
| [status/test_status.md](evidence/status/test_status.md) | Haskell checker test results: the 8 `nf`/`≡` properties + the LP-seed properties, verbatim runner output |
| [results/prop_layer.md](evidence/results/prop_layer.md) | Run record for the `Lara.Prop` build + property suite |
| [proofs/backend_replacement.md](evidence/proofs/backend_replacement.md) | Theorem 2 (backend replacement) — paper proof, from strict-backend-decision §5 |
| [proofs/nd_adapter_soundness.md](evidence/proofs/nd_adapter_soundness.md) | Theorem 4 + Lemma 5 (natural-deduction soundness + dependency exactness) |
| [proofs/nonfactivity_and_defeat.md](evidence/proofs/nonfactivity_and_defeat.md) | Theorem 3 (source non-factivity) + Prop 8 (monotonic consequence cannot represent defeat) |
