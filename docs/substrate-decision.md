# Substrate decision: Haskell core + Python front-end

_Status: settled for Phases 0–2. Recorded 2026-07-20; strict-core description amended 2026-07-21 by
`strict-backend-decision.md`._

## Decision

- **Trusted core** (warrant checker, strict-backend registry and selected adapters,
  argumentation/defeat layer): **Haskell**.
- **Untrusted front-end** (LLM elaborator, LLM-as-judge, model-checker dispatch, reporting): **Python** (added at Phase 3).
- **Interface**: JSON over stdio. The language boundary *is* the trust boundary — Python emits
  warrant programs, opaque strict-certificate payloads, and leaf atoms; the Haskell checker decides
  validity. Nothing above the leaves runs Python.

## Why (evidence)

Five parallel research sweeps (proof-checker kernels, existing JL implementations, logical frameworks / dependent types, argumentation solvers, LLM autoformalization + model checking) converged on a two-language architecture split on the trust boundary.

1. **Greenfield.** The source calculus and strict-backend interface are new. The required
   natural-deduction adapter is small and direct. LP and an S4→LP realizer are optional adapters:
   realization theory is mature and constructive, but implementation is justified only if corpus
   evidence needs modal certificates.
2. **Kernel language.** Proof-engineering tradition leans OCaml (LCF lineage; HOL Light ≈ 400 LOC; sealed abstract `thm` type; strict evaluation). Haskell is a proven equal for a *de Bruijn–style* checker (Metamath's `hmm` ≈ 400 LOC). For **this** project Haskell edges OCaml on: existing author fluency (velocity on a research prototype), QuickCheck for the Phase-1 property tests, and GADT support for well-typed-by-construction certificate internals. Sealing checked results via hidden constructors is adequate for the production implementation, while the mechanized development supplies the metatheorem.
3. **Dependent types are off the production critical path.** The natural-deduction checker and
   backend interface are small explicit recursions. A dependently typed host is still appropriate
   for the separate mechanized reference semantics and backend-replacement theorem, but LARA's
   source language does not need dependent types.
4. **Defeat layer imposes nothing.** Grounded semantics is a ~50-line monotone least-fixpoint labelling (IN/OUT/UNDEC → justified/defeated/gap·contested); hand-rolled in the core language. External solvers (μ-toksia, ASPARTIX) matter only for the NP-hard semantics we don't need. `PyArg` (Python) is a reference oracle for the ASPIC+/ABA structured layer.
5. **Front-end must be Python.** Every mature autoformalization stack (LeanDojo, PyPantograph, Lean-Interact, nl2spec) and every model-checker CLI (NuSMV/nuXmv, CBMC, Kani) is Python-first and driven via subprocess + JSON, with typed structured output (Instructor/Pydantic) or grammar-constrained decoding (XGrammar) guaranteeing well-formed emitted terms.

## Flip criteria (to OCaml)

Switch the core to OCaml if we later decide to (a) model the kernel line-for-line on HOL Light, (b) treat strict-evaluation auditability as a hard requirement, or (c) commit early to the Twelf/LF metatheory path. Switching cost is low (ML is close to Haskell).

## First model-checker backends (TL-1)

Start with **NuSMV/nuXmv** (matches the NL→Kripke-model+LTL→certify precedent; single binary; auto counterexamples), then **CBMC** (`--json-ui`, Python-native tooling; also underpins Kani for Rust-level behavioral claims). Standing caveat: a model checker certifies the *formalization it is handed*, so the real risk is faithful NL→formal lowering, not the checking step — isolated by the two-axis eval.
