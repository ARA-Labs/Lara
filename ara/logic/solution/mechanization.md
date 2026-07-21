# Mechanization architecture (the "experiment" design)

_Source of truth: `docs/mechanization-plan.md`. Because LARA's contribution is a calculus, the
mechanization + test status IS the empirical signal that grounds design decisions — this file is the
method by which that signal is produced. The 12 required results are spec §9; their live status is
`evidence/status/mechanization_status.md`._

## 1. Why mechanization is the evaluation (not a nice-to-have)

Three deep-research findings (adversarially verified, E02) make mechanization load-bearing:

- Mechanized metatheory *can be* the entire evaluation for a language-semantics paper (Two
  Mechanisations of WebAssembly 1.0, FM 2021).
- **POPL artifact evaluation excludes non-mechanized (paper) proofs from review** — an un-mechanized
  soundness argument earns no artifact credit, so M2 stays on the critical path (C10).
- Artifact evaluation certifies reproducibility, not claim-support — a weak evaluation cannot be
  rescued by a badge.

Property tests are conformance evidence, not soundness (spec §9 closing note). The mechanized theorems
carry soundness; the tests cross-check the implementation against them.

## 2. Prover choice and gating

**Default Lean 4** (decide vs Rocq before M1 by collaborator expertise; open question §8 #8). Rationale:
Mathlib's order-theory/fixpoint and `Finset` machinery for result 5; Lean's `Decidable` typeclass makes
results 1/5/11 executable *and* proved-decidable in one artifact (the differential-testing anchor needs
this); reviewer familiarity. Do NOT start proving until M1 freezes the definitions — re-proving after
definition churn is the main way a mechanization track blows its schedule.

## 3. One shared core, two implementations, a differential anchor

The Haskell checker and the Lean model are **separate developments sharing one serialized first-order
core AST** (S-expressions on disk). Because the Lean definitions are executable (results 1/5/11 are
decidable), the Lean side runs, not just proves — so the same core programs + expected four-state
verdicts run through both and are compared. Design implication landing at M1: `Lara.SupportTerm`'s AST
must serialize losslessly into the Lean inductive from day one; the S-expr codec *is* the anchor, not a
convenience layer.

**Framing** (C12): frame the Haskell↔Lean cross-check as **JEST-style N+1** (the reference is one
fallible oracle among N; a divergence indicts either side; finding a Lean-model bug is a legitimate
result) — NOT Csmith-style oracle-free voting. LARA's grounded status is deterministic (C07), so the
single-interpretation precondition holds by construction. Executable-oracle-from-mechanized-semantics
has precedent (Marmsoler–Brucker code-generate a Haskell oracle from an Isabelle Solidity semantics).

## 4. Per-result proof recipes

- **Result 5 (grounded lfp)** — define `D_AF` on `Finset Args`, prove monotone, compute the lfp by
  bounded iteration from ∅ with fuel `|Args|`; determinism/termination immediate; executable.
- **Results 8 + 10 (strict / ND soundness)** — make the backend a *structure carrying its soundness
  obligation as a field*; result 8 is one line per accepted instance; the ND adapter is an `instance`
  whose obligation is discharged by induction on the typing derivation.
- **Result 9 (backend replacement)** — parametricity over the `Backend` structure + graph isomorphism
  under `eraseCert` + lfp invariance.
- **Result 4 (compilation soundness + subargument closure)** — mechanize `w@π` as a partial subterm
  lookup; prove every compiled edge has a typed source and closure adds edges only onto arguments
  containing the attacked occurrence.
- **Result 7 (consistency, Path B)** — mechanize the compile-time strict-reachable validator; direct =
  indirect consistency by construction. Do NOT mechanize Path A unless the corpus forces the flip.

## 5. The result-6 gap (found this session; must close before M1 freeze)

Result 6 ("status preservation between a *direct source semantics* and the compiled-AF semantics") is
**currently unprovable as written**: spec §8 defines only the compiled route, so there is no
independent direct semantics to preserve. Action: define a direct big-step claim-status judgment
`Σ; Π; Γ; R ; W ⊢ p ⇓ status` *without* the Dung translation, then state result 6 as agreement with
`grounded(compile(W))`, and mechanize both. Alternative (weaker): reframe the compilation as *the*
definition and drop result 6 — this loses the "semantics-preserving compilation" headline, so the
direct-semantics route is preferred. Two other definitional holes must close for result 5's totality:
the hole-vs-complete-alternative case and `contested`-SCC provenance.

## 6. Sequencing and artifact hygiene

Mechanization starts at M1 freeze, parallel to the Haskell compiler (M3). The two carve-outs (`nf`/`≡`,
the ND adapter) may be *ported* to the prover early as a low-risk warm-up seeding results 10/11. The
proof development is anonymizable from day one; no `sorry`/`admit` in main theorems at M2 exit; a single
replay command checks the whole development; every prover axiom and backend assumption is recorded.
Differential + property + golden + mutation tests remain conformance evidence across the boundary.
