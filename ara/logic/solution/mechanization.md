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

**Lean 4 — resolved** (open question §8 #8 closed 2026-07-22 at the M1 pre-freeze, N38: host fixed
in spec §1.1 alongside the TCB enumeration). Rationale: Mathlib's order-theory/fixpoint and `Finset`
machinery for result 5; Lean's `Decidable` typeclass makes results 1/5/11 executable *and*
proved-decidable in one artifact (the differential-testing anchor needs this); reviewer familiarity;
and by resolution time three results were already mechanized in Lean. The "don't prove before M1
freezes" gate was refined at M1 into **port-as-we-lock** (N39): each definition ports the moment it
individually freezes — the §6.1 D⊎H defect is the evidence for why frozen-but-unmechanized
definitions shouldn't accumulate. (No Mathlib needed so far: the fixpoint core was done by hand in
core Lean 4.)

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
  under `eraseCert` + lfp invariance. Before the proof, extend `CheckedProgram` with stable argument
  identity and a certificate-erased skeleton/bijection; certificate-bearing `SupportTerm` equality
  cannot state the payload-varying node correspondence (O09).
- **Result 4 (compilation soundness + subargument closure)** — mechanize `w@π` as a partial subterm
  lookup; prove every compiled edge has a typed source and closure adds edges only onto arguments
  containing the attacked occurrence.
- **Result 7 (consistency, Path B)** — the compile-time strict-reachable validator is mechanized in
  `Lara.Policy` (`strictReachable_iff_mem`, `aPatMayOverlap_of_instances`, `wfB_iff`,
  `wellFormed_no_strict_contrary_left/right`). The executable judgment uses a conservative
  structural overlap relation rather than syntactic pattern equality, aligning it with
  instance-level `ContraryMatch` (N45). The direct/indirect consistency theorem next needs attack
  completeness from the executable checker; `CheckedProgram.typed` supplies only attack soundness
  (O10). Do NOT mechanize Path A unless the corpus forces the flip.

## 5. Result 6: source-to-compiled bridge mechanized modulo the edge decider

Result 6 ("status preservation between a *direct source semantics* and the compiled-AF semantics") is
no longer blocked on a missing direct semantics. `Lara.Compile.SrcIn`/`SrcOut`/`SrcStatus` read the
Prop-level source closure relation, and `srcIn_iff_grounded`/`srcStatus_iff` prove equality with
executable grounded evaluation under `Compile.Faithful`; `Lara.Examples.edgeBEx_faithful` exercises
a concrete strict-superset closure. The residual is constructive: the raw-source checker must build
the general Boolean edge decider and its `Faithful` proof once backend replay is decidable (O06/O08).

## 6. Sequencing and artifact hygiene

Mechanization starts at M1 freeze, parallel to the Haskell compiler (M3). The two carve-outs (`nf`/`≡`,
the ND adapter) may be *ported* to the prover early as a low-risk warm-up seeding results 10/11. The
proof development is anonymizable from day one; no `sorry`/`admit` in main theorems at M2 exit; a single
replay command checks the whole development; every prover axiom and backend assumption is recorded.
Differential + property + golden + mutation tests remain conformance evidence across the boundary.
