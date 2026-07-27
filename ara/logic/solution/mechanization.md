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
- **Result 1 (checking decidability)** — done for the frozen checker surface:
  `Lara.Check.inferSupport`, `checkAttack`, and `checkProgram` execute and
  have exact relational soundness/completeness theorems. `checkProgram`
  constructs the proof-bearing compile boundary from raw declarations. This
  does not claim a production Haskell M3 checker.
- **Result 7 (consistency, Path B)** — complete for the Lean reference PL. The canonical
  `checkUnit` boundary runs duplicate-rule and exact Path-B/R12 checks before detailed program
  acceptance, reuses one retained checked-node cache, and rejects the first uncovered ordered
  attackable contrary pair. `coveredB_iff` ties the executable scan to the frozen unlabelled
  compiled `Edge`, so a closure edge or a differently labelled typed attack with the same endpoints
  supplies coverage; self-pairs are included. `Unit.CheckedUnit` carries these invariants while
  generic `CheckedProgram` remains attack-soundness-only. `grounded_conflictFree`,
  `claimSupportFor`, and `contrary_claims_not_both_justified` close computed complete-claim
  consistency. Do NOT mechanize Path A unless the corpus forces the flip. Full hole computation,
  a production Haskell checker/evaluator, and NL-to-structure validation remain outside this result.

## 5. Result 6: source-vs-compiled half complete — oracle eliminated (#17 closed)

Result 6 ("status preservation between a *direct source semantics* and the compiled-AF semantics") is
no longer blocked on a missing direct semantics. `Lara.Compile.SrcIn`/`SrcOut`/`SrcStatus` read the
Prop-level source closure relation — the shadow of the *same* compiled `Edge`, not an independent
calculus — and `srcIn_iff_grounded`/`srcStatus_iff` prove equality with executable grounded
evaluation under `Compile.Faithful`. That `Faithful` obligation is no longer parametric: the
checker-built closure decider `edgeB` (from `containsB`/`attackClosureB`) decides the frozen closure
`Edge` relation exactly (`edgeB_faithful`, with the `DisNodup` side condition discharged by the
checker's `hasSupport_disNodup`), so the specialized wrappers `checkedAF`,
`srcIn_iff_checkedGrounded`, `srcStatus_checked`, and `srcStatus_iff_checked` give source-vs-compiled
agreement over an accepted program with **no oracle hypothesis**; `Lara.Examples` pins the decider on
concrete fixtures. Executable backend replay and proof-bearing raw-program construction are complete.
This closes issue #17. Issue #18 subsequently closes attack completeness and result 7 at the
proof-bearing `CheckedUnit` boundary; the generic `CheckedProgram` boundary remains unchanged.

## 6. Result 7: checked-unit consistency complete (#18)

The public accepted-program path is `checkUnit → Unit.CheckedUnit`. Its fixed rejection order is:
duplicate rule identifiers, R12/Path-B violations, duplicate arguments, support failures, typed
attack failures, then missing conflict coverage. Policy validation precedes program checking, so
strict-root conflicts are owned by R12 rather than misreported as missing attacks.

Detailed program acceptance retains the support checker's indexed nodes and per-source typed-attack
buckets. The completeness scan reuses those values and `coveredB`; it does not re-infer support or
materialize an edge matrix. Coverage is intentionally unlabelled compiled-edge coverage, including
subargument closure, alternate typed reasons with identical endpoints, and ordered self-pairs.

Downstream, `Lara.Consistency` converts retained nodes to exact stable support indices through
`claimSupportFor`. `completeClaimFor` denotes the complete-support projection and therefore has no
holes; it is not the full spec-level `holes(P,p)` algorithm. The headline theorem combines the
Path-B attackability bridge, checked-unit completeness, and generic grounded conflict-freedom to
exclude simultaneous justification of computed contrary claims. `Lara.Grounded` remains the
proof-oriented executable reference semantics, not an optimized production evaluator.

## 7. Sequencing and artifact hygiene

Mechanization starts at M1 freeze, parallel to the Haskell compiler (M3). The two carve-outs (`nf`/`≡`,
the ND adapter) may be *ported* to the prover early as a low-risk warm-up seeding results 10/11. The
proof development is anonymizable from day one; no `sorry`/`admit` in main theorems at M2 exit; a single
replay command checks the whole development; every prover axiom and backend assumption is recorded.
Differential + property + golden + mutation tests remain conformance evidence across the boundary.
