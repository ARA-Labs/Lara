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

## 8. M5 verifies the full presentation boundary

M5 quantifies over the complete `Lara.Presentation.Program` and
`Lara.Presentation.Policy` AST at `lara-syntax@0.10`. It adds a
syntax-directed surface judgment independent of core elaboration, mirrors the
production elaboration pass order in Lean, and proves preservation,
supported-fragment reflection, and semantics-parametric claim-observation
coherence. Cross-language conformance must compare independently emitted
Haskell and Lean results, while the existing core bytes and verdicts remain
unchanged.

Alpha-equivalence applies only to genuine lexical binders: rule parameters and
named `nd@1` lambda binders. Other source names use typed fresh-renaming
equivariance, and replay-significant identities remain fixed. Concrete `.lara`
parser correctness, arbitrary-core surjectivity, and unique source recovery
stay outside the theorem.

The M5 modules may import M1/M2 observation and compilation interfaces but do
not modify M2b's realizability, semantics, observation, or complexity
definitions. Shared axiom-audit and paper-name-map edits land in a final
additive integration commit.

_Committed by N269/N270; durable theorem contract:
`docs/theory-m5-surface-calculus.md`. Reviewed implementation-plan history:
`git show aec9facc1ba3890016401847e6ddca09c0715795:plans/2026-08-30-m5-surface-calculus.md`;
promoted from O110._

## 9. PW0 wraps the local layer without redefining it

PW0 is a spike, not a milestone: it mechanizes the minimum typed possible-world
wrapper so that the decision on proceeding to structural bridges (T6, #191) is
taken against proved objects rather than a design sketch. The exit decision
itself stays on tracker #189.

The architectural commitment is that the wrapper only *imports*. Five modules
land under `Lara.PW` and `Lara.Examples.PW`; no existing checking, compilation,
grounded-labelling, or status definition is touched, and the diff is pure
insertion. Conservativity is then cheap to state — with a singleton context and
no bridges the outer language contains no modal formula, and atomic
satisfaction is definitionally the local status judgment, so both T0 directions
are `Iff.rfl`.

The model is factored as frame plus valuation, with the valuation a parameter
of satisfaction rather than a frame field. That factoring is what lets one
parameterized model be instantiated at the two independently defined Lara
observations — the relational oracle-free `Compile.SrcStatus` and the
executable `Grounded.statusC ∘ Compile.checkedAF` — so their agreement is a
theorem (T1, the existing `srcStatus_iff_checked` chain applied at a world)
rather than a definitional identity. `Prop`-valued valuations do not by
themselves make status a function; `Valuation.Functional`/`.Total` name that
side condition and both Lara valuations discharge it, the source one only
through T1.

Two obligations sit around that spine and are easy to lose. The executable
`crossCompare` takes its candidate list and acceptance test as plain inputs, so
`Presents` plus `mem_compare_iff_sat_dia` are what make it an implementation of
`⟨b⟩` rather than a separate artifact that resembles one; PW0 discharges
`Presents` at a real bridge so the adequacy theorem has an instance.
Incomparability is kept out of the status lattice structurally, behaviorally,
and semantically, never by convention.

What PW0 deliberately does not contain: structural bridges and T6 (#191),
conditional status preservation T8 (#193), exact structural-path composition T9
(#190), approximation bridges, epistemic/dynamic/hybrid operators, global
scenarios, and surface syntax. The well-sortedness refinement of `Query_κ` is
deferred to the M5 surface layer, which is why `gap` currently conflates four
distinct conditions.

_Committed by N271/N272; durable theorem contract:
`docs/theory-pw0-outer-model.md`; proof record:
`evidence/proofs/pw0_outer_model.md`. The T7 finding is C47._

## 10. T6 transports the typing judgment, not the checker

T6 is the first structural result over the PW0 wrapper, and its architecture
is that the transported object is the *relational typing judgment*
(`HasSupport`), never a checker run. The bridge's translation is a partial
symbol map lifted structurally (`Lara.PW.Translation`); the contract
(`Lara.PW.StructuralBridge`) states one correspondence per environment
parameter the judgment reads — leaf typing, rule lookup, certificate
acceptance — over a shared canonicalizer, and nothing else. That "nothing
else" is enforced by issue #191's acceptance bullet taken literally: every
contract field is consumed by a named arm of the transport induction.

Two design facts carry the proof. First, the translation's footprint is
disjoint from `nf`'s — `nf` canonicalizes numeric literals, the translation
renames predicate/constructor names — so `≡` survives translation
(`equiv_tr`) and premise identity and discharge answers transport. Second,
question keys are rule-local vocabulary the translation preserves, so the
obligation list transports *verbatim* and the design's conditional
completeness clause becomes the `O = []` special case rather than a
hypothesis.

The corollaries are deliberately induction-free: target-registry occurrence
replay is B0's headline applied to the transported derivation, and the
checker tie for PW0's `accept` (`Admits`/`admits_transport`) is membership
plus the main theorem. The T6/T8 boundary is now packaged at the live T7
fixtures (`t7_t6_boundary`): transport succeeds, status still flips.

What T6 deliberately does not contain: edge-indexed translation (see the
PW-T6 translation-form constraint in `constraints.md`), partial leaf maps,
attack correspondence (T8, #193), and bridge composition (T9, #190).

_Committed by N275/N276; durable theorem contract:
`docs/theory-pw-t6-structural-transport.md`; proof record:
`evidence/proofs/pw_t6_transport.md`. The headline finding is C48._

## 11. T9 composes exact structural bridges along explicit paths

T9 keeps the T6 contract fixed and adds composition above it. `SymMap.comp` is
first-leg-first Kleisli composition for the existing partial predicate and
constructor maps; the lifted `_comp` theorem family proves that atoms, rules,
support terms, questions, and substitutions follow the same definedness law.
`StructuralBridge.comp` then chains T6's leaf, rule, and certificate clauses
through the intermediate environment. `support_transport_comp` deliberately
returns the intermediate and final `HasSupport` judgments instead of erasing
the middle step.

An indexed `BridgePath` carries every intermediate checking environment as
constructor data. `BridgePath.trans` executes the chosen path stepwise,
`BridgePath.compose` folds it to one bridge (reflexivity at the empty path), and
`BridgePath.trans_eq_compose` proves the two views equal. Consequently
`path_support_transport` is T6 transport over an arbitrary chosen path, with
the obligation list preserved. It does not assert independence from path
choice: the path is explicit because different intermediate environments may
induce different partial translations.

A named direct bridge agrees with a chosen path only under the explicit
`Commutes` triangle, which equates atom translation and support transport for
that arbitrary `BridgePath`. `direct_transport_agrees` yields the common
translated conclusion and checked target judgment. Agreement of the outer
accepted edge is intentionally split: `Accepted R` is literally
`R ∧ Admits`; `Commutes` supplies the `Admits` equivalence, while
`accepted_iff_of_commutes` separately requires the caller's direct and path
candidate relations to agree. This prevents support membership from silently
constraining PW0's independent `Frame.R`.

The counterexamples are part of the contract. The leaf-map triangle contains
its source and target `HasSupport` judgments and proves `¬ Commutes`. The
predicate-only triangle deliberately uses empty environments: its leaf and
constructor maps agree, a constructor-bearing support translates identically,
and only atom translation disagrees. It is a structural independence witness,
not a checked-judgment witness. The vocabulary-gap fixture is an actual typed
`BridgePath`: its first edge succeeds, its second edge rejects the intermediate
atom, and the comparison layer reports `incomparable translationUndefined`,
never a local status. Approximation composition and status preservation remain
separate work; the latter still requires T8 attack correspondence.

_Committed by N293/N294; durable theorem contract:
`docs/theory-pw-t9-path-composition.md`; proof record:
`evidence/proofs/pw_t9_path_composition.md`. Promoted from O125/O126._
