# Experiments

_For a calculus-contribution paper the "experiments" are metatheory proof obligations and checker
conformance tests, not benchmark runs. Each experiment is directional; exact status (proved / passing
/ open) lives in `evidence/status/`. The 12 required results are spec §9; the mechanization plan is
`docs/mechanization-plan.md`._

## E01: Normalizer / identity conformance (the implemented carve-out)
- **Verifies**: C01
- **Evidence**: evidence/status/test_status.md, evidence/results/prop_layer.md
- **Run**: src/execution/Prop.hs (module `Lara.Prop`); test/PropSpec.hs (QuickCheck)
- **Setup**:
  - Model: n/a (analytical + property-based testing)
  - Hardware: developer workstation (GHC 9.14.1 / cabal 3.16)
  - Dataset: QuickCheck-generated ground atoms with cosmetic literal noise (signs, leading/trailing zeros)
  - System: `Lara.Prop` `nf`/`≡`/`canonNum`
- **Procedure**:
  1. Generate random propositions and terms, including numeric literals with cosmetic variants.
  2. Assert `≡` is reflexive, symmetric, transitive, and equals `nf`-equality.
  3. Assert `nf` is idempotent and does NOT reorder arguments (`p(a,b) ≢ p(b,a)` for distinct a,b).
  4. Assert `canonNum` collapses surface variants of one value and is idempotent.
- **Metrics**: fraction of QuickCheck properties passing (target: all).
- **Expected outcome**:
  - All equivalence-law, idempotence, no-reorder, and canon properties hold.
  - This grounds the "trivial TCB addition" claim empirically.
- **Baselines**: none (self-contained property suite).
- **Dependencies**: none.

## E02: POPL evaluation-methodology synthesis (deep-research, adversarially verified)
- **Verifies**: C10, C11, C12
- **Evidence**: evidence/status/mechanization_status.md (methodology section); docs/mechanization-plan.md §0/§3; docs/worked-examples-plan.md §6
- **Run**: deep-research workflow (fan-out web search → fetch → 3-vote adversarial verification → synthesis), 104 agents
- **Setup**:
  - Model: LLM research agents (workflow harness)
  - Hardware: n/a
  - Dataset: 21 fetched primary sources; 95 extracted claims; 25 verified
  - System: 6 search angles (PL evaluation norms; neurosymbolic LLM+checker; differential/mutation testing; rejection reasons; AEC badging; corpus/argumentation grounding)
- **Procedure**:
  1. Decompose "how are new-language/calculus papers evaluated at POPL" into 6 angles.
  2. Fetch primary sources; extract falsifiable claims.
  3. Adversarially verify each claim with 3 skeptical voters (≥2 refutes kills it).
  4. Synthesize surviving claims into the mechanization / worked-examples plans.
- **Metrics**: fraction of extracted claims that survive adversarial verification.
- **Expected outcome**:
  - Mechanized metatheory can serve as the evaluation; benchmarks/user-studies not load-bearing.
  - Untrusted-producer/checker judged by verified-success + adversarial zero-false-positive + anti-memorization.
  - Differential testing framed N+1 (JEST), not oracle-free voting (Csmith).
- **Baselines**: the project's prior (un-cited) evaluation intuitions, corrected against exemplars.
- **Dependencies**: none.

## E03: Strict-certificate soundness + reference-adapter soundness (paper proofs)
- **Verifies**: C03, C05
- **Evidence**: evidence/proofs/nd_adapter_soundness.md, evidence/proofs/nonfactivity_and_defeat.md
- **Run**: docs/strict-backend-decision.md §5 (Theorems 1, 3, 4; Lemma 5); target Lean 4 mechanization (results 8, 10)
- **Setup**:
  - Model: n/a (metatheory)
  - System: the backend interface (six obligations) + the natural-deduction reference adapter
- **Procedure**:
  1. State certificate soundness as backend obligation 3; derive Theorem 1 (strict-step soundness) as a one-line application.
  2. Prove source non-factivity (Theorem 3) by inversion on the source rules.
  3. Prove ND adapter soundness (Theorem 4) by induction on the typing derivation; Lemma 5 (dependency exactness) by structural induction on free de Bruijn indices.
- **Metrics**: proof status per theorem (paper-proved / mechanized / open).
- **Expected outcome**:
  - Accepted certified instances are backend consequences of encoded premises; support never becomes truth.
  - ND certificates are sound (not complete) and report exact dependencies.
- **Baselines**: none.
- **Dependencies**: none.

## E04: Backend replacement preserves claim status (paper proof → mechanization)
- **Verifies**: C04
- **Evidence**: evidence/proofs/backend_replacement.md
- **Run**: docs/strict-backend-decision.md §5 (Theorem 2); target Lean 4 mechanization (result 9)
- **Setup**:
  - Model: n/a (metatheory)
  - System: two backends with identical strict-acceptance profiles; `eraseCert`; grounded labelling
- **Procedure**:
  1. Show by structural induction on support terms that the same leaves and rule instances check in both programs.
  2. Show `eraseCert` induces a bijection on argument nodes and typed attacks.
  3. Show compilation preserves the bijection (graph isomorphism); grounded lfp commutes with isomorphism; aggregation yields equal statuses.
- **Metrics**: proof status (paper-proved / mechanized / open).
- **Expected outcome**: isomorphic AFs and equal four-state statuses whenever acceptance profiles match.
- **Baselines**: none.
- **Dependencies**: E03.

## E05: Positional attack typing + strict-reachable consistency validator (corpus-gated)
- **Verifies**: C02, C09
- **Evidence**: partial — positional attack typing and the instance-overlap validator are mechanized;
  corpus defeat coverage and the result-7 status theorem remain pending
- **Run**: docs/spec.md §7 (attack judgment), §8.1 (Path-B validator); M0 corpus study fixes defeat typing (open question §8 #3)
- **Setup**:
  - Model: n/a
  - Dataset: 50–100 corpus claims annotated for rebut/undercut/undermine candidates (`docs/corpus-map.md` §4)
  - System: positional attack checker + compile-time strict-reachable validator
- **Procedure**:
  1. For each corpus dead end, decide rebut / undercut / undermine / no-edge with target position and contrary pair.
  2. Confirm every attack types as an attack on a root / internal-rule / leaf position.
  3. Compute the strict-reachable pattern set; reject policies whose `contrary` sides may overlap it
     at the ground-instance level.
- **Metrics**: fraction of annotated defeats typable within the three position kinds; policy-validator rejection correctness.
- **Expected outcome**:
  - Every real defeat fits one of the three position kinds (else a fourth primitive is needed → falsifies C02).
  - Path-B-well-formed policies never make two contrary claims jointly justified.
- **Baselines**: unconstrained attack-graph producer (any node can attack any node).
- **Dependencies**: E01.

## E06: Non-monotonic defeat — the differentiator (dead-end flips claim to defeated)
- **Verifies**: C06
- **Evidence**: evidence/proofs/nonfactivity_and_defeat.md; worked example E3 (docs/worked-examples-plan.md §3)
- **Run**: docs/strict-backend-decision.md §6 (Proposition 8); the `defeat-suite` worked example (ResNet-anchored)
- **Setup**:
  - Model: n/a
  - Dataset: the ResNet ARA (C01/C02) with the real N04 vanishing-gradient dead-end (a NON-attack) plus a constructed conflicting-measurement dead-end (a rebut)
  - System: compile → grounded labelling → four-state aggregation
- **Procedure**:
  1. Prove Proposition 8 (a subset X justifies p; adding a checked attacker in Y ⊇ X retracts it) — no monotonic relation can represent this.
  2. In the worked example, show a recorded dead end constructing a typed attack flips a claim to `defeated`, while N04 (an alternative-explanation dead end) compiles to no edge.
- **Metrics**: proof status; worked-example status-coverage (justified/gap/defeated/contested all present).
- **Expected outcome**: defeat is non-monotonic and localizable; the dead-end-flips-claim capability is exactly what a holistic reviewer cannot produce.
- **Baselines**: `rigor-reviewer` (holistic score, cannot localize); a monotonic proof-or-evidence attestation (e.g. `rit`).
- **Dependencies**: E04, E07.

## E07: Grounded evaluation determinism + termination (fixed-point construction)
- **Verifies**: C07
- **Evidence**: **core mechanized** — `lean/Lara/Grounded.lean`: `grounded` = bounded characteristic-operator iteration from ∅; `grounded_stable` proves the ascending chain reaches the least fixed point within `|args|` steps (deficit measure + strict-filter-length, done by hand in core Lean 4 — no `Finset`/Mathlib needed); `grounded_fixpoint` gives the fixed point. Total, deterministic function. Full instance over concrete compiled support terms is M1-gated. (canonical status: `evidence/status/mechanization_status.md` result 5)
- **Run**: docs/spec.md §8; Lean 4 mechanization by bounded iteration (result 5; docs/mechanization-plan.md §4)
- **Setup**:
  - Model: n/a
  - System: Dung characteristic function `D_AF` on the finite argument set
- **Procedure**:
  1. Prove `D_AF` monotone on the subset lattice.
  2. Compute the least fixed point by bounded iteration from ∅ with fuel |Args|; prove it stabilizes and is unique.
  3. Show attack cycles yield `undec`/`contested`, not divergence.
- **Metrics**: proof status (paper-proved / mechanized / open).
- **Expected outcome**: one grounded labelling, in ≤ |Args| steps, terminating.
- **Baselines**: none.
- **Dependencies**: none.

## E08: Dependency accountability (leaves(w) = frontier) + status preservation (partially closed gap)
- **Verifies**: C08
- **Evidence**: **result 6 abstract core mechanized; leaf accountability + compile step still pending.** `lean/Lara/Grounded.lean` defines the direct big-step judgment (`DirectIn`/`DirectOut`, no iteration) and proves it equals the executable grounded labelling over any AF (`directIn_iff`, `labelC_*_iff`, `status_preservation`) — an independent semantics now exists, closing N16's core objection. STILL OPEN: (a) leaf accountability (`Lara.SupportTerm` spec-only); (b) the source-vs-compiled *preservation itself* — the equivalence quantifies over one `F : AF`, so `compile`/subargument closure are only characterized (`compile_attack_iff`), not exercised (M1). (canonical status: `evidence/status/mechanization_status.md` result 6 = "partially mechanized (abstract AF layer)")
- **Run**: docs/spec.md §6 (`leaves`/`certDeps`), §8.2 (direct semantics), §9 results 3 & 6; docs/mechanization-plan.md §5
- **Setup**:
  - Model: n/a
  - System: support-term checker + compilation + direct source semantics (abstract layer defined; concrete layer M1)
- **Procedure**:
  1. Prove the reported leaf set equals `leaves(w)` by inversion on term structure; strict deps via `uses`. *(pending)*
  2. ✅ **Direct big-step claim-status semantics defined** (spec §8.2, `DirectIn`/`DirectOut`) and proved to agree with the executable grounded labelling over any AF (abstract core of result 6).
  3. **Still to do (M1):** instantiate the agreement at `F = compile(W)` with a source-level status, so the subargument-closure edges are exercised — the genuine source-vs-compiled preservation.
- **Metrics**: proof status per part; whether the compile step exercises `compile`/subargument closure.
- **Expected outcome**: exact dependency accountability; a genuine two-semantics preservation theorem once the compile step is instantiated over concrete support terms.
- **Baselines**: none.
- **Dependencies**: E07.

## E09: M0 semantic corpus study — 60-claim stratified annotation (open questions §8 #1/#2/#3/#5)
- **Design**: 231-claim sampling frame + 279 dead-end attack pool extracted from
  `corpus/ara-paperbench` @ `62e9b54`; six-way claim typing over the full frame (blind
  double-annotation of an 18-claim subset on a different model: 14/18, κ = 0.73, 4
  adjudications); stratified 60-claim sample (seed 42, quotas with floor, paperbench-first)
  annotated per the 8-field schema (`m0/annotations/SCHEMA.md`) by 27 independent AI
  annotators (one per artifact, shared codebook, no cross-talk); aggregation and
  coverage-flag adjudication in `m0/annotation-summary.md`.
- **Status**: done (2026-07-22); human affirmation of the summary on 2026-07-22.
- **Artifacts**: `m0/` (claims-index.tsv, claim-types.tsv, sample.tsv, annotations/,
  double-annotation.tsv, annotation-summary.md), commits `75e2a65`…`6524e8c`.
- **Grounds**: C13, C14, C15, C16, C17.
