# Problem Specification

## Observations

### O1: Research artifacts assert claims and gesture at evidence, but the support relation is never checked
- **Statement**: Papers, code, and experiment logs assert claims and point at evidence, yet the step
  "this evidence supports this claim" is only ever *declared*, never *checked*. Prior
  claim-formalization systems (Micropublications, AIF, nanopublications) are representation models: a
  support edge is asserted, with no status computation, no located defeat, no soundness theorem.
- **Evidence**: `docs/novelty-and-related-work.md` §2 delta table.
- **Implication**: There is room for a *checked* claim-support object with a computed, replayable
  status — distinct from a representation format.

### O2: An LLM reviewer's holistic score cannot say WHICH premise is missing or WHICH dead end kills a claim
- **Statement**: The named baseline `rigor-reviewer` scores six dimensions (D1–D6) 1–5 and emits an
  accept/reject recommendation, but "does NOT execute code, fetch URLs, or consult external sources"
  and is "not a bug detector." It cannot point to the load-bearing premise or the defeating dead end.
- **Evidence**: `docs/corpus-map.md` §1 (the confirmed baseline).
- **Implication**: A localizing checker — one that reports *which* obligation is open or *which*
  attack defeats an argument — provides a capability a holistic reviewer cannot.

### O3: Autoformalization compile-success materially exceeds semantic faithfulness
- **Statement**: Recent autoformalization work reports compile success far above faithfulness — e.g.
  "Beyond Compilation" reports 89.5% compile vs 60.5% faithfulness, a ~29-point gap; over half of
  miniF2F v1 formal statements were misaligned with their informal text until manually re-aligned.
- **Evidence**: `docs/gap-resolution.md` (Gap 2, autoformalization faithfulness); the LLM risk is not
  confined to leaves — it also chooses the proposition, inference scheme, attack type/target, and
  what to omit, so every untrusted boundary must be measured separately.
- **Implication**: An LLM that produces formalizations cannot be trusted as the source of validity;
  every untrusted boundary (proposition, leaf, scheme, backend/theory, attack) must be measured
  separately, and the checker must be the sole arbiter of structure.

### O4: The evidence→claim step is contingent and defeasible, not deductive
- **Statement**: `supported(E, C)` does not entail `C`. A bridge from evidence to an empirical claim
  is a non-logical, usually defeasible inference scheme; treating it as deductive certifies a hidden
  axiom. A recorded dead end can retract a prior conclusion — a non-monotonic phenomenon.
- **Evidence**: empirical support is not deductive implication — the evidence→claim bridge must be a
  named, defeasible inference scheme open to undercutting, not a hidden axiom, and a missing
  certificate is not a proof of underivability, only an explicit gap; `docs/comparison-rit-lara.md` §5.
- **Implication**: The core cannot be a monotonic proof system; it needs a defeasible layer with
  typed defeat and a non-monotonic acceptance semantics.

## Gaps

### G1: No checkable, defeasible claim-support object with located four-state status
- **Statement**: No prior system combines (a) a typed claim-support calculus with policy-generated
  obligations and typed attacks, (b) a semantics-preserving compilation into a Dung framework with
  grounded four-state status, and (c) mechanized accountability/status-preservation theorems.
- **Caused by**: O1, O2, O4.
- **Existing attempts**: Micropublications/AIF (represent, don't check); Pandžić's default
  justification logic (pure logic, factive, no policy/CQ layer, no artifact/evaluation); EG-VAR
  (tool-attested but monotonic, no defeat, no critical-question completeness); PCC/FPC (the
  architecture ancestor, for machine proofs only).
- **Why they fail**: each supplies at most one of the three parts; none yields a *located, defeasible,
  replayable* claim status.

### G2: Where does trust in strict deductive steps live, without privileging one logic?
- **Statement**: A strict sub-step ("premises deductively yield conclusion") needs a soundness
  guarantee, but building one logic (LP/S4) into the core over-commits and invites objections
  (Pandžić already occupies modal/JL ground; realization does not guarantee lowering).
- **Caused by**: O3, O4.
- **Existing attempts**: The original LARA design made LP the strict fragment and leaned on Artemov
  realization as a lowering guarantee.
- **Why they fail**: Artemov's theorem is `S4 ⊢ F ⟹ LP ⊢ Fʳ` — theorem-to-realization only; it says
  nothing about whether NL→formal lowering was faithful (see the PIVOT recorded in trace N05).

### G3: A language-design paper's "experiment" is undefined when there is no benchmark
- **Statement**: LARA's contribution is a calculus, not a system with runtime numbers, and
  benchmarking has been ruled out of scope for the first submission. What, then, is the evaluation?
- **Caused by**: the project being a POPL-track type-theory contribution.
- **Existing attempts**: treat it like a systems paper (perf tables) — rejected.
- **Why they fail**: perf/user-studies are not load-bearing for a calculus paper; a deep-research
  pass (trace N14) confirmed mechanized metatheory can *be* the evaluation, and POPL artifact
  evaluation excludes non-mechanized proofs from review.

## Key Insight
- **Insight**: Make the claim-support *object* a checkable, typed term whose three attack kinds are
  exactly its three position kinds, compile it to a Dung framework for non-monotonic status, and
  confine every strict logic behind an opaque backend interface — so the calculus is non-factive and
  logic-agnostic, and its *status semantics* is provably independent of certificate internals.
  Because it is a calculus, treat **mechanization/test status as the empirical signal** that grounds
  each design claim.
- **Derived from**: O1, O2, O4 (the object + defeat), O3, G2 (the backend seam), G3 (the evaluation).
- **Enables**: positional attack checking as subterm lookup, dependency accountability as an
  inversion lemma, backend replacement as graph isomorphism, and a four-state located status.

## Assumptions
- A1: Leaves are untrusted hypotheses; the checker never establishes empirical truth (Hume's fork).
- A2: A versioned claim-support policy `Pi` (inference schemes, contrary relation, admission table) is
  a *trusted input*; policy quality is an evaluated axis, not a proven property.
- A3: The NL↔formal `binding` of a claim is the single most load-bearing unchecked step; it is
  human-signed and audited, never proven.
- A4: Support-level propositions are ground first-order atoms; richer structure lives inside backend
  encodings, not the source proposition language.
- A5: v0.1 uses grounded semantics only; attack cycles yield `undec`/`contested`, not nontermination.
