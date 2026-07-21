# LARA — a Language for formally verifying ARA

### Mechanized Warrant Checking for Research Claims — A Research Proposal

> **The name.** **LARA** = a **L**anguage for formally verifying **ARA** (Agent-Native Research
> Artifacts). The `L` is the contribution: a small formal language — justification terms `t : F`
> checked by a trusted kernel, wrapped in an argumentation layer — in which an ARA's evidence→claim
> warrants become _checkable objects_ rather than holistically-scored prose. LARA is to an ARA what a
> type checker is to a program: a deterministic verdict on whether the thing holds together, with a
> located reason when it does not.

> **One-line thesis.** Given a structured research artifact (an ARA), mechanically decide — for each
> claim — whether the _argument from declared evidence to the claim is valid and complete_, and
> produce a checkable, four-state warrant object explaining why; do this with a tiny trusted logical
> kernel, so the verdict does not depend on trusting a language model.

This document is the self-contained research proposal: purpose, background, the theory and how we
make sense of it, why we believe it will work, and how we will know whether it does. It sits above
the operational plan (`../ARA-verification-plan.md`) and the three track guides
(`../Track-C-argumentation-guide.md`, `../Track-D-architecture-guide.md`, and the gap-filling
section of the plan for Tracks A/B). Where this proposal states a design decision, those documents
carry the sourcing.

---

## 1. Purpose and goal

**The problem.** Research artifacts — papers, code, experiment logs — assert claims and gesture at
evidence, but the _link_ between the two is left implicit and is judged holistically by human
reviewers (or, lately, by an LLM reviewer that outputs a score). Holistic judgment is unauditable:
it cannot point to _which_ premise is missing, _which_ dead-end kills a claim, or _whether_ a
conclusion is contested rather than merely unsupported. The Agent-Native Research Artifact (ARA)
format already records the raw material that would make this link explicit — claims, evidence, an
exploration trace with dead ends, provenance tags — but nothing yet _computes_ over it.

**What we build.** `lara` lowers an ARA artifact into a **warrant graph** and computes, for every
claim, one of four statuses:

- `justified` — there is a complete, undefeated justification;
- `gap` — no complete justification exists (a premise or inferential step is missing);
- `defeated` — a justification exists but an unrebutted defeater (a dead-end, a conflicting result)
  overturns it;
- `contested` — mutual defeat leaves the claim undecided.

Crucially, `gap ≠ defeated`: "we never showed it" and "we showed it, then it was refuted" are
different epistemic states, and keeping them distinct is a first-class requirement.

**The goal, stated precisely.** We do **not** prove that a research claim is _true_ — empirical
claims have no deductive proof. We prove that the **warrant is valid and complete**: that the
argument leading from the artifact's own declared evidence to the claim holds up, mechanically and
locally, and survives global defeat. This is the formal analog of a rigor review, but _computed
deterministically on an explicit graph_ rather than scored holistically by a model. The headline
contribution is the ability to surface **failure knowledge** — the dead-end-defeats-claim capability
that ARA's data model uniquely enables and that a holistic reviewer structurally cannot produce.

**Why it matters.** A deterministic, auditable warrant object is a reusable research artifact in its
own right: a reviewer can locate every gap and defeater without reading code; an author can see
which claims stand on brittle evidence; a downstream agent can traverse a machine-checked knowledge
package rather than re-deriving trust. It is the increment over an LLM rigor-reviewer, and it is the
piece that makes "AI-assisted research verification" credible rather than circular.

---

## 2. Background

**ARA.** The artifact has a cognitive layer (claims, concepts, heuristics), a physical layer (code,
configs), an exploration graph (`trace/`, including dead ends and conflicting evidence), and grounded
evidence with provenance tags (`user` vs `ai-executed`). The exploration graph is the differentiator:
it records not just what was concluded but what was _tried and abandoned_. Our defeat layer consumes
exactly this.

**The baseline we improve on.** `rigor-reviewer` scores an ARA holistically across six dimensions and
recommends accept/reject. It is our comparison point: `lara` is the deterministic, locatable
increment. The claim is not "we score better" but "we compute a structured object a score cannot
express, and we do so without the logic layer's rigor depending on the model's accuracy."

**Four theory pillars** (each researched; see the track guides):

- **Track A — the checker spine.** Propositional modal logic → S4 → the Logic of Proofs (LP) /
  Justification Logic → the Realization Theorem. This is what the trusted kernel implements. Sources:
  Artemov (2001) for the LP rule system and realization; Boxes and Diamonds for the modal core; the
  Gödel–McKinsey–Tarski translation for the S4↔intuitionistic bridge.
- **Track B — evidence semantics.** Neighborhood semantics (Pacuit) and van Benthem–Pacuit evidence
  logic. Not implemented in the kernel, but the _design conscience_: the principled account of when
  evidence justifies belief, against which our boolean `supported(E,c)` interface and defeat layer
  must not silently contradict established semantics.
- **Track C — the defeat layer.** Dung abstract argumentation, Caminada labelling, and structured
  argumentation (ABA / ASPIC+). This is the non-monotonic layer that lets dead ends enter (plain LP
  is monotonic). See `Track-C-argumentation-guide.md`.
- **Track D — the trust architecture.** LCF / de Bruijn criterion / Proof-Carrying Code, and the LLM
  autoformalization precedent (Draft-Sketch-Prove, LeanDojo, Baldur). See
  `Track-D-architecture-guide.md`.

**Current state of the build.** The kernel exists. `Lara.Kernel` checks explicit LP derivations
(`Const`, `Hyp`, `App`, `Sum-L/R`, `Check`) and produces a **sealed `Judgment`** — a type whose
constructor is not exported, so the only way to obtain one is a successful `check`. A `Judgment` is
therefore a machine-checked certificate that its `t : F` was built solely by the LP rules. A
QuickCheck suite exercises the deterministic-correctness axis (sum-monotonicity, positive
introspection, rejection of malformed derivations). Substrate is settled: Haskell core, Python
front-end at Phase 3, with the language boundary _being_ the trust boundary. Still to come: the
leaf-atom interface, the ARA→core mapping, the S4→LP realizer, the argumentation layer, and the
elaborator.

---

## 3. The theory, and how we make sense of it

This section answers **question 1 — how we make sense of the theory** — by telling the single
coherent story that ties the four pillars into one machine.

**Step 1 — Modal logic gives the frame.** Ordinary logic asks whether a proposition is true. Modal
logic adds an operator □ that qualifies _in what mode_ it holds, with semantics given by
quantification over related worlds. The reading we want is Gödel's: □F = "F is _provable_ /
_justified_." The system that captures this reading is S4 (reflexive + transitive accessibility).
So the natural home of "claim C is warranted" is an S4 modality: □(evidence → C).

**Step 2 — Justification logic de-modalizes □ into a checkable witness.** S4's □F asserts a
justification _exists_ but names none — useless for auditing. The Logic of Proofs makes it explicit:
instead of □F we write `t : F`, "_this specific term_ t justifies F," where t is built from
variables, constants, and three operations — application (`s · t`), sum (`s + t`), and the
proof-checker (`!t`). This is the entire move. A warrant stops being "there exists support" and
becomes "here is the support term; check it." The kernel's rules are exactly the LP typing rules,
and they are what `Lara.Kernel` implements today.

**Step 3 — Realization guarantees the witnesses exist.** The bridge that makes the lowering
well-posed is Artemov's Realization Theorem: every S4 theorem can be turned into an LP theorem by
filling each □ with a concrete proof term, and S4 is exactly the forgetful projection of LP. This is
the theoretical model of our elaborator's job. It tells us that for the S4-embeddable fragment the
`t` our front-end must construct _provably exists_, and its constructive proof (a three-step
procedure on a cut-free sequent derivation) constrains the term's shape. The lowering pass is, in
one line, _realization performed by an untrusted search procedure and re-checked by the kernel_.

**Step 4 — Argumentation adds the non-monotonic defeat the kernel cannot express.** LP is monotonic:
adding facts never retracts a conclusion, so the kernel alone can never say "this dead-end kills the
claim." We therefore layer Dung abstract argumentation on top: each kernel-checked `t : F` becomes a
_node_; conflicting evidence, dead-end nodes, and provenance downgrades become _attacks_; and a
**grounded-semantics labelling** assigns each node `in` / `out` / `undec`. This labelling _is_ the
four-state output: `in → justified`, `out → defeated`, `undec (in a cycle) → contested`, and `gap`
sits one layer down (the kernel produced no node at all). Grounded is the least fixpoint of Dung's
characteristic function — the same Knaster–Tarski machinery as abstract interpretation and the
μ-calculus, hence polynomial and native to implement.

**Step 5 — The trust architecture keeps the model out of the trusted base.** The producer/checker
split is Proof-Carrying Code, one generation earlier: an untrusted producer ships an object plus a
checkable certificate, and a small trusted checker validates it before anything is accepted. Our
`t : F` term _is_ the certificate; the sealed `Judgment` _is_ the "cannot forge validity" guarantee;
the LLM elaborator _is_ an LCF-style tactic — it proposes, never guarantees, and a rejected proposal
costs nothing. (Note the precise lineage: we are de-Bruijn/PCC-style, not LCF-style — we check a
proof object, we do not merely trust an inference API. See `Track-D-architecture-guide.md` §0.)

**Step 6 — Evidence semantics is the design conscience for the leaves.** Where do the leaf atoms
`supported(E,c)` come from, and when does evidence actually justify belief? Neighborhood/evidence
logic (van Benthem–Pacuit) is the principled answer, and we read it not to implement it in the kernel
but to make sure our boolean thresholding and defeat rules are a _defensible simplification_ of it,
not an accidental contradiction. Graded value is never discarded at thresholding: it rides along as
metadata and drives fragility annotations (a link that stands on 0.79-vs-0.75 is flagged brittle).

**The synthesis in one sentence.** Modal logic supplies the frame; justification logic turns the
frame's existential □ into a checkable witness; realization guarantees the witness exists and shapes
the search; argumentation adds the non-monotonic defeat that failure knowledge requires; and
Proof-Carrying Code keeps the whole thing sound by making the untrusted model's output a certificate
the tiny kernel re-checks. **That is the theory, and that is why the four tracks are one design and
not four.**

### 3.1 What LARA is as a language (and what it is not)

The right mental model for the core is **Lean, with the logic swapped out**. Lean's trusted kernel
checks proof terms in a fixed type theory (CIC); LARA's trusted kernel checks proof terms in a fixed
logic (LP). The correspondence is tight because both are **Curry–Howard systems** — LP is the
explicit-term counterpart of modal S4 exactly as CIC's terms are the explicit content of
intuitionistic proofs (Track A5). The one-line statement of the analogy: **Lean : CIC-kernel ::
LARA : LP-kernel.** We are building a proof checker for a different logic, not a new kind of tool.

|              | Lean                             | LARA                                         |
| ------------ | -------------------------------- | -------------------------------------------- |
| Foundation   | CIC (dependent type theory)      | LP / Justification Logic (explicit S4)       |
| Proof object | a term `e : A`                   | a justification term `t : F`                 |
| Kernel       | checks the term; small, trusted  | `Lara.Kernel`; ~130 lines; sealed `Judgment` |
| Producer     | elaborator + tactics (untrusted) | LLM elaborator + realizer (untrusted)        |
| Discipline   | de Bruijn / proof-object         | de Bruijn / proof-object                     |

But the analogy breaks in two load-bearing places, and those breaks _are_ the contribution:

1. **Empirical, untrusted leaves.** Lean's proof leaves are a tiny fixed axiom set (`propext`,
   `Classical.choice`, `Quot.sound`). LARA's leaves are `supported(E,c)` atoms — LLM-judged or
   measured facts about the world, with a graded value and a provenance tag. The kernel is sound only
   _down to the leaf interface_; the leaves are the interface to the messy world (§3.2).
2. **A non-monotonic layer on top.** Lean is purely monotonic — proved is proved. LARA wraps the
   monotonic kernel in an argumentation/defeat layer where a dead-end can _retract_ a claim's status.
   LARA is therefore a **monotonic proof-term language embedded in a non-monotonic warrant system**;
   Lean is only the inner half.

**What we are designing:** the object logic — grammar (`Lara.Term`, `Lara.Formula`) + the LP
deduction rules + the checker — and the pipeline that consumes it (ARA in, warrant object out). The
core language is the _internal representation_ that makes the verdict checkable and auditable.

**What we are deliberately not designing:** a human-facing surface language in the Lean-4 sense —
concrete syntax, notation, a tactic DSL, an IDE, a standard library. The producer is an LLM emitting
derivations (as JSON), not a human writing `.lara` files. A small surface syntax may appear later
purely for debugging and hand-lowering (the Phase-0 hand-worked examples are that, done on paper),
but it is a convenience, not the contribution. Building tactics and notation for human authors would
be scope creep away from the thesis.

### 3.2 Two tiers of axioms: the logic vs. the leaves

"What are the axioms?" has two answers, and keeping them apart is the crux a reviewer will probe.

- **Tier 1 — logical axioms (the JL/LP schemes).** A0 (propositional tautologies), A1 reflection
  `t:F→F`, A2 application, A3 proof-checker, A4 sum, plus the rules. These are the _logic itself_:
  domain-independent, formalized **once**, baked into the kernel. The LLM never invents or supplies
  them. This is the tier the intuition "we formalize to justification logic's axioms" correctly
  names — it is the language's type system, the analog of Lean's fixed CIC rules.
- **Tier 2 — non-logical premises (the leaves).** A research warrant is **not a tautology**:
  "experiment E supports claim C" is contingent and is _not derivable from A0–A4_, so it cannot be a
  JL axiom (JL axioms hold in every model). The empirical content therefore enters the derivation as
  **leaves** — `supported(E,c)` atoms — supplied per artifact and **audited**, never baked in. In
  proof-theoretic usage these leaves are also called the "axioms" of that particular derivation,
  which is why the two tiers read as one; they are not. The Lean parallel is exact: CIC rules are the
  fixed logic (Tier 1); an `axiom foo : P` declaration flagged by `#print axioms` is a supplied,
  audited premise (Tier 2).

**What the kernel actually certifies is therefore conditional.** A warrant derivation reads: _from
the leaves `x₁ : supported(E₁,c)`, … and the LP axioms, construct `t : C`._ `check` certifies the
**inference** — IF the leaves hold, THEN `t` justifies `C` — and pointedly does **not** certify that
the leaves are true. Whether `supported(E,c)` actually holds is an empirical judgment (LLM-as-judge,
a measurement, or a model checker). **That gap is the trust boundary**, and it is the whole reason
the evaluation splits into a model-independent logic axis and an empirical leaf axis (§5).

**This split is already in the code.** `Lara.ConstantSpec` holds the Tier-1 logical axioms
(propositional-tautology and factivity `t:F→F` instances, pinned to proof constants). Empirical
leaves enter through the `Context` / `Hyp` path (and the still-TODO leaf-atom interface), _not_ as
constant-spec entries. The kernel already keeps "the logic" and "the evidence" on opposite sides of
the trust boundary.

**The LLM's job, stated precisely.** It **translates** the ARA into a LARA program — this framing is
right — but the output is _two_ things, not one: (a) a **derivation** (kernel-checked, deterministic)
and (b) a set of **leaf assertions** (empirical, untrusted, provenance-tagged, audited). The
translation is faithful only if both are; the reliability risk lives entirely in (b), which is why
that axis is measured separately and never laundered through the kernel's rigor.

**A design knob this exposes (open question #6 in the plan).** A leaf can be modeled two ways:
as a **hypothesis** (`Γ ⊢ t:C` with `x : supported(E,c)` assumed — "_if_ E supports C…", conditional)
or as a **non-logical axiom** (a constant `c_E : supported(E,c)` asserted outright). The choice is a
provenance-policy knob: `user`-confirmed evidence can be admitted as an axiom; `ai-executed` /
unconfirmed evidence stays a hypothesis or is only `contested`-eligible until confirmed. Decide this
against the actual trust policy before Phase 1 locks.

---

## 4. Why we think it will work

This section answers **question 2 — why we believe it will work** — as a set of explicit bets, each
with its supporting reason and its failure condition.

**Bet 1 — The core is small, decidable, and already runs.** The `t : F` checker is a straight
structural recursion with no proof search (the derivation is explicit — the de Bruijn criterion). The
rules fit on a page; `Lara.Kernel` is ~130 lines and its trusted surface is a single sealed type.
Boolean propositional LP is decidable. _Why this is a good bet:_ smallness is auditable, and a
standalone checker plus property tests already constitutes a trustworthy kernel — we do not need to
extend Coq/Lean to have soundness we can defend. _Fails if:_ the claim fragment forces connectives or
a first-order extension that blows up the kernel; mitigated by fixing the fragment in Phase 0 before
locking.

**Bet 2 — Soundness is provably local, down to the leaves.** The kernel is sound relative to its leaf
atoms; nothing above the leaves depends on the model. The recent Lean-4 certificate work
(2025–2026, `Track-D` §4) independently confirms the precise pitfall and its fix: kernel-checking a
term is _necessary but not sufficient_ — a certificate can discharge every obligation with a `sorry`
axiom and still type-check — so you must **audit the leaves**. Our trust-boundary-stops-at-leaf-atoms
rule is exactly this audit, made a first-class part of soundness with provenance tags. _Why this is a
good bet:_ it converts the scariest failure mode ("hallucinated evidence atom → sound proof of false
claim") into a managed, explicit interface rather than a hidden assumption. _Fails if:_ leaf
extraction is unfaithful and un-audited; mitigated by requiring `user`-confirmed provenance for
load-bearing atoms and treating extraction as reliability-critical.

**Bet 3 — The two-axis separation makes the logic result independent of LLM noise.** We evaluate two
things on two axes that never mix: (a) deterministic status computation correctness, and (b)
atom-level LLM reliability. The logic layer's rigor is _never_ used to launder the model's judgments.
_Why this is a good bet:_ it defuses the obvious objection ("you're just typechecking LLM-written
formalizations") — axis (a) is a clean, strong result that holds with zero LLM dependence, and the
architecture's credibility comes precisely from keeping the two separable. _Fails if:_ we let the
kernel's authority silently vouch for leaf content; prevented by construction (Bet 2).

**Bet 4 — The lowering target is not speculative — it is a mature, constructive theorem.** Unlike
open-ended autoformalization, our elaborator has a theorem telling it the target exists and roughly
what it looks like (Realization, Bet in §3 step 3). And the "untrusted LLM proposes, trusted kernel
checks, repair loop on failure" pattern is not hypothetical: Draft-Sketch-Prove, LeanDojo, Baldur,
and AlphaProof all instantiate it against Lean/Isabelle, and six 2025–2026 papers frame _exactly_ our
untrusted-producer/tiny-kernel architecture — one (EG-VAR) even connecting tool-attested evidence to
justification-logic terms and Curry-Howard witnesses. _Why this is a good bet:_ we are reusing a
validated systems pattern, not inventing one. _Fails if:_ realization only covers an S4-embeddable
fragment too small to hold real claims; mitigated by characterizing which claim-structures fall
inside it and treating the rest as elaborator-supplied leaves.

**Bet 5 — The defeat layer imposes almost nothing and reuses machinery we already understand.**
Grounded labelling is a ~50-line monotone least-fixpoint computation; it is polynomial, needs no SAT
solver, and is the same fixpoint machinery as the abstract-interpretation background. Flat ABA is an
_instance_ of Dung's framework, so grounded semantics applies directly with soundness for free. _Why
this is a good bet:_ the hardest-sounding layer (non-monotonic reasoning) is in fact the cheapest to
implement correctly. _Fails if:_ the lowering produces non-flat ABA (assumptions that are rule-heads),
which breaks the clean correspondence; mitigated by verifying flatness on the corpus before
committing.

**The composite bet.** Each layer is individually mature and individually cheap; the novelty is the
_composition_ and its application to research warrant. We are not betting on a breakthrough in any one
theory — we are betting that assembling four settled theories along a single trust boundary yields an
artifact that does something none of them does alone.

---

## 5. How we will know if it is working

This section answers **question 3 — how we will know** — the evaluation design. It is deliberately
two-axis, mirroring §4 Bet 3, and the axes are reported separately and never averaged.

### Axis (a) — deterministic correctness of the logic layer

_The strong, clean result; independent of LLM accuracy._

- **Gold-set construction.** Build a set of warrant graphs with **known-correct leaf atoms** and
  hand-computed statuses, including the two structurally important cases: a _dead-end-defeats-claim_
  graph and a _mutual-defeat contested_ graph.
- **Metric.** Status computation must be **exactly right** on every gold graph — this is a
  correctness property, not a score. Grounded labelling is deterministic, so "exactly right" is
  well-defined.
- **Kernel property tests.** Soundness on each derivation rule; rejection of malformed terms; sum
  monotonicity (adding a `+`-summand never invalidates); positive introspection. (Partially in place
  today via QuickCheck.)
- **Exit criterion (already stated in the plan):** given correct leaf atoms and a hand-built graph,
  computed statuses match hand computation exactly.

### Axis (b) — atom-level LLM reliability (empirical, reported honestly)

_The noisy layer; measured, not hidden._

- **Leaf accuracy.** Measure judge/elaborator accuracy at the **leaf level** against human-labeled
  atoms. Report noise honestly, with an error taxonomy distinguishing _logic-layer_ misses (a status
  computed wrong) from _atom-layer_ misses (a leaf judged wrong).
- **The decisive ablation.** Compare **kernel-checked** vs. **LLM-only**: does the kernel catch
  invalid `t` that the model confidently emitted? A positive result here is the core evidence that the
  logic layer adds real value beyond the model.
- **Elaborator yield.** What fraction of claims does the elaborator successfully lower to a
  kernel-checkable derivation (vs. falling back to opaque leaves)?

### Cross-cutting measures

- **Headline number.** The **fraction of load-bearing leaves that can be moved off the LLM** onto a
  checker (certified leaves, if the model-checking backend TL-1 is built) — a direct, quantitative
  measure of how much trust we removed from the model.
- **Corpus.** Reuse the ARA paper's corpus (the 30 papers) so results are comparable, and **compare
  against `rigor-reviewer`** as the baseline the warrant object is the increment over.
- **Failure-knowledge demonstration (the differentiator).** Show, on real artifacts, cases where a
  recorded dead-end correctly flips a claim to `defeated` — the capability a holistic reviewer cannot
  produce. This is the qualitative result that carries the contribution.

### What counts as success

1. Axis (a) is **exact** on the gold set (a correctness claim, defended independently of any model).
2. Axis (b) is **reported with its noise**, and the kernel-checked-vs-LLM-only ablation shows the
   kernel catches invalid derivations the model emits.
3. At least one real ARA claim is discharged end-to-end (ARA → warrant object) with the dead-end
   defeat demonstrated, and the report lets a reviewer locate every gap and defeater without reading
   code.

If (1) holds but (2) shows the elaborator is too noisy to be useful, we still have a publishable
result: the deterministic warrant-checking engine and the honest measurement of where the model-based
front-end fails — which is itself the map of what to move onto checkers.

---

## 6. Risks and mitigations (condensed)

| Risk                                                       | Mitigation                                                                                                                                                 |
| ---------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------- |
| "You're just typechecking LLM-written formalizations."     | Two-axis eval; axis (a) is model-independent; framed as warrant _validity_, not truth.                                                                     |
| Hallucinated evidence atom → sound proof of a false claim. | Trust boundary stops at leaves; provenance tags; `user`-confirmed provenance required for load-bearing atoms; leaf/axiom audit (the `sorry`-audit lesson). |
| Plain LP can't express dead-end defeat.                    | Argumentation layer is in scope from Phase 2, not bolted on.                                                                                               |
| Scope creep into a graded/probabilistic core.              | Hard rule: kernel stays boolean; graded lives in the judge as metadata.                                                                                    |
| Realization only covers the S4-embeddable fragment.        | Characterize which claim-structures fall inside; treat the rest as elaborator-supplied leaves.                                                             |
| Extending Coq/Lean eats months.                            | Standalone Haskell kernel first; logical framework (Twelf/LF, Abella) only if kernel metatheory is later wanted.                                           |
| Non-flat ABA breaks the clean Dung correspondence.         | Verify flatness on the corpus before committing the defeat-layer engine.                                                                                   |
| Temporal logic (TL-1/TL-2) sprawls into a second project.  | Optional, strictly outside the kernel; ship the LLM-judged pipeline end-to-end first.                                                                      |

---

## 7. Plan of work and milestones (condensed)

Full detail in `../ARA-verification-plan.md`. The spine:

| Milestone                         | Definition of done                                                                                |
| --------------------------------- | ------------------------------------------------------------------------------------------------- |
| M0 — spec + hand-lowered examples | one real claim typechecks on paper; leaf-atom interface + ARA→core mapping written                |
| M1 — trusted kernel               | Phase-0 examples check _in code_; kernel auditable in one sitting **(largely done)**              |
| M2 — defeat layer + 4-state       | dead-end-defeats-claim demonstrated; grounded labelling → four states                             |
| M3 — walking skeleton             | one claim ARA → warrant object, no hand steps                                                     |
| M4 — full artifact pipeline       | one full paper → warrant object                                                                   |
| M5 — evaluation (both axes)       | split results + `rigor-reviewer` baseline comparison                                              |
| M6 — draft                        | submittable positioning (warrant checking, anchored in realization / PCC / Dung / evidence logic) |
| TL-1 (optional)                   | one behavioral claim certified by a model checker; one counterexample → `defeated`                |

**Walking skeleton first.** Get _one_ claim end-to-end (ARA → `t:F` → kernel → argumentation →
warrant status) before broadening. A vertical slice beats horizontal completeness.

---

## 8. Open questions to resolve before Phase 1 locks

These are the decisions that shape the calculus; each is tracked in `../ARA-verification-plan.md` §3.

1. **Base logic.** Plain LP (S4-explicit) or a JT/JD variant if claims need factivity/consistency?
2. **Defeat typing.** Distinguish rebut (attack the claim) / undercut (attack the inference or
   experiment) / undermine (attack an evidence atom)? ASPIC+ gives this vocabulary; it maps onto ARA
   (dead-end = undercut, conflicting result = rebut, evidence challenge = undermine).
3. **Defeat-layer engine.** Flat ABA for the engine (instance of Dung → grounded labelling free) +
   ASPIC+ vocabulary for classifying edges; verify no non-flat ABA arises.
4. **Four-state mapping, cross-layer.** `justified`=`in`, `defeated`=`out`, `contested`=`undec`
   (cycle), `gap` = no node (kernel-level underivability). Keep `gap` and `contested` in different
   layers.
5. **Leaf-atom granularity.** One atom per (experiment, claim) or finer (per result-cell)? Sets LLM
   load and gap-detection resolution.
6. **Provenance → trust.** Is `ai-executed` evidence admissible as load-bearing, or only
   `contested`-eligible until `user`-confirmed?
7. **Behavioral vs. empirical routing (gates TL-1).** What fraction of corpus claims are behavioral
   (checkable against a model/code) vs. purely empirical? Decide by sampling the corpus before
   building the model-checking backend.

---

## 9. Positioning (the one-paragraph pitch for the paper)

Frame the contribution as **mechanized warrant checking** — the validity _and completeness_ of the
argument from declared evidence to claim — explicitly _not_ a proof of claim-truth. Anchor it in four
lineages: **realization** (the lowering pass has a constructive theorem behind it), **LCF /
Proof-Carrying Code** (the untrusted-producer / tiny-trusted-checker trust architecture),
**Dung / ASPIC+ / ABA** (the non-monotonic defeat that lets failure knowledge kill claims), and
**evidence logic** (the principled semantics the leaf interface answers to). Lead with the
failure-knowledge capability — dead-end-defeats-claim — because that is the delta over a holistic LLM
reviewer, and it is the thing ARA's data model uniquely enables.
