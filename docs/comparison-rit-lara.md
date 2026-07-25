# `rit` vs `lara` — what each verifies, and what it does not

_Status: analysis note. First written 2026-07-20; revised 2026-07-21 against the POPL-track
`docs/spec.md` and `docs/strict-backend-decision.md`; §11 addendum 2026-07-25 verified against
`rit`'s current source tree. LP is now an optional strict adapter, and the
evidence→claim support lives in a versioned policy of defeasible schemes. Compares the two sibling
projects under `ara/`: `rit` (a verification core built on the Lean kernel) and `lara` (this project,
a claim-support language with a backend-parametric strict seam plus an argumentation layer). Goal:
state precisely what each checks, where they agree, where they differ, and where the framing promises
more than the mechanism delivers._

---

## 1. One-line theses

- **`rit`** — an *untrusted* agent runs experiments and proposes claims; a *trusted*
  verification core turns each claim into a machine-recheckable proof-or-evidence.
  "Trust comes from the verification layer, not the agent." Kernel = **Lean 4** +
  deterministic extractors + sha256 integrity locks.
- **`lara`** — a small language of proof-carrying, **policy-relative** claim support. A
  program declares propositions, evidence leaves, instances of strict or defeasible inference
  schemes, their obligations, typed attacks, and claim roots. The checker compiles this to a Dung
  framework and reports, per claim, one of `justified / gap / defeated / contested`. Strict steps use
  a small certificate interface with a natural-deduction reference adapter and optional LP adapter;
  the empirical evidence→claim step is a **defeasible scheme in a versioned policy `Pi`**, not a
  proof term.

Both are the *same architecture* — untrusted proposer, tiny trusted checker — applied to
research artifacts. They differ in the kernel logic and, more importantly, in **where each
draws the line between what the checker guarantees and what it merely assumes.**

---

## 2. What the pipeline actually does (jargon removed)

Take a concrete claim: *"v3 hit the target in 2875 steps, beating the 2900 baseline."*

- **`rit`:** split the claim into a **fact** ("2875 steps") and a **relation** ("2875 < 2900").
  Lean proves the relation; the fact is *pinned* — hash the log, re-run an extractor to confirm
  the number came from those bytes. Roll up AND/OR over a claim DAG; print an attestation.
- **`lara`:** the fact enters as a **leaf** (`observed`, provenance `ai-executed`, bound to a
  data ref). The step "this experiment supports the claim" is **not** proved — it is an instance
  of a named **defeasible rule** in the policy (e.g. `controlled_experiment`), which carries
  *critical questions* (randomization, power, external validity) that must each be discharged or
  left as an explicit hole. A recorded dead-end can attack the argument. Grounded labelling over
  the compiled graph yields the four-state status.

The honest one-liner still holds for both: **the checker validates the argument structure —
that steps instantiate declared rules, obligations are explicit, attacks are type-correct, and
the status is the grounded result. It does not establish that the evidence is true, nor that the
declared scheme is a correct account of what supports a claim.** That judgment lives in the leaves
(both systems) and now, for `lara`, also in the policy.

---

## 3. What is the same

| | Shared design |
|---|---|
| Trust model | Untrusted proposer, tiny trusted checker. Proof-Carrying Code / de Bruijn / LCF lineage. A bad proposal costs one failed check, never a false attestation. |
| Sealed kernel | `rit` seals the Lean `Judgment`; `lara` seals `Judgment` via a hidden Haskell constructor. The only way to get one is a successful `check`. |
| Input | Both consume an ARA and decompose it into a graph of claims (`rit`: *claim DAG*; `lara`: *claim-support graph / compiled Dung framework*). |
| Hume's fork | Both refuse to prove the empirical. Empirical content enters as leaves / groundings; only structural relations are checked. |
| Dependency exposure | Both surface exactly which unverified inputs a conclusion rests on (`rit`: tiers T0–T4, `#print axioms`; `lara`: the leaf-dependency set `L` and open obligations `O` reported per argument). |
| Two-axis honesty | Both keep deterministic structural correctness separate from noisy empirical reliability, and never average the two. |

---

## 4. Where they differ

| Dimension | `rit` | `lara` (current spec) |
|---|---|---|
| Kernel logic | Lean 4 / CIC (dependent type theory) | typed argumentation checker + registered strict-certificate adapters (natural deduction required; LP optional) |
| The evidence→claim step | analytic relations proved; extraction pulled INTO the kernel (K-tier) | a **defeasible scheme** in a versioned policy `Pi`, with critical questions — *not* proved |
| Empirical content | sha256 byte-capture + deterministic re-extraction; compressed *toward* the kernel | untrusted leaves (`observed/attested/assumed/certified`), kept *out* of the kernel |
| Monotonic? | **Yes** — Lean is monotonic; proved is proved | **No** — typed attacks (rebut/undercut/undermine) + grounded semantics on top |
| Failure knowledge | not first-class; a claim simply fails to verify | first-class: a dead-end that constructs a typed attack can **defeat** a claim |
| `gap` vs `defeated` | not distinguished | distinguished by design (`gap` = no complete argument / open obligation; `defeated` = complete but labelled `out`) |
| Trust locus beyond leaves | the byte-capture event | the byte-capture event **and the policy `Pi`** (trusted input) |
| Human surface | Lean source + `@claim` NL comment | a declarative presentation syntax (`claim`/`leaf`/`arg`/`undercut`/`status`) over a shared abstract syntax; JSON is the wire format |
| Stack | Python front-end + Lean | Haskell core + Python front-end (Phase 3) |

**The deepest difference is a dual strategy toward the same wall.** `rit` pushes as much of the
empirical world *into* the kernel as it can: embed the evidence bytes as a Lean literal, ship the
extractor as a Lean function, so the grounding itself becomes a theorem and the world enters at
one byte-capture event. `lara` does the opposite: it keeps the empirical content *outside* as
untrusted leaves, and spends its formal budget on the layer Lean cannot express — **typed,
non-monotonic defeat**, where a recorded dead-end retracts a claim. That defeat capability is
`lara`'s actual novelty and is invisible to a purely Lean approach.

---

## 5. The dependent-type question: can a kernel "express" a research claim?

No — and neither project claims it can, once you read the fine print. A dependent-type kernel
cannot express, let alone prove, the empirical content of a claim. "v3 reached the target in 2875
steps" is not a theorem; it enters as an assumption:

```lean
opaque best_steps : Nat
axiom best_steps_grounded : best_steps = 2875   -- NOT proved; asserted
-- @claim: a real run reaches the target in under 3500 steps
theorem reach_3500 : best_steps < 3500 := by rw [best_steps_grounded]; omega
```

The kernel proves only the **analytic** slice (`2875 < 3500`). The empirical `= 2875` is
established *outside* — `rit` re-hashes and re-extracts; `lara` records it as a leaf — and the
dependency is exposed (`#print axioms` / the leaf set `L`).

- **What dependent types express well:** the relational / analytic skeleton — inequalities,
  logical combinations, "premises ⇒ claim." Arguably more power than the task needs.
- **What they cannot express:** the truth of a measurement. That always enters as an assumption.

`lara`'s current design draws the sharper conclusion: it does *not* try to express the
evidence→claim step as a proof at all. That step is contingent (`supports(E,C) -> C` "is not a
logical axiom", per `spec.md §5`), so it is modeled as a **defeasible rule**, checked by
instantiation against a policy rather than by proving. Proof systems are reserved for genuinely
strict sub-steps and connected through one explicit backend interface.

---

## 6. Curry-Howard: what "compiles" actually certifies

The tempting slogan is *"by Curry-Howard, if the program compiles the paper's claim is valid."*
The natural-deduction adapter and optional LP adapter genuinely have proof-term readings, but the
claim they license is narrower than it sounds, and the whole credibility turns on one word.

**Validity, not soundness.** A strict adapter validates that its encoded conclusion follows from
encoded premise conclusions and a declared theory; the claim-support checker validates scheme
instantiation. Leaves remain **hypotheses**, not theorems. Compilation therefore certifies a
conditional, not premise truth. LARA's end-to-end guarantee is structural validity relative to the
selected policy, backend theories, and admitted leaves; completeness is policy-relative.

**The right analogy — and it is still a strong pitch.** No type-checker proves a program
correct; it proves it well-typed. `tsc` passing means no category errors *given your
annotations*, not that the code does what you want. `lara` is the exact analog:

> compiles ≠ claim true — compiles = **the argument is well-typed and undefeated, given its
> evidence and the chosen policy.**

That is a real contribution (mechanized well-typedness for research arguments); "compiles ⇒ true"
is not, and a reviewer will reject the latter on sight.

**Three things `compiles` does *not* cover** — name them first, because they are where every
critique lives:

1. **Leaf truth (soundness).** The evidence atoms are assumed. Empirical, untrusted.
2. **NL→proposition faithfulness (the translation gap).** That the formal `F` faithfully renders
   the prose claim. No checker can verify this; `spec.md §11` lists it as an untrusted elaborator
   task evaluated against human annotations. It is the single most load-bearing unchecked step.
3. **Policy faithfulness.** That the defeasible rule (and its critical questions) is a correct
   account of what actually supports the claim. `Pi` is a *trusted input*.

**Curry-Howard covers adapters, not LARA as a whole.** The clean story ("well-typed proof term
implies valid derivation") applies to proof-term adapters in `spec.md` Section 5. The defeasible layer
is argumentation-framework defeat, which is not a Curry-Howard phenomenon: a valid argument can be
retracted by a dead end. The honest framing is a **typed argument checker with pluggable strict
certificate adapters**, not a Curry-Howard proof system end-to-end.

---

## 7. The necessity question: why a formal system at all?

The earlier draft's sharpest critique was that a proof kernel is overkill for the shallow
arithmetic that shows up between grounded facts and claims. The current `lara` design answers this
by putting strict checkers behind one backend seam and moving the real work to the
argumentation-scheme + policy + grounded-labelling layer. The necessity test now applies per
adapter:

- **What the formal system now does** is enforce, across a whole artifact, that every argument
  correctly instantiates a declared scheme, every critical question is discharged or explicitly
  held, attacks are type-correct, and defeat propagates — then locate the gaps. That is the
  "type system for arguments" value, and it *does* survive the necessity test better than "a
  prover for `2875 < 2900`", because the payoff is consistency-and-gap-location at scale, not
  single-step depth.
- **The live question is which optional adapters earn their keep.** Natural deduction is the small
  reference implementation. LP, arithmetic, temporal, or code adapters ship only when corpus steps
  use their distinct capabilities. Backend replacement proves none is foundational; corpus evidence
  decides utility.
- **For `rit`,** the original critique still lands unchanged: Lean is a heavyweight trusted base
  (Mathlib; `native_decide` → compiler axiom; `grind` → classical axioms) doing the most trivial
  job (`a < b`), while the components that do real work — sha256 locks, extractors, re-execution,
  spec-checkers — are the *non-Lean* parts. The formal kernel is the least load-bearing piece
  with the largest footprint.

**The criterion to keep.**

> A formal system earns its place when it enforces consistency a human cannot audit at scale and
> emits a portable, re-checkable certificate. `lara`'s scheme/defeat checker plausibly clears
> this bar; a heavyweight proof kernel over shallow arithmetic (`rit`'s Lean use) does not, and
> each optional `lara` adapter must show it is used by real support derivations.

---

## 8. The honest read: what these systems are, and what they are not

The grand framing on `rit`'s README is *"trust comes from the verification layer, not the
agent."* But the research judgment — "does E support C?" — is a leaf, decided by an LLM or a
human, never by the kernel. The kernel rigorously verifies what was never in doubt (`2875 <
2900`) and not what decides whether the research is sound. That is the same lock-next-to-an-open-
window as before.

`lara`'s current spec is, to its credit, **already honest about this** — it states that
acceptance is "structural validity only," that completeness is policy-relative, that realization
does *not* justify the lowering (`§11`), and that the current LP code is a non-conforming adapter
seed rather than the trusted core (`§5`). The critique therefore now
differentiates the two projects:

- **`rit`** still over-frames: "verify claims" reads as epistemic verification the mechanism does
  not deliver. The defensible description is *tamper-evident bookkeeping + arithmetic checking +
  dependency exposure*.
- **`lara`** describes itself accurately. Its exposure is not dishonest framing but a **relocated
  hard problem**: the epistemic content moved into the policy `Pi`, which is trusted, unchecked
  input. The checker's guarantee is now three-way conditional — *given* true leaves, *and* a
  faithful policy, *and* a faithful NL→proposition translation, the argument is valid and
  undefeated.

**The modest, defensible version of each:**

- **`rit`** = tamper-evident bookkeeping + arithmetic checking. Guarantees the numbers came from
  the stored logs and the composition math is error-free; tracks per claim what it rests on. Real
  and useful. Not "verification of research."
- **`lara`** = a typed, policy-relative argument checker with first-class defeat. Guarantees that
  a paper's argument instantiates declared schemes, discharges or flags every critical question,
  and survives recorded defeaters — and *locates* the gaps and defeaters. The one capability `rit`
  lacks: a recorded dead-end can flip a claim to `defeated`.

---

## 9. The sharp questions each project should answer

- **To `rit`:** the stated hook is that LLM-judges pass ~97% while only ~66% is real. What
  fraction of that gap is *arithmetic / tampering / composition* error (which the kernel catches)
  versus *bad judgment about whether evidence supports a claim* (which lives in the leaves and the
  kernel never sees)? If mostly the latter, the kernel attacks the minority failure mode while
  being sold as closing the whole gap.

- **To `lara`, three:**
  1. **Who writes `Pi`, and why is it right?** The policy is now the load-bearing epistemic
     artifact and it is trusted input. The rebuttal-bait question is "your checker is only as good
     as its policy" — have the answer ready (schemes curated from methodology literature,
     versioned, corpus-validated), and treat policy quality as an evaluated axis, not an
     assumption.
  2. **Which strict adapters earn their keep?** Measure certified strict steps by backend and
     distinguish generic propositional consequence from genuinely LP-, arithmetic-, temporal-, or
     code-specific checks. Keep adapters optional unless they reduce trust on real support derivations.
  3. **Is the concrete syntax the audit surface it needs to be?** Today a `claim` carries only its
     NL string; the formal proposition appears only inside the `supports(...)` argument. Put the
     claim's formal target next to its NL (as `rit`'s `@claim` does) so the highest-risk
     translation step is auditable at a glance.

---

## 10. Bottom line

Neither system verifies research claims, and both now say so — `rit` in its fine print ("the
world enters at one arrow"), `lara` in its spec ("structural validity only… policy-relative
completeness… realization is not a guarantee for this lowering"). What they build is auditing
infrastructure: tamper-evidence and arithmetic soundness (`rit`); typed, policy-relative argument
checking with located gaps and first-class defeat (`lara`).

The accurate way to read `rit`'s README: **cross out "verify claims" and write "make the
bookkeeping around claims tamper-evident."** `lara`'s current spec already reads accurately; its
job now is to defend the **policy** as a first-class, evaluated object rather than a trusted
given, and to prove the **defeat layer** carries the contribution.

For `lara` specifically, the one claim that survives every version of this critique is the
**typed defeat layer**: dead-end-defeats-claim is a real capability a holistic reviewer cannot
produce, it is what the ARA data model uniquely enables, and it does not depend on the checker
laundering the model's leaf judgments. That — not Curry-Howard, not justification logic — is the
contribution to lead with.

---

## 11. Addendum (2026-07-25): the expressible fragment, verified against `rit`'s code

_`rit` has restructured since its README was written (the `formal/core/action/algorithms` layout is
gone; the package now lives in `src/rit/{formal,gate,action,admit,derive,grounding,store}` plus
benchmark `adapters/` and `eval/`). The claims below were checked against the current tree, not the
README._

### 11.1 What `rit`'s formal layer can literally say

The entire world-facing vocabulary (`src/rit/formal/primitives.py`) is five object kinds — GOAL,
EVIDENCE, FACT, RECORD, BASELINE — and six relations:

| Relation | Meaning |
|---|---|
| GROUNDS | evidence ⊢ fact (deterministic extraction, sha256) |
| ORDER | record ≤ record |
| BEAT | record vs. an external baseline constant |
| BOUND | ∀ run in cohort, lo ≤ value ≤ hi |
| ENTAIL | do the grounded records reach the goal (overclaim check) |
| CONTRADICT | two claims whose conjunction proves ⊥ |

A FACT is a natural number extracted from a log. The grammar (`src/rit/formal/grammar.py`) renders
each conclusion as a "decidable arithmetic fact" proved `by decide`, with preconditions (code hash,
GPU count) as *documented* hypotheses whose truth is checked by sha256 outside Lean. Even ENTAIL and
CONTRADICT are arithmetic over these scalars. **So the observation "rit can only express numerical
comparison" is correct for the implemented system** — comparisons and interval bounds over
extracted numbers.

The ceiling is not Lean (which can state arbitrary mathematics) but structural, and two-fold:

1. **The grounding interface.** The only place the world enters is deterministic extraction of
   values from bytes. Any empirical claim must therefore be *reducible to a predicate over
   extractable quantities*. "top-1 = 78.4%" fits; "the gain comes from the attention mechanism,"
   "this generalizes beyond the benchmark," "the comparison was fair" have no extractor.
2. **The auto-discharge portfolio.** The solver tries `decide` → `omega` → `simp`, capping the
   analytic side at decidable / linear-arithmetic goals in practice.

`rit` concedes this in its own source: `primitives.py` states that "'why' as VALUE
(important/novel) is NOT formalizable and is kept as context, never proven," and the `@claim`
convention already conceded the NL sentence is unchecked.

### 11.2 The silent narrowing — the sharpest form of the delta

Every claim a paper makes reaches `rit`'s kernel only through a **narrowing step**: from "method M
is faster" to "this extracted number beats that constant." That step is itself an inference, and a
defeasible one — it presumes the runs are comparable, the metric is the right operationalization,
the cohort is representative. `rit` performs it silently and unverifiably, in the gap between the
NL sentence and the theorem; the claim either shrinks to its numeric shadow (`improves(M,D)` becomes
`2875 < 3225`) or survives only as an unverified comment. `lara` types exactly this step: the leaf
supports the claim *via a named scheme* whose critical questions must be discharged or stand as
located holes, and which can be undercut. Our predicates need not be machine-decidable because
their role is argumentative, not deductive; the decidable numeric fragment is what we delegate to
a strict backend — which is the slot `rit` fits into.

### 11.3 `rit`'s non-kernel defeat machinery is a shadow argumentation framework

To handle disagreement `rit` had to build substantial machinery *outside* the kernel: a verdict
lattice, collision detection ("same premises, different conclusion"), evidence-tier winner-picking,
dispute branches, weakest-link trust roll-up. Structurally, collisions are rebuttals, "missing
premises" are undischarged critical questions, and tier-based resolution is a preference-based
defeat relation — an ad hoc, unproven argumentation layer. Their design doc lists honest
aggregation as an open problem that "getting this wrong makes the whole ledger dishonest"
(`rit/notes/DESIGN.md` §7b#3). That layer is `lara`'s object of study, with the grounded-labelling
metatheory mechanized.

### 11.4 The composition, stated as engineering

- **`rit` as a `lara` strict backend / leaf oracle.** `rit`'s portable kernel certificates and
  K-tier groundings are exactly the shape of opaque certificate the `Lara.Strict` seam accepts;
  its T0–K tiers map onto our leaf provenance vocabulary. This upgrades our leaves from
  "declared" to "machine-rechecked" without widening our TCB.
- **`lara` as `rit`'s aggregation semantics.** Replacing their AND/OR + collision heuristics with
  compilation to a Dung framework and grounded labelling would give their roll-up a proven
  propagation story — a principled answer to their open problem §7b#3.

Neither subsumes the other: a fully `rit`-verified artifact can still be *defeated* (valid
measurement, undermined setup), and a fully `lara`-justified argument can still rest on fabricated
leaves `rit` would catch. They compress the world into bytes; we adjudicate what the bytes are
allowed to mean.
