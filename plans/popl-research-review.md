# LARA: deep research review and POPL plan

_Research snapshot: 2026-07-20. This is an adversarial design review, not a claim that the cited
preprints have passed peer review._

## 1. Executive verdict

The central problem is real and the producer/checker architecture is sound as a direction. The
current proposal, however, gives LP realization more work than the theorem supports and gives the
prototype checker a stronger trust claim than the code supports. It also treats attack extraction
and absence of a certificate too casually. Those are correctable, but they change the center of the
paper.

The strongest POPL version of LARA is:

> A small proof-carrying language for policy-relative research warrants. Programs name evidence
> leaves, instantiate strict or defeasible warrant schemes, discharge scheme-specific critical
> questions, and declare typed rebut/undercut/undermine relations. A checked compilation produces a
> structured argumentation framework and a replayable claim status. The guarantee is certificate
> validity, dependency accountability, and policy-relative coverage, not empirical truth.

LP remains useful as the strict proof-term fragment. It should not be the semantic center unless a
corpus study shows that research warrants are predominantly modal-deductive structures.

POPL 2027's submission deadline was 2026-07-09, so as of this review the realistic main-conference
target is POPL 2028. The current POPL call asks for principled, enduring PL contributions and, since
2027, strongly encourages submission-time proof scripts when mechanized proofs are a main
contribution. Plan the project around a mechanized language result, not only a checker demo.

## 2. Corrections to the current ideas

### Critical

1. **Realization does not guarantee ARA lowering.** Artemov's theorem is `S4 ⊢ F` implies
   `LP ⊢ F^r` for some realization. Its input is an already-formal S4 theorem. It says nothing about
   whether natural-language claim `C`, evidence `E`, or `E → C` was faithfully formalized, nor
   whether the latter is a theorem. Use realization only for an explicitly modal strict fragment.

2. **The current checker trusts arbitrary logical constants.** `ConstantSpec` is input data and
   `DConst` checks only membership. It does not recognize A0–A4 instances. A caller can register
   `c : P` and obtain a checked `P`. Either implement fixed axiom-schema recognition or include the
   constant-spec producer in the TCB. The proposal's current "baked into the kernel" claim is false.

3. **Empirical support is not deductive implication.** `supported(E,C)` does not entail `C` by LP.
   A bridge from evidence to claim is a non-logical, usually defeasible warrant rule. It must be
   named, instantiated, and open to undercutting. Otherwise the system certifies a hidden axiom.

4. **No certificate is not underivability.** A checker decides whether a supplied certificate is
   valid. Failure to receive one means missing support, producer failure, or timeout; it does not
   prove no term exists. Define `gap` syntactically through explicit holes/mandatory obligations, or
   implement a complete decision procedure and state its scope.

5. **Attack construction is part of the trust boundary.** If an LLM can emit arbitrary attack edges,
   the grounded fixpoint is deterministic but the verdict is still model-controlled. Attacks need
   typed constructors and checked targets. A dead end is evidence of a failed route, not automatically
   a defeater of every claim it touches.

### Major

6. **Grounded `undec` is broader than mutual defeat.** Even and odd cycles and undecidedness
   propagation can yield `undec`. `contested` should mean unresolved under the selected semantics,
   with the report explaining the responsible SCC/attack provenance.

7. **Provenance is not an attack.** `user`, `ai-executed`, or `certified` labels support an admission
   policy and audit report. Low-trust provenance does not logically rebut or undercut an argument.

8. **"Complete warrant" needs a relative definition.** Scientific argument completeness is not
   mechanically decidable from a finite artifact without a closed-world assumption. A defensible
   definition is scheme-completeness: every premise and critical question required by the selected,
   versioned warrant policy is discharged or surfaced as a hole.

9. **Property testing is not a soundness proof.** QuickCheck is valuable implementation testing.
   POPL-level claims need formal definitions, paper proofs, and preferably mechanized main theorems.

10. **The LLM risk is not confined to leaves.** It also chooses the proposition, warrant scheme,
    attack type/target, and what to omit. Recent autoformalization work reports a material gap between
    compile success and semantic faithfulness. Evaluate every boundary separately.

11. **The Lean analogy is architectural only.** LP proof polynomials are explicit proofs and have
    close ties to typed combinatory logic, but LARA's defeasible policies, untrusted leaves, and graph
    semantics are not "Lean with CIC swapped for LP." That phrase invites avoidable objections.

12. **Composition alone is a weak novelty claim.** Dung/ASPIC+, proof certificates, semantic
    publishing, and untrusted-producer/checker systems all exist. The novelty must live in a precise
    language abstraction and theorem: for example, a typed compilation from warrant programs to
    structured argumentation that preserves dependency provenance, attack targets, open obligations,
    and claim status.

## 3. Proposed language architecture

### 3.1 Program layers

Keep five syntactic classes distinct:

```text
proposition p   ::= opaque natural-language claim id | typed domain proposition
leaf        l   ::= observed | attested | assumed | certified
rule        r   ::= strict scheme | defeasible warrant scheme
argument    a   ::= leaf l | apply r [a1, ..., an]
attack      k   ::= rebut a a | undercut a (a.r) | undermine a l
obligation  o   ::= need-premise ... | answer-critical-question ...
```

A complete program also declares the artifact snapshot, policy version, claim roots, provenance,
source spans, and certificate hashes. JSON is the wire encoding; a canonical presentation syntax is
the paper/debugging language. Both decode to one abstract syntax.

### 3.2 Example direction

```lara
artifact paper_17 at sha256:...
policy empirical-v1

claim c1 : "Method M improves accuracy on distribution D"

leaf e1 : reports(exp_3, effect(M, accuracy, D, +2.1))
  provenance = ai-executed
  refs = [evidence/table_2.csv#row=mean]

arg a1 : supports(c1) by controlled_experiment(e1)
  discharge randomization with leaf e2
  discharge adequate_power with leaf e3
  open external_validity

arg d1 : challenges(external_validity(a1)) by distribution_shift(e4)
undercut d1 a1.rule

status c1
```

This should report `gap` while `external_validity` is open. If it is discharged, the undercut may
make the support defeated or contested according to the graph. The checker never claims `c1` true.

### 3.3 Static judgments

The spec should define at least:

```text
Σ; Π; Γ ⊢ a : supports(p) ▷ L, O
Σ; Π; Γ ⊢ k : attacks(a, target)
Σ; Π ⊢ W wf
compile(W) = AF
AF ⊢ a ⇓ in | out | undec
W ⊢ p ⇓ justified | defeated | contested | gap
```

`Σ` is the fixed logical signature, `Π` the versioned warrant policy, `Γ` admitted leaves, `L` the
exact dependency set, and `O` unresolved obligations. Make dependency sets explicit in the judgment;
they are central to the accountability theorem.

### 3.4 Status aggregation

For the initial language, use a total, deterministic priority:

```text
gap       if there is no checked support argument, or a mandatory root obligation is open
justified if some support argument is in
contested if none is in and some support argument is undec
defeated  if support arguments exist and all are out
```

Require contrary conclusions to generate conflict attacks so incompatible claims cannot both become
`justified` under grounded semantics. State whether an open obligation inside one argument gaps only
that argument or the whole claim; the recommended design excludes incomplete arguments from the AF
and reports their holes alongside complete alternatives.

## 4. Required metatheory

The paper should target these results:

1. **Decidable checking.** Well-formedness, rule instantiation, obligation discharge, and attack
   typing terminate and are decidable for a finite policy/program.
2. **Axiom safety.** Every accepted strict constant is an instance of a fixed logical schema; no
   artifact or producer can extend `Σ` silently.
3. **Dependency accountability.** If an argument checks with dependency set `L`, every leaf used by
   its derivation is in `L`, and each member of `L` has a declared artifact reference/provenance.
   Strengthen to exactness if weakening is controlled.
4. **Compilation soundness.** Every node and attack in `compile(W)` comes from a checked source
   construct with matching target and source provenance.
5. **Status determinism and termination.** Finite grounded evaluation yields one labelling and one
   claim status under the aggregation definition.
6. **Status preservation.** A direct source semantics and compiled AF semantics agree.
7. **Diagnostic localization.** Rejected derivations and unresolved obligations identify a source
   span and rule/target, not merely a global failure.
8. **Codec adequacy.** Presentation syntax and JSON decode to alpha-equivalent ASTs; canonical print
   round-trips. This is engineering, but it matters for replayability.
9. **Optional LP conservativity.** The strict fragment agrees with standard LP under an admissible
   constant specification. Realization belongs here, not in the ARA-lowering theorem.

Mechanize items 1–6. A small Rocq, Lean, or Isabelle development is more persuasive than relying on
the Haskell implementation as its own model. The 2027 POPL call explicitly asks authors to expose
mechanized proof scripts and non-standard axioms when proofs are a main contribution.

## 5. Detailed work plan

### Phase A: semantic corpus study (3–4 weeks)

- Sample 50–100 claims across the 30-paper corpus, stratified by descriptive, comparative, causal,
  generalization, negative-result, and implementation/behavioral claims.
- For each, annotate propositions, evidence granularity, warrant scheme, premises, critical
  questions, rebut/undercut/undermine candidates, and unresolved holes.
- Double-annotate at least 20–30% and adjudicate disagreements.
- Exit: a finite set of constructs covers at least 80% of sampled argument shapes without encoding
  whole reasoning steps as opaque leaves.

### Phase B: language v0.1 (4–6 weeks)

- Freeze abstract and presentation syntax, name resolution, policy modules, leaf admission, strict
  and defeasible rules, obligations, typed attacks, and claim aggregation.
- Write three complete examples and three intentionally rejected examples.
- Specify the JSON codec separately from the language.
- Exit: independent readers can derive the expected diagnostics and status from the spec.

### Phase C: mechanized metatheory (6–10 weeks, overlaps B)

- Formalize syntax, checking, source semantics, AF compilation, and grounded labelling.
- Prove the results in Section 4; record all axioms.
- Keep the proof development as an anonymizable artifact from day one.
- Exit: no `admit`/`sorry` in main theorems; a replay command checks the development.

### Phase D: compiler/checker (5–7 weeks)

- Implement parser, resolver, fixed axiom-schema recognizer, policy checker, dependency extraction,
  compiler, status engine, canonical printer, JSON codec, and structured diagnostics.
- Differential-test status against the mechanized executable semantics or a separately implemented
  reference.
- Add mutation generators for wrong formulas, undeclared leaves, hidden policy extension, bad attack
  targets, open obligations, cycles, and codec corruption.
- Exit: all examples replay; every mutation class is rejected or assigned the specified status.

### Phase E: untrusted ARA elaborator (4–6 weeks)

- Split proposition formalization, leaf extraction, rule selection, obligation filling, and attack
  extraction into logged stages.
- Retain rejected candidates and checker feedback; cap repair loops and support explicit abstention.
- Do not allow the model to define policy rules or logical schemas at runtime.
- Exit: one full artifact compiles without hand-editing; every accepted construct has a source span.

### Phase F: evaluation (6–8 weeks)

- Freeze a blinded held-out set and annotation guide before final experiments.
- Baselines: schema-only JSON, unconstrained LLM graph/prose, LARA without typed attacks, LARA without
  critical-question obligations, and human-authored certificates.
- Report formalization precision/recall by construct, checker yield, abstention, repair iterations,
  defect detection/localization, status agreement, runtime, certificate size, and policy sensitivity.
- Include qualitative cases for each attack type and each status.
- Exit: all four evaluation axes in the proposal have evidence, not only examples.

### Phase G: paper (continuous; final 6 weeks)

- Write the calculus and theorem statements before implementation details.
- Position against structured argumentation and semantic publishing, not only theorem proving.
- Present the LLM as an untrusted producer and the formalization gap as measured residual risk.
- Package anonymized code, mechanization, policies, corpus annotations, and replay scripts.

## 6. Evaluation design in detail

### Gold data

The unit should be a claim-warrant instance, not a paper. Report the number of claims, arguments,
leaves, obligations, and attacks. Separate development, tuning, and held-out sets. Use two domain-aware
annotators on the held-out subset and report agreement per construct; raw status agreement alone can
hide compensating annotation errors.

### Baselines and ablations

- **Schema-only:** same JSON fields and references, no logical/policy/attack checking.
- **LLM-only:** model directly emits status plus prose explanation.
- **Untyped graph:** nodes and arbitrary attack edges, grounded evaluation only.
- **No-CQ:** warrant rules without mandatory critical questions.
- **No-defeat:** checked support derivations without attacks.
- **Human certificate:** upper bound on producer yield and lower bound on required repair.

`rigor-reviewer` can show complementary defect coverage and human-facing usefulness, but its
accept/reject score is not ground truth for LARA's four states.

### Metrics

- Proposition, leaf, rule, obligation, and attack precision/recall/F1.
- Certificate acceptance and semantic-faithfulness rates, jointly and separately.
- Correct abstention, false acceptance, and false gap rates.
- Status macro-F1 and per-state confusion matrix on adjudicated gold.
- Mutation detection and exact/near source-location accuracy.
- Dependency audit precision/recall: reported load-bearing leaves versus actual checked dependency.
- Runtime and certificate size by graph size; grounded evaluation should be a minor component.
- Sensitivity across policy versions and admission thresholds.

### Claims the experiments may support

- The checker prevents structurally invalid or policy-incomplete certificates from receiving a
  non-gap status.
- Typed attacks reduce unsupported defeat edges relative to an unconstrained graph producer.
- Critical-question obligations expose omissions that schema validation misses.
- LLM generation is useful only to the measured extent shown by semantic-faithfulness and abstention.

Do not claim that LARA establishes scientific truth, exhaustive completeness, or reviewer agreement.

## 7. Literature map

### Must read

1. **Artemov 2001, "Explicit Provability and Constructive Semantics."** Exact LP axioms, constant
   specifications, soundness/completeness, and realization. Theorem 9.4 is explicitly theorem-to-
   realization, which bounds its relevance to LARA lowering.
   <https://sartemov.ws.gc.cuny.edu/files/2014/01/Artemov-Explicit-Provability-and-Constructive-Semantics.pdf>
2. **Dung 1995, "On the Acceptability of Arguments..."** Abstract frameworks and grounded semantics.
   <https://doi.org/10.1016/0004-3702(94)00041-X>
3. **Modgil and Prakken 2014, ASPIC+ tutorial.** Structured arguments, rebut/undercut/undermine,
   preferences, and conditions for rationality postulates.
   <https://doi.org/10.1080/19462166.2013.869766>
4. **Necula 1997, "Proof-Carrying Code."** The correct producer/certificate/checker ancestor.
   <https://doi.org/10.1145/263699.263712>
5. **Miller 2015, "Foundational Proof Certificates" (2014 manuscript).** A broader certificate-language
   precedent: define certificate semantics against a small proof-theoretic kernel.
   <https://www.lix.polytechnique.fr/~dale/papers/appa2014.pdf>
6. **Clark, Ciccarese, and Goble 2014, "Micropublications."** Direct prior work on machine-readable
   scientific claims, evidence, support, challenge, and attribution. LARA must explain the delta:
   checked warrant programs and status semantics rather than an RDF/OWL representation model.
   <https://doi.org/10.1186/2041-1480-5-28>
7. **AIF specification.** Prior typed graph vocabulary for inference, conflict, and preference. Use
   it as an interchange/related-work reference, not as the checking semantics.
   <https://www.arg-tech.org/wp-content/uploads/2011/09/aif-spec.pdf>
8. **Yu and Zenker 2020, schemes and critical questions.** Supports policy-relative completeness:
   complete evaluation of a scheme instance requires addressing its relevant critical questions.
   <https://doi.org/10.1007/s10503-020-09512-4>
9. **Pandžić 2022, defeasible argumentation in justification logic (two papers).** The closest
   prior art: defeasible arguments as object-level justification terms, with rebutting,
   undercutting, and undermining attacks. Validates the terms-as-arguments design and bounds the
   novelty claim — see `../docs/term-calculus-decision.md` for the delta LARA must defend.
   <https://doi.org/10.3233/AAC-200536>, <https://doi.org/10.1007/s10472-021-09765-z>

### Should cite

9. **van Benthem and Pacuit 2011, dynamic evidence-based belief.** Evidence families, aggregation,
   and update; useful semantic contrast to scalar threshold metadata.
   <https://dare.uva.nl/record/1/354377>
10. **van Benthem, Fernández-Duque, and Pacuit 2014.** Evidence and plausibility in neighborhood
    structures. <https://arxiv.org/abs/1307.1277>
11. **LeanDojo (NeurIPS 2023).** Checked LLM proof production and retrieval.
    <https://proceedings.neurips.cc/paper_files/paper/2023/hash/4441469427094f8873d0fecb0c4e1cee-Abstract-Datasets_and_Benchmarks.html>
12. **Draft, Sketch, and Prove (ICLR 2023).** Informal-to-formal sketches guiding checked proof
    search. <https://arxiv.org/abs/2210.12283>
13. **Baldur (FSE 2023).** Whole-proof generation and repair in Isabelle.
    <https://people.cs.umass.edu/brun/pubs/pubs/First23fse.pdf>
14. **Beyond Compilation (2026 preprint).** Direct warning that typechecking/compilation and semantic
    faithfulness differ; use cautiously until peer reviewed. <https://arxiv.org/abs/2606.31002>
15. **EG-VAR (2026 preprint).** Very close recent architecture for tool-attested empirical claims in
    Lean; it narrows novelty and provides a useful trust-boundary comparison. It explicitly leaves
    natural-language faithfulness and source-lift correctness outside its structural guarantee.
    <https://arxiv.org/abs/2607.12650>
16. **Workflow Run RO-Crate (2024).** Current provenance packaging for scientific workflows; LARA
    should reuse identifiers/provenance rather than invent another archive format.
    <https://arxiv.org/abs/2312.07852>
17. **POPL 2027 call.** Scope, evaluation criteria, and mechanized-proof expectations.
    <https://conf.researchr.org/track/POPL-2027/POPL-2027-popl-research-papers>

## 8. Recommended reading order

Read Modgil–Prakken, Artemov sections 5/8/9, Micropublications, FPC, and AIF first. Then freeze the
corpus annotation guide. Read the evidence-logic papers while designing policy semantics. Read
Beyond Compilation and EG-VAR before finalizing evaluation and novelty claims. LeanDojo/DSP/Baldur
are implementation precedents, not foundations of the calculus. A starter BibTeX database is in
`lara-related-work.bib`.

## 9. Venue calibration

The project is in POPL scope if the paper contributes a principled language and enduring formal
result. The current prototype plus four-state graph engine would be closer to CPP, CADE, COMMA, or a
workshop. To clear the POPL bar, the submission should lead with:

1. a novel typed warrant-certificate calculus;
2. a semantics-preserving compilation into structured argumentation;
3. mechanized accountability and status theorems;
4. an implementation with replayable diagnostics; and
5. an evaluation showing that the language catches and localizes errors on real research artifacts.

The ARA case study supplies importance and stress-tests the abstraction. It cannot substitute for the
language theorem, and the LLM should not be presented as the source of formal validity.
