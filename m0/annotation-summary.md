# M0 annotation summary — 60-claim sample, first full pass

_2026-07-22. Inputs: `m0/sample.tsv` (60 claims), `m0/annotations/*.yaml` (27 artifacts,
8-field schema per `annotations/SCHEMA.md`), `m0/double-annotation.tsv`. Provenance:
per-artifact annotation by independent AI annotators (ai-executed, one agent per artifact,
shared codebook, no cross-talk); aggregation and adjudication by the session AI; human
review still pending. Corpus pin `62e9b54`._

## 1. Double annotation (claim-type field, 18 claims)

Protocol: second annotator = a *blind* agent on a different model (Opus), given only the
rubric and `claims-index.tsv`, forbidden from reading any label file.

- **Raw agreement 14/18 (77.8%); Cohen's κ = 0.73** (substantial).
- All 4 disagreements adjudicated to the blind annotator's label
  (`double-annotation.tsv`): fre C01 → generalization, lbcs C05 → comparative,
  robust-clip C07 → negative-result, rebench-triton_cumsum C09 → negative-result.
- **Rubric lesson**: annotator A systematically typed the *mechanism/subject* where the
  precedence rule demands typing the *headline outcome* — both negative-result misses
  are cases where a "fails/cannot-reach" reading fit and should have won by precedence.
  Codebook amendment for the full pass: apply the precedence check ("does a
  negative-result reading fit?") before any content judgment.
- Adjudications propagated to `claim-types.tsv`, `sample.tsv`, and the four annotation
  files. Post-adjudication stratum counts: comparative 17, causal 13, descriptive 9,
  implementation-behavioral 7, negative-result 9, generalization 5 (sample drawn at the
  pre-adjudication counts; not redrawn).

## 2. Aggregates over the 60 annotated claims

**Inference schemes.** Annotators coined 22 raw names; they normalize to **9 families**:

| Family (raw names merged) | Claims |
| --- | --- |
| controlled_comparison (+cost-accounting, resource, noninferiority, compute-matched, cross-model-transfer, spectral variants) | 25 |
| intervention/ablation (component_ablation, component_substitution, dose_response) | 14 |
| observation/measurement (cross_run_observation, exhaustive_pairwise, case_demonstration) | 7 |
| analytic (analytic_proof, analytic_bound_with_consequence_check) | 4 |
| benchmark/stress evaluation | 3 |
| code_inspection (+plan_vs_shipped_diff) | 3 |
| statistical_correlation | 2 |
| inductive_generalization | 1 |
| blind_paired_human_evaluation | 1 |

Top-3 families cover 46/60 (77%); all 60 are assignable to the 9 families.
**→ open question §8 #2**: a scheme vocabulary of ~9 entries suffices for this sample;
comparison + ablation alone carry two-thirds of the corpus.

**Strict certifiers** (§8 #1): domain-checker 35, none 21, lp 3, reference-nd 1.
The 35 domain-checker calls are overwhelmingly *arithmetic re-checks of reported tables*
(deltas, ratios, aggregations, inequalities) plus a few code inspectors. **The smallest
useful adapter portfolio is one rational-arithmetic/table-recheck checker and one static
code-inspection checker — not LP** (3 calls, all speculative). The single reference-nd
call (tournament call-count arithmetic) is plausibly also arithmetic.

**Typed attacks** (§8 #3): 194 dead-end classifications → **4 undercut, 0 rebut,
0 undermine, 190 none (98%)**. Confirms the corpus-map prediction (most dead ends are
rejected alternatives, not defeaters) far more strongly than expected. Two caveats:
(a) rebut/undermine are entirely unexercised in this sample — expectedly, since the
corpus is polished, peer-reviewed top-venue work; per decision N29 (2026-07-22) they are
exercised through *self-authored adversarial reports/mutations* against corpus claims at
language-testing time, extending the rejection-class negative-suite discipline to the
defeat layer, not through corpus mining; (b) two annotators found counter-evidence living *outside*
dead_end nodes (experiment nodes in fix_embedding; score-filtered runs in triton_cumsum)
— **the attack-candidate walk must cover the whole trace, not only dead ends**.

**Leaf granularity** (§8 #5): per-result-cell 45, mixed 7, per-experiment-claim 6,
per-run 2. **→ per-result-cell is the default leaf grain (75%)**.

**Critical questions**: 249 total. Mandatory: 105 met, **68 unmet-gap (39%)**,
3 unmet-defeater; optional: 34 met, 39 unmet-gap. The corpus systematically leaves
mandatory CQs (seeds/variance, statistical significance, baseline completeness) unstated
— strong support for LARA's gap-vs-defeater distinction: these must surface as *gaps*
(holes), not defeat edges, or nearly every claim would be spuriously attacked.

## 3. Construct-coverage assessment (the ≥80% exit gate)

21/60 claims (35%) carry coverage flags. Adjudicated into three kinds:

**(a) Absorbed by existing design decisions — 12 claims.** Open-class/universal/
asymptotic scope (all-in-one C03, bbox C05, ftrl C01, self-expansion C04,
stochastic-interpolants C01, mechanistic-understanding C04, lbcs C03) is exactly what the
`nl` / `formal` / `binding` split carries: the atom instantiates per tested case; claimed-
class-vs-tested-set lives in the binding and is audited on the faithfulness axis, not
checked. Heterogeneous support strands (pinn C03, rice C01, lbcs C03) are multiple `arg`
declarations for one claim — already required by the no-accrual decision (N19). Bundled
conjunctive claims (sample-specific-masks C05, sapg C01, sapg C06) are claim-splitting
conventions for the elaborator, not new constructs.

**(b) Genuine candidate constructs — 6 claims (10%).** Equivalence/non-inferiority as a
first-class scheme with its own defeat conditions (all-in-one C06); monotone-functional-
relationship propositions (pinn C01); parametric growth-rate claims (nanogpt_chat_rl C04);
stochastic measurand dispersion — a leaf whose value is a distribution, not a number
(triton_cumsum C09); negative existentials over code (rust_codecontests C09); graded/
undefined predicates (what-will-my-model-forget C03, resolvable by binding discipline).

**(c) Evidence-model findings — 3 claims.** Attack walk beyond dead ends
(fix_embedding C12); dead-end-as-*support* (restricted_mlm C14 — a dead end is the
claim's evidence, which the attack vocabulary cannot say); conflicting duplicate reports
of one result cell (bridging-data-gaps C05 — neither attack nor provenance grade).

**Preliminary gate verdict: PASS — ~90% of sampled argument shapes are expressible**
with the 9 scheme families + existing design decisions, without opaque-leaf encoding of
whole reasoning steps; the 10% residue (kind b) is a concrete, finite construct wishlist
for the v0.1 freeze rather than an open-ended gap. Conditions: the kind-(a) annotation
conventions must be written into the spec; rebut/undermine are exercised via authored
adversarial attack cases (decision N29) alongside the negative suite; kind-(c) requires
trace-walk and evidence-model decisions (support-from-dead-end, result-cell conflict) in
spec §7/§8 terms.

## 4. Known limitations

- All annotation is single-pass AI per artifact; only the claim-type field was
  double-annotated. Full-schema double annotation on a subset (especially attack
  decisions and CQ mandatory/optional calls) is still open.
- Dead-end caps applied in 3 rebench artifacts (15 of 70/40/95), rules recorded in each
  file's `deadend_cap`.
- The 4 real attack edges all come from agent-run artifacts (rebench) or method-failure
  claims (ttma) — paperbench papers' polished traces contain almost no self-attacks;
  defeat-layer evaluation therefore uses self-authored adversarial reports against corpus
  claims (decision N29), not corpus mining.
