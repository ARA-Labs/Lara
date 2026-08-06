# Corpus-unit lowering conventions (M5 tracker #48, T2)

How the 60 claims of `m0/sample.tsv` lower into `.lara` units under
`corpus-units/corpus-v1.policy.lara`. Every unit's header comment cites this
file; per-claim judgment calls are recorded in that header, never silently.
Plan: M5 T2 corpus units (tracker #48; freeze `docs/m5-freeze-checklist.md`).
Exemplars:

- `sample-specific-masks/C06` — justified (all mandatory CQs met).
- `adaptive-pruning/C03` — gap (mandatory CQ unmet ⇒ E2-style, no arg).
- `test-time-model-adaptation/C04` — defeated (complete arg + licensed undercut).

## Unit shape

- One unit per sampled claim: `corpus-units/<artifact>/<claim_id>/unit.lara`,
  where `<artifact>`/`<claim_id>` match `m0/sample.tsv` exactly.
- Header: `artifact <artifact> at sha256:<digest>` / `policy corpus-v1` /
  `use backends [nd@1]` (a unit carrying an `ra@1` certificate additionally
  selects `ra@1`: `adaptive-pruning/C04`). The digest is the first 12 hex
  chars of `sha256("ara-paperbench@62e9b54 <artifact>")` — one digest per
  artifact, shared by its units (the corpus pin is the trusted-input
  identity).
- Claim block fields in order `nl`, `formal`, `binding`. Claim id is the
  lowercased annotation id (`C04` → `c04`).
- `binding = { author = m0-annotator, audit-status = reviewed|unreviewed }`:
  `reviewed` iff the sample row has `double_annotate = yes` (the adjudicated
  subset), else `unreviewed` (single-pass AI annotation, human review pending).
- Golden-oracle comment at the bottom: compiled AF, labels, claim status, with
  the spec-§ rationale, exactly as the worked examples do.

## Formal atoms

- Constants by convention. Thresholds, ratios, and table cells live in
  `nl`, `binding`, and leaf `refs`; constants are snake_case
  (`apt`, `mnli`, `train_cost_at_parity`). SOLE exception: the Family-10
  certificate-checked atoms (`rational_drop_recheck` premises/conclusion,
  issue #57), whose cells are `num` literals in canonical spelling (`50`,
  never `50.0`). Both production drivers share `canonNum`.
- The scheme instance fixes the atom: pick the policy rule via the family map
  below, instantiate its variables with claim constants, and let the claim's
  `formal` be exactly the rule's instantiated conclusion.
- Bundled/conjunctive claims: pick the binding conjunct (e.g. the
  nearest-competitor convention of `sample-specific-masks/C06`); the rest
  stays in `nl` and refs, noted in the header.
- Negative-result claims lower as a POSITIVE conclusion over negative-content
  constants (`contributes(entropy_only_fitness, cma_es_tta,
  adaptation_collapse)`) — or through a `null_*` dual rule when the claim is
  genuinely the negation of a comparison/benchmark/correlation conclusion.
  Never argue both sides of a declared contrary pair in one unit unless the
  forced mutual rebut edges are declared too (attack completeness is
  arg-conclusion-level).
- `nl` is one ASCII line with no inner double quotes (spell `+-`, `x`, `~=`).

## Scheme family map (annotation `scheme` → corpus-v1 rule)

| Annotation scheme names | corpus-v1 rule |
| --- | --- |
| controlled_comparison, cost_accounting_comparison, cross_model_transfer_evaluation, noninferiority_comparison, resource_benchmarking_comparison, component_spectral_comparison, compute_matched_equivalence | `controlled_comparison(S, B, Q, D, Exp)` (dual `null_comparison`) |
| component_ablation, component_substitution, dose_response | `component_ablation(C, S, Q, Exp)` |
| cross_run_observation, exhaustive_pairwise_measurement, case_demonstration | `measurement(P, S, Exp)` |
| analytic_proof, analytic_bound_with_consequence_check | `analytic_argument(P, Prf)` |
| benchmark_evaluation, adversarial_stress_test | `benchmark_evaluation(S, B, Q, Exp)` (dual `null_benchmark`) |
| code_inspection, plan_vs_shipped_diff | `code_inspection(P, Src, Insp)` |
| statistical_correlation | `statistical_correlation(X, Y, S, Exp)` (dual `null_correlation`) |
| inductive_generalization | `inductive_generalization(P, C, Exp)` |
| blind_paired_human_evaluation | `human_evaluation(S, B, Q, Exp)` |

The strict-flavored annotations lower through `analytic_argument` (defeasible)
by default. Since #57 the rational-arithmetic re-check adapter (`ra@1`)
exists: `adaptive-pruning/C04`'s derived-arithmetic leg migrates onto the
strict `rational_drop_recheck` rule (Family 10) under a checked certificate —
the headline claim itself stays on its defeasible family and its status is
unchanged. The remaining strict-flavored units await their own certifier
backends, noted per unit.

## Leaves

Declare ONLY leaves the unit uses: the principal premise, each discharged CQ's
leaf, and attack roots. Per-result-cell detail folds into the premise leaf's
`refs` (per-result-cell is the corpus's dominant grain; the refs keep each
cell addressable). Unused leaves are legal but noise — E2-style gap units keep
exactly the leaves the paper does supply (premise + met CQs).

- `kind = observed` for measured result cells / trace records; `attested` for
  setup, procedure, and paper-text assertions. `assumed` is never used — an
  obligation without evidence is a gap, not an assumption.
- `provenance = ai-executed` everywhere (the lowering and its annotation
  source are AI passes; `user` is reserved for researcher-authored leaves).
- `refs` entries contain no spaces/commas/brackets — join with `#` and `-`
  (`logic/experiments.md#E06-Metrics`, `trace/exploration_tree.yaml#N02-N03`).

## Critical questions: the status map

Map each annotated CQ onto the nearest policy CQ of the chosen rule; then:

- annotated **met** → `discharge <question> with <leaf>` (leaf cites the
  annotation's basis).
- annotated **unmet-gap** on a policy-MANDATORY question → **do not declare
  the arg** (E2-style unit). An open mandatory obligation is an
  IncompleteArgument rejection, never a hole in an accepted unit; `gap` is
  produced exactly one way — empty complete support. This applies even when
  the annotator rated the CQ optional (uniform-standard rule: the policy call
  wins; record the divergence in the header — see `adaptive-pruning/C03`).
- annotated **unmet-defeater** → the arg IS declared complete (discharge the
  contested question with the paper's own claimed basis) and the defeating
  evidence forms a leaf-rooted challenge arg concluding the rule's exception
  atom, with `undercut dX a1.rule` (see `test-time-model-adaptation/C04`).
- **no matching annotated CQ** for a policy-mandatory question → discharge
  ONLY with an honest, citable basis from the annotation (e.g. margins orders
  of magnitude beyond run noise), recording the judgment in the header;
  otherwise the unit is E2-style gap.
- optional policy CQs: discharge when the annotation supports it; when unmet,
  declare the hole explicitly with `open <question> as <question>` — the
  checker's question accounting (R5) requires EVERY rule question to be
  either discharged or opened, and an open OPTIONAL question is excluded from
  the obligation set (the arg stays complete, the claim's status is
  unaffected; see `bam/C05`).

## Attacks

The corpus is polished top-venue work: rebut/undermine pressure comes from
authored adversarial mutants (decision N29, T1 rerun), not corpus mining. The
only corpus-native attacks are undercuts:

- dead-end annotations with `decision: undercut`
  (rebench-nanogpt_chat_rl N604, rebench-fix_embedding N603/N759,
  test-time-model-adaptation N03), and
- the `unmet-defeater` CQs (fre C04 `within_noise`,
  rebench-triton_cumsum C09 `measurement_artifact`,
  test-time-model-adaptation C04 `confounded_ablation`).

Pattern: `leaf uN : <exception atom instance>` (kind observed, refs = the
dead-end/counter-evidence), `arg dN : challenges(<question>(a1)) by leaf(uN)`,
`undercut dN a1.rule`. An unattacked undercutter drives the support out ⇒
claim `defeated`. If a mandatory CQ of the same arg is independently
unmet-gap, the gap rule wins (no arg to attack) and the undercut evidence
stays as a header note — the status is `gap`, not `defeated`.

## After writing a unit

Add its row to `corpus-units/MANIFEST.tsv`
(`group  artifact  claim_id  claim_type  double_annotate  expected_status`,
tab-separated, claim_type from `m0/sample.tsv`), then regenerate:

```
cabal exec -- runghc --ghc-arg=-package --ghc-arg=lara scripts/gen-corpus-units.hs
```

The generator fails loudly on parse/elaboration/replay errors;
`expected.json`'s computed status must equal both the manifest column and the
unit's golden-oracle comment. Any mismatch is a bug in the unit (or, if the
policy genuinely lacks vocabulary, in the policy — with a note in the plan
doc), never a silent re-annotation.
