# M5 — T2 corpus units (tracker #48)

Branch `m5-t2-corpus-units`. Scope: T2 of issue #48 — hand-lower a stratified
sample of M0 claims into `.lara` units, each a claim-support instance with a
golden verdict through both drivers. T3/T5/T6 follow separately.

## The sample is already drawn

T2 says "hand-lower a stratified sample of M0 claims (`m0/claims-index.tsv`,
sampling by claim type)". That sample exists: `m0/sample.tsv` — 60 claims,
seed-42 rerun-identical draw, stratified by the six claim types with
largest-remainder quotas (comparative 17, causal 13, descriptive 9,
negative-result 9, implementation-behavioral 7, generalization 5 after
adjudication), 52 paperbench + 8 rebench, with a full 8-field annotation per
claim (`m0/annotations/*.yaml`) and an adjudicated double-annotation subset.
Redrawing would discard the annotation pass for no benefit; the unit set is
therefore **exactly the 60 rows of `m0/sample.tsv`**, one unit per claim.
PaperBench claims are included by construction (52/60), satisfying the
tracker's status-diversity note.

## Layout and derivation pipeline

Mirror the worked-examples pipeline (M4a) — same derivation path, same
freshness discipline, new root:

```
corpus-units/
├── corpus-v1.policy.lara            # one shared policy (below)
├── MANIFEST.tsv                     # group, artifact, claim_id, claim_type, unit dir, expected status
└── <artifact>/<claim_id>/
    ├── unit.lara                    # hand-lowered claim-support instance
    ├── unit.core.sexp               # generated canonical CheckInput envelope
    └── expected.json                # generated golden verdict (Haskell-only convenience)
```

- `scripts/gen-corpus-units.hs`: manifest-driven (like the mutant suite —
  discovery by `MANIFEST.tsv`, never by globbing); for each row, parse
  `unit.lara` + the shared policy, elaborate, `sourceCheckInput`, write
  `unit.core.sexp` and `expected.json`. Fails loudly on any elaboration or
  replay error and on manifest/filesystem disagreement.
- `test/CorpusUnitsSpec.hs`: freshness (re-deriving each committed
  `unit.core.sexp` and `expected.json` reproduces the bytes), manifest
  completeness (the 60 manifest rows are exactly the 60 `m0/sample.tsv` rows),
  expected-status agreement (manifest column == status in `expected.json`),
  and stratum coverage counts.
- `scripts/differential.sh`: add `corpus-units` to the required anchor roots
  (the `*.sexp` glob picks up `unit.core.sexp`; the root must be non-empty or
  the harness exits 2, same as `fixtures/`/`examples/`/`bundles/`).

## corpus-v1: one shared policy from the 9 scheme families

The M0 aggregation (`m0/annotation-summary.md` §2) normalizes all 60 claims to
9 scheme families. `corpus-v1.policy.lara` declares one defeasible rule per
family (plus null-conclusion duals where the sample's negative-result claims
need them), generic conclusion predicates, symmetric contrary pairs per
conclusion/negation, and one exception per family so undercuts are licensed.
All rules defeasible ⇒ R12 Path B holds as in empirical-v1/v2.

Conventions, fixed here once:

- **Constants only, no `num` literals** (the Lean `canon = id` caveat,
  `scripts/gen-corpus.hs` header). Quantitative content — thresholds, ratios,
  table cells — lives in `nl` strings, `binding`, and leaf `refs`; formal
  atoms use snake_case constants (`apt`, `cofi`, `mnli`, `acc_gap_0p9`).
- **CQ mandatoriness is a policy fact, not a per-claim fact.** A CQ is
  mandatory in corpus-v1 iff the M0 annotators predominantly marked that
  question mandatory for the family (the recurring trio: setup/baseline
  parity, measurement validity, variance/seeds). Per-claim disagreement with
  the policy call is recorded in the unit's comment header, not by forking the
  policy.
- **Lowering map from annotation to unit** (per claim):
  - `proposition_shape.sketch` → `claim … formal =` atom over constants,
    flattened to the family's conclusion predicate; the sketch's extra
    arguments move into `nl`/`binding` when they exceed the family arity.
  - `leaves` → `leaf` declarations (`provenance` kept; `kind` observed for
    result-cell leaves, attested for setup/procedure leaves; `refs` from the
    annotation refs).
  - `inference_scheme` → one `arg … by <family>(…)` per support strand
    (multiple strands ⇒ multiple args, per no-accrual N19).
  - CQ `met` → `discharge … with` a leaf matching the question pattern.
  - CQ `unmet-gap` on a mandatory question → **the arg is not declared**
    (E2-style). An argument with an open mandatory obligation is an
    IncompleteArgument *rejection* (`Check.checkArguments`), never a hole in
    an accepted unit; `gap` is produced exactly one way — empty complete
    support (M4a decision #8, `Grounded.statusC`). The unit keeps the claim,
    the premise leaf, and every met-CQ leaf; the header comment names the
    scheme instance and the missing obligation. The claim lands `gap` — 39%
    of mandatory CQs in the corpus are unmet, and this is the point of the
    gap-vs-defeater distinction.
  - CQ `unmet-defeater` (fre, rebench-triton_cumsum, semantic-self-consistency,
    test-time-model-adaptation) → an authored attack arg per the annotation's
    basis; the claim lands `defeated` (or `contested` if the attacker is
    itself attackable).
  - Dead-end `decision: undercut` (rebench-nanogpt_chat_rl N604,
    rebench-fix_embedding N603/N759, test-time-model-adaptation N03) →
    `undercut` edge from a leaf-rooted arg carrying the dead-end evidence,
    licensed by the family's exception.
  - `status <claim>` closes every unit.
- **Expected statuses**: mostly `justified` and `gap` (the corpus is polished
  top-venue work; per decision N29 rebut/undermine pressure comes from
  authored adversarial mutants, i.e. T1 rerun over these units, not from
  corpus mining). The handful of `defeated`/`contested` units come from the
  unmet-defeater and undercut rows above. Full status × attack-kind coverage
  is the worked examples' and the mutation suite's job, not the corpus's.

## Execution order

1. `corpus-v1.policy.lara` + three exemplar units spanning the three outcome
   shapes (justified, gap, undercut-defeated), pipeline green end-to-end
   (generator, spec test, differential root).
2. Batch-lower the remaining claims from `m0/annotations/*.yaml` following the
   exemplar conventions; regenerate; every elaboration failure is fixed in the
   unit (or, if the policy is genuinely missing vocabulary, the policy — with
   a note here).
3. `MANIFEST.tsv` finalized; `cabal test all`; `bash scripts/differential.sh`
   (Lean as oracle, byte-exact stdout + exit codes over all 60 new anchors).
4. Rerun mutation generation over the corpus anchors is **T1's open half**,
   not T2 — left to a follow-up so this diff stays reviewable.

## Execution record (2026-08-01)

All 60 sampled claims lowered and verified. Computed status distribution:
**9 justified / 48 gap / 3 defeated** — the corpus is honestly gap-heavy
(48/60 units cannot assemble a complete argument at corpus-v1's uniform bar,
dominated by unreported variance/seeds/significance), which is the M0
finding (39% of mandatory CQs unmet) surfacing as computed verdicts. The
3 defeated units are exactly the annotation's unmet-defeater cases realized
as licensed undercuts (test-time-model-adaptation/C04 `confounded_ablation`,
fre/C04 `within_noise`, rebench-triton_cumsum/C09 `measurement_artifact`);
the two dead-end-undercut candidates (rebench-fix_embedding/C12,
rebench-nanogpt_chat_rl/C04) land gap because a mandatory CQ is
independently unmet — the gap rule pre-empts, undercut evidence kept as
header notes.

Verification: `cabal test all` green (141 properties, incl. the 5 new
CorpusUnitsSpec pins); `bash scripts/differential.sh` positive
**pass=206 fail=0** (146 prior + 60 corpus anchors, byte-exact stdout +
exit codes, Lean as oracle), negative pass=54 fail=0.

Findings worth keeping:

- **R5 question accounting covers optional CQs**: every rule question must
  be discharged or explicitly `open <q> as <q>`; an omitted optional CQ is
  an R5 rejection. An open OPTIONAL question adds no obligation
  (`openMandatory` filters), so the arg stays complete and the status is
  unaffected. LOWERING.md updated; `bam/C05`, `fre/C01`,
  `rebench-restricted_mlm/C14`, `rebench-triton_cumsum/C09` exercise it.
- `differential.sh` discovers per-root anchor lists in a loop but
  concatenated a hardcoded list — adding a root requires touching both
  sites (fixed for `corpus-units`; the pass count is the guard).
- Scheme divergences recorded in headers: lbcs/C03 lowered analytic
  (annotator scheme `dose_response` — a convergence theorem; analytic is
  the honest family); stay-on-topic/C02 lowered `null_comparison`
  (claim_type comparative but the headline is an equivalence).
- Policy vocabulary gaps observed, none blocking (candidates for a future
  corpus-v2 / spec discussion): equivalence/non-inferiority margins
  (all-in-one/C06 — the missing margin is exactly the undischargeable
  `adequate_power`), open-class generalization quantifiers (bbox/C05),
  a significance-test CQ stronger than `variance_reported` (fre/C01),
  a significance CQ for the measurement family (stay-on-topic/C06), and a
  family-agnostic `records_consistent` bookkeeping CQ
  (rebench-restricted_mlm/C14). These are the kind-(b)/(c) residue of the
  M0 gate showing up in practice.

## Exit (T2 slice of #48)

- 60/60 sampled claims lowered, elaborating, with committed `.core.sexp`
  anchors and `expected.json` goldens.
- Both drivers byte-identical on all 60 anchors.
- Manifest ↔ sample ↔ filesystem agreement pinned by `CorpusUnitsSpec`.
