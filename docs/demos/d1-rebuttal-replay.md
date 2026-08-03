# D1 — Rebuttal replay: a paper + reviews + rebuttal as a sequence of checked programs

Issue [#62](https://github.com/EYH0602/lara/issues/62) (tracker [#61](https://github.com/EYH0602/lara/issues/61)); case-study material for the M7 paper package [#60](https://github.com/EYH0602/lara/issues/60) (T3). This is the **paper + reviews** population size that `examples/README.md` names but no prior example exhibits.

## What the demo shows

A peer-review exchange — the submitted paper, the review round, and the author's rebuttal — is **not a new calculus**. It is the *same* Dung framework at a larger population size (`examples/README.md`; spec §8, cross-framework non-monotonicity). Reviews are typed attacks on the paper's arguments; a rebuttal is new evidence leaves and counter-attacks. Grounded semantics re-adjudicates the whole graph each round, so a claim's status moves **non-monotonically** across rounds — `justified → defeated → justified` — with **no change to the trusted policy**.

The demo is three checked programs, one per round, in `examples/rebuttal-replay/{round0,round1,round2}/`. All three share **one artifact identity** and **one policy** (`rebuttal-v1`): the reviews and the rebuttal are *about* the paper, not a new artifact, and the reviewing standard is fixed. Only the argument population grows. The status trajectory is therefore a property of the growing graph under a constant replay identity — the demonstration the paper needs.

## Candidate: `adaptive-pruning` (APT)

Chosen from the ara-paperbench corpus as issue #62 flags: APT's kurtosis-salience ablation is **single-run**, so `corpus-v1`'s mandatory `variance_reported` critical question has no discharging leaf and the ablation claim lands `gap` (corpus unit `corpus-units/adaptive-pruning/C04`). That annotated gap is exactly what a rebuttal round can discharge when the author supplies variance runs — a real `gap → justified` transition, not a synthetic one. The demo carries the **defeasible ablation leg only**; C04's separate `ra@1` arithmetic certificate is orthogonal to the review exchange and is omitted here.

The demo constructs three claims from the paper so the review round has arguments to attack and the rebuttal round has a gap to discharge. Two use scheme families with **no** variance CQ (`benchmark_evaluation`, `measurement`), so they are honestly `justified` at submission without seeds; the third is the single-run ablation (`component_ablation`), `gap` at submission.

| Claim | Scheme family | Formal atom | Round-0 status | Role in the exchange |
| --- | --- | --- | --- | --- |
| `c_bench` | `benchmark_evaluation` | `performs(apt, dense_baseline, openllm_avg)` | justified | attacked two ways in R1, **reinstated** in R2 |
| `c_measure` | `measurement` | `holds(low_memory_footprint, apt)` | justified | attacked in R1, **conceded** in R2 |
| `c_kurt` | `component_ablation` | `contributes(kurtosis_salience, apt_llama2_7b, openllm_avg)` | gap | **gap → justified** discharge in R2 |

## The policy: `rebuttal-v1`

`rebuttal-v1` is `corpus-v1`'s defeasible families (1–9) verbatim, **minus** `corpus-v1`'s strict Family 10 (the `ra@1` re-check and its theory — so the demo stays defeasible-only and num-literal-free, like `empirical-v1/v2`), **plus** two defense contraries the exchange needs:

- `contrary not_fixed_protocol(S, B, Exp) fixed_protocol(S, B, Exp)` — lets Reviewer 1 **undermine** a benchmark argument's `protocol_fixed` leaf.
- `contrary protocol_confirmed(S, B, Exp) not_fixed_protocol(S, B, Exp)` — declared **one direction only**, so the author's confirmation leaf undermines the reviewer's leaf with no reverse edge — grounded reinstatement (the `empirical-v2` / E4 trick). A symmetric pair would force the reverse edge and collapse reinstatement into a contested 2-cycle.

Every other attack reuses existing `corpus-v1` vocabulary: the rebut fires through the declared `performs`/`not_performs` contrary; the two undercuts fire through the declared exceptions `measurement : measurement_artifact` and `null_benchmark : environment_mismatch`. Defense is policy vocabulary, not a new mechanism. Round 0 reproduces the corpus-unit gap verdict under this standard.

## Per-round lowering rationale

### Round 0 — submission (the paper alone)

The paper states three claims and supplies its evidence. `c_bench` and `c_measure` assemble complete arguments (their mandatory CQs are met; the optional `environment_match` / `confound_control` are left `open` with no status effect). `c_kurt` supplies the ablation premise and both met CQs (`single_variable`, `protocol_parity`) but **no** `variance_reported` leaf — the ablation is single-run. An argument with an open **mandatory** CQ is an `IncompleteArgument` rejection, so no argument is declared for `c_kurt`: its complete-support set is empty and it is `gap` (E2-style; the corpus-unit C04 mechanism).

### Round 1 — reviews (three reviewer comments as typed attacks)

Reviewer-cited external evidence enters as `attested` leaves with OpenReview refs. One comment per attack kind:

| Reviewer | Attack kind | Comment (paraphrase) | Lowering |
| --- | --- | --- | --- |
| R1 | **undermine** | "Your OpenLLM protocol wasn't held fixed — hyperparameters were tuned on the eval tasks." | Leaf `not_fixed_protocol(...)` (contrary of `c_bench`'s `protocol_fixed` leaf `pb2`); `undermine d_um a_bench.protocol_fixed.leaf`. |
| R2 | **rebut** | "A concurrent replication finds APT does **not** match the dense baseline on OpenLLM." | `null_benchmark` argument concluding `not_performs(...)` (declared contrary of `c_bench`'s conclusion), with its own `protocol_fixed` + `matched_environment` leaves; mutual `rebut` (attack completeness). |
| R3 | **undercut** | "Your low-memory number is a measurement artifact of gradient checkpointing enabled only for APT." | Leaf `measurement_artifact(...)` (declared exception); `undercut d_meas a_meas.rule`. |

The reviewers also note the ablation is single-run ("add error bars"). That is **not** a typed attack — it is the already-unmet mandatory `variance_reported` CQ that keeps `c_kurt` `gap`. The framework flagged it at submission; the reviewer merely agrees.

Grounded result: the undermine and the rebut each drive `a_bench` out; the undercut drives `a_meas` out. `c_bench` and `c_measure` become `defeated`; `c_kurt` stays `gap`.

### Round 2 — rebuttal (three standard author moves, one calculus each)

- **Discharge the gap** (`c_kurt` gap → justified): the author supplies 5-seed variance runs, so `variance_reported` now has a leaf. The previously undeclarable `component_ablation` argument becomes complete and, unattacked, is `in`. This is the headline `gap → justified` discharge.
- **Counter-attack to reinstate** (`c_bench` defeated → justified): the author defeats **both** reviewer attacks (E4-style reinstatement). Against R1's undermine, an author leaf concluding `protocol_confirmed` undermines the reviewer's `not_fixed_protocol` leaf (one-directional contrary → the defender is unattacked). Against R2's rebut, the author shows the cited replication ran on a mismatched eval harness, **undercutting** the reviewer's `null_benchmark` at its rule via `null_benchmark : environment_mismatch`. With both attackers out, `a_bench` is reinstated.
- **Concede** (`c_measure` defeated → defeated): the author accepts R3's point and adds **no** counter-argument. `a_meas` stays out, so `c_measure` stays `defeated`. Concession is the *absence* of a defense — no special construct.

The "at least one gap→justified discharge and at least one counter-attack on a reviewer leaf" requirement is met by the variance discharge (`c_kurt`) and the counter-undermine of the reviewer's leaf (`r_um`). "Some statuses recover, some don't" is met by `c_bench` (recovers) versus `c_measure` (does not).

## Per-claim status trajectory

| Claim | Round 0 (submission) | Round 1 (reviews) | Round 2 (rebuttal) |
| --- | --- | --- | --- |
| `c_bench` — APT competitive vs dense on OpenLLM | **justified** | **defeated** | **justified** |
| `c_kurt` — kurtosis salience term is critical | **gap** | **gap** | **justified** |
| `c_measure` — low training-memory footprint | **justified** | **defeated** | **defeated** |

`c_bench` is the non-monotonic reinstatement (justified → defeated → justified) across an undermine and a rebut; `c_kurt` is the gap discharge; `c_measure` is the conceded non-recovery. The reviewer's counter-claim `not_performs(...)` (supported by `d_rebut`) is present but not queried; it is `justified` in R1 and `defeated` in R2 once its argument is undercut.

## Verification

Every command was run from a clean tree on branch `demo/d1-rebuttal-replay`.

- `cabal build exe:lara` — OK.
- `cabal run exe:lara -- check examples/rebuttal-replay/round0/example.lara` (and `round1`, `round2`) — all exit 0; printed statuses match the trajectory table above.
- `cabal exec -- runghc scripts/gen-worked-examples.hs` — regenerates each round's `example.core.sexp` + `expected.json`; no churn in other examples.
- `cabal test` — PASS. `WorkedExamplesSpec` adds three explicit verdict assertions (`prop_D1Round0/1/2`) and covers all three rounds in the freshness, `expected.json`, and coverage-matrix properties.
- `cd lean && lake build` then `bash scripts/differential.sh` — both drivers agree byte-exactly on all three anchors: positive `pass=421 fail=0`, negative `pass=54 fail=0`, exit 0.

## Layout

```
examples/rebuttal-replay/
  round0/  example.lara  rebuttal-v1.policy.lara  example.core.sexp  expected.json
  round1/  example.lara  rebuttal-v1.policy.lara  example.core.sexp  expected.json
  round2/  example.lara  rebuttal-v1.policy.lara  example.core.sexp  expected.json
```

Each `example.lara` carries a bottom-of-file golden-oracle comment (the expected labels + statuses); the `.core.sexp` wire anchor and `expected.json` located-diagnostic golden are **derived** by `scripts/gen-worked-examples.hs` and freshness-pinned by `test/WorkedExamplesSpec.hs`.

## Scaled version (out of scope, post-PLDI)

LLM elaboration of real OpenReview threads at scale, and correlation studies of LARA verdicts vs. human reviewer complaints, are the ACL/EMNLP follow-up (tracker #61). Here the reviews are **hand-lowered** per the corpus-unit discipline, grounded in the gaps the C04 annotation already documents.
