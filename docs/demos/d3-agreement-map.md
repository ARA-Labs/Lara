# D3 — cross-paper agreement map (issue #64)

Draftable into #60 (M7 paper package), sections T1/T3. The checked artifact is
`examples/agreement-map/` (`example.lara`, `agreement-v1.policy.lara`, derived
`example.core.sexp` + `expected.json`); its verdict is pinned by
`test/WorkedExamplesSpec.hs` (`prop_agreementMap`, plus freshness, expected-json,
coverage, and the byte-differential through both drivers).

## What this demo shows

When several same-topic papers appear to disagree, LARA distinguishes two
outcomes by **atom identity** (spec §3.2), not by prose:

1. **Genuine disagreement** — two conclusions land on the *same* atoms and are a
   declared `contrary` pair, so each rebuts the other: a 2-cycle grounded
   semantics labels `undec`, and both claims are `contested` (not "both
   justified"). This is example `B`'s shape at the pruning cluster's real grain.
2. **Setting-mismatch non-attack** — two conclusions that read as a flat
   contradiction in prose but differ in their *setting index*, so they are not a
   `contrary` instance and **no attack forms**. Both claims stand `justified`.
   v0.1 deliberately has no cross-setting contrary, so LARA refuses to
   manufacture the disagreement; the open comparability critical question
   (below) names exactly what evidence would connect them.

The two pairs have **identical prose-level disagreement structure**. Only the
setting index differs, and that single difference flips the verdict from
`contested ×2` to `justified ×2`. That is the point: the calculus recognizes a
disagreement only when the formalized atoms license it.

## The cluster and the propositions

Cluster: structured/unstructured pruning of transformer LMs — the pruning family
the corpus already annotates (`corpus-units/adaptive-pruning/`, whose C03 claim
is `better(apt, prune_distill_cofi, ...)`). The policy `agreement-v1` is the
comparison family of `corpus-units/corpus-v1.policy.lara` (`controlled_comparison`
+ its `null_comparison` dual, concluding `better` / `not_better`), modeled on
`examples/A/empirical-v1.policy.lara`.

Two propositions are hand-aligned across four "papers":

**P1 — genuine disagreement (same atoms).**

| Paper | Claim | `formal` | Scheme |
| --- | --- | --- | --- |
| A | APT beats CoFi | `better(apt, cofi, accuracy, roberta_mnli_s60)` | `controlled_comparison` |
| B | replication finds no advantage | `not_better(apt, cofi, accuracy, roberta_mnli_s60)` | `null_comparison` |

Same `(apt, cofi, accuracy, roberta_mnli_s60)` on both sides → a `contrary`
instance → mutual `rebut` → both `contested`.

**P2 — setting mismatch (same S/B/Q, different D).**

| Paper | Claim | `formal` | Scheme |
| --- | --- | --- | --- |
| C | pruning near-lossless | `better(magnitude_pruning, dense_baseline, accuracy, bert_glue_s50)` | `controlled_comparison` |
| D | pruning destructive | `not_better(magnitude_pruning, dense_baseline, accuracy, llama_openllm_s90)` | `null_comparison` |

Same system, baseline, and metric; the **only** non-matching atom is the setting
index `D` (`bert_glue_s50` vs `llama_openllm_s90`). The `contrary` pattern
`better(S,B,Q,D)` / `not_better(S,B,Q,D)` requires the *same* `D` on both sides,
so the two conclusions never unify to one contrary instance → **no attack** →
both `justified`.

## Per-proposition A3 (atom-matching) alignment rationale

Assumption A3 (README.md design constraint #1) makes atom identity load-bearing:
the `binding` rationale asserts the alignment decision per proposition, so the
attack / non-attack is an audited decision, not an accident of spelling.

- **P1, both sides (asserting identity):** the replication (B) targets the
  identical `(system, baseline, metric, setting)` as the original (A) — same
  method `apt`, same baseline `cofi`, same `accuracy` metric, same RoBERTa/MNLI
  at 60% sparsity. Verified identical under normalization. This is what makes the
  pair a *real* contrary instance and the rebut edges genuine. (If B's claim had
  formalized to a different accuracy atom or a different `D`, the pair would not
  match and no attack would form — the silent false-independence A3 exists to
  catch.)
- **P2, both sides (asserting deliberate non-identity):** the setting index is
  *deliberately* distinct (`bert_glue_s50` for C, `llama_openllm_s90` for D)
  while system/baseline/metric are held identical. The prose disagreement is
  real to a human reader, but it is **not** an atom-level conflict: the papers
  never measured the same setting. Recording this on the `binding` is the honest
  alternative to silently letting the two claims coexist as if independent.

## The agreement map

Compiled argumentation framework (args in declaration order pa=0, pb=1, pc=2,
pd=3; all complete):

```
   pa  ⇄  pb        pc          pd
 (undec) (undec)   (in)        (in)
   P1: rebut 2-cycle   P2: no edge (settings differ)
```

| Claim | Support label | Status | Why |
| --- | --- | --- | --- |
| `better(apt, cofi, accuracy, roberta_mnli_s60)` | pa `undec` | **contested** | 2-cycle with pb; same atoms → contrary |
| `not_better(apt, cofi, accuracy, roberta_mnli_s60)` | pb `undec` | **contested** | 2-cycle with pa |
| `better(magnitude_pruning, dense_baseline, accuracy, bert_glue_s50)` | pc `in` | **justified** | unattacked; setting differs from D |
| `not_better(magnitude_pruning, dense_baseline, accuracy, llama_openllm_s90)` | pd `in` | **justified** | unattacked; setting differs from C |

- **Which claims attack:** P1's A and B, and *only* through the same
  `better`/`not_better` contrary instance on identical atoms. Attack completeness
  (spec §8) then forces *both* edges of the 2-cycle.
- **Which claims do not, and why:** P2's C and D do not attack. Their conclusions
  differ in the setting index `D`, so neither orientation of the `contrary`
  pattern unifies them; attack completeness forces no edge because there is no
  contrary instance to complete. No preference, no partial match, no silent link
  — zero attacks.

## The comparability critical question — "what would resolve the literature"

The setting-mismatch non-attack is a *feature*: LARA declines to fabricate a
disagreement the atoms do not license. But declining is not the same as claiming
the two papers agree — it makes the gap **explicit** and names what would close
it. The open comparability CQ for P2:

> *C and D become comparable only if a bridging experiment reports
> `compares(magnitude_pruning, dense_baseline, accuracy, D, ·)` at a **shared**
> setting `D` — e.g. both at `bert_glue_s50`, or both at `llama_openllm_s90`, or
> a common intermediate `(model, dataset, sparsity)`. Absent such a shared-setting
> measurement, the prose contradiction is a claim about two different worlds, and
> the corpus records no conflict.*

This is the artifact the map contributes to a literature review: not a verdict of
agreement or disagreement, but a precise statement of the missing measurement.
v0.1 has no vocabulary to encode a cross-setting contrary (that would be
eval-settings-as-worlds, the possible-worlds follow-up — out of scope per #64),
so the comparability CQ lives here in the write-up and in the artifact's
golden-oracle comment, not as a checker edge. That boundary is deliberate: adding
a cross-setting contrary would be exactly the kind of manufactured disagreement
the demo argues against.

## §8.1 Path A/B note (recorded, not routed around)

README.md flags a specific pressure point: *"the strict well-formedness
restriction (spec §8.1, Path B) bites harder across a contested field ... whose
headline claims are themselves the contested ones."* This demo sits exactly in
that condition — P1's contested propositions (`better` / `not_better` on
`roberta_mnli_s60`) are the **headline claims**.

**No collision occurs.** Both are conclusions of *defeasible* schemes only
(`controlled_comparison`, `null_comparison`); no strict rule and no strict chain
in `agreement-v1` touches them. The §8.1 Path B check (spec §8.1: no
strict-reachable pattern may overlap either side of a `contrary` declaration;
violation = rejection class R12) is therefore satisfied, and the policy is
accepted. Had either headline been the consequent of a strict rule — or reachable
on a strict chain — the policy would be **rejected at compile time (R12)**, and
resolving it would require the §8.1 **flip to Path A** (an involutive
contradictory map with transposition-closed strict rules). This demo does not
force that flip; it stays on Path B by keeping every contested proposition on a
defeasible step, which is the discipline §8.1 requires and the reason the flip
criterion is not triggered here. Recorded as a decision, per the load-bearing
constraint.

## Validation

All commands run from a clean tree in the worktree.

| Command | Result |
| --- | --- |
| `cabal build exe:lara` | success |
| `cabal run exe:lara -- check examples/agreement-map/example.lara` | accept, exit 0; labels `pa/pb undec, pc/pd in`; statuses `contested, contested, justified, justified` |
| `cabal exec -- runghc scripts/gen-worked-examples.hs` | regenerated all anchors; only `examples/agreement-map/` new, no drift elsewhere |
| `cabal test` | PASS (adds `prop_agreementMap`; freshness, expected-json, coverage, DifferentialSpec all green) |
| `cd lean && lake build` | success (52 jobs) |
| `bash scripts/differential.sh` | `pass=419 fail=0`, `negative pass=54 fail=0` — Haskell and Lean drivers agree byte-exactly on the agreement-map verdict |
