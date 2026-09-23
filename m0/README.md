# M0 — semantic corpus study workspace

Working directory for the M0 annotation task (`docs/engineering-plan.md` §2,
`docs/corpus-map.md` §4). Source corpus: the `corpus/ara-paperbench` submodule,
pinned at `62e9b54` — all row references below are valid only at that pin.

## Sampling frame

`extract_claims.py` (stdlib-only) parses the corpus into two TSV indices:

| File | Rows | One row per |
| --- | --- | --- |
| `claims-index.tsv` | 231 | `## Cxx` entry in every `logic/claims.md` |
| `deadends-index.tsv` | 279 | `type: dead_end` node in every `trace/exploration_tree.yaml` |

Regenerate (idempotent, overwrites in place):

```
python3 m0/extract_claims.py
```

The claims index is the M0 **sampling frame**: 136 paperbench / 65 rebench /
20 extra / 10 speedrun claims, with statement, normalized status
(213 supported, 1 partially_supported, 2 untested, 1 hypothesis, 14 blank —
`rebench-restricted_mlm` carries no Status field), falsification criteria,
proof/evidence refs, dependencies, and tags. The dead-end index is the
attack-candidate pool for annotation field 7 (rebut / undercut / undermine /
**none** per dead end).

Parser notes (why not plain YAML/markdown tooling):

- `rebench-restricted_mlm/logic/claims.md` uses `Evidence` for `Proof` and
  omits `Status`/`Falsification criteria`; both falsification spellings occur
  corpus-wide. The extractor maps all variants onto one column set.
- Trace YAMLs are hand-written with two key orders (`id`-first vs
  alphabetized, where `id` is mid-item) and one malformed line
  (`rebench-triton_cumsum`); nodes are therefore delimited on list-item
  boundaries, and only keys from the observed vocabulary are treated as keys.

## Claim typing (`claim-types.tsv`)

Every claim in the frame carries one of the six types from
`docs/corpus-map.md` §4 field 1. Provenance: single-annotator AI pass
(2026-07-21, ai-executed); the double-annotation subset below is the
adjudication check on it. Rubric applied:

- **Precedence** when several readings fit: negative-result > causal >
  generalization > comparative > implementation-behavioral > descriptive.
  Type the *headline assertion*, not the evidence.
- **negative-result**: absence of effect/capability, failure, equivalence
  ("does not hurt"), or contradiction of a documented claim.
- **causal**: effect attributed to a component or intervention — ablations,
  single-component swaps within one system, dose-response (hyperparameter →
  outcome), mechanistic "X arises from Y".
- **generalization**: only when breadth itself is the claimed content
  (a law across model families, transfer without retraining, scenario
  robustness). Routine multi-benchmark evaluation does *not* qualify.
- **comparative**: relation between distinct named systems/methods on a
  metric ("A outperforms B"). Design-variant *rankings* are comparative;
  single-component ablations are causal.
- **implementation-behavioral**: behavior of concrete code/infrastructure
  (scorer mechanics, dtype promotion, rate limits, shipped-config facts).
- **descriptive**: measured property under one condition; purely analytic
  results (theorems, bounds) are descriptive/comparative per content with an
  `analytic` note — the note marks strict-certifier candidates (§4 field 4).

Distribution: comparative 72, causal 54, descriptive 36,
implementation-behavioral 31, negative-result 26, generalization 12.
**Finding:** implementation-behavioral claims occur *only* in
rebench/speedrun (31/31); paperbench+extra papers are comparative/causal
heavy. The claim-type mix is benchmark-group-dependent, so the frozen
construct set must be validated against both populations.

## The sample (`sample.tsv`)

`draw_sample.py` (seed 42, rerun-identical) draws **60 claims**: quotas by
largest-remainder proportional allocation with a floor of 5 per type
(comparative 17, causal 14, descriptive 9, implementation-behavioral 8,
negative-result 7, generalization 5), groups exhausted paperbench > extra >
rebench > speedrun within each stratum, round-robin across artifacts so no
artifact dominates. Result: 52 paperbench + 8 rebench (the
implementation-behavioral stratum has no paperbench members), 18 claims
(30%) flagged `double_annotate=yes`.

## Annotation pass (done 2026-07-22) and results

- `annotations/SCHEMA.md` — the 8-field per-claim schema and judgment rules.
- `annotations/<artifact>.yaml` — 27 files, all 60 sampled claims annotated
  (one independent AI annotator per artifact, shared codebook).
- `double-annotation.tsv` — blind second typing pass (different model) on the
  18-claim subset: 14/18 agreement, κ = 0.73; 4 adjudications propagated into
  `claim-types.tsv`, `sample.tsv`, and the affected annotation files.
- `annotation-summary.md` — aggregates, answers to open questions §8 #1/#2/#3/#5,
  and the preliminary construct-coverage verdict (**PASS, ~90%**, with a 6-item
  construct wishlist and evidence-model conditions).

## Next steps

1. Spot checks of attack decisions; full-schema double annotation on a subset.
   (Summary affirmed by the researcher 2026-07-22; findings crystallized as
   ara claims C13–C17.)
2. Author adversarial attack reports (rebut/undermine test cases) against corpus
   claims when testing the language — the corpus itself, being polished top-venue
   work, cannot supply them (decision N29).
3. Feed §8 #1/#2/#3/#5 answers (C13–C16) into the v0.1 calculus freeze
   (spec §4, §7, §8).
