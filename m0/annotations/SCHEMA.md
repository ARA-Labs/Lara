# M0 annotation schema (per sampled claim)

Implements the 8-field schema of `docs/corpus-map.md` §4 against the corpus pinned at
`62e9b54`. One YAML file per artifact: `m0/annotations/<artifact>.yaml`. Field 1
(claim type) is fixed upstream in `m0/sample.tsv` — copy it, do not re-type.

## File format

```yaml
artifact: <name>
group: paperbench | rebench | extra | speedrun
annotator: "ai-executed (claude, 2026-07-21)"
deadend_cap: null            # or "capped at N of M — selection rule stated below"
claims:
  - claim_id: C0x
    claim_type: <from sample.tsv>
    # 2. proposition shape — how the claim's formal atom would look in Sigma
    proposition_shape:
      sketch: "pred(arg1, ..., argN)"   # predicate + arguments, named meaningfully
      arity: <N>
      phase0_nullary_sufficient: true|false   # would an opaque nullary atom lose checkable structure?
      note: ""
    # 3. inference scheme instantiated by the supporting experiment(s)
    inference_scheme:
      scheme: <snake_case name, e.g. controlled_comparison, component_ablation,
               dose_response, statistical_correlation, analytic_proof, code_inspection,
               cross_run_observation, benchmark_evaluation — coin a new name if none fits>
      strict_or_defeasible: strict | defeasible
      premises: ["<premise 1>", "..."]   # what must hold for the scheme to yield the claim
      supporting_experiments: [E0x, ...]
    # 4. smallest plausible strict certifier for any strict step (else none)
    strict_certifier: none | reference-nd | domain-checker(<name it>) | lp | trusted-policy
    certifier_note: ""       # required if not "none": what exactly would be certified
    # 5. critical questions from Setup/Procedure/Baselines
    critical_questions:
      - cq: "<question>"
        mandatory: true|false
        status: met | unmet-gap | unmet-defeater   # unmet: is it a question (gap) or an exception (defeater)?
        basis: "<where in experiments.md this comes from>"
    # 6. leaf granularity that the evidence actually requires
    leaf_granularity: per-experiment-claim | per-result-cell | per-run | mixed
    leaves:
      - atom: "<what one leaf asserts>"
        provenance: observed | attested | assumed   # explicit trace/evidence -> observed/attested; inferred -> assumed
        refs: ["<evidence path / table / trace node>"]
    # 7. typed-attack candidates: walk the artifact's dead_end nodes
    attack_candidates:
      - node: N0x
        decision: rebut | undercut | undermine | none
        target: "<claim id or 'support of C0x' or n/a>"
        rationale: "<one sentence>"
    # 8. holes — required premises or CQs the artifact leaves open
    holes: ["<hole 1>", "..."]
    coverage_flags: []       # anything the LARA construct vocabulary above could NOT express — be honest, this feeds the 80% exit gate
    uncertain: false         # true + note if any judgment is a coin-flip
    note: ""
```

## Judgment guidance (from docs/corpus-map.md §3–4)

- **Dead-end discrimination is the core judgment.** A dead end that rules out an
  *alternative explanation* or a *rejected design/approach* is **none** (no edge) — expect
  most dead ends to be non-attacks. `rebut` = conflicting result on the claim's conclusion;
  `undercut` = attacks the inference/scheme link (e.g. confound, invalid setup);
  `undermine` = attacks a premise/leaf (e.g. the measurement itself is wrong).
- **Provenance is not attack**: `support_level: explicit` vs `inferred` maps to leaf
  provenance (observed/attested vs assumed), never to an edge.
- **Critical questions**: mandatory = the scheme is not policy-complete without it
  (e.g. baseline presence for a comparison); optional = strengthens. Unmet mandatory CQ
  whose absence merely leaves the claim unestablished = `unmet-gap`; unmet CQ that,
  given what the artifact shows, actively defeats the inference = `unmet-defeater`.
- **Strict certifier**: only for steps that are genuinely deductive/algorithmic
  (arithmetic re-checks, complexity claims, type-checkable derivations, code-inspection
  facts). Empirical inference is never strict. `trusted-policy` = strict-by-fiat, flag it.
- **Dead-end cap**: artifacts with >15 dead ends: classify every dead end that names or
  clearly bears on a sampled claim, plus enough others to reach 15; record the cap and
  selection rule in `deadend_cap`. Never cap silently.
