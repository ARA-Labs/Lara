# ARA → LARA corpus map and M0 annotation guide

_The M0 kickoff artifact (`../plans/research-proposal.md` §7; `engineering-plan.md` §2). Fixes the
source corpus, the field-level lowering map from an ARA to a LARA program, and the annotation schema
for the semantic corpus study. Written 2026-07-21 after inspecting the two upstream repos._

## 1. Source repositories

| Repo | Role for LARA |
| --- | --- |
| [`ARA-Labs/Agent-Native-Research-Artifact`](https://github.com/ARA-Labs/Agent-Native-Research-Artifact) | The ARA **format definition + tooling**. Defines the four-layer anatomy; ships worked examples (`resnet-ara-example`, `the-ara-of-ara`); contains the **`rigor-reviewer` skill** — our named baseline. |
| [`AmberLJC/ara-paperbench`](https://github.com/AmberLJC/ara-paperbench) | The **corpus**. 32 ARAs, schema-uniform, each `artifacts/<benchmark>/<name>/`. This is the "30-paper corpus" the proposal reuses (`research-proposal.md:395`). |

**The task.** Each corpus artifact is converted into a LARA program: its claims become claim roots,
its experiments/evidence become leaves and inference-scheme instances, and its exploration trace becomes
the typed-attack (defeat) layer. M0 annotates what that conversion must produce *before* the calculus
freezes, so the frozen v0.1 constructs actually cover the corpus.

### The baseline, confirmed

`rigor-reviewer` (skill v3.0.0) scores six dimensions 1–5 — D1 Evidence Relevance, D2 Falsifiability
Quality, D3 Scope Calibration, D4 Argument Coherence, D5 Exploration Integrity, D6 Methodological
Rigor — and emits `level2_report.json` with an accept/reject recommendation. It "does NOT execute
code, fetch URLs, or consult external sources" and is explicitly "not a bug detector." That is the
holistic, unauditable judgment LARA improves on (`research-proposal.md:74`): a score that cannot
point to *which* premise is missing or *which* dead end kills a claim. It is a complementary
qualitative baseline, **not** a status-accuracy baseline (`research-proposal.md:382`).

## 2. Corpus inventory

32 artifacts, **231 claims total**, every artifact carrying `logic/claims.md`,
`logic/experiments.md`, and a `trace/` exploration tree. Comfortably covers M0's 50–100 target with a
large held-out reserve.

| Benchmark group | Artifacts | Claims | Notes |
| --- | --- | --- | --- |
| `paperbench` | 23 | 136 | published-paper ARAs (4–8 claims each); the primary M0 pool |
| `rebench` | 5 | 65 | reproduction artifacts, claim-dense (12–14 each) |
| `extra` | 3 | 20 | andes, expbench, venn |
| `speedrun` | 1 | 10 | nanogpt-speedrun |

`paperbench` `resnet-ara-example` (in the format repo, not paperbench) is the reference worked example
for the map below; its `trace/exploration_tree.yaml` is the only YAML trace read in full so far
(paperbench traces ship as `.html` + `.yaml`).

## 3. The field-level lowering map

Every ARA field maps onto a LARA construct. This is the spine of both M0 annotation and the eventual
untrusted elaborator (spec §11).

| ARA source (file → field) | LARA construct | Spec | Trust |
| --- | --- | --- | --- |
| `logic/claims.md` → `## C0x` **Statement** | `claim c.nl` | §3.1 | verbatim copy |
| formal content of the Statement | `claim c.formal` (atom) | §3.1 | **untrusted** (LLM), audited on faithfulness axis |
| NL↔formal correspondence | `claim c.binding` | §3.1 | **untrusted**, human-signed, never checked |
| **Proof**: `[E01, E02]` | which support terms (`arg`) support the claim | §4.4 | structural |
| **Dependencies**: `C01` | inter-claim edge → a premise support term of the supporting scheme | §6 | structural |
| **Evidence basis**: Table 2, Fig. 4 | `leaf` declarations; `refs` → `evidence/` paths | §3 | leaf admission §4.3 |
| `logic/experiments.md` → Setup / Procedure / Baselines | **inference-scheme** instance (e.g. `controlled_experiment`) + its critical questions (randomization, adequate power, baseline presence) | §4 | policy-relative |
| **Falsification criteria** | the `contrary` proposition / candidate rebut target | §4, §7 | policy `contrary` |
| `trace/…` node `type: dead_end` + `why_failed` | **typed-attack candidate** (undercut / rebut / undermine) — or **no edge** | §7 | typed constructor required |
| node `support_level: explicit` vs `inferred` | leaf provenance: `observed`/`attested` vs `assumed` | §3, §4.3 | provenance ≠ attack |
| node `also_depends_on: [...]` | cross-branch premise dependency | §6 | structural |

### The dead-end discrimination (the differentiator)

Not every dead end is an attack. Resnet node **N04 "Vanishing-gradient hypothesis"** is a
`dead_end` whose `why_failed` rules out an *alternative explanation* of the degradation result — it
does **not** rebut, undercut, or undermine C01/C02, so it compiles to **no edge**. Contrast a dead
end that reports a *conflicting measurement* on the same claim, which would be a typed `rebut`.
Making this call per dead-end node is the core M0 judgment and the exact capability
`research-proposal.md:400` says a holistic reviewer cannot produce. **Expect most dead ends to be
non-attacks** (rejected alternatives); that ratio is itself a reportable M0 finding justifying typed
edges over "dead end = defeater."

## 4. M0 annotation schema

Per sampled claim, annotate:

1. **Claim type** — descriptive | comparative | causal | generalization | negative-result |
   implementation/behavioral (feeds open question §8 #2: which rule schemes).
2. **Proposition shape** — the `formal` atom's predicate/arity as it would appear in `Sigma`
   (feeds `Lara.Prop` and whether the Phase-0 opaque-identifier nullary case suffices).
3. **Inference scheme + premises** — which scheme the experiment instantiates; strict vs defeasible
   (feeds §8 #2 strict/defeasible split).
4. **Strict certifier/theory** — for each proposed strict step, record the smallest plausible
   certifier: reference natural deduction, a named domain checker, optional LP, or none
   (`trusted-policy`); identify any required background theory.
5. **Critical questions** — from Setup/Procedure/Baselines: randomization, power, baselines,
   external validity, etc. Mark each mandatory vs optional, and whether an unmet one is a *gap*
   (question) or a *defeater* (exception) — spec §4.2.
6. **Leaf granularity** — one atom per (experiment, claim), or per result-cell? (feeds §8 #5).
7. **Attack candidates** — walk the exploration tree; for each `dead_end`, decide rebut / undercut /
   undermine / **none**, with the target position and the `contrary` pair it needs.
8. **Holes** — required premises or critical questions the artifact leaves open.

### Process (from `popl-research-review.md` §5 Phase A)

- Sample 50–100 claims stratified by the six claim types above, drawing first from `paperbench`.
- Double-annotate ≥20–30%; adjudicate and record disagreements.
- **Exit gate:** a finite construct set covers ≥80% of sampled argument shapes without encoding whole
  reasoning steps as opaque leaves. Failing the gate means the calculus (not the annotation) needs
  more constructs — that feedback is the point of doing M0 before freeze.

### What M0 unblocks

The annotation directly answers the corpus-gated decision gates in `engineering-plan.md` §6:
§8 #1 (optional adapter portfolio), §8 #2 (rule schemes → `Lara.Policy`), §8 #3 (defeat typing →
`Lara.Attack`), §8 #5 (leaf granularity → `Lara.SupportTerm`), and §8 #7
(behavioral-vs-empirical routing → optional TL-1).

## 5. Local inspection

Both repos were cloned to `/tmp/ara-inspect/` for this analysis (not committed). Re-clone with:

```
git clone --depth 1 https://github.com/AmberLJC/ara-paperbench
git clone --depth 1 https://github.com/ARA-Labs/Agent-Native-Research-Artifact
```
