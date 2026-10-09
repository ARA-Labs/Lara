# ARA → Lara corpus map

An ARA (Agent-Native Research Artifact) is a structured research artifact
carrying claims, experiments, evidence and an exploration trace. A Lara program
is the checkable claim-support form this map lowers one into. This document
fixes the source corpus and the field-level lowering map from an ARA to a Lara
program.

## 1. Source repositories

| Repo | Role for Lara |
| --- | --- |
| [`ARA-Labs/Agent-Native-Research-Artifact`](https://github.com/ARA-Labs/Agent-Native-Research-Artifact) | The ARA **format definition + tooling**. Defines the four-layer anatomy; ships worked examples (`resnet-ara-example`, `the-ara-of-ara`); contains the `rigor-reviewer` skill. |
| [`AmberLJC/ara-paperbench`](https://github.com/AmberLJC/ara-paperbench) | The **corpus**. 32 ARAs, schema-uniform, each `artifacts/<benchmark>/<name>/`. |

Each corpus artifact lowers to a Lara program: its claims become claim roots,
its experiments and evidence become leaves and inference-scheme instances, and
its exploration-trace dead ends become typed attacks or no edge.

`rigor-reviewer` (skill v3.0.0) scores an artifact on six dimensions from 1 to
5 (evidence relevance, falsifiability, scope calibration, argument coherence,
exploration integrity, methodological rigor) and emits an accept/reject
recommendation without executing code or consulting external sources. Its
score does not locate which premise is missing or which dead end defeats a
claim, so it is a complementary qualitative reference, not a status-accuracy
baseline.

## 2. Corpus inventory

32 artifacts, **231 claims total**, every artifact carrying `logic/claims.md`,
`logic/experiments.md`, and a `trace/` exploration tree.

| Benchmark group | Artifacts | Claims | Notes |
| --- | --- | --- | --- |
| `paperbench` | 23 | 136 | published-paper ARAs (4–8 claims each) |
| `rebench` | 5 | 65 | reproduction artifacts, claim-dense (12–14 each) |
| `extra` | 3 | 20 | andes, expbench, venn |
| `speedrun` | 1 | 10 | nanogpt-speedrun |

`resnet-ara-example` (in the format repo, not paperbench) is the reference
worked example for the map below; its trace is `trace/exploration_tree.yaml`
(paperbench traces ship as `.html` + `.yaml`).

## 3. The field-level lowering map

Every ARA field maps onto a Lara construct. The same map is the specification
for the untrusted elaborator (spec §11).

| ARA source (file → field) | Lara construct | Spec | Trust |
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

### The dead-end discrimination

Not every dead end is an attack. Resnet node **N04 "Vanishing-gradient hypothesis"** is a
`dead_end` whose `why_failed` rules out an *alternative explanation* of the degradation result — it
does **not** rebut, undercut, or undermine C01/C02, so it compiles to **no edge**. Contrast a dead
end that reports a *conflicting measurement* on the same claim, which would be a typed `rebut`.
The lowering makes this call per dead-end node, which a holistic score cannot
express. Most dead ends are rejected alternatives and lower to no edge, which is
why defeat edges are typed rather than read as "dead end = defeater."

## 4. Annotation schema

The semantic corpus study annotated each claim of a 60-claim stratified sample
with eight fields: claim type (descriptive, comparative, causal, generalization,
negative-result, implementation/behavioral); proposition shape (the `formal`
atom's predicate and arity in `Sigma`); inference scheme and premises, strict
or defeasible; the smallest plausible strict certifier (reference natural
deduction, a named domain checker, optional LP, or none) and any background
theory; critical questions, each marked mandatory or optional and as a gap
(question) or defeater (exception) per spec §4.2; leaf granularity; attack
candidates (rebut, undercut, undermine or none for each `dead_end`, with target
position and `contrary` pair); and holes the artifact leaves open. The
sampled claims are listed in `corpus-units/MANIFEST.tsv`, and each unit's
header comment records the annotation it was lowered from.

## 5. Local corpus checkout

The corpus is vendored as a git submodule at `corpus/ara-paperbench`, pinned to commit
`62e9b54b2d4efe45b97f25676a16784530dd552a` (upstream `main`). The
`corpus-units/` lowerings reference artifacts at this pin,
so changing the pin requires re-checking them. Fetch it with:

```
git submodule update --init --depth 1 corpus/ara-paperbench
```

The format repo (`ARA-Labs/Agent-Native-Research-Artifact`, home of `resnet-ara-example` and the
`rigor-reviewer` skill) is not vendored; it is tooling and reference, not corpus
input. Clone it when needed:

```
git clone --depth 1 https://github.com/ARA-Labs/Agent-Native-Research-Artifact
```
