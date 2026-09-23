# D3 — cross-paper agreement map

Draftable into the M7 paper package, sections T1/T3. The demo ships **twice**,
and the pair is the point of the second half of this write-up:

| Artifact | What it is |
| --- | --- |
| `examples/agreement-map/` | The original: all four papers in **one** `.lara` file, which therefore declares its own cross-paper attacks. Kept byte-unchanged as the oracle. |
| `examples/agreement-map-multi/` | The same demonstration as **four independently authored, independently checkable artifacts** under one `map.laramap`. No member declares a cross-paper attack; the map generates them. |

The single-file artifact (`example.lara`, `agreement-v1.policy.lara`, derived
`example.core.sexp` + `expected.json`) has its verdict pinned by
`test/WorkedExamplesSpec.hs` (`prop_agreementMap`, plus freshness, expected-json,
coverage, and the byte-differential through both drivers). The four-member map is
covered by `test/MapExampleSpec.hs` and by `scripts/check-map-conformance.sh`;
[§ The same map as four artifacts](#the-same-map-as-four-artifacts) below is its
section.

_A demo write-up (2026-08-02). The question it answers: when several papers
on one topic appear to disagree, which disagreements are real? The paragraph
above locates the checked artifact and its pinned tests; the demo itself
starts below._

## What this demo shows

When several same-topic papers appear to disagree, Lara distinguishes two
outcomes by **atom identity** (spec §3.2), not by prose:

1. **Genuine disagreement** — two conclusions land on the *same* atoms and are a
   declared `contrary` pair, so each rebuts the other: a 2-cycle grounded
   semantics labels `undec`, and both claims are `contested` (not "both
   justified"). This is example `B`'s shape at the pruning cluster's real grain.
2. **Setting-mismatch non-attack** — two conclusions that read as a flat
   contradiction in prose but differ in their *setting index*, so they are not a
   `contrary` instance and **no attack forms**. Both claims stand `justified`.
   v0.1 deliberately has no cross-setting contrary, so Lara refuses to
   manufacture the disagreement; the open comparability critical question
   (below) names exactly what evidence would connect them.

Once their setting qualifiers are elided, the two pairs have the same
positive-versus-negative comparison rhetoric. At full claim granularity, the
setting index differs only in the second pair, and that difference flips the
verdict from `contested ×2` to `justified ×2`. That is the point: the calculus
recognizes a disagreement only when the formalized atoms license it.

## Read it first as four paper abstracts

The following miniature abstracts are **illustrative reconstructions**, not
quotations from published papers. They are the natural-language counterparts of
the four checked arguments in `examples/agreement-map/example.lara`.

### Pair 1 — a genuine same-setting disagreement

> **Paper A — “Adaptive Pruning at High Sparsity.”** We compare APT with CoFi on
> RoBERTa-base at 60% sparsity using MNLI accuracy. Across matched runs, APT
> achieves higher accuracy than CoFi. We conclude that APT outperforms CoFi in
> this setting.

> **Paper B — “Re-evaluating Adaptive Pruning.”** We replicate the APT–CoFi
> comparison on RoBERTa-base, MNLI, and 60% sparsity. Under the same evaluation
> protocol, we find no accuracy advantage for APT. We conclude that APT does not
> outperform CoFi in this setting.

A literature review may reasonably say that these papers disagree. Lara reaches
the same result because every comparison coordinate matches: system, baseline,
metric, and setting. Their conclusions instantiate a declared contrary pair,
so the two arguments rebut one another and both claims become `contested`.

### Pair 2 — similar prose about different experimental worlds

> **Paper C — “Magnitude Pruning Improves BERT at Moderate Sparsity.”** On BERT
> evaluated across GLUE at 50% sparsity, magnitude pruning achieves higher
> accuracy than the dense baseline. We conclude that it performs better in this
> setting.

> **Paper D — “No Accuracy Benefit from Magnitude Pruning at Extreme
> Sparsity.”** On LLaMA2-7B evaluated with OpenLLM at 90% sparsity, magnitude
> pruning does not achieve higher accuracy than the dense model. We conclude
> that it is not better in this setting.

At the slogan level—“pruning is better” versus “pruning is not better”—these
papers sound contradictory. Their experiments do not, however, answer the same
proposition. Model family, benchmark, and sparsity are bundled into different
setting atoms (`bert_glue_s50` and `llama_openllm_s90`). Lara therefore creates
no rebuttal edge and leaves both claims `justified`. This does **not** mean the
papers agree; it means that a cross-setting conclusion would require an
additional bridging experiment or a policy that explicitly licenses such
generalization.

| What a literature reviewer asks | Pair 1 | Pair 2 |
| --- | --- | --- |
| Are the systems and baselines aligned? | yes | yes at the coarse method level |
| Are metric and experimental setting aligned? | yes: RoBERTa/MNLI, 60% sparsity | no: BERT/GLUE at 50% vs LLaMA/OpenLLM at 90% |
| Do the conclusions instantiate one contrary pair? | yes | no |
| Lara result | mutual rebuttal; both `contested` | no attack; both `justified` |
| What evidence would move the map? | evidence that defeats or privileges one same-setting result | a shared-setting bridging comparison |

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
| C | magnitude pruning has higher accuracy than the dense baseline | `better(magnitude_pruning, dense_baseline, accuracy, bert_glue_s50)` | `controlled_comparison` |
| D | magnitude pruning does not have higher accuracy than the dense baseline | `not_better(magnitude_pruning, dense_baseline, accuracy, llama_openllm_s90)` | `null_comparison` |

Same system, baseline, and metric; the **only** non-matching atom is the setting
index `D` (`bert_glue_s50` vs `llama_openllm_s90`). The `contrary` pattern
`better(S,B,Q,D)` / `not_better(S,B,Q,D)` requires the *same* `D` on both sides,
so the two conclusions never unify to one contrary instance → **no attack** →
both `justified`.

## Per-proposition A3 (atom-matching) alignment rationale

Assumption A3 (README.md design constraint #1) makes atom identity load-bearing:
the alignment decision is asserted per proposition, so the attack / non-attack is
an audited decision, not an accident of spelling. In the single-file artifact
that assertion lives in each claim's `binding` rationale, which is what the two
bullets below quote. In the four-artifact map it splits — a paper's rationale
about its *own* atoms stays on its `binding`, and the cross-paper half moves to
the manifest, which is the only place that can name both sides at once; see
[§ What the map owns and what a member owns](#what-the-map-owns-and-what-a-member-owns).

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

The setting-mismatch non-attack is a *feature*: Lara declines to fabricate a
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
eval-settings-as-worlds, the possible-worlds follow-up — out of scope for this demo),
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

## The same map as four artifacts

Everything above is written against the single-file artifact, where the four
papers share one file and each can name the others' arguments. That is a fair
teaching artifact and a dishonest picture of a literature: papers are not
co-authored into one document, and the file's two `rebut` lines are exactly the
edges no real reviewer would be in a position to write.

`examples/agreement-map-multi/` removes that liberty. Its layout:

```text
examples/agreement-map-multi/
  map.laramap                     the manifest: four members, four alignments, one question
  agreement-v1.policy.lara        the shared contract every member is compared against
  paper-a/  example.lara + agreement-v1.policy.lara + example.core.sexp + expected.json
  paper-b/  …
  paper-c/  …
  paper-d/  …
  map.core.sexp                   the map-check-input@1 parity envelope (derived)
  map.verdict.sexp                the map-verdict@1 composite verdict (derived, golden)
```

Each `paper-*/` directory is an ordinary paper artifact with its own declared
`artifact` identity, and each is a registered worked example — so each is checked
alone, on every CI run, through both drivers. **Alone, each one accepts and its
single claim is `justified`**: no member declares an attack, because a member
cannot name another artifact's argument.

Run either form:

```sh
cabal run exe:lara -- check examples/agreement-map/example.lara       # one file
cabal run exe:lara -- check examples/agreement-map-multi/map.laramap  # four artifacts
make map-check                                                       # same, via Make
make map-check OUT=/tmp/map.verdict.sexp                             # …to a file
```

### What the map owns and what a member owns

The split is the interesting part, and it is forced rather than stylistic.

| | Single file | Four artifacts |
| --- | --- | --- |
| Paper's claim, leaves, argument, authorship | in the file | in the member, unchanged |
| A3 rationale about **this paper's own** atom choice | `binding` rationale | `binding` rationale, in the member |
| A3 rationale about **two papers' atoms matching** | `binding` rationale | the manifest's `alignments` |
| The two rebut edges | declared by hand (`rebut pb pa`, `rebut pa pb`) | **generated** by cross-member saturation |
| The comparability CQ for pair 2 | a comment | the manifest's `questions` (`q_comparability`) |

A cross-paper alignment assertion names *both* sides, so it cannot live in either
member: paper A cannot audit the identity of paper B's atoms without containing
paper B. Moving it to the manifest is what makes the map's A3 discipline
expressible at all once the papers are genuinely separate. The manifest states
each alignment's author, audit status and rationale, and the checker **verifies
the asserted `same`/`different` actually holds** of the normalized propositions
or of the selected argument coordinate — it does not verify the prose, and it
records the audit status rather than treating it as evidence of review. An
alignment neither creates nor suppresses an attack; it documents and validates
the atom choices that decide one.

### The composite verdict

```text
(nodes  (node paper_a pa 0) (node paper_b pb 1) (node paper_c pc 2) (node paper_d pd 3))
(labels (0 undec) (1 undec) (2 in) (3 in))
(edges  (0 1) (1 0))
(statuses paper_a c_pos contested,  paper_b c_neg contested,
          paper_c c_low justified,  paper_d c_high justified)
```

Identical labels, edges and statuses to the single-file oracle under the node
correspondence `pa=0, pb=1, pc=2, pd=3` — asserted by
`test/MapExampleSpec.hs`'s `prop_compositeMatchesLegacyOracle`, which reads the
legacy artifact's own verdict rather than a transcription of it.

That agreement is not a tautology. **The two edges come from somewhere else.**
In the single file they are two lines an author wrote; here no member declares
them and none could, so they are derived by the saturation from the declared
`contrary` pair — and pair 2 still gets **no** edge, because `bert_glue_s50` and
`llama_openllm_s90` are different setting atoms. The single-file version proves
the calculus does the right thing when a human has already collated the papers;
this one proves the collation itself is mechanical.

The *bytes* are deliberately not equal. A composite verdict leads with
`(scope map)` and reports every status under its `(member alias, claim name)`
handle, so nothing can mistake it for a solo `(verdict …)`.

### A map is a recheck, not a build

`lara check map.laramap` rereads and rechecks every member's current bytes on
every invocation. There is no cache, no lockfile, no pinned digest, and the
`make map-check` target is phony for exactly that reason. Three consequences,
each pinned by a property in `test/MapExampleSpec.hs`:

- **An edited member is picked up with no manifest update**, even when the edit
  preserves the file's modification time and the member's declared `artifact`
  identity. `prop_editedMemberIsRecheckedWithoutManifestUpdate` makes paper B's
  system constant `magnitude_pruning` instead of `apt`: its conclusion stops
  landing on paper A's atoms, the contrary instance dissolves, both generated
  edges vanish, and the two `contested` claims become `justified`.
- **Moving the tree does not move the answer.** Member paths resolve against the
  *manifest's* directory, not the process working directory, and the verdict
  carries the manifest-spelled path rather than a resolved one — so a relocated
  copy with unchanged relative paths produces byte-identical verdict bytes, from
  any working directory.
- **An invalid edit is refused the ordinary way**, as the member's own rejection
  named by alias, one line on stderr, exit 1.

The paper contents and the declared `artifact` digests are illustrative
reconstructions, as everywhere in `examples/`; a digest is author-declared
metadata carried into the composite unchanged, never a checksum of the member's
bytes.

## Validation

### The single-file artifact

All commands run from a clean tree in the worktree.

| Command | Result |
| --- | --- |
| `cabal build exe:lara` | success |
| `cabal run exe:lara -- check examples/agreement-map/example.lara` | accept, exit 0; labels `pa/pb undec, pc/pd in`; statuses `contested, contested, justified, justified` |
| `cabal exec -- runghc scripts/gen-worked-examples.hs` | regenerated all anchors; only `examples/agreement-map/` new, no drift elsewhere |
| `cabal test` | PASS (adds `prop_agreementMap`; freshness, expected-json, coverage, DifferentialSpec all green) |
| `cd lean && lake build` | success (52 jobs) |
| `bash scripts/differential.sh` | `pass=419 fail=0`, `negative pass=54 fail=0` — Haskell and Lean drivers agree byte-exactly on the agreement-map verdict |

### The four-artifact map

All commands run from the worktree root.

| Command | Result |
| --- | --- |
| `cabal run exe:lara -- check examples/agreement-map-multi/paper-{a,b,c,d}/example.lara` | each accepts, exit 0; one unattacked argument, one `justified` claim |
| `cabal run exe:lara -- check examples/agreement-map-multi/map.laramap` | accept, exit 0; `(labels (0 undec) (1 undec) (2 in) (3 in))`, `(edges (0 1) (1 0))`, statuses `contested, contested, justified, justified` — 1032 bytes |
| `make map-check` | same bytes |
| `make map-check OUT=/tmp/map.verdict.sexp` | same bytes, written atomically to the file; stdout empty |
| `cabal exec -- runghc scripts/gen-worked-examples.hs` | wrote the four members' `example.core.sexp` + `expected.json`; **no other anchor changed** |
| `cabal test all --test-show-details=direct` | PASS (adds `MapExampleSpec`'s twelve properties and four `DifferentialSpec` verdict goldens) |
| `cd lean && lake build` | success (179 jobs) |
| `bash scripts/differential.sh` | `pass=673 fail=0`, `negative pass=66 fail=0` — the four new solo anchors included |
| `bash scripts/check-map-conformance.sh` | `map anchors pass=6 fail=0`, `negative pass=16 fail=0`; the new anchor reports `verdicts agree (1032 bytes)` |

The last row is the cross-driver claim in full: the Haskell driver reads the
manifest, rereads the four members and links them; the Lean `lara-map-driver`
is handed only the `map-check-input@1` envelope — four unqualified units — and
performs the qualification, the merge, the saturation, `checkUnit` and the
grounded read itself. Neither reads the other's verdict, and the 1032 bytes are
two computations meeting.

### End-to-end cost

Measured by `make bench-map`, the map mode of the committed bench harness.
Its protocol, and the dated table for every accepted map anchor,
are in [`../performance.md`](../performance.md#the-multi-artifact-map-a-separate-protocol).
A map is a different shape of work from the kernel bench's: it reads and parses
several `.lara` sources, checks each, then links and checks again. So it has its
own protocol and its own table, and none of its numbers may be set beside the
kernel rows. There is no cache across invocations, so a full pass is the cost of
*every* `lara check <map.laramap>`, including one whose members have not
changed.

For this map at commit `ad513b5`, on an AMD EPYC 9354 with GHC 9.10.3, with
every file pre-read and then medians over 5 sections of 100 batched passes:

| Work | Median | Worst |
| --- | --- | --- |
| the map: four members loaded, rechecked, linked, checked again, evaluated, rendered | **2.78 ms** | 2.81 ms |
| the same over pre-loaded members: link, linked check, evaluate, render | 0.27 ms | 0.28 ms |

About nine tenths of a pass is the four members' own load and recheck.
Qualification, the merge, cross-member saturation, the linked `checkUnit`, the
grounded evaluation and the composite encoding together cost about 0.27 ms.

An earlier version of this section quoted a hand-taken table instead: 4.02 ms
per pass, timed around `Lara.Map.Driver.runMap` with file reads included, on GHC
9.6.6 `-O1`, beside per-member and single-file rows. It was retired because no
committed harness could regenerate it; the table above comes from one command.
The two protocols differ (the harness pre-reads the files, the old timing did
not), so the old and new figures should not be compared.

**Why there is no per-command wall-clock row.** Timing the CLI was tried and the
result is not reportable as a property of Lara. In a shell loop of 300 execs on
the machine above, `lara check <map>` measured ≈12.4 ms per invocation and the
same binary *with no arguments at all* measured ≈11.7 ms — a difference of
≈0.7 ms, where the pipeline it added measured about 4 ms in-process at the time.
The two cannot both be serial, so the ≈11.7 ms floor is not startup being paid
before the work begins.
It is per-exec overhead of the measuring environment that overlaps the child's
execution: in the same loop `/usr/bin/true` measured ≈1.0 ms per exec, which is
one to two orders of magnitude above a bare `fork`+`exec` and is a fact about
the harness, not about any program run under it.

So a number from that loop is a property of the sandbox it was measured in and
would mislead anyone who read it as the cost of `make map-check` on their own
machine. The in-process table above is the figure this document stands behind;
whoever wants a per-command number should measure it in the environment they
care about.

No caching was added, and none is planned: see D1 of
[`../multi-artifact-composition-decision.md`](../multi-artifact-composition-decision.md).
