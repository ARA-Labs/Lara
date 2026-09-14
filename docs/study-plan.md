# LARA study plan

_What to read before implementing, ordered by what it unblocks. Companion to
`lara-related-work.bib` (the BibTeX). This plan prioritizes by the build order in
`engineering-plan.md`: M0 corpus annotation first, then the trusted-core modules, then evaluation.
Written 2026-07-21._

_A dated onboarding reading list for new contributors, keyed to a build order
that has since completed (M1–M5 are closed). The readings still orient; the
urgency ordering is historical._

## How to use this

Each item has a **depth** and an **unblocks** target. Depth is either **deep** (read closely, work
the key definitions by hand) or **skim** (grasp the idea and one load-bearing result). Do not read
linearly — read each tier just before you start the work it unblocks. The minimum path is starred
(★): three readings cover the M0 annotation vocabulary and the strict-certificate
producer/checker discipline.

Track the deep readings by writing a one-paragraph note per paper into `docs/reading-notes/` (the
delta LARA must defend, and any corpus pattern it predicts). Those notes seed the related-work
section of the paper.

---

## Tier 0 — before M0 corpus annotation (start now)

M0 fixes the inference schemes, critical questions, and attack typing you annotate the corpus with;
these three define that vocabulary. Getting them wrong pollutes the frozen v0.1 benchmark.

| # | Reading | Depth | Unblocks | Link |
| --- | --- | --- | --- | --- |
| ★1 | **Modgil & Prakken 2014**, ASPIC+ tutorial (§2–3 closely) | deep | the whole defeat layer; annotation fields #3 (rules), #6 (attacks) | doi:10.1080/19462166.2013.869766 |
| ★2 | **Yu & Zenker 2020**, Schemes, Critical Questions, and Complete Argument Evaluation | deep | "policy-complete"; annotation field #4 (mandatory vs optional CQs), spec §4.2 | doi:10.1007/s10503-020-09512-4 |
| 3 | **Caminada & Amgoud 2007**, On the Evaluation of Argumentation Formalisms — **Examples 5–6 especially** | skim + 2 examples | recognizing the §8.1 Path-B/Path-A situation in the corpus | doi:10.1016/j.artint.2007.02.003 |

**Why these first.** #1 is LARA's semantic center (Track C): rebut/undercut/undermine, strict-vs-
defeasible, and the rationality-postulate conditions §8.1 exists to satisfy. #2 is the theory behind
critical-question obligations — how an experiment's Setup/Baselines becomes mandatory-vs-optional
CQs. #3's Examples 5–6 are *why* §8.1 exists (a conflict behind a strict rule going unregistered);
you need to spot that pattern if the corpus produces it, since it is the flip criterion to Path A.

**Checkpoint before annotating:** you can, by hand, take resnet claim C02 + experiment E01 and write
the inference scheme, its critical questions, and classify exploration node N04 as attack-or-no-edge.

---

## Tier 1 — while annotating / before freezing the calculus (M0 → M1)

| # | Reading | Depth | Unblocks | Link |
| --- | --- | --- | --- | --- |
| 4 | **Clark, Ciccarese & Goble 2014**, Micropublications | deep | how to read `claims.md`; the delta LARA must defend vs prior claim models | doi:10.1186/2041-1480-5-28 |
| 5 | **AIF specification** (arg-tech) | skim | "support = positional identity" (spec §3.1); why `supports` needs no solver | arg-tech.org/wp-content/uploads/2011/09/aif-spec.pdf |
| 6 | **Pandžić 2022**, A Logic of Defeasible Argumentation (first paper) | deep | the closest prior system; bounds LARA's novelty claim | doi:10.3233/AAC-200536 |
| 7 | **Pandžić 2022**, Undermining Attacks in Default Justification Logic (second paper) | skim | undermining-attack treatment; confirms `gap-resolution.md` finding firsthand | doi:10.1007/s10472-021-09765-z |
| 8 | **Dung 1995**, On the Acceptability of Arguments | skim | grounded labelling as a least fixpoint, for `Lara.Grounded` | doi:10.1016/0004-3702(94)00041-X |

**Why now.** #4 is the closest prior art on machine-readable claims+evidence+support+challenge; LARA
must state its delta (checked claim-support programs + status semantics vs their RDF model). #6/#7 are the
single closest system — `gap-resolution.md` already extracted the key finding (Pandžić keeps
factivity global; LARA confines it to the strict sort), but read them firsthand because a reviewer
will, and this is the "what's the delta from Pandžić?" defense. #8: you will implement grounded from
#1's presentation, but read Dung for the fixpoint definition.

---

## Tier 2 — before `Lara.Strict` and the reference adapter

| # | Reading | Depth | Unblocks | Link |
| --- | --- | --- | --- | --- |
| ★9 | **Miller 2015**, Foundational Proof Certificates | deep | certificate semantics against a small checker; the backend contract | lix PDF (bib `url`) |
| 10 | **Pierce 2002**, Types and Programming Languages — STLC chapters | deep | de Bruijn natural-deduction certificates and the reference soundness induction | book (bib) |
| 11 | **Necula 1997**, Proof-Carrying Code | skim | the producer/checker TCB discipline (Track D) | doi:10.1145/263699.263712 |
| 12 | **Artemov 2001**, Explicit Provability — **Sections 5, 8, 9 only** | conditional deep | optional LP adapter: A0–A4, constant specifications, realization boundary | sartemov PDF (bib `url`) |

**Why.** #9 defines the general certificate-to-kernel relationship rather than privileging one
logic. #10 supplies the small reference adapter and its structural proof method. #11 internalizes
"rejection costs nothing; the checker is the TCB." Read #12 only if corpus evidence selects LP; its
realization theorem is theorem-to-realization, **not** an ARA-lowering guarantee.

**Checkpoint:** you can state the six backend obligations, prove natural-deduction soundness by
induction, and prove backend replacement through AF isomorphism after certificate erasure. If LP
ships, additionally state A0–A4 and the exact admissible constant-specification predicate.

---

## Tier 3 — before evaluation design (defer to ~M5; know they exist now)

| # | Reading | Depth | Unblocks | Link |
| --- | --- | --- | --- | --- |
| 13 | **Zhang et al. 2026**, Beyond Compilation | deep (at eval) | Axis (b): compile-success ≠ faithfulness (89.5% vs 60.5%) | arXiv:2606.31002 |
| 14 | **Ren et al. 2026**, EG-VAR | skim now / deep at eval | sharpest trust-boundary comparison; narrows novelty | arXiv:2607.12650 |
| 15 | **Jiang et al. 2023**, Draft-Sketch-Prove | skim | untrusted-producer/checked-output precedent (elaborator, Phase E) | arXiv:2210.12283 |
| 16 | **Yang et al. 2023**, LeanDojo | skim | retrieval-augmented checked proof production | arXiv:2306.15626 |
| 17 | **First et al. 2023**, Baldur | skim | whole-proof generation + repair | people.cs.umass.edu (bib `url`) |

These are preprints (#13, #14) or implementation precedents (#15–17), not foundations. Read #13/#14
before finalizing evaluation and novelty claims; read #15–17 when building the elaborator, not before.

---

## Deliberately deferred

**Evidence logic** — van Benthem & Pacuit 2011 (dynamic evidence-based beliefs, `dare.uva.nl`
record) and van Benthem, Fernández-Duque & Pacuit 2014 (doi:10.1016/j.apal.2013.07.007). This is
Track B, the "design conscience" explicitly *not* in the kernel (spec §3). Read only when a policy
needs graded-evidence semantics; it is not on the implementation path.

---

## Schedule (maps to milestones)

| Window | Read | In parallel with |
| --- | --- | --- |
| Week 1 (now) | Tier 0 (#1–3) | drafting the M0 annotation guide |
| Weeks 2–4 | Tier 1 (#4–8) | M0 annotation (`corpus-map.md` §4) |
| M0→M1 freeze | re-read #1, #9 | writing the frozen spec / static judgments |
| Before `Lara.Strict` | Tier 2 (#9–11; #12 only if LP ships) | backend registry + natural-deduction adapter |
| ~M5 | Tier 3 | evaluation design and the untrusted elaborator |

**If you read only three:** #1 (ASPIC+), #2 (Yu–Zenker), #9 (Miller). They cover the annotation
vocabulary, policy-relative completeness, and the backend-neutral certificate discipline.
