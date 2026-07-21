# Novelty and related work: the delta LARA must defend

_The novelty-defense artifact. Consolidates the deltas scattered across `gap-resolution.md`,
`comparison-rit-lara.md`, and `../plans/popl-research-review.md` §7 into one place, so the paper's
related-work section and the "why is this new?" rebuttal are on record before M0. Written
2026-07-21._

## 0. The framing rule (read first)

**Do not claim "no prior work formalizes research claims."** It is false and it is the fastest path
to desk rejection: Micropublications, AIF, nanopublications, and — most sharply — EG-VAR all
formalize scientific claims and their evidence. A reviewer who knows any of these stops reading at
that sentence. The space is *populated*; the contribution is a precise **delta within it**, not the
discovery of an empty field (`popl-research-review.md` §2 #12: composition alone is a weak novelty
claim).

## 1. The one-sentence novelty claim

> LARA is the first **proof-carrying language** whose programs are typed warrant certificates —
> evidence leaves, strict/defeasible warrant-rule instances, critical-question obligations, and
> typed rebut/undercut/undermine relations — that a small checker **compiles into an argumentation
> framework and a replayable four-state claim status**, with **mechanized accountability and
> status-preservation theorems** stated over an explicit leaf interface.

The novelty is the **object and its guarantee** — a checked, defeasible, replayable warrant
certificate with located failure — not the act of formalizing a claim. Three parts, none of which
any prior system combines:

1. a typed warrant-certificate **calculus** with policy-generated obligations and typed attacks;
2. a **semantics-preserving compilation** into a Dung framework with grounded four-state status;
3. **mechanized** accountability / status-preservation theorems over the leaf interface.

## 2. The delta table (prior art → what LARA adds)

| Prior art (in bib) | What it does | What it lacks that LARA has |
| --- | --- | --- |
| **Micropublications** (Clark et al. 2014) | RDF model of claims, evidence, support, challenge, attribution | A **representation model, not a checker.** Support is a *declared* relation, never checked; no status computation, no located defeat, no typed attacks, no soundness theorem. |
| **AIF** (arg-tech) | Typed interchange vocabulary for inference, conflict, preference | An **interchange format, not a language with checking semantics.** No proof-carrying discipline, no compilation theorem, no replay. LARA reuses its "support = positional identity" idea (spec §3.1) and cites it as related, not as the mechanism. |
| **EG-VAR** (Ren 2026; ICML TAIGR **workshop**) | Tool-attested empirical claims verified via Lean 4 kernel proofs; `mkVerified` requires an `Attested_T` runtime token, so a verified output structurally descends from a tool call (Thm 3.1) and type-checks (Thm 3.2) | **Monotonic**: attest a leaf, prove a Σ-goal, done — **no defeasible reasoning, no defeat, no argumentation layer, no critical-question completeness**; a recorded dead end cannot retract anything. By its own admission (M.1(ii)) the tools and per-source *lifts* are **trusted, not checked** ("a semantically wrong audited lift can certify a wrong formalized claim") — so despite the title's "eliminating hallucination," it relocates trust to the lift rather than removing it. LARA's non-monotonic defeat, policy-relative completeness, and four-state located status are exactly what it lacks. Its self-claim — "the **first** proof-assistant-verified architecture in Lean 4 for this setting" — bounds *our* claim: LARA must not claim first-to-formalize, only first-to-make-defeasible-and-checkable. |
| **Pandžić** (2022, two papers) | Defeasible arguments as justification-logic terms with rebut/undercut/undermine | Pure logic, **no artifact application**; **factive** (keeps A1 globally — LARA confines it to the strict sort, `gap-resolution.md`); no policy / critical-question layer; no compilation-to-AF theorem; no evaluation. |
| **ASPIC+** (Modgil–Prakken 2014) | Structured-argumentation framework: rules, attacks, rationality postulates | A **framework, not a language or artifact.** LARA is a concrete typed calculus that compiles to it, with a proof-carrying checker and mechanized metatheory, applied to research warrants. |
| **Dung** (1995) | Abstract argumentation, grounded semantics | Abstract nodes/edges only; **no structure inside arguments**, no leaves, no obligations, no provenance, no source language. LARA supplies all of these and compiles down to Dung. |
| **PCC / FPC** (Necula 1997; Miller 2015) | Untrusted-producer / checked-certificate architecture | The **architecture ancestor**, applied to machine proofs. LARA is that discipline applied to *defeasible empirical warrants* with a non-monotonic layer PCC never has. |
| **`rit`** (sibling project) | Lean kernel + sha256-pinned facts + AND/OR claim DAG | Monotonic proof-or-evidence attestation; **no defeasible defeat, no `gap`/`contested`/`defeated` distinction, no policy of warrant schemes.** See `comparison-rit-lara.md` for the full sibling delta. |

## 3. The two real novelty risks (and the defense for each)

Novelty is a concern — but the concern is precision, not emptiness. Two threats are sharp enough to
name and pre-empt:

### 3.1 EG-VAR proximity (the sharpest)

EG-VAR (2026) is "very close" (`popl-research-review.md` §7 #15): tool-attested empirical claims,
kernel-checked. It can genuinely narrow the contribution — but note the venue is the **ICML 2026
TAIGR workshop** (single-author, n=120 single-substrate eval), not a peer-reviewed conference paper,
and its own limitations (App. M.1) concede the trust boundary its title overclaims. See
`prior-art-lessons.md` for the full firsthand read and what to borrow. **Defense — three concrete
differentiators it does not have:**

- **Non-monotonic defeat.** A recorded dead end can flip a claim to `defeated`. EG-VAR has no
  retraction mechanism; adding an attested fact never overturns a prior conclusion.
- **Policy-relative completeness.** Critical-question obligations surface *what was not shown*
  (`gap`), distinct from *what was refuted* (`defeated`). EG-VAR attests presence, not coverage.
- **Four-state located status.** `justified / gap / defeated / contested` with a source-located
  reason, vs. per-leaf pass/fail attestation.

State this delta **early and explicitly** in related work; it is a strength, not something to hide.

### 3.2 "Composition of mature parts"

Dung + ASPIC+ + LP + PCC all exist; "we glued them" is the weak-novelty objection
(`popl-research-review.md` §2 #12). **Defense — a theorem specific to the combination:** a typed
compilation from warrant programs to structured argumentation that **preserves dependency
provenance, attack targets, open obligations, and claim status** — a property none of the parts
provides individually. The evaluation then shows the abstraction catches and *localizes* real
warrant failures a holistic reviewer cannot (`research-proposal.md:400`). Composition is the method;
the theorem + localization is the contribution.

## 4. Positioning (where to anchor the paper)

Per `research-proposal.md` §9, anchor in this order:

1. **Structured argumentation** (Dung, ASPIC+, schemes/CQs) — the semantic center.
2. **Proof certificates / PCC** (Necula, Miller, LP) — the trust architecture.
3. **Semantic publishing / provenance** (Micropublications, AIF, RO-Crate) — the application domain
   and the closest claim-formalization prior art.
4. **Autoformalization faithfulness** (Beyond Compilation, EG-VAR, DSP/LeanDojo/Baldur) — the
   measured-residual-risk framing for the untrusted lowering.

LP realization is **supporting metatheory for the optional strict fragment**, never the novelty and
never the guarantee behind NL lowering. Leading with modal/JL depth moves LARA onto ground Pandžić
already occupies — the opposite of a novelty argument; the design keeps modal logic off the critical
path deliberately (`research-proposal.md` §3, Steps 1–3).

## 5. Sentences to use, and to avoid

**Use:**
- "the first checkable, defeasible warrant-certificate language for research claims, with mechanized
  accountability and located four-state status."
- "prior systems represent or attest claims; LARA compiles them to a replayable status object and
  proves the compilation sound."

**Avoid:**
- "no prior work formalizes research claims" (false — Micropublications, AIF, EG-VAR).
- "LARA is Lean for science" / "modal logic for research" (invites Pandžić and EG-VAR objections;
  obscures the defeasible + graph-semantics contribution — see `../plans/research-proposal.md` §3.1).
- any novelty claim resting on composition alone.

## Sources

All in `../plans/lara-related-work.bib`. The must-explain-the-delta set: Micropublications
(doi:10.1186/2041-1480-5-28), AIF (arg-tech spec), EG-VAR (arXiv:2607.12650), Pandžić
(doi:10.3233/AAC-200536, doi:10.1007/s10472-021-09765-z), ASPIC+ (doi:10.1080/19462166.2013.869766).
