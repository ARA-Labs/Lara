# Novelty and related work

This document states how Lara differs from its nearest neighbors. The lines of
work Lara builds on are described in [`foundations.md`](foundations.md).

## 1. The one-sentence novelty claim

> Lara is the first **proof-carrying language** whose programs are typed claim-support certificates —
> evidence leaves, strict/defeasible inference-scheme instances, critical-question obligations, and
> typed rebut/undercut/undermine relations — that a small checker **compiles into an argumentation
> framework and a replayable four-state claim status**, with **mechanized accountability and
> status-preservation theorems** stated over an explicit leaf interface and a
> **backend-parametric strict-certificate seam**.

Formalizing scientific claims and their evidence is not new: Micropublications, AIF,
nanopublications and EG-VAR all do it. The novelty is the **object and its guarantee** — a checked,
defeasible, replayable claim-support certificate with located failure. Three parts, none of which
any prior system combines:

1. a typed claim-support **calculus** with policy-generated obligations and typed attacks;
2. a **semantics-preserving compilation** into a Dung framework with grounded four-state status;
3. **mechanized** accountability, backend-replacement, and status-preservation theorems over the
   leaf and strict-certificate interfaces.

## 2. The delta table (prior art → what Lara adds)

| Prior art (in bib) | What it does | What it lacks that Lara has |
| --- | --- | --- |
| **Micropublications** (Clark et al. 2014) | RDF model of claims, evidence, support, challenge, attribution | A **representation model, not a checker.** Support is a *declared* relation, never checked; no status computation, no located defeat, no typed attacks, no soundness theorem. |
| **AIF** (arg-tech) | Typed interchange vocabulary for inference, conflict, preference | An **interchange format, not a language with checking semantics.** No proof-carrying discipline, no compilation theorem, no replay. Lara adopts its "support = positional identity" idea (spec §3.1): support is an edge landing on the claim node, not an entailment query, which keeps entailment out of the trusted base. |
| **EG-VAR** (Ren 2026; ICML TAIGR workshop) | Tool-attested empirical claims verified via Lean 4 kernel proofs; `mkVerified` requires an `Attested_T` runtime token, so a verified output structurally descends from a tool call (Thm 3.1) and type-checks (Thm 3.2) | **Monotonic**: attest a leaf, prove a Σ-goal, done — **no defeasible reasoning, no defeat, no argumentation layer, no critical-question completeness**; a recorded dead end cannot retract anything. By its own statement (App. M.1(ii)) the tools and per-source *lifts* are **trusted, not checked** ("a semantically wrong audited lift can certify a wrong formalized claim"), so trust is relocated to the lift rather than removed. Lara's non-monotonic defeat, policy-relative completeness, and four-state located status are exactly what it lacks. |
| **Pandžić** (2022, two papers) | Defeasible arguments as justification-logic terms with rebut/undercut/undermine | Pure logic, **no artifact application**; **factive** (keeps A1 globally — Lara has no support-level modality and confines factive logics behind the strict-backend interface); no policy / critical-question layer; no compilation-to-AF theorem; no evaluation. |
| **ASPIC+** (Modgil–Prakken 2014) | Structured-argumentation framework: rules, attacks, rationality postulates | A **framework, not a language or artifact.** Lara is a concrete typed calculus that compiles to it, with a proof-carrying checker and mechanized metatheory, applied to research claim support. |
| **Dung** (1995) | Abstract argumentation, grounded semantics | Abstract nodes/edges only; **no structure inside arguments**, no leaves, no obligations, no provenance, no source language. Lara supplies all of these and compiles down to Dung. |
| **PCC / FPC** (Necula 1997; Miller 2015) | Untrusted-producer / checked-certificate architecture | The **architecture ancestor**, applied to machine proofs. Lara is that discipline applied to *defeasible empirical claim support* with a non-monotonic layer PCC never has. |
| **`rit`** (sibling project) | Lean kernel + sha256-pinned facts + AND/OR claim DAG. Formal vocabulary: six relations over log-extracted numbers — ≤, beats-baseline, interval bounds, arithmetic entail/contradict — proved `by decide` | Monotonic proof-or-evidence attestation; **no defeasible defeat, no `gap`/`contested`/`defeated` distinction, no policy of inference schemes.** Every paper claim reaches its kernel through a **silent, unverified narrowing** ("faster" ⇒ `2875 < 3225`); Lara types and adjudicates that narrowing. Its non-kernel disagreement machinery (collisions, tiers, weakest-link roll-up) is an unproven shadow argumentation framework whose aggregation Lara's grounded semantics answers. |

## 3. The closest neighbors

### 3.1 EG-VAR

EG-VAR is a four-layer stack for verified empirical claims: deterministic tool queries, audited
per-source lifts from storage to world facts, a Lean 4 kernel that mints `Verified` claims, and a
solver LLM that proposes proofs the kernel checks. `mkVerified`, the sole constructor of
`Evidence Verified w`, requires an `Attested_T` token emitted by the runtime; the answer is the
witness of a Σ-type goal. Cases it cannot verify return an abstention with a replayable audit
trail. Its fully passing tier uses committed gold typed goals that bypass the NL→Lean formalizer;
only its second tier runs the formalizer end to end.

Lara shares two design choices with it. Certified evidence enters Lara only through sealed
admission judgments whose constructors are hidden
([`evidence-admission-design.md`](evidence-admission-design.md), "Sealed types and source-door
guarantees"), the same sole-witness-constructor shape as `mkVerified`. Lara's evaluation likewise
separates the LLM-independent checker measurements (axis (a)) from the faithfulness of the
untrusted lowering (axis (b)) ([`evaluation.md`](evaluation.md)), as EG-VAR separates its kernel
tier from its formalizer tier. Both systems trust their leaf boundary; Lara states it as a
hypothesis of its theorems (spec §1, §11).

Three differences carry the delta:

- **Non-monotonic defeat.** A recorded dead end can flip a claim to `defeated`. EG-VAR has no
  retraction mechanism; adding an attested fact never overturns a prior conclusion.
- **Policy-relative completeness.** Critical-question obligations surface *what was not shown*
  (`gap`), distinct from *what was refuted* (`defeated`). EG-VAR attests presence, not coverage.
- **Four-state located status.** `justified / gap / defeated / contested` with a source-located
  reason, vs. per-leaf pass/fail attestation.

### 3.2 Composition of existing parts

Dung, ASPIC+, proof-certificate backends and PCC all exist separately. The property specific to
their combination is a typed compilation from claim-support programs to structured argumentation
that **preserves dependency provenance, attack targets, open obligations, and claim status** — a
property none of the parts provides individually. The evaluation measures whether the abstraction
catches and *localizes* real claim-support failures that a holistic reviewer score does not.

## 4. Related areas and the role of strict logic

Lara's related work falls into four areas: structured argumentation (Dung, ASPIC+, schemes and
critical questions) as the semantic center; proof certificates and PCC (Necula, Miller; natural
deduction and optional adapters) as the trust architecture; semantic publishing and provenance
(Micropublications, AIF, RO-Crate) as the application domain and the closest claim-formalization
prior art; and autoformalization faithfulness (Beyond Compilation, EG-VAR, DSP, LeanDojo, Baldur)
as the measure of residual risk in the untrusted lowering.

Backend replacement and strict-certificate soundness are the core strict metatheory. LP realization
is supporting metatheory for an optional adapter, never the guarantee behind NL lowering. Modal and
justification logic stay off the critical path: structured argumentation is the outer frame, and the
strict-certificate interface is isolated behind it.

## Sources

All in `lara-related-work.bib`. The neighbors whose delta this document states: Micropublications
(doi:10.1186/2041-1480-5-28), AIF (arg-tech spec), EG-VAR (arXiv:2607.12650), Pandžić
(doi:10.3233/AAC-200536, doi:10.1007/s10472-021-09765-z), ASPIC+ (doi:10.1080/19462166.2013.869766).
