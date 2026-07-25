# Related Work

_Typed dependency graph. Anchored per `plans/popl-research-review.md` §9 and `docs/novelty-and-related-work.md`:
structured argumentation is the semantic center; proof-certificates/PCC is the trust architecture;
semantic publishing is the application domain; autoformalization is the measured-residual-risk framing._

## RW01: Dung 1995, "On the Acceptability of Arguments and its Fundamental Role in Nonmonotonic Reasoning…"
- **DOI**: 10.1016/0004-3702(94)00041-X
- **Type**: imports
- **Delta**:
  - What changed: LARA compiles its typed source programs *down* to Dung's abstract frameworks and uses grounded semantics for the four-state status.
  - Why: Dung supplies the non-monotonic acceptance semantics and the least-fixpoint labelling.
- **Claims affected**: C06, C07
- **Adopted elements**: abstract argumentation framework `(Args, Attack)`; grounded labelling as a least fixed point.

## RW02: Modgil & Prakken 2014, "The ASPIC+ framework for structured argumentation: a tutorial"
- **DOI**: 10.1080/19462166.2013.869766
- **Type**: imports
- **Delta**:
  - What changed: LARA is a concrete typed *calculus* that compiles to structured argumentation, with a proof-carrying checker and mechanized metatheory; ASPIC+ is a framework.
  - Why: ASPIC+ supplies rebut/undercut/undermine, strict-vs-defeasible, subargument closure, and the rationality-postulate conditions §8.1 exists to satisfy.
- **Claims affected**: C02, C09
- **Adopted elements**: the three attack types; strict rules are unnamed/unattackable; sub-argument closure; the consistency postulates.

## RW03: Pandžić 2022, "A logic of defeasible argumentation: constructing arguments in justification logic" (+ the undermining-attacks paper)
- **DOI**: 10.3233/AAC-200536 ; 10.1007/s10472-021-09765-z
- **Type**: bounds
- **Delta**:
  - What changed: Pandžić represents defeasible arguments as object-level justification terms with rebut/undercut/undermine — the closest prior art, so it *bounds* LARA's novelty. But it is pure logic (factive JT, keeps A1 globally; no policy/critical-question layer; no artifact application; no compilation-to-AF theorem; no evaluation).
  - Why: validates the terms-as-arguments shape and forces LARA's delta to be precise: LARA is the calculus-as-language (policy obligations, positional attacks, compilation theorem, mechanization, four-state aggregation), NOT terms-as-arguments per se.
- **Claims affected**: C03, C06
- **Adopted elements**: terms-as-defeasible-arguments as a viable shape; the JT-vs-J4 factivity diagnosis (LARA departs by removing the support-level modality entirely).

## RW04: Clark, Ciccarese & Goble 2014, "Micropublications: a semantic model for claims, evidence, arguments and annotations…"
- **DOI**: 10.1186/2041-1480-5-28
- **Type**: bounds
- **Delta**:
  - What changed: Micropublications is an RDF *representation model* — support is a declared relation, never checked; no status computation, no located defeat, no soundness theorem. LARA compiles claim-support programs to a *checked, replayable status object*.
  - Why: the closest claim-formalization prior art; LARA must state the delta (checked programs + status semantics vs an RDF model) and must NOT claim "no prior work formalizes research claims."
- **Claims affected**: C01
- **Adopted elements**: NL Statement as truth-bearer with a formal side-car; support as a defeasible, declared relation kept explicit.

## RW05: AIF (Argument Interchange Format) specification, arg-tech
- **DOI**: arg-tech.org/wp-content/uploads/2011/09/aif-spec.pdf
- **Type**: bounds
- **Delta**:
  - What changed: AIF is a typed interchange *vocabulary* for inference/conflict/preference — no proof-carrying discipline, no compilation theorem, no replay. LARA is a language with checking semantics.
  - Why: LARA reuses AIF's "support = positional identity" idea (the inference node's out-edge lands on the claim node) and cites it as related, not as the mechanism.
- **Claims affected**: C01
- **Adopted elements**: positional-identity support (no entailment query).

## RW06: Necula 1997, "Proof-Carrying Code" ; Miller 2015, "Foundational Proof Certificates"
- **DOI**: 10.1145/263699.263712 ; lix.polytechnique.fr/~dale/papers/appa2014.pdf
- **Type**: imports
- **Delta**:
  - What changed: PCC/FPC is the untrusted-producer / checked-certificate architecture, applied to machine proofs; LARA applies that discipline to *defeasible empirical claim support* with a non-monotonic layer PCC never has, and defines certificate semantics against a small kernel (FPC).
  - Why: the architecture ancestor and the "certificate semantics against a small checker" precedent for the backend contract.
- **Claims affected**: C03, C05, C11
- **Adopted elements**: untrusted producer / tiny trusted checker; rejection costs one failed check; the backend-neutral certificate contract.

## RW07: Ren 2026, "EG-VAR" (ICML 2026 TAIGR workshop)
- **DOI**: arXiv:2607.12650
- **Type**: bounds
- **Delta**:
  - What changed: EG-VAR verifies tool-attested empirical claims via Lean 4 kernel proofs (`mkVerified` requires an `Attested_T` runtime token). But it is *monotonic* — no defeasible reasoning, no defeat, no argumentation layer, no critical-question completeness — and by its own App. M.1(ii) the per-source lifts are trusted, not checked. Its self-claim ("first proof-assistant-verified architecture in Lean 4 for this setting") bounds LARA to first-to-make-defeasible-and-checkable, never first-to-formalize.
  - Why: the sharpest proximity; the differentiators (non-monotonic defeat, policy-relative completeness, four-state located status) must be stated early.
- **Claims affected**: C06, C11
- **Adopted elements**: the attested-constructor pattern (a fact type whose sole constructor needs a runtime witness) → maps onto spec §4.3 `certified` leaves / optional TL-1; the Tier-1/Tier-2 eval split corroborating LARA's Axis (a) vs (b) separation.

## RW08: Jiang et al. 2023, "Draft, Sketch, and Prove" ; First et al. 2023, "Baldur" ; Yang et al. 2023, "LeanDojo" ; Sun et al. 2023, "Clover"
- **DOI**: arXiv:2210.12283 ; arXiv:2303.04910 ; arXiv:2306.15626 ; arXiv:2310.17807
- **Type**: baseline
- **Delta**:
  - What changed: these are the untrusted-LLM-producer / trusted-checker precedents. They are judged by *verified-success-rate* (DSP 20.9%→39.3% on miniF2F; Baldur over 6,336 Isabelle/HOL theorems), *adversarial zero-false-positive rejection* (Clover: high acceptance on correct, zero false positives on incorrect Dafny), and *anti-memorization* (LeanDojo's novel-premises split) — never user studies or latency.
  - Why: they fix the evaluation methodology for LARA's untrusted Python elaborator (Phase E) and ground C11.
- **Claims affected**: C11
- **Adopted elements**: verified-success-rate as the metric; the adversarial rejection-class and anti-memorization design levers.

## RW09: Yang et al. 2011 (Csmith, PLDI 2011) ; Park et al. 2021 (JEST, ICSE 2021) ; Marmsoler & Brucker 2022 (Solidity conformance, TAP 2022)
- **DOI**: PLDI 2011 (Csmith) ; JEST ICSE 2021 ; logicalhacking.com/publications/marmsoler.ea-conformance-2022
- **Type**: imports
- **Delta**:
  - What changed: these fix how LARA frames its Haskell↔Lean differential testing — JEST-style N+1 (reference is a fallible oracle; localizes spec vs implementation bugs) rather than Csmith-style oracle-free voting; Marmsoler–Brucker code-generate an executable oracle from a mechanized semantics.
  - Why: corrects the differential-testing precedent and grounds C12; the single-interpretation discipline (from Csmith) is what makes divergence a real bug.
- **Claims affected**: C12
- **Adopted elements**: N+1-version framing; executable-oracle-from-mechanized-semantics; single-interpretation discipline.

## RW10: Artemov 2001, "Explicit Provability and Constructive Semantics" (Logic of Proofs)
- **DOI**: sartemov.ws.gc.cuny.edu/files/2014/01/Artemov-Explicit-Provability-and-Constructive-Semantics.pdf
- **Type**: bounds
- **Delta**:
  - What changed: LP's realization theorem is `S4 ⊢ F ⟹ LP ⊢ Fʳ` — theorem-to-realization only. The original LARA design over-used it as an ARA-lowering guarantee; the pivot (trace N05) demoted LP to an *optional* adapter behind the backend seam and made natural deduction the required reference.
  - Why: realization says nothing about NL→formal faithfulness; LP ships only if corpus evidence shows LP-specific `t:F`/`!`/`+`/realization occurs in real certificates.
- **Claims affected**: C04 (LP is one adapter among many; backend replacement makes it non-foundational)
- **Adopted elements**: LP proof polynomials retained as an optional adapter's internal language; A0–A4 + constant specification live only inside that adapter.

## Additional citations (briefer — no distinct technical delta)
- **Yu & Zenker 2020** (schemes, critical questions, complete argument evaluation, doi:10.1007/s10503-020-09512-4) — theory behind policy-relative completeness / mandatory-vs-optional critical questions (spec §4.2).
- **Caminada & Amgoud 2007** (evaluation of argumentation formalisms, doi:10.1016/j.artint.2007.02.003) — Examples 5–6 motivate the §8.1 Path-B/Path-A consistency situation.
- **Zhang et al. 2026, "Beyond Compilation"** (arXiv:2606.31002) — compile-success ≠ faithfulness (89.5% vs 60.5%); the measured-residual-risk framing for Axis (b).
- **SIGPLAN "Checklist Manifesto for Empirical Evaluation" 2019** — artifact evaluation certifies reproducibility, not claim-support; grounds C10.
- **`rit`** (sibling project) — Lean kernel + sha256-pinned facts + AND/OR claim DAG; monotonic, no `gap`/`contested`/`defeated` distinction. Source-verified 2026-07-25 (C18): its world-facing fragment is five object kinds / six relations over log-extracted naturals discharged `by decide`, so paper claims enter through a silent defeasible narrowing LARA types; its non-kernel disagreement machinery (collisions, tiers, weakest-link roll-up) is an unproven shadow argumentation framework whose open aggregation problem grounded semantics answers (see `docs/comparison-rit-lara.md` §11).
