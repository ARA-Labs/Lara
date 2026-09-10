# Claim-support calculus decision: one support-term language

_Status: settled for language v0.1. Recorded 2026-07-20; amended 2026-07-21 by
`strict-backend-decision.md`. Supersedes the two-layer reading of `spec.md` (argumentation calculus
+ LP sub-fragment as separate source systems); `spec.md` Sections 3–7 now reflect one claim-support
calculus with a backend-parametric strict-certificate interface._

In plain terms, this record fixes the shape of an *argument* in LARA: one term
language in which every argument (whether a strict, certificate-checked step
or a defeasible, overridable one) is the same kind of object, so the checker
needs only one typing judgment. The strict-certificate interface the terms
plug into is specified separately in `strict-backend-decision.md`; spec §0 has
the one-paragraph vocabulary (claims, leaves, schemes, attacks) this record
assumes.

## Decision

1. **One syntactic category.** Every argument is a **support term**
   `w ::= l | r⟨w₁,…,wₙ ; {q ↦ w_q} ; {o}⟩`. Strict and defeasible are a *mode* of the policy
   rule `r`, not separate syntax. A strict instance is the degenerate case (empty
   critical-question map, no holes) and carries either an explicit trust marker or an opaque
   certificate for a registered backend.
2. **Proof-term traditions supply the term discipline, not LARA's axioms.** The central judgment is
   `Σ; Π; Γ; R ⊢ w : F ▷ O`, read "w supports F with open obligations O." The leaf dependency set
   is `leaves(w)` — the frontier of the term — derived, not tracked. Backend-certificate
   dependencies are reported separately. LP's A0–A4 and realization, when used, belong only to an
   optional LP adapter; they are not axioms of the source calculus.
3. **The support judgment is non-factive.** No support-level justification operator
   (`justified(term, prop)` is removed from v0.1). A strict backend receives only encoded premise
   conclusions and returns acceptance, dependencies, and diagnostics. Its formulas and proof terms
   cannot enter source syntax, so even a factive backend cannot eliminate support into truth.
4. **Attacks are positional.** `rebut w u` targets the root conclusion; `undercut w u@π` targets
   the rule occurrence at position `π`; `undermine w u@π` targets the leaf occurrence at `π`.
   Rebut and undermine type-check against a policy-declared contrary relation, not full classical
   negation.
5. **Absent from the support level:** backend-specific sum, proof variables, modalities, and
   internalized justification operators. Multiple independent supports for a claim are multiple
   support terms (separate AF nodes), never one backend-combined term.

## Why (evidence)

1. **Factivity is wrong for empirical support.** LP A1 (`t:F → F`) says justified implies true —
   correct for mathematical proof, exactly what LARA's honesty story denies for empirical support.
   Non-factive J/J4 motivates the source judgment, but LARA is not axiomatized as either: it avoids
   the support-level modality entirely. Adapter opacity is the stronger firewall because it also
   covers classical provers, model checkers, and future backends.
2. **Backend combination can destroy defeat granularity.** LP's `s + t` is the concrete example: it
   merges alternative supports into one term; the
   defeat semantics needs them as separate AF nodes so an undercut can kill one while the other
   survives (already required by `spec.md` §4). Multiple `arg` declarations play sum's role with
   the correct granularity.
3. **Accountability by construction.** The former judgment component `L` and the intended
   leaf-accountability theorem ("every leaf used is declared and reported") collapse into a
   structural fact: the leaf dependency set of a checked term is exactly the set of leaf constants
   occurring in it. Backend theory dependencies remain explicit through each certificate's
   `uses_beta`; they do not get misclassified as leaves.
4. **The three ASPIC+ attack types are the three kinds of positions in a term** — root
   (conclusion → rebut), internal rule occurrence (→ undercut), frontier leaf (→ undermine).
   Attack well-formedness becomes subterm-occurrence checking plus the contrary relation:
   decidable, local, and source-located diagnostics come for free because a position *is* a
   location. The previous design (`undercut a b.rule`) could only address the outermost rule;
   positions make attacks on inner steps expressible.
5. **Prior art validates the shape and forces precision about the delta.** Pandžić's default
   justification logic represents defeasible arguments as object-level terms `t : F` and covers
   rebutting, undercutting, and undermining attacks (Argument & Computation 2022,
   doi:10.3233/AAC-200536; Ann. Math. Artif. Intell. 90(2–3):297–337, 2022,
   doi:10.1007/s10472-021-09765-z). Terms-as-defeasible-arguments is therefore viable, and LARA
   must not claim it as the novelty.

## Delta vs. Pandžić (what LARA contributes that his logic does not)

| Pandžić (the logic) | LARA (the language and system) |
|---|---|
| Operator-theoretic default justification logic | A checkable certificate language with versioned policies |
| Default rules, no completeness obligations | Scheme instances with critical-question obligations and explicit holes |
| Undermining via belief-revision contraction | Undermining via a typed, policy-declared contrary relation (smaller TCB, decidable) |
| No provenance, artifacts, or admission | Provenance-gated leaf admission, artifact digests, replay identity |
| Semantics given logically | Checked compilation to Dung AFs with mechanized soundness / accountability / status-preservation theorems |
| No implementation or evaluation | Haskell checker, untrusted-LLM producer (PCC architecture), corpus evaluation |

Positioning rule for the paper: cite Pandžić in the must-read tier; the novelty claim is the
calculus-as-language (policy obligations, positional attacks, compilation theorem, mechanization,
four-state aggregation), never terms-as-arguments per se.

## What this dissolves

The question "does LP earn its keep?" no longer determines the core calculus. Backend replacement
proves that claim-support semantics is independent of certificate internals when acceptance profiles
match. The corpus still decides whether the optional LP adapter ships: measure how many strict steps
need LP-specific `t:F`, `!`, `+`, or realization rather than the reference natural-deduction or a
domain checker. The pitch is now: *a claim-support calculus with a small strict-certificate
interface — terms give syntactic accountability and positional defeat; argumentation gives the
non-monotonic semantics; registered backends reduce trust in strict steps without defining
claim-support semantics.*

## Flip criteria

- **Reintroduce an internalized justification operator** if Phase A shows meta-level claims
  ("the paper argues that…", claims about other arguments) are a material fraction of the corpus.
- **Promote the optional LP adapter** (dedicated payload codec and realization results in the paper
  body) if Phase A shows strict modal-deductive chaining is common rather than rare.
- **Revisit belief-revision-style undermining** if the typed contrary relation proves too weak to
  express the undermining attacks annotators actually find.
