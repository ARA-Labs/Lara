# Term-calculus decision: one warrant-term language

_Status: settled for language v0.1. Recorded 2026-07-20. Supersedes the two-layer reading of
`spec.md` (argumentation calculus + LP sub-fragment as separate systems); `spec.md` §§3–7 now
reflect this decision._

## Decision

1. **One syntactic category.** Every argument is a **warrant term**
   `w ::= l | r⟨w₁,…,wₙ ; {q ↦ w_q} ; {o}⟩`. Strict and defeasible are a *mode* of the policy
   rule `r`, not separate syntax. The strict LP fragment survives as the embedded degenerate
   case (strict rule, empty critical-question map, no holes), not as a sibling system.
2. **Justification logic supplies the term discipline, not the axioms.** The central judgment is
   `Σ; Π; Γ ⊢ w : F ▷ O`, read "w warrants F with open obligations O." The dependency set is
   `leaves(w)` — the frontier of the term — derived, not tracked. LP's axiom system (A0–A4,
   realization) is confined to strict subderivations.
3. **The warrant judgment is non-factive.** No warrant-level justification operator
   (`justified(term, prop)` is removed from v0.1); LP's factivity axiom `t:F → F` may be
   recognized only inside strict subderivations, and the grammar keeps LP proof polynomials and
   warrant terms in separate syntactic categories so a defeasible warrant can never appear under
   `t : F`.
4. **Attacks are positional.** `rebut w u` targets the root conclusion; `undercut w u@π` targets
   the rule occurrence at position `π`; `undermine w u@π` targets the leaf occurrence at `π`.
   Rebut and undermine type-check against a policy-declared contrary relation, not full classical
   negation.
5. **Dropped from the warrant level:** LP sum (`+`), hypothesis variables, and the internalized
   justification operator. Multiple independent supports for a claim are multiple warrant terms
   (separate AF nodes), never one summed term.

## Why (evidence)

1. **Factivity is wrong for warrants.** LP A1 (`t:F → F`) says justified implies true — correct
   for mathematical proof, exactly what LARA's honesty story denies for empirical warrants. If an
   axiom-schema recognizer admits A1 instances and a defeasible conclusion ever enters the
   modality, the kernel derives claim truth from warrant existence. The non-factive justification
   logics (J/J4, logics of justified *belief*) are the right family for the warrant judgment;
   factivity is sound only where the premises are themselves strict.
2. **Sum destroys defeat granularity.** `s + t` merges alternative supports into one term; the
   defeat semantics needs them as separate AF nodes so an undercut can kill one while the other
   survives (already required by `spec.md` §4). Multiple `arg` declarations play sum's role with
   the correct granularity.
3. **Accountability by construction.** The former judgment component `L` and the intended
   accountability theorem ("every leaf used is declared and reported") collapse into a structural
   fact: the dependency set of a checked term is exactly the set of leaf constants occurring in
   it. A theorem about a bookkeeping side-channel becomes an inversion lemma on syntax.
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

The open question "does the LP fragment earn its keep?" (comparison note §9) no longer needs a
corpus answer to justify the design: strict rules are a mode, and the Phase A question becomes
"which rule-library entries are strict vs. defeasible, and which critical-question sets cover the
sampled claim shapes" — which Phase A was measuring anyway. The pitch reframes from "a language
backed by justification logic" to: *a warrant-term calculus in the justification-logic tradition —
terms give syntactic accountability and positional defeat; argumentation gives the non-monotonic
semantics; the checker gives policy-relative validity.*

## Flip criteria

- **Reintroduce an internalized justification operator** if Phase A shows meta-level claims
  ("the paper argues that…", claims about other arguments) are a material fraction of the corpus.
- **Promote the strict LP fragment** (dedicated surface syntax, realization results in the paper
  body) if Phase A shows strict modal-deductive chaining is common rather than rare.
- **Revisit belief-revision-style undermining** if the typed contrary relation proves too weak to
  express the undermining attacks annotators actually find.
