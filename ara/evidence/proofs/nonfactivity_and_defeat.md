# Theorem 3 (source non-factivity) + Proposition 8 (monotonic consequence cannot represent defeat)

- **Source**: docs/strict-backend-decision.md §5 Theorem 3, §6 Proposition 8. Theorem 3 is
  **mechanized** in Lean (`lean/Lara/Strict.lean`: `no_truth_projection` / `nd_nonfactive_witness` /
  `nd_relative_not_absolute`; spec §9 result 2, `propext` only, `sorry`-free); Proposition 8 is
  paper-proved (grounds the design behind result 5/§8).
- **Grounds**: C03 (non-factivity), C06 (non-monotonic defeat).
- **Assumptions used**: the source judgment forms (support / attack / status only, no truth judgment);
  grounded semantics; framework extension.

## Theorem 3: source non-factivity

**Statement.** No source derivation can use backend acceptance to derive a truth judgment for a
supported proposition.

**Proof.** The source calculus has judgments only of the form `Σ; Π; Γ; R ⊢ w : p ▷ O`, attack
judgments, and status judgments. It has no judgment `⊢ p true` and no rule eliminating support into
such a judgment. `Strict-Cert` returns another support judgment and exports no backend formula
constructor. By inversion on the final source rule, backend acceptance can therefore produce only
support. QED.

This is a *syntactic confinement* result — it does not claim a selected backend is non-factive
internally (an LP or theorem-prover adapter may be fully factive). It is the factivity firewall: even a
factive backend cannot eliminate source support into truth (C03).

## Proposition 8: monotonic consequence cannot represent defeat-driven retraction

**Statement.** No monotonic consequence relation can, by itself, represent LARA claim acceptance under
framework extension.

**Proof.** Let input `X` contain a complete unattacked support for `p`, so `p` is `justified`. Extend
it to `Y` by adding a checked, undefeated attacker, so `X ⊆ Y` but `p` is no longer `justified`. If
acceptance were represented by a monotonic consequence relation, `X ⊢ p` and `X ⊆ Y` would imply
`Y ⊢ p`, a contradiction. QED.

Ordinary S4, LP, J, and J4 are monotonic and therefore cannot be the whole status semantics (their
strict consequences can still be used *behind* the backend interface). This is why LARA's status
semantics is argumentation-framework defeat, not a proof-theoretic consequence relation — and it is the
capability a purely monotonic (e.g. Lean-kernel) approach cannot express (C06).

## The reconciliation (no contradiction with determinism)

Proposition 8 is non-monotonicity at the **consequence level, across extensions** of the input
framework. For a **fixed** framework, Dung's characteristic function is monotone over a finite-height
lattice, so the grounded least fixed point is unique and reached by bounded iteration (spec §8; C07).
"The internal transfer operator is monotone over a finite-height lattice; it is the external map from
an extensible argument framework to accepted claims that is non-monotonic." Both hold simultaneously.

## Why it matters (the differentiator)

This pair is the formal backbone of LARA's headline capability: a recorded dead end that constructs a
typed attack can flip a claim to `defeated` (worked example E3, docs/worked-examples-plan.md §3) — a
localizing, retractable status a holistic reviewer (`rigor-reviewer`) and a monotonic attestation
(`rit`, EG-VAR) cannot produce.
