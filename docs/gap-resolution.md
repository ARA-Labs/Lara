# Resolving the two `(Inst)`-checkability gaps: strict certificates and claim targets

_Status: settled for v0.1, backed by targeted research. Recorded 2026-07-20; strict-witness portion
amended 2026-07-21 by `strict-backend-decision.md`. Extends
`claim-support-calculus-decision.md`. All current
recommendations are applied to `spec.md`._

Two gaps kept the instantiation rule `(Inst)` from being fully checkable:

- **Gap 1 — the strict-mode witness condition was prose, not a premise.** `spec.md` said a strict
  instance "may carry an LP subderivation as its witness" without saying what the checker verifies,
  where factivity is confined, or whether a witness is required.
- **Gap 2 — claims carried only an NL string, so `supports(p)` had no checkable meaning.** Nothing
  connected an argument's conclusion to the claim it is supposed to support.

Three research threads (Pandžić's default justification logic; ASPIC+ strict rules and the
rationality postulates; the claim-formalization boundary in AIF / micropublications /
autoformalization) settled both. Findings and the resulting design follow.

---

## Gap 2 — claim targets and the `supports` relation

### What the closest systems do

- **AIF** identifies a claim with an information node (I-node); "the argument concludes claim `c`"
  is *positional identity* — the inference node's out-edge lands on the I-node that is `c`. No
  entailment step at query time. (AIF specification, arg-tech.)
- **Micropublications** make the claim a truth-bearing **NL Statement**; a formal rendering is an
  *optional side-car* (`qualifiedBy`), and support is a *declared, defeasible* relation, never a
  proof. (Clark, Ciccarese, Goble 2014.)
- **Autoformalization faithfulness** is the decisive evidence: NL→formal correspondence *cannot be
  proven* and is *audited*. "Beyond Compilation" reports 89.5% compile vs 60.5% faithfulness — a
  29-point gap — and evaluates faithfulness by model-consensus plus human calibration. The
  miniF2F v1→v2 story (>50% of formal statements misaligned with their informal text until manually
  re-aligned) is the cautionary case for keeping the binding explicit and versioned rather than an
  implicit comment.

Two cross-system invariants: the *checkable* object is a formal proposition tied to the argument by
**identity**; the *NL↔formal* link is an **audited annotation that is provably unprovable**, kept
side by side.

### Decision

A claim is a triple, and `supports` is normalized identity:

```text
claim c
  nl      = "Method M improves accuracy on distribution D"   -- primary, human-facing
  formal  = atom                                             -- the checkable target
  binding = { author, rationale, audit-status }              -- UNTRUSTED, audited
```

- **`w supports c`  iff  `concl(w) ≡ c.formal`**, where `≡` is structural identity up to a fixed,
  total normalization (the `nf`/`≡` normal form fixed in `spec.md` §3.2: literal canonicalization
  plus structural recursion over ground atoms — no argument reordering, no binders). No entailment, no
  solver, nothing added to the TCB. This is AIF/Lean positional identity.
- **`c.binding` is not a checker obligation.** The NL↔formal link is the single most load-bearing
  unchecked step (already `spec.md` §11); it is a first-class, versioned, human-signed audit field,
  evaluated on the semantic-faithfulness axis — never proven.

### Forward path (not v0.1)

Policy-declared entailment (`concl(w)` entails `c.formal`) is strictly more expressive but would put
an entailment procedure in the TCB. Add it later as sugar: an explicit `entails` support step whose
*own* conclusion is discharged against `c.formal` by identity, so the trusted core never grows.

---

## Gap 1 — the strict-rule certificate and where factivity lives

### The Pandžić finding

Pandžić's default justification logic is the closest term-based defeasible system, but it is **not
non-factive**. He keeps factivity (axiom A1, `t:F → F`) globally — the whole logic is JT, the
explicit analogue of modal T — and confines *defeasibility* by two other devices: the inference
license ("warrant") is kept *out of the evidence base* so it can be attacked without inconsistency,
and retraction happens at the *extension* layer. His `t:F` is therefore
"factive-within-an-accepted-extension," never globally non-factive. LARA wants a genuinely
non-factive support judgment, so it must depart from him on exactly this axis.

The JT-vs-J4 distinction identifies the problem but no longer defines LARA's mechanism. Factivity is
exactly one axiom (A1), present in JT/LP and absent in J/J4. Rather than choose one justification
logic for every future strict domain, LARA removes the support-level modality and confines every
strict logic behind the backend interface. This also covers non-JL backends such as arithmetic
checkers and model checkers.

### How this maps onto LARA

- **Source claim-support calculus.** Non-factive because its only conclusion is "`w` supports atom
  `p`"; it has no truth judgment and no elimination from support to truth.
- **Strict-certificate backend.** May be factive internally. It receives encoded premise
  conclusions as assumptions and returns acceptance, dependencies, and diagnostics.
- **Opaque one-way result.** Acceptance creates a strict support instance. Backend formulas and
  proof terms cannot enter source propositions, so source support never becomes a backend truth.

The source non-factivity theorem is syntactic: by inversion on the source rules, no rule concludes a
truth judgment because no such judgment exists. This is stronger and more general than recognizing
A1 only for an LP constant specification.

### The certificate interface

A strict rule `r : P₁,…,Pₙ ⇒ C` instantiated at `theta` may carry a backend certificate `kappa`:

```text
check_beta(T,
  [encode_beta(P₁theta), ..., encode_beta(Pₙtheta)],
  encode_beta(Ctheta),
  kappa) = accept
```

Every registered backend proves that acceptance implies

```text
T ; [encode_beta(P₁theta), ..., encode_beta(Pₙtheta)] |=_beta encode_beta(Ctheta).
```

This is still a **conditional deductive skeleton**, but it does not privilege LP. The backend theorem
establishes local consequence; premise truth is not exported or assumed by the source checker.
Support-layer defeat propagates through subargument closure regardless of certificate internals.

### The certificate is optional — and trust reduction is backend-neutral

Distinguish two ways a rule can be strict:

- **Strict, trusted-policy** — an indefeasible trusted policy schema or domain law. It remains in the
  policy TCB and receives no semantic-consequence theorem.
- **Strict, certified** — a registered backend discharges the instance relative to its declared,
  digest-addressed theory.

The trust-reduction measure is the fraction of load-bearing strict steps that carry an accepted
certificate, broken down by backend and theory. Whether LP earns a place is empirical: measure the
steps that require LP-specific `t:F`, `!`, `+`, or realization. Backend replacement proves that this
choice does not alter claim-support status when adapters accept the same instances; it cannot prove which
adapter is useful on the corpus.

### ASPIC+ guardrails (Thread B)

- **Strict rules cannot be undercut or rebutted.** In ASPIC+ only defeasible rules are named, so
  there is nothing to undercut; permitting attacks on strict conclusions breaks the postulates even
  under transposition. `spec.md` §7 must state: `undercut` targets defeasible rule occurrences only;
  `rebut` targets arguments with a defeasible top rule. A conflict "behind" a strict rule must be
  reachable through a defeasible step or it is silently dropped — the single most common way these
  systems violate consistency.
- **Rationality postulates under grounded + arbitrary contrary + no transposition.** Only
  *sub-argument closure* is free (ASPIC+ Theorem 3.18, unconditional). *Direct* and *indirect*
  consistency and *closure under strict rules* fail in general (Caminada–Amgoud Examples 5–6): a
  conflict that surfaces only after a strict rule is invisible to the attack relation.

  Two ways to recover consistency:

  - **Path A** — give the contrary relation enough structure to define transposition (a total,
    involutive contradictory map `−φ` with `−−φ = φ`), and close strict rules under transposition.
    Buys all four postulates under grounded (C–A Theorem 3). Negation lives in the *contrary
    relation*, not the proposition language, so "no classical negation in props" survives.
  - **Path B (recommended for v0.1)** — forbid strict rules from producing contested conclusions: a
    compile-time well-formedness check that **no strict-rule consequent (nor any proposition on a
    strict chain) can overlap either side of a declared contrary pair at the ground-instance
    level.** Then every conflict is rebuttable at a defeasible step, strict closure introduces no
    new conflict, and direct = indirect consistency hold by construction. This keeps the contrary
    relation arbitrary and adds no negation; the cost is a real expressiveness limit (strict chains
    may only target uncontested claims).

  **Decision: Path B for v0.1** (settled — a compile-time well-formedness check), with Path A
  recorded as the flip criterion if the corpus shows strict rules genuinely feeding contested claims.
  Applied to `spec.md` §8.1 and §9.

### One caveat carried from Pandžić

Do not adopt LP sum/accrual `t:F → (t+u):F` at the support level (it is already absent in
`claim-support-calculus-decision.md`): Pandžić notes monotonicity fails once a defeater `u`
co-occurs. Sum may
exist inside an optional LP certificate, where it cannot merge source argument nodes.

---

## Two smaller mismatches (resolved, applied to spec)

1. **Support `prop` is atomic.** `->`, `⊥`, modalities, and domain-specific formula formers belong
   to backend encodings only. At the support level, conflict comes from `contrary` (not
   negation-to-falsum) and implication is reified as a named rule (not a proposition), so none is
   needed. `prop ::= atom`.
2. **`undermine` attacks a leaf's proposition only, not its "admissibility."** Admissibility is
   entirely a §4.3 pre-evaluation policy decision (admit/quarantine/reject) and "never creates an
   attack"; there is no atom to conclude for an admissibility attack, and inventing one would revive
   provenance-as-attack. Drop the "or admissibility" branch.

---

## Net effect on `(Inst)` checkability

With Gap 2 (identity-checkable claim targets), Gap 1 (the backend-parametric conditional certificate
with source-level non-factivity), and the ASPIC+ guardrails, `(Inst)` and `supports` are fully
checkable. The trusted base for a run is the policy validator, term/attack checker, normalization
function, grounded engine, and exactly the selected strict-backend adapters. Certified strict steps
shrink the policy TCB instance by instance; trusted-policy steps remain explicit.

## Sources

- Pandžić 2022, *A logic of defeasible argumentation*, Argument & Computation 13(1), doi:10.3233/AAC-200536.
- Pandžić 2022, *Structured argumentation dynamics: undermining attacks in default justification logic*, Ann. Math. Artif. Intell. 90(2–3):297–337, doi:10.1007/s10472-021-09765-z.
- Modgil & Prakken 2014, *The ASPIC+ framework: a tutorial*, Argument & Computation 5(1), doi:10.1080/19462166.2013.869766.
- Caminada & Amgoud 2007, *On the evaluation of argumentation formalisms*, Artificial Intelligence 171(5–6):286–310, doi:10.1016/j.artint.2007.02.003.
- Clark, Ciccarese, Goble 2014, *Micropublications*, J. Biomedical Semantics 5:28, doi:10.1186/2041-1480-5-28.
- Zhang et al. 2026, *Beyond Compilation*, arXiv:2606.31002.
