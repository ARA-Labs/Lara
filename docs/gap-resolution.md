# Resolving the two `(Inst)`-checkability gaps: strict witnesses and claim targets

_Status: settled for v0.1, backed by targeted research. Recorded 2026-07-20. Extends
`term-calculus-decision.md`. All recommendations here are applied to `spec.md`._

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
an entailment procedure in the TCB. Add it later as sugar: an explicit `entails` warrant step whose
*own* conclusion is discharged against `c.formal` by identity, so the trusted core never grows.

---

## Gap 1 — the strict-rule witness and where factivity lives

### The Pandžić finding (it overturns an assumption)

Pandžić's default justification logic is the closest term-based defeasible system, but it is **not
non-factive**. He keeps factivity (axiom A1, `t:F → F`) globally — the whole logic is JT, the
explicit analogue of modal T — and confines *defeasibility* by two other devices: the inference
license ("warrant") is kept *out of the evidence base* so it can be attacked without inconsistency,
and retraction happens at the *extension* layer. His `t:F` is therefore
"factive-within-an-accepted-extension," never globally non-factive. LARA wants a genuinely
non-factive warrant judgment, so it must depart from him on exactly this axis.

The standard justification-logic knob he declined to use is the fix: the **JT-vs-J4 split**.
Factivity is exactly one axiom (A1), present in JT/LP and absent in J/J4 (the belief logics, explicit
counterparts of modal K/K4). Confine A1 to a *strict sort*; the *defeasible sort* omits it and is
non-factive by construction. Confinement is enforced through the **constant specification**: only
strict constants may justify A1 instances.

### How this maps onto LARA (the two categories already are the firewall)

LARA's `term-calculus-decision.md` already split the syntax into two categories: warrant terms (which
conclude atoms via rule instances) and LP proof terms (`t : F`). That split *is* Pandžić's
recommended JT/J4 firewall, realized structurally rather than by a shared sort discipline:

- **Defeasible sort = the warrant-term calculus.** Already non-factive: a term concludes an atom,
  and `justified` status ≠ truth. There is no `t:F → F` construct at this level to remove.
- **Strict sort = the embedded LP fragment.** Factive and sound (JT). Its `ConstantSpec` may contain
  A1 instances; the fixed axiom-schema recognizer (the planned `ConstantSpec` fix) is the exact lever
  that admits A1 for strict constants and nothing else.
- **One-directional coercion strict → defeasible.** A checked strict witness lifts to a warrant;
  a warrant never becomes a free LP truth. This is the only bridge, and it goes one way.

### The witness interface

A strict rule `r : P₁,…,Pₙ ⇒ C` instantiated at `theta` has, as its optional witness, an LP
derivation `d` such that

```text
Sigma_LP ; { x₁ : P₁theta, …, xₙ : Pₙtheta }  ⊢  d ⇒ t : Ctheta
```

— a **conditional deductive skeleton**: given justifications for the premises (LP hypotheses `xᵢ`,
one per premise term `wᵢ`), `d` builds a justification for the conclusion. The witness may use
logical-axiom constants (A0–A4, including A1) freely, because it proves a *logical entailment* among
propositions, which is legitimately factive. No bare `F` ever escapes: the interface consumes premise
warrants as hypotheses and emits `t : Ctheta`, which the strict rule reads as "`Ctheta` is warranted
given its premises." Warrant-layer defeat still propagates through sub-argument closure regardless of
what `d` does internally.

### The witness is optional — and that makes LP's role measurable

Distinguish two ways a rule can be strict:

- **Strict, unwitnessed** — an indefeasible *trusted policy schema* (an ASPIC+ strict rule; a
  declared domain law). In the policy TCB.
- **Strict, witnessed** — the LP derivation discharges the step to logical axioms, so it is
  *kernel-checked* and leaves the policy TCB.

This resolves the standing "does the LP fragment earn its keep?" question (comparison note §9) by
turning it into a *gradient*: the **trust-reduction number** (research-proposal §5) is literally the
fraction of load-bearing strict steps that carry a checked witness. LP earns its keep exactly to the
extent witnesses are present; where they are absent, the rule is honestly marked trusted.

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
    strict chain) participates in a declared contrary pair.** Then every conflict is rebuttable at a
    defeasible step, strict closure introduces no new conflict, and direct = indirect consistency
    hold by construction. This keeps the contrary relation arbitrary and adds no negation; the cost
    is a real expressiveness limit (strict chains may only target uncontested claims).

  **Decision: Path B for v0.1** (settled — a compile-time well-formedness check), with Path A
  recorded as the flip criterion if the corpus shows strict rules genuinely feeding contested claims.
  Applied to `spec.md` §8.1 and §9.

### One caveat carried from Pandžić

Do not adopt LP sum/accrual `t:F → (t+u):F` at the warrant level (it is already dropped in
`term-calculus-decision.md`): Pandžić notes A2 monotonicity fails once a defeater `u` co-occurs. Sum
stays inside LP witnesses, where it is sound.

---

## Two smaller mismatches (resolved, applied to spec)

1. **Warrant `prop` is atomic.** `->` and `⊥` are the LP fragment's formula formers only. At the
   warrant level, conflict comes from `contrary` (not negation-to-falsum) and implication is reified
   as a named rule (not a proposition), so neither is needed. `prop ::= atom`.
2. **`undermine` attacks a leaf's proposition only, not its "admissibility."** Admissibility is
   entirely a §4.3 pre-evaluation policy decision (admit/quarantine/reject) and "never creates an
   attack"; there is no atom to conclude for an admissibility attack, and inventing one would revive
   provenance-as-attack. Drop the "or admissibility" branch.

---

## Net effect on `(Inst)` checkability

With Gap 2 (identity-checkable claim targets), Gap 1 (the conditional-skeleton witness with
factivity confined by the two categories + constant spec), and the ASPIC+ guardrails, `(Inst)` and
`supports` are fully checkable and the trusted base is: the fixed axiom-schema recognizer, the policy
validator, the term/attack checker, the normalization function, and the grounded engine — with the
strict-witness discharge as the mechanism that shrinks the policy TCB rule by rule.

## Sources

- Pandžić 2022, *A logic of defeasible argumentation*, Argument & Computation 13(1), doi:10.3233/AAC-200536.
- Pandžić 2022, *Structured argumentation dynamics: undermining attacks in default justification logic*, Ann. Math. Artif. Intell. 90(2–3):297–337, doi:10.1007/s10472-021-09765-z.
- Modgil & Prakken 2014, *The ASPIC+ framework: a tutorial*, Argument & Computation 5(1), doi:10.1080/19462166.2013.869766.
- Caminada & Amgoud 2007, *On the evaluation of argumentation formalisms*, Artificial Intelligence 171(5–6):286–310, doi:10.1016/j.artint.2007.02.003.
- Clark, Ciccarese, Goble 2014, *Micropublications*, J. Biomedical Semantics 5:28, doi:10.1186/2041-1480-5-28.
- Zhang et al. 2026, *Beyond Compilation*, arXiv:2606.31002.
