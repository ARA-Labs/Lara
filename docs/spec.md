# Core calculus spec (Phase 0 — WIP)

_This is the living formal spec of the trusted core. The code in `src/Lara/`
implements a minimal seed of it; both evolve together. **Not yet frozen** —
the Phase-0 deliverable is this document plus 2–3 hand-lowered example claims
that typecheck on paper._

## 1. Fragment

Propositional boolean **Logic of Proofs (LP)** — the explicit-proof counterpart
of S4. Graded/probabilistic reasoning stays *outside* this kernel (in the LLM
judge, as leaf-atom metadata).

## 2. Grammar

Justification terms (`Lara.Term`):

```
t ::= x            variable (hypothesis)
    | c            constant (pinned to an axiom by the constant specification)
    | s · t        application
    | s + t        sum (monotone choice)
    | !t           proof checker (positive introspection)
```

Formulas (`Lara.Formula`):

```
F ::= p            atom
    | ⊥            falsum
    | F → G        implication
    | t : F        justification assertion ("t justifies F")
```

> Open (decide before Phase 1 locks): which further connectives (∧, ∨, ¬) enter
> the fragment, and whether we need a JT/JD variant for factivity/consistency.
> See `ARA-verification-plan.md` §3 Q1.

## 3. Derivation rules (`Lara.Kernel`)

The kernel checks an **explicit derivation** (de Bruijn criterion) rather than
searching. `Judgment` is sealed: only a successful `check` produces one.

```
              c justifies f in the spec              x : f in the context
(Const) ─────────────────────────────      (Hyp) ─────────────────────────
                  c : f                                    x : f

          s : (A → B)      t : A
(App) ───────────────────────────────
                (s · t) : B

             s : A                                   s : A
(Sum-L) ───────────────────                (Sum-R) ───────────────────
           (s + t) : A                               (t + s) : A

                  t : A
(Check) ─────────────────────────
             (!t) : (t : A)
```

Constant specification: propositional-tautology axioms and factivity instances
(`t : F → F`) are registered as `(constant ↦ formula)` entries. See
`Lara.ConstantSpec`.

## 4. Leaf-atom interface (TODO — Phase 0 deliverable)

Schema for the `supported(E, c)` atoms the LLM judge emits, with the metadata
envelope `(graded_value, threshold, provenance, refs)`. Certified leaves
(`mc-certified`, from a model checker) are a strictly stronger variant. To be
specified here before the elaborator is built.

## 5. ARA → core mapping (TODO — Phase 0 deliverable)

claim → target formula; experiment/evidence → leaf atoms; solution/algorithm
steps → composite justification term; `trace/` dead-ends + conflicting evidence
→ defeaters; provenance tags → trust labels.

## 6. Worked examples (TODO — Phase 0 deliverable)

2–3 real claims from a corpus paper, hand-lowered and shown to typecheck.
`app/Main.hs` currently carries one toy example (`(c0 · x) : Q`).
