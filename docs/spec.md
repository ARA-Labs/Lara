# LARA core language specification (Phase 0 — WIP)

_This is the living formal spec of the trusted core. The code in `src/Lara/`
implements a minimal seed of it; both evolve together. **Not yet frozen** —
the Phase-0 deliverable is this document plus 2–3 hand-lowered example claims
that typecheck on paper._

## 1. Scope

LARA is a small language of **warrant certificates**. A LARA certificate states
that a concrete justification term `t` supports a formula `F`, relative to an
explicit constant specification and an explicit set of leaf assumptions. The
trusted compiler/checker validates the certificate; it does not search for one.

The core fragment is propositional boolean **Logic of Proofs (LP)** — the
explicit-proof counterpart of S4. Graded/probabilistic reasoning stays
*outside* this kernel, in the judge and warrant layer, as leaf-atom metadata.

JSON is the intended producer/checker wire format. The syntax below is the
canonical human-readable presentation used in the paper, examples, debugging,
and reports. It is a certificate notation, not a Lean-style proof authoring
language with tactics, notation packages, or an IDE.

## 2. Lexical classes

```
x, y       justification variables / hypothesis names
c, k       proof constants
p, q       formula atoms
E          evidence identifiers
claim      claim identifiers
```

Identifiers are finite strings in the implementation. The presentation syntax
uses conventional mathematical metavariables.

## 3. Core syntax

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

Typing contexts and constant specifications:

```
Γ ::= · | Γ, x : F
Σ ::= · | Σ, c ↦ F
```

`Γ` contains artifact-specific leaf assumptions. `Σ` contains proof constants
pinned to logical axiom instances. The two are intentionally separate: `Σ`
belongs to the fixed logic; `Γ` is where empirical or certified leaves enter.

> Open (decide before Phase 1 locks): which further connectives (∧, ∨, ¬) enter
> the fragment, and whether we need a JT/JD variant for factivity/consistency.
> See `ARA-verification-plan.md` §3 Q1.

## 4. Certificate syntax

The checker consumes explicit derivation trees. In presentation form:

```
d ::= const c F        constant certificate
    | hyp x F          hypothesis certificate
    | app d d          application
    | sumL d t         add a right summand
    | sumR t d         add a left summand
    | check d          positive introspection
```

The implementation constructors are `DConst`, `DHyp`, `DApp`, `DSumL`,
`DSumR`, and `DCheck`.

## 5. Static semantics: local certificate checking

The kernel checks an **explicit derivation** (de Bruijn criterion) rather than
searching. Its main judgment is:

```
Σ; Γ ⊢ d ⇝ t : F
```

Read this as: under constant specification `Σ` and leaf context `Γ`, derivation
tree `d` checks and elaborates to the certified assertion `t : F`. `Judgment`
is sealed in code: only a successful `check` produces one.

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

## 6. Dynamic semantics: warrant evaluation

The core checker only establishes local validity. A full LARA program also
contains a warrant graph:

```
W ::= (N, Attack)
n ∈ N ::= checked(t : F, metadata)
Attack ⊆ N × N
```

Each checked node must come from a successful core judgment. Attack edges are
constructed from ARA dead ends, conflicting evidence, provenance challenges, or
explicit undercut/rebut/undermine relations. The argumentation layer applies
grounded labelling:

```
label(n) ∈ {in, out, undec}
```

The claim-level status is then:

```
justified  if a checked support node for the claim is labelled in
defeated   if a checked support node exists but all relevant support is out
contested  if support is undec because of mutual defeat
gap        if no checked support node exists
```

This is the non-monotonic layer. It never manufactures local proofs; it only
accepts, rejects, or suspends already checked nodes.

## 7. Leaf-atom interface (TODO — Phase 0 deliverable)

Schema for the `supported(E, c)` atoms the LLM judge emits, with the metadata
envelope `(graded_value, threshold, provenance, refs)`. Certified leaves
(`mc-certified`, from a model checker) are a strictly stronger variant. To be
specified here before the elaborator is built.

Suggested presentation form:

```
leaf x : supported(E, claim)
  value      = 0.87
  threshold  = 0.75
  provenance = user | ai-executed | mc-certified
  refs       = [...]
```

The logical formula `supported(E, claim)` enters `Γ`; the metadata remains
outside the kernel and is consumed by reporting, fragility analysis, and defeat
construction.

## 8. ARA → core mapping (TODO — Phase 0 deliverable)

claim → target formula; experiment/evidence → leaf atoms; solution/algorithm
steps → composite justification term; `trace/` dead-ends + conflicting evidence
→ defeaters; provenance tags → trust labels.

## 9. Worked examples (TODO — Phase 0 deliverable)

2–3 real claims from a corpus paper, hand-lowered and shown to typecheck.
`app/Main.hs` currently carries one toy example (`(c0 · x) : Q`).
