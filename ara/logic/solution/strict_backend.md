# The backend-parametric strict-certificate interface

_Source of truth: `docs/spec.md` §5 and `docs/strict-backend-decision.md`. This is the one seam for
strict deductive steps. It replaces the earlier LP-specific strict fragment (the pivot recorded in
trace N05); LP is now an optional adapter._

## 1. The seam

A strict rule instance may carry an opaque certificate `κ` checked by a registered backend `β`. The
claim-support calculus knows neither the backend's proof-term grammar nor its axioms. Where the old
design wrote an LP subderivation `Σ_LP ; {xᵢ : Pᵢθ} ⊢ d ⇒ t : Cθ`, the new one writes

```
strictCheck(β, T, [P₁θ, …, Pₙθ], Cθ, κ) = accept
```

with `β` a fixed backend id+version, `T` a digest-addressed theory, `κ` opaque. A successful check
discharges the *deductive validity* of the step conditional on its premise conclusions and the declared
theory; it does NOT establish that the premises are true, does not expose a backend formula/proof term
to the source language, and does not change attack or status semantics (C03).

Two ways a rule is strict: **certified** (a registered backend discharges the instance) or
**trusted-policy** (an indefeasible domain law, `assurance = trusted`). Reports distinguish
`certified(β, theory-digest)` from `trusted-policy`; only the first receives the soundness guarantee.

## 2. The backend interface and six obligations

A registered backend supplies `encode_β : prop → Form_β`, `check_β : Theory_β → List Form_β → Form_β →
Cert_β → accept | reject`, `uses_β : Cert_β → Set Dependency`, and a semantics `models_β` (written
`T ; Δ ⊨_β φ`). It must discharge:

1. **Decidable replay** — `check_β` total, deterministic, terminating on finite input.
2. **Normalization fidelity** — `p ≡ q iff encode_β(p) = encode_β(q)` (forward preserves source
   identity; reverse stops an encoder collapsing distinct propositions).
3. **Certificate soundness** — `check_β(T, Δ, φ, κ) = accept ⟹ T ; Δ ⊨_β φ`.
4. **Dependency accountability** — every free premise/theory entry consulted by `κ` is returned by
   `uses_β(κ)`, and every returned dependency names a declared slot or a `T` entry.
5. **Closed registration** — implementation, decoder, encoding, and admissible theory format are fixed
   by `(β, version)`; artifacts cannot upload code, axioms, or a new encoding.
6. **Structural consequence laws** — `models_β` has reflexivity, cut/transitivity, and weakening. A
   non-monotonic reasoner is not a strict backend; it belongs in the support/attack layer.

The backend receives only normalized proposition encodings; it never sees support terms, argument ids,
attacks, provenance, or statuses. Its return is only accept/reject + dependencies + diagnostics. No
backend proof term can be reinserted as a source proposition — **the factivity firewall** (C03,
Theorem 3).

## 3. Required reference adapter: intuitionistic natural deduction

```
φ ::= a | false | φ → φ
e ::= hyp i | lam φ e | app e e | abort φ e
```

with the standard Hyp / Imp-I / Imp-E / False-E rules; certificates use de Bruijn indices (binding and
dependency checking are syntactic). Encodes `encode_ND(p) = atom(canonicalSerialize(nf(p)))` with an
injective structural serialization, so backend equality coincides with source `≡` (discharges
obligation 2). Soundness (Theorem 4) is by induction on the typing derivation for the Boolean
semantics `T ; Δ ⊨_ND φ`; it is sound but **not complete** — completeness is not required because LARA
checks submitted certificates rather than searching (C05). Dependency exactness (Lemma 5): the free de
Bruijn indices are exactly the premise/theory slots the derivation depends on.

This adapter is intentionally modest: it certifies only propositional consequences visible in its
encoding. A non-logical domain law stays a reported theory dependency or a trusted policy rule; the
checker does not relabel it a tautology.

## 4. Optional LP and domain adapters

LP may be registered as an optional backend keeping `t:F`, application, sum, positive introspection,
reflection, constant specification, and S4 realization *internal to that adapter*. Other adapters may
certify classical propositional reasoning, arithmetic, temporal properties, or code behavior (each with
its own semantics and soundness theorem). The current Haskell `ConstantSpec` accepts arbitrary
`(constant, formula)` pairs, so it is **not** yet a conforming adapter — eligibility requires fixed LP
schema recognition and a soundness/conformance argument.

## 5. The two backend-parametric results

- **Strict-step soundness** (Theorem 1) — an accepted certified instance satisfies `T ; [encode_β(Pᵢθ)]
  ⊨_β encode_β(Cθ)` by obligation 3; excludes trusted-policy instances.
- **Backend replacement** (Theorem 2, C04) — source-identical programs whose backends accept the same
  strict instances compile (after `eraseCert`) to isomorphic AFs and yield equal claim statuses. This
  proves backend internals are not part of claim-status semantics when acceptance profiles match — the
  formal reason no single logic (LP, S4, …) is foundational. Backend identity, theory, dependencies,
  and certificate size stay visible for audit.

Whether a particular backend is *useful* cannot be proved from the calculus; it is measured by corpus
coverage, checking cost, and the fraction of strict steps moved out of the policy TCB (the
strict-certification rate). This is why the corpus study (M0) gates which optional adapters ship.
