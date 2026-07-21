# Theorem 4 + Lemma 5: natural-deduction adapter soundness and dependency exactness

- **Source**: docs/strict-backend-decision.md §5, Theorem 4 and Lemma 5; §4.1 (the adapter). Target:
  Lean 4 mechanization (spec §9 result 10); currently paper-proved, not machine-checked.
- **Grounds**: C03, C05.
- **Assumptions used**: the ND typing rules (Hyp / Imp-I / Imp-E / False-E); the Boolean semantics
  `T ; Δ ⊨_ND φ` (every valuation satisfying `T` and `Δ` satisfies `φ`).

## Theorem 4 (soundness)

**Statement.** If `Γ ⊢ e : φ`, then every Boolean valuation satisfying all formulas in `Γ` satisfies `φ`.

**Proof.** By induction on the typing derivation.
- `Hyp`: `φ ∈ Γ`, so it is satisfied by assumption.
- `Imp-I`: assume the valuation satisfies the antecedent; it then satisfies the extended context; the
  induction hypothesis gives the consequent, hence it satisfies the implication.
- `Imp-E`: the induction hypotheses give both `φ → ψ` and `φ`; Boolean implication yields `ψ`.
- `False-E`: no valuation satisfies `false`, so the conclusion follows vacuously.

Thus accepted natural-deduction certificates satisfy backend obligation 3 (certificate soundness). QED.

**Note on completeness.** Intuitionistic natural deduction is sound but *not complete* for this Boolean
semantics; completeness is not required because LARA checks *submitted* certificates rather than
searching for every valid proof (C05). This is a deliberate design choice, not a gap.

## Lemma 5 (dependency exactness)

**Statement.** For a well-typed certificate `e`, the free de Bruijn indices in `e` are exactly the
premise/theory slots on which its derivation depends.

**Proof sketch.** Structural induction on `e`: `hyp i` contributes `{i}`; `app` takes the union;
`abort` preserves the child's set; `lam` removes the newly bound index and shifts the remaining free
indices. The checker rejects every out-of-range free index. QED.

This discharges backend obligation 4 (dependency accountability) exactly: `uses_ND(e)` = the free-index
set, with no hidden free strict assumption.

## Encoding fidelity

`encode_ND(p) = atom(canonicalSerialize(nf(p)))` with a fixed, structural, injective serialization on
normalized source ASTs. Hence `p ≡ q iff encode_ND(p) = encode_ND(q)`, discharging obligation 2
(normalization fidelity) and tying the adapter to the implemented `Lara.Prop` `nf`/`≡` (C01).

## Mechanization plan (docs/mechanization-plan.md §4)

The ND adapter is an `instance : Backend` whose `sound` field is discharged by this induction; free-index
collection gives `uses`. "Must"-tier (result 10). The `nf`/`≡` it depends on is already
implemented+tested, so it can be ported early as a warm-up.
