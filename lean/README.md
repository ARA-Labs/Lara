# LARA mechanized reference semantics (Lean 4)

The machine-checked companion to the Haskell checker (`../src/`) and the spec
(`../docs/spec.md` §9). Prover: **Lean 4** (v4.32.0; toolchain pinned in
`lean-toolchain`). Architecture, prover choice, and per-result plan:
`../docs/mechanization-plan.md`.

## Status

| Spec §9 result | Content | Lean status |
| --- | --- | --- |
| **11** (support adequacy / `nf`/`≡`) | `Lara/Prop.lean` | ✅ **mechanized** — `nf`, `≡`, equivalence laws, decidability, idempotence, no-argument-reordering. No `sorry`; axioms: `propext` only. |
| **10** (ND adapter soundness + dependency exactness) | `Lara/ND.lean` | ✅ **mechanized** — `nd_sound`, `nd_relevance`, `fv_in_range`, `hyp_out_of_range_untypable`, plus the `infer` decision-procedure bridge. No `sorry`; `propext`/`Quot.sound` only. |
| **8** (strict-certificate soundness / Theorem 1) | `Lara/Strict.lean` | ✅ **mechanized** — abstract `Backend`/`StrictJudgment`, `strict_step_sound`, ND instantiation. No `sorry`; `propext` only. |
| **2** (strict-backend isolation / Theorem 3, non-factivity) | `Lara/Strict.lean` | ✅ **mechanized** — `no_truth_projection`, `nd_nonfactive_witness`, `nd_relative_not_absolute` (the factivity firewall). No `sorry`; `propext` only. |
| 1, 3, 4, 5, 7, 9 | — | not started (gated to M1 freeze / compiled AF layer; see mechanization-plan §6) |
| 6 (status preservation) | — | blocked — no direct source semantics yet (`../docs/mechanization-plan.md` §5) |

This is the **low-risk warm-up** (`../docs/mechanization-plan.md` §6): the `nf`/`≡`
carve-out is corpus-independent and already frozen, so it is safe to mechanize
before M1. It mirrors the Haskell `Lara.Prop` (`../src/Lara/Prop.hs`) and the
QuickCheck properties in `../test/PropSpec.hs`.

## Build

```sh
# needs elan / lean / lake on PATH (installed to ~/.elan)
cd lean
lake build
```

## Check the proofs are real

```sh
lake env lean AxCheck.lean   # runs `#print axioms` on every main theorem
```

Every main theorem depends on at most `propext` (standard) and no `sorry`/`admit`.
CI enforces this: the `lean` job fails if any theorem's transitive axiom set
contains `sorryAx` or anything outside the standard trio (`propext`,
`Classical.choice`, `Quot.sound`).

## Modeling notes

- The proposition type is `Atom` (Lean reserves `Prop` for its sort of props).
- A constructor's argument list is a bespoke `Terms` type mutual with `Term`
  (Lean's `deriving DecidableEq` doesn't recurse through `List`, but handles
  mutual inductives — and a mechanized AST wants derived decidable equality).
- The literal canonicalizer is an explicit parameter `canon : String → String`
  with an idempotence hypothesis, not a port of Haskell's `canonNum` string
  surgery: idempotence is the only property the structural metatheory needs
  (spec §3.2), so modeling it abstractly keeps the development axiom-free.

## Next (post-M1)

Add Mathlib as a dependency for result 5 (grounded least-fixpoint: needs
`Finset` / complete-lattice / monotone-map machinery), then the backend
interface + ND adapter (results 8, 10) and backend replacement (result 9). The
shared serialized first-order core AST is the Haskell↔Lean differential-testing
anchor (mechanization-plan §3).
