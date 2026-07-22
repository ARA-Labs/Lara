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
| **6** (status preservation: direct vs compiled) | `Lara/Grounded.lean` | ◐ **partially mechanized (abstract AF layer)** — declarative grounded (`DirectIn`/`DirectOut`) ≡ executable grounded labelling *over any AF*: `directIn_iff`, `labelC_inn/out/undec_iff`, `status_preservation`. Genuine core (N16's "no independent semantics" gap closed), but `compile`/subargument closure are only defined + characterized (`compile_attack_iff`), **not exercised** — the source-vs-compiled preservation is M1 work. N17: `statusC_gap_iff` mechanizes "gap iff empty support"; the hole diagnostic is a defined convention. No `sorry`; trio axioms. |
| **5** (grounded termination + determinism, core) | `Lara/Grounded.lean` | ✅ **mechanized (core)** — `grounded_stable`/`grounded_fixpoint`: bounded characteristic-operator iteration reaches the least fixed point within `\|Args\|` steps. Full compiled-AF instance is M1-gated. |
| 1, 3, 4, 9 | — | not started (gated to M1 freeze / compiled AF layer; see mechanization-plan §6) |

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

The grounded least-fixpoint (result 5 core) is done **in core Lean 4** —
`Lara/Grounded.lean` builds the finite fixpoint by hand (bounded iteration +
a deficit-measure stabilization argument), so no Mathlib dependency was needed.
Remaining work: the concrete compiled-AF construction over corpus support terms
(results 4 / full 5) and backend replacement (result 9), which may still pull in
Mathlib's `Finset` / order machinery once the support-term layer lands. The
shared serialized first-order core AST is the Haskell↔Lean differential-testing
anchor (mechanization-plan §3).
