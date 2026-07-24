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
| **6** (status preservation: direct vs compiled) | `Lara/Grounded.lean`, `Lara/Compile.lean` | ◐ **mechanized modulo the executable edge decider** — source `SrcIn`/`SrcOut` and four-state `SrcStatus` agree exactly with executable grounded evaluation over `toAF` (`srcIn_iff_grounded`, `srcStatus_iff`) whenever `Faithful` decides the frozen closure relation. `Lara/Examples.lean` supplies a concrete faithful decider that exercises a strict closure edge. The general checker-produced decider remains M2 work. |
| **5** (grounded termination + determinism) | `Lara/Grounded.lean`, `Lara/Compile.lean` | ✅ **mechanized** — bounded characteristic-operator iteration reaches the least fixed point within `\|Args\|` steps; `toAF` instantiates the result for checked programs. |
| **4** (compilation soundness) | `Lara/Compile.lean`, `Lara/Examples.lean` | ✅ **mechanized (relational compile layer)** — only complete checked terms become nodes; only typed declared attacks produce edges; direct and strict-superset closure behavior are proved concretely. |
| **3** (dependency accountability) | `Lara/Support.lean` | ◐ **partially mechanized** — `leaves_declared` proves the source-leaf half; backend `certDeps` accountability awaits the executable backend interface. |
| **1** (checking decidability) | `Lara/Support.lean`, `Lara/Attack.lean` | ◐ **relational metatheory mechanized** — typing uniqueness and inversion properties are proved. Executable support/attack decision procedures require the abstract strict-backend seam to expose decidable replay acceptance (`Backend.check` is currently an arbitrary `Prop`). |
| **7** (Path-B consistency) | `Lara/Policy.lean` | ◐ **validator mechanized** — `StrictReachable`, conservative instance-overlap checking, `aPatMayOverlap_of_instances`, and `wfB_iff` prove the finite `wf(Pi)` check catches canonically equivalent ground instances; `wellFormed_no_strict_contrary_left/right` connect it to `ContraryMatch`, and `firstViolation?` carries the located R12 rule/pair. The status-consistency theorem still needs attack completeness, which `CheckedProgram.typed` does not provide. |
| **9** (backend replacement) | — | **statement-model blocker recorded** — `CheckedProgram` currently identifies nodes only by certificate-bearing `SupportTerm`; it lacks stable argument ids and a certificate-erased skeleton/bijection. Add that representation before stating payload-varying AF isomorphism faithfully. |

The development now covers the frozen M1 relational support, attack, and
compile layers in addition to the earlier `nf`/`≡`, ND, strict-backend, and
grounded-semantics cores. `Lara/Examples.lean` provides closed conformance
fixtures for duplicate-free obligation accounting, all three attack forms,
position traversal, and closure behavior.

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

Every main theorem stays within the standard trio (`propext`,
`Classical.choice`, `Quot.sound`) and uses no `sorry`/`admit`. CI enforces this:
the `lean` job fails if any theorem's transitive axiom set contains `sorryAx` or
anything outside that trio.

## Modeling notes

- The proposition type is `Atom` (Lean reserves `Prop` for its sort of props).
- A constructor's argument list is a bespoke `Terms` type mutual with `Term`
  (Lean's `deriving DecidableEq` doesn't recurse through `List`, but handles
  mutual inductives — and a mechanized AST wants derived decidable equality).
- The literal canonicalizer is an explicit parameter `canon : String → String`
  with an idempotence hypothesis, not a port of Haskell's `canonNum` string
  surgery: idempotence is the only property the structural metatheory needs
  (spec §3.2), so modeling it abstractly keeps the development axiom-free.

## Next

The grounded least-fixpoint (result 5 core) is done **in core Lean 4** —
`Lara/Grounded.lean` builds the finite fixpoint by hand (bounded iteration +
a deficit-measure stabilization argument), so no Mathlib dependency was needed.
Remaining work: strengthen the strict-backend interface with decidable replay
acceptance, then construct executable support/attack checking and its general
`Faithful` edge decider (closing results 1 and 6 constructively); backend dependency
accountability (the remaining half of result 3); the result-7 consistency theorem
after adding attack completeness; and the certificate-erased argument identity
needed to state backend replacement (result 9). The shared serialized first-order
core AST is the Haskell↔Lean differential-testing anchor (mechanization-plan §3).
