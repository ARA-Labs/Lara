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
| **8** (strict-certificate soundness / Theorem 1) | `Lara/Strict.lean` | ✅ **mechanized** — abstract `Backend`/`StrictJudgment`, `strict_step_sound`, ND instantiation. No `sorry`; `strict_step_sound` needs no axioms, while `nd_strict_step_sound` uses the standard trio (`propext`, `Classical.choice`, `Quot.sound`). |
| **2** (strict-backend isolation / Theorem 3, non-factivity) | `Lara/Strict.lean` | ✅ **mechanized** — `no_truth_projection`, `nd_nonfactive_witness`, `nd_relative_not_absolute` (the factivity firewall). No `sorry`; AxCheck reports the standard trio (`propext`, `Classical.choice`, `Quot.sound`) for all three results. |
| **6** (status preservation: direct vs compiled) | `Lara/Grounded.lean`, `Lara/Compile.lean` | ◐ **source-vs-compiled half complete: the `Faithful` oracle is constructively supplied by `Compile.edgeB_faithful`** — the checker-built closure decider `edgeB` decides `Edge` exactly, so the specialized wrappers state agreement over a checked program with no oracle hypothesis. Issue #17 closed; issue #18 separately closed the attack-completeness premise needed by result 7. |
| **5** (grounded termination + determinism) | `Lara/Grounded.lean`, `Lara/Compile.lean` | ✅ **mechanized** — bounded characteristic-operator iteration reaches the least fixed point within `\|Args\|` steps; `toAF` instantiates the result for checked programs. |
| **4** (compilation soundness) | `Lara/Compile.lean`, `Lara/Examples.lean` | ✅ **mechanized (relational compile layer)** — only complete checked terms become nodes; only typed declared attacks produce edges; direct and strict-superset closure behavior are proved concretely. |
| **3** (dependency accountability) | `Lara/Support.lean` | ◐ **partially mechanized** — `leaves_declared` proves the source-leaf half; backend `certDeps` accountability separately awaits a `Backend.uses` field. |
| **1** (checking decidability) | `Lara/Check/` | ✅ **checker portion mechanized** — the legacy `inferSupport`, `checkAttack`, and `checkProgram` behavior remains generic and unchanged. The public `checkUnit` path additionally constructs `Unit.CheckedUnit` in the fixed order rule-ID duplicates → R12 → argument duplicates → support → typed attacks → missing conflict. |
| **7** (Path-B consistency; C09) | `Lara/Policy.lean`, `Lara/Unit.lean`, `Lara/Check/Unit.lean`, `Lara/Consistency.lean` | ✅ **mechanized for the Lean reference PL; issue #18 closes this scope** — `checkUnit` canonically constructs the accepted-program abstraction with unique rule IDs, Path B enforced before program checking, exact attack completeness, and retained checker nodes. `claimSupportFor` exactly aggregates complete checked nodes and `contrary_claims_not_both_justified` applies only to computed `completeClaimFor` claims. Ordered self-pairs cover self-conflict. |
| **9** (backend replacement) | `Lara/Erase.lean`, `Lara/EraseTransport.lean` | ✅ **mechanized (Model A: uniform injective relabel)** — `backend_replacement`: two `CheckedProgram`s related by a uniform assurance relabel `mapAssur f` (`f` injective) compile to a definitionally equal AF (`checkedAF_relabel`), so every grounded label and claim status agrees. Nodes are list positions, so the bijection is the identity; `containsB_mapAssur`/`mapAssur_injective` carry edge-relation payload-independence. The doc's non-injective erase-to-`certified` marker is *not* an isomorphism (it can merge subterms and add closure edges); injectivity-on-used-certs is the faithful backend-swap condition. **Non-vacuous by construction** (`EraseTransport.lean`): `hasSupport_mapAssur`/`hasAttack_mapAssur`/`mapCertProg` transport well-checkedness under any acceptance-preserving relabel (`hpres`), so `backend_replacement_transport` exhibits the second program rather than assuming it. |

`Unit.CheckedUnit` is the accepted-program abstraction. `checkUnit` is its
canonical executable constructor; manual proof-level construction remains
possible only by supplying every invariant. The retained nodes come directly
from the support-checker cache and are reused by typed-attack checking,
attack-completeness checking, and complete-claim aggregation—support is not
re-inferred. `CheckedProgram` and legacy `checkProgram` remain the unchanged
generic attack-soundness boundary.

The result-7/C09 scope is deliberately narrow. It proves that directionally
contrary claims computed by `completeClaimFor` from all retained, canonically
matching complete nodes cannot both be justified. It does not implement or
claim Path A, the production Haskell checker, NL-to-structure validation, full
`holes(P,p)`, or `incompleteAlternative` computation. `Lara.Grounded` is a
transparent proof-oriented reference evaluator, not the deferred optimized
production evaluator.

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

The issue-#18 verification snapshot is: 70 traceability IDs and six author
flows pass; `lake build` completes 25 jobs; AxCheck emits 430 theorem reports
with no `sorryAx` and only `propext`, `Classical.choice`, and `Quot.sound`; and
the multiline CI axiom parser is repaired and negative-tested. `cabal build`
and `cabal test` also pass (one suite, 30 QuickCheck groups, 100 cases each),
but those Haskell commands are regression-compatibility evidence only—not new
Lean accepted-unit-flow evidence.

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
The checker-built `Faithful` edge decider (issue #17, closing result 6's
source-vs-compiled half) is now done — `Compile.edgeB`/`edgeB_faithful` discharge
the oracle constructively. Issue #18 now closes attack completeness and result 7
for the Lean reference PL. Remaining work includes backend dependency
accountability (the remaining half of result 3), the certificate-erased argument
identity needed to state backend replacement (result 9), the production Haskell
checker, and the deferred full hole/incomplete-alternative computation. The shared
serialized first-order core AST remains the Haskell↔Lean differential-testing
anchor (mechanization-plan §3).
