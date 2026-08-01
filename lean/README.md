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
| **3** (dependency accountability) | `Lara/Support.lean`, `Lara/Strict.lean` | ✅ **mechanized** — `leaves_declared` proves the source-leaf half; the certificate half is closed by `Backend.uses` under obligation 4's three laws, each stated over the explicit full consulted context `Δ ++ T` for **one fixed backend core per registered identity**, where a digest resolves only to theory *data* (`RegisteredBackend.resolveTheory`), so digest resolution cannot introduce behavior and hidden theory consultation through the digest mechanism is impossible (`replay_theory_covers`/`certOkBOf_theory_covers`) — coverage (`uses_covers`: replay consults no premise or theory entry outside the report), validity (`uses_valid`: reported slots stay within the consulted context), semantic accounting (`uses_account`: the conclusion follows from just the reported entries; ND instances discharged by `infer_agree`/`fv_in_range`/`nd_relevance`) — and the support-level `certDeps` layer over the typed premise/theory `CertDep` report (nothing filtered): `cert_steps_accounted`, the collection identity `mem_certDeps_step`/`certStep_deps_subset`, `certDeps_resolved` (premise entries resolve to the corresponding premise subterm of their own reporting node, up to `≡`), and `certDeps_theory_valid` (theory entries name genuine entries of the digest-resolved data). |
| **1** (checking decidability) | `Lara/Check/` | ✅ **checker portion mechanized** — the legacy `inferSupport`, `checkAttack`, and `checkProgram` behavior remains generic and unchanged. The public `checkUnit` path additionally constructs `Unit.CheckedUnit` in the fixed order rule-ID duplicates → R12 → argument duplicates → support → typed attacks → missing conflict. |
| **7** (Path-B consistency; C09) | `Lara/Policy.lean`, `Lara/Unit.lean`, `Lara/Check/Unit.lean`, `Lara/Consistency.lean` | ✅ **mechanized for the Lean reference PL; issue #18 closes this scope** — `checkUnit` canonically constructs the accepted-program abstraction with unique rule IDs, Path B enforced before program checking, exact attack completeness, and retained checker nodes. `claimSupportFor` exactly aggregates complete checked nodes and `contrary_claims_not_both_justified` applies only to computed `completeClaimFor` claims. Ordered self-pairs cover self-conflict. |
| **9** (backend replacement) | `Lara/Erase.lean`, `Lara/EraseTransport.lean` | ✅ **mechanized (Model A: uniform injective relabel)** — `backend_replacement`: two `CheckedProgram`s related by a uniform assurance relabel `mapAssur f` (`f` injective) compile to a definitionally equal AF (`checkedAF_relabel`), so every grounded label and claim status agrees. Nodes are list positions, so the bijection is the identity; `containsB_mapAssur`/`mapAssur_injective` carry edge-relation payload-independence. The doc's non-injective erase-to-`certified` marker is *not* an isomorphism (it can merge subterms and add closure edges); injectivity-on-used-certs is the faithful backend-swap condition. **Non-vacuous by construction** (`EraseTransport.lean`): `hasSupport_mapAssur`/`hasAttack_mapAssur`/`mapCertProg` transport well-checkedness under any acceptance-preserving relabel (`hpres`), so `backend_replacement_transport` exhibits the second program rather than assuming it. |
| **12** (presentation-codec round trip) | `Lara/Presentation.lean` | ✅ **mechanized for the full frozen presentation AST** — structured encode/decode round trips every `Program`/`Policy` field. This anchors AST shape, not the concrete Haskell `.lara` parser; the latter is covered separately by QuickCheck conformance. |

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

The latest result-9 verification snapshot is: `lake build` completes 48 jobs;
AxCheck emits 516 declaration reports with no `sorryAx` and no axiom outside
`propext`, `Classical.choice`, and `Quot.sound`. The transport declarations use
only `propext` and `Quot.sound`. Exact commands and per-result evidence are
recorded in `../ara/evidence/status/mechanization_status.md`.

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

The headline Lean obligations are complete through result 9, including
constructive well-checkedness transport, and result 12's presentation-codec
round trip. Result 3's last gap — backend certificate dependencies —
is closed by the `Backend.uses` report laws (coverage, validity, semantic
accounting, stated for one fixed core per registered identity with digests
resolving only to theory data) and the support-level `certDeps` layer over
the typed premise/theory `CertDep` report (#46), so dependency
accountability is mechanized in both halves. The abstract contract proves
conservative coverage — replay consults nothing outside the report;
exactness of the report is proved for the ND adapter specifically
(result 10, exactness half).

The project-level next milestone is M5. Its immediate cross-layer prerequisites
are verdict-carried replay identity (#36) and duplicate-report groups with R9
checking (#38); these are language/reporting additions, not missing pieces of
the existing Lean checker proofs. The shared serialized first-order core AST
remains the Haskell↔Lean differential-testing anchor.
