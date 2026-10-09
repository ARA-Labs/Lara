# Implementation and mechanization

The production checker is Haskell; Lean supplies the mechanized reference semantics and soundness proofs. Producers and elaborators supply candidate programs that the checker validates. This document defines module responsibilities, proof and example discipline, and the checks required locally and in CI.

## The trust boundary: Haskell core, Python front-end

The Haskell checker implements support typing, registered strict backends, compilation and argumentation semantics. Candidate-producing tools do not establish acceptance. The repository includes both the Haskell `.lara` parser/elaborator and a Python producer; their implementation language does not by itself determine which guarantees they provide.

Python emits claim-support programs, opaque strict-certificate payloads, and leaf atoms; the Haskell checker decides validity, and nothing above the leaves runs Python. The shipped checker-input wire is the `Lara.Wire` S-expression codec. JSON output and producer-side data are not an alternative trusted checker-input codec.

Haskell supplies algebraic data types for the symbolic core and QuickCheck for conformance testing. Lean carries dependent proof obligations outside the production checker. The shipped strict adapters are `nd@1`, `ra@1`, `ord@1` and `insp@1`; experimental LP code is not a conforming shipped adapter.


## Module dependency order

The principal core dependencies are listed below. [The specification](spec.md) defines the contracts these modules implement.

| # | Module | Spec | Depends on |
| --- | --- | --- | --- |
| 1 | `Lara.Prop` (ground atoms plus `nf`/`≡`) | §3, §3.2 | none |
| 2 | `Lara.Strict` and `Lara.Strict.ND` (closed registry, backend contract, reference natural-deduction adapter) | §5 | Prop |
| 3 | `Lara.Policy` (rule schemas, `contrary`, `exception`, admission table, §8.1 strict-reachable validator) | §4, §8.1 | Prop, Strict |
| 4 | `Lara.SupportTerm` (`w` AST, `⊢ w : supports(p) ▷ O`, `leaves(w)`, `certDeps(w)`) | §6, §4.1–§4.3 | Prop, Strict, Policy |
| 5 | `Lara.Attack` (positional `w@π`, rebut/undercut/undermine typing) | §7 | SupportTerm, Policy |
| 6 | `Lara.Compile` (`compile(P) = AF`, subargument closure) | §8 | SupportTerm, Attack |
| 7 | `Lara.Grounded` (least-fixpoint labelling plus four-state aggregation) | §8 | Compile |
| 8 | `Lara.Diagnostics` (located rejection for every ill-formed construct) | §1, §10 | all above |

The policy validator computes strict-reachable patterns and rejects a policy whose `contrary` sides can overlap them at the ground-instance level. `Lara.Syntax` parses and prints presentation syntax; `Lara.Elaborate` lowers it to core units. Producer and elaborator outputs remain subject to checking. See [the base-language theory](theory-core.md) for the distinction between structured presentation proofs and concrete-parser conformance.

Layers added beyond the spine are `Lara.Admission` (the `.lara` source-boundary admission judgment), the `ra@1`, `ord@1`, and `insp@1` strict backends beside `nd@1`, `Lara.Runtime` (the cached-adjacency production evaluator), `Lara.Reporting` (the `holes(P,p)` / `incompleteAlternative` claim diagnostics), `Lara.Mutate` with `Lara.Measure` (the seeded mutation suite and the axis-(c) harness), `Lara.ClaimSupport` with `Lara.BindingAudit` (reporting and the blinded audit pipeline), the multi-artifact map loader, and the cross-language presentation-parity guard (`scripts/check-presentation-parity.sh`).

## Checker acceptance is one fixed pipeline

`Lara.Check.checkUnit` decides whole-unit acceptance in one fixed stage order, mirrored exactly by `lean/Lara/Check/Unit.lean`:

```text
duplicate rule IDs → R2 signature → R12 policy violation
                   → duplicate arguments → support
                   → typed attacks → missing conflict
```

The support stage builds the retained checked-node cache; the typed-attack and missing-conflict stages reuse it, and so does downstream claim aggregation, so no support re-inference occurs. `Lara.Runtime` is the cached-adjacency evaluator whose verdict is byte-identical to the un-cached `Lara.Compile.checkedAF` path, guarded by `RuntimeSpec` including a 120-argument ≤5 s performance guard. `Lara.Wire` is the single S-expression codec that both the `lara check` CLI and the Lean driver print through, so differential testing is byte comparison.

Rejection classes R1–R14 are the frozen located vocabulary (spec §10.1). `checkUnit` decides R1, R2, R3, R4, R5, R6, R7, R10, R11, R12, and R13 plus the structural outcomes (duplicate-rule, duplicate-argument, missing-conflict); the production driver decides replay-preflight R13 and the escalated data-integrity class R9; R8 is the source-admission boundary; R14 is the wire-decode boundary, covered by `WireSpec`'s malformed-input matrix. An open mandatory question is an accepted located hole rather than a rejection; `lara-core@0.3` retired the earlier incomplete-argument rejection class for that case.

## What the v0.1 freeze fixed

The versioned contracts cover syntax, wire schemas, static judgments, policy, attacks, holes, compilation and rejection behavior. The strict-chain `contrary` restriction (§8.1, Path B) and proposition normalization (§3.2) are part of the core definition. The current core is `lara-core@0.3`; the separately versioned authoring surface is `lara-syntax@0.11`. `spec-v0.1` is a historical freeze tag that does not resolve in this repository's release-rooted history.

Versioning is by the replay-identity tuple. The frozen core version governs replay, so an input's bytes change when core behavior changes and otherwise do not.

The following are frozen and not open for re-litigation:

- `nf`/`≡` proposition normalization (§3.2), the carve-out that never depended on the corpus.
- Proposition and leaf shape (`nl`/`formal`/`binding`, per-cell grain) at §3 and §3.1. Distribution-valued leaves are deferred, not gaps.
- The policy language: patterns, substitution, critical-question discharge, and the admission table (§4.1–§4.4). The `Gamma(P)` construction figure is §4.3.
- The reference scheme vocabulary, nine families (§4.5).
- The §8.1 strict-reachable `contrary` well-formedness check, whose violation is R12. Duplicate rule IDs and R12 run before program checking.
- The strict-backend seam and the ND reference adapter (§5.1, §5.3).
- The support-term `w` AST and typing, including `leaves` and `certDeps` (§6, §6.1).
- Typed positional attacks, rebut, undercut, and undermine with `w@π` (§7, §7.1).
- Holes as open obligations (§4.2, §6.1, §10.1). A mis-declared hole is R5; an open mandatory question is gap-routed rather than rejected.
- Compilation `compile(P) = AF` with subargument closure (§8).
- Grounded labelling and four-state aggregation (§8, §8.2).
- The abstract syntax plus the wire schema and versioning (§2, §2.1).
- Specified rejection behavior, R1–R14, located per class (§10.1). Quarantine and cycles are deliberately not classes.

The shipped adapter portfolio is `nd@1` (the §5.1 reference backend), `ra@1` (rational-arithmetic and table re-check), `ord@1` (ordered comparison), and `insp@1` (static code inspection). Each discharges the same soundness and dependency obligations as `nd@1`. The LP adapter does not ship.

The original corpus study excluded equivalence and non-inferiority schemes, monotone-functional propositions, parametric growth rates, distribution-valued leaves, negative existentials over code and graded predicates. Static inspection now supports the closed-inventory form of code absence through `insp@1`; it does not prove that the inventory faithfully captures the source bytes. The remaining exclusions are boundaries of the evaluated corpus, not missing checker proofs.

## Mechanization: one core, two implementations

The Haskell checker and the Lean model are separate developments that share one serialized first-order core AST, an S-expression program on disk. That shared serialization is the differential-testing anchor.

```
                    hand-written / elaborator-emitted
                         core programs + expected verdicts
                                     |
                    +----------------+----------------+
                    |  serialized first-order core    |   the shared vocabulary
                    |  (S-expressions on disk)        |
                    +----------------+----------------+
                     decode                     decode
                    +---+---+                 +---+---+
                    |Haskell|                 | Lean  |
                    |checker|                 | model |
                    +---+---+                 +---+---+
                    verdict                   verdict
                        +-------- compare --------+
                              (differential test)
```

The Lean model holds definitions plus theorems: syntax (`Prop`, `Term`, support terms `w`, attacks), the checking judgments as inductive relations *and* as decidable functions proved to agree, the `Backend` structure, the ND adapter as an instance, `compile`, grounded labelling as a bounded least fixed point, and the results listed below. The Haskell side is the production checker. Because the Lean definitions are executable (results 1, 5, and 11 are decidable), the Lean side runs as well as proves, so the differential test compares a model against an implementation rather than a proof against nothing.

The design implication is that `Lara.SupportTerm`'s AST must serialize losslessly into the Lean inductive from the start. The S-expression codec *is* the differential anchor, so it is not a convenience layer bolted on later.

Mechanization carries the paper's formal claim, so the project is planned around a mechanized language result rather than a checker demo. One of the headline contributions is a semantics-preserving compilation into structured argumentation; a paper proof of that is acceptable, but a machine-checked one is the difference between a principled language result and an appendix the reader has to trust. Corpus evidence gathered for this project (deep-research, 2026-07-21, adversarially verified) supports treating it as load-bearing. Mechanized metatheory can be the entire evaluation for a language-semantics paper: "Two Mechanisations of WebAssembly 1.0" (Watt et al., FM 2021) ships two independent mechanised semantics and a type-soundness result as its substance, with no performance numbers or user studies. Artifact evaluation can exclude non-mechanized (paper) proofs from review, because committees lack the time and expertise to check them, so an un-mechanized soundness argument gets no artifact credit. And artifact evaluation certifies reproducibility, not claim-support (SIGPLAN "Checklist Manifesto," 2019), so a badge cannot rescue a weak evaluation; the mechanized theorems have to convince on their own. Property tests remain conformance evidence rather than soundness, so what the soundness claim rests on is the mechanized theorems, not the test suite.

Prover choice is settled: **Lean 4**. Mathlib carries the order-theory and finite-set machinery the AF work could need (result 5 was in fact proved in core Lean without it; only the later BHL numeric theory imports Mathlib), Lean's `Decidable` typeclass makes results 1 and 11 executable and proved-decidable in one artifact, and community familiarity among programming-languages researchers is high. The gate on starting is that the frozen definitions must already be in place: a theorem about a model does not transfer to the Haskell checker without the conformance argument, and re-proving after definition churn is the main way a mechanization track loses its schedule.

Two methodological points govern how the differential test is framed and cited:

- Csmith (PLDI 2011) is oracle-free cross-implementation *voting*: N independent implementations of one spec, where disagreement flags a bug and no reference is trusted. Its transferable lesson is the single-interpretation requirement, that generated core programs must have one well-defined verdict. Lara's grounded status is deterministic by result 5, so this holds by construction. Cite Csmith for that discipline, not for testing against a reference.
- The right precedent for testing an implementation against a mechanized reference is JEST-style N+1-version differential testing (Park et al., ICSE 2021): treat the reference semantics as one fallible oracle among N, cross-execute, and localize whether the spec or an implementation is wrong. The JEST study found 44 engine bugs and 27 spec bugs, so divergence indicts either side; finding a Lean-model bug is a legitimate result.
- An executable oracle generated from mechanized semantics has precedent (Marmsoler and Brucker, TAP 2022, generated a Haskell oracle from an Isabelle Solidity semantics), which is why the executable-Lean route is preferred.
- Feature-sensitive coverage over inductive semantic definitions (OOPSLA 2023, TOSEM 2026) gives a coverage argument that the worked examples exercise every rule and status, rather than an assertion that they do.

## What the Lean development mechanizes

The Lean development mechanizes the frozen semantics under `fullConfig` alone. `Lara.Check.CheckConfig` is a Haskell-side ablation carrier that exists only at the checker boundary for the evaluation baselines; it never reaches the support kernel, is never carried on the wire, and has no Lean counterpart by design.

The scope rule is stated in the Haddock on `Lara.Check.CheckConfig`: evaluation switches do not change the production `fullConfig` semantics. With `CompleteNodesOnly`, `ccTypedAttacks` and `ccConflictScan` only remove rejection arms, so `accept(fullConfig) ⊆ accept(cfg)` for all settings of those two flags. `PromoteTypedHoles`, selected by `noCQConfig`, changes which declarations become graph nodes. It can introduce a required conflict and turn a full-system acceptance into `missing-conflict` rejection; no monotonicity theorem is claimed for that switch.

The strong form of the argument is what makes the exemption sound. The conflict scan, the stage the split made separately ablatable, is itself fully mechanized and axiom-checked, so the semantics the flag switches off is proved regardless of what the Haskell-side switch does. Six `AxCheck.lean` entries cover it:

| Theorem audited in `AxCheck.lean` |
| --- |
| `Lara.Compile.conflictAttackableB_iff` |
| `Lara.Compile.complete_conflict_edge` |
| `Lara.Check.missingConflict_no_rejectClass` |
| `Lara.Check.conflictCache_terms` |
| `Lara.Check.firstMissingConflict_none_iff` |
| `Lara.Examples.check_unit_missing_conflict_wrapped` |

A split that silently changed `fullConfig` would break these proofs or the differential that anchors them, so it could not pass quietly.

`test/AblationSpec.hs` enforces rejection-relaxation inclusion with `prop_monotonicity` over every manifest input and all four combinations of `ccTypedAttacks` and `ccConflictScan`, keeping `CompleteNodesOnly`. This includes the otherwise unnamed combination `ccTypedAttacks = False, ccConflictScan = True`. Hole promotion is checked separately, including `prop_promotionIdentityWithoutHoles`. These are conformance properties of the measurement configurations, not additional Lean semantics.

The per-result status table lives in [`../lean/README.md`](../lean/README.md), which is the authoritative catalogue of what is mechanized. The shape of the results is:

| Spec §9 result | Content | Key theorems and status |
| --- | --- | --- |
| 1 | Decidability of program and attack checking | Checker portion mechanized. `Lara.Check.inferSupport`, `checkAttack`, and `checkProgram` decide the frozen §6.1/§7.1 judgments; `checkUnit` constructs `Unit.CheckedUnit` in the fixed stage order. |
| 2 | Strict-backend isolation | Mechanized: `no_truth_projection`, `nd_nonfactive_witness`, `nd_relative_not_absolute` (the factivity firewall). |
| 3 | Dependency accountability | Mechanized: `leaves_declared` for the source-leaf half; the certificate half closed by `Backend.uses` under obligation 4's three laws (`uses_covers`, `uses_valid`, `uses_account`) over the consulted context `Δ ++ T`, lifted to `certDeps` (`cert_steps_accounted`, `certDeps_resolved`, `certDeps_theory_valid`). |
| 4 | Compilation soundness and subargument closure | Mechanized relational layer: `compile_nodes_checked`, `edge_iff`, `closure_includes_direct`. |
| 5 | Termination and determinism of grounded evaluation | Mechanized: bounded characteristic-operator iteration reaches the least fixed point within `\|Args\|`; `grounded_stable`. |
| 6 | Status preservation, direct source semantics versus compiled-AF semantics | Source-vs-compiled half done: `directIn_iff`, `labelC_inn/out/undec_iff`, `status_preservation`, and `srcIn_iff_grounded`/`srcStatus_iff`. The `Faithful` obligation is discharged constructively by `edgeB_faithful` (`containsB_iff`, `attackClosureB_iff`, `edgeB_iff`), so `checkedAF`, `srcIn_iff_checkedGrounded`, and `srcStatus_iff_checked` state agreement over an accepted program with no oracle hypothesis. |
| 7 | Rationality postulates | Mechanized for the Lean reference PL: `strictReachable_iff_mem`, `aPatMayOverlap_of_instances`, `wfB_iff`, and `contrary_claims_not_both_justified`, whose claims come from `completeClaimFor` with ordered self-pairs covering self-conflict. |
| 8 | Strict-certificate soundness | Mechanized: `strict_step_sound` is the backend obligation projection; `ndBackend` discharges it via `nd_sound`. |
| 9 | Backend replacement | Mechanized as Model A: `backend_replacement` proves status invariance under a uniform injective assurance relabel (an erase-to-one-marker collapse is not an isomorphism, because it can merge occurrences), with `EraseTransport.backend_replacement_transport` constructing the relabeled well-checked program. |
| 10 | Reference natural-deduction adapter soundness and exact dependencies | Mechanized and executable: `nd_sound`, `nd_relevance`, `fv_in_range`, the sound and complete `infer` bridge, and the concrete `ndBackend` replay boundary. |
| 11 | Support adequacy | Mechanized: `nf`/`≡` frozen at §3.2, with equivalence laws, decidability, idempotence, and no argument reordering in `Lara.Prop`. |
| 12 | Codec round-trip to an α-equivalent AST | Mechanized structured presentation codec: `parse ∘ print = id` for the live `Program`/`Policy` AST. This is distinct from correctness of the concrete `.lara` parser, which is covered by conformance tests and presentation parity. See the live proof catalogue and [surface grammar](lara-surface-grammar.md) for versioned fields. |
| 13 | Well-sortedness is decidable and preserved by rule instantiation (`lara-core@0.2`) | Mechanized in `Lara.Sigma`: `wellSorted_decidable`, `wellSorted_subst` (with `_list`, `_mem`, `_rule`), `thetaWellSorted_ruleSortRespecting`, and `checkUnit_wellSorted`. |
| 14 | Supported surface calculus and full-AST elaboration | Mechanized model plus cross-language conformance: `supportedB_iff`, `check_sound`/`check_complete`/`checks_deterministic`, `CoreObligations.checkUnit_complete`, `elaborate_preserves`/`elaborate_reflects`, `global_renaming_equivariant`, and `observe_coherent`. The theorem input is an already-constructed `Presentation.Program`/`Policy`; the concrete parser is excluded, arbitrary accepted core units need not have a source preimage, and source recovery is not unique. See `theory-core.md#surface-calculus-and-verified-elaboration`. |

Results 12 and 14 are intentionally separate. Result 12 says the structured S-expression codec round-trips the live presentation AST; it does not validate the concrete `.lara` parser or elaboration. Result 14 begins with that already-constructed AST and proves the supported surface-calculus and elaboration contracts; it does not turn result 12 into a parser-correctness theorem.

The mechanization rests on a few design choices worth recording. The grounded least fixed point is computed by bounded iteration from the empty set with fuel `|Args|`, not by domain-theoretic fixpoints, so determinism and termination are immediate and the function is executable for the differential anchor. A backend is a structure that carries its own soundness obligation as a field, so result 8 is one line per accepted instance and any future adapter discharges the same fields. Result 4 mechanizes `w@π` as a partial subterm lookup and proves that every compiled edge has a typed source construct and that closure adds edges only onto arguments containing the attacked occurrence. Result 7 mechanizes the compile-time strict-reachable validator rather than Path A.

Result 6 is mechanized for its source-vs-compiled half. `spec.md` §8.2 defines a direct big-step claim-status judgment as the least fixed point of the defense operator (mutually-inductive `DirectIn`/`DirectOut`), and `Lara.Grounded` proves it equal to the executable bounded-iteration labelling over an arbitrary framework. The source composition then reads the Prop-level frozen closure relation directly, the shadow of the same compiled `Edge` rather than an independent calculus, and proves equality with executable grounded status given `Compile.Faithful`; the checker-built `edgeB` discharges that obligation, so the agreement holds over an accepted program with no oracle hypothesis. The theorem was unprovable as first stated, because the spec defined only the compiled route and no independent direct semantics, so there was nothing to preserve; the direct semantics above is what supplies the missing half. The two definitional holes that once made the status function partial are addressed in spec §8: a complete `in` alternative dominates (`statusC_gap_iff` mechanizes "gap only on empty complete support"), and `contested` is grounded `undec` with SCC provenance as a separate defined report. The four-state status is total and deterministic by construction.

No main theorem uses `sorry` or `admit`, and the whole development stays within the standard axiom trio `propext`, `Classical.choice`, and `Quot.sound`. A single replay command checks the development, and `AxCheck.lean` audits each theorem's transitive axiom set. Backend assumptions are recorded explicitly, applying the `sorry`-audit lesson to proof holes as well.

The possible-world layer imports the existing local semantics and adds checking contexts, bridge relations, transport, sorted queries and runtime comparison. [Possible-world theory](theory-pw.md) owns those contracts and their limitations. [Belief Hoare Logic](theory-bhl.md) separately owns statistical-method semantics and artifact binding; its epistemic relations are not interchangeable with possible-world bridges.

## The Lean example corpus

`lean/Lara/Examples/` is the shared fixture corpus that the differential emitters run on, plus the concrete witnesses that separation results require. It is not a second copy of the gates, and the "delete the duplicate test suite" refactor is not attempted again.

Two distinct loads make it structural. First, every golden emitter that anchors a cross-language differential imports its definitions from `Examples.*`, so deleting the corpus does not shrink the gates, it breaks them. The emitters and their imports are `lean/BackendDepsGolden.lean` (imports `Lara.Examples.BackendComposition`), `lean/SemanticsGoldens.lean` (`Lara.Examples.Semantics`), `lean/UpdateMatrices.lean` (`Lara.Examples.Update`), `lean/Lara/SurfaceConformanceMain.lean` (`Lara.Examples.Surface`), and `lean/Lara/UpdatePreconditionParityMain.lean` (`Lara.Examples`). Second, a differential proves *agreement* with the Haskell checker and can never establish a negative. Statements of the form "this weaker property does not imply that stronger one" or "this observation is not determined by that profile" need an exhibited counterexample, and that counterexample is a closed term in `Examples/`. Named instances include `agreesOnArgs_strictly_weaker_than_faithful`, `observe_not_determined_by_profile`, and `not_faithful_eJunk`.

At the audit that settled this, `Examples/` declared 797 theorems, of which 116 carried a negative or separation morpheme in the name (`not`, `no`, `ne`, `non`, `never`, `fails`, `rejected`, `counter`, `strictly`, `absent`, `excluded`, `weaker`). Treat 116 as a floor on the separation results, because the morpheme scan is a name-shape heuristic and not a proof-shape classifier. The argument does not depend on the exact figure.

Two counting rules matter for anyone re-running that analysis. Ledger absence (`#print axioms`, as read by `AxCheck.lean`) is meaningful only for public declarations, because it cannot reach a `private` declaration from another module; `Examples/` holds 137 private theorems, and reading their absence as evidence of deadness produced false positives. And `scripts/check-axcheck-coverage.py` is the number of record for any recount: two reimplementations written during the audit reported 264 and 449 gaps against the checker's 353, one missing attribute-prefixed declarations and the other mishandling a bare `end`. The script resolves names fully qualified and is unit-tested by `scripts/test_check_axcheck_coverage.py`; write ledger entries fully qualified.

The volume question has a separate answer. Scored in CompCert's published categories, `lean/` is about 24.4% definitions, 18.1% theorem statements, and 43.4% proof scripts, against CompCert's 14%, 21%, and 44%. Verification-to-code is about 2.5 times here, about 6 times for CompCert, and about 23 times for seL4, so the mechanization is not disproportionate for what it claims.

## Worked examples

A worked example is a self-contained directory: a surface `.lara` artifact, its co-located policy, the derived `example.core.sexp` wire anchor, and the derived `expected.json` golden. Both derived files are regenerated by `scripts/gen-worked-examples.hs` (parse, then elaborate, then `encodeUnit` or `Lara.ExpectedJson.expectedJson`), and `test/WorkedExamplesSpec.hs` asserts each stays in sync with its `.lara` source. The live catalogue of every committed example, with its witnesses, attack kinds, and statuses, is [`../examples/README.md`](../examples/README.md); this section records the requirements the suite has to satisfy, not the inventory.

Two requirements are hard. Every example is dual-form: a presentation-syntax `.lara` listing and the serialized core S-expression that the Haskell checker *and* the Lean model consume, the differential anchor of the mechanization architecture. The two must decode to the same AST (spec §9 result 12). And every example carries its expected verdict: the four-state status of each claim root, the grounded label of each argument, the located obligations, and, for a rejected example, the exact diagnostic naming the rule, position, and reason. The golden file is the test oracle.

The suite has to exercise every status and every attack constructor so no corner of the calculus is unwitnessed. The original six-example coverage set was three complete programs (`justified-clean`, `open-gap`, `defeat-suite`) and three rejected ones (`undeclared-leaf`, `strict-contrary-violation`, `bad-attack-target`). The delivered suite is larger and includes the two teaching examples A and B, the E4/E5 defeat-semantics cases, the `R2-sort` and `R4` negatives, the P1 philosophy debate, and the S1 through S9 strict-certificate series. Coverage across the suite is justified, gap, contested, and defeated, with rebut, undercut, and undermine all present.

Rejected examples provide conformance evidence for refusal behavior. Clover (arXiv 2310.17807) reports high acceptance on correct instances and zero false positives on deliberately-incorrect (adversarial) instances. Lara's rejection-class mutants test the same two-sided boundary; accept mutants instead exercise valid status changes. Accepting a rejection-class mutant is a defect, while accepting a deliberately valid mutant is required. The Lean proofs, not the examples or mutation rate, carry soundness.

Feature-sensitive coverage over a mechanized specification is a useful precedent for organizing examples by rules and statuses. The current catalogue states the witnesses the suite contains; it should not be read as a claim that a separate published coverage method was run here. Quantitative checker benchmarks and mutation measurements are documented in [evaluation](evaluation.md).

The examples anchor in real artifacts rather than toy-only inputs. The `defeat-suite` case uses the ResNet claim that residual connections enable substantially deeper networks, and demonstrates dead-end discrimination directly: a real dead-end that rules out an alternative explanation compiles to *no edge*, not an attack, so the example shows that "a dead end is not automatically a defeater." Constructed conflicts needed to exercise undercut, undermine, and contested are labelled as synthetic extensions of the real artifact, because saying plainly what is real and what is constructed is itself a reviewer trust signal.

The rejection examples have a spec-class mapping that a reader must not confuse with the example labels. Example `undeclared-leaf` is spec class R1 (an undeclared reference), not R8 (admission reject, which is outside the executable core); example `strict-contrary-violation` is spec class R12 (the §8.1 policy well-formedness check), not spec class R2 (signature); and example `bad-attack-target` is spec class R10 (a `rebut` targeting a leaf occurrence, the wrong occurrence kind), not R7 (assurance). The strict-rule-not-attackable case is supplied by `examples/R4`, where an undercut on a valid strict step rejects R11 `StrictTarget`. The A/B teaching examples and the original frontend suite are defeasible-only, so the strict-certificate frontend path is exercised by `examples/S1` and its successors.

`gap` means that a claim has no complete supporting argument. An open mandatory question is reported as a located hole under `lara-core@0.3`; when the claim has only such incomplete support, its status is `gap`. Hole reporting is distinct from grounded status and is mechanized in the current core.

Goldens must state the intended verdict. Investigate a disagreement between a golden and either checker; do not re-annotate expected output merely to hide that disagreement.

## CI and local gates

The required `Haskell` workflow (`.github/workflows/haskell.yml`) gates the Haskell compiler only. It runs `cabal build`, `cabal test`, the Haddock build, the Python unit tests, the ARA checks, the policy-copy authenticity check, the walking-skeleton golden, replay, and tamper gates, and the mutation-suite freshness check. No step in it installs Lean or runs `lake`.

The ARA checks cover source quotations, session-index consistency, and unique effective observation lookup. The observation gate validates append-only aliases and qualified historical references; it does not rewrite the trace. Its operational contract is [`../CONTRIBUTING.md`](../CONTRIBUTING.md#observation-identity-and-historical-lookup), and the session-file schema and what `session_index.yaml` rows project from it are [`../CONTRIBUTING.md`](../CONTRIBUTING.md#session-records-and-their-index). The additive certified-evidence corpus and the frozen JSON/TSV reports are rechecked against the built Haskell binary, and that gate does not need Lean.

Everything that needs a Lean build runs outside the required workflow:

| Check | Local | On GitHub |
| --- | --- | --- |
| `lake build`, PW example, axiom-withdrawal example, `AxCheck.lean` axiom audit, semantics registry | Included in `make lean-gate` | `Lean` workflow, when a reviewer adds the `lean` label to a PR (or `gh workflow run lean.yml --ref <branch>`) |
| BHL checker and finite-semantics runner | `make bhl-theory`, also included in `make lean-gate` | not run by the optional Lean workflow |
| Haskell-Lean cross-checks: presentation parity, surface conformance and its gate test, semantics, certDeps and update-matrix goldens, update and wire differentials, admission and evidence differentials, evidence CLI and measured-input checks, map conformance, PW conformance | `make cross-check` | not run |

`make local-gates` runs both. The repository's focus is the compiler; the Lean development carries the soundness argument, but whether a given PR needs it re-checked is a review judgment. A PR that changes proofs, or one where review finds something that should be mechanized, gets the `lean` label. Most PRs do neither, and paying for a Lean build and the cross-checks on each of them spends Actions minutes on checks whose outcome the change cannot affect.

The cost picture that motivated the split is historical and was measured by replaying every step of the previous two-job `CI` workflow on a local 128-core machine with a cold build under GHC 9.6.6. The Lean job took about 8.4 minutes (`lake build` 311 s, semantics registry check and tests 191 s), and the Haskell job took about 5.8 minutes (cross-checks 201 s, `cabal test` 69 s, `cabal build` 67 s). On GitHub runners the previous workflow took a median 8.0 minutes of wall clock over its last 100 successful runs with both jobs in parallel.

What this gives up is that nothing on GitHub checks, on every change, that the Haskell and Lean implementations still agree, and a gate that nothing runs drifts silently. When the decision was taken, `make pw-conformance` was already failing on `main`, because its fixture-ownership check had not been taught about `fixtures/pw/source/` while CI was switched off. The mitigation is procedural. A change that touches `lean/`, a wire or envelope contract, or any golden that either side emits runs `make local-gates` before review, and a reviewer adds the `lean` label to a PR that changes proofs.

The rejected alternatives were keeping everything on every push (rejected for the cost above), running the heavy tier on a nightly or weekly schedule (catches drift without a person remembering, but still spends minutes on unchanged trees and reports failures detached from the PR that caused them), and keeping the cross-checks in the required job but dropping the Lean job (the cross-checks need a Lean build, so this keeps most of the cost).

## Test discipline

Property, golden, mutation, and differential tests are conformance evidence, not soundness proofs. They are mandatory at every layer, they are how a checker change is caught, and they do not replace the mechanized theorems. The mechanized theorems carry soundness.

Property tests (QuickCheck) pin the algebraic laws: `≡` reflexive, symmetric, transitive, and linear; natural-deduction weakening; backend replacement; grounded labelling determinism. Golden tests pin complete and rejected examples covering every status and attack type. The mutation suite seeds known defects (wrong formulas, undeclared leaves, hidden policy extension, bad attack targets, open obligations, cycles, codec corruption) and requires every rejection class to be caught. Differential tests run the serialized core programs and verdicts through both the Haskell and the Lean implementations. The differential harness is live: `scripts/differential.sh` runs every `fixtures/**/*.sexp` through both drivers and asserts byte-exact stdout and exit-code agreement, with the Lean executable as the oracle, and `test/DifferentialSpec.hs` pins the agreed verdict bytes so `cabal test` catches regressions without the Lean binary. The conformance corpus lives under `fixtures/corpus/` (generated by `scripts/gen-corpus.hs`) plus committed self-edge fixtures and a 120-argument default-heartbeat stress fixture. The soundness proofs remain in Lean; these tests are conformance evidence.
