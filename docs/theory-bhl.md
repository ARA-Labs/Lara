# Belief Hoare Logic theorem record
**Date:** 2026-10-07

## TL;DR

Lara's Belief Hoare Logic (BHL) work begins with an audited mathematical contract, distinct symbolic identities and concrete countermodels to discrepancies in the published reference. The researcher approved documented corrections and a pinned Mathlib dependency for actual real-number and probability semantics. Later model, assertion, execution, soundness, completeness, finite-checking and source-composition results remain required by [issue #24](https://github.com/ARA-Labs/Lara/issues/24). This record names checked declarations separately from the statement inventory in [the assessment](belief-hoare-logic-assessment.md).

## Which definitions are frozen?

`Lara.BHL.Types` defines separate `VarId`, `TestId`, `DatasetId`, `HypothesisId` and `GhostId` types. `Variable sort visibility` binds a variable's sort and visibility in its type. `ValueSort` has Boolean, integer, real, population, product and list constructors; fixed visibility, test-tail and comparison vocabularies are closed sum types. A dataset identifier does not stand for its mathematical value, so these types do not prohibit aliases.

The corrected artifact and numeric contracts are in [the architectural decision](theory-bhl-decision.md). A modeled application requires a genuine satisfied precondition and an actual terminating execution bound to the exact model and program. Artifact support supplies neither premise. Residual interpretation, physical sampling and submitted-history completeness assumptions remain external.

## Which symbolic identity results are available?

Each row is a vocabulary result, not inherited statistical metatheory. Its axiom-audit entry is `#print axioms` followed by the fully qualified declaration below in `lean/AxCheck.lean`. The only hypotheses are the displayed identity values at the same type; no model, probability or scientific assumption enters these proofs.

| Declaration in `Lara.BHL` | Statement | Source |
| --- | --- | --- |
| `varId_index_injective` | Equal variable indices iff equal variable identities | `Types.lean` |
| `testId_index_injective` | Equal test indices iff equal test identities | `Types.lean` |
| `datasetId_index_injective` | Equal dataset-name indices iff equal dataset identities | `Types.lean` |
| `hypothesisId_index_injective` | Equal hypothesis indices iff equal hypothesis identities | `Types.lean` |
| `ghostId_index_injective` | Equal logical-variable indices iff equal logical-variable identities | `Types.lean` |
| `variable_id_injective` | Equal underlying identities iff equal variables at the same sort and visibility | `Types.lean` |

## Which source discrepancies have checked witnesses?

`Lara.BHL.ReferenceAudit` contains bounded countermodels to individual source claims. It is not the reference BHL model, assertion language or derivation system. The audit explains why literal transcription is insufficient; later modules must implement the corrected contract and prove their own metatheory.

| Declaration in `Lara.BHL.ReferenceAudit` | Checked witness | Reference location |
| --- | --- | --- |
| `equal_memory_equal_valuation` | The memory-dependent atomic valuation respects equality of memory | §4.3 predicate restriction |
| `assignment_substitution_counterexample` | A syntactically nullary atom can be true before assignment and false afterward | Figure 2 UpdVar; Appendix B.4 Lemma 8 |
| `alias_history_consistent` | Two names for the same dataset both read test count one | §5.2.2 history consistency |
| `history_assertion_counterexample` | The value-indexed exact-history equation holds while the name-count equation fails | §6 equations (8) and (11) |
| `named_history_update_inconsistent` | Updating only the selected name leaves the other alias inconsistent | Figure 1 test transition |
| `modal_memory_encoding_counterexample` | Knowledge of the hidden value fails, but substitution of its actual value gives a tautology | Appendix B.5 Proposition 4 equation (11) |
| `equality_threshold_not_monotone` | Equality with one threshold does not imply equality with a larger threshold | Proposition 2 SB-< |

Each witness is inhabited and independent of Lara's core. The equality-threshold witness is the arithmetic obstruction to the proposed monotonicity step; the full statistical-belief countermodel belongs to the assertion/statistical stages. All declarations have explicit axiom-audit rows. These findings are source-audit results, not claims that current Lara source checking is unsound.

## Which real probability results are available?

`Lara.BHL.Numeric` imports `Mathlib.MeasureTheory.Measure.ProbabilityMeasure` at the approved pin. `NumericTest` contains a measurable statistic, actual normalized null probability law, tail relation and measurable-tail evidence. `tailProbability` is the real measure of that event. `ProbabilityCoupling` contains a joint probability law and exact push-forward marginal equations. Neither structure assumes calibration or BHL soundness.

These are concrete mathematical carrier/correspondence results needed by the statistical semantics. Each declaration below has its own `#print axioms` row in `lean/AxCheck.lean`. Event bounds require the displayed probability measure; tail bounds require a `NumericTest`; coupling results require its exact marginal equations and measurable component events. The sum may exceed one and is not clamped.

| Declaration in `Lara.BHL` | Result and exact additional hypotheses |
| --- | --- |
| `eventProbability_nonneg`, `eventProbability_le_one` | Every event has real mass between zero and one |
| `eventProbability_empty`, `eventProbability_univ` | Empty event has mass zero; whole space has mass one |
| `eventProbability_mono` | Event inclusion implies probability order |
| `eventProbability_union_le` | Union mass is at most the sum, without independence |
| `eventProbability_inter_le_min` | Intersection mass is at most either component mass |
| `eventProbability_map` | A measurable map and measurable target event give exact preimage probability |
| `NumericTest.measurable_tailEvent` | The declared event has its required measurable-set proof |
| `NumericTest.tailProbability_nonneg`, `NumericTest.tailProbability_le_one` | The computed mathematical tail probability is in the unit interval |
| `NumericTest.tailProbability_mono` | Tail-event inclusion implies probability order; arbitrary observation-order monotonicity is not assumed |
| `ProbabilityCoupling.left_event`, `ProbabilityCoupling.right_event` | Joint lifted events equal their measurable marginal probabilities |
| `ProbabilityCoupling.union_le`, `ProbabilityCoupling.inter_le_min` | Exact marginals imply union and intersection bounds, without independence |
| `NumericTest.coupled_tail_union_le`, `NumericTest.coupled_tail_inter_le_min` | Apply those coupling bounds to the two declared measurable tail events |
| `eventProbability_dirac_of_mem` | A Dirac point in an event gives mass one |
| `eventProbability_dirac_of_notMem` | A Dirac point outside a measurable event gives mass zero |
| `realDiracTest_inhabits` | The identity statistic, Dirac null law at zero and inclusive upper tail inhabit the actual-real test carrier |
| `realDiracTest_tailProbability_zero`, `realDiracTest_tailProbability_one` | This carrier witness has tail probability one at zero and zero at one |

The Dirac witness proves nonemptiness, not calibration of the final binary test. These actual-real measure definitions are noncomputable. Their exact identities are checked by proof elaboration; the initial smoke run executes the symbolic bindings and source-countermodel operations. No executable arbitrary-real evaluator is claimed.

## What was verified before the server handoff?

The researcher requested a partial commit and draft PR, with continuation on a server. At that handoff PR 01 was incomplete and later implementation stages had not started. The server acceptance below supersedes that implementation status without changing the historical outcomes.

| Check | Observed result and coverage |
| --- | --- |
| Focused Lean builds | `Lara.BHL.Types`, `Lara.BHL.ReferenceAudit` and `Lara.BHL.Numeric` compiled |
| Library-based throwaway smoke | Executed typed dataset/result/test bindings and the actual audit operations: assignment precondition true/postcondition false; both dataset aliases count one; name-count equation false; selected-name-only update leaves the other alias at zero |
| Real carrier proof examples | Checked the Dirac tail identities: probability one at zero and zero at one; no arbitrary-real runtime computation claimed |
| macOS integrated Lean build/audit | Passed; AxCheck coverage was 3,614 declarations, including all 36 new BHL theorems, with only the standard axiom trio |
| macOS `make local-gates` | Failed later at existing `evidence-cli` publication: no Linux `SYS_renameat2` on macOS; the existing implementation fails closed with `ENOSYS` |
| Linux container, original 16 GiB VM cap | Two attempts failed compiling existing `Lara.Examples.Surface`; kernel cgroup accounting reported two OOM kills |
| Linux container, temporary 32 GiB VM cap | Lean build passed (2,799 jobs), PW file-driven gate passed (24 cases), and the 3,614-declaration axiom audit passed; stopped at the researcher's handoff request before the complete registry/cross-check gate finished |
| ARA gates before handoff capture | Source spans passed (66 quotations); session index passed (83 sessions); observations passed (191 unique effective observations, two ambiguous historical IDs, 14 audited reference lines) |

At handoff no complete `make local-gates` pass was available. The owned verification container was stopped and OrbStack's original 16 GiB setting restored. No gate or existing publication behavior was weakened.

## What completed PR 01 on the server?

PR 01's reference, artifact and numeric contract passed acceptance on 2026-10-08. The reference inventory now retains the complete corrected BHκ equivalence `κS ↔ PκS ↔ KκS`, with observable dataset terms, canonical ledger and full-history observations. In particular, the possibility-to-history direction used by the hidden-test argument is an explicit PR 03 proof obligation, not a theorem already supplied by this stage.

| Executed command | Observed result and coverage |
| --- | --- |
| `(cd lean && lake exe cache get)` | Resolved the approved manifest and downloaded/decompressed all 8,639 cache files |
| `(cd lean && lake build Lara.BHL.Types Lara.BHL.ReferenceAudit Lara.BHL.Numeric)` | Passed, 2,548 jobs |
| `(cd lean && lake env lean --run BHLStageSmoke.lean)` | Passed: typed identities; assignment pre=true/post=false; dataset aliases both count one; name-count equation=false; selected-name-only update inconsistent. The Dirac probability identities elaborated; no arbitrary-real runtime computation was claimed |
| `make local-gates` | Passed the complete Linux Lean and cross-check gate. Lean build: 2,799 jobs; axiom coverage: 3,614 declarations, including all 36 BHL theorems, with only the standard trio; semantics registry: 168 modules; evidence CLI: 58 scenarios; frozen evidence inputs: all 10 reproduced byte-identically; map differential: 1,651 cases, no failures |
| `make ara-source-spans ara-session-index ara-observations` | Passed: 66 quotations, 83 agreeing sessions, 192 unique effective observations, two ambiguous historical IDs and 14 audited reference lines |

Independent specification reviews covered the source/artifact contract and frozen numeric code. The missing BHκ directions were corrected and rechecked; code-quality review approved the frozen modules. The scratch main was removed after the run. The executed PR 01 plan is retired; its durable contract and source inventory remain in this record, the assessment and the architectural decision.

PR 02-09 remain mandatory. This acceptance establishes the audited contract and initial carriers, not BHL execution, soundness, completeness, calibrated binary tests or the Lara bridge.

## What remains required?

The assessment maps the model and history laws to PR 02, assertion/substitution/belief results to PR 03, execution and parallel correspondence to PR 04, inductive derivation soundness to PR 05, and relative completeness with a proved legal assertion representation to PR 06. PR 07 must independently prove the binary distribution, ties, calibration and valid/invalid statistical procedures. PR 08 must prove executable correspondence and register the real runner. PR 09 must prove exact source/evidence binding, dependency loss, safe rebinding, ordinary-observation preservation and the incomplete-record witness.

All stage PRs target `feat/belief-hoare-logic`. The integration branch retains planning commit `46a9747` and one commit per completed stage. Integrated acceptance joins both completeness and source composition before the version bump, merge commit to `main` and release. This work does not discharge [issue #23](https://github.com/ARA-Labs/Lara/issues/23)'s wider research-process theory or authorize an empirical protocol.

## Recommendations

1. Use the corrected contracts and explicit source mapping when adding semantics; do not import the paper's conclusions as axioms.
2. Update this record with exact theorem assumptions, audit entries and exercised commands in each completed stage.
3. Require joined-tree proof, runtime, source/evidence and release evidence before closing the workstream.
