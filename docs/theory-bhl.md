# Belief Hoare Logic theorem record
**Date:** 2026-10-08

## TL;DR

Lara's Belief Hoare Logic (BHL) work now has an audited mathematical contract, typed mathematical values, canonical test histories and a nonempty observation-based model. Published-reference discrepancies have checked countermodels and documented corrections. Assertion, execution, soundness, completeness, finite-checking and source-composition results remain required by [issue #24](https://github.com/ARA-Labs/Lara/issues/24). This record names checked declarations separately from the statement inventory in [the assessment](belief-hoare-logic-assessment.md).

## Which definitions are frozen?

`Lara.BHL.Types` defines separate `VarId`, `TestId`, `DatasetId`, `HypothesisId`, `GhostId` and `PopulationId` types. `Variable sort visibility` binds a variable's sort and visibility in its type. `ValueSort` has Boolean, integer, real, product, list and sample-indexed population constructors; fixed visibility, test-tail and comparison vocabularies are closed sum types. A dataset identifier does not stand for its mathematical value, so these types do not prohibit aliases.

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
| `populationId_index_injective` | Equal population-name indices iff equal population identities | `Types.lean` |

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

## Which model and history laws are checked?

The source mapping is [§4.1 values, Definitions 1-4, §5.2.2 history and Definitions 6-7](belief-hoare-logic-assessment.md#which-model-and-numerical-statements-must-be-reconstructed). The corrected local model and assertion-view boundary follow [the architectural decision](theory-bhl-decision.md). All declarations below are in `Lara.BHL`; nested names are written explicitly. Each has its own `#print axioms` row in `lean/AxCheck.lean`.

### What do the typed carriers preserve?

`Value` denotes actual mathematical values. `Value (.population sample)` is a normalized `ProbabilityMeasure (Value sample)`, not a dataset name or a tuple of scalar marginal laws. Boolean and integer carriers are discrete; reals use their Borel sigma algebra; products use the product sigma algebra. Lists use the sigma algebra generated by every optional coordinate. Population-valued samples use the measurable evaluation structure on measures, restricted to probability measures.

`Memory` stores `Option (Value sort)` at each sort, visibility and symbolic identifier. Undefined cells are `none`. The value-carrier witness does not initialize memory cells. Ordinary hidden bindings are immutable in admitted traces; test counters are derived from the ledger and current dataset valuation, not independently mutable hidden cells.

| Declaration or family | Exact result and assumptions | Owning module |
| --- | --- | --- |
| `measurable_list_coordinate` | Every optional list coordinate is measurable for the declared coordinate-generated sigma algebra | `Value.lean` |
| `value_population_carrier`, `value_measurable_product` | Exact population denotation and product sigma-algebra identities | `Value.lean` |
| `value_population_mass`, `value_nonempty` | Every population law has total mass one; every recursive sample sort is inhabited | `Value.lean` |
| `Memory.read_empty`, `Memory.ext` | Undefined reads are `none`; equality of every typed read determines the memory | `Value.lean` |
| `Memory.read_update_self`, `Memory.read_update_other`, `Memory.read_update_invisible`, `Memory.memory_update_typed` | Updates affect only the exact sort/visibility/id cell; the other-read law requires a difference in at least one index | `Value.lean` |
| `Memory.update_overwrite`, `Memory.observable_assemble`, `Memory.hidden_assemble`, `Memory.assemble_projections` | Last same-cell update wins; visible/hidden assembly preserves both projections and reconstructs the original memory | `Value.lean` |
| `Variable.rename_id`, `Variable.rename_comp`, `Variable.rename_symm` | Variable renaming respects identity, composition and inverse bijections | `Value.lean` |
| `Memory.read_rename`, `Memory.rename_binding_preserves`, `Memory.rename_update` | A bijection on `VarId` consistently renames reads and bindings and commutes with typed updates | `Value.lean` |
| `Memory.rename_id`, `Memory.rename_comp`, `Memory.rename_symm`, `Memory.rename_empty` | Corresponding memory-renaming identities, including undefined memory | `Value.lean` |
| `History.record_card`, `History.record_preserves_entries`, `History.record_strict`, `History.record_ne_self` | Every recorded occurrence grows the finite multiset by one, preserves prior entries and changes the ledger, even for a repeated pair | `History.lean` |
| `History.record_count_self`, `History.record_count_other` | Under `DecidableEq D`, matching pair count increments; a distinct pair count is unchanged | `History.lean` |
| `History.recordRepeated_zero`, `History.recordRepeated_succ`, `History.recordRepeated_count_self`, `History.recordRepeated_count_other` | Repetition has no fixed bound; it adds exactly `n` matching occurrences and preserves distinct counts | `History.lean` |
| `History.empty_eq_zero`, `History.empty_count`, `History.record_comm`, `History.eq_iff_counts` | Empty ledger/count identities; recording order commutes; all value/test multiplicities characterize ledger equality | `History.lean` |
| `history_count_lookup`, `history_count_alias`, `history_count_reassignment`, `history_count_update_self`, `history_count_update_other` | Named counts resolve current dataset values. Equal values share counts; reassignment changes lookup, not the recorded ledger. The other-name update requires distinct names | `History.lean` |
| `decompose_leaf`, `decompose_disj`, `decompose_conj` | Both combination connectives preserve all leaf occurrences by multiset addition | `History.lean` |
| `decompose_disj_comm`, `decompose_conj_comm`, `decompose_disj_assoc`, `decompose_conj_assoc` | Order/grouping identities for the flattened ledger, not statistical-event identities | `History.lean` |
| `decompose_count_leaf_self`, `decompose_count_disj`, `decompose_count_conj`, `decompose_repeated_pair_disj`, `decompose_repeated_pair_conj` | Leaf count is one, combination counts add, and repeated pairs count twice under either connective | `History.lean` |

### How are worlds admitted and observations preserved?

`World` stores a nonempty finite trace with empty initial ledger. Trace length is unbounded; neither the model nor its world class needs an execution fuel or finite universe. `Dynamics` supplies independent initial evidence, visible-only command effects and a separate sampling relation that may depend on hidden population laws. A command returns its exact visible output and finite ledger delta.

`TraceAllowed` checks initial evidence and every adjacent observation edge. `Admitted` additionally requires constant ordinary hidden memory. `Model.worlds` contains **all** traces satisfying these conditions, not a caller-selected set. The only model-inhabitation premise is independently inhabited initial evidence. Sampling provenance is extracted from later sampling actions, excluding the initial state; admission proves each such action has a genuine predecessor satisfying the declared sampling relation.

Reference `Accessible` remains equality of the complete ordered observation lists: visible memory, dataset valuation, ledger and action at every state. `SemanticView` exposes current visible state, ledger, actual hidden memory, derived compatible-hidden set and sampling provenance. It does not expose ambient raw trace, action or length. `Model.ValidView` is the image of admitted worlds. The forth/back construction relates view accessibility to the full reference relation; it does not replace that relation with endpoint equality.

| Declaration or family | Exact result and assumptions | Owning module |
| --- | --- | --- |
| `World.trace_nonempty`, `World.start_current`, `World.initial_history` | Nonempty trace, exact initial state and empty initial ledger | `State.lean` |
| `World.extend_trace`, `World.extend_current`, `World.extend_prefix` | Extension appends the intended state, makes it current and preserves the prior trace as a prefix | `State.lean` |
| `accessible_refl`, `accessible_symm`, `accessible_trans` | Equivalence laws for full-observation equality, without a model-admission assumption | `State.lean` |
| `observe_current`, `accessible_current_observation`, `accessible_history_eq`, `accessible_dataset_eq`, `accessible_visible_eq` | Accessibility preserves the complete current observation, including ledger, named dataset values and visible typed reads | `State.lean` |
| `observe_extend`, `extend_accessible_iff` | Extended observations append exactly one observation; two extensions are accessible iff their prefixes and appended observations agree | `State.lean` |
| `World.samplingProvenance_extend_command`, `World.samplingProvenance_extend_sample`, `accessible_sampling_provenance` | Ordinary commands preserve sampling provenance; a sampling action adds exactly its data/population pair; accessibility preserves provenance | `State.lean` |
| `traceEdges_append`, `traceEdges_take_drop`, `traceEdges_prefix`, `traceEdges_take` | Decompose finite adjacent-edge constraints at the actual last prefix observation; prefixes retain those constraints | `TraceLaws.lean` |
| `constantHidden_current`, `constantHidden_binding`, `admitted_current_hidden`, `admitted_hidden`, `admitted_current_hidden_binding` | Constant-hidden/admission premises imply exact hidden-memory and typed invisible-binding preservation | `TraceLaws.lean` |
| `admitted_start`, `admitted_initial` | Independent initial evidence admits a start world; admission supplies its initial action and evidence | `TraceLaws.lean` |
| `constantHidden_prefix`, `admitted_prefix`, `constantHidden_extend`, `admitted_extend` | Prefix closure; lawful extension requires the independently checked last edge and preserved ordinary hidden memory | `TraceLaws.lean` |
| `traceAllowed_extend` | Full-trace constraints after extension are equivalent to the old constraints and the independently checked last edge | `TraceLaws.lean` |
| `traceEdges_sample`, `admitted_sample_transition` | A later sampling label in a constrained trace has an actual preceding state satisfying the sampling relation and unchanged ledger | `TraceLaws.lean` |
| `observeState_withHidden`, `State.withHidden_visible`, `State.withHidden_hidden`, `State.withHidden_history` | Replacing hidden bindings preserves observation, visible state and ledger and sets the exact hidden memory | `ModelLaws.lean` |
| `World.rebuildHidden_trace`, `World.rebuildHidden_current`, `World.rebuildHidden_initial_hidden`, `World.rebuildHidden_current_hidden` | Reconstruction changes hidden memory in every state, including the initial/current states | `ModelLaws.lean` |
| `observe_rebuildHidden`, `rebuildHidden_accessible`, `World.rebuildHidden_samplingProvenance`, `constantHidden_rebuildHidden` | Reconstruction preserves the full ordered observations and provenance and makes hidden memory constant | `ModelLaws.lean` |
| `admitted_rebuildHidden_iff` | For any raw world, reconstructed admission is equivalent to the new hidden memory satisfying its derived full-trace compatibility constraint | `ModelLaws.lean` |
| `admitted_initial_hidden_mem_compatible`, `admitted_hidden_mem_compatible` | Admission supplies both initial and current actual-hidden compatibility witnesses | `ModelLaws.lean` |
| `model_has_world`, `Model.validWorld_nonempty`, `Model.validView_nonempty` | Independently inhabited initial evidence constructs an admitted world and realized view | `ModelLaws.lean` |
| `compatibleHidden_eq_of_accessible`, `compatibleHidden_rebuildHidden`, `accessible_current_visible`, `semanticView_rebuildHidden` | Full accessibility/reconstruction preserve derived compatibility and visible state; reconstruction changes only the view's actual hidden component | `ModelLaws.lean` |
| `compatibleHidden_extend_command` | A visible-only command satisfying its exact effect equations preserves the complete compatible-hidden set; sampling transitions are not covered by this law | `ModelLaws.lean` |
| `view_accessible_forth`, `view_accessible_back` | Full accessibility implies view accessibility. Given an admitted target and accessible views, reconstruct an admitted world with the source's complete observations and target's exact semantic view | `ModelLaws.lean` |
| `view_accessible_refl`, `view_accessible_symm`, `view_accessible_trans`, `view_accessible_equivalence` | View accessibility is an equivalence relation | `ModelLaws.lean` |
| `Model.accessible_refl`, `Model.accessible_symm`, `Model.accessible_trans`, `Model.accessible_equivalence` | Reference equivalence laws restricted to valid BHL worlds; no Lara accepted-context relation is involved | `ModelLaws.lean` |
| `Model.view_accessible_forth`, `Model.view_accessible_back`, `Model.viewOf_surjective`, `Model.viewOf_forth`, `Model.viewOf_back` | The admitted-world map is onto the realized view carrier and supplies reference/view forth/back | `ModelLaws.lean` |

### Which inhabited witnesses exercise these laws?

`Lara.BHL.ModelExamples` supplies a concrete test-only dynamics with initial evidence `True`, visible-state-preserving test effects and exact singleton ledger deltas. It admits no sampling transitions; later statistical instances supply their own independent population/sampling constraints. This is a genuine nonempty model, not a calibration or BHL derivation claim.

The checked declarations are `model_inhabited`, `initial_admitted`, `recordSnapshot_admitted`, `single_admitted`, `repeated_admitted`, `lawful_prefix`, `initial_has_defined_result`, `alias_names_distinct`, `aliases_have_equal_values`, `alias_count_one`, `repeated_count_two`, `same_final_memory`, `different_histories`, `same_memory_different_observations`, `reassignment_changes_lookup_not_ledger`, `hidden_alternatives_accessible`, `hidden_alternatives_different`, `histories_initially_empty` and `repeated_combination_keeps_multiplicity`. They establish admitted alias counts one then two, same final memory with different ledgers, nonaccessibility despite that memory equality, changed lookup after reassignment, and distinct hidden alternatives with equal full observations.

`mathematical_carriers_defined` also places actual reals, product lists and a normalized scalar-real law into typed memory. `joint_list_boolean_laws_inhabit_memory` places joint real-pair, real-list and Boolean laws into memory; `joint_law_normalized` proves the joint law's mass is one. These mathematical law witnesses elaborate in Lean; arbitrary-real/measure evaluation is not claimed executable.

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

PR 01 established the audited contract and initial carriers. The later stages remain mandatory; this reference acceptance alone supplies no BHL execution, soundness, completeness, calibrated binary test or Lara bridge.

## What completed PR 02 on the server?

PR 02's typed carriers, canonical model and test history passed server acceptance on 2026-10-08. It adds 154 audited theorems, giving 190 BHL theorems across the two completed stages. The model and carrier reviews found no remaining blockers. Review corrected a scalar-only population carrier before acceptance: population sorts now carry their sample sort and include genuine joint, list-valued, Boolean and nested population laws.

| Executed command | Observed result and coverage |
| --- | --- |
| `(cd lean && lake build Lara.Examples.BHLModel)` | Passed, 2,555 jobs, including every new model/history proof and the joint/list/Boolean population witnesses |
| `(cd lean && lake env lean --run BHLStageSmoke.lean)` | Passed: alias counts `(0,0) → (1,1) → (2,2)`; reassignment `(0,1)` against the unchanged ledger; reported value one in both worlds; ledger sizes one/two and full-observation lengths two/three; 1,000 repeated occurrences; distinct hidden Booleans; exact product-list read; undefined read `none` |
| `make local-gates` | Passed on the final proof candidate. Lean build: 2,807 jobs; axiom coverage: 3,768 declarations, including all 154 additions, with only the standard trio; semantics registry: 176 modules; evidence CLI: 58 scenarios; frozen evidence: 10/10 reproduced; map differential: 1,651 cases, no failures |
| `make ara-source-spans ara-session-index ara-observations` | Passed: 66 quotations, 83 agreeing sessions, 192 unique effective observations, two ambiguous historical IDs and 14 audited reference lines |

The smoke main is removed after verification. The executed model/history plan is retired into the definitions and theorem map above. These results do not claim assertion satisfaction, BHL program execution, derivation soundness, relative completeness, test calibration or artifact composition.

## What remains required?

PR 02 supplies the model and history laws. The assessment maps the remaining assertion/substitution/belief results to PR 03, execution and parallel correspondence to PR 04, inductive derivation soundness to PR 05, and relative completeness with a proved legal assertion representation to PR 06. PR 07 must independently prove the binary distribution, ties, calibration and valid/invalid statistical procedures. PR 08 must prove executable correspondence and register the real runner. PR 09 must prove exact source/evidence binding, dependency loss, safe rebinding, ordinary-observation preservation and the incomplete-record witness.

All stage PRs target `feat/belief-hoare-logic`. The integration branch retains planning commit `46a9747` and one commit per completed stage. Integrated acceptance joins both completeness and source composition before the version bump, merge commit to `main` and release. This work does not discharge [issue #23](https://github.com/ARA-Labs/Lara/issues/23)'s wider research-process theory or authorize an empirical protocol.

## Recommendations

1. Use the corrected contracts and explicit source mapping when adding semantics; do not import the paper's conclusions as axioms.
2. Update this record with exact theorem assumptions, audit entries and exercised commands in each completed stage.
3. Require joined-tree proof, runtime, source/evidence and release evidence before closing the workstream.
