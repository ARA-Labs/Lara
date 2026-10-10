# Research-process semantics: entitlement over incomplete histories

## TL;DR

The research-process layer (`lean/Lara/Process/`, namespace `Lara.Process`) states when a research record *entitles* a claim to be asserted, as opposed to when the claim is true. A record denotes the set of complete modeled histories and reporting choices it could have come from, relative to an explicit model and scoped coverage assumptions; executable verdicts range over a declared finite carrier. A verdict quantifies over that set and is `inconsistent` when it is empty. Claim-level entitlement requires the set to be nonempty and some warrant in every compatible history; auditing a submitted argument requires one fixed witness to warrant in every compatible history. The layer is an outer layer over the core calculus and [BHL](theory-bhl.md) and changes neither. It adds no wire format, `.lara` syntax, Haskell checker or corpus change.

## What are the boundaries?

Entitlement is non-factive and separate from every existing judgment. It implies neither the claim's truth nor BHL knowledge of it, and an unchanged public status does not transport it. There is no coercion between this layer's verdicts and the core's statuses or BHL's modalities; every translation states its hypotheses and proves preservation.

`Lara.BHL.HistoryCoverage` keeps its single constructor `completeModeled`. The omission models of this layer live in the separate type `RecordCoverage`, and `coverage_complete_conservative` relates the two. `Lara.BHL.History` stays a multiset; ordered process histories are a separate view, and `admitted_testProjection` proves the two agree on which tests ran. `ArtifactBinding` still reads the multiset `History`.

No theorem here establishes the honesty of an external log, the faithfulness of a natural-language interpretation or the adequacy of a model for the real world. A finite carrier and horizon are model assumptions with explicit parameters, not facts inferred from a short record.

## Which vocabulary is frozen?

`Lara.Process.Vocabulary` and `Lara.Process.Contract` fix the shared vocabulary:

- Distinct identifier newtypes for events, actors, plans, runs, claims, sources, datasets, versions, statistical families and justification witnesses. `DataId` is distinct from `Lara.BHL.DatasetId`, and distinct dataset identities never imply statistically independent samples.
- A closed `Event` type distinguishing plan commitment, data access (with an explicit `selection` or `evaluation` purpose), analysis runs (naming their plan, inputs and statistical family), results, claim assertions, source retractions and dataset updates. `ProcessHistory` is an ordered list of identified events; neither file order nor display order of a record is temporal evidence.
- `RecordCoverage` with constructors `complete`, `countBounded`, `declaredPolicy` and `openWorld`, each carrying a `CoverageScope` (event kinds, optional family, optional actor and dataset restrictions, and a submission cutoff; a restricted scope excludes events that carry no actor or no dataset). The constructors are not a strength order: strength is inclusion of compatible sets, `Assumptions.Stronger`.
- `Verdict` with the four values `inconsistent`, `certainTrue`, `certainFalse` and `unknown`.
- The evidence-kind lattice `hypothetical < conditional < supported < observed`, error kinds, guarantee classes (`fwer`, `fdr` and `mfdr` are distinct) and `Profile`, whose coverage policy is a decidable predicate rather than an order on constructors. The lattice is this layer's own construction; existing ARA provenance labels are not read as members of it.

A `ProcessModel` supplies `Valid` histories and the `Report` each history yields under each reporting choice. `Compatible M A r (h, rho)` holds when `h` is valid, the admitted assumptions `A` allow `rho`, and that choice reports exactly `r`. The carrier is the pair of history and reporting choice because a semantics that ignores the reporting protocol conditions wrongly. `compat` describes completions of the past; `FutureSemantics.continues` is a separate relation for later events.

`verdictOf` is the classical reference verdict over an arbitrary carrier, with the empty-set check first. `verdict` is the executable version over a declared finite carrier with decidable predicates.

The witness quantifiers are frozen as `EntitledBy compat warranted` (nonempty, and every compatible history has *some* warranting witness) and `ArgumentEntitledBy compat warranted w` (nonempty, and the one fixed witness `w` warrants in every compatible history). Runs name the plan version and the input dataset versions they used.

## Which tempting laws are false?

`Lara.Examples.ProcessFalseLaws` refutes six laws with small decidable countermodels before any positive result is attempted. Each refutation decides the shape of a later theorem.

| False law | Countermodel | Consequence |
| --- | --- | --- |
| A stricter profile entitles fewer claims | `stricter_profile_reinstates`: dropping the admissible kind `supported` removes an attacker and turns a defeated claim justified | Only a directional version is proved |
| Quarantine only removes warrant | `quarantine_reinstates`: quarantining a defeater's leaf reinstates its target | The quarantine iff holds only on the support-only fragment |
| Unchanged status means unchanged warrant | `unchanged_status_different_basis`: a claim is justified in two frameworks, but only one justification depends on a defender whose removal defeats it | Entitlement is keyed by justification witness |
| An empty compatible set is harmless | `empty_compatible_vacuous`: naive supervaluation certifies a property and its negation; the verdict is `inconsistent` | Positive verdicts require a nonempty set |
| Completing the past is continuing the future | `past_completion_not_future`: every past completion warrants a claim that a later retraction defeats | `compat` and `continues` stay separate |
| Ordering predicates can be stated over the event multiset | `multiset_forgets_plan_order`: two histories with one event multiset differ on plan precommitment, so no multiset predicate decides it | Order predicates are stated over ordered histories |

## What does the compatible-history core prove?

`Lara.Process.Verdict`, `Kleene`, `Coverage` and `Conservative` hold the laws of the four-valued verdict. They are stated for the reference `verdictOf`; `verdict_eq_verdictOf` transfers them to the executable `verdict`, and `verdictOf_inconsistent_iff`, `verdictOf_certainTrue_iff`, `verdictOf_certainFalse_iff` and `verdictOf_unknown_iff` characterize each verdict exactly.

| Theorem | Statement |
| --- | --- |
| `verdict_sound`, `verdict_sound_false` | `certainTrue` (`certainFalse`) implies the property (its negation) at every compatible history |
| `positive_needs_nonempty` | a `certainTrue` or `certainFalse` verdict implies a compatible history exists |
| `certain_refine` | if the refined compatible set is contained in the original and is nonempty, a determinate verdict transfers |
| `certain_weaken_assumption` | stronger admitted assumptions preserve a determinate verdict when their compatible set is nonempty |
| `certain_factor` | if a coarse observation is `g` of a finer one, a determinate coarse verdict transfers to every realized finer observation |
| `determined_iff_no_witness` | a verdict is determinate iff the compatible set is nonempty and no two compatible histories disagree |
| `verdict_of_generator` | a realized record whose compatible histories agree with its generating history on the property has that history's verdict |
| `history_independent_verdict` | a property that reads no history gets its constant truth value on every consistent record |
| `naive_sound_iff_factors`, `factors_iff_determinate` | an exact record-level evaluator exists iff the property factors through the observation on valid histories, iff every realizable record is determinate |
| `kleene_sound` | whenever the compositional strong-Kleene verdict is not `unknown`, the reference verdict agrees; its empty-set check comes first |
| `referenceAtoms_sound`, `finiteAtoms_eq`, `kleeneVerdictFinite_eq` | the atom valuation read off atom verdicts is sound, and the executable Kleene evaluator equals the reference one |
| `RecordCoverage.stronger_openWorld`, `RecordCoverage.countBounded_mono` | every scoped assumption implies open-world coverage; a smaller count bound is stronger |
| `complete_scope_events`, `complete_coverage_determines` | under `complete` coverage of a scope, with reports exposing only in-scope events, every compatible history has exactly the record's in-scope events, so every property reading only those events gets its generating history's verdict |
| `coverage_complete_conservative` | admitting a binding's own `HistoryCoverage` through `RecordCoverage.ofHistoryCoverage`, if the artifact warrant reads only in-scope events, a realized record's verdict is exactly `ArtifactWarrant` at the generating bridge history |
| `realized_conservative`, `completeObservation_conservative` | the same agreement for any realized record that determines the warrant; the complete observation always determines it |

`RecordCoverage.ofHistoryCoverage` reads BHL's only constructor `completeModeled` as `complete` coverage of a stated scope. Conservativity needs more than a complete test ledger: the `reads` hypothesis requires every input the warrant reads, data accesses included, to lie in the covered scope. Profile checks beyond `ArtifactWarrant` are a separate obligation.

`Lara.Examples.ProcessCore` supplies the witnesses: `refine_needs_nonempty` and `weaken_assumption_needs_nonempty` (refining a record or strengthening its assumptions until the set is empty yields `inconsistent`), `kleene_incomplete` (the compositional evaluator answers `unknown` on `p ∨ ¬p` where supervaluation answers `certainTrue`), `coverage_incomparable` (complete and count-bounded coverage of one scope allow incomparable sets), `partialRecord_unknown` (the existing `record_does_not_determine_conclusion`, restated as the verdict `unknown` of a process model built from the same two BHL histories) and `partialRecord_not_factors` (naive evaluation of the method conclusion on the submitted record is unsound).

## How are entitlement and no-promotion defined?

`Lara.Process.Entitlement` follows a justification norm rather than a truth or knowledge norm, because only a non-factive norm can be decided from a record. Pollock's warrant, an ultimately undefeated argument, is Lara's grounded `in` label.

A `WarrantModel` says, for each complete history, which kinded argumentation framework holds, which argument each justification witness submits and what it concludes, which errors its method probed, which guarantee it attains, and whether an external artifact check holds (for example a BHL `ArtifactWarrant`). The claim's truth at the history is a separate field that no warrant condition reads. `Warranted M P h c w` is the artifact check together with `ProfileChecks`: the conclusion, an admissible evidence kind, every required probe, the profile's guarantee class at a level no larger than the profile's, and the grounded label `in` in the framework the profile sees (`underProfile`, which keeps only arguments of admissible kinds). Warrant is keyed by the witness's own argument, never by claim status. `WarrantModel.withArtifact` binds the artifact check to BHL's `ArtifactWarrant` over bridge histories, so `bridge_warranted_iff` reads warrant as exactly `ArtifactWarrant` plus the profile checks.

`Admitted` carries a scoped coverage assertion together with the traces, reported events and policy interpretation that give it meaning, plus any further admitted restriction; `Admitted.assumptions` is the coverage's own restriction conjoined with that extra one, so an accepted coverage assertion is never detached from the compatible set it constrains. `Entitled M P S A r c` requires the profile to accept the admitted coverage and `EntitledBy` over the compatible completions. `ArgumentEntitled M P S A r c w` requires the same with `ArgumentEntitledBy` for the fixed witness `w`. ARA submitted-argument audits use `ArgumentEntitled`; claim-level `Entitled` is never reported as verification of a particular argument.

`Profile.strict α` is the one concrete profile: `complete` or `countBounded` coverage, `observed` evidence only, FWER at `α`, sampling error probed, grounded acceptance.

| Theorem | Statement |
| --- | --- |
| `argumentEntitled_implies_entitled` | auditing the submitted argument implies claim-level entitlement |
| `argumentEntitled_verdict` | an audited witness's warrant has verdict `certainTrue` over the compatible completions |
| `KindDerivation.kind_le_leafMeet`, `no_promotion_any_leaf`, `no_promotion` | when every rule outputs a kind at most the meet of its inputs, a derivation concludes at most the meet of its leaves; with only hypothetical or conditional leaves it never concludes `observed` |
| `strict_no_promotion` | an argument whose kind comes from such a derivation is never warranted under `Profile.strict` |
| `no_promotion_agrees_blocking` | a warranted argument outside a blocked set is `in`, and its claim `justified`, in the larger declared framework: `Blocked.justified_nonpromotion` specialized to a witness |
| `profile_restriction_nonpromotion` | if every argument a profile removes lies outside the witness's ancestry, a warranted argument is `in`, and its claim `justified`, in the full framework: removing inadmissible kinds never manufactures acceptance, just as quarantine does not |
| `stricter_directional`, `stricter_directional_argument`, `stricter_directional_entitled` | if every argument a stricter profile removes lies outside the witness's attack ancestry, warrant, submitted-argument entitlement and (when the condition holds for every witness) claim-level entitlement transfer from the stricter profile to the laxer one |
| `bridge_warranted_iff`, `bridge_argument_audit` | over bridge histories, warrant is `ArtifactWarrant` plus the profile checks, and an audited submitted argument certifies `ArtifactWarrant` in every compatible history |
| `conditional_not_applied` | BHL's conditional-false method is a valid conditional triple without a modeled application, and a conditional payload (`payloadKind`) is not admissible under `Profile.strict` |

The evidence-kind lattice and the no-promotion law are this layer's construction; no published no-promotion theorem for scientific claim kinds was found. The kind law and the core's blocking laws forbid different promotions: the kind law forbids raising evidence kind through rules, the blocking laws forbid deletion from manufacturing acceptance. Where they meet, a warranted witness under a profile, `no_promotion_agrees_blocking` and `profile_restriction_nonpromotion` reuse `Blocked.justified_nonpromotion`, the law that `quarantine_nonpromotion_corollary` and `package_source_justified_nonpromotion` also instantiate; those existing theorems are unchanged.

`Lara.Examples.ProcessEntitlement` uses one two-history model in which the claim's two witnesses swap roles between histories. `entitled_not_argument` shows the claim entitled while no submitted witness is `ArgumentEntitled`. The non-collapse countermodels are `defeated_not_warranted` (a present, observed argument that is defeated), `conditional_not_warranted` (an undefeated conditional argument the strict profile rejects and a laxer one accepts, which also separates the two profile instances), BHL's `conditional_not_applied`, `warranted_not_true` and `entitled_not_known` (the record's reader cannot exclude a history that reports the same and where the claim is false). `Known` is this layer's own knowledge notion, parametric in an accessibility relation; BHL's `K` has the same shape over `Lara.BHL.Accessible`, but no theorem here identifies the two. `promotion_needs_wellKinded` shows that the rule-kind discipline is what blocks promotion, and `stricter_directional_instance` exercises the directional law.

## How does order enter the history?

`Lara.Process.Order` gives process histories a transition relation. `ProcessState.step` requires fresh event identities; a committed plan version, a fresh run identity and the current version of every input for each run; an existing run for each result; and at most one retraction per source. Dataset updates set the current version. `Step` is that relation, `ValidHistory` means the history executes from the initial state, and `ValidThrough cutoff` adds the submission cutoff: completions never extend past it, and later events are future continuations. `run_some_iff_steps` unfolds execution into `Step` transitions, and `valid_prefix` shows validity only constrains the past.

The analysis-order predicates are decidable over complete ordered histories:

- `PlanCommittedBefore h plan version data`: some commitment of that plan version precedes every evaluation access to the datasets. Every evaluation access to those datasets counts, whichever run or version it served; this is the conservative reading.
- `RunPrecommitted h run`: every run with that identity used a plan version committed before every evaluation access to its inputs.
- `Predictable h`: every run is precommitted in that sense. Reading each run as one e-value factor, each factor is fixed before its evaluation data is read. This is order evidence under the model's complete account of relevant accesses, not a measurability proof.
- `SplitSelection h selection test`: selection reads only `selection` datasets, evaluation reads only `test` datasets, and the identity lists are disjoint. This is read separation only, never statistical independence.
- `familyCount h family`: the number of runs of a family, failed trials included (`familyCount_append_run`). `successfulRuns h` lists the runs with a positive result; only those are lowered to arguments, so a failed run neither supports nor attacks.

A partial-order record (`OrderRecord`) lists reported events and explicit precedence constraints. `OrderCompatible` admits every history valid through the record's cutoff that contains the reported events and respects the constraints, so all valid orderings the evidence does not rule out stay compatible. `orderCompatible_perm` proves the listing order of a record is not temporal evidence. `orderCompatible_mono` proves more evidence never adds completions, so a record that leaves an order unconstrained keeps every history the constrained one keeps, violating ones included; missing entries therefore never establish an order predicate, because a verdict is certain only when every compatible completion satisfies it. `contradictory_constraints` and `contradictory_constraints_inconsistent` make contradictory constraints `inconsistent`. `ConservativeFor ev ref` is the contract for cheaper evaluators: inconsistency exactly when the reference is inconsistent, and otherwise the reference answer or `unknown`. `refuse_conservative` and `kleene_conservative` show the refusing evaluator and the Kleene evaluator meet it.

`Lara.Process.WorldView` connects the ordered view to BHL. `testProjection` reads the test events off a BHL world's ordered trace as consecutive ledger increments; `ledgerDeltas_sum` and `testProjection_eq` show they sum to the final ledger whenever ledgers only grow, `traceEdges_chain` shows locally allowed edges only grow it, and `admitted_testProjection` concludes that every admitted world's projection is its multiset `History`. An `AnnotatedWorld` annotates each trace step with its process event and the tests it adds; the annotation must equal the step's ledger increment, put tests only on run events, and form a valid process history. `AnnotatedWorld.tests_sum` shows the annotated tests are exactly the BHL `History`, and `AnnotatedWorld.test_from_run` that every test occurrence comes from a run event of the process history. Whether `ArtifactBinding` should move to the ordered view is a separate decision; nothing here needs it.

`Lara.Examples.ProcessOrder` supplies the fixtures. `omitted_read_unknown` and `complete_access_certain`: a record stating that the plan commit precedes the reported read leaves an unreported earlier read possible, so precommitment is `unknown`, until complete coverage of evaluation reads excludes the violating history and makes it `certainTrue`. `unordered_record_unknown` and `record_order_irrelevant` admit both orders when no constraint is recorded. `contradictory_record_inconsistent` reports contradictory constraints as `inconsistent`. `failed_sibling_counts` keeps a failed sibling run in the family count although it yields no argument. `run_uses_current_version`, `cutoff_excludes_longer` and `refusing_evaluator` exercise versions, the cutoff and the conservative-evaluator contract, and `startAnnotated` inhabits the annotation contract. `history_forgets_precommitment` gives two valid histories with one event multiset that disagree on `RunPrecommitted`. `split_selection_fixture` separates selection on another dataset from selection on the test data.

## What does the statistical layer prove?

`Lara.Process.Statistics` and `Lara.Process.Ledger` follow the exact-rational style of `Lara.BHL.Tests.Binary`: finite carriers, rational masses (`FiniteProbability.Law`) and expectations as finite sums (`expect`). The pinned Mathlib has no Ville inequality and no e-values, p-values or FDR, so every bound is proved directly. A guarantee survives an incomplete ledger only through a bounded quantity: a certified count bound, or an e-process fixed before its data.

| Theorem | Statement |
| --- | --- |
| `markov`, `eventMass_exists_le` | Markov's inequality for an e-value (nonnegative, expectation at most one) and the finite union bound |
| `bonferroni_bounded` | for every completion with `k ≤ K` tests and calibrated null p-values (`IsPValue`, inhabited by `fair_pvalue`), rejecting a null whose p-value is at most `α/K` has probability at most `α` |
| `eBonferroni_bounded` | for every completion with `k ≤ K` tests, any null set and arbitrary dependence, rejecting a null whose e-value reaches `K/α` has probability at most `α` |
| `fdp_le_sum`, `selfConsistent_fdr` | a rejection set in which every rejected e-value reaches `K/(α·|rejected|)` has FDR at most `α·|nulls|/K` |
| `eBH_selfConsistent`, `eBH_bounded` | e-BH run at the bound `K` is self-consistent, and with unreported tests entering as e-value `0` (never rejected) it controls FDR at `α` for every completion with at most `K` tests, even when which tests are reported depends on the outcome; proved directly rather than from Wang–Ramdas Prop. 2, which fixes the family size |
| `stoppedHitProb_le`, `ville_finite`, `ville_crossing` | a nonnegative test supermartingale started at most one is at or above `1/α` at any stopping time within any finite horizon with probability at most `α`, and stopping at the first crossing gives the crossing probability; proved by induction on the horizon, not from Mathlib's `maximal_ineq`, which concerns submartingales |
| `stoppedHitProb_mem_unit` | `stoppedHitProb`, the stopped event's probability computed by conditioning on each next observation, lies in `[0, 1]` |
| `split_selection_valid` | selection on one sample and a calibrated test on the other keep the level when the joint law is the product of the marginals; independence is that explicit premise |
| `warrantedLevel_failClosed`, `warrantedLevel_needs_fwer`, `warrantedLevel_eValue`, `warrantedLevel_pValue` | the warranted level of a ledger (`WithTop ℚ`) is `⊤` when the statistic kind, value, count bound or guarantee is missing, the guarantee is not FWER, or the bound or statistic is not positive; a finite level `a` means an e-value reaches the e-Bonferroni threshold `K/a`, or a p-value is at most the Bonferroni threshold `a/K` |

`onlineLevel` is a wealth-spending online rule, used only to show that online replay needs a complete ordered ledger. `SplitSelection` on a process history is what licenses modeling the selection as a function of the selection sample and the test as a function of the test sample, which is how `split_selection_valid` receives read separation; the product law is a separate premise that no process record supplies.

`Lara.Examples.ProcessStatistics` holds the fixtures and every counterexample twin:

- `evalue_calibrated`, `countBounded_determinate`, `countBounded_rejection_valid`, `warrantsRejection_valid`: a calibrated e-value fixture (score `60` with null mass `1/60`). The bound-adjusted e-Bonferroni rejection at `K̄ = 2` and `α = 1/20` (threshold `40`) is `certainTrue` under an admitted count bound of two. Allowing four tests admits completions with three and four tests, where that rejection is not warranted and the four-test threshold `80` exceeds the score, so the verdict is `unknown`. In every warranted completion e-Bonferroni gives FWER at most `α` under any null law and dependence.
- `partialRecord_unknown_countBounded`: the original BHL conclusion stays `unknown` under a bound of two, because its one-test and two-test completions both satisfy the bound. Its p-value is not reinterpreted as an e-value.
- `optional_stopping_inflation`: a p-value calibrated at `1/2` at a fixed time reaches `1/2` with probability `3/4` under stopping as soon as it crosses. By contrast `likelihoodRatio_martingale` and `likelihoodRatio_ville` give a concrete test martingale whose crossing probability stays within its level.
- `same_data_selection_inflates`, `same_data_identical_record`: selecting between two calibrated analyses on the test data rejects with probability `3/4`, while selecting on an independent coin keeps `1/2`; both worlds can report the same record (which analysis was selected and that it rejected).
- `dependent_split_invalid`: with structurally split reads and distinct dataset identities, but perfectly dependent samples with the same fair marginals, the selected test always rejects; under the product law it keeps its level.
- `online_replay_anticonservative`: replaying the online rule over a ledger missing a non-rejection grants level `1/40` instead of `1/80`, although both ledgers satisfy a count bound of one.
- `mfdr_not_fdr`: an outcome law with mFDR at most `1/10` and FDR `1/2`. It separates the guarantee classes a profile must name; a procedure that guarantees mFDR, as alpha-investing does, is not thereby an FDR procedure. The witness is an outcome law, not a run of alpha-investing itself.
- `eBH_reported_count_unsound`: e-BH run with the reported count one instead of the bound two rejects a null with probability `3/4` at `α = 1/2`.
- `warrantedLevel_fixtures`: the e-value `60` under bound two is warranted at `1/30` and the p-value `1/40` at `1/20`; a missing bound, a zero bound, an FDR guarantee or a missing kind gives `⊤`.

Infinite-horizon Ville and online FDR procedures over complete ledgers (LORD, e-LOND) are not part of this layer.

## How does entitlement survive revision?

`Lara.Process.Revision` sorts every edit into three classes.

| Class | Criterion | Exactness |
| --- | --- | --- |
| Survives by structure | a minimal support avoids the quarantined sources, the edit is outside the claim's argument ancestry, or the recorded reads are unchanged | the quarantine criterion is an iff on the support-only fragment and only necessary with attacks; ancestry locality and trace reuse are sufficient |
| Survives by transport | the edit is a renaming or re-encoding under which warrant is natural | every source renaming and every injective atom re-encoding for derivability; for a source count, exactly the renamings injective on the supplying sources |
| Must be re-established | the edit changes something the derivation read | Lara recomputes the affected region; it never searches for a minimal repair |

| Theorem | Statement |
| --- | --- |
| `Derives.mono`, `not_derives_empty` | support-only derivability (`SupportSystem`, Horn rules over source supplies) is monotone, and nothing is derivable from no supplies when every rule has a premise |
| `quarantine_iff_support` | after quarantining sources `Q`, a claim stays derivable iff some minimal support (`MinimalSupport`, a set of source supplies: an ATMS label environment or why-provenance witness) inside the available supplies has no source in `Q`. On the support-only fragment this is the exact criterion of which `tighten_artifact_warrant_loss` states one direction (a used quarantined leaf loses the selected warrant) for the full bridge |
| `grounded_directional_locality` | if two frameworks contain the same ancestors of `t` and give each the same attackers, `t` has the same grounded label in both |
| `warranted_locality` | warrant is local in the same sense once every other input it reads (artifact check, conclusion, kind, probes, attained guarantee) is preserved too; graph agreement alone is not enough |
| `warranted_natural` | derivability transports along every renaming of sources (`renameSupplies`, `SupportSystem.rename`), injective or not, because no rule compares source identities |
| `derives_reencode`, `derives_reencode_iff` | re-encoding atoms preserves derivations, and for injective re-encodings derivability transports in both directions |
| `corroboration_injective`, `corroboration_preserved_iff` | a renaming preserves the number of distinct sources supplying a claim iff it is injective on those sources |
| `verifying_trace_reuse` | if a check's result depends only on its recorded reads (`RecordsReads`) and every recorded read is unchanged, the stored result is the recomputed one; the hypothesis is complete read recording |
| `version_update_keeps_old`, `revision_withdraws_dependents` | publishing a new dataset version keeps every warrant indexed by the versions it read; declaring a version defective withdraws exactly the warrants that read it |
| `tighten_revision` | over core source edits (`SourceUpdate`), `tighten` is the revision class (`editClass`), and an actual `tighten` of material a support uses leaves no `ArtifactWarrant` |
| `update_keeps_old`, `update_reestablish` | an artifact warrant is indexed by its source snapshot, so applying any update leaves the old-snapshot warrant in place; at the new snapshot warrant must be re-established, and `RebindConditions` suffices (`rebind_warrant`) |

`RebindConditions` requires injective raw and checked index maps. `warranted_natural` and `corroboration_preserved_iff` show that, on the support-only fragment, injectivity is needed exactly where a profile counts sources, which refines that sufficient contract toward a characterization there.

`Lara.Examples.ProcessRevision` holds the witnesses. `quarantine_one_support` and `quarantine_all_supports` exercise the quarantine iff on two independent supports. `support_avoids_but_defeated` shows a support that avoids the quarantine is not enough once attacks exist. `stable_not_directional` adds a self-attacking argument outside the claim's ancestry: every stable extension disappears while the grounded label is unchanged, and `grounded_locality_instance` derives that grounded fact from the general theorem. `failed_sibling_changes_warrant` keeps the lowered arguments, and so every attack edge, unchanged while a failed sibling run flips the e-Bonferroni warrant through the family count. `merge_breaks_corroboration` merges two sources: derivability survives, corroboration halves. `incomplete_reads_unsound` and `complete_reads` separate incomplete from complete read recording. `update_and_revision` keeps an old-version warrant across a new version and withdraws it when the old version is declared defective.

## What crosses the ARA boundary?

`Lara.Process.Bridge` decodes an ARA record, at the boundary, into a symbolic `DecodedRecord`: identified events, precedence constraints and scoped coverage assertions, each carrying the ARA file and entry reference (`SourceRef`) it came from, plus the submitted claims and witnesses. Source references are decode-boundary evidence; the theory only reports them. A coverage assertion carries its evidence and an `AdmissionBasis` (instrumented log, signed attestation or author declaration); a reader states which bases it admits, and an attestation labeled complete does not prove its own reliability.

The ARA side is an `AraSource`: a list of entries in file order, which carries no meaning. `extract` keeps every event entry (failed and sibling trials included) and every ordering entry, admits exactly the coverage attestations with an admitted basis, and never infers order from file position or completeness from absence. `SourceRel` states what it means for a modeled history to be faithfully described by the source; it is the trust boundary, an assumption about the source rather than something the theory checks.

| Part | Theorem |
| --- | --- |
| A1 encoding | `encode_extract`: encoding a decoded record as ARA entries and extracting it is the identity. This is representation consistency only; no round trip reconstructs a unique history from an incomplete record. `extraction_preserves_compatibility`: every history the source faithfully describes stays compatible with the extracted record, so with `extraction_verdict_sound` a certain verdict holds at the generating history, conditional on source fidelity and the admitted bases. `extraction_overapprox_safe`: an extraction admitting a superset of the source-compatible histories can lose certainty but never invents it for a nonempty source-compatible set; `extraction_safe_for_source` is its instance for `extract` and `SourceRel`. |
| A2 conservativity | `coverage_complete_conservative` and `history_independent_verdict` (see the compatible-history core) |
| A3 invariance | `verdict_invariant` and `verdictQ`: verdicts respect equivalence of decoded records (equal compatible sets) and lift to the quotient; `perm_equivalent` and `RecordCoverage.allowed_perm` show reordered events, constraints and attestations give an equivalent record |
| A4 separation | `Separates`, `separation_unknown`, `separates_not_factors`: when a coarsening identifies two histories that disagree on a warrant, the shared coarse record's verdict is `unknown` and no exact evaluator reads the coarse record |

`Lara.Process.Prov` defines one explicit W3C PROV projection, `provGraph`: `used`, `wasAssociatedWith`, plan, `wasGeneratedBy` and invalidation relations, with event order and access purpose omitted. `provGraph_perm` shows it forgets order. It is one specified projection, not a claim that every PROV encoding must erase these distinctions: qualified PROV with timestamps and roles can keep them.

`Lara.Examples.ProcessAdequacy` separates every specified coarsening:

| Coarsening | Witness |
| --- | --- |
| latest-test projection | `latestTest_separates` (the BHL partial record) |
| event multiset, the shape of `History` | `multiset_separates`, `multiset_record_unknown` |
| dropping failed or unreported analyses | `dropFailed_separates` |
| dropping selection-read provenance | `selectionProvenance_separates` |
| collapsing source identities | `collapse_separates`, over source supplies and the two-source corroboration check rather than whole histories |
| dropping retractions | `dropRetractions_separates` |
| the PROV graph | `prov_separates`, with PROV graphs compared as relation sets (`ProvGraph.Equiv`) |

A Hennessy–Milner-style characterization (histories are entitlement-equivalent iff no profile formula separates them) is not proved; the separation table is the adequacy result.

`Lara.Examples.ProcessARA` runs the contract on hand-decoded records with source references and spans. `omitted_read_compatible` and `omitted_read_ara`: the same recorded plan and evaluation are compatible with and without an unrecorded earlier read, so ordering evidence alone leaves precommitment `unknown`. `admitted_coverage_ara`: an admitted instrumented-log attestation of complete evaluation-read coverage makes it `certainTrue`. `declared_coverage_not_admitted`: the same attestation as an author declaration is not admitted. `generating_history_compatible` instantiates preservation, `failed_trial_preserved` keeps a failed sibling through extraction, `contradictory_ara_inconsistent` reports contradictory ordering entries as `inconsistent`, `submission_extracted` keeps every submitted witness, and `reordered_equivalent` shows file order changes no verdict.

## How is the development checked?

- `cd lean && lake build`
- `make process-theory` (runs `lake exe process-examples`, which recomputes every fixture through the shared executable definitions)
- `make local-gates`, which includes the `AxCheck.lean` axiom audit and its coverage check; every public theorem of this layer, countermodels included, has an explicit `#print axioms` row and uses only `propext`, `Classical.choice` and `Quot.sound`. No proof uses `native_decide`.
