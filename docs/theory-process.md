# Research-process semantics: entitlement over incomplete histories

## TL;DR

The research-process layer (`lean/Lara/Process/`, namespace `Lara.Process`) states when a research record *entitles* a claim to be asserted, as opposed to when the claim is true. A record denotes the set of complete modeled histories and reporting choices it could have come from, relative to an explicit model and scoped coverage assumptions; executable verdicts range over a declared finite carrier. A verdict quantifies over that set and is `inconsistent` when it is empty. Claim-level entitlement requires the profile to accept the admitted coverage, the set to be nonempty, and some warrant in every compatible history; auditing a submitted argument requires one fixed witness to warrant in every compatible history. The layer is an outer layer over the core calculus and [BHL](theory-bhl.md) and changes neither. Its separately versioned `process-input 1` format has a Lean reference runner and an independent Haskell library model and codec, with no `.lara` syntax, core wire or corpus change. Its fixtures are finite reference models, and no theorem here is an empirical claim.

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

`Admitted` carries a scoped coverage assertion together with the traces, reported events and policy interpretation that give it meaning, plus any further admitted restriction; `Admitted.assumptions` is the coverage's own restriction conjoined with that extra one, so an accepted coverage assertion is never detached from the compatible set it constrains. `Entitled M P S A r c` requires the profile to accept the admitted coverage and `EntitledBy` over the compatible completions. `ArgumentEntitled M P S A r c w` requires the same with `ArgumentEntitledBy` for the fixed witness `w`. An audit of an ARA submitted argument must use `ArgumentEntitled` with the decoded submitted witness (`DecodedRecord.submitted`); claim-level `Entitled` is never reported as verification of a particular argument. The decoded-record fixtures check extraction of the submission; the audit judgment itself is exercised on the entitlement fixtures and, for BHL bridge histories, by `bridge_argument_audit`.

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
- `mfdr_not_fdr`, `alpha_investing_mfdr_not_fdr`: an outcome law with mFDR at most `1/10` and FDR `1/2` separates the guarantee classes a profile must name, and an actual alpha-investing run exhibits the same gap. With the standard Foster–Stine parameters at `α = 1/10` (initial wealth `α(1-α)`, payout `α`), independent calibrated null p-values (`investing_pvalues`) and a non-monotone policy that respects the wealth rule on every outcome, the run (`investRun`, `invest`) has mFDR `183/2033 ≤ 1/10` and FDR `2663/24000 > 1/10`. The policy stops after a first null rejection, so it is not monotone in past rejections.
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

`Lara.Process.Characterization` gives a Hennessy–Milner characterization. A `TransitionSystem` has labelled steps and atomic predicates; `ProfileFormula`s combine atoms with truth, negation, conjunction and possibility after one labelled step. Two states are `FormulaEquivalent` when no formula separates them; with the warrant, order and statistical predicates an entitlement verdict reads as atoms, this is the entitlement equivalence the adequacy question asks about, but the theorems hold for any atoms and no theorem shows a verdict depends only on these formulas. `bisimilar_formulaEquivalent` gives one direction; for an `ImageFinite` system `formulaEquivalent_isBisimulation` and `formulaEquivalent_iff_bisimilar` give the converse. `processSystem` steps a process history to its valid one-event extensions, which is deterministic and hence image-finite for any alphabet (`processSystem_imageFinite`), so `process_characterization` applies; for such deterministic systems the result is close to the standard theorem. `Lara.Examples.ProcessCharacterization` separates the commit-first and read-first histories by the formula "after the run event, the run is precommitted", although no atom distinguishes them before the run, so they are not bisimilar (`not_bisimilar`, by the easy direction).

`Lara.Examples.ProcessARA` runs the contract on hand-decoded records with source references and spans. `omitted_read_compatible` and `omitted_read_ara`: the same recorded plan and evaluation are compatible with and without an unrecorded earlier read, so ordering evidence alone leaves precommitment `unknown`. `admitted_coverage_ara`: an admitted instrumented-log attestation of complete evaluation-read coverage makes it `certainTrue`. `declared_coverage_not_admitted`: the same attestation as an author declaration is not admitted. `generating_history_compatible` instantiates preservation, `failed_trial_preserved` keeps a failed sibling through extraction, `contradictory_ara_inconsistent` reports contradictory ordering entries as `inconsistent`, `submission_extracted` keeps every submitted witness, and `reordered_equivalent` shows file order changes no verdict.

## What does the inquiry interface provide?

`Lara.Process.Inquiry` is the interface issue #22 builds on; it does not implement #22's procedures. A finite inquiry (`Inquiry`) is a finite family of compatible completions; `Inquiry.ofRecord` builds it from a record's compatibility predicate over a declared finite carrier (`mem_ofRecord`). A claim is `Stable` over it when the family is nonempty and no two completions disagree, which is `determined_iff_no_witness` over the family (`stable_iff_determinate`, and `ofRecord_stable_iff` for a record's inquiry). The `sensitivity` of a claim relative to a reference completion is the set of completions that flip it; `sensitivity_empty_iff_stable` and `mem_sensitivity` characterize it.

Stability is not scientific adequacy, and status is not entitlement. `Lara.Examples.ProcessInquiry` shows both: `stable_not_entitled` has a claim that is true in every completion of a record's inquiry (`leftOnly_completions`), hence stable, that no witness warrants; `status_does_not_transport` keeps the claim's grounded status `justified` in two histories while the submitted argument is entitled on the record of one history and not on the record of the other. `sensitivity_fixture` exhibits the history that flips an unstable audit.

## How does a checked source meet the audit layer?

`Lara.Process.Source` is the proof-retaining source observer the audit layer reads. `checkSource` returns `SourceOutcome input` — an `Except SourceRejection (AcceptedObservation input)` — so a rejected source never acquires a graph, a public status or a warrant. An accepted observation carries the exact `Surface.SourceWithEvidenceAudit` result, replay compatibility, the capture/evidence guard and certificate selection together, and `exact_source`, `exact_audit`, `evidence_admitted` and `certificates_selected` project them; nothing re-runs the checker to recover what it already proved. `Lara.Process.SourceWire` is the source envelope codec, and `SourceDiagnosticWire` with `SourceResultWire` give complete typed codecs for every rejection payload and for `Driver.PublicStatus` and `QueryOutcome`, so the four fault categories (surface, admission, check, evidence) cross the wire with their locations rather than as rendered text.

The Haskell companion is `Lara.Process.Source` with `Source.Types`, `Source.Wire`,
and `Source.Diagnostic.Wire`. Its opaque `SourceInput` and `Fragment` keep authored
ASTs coupled to the original typed opaque certificate payloads. Authored versions
and positions are unbounded signed integers; source lowering rejects negative
certificate versions and attack indices, while policy certificate references use
the reference's nonnegative core conversion.

`Lara.Elaborate.SourceResult` retains one production checker decision: either the
full failure or an opaque `AcceptedSource` containing its source admission state
and `CheckedUnit`. The source observer derives the framework, grounded labels,
blocked overlay, support index and hole coordinates from that retained result.
Modeled capture admission accepts the reference's arbitrary metadata and ordered
JSON values; package metadata validation remains a separate boundary. Original
authored-source guards run after semantic reconstruction and status resolution,
so substitution cannot repair an unsupported original directive, argument or
comparison.

The Haskell `Lara.Process.Audit` and `CheckedMethods` implement the closed support,
association, method and ledger checks. Native method applications retain the
computed finite execution; conditional interpretations do not assert execution.
The audit checks the submitted node itself, so another justified support for the
same query cannot rescue a defeated witness.

`Lara.Process.Enumerate` retains the originating family, bounded completions and
exact history/search counts in an opaque value. It counts guarded products before
allocation and charges live prefixes even when a later empty guard removes every
row. `Lara.Process.Projection.checkFamily` takes that enumeration and its audit
configuration, not a separately replaceable family. It snapshots each completion
once, retains source rejections, and shares stable coordinates, grades, witness
checks and fixed-claim observations across consumers.

Four computations turn an accepted source into warrant data, each stated as an equation against an independently defined reference rather than against a producer label:

- `Lara.Process.SourceCoordinates` lifts the checked framework to stable declaration identities. `graph_label` shows a lifted node's grounded label is the compiled one, and `supports_exact` characterizes a query's support as exactly the checked nodes whose conclusion is `≡` to it.
- `Lara.Process.SourceKinds` computes a node's evidence kind as the meet of its own argument key with every support leaf and method key (`nodeKind`). `nodeKind_no_promotion` is the no-promotion law: a slot key forces `hypothetical` however the node is used. `SourceKindTable` caches the same grades once per family; `lookup_build` equates the cache with `inputKind` plus the conditional meet for every key, with no uniqueness premise, and `lookup_build_no_promotion` / `lookup_build_conditional_cap` carry the two caps through the cache.
- `Lara.Process.SourceProvenance` extracts the authored dependency relation from the authoritative retained reconstruction rather than from core-term coincidence: named references, both discharge forms and unique omitted premises (`ofObservation`, with `direct_source_correspondence` tying the extracted list to an independent syntax-directed derivation). `ordered_*` proves the table is source-ordered and propagates keys along real dependency paths, and `scalar_*` bounds a dependent's meet by the actual leaf, method and prior-argument keys it uses. Because a leaf-root argument and an unrelated argument's explicit rule can share the same core subterm, the fixture pins that the unrelated use stays observed while the dependent on the capped argument does not.
- `Lara.Process.SourceLedger` checks a ledger binding against the modeled history: exact run/family/result membership, a metadata bound that counts every family sibling including failed and resultless ones, and `fwer` only. Soundness and completeness are stated over the independent `LedgerValid` predicate, so a certificate carries the exact count and finite level rather than accepting a desired level as input. Calibration and completeness of the modeled ledger remain assumptions.

`Lara.Process.SourceAudit`, with `SourceAuditSupport` and `SourceAuditAssociation`, is the closed audit specification. A witness declares its source pin, its interpretation, its dependencies, its probed error kinds and either a conditional guarantee or a ledger binding. Support resolution independently infers the declaration and checks query equivalence, retention, the fresh checked node and blocking; claim association additionally requires the exact authored and semantic formal query, the authoritative reconstructed pair at the selected index and membership in the claim-alternative ledger; a checked BHL method binding runs the real `BHL.checkBridgeNative` and `checkMethod_sound` extracts the actual `ArtifactMeaning`. Conditional guarantees are capped at `conditional` kind (`conditionalKeys`) and levels outside `[0,1]` are refused, and the config's own assumption list is exactly the reader's admission — the basis it reports is not a second filter. Fail-closed metadata is explicit: `observeWitnesses_ambiguous` reports `ambiguousMetadata` for every row when claim, witness, source/key or assumption metadata is duplicated, and `warranted_source_witness` traces a positive warrant back to a real `checkWitness` certificate over the actual source.

`Lara.Process.SourceModel` and `Lara.Process.FamilyAudit` assemble those fields into the total model. `prepare` computes one `Snapshot` per completion — the checked outcome, the carrier coordinates, the graded node table — and `rowModel` is the resulting `WarrantModel` over rows: the profile graph (`profile_graph_exact`), the per-node kind, the concluded claim, the probed set, the attained guarantee and the artifact check. `warranted_iff` relates the executable `warranted` to `Warranted`, `rejected_not_warranted` and `incomplete_not_warranted` pin the two fail-closed cases, `prepare_complete_all_nodes` shows completeness requires every node's grade, and `warranted_source_witness` links an affirmative audit to a genuine source certificate. `audit` quantifies the fixed witness over the guarded product in the frozen order — nonempty family, every coverage assertion accepted, `Warranted` in every row — and `audit_iff` proves it equal to `ProductAuditHolds`, with `no_slots_audit_iff` specialising to the existing `Universe.AuditHolds` when a family has no slots; `Lara.Process.Enumerate.searchFamily_perm` is the proved equality that ties the caller-supplied completion list to `Family.referenceFamily`, so an audit is about the declared family and not about whatever rows were passed. `Lara.Process.Family` supplies the fragments, slots and guarded product (`selectedDecls`, `materialize`, `referenceFamily`) with `FamilyWire` and `InquiryProcessWire` as their contextual codecs.

The boundary is unchanged by any of this: no theorem turns a producer's kind label into an observation. An `observed` grade requires an explicitly reader-admitted `CaptureAssumption` with exact source and process bindings, the audit is conditional on the assumptions a result prints, and an audit over a family containing a rejected source is false (`audit_rejection_fails`). The standalone version-1 `process-input 1` runner remains Lean-only and refuses a submitted-witness audit as `unsupported`; the native checked-inquiry wrapper consumes this boundary through its own entry point.

## What do the exact inquiry analyses compute?

`Lara.Process.Analysis` answers three questions about one enumerated, checked family, and it answers all of them from a single projection rather than by asking the checker again. `Lara.Process.Source.checkFamily` runs `checkSource` once per completion and prepares its row; the observable entry points project that view once into `statusObservations` or `auditObservations` — a completion-to-observation table read by `tableRead` — and every later fact is a lookup or a structural law about that table, so a query costs one observation pass plus its own enumeration rather than a checker run per compared pair.

An observable is the public status of a claim at its frozen atom or an audit of a submitted witness under a profile. A row is either a rejection reason or an accepted value, and an accepted value is a `Driver.PublicStatus` with the conditional label retained inside `evidenceBlocked`. Rejected rows are first-class members: they are counted, they are bucketed by reason (`buckets_closed`, `buckets_covers`, `buckets_disjoint`), and they carry no public status.

Stability is whole-outcome: nonempty and the same observation on every pair of rows (`WholeStable`, `wholeStableB_iff`). Accepted-only stability is reported separately, with an explicit accepted domain and a rejection count, and is never substituted for the whole-family answer; an all-rejected family can be outcome-stable while having no accepted status (`acceptedStableB_of_all_rejected`), and the empty family is inconsistent (`not_wholeStable_nil`). `wholeStable_iff_positions` and `sensitivity_empty_iff_inquiry` tie the Boolean forms to the landed `Inquiry.Stable` and `Inquiry.sensitivity` instead of restating them.

Sensitivity is relative to a named reference completion that must be in the family. Changed-slot sensitivity holds the history fixed and computes exactly the slots whose choice differs from the reference (`changedSlots`, `mem_differingRows`). Joint sensitivity returns *every* inclusion-minimal nonempty change set that admits a flip, proved inclusion-minimal and complete (`SlotMinimal`, `minimalSlotSets_sound`, `minimalSlotSets_complete`), each paired with a realizing row (`realizing_spec`); the singleton case is `singleton_minimal_iff`. Minimality is decided from the immediate removals alone, which the module's own monotonicity lemma shows is equivalent and which avoids re-enumerating every sub-change-set.

Minimal conditional assumptions use a finite user-declared catalog of literals — slot equality or inequality, event presence or absence, event precedence, or a process formula and its negation. Each subset restricts the original family, must leave it nonempty, and must carry the requested accepted status or positive submitted-witness audit on every remaining row with no rejections (`Satisfies`, `satisfied_no_rejection`). Every subset-minimal satisfying set is returned, with an immediate-deletion countercompletion for each literal removed (`minimalAssumptions_sound`, `minimalAssumptions_complete`, `deletion_fails`, `deletion_witness`); inconsistent and contradictory restrictions certify nothing, and the empty set is minimal exactly when the whole family already satisfies the target (`minimalAssumptions_empty_mem`). `Lara.Process.Analysis.AnalysisWire` gives these records canonical codecs, one closed `Tag` table with the usual spelling and parser laws and decode-success re-encoding.

None of this is a statement about truth, calibration or entitlement transfer: the analyses are conditional on the printed assumptions and on the declared finite family, the enumerations are exponential in the catalog and product, and the caps below refuse the whole inquiry rather than returning a partial answer.

The Haskell `Lara.Process.Analysis` reads the same retained `CheckedFamily` rows.
`AnalysisWire` provides the observable, target, literal and finite-result codecs.
Wrapper profiles use bare evidence/coverage/probe lists and retain a zero
denominator's reference meaning; the embedded process profile codec keeps its
tagged lists and positive-denominator requirement.
Native sensitivity derives inclusion-minimal sets from the retained same-history
differing rows rather than enumerating every subset of the declared slots.
Sets retain the reference's subsequence order and first realizing completion.
If a differing row has no changed slot identity, the reference's nonempty
minimality rule yields every universe singleton.

## What does graph-difference locality prove?

`Lara.Process.Locality` decides whether an edit could have changed a grounded label, and proves that its decision is sound. It compares two actually checked sources after lifting both compiled frameworks to a common declaration-identity carrier (`sharedCarrier`, `claimOf`, `querySupport_exact` reusing `Coordinates.supports_exact`). It then builds the symmetric difference of node membership and of compiled incoming edges (`nodeDiff`, `edgeDiff`, with `mem_nodeDiff` and `mem_edgeDiff`), computes the backward ancestry of the queried claim's complete support in both graphs, and requires that the two supports correspond and that no changed node or changed incoming edge reaches that combined region (`LocalityClaim`, `Contained`, `supportCorresponds`, `correlates`, `accepted_iff`, `checkLocality`, `checkLocality_accepts_iff`).

What makes the test sound is an implication, not a definition: `Certificate.locality_premises` states the three hypotheses of the existing core lemma `Lara.Process.grounded_directional_locality` — the queried argument is present, every ancestor in the old graph is present in the new one, and each ancestor has exactly the same attackers in both — and `Certificate.label_eq` is that lemma applied to them. No label equality is assumed anywhere, and `Certificate.status_eq` lifts the per-support label equality to complete-claim status equality under exact support correspondence. `checked_status_eq` is the capstone over two real checked runs, and `checked_certificate_of_accepts` turns an accepted certificate into it.

The comparison uses the compiled closure edges (`Compile.edgeB`/`checkedAF`), not the authored raw attacks, because rebut, undermine and undercut propagate through premise and discharge occurrences: the discharge fixture shows one undermine attack producing two closure edges, onto the discharged occurrence and onto the wrapper that discharges it. New attackers are checked in the target graph; reachability in the old graph alone is unsound, and a fresh declaration name or a disjoint leaf set proves nothing. The fixtures refute both weaker criteria explicitly (`nodeDiffDisjoint`, `edgeDiffInternal`, `oldRegionCriterion`, refuted in `Lara.Examples.ProcessLocality`), and cover a new attacker outside the old graph, a node deletion, a hole becoming complete support, and an unrelated self-attack.

A successful test is sufficient, not necessary: changes inside the region can cancel, so a failed test does not imply a changed label. The fixtures pin that scope with a case whose test fails while both statuses stay `justified`. Reindexing invariance and pure declaration permutation invariance hold with the query atom held fixed (`iso_of_same_carrier`, `labelC_of_same_carrier`, `statusC_of_same_carrier`, `isoCheck_iff`, `graph_label_reindex`). The result is **grounded-semantics locality only**: no stable, preferred or other extension-semantics claim follows, and a fixture shows an edit that destroys a stable-credulous property while the grounded label is unchanged. `Lara.Process.Ancestry`, added to `Lara.Process.Revision`, supplies the finite ancestor iteration that `Locality` builds on.

## How is an edit's impact certified?

`Lara.Process.Impact` compares two complete source snapshots and issues a certificate that a verifier recomputes from the inputs alone. A comparison records both inputs, their replay and backend identities, both exact checker outcomes, the queried atoms, the per-endpoint reference, checked and compiled carriers, the blocked closure, per-query support maps, the graph difference and the checked locality facts (`EndpointReport`). Rejected-to-accepted, accepted-to-rejected and rejected-to-rejected are first-class transitions of the same shape as accepted-to-accepted, and a rejected endpoint carries its exact rejection payload and no status at all — nothing is invented for it.

For two accepted endpoints, every requested full public status is computed with `BHL.ordinaryStatus`, and the queries are partitioned into changed and unchanged. The partition is over the whole `Driver.PublicStatus`, so two blocked results with different conditional labels are `changed` (`evidenceBlocked_conditional_changed`) and the changed conditional diagnostic is retained; equality of `Update.PublicReport` is never substituted, and `ordinaryStatus_eq_of_certificate` derives status equality from a locality certificate via `statusC` equality plus equal blocking.

The certificate's dependency evidence is a closed read inventory. `ReadKey` names the material a status calculation actually reads — leaf contents and metadata, rule and admission lookups including absent ones, duplicate-group membership and conflicts, raw endpoint resolution and retention, signature, policy contraries and substitution, backend theory/digest/certificate inputs, premise and discharge subterms, normalized conclusion-to-query equivalence, complete support and hole membership, the reference/checked/compiled carriers, the blocked closure and the compiled attack edges — and `ReadKey.Val` gives each key its exact value type, with `decode`/`accepts` and `inputReading_accepts` proving the canonical reading is well-typed for every key. Reads are tagged with the endpoint they belong to (`Side`), so `impactReads` is a set of side-tagged key-value triples and one key has exactly one value per side (`impactReads_functional`); the reference, checked and compiled carriers keep their distinct meanings.

Proved coverage backs that inventory. `recordsReads_labelC` and `recordsReads_statusC` show the grounded label and status are determined by their small footprints, exactly the compiled carrier plus the ancestry attack rows, and `impactReads_covers_status`/`_after` prove every key of every queried footprint is recorded under its side. The reused run-level calculations — `Source.checkSource`'s outcome record, `BHL.ordinaryStatus`'s public-status row, `Update.blockedQueriesForRun` and `transitionOf` — are each covered by a `RecordsReads` instance over the finite whole-input key space, which is the conservative whole-input fallback the plan allows where a smaller footprint is not justified; `impactReads_determines_statusRow` then proves that any environment agreeing with the recorded reads reproduces both endpoints' public-status rows. `Support.certDeps` is never used as a dependency footprint, because it only reports backend acceptance dependencies.

`verifyImpact` reruns the shared observer on both supplied inputs and recomputes every certificate field, returning `verified` or an `invalid-certificate` with a closed fault. `verified_iff_verifyImpact_true` states the equivalence, `verifyImpact_verified_*` exposes what a verified certificate asserts (binding, transition, rows, partition, graph, locality, reads, impact, result), the `verifyImpact_false*` theorems show a fault cannot be produced without its condition, and `firstFault_some_iff` gives the converse, so a fault fires exactly for its condition. A well-formed but false certificate is a result, not a refusal. Finally, the impact layer deliberately does not transport entitlement: `no_entitlement_from_public_status` is the standing theorem that equal public status proves nothing about warrant, and `impact_records_distinction` records that a failed sibling can leave the graph and the public status equal while the audit's count or guarantee changes.

The Haskell `Lara.Process.Impact` retains each endpoint's production checker
outcome in an opaque `Endpoint`, then shares a `Comparison` across result,
certificate, read-count and verification consumers. Verification uses the supplied
endpoints and the certificate's query list, not its untrusted embedded source
fields. `ResultWire` decodes complete false certificates as data. Read triples
retain wire order and duplicates; verification accepts reordered or repeated
identical triples but rejects missing keys, conflicting values and wrong-shaped
values. `Locality` keeps endpoint-compact read coordinates separate from the
shared declaration-identity coordinates used for graph differences.

## What does the `process-input 1` contract fix?

`process-input 1` is the outer document that states a process question outside Lean; `process-result 1` and `process-error 1` are its answers. They are versioned separately from `lara-core@0.3`, like `lara-map@1` and `pw-run 1`. Their Lean modules are `Lara.Process.Universe` (the carrier, queries and answers), `Lara.Process.Rename` (identifier renaming), `Lara.Process.Wire` (the codec) and `Lara.Process.Run` (evaluation and envelopes); `lake exe process-run FILE` is the reference runner, and it remains a history-only runner that refuses an audit. The wrapper described below is a second, separately versioned entry point, not a reinterpretation of this one. The Haskell modules `Lara.Process.Types`, `Lara.Process.History`, and `Lara.Process.Wire` provide the independent symbolic model, transitions, scoped compatibility, finite verdicts, and embedded input codec. There is no standalone Haskell process command.

### Grammar

One top-level form, printed by the canonical `Lara.Driver` printer:

```text
(process-input 1
  (names (event NAME...) (actor NAME...) (plan NAME...) (run NAME...) (claim NAME...)
         (source NAME...) (data NAME...) (family NAME...) (witness NAME...))
  (record (cutoff N) ENTRY...)
  (reader BASIS...)
  (universe (event NAME BODY)...)
  (limits (events N) (completions N))
  (queries QUERY...))

ENTRY   := (event NAME BODY REF) | (order NAME NAME REF)
         | (coverage COVERAGE REF BASIS) | (submit CLAIM WITNESS)
BODY    := (commit-plan ACTOR PLAN V) | (access ACTOR DATA selection|evaluation)
         | (run RUN PLAN V (inputs (input DATA V)...) FAMILY) | (result RUN N)
         | (assert CLAIM WITNESS) | (retract SOURCE) | (update-data DATA V)
REF     := (at FILE ENTRY) | (at FILE ENTRY START END)
COVERAGE:= (complete SCOPE) | (count-bounded SCOPE N) | (open-world SCOPE)
SCOPE   := (scope (kinds KIND...) (cutoff N) [(family FAMILY)] [(actors ACTOR...)] [(data DATA...)])
QUERY   := (verdict LABEL FORMULA) | (audit LABEL CLAIM WITNESS PROFILE)
FORMULA := (run-precommitted RUN) | (predictable) | (split-selection (DATA...) (DATA...))
         | (family-count-at-most FAMILY N) | (not F) | (and F F) | (or F F)
PROFILE := (profile (admissible EVIDENCE...) (accepts complete|count-bounded|open-world...)
                    (guarantee fwer|fdr|mfdr NUM DEN) (probes ERROR...) (acceptance grounded-justified))
```

Every fixed vocabulary (event kinds, purposes, admission bases, evidence and error kinds, guarantee classes, verdicts, refusal tags and the structural keywords) has one spelling table in `Lara.Process.Wire`, and each table is injective. Names are interned per namespace to their position in the `names` block; an undeclared or duplicated name is refused. Versions `V` and counts `N` are canonical decimals, never interned, because `ProcessState.version` reads an unupdated dataset as version `0`. The scope clauses are optional but ordered. `FILE`, `ENTRY` and `LABEL` are report strings the semantics never reads. A `declared-policy` coverage form is refused as `unsupported`: version 1 interprets no reporting policy.

`decodeDocument_canonical` proves the decoder loses nothing: every accepted document re-encodes to the exact S-expression it came from, so `decode_encode` holds for every decodable document. Text reading and printing reuse `Lara.Driver` and are tested, not proved.

### What does a document mean?

A document denotes a `Problem`: the record `extract` produces under the reader's admitted bases, and the declared universe of events that may have happened unrecorded. Its completions are exactly the duplicate-free histories compatible with the extracted record that contain only recorded or universe events (`mem_completions`). That set is finite by construction, which supplies the carrier `verdict` needs, and over the candidate carrier the reported verdict is the landed `verdict` of the record's compatibility predicate (`answerVerdict_eq_verdict`), so the wire adds no second semantics. Declaring the universe is a modeling assumption: an empty universe asserts that nothing unrecorded happened, and enlarging it can only lose certainty (`completions_mono`, `certain_antitone_universe`). The universe carrier reads the record's events as the reported ones, as `DecodedRecord.Compatible` does; there is no separate reporting choice, so selective reporting must be stated as a coverage assertion.

A `verdict` query answers with the exact supervaluation verdict, the number of completions and, for `unknown`, one completion where the formula holds and one where it fails (`answer_witnesses`). The Kleene evaluator is sound but weaker (`kleene_incomplete`) and is not reported. An `audit` means `AuditHolds`: the profile accepts every admitted coverage assertion (open-world coverage when none is admitted) and the submitted witness warrants the claim in every completion (`auditHolds_iff`). Warrant needs each completion's argumentation framework from a checked Lara source, which the checked-source boundary above supplies; the version-1 runner still refuses a submitted-witness audit as `unsupported`, and an audit of a witness the record does not submit as `malformed`.

Positions in the `names` block cannot matter. For one injective renaming per namespace, `step_rename` and `validThrough_rename` commute the transition relation with renaming, `compatible_rename` preserves record compatibility, `completions_rename` maps the completion set, and `answer_rename` keeps every verdict and count while renaming the witnesses.

### Results, refusals and limits

```text
(process-result 1
  (assumptions (universe (event NAME BODY)...) (admitted (coverage ...)...)
               (unadmitted (coverage ...)...) (limits (events N) (completions N)))
  (answers (answer LABEL VERDICT (completions N) [(holds (history NAME...)) (fails (history NAME...))])...))

(process-error 1 TAG DETAIL)
```

Every verdict is conditional on the printed universe, admitted coverage and limits; unadmitted attestations are reported and never applied. `TAG` is `syntax`, `malformed`, `unsupported-version`, `unsupported`, `limit-exceeded`, `usage` or `io`; consumers branch on the tag only. The exit code is 0 for a result, 1 for `unsupported` and `limit-exceeded`, and 2 otherwise; stderr stays empty.

The reference enumerator interleaves the recorded events with each sublist of the universe and is exponential in the event count. A document's `limits` are capped by the checker's ceilings `maxProcessEvents = 8` and `maxProcessCompletions = 10000`, which no document can raise; P2 may raise the event ceiling once a faster generator is proved equal to this one. Evaluation fails closed: too many events or completions, or any audit, yields a refusal and no verdict at all (`run_eventLimit`, `run_completionLimit`, `run_audit`). An accepted document's answers are exactly `answer` of its problem, one per verdict query in order (`run_answers`), so every theorem above applies to what the runner prints.

`Lara.Examples.ProcessWire` checks the carrier on the decoded ARA records of `Lara.Examples.ProcessARA` by kernel `decide`: `omitted_read_universe` (with an unrecorded earlier read possible, precommitment is `unknown`, holding on the committed-first history and failing on the early-read one), `admitted_coverage_universe`, `declared_coverage_universe`, `contradictory_universe`, and `empty_universe_certain` (the same record over an empty universe is `certainTrue`). The fixtures in `fixtures/process/run/` spell the same records as wire documents, add identifier-renaming, entry-reordering and failed-sibling documents, and include one refused document per refusal path; `scripts/check-process-run.sh` compares `process-run` with their goldens byte for byte and checks each exit code.

## What does the inquiry wrapper add?

The checked-inquiry wrapper is a second, separately versioned entry point; it leaves `process-input 1` and its runner untouched. `inquiry-input 1` embeds a complete `process-input 1` document, a base source, guarded slots whose choices carry source fragments, the fixed claim bindings and witness audit specifications, the kind metadata, the reader-admitted capture assumptions, a finite assumption catalog, per-document inquiry limits and a list of requests. Each request is one of `status`, `audit`, `stable`, `sensitivity`, `slots-sensitive`, `minimal-assumptions`, `impact` or `verify-impact`, carrying its label; an observable is a fixed-atom claim status or a submitted-witness audit, and a target adds the expected status or a positive audit. Nothing in the language can name a caller-supplied framework, status function or witness chooser.

`Lara.Process.InquiryWire` is the codec. It has one closed `Tag` table with the usual spelling and parser laws, exact arity and strict canonical naturals, decode-success re-encoding on the public entry points and unconditional round trips for type-level data; contextual forms borrow the existing `UniqueNames` bound rather than inventing a second one. It reuses the stage codecs — the embedded process document, the source envelope, slots and fragments, the audit configuration, observables, targets, literals and the P3 result records — so each fixed vocabulary keeps one spelling owner, and it adds the nested codecs the wrapper owns, including the impact certificate and the verification result, which are pure data and round-trip unconditionally. Slot, choice and argument identities are interned in their own namespace and are renameable, while the embedded process names stay independently interned. The version is checked strictly: anything but version 1 is refused, not silently accepted.

`Lara.Process.InquiryRun` is the reference semantics and the bounded runner. The reference side projects one `checkFamily` per family, so the checker runs once per completion and every request reads the shared projection. The runner threads a single budget through enumeration, observation and each dispatched request and returns a refusal instead of a partial answer; `runBounded_eq_reference` proves a successful bounded result equals the reference result, and every cap has an exact-at-cap and a cap-plus-one lemma (`checkBudgets_at_cap_*` / `checkBudgets_cap_plus_one_*`, `family_at_cap`, `family_histories_cap_plus_one`, `family_steps_cap_plus_one`, `family_sources_cap_plus_one`). Product and powerset bounds are allocation guards only, so a loose declared bound never refuses a guarded family that fits the actual counters. Embedded verdict queries are emitted first in their original order and wrapper requests after them, with labels required to be unique across the two lists, history-verdict results tagged separately from source-family results, and the unguarded history count kept distinct from the guarded source count.

The native Haskell door is `lara inquiry FILE`. `Lara.Process.Inquiry.Types`
defines the typed input, request, result and refusal records.
`Lara.Process.Inquiry.Wire` exposes `parseInquiryInputBS` / `encodeInquiryInput`,
`parseInquiryResult` / `encodeInquiryResult`, and
`parseInquiryError` / `encodeInquiryError`. Result codecs take the embedded
document's `Names`; error codecs need no namespace table. Public decoders enforce
exact envelope versions, canonical contextual forms and constructor shapes,
and distinguish unsupported versions, malformed envelopes and wrong envelope kinds.
`Lara.Process.Inquiry.Run` exposes
`runBounded :: InquiryInput -> Natural -> Either RunRefusal [InquiryResult]`,
`runInquiryFile` and `exitCodeOf`. It retains one checked family for all family
requests and reuses observed impact endpoints for pair accounting and dispatch.
Unresolved impact claim bindings are malformed refusals after budget, label and
reference checks; the reference's inert query contributes only to private
prevalidation accounting and cannot become an accepted result.

The CLI reads strict bytes and validates the entire file as UTF-8 before parsing,
including comments and trailing bytes. Read failures and invalid UTF-8 produce
`io "cannot read PATH"` with the original path. Every argument list beginning
with `inquiry` uses this stdout-only boundary; missing or extra arguments report
`usage "usage: lara inquiry FILE"`. The shared reader keeps legacy diagnostics
unchanged and uses the reference's singleton-character spelling for inquiry
syntax errors.

All output is rendered before emission. Success prints one LF-terminated
`inquiry-result 1` per embedded query, then per wrapper request; no queries or
requests means zero stdout bytes. Refusal prints exactly one LF-terminated
`inquiry-error 1`, with no preceding results. Stderr stays empty. Success,
including an invalid-certificate result, exits 0; unsupported or limit refusals
exit 1; other refusals exit 2.

`source-bytes` counts the original file's UTF-8 bytes, including whitespace and
multibyte characters. The executable passes that count to `runBounded`.
Lean typed callers without a file use `actualOf input .sourceBytes`, the canonical
encoding's UTF-8 size. Native typed callers supply the byte count explicitly.
`runBounded_sourceBytes_limit` proves an oversize input
is refused before source checking (after the embedded event-bound check).
`scripts/check_inquiry_bytes.py` exercises exact-cap and cap-plus-one inputs
with ASCII, extra whitespace and multibyte text through the real executable.

Before allocating family rows, `Enumerate.familyCount` counts guard-surviving
choices per slot and accumulates product sizes across bounded histories,
saturating at `sources + 1` (using the effective, ceiling-clamped cap).
An over-cap product reports that first excess rather than constructing the
complete product to report its size. Empty choice lists prune the suffix;
nonempty lists share the computed suffix. The count equals the capped reference
family length, and every expanded suffix is bounded by its enclosing product.
The runner reuses the bounded rows for accounting and checks source and subset
allocation limits before materialization and subset comparisons.
`scripts/check_inquiry_products.py` exercises large products with tiny caps,
exact-cap boundaries and early/late empty guards, with a timeout on each CLI
invocation. Logical search-step charges still apply when late guards eliminate
every final row.

Each declared inquiry limit is clamped to its fixed checker ceiling. Equality
at the effective cap is accepted. The counters measure the following work:

| Counter | Fixed ceiling | Charged work |
| --- | ---: | --- |
| `histories` | 10000 | Distinct unguarded history completions, also clamped by the embedded document's completion limit |
| `sources` | 10000 | Actual guard-surviving family rows, including rejected sources, plus two endpoints per `impact` or `verify-impact` request |
| `source-bytes` | 1048576 | Original input UTF-8 bytes, including whitespace and comments |
| `declarations` | 10000 | Aggregate declarations in materialized family rows, plus both endpoint declaration counts for each impact request |
| `search-steps` | 200000 | Full history DFS visits plus logical slot extensions, including prefixes whose later guard leaves zero rows |
| `pairs` | 4096 | Family rows per ordinary wrapper request; sum of surviving rows over all catalog subsets per `minimal-assumptions` request; twice the original query-list length plus the distinct side-tagged read-key count per impact request |
| `subsets` | 4096 | Sum of `2 ^ length (dedupLast catalog)` over all `minimal-assumptions` requests |

For `verify-impact`, the query list used in pair accounting comes from the
certificate, but the supplied request endpoints are authoritative. Duplicate
queries still count in the original list length. The embedded event bound is
separate: it is the minimum of its declared event limit and 8, and exceeding it
reports a `histories` refusal with the event count and effective event cap.

After input decoding, refusal priority is fixed:

1. Check the embedded event bound, then the original source-byte count.
2. Enumerate the family: check full history DFS steps, distinct histories,
   then guarded products. Product counting saturates at the effective source
   cap plus one.
3. Check cheap source and subset allocation counts, in that order.
4. Check remaining counters in order: source bytes, declarations, pairs,
   subsets, sources, then combined history-and-slot search steps.
5. Reject duplicate result labels across embedded queries and wrapper requests,
   then unresolved or out-of-family sensitivity references, then unresolved
   impact claim bindings.
6. Build the shared checked-family projection and dispatch requests.

Budget refusals therefore precede label, reference and binding failures.
For example, the private accounting placeholder for a missing impact binding
can yield a `pairs` count of 18 before the binding is reported malformed.
It is not a public empty-atom fallback.

Compatibility with the old entry point is a theorem, not an assumption: `embeddedVerdicts_eq_p0` and `embedded_verdict_bytes_eq_p0` state that a slotless wrapper document's embedded verdicts and their bytes agree with P0's own `answer`, and `p0_run_answers_preserved` and `p0_run_audit_preserved` pin that the old runner's verdict list and its audit refusal are unchanged. New-runner witnesses carry membership proofs rather than byte equality with P0 witnesses. A `verify-impact` request decodes a typed certificate, reruns the shared observer on both sources and returns the labelled `VerificationResult`; `verifyCertificate_verified_iff` proves its `verified` case equivalent to `verifyImpactBool = true`, a false claim returns `invalid-certificate` with the closed fault, and a malformed wire certificate is an outer refusal. Exit codes are 0 for a result, 1 for `unsupported` and `limit`, and 2 for every other refusal, with empty stderr on the success path.

`lake exe inquiry-run FILE` is the reference runner and `lake exe inquiry-examples` recomputes a built-in suite; `fixtures/process/inquiry/` holds one executable document per acceptance row with its `.expected` golden, and `scripts/check-inquiry-run.sh` compares stdout, stderr and exit codes byte for byte (`UPDATE=1` rewrites the goldens). `make process-theory` runs both the old process gates and this one.

`make inquiry-conformance` runs `scripts/check-inquiry-conformance.py`. It builds
each native Haskell and Lean inquiry driver once, then invokes the binaries
directly. It discovers every inquiry fixture and checks each driver's raw
stdout, exit code and empty stderr independently against the unchanged golden.
Generated cases have independent expected outcomes, so driver agreement alone
cannot pass the gate. The sole intended CLI usage difference is
`usage: lara inquiry FILE` versus `usage: inquiry-run FILE`.

The gate sends original inputs and actual captured outputs through the public
Haskell consumer codecs using `scripts/inquiry-codec-client.hs`, including the
temporary byte/product boundary inputs. Generated cases pin allocation guards,
shared counters and refusal precedence, full certificate faults and read-value
validation, empty output, reader depth, UTF-8 and locale-independent paths.
A missing fixture/golden partner, empty process fixture family, nested or unowned
process fixture, spawn failure, signal or timeout fails the gate. Driver and
product invocations have a 10-second timeout. Boundary scripts retain their
Lean defaults and accept a complete driver command plus an optional consumer
observer. Temporary cases are removed when the gate exits; there is no
golden-update mode.

This target is part of `make cross-check`, hence `make local-gates`.
`make process-theory` remains the Lean reference gate. Neither required GitHub
workflow nor the optional Lean workflow runs the inquiry conformance target;
the guarantee is the local pre-review procedure described in
[CI and local gates](implementation.md#ci-and-local-gates).
These finite checks provide conformance evidence. Soundness comes from the
mechanized theorems; the gate establishes no performance or scientific-discovery
claim.

## How is the development checked?

- `cd lean && lake build`
- `make process-theory` runs `lake exe process-examples`. It recomputes every fixture through the shared executable definitions, including the decoded-record bridge, and fails on the first disagreement. Each ARA verdict is printed with its model, query, admitted coverage and admission bases, unadmitted attestations, submitted claims and witnesses, and the source reference and span of every decoded fact. Every other contract fixture (the BHL partial record under a count bound of two, the e-value under bounds two and four, the different-witness entitlement with the profile read from its value, dependent samples, the failed sibling, retraction and version change) is printed with its model, query, assumptions, profile, claim and witness, and a note that it is hand-modeled rather than decoded.
- `make process-theory` then runs `scripts/check-process-run.sh`, which compares `lake exe process-run` with every golden in `fixtures/process/run/` and checks exit codes and empty stderr; `UPDATE=1` rewrites the goldens.
- `make process-theory` also runs `lake exe inquiry-examples` and `scripts/check-inquiry-run.sh`, which compares `lake exe inquiry-run` with every golden in `fixtures/process/inquiry/` and checks exit codes and empty stderr on the same terms. The two legs are independent: neither rewrites the other's goldens.
- `make local-gates`, which includes the `AxCheck.lean` axiom audit and its coverage check; every public theorem of this layer, countermodels included, has an explicit `#print axioms` row and uses only `propext`, `Classical.choice` and `Quot.sound`. No proof uses `native_decide`.
