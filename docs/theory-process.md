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

## How is the development checked?

- `cd lean && lake build`
- `make process-theory` (runs `lake exe process-examples`, which recomputes every fixture through the shared executable definitions)
- `make local-gates`, which includes the `AxCheck.lean` axiom audit and its coverage check; every public theorem of this layer, countermodels included, has an explicit `#print axioms` row and uses only `propext`, `Classical.choice` and `Quot.sound`. No proof uses `native_decide`.
