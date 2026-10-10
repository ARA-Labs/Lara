# Research-process semantics: entitlement over incomplete histories

## TL;DR

The research-process layer (`lean/Lara/Process/`, namespace `Lara.Process`) states when a research record *entitles* a claim to be asserted, as opposed to when the claim is true. A record denotes the set of complete modeled histories and reporting choices it could have come from, relative to an explicit model and scoped coverage assumptions; executable verdicts range over a declared finite carrier. A verdict quantifies over that set and is `inconsistent` when it is empty. Claim-level entitlement requires the set to be nonempty and some warrant in every compatible history; auditing a submitted argument requires one fixed witness to warrant in every compatible history. The layer is an outer layer over the core calculus and [BHL](theory-bhl.md) and changes neither. It adds no wire format, `.lara` syntax, Haskell checker or corpus change.

## What are the boundaries?

Entitlement is non-factive and separate from every existing judgment. It implies neither the claim's truth nor BHL knowledge of it, and an unchanged public status does not transport it. There is no coercion between this layer's verdicts and the core's statuses or BHL's modalities; every translation states its hypotheses and proves preservation.

`Lara.BHL.HistoryCoverage` keeps its single constructor `completeModeled`. The omission models of this layer live in the separate type `RecordCoverage`, and `coverage_complete_conservative` relates the two. `Lara.BHL.History` stays a multiset; ordered process histories are a separate view.

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

## How is the development checked?

- `cd lean && lake build`
- `make process-theory` (runs `lake exe process-examples`, which recomputes every fixture through the shared executable definitions)
- `make local-gates`, which includes the `AxCheck.lean` axiom audit and its coverage check; every public theorem of this layer, countermodels included, has an explicit `#print axioms` row and uses only `propext`, `Classical.choice` and `Quot.sound`. No proof uses `native_decide`.
