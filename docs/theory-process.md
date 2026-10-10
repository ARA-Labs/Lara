# Research-process semantics: entitlement over incomplete histories

## TL;DR

The research-process layer (`lean/Lara/Process/`, namespace `Lara.Process`) states when a research record *entitles* a claim to be asserted, as opposed to when the claim is true. A record denotes the set of complete modeled histories and reporting choices it could have come from, relative to an explicit model and scoped coverage assumptions; executable verdicts range over a declared finite carrier. A verdict quantifies over that set and is `inconsistent` when it is empty. Claim-level entitlement requires the set to be nonempty and some warrant in every compatible history; auditing a submitted argument requires one fixed witness to warrant in every compatible history. The layer is an outer layer over the core calculus and [BHL](theory-bhl.md) and changes neither. It adds no wire format, `.lara` syntax, Haskell checker or corpus change.

## What are the boundaries?

Entitlement is non-factive and separate from every existing judgment. It implies neither the claim's truth nor BHL knowledge of it, and an unchanged public status does not transport it. There is no coercion between this layer's verdicts and the core's statuses or BHL's modalities; every translation states its hypotheses and proves preservation.

`Lara.BHL.HistoryCoverage` keeps its single constructor `completeModeled`. The omission models of this layer live in the separate type `RecordCoverage`. `Lara.BHL.History` stays a multiset; ordered process histories are a separate view.

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

## How is the development checked?

- `cd lean && lake build`
- `make process-theory` (runs `lake exe process-examples`, which recomputes every fixture through the shared executable definitions)
- `make local-gates`, which includes the `AxCheck.lean` axiom audit and its coverage check; every public theorem of this layer, countermodels included, has an explicit `#print axioms` row and uses only `propext`, `Classical.choice` and `Quot.sound`. No proof uses `native_decide`.
