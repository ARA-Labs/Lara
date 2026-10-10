# Research-process semantics: entitlement over incomplete histories
**Date:** 2026-10-09

## TL;DR

Formalize when a research record entitles a claim to be asserted, as opposed to when the claim is true. The [BHL baseline](../../docs/theory-bhl.md) already does this for complete modeled histories. This plan covers the case BHL leaves open: a submitted record that is only part of what happened.

The design has one idea at its center. A partial record denotes the finite set of complete histories it could have come from. A claim is entitled under a profile only when the BHL warrant holds in every compatible history and that set is non-empty. Omission assumptions, statistical validity under researcher degrees of freedom, revision transport and adequacy countermodels are all instances of that core or side conditions on it. The supporting literature survey is [research.md](research.md).

Plan status: proposed on 2026-10-09, not yet reviewed. No definition or theorem below exists yet. Tracked by [issue #23](https://github.com/ARA-Labs/Lara/issues/23); [issue #22](https://github.com/ARA-Labs/Lara/issues/22) stays downstream. This plan replaces the lost `plans/research-process-semantics.md` from source revision `5ba5f63`, which is no longer reachable from any ref; its T0–T8 stage labels are kept as the "Original scope" column below.

## Problem

BHL proves what a statistical procedure establishes given its complete history. Lara proves which claims an accepted source supports. Neither says what a reader may conclude from a record that omits part of the history, and real submissions always omit something.

The repo already shows the gap is real. `record_does_not_determine_conclusion` in `lean/Lara/Examples/BHLPartialRecord.lean` exhibits one latest-test record that is compatible with two complete executions whose method conclusions disagree. That is one witness. There is no general account of what a partial record does determine, which omission assumptions make a conclusion determinate, or how entitlement changes when a claim, model or source is revised.

Four further gaps follow:

- **Entitlement has no definition.** Lara has statuses (`justified`, `contested`, `defeated`, `gap`, `evidenceBlocked`) and BHL has `ArtifactWarrant`, but nothing says what standard a claim must meet to be asserted, or keeps hypothetical and conditional results from acquiring observed-evidence standing.
- **The history forgets order.** `History D := Multiset (D × TestId)` cannot state "the analysis plan was fixed before the data was read", which is the central condition for selection and optional-stopping validity.
- **Revision results are only sufficient.** `tighten_artifact_warrant_loss` and `rebind_warrant` give sufficient conditions. There is no characterization, and the obvious general laws are false once attacks exist.
- **Adequacy is unargued.** Nothing shows the history representation distinguishes what matters for entitlement, or that coarser representations (including W3C PROV) do not.

## Constraints

Preserve `lara-core@0.3`, grounded status semantics, admission, quarantine, evidence admission, the BHL baseline and every existing theorem statement. The new theory is an outer layer: it imports the core and BHL and changes neither. In particular `HistoryCoverage` keeps its single constructor `completeModeled`; the new omission models live in a new type, and a conservativity theorem relates the two.

Entitlement is non-factive and separate from every existing judgment. `Entitled` implies neither the claim's truth nor BHL knowledge of it, and unchanged public status does not transport entitlement. There is no coercion between modalities: any translation states its hypotheses and proves preservation.

Proofs are `sorry`-free and use only `propext`, `Classical.choice` and `Quot.sound`. Every theorem, including every countermodel, gets a `#print axioms` row in `lean/AxCheck.lean`. No `native_decide` or `Lean.ofReduceBool`. Mathlib (pinned `81a5d257`) is allowed in the new modules because they sit above BHL; the core calculus stays Mathlib-free. Finite witnesses stay small enough for kernel `decide`.

No wire change, `.lara` syntax, Haskell checker, corpus regeneration, mutation-base rewrite or freeze-tag bump is planned. If a stage finds it needs one, it stops and the change is budgeted in an issue before work continues.

No empirical experiment design or execution happens before the acceptance gate in R7. Finite countermodels, theorem witnesses and executable reference checks are theory verification, not an empirical study. No novelty or research-outcome claim follows from this plan; the prior-art search in [research.md](research.md#prior-art-leaves-the-combination-open-with-caveats) is qualified and must be rechecked before publication.

Every stage inherits this contract. A stage is complete only with the results provable from its definitions, positive and negative witnesses, an executable smoke run, updated theorem documentation and an axiom audit. A compiling interface is not a completed stage, and no stage defers its proofs to R7.

## Proposed approach

### Which stages are there, and what does each depend on?

| Stage | Scope | Original scope | Depends on |
| --- | --- | --- | --- |
| R0 | Reference contract and refutation of the tempting false laws | T0 | None |
| R1 | Compatible-history core, omission models and conservativity | T1, T5 (incomplete-history part) | R0 |
| R2 | Profiles, entitlement and no-promotion | T3 | R1 |
| R3 | Ordered process histories and analysis-order predicates | T2 | R1 |
| R4 | Finite statistical validity over incomplete ledgers | T6 | R2, R3 |
| R5 | Revision and transport of entitlement | T4 | R2 |
| R6 | Representation adequacy and separation | T5 | R1–R5 |
| R7 | Inquiry interface for #22, integrated runner, acceptance gate | T7, T8 | R1–R6 |

After R1, the R2 → R5 line and the R3 line proceed independently; R4 joins them. Each stage is one PR to `main`, with a Conventional Commit title of the form `theory(process): …`. A stage that grows past one reviewable PR gets its own numbered plan file in this directory, as BHL did.

All new code lives under `lean/Lara/Process/` (namespace `Lara.Process`), with witnesses under `lean/Lara/Examples/Process*.lean`.

Most of T1–T3 and T6 for complete histories already landed with BHL, so they are not repeated here:

- typed histories and executions;
- assertions and statistical belief;
- derivation soundness and relative completeness;
- the calibrated binary test;
- quarantine warrant loss and safe rebinding.

### What is the shared vocabulary?

The signatures below are proposals to be frozen in R0. Names may change; the separations may not.

```text
-- R1: a record denotes the complete histories it could have come from
structure RecordSemantics (H R : Type) where
  compat    : R → H → Prop          -- past completions only
  [fin      : Fintype H]
  [dec      : DecidableRel compat]

inductive Verdict | inconsistent | certainTrue | certainFalse | unknown

verdict  : RecordSemantics H R → R → (H → Prop) → Verdict   -- supervaluation
continues : H → H → Prop                                    -- future, kept separate

inductive RecordCoverage            -- omission models, weakest last
  | complete                        -- obs h = r
  | countBounded (bound : ℕ)        -- r ≤ obs h ∧ card (obs h) ≤ bound
  | declaredPolicy (policy : …)     -- ∃ choice, policy h choice ∧ report h choice = r
  | openWorld                       -- r ≤ obs h

-- R2: entitlement is profile-relative and keyed by a justification witness
inductive EvidenceKind | hypothetical | conditional | supported | observed   -- a finite lattice

structure Profile where
  admissible     : Finset EvidenceKind
  minCoverage    : RecordCoverage
  guarantee      : GuaranteeClass × ℚ   -- e.g. FWER at α
  requiredProbes : Finset ErrorKind
  acceptance     : Status               -- grounded `justified`

Warranted P h c w : Prop   -- ArtifactWarrant on a complete history, plus profile checks, for witness w
Entitled  P r c   : Prop   -- verdict over compat r of (∃ w, Warranted P · c w) = certainTrue

-- R4: the warranted level fails closed by type
warrantedLevel : Ledger → WithTop ℚ    -- ⊤ means no warrant
```

The compatible set ranges over pairs of an execution and a reporting choice, not over executions alone. Grünwald and Halpern's Monty Hall analysis shows why: conditioning in a space that ignores the reporting protocol gives wrong answers.

### Which false laws must be refuted before anything positive is proved (R0)?

R0 fixes the vocabulary above as a reference contract and proves a countermodel for each tempting law that the literature says is false. These are cheap, decidable, and they decide which positive theorems later stages may even attempt. Full rationale for each is in [research.md](research.md#pitfalls-and-false-conjectures-to-refute-in-lean-before-proving-anything-positive).

| False law | Countermodel | Consequence for later stages |
| --- | --- | --- |
| A stricter profile entitles fewer claims | removing an admissible kind deletes an attacker and reinstates a defeated claim | R2 proves only the directional version |
| Quarantine only removes warrant | quarantining a defeater's support reinstates its target | R5 proves an iff only on the support-only fragment |
| Unchanged status means unchanged warrant | the claim stays `justified` through a different defender | R2 keys entitlement by justification witness |
| An empty compatible set is harmless | supervaluation makes every conclusion vacuously certain | R1 adds `inconsistent` and `positive_needs_nonempty` |
| Completing the past is the same as continuing the future | a later retraction defeats a claim that every past completion warrants | R1 keeps `compat` and `continues` separate |
| Ordering predicates can be stated over `History` | two traces with the same multiset, plan fixed before vs after data access | R3 states order over `World.trace` |

The first three use only the Lara core and can be stated before any new definition; the last three need R0's types. The remaining false laws are refuted in the stage that owns the positive result:

- Kleene completeness and naive evaluation, in R1.
- Online-FDR replay, the e-BH bound, alpha-investing FDR and Ville via `maximal_ineq`, in R4.
- Directionality for stable semantics and unsafe non-injective rebinding, in R5.

### What does the compatible-history core prove (R1)?

| Theorem | Statement |
| --- | --- |
| `verdict_sound` | `certainTrue` implies φ holds at every compatible history |
| `positive_needs_nonempty` | a `certainTrue` or `certainFalse` verdict implies a compatible history exists |
| `certain_refine` | if the records' compatible sets satisfy `[[r']] ⊆ [[r]]`, certainty transfers from `r` to `r'` |
| `certain_weaken_assumption` | a stronger omission model preserves certainty: `compat₁ ≤ compat₂ → certain₂ → certain₁` |
| `certain_factor` | a finer view knows more: `obs₁ = g ∘ obs₂` transfers certainty from `obs₁` to `obs₂` |
| `determined_iff_no_witness` | φ is determined by the record iff no pair of compatible histories disagrees on φ |
| `naive_sound_iff_factors` | evaluating φ on the record as if complete is exact iff φ factors through the observation |
| `kleene_sound` | the compositional three-valued evaluator the checker runs is sound against supervaluation |
| `kleene_incomplete` | a witness where the evaluator answers `unknown` and supervaluation answers `certainTrue` |
| `coverage_complete_conservative` | under `RecordCoverage.complete` the verdict coincides with the existing `ArtifactWarrant` |
| `partialRecord_unknown` | `record_does_not_determine_conclusion`, restated as `verdict = unknown` |

`coverage_complete_conservative` is what keeps this an extension: for complete records, nothing BHL already says changes. Mathlib's `GaloisConnection` can carry the abstraction chain from histories through full records to the latest-test projection, but the plain `Finset` proofs are the foundation and the Galois packaging is optional.

### How are entitlement and no-promotion defined (R2)?

Entitlement follows a justification norm, not a truth or knowledge norm, because only a non-factive norm can be decided from a record. Pollock's warrant gives it operational form: a claim is warranted when an ultimately undefeated argument from the evidence supports it, which is Lara's grounded `justified`.

The profile states the inductive-risk policy explicitly: admissible evidence kinds, the weakest omission model it accepts, the guarantee class and level, and the error kinds the method must have probed (Mayo's severity is relative to a named error).

The profile is a parameter. R2 ships one concrete strict instance, `Profile.strict`, with these fields:

- coverage: `complete` or `countBounded`;
- admissible kinds: `observed` only;
- guarantee: FWER at a declared α;
- required probes: sampling error;
- acceptance: grounded `justified`.

A second, lenient instance is added only with a witness showing the two instances differ.

Required results:

- `no_promotion`: every rule outputs a kind at most the meet of its inputs, so by structural induction no derivation whose leaves are all `hypothetical` or `conditional` yields an `observed` entitlement. This generalizes the existing `justified_nonpromotion`, `quarantine_nonpromotion_corollary` and `package_source_justified_nonpromotion`, and R2 proves it agrees with them where they overlap.
- Non-collapse countermodels: supported but not warranted, conditional but not applied, warranted but false, entitled but not known.
- `stricter_directional`: a stricter profile entitles fewer claims when the arguments it removes attack nothing in the claim's ancestry. The unrestricted version is the R0 countermodel.
- Every entitlement result is stated with its justification witness, so "same status" and "same entitlement" stay distinct.

No published no-promotion theorem for scientific claim kinds was found. The evidence-kind lattice is this plan's construction and should be reviewed as such.

### How does order enter the history (R3)?

`History` stays a multiset; BHL's ledger semantics depends on that. R3 defines an ordered process view derived from `World.trace` and proves it projects onto `History`. On that view it defines and proves the decidability of:

- `PlanCommittedBefore`: the analysis commit precedes every access to the test data;
- `SplitSelection`: selection reads only one split and the test only the other, and the two are disjoint;
- `Predictable`: each e-value factor is fixed before the data it is evaluated on.

Each predicate fails closed: a missing index or unknown provenance counts against it.

R3 also proves the separation countermodel showing `History` forgets order.

Whether `ArtifactBinding` itself moves from `History` to the ordered view is a separate decision with its own cost (it touches every bridge theorem and the theorem inventory). R3 does not make it. If R4 cannot be stated without it, R3 stops and the change is opened as its own issue first.

### What does the statistical layer prove (R4)?

R4 follows the finite exact-rational style of `lean/Lara/BHL/Tests/Binary.lean`: finite horizon, `Fintype` outcomes, rational null masses, and expectations as `Finset.sum`. Mathlib at the pinned revision has no Ville inequality and no e-values, p-values or FDR, so these are proved directly.

| Result | Content |
| --- | --- |
| `ville_finite` | a nonnegative test supermartingale exceeds `1/α` within a finite horizon with probability at most α, under any stopping rule; proved by induction on the horizon |
| `eBonferroni_bounded` | rejecting when `e ≥ K̄/α` controls FWER at α for every completion with at most `K̄` tests |
| `eBH_bounded` | e-BH at `K̄` controls FDR at α, counting unreported tests as non-rejections; proved directly, since Wang–Ramdas Prop. 2 is stated for a fixed K |
| `split_selection_valid` | a test is valid conditional on a selection that read only the disjoint split |
| `countBounded_determinate` | with `RecordCoverage.countBounded 2`, the partial-record witness's e-Bonferroni verdict becomes `certainTrue`; the positive counterpart to `partialRecord_unknown` |
| `warrantedLevel_failClosed` | any required ledger field that is missing yields `⊤` |

Each result has a decidable counterexample twin:

- fixed-sample p-value inflation under optional stopping at a concrete horizon;
- selection on the same data, with an identical record in both worlds;
- online-FDR replay over a ledger missing a non-rejection, which comes out anti-conservative;
- alpha-investing controlling mFDR but not FDR.

Infinite-horizon Ville and online FDR procedures over complete ledgers (LORD, e-LOND) are outside this plan. If wanted, they are opened as issues with their Mathlib cost stated.

### How does entitlement survive revision (R5)?

Every edit puts a claim's entitlement into one of three classes:

| Class | Criterion | Exactness |
| --- | --- | --- |
| Survives by structure | a support label disjoint from the quarantine set, the edit outside the claim's ancestry, or an unchanged verifying trace | iff on the support-only fragment; sufficient with attacks |
| Survives by transport | the edit is a renaming or re-encoding under which `Warranted` is natural | iff relative to the class of maps |
| Must be re-established | the edit changes something the derivation read | Lara checks the recomputed region; it never searches for a minimal repair |

Required results:

- `quarantine_iff_support`: on the support-only fragment, a claim stays warranted after quarantining Q iff some minimal supporting source set avoids Q. This uses ATMS labels / why-provenance and sharpens `tighten_artifact_warrant_loss`.
- `grounded_directional_locality`: under grounded semantics, edits outside a claim's ancestry leave its status and entitlement unchanged; plus a countermodel for stable semantics.
- `warranted_natural`: on the fragment that never compares identifiers, warrant transports along every renaming. A two-source merge countermodel shows injectivity is necessary exactly where a profile counts independent sources. This refines `RebindConditions` from sufficient toward characterizing.
- `verifying_trace_reuse`: if a derivation recorded all its reads and all read values are unchanged, its warrant is unchanged. The theorem's hypothesis states complete read recording.
- Update vs revision: a dataset version change keeps old warrants for the old version; a discovered defect withdraws dependent warrants. Both are stated over `SourceUpdate`.

### What counts as representation adequacy (R6)?

| Part | Theorem |
| --- | --- |
| A1 Encoding | a section/retraction pair between decoded artifacts and the process history and ledger types |
| A2 Conservativity | `coverage_complete_conservative` from R1, plus agreement with the core on claims that do not depend on history |
| A3 Invariance | entitlement respects the representation's equivalence (`Quotient.lift`) |
| A4 Separation | for each coarsening π, two histories with `π h₁ = π h₂` that differ in entitlement |

The coarsenings A4 must separate:

- the latest-test projection (exists);
- `History` as a multiset (from R3);
- dropping failed or unreported analyses;
- dropping selection-read provenance;
- collapsing source identities;
- dropping retractions;
- the W3C PROV graph of the process.

The PROV row is the external positioning result. Absence of a record is not a record of absence, so two processes with identical PROV graphs can differ in entitlement.

A Hennessy–Milner-style characterization (histories are entitlement-equivalent iff no profile formula separates them) is attempted only for image-finite instances. If it does not go through, the separation table is the deliverable and the gap is recorded in the theory doc.

### What does R7 add, and what finishes issue #23?

R7 defines the interface issue #22 builds on. A finite inquiry is a finite family of compatible completions. Stability of a claim is `determined_iff_no_witness` over that family. Sensitivity is the set of histories that flip the verdict. R7 proves that stability is distinct from scientific adequacy, using a stable claim that is not entitled, and that unchanged status alone does not transport entitlement. It does not implement #22's P0–P9.

R7 also adds a `process-examples` Lake executable, run by a `process-theory` target inside `lean-gate`, mirroring `bhl-theory`. It writes `docs/theory-process.md` in the present-tense subject-document style and updates the boundary sentences in `docs/theory-bhl.md` that say this work is outside BHL.

Issue #23 closes, and the gate before empirical experiment design opens, only when all of the following hold:

- every R0–R7 theorem is proved and audited;
- the integrated runner passes;
- `make local-gates` passes;
- the three ARA gates pass;
- `docs/theory-process.md` states the boundary.

The researcher then decides whether experiment design starts.

### How is each stage verified?

- `cd lean && lake build`
- `make local-gates` (includes `axiom-audit` and the AxCheck coverage script)
- `cd lean && lake exe bhl-examples`, and from R7 `lake exe process-examples`
- `make ara-source-spans ara-session-index ara-observations` when the stage touches `ara/`

The PR description states that `make local-gates` passed, since the required GitHub workflows do not build Lean.

## Alternatives considered

| Alternative | Decision |
| --- | --- |
| Add constructors to `HistoryCoverage` | Rejected: breaks exhaustive matches across the bridge and inventory; a new type with a conservativity theorem achieves the same with no change |
| Replace `History` with an ordered ledger now | Deferred: it touches every bridge theorem; R3 works over `World.trace` and escalates only if R4 needs it |
| A three-valued (Kleene) semantics as the reference | Rejected: it loses classical truths; it is kept as the fast evaluator, proved sound against supervaluation |
| A knowledge norm of assertion | Rejected: factive, so not decidable from a record |
| AGM belief-set revision for quarantine | Rejected: belief sets carry no sources; support labels / provenance are the right layer |
| Infinite-horizon Ville and online FDR in this plan | Deferred to issues: the finite instance suffices for the gate and fits the existing exact-rational style |
| Several profiles from the start | Rejected for R2: one strict instance with a parametric type; a second instance needs a separating witness |
| A Haskell executable checker | Out of scope: no wire or corpus surface is introduced |

## Tradeoffs

Supervaluation over a finite compatible set is exact but exponential, so witnesses must stay tiny for kernel `decide`. That is acceptable for a reference semantics. Any production checker would use the Kleene evaluator under `kleene_sound`.

Fail-closed defaults make many real records come out `unknown`. That is the point: a verdict should be determinate only when the record certifies the bound or order it relies on.

Keeping `History` unordered avoids churn now but leaves two history views. R3's projection theorem is what keeps them consistent.

The strict profile is conservative. A lenient profile is useful only once a witness shows what it changes.

## Migration

Each stage removes its section from this plan when it lands and moves the durable content into `docs/theory-process.md`. The partially executed plan keeps a status banner listing the remaining stages. `research.md` stays until R7 lands. Its verified references then move into `docs/lara-related-work.bib`; references marked "from memory" are verified first or dropped. The plan directory is deleted when issue #23 closes.

## Recommendations

1. Review the shared vocabulary and the R0 false-law table first; they decide which positive theorems later stages attempt.
2. Implement R0, then R1, and stop to re-review if `coverage_complete_conservative` needs any change to the BHL bridge.
3. Run the R2 → R5 line and the R3 → R4 line in parallel after R1.
4. Recheck the prior-art search before any public novelty claim; arXiv 2609.25421 is this project's own paper, not prior art.
5. Update issue #23 to point at this plan and record that the complete-history parts of T1–T3 and T6 landed with BHL.
