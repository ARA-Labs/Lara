# M3 Source Updates and Status Dynamics

This document is the durable record for Theory M3. It fixes a one-step source
update model, states the hypotheses proved for each constructor, and records the
theorem-backed transition matrices. The intended reader is a maintainer checking
what the paper may say without reconstructing the milestone from commit history.
The Lean sources are authoritative.

## Frozen Source Boundary

`Lara.Update.SourceState` in `lean/Lara/Update.lean` contains exactly the raw
inputs from which admission and whole-unit checking are derived:

```text
sigma, policy, table, metas, leaves, argsRaw, rawAtts, groups, ground
```

It contains no `CheckedUnit`. `Lara.Update.Accepted reg state` means that an
aligned raw-attack resolution exists, `Admission.evaluateAdmission` accepts the
raw carriers, and `Check.Unit.checkUnit` accepts the exact pruned unit and
checker context produced by that admission result. `Lara.Update.AcceptedRun`
retains one proof-relevant successful run: its aligned attacks, admission result,
checked unit, admission equality, and checker equality. The theorem
`AcceptedRun.accepted` forgets those witnesses into `Accepted`.

`Lara.Update.SourceUpdate` is the closed first-fragment update vocabulary:

```text
addLeaf id atom metadata
tighten (leaf-kind, provenance)
addAttack raw-attack
addInstance raw-name support-term
```

The `String` in `addInstance` is deliberate. It names a pre-parse `argsRaw` row;
it is not a second parsed argument identifier. Raw attack endpoints use the same
pre-parse names. The Haskell mirror in `src/Lara/Update.hs` preserves this
exception and otherwise reuses the project's symbolic ADTs.

`Lara.Update.UpdateRejection` is a closed diagnostic type. Its constructor-side
cases are `leafNotFresh`, `keyNotAdmitted`, `endpointNotDeclared`, and
`instanceNotFresh`. Revalidation can also report duplicate raw argument names,
attack-resolution failure, source invalidity, source rejection, or whole-unit
rejection. No free-form rejection string crosses this boundary.

`Lara.Update.applyUpdate` checks the constructor side condition, edits only the
corresponding raw carrier, and calls the real admission and whole-unit checker
on the edited state. It returns the edited `SourceState` only after both stages
accept. The four edits append a leaf and its metadata, replace or append one
admission row with `quarantine`, append one raw attack, or append one raw
argument row. There is no admit-to-reject constructor because
`Admission.source_reject_no_checked_unit` proves that a rejected source has no
checked-unit target.

The Haskell mirror intentionally stops before `applyUpdate`. It provides
constructor and decider conformance only. No driver, parser, `.lara` section,
wire command, corpus case, or runtime update feature is part of M3.

## Side Conditions and Preservation Hypotheses

The named executable deciders and Lean adequacy theorems are:

| Update | Side condition | Decider and adequacy |
|---|---|---|
| `addLeaf` | The id is absent from semantic leaf rows, metadata rows, and every duplicate-group member list. | `AddLeafFresh`, `addLeafFreshB`, `addLeafFreshB_iff` |
| `tighten` | `Admission.decisionFor` returns `admit` at the key; omitted keys default to `admit`. | `AdmittedAt`, `admittedAtB`, `admittedAtB_iff` |
| `addAttack` | Both raw endpoints name rows in `argsRaw`. | `EndpointDeclared`, `endpointDeclaredB`, `endpointDeclaredB_iff` |
| `addInstance` | Both the raw name and the semantic support term are fresh in `argsRaw`. | `InstanceFresh`, `instanceFreshB`, `instanceFreshB_iff` |

The preservation theorems in `lean/Lara/Update.lean` are sufficient-condition
results, not unconditional admissibility claims:

- `applyUpdate_addLeaf_ok` assumes an accepted source, three-carrier freshness,
  and admission of the new metadata key.
- `applyUpdate_tighten_ok` assumes an accepted source, an admitted old key, a
  tightened table at least as restrictive as the old table, a valid and
  rejection-free tightened table, agreement of the old and new checker contexts
  on retained leaves, and survival of old coverage witnesses between retained
  endpoints.
- `applyUpdate_addAttack_ok` assumes an accepted source, successful resolution
  of the new raw attack to one typed attack, typing of that attack, and retention
  of both endpoint terms under the existing prune.
- `applyUpdate_addInstance_ok` assumes an accepted source, name-and-term
  freshness, well-sortedness of the new term, a complete support derivation for
  it, and `Compile.AttackComplete` for the old retained arguments extended by
  that term.

Each conclusion produces a state for which the actual `applyUpdate` call returns
`ok` and `Accepted` holds. None says that its constructor always succeeds.

## Core and Public Observations

`Lara.Update.coreObs` applies an arbitrary
`Semantics.ExtensionSemantics` to the checked framework and the complete claim
projection for an atom. `CoreTransition` pairs the source and target
observations. The matrices below instantiate it with `Semantics.groundedSem`.
They therefore classify grounded four-state transitions; they are not a matrix
for every extension semantics.

Three theorems give the full semantics-parametric update-transition boundary.
Each quantifies over an arbitrary `Semantics.ExtensionSemantics` and assumes
explicit alignment, admission, and checking for the source and target, plus a
successful update.

Their classification hypotheses are constructor-specific.
`Update.AdditiveUpdate.addLeaf` carries `AddLeafFresh source id` and
`Admission.decisionFor source.table m.kind m.provenance = .admit` for the new
metadata row. Its `.addAttack` and `.addInstance` constructors carry no extra
classification premise beyond the theorem's exact source and target runs and
successful `applyUpdate`. `Update.NonInstanceUpdate.addLeaf` carries the same
freshness and admit conditions, while its `.addAttack` constructor carries no
extra classification premise. Its `.tighten` constructor carries the exact
`Admission.AtLeastAsRestrictive` and retained-Gamma premises; the successful
`applyUpdate` and target admission/checking hypotheses supply the admitted-key
and tightened-table validity checks.

`Update.addAttack_gap_fixed` covers only `addAttack` and maps a source `gap`
observation to target `gap`. `Update.additive_no_gap_entry` covers the three
`Update.AdditiveUpdate` constructors and maps source non-`gap` to target
non-`gap`; `tighten` is outside its scope. `Update.nonInstance_gap_fixed`
covers the three `Update.NonInstanceUpdate` constructors and maps source `gap`
to target `gap`. `addInstance` is deliberately outside its scope.
`addInstance` is the only constructor that may move from a source `gap` to a
non-`gap` target. These are M3's only update-transition claims that are not
restricted to grounded semantics. The matrix claims instantiate
`Semantics.groundedSem`.

`Lara.Update.PublicReport` has five constructors: `gap`, `justified`,
`contested`, `defeated`, and `evidenceBlocked`. Its publication labels are
`gap`, `justified`, `both`, `refuted`, and `evidence-blocked`.
`publicReport` uses the exact production blocked-query computation first. If the
query is blocked it returns `evidenceBlocked`; otherwise it embeds the grounded
core status. `PublicTransition` recomputes the complete claim for the same atom
on both accepted runs. It does not transport checked support indices or holes
across an update.

`Lara.Update.CleanBase run` means exactly
`run.admission.prune.removedSeed = []` for the source accepted run. Under this
hypothesis, `publicReport_eq_core_of_clean` identifies the source public report
with its grounded core report. For a successful `AdditiveUpdate` (`addLeaf`,
`addAttack`, or `addInstance`), `additive_clean_target` derives a clean target,
and `additive_public_eq_core` identifies the target public and core reports.
`additive_public_ne_evidenceBlocked` then excludes the blocked target column.
This boundary does not apply to `tighten`, which may prune arguments.

`Update.quarantine_nonpromotion_corollary` quantifies over exact source and
target `AcceptedRun`s, a key, and
`applyUpdate reg source (.tighten key) = .ok target`. It assumes
`CleanBase sourceRun`, the `.tighten` case of `NonInstanceUpdate` (which carries
the exact restrictiveness and retained-Gamma hypotheses), an atom `p`, and
`publicReport targetRun p = .justified`. The proof first applies
`tighten_public_justified_source_justified` to derive justification for the
source checked complete claim. The clean-source framework and lifted-claim
identities then yield the justified lifted claim in the source declared
framework, exactly the conclusion shape of
`Admission.source_justified_nonpromotion`. This is the matrix-to-legacy
direction, and the proof does not call the older admission theorem.

`CleanBase` cannot be dropped from the universal additive theorem.
`Examples.Update.addAttack_blocked_growth` gives a real accepted, non-clean
source whose removed incoming edge already blocks one retained argument. A
successful `addAttack` extends that blocked closure and changes the public report
from `justified` to `evidenceBlocked`, while the target conditional core status
is `defeated`. This witness refutes an unconditional additive/core equality
theorem; it does not make `CleanBase` necessary for every individual run.

## Generated Matrices

`lean/UpdateMatrices.lean` prints
`Examples.Update.groundedCoreMatrixReport` and
`Examples.Update.fiveValuedPublicMatrixReport`. `R` marks a reachable cell with
a successful accepted source/target witness. `U` marks a cell excluded by the
named theorem under the constructor-local hypotheses encoded by the matrix
domain. The committed byte-for-byte output is
`test/update-matrices.golden`:

<!-- BEGIN GENERATED UPDATE MATRICES -->
```text
addLeaf grounded core matrix
reachable=4/16
source \ target | justified                        | refuted                      | both                   | gap                  
justified       | R addLeaf_justified_to_justified | U* addLeaf_core_fixed        | U* addLeaf_core_fixed  | U* addLeaf_core_fixed
refuted         | U* addLeaf_core_fixed            | R addLeaf_refuted_to_refuted | U* addLeaf_core_fixed  | U* addLeaf_core_fixed
both            | U* addLeaf_core_fixed            | U* addLeaf_core_fixed        | R addLeaf_both_to_both | U* addLeaf_core_fixed
gap             | U* addLeaf_core_fixed            | U* addLeaf_core_fixed        | U* addLeaf_core_fixed  | R addLeaf_gap_to_gap 
U* requires AddLeafFresh and admission of the new metadata key.

tighten grounded core matrix
reachable=13/16
source \ target | justified                        | refuted                        | both                        | gap                       
justified       | R tighten_justified_to_justified | R tighten_justified_to_refuted | R tighten_justified_to_both | R tighten_justified_to_gap
refuted         | R tighten_refuted_to_justified   | R tighten_refuted_to_refuted   | R tighten_refuted_to_both   | R tighten_refuted_to_gap  
both            | R tighten_both_to_justified      | R tighten_both_to_refuted      | R tighten_both_to_both      | R tighten_both_to_gap     
gap             | U* nonInstance_gap_fixed         | U* nonInstance_gap_fixed       | U* nonInstance_gap_fixed    | R tighten_gap_to_gap      
U* requires NonInstanceUpdate restrictiveness and retained-Gamma premises.

addAttack grounded core matrix
reachable=10/16
source \ target | justified                          | refuted                          | both                          | gap                    
justified       | R addAttack_justified_to_justified | R addAttack_justified_to_refuted | R addAttack_justified_to_both | U additive_no_gap_entry
refuted         | R addAttack_refuted_to_justified   | R addAttack_refuted_to_refuted   | R addAttack_refuted_to_both   | U additive_no_gap_entry
both            | R addAttack_both_to_justified      | R addAttack_both_to_refuted      | R addAttack_both_to_both      | U additive_no_gap_entry
gap             | U addAttack_gap_fixed              | U addAttack_gap_fixed            | U addAttack_gap_fixed         | R addAttack_gap_to_gap 

addInstance grounded core matrix
reachable=10/16
source \ target | justified                            | refuted                             | both                                | gap                     
justified       | R addInstance_justified_to_justified | U* addInstance_sink_status_monotone | U* addInstance_sink_status_monotone | U additive_no_gap_entry 
refuted         | R addInstance_refuted_to_justified   | R addInstance_refuted_to_refuted    | R addInstance_refuted_to_both       | U additive_no_gap_entry 
both            | R addInstance_both_to_justified      | U* addInstance_sink_status_monotone | R addInstance_both_to_both          | U additive_no_gap_entry 
gap             | R addInstance_gap_to_justified       | R addInstance_gap_to_refuted        | R addInstance_gap_to_both           | R addInstance_gap_to_gap
U* requires InstanceSinkPremises freshness and complete support.

additive public rows under CleanBase (via additive_public_eq_core)
addLeaf reachable=4/20 (conditional exclusions); evidenceBlocked=0; addAttack reachable=10/20; evidenceBlocked=0; addInstance reachable=10/20; evidenceBlocked=0
addLeaf conditional exclusions require AddLeafFresh and admission of the new metadata key.

tighten five-valued public matrix under CleanBase
reachable=13/20; evidenceBlocked=3
source \ target | justified                                   | refuted                                | both                                    | gap                               | evidence-blocked                             
justified       | R tighten_public_justified_to_justified     | R tighten_public_justified_to_defeated | R tighten_public_justified_to_contested | R tighten_public_justified_to_gap | R tighten_public_justified_to_evidenceBlocked
refuted         | U tighten_public_justified_source_justified | R tighten_public_defeated_to_defeated  | U tighten_public_defeated_not_contested | R tighten_public_defeated_to_gap  | R tighten_public_defeated_to_evidenceBlocked 
both            | U tighten_public_justified_source_justified | R tighten_public_contested_to_defeated | R tighten_public_contested_to_contested | R tighten_public_contested_to_gap | R tighten_public_contested_to_evidenceBlocked
gap             | U tighten_public_gap_fixed                  | U tighten_public_gap_fixed             | U tighten_public_gap_fixed              | R tighten_public_gap_to_gap       | U tighten_public_gap_fixed                   
```
<!-- END GENERATED UPDATE MATRICES -->

<!-- BEGIN GENERATED UPDATE SUMMARY -->
The four core products contain 64 cells and 37 reachable cells: `addLeaf` 4,
`tighten` 13, `addAttack` 10, and `addInstance` 10. Cells marked `U*` are
unreachable only under the premise printed below their matrix. Under `CleanBase`,
the public additive products contain 20 cells each and retain the core reachable
counts, with zero reachable `evidenceBlocked` targets. The `addLeaf` count also
uses the admitted-new-key blocker premise. Under `CleanBase`, the public
`tighten` product has 13 reachable cells, including 3 `evidenceBlocked`
targets.

The mechanization refuted the predicted `addInstance` count of 13. The actual
count is 10. A fresh instance is a sink in the old framework: freshness prevents
old raw attacks from naming it, while old-to-old edges and labels are preserved.
`Grounded.SinkExtension`, `SinkExtension.label_old`,
`SinkExtension.justified_preserved`, and
`SinkExtension.contested_not_defeated` support
`addInstance_sink_status_monotone`. This excludes justified-to-refuted,
justified-to-both, and both-to-refuted, in addition to the additive no-gap
column. The matrix and `addInstance_reachable_count` record 10.
<!-- END GENERATED UPDATE SUMMARY -->

## Holes and the AGM Probe

`Semantics.observe_holes_independent` proves, for every extension semantics,
that changing only `Grounded.Claim.holes` leaves observation unchanged. It also
states that the observation is `gap` exactly when complete support is empty.
`Consistency.completeClaimFor` therefore sets `holes := []` without changing
the status subject. This D9 result does not erase diagnostics:
`Grounded.incompleteAlternative` separately reports whether the full reporting
claim has holes, and the Haskell reporting path computes located incomplete
alternatives in `src/Lara/Reporting.hs`. Holes are neither a fifth grounded
status nor a sixth public report.

`Lara.Update.beliefSet sem unit p` means
`coreObs sem unit p = observed justified`. The M3 AGM comparison fixes
`sem = Semantics.groundedSem` and tests exactly two probes.
`Examples.Update.agm_success_fails` gives an accepted `addInstance` whose new,
sole support for the target claim is defeated on arrival, so the inserted claim
is absent from the target belief set. `Examples.Update.agm_inclusion_fails`
gives an accepted `addAttack` that removes a previously justified claim, so the
source belief set is not a subset of the target belief set. Both probes fail.
The comparison stops there; no remaining AGM postulate was tested and the
projection was not adjusted to recover one.

## Paper Claim Boundary

The paper may claim:

- a checked, one-step source-update calculus with four constructors and named,
  executable constructor side conditions;
- sufficient-condition acceptance preservation under the exact hypotheses of
  `applyUpdate_addLeaf_ok`, `applyUpdate_tighten_ok`,
  `applyUpdate_addAttack_ok`, and `applyUpdate_addInstance_ok`;
- complete grounded core 4 by 4 matrices for the four constructors, with
  mechanized reachable and unreachable evidence and counts 4, 13, 10, and 10;
- clean-base public additive summaries and the complete clean-base public
  `tighten` 4 by 5 matrix, using publication labels `refuted`, `both`, and
  `evidence-blocked`;
- the full semantics-parametric gap boundary: `addAttack` preserves `gap`,
  additive updates cannot enter `gap`, and every non-instance update preserves
  a source `gap`; these are M3's only non-grounded update-transition claims;
- from a justified target public report, under `CleanBase` on the exact source
  run, an exact successful `tighten`, and its `NonInstanceUpdate` hypotheses,
  the matrix-to-legacy `Update.quarantine_nonpromotion_corollary` for the
  source declared framework;
- the count refutation for `addInstance`, the counterexample to dropping
  `CleanBase` from the universal additive theorem, holes independence, and the
  two failed grounded AGM probes.

The paper must not claim:

- an unindexed four-valued general-semantics matrix;
- public additive behavior equals core behavior without `CleanBase`;
- unconditional `addInstance` admissibility;
- a theory of update composition, removal, or un-tightening;
- a CLI or runtime update feature;
- full AGM compliance;
- that the holes diagnostic is a sixth report.

## Scope and Verification

M3 covers the first update fragment and one successful source edit at a time.
It does not define update sequences, inverse operations, conflict resolution
between edits, or algebraic laws for composition. M3 also does not prove
contextual adequacy. Theory M4 (issue #187) retains that obligation: define
fragments, imports, exports, holes, hygienic linking, ill-linked rejection, and
contextual equivalence; then prove both directions of full abstraction against
an independently defined logical relation. Backend representation independence
is a corollary target of that work, not a result of these one-step matrices.

**Update (2026-09-02) — the contextual-adequacy obligation is *partially*
discharged.** M4 Part A landed the fragment/linking calculus and proved backend
replacement a congruence: an injective, acceptance-preserving relabel of a
fragment's certificates is unobservable in every admissible context whose own
assurances it fixes (`Lara.Context.backend_replacement_congruence`;
`docs/theory-m4-contextual-adequacy.md`). Two pieces of the sentence above
were left open by that milestone. **Holes (#217)** are now supplied by the
additive `Lara.Context.Holes` calculus: named CQ-answer templates, typed context
fillings, substitution into arguments and attack endpoints, checked linking,
composition, and functional/relational backend transport. The original complete
program boundary remains intact: substitution closes mandatory obligations before
compilation. `Examples.TermHoles` proves a genuinely open source judgment and
substitution-derived closure, with nested holes and a typed substituted attack;
see `docs/theory-term-level-holes.md`.

**Full abstraction** remains separate: Part B — a logical relation with soundness
and completeness — is gated and was not entered; the two obstructions remain in
`docs/theory-m4-contextual-adequacy.md` §7. Closing the term-hole obligation does
not establish that independently defined logical relation.

Run the maintained checks from the repository root:

```sh
cabal build lara-test
cabal test lara-test --test-show-details=direct
make update-goldens
make update-goldens UPDATE=1   # deterministic regeneration, then review the diff
cd lean && lake build Lara.Update Lara.Examples.Update
```

`make update-goldens` rebuilds `Lara.Examples.Update`, runs
`lean/UpdateMatrices.lean`, checks the output against
`test/update-matrices.golden`, and checks that golden against the generated
documentation block. A byte of drift in either comparison fails with a unified
diff.
