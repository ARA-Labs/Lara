# M3 Source Updates and Status Dynamics

This document is the durable record for Theory M3. It fixes a one-step source
update model, states the hypotheses proved for each constructor, and records the
theorem-backed transition matrices. The intended reader is a maintainer checking
what the paper may say without reconstructing the milestone from commit history.
The Lean sources are authoritative.

_Status: settled record (2026-08-29; theory spine). The
question it answers, in plain terms: if you edit one declaration of a checked
source program — add a leaf, retract an argument, change an attack — what can
happen to each claim's status, and which transitions are provably
impossible?_

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

`Lara.Update.SourceUpdate` is the closed update vocabulary. The first fragment
has four constructors; the two completion constructors were added later
(`docs/located-gap-decision.md` §6a, D13 and D14):

```text
addLeaf id atom metadata
tighten (leaf-kind, provenance)
addAttack raw-attack
addInstance raw-name support-term
dischargeOpen raw-name position question support-term
atomic [atomic-edit]
```

An `AtomicEdit` is one of `addLeaf`, `addInstance`, `addAttack`, or
`dischargeOpen`. It is a separate type, so a batch cannot contain a batch.

The `String` in `addInstance` and `dischargeOpen` is deliberate. It names a
pre-parse `argsRaw` row; it is not a second parsed argument identifier. Raw
attack endpoints use the same pre-parse names. The Haskell mirror in
`src/Lara/Update.hs` preserves this exception and otherwise reuses the
project's symbolic ADTs.

`Lara.Update.UpdateRejection` is a closed diagnostic type. Its constructor-side
cases are `leafNotFresh`, `keyNotAdmitted`, `endpointNotDeclared`,
`instanceNotFresh`, and `notDischargeable`; a batch reports its first failing
edit as `batchEdit index reason`. Revalidation can also report duplicate raw
argument names, attack-resolution failure, source invalidity, source rejection,
or whole-unit rejection. No free-form rejection string crosses this boundary.

`Lara.Update.applyUpdate` checks the constructor side condition, edits only the
corresponding raw carrier, and calls the real admission and whole-unit checker
on the edited state. It returns the edited `SourceState` only after both stages
accept. The first four edits append a leaf and its metadata, replace or append
one admission row with `quarantine`, append one raw attack, or append one raw
argument row. `dischargeOpen` rewrites one raw argument row in place: at the
rule occurrence at the position it removes the question from the open set and
appends the discharge (`Lara.Update.Discharge.dischargeAt`); the row keeps its
name and declaration index. `atomic` applies its raw edits in order, checking
each edit's side condition against the state the earlier edits produced
(`applyBatch`), and then admits and checks the final raw state once. There is no
admit-to-reject constructor because `Admission.source_reject_no_checked_unit`
proves that a rejected source has no checked-unit target.

The Haskell mirror intentionally stops before `applyUpdate`. It provides
constructor and decider conformance, the discharge rewrite, and the raw stage of
a batch only. No driver, parser, `.lara` section, wire command, corpus case, or
runtime update feature is part of M3.

## Side Conditions and Preservation Hypotheses

The named executable deciders and Lean adequacy theorems are:

| Update | Side condition | Decider and adequacy |
|---|---|---|
| `addLeaf` | The id is absent from semantic leaf rows, metadata rows, and every duplicate-group member list. | `AddLeafFresh`, `addLeafFreshB`, `addLeafFreshB_iff` |
| `tighten` | `Admission.decisionFor` returns `admit` at the key; omitted keys default to `admit`. | `AdmittedAt`, `admittedAtB`, `admittedAtB_iff` |
| `addAttack` | Both raw endpoints name rows in `argsRaw`. | `EndpointDeclared`, `endpointDeclaredB`, `endpointDeclaredB_iff` |
| `addInstance` | Both the raw name and the semantic support term are fresh in `argsRaw`. | `InstanceFresh`, `instanceFreshB`, `instanceFreshB_iff` |
| `dischargeOpen` | The raw name resolves (first match, as endpoints do) to a term whose occurrence at the position is a rule instance with the question in its open set. | `DischargeOpen`, `dischargeOpenB`, `dischargeOpenB_iff` (term level: `Discharge.OpenAt`, `openAtB`, `openAtB_iff`) |
| `atomic` | Each edit's own side condition, above, against the state the earlier edits produced. | `applyBatch`; the first failure is `batchEdit index reason` |

The two completion constructors are characterized exactly rather than by
sufficient conditions: `applyUpdate_dischargeOpen_ok_iff` (site precondition
and acceptance of the rewritten source) and `applyUpdate_atomic_ok_iff` (raw
batch success and acceptance of its final state). Their metatheory lives in
`lean/Lara/Update/Discharge.lean` and `lean/Lara/Update/Completion.lean` and is
summarized under "Holes and the AGM Probe" below.

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
non-`gap` target. For the first fragment these are the only non-grounded
update-transition claims (completion: "Holes and the AGM Probe"). The matrix
claims instantiate `Semantics.groundedSem`.

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
source checked complete claim. `tighten_public_row_justified_nonpromotion`
then lifts that claim along the source's checked carrier into the source
declared framework over the specification carrier (every declaration except
the typed holes), exactly the conclusion shape of
`Admission.source_justified_nonpromotion`. With holes the compact framework
only embeds into the declared one, so the lift is not the identity. This is the
matrix-to-legacy direction, and the proof does not call the older admission
theorem.

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

completion witnesses (atomic batches and in-place discharge)
addInstance b alone | rejected missing-conflict | sequential_completion_fails
addAttack b->a alone | rejected endpoint-not-declared | sequential_completion_fails
atomic [addInstance b, addAttack b->a] | accepted | sequential_completion_fails
atomic [addInstance b] | rejected missing-conflict; source kept | partial_batch_rejected
atomic [addAttack b->a, addInstance b] | rejected at edit 0: endpoint-not-declared | batch_edits_checked_in_order
atomic beside hole h | accepted; holes 1 -> 1, h kept | atomic_keeps_old_hole
dischargeOpen h eps q1 | accepted; holes 1 -> 0; p gap -> justified | discharge_hole_becomes_node
dischargeOpen h 0 q1 alone | rejected missing-conflict | discharge_needs_attack
atomic [dischargeOpen h 0 q1, addAttack h->a] | accepted; holes 1 -> 0; q gap -> justified | discharge_needs_attack
atomic [addInstance b] beside lone hole h | accepted; holes 1 -> 1; p gap -> justified | atomic_completion_public_justified
dischargeOpen h eps q2 by hole tUse | accepted; holes 0 -> 1; p justified -> gap | discharge_optional_enters_gap
dischargeOpen h 0 q1 after addAttack h->a | accepted; holes 1 -> 0; p justified -> refuted | discharge_outgoing_defeats
atomic [addLeaf l3 quarantined, addInstance c] beside hole h | accepted; args 1 -> 1; holes 1 -> 1, c pruned | atomic_quarantined_leaf_pruned
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

Since `lara-core@0.3` (`docs/located-gap-decision.md`) an accepted source can
contain holes: declared arguments that type-check with a nonempty mandatory
obligation set. The checked framework holds only the complete arguments, so
`completeClaimFor` and every matrix above still read complete support only.
`Accepted` no longer implies that every raw argument is complete: what an
accepted run yields as checked arguments and attacks is the complete arguments
and the attacks whose source is complete. `applyUpdate_addInstance_ok` keeps
its complete-support premise: it is the completion case.
`applyUpdate_addInstance_hole_ok` is the hole case; it needs no conflict
premise, since attack completeness constrains complete arguments only.

Adding a hole is inert only conditionally. A fresh `addInstance` whose term is
a hole, with the attacks unchanged, leaves the complete arguments, their typing
context and the closure coverage between them fixed, so every core status is
unchanged and the only new output is the hole's diagnostic
(`addInstance_hole_core_fixed`, witnessed by
`Examples.Update.addInstance_hole_inert`). The unconditional
claim is false: an attack from a complete source onto an occurrence inside a
hole produces closure edges onto complete arguments containing that occurrence,
so `addAttack` onto a hole can change a core status, and removing a hole can
remove such an attack at the raw endpoint boundary. Graph and status invariance
is therefore stated under unchanged complete-to-complete coverage, or for the
fresh hole-only `addInstance` above. No update other than `addInstance` changes
which declared terms are holes: a typed term keeps its obligations wherever the
leaf context agrees on its leaves (`typed_obligations_preserved`), so `addLeaf`
and `addAttack` leave the reported holes unchanged and `tighten` preserves the
obligations of every surviving term (`addLeaf_obligations_preserved`,
`addAttack_obligations_preserved`, `tighten_obligations_preserved`). Tightening
can still quarantine a hole, so its reported hole list only shrinks.

Completion has three routes (`docs/located-gap-decision.md` D11, §6a).

*Additive.* An author adds each fresh admitted leaf with `addLeaf`, then a
distinct complete term under a fresh raw name with `addInstance`. The old hole
and every raw attack stay declared, and the old hole stays reported
(`addInstance_holes_persist`). This sequence is not accepted step by step in
general: the complete term goes through ordinary attack-completeness checking,
so if it licenses an outgoing conflict that no declared attack covers,
`addInstance` rejects, and the `addAttack` that would cover it rejects first
because its source is not declared yet
(`Examples.UpdateCompletion.sequential_completion_fails`).

*Atomic* (D14). `atomic` performs the whole completion as one batch and checks
the completed program once. It is accepted exactly when its raw edits apply and
the final state is accepted (`applyUpdate_atomic_ok_iff`); a rejected batch
leaves the source unchanged (`atomic_partial_rejected`, with `applyOrKeep`).
Completion is complete: whenever the program obtained by adding fresh leaves,
fresh instances or an in-place discharge, and the needed attacks is accepted,
the batch yields exactly that program (`atomic_completion_complete`,
`atomic_discharge_completion_complete`). Every batch keeps raw attacks and
argument names at their indices, and a batch without discharge keeps every
argument row (`applyBatchFrom_prefix`). Whether or not its new leaves are
admitted, it keeps the old complete arguments and the old reported holes as
prefixes of the new ones (`atomic_additive_checked_prefix`, exact form
`atomic_additive_checked_split`, witnessed by
`Examples.UpdateCompletion.atomic_keeps_old_hole`). A quarantined new leaf
prunes only new rows: the removed seed grows by exactly the quarantined new
leaves, so every old kept row stays kept under the same checker context
(`atomic_additive_kept`), and a pruned row is neither an AF argument nor a
reported hole (`AcceptedRun.pruned_not_reported`, witnessed by
`atomic_quarantined_leaf_pruned`). An admitted batch keeps a clean source run
clean (`atomic_additive_clean_target`).

The per-constructor transition results compose over an additive batch as far
as follows (`lean/Lara/Update/Transitions.lean`). No claim enters `gap`, under
every extension semantics (`atomic_additive_no_gap_entry`). A batch with no
`addInstance` keeps every `gap` claim in `gap` (`atomic_instanceFree_gap_fixed`).
A batch with no `addAttack` adds only fresh sinks, so a grounded `justified`
claim stays `justified` and a `contested` one is not `defeated`
(`atomic_attackFree_sink_status_monotone`). Nothing else composes: one
`addAttack` already reaches every transition among the three non-`gap`
statuses. After an admitted batch from a clean source run, a complete target
row that no compiled attack reaches justifies every claim equivalent to its
conclusion, in the core and in the public report (`atomic_completion_justified`,
run-level form `AcceptedRun.justified_of_unattacked_row`, witnessed by
`atomic_completion_public_justified`).

*In place* (D13). `dischargeOpen` answers an open question of a declared
argument under its own name. The term-level results in
`lean/Lara/Update/Discharge.lean` show that every old position stays defined at
the same occurrence kind (`subterm_dischargeAt_old`), that the conclusion is
unchanged (`dischargeAt_conclusion`) and typing preserved when the discharge
answers the question (`dischargeAt_hasSupport`), and that the new obligations
are exactly the old ones away from the site, the ones still open at the site,
and the discharge's own (`dischargeAt_obligations_iff`). Through the pipeline,
raw endpoint alignment is preserved index by index (`dischargeOpen_resolved`),
every other hole and complete argument persists (`dischargeOpen_others_persist`),
and a retained hole discharged to completion becomes an AF node whose claim
leaves `gap` under every extension semantics
(`dischargeOpen_hole_becomes_node`, witnessed by
`Examples.UpdateCompletion.discharge_hole_becomes_node`). Because the
discharged argument keeps its declared name, its covering attack can also be
added first, one update at a time (`discharge_needs_attack`).

`dischargeOpen` has no unrestricted transition theorem. Discharging an optional
question of a complete argument with a hole turns an AF node into a hole, and
its claim moves from `justified` to `gap`
(`Examples.UpdateCompletion.discharge_optional_enters_gap`). Completing a hole
that a declared raw attack already names as its source makes that attack fire,
and the attacked claim moves from `justified` to `refuted`
(`discharge_outgoing_defeats`). The transition results are therefore stated for
a discharge that completes a retained hole, which inserts one AF node into the
old framework. No claim enters `gap` (`dischargeOpen_completion_no_gap_entry`),
and only a claim equivalent to the completed conclusion leaves it
(`dischargeOpen_completion_gap_fixed`), under every extension semantics. When,
in addition, no raw attack names the discharged argument, which is what
freshness gives `addInstance`, the compiled attacks are unchanged and the new
node is a sink, so `addInstance_sink_status_monotone` carries over
(`dischargeOpen_completion_sink_status_monotone`). A completed argument that no
compiled attack of the target reaches justifies every claim equivalent to its
conclusion, in the core and in the public report unless the claim is blocked
(`dischargeOpen_completion_justified`), which a clean source run rules out
(`dischargeOpen_completion_public_justified`, witnessed by
`discharge_completion_public_justified`). The grounded results rest on
`Grounded.SinkEmbedding`, which inserts sinks anywhere in the declaration order.
The update golden prints the completion witnesses and the counterexamples below
the matrices; no transition matrix is computed for `dischargeOpen` or `atomic`.

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

- a checked, one-step source-update calculus with four first-fragment
  constructors and named, executable constructor side conditions;
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
  a source `gap`; for the first fragment these are the only non-grounded
  update-transition claims;
- from a justified target public report, under `CleanBase` on the exact source
  run, an exact successful `tighten`, and its `NonInstanceUpdate` hypotheses,
  the matrix-to-legacy `Update.quarantine_nonpromotion_corollary` for the
  source declared framework;
- the count refutation for `addInstance`, the counterexample to dropping
  `CleanBase` from the universal additive theorem, holes independence, and the
  two failed grounded AGM probes;
- two completion constructors with exact acceptance characterizations: in-place
  discharge with position, conclusion, typing and obligation preservation, and
  atomic batches that are all-or-nothing and complete for completion, with the
  concrete sequential-failure counterexample;
- restricted transitions for both: a discharge that completes a retained hole
  never enters `gap` and exits it only for the completed conclusion, keeps the
  `addInstance` sink guarantees when no raw attack names the argument, and
  justifies an unattacked completion; an additive batch never enters `gap`,
  keeps `gap` without `addInstance`, and keeps the sink guarantees without
  `addAttack`; with the two discharge counterexamples that bound these
  restrictions.

The paper must not claim:

- an unindexed four-valued general-semantics matrix;
- public additive behavior equals core behavior without `CleanBase`;
- unconditional `addInstance` admissibility;
- a transition matrix for `dischargeOpen` or `atomic`, or a transition result
  for either without the restrictions above;
- a theory of update composition beyond one atomic batch, removal, or
  un-tightening;
- a CLI or runtime update feature;
- full AGM compliance;
- that the holes diagnostic is a sixth report.

## Scope and Verification

M3 covers the first update fragment and one successful source edit at a time;
the completion constructors add one in-place rewrite and one atomic batch, which
is checked once as a single edit. M3 does not define update sequences beyond a
batch, inverse operations, conflict resolution between edits, or algebraic laws
for composition. M3 also does not prove
contextual adequacy. Theory M4 retains that obligation: define
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
were left open by that milestone. **Holes** are now supplied by the
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
cd lean && lake build Lara.Update Lara.Update.Completion Lara.Update.Transitions Lara.Examples.Update Lara.Examples.UpdateCompletion
```

`make update-goldens` rebuilds `Lara.Examples.Update`, runs
`lean/UpdateMatrices.lean`, checks the output against
`test/update-matrices.golden`, and checks that golden against the generated
documentation block. A byte of drift in either comparison fails with a unified
diff.
