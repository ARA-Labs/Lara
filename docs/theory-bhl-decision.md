# BHL and research-artifact semantics
**Date:** 2026-10-07

## TL;DR

Lara is a lower-level language for expressing the semantics of Agent-Native Research Artifacts (ARA). Belief Hoare Logic (BHL) is approved as its statistical-method component, alongside argumentation and context semantics. The implementation must distinguish conditional procedure validity, application in a mathematical model, and defeasible artifact warrant under residual assumptions. The Lara-specific targets concern dependency-sensitive warrant and revision; the existing BHL metatheory remains attributed to its source.

Decision status: the researcher approved the architectural role on 2026-10-07 and explicitly approved documented reference corrections and the pinned Mathlib numeric dependency during implementation. The reference audit is recorded in [the assessment](belief-hoare-logic-assessment.md). Implementation proceeds through the nine required stages; this decision does not assert their soundness or relative completeness before the corresponding Lean proofs land.

## Problem

A research artifact can report a result and give an argument for a claim without specifying whether the procedure warrants that inference. BHL expresses this missing methodological meaning through preconditions, programs, epistemic postconditions and test histories. The reference is Kawamoto, Sato and Suenaga, [Sound and Relatively Complete Belief Hoare Logic for Statistical Hypothesis Testing Programs](https://arxiv.org/html/2208.07074v3). Its history sensitivity, statistical-belief semantics, soundness and relative completeness are prior results.

Lara's purpose is broader than checking statistical programs. It must connect method judgments to claims, interpretations, evidence and source revisions. A bridge that only packages a BHL certificate beside an accepted argument does not establish how those meanings interact. [Issue #24](https://github.com/ARA-Labs/Lara/issues/24) owns the approved implementation and bounded composition results; [issue #23](https://github.com/ARA-Labs/Lara/issues/23) owns the wider research-process theory.

## Constraints

Preserve the existing core, admission, quarantine, evidence and public-status semantics. Neither statistical belief nor Lara support implies empirical truth. Support for an assumption also cannot establish that assumption or knowledge of it in BHL. Keep residual assumptions visible in the artifact even when evidence supports their applicability.

BHL's observation-equivalence relation differs from Lara's accepted-context bridge relation. The former supports its epistemic laws; the latter generally lacks the stronger frame laws, as recorded in [the PW0 theory](theory-pw0-outer-model.md). No modality coercion is approved. A future translation must state and prove the required conditions.

This decision introduces no `.lara` syntax, core/wire migration, corpus regeneration, mutation-base rewrite or freeze-tag bump. It does not add physical history capture, a receipt service or an empirical protocol. Any later need for those changes requires separate approval and explicit costs. Every definition frozen during implementation must land with its available metatheory and axiom audit.

## Proposed approach

### What does the artifact assertion bind?

PR 01 must specify the abstract artifact fragment and its reference interpretation before later semantic interfaces freeze. The binding includes the accepted source snapshot, claim and hypothesis interpretation, model, precondition/program/postcondition, execution, applicability evidence dependencies, residual assumptions and declared history coverage. The reference meaning must be independent of the executable bridge. No parser is needed to specify this fragment.

| Judgment | Required evidence | Conclusion boundary |
| --- | --- | --- |
| Conditional method validity | A checked derivation with valid underlying premises and model side conditions | Every terminating modeled run from a precondition-satisfying world has the stated postcondition |
| Modeled application | Conditional validity, actual initial-world precondition satisfaction and the bound execution | The modeled final world satisfies the postcondition |
| Artifact warrant under residual assumptions | Exact accepted run, raw/checked typing, retention, grounded in-label and unblocked status for selected support and every named dependency | Selected supports remain eligible; independent `ArtifactMeaning` also requires claim association, conditional validity and applied-mode application, without proving residual assumptions true |

A claim identifier does not prove interpretation fidelity. A modeled execution does not prove that physical sampling occurred as modeled. BHL's complete modeled history does not prove completeness of a submitted log. Each remains an explicit external obligation where the application needs it.

### What must composition prove?

The bridge must use actual accepted source/evidence runs. It must preserve ordinary observations when method metadata is forgotten and characterize warrant under source changes. Its result must not be a theorem obtained solely by projecting fields from a conjunction of two successful checks.

| Required case | Acceptance distinction |
| --- | --- |
| Quarantine of selected applicability evidence | An accepted source loses that dependent warrant while the conditional BHL theorem remains valid |
| Safe source update | An explicitly rebound warrant survives under binding, admission, support and attack preservation hypotheses |
| Stale or incompatible certificate | A copied certificate cannot attest a different source snapshot, hypothesis interpretation, model or dependency binding |
| Supported applicability with a false assumption | Lara support cannot discharge a mathematical precondition or BHL knowledge premise |
| Partial submitted record | A nonempty pair of compatible histories can disagree on the proposed method conclusion; omitted tests cannot certify completeness |

The quarantine theorem concerns a selected dependency witness. Independent alternative support can preserve another warrant for the same claim. Source acceptance, claim status, mathematical theorem validity and applicability warrant must remain distinguishable in the examples.

### Which results belong to this workstream?

The theorem inventory must distinguish inherited BHL metatheory, concrete-instance and executable correspondence results, and Lara-specific composition results. The last category is a candidate contribution until the statements are proved and compared with prior art. No claim that BHL cannot encode arguments or revision is approved.

Issue #24 owns the complete-history BHL baseline, the artifact binding contract, bounded evidence-sensitive revalidation and the partial-record separating witness. Issue #23 retains the general compatible-history calculus, broader claim/model revision, representation adequacy and inquiry/impact composition. Completing BHL does not release empirical experiment design before that wider theory acceptance.

### How are the proofs mechanized?

The researcher approved reusing the BHL paper's mathematics while requiring checked proof dependencies for Lara. PR 01 must audit available mechanizations and record their coverage, hypotheses, toolchain and axiom dependencies. Reuse compatible checked declarations with any necessary representation correspondence; otherwise reconstruct the published arguments in Lean. A citation or a proof checked in another system cannot by itself discharge a Lean obligation. No axiom asserting published soundness or completeness is permitted.

Keep reference BHL metatheory, concrete-instance and checker correspondence, and Lara-specific composition as separate proof layers. Construct local soundness by induction on derivations over independent satisfaction and execution, then compose it with checker correspondence and genuine application premises. Prove revision results from actual source/evidence semantics and negative boundaries with inhabited countermodels. Record each theorem's source or motivation, assumptions, checked dependencies, axiom audit and witness. Tests check executable examples; they do not replace proofs or establish interpretation fidelity.


### How do the implementation dependencies change?

The [durable stage record](theory-bhl.md#what-remains-required) retains the PR identifiers and earlier acceptance. After soundness in PR 05, relative completeness in PR 06 is independent of the concrete PR 07-09 branch. The latter needs soundness, not relative completeness. Both branches remain mandatory; PR 06 is already integrated and PR 09 owns final B8 acceptance.

Final acceptance B8 belongs to the last-ready PR among PR 06 and PR 09. It must include the other's merged work, reconcile the full theorem inventory and run integrated gates on its candidate tree before review. Workstream completion is recorded only after both merge. This removes an unnecessary dependency without dropping a theorem or creating a separate acceptance-only PR.

### Which reference corrections are required?

The [reference assessment](belief-hoare-logic-assessment.md) distinguishes the published statements from the contracts required to prove them. Ordinary predicate meanings must be rigid relations on explicit arguments, or supply a proved preimage operation for their declared dependencies. Test execution has distinct syntax from pure assignment. Statistical atoms take explicit dataset terms. These choices prevent assignment substitution from overlooking state changes hidden in a predicate name.

History is a canonical finite multiset indexed by dataset values and test identities. A history-variable lookup reads its count from that multiset, so equal dataset values share counts even through different names. Dataset reassignment changes the lookup, not the historical ledger. Exact-history assertions compare the value-indexed multisets; they do not use the paper's alias-inconsistent name-count conjunction. Test execution records multiplicity, including aliases and repeated tests.

Knowledge uses equality of complete observation traces. Admissible worlds must satisfy the prefix, extension and accessibility-lifting conditions used by modal substitution and parallel correspondence. Equal final memory and test history alone cannot establish modal equivalence. Prove the required correspondence before using the parallel rule. Threshold monotonicity uses `≤`, while equality-indexed beliefs retain their distinct meaning.

The reference's integer-tuple loop encoding cannot represent arbitrary real values or substitute an actual hidden value under knowledge. The completeness branch must use a typed, finite assertion syntax with explicit encoding of runs and epistemic evaluation. It must prove representability against independent execution; an opaque weakest-precondition atom or an assumed completeness result is excluded. Quantified run/value carriers must state their sorts and legal scope. The general theorem remains relative to the named assertion-theory premises, and its concrete expressiveness obligation remains mandatory in PR 06.

The corrected assertion syntax separates fixed ghost worlds/traces from the ambient world. Ambient terms expose memory, the canonical ledger, derived sampling provenance and the derived hidden-possibility view, not the ambient raw action trace, last action or trace length. A raw world ghost retains its own trace; matching it to the ambient world compares the complete semantic view. Otherwise a ghost naming the left-then-right schedule could distinguish it from an independent right-then-left schedule and invalidate `Par`. The model and assertion stages must prove the full-observation/view correspondence structurally, including nested knowledge and unchanged ghost environments. Completeness must expand finite local control/effect equations and reconstruct an actual prefix-extending execution, not treat a list of endpoint witnesses as an execution by definition.

### Which numeric dependency is approved?

Use Mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997` with Lara's existing `leanprover/lean4:v4.32.0`. The researcher selected this pin explicitly. Mathlib supplies actual real numbers and countably additive probability measures under Apache-2.0. Import only the modules the BHL theory uses; `lean/lake-manifest.json` records the transitive dependency pins. The existing compiler calculus remains independent of Mathlib imports.

A test's p-value is its null distribution's measure of the declared tail event. Statistic and tail-event measurability, normalization and the binding of that distribution to the null model must be explicit. Combination bounds require a coupling and its marginal equations; independence is unnecessary for the union bound or intersection bound. These local mathematical obligations cannot be replaced by a field asserting BHL soundness.

The finite statistical instance uses exact rational masses and a non-strict tail including ties. It must prove normalization, event probability, calibration and its correspondence to the real probability interpretation. Rational execution covers that instance only. No equality between rational arithmetic and arbitrary real or continuous models is claimed.

### What exactly does the independent artifact judgment require?

Let `s` be the declared source snapshot, `r` its exact accepted admission/checker run, `k` a claim identifier, and `ι(k)` its declared hypothesis interpretation. A method binding retains the model `M`, assertions `P,Q`, program `C`, derivation premises, initial/final worlds `w,w'`, selected raw argument identities, applicability dependencies, evidence snapshot/manifest/registry identities, residual assumptions and history coverage. Field identity means equality of the actual carriers or a proved interpretation-preserving map, rather than equality of author-chosen labels.

`ConditionalMethod(M,P,C,Q)` means every independent terminating execution `Exec M C w w'` from a world satisfying `P` ends in a world satisfying `Q`. `ModeledApplication` adds satisfaction of `P` at the exact bound initial world and that exact execution. Its postcondition follows by applying conditional validity; it is not a certificate premise. `ArtifactWarrant` requires the selected argument and each declared applicability dependency to survive ordinary admission, typecheck in the accepted source, have the required grounded justification and remain unblocked. It binds their conclusions to `k` and its explicit interpretation. A warrant for a conditional payload retains its residual assumptions without asserting a modeled application.

Certificate checking must establish this reference meaning. Quarantine removes eligibility by pruning the selected raw dependency, while leaving the conditional method theorem untouched. Rebinding across a source edit requires exact method/run/interpretation preservation, recomputed source and evidence admission, and proved preservation of the relevant support and complete attack/defense component. A fresh unrelated admitted leaf supplies the harmless-edit witness; the old snapshot-bound certificate still fails. A partial-record projection must exhibit compatible complete histories with different method conclusions before any complete-history inference is rejected.

### Which concrete bridge contract replaces the proposed interface?

The declarations are in `Lara.BHL.BridgeSource` and `Lara.BHL.LaraBridge`; [the theorem record](theory-bhl.md#which-pr-09-source-and-claim-contracts-are-implemented) retains their exact source-facing hypotheses and direct acceptance. The integrated root, extended native runner, complete joined local gates, standard-trio axiom audit and three ARA gates passed on 2026-10-09. [The exact inventory](bhl-theorem-inventory.jsonl) maps all 1,754 relevant declarations to source, fully explicit unelided kernel type, scientific basis/scope and audit entry. The prior-art comparison does not assert novelty.

`ArtifactBinding` uses exact structural `Update.SourceState`, selected and dependent raw/checked occurrence references, closed method/interpretation/request codes, residual assumptions and complete-modeled-history coverage. `ClaimOrigin.authored` explicitly marks a bridge-authored association. A declared origin names a real `Presentation.ArgId`; independent `ClaimAssociation.declared` requires the actual certified source/material, formal claim lookup in input and semantic programs, matching selected audit pair/core/argument/supports-claim relation and membership in the unpruned alternatives ledger. Both certificate and meaning retain this association. Neither a stable claim spelling nor an independently accepted unrelated source can supply it.

`ConditionalMethod` is independent `ValidTriple`; `ModeledApplication` is genuine initial satisfaction and actual reference execution, and `modeled_application_post` derives final satisfaction. `ArtifactWarrant` independently quantifies actual raw/checked typing, retention, node material, grounded in-label and production unblocked status over selected support and every named dependency. `checkBridge` compares every binding field and composes real PR 08 derivation/application checking with ordinary support checks. It cannot make supported applicability true. Conditional `.conditionalFalse` may succeed while the applied version fails `.falsePrecondition`; support-to-truth/knowledge and belief-to-truth countermodels remain separate.

The ordinary projection retains complete public status, labels/edges, checked arguments/attacks/holes, raw masks and retained original occurrence coordinates. Actual `Driver.holeRows` derives located sites from the accepted run; `observeOrdinaryWire` uses production `Driver.buildAccept`, with no caller-supplied holes. The same-source CSV example composes actual `Surface.sourceWithEvidence` and `Evidence.extract`; JSON is a separate actual extraction witness. Evidence success does not admit a policy-quarantined leaf, and no metadata gate changes source/update rejection precedence.

`tighten_dependency_loss` derives missing target support from an actual accepted tighten, source metadata/key membership, raw typing and use of the quarantined leaf. Independent alternative support and mathematical method validity may survive. `RebindConditions` requires injective raw/checked maps, actual target retention/node/material and admission facts, a whole-carrier `Grounded.SinkEmbedding`, target `CleanBase`, fresh source-evidence success, exact evidence transport and syntactic claim association. `rebind_warrant` derives target warrant from these facts and old warrant, rather than assuming it. Mathematical fields and actual run remain unchanged by construction. Fresh unrelated leaf addition satisfies the concrete conditions, but changes the snapshot: the old certificate is stale and the newly rebound one is checked again.

`BHLPartialRecord.submittedRecord` reports only the latest actual emitted test, not a complete log or an ordered prefix. The nonempty record target 12/test 0/true/`1/4` fits both the single-test run and a run with earlier hidden test 4; their complete ledgers have cardinalities one and two and their finite method conclusions are true and false. Reference execution and finite satisfaction correspondence ground the record-specific non-determination theorem. A general compatible-completion calculus and physical capture completeness remain outside this decision.

### What does this comparison establish scientifically?

The [assumption and novelty comparison](belief-hoare-logic-assessment.md#which-assumptions-change-and-what-novelty-is-established) distinguishes inherited corrected BHL metatheory, changed typed history/representation contracts, exact finite rational calibration/checker specialization and Lara-specific binding/revision. No novelty or expressivity separation claim is established. B7's accepted calibration concerns the exact bound mathematical null law, not model adequacy for a physical population. Interpretation fidelity, physical sampling, capture adequacy and runtime refinement remain external assumptions, even for a fully checked artifact.

Issues [#23](https://github.com/ARA-Labs/Lara/issues/23) and [#22](https://github.com/ARA-Labs/Lara/issues/22) retain their wider theory gates. B8 requires all earlier method/history/loop/parallel/checker cases plus conditional/applied, blocked/defeated/rejected, selected tighten loss with surviving alternative, stale/rebound/incompatible copies, supported false precondition, certified composition/quarantine and nonempty record separation on the joined candidate. Completion of this baseline does not release an empirical protocol or establish improved research outcomes.


## Alternatives considered

| Alternative | Decision |
| --- | --- |
| Make BHL the semantics of all research | Rejected: claim interpretation, defeasible argumentation and incomplete records require additional semantics |
| Keep BHL only as a literature comparison | Rejected: Lara needs a faithful, checked statistical-method component |
| Implement the standalone logic before deciding artifact meaning | Rejected: the binding and assumption contracts constrain the implementation |
| Treat supported assumptions as true preconditions | Rejected: defeasible support cannot discharge mathematical satisfaction |
| Drop relative completeness to reach the bridge sooner | Rejected: retain completeness on an independent required branch |

## Tradeoffs

Early artifact contracts add design work before the paper formalization. They expose errors that would otherwise appear only when connecting the checker to actual source and evidence semantics. The bounded revision and record witnesses add Lean proof and execution work without claiming to complete the wider process calculus.

Keeping physical sampling, interpretation and record completeness as external obligations limits what checking can establish. It also prevents a successful checker result from being reported as empirical truth. The approved Mathlib pin supplies the real/probability carrier; later stages must discharge each model's measurability, calibration and transport obligations.

## Migration

The reference audit, corrected contract, numeric dependency decision, actual PR 09 interfaces and observed joined acceptance are durable here, in the assessment and in the theorem record. Earlier stage evidence remains intact. Existing compiler, wire and frozen corpus contracts remain unchanged. The executed stage 09 plan is retired; its sequence index remains only until both PR 06 and PR 09 are integrated. Issue #24 owns version/main/release delivery; issues #23 and #22 retain the wider theory and downstream inquiry/impact boundary.

## Recommendations

1. Use the audited reference and independent artifact judgment when freezing later definitions.
2. Prove the bounded revalidation and separation results alongside the faithful BHL baseline.
3. Complete both dependency branches and the B8 joined-tree gates before closing issue #24.
