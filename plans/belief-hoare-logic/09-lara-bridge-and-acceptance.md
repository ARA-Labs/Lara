# PR 09: Lara composition and integrated acceptance
**Date:** 2026-10-07

## TL;DR

Give BHL method assertions a precise meaning inside Lara research artifacts, then prove how their warrant changes when source dependencies change. Bind conditional procedure validity and actual modeled applications to the exact checked artifact without treating supported applicability as mathematical truth. PR 09 implements B7 after PR 08; it can land before mandatory relative completeness in PR 06. Original B8 is the final join, owned by whichever of PR 06 and PR 09 lands last.

Plan status: approved by the researcher on 2026-10-07. Implementation status: pending. Original scope: B7 and, if PR 06 has landed, the B8 final join. Dependency: PR 08; PR 06 is not a prerequisite. Proposed PR title: `theory(bhl): compose belief proofs with checked arguments`. Read the [shared contract and sequence](README.md) before execution. [Issue #24](https://github.com/ARA-Labs/Lara/issues/24) tracks this work; no definition or theorem below is claimed to exist yet.

## Problem

Lara is a lower-level language for the meaning of ARA research artifacts. BHL supplies one statistical-method component of that meaning. A valid procedure, an execution record and a supported argument may refer to different claims or source snapshots. The bridge must express which conditional claim is warranted, what remains assumed, and whether the selected support still applies after an edit. A record containing both a BHL proof and an accepted argument is insufficient without these bindings and revision results.

## Constraints

Preserve core and evidence semantics exactly. Consume PR 08's real checker/runner; no fabricated source observation vector or caller-authored acceptance flag is allowed. Keep `.lara` syntax, verdict bytes, frozen corpora and ordinary reporting unchanged. Approval establishes the architectural boundary; PR 01 still owns the exact paper audit, numeric contract and detailed binding contract before implementation.

Separate BHL observation-equivalence/S5 semantics from Lara's existing possible-world accepted-context bridges, which generally require only normal K. No free coercion connects their modalities. Neither `Justified(P)` nor supported applicability proves `P` or BHL `K(P)`. BHL belief never implies the truth of its alternative hypothesis. Interpretation fidelity, real sampling and physical log completeness remain explicit external limits.

Use the complete-modeled-history baseline fixed by the earlier PRs. This PR owns a separating witness for incomplete submissions, not a general compatible-completion calculus. [Issue #23](https://github.com/ARA-Labs/Lara/issues/23) retains that calculus, broad revision and inquiry/impact work, and the wider theory gate. This PR releases no empirical experiment design and claims no improved research outcomes.

## Proposed approach

### What does an artifact assertion mean?

Implement PR 01's artifact binding contract as a proposed `ArtifactBinding` record. Bind the exact declared source snapshot and its raw/checked carriers; the claim identifier and explicit interpretation; the model, `P`, `C`, `Q` and derivation assumptions; the initial/final worlds and actual reference execution; selected argument identifiers and evidence dependencies; residual assumptions; and the declared history coverage. Bind evidence snapshots, manifests and registries where certified evidence is used. Stable labels alone do not establish identity: require equality or a proved interpretation-preserving map for each transported field.

Keep three judgments distinct. `ConditionalMethod` states `validTriple model P C Q` under named mathematical premises, regardless of whether this artifact establishes `P`. `ModeledApplication` requires actual `satisfies model initial P` and `executes model C initial final`; soundness then proves `satisfies model final Q`. `ArtifactWarrant` records the selected claim's justified, unblocked argument and dependency support at the bound source snapshot. It may warrant the conditional method claim with residual assumptions still listed, without asserting `Q` at the actual modeled final world. An applied-method payload must additionally contain the proved `ModeledApplication`; support for an applicability claim cannot replace its precondition proof.

These are proposed interfaces, not existing Lean declarations. Define their reference meaning through independent satisfaction/execution and existing Lara admission, support and grounded semantics before defining a certificate checker. A proposed `BridgeCertificate` carries the binding, checked derivation or proof-backed premises, actual run witness, selected support/dependency witnesses, residual-assumption ledger and whether its claim is conditional or applied. Checking it must establish the reference judgment by the PR 08 correspondence theorems and exact source witnesses. Do not define reference warrant as “the checker returned success,” or assume the desired postcondition as a certificate premise.

### Which existing source boundaries does the bridge use?

`Lara.Update.AcceptedRun` in `lean/Lara/Update.lean` retains aligned declared attacks, the admission result and the exact `Check.Unit.checkUnit` equation. `Lara.Update.applyUpdate` reruns admission and whole-unit checking through the private `acceptEdited` function. Use these carriers for ordinary source witnesses and revisions; do not infer acceptance from a pruned envelope or reconstruct raw attack identities from equal support terms.

For certified inputs, use `Lara.Surface.sourceWithEvidence` and `sourceWithEvidence_core_and_semantic` in `lean/Lara/Surface/Source.lean`. Reuse `Lara.Evidence.Composition` results `package_source_preserves`, `package_checked_context_exact`, `package_same_source_witness` and `package_source_justified_nonpromotion`. Prove that the surface/evidence and update witnesses refer to the same declared, raw and checked source; independently accepted but unrelated witnesses cannot be combined. Preserve capture/admission composition, rejection precedence and full public status, including the conditional core value inside `evidence-blocked`. BHL metadata cannot certify a leaf or admit a leaf quarantined by ordinary policy/group rules.

### Which files own bridge and acceptance?

| File | Deliverable |
| --- | --- |
| `lean/Lara/BHL/LaraBridge.lean` | Binding and certificate types, independent artifact meaning, checker soundness, source projection, dependency revalidation and explicit snapshot transport |
| `lean/Lara/Update.lean` only if required | Narrow proof-relevant exposure of `acceptEdited`, preserving old results and rejection precedence |
| `lean/Lara/Evidence/Composition.lean`, `lean/Lara/Surface/Source.lean` only if required | Same-source alignment lemmas at the existing evidence/source boundary, without another admission pipeline |
| `lean/Lara/Examples/BHLBridge.lean` | Positive, blocked, defeated, rejected, dependency-loss, harmless-update, stale-binding and incomplete-record witnesses |
| `lean/Lara/BHL/ExampleMain.lean` | Extend the registered runner with computed bridge and revision outcomes |
| `docs/theory-bhl.md` | B7 results and pending obligations; complete B0-B8 inventory and acceptance evidence when this PR owns the final join |
| `lean/Lara.lean`, `lean/AxCheck.lean`, `lean/lakefile.toml`, `Makefile` only as needed | Imports/audit/build integration without duplicating PR 08 registration |

Keep the bridge-specific revision proofs in `LaraBridge.lean`. Do not create a generic revision module or move BHL-independent update semantics here. Factor the private revalidator only if the executable exact-source witness needs it; prove that forgetting its added witness gives the old `applyUpdate` results, including every error-precedence case. Migrate affected callers without a compatibility shim.

### Which composition results must land?

- Prove certificate-checker soundness against the independently defined artifact judgment. For an applied payload, derive `Q` from conditional validity, genuine satisfaction of `P` and the actual terminating run. A conditional payload retains its residual assumptions and cannot be accepted as an applied payload without the required premise evidence. Demonstrate the invalid general implication with a countermodel.
- Prove that forgetting BHL-only metadata preserves ordinary source/core observations and every public status. Missing method assurance leaves ordinary Lara acceptance unchanged; blocked/defeated arguments and rejected edits retain their existing meaning.
- Prove binding integrity for the model, method, `P/C/Q`, claim interpretation, evidence dependencies, actual run and snapshot. Show that a certificate copied to an incompatible binding fails, even if the destination has an accepted source and an identically spelled claim.
- Prove dependency-sensitive revalidation and harmless-update transport as specified below. They must derive a target judgment or its failure from source-level facts, not take target warrant as a premise.
- Preserve the distinction between conditional validity, modeled application and defeasible artifact warrant in theorem conclusions. Supply countermodels to any proposed `Justified(P) → P`, `Justified(P) → K(P)` or belief-to-truth shortcut.

### Which proofs are inherited and which must be constructed here?

Reuse PR 08's checker-to-derivation correspondence and PR 05's soundness for the modeled-application theorem. Its remaining premises are genuine initial-world satisfaction and the exact run, not support for the precondition. This theorem composes inherited results; it does not supply the source-binding or revision results below.

Mechanize source projection, binding integrity and warrant revision over the existing accepted-run, admission, evidence and grounded semantics. For quarantine, derive selected-dependency loss from the actual prune and retained support. For transport, derive target warrant from the structural hypotheses, without assuming it in the premises. Audit all dependencies, including reused Lara lemmas, under the same axiom contract as BHL.

Prove the negative boundaries by inhabited countermodels: justified applicability with a false assumption, statistical belief with a false alternative, and the compatible-history pair below. A finite evaluation supplies an executable witness; the Lean theorem must establish that the witness has the stated properties. The partial-record result shows that this record does not determine this method conclusion, not that every incomplete record is useless.


### What changes when applicability evidence is quarantined?

Construct accepted source and target runs joined by an actual `applyUpdate ... (.tighten key) = .ok target`. In the source, select a warranted method claim whose declared dependency includes the argument using an applicability leaf `e`. In the target, ordinary admission quarantines `e` and prunes that selected dependency. Prove both source runs remain accepted, the model and `P/C/Q` are unchanged, and the same conditional BHL validity theorem still holds. The selected dependency-bearing warrant must lose eligibility at the target, even if a separate modeled-application proof remains mathematically valid.

The loss theorem must follow the named dependency through aligned raw identifiers, the ordinary prune and the retained checked support. It must not amount to unfolding a Boolean field labeled “invalid.” Use existing update nonpromotion results only with their stated hypotheses; they do not alone prove loss of this selected warrant. If independent alternative support survives, leave its warrant and the ordinary claim status available. Any example claiming loss of all warrants must additionally prove that no alternative eligible support remains.

### When can a warrant survive a source edit?

Prove an explicit `rebind` transport theorem between two exact accepted runs. Require an unchanged model, method, assertion interpretation, run and residual-assumption/history contract, or separately proved semantic transport for each changed field. Map selected raw argument/dependency identities injectively, preserve their conclusions and support typing, and preserve their evidence bindings and policy/group admission. Give explicit conditions preserving the relevant attack/defense structure and grounded support. "No new attack on the selected node" alone is insufficient because indirect attacks can change its defenders.

Use a checkable sufficient condition, such as an isomorphism of the selected support/dependency component including every incoming attack and defense path, with any added component disconnected in both directions. Also preserve the declared reference-support and checked-carrier facts used by the blocked-query computation. Prove that these conditions preserve the required grounded labels and unblocked status using the existing semantics. Recompute ordinary admission and, for certified inputs, evidence admission at the target. Transport derives target warrant under those conditions; it cannot assume target warrant or target justification as its entire premise.

Include a genuine harmless edit, such as a fresh unrelated admitted leaf with no group collision or new support/attack edges, and prove the conditions for it. Its source snapshot differs from the original, so the old exact-bound certificate remains stale. A newly rebound certificate may reuse the mathematical theorem only after rechecking source and evidence bindings. Run both the stale failure and rebound success, plus an incompatible copied-certificate failure with a changed method, claim interpretation or dependency.

### What does the incomplete-record witness rule out?

Exhibit one submitted record and two concrete complete modeled histories compatible with that record. Omit a test entry so the histories agree on the submitted observations but differ on history-sensitive method conclusions under the earlier BHL semantics. State the observation/projection relation for this witness and compute the differing conclusions with the actual finite evaluator. A record-only conclusion that selects one history's method assurance is therefore not justified by those observations alone.

This witness must preserve the earlier hidden-testing and multiple-comparison distinctions. It proves a limitation of the submitted record, not that any real researcher omitted tests or that a physical logger captured all of them. Do not infer complete history from an absent test entry. The general partial-history compatible-completion calculus remains in issue #23.

### What finishes original B8 acceptance?

B8 is required when both PR 06 and PR 09 are integrated. If PR 06 has already merged, base or rebase PR 09 on that main and execute B8 on the candidate tree before review. If completeness is pending, finish B7 and its own proofs, runner extension and shared gates; record B8 as pending and hand the final join to PR 06. The last-landing PR owns the integrated record, and whole-workstream completion is recorded only after both merge. There is no acceptance-only PR.

The durable theorem record must map every BHL theorem to its source, Lean declaration and exact hypotheses. Separately inventory inherited BHL results, finite-instance/checker results and Lara-specific composition. Include concrete derivations and countermodels, loop/parallel coverage, executable/reference correspondence, realizable artifact bindings, dependency quarantine and transport theorems, and the incomplete-record limitation. Complete the novelty/assumption comparison before claiming novelty; no unproved expressivity separation may be inferred from the module structure.

Execute the extended `bhl-examples` over the positive conditional and modeled assertions, blocked source, defeated argument, rejected source edit, accepted quarantine with selected warrant loss, surviving alternative support, harmless edit with stale failure and rebound success, and incompatible copied certificate. Exercise a supported applicability claim for which `P` is false: the conditional payload may remain available, but no modeled application may be accepted. Keep the earlier history, statistical, loop, parallel, fuel and non-truth witnesses passing, and run the incomplete-record separating pair. Each mismatch must fail the runner; no hardcoded observation vectors are allowed.

Run `(cd lean && lake exe bhl-examples)`, `make local-gates` with the documented macOS GNU-tool PATH, and `make ara-source-spans ara-session-index ara-observations`. Confirm every theorem is axiom-audited. When PR 06 lands last, use this same registered runner and complete gate set on the integrated candidate tree; the earlier bridge run cannot substitute for that final join.

Reconcile the resulting interfaces with issue #23 and its inquiry/impact dependencies. External sampling, interpretation fidelity and capture assumptions remain visible in the durable record. Completing BHL does not discharge that issue's incomplete-record, broad revision or representation-adequacy obligations, or release empirical experiment design.


## Alternatives considered

A second validator could bypass evidence admission or change rejection precedence. A bridge using an accepted flag, pruned envelope or coarse status vector loses the exact source assurance. Defining warrant as a conjunction and proving only its projections leaves dependency-sensitive revision unproved. A separate acceptance-only PR adds no semantic boundary; the last of PR 06 and PR 09 owns B8.

## Tradeoffs

The bridge crosses source, evidence and method boundaries, so it needs explicit alignment and revision proofs. Its sufficient transport conditions may reject some harmless edits; any broader result needs its own proof rather than a relaxed certificate check. Relative completeness is independent of this composition, but remains mandatory for final acceptance.

## Migration

Migrate every affected source-witness caller if a factor is required; leave no deprecated revalidator shim. Preserve `.lara` syntax, verdict bytes and frozen corpora. Move settled integration decisions and B7 evidence into the existing durable BHL records. If PR 06 is pending, retain its plan and the sequence index and leave issue #24 open. Only after both branches merge with the B8 record may the workstream close and the completed index be removed. Remove this executed plan once its durable content is retained. Open issues for any new actionable scope change with explicit costs.

## Recommendations

1. Bind conditional method proofs, genuine modeled applications and selected warrant to exact accepted source/evidence runs.
2. Prove and execute dependency quarantine, explicit rebinding and all original positive and negative bridge outcomes.
3. Complete B8 when this PR lands last; otherwise hand its inventory and integrated gate contract to PR 06 without claiming whole-workstream completion.
