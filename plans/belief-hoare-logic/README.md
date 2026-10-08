# Belief Hoare Logic: artifact semantics and implementation plan
**Date:** 2026-10-07

## TL;DR

Develop Belief Hoare Logic (BHL) as Lara's statistical-method semantics within its role as a lower-level language for Agent-Native Research Artifacts (ARA). Define the artifact-level meaning and assumption boundaries first, then mechanize the reference logic and its composition with checked arguments. Retain soundness, relative completeness, concrete statistical instances and executable checking. The Lara-specific work must explain how evidence changes affect methodological warrant; attaching two successful checks is insufficient.

Plan status: approved by the researcher on 2026-10-07. Implementation status: PR 01–05 passed server acceptance on 2026-10-08; PR 06–09 remain unimplemented. Accepted stages have 1,119 mapped BHL theorems with actual smoke and complete `make local-gates` evidence. PR 01–02 also passed the three ARA gates; the qualifying research record is captured at the end of the implementation session. Every stage targets `feat/belief-hoare-logic`. [Issue #24](https://github.com/ARA-Labs/Lara/issues/24) tracks the remaining work. The settled architectural decision is [recorded in docs](../../docs/theory-bhl-decision.md), and exact theorem assumptions and current acceptance evidence are in the [theorem record](../../docs/theory-bhl.md).

## Problem

Lara expresses the semantics of research artifacts. Argumentation checking and other validation are consequences of that semantics, not its entire purpose. A research artifact needs to state which claim a result concerns, what a procedure establishes under explicit assumptions, and how supporting evidence affects the warrant for applying that result.

BHL supplies a semantics for statistical-testing procedures and their epistemic postconditions. Two procedures can report the same value while their histories justify different statistical beliefs. This is a useful research distinction, but BHL does not by itself define claim interpretation, defeasible support, or the meaning of an incomplete submitted record.

This workstream owns the faithful BHL baseline and a bounded Lara composition with evidence-sensitive revalidation. The wider process theory in [issue #23](https://github.com/ARA-Labs/Lara/issues/23) retains general incomplete-record reasoning, broader claim/model revision, representation adequacy, and the inquiry/impact connection. PR 01 fixes that boundary before downstream definitions depend on it. No empirical experiment design is released by completing BHL.

## Constraints

Preserve `lara-core@0.3`, current support and grounded status semantics, ordinary source admission, quarantine, strict backends, and evidence admission. BHL assertions live in a separate language and namespace. A statistical belief cannot be eliminated to the truth of its alternative hypothesis, turned into a posterior probability, or inserted into the core as an automatically trusted leaf.

Lara support for an assumption does not prove the assumption or BHL knowledge of it: `Justified(P)` implies neither `P` nor `K(P)`. Keep conditional method validity, application in a mathematical model, and defeasible artifact warrant as separate judgments. The artifact must retain residual assumptions even when it records support for their applicability.

BHL observation-based accessibility is an equivalence relation. Lara's existing possible-world context bridges need not satisfy those frame laws. Keep both relations and modalities distinct; any translation requires stated hypotheses and a preservation proof.

Every frozen corpus-independent definition must land with the metatheory provable at that step. Proofs must be `sorry`-free and use only `propext`, `Classical.choice`, and `Quot.sound`; add every new theorem to `lean/AxCheck.lean`. Do not use `native_decide`, `Lean.ofReduceBool`, or an unproved probability axiom in theorem dependencies. During PR 01 the researcher explicitly approved Mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997` for real/probability semantics and documented corrections to the audited source discrepancies. The corrected contract is in `docs/theory-bhl-decision.md`. Rational arithmetic is not an exact implementation of arbitrary real-valued tests.

No core or wire migration, legacy corpus regeneration, mutation-base rewrite, or freeze-tag bump is planned. Any proof or integration need that changes those contracts requires a separately approved change with regeneration and rerun costs in the tracker. This branch introduces no receipt service, authenticated history capture, statistical-test marketplace, general experiment orchestrator, or empirical protocol.

Every plan inherits this shared contract. A PR is complete only with the results provable from its definitions, positive and negative witnesses, an actual smoke run, updated theorem documentation and an axiom audit. Do not leave proofs for PR 09 or call a compiling interface a completed stage. If the paper audit exposes an obstacle, record it in issue #24 and obtain an explicit scope decision before reducing a requirement.

## Proposed approach

### Which dependencies does each PR require?

PR numbers identify plans; they do not impose a total merge order.

| PR | Plan | Original scope | Depends on |
| --- | --- | --- | --- |
| 01 | [Completed reference and artifact contract](../../docs/theory-bhl.md#what-completed-pr-01-on-the-server), [PR #25](https://github.com/ARA-Labs/Lara/pull/25) | B0, artifact judgment and cross-layer witness specification | None |
| 02 | [Completed epistemic model and test history](../../docs/theory-bhl.md#what-completed-pr-02-on-the-server) | B1 | PR 01 |
| 03 | [Completed assertions, substitution and statistical belief](../../docs/theory-bhl.md#what-completed-pr-03-on-the-server) | B2 | PR 02 |
| 04 | [Completed program execution and parallel correspondence](../../docs/theory-bhl.md#what-completed-pr-04-on-the-server) | B3 | PR 03 |
| 05 | [Completed independent derivations and soundness](../../docs/theory-bhl.md#what-completed-pr-05-on-the-server) | B4, soundness | PR 04 |
| 06 | [Relative completeness](06-relative-completeness.md) | B4, completeness | PR 05 |
| 07 | [Exact finite statistical instance](07-finite-statistical-instance.md) | B5 | PR 05 |
| 08 | [Executable proof checking and finite semantics](08-executable-checking.md) | B6 | PR 07 |
| 09 | [Lara composition and acceptance](09-lara-bridge-and-acceptance.md) | B7, evidence-sensitive warrant and revision witnesses | PR 08 |

After PR 05, PR 06 and the PR 07-09 branch can proceed independently. Relative completeness remains mandatory, but concrete tests and the bridge use soundness rather than completeness. Base each implementation PR on `feat/belief-hoare-logic` after its listed dependencies land there. Keep the existing plan filenames and avoid importing unmerged definitions.

B8 is the final acceptance join of PR 06 and PR 09. Whichever PR is ready last must contain the other's integrated work, reconcile the complete theorem inventory, and execute the integrated acceptance commands on its candidate tree before review. Record workstream completion only after both merge to `feat/belief-hoare-logic`. If PR 09 lands first, it reports bridge completion with B8 still pending; it cannot close issue #24. No separate acceptance-only PR or deferred-proof bucket is introduced.

The researcher's implementation instruction supersedes the numbered plans' former `main` base references: every stage PR targets `feat/belief-hoare-logic`. Preserve planning/research commit `46a9747` and land one verified commit per stage. After the full joined-tree acceptance, bump the release version and merge the integration branch to `main` with a merge commit, then publish and verify the release.

### Which interfaces and meanings are shared?

Define satisfaction and terminating execution independently of the executable checker. The reference theory must not impose a finite universe or fuel bound just to make evaluation easy. General proofs may be parametric in a mathematical model with explicit local hypotheses. B5 must construct a concrete model and discharge those hypotheses; assuming the final soundness theorem as a model field is not acceptable.

```text
satisfies model world assertion            -- independent assertion meaning
executes model program world finalWorld    -- terminating reference relation
validTriple model pre program post        -- every terminating run preserves post
Derivation assumptions pre program post   -- explicit BHL proof rules
checkDerivation context proof             -- checks rules and discharged premises
runFinite model program initial fuel      -- execution witness or incomplete run
```

These are proposed interfaces. Define assertion-premise evidence precisely. For the general logic, Lean proof terms can discharge implications in the underlying assertion theory. A finite checker can discharge them by exact model checking only over its declared model. Neither path may treat a caller-supplied `true` flag as proof or claim completeness for unrestricted automatic proof search.

PR 01 must map the paper's definitions, rules and theorem assumptions before fixing these interfaces. PR 07 constructs the concrete model required by the original B5 nonvacuity obligation.

New module paths in the plans are proposed. Reuse existing ownership when it fits, inspect callers and references before changing an exported symbol, and register imports and axiom-audit rows in the PR that creates a theorem. Keep the base `Lara.BHL` logic independent of the Lara-specific bridge.

### How are published proofs reused and new results mechanized?

The BHL paper supplies theorem statements and proof arguments, not a checked dependency for Lara's implementation. PR 01 must look for an existing compatible mechanization. Reuse it when its definitions, hypotheses, toolchain and axiom dependencies satisfy the reviewed contract, proving any required representation correspondence. Otherwise translate the published arguments into Lean. A citation alone cannot discharge a Lean obligation, and an axiom asserting published BHL soundness or completeness is forbidden.

| Proof layer | Required checked result | Owner |
| --- | --- | --- |
| Reference BHL | Soundness of the explicit derivation rules and relative completeness under the audited assertion-theory assumptions | PR 02-06 |
| Concrete instance and implementation correspondence | The statistical instance satisfies the primitive contracts; checker acceptance and finite execution agree with the independent reference semantics | PR 07-08 |
| Lara-specific composition | Exact artifact bindings, conservative observations, dependency-sensitive warrant, safe revision and record-limit countermodels | PR 09 |

Define worlds, satisfaction, execution and semantic triple validity before proving the inductive derivation system sound. Follow the published soundness argument by induction on derivations, using substitution, loop-invariant and parallel noninterference lemmas at their owning rules. Concrete distribution and calibration obligations must be proved independently, not hidden in a field assuming the desired global theorem. Compose checker-to-derivation correspondence with soundness; derive a modeled postcondition only after adding genuine initial-world precondition satisfaction and the bound execution.

Relative completeness concerns derivability under the assertion theory's stated premises. It is not needed to apply soundness to a checked derivation and does not establish that BHL expresses every relevant research distinction. Retain its independent mandatory branch. Lara's new results must follow from the actual source/evidence and argumentation semantics; a conjunction of certificates or a caller-set validity flag cannot replace those proofs.

For every theorem, retain the chain from source or motivation to exact statement and assumptions, checked proof dependencies, concrete witness or countermodel, and executable correspondence where applicable. The theorem record must also identify the axiom-audit entry. Lean proofs establish general properties, while smoke runs check executable examples. Neither establishes that the formalization faithfully captures an intended scientific interpretation; the source audit and explicit interpretation boundary remain necessary.


### What does an artifact-level assertion mean?

PR 01 must specify an abstract artifact judgment before freezing the reference interfaces. It binds the accepted source snapshot, claim and hypothesis interpretation, statistical model, precondition/program/postcondition, execution, evidence dependencies, residual assumptions and declared history coverage. This is a semantic contract; a new parser or `.lara` syntax is not required.

| Judgment | Meaning | What it does not establish |
| --- | --- | --- |
| Conditional method validity | Every terminating modeled execution from a world satisfying `P` satisfies `Q` | That a submitted execution starts in such a world |
| Modeled application | The exact initial world satisfies `P`, and the bound execution reaches a world satisfying `Q` | Physical sampling fidelity or truth of the alternative hypothesis |
| Artifact warrant under residual assumptions | The bound conditional result has justified, unblocked claim support and the required applicability evidence in the exact accepted artifact | Truth or BHL knowledge of the residual assumptions |

Evidence may support applicability without discharging a mathematical premise. A checker may claim a modeled application only with genuine premise evidence and an actual modeled run. If only conditional validity and applicability support are available, the artifact judgment remains conditional; it cannot report unconditional `Q`.

The reference artifact meaning must be independent of bridge acceptance. PR 09 proves its checker corresponds to that meaning and proves update results using actual source/evidence checking. A theorem that merely projects the two fields of a conjunction does not satisfy the composition obligation.

### Which research distinctions must the examples preserve?

PR 01 specifies the examples and their expected semantic distinctions; the owning implementation PR proves and executes them.

| Distinction | Required witness or result | Owner |
| --- | --- | --- |
| Same reported values, different procedures | Accounted testing and unaccounted hidden testing do not justify the same proposed postcondition | PR 02, PR 07 |
| Belief, support and truth | Belief can hold with a false alternative; justified applicability does not establish `P` or `K(P)` | PR 03, PR 09 |
| Theorem validity versus applicability warrant | Quarantining a selected applicability dependency leaves the conditional method theorem valid but removes that dependent warrant in an accepted source | PR 09 |
| Revision versus certificate copying | An explicitly rebound certificate survives a harmless update under proved support, attack, admission and binding conditions; a stale snapshot certificate cannot be reused | PR 09 |
| Modeled history versus submitted record | A nonempty pair of compatible histories can give different method conclusions for one incomplete record; missing entries cannot certify completeness | PR 09 |

Warrant loss is relative to the selected dependency evidence. Do not claim that every warrant for the claim disappears if independent alternative support survives. General reasoning over all histories compatible with a partial record stays in issue #23; this workstream supplies the complete-history baseline and the separating witness it must respect.

### What verifies each PR?

Every PR that adds or changes Lean must pass `make local-gates` before review. The required Haskell workflow alone does not build the Lean theory. Run a focused smoke scenario first: evaluate actual library operations and compare their outcomes with the declared witnesses. Before PR 08's permanent runner exists, use a throwaway Lean main importing the changed definitions, run it with `lake env lean --run`, and remove it after verification. Proof elaboration alone is not an execution witness; printing hardcoded expected output or theorem names is not acceptable.

Register `bhl-examples` and a `bhl-theory` Make target in PR 08, when the checker and finite execution are real. Include that target in `lean-gate` in the same PR. Extend the runner with the source-bridge scenarios in PR 09. Commands after runner registration are:

```sh
(cd lean && lake exe bhl-examples)
PATH="/opt/homebrew/opt/gnu-sed/libexec/gnubin:/opt/homebrew/opt/coreutils/libexec/gnubin:$PATH" make local-gates
make ara-source-spans ara-session-index ara-observations
```

The runner must exercise test-history aliasing and multiplicity, valid inference, hidden testing, accounted multiple comparisons, a loop witness, noninterfering parallel runs, fuel exhaustion, belief without truth, and the source-bridge outcomes specified in PR 09. `make local-gates` includes the axiom audit with producer `pipefail`; the required Haskell workflow alone does not build the Lean theory. Planning verification checks these documents and research records only; no BHL runtime or new Lean result exists yet.

Each PR must add or update `docs/theory-bhl.md` as its results land. Classify every statement as inherited BHL metatheory, a concrete-instance or executable correspondence result, or a Lara-specific composition result. Record the source, exact hypotheses, Lean declaration, and remaining obligations in issue #24. History sensitivity and relative completeness are inherited results, not new Lara novelty claims. Extend `docs/theory-bhl-decision.md` in PR 01 with the audited mathematical and numeric contract. State the executed commands and outcomes in each PR.

### What finishes the whole workstream?

B8 requires both the relative-completeness branch and the concrete checking/bridge branch. The durable theorem record must link every mapped theorem to its Lean declaration and hypotheses. Acceptance includes artifact-level meaning, conditional application, dependency-sensitive revalidation, explicit rebinding under safe updates, the incomplete-record separation witness, and preservation of ordinary Lara observations. Compare the actual Lara-specific statements with prior art before making a novelty claim. Record the general incomplete-record, revision, adequacy and inquiry obligations still owned by issue #23.

A model with no realizable precondition or an always-rejecting checker does not finish a PR. Keep the general semantics, finite executable coverage, conditional statistical guarantees and external premises distinct. Decomposing delivery does not release empirical experiment design or reduce the wider issue #23 theory gate.

## Alternatives considered

| Alternative | Decision |
| --- | --- |
| Keep BHL solely as a literature comparison | Does not meet the requested dedicated research and implementation workstream |
| Rename a history-permission checker BHL | Reject: it omits the assertion semantics and Hoare derivations that define the logic |
| Implement only a finite evaluator and claim full BHL completeness | Reject: finite evaluation does not prove the general relative-completeness result |
| Replace Lara's argumentation core with statistical beliefs | Reject: preserve argument checking and compose at an outer judgment |
| Add Mathlib without a reviewed dependency decision | Reject: B0 first identifies which real/probability results require it and the cost of adding it |

A proof-free type skeleton followed by one final proof PR was rejected: every frozen definition must land with its available metatheory. B8 runs at the dependency join in the last of PR 06 and PR 09, so a separate acceptance-only PR is unnecessary.

## Tradeoffs

Faithful relative completeness and parallel/loop semantics create more proof work than a finite history checker. They also make the baseline identifiable as BHL. Exact finite tests keep execution reproducible, while the general semantic layer must state the additional assumptions needed for real-valued or continuous models. A dependency decision may change proof engineering costs; it cannot silently change the mathematical target.

The Lara-specific targets concern how procedure semantics, claim interpretation and defeasible evidence compose. Their novelty remains open until the proved statements are compared with prior art. Real sampling conditions, interpretation fidelity and completeness of external logs remain external obligations, even when every formal derivation checks.

The dependency graph permits concrete and bridge work before relative completeness lands without weakening the final acceptance requirement. PR 01 can refine implementation interfaces after the paper audit, but any reduction in the approved theorem or witness scope requires a new researcher decision.

## Migration

The former `plans/belief-hoare-logic.md` is replaced by this index and the nine PR plans. Its committed original remains available with `git show 2ffbbf7:plans/belief-hoare-logic.md`. Historical ARA citations remain unchanged; new trace entries record the replacement. Current tracker links point here, with no obsolete-path compatibility file.

Branch `research/belief-hoare-logic` starts directly at `main` commit `e1d0486`. Prior planning stays on `research/auto-research-integration`; no unrelated commits are imported. The prior process plan and foundation assessment are available in local revision `5ba5f63838fae765ebc5fda1818710bbefd8d5b8`. GitHub did not resolve that revision during verification, so it is local provenance, not a published dependency. Read the context without switching branches:

```sh
git show 5ba5f63838fae765ebc5fda1818710bbefd8d5b8:plans/research-process-semantics.md
git show 5ba5f63838fae765ebc5fda1818710bbefd8d5b8:docs/research-process-semantics-foundations.md
```

Implementation adds an outer Lean library, abstract artifact judgment and theorem runner without changing existing `.lara` syntax or verdict bytes. Wider process work must reuse the BHL semantics and explicitly extend its complete-modeled-history boundary. Issue #24 owns the bounded evidence-revalidation and record-separation results listed here; issue #23 owns the general extension.

Remove an executed PR plan after moving its durable decisions and theorem evidence into `docs/`. While work remains, retain this index, mark the relevant row completed with its merged PR reference, and keep the unexecuted plans. Delete the index once the entire sequence is executed and its durable contents have moved to the theorem record. Actionable changes to scope remain tracked in GitHub issues, not a new backlog file.

## Recommendations

1. Execute approved PR 01, including the artifact contract and cross-layer witness specifications, before freezing later definitions or numeric dependencies.
2. Follow the dependency graph, with proofs and execution evidence in each implementation PR.
3. Complete B8 on the joined PR 06/09 tree; keep the wider issue #23 theory gate in force.
