# Evaluation

This document defines Lara's evaluation metrics, mutation-generation contracts, frozen input and output hashes, and performance benchmarks. Historical snapshots are labeled by freeze version; the current base-language evaluation pins are marked current. The separate certified-evidence evaluation is documented in [the measured-input freeze](../measurements/frozen/evidence-measured-inputs-v2.md).

## What the evaluation covers

The frozen evaluation covers the LLM-independent axes only: axis (a), mutation and differential testing, and the checker side of axis (c), the localization and ablation measurements. The human-authored natural-defect ablation and every LLM-producer and annotator axis (axes b and d) are out of scope and are deliberately not in this freeze.

A *corpus unit* is a checked program lowered from a real research artifact. A *mutant* is a controlled edit with an expected outcome: rejection-class mutants must fail at the specified class and location, while accept mutants exercise valid changes in status or diagnostics. The corpus sample is the hand-lowered semantic-study sample.

One stance governs every metric here: measurements are reported, not gated. Class match is the only gate. The harness records `location_match`, `location_primary`, agreement, and ablation deltas, but a lower value on any of them is evidence rather than a build failure, and a gate that would make a rate move is deliberately avoided (see the location caveat below).

## The measurement harness

One command, with manifest-driven discovery, produces the measurement records:

```sh
cabal exec -- runghc scripts/measure.hs
```

It emits `measurements/{report,ablation}.{json,tsv}` over the measured inputs; `scripts/claim-support.hs` emits the claim-support aggregation and the committed `measurements/binding-audit/worklist.tsv`. The canonical aggregate snapshot is committed under `measurements/frozen/`; other working measurement outputs remain gitignored as regenerable output. `measurements/binding-audit/**` is frozen input, excluded from regeneration (decision D-5 in the mutation record).

`report.{json,tsv}` carries 17 columns, of which columns 1 through 15 are deterministic. Columns 16 and 17 (`hs_check_ns`, `lean_wall_ns`) are wall-clock timing, reported and environment-dependent, and are not frozen. `ablation.{json,tsv}` carries no timing and is fully deterministic. The reproducibility anchors hash only the deterministic content.

The header order of `report.tsv` is executable contract, not prose: `test/MeasureSpec.hs`'s `prop_reportColumnOrder` pins the header verbatim and pins `location_match` and `location_primary` apart on a synthetic record, so a silent column swap would keep the arity identical while mislabelling every `cut -f` consumer.

## Ablation configurations

Three ablation configurations come from `Lara.Check.CheckConfig` in `src/Lara/Check.hs`: `noCQConfig`, `noTypedConfig`, and `noConflictScanConfig`. `fullConfig` is the frozen semantics and the reference against which the ablations are read.

`noTypedConfig` clears both `ccTypedAttacks` and `ccConflictScan`, preserving the published "nodes and arbitrary attack edges" baseline. `noConflictScanConfig` isolates the conflict scan. With `CompleteNodesOnly`, acceptance is monotone across all four settings of those two rejection-relaxing flags, as checked by `prop_monotonicity` over every manifest input. `noCQConfig` instead selects `PromoteTypedHoles`: promoting incomplete terms to graph nodes can introduce required conflicts and new rejections. A frozen measurement of zero new rejections is a result for that corpus, not a universal property of this ablation.

The ablation configurations are the reporting vocabulary; the Lean side deliberately knows nothing about them, because it mechanizes `fullConfig` alone. That scope rule and its proof obligations are in [`implementation.md`](implementation.md#what-the-lean-development-mechanizes).

## Metric contracts: class match, location, and coverage

Landmark metrics in the frozen headline are class match (`actual` equals `expected`) and cross-driver agreement (`lean_agree`). Class match is the gate; everything else is measured.

Ground truth for a localized row is an ordered, non-empty list of admissible constituents, predicted at generation time from the spec's stage order, and two metrics derive from it:

- `location_match` (headline, keeps its name) is membership: the reported constituent is an element of the list. This is the faithfulness claim, that the checker pointed at a seeded or predicted defect site rather than somewhere else.
- `location_primary` (a separate column) is equality with the list head, the constituent the spec's stage order designates first. This makes diagnostic ordering measured rather than assumed.

For a single-defect row the list is the singleton of its seeded site, so both metrics degenerate to plain equality with that site. The earlier single-site rows therefore keep their meaning under the list definition, with no silent reinterpretation.

Ground truth means the predicted *manifestation* site, not the edit site. For every single-site operator the two coincide; for an off-site operator they do not, by construction, so an edit to the policy whose manifestation is an argument's support failure has ground truth `[arg:i]`, not `[policy]`. The operator's site enumerator owns the prediction, per operator, the same way it owns the expected class.

The checker reports exactly one location, because `checkUnitWith` is fail-fast (`Either UnitError CheckedUnit`, one error, one located constituent), and there is no report-all-defects mode. Adding one would change the frozen acceptance boundary and its Lean mirror, so it is rejected. Because the seven-stage order is public contract and constituents within a stage are visited in declaration-index order, the reported location is deterministic and computable at generation time. There is therefore no search quality to benchmark: localization here is not a ranking problem. The honest claims are faithfulness (the reported constituent is genuinely defective) and ordering conformance (it is the one the stage order designates first), and both are falsifiable by an implementation or modelling error.

The metric is discriminating through three families of mutant, in order of value:

1. Off-site families, where the edit site and the manifestation site differ, so ground truth is a genuine prediction that a mislocating implementation or a wrong model of the cascade fails. This is the strongest gate the suite can state.
2. Multi-defect families crossing stage boundaries, for example a support defect in `arg:i` with an attack defect at `attack:j`, which make `location_primary` test that stage order rather than accident chose the report.
3. Multi-defect families within one stage, where two defective arguments test the declaration-index order.

These families do not make the reported rate move. Every published site is gated against the checker before it reaches `MANIFEST.tsv`: `prop_siteMatchesChecker` pins every list's head to the constituent `runCheckLocated` actually reports, and `prop_localizationSites` pins the tails by re-deriving each composite's set from the mutant and re-running the checker with the head defect reverted. A row whose ground truth the checker disagrees with fails CI at generation time and never becomes a measured row, so `location_match` and `location_primary` are 100% on the committed suite by construction, exactly as the single-defect families were, under a strictly stronger construction. What the families buy is the strength of that gate, not the value of the rate: their ground truth is a genuine prediction that a mislocating checker fails, which the echo-the-edit-site families could not state at all.

The caveat below is the canonical statement of this and must travel with the headline number.

> `location_match` is ≈100% by construction and stays that way — every published site is checker-gated before it reaches `MANIFEST.tsv`, so a mislocating ground truth fails CI instead of lowering the rate. The off-site and multi-defect rows add a stronger gate, not a number that moves; the ordering claim is `location_primary`, reported separately.

The alternatives were rejected as follows. Keeping single-site equality and adding multi-defect mutants anyway is ill-posed and silently smuggles the ordering claim into the headline. Ground truth equal to "whatever the checker reports" is circular and makes the metric 100% by definition. Ordering-only (primary equality as the headline) overstates what the paper needs, because ordering conformance is a secondary, differential-style property. A report-all-defects checker mode changes the frozen acceptance boundary for the benefit of a metric.

Implementation consequences of the contract: `mutantSite :: Maybe Constituent` widens to `[Constituent]` (empty means no seeded site, and likewise `imExpectedLocation` in `src/Lara/Measure.hs`); `detLocationMatch` becomes membership and `detLocationPrimary` is added beside it. Both fields are now `Maybe SeededSites`, a newtype over `NonEmpty Constituent`, because a bare list made an enumerator that accidentally published `[]` indistinguishable from one that seeds nothing, silently dropping the row from the location denominator instead of counting it as a miss. Manifest column 8 spells the list as elements joined by `,` in ground-truth order (`arg:0,attack:2`); `-` still means no seeded site, and single-element rows are byte-identical to the older spelling. `GroupId` is free-form, so the list codec rejects group ids containing `,` to keep the round-trip unambiguous. `report.tsv` gains the `location_primary` column after `location_match`, and the pinned `cut` range moves with it.

## Mutation generation and module ownership

`Lara.Mutate` generates the mutants. This section fixes which of its modules owns what, because the mutation suite's byte-stability depends on the layout: a reordered enumerator, a reordered constructor, or a renamed operator moves committed bytes and invalidates the freeze.

`A → B` below is an import inside the `Lara.Mutate` namespace.

```
Lara.Mutate                 core; imports only Outcome
├── Outcome ─────────────→ (no sibling; the specified-outcome vocabulary)
├── Manifest ─────────────→ core
├── Seed ─────────────────→ core
├── Sites ────────────────→ core + Sites.Cert + Sites.Conflict + Sites.Nav
│   ├── Sites.Cert ───────→ core + Sites.Nav
│   ├── Sites.Conflict ───→ core + Sites.Nav (mirrors the checker)
│   ├── Sites.Localize ───→ core + Sites + Sites.Nav (imports the facade; not re-exported)
│   └── Sites.Nav ────────→ (no sibling; structural only)
├── Suite ────────────────→ core + Seed + Sites + Sites.Localize + Sorts
├── Codec ────────────────→ core
├── Cycle ────────────────→ core + Seed
├── Accept ───────────────→ core + Accept.Ops + Accept.Build
│   ├── Accept.Ops ───────→ core + Accept.Build
│   └── Accept.Build ─────→ core
└── Sorts ────────────────→ Sites.Nav (not core)
```

The graph is acyclic because nothing the root imports imports it back. Since the `Outcome` split the root has exactly one sibling import, `Outcome`, which imports no sibling in turn and so is the bottom of the namespace. That is the load-bearing property of the arrangement, and it is what the D1 rule below protects.

### Export ownership

| Module | Exported names |
| --- | --- |
| `Lara.Mutate` | `MutationOp(..)`, `opName`, `OpFamily(..)`, `opFamily`, `familyText`, `parseFamily`, `codecDiagnostics`, `Mutant(..)`, `mutantFileName`, `mutationSeed`, `mutationBases`, plus `Expected(..)`, `expectedText`, `parseExpected`, `statusText` re-exported from `Outcome` |
| `Lara.Mutate.Outcome` (internal) | `Expected(..)`, `expectedText`, `parseExpected`, `statusText` |
| `Lara.Mutate.Manifest` | `mutantPath`, `manifestFor` |
| `Lara.Mutate.Seed` (internal) | `streamForKey`, `streamFor`, `pickWithStream`, `pickSome` |
| `Lara.Mutate.Sites` (internal) | the sixteen per-operator site enumerators, four of them re-exported from `Sites.Cert` and `Sites.Conflict` |
| `Lara.Mutate.Sites.Cert` (internal) | `certTheorySwapSites`, `certPayloadSites`, `certWrongFractionSites`, `bumpWitness` |
| `Lara.Mutate.Sites.Conflict` (internal) | `dropCoveringAttackSites` |
| `Lara.Mutate.Sites.Localize` (internal) | `retractRuleSites`, `twinSupportDefectSites`, `crossStageDefectSites` |
| `Lara.Mutate.Sites.Nav` (internal) | `CheckedIx(..)`, `DeclaredIx(..)`, `occurrences`, `rewriteAt`, `rewriteArg`, `setAttackAt`, `dropAttackAt`, `argSites`, `ruleSites`, `leafSites`, `attackSites`, `ruleOf`, `inequivLeaf` |
| `Lara.Mutate.Suite` | `mutantsForBase`, `corpusBudget`, `corpusMutants`, `corpusSweepReport`, `SiteOp(..)`, `siteOps`, `dropCoveringAttackSites` (re-export, tests only) |
| `Lara.Mutate.Codec` | `codecMutantsForBase` |
| `Lara.Mutate.Cycle` | `cycleMutants` |
| `Lara.Mutate.Accept` | `acceptMutants`, `acceptStructureOk` |
| `Lara.Mutate.Accept.Ops` (internal) | `opDropSupport`, `opAttachUndercut`, `opQuarantineAttacker`, `opAttachUndermine`, `opAttachRebutCycle`, `opAttachReinstate` |
| `Lara.Mutate.Accept.Build` (internal) | `acceptMutant`, `acceptMutantBlocked`, `acceptMutantWith`, `theQuery`, `theSupport`, `argConclusion`, `exceptionProp`, `firstPremiseLeaf`, `attackerArg`, `defenderArg`, `groundPat`, `propArgs`, `propPred`, `attackEndpoints` |
| `Lara.Mutate.Sorts` | `undeclaredPredSites`, `wrongPredAritySites`, `wrongArgSortSites`, `undeclaredConSites`, `wrongThetaSortSites`, `outOfScopeVarSites`, `duplicateSortSites`, `shadowBaseSortSites`, `duplicateConSites`, `duplicatePredSites`, `conUndeclaredSortSites`, `predUndeclaredSortSites` |

`Outcome`, `Seed`, `Sites`, `Sites.Cert`, `Sites.Conflict`, `Sites.Localize`, `Sites.Nav`, `Accept.Ops`, and `Accept.Build` are in `other-modules`, so the package's public surface does not grow, with one deliberate exception. A review added `prop_conflictSiteMatchesChecker`, which has to compare the enumerator's predicted conflict pair against the checker's and therefore calls `dropCoveringAttackSites` directly; since `Sites.Conflict` is an `other-module`, the name is re-exported from `Suite`, which is exposed. That grows the public API by exactly one name. Any further such re-export should be weighed against a test-only `.Internal` module instead. `Sites` is the only importer of `Sites.Cert` and `Sites.Conflict` and re-exports their enumerators, so `Suite` sees one module for them. `Sites.Nav` is the shared navigation layer, imported by `Sites.Cert`, `Sites.Conflict`, `Sites.Localize`, and `Sorts`. `splitMix64` and `stringSeed` stay private inside `Seed`.

### Import ownership

| Module | Imports |
| --- | --- |
| `Lara.Mutate` | `Data.Word`, `Lara.Diagnostics`, `Lara.Mutate.Outcome` |
| `Outcome` | `Lara.AST` |
| `Seed` | `Data.Bits`, `Data.Char`, `Data.Word`, `Lara.Mutate` |
| `Manifest` | `Lara.Diagnostics`, `Lara.Mutate` |
| `Sites` | `Data.List`, `Lara.AST`, `Lara.Blocked`, `Lara.Diagnostics`, `Lara.Prop`, `Lara.Sigma`, `Lara.SupportTerm`, `Lara.Mutate`, `Lara.Mutate.Sites.Cert`, `Lara.Mutate.Sites.Conflict`, `Lara.Mutate.Sites.Nav` |
| `Sites.Cert` | `Data.Ratio`, `Lara.AST`, `Lara.Blocked`, `Lara.Diagnostics`, `Lara.Strict`, `Lara.Strict.Cell`, `Lara.Strict.RA`, `Lara.Mutate`, `Lara.Mutate.Sites.Nav` |
| `Sites.Conflict` | `Lara.AST`, `Lara.Attack`, `Lara.Blocked`, `Lara.Check`, `Lara.Compile`, `Lara.Diagnostics`, `Lara.Driver`, `Lara.Policy`, `Lara.Prop`, `Lara.SupportTerm`, `Lara.Mutate`, `Lara.Mutate.Sites.Nav` |
| `Sites.Localize` | `Data.List`, `Data.List.NonEmpty`, `Data.Maybe`, `Lara.AST`, `Lara.Blocked`, `Lara.Diagnostics`, `Lara.Policy`, `Lara.Sigma.WellSorted`, `Lara.Mutate`, `Lara.Mutate.Sites`, `Lara.Mutate.Sites.Nav` |
| `Sites.Nav` | `Data.List`, `Lara.AST`, `Lara.Blocked`, `Lara.Prop` |
| `Suite` | `Lara.AST`, `Lara.Diagnostics`, `Lara.Replay`, `Lara.Wire`, `Lara.Mutate`, `Lara.Mutate.Seed`, `Lara.Mutate.Sites`, `Lara.Mutate.Sites.Localize`, `Lara.Mutate.Sorts` |
| `Codec` | `Lara.Strict`, `Lara.Wire`, `Lara.Mutate` |
| `Cycle` | `Lara.AST`, `Lara.Prop`, `Lara.Replay`, `Lara.Sigma`, `Lara.Wire`, `Lara.Mutate`, `Lara.Mutate.Seed` |
| `Accept` | `Data.List`, `Lara.AST`, `Lara.Driver`, `Lara.Replay`, `Lara.Wire`, `Lara.Mutate`, `Lara.Mutate.Accept.Build`, `Lara.Mutate.Accept.Ops` |
| `Accept.Ops` | `Lara.AST`, `Lara.Prop`, `Lara.Replay`, `Lara.Sigma`, `Lara.Mutate`, `Lara.Mutate.Accept.Build` |
| `Accept.Build` | `Data.List`, `Lara.AST`, `Lara.Prop`, `Lara.Replay`, `Lara.SupportTerm`, `Lara.Wire`, `Lara.Mutate` |
| `Sorts` | `Lara.AST`, `Lara.Blocked`, `Lara.Diagnostics`, `Lara.Prop`, `Lara.Sigma`, `Lara.Sigma.WellSorted`, `Lara.Mutate.Sites.Nav` |

## D1: Hard split, not a re-export façade

`Lara.Mutate` exports what it owns, plus the `Outcome` names it re-exports because `Mutant` carries one of them. It does not re-export the names that moved upward (the generators in `Sites`, `Suite`, `Codec`, `Cycle`, `Accept`), and a future change should not add such a re-export.

The rejected alternative is a façade root that imports its siblings and re-exports their names. It is unavailable at this shape of the graph, not merely unwanted: every generator sibling imports the root for the operator vocabulary and the `Mutant`/`Expected` core, so a root that imported them back would close a cycle. Restoring the old surface would require interposing a new `Lara.Mutate.Core` module, which is extra public surface bought purely for source compatibility.

The source-API break was bounded before it was accepted and is small in-repo. Exactly two files import `Lara.Mutate` wholesale (`test/MutationSpec.hs`, `scripts/gen-mutants.hs`), and both were updated. The four selective importers (`Lara.Measure`, `test/AblationSpec.hs`, `scripts/bench.hs`, `scripts/measure.hs`) take only `Expected`/`parseExpected`/`statusText`, which stay in the root, so they did not change. The accept family's four imported names also stay in the root, though since the `Accept` split they are spread across its three modules: the facade takes `Expected`/`Mutant`/`MutationOp`, `Accept.Ops` takes `Mutant`/`MutationOp`, and `Accept.Build` takes all four including `mutantFileName`.

### The `Outcome` re-export is the one exception, and it is not a façade

`Lara.Mutate.Outcome` sits below the root, not above it: it imports no sibling and in particular does not import `Lara.Mutate`. The direction is forced by the data, because `Mutant` has an `Expected` field, and it is what makes the re-export cycle-free where a generator re-export would not be.

Re-exporting rather than repointing importers is deliberate. Fourteen call sites across `src/`, `test/`, and `scripts/` name `Expected` in an explicit import list, and five also name `parseExpected`, `statusText`, or `expectedText`; `Lara.Mutate.Suite` imports the root openly, so a fifteenth module would have been affected though not by name. Repointing them would be a wide diff for no gain and would force `Outcome` into `exposed-modules`. With the re-export, `Outcome` stays an `other-module`, no importer changed, and the public surface is what it was.

The rule this leaves for a future contributor: a re-export from the root is admissible only for a module the root itself imports, that is one strictly below it in the graph. Everything above it stays a hard split.

## D2: Ownership modules and what each owns

The original sketch was `Sites`, `Codec`, and `Corpus` plus core, which at the measured line counts left core and `Sites` both over the guideline. Three further cuts along seams already present fix that: `Seed` (the SplitMix64 stream), `Cycle` (the constructed rebut-cycle family), and `Manifest` (the `MANIFEST.tsv` contract). The frozen public `mutationSeed` constant and the operator metadata function `codecDiagnostics` stay in the root, which is what keeps `Seed` internal and the root small enough to read in one sitting.

`codecDiagnostics` cannot move to `Outcome`. Its type is `MutationOp -> Maybe (String, String)`, so an `Outcome` that owned it would import the root for `MutationOp`, while the root already imports `Outcome` for `Expected` because `Mutant` has an `Expected` field. That is a cycle, and resolving it would require `MutationOp` and `Mutant` to part company, a larger redesign than the seam calls for. So the seam cuts at `Expected` and its spellings only.

`Lara.Mutate.Accept` was later split along the seam this record predicted, the constructed accept-verdict family versus its site and assembly helpers, into three modules under a facade: `Lara.Mutate.Accept` (154 lines, the facade and the whole public surface, exporting `acceptMutants`, `isJustified`, and `acceptStructureOk`), `Lara.Mutate.Accept.Ops` (241 lines, the six constructions and the vocabulary each injects), and `Lara.Mutate.Accept.Build` (162 lines, mutant assembly, the asserted justified-unit invariants, and the attack-site helpers). The dependency order is forced: every operator emits through `acceptMutantWith`, so a facade that both listed the operators and owned the assembly would close an import cycle. The public API did not change, because the facade kept both names, and `scripts/gen-mutants.hs` and `test/MutationSpec.hs` are untouched. The move was verified byte-preserving: the generated suite came out byte-identical, and every non-comment, non-import code line of the original file is present in the union of the three new files.

## D3: `Suite`, not the issue's `Corpus`

The issue named the sweep module `Lara.Mutate.Corpus`, but the corpus sweep (`sweepOps`, `corpusMutants`) and the worked-example assembly (`mutantsForBase`, `unitMutants`) are the same job over two base populations. They share `unitMutants` and the same operator order, and splitting them would put a short module beside another that has to be read with it. `Lara.Mutate.Suite` owns both. Here `Suite` means seeded rejection-suite assembly, not the complete fixture suite; `scripts/gen-mutants.hs` combines it with the codec, cycle, and accept families. This is a deliberate deviation from the issue's sketch, and this record is the one that shipped.

## Module size

There is no numeric line bound in this namespace, and CI does not measure one. The earlier rule (every module at or below 300 code lines, warning from 250, enforced by `scripts/check-module-size.sh` against a table of per-module counts) is retired, and the guard, its self-test, the CI step, and the table are gone.

The bound measured the wrong quantity. Every split was decided by a seam (specified outcome versus operator vocabulary, certificate family versus shared navigation, operator constructions versus mutant assembly), and each seam was visible in the export list before any line count was consulted. The number added pressure at the wrong moment; a two-line Haddock clarification asked for in review once broke the rule and was repaired by reflowing prose to buy the line back. Eleven modules elsewhere in `src/` exceed 400 lines by design, three of them past 800 (`Lara.Syntax` at 2136, `Lara.Wire` at 1579, `Lara.BindingAudit` at 1365), so the bound was never a property of this repository.

What governs module boundaries is D1, D2, and D3. Split when a nameable seam appears: a group of definitions with its own vocabulary, its own dependencies, or its own reason to be read alone. Length is a hint that one may have appeared, not by itself a reason to cut, and a module that is long because it is well documented is not a module to split.

## D4: The index-space contract the site enumerators publish

The checker does not run on the declared unit; it runs on the §4.3 quarantine of it. The contract that replaced the old fail-closed `quarantineIsIdentity` gate is frozen here because it is split across three modules and is not reconstructable from any one of them.

- The published `si`/`ti` are in checked index space. The scan cache, the coverage decider, and the emitted `Lara.Diagnostics.CConflictPair` all index the checked unit. `Lara.Diagnostics` builds the verdict's pair as `CConflictPair (mcSourceIndex mc) (mcTargetIndex mc)` with no remapping, so checked space is the space the verdict names, and the mirror must name the same one or the answer key is wrong.
- The deletion is in declared index space. The mutation edits `unitAttacks` of the declared unit, because that is what gets re-encoded.
- `Lara.Blocked.retainedAttackIndices` is the sole bridge between the two spaces. Entry `i` of it is the declared index of checked attack `i`.

Soundness rests on attack deletion commuting with the prune, which holds because the kept-argument set is attack-independent: `pruneWithPolicySeed` derives it from the policy seed and inconsistent-group members via `supportUsesLeafSet` over arguments, strictly before any attack is examined. Deleting retained declared attack `d` therefore prunes to exactly the checked attack list minus entry `i`. Deleting a pruned attack is an accepting no-op, which is why only retained attacks are candidate sites.

The rejected alternative was to keep a fail-closed `quarantineIsIdentity`-style guard and merely relax its condition. That preserves the defect it was hiding: the gate existed because a declared-space mirror publishes a plausible but wrong pair on a quarantining base rather than failing loudly, and no widening of a guard fixes a wrong mapping. The gate is gone, replaced by `retainedAttackIndices` plus the R9 pre-scan gate (`Lara.Driver.groupConflictReject`), which is a different condition, because it excludes bases the driver rejects before the scan, where no deletion could yield `MissingConflict` at all.

No Lean entry is owed for this. The prune's attack-retention predicate is already mechanized: `Admission.buildPrune`'s `keepAttack` is exactly "both endpoints ∈ keptIds" (`lean/Lara/Admission.lean` `retained_attack_endpoints`, axiom-checked), and `retained_attacks_selectAligned` with `RawAttack.resolve_filter_commute` pins that the checker consumes exactly that filtered sublist. `retainedAttackIndices` only re-expresses that proved filter as an index list for the generator, so it introduces no new definition the proofs do not already quantify over. This is the strong form of the exemption argument, not the weak "the type has no counterpart" form, which is false here anyway, since a `retainedIndices` counterpart exists at `lean/Lara/BlockedProgram.lean`.

The contract is guarded by `test/BlockedSpec.hs` `prop_retainedAttackIndices` (the bridge is an exact projection, with `CheckSpec.quarantiningConflictBase` supplying the gapped retained list `[1]` that makes it non-vacuous) and `test/MutationSpec.hs` `prop_conflictSiteQuarantiningBase` and `prop_conflictSiteMatchesChecker` (the published pair is the one the checker reports). No corpus base declares a `groups` form, so on every committed mutant `retainedAttackIndices == [0..n-1]` and the emitted sites are byte-identical to the ones emitted before the change, which is why the change needed no corpus regeneration and no freeze-tag bump, and equally why the quarantining path is reachable only from the in-memory fixtures.

### Generalized to every enumerator

The contract binds every site enumerator, not `Sites.Conflict` alone. It was first stated for `Sites.Conflict` while the sibling enumerators in `Lara.Mutate.Sites` and `Sites.Cert` still published `CArgument` in declared index space, latent because no corpus base quarantines; the generalization closed that asymmetry, and the bullets below are the contract for all of them.

- Sites are drawn from the checked unit. `Sites.Nav`'s `argSites`, `ruleSites`, `leafSites`, and `attackSites` read a `Prune`, not a `Unit`. A mutation into pruned material is an accepting no-op the checker never sees, so it can witness nothing, and self-gating on retained material is part of the contract, not an optimization. This binds the space-free enumerators too: the `Lara.Mutate.Sorts` leaf and θ operators publish `CPolicy`, which needs no mapping, but still draw their sites from retained leaves and arguments.
- Every indexed constituent is published in checked space. `CArgument`, `CAttack`, and `CConflictPair` all index the checked unit, because that is the space `Lara.Diagnostics` names in the verdict. `CPolicy`, `CGroup`, and `CReplayEnvelope` are space-free and are published as-is.
- Only the rewrite maps back to declared space, and the three retained-index lists are the sole bridges: `Lara.Blocked.retainedIndices` (arguments), `retainedAttackIndices` (attacks), and `retainedLeafIndices` (leaves, added by the generalization).

The two spaces are types, not a naming convention. `Sites.Nav` exports `CheckedIx` and `DeclaredIx` newtypes and the site tuples pair them; `rewriteArg`, `setAttackAt`, and `dropAttackAt` take a `DeclaredIx`. A transposed pair is a compile error rather than a silently corrupted answer key. The invariant is not a count of unwrap sites; it is that nothing pairs the two spaces except a retained-index list. Construction is either from such a list (`argSites` and `attackSites` in `Sites.Nav`, `retainedLeafDecls` and `retainedArgDecls` in `Sorts`) or directly in checked space from a measurement of the checked unit, which pairs nothing (`unlicensedAttackSites`' `CheckedIx (length (unitAttacks checked))` is the one such site). `Constituent` and the `Lara.Blocked` retained-index lists keep their bare-`Int` APIs.

The rejected alternative was a quarantining corpus base. The quarantining path is exercised only from in-memory fixtures (`CheckSpec.quarantiningConflictBase` and the derived skew), so no committed mutant file walks it. Adding such a base forces a full corpus regeneration and a freeze-tag bump, which must be budgeted rather than discovered.

There is one known boundary, and it fails closed. A leaf-mutating operator striking a member of a consistent group would flip that group inconsistent, turning the mutant's outcome into R9/quarantine instead of R2. No base carries a consistent group today; if one enters the corpus, `scripts/gen-mutants.hs`'s per-mutant `verify` and `prop_siteMatchesChecker` both fail loudly at that point, unlike the index skew the generalization closed, which failed open.

The generalization is guarded by `test/MutationSpec.hs` `prop_siteMatchesChecker` (every site of every enumerator, over the worked examples, all corpus units, the quarantining fixture, and a skewed sibling of each, rejects with its specified outcome at exactly the predicted `Constituent`, which is what turns `expected-location` from a measured column into a gated one), `prop_sitesQuarantiningBase` (the hand-checked absolute pins on the fixture), and `prop_siteDirectionSkewed`. That last property answers the coverage gap a review found: the one committed quarantining base has no rules, so every `ruleSites`-based enumerator was exercised only where checked and declared indices coincide, and a per-operator transposition would have failed open. `quarantineSkewed` gives every base a skewed sibling by prepending an inconsistent group, an argument on one of its members, and an attack targeting that argument, all declared first, so quarantine removes exactly the added material and the checked unit is the original base; the property then states the mapping itself and carries an anti-vacuity gate.

`retainedLeafIndices` owes no Lean entry, for the same strong-form reason. `Admission.buildPrune` proves `p.removedLeaves = leaves.filterMap …` and `p.checkedLeaves = Groups.quarantineLeaves qs leaves` (`lean/Lara/Admission.lean:764-765`), the argument-side `retainedIndices` counterpart exists at `lean/Lara/BlockedProgram.lean:80` with axiom-checked theorems, and `retainedLeafIndices` only re-expresses an already-proved filter as an index list for the generator.

## What the split deliberately did not change

Every moved definition and signature is cut-and-paste: no renaming, no signature change, no reformatting, no incidental cleanup. Only module headers, imports, export lists, and Haddock links differ from the pre-split text. This is what lets byte-identical regeneration of the frozen suite serve as the primary correctness gate, because the seeded stream is keyed `(base, operator)` through `opName` and selection draws from each enumerator's list in order, so a reordered constructor, a reordered `mutantsForBase` entry, a reordered comprehension, or a renamed operator would each move committed bytes. Consolidating operator registration to a single site was not attempted and is not implied by the layout; adding an operator still requires coordinated vocabulary, metadata, generator, assembly, and sweep edits.

## Frozen provenance: current evaluation freeze v8

The committed `measurements/frozen/` snapshot is v8, recorded 2026-10-05. It describes 600 mutants + 60 corpus units = 660 measured inputs under `lara-core@0.3`, as amended in place by the located-gap follow-ups (decision D12 in the located-gap record). It was measured from clean input commit `59a94c866c2214ef1042c3b83fb6480da3bcf17d` (`git-dirty: false`) on the PR branch that introduced the core bump; no `m5-freeze-v8` tag exists in this repository. The v7 snapshot, cut earlier on the same branch, is preserved below.

### Scope and class deltas

v8 is a corpus re-cut. Two changes move measured bytes; the seed (`20260801`), the operators, and the sample are unchanged. The full record is `measurements/frozen/corpus-relowering-v8-diffs.md`.

- Hole rows locate their obligations (issue #16): each obligation names the rule occurrences that leave it open. No outcome moves.
- The corpus declares its incomplete arguments (issue #15): all 48 `gap` units carry one located hole and stay `gap`; the corpus `MANIFEST.tsv` gains a `located_holes` column, and those units are measured as `accept-located-hole`. Two of them also declare their dead-end undercut against the hole, which is inert.
- Mutants: the re-lowered bases add 5 mutants (2 `reject-R10`, 3 `reject-R4`), and `hole-obligation` now seeds only complete arguments.

| Outcome | v7 | Change | v8 |
| --- | ---: | ---: | ---: |
| `accept-gap` | 57 | −48 | 9 |
| `accept-located-hole` | 18 | +48 | 66 |
| `reject-R10` | 11 | +2 | 13 |
| `reject-R4` | 34 | +3 | 37 |

All other outcome counts are unchanged.

### Frozen inputs and deterministic outputs

| Input | Count | Git tree SHA |
| --- | --- | --- |
| `fixtures/mutants/` | 600 (543 verdict/status anchors + 57 codec negatives) | `706fa15eb809b4810825bf798b8f20c5c649ce7e` |
| `corpus-units/` | 60 measured units (48 with a located hole) | `2ac98f01fbc98f7fa6cd7292986c90045b8dde92` |
| `examples/` | worked examples | `278e931bdcf4e888b6183e1f851a5b249792acff` |

| Output | SHA-256 |
| --- | --- |
| `report.tsv`, `cut -f1-15` | `e263e7db188b3aca4e7e3db55c88bf7573817c47228d20c986d15d4b0f08c8f3` |
| `ablation.tsv`, full | `ab2042f1e132372ea9ca9da11ec342e0298d742f4e6d58f7db754fc29d8cb444` |

Environment: GHC **9.10.3**, Lean **4.32.0** (commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`), Linux/x86_64. Timing columns are machine-dependent and excluded from the hash.

### Measured results

| Metric | v8 result |
| --- | --- |
| Class match | 660 / 660 |
| Haskell–Lean agreement | 660 / 660 |
| Location match and primary | 485 / 485 each (175 not applicable) |
| Corpus replay | 60 / 60 |
| `no-cq` (hole promotion) | 66 / 66 located-hole verdicts change, 0 reject flips either way; 65 shift a status: `gap→justified` 57, `gap→defeated` 6, `gap→contested` 2, `justified→contested` 1 |
| `no-cq` on the corpus alone | 48 / 48 change: `gap→justified` 46, `gap→defeated` 2 |
| `no-typed` missed rejections | 39: 13 R10 + 21 R11 + 5 MissingConflict |
| `no-conflict-scan` missed rejections | 5, all MissingConflict |
| Claim support | 171 leaves, 38 load-bearing; 5 typed attacks, 4 dead-end-sourced; binding-audit worklist unchanged |

The corpus row is the headline the re-lowering buys: on the real sample, without node completeness, 46 of the 48 claims whose argument leaves a mandatory question open would publish as `justified`.

### Verification and reproduction

| Gate | Result on the v8 input tree |
| --- | --- |
| `cabal build all` / `cabal test all --test-show-details=direct` | pass, apart from the two frozen-deliverable re-diffs, which pass once this snapshot is committed |
| `cabal exec -- runghc scripts/gen-mutants.hs` | 600 verified mutants |
| `make local-gates` | pass |
| `bash scripts/differential.sh` (inside `local-gates`) | 683 verdict anchors, 66 codec negatives; zero failures |
| `bash scripts/admission-differential.sh` | 20 / 20 |
| `bash scripts/replay.sh bundles/walking-skeleton` | byte-identical verdict |
| `bash scripts/test-replay-tamper.sh` | both tamper classes detected |
| `python3 -m unittest scripts/test_freeze_bundle.py -v` | pass |

Reproduce from the clean input commit:

```sh
git checkout 59a94c866c2214ef1042c3b83fb6480da3bcf17d
cabal build all
(cd lean && lake build)
cabal exec -- runghc scripts/gen-mutants.hs --check
bash scripts/differential.sh
ELAN_TOOLCHAIN=leanprover/lean4:v4.32.0 make measure
cabal exec -- runghc scripts/claim-support.hs
cut -f1-15 measurements/report.tsv | sha256sum
sha256sum measurements/ablation.tsv
```

## Historical freeze record: evaluation freeze v7

v7 was recorded 2026-10-05 and describes 595 mutants + 60 corpus units = 655 measured inputs under `lara-core@0.3`, measured from clean input commit `be82e970f3d26647a9c8accb084c452544851d6f` (`git-dirty: false`) on the PR branch that introduced the core bump; no `m5-freeze-v7` tag exists in this repository, and v7 was superseded before it landed by v8.

v7 is a core-version re-cut, not an additive one: every replay-bearing input was regenerated under `lara-core@0.3`, while the seed (`20260801`), the operators, and the corpus are unchanged. The full regeneration record is `measurements/frozen/lara-core-0.3-regeneration-diffs.md`. Exactly the 18 `hole-obligation` rows move, `reject-IncompleteArgument` to `accept-located-hole`; every other column of every row, the seeded location included, is byte-identical, and every mutant file differs from v6 only in its replay identity plus the 18 verdicts. The mutant split is 519 reject (codec included) and 76 accept. The verdict and status diff over all 60 corpus units is empty. The report rows change in exactly the same 18 deterministic columns 1 through 15, and claim-support and the binding-audit worklist are byte-identical to v6.

| Outcome | v6 | Change | v7 |
| --- | ---: | ---: | ---: |
| `reject-IncompleteArgument` | 18 | −18 | 0 |
| `accept-located-hole` | 0 | +18 | 18 |

| Input | Count | Git tree SHA |
| --- | --- | --- |
| `fixtures/mutants/` | 595 (538 verdict/status anchors + 57 codec negatives) | `94fc13c83d5389015f1154c34a02cd6985c87d51` |
| `corpus-units/` | 60 measured units | `42775090095306d799fe8961b7c036a459c35054` |
| `examples/` | worked examples, including the run1 and rebuttal-replay rewrites that now declare their holes | `948c14bef76a6621d0f23e47f6d38701e10ab713` |

| Output | SHA-256 |
| --- | --- |
| `report.tsv`, `cut -f1-15` | `e19c9af3528af92bf0d17bd9416b947a49cca65262e765d9d26e74015f433407` |
| `ablation.tsv`, full | `34a448a6542197c0d88a84d9605d676fc0135f439d33e1eb299900a0733b68df` |

The ablation TSV gained four columns at v7 (`full_statuses`, `ablation_statuses`, `new_reject`, `changed`), so its hash is not comparable with v6's. Environment: GHC **9.10.3**, Lean **4.32.0** (commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`), Linux/x86_64.

| Metric | v7 result |
| --- | --- |
| Class match | 655 / 655 |
| Haskell–Lean agreement | 655 / 655 |
| Location match and primary | 480 / 480 each (175 not applicable) |
| Corpus replay | 60 / 60 |
| `no-cq` (hole promotion) | 18 / 18 located-hole verdicts change, 0 reject flips either way; 17 shift a status: `gap→justified` 11, `gap→defeated` 4, `gap→contested` 2, `justified→contested` 1 |
| `no-typed` missed rejections | 37: 11 R10 + 21 R11 + 5 MissingConflict |
| `no-conflict-scan` missed rejections | 5, all MissingConflict |

The location metrics cover the 18 located-hole rows through the verdict's hole row (its original argument index) rather than a rejection constituent; the denominator is unchanged at 480. `no-cq` changed in kind: through v6 it removed the obligation gate and missed 18 rejections; at v7 there is no rejection to miss, so it promotes typed holes to AF nodes and is measured by what it changes. The eleven `gap→justified` shifts are the alarming case the ablation exists to show: without node completeness, an argument with an open mandatory question would publish its claim as justified.

| Gate | Result on the v7 input tree |
| --- | --- |
| `cabal build all` / `cabal test all --test-show-details=direct` | pass |
| `cabal exec -- runghc scripts/gen-mutants.hs --check` | 595 mutants byte-identical |
| `make local-gates` | pass |
| `bash scripts/differential.sh` (inside `local-gates`) | 677 verdict anchors, 66 codec negatives; zero failures |
| `bash scripts/admission-differential.sh` | 20 / 20 |
| `bash scripts/test-replay-tamper.sh` | both tamper classes detected |
| `python3 -m unittest scripts/test_freeze_bundle.py -v` | 4 / 4 |

The positive differential grew 669 to 677 from the new located-hole anchors. Reproduce from the clean input commit:

```sh
git checkout be82e970f3d26647a9c8accb084c452544851d6f
cabal build all
(cd lean && lake build)
cabal exec -- runghc scripts/gen-mutants.hs --check
bash scripts/differential.sh
ELAN_TOOLCHAIN=leanprover/lean4:v4.32.0 make measure
cabal exec -- runghc scripts/claim-support.hs
cut -f1-15 measurements/report.tsv | sha256sum
sha256sum measurements/ablation.tsv
```

## Historical freeze record: evaluation freeze v6

v6 was recorded 2026-09-09 and describes 595 mutants + 60 corpus units = 655 measured inputs, measured from clean input commit `bc888a5d4b60438565bcf0922a8a3f04cfc645b8` (`git-dirty: false`). The v6 inputs and outputs shipped in the v0.1.0 release; no `m5-freeze-v6` tag exists in this repository.

The v6 cycle adds S9 (`insp@1`) and batches S2 (`ord@1`) into the same freeze, each adding 27 verified mutants (22 verdict anchors and 5 codec negatives). The seed remains `20260801`; the checker and operators are unchanged. A byte comparison against parent `08ebe6a` verified all 541 old mutant files and all 541 old manifest rows unchanged; only 54 mutant files are added, and `MANIFEST.tsv` and the generated `README.md` are the only existing mutation-suite files modified. All 601 pre-existing report rows retained identical deterministic columns 1 through 15, and every old ablation row is unchanged.

| Outcome | v5 | Added | v6 |
| --- | ---: | ---: | ---: |
| `reject-R1` | 63 | +8 | 71 |
| `reject-R12` | 40 | +4 | 44 |
| `reject-R3` | 19 | +2 | 21 |
| `reject-R4` | 30 | +4 | 34 |
| `reject-R7` | 20 | +4 | 24 |
| `reject-R13` | 43 | +6 | 49 |
| `reject-R11` | 19 | +2 | 21 |
| `reject-R9` | 19 | +2 | 21 |
| `reject-R2` | 113 | +12 | 125 |
| `codec-reject` | 47 | +10 | 57 |

The new certificate cases cover the backend payload decoder (R13) and the certificate theory allowlist (R7). `cert-payload-tamper` writes `mut_corrupt` and does not drop a slot; for S9 it corrupts an `inspect` certificate, while `cert-theory-swap` changes an `inspectdiff` certificate's digest. These are not measurements of every inspection semantic guard or of well-formed false certificates; the backend properties and Lean proofs remain the evidence for those obligations. `MutationSpec.prop_backendCertificateCoverage` requires measured certificate mutants for both backends and replays them to their specified R7/R13 outcomes.

| Input | Count | Git tree SHA |
| --- | --- | --- |
| `fixtures/mutants/` | 595 (538 verdict/status anchors + 57 codec negatives) | `e68a33bf80de8535d64c9483d24626ee0d8c5959` |
| `corpus-units/` | 60 measured units | `cadb5fa62b9f7f6ace14129f1435e3c32b2dff7b` |
| `examples/` | 11 historically measured examples plus additive demonstrators; S2 and S9 now feed mutations | `046c0981e575b6efd944e217dd4b2572855459b2` |

| Output | SHA-256 |
| --- | --- |
| `report.tsv`, `cut -f1-15` | `32aa22cdcbe159d460124c932911848dc776723b7b73c6063755cef3261f7262` |
| `ablation.tsv`, full | `df25144c687e831fb4401eb4ad4f25373e8e987611e69e6aaed82dfabc86e01f` |

Environment: GHC **9.10.3**, Lean **4.32.0** (commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`), Linux/x86_64. The two report timing columns are machine-dependent and excluded from the deterministic hash, and they must not be read as a performance change relative to the v5 macOS/ARM run. Claim-support is Haskell-only and records an empty Lean-version field.

| Metric | v6 result |
| --- | --- |
| Class match | 655 / 655 |
| Haskell–Lean agreement | 655 / 655 |
| Location match and primary | 480 / 480 each (175 not applicable) |
| Corpus replay | 60 / 60 |
| Load-bearing strict steps with checked certificates | 1 / 1 |
| `no-cq` missed rejections | 18, all `reject-IncompleteArgument` |
| `no-typed` missed rejections | 37: 11 R10 + 21 R11 + 5 MissingConflict |
| `no-conflict-scan` missed rejections | 5, all MissingConflict |

`no-typed` grew 35 to 37 solely from the two new `unlicensed-attack` mutants; no ablation configuration changed. Location agreement remains a construction and harness check, not an independent localization-accuracy estimate.

| Gate | Result on the v6 input tree |
| --- | --- |
| `cabal build all` / `cabal test all --test-show-details=direct` | pass |
| `cabal exec -- runghc scripts/gen-mutants.hs --check` | 595 mutants byte-identical |
| `bash scripts/differential.sh` | 669 verdict anchors, 66 codec negatives; zero failures |
| `bash scripts/admission-differential.sh` | 20 / 20 |
| `bash scripts/test-replay-tamper.sh` | both tamper classes detected |
| `cd lean && lake build` | pass (existing linter warnings) |
| `lake env lean AxCheck.lean` piped through `check-axioms.sh` with `pipefail` | pass; standard axiom trio only |
| `python3 -m unittest scripts/test_freeze_bundle.py -v` | 4 / 4 |
| `make presentation-parity` | 78 rows |

The positive differential grew 625 to 669 and the negative 56 to 66, exactly 44 verdict additions and 10 codec additions. Reproduce from the clean input commit, or from `v0.1.0` in this repository, whose `fixtures/mutants/` and `corpus-units/` tree hashes match the table above:

```sh
git checkout bc888a5d4b60438565bcf0922a8a3f04cfc645b8
cabal build all
(cd lean && lake build)
cabal exec -- runghc scripts/gen-mutants.hs --check
bash scripts/differential.sh
ELAN_TOOLCHAIN=leanprover/lean4:v4.32.0 make measure
cabal exec -- runghc scripts/claim-support.hs
cut -f1-15 measurements/report.tsv | sha256sum
sha256sum measurements/ablation.tsv
```

Pinning `ELAN_TOOLCHAIN` makes the measurement harness's root-directory `lean --version` agree with the driver built under `lean/lean-toolchain`, even when the machine's default toolchain differs. Freeze publication verifies all three input tree SHAs and both deterministic output hashes above; do not move an old tag or replace an anchor merely to match an unexplained difference.

## Historical freeze anchors: v1 through v5

Everything in this section describes the earlier freezes and is retained as provenance, not as a description of the current `measurements/frozen/` contents. The `m5-` prefix is legacy: the series is the evaluation-corpus freeze, and the four re-cuts after v1 were unrelated to any milestone (v2 for the `ra@1` certifier, v3 for conservative quarantine reporting, v4 for the `lara-core@0.2` signature bump, v5 for the evaluation-suite completion batch). The name is kept because v1 through v5 are published, addressable anchors and a mid-series rename would give "the freeze after v4" two names; `corpus-units/corpus-v1.policy.lara` is itself a frozen input that references the record by path, so renaming it would change frozen corpus bytes for a cosmetic reason.

The tag and commit anchors are:

| Freeze | Snapshot or measurement commit | Tag |
| --- | --- | --- |
| v1 (358 mutants) | `300b235` (T5 freeze merge commit) | `m5-freeze-v1` (annotated) |
| v2 (360 mutants) | `68e7298` (merge commit of the `ra@1` certifier change) | `m5-freeze-v2` (annotated), cut retroactively alongside v3 |
| v3 (369 mutants, 429 measured) | snapshot `4d5c6ae`, measured at clean `3108a5f` | `m5-freeze-v3` (annotated), on `62eea92` |
| v4 (504 mutants, 564 measured) | snapshot `ced19fe` | `m5-freeze-v4` (annotated), on `f4327b4` |
| v5 (541 mutants, 601 measured) | snapshot `89c25ef`, clean measurement recorded in `report.json` | `m5-freeze-v5` (annotated), on `5dd326b` |

v5's numbers of record are 601 measured inputs (541 mutants + 60 corpus units), class match 601/601, cross-driver agreement 601/601, location match 436/436, location primary 436/436, corpus replay 60/60, one load-bearing strict step carrying a checked certificate, `no-cq` 18 missed rejections (all `reject-IncompleteArgument`), `no-typed` 35 (11 `reject-R10` + 19 `reject-R11` + 5 `reject-MissingConflict`), and `no-conflict-scan` 5 (all `reject-MissingConflict`). The positive differential read 620/0 and the negative 56/0, and presentation parity 73 rows. Measurement environment of record: GHC 9.14.1, Lean 4.32.0, darwin/aarch64.

| v5 frozen input | Count | Git tree SHA |
| --- | --- | --- |
| `fixtures/mutants/` | 541 (494 verdict/status anchors + 47 codec negatives) | `9c174f459d3fd856d306282d1ceb38891e0beff2` |
| `corpus-units/` | 60 measured units | `cadb5fa62b9f7f6ace14129f1435e3c32b2dff7b` |
| `examples/` | 11 measured examples plus additive demonstrators | `34b3451b4afc2a5a30814db8062ea1d69803f9bb` |

| v5 frozen output anchor | SHA-256 |
| --- | --- |
| `report.tsv` deterministic projection (`cut -f1-15`) | `d7396558022965c842e51bb223dce9ef6753325d2a638c2753558239e99aaff0` |
| `ablation.tsv` (full, deterministic) | `503c231a2e9759c1207cbf48dbb9b446466c84237b2cdac2091a26de85821c1b` |

The v5 snapshot absorbed the `insp@1` backend additively: registering a fourth backend changed zero frozen bytes, because no frozen unit selects it, the registry is keyed by `(name, version)`, and `Lara.Replay.supportedBackends` only widens. One deferral is recorded as a cost rather than discovered as one. Adding `S9` to `Lara.Mutate.mutationBases` would give `insp@1` genuine mutation coverage, because the certificate-tampering operators would run against its payloads and theory digests instead of only `nd@1`'s; it was built and verified (27 mutants, all passing the generator's verified-by-construction gate) and then reverted, because it grows the seeded suite 541 to 568 and `fixtures/mutants/` is frozen input row 1, which is a re-cut plus a full axis-(c) re-run. It rode the next freeze cycle. `ord@1` shipped under the same constraint and likewise has no mutation base.

The v4 anchors superseded at v5 are retained as provenance: `report.tsv` (`cut -f1-14`, 564 records) `eae0c82e8c1607a4daf74b8dfb8ecab333996f0e213bcbf22f9b81533add3d7a`, and `ablation.tsv` `23112189212d4e6e154fafa4a7a2d9425e9d77de2b228702f3bf52b29859cdc3`. Both remain correct for the tree `m5-freeze-v4` names.

The intermediate surface releases between v4 and v5 moved no measured byte. `lara-syntax@0.7` (grammar Appendix F) is a surface-only release that restricted three spellings; it moved 10 lines in 7 of 109 tracked `.lara` files, all of the equal form `open X as X`, and no derived byte changed. Two source trees re-pinned because authored `.lara` sources live inside them: `corpus-units/` from `1dc20ea9d79adb2690731a66216dae828a100cf3` to `cadb5fa62b9f7f6ace14129f1435e3c32b2dff7b`, and `examples/` from `4ab6b5f480d9e3bddd94b17908d1c6a910b7944f` to `9e6291fbf1a53703092123a4550ab2099cbed52c`, later to `9ac2b03eec8dd3043ccb9ac99e685265cc69b122` with the S7 addition. `lara-syntax@0.8` (Appendix G) added names to a namespace and removed nothing, so no tracked source moved; `examples/` re-pinned only for the S7 addition. `lara-syntax@0.9` (Appendix H) and `@0.10` (Appendix I) added named `nd@1` proof terms and source-authored formula annotations, and worked example S8 was the additive byte-identity witness for each, with no measured byte changed. Each release moved only the differential gate count by the added anchor.

The v4 mutation tree was `fd7142072d58da4d35642cbad6f144c970627afa`, and the frozen measurement tree was `a067c921e0142eae69b34ed500ff18c7efea1bed`. Both stayed unchanged through the `lara-syntax@0.7` and `@0.8` source-only amendments. These are historical tree anchors, not the current freeze's hashes.

## Freeze protocol

The freeze commits the fixture set, corpus sample, and generator seeds before the final measurement runs, so the final numbers come only from post-freeze runs. It does not add checker or corpus content; it locks what the corpus and mutation work produced and records the reproducibility anchors. The deterministic analogue of a blinded held-out freeze is this freeze.

The frozen inputs are three trees, and the git tree object SHA is itself the content hash of the tree: `fixtures/mutants/`, `corpus-units/`, and `examples/`. The generator seed is `mutationSeed = 20260801` (`src/Lara/Mutate.hs`, SplitMix64, keyed per `(base, operator)`). It is verified byte-identically reproducible: `cabal exec -- runghc scripts/gen-mutants.hs` over the committed tree leaves the generated suite unchanged. CI enforces this between freezes, because the Generated mutation suite is fresh step runs `gen-mutants.hs --check`, so a tree that no longer regenerates its own committed suite fails before it can reach a measurement run.

The post-freeze rule is that any change to a frozen input or the seed invalidates the freeze, and the next tag follows a re-run of the gates. Two mechanisms keep that true between freezes rather than by trust: the `gen-mutants.hs --check` step fails a tree that no longer regenerates its committed suite, and the generator's string-keyed streams (`src/Lara/Mutate/Seed.hs`) make a new operator additive by construction, so intermediate PRs may grow `fixtures/mutants/` without owing a measurement run. The bytes do move if an enumerator's output is reordered or an existing operator is renamed, because `pickWithStream` draws in candidate-list order, so neither is a cosmetic edit and both invalidate the freeze.

The clean-tree verification is the exit criterion that the artifact reproduces the frozen numbers from a fresh clone, not from a working tree. Its written record is deferred to the artifact and release stage, because artifact evaluation runs post-submission. The protocol, when it is produced, is:

```sh
git clone --branch <tag-or-branch> <this-repo> "$SCRATCH/lara-t7"
cd "$SCRATCH/lara-t7" && git submodule update --init
cabal build all && (cd lean && lake build)
cabal exec -- runghc scripts/gen-mutants.hs
bash scripts/differential.sh
bash scripts/admission-differential.sh
bash scripts/test-replay-tamper.sh
(set -o pipefail; cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
cabal test all --test-show-details=direct
python3 scripts/test_freeze_bundle.py -v
cabal exec -- runghc scripts/measure.hs
cut -f1-15 measurements/report.tsv | shasum -a 256
shasum -a 256 measurements/ablation.tsv
```

Two notes carry over from the first execution pass. `scripts/replay.sh` takes a `BUNDLE_DIR` argument, so a bare `bash scripts/replay.sh` is not a gate; replay coverage comes from `scripts/test-replay-tamper.sh` plus the harness `replay_ok` column. And the record must state the environment (GHC, Lean, OS and architecture) and note that the wall-clock columns are excluded from the deterministic projection being hashed. If any gate is red, stop and diagnose; never adjust an anchor to match observed output.

## What the certified-evidence addition does not refreeze

`lara-evidence@0.1` adds the `check-ara` package command. The v8 measurements above remain historical results over declared evidence; they do not measure package capture or extraction and must not be presented as evidence-checked runs. The separate package evaluation and accepted independent payload-to-proposition review were delivered under `evidence-measured-inputs@2`. They do not satisfy the separate archival paper-promotion gate in the evidence design.

The additive evaluation has its own independent freeze, `evidence-measured-inputs@2` (tagged `evidence-measured-inputs-v2`). Its protocol and budget live in `../measurements/frozen/evidence-measured-inputs-v2.md`, and `measurements/frozen/evidence-report-v2.{json,tsv}` record the reviewed and re-pinned original packages. The first content freeze, `../measurements/frozen/evidence-measured-inputs-v1.md` with `measurements/frozen/evidence-report.{json,tsv}`, remains unchanged. Neither is a v9 or an amendment of the 660 v8 inputs, seed, operators, or results. The corpus remains `fixtures/evidence/measured/MANIFEST.tsv`, measured by `scripts/evidence-measure.py` over the real `lara check-ara` door.

The real package acceptance cases and R8 rejection scenarios run in `test/evidence-cli.sh`, and the typed Haskell and Lean cases are pinned in `fixtures/evidence/model/MANIFEST.tsv` and run by `scripts/evidence-differential.sh`. Those gates validate the implemented boundary but do not extend this measured-input snapshot. The contract and trusted base are in [`evidence-admission-design.md`](evidence-admission-design.md).

## Checker performance

E1 is the checker-performance bench: it times the Haskell checker over the frozen evaluation corpus, both the per-unit check cost and one full pass over the harness records, via `make bench`. The numbers in this section are indicative documentation, not frozen evaluation numbers. They describe one machine at one commit; re-run the bench rather than trusting them. The paper's typeset table is generated separately and is not tracked in this repository.

### Running the bench

```sh
make bench                                                 # aligned text (default)
make bench FORMAT=markdown                                 # markdown
make bench FORMAT=latex OUT=../paper/tables/performance.tex
```

The table goes to stdout unless `--out` names a file, and progress goes to stderr, so stdout stays pipeable. Every run also writes the raw per-unit record to `measurements/bench.json`, which is gitignored as regenerable output. `make bench` builds the Haskell benchmark executable and the Lean driver before it runs; a direct `lara-bench --prebuilt` invocation suppresses that build only when an existing Lean driver is present.

A publication measurement uses a pinned Linux/arm64 container on the local Apple M5 Pro:

```sh
make bench-container
```

The host runner requires a clean commit with successful GitHub Actions CI for that exact SHA. It builds the image before measurement, then waits until the macOS one-minute load average remains below `0.5` for 120 continuous seconds; any excursion resets the quiet interval. The timed container has no network, uses a read-only root filesystem, and performs no compilation. A successful run writes `provenance.json`, `bench.json`, and text, Markdown, and LaTeX tables under `measurements/bench-runs/<UTC>-<short-SHA>/`; those regenerable files remain gitignored, and `provenance.json` records the exact CI and job times, host and container resources, the image ID, every quiet-window sample, the timed command, and SHA-256 digests of the four benchmark outputs. For a local wiring smoke test that does not claim a publication measurement, use `BENCH_ARGS="--skip-ci --quiet-seconds 0" make bench-container`; the bypass is explicit in its provenance.

### What is measured

The bench runs the production checker over the frozen corpus units and the manifest-discovered harness, and its protocols are deliberately aligned with `scripts/measure.hs`.

- Haskell sections are in-process and exclude decode. The timed work is `runCheck` plus forcing the rendered verdict text. One check runs in single-digit microseconds, below timer noise, so each section runs the work 100 times and divides; the reported value is the median of 5 such sections.
- Phases are timed against forced outputs, with earlier stages pre-forced: parse (decode plus forced re-encode), validate (replay preflight plus group boundary), check (the six-stage `checkUnitWith`), compile (the cached-adjacency AF and its closure edges), and evaluate (grounded labels plus per-query four-state statuses). Phases are therefore attributable but need not sum to the end-to-end row.
- `parse` is the marginal decode cost inside the real pipeline: end-to-end minus the pre-decoded check and render section.
- The Lean row is full subprocess wall time of the reference driver, startup and decode included. This is a different protocol, reported only to justify why the Lean executable stays a test oracle rather than a production path. No cross-driver ratio may be derived from it.
- The harness sweep pre-reads every manifest input, then times one full in-memory pass (decode, check, and render, or the codec-failure path).
- The multi-artifact map is measured separately and never in these rows, because a `.laramap` run is a different shape of work that scales with member count rather than with one unit's size.

### Native snapshot

Measured on 2026-08-23 at commit `7183c48` of the pre-release development history, which is not part of the published `main`. Setting: 564-record harness; Apple M5 Pro, 64 GB RAM, darwin/aarch64, GHC 9.14.1, Lean 4.32.0; medians over 5 sections of 100 batched runs each.

| | median | worst |
| --- | ---: | ---: |
| Corpus unit, end-to-end (µs) | 523.7 | 580.4 |
| &nbsp;&nbsp;parse (µs) | 319.5 | 366.8 |
| &nbsp;&nbsp;check + render, pre-decoded (µs) | 202.2 | 218.7 |
| &nbsp;&nbsp;validate (µs) | 0.4 | 0.5 |
| &nbsp;&nbsp;check (µs) | 189.9 | 214.2 |
| &nbsp;&nbsp;compile (µs) | 0.5 | 2.0 |
| &nbsp;&nbsp;evaluate (µs) | 1.5 | 2.9 |
| Per-artifact total (27 artifacts, µs) | 1075.8 | 1899.0 |
| Framework size (nodes / edges) | 0 / 0 | 2 / 1 |
| Lean reference driver, subprocess (ms) | 2.9 | 3.3 |
| 564-record harness, one full pass (ms) | 187.8 | |

In one line: checking a corpus unit costs about 200 µs, decoding is the same order of magnitude rather than several times larger, and one pass over all 564 harness records takes under 200 ms. Checking is cheap enough to sit inside an edit loop or a CI step. The `check + render, pre-decoded` row is the stable control, because it sits downstream of the decode boundary and no wire-codec change can move it; a run whose control row deviates markedly from about 203 µs is measuring machine load rather than the checker and should be discarded rather than quoted.

This snapshot's absolute numbers are stale and should not be cited. A review of the harness (no fix planned, 2026-08-24) found that the benchmark harness changed from interpreted (`cabal exec -- runghc scripts/bench.hs`, the driver that produced this snapshot) to compiled (`cabal run exe:lara-bench`) with no protocol line altered, and that the change alone moves every row: a loaded-machine compiled run beat this quiet-machine interpreted snapshot on every metric (end-to-end −22%, parse −31%, check plus render pre-decoded −9.4%, check −8%). Load inflates timings and never deflates them, so the harness is the explanation, not noise. The about-203 µs control-row reference is therefore itself an interpreted-harness artifact, not a compiled-harness baseline, and no corrected snapshot has been produced because no host available to the project reaches the container publication runner's quiet-window gate. Treat every number in this section as an upper bound from a retired harness until a fresh compiled-harness snapshot replaces it.

## The multi-artifact map: a separate protocol

```sh
make bench-map                     # aligned text (default)
make bench-map FORMAT=markdown     # markdown
```

`make bench-map` runs `lara-bench --map`. It measures every accepted `map.laramap` conformance anchor, which are the maps `scripts/check-map-conformance.sh` discovers under `test/fixtures/map/` and `examples/agreement-map-multi/`, and writes the raw record to `measurements/bench-map.json`, which is gitignored. An anchor that does not accept has no full pass to time, so it is left out, and stderr names it with the one-line diagnostic and exit code `lara check` would print: 1 when the checker refuses the map, 2 when the map stops before the checker (a member that cannot be read, a manifest that no longer parses, a reference that does not resolve). A renamed member file therefore shows up as what it is, not as one more refusal. The run fails, with the same diagnostic, if the shipped map is not among the measured ones. Nothing Lean runs, so there is no Lean build step and no LaTeX format: the paper typesets the kernel table, and a map row must never be read as one of its rows.

- Pre-read, then full passes. One untimed pass reads the manifest, its policy, every member and every member's policy into a fresh source cache (`Lara.Map.Load.loadMapWith`). Each timed pass then does everything `lara check <map.laramap>` does after argument parsing, over that cache: load and recheck every member, qualify, merge, saturate, check the linked unit, evaluate, and render the composite verdict. No timed pass reads a file's bytes. Each pass still resolves paths, because `canonicalizePath` is the cache key, and that is the one filesystem call left in the timed work.
- The indented row times the pure stage alone (`checkMap` plus rendering) over members the warm-up pass has already loaded, so the difference between the two rows is the cost of loading and rechecking the members.
- Batching matches the kernel bench: medians over 5 sections of 100 batched runs each, with worst being the slowest section rather than the slowest input.
- Member count, linked nodes, and edges are printed beside each figure, because those are the variables a map's cost scales with.

No number from this table may be set beside the kernel table's. The two protocols time different work on different inputs.

### Map snapshot

Measured on 2026-09-11 at pre-release commit `ad513b5` (not on the published `main`) with `make bench-map FORMAT=markdown`. The one-minute load average was 0.6 on 128 cores. The CPU and RAM fields were supplied through `LARA_BENCH_HOST_CPU` and `LARA_BENCH_HOST_RAM_BYTES`, because at that commit the environment probe read only macOS `sysctl`; the Linux probe (`/proc/cpuinfo`, `/proc/meminfo`) landed afterwards, so the next snapshot needs no overrides. Like the kernel snapshot, this is indicative: re-run it rather than cite it. Setting: 3 accepted map anchors; AMD EPYC 9354 32-Core Processor, 1507 GB RAM, linux/x86_64, GHC 9.10.3; every file pre-read by one untimed pass (paths are still resolved per pass); medians over 5 sections of 100 batched runs each.

| | median | worst |
| --- | ---: | ---: |
| test/fixtures/map/agreement (3 members, 3 nodes / 2 edges, µs) | 1729.2 | 1742.6 |
| &nbsp;&nbsp;link + check + render, members pre-loaded (µs) | 148.8 | 154.8 |
| test/fixtures/map/merge (2 members, 2 nodes / 2 edges, µs) | 630.0 | 645.0 |
| &nbsp;&nbsp;link + check + render, members pre-loaded (µs) | 60.8 | 62.5 |
| examples/agreement-map-multi (4 members, 4 nodes / 2 edges, µs) | 2778.2 | 2808.1 |
| &nbsp;&nbsp;link + check + render, members pre-loaded (µs) | 272.9 | 276.8 |

In one line: the shipped four-member map costs about 2.8 ms per full pass, and about nine tenths of that is loading and rechecking its members; linking, the linked check, evaluation, and rendering together take about 0.27 ms. The three maps differ in what their members contain as well as in how many there are, so the rows show that cost follows the members' work. They are not a scaling curve.

## Why no rendered table is committed

A timing table is machine state, not source: it is valid only for the machine and the commit that produced it, so tracking a rendered table guarantees that sooner or later the copy in the tree disagrees with the code beside it. That is exactly what happened. `tables/performance.tex` was generated at pre-release commit `0aa97ef`, before two later wire optimizations, and then sat in the repository reporting a `parse` row that no longer described the shipped decoder, a byte-identical hand-synced duplicate of the paper repository's copy and the stale one of the two. `measurements/` was already gitignored under precisely this rule; the rendered table was the inconsistent exception.

So the bench prints, and each consumer owns its copy. The paper repository owns the `tables/performance.tex` it typesets and refreshes it with one `make bench FORMAT=latex OUT=…`; this document owns a dated, explicitly indicative snapshot for readers who want an order of magnitude without building the project. The snapshot may drift, which is acceptable because it is dated and labelled and because nothing typesets it into a submitted claim.
