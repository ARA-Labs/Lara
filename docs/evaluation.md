# Evaluation

This document defines Lara's evaluation metrics, mutation-generation contracts, frozen input and output hashes, and performance benchmarks. The current base-language freeze is v8; superseded freezes are listed by anchor only. The separate certified-evidence evaluation is documented in [the measured-input freeze](../measurements/frozen/evidence-measured-inputs-v2.md).

## What the evaluation covers

The frozen evaluation covers the LLM-independent axes only: axis (a), mutation and differential testing, and the checker side of axis (c), the localization and ablation measurements. The human-authored natural-defect ablation and every LLM-producer and annotator axis (axes b and d) are out of scope and are deliberately not in this freeze.

A *corpus unit* is a checked program lowered from a real research artifact. A *mutant* is a controlled edit with an expected outcome: rejection-class mutants must fail at the specified class and location, while accept mutants exercise valid changes in status or diagnostics. The corpus sample is the hand-lowered semantic-study sample.

One stance governs every metric here: measurements are reported, not gated. Class match is the only gate. The harness records `location_match`, `location_primary`, agreement, and ablation deltas, but a lower value on any of them is evidence rather than a build failure, and a gate that would make a rate move is deliberately avoided (see the location caveat below).

## The measurement harness

One command, with manifest-driven discovery, produces the measurement records:

```sh
cabal exec -- runghc scripts/measure.hs
```

It emits `measurements/{report,ablation}.{json,tsv}` over the measured inputs; `scripts/claim-support.hs` emits the claim-support aggregation and the committed `measurements/binding-audit/worklist.tsv`. The canonical aggregate snapshot is committed under `measurements/frozen/`; other working measurement outputs remain gitignored as regenerable output. `measurements/binding-audit/**` is frozen input, excluded from regeneration.

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

For a single-defect row the list is the singleton of its seeded site, so both metrics degenerate to plain equality with that site.

Ground truth means the predicted *manifestation* site, not the edit site. For every single-site operator the two coincide; for an off-site operator they do not, by construction, so an edit to the policy whose manifestation is an argument's support failure has ground truth `[arg:i]`, not `[policy]`. The operator's site enumerator owns the prediction, per operator, the same way it owns the expected class.

The checker reports exactly one location, because `checkUnitWith` is fail-fast (`Either UnitError CheckedUnit`, one error, one located constituent), and there is no report-all-defects mode: the frozen acceptance boundary and its Lean mirror are fail-fast. Because the seven-stage order is public contract and constituents within a stage are visited in declaration-index order, the reported location is deterministic and computable at generation time. There is therefore no search quality to benchmark: localization here is not a ranking problem. The honest claims are faithfulness (the reported constituent is genuinely defective) and ordering conformance (it is the one the stage order designates first), and both are falsifiable by an implementation or modelling error.

The metric is discriminating through three families of mutant, in order of value:

1. Off-site families, where the edit site and the manifestation site differ, so ground truth is a genuine prediction that a mislocating implementation or a wrong model of the cascade fails. This is the strongest gate the suite can state.
2. Multi-defect families crossing stage boundaries, for example a support defect in `arg:i` with an attack defect at `attack:j`, which make `location_primary` test that stage order rather than accident chose the report.
3. Multi-defect families within one stage, where two defective arguments test the declaration-index order.

These families do not make the reported rate move. Every published site is gated against the checker before it reaches `MANIFEST.tsv`: `prop_siteMatchesChecker` pins every list's head to the constituent `runCheckLocated` actually reports, and `prop_localizationSites` pins the tails by re-deriving each composite's set from the mutant and re-running the checker with the head defect reverted. A row whose ground truth the checker disagrees with fails CI at generation time and never becomes a measured row, so `location_match` and `location_primary` are 100% on the committed suite by construction, exactly as the single-defect families were, under a strictly stronger construction. What the families buy is the strength of that gate, not the value of the rate: their ground truth is a genuine prediction that a mislocating checker fails.

The caveat below is the canonical statement of this and must travel with the headline number.

> `location_match` is ≈100% by construction and stays that way — every published site is checker-gated before it reaches `MANIFEST.tsv`, so a mislocating ground truth fails CI instead of lowering the rate. The off-site and multi-defect rows add a stronger gate, not a number that moves; the ordering claim is `location_primary`, reported separately.

In code, `mutantSites` and `imExpectedLocation` (`src/Lara/Measure.hs`) are `Maybe SeededSites`, a newtype over `NonEmpty Constituent`, with `Nothing` meaning no seeded site. The non-empty type keeps an enumerator that accidentally publishes an empty list from passing for one that seeds nothing, which would drop the row from the location denominator instead of counting it as a miss. `detLocationMatch` is membership and `detLocationPrimary` is head equality. Manifest column 8 spells the list as elements joined by `,` in ground-truth order (`arg:0,attack:2`), and `-` means no seeded site. `GroupId` is free-form, so the list codec rejects group ids containing `,` to keep the round-trip unambiguous. `report.tsv` carries `location_primary` immediately after `location_match`.

## Mutation generation and module ownership

`Lara.Mutate` generates the mutants. This section fixes which of its modules owns what, because the mutation suite's byte-stability depends on the layout. The seeded stream is keyed `(base, operator)` through `opName`, and selection draws from each enumerator's list in order, so a reordered constructor, a reordered `mutantsForBase` entry, a reordered comprehension, or a renamed operator moves committed bytes and invalidates the freeze. Byte-identical regeneration of the frozen suite is therefore the correctness gate for any change to this namespace. Operator registration is not consolidated in one place: adding an operator takes coordinated vocabulary, metadata, generator, assembly, and sweep edits.

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

The graph is acyclic because nothing the root imports imports it back. The root has exactly one sibling import, `Outcome`, which imports no sibling in turn and so is the bottom of the namespace. That is the load-bearing property of the arrangement, and it is what the re-export rule below protects.

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

`Outcome`, `Seed`, `Sites`, `Sites.Cert`, `Sites.Conflict`, `Sites.Localize`, `Sites.Nav`, `Accept.Ops`, and `Accept.Build` are in `other-modules`, so the package's public surface does not grow, with one exception. `prop_conflictSiteMatchesChecker` compares the enumerator's predicted conflict pair against the checker's and therefore calls `dropCoveringAttackSites` directly; since `Sites.Conflict` is an `other-module`, the name is re-exported from `Suite`, which is exposed. It is the only test-only public name. Any further such re-export should be weighed against a test-only `.Internal` module instead. `Sites` is the only importer of `Sites.Cert` and `Sites.Conflict` and re-exports their enumerators, so `Suite` sees one module for them. `Sites.Nav` is the shared navigation layer, imported by `Sites.Cert`, `Sites.Conflict`, `Sites.Localize`, and `Sorts`. `splitMix64` and `stringSeed` stay private inside `Seed`.

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

### Re-export rule

`Lara.Mutate` exports what it owns, plus the `Outcome` names it re-exports because `Mutant` carries one of them. It does not re-export the generators in `Sites`, `Suite`, `Codec`, `Cycle`, and `Accept`, and a future change should not add such a re-export. A root that re-exported them would have to import them, and every generator sibling imports the root for the operator vocabulary and the `Mutant`/`Expected` core, so that import would close a cycle.

`Lara.Mutate.Outcome` sits below the root, not above it: it imports no sibling and in particular does not import `Lara.Mutate`. The direction is forced by the data, because `Mutant` has an `Expected` field, and it is what makes the re-export cycle-free where a generator re-export would not be. Because the root re-exports its names, `Outcome` stays an `other-module` and importers reach `Expected` and its spellings through `Lara.Mutate`.

A re-export from the root is admissible only for a module the root itself imports, that is, one strictly below it in the graph. Everything above it stays a hard split.

### What each module owns

Each module owns one seam. `Outcome` owns the specified-outcome vocabulary (`Expected` and its spellings). `Seed` owns the SplitMix64 stream, `Manifest` the `MANIFEST.tsv` contract, `Codec` the codec-negative family, and `Cycle` the constructed rebut-cycle family. `Sites` owns the per-operator site enumerators, with the certificate family in `Sites.Cert`, the conflict mirror in `Sites.Conflict`, the localization family in `Sites.Localize`, and the shared structural navigation in `Sites.Nav`. `Sorts` owns the signature and sort operators. The frozen public `mutationSeed` constant and the operator metadata function `codecDiagnostics` stay in the root, which keeps `Seed` internal.

`codecDiagnostics` cannot move to `Outcome`. Its type is `MutationOp -> Maybe (String, String)`, so an `Outcome` that owned it would import the root for `MutationOp`, while the root already imports `Outcome` for `Expected` because `Mutant` has an `Expected` field. That is a cycle, and resolving it would require `MutationOp` and `Mutant` to part company, a larger redesign than the seam calls for. So the seam cuts at `Expected` and its spellings only.

`Lara.Mutate.Suite` owns both the corpus sweep (`sweepOps`, `corpusMutants`) and the worked-example assembly (`mutantsForBase`, `unitMutants`), because they are the same job over two base populations and share `unitMutants` and the operator order. `Suite` means seeded rejection-suite assembly, not the complete fixture suite; `scripts/gen-mutants.hs` combines it with the codec, cycle, and accept families.

The accept-verdict family is a facade over two modules. `Lara.Mutate.Accept` is the facade and the family's whole public surface (`acceptMutants`, `acceptStructureOk`); `Lara.Mutate.Accept.Ops` holds the six constructions and the vocabulary each injects; `Lara.Mutate.Accept.Build` holds mutant assembly, the asserted justified-unit invariants, and the attack-site helpers. The dependency order is forced: every operator emits through `acceptMutantWith`, so a facade that both listed the operators and owned the assembly would close an import cycle.

### Module size

There is no numeric line bound in this namespace, and CI does not measure one. Module boundaries follow the re-export rule and the seams above. Each split here follows a seam that is visible in the export list (specified outcome versus operator vocabulary, certificate family versus shared navigation, operator constructions versus mutant assembly), not a line count. Split when a nameable seam appears: a group of definitions with its own vocabulary, its own dependencies, or its own reason to be read alone. Length is a hint that one may have appeared, not by itself a reason to cut, and a module that is long because it is well documented is not a module to split.

## The index-space contract the site enumerators publish

The checker does not run on the declared unit; it runs on the §4.3 quarantine of it. This contract is frozen here because it is split across three modules and is not reconstructable from any one of them.

- The published `si`/`ti` are in checked index space. The scan cache, the coverage decider, and the emitted `Lara.Diagnostics.CConflictPair` all index the checked unit. `Lara.Diagnostics` builds the verdict's pair as `CConflictPair (mcSourceIndex mc) (mcTargetIndex mc)` with no remapping, so checked space is the space the verdict names, and the mirror must name the same one or the answer key is wrong.
- The deletion is in declared index space. The mutation edits `unitAttacks` of the declared unit, because that is what gets re-encoded.
- `Lara.Blocked.retainedAttackIndices` is the sole bridge between the two spaces. Entry `i` of it is the declared index of checked attack `i`.

Soundness rests on attack deletion commuting with the prune, which holds because the kept-argument set is attack-independent: `pruneWithPolicySeed` derives it from the policy seed and inconsistent-group members via `supportUsesLeafSet` over arguments, strictly before any attack is examined. Deleting retained declared attack `d` therefore prunes to exactly the checked attack list minus entry `i`. Deleting a pruned attack is an accepting no-op, which is why only retained attacks are candidate sites.

The mapping, not a guard, is what makes the published pair correct: a declared-space mirror would publish a plausible but wrong pair on a quarantining base rather than failing loudly. The R9 pre-scan gate (`Lara.Driver.groupConflictReject`) is a separate condition: it excludes bases the driver rejects before the scan, where no deletion could yield `MissingConflict` at all.

No Lean entry is owed for this. The prune's attack-retention predicate is already mechanized: `Admission.buildPrune`'s `keepAttack` is exactly "both endpoints ∈ keptIds" (`lean/Lara/Admission.lean` `retained_attack_endpoints`, axiom-checked), and `retained_attacks_selectAligned` with `RawAttack.resolve_filter_commute` pins that the checker consumes exactly that filtered sublist. `retainedAttackIndices` only re-expresses that proved filter as an index list for the generator, so it introduces no new definition the proofs do not already quantify over. This is the strong form of the exemption argument, not the weak "the type has no counterpart" form, which is false here anyway, since a `retainedIndices` counterpart exists at `lean/Lara/BlockedProgram.lean`.

The contract is guarded by `test/BlockedSpec.hs` `prop_retainedAttackIndices` (the bridge is an exact projection, with `CheckSpec.quarantiningConflictBase` supplying the gapped retained list `[1]` that makes it non-vacuous) and `test/MutationSpec.hs` `prop_conflictSiteQuarantiningBase` and `prop_conflictSiteMatchesChecker` (the published pair is the one the checker reports). No corpus base declares a `groups` form, so on every committed mutant `retainedAttackIndices == [0..n-1]`, and the quarantining path is reachable only from the in-memory fixtures.

### Generalized to every enumerator

The contract binds every site enumerator, not `Sites.Conflict` alone. The bullets below are the contract for all of them.

- Sites are drawn from the checked unit. `Sites.Nav`'s `argSites`, `ruleSites`, `leafSites`, and `attackSites` read a `Prune`, not a `Unit`. A mutation into pruned material is an accepting no-op the checker never sees, so it can witness nothing, and self-gating on retained material is part of the contract, not an optimization. This binds the space-free enumerators too: the `Lara.Mutate.Sorts` leaf and θ operators publish `CPolicy`, which needs no mapping, but still draw their sites from retained leaves and arguments.
- Every indexed constituent is published in checked space. `CArgument`, `CAttack`, and `CConflictPair` all index the checked unit, because that is the space `Lara.Diagnostics` names in the verdict. `CPolicy`, `CGroup`, and `CReplayEnvelope` are space-free and are published as-is.
- Only the rewrite maps back to declared space, and the three retained-index lists are the sole bridges: `Lara.Blocked.retainedIndices` (arguments), `retainedAttackIndices` (attacks), and `retainedLeafIndices` (leaves).

The two spaces are types, not a naming convention. `Sites.Nav` exports `CheckedIx` and `DeclaredIx` newtypes and the site tuples pair them; `rewriteArg`, `setAttackAt`, and `dropAttackAt` take a `DeclaredIx`. A transposed pair is a compile error rather than a silently corrupted answer key. The invariant is not a count of unwrap sites; it is that nothing pairs the two spaces except a retained-index list. Construction is either from such a list (`argSites` and `attackSites` in `Sites.Nav`, `retainedLeafDecls` and `retainedArgDecls` in `Sorts`) or directly in checked space from a measurement of the checked unit, which pairs nothing (`unlicensedAttackSites`' `CheckedIx (length (unitAttacks checked))` is the one such site). `Constituent` and the `Lara.Blocked` retained-index lists keep their bare-`Int` APIs.

The quarantining path is exercised only from in-memory fixtures (`CheckSpec.quarantiningConflictBase` and the derived skew), so no committed mutant file walks it. Adding a quarantining corpus base forces a full corpus regeneration and a freeze-tag bump, which must be budgeted rather than discovered.

There is one known boundary, and it fails closed. A leaf-mutating operator striking a member of a consistent group would flip that group inconsistent, turning the mutant's outcome into R9/quarantine instead of R2. No base carries a consistent group; if one enters the corpus, `scripts/gen-mutants.hs`'s per-mutant `verify` and `prop_siteMatchesChecker` both fail loudly at that point.

The contract for every enumerator is guarded by `test/MutationSpec.hs` `prop_siteMatchesChecker` (every site of every enumerator, over the worked examples, all corpus units, the quarantining fixture, and a skewed sibling of each, rejects with its specified outcome at exactly the predicted `Constituent`, which is what turns `expected-location` from a measured column into a gated one), `prop_sitesQuarantiningBase` (the hand-checked absolute pins on the fixture), and `prop_siteDirectionSkewed`. That last property covers the `ruleSites`-based enumerators, which the quarantining fixture cannot exercise because it has no rules, so without it a per-operator transposition would fail open. `quarantineSkewed` gives every base a skewed sibling by prepending an inconsistent group, an argument on one of its members, and an attack targeting that argument, all declared first, so quarantine removes exactly the added material and the checked unit is the original base; the property then states the mapping itself and carries an anti-vacuity gate.

`retainedLeafIndices` owes no Lean entry, for the same strong-form reason. `Admission.buildPrune` proves `p.removedLeaves = leaves.filterMap …` and `p.checkedLeaves = Groups.quarantineLeaves qs leaves` (`lean/Lara/Admission.lean:764-765`), the argument-side `retainedIndices` counterpart exists at `lean/Lara/BlockedProgram.lean:80` with axiom-checked theorems, and `retainedLeafIndices` only re-expresses an already-proved filter as an index list for the generator.

## Frozen provenance: current evaluation freeze v8

The committed `measurements/frozen/` snapshot is v8. It describes 600 mutants + 60 corpus units = 660 measured inputs under `lara-core@0.3`, measured from clean input commit `59a94c866c2214ef1042c3b83fb6480da3bcf17d` (`git-dirty: false`). v8 has no tag; the clean input commit is its anchor.

### Scope

The generator seed is `20260801`. Hole rows locate their obligations: each obligation names the rule occurrences that leave it open. All 48 `gap` corpus units declare their incomplete argument, carry one located hole, and keep status `gap`; the corpus `MANIFEST.tsv` records the count in its `located_holes` column, and a unit with a located hole is measured as `accept-located-hole`. Two of those units also declare their dead-end undercut against the hole, which is inert. The `hole-obligation` operator seeds only complete arguments. The regeneration diffs against the superseded v7 tree are recorded in `measurements/frozen/corpus-relowering-v8-diffs.md`.

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
| Claim support | 171 leaves, 38 load-bearing; 5 typed attacks, 4 dead-end-sourced; binding-audit subjects: 1 strict step and 3 attacks |

The corpus row is the headline: on the real sample, without node completeness, 46 of the 48 claims whose argument leaves a mandatory question open would publish as `justified`.

### Verification and reproduction

| Gate | Result on the v8 input tree |
| --- | --- |
| `cabal build all` / `cabal test all --test-show-details=direct` | pass |
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

## Superseded freezes

Superseded freezes are listed by anchor only:

| Freeze | Measured inputs | Anchor | Record |
| --- | --- | --- | --- |
| v7 | 655 (595 mutants), `lara-core@0.3` | clean input commit `be82e970f3d26647a9c8accb084c452544851d6f`, no tag | `measurements/frozen/lara-core-0.3-regeneration-diffs.md` |
| v6 | 655 (595 mutants) | clean input commit `bc888a5d4b60438565bcf0922a8a3f04cfc645b8`; the `v0.1.0` tag carries the same `fixtures/mutants/` and `corpus-units/` trees | the frozen trees at `v0.1.0` |
| v5 | 601 (541 mutants) | `m5-freeze-v5` | none in this repository |
| v4 | 564 (504 mutants), `lara-core@0.2` | `m5-freeze-v4` | `measurements/frozen/lara-core-0.2-regeneration-diffs.md` |
| v1 to v3 | 358, 360, and 369 mutants | `m5-freeze-v1` to `m5-freeze-v3` | none in this repository |

The `m5-freeze-*` tags belong to the pre-release history and do not resolve in this repository.

## Freeze protocol

The freeze commits the fixture set, corpus sample, and generator seeds before the final measurement runs, so the final numbers come only from post-freeze runs. It does not add checker or corpus content; it locks what the corpus and mutation work produced and records the reproducibility anchors. The deterministic analogue of a blinded held-out freeze is this freeze.

The frozen inputs are three trees, and the git tree object SHA is itself the content hash of the tree: `fixtures/mutants/`, `corpus-units/`, and `examples/`. The generator seed is `mutationSeed = 20260801` (`src/Lara/Mutate.hs`, SplitMix64, keyed per `(base, operator)`). It is verified byte-identically reproducible: `cabal exec -- runghc scripts/gen-mutants.hs` over the committed tree leaves the generated suite unchanged. CI enforces this between freezes, because the Generated mutation suite is fresh step runs `gen-mutants.hs --check`, so a tree that no longer regenerates its own committed suite fails before it can reach a measurement run.

The post-freeze rule is that any change to a frozen input or the seed invalidates the freeze, and the next tag follows a re-run of the gates. Two mechanisms keep that true between freezes rather than by trust: the `gen-mutants.hs --check` step fails a tree that no longer regenerates its committed suite, and the generator's string-keyed streams (`src/Lara/Mutate/Seed.hs`) make a new operator additive by construction, so changes between freezes may grow `fixtures/mutants/` without owing a measurement run. The bytes do move if an enumerator's output is reordered or an existing operator is renamed, because `pickWithStream` draws in candidate-list order, so neither is a cosmetic edit and both invalidate the freeze.

The clean-tree verification is the exit criterion that the artifact reproduces the frozen numbers from a fresh clone, not from a working tree. The protocol is:

```sh
git clone --branch <tag-or-branch> <this-repo> "$SCRATCH/lara-clean"
cd "$SCRATCH/lara-clean" && git submodule update --init
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

`scripts/replay.sh` takes a `BUNDLE_DIR` argument, so a bare `bash scripts/replay.sh` is not a gate; replay coverage comes from `scripts/test-replay-tamper.sh` plus the harness `replay_ok` column. A verification record states the environment (GHC, Lean, OS and architecture) and notes that the wall-clock columns are excluded from the deterministic projection being hashed. Pinning `ELAN_TOOLCHAIN` makes the measurement harness's root-directory `lean --version` agree with the driver built under `lean/lean-toolchain`, even when the machine's default toolchain differs.

Freeze publication verifies all three input tree SHAs and both deterministic output hashes. If any gate is red, stop and diagnose; never move a tag or adjust an anchor to match observed output.

## What the certified-evidence addition does not refreeze

`lara-evidence@0.1` adds the `check-ara` package command. The v8 measurements above are results over declared evidence; they do not measure package capture or extraction and must not be presented as evidence-checked runs.

The separate certified-evidence evaluation is the `evidence-measured-inputs@2` freeze (tagged `evidence-measured-inputs-v2`). Its protocol and budget live in [the measured-input freeze](../measurements/frozen/evidence-measured-inputs-v2.md), and `measurements/frozen/evidence-report-v2.{json,tsv}` record the measured packages. It is not a v9 and does not amend the 660 v8 inputs, seed, operators, or results. Its corpus is `fixtures/evidence/measured/MANIFEST.tsv`, measured by `scripts/evidence-measure.py` over the real `lara check-ara` door.

The real package acceptance cases and R8 rejection scenarios run in `test/evidence-cli.sh`, and the typed Haskell and Lean cases are pinned in `fixtures/evidence/model/MANIFEST.tsv` and run by `scripts/evidence-differential.sh`. Those gates validate the implemented boundary but do not extend this measured-input snapshot. The contract and trusted base are in [`evidence-admission-design.md`](evidence-admission-design.md).

## Checker performance

E1 is the checker-performance bench: it times the Haskell checker over the frozen evaluation corpus, both the per-unit check cost and one full pass over the harness records, via `make bench`. Bench timings are not frozen evaluation numbers: they describe one machine at one commit, and no timing snapshot is published here. Run the bench to obtain numbers. The paper's typeset table is generated separately and is not tracked in this repository.

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
- The `check + render, pre-decoded` row is the stable control, because it sits downstream of the decode boundary and no wire-codec change can move it. A run whose control row deviates markedly from repeated runs on the same machine and commit is measuring machine load rather than the checker and should be discarded rather than quoted.

## The multi-artifact map: a separate protocol

```sh
make bench-map                     # aligned text (default)
make bench-map FORMAT=markdown     # markdown
```

`make bench-map` runs `lara-bench --map`. It measures every accepted `map.laramap` conformance anchor, which are the maps `scripts/check-map-conformance.sh` discovers under `test/fixtures/map/` and `examples/agreement-map-multi/`, and writes the raw record to `measurements/bench-map.json`, which is gitignored. An anchor that does not accept has no full pass to time, so it is left out, and stderr names it with the one-line diagnostic and exit code `lara check` would print: 1 when the checker refuses the map, 2 when the map stops before the checker (a member that cannot be read, a manifest that no longer parses, a reference that does not resolve). A renamed member file therefore shows up as what it is, not as one more refusal. The run fails, with the same diagnostic, if the shipped map is not among the measured ones. Nothing Lean runs, so there is no Lean build step and no LaTeX format: the paper typesets the kernel table, and a map row must never be read as one of its rows.

- Pre-read, then full passes. One untimed pass reads the manifest, its policy, every member and every member's policy into a fresh source cache (`Lara.Map.Load.loadMapWith`). Each timed pass then does everything `lara check <map.laramap>` does after argument parsing, over that cache: load and recheck every member, qualify, merge, saturate, check the linked unit, evaluate, and render the composite verdict. No timed pass reads a file's bytes. Each pass still resolves paths, because `canonicalizePath` is the cache key, and that is the one filesystem call left in the timed work.
- For each map, an indented row times the pure stage alone (`checkMap` plus rendering) over members the warm-up pass has already loaded, so the difference between the two rows is the cost of loading and rechecking the members.
- Batching matches the kernel bench: medians over 5 sections of 100 batched runs each, with worst being the slowest section rather than the slowest input.
- Member count, linked nodes, and edges are printed beside each figure, because those are the variables a map's cost scales with.

No number from the map table may be set beside the kernel table's. The two protocols time different work on different inputs.

## Why no rendered table is committed

A timing table is machine state, not source: it is valid only for the machine and the commit that produced it, so a tracked rendered table eventually disagrees with the code beside it. `measurements/` is gitignored under the same rule.

The bench prints, and each consumer owns its rendered copy. The paper repository owns the `tables/performance.tex` it typesets and refreshes it with one `make bench FORMAT=latex OUT=…`.
