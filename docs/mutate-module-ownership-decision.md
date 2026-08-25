# Decision: module ownership in the `Lara.Mutate` namespace

_Records the settled ownership contract for the seeded mutation generators
after the seven-module split (issue #122, PR #142). The implementation plan that
produced the split was deleted when the work landed, per the `plans/` rule; this
record carries its durable decisions — which module owns what, what the root may
and may not re-export, and which alternatives were rejected. Companion
to `docs/m5-freeze-checklist.md` (the freeze the generators feed) and the root
module Haddock in `src/Lara/Mutate.hs` (the same graph, stated for readers of the
code)._

## The namespace

`A → B` is an import inside the `Lara.Mutate` namespace.

```
Lara.Mutate                 core; imports only Outcome
├── Outcome ─────────────→ (no sibling; the specified-outcome vocabulary)
├── Manifest ─────────────→ core
├── Seed ─────────────────→ core
├── Sites ────────────────→ core + Sites.Cert + Sites.Conflict + Sites.Nav
│   ├── Sites.Cert ───────→ core + Sites.Nav
│   ├── Sites.Conflict ───→ core (no sibling; mirrors the checker)
│   ├── Sites.Localize ───→ core + Sites + Sites.Nav (imports the facade; not re-exported)
│   └── Sites.Nav ────────→ (no sibling; structural only)
├── Suite ────────────────→ core + Seed + Sites + Sites.Localize + Sorts
├── Codec ────────────────→ core
├── Cycle ────────────────→ core + Seed
├── Accept ───────────────→ core + Accept.Ops + Accept.Build
│   ├── Accept.Ops ───────→ core + Accept.Build
│   └── Accept.Build ─────→ core
└── Sorts ────────────────→ core
```

The graph is acyclic **because nothing the root imports imports it back**. Since
#157 the root has exactly one sibling import, `Outcome`, which imports no sibling
in turn and so is the new bottom of the namespace. That is the load-bearing
property of the whole arrangement, and it is what D1 below protects.

### Export ownership

| Module | Exported names |
|---|---|
| `Lara.Mutate` | `MutationOp(..)`, `opName`, `OpFamily(..)`, `opFamily`, `familyText`, `codecDiagnostics`, `Mutant(..)`, `mutantFileName`, `mutationSeed`, `mutationBases`, plus `Expected(..)`, `expectedText`, `parseExpected`, `statusText` re-exported from `Outcome` |
| `Lara.Mutate.Outcome` (internal) | `Expected(..)`, `expectedText`, `parseExpected`, `statusText` |
| `Lara.Mutate.Manifest` | `mutantPath`, `manifestFor` |
| `Lara.Mutate.Seed` (internal) | `streamForKey`, `streamFor`, `pickWithStream`, `pickSome` |
| `Lara.Mutate.Sites` (internal) | the sixteen per-operator site enumerators, four of them re-exported from `Sites.Cert` and `Sites.Conflict` |
| `Lara.Mutate.Sites.Cert` (internal) | `certTheorySwapSites`, `certPayloadSites`, `certWrongFractionSites`, `bumpWitness` |
| `Lara.Mutate.Sites.Conflict` (internal) | `dropCoveringAttackSites` |
| `Lara.Mutate.Sites.Localize` (internal) | `retractRuleSites`, `twinSupportDefectSites`, `crossStageDefectSites` |
| `Lara.Mutate.Sites.Nav` (internal) | `occurrences`, `rewriteAt`, `rewriteArg`, `ruleSites`, `leafSites`, `ruleOf`, `inequivLeaf` |
| `Lara.Mutate.Suite` | `mutantsForBase`, `corpusBudget`, `corpusMutants`, `corpusSweepReport`, `dropCoveringAttackSites` (re-export, tests only) |
| `Lara.Mutate.Codec` | `codecMutantsForBase` |
| `Lara.Mutate.Cycle` | `cycleMutants` |

`Outcome`, `Seed`, `Sites`, `Sites.Cert`, `Sites.Conflict`, `Sites.Localize`,
and `Sites.Nav` are in `other-modules`: their names had to become
module-visible so `Suite`, `Cycle`, `Sites`, and the root could consume them,
but keeping them out of `exposed-modules` means the package's public surface
does not grow — with one deliberate exception. The
#158 review added a property (`prop_conflictSiteMatchesChecker`) that has to
compare the enumerator's *predicted* conflict pair against the checker's, which
means calling `dropCoveringAttackSites` directly; going through `mutantsForBase`
sees only the seeded subset and the rendered bytes. Since `Sites.Conflict` is an
`other-module`, the name is re-exported from `Suite`, which *is* exposed. That
grows the public API by exactly one name, recorded here rather than left to be
discovered. Any further such re-export should be weighed against a test-only
`.Internal` module instead. `Sites` is the only importer of its
three children, and it re-exports their enumerators, so `Suite` still sees one
module. `splitMix64`
and `stringSeed` stay private inside `Seed` — the old "exposed for tests"
heading was stale, no test or script imported either name.

### Import ownership

| Module | Imports |
|---|---|
| `Lara.Mutate` | `Data.Word`, `Lara.Diagnostics`, `Lara.Mutate.Outcome` |
| `Outcome` | `Lara.AST` |
| `Seed` | `Data.Bits`, `Data.Char`, `Data.Word`, `Lara.Mutate` |
| `Manifest` | `Lara.Diagnostics`, `Lara.Mutate` |
| `Sites` | `Data.List`, `Lara.AST`, `Lara.Diagnostics`, `Lara.Prop`, `Lara.Sigma`, `Lara.SupportTerm`, `Lara.Mutate`, `Lara.Mutate.Sites.Cert`, `Lara.Mutate.Sites.Conflict`, `Lara.Mutate.Sites.Nav` |
| `Sites.Cert` | `Data.Ratio`, `Lara.AST`, `Lara.Diagnostics`, `Lara.Strict`, `Lara.Strict.Cell`, `Lara.Strict.RA`, `Lara.Mutate`, `Lara.Mutate.Sites.Nav` |
| `Sites.Conflict` | `Lara.AST`, `Lara.Attack`, `Lara.Blocked`, `Lara.Check`, `Lara.Compile`, `Lara.Diagnostics`, `Lara.Driver`, `Lara.Policy`, `Lara.Prop`, `Lara.SupportTerm`, `Lara.Mutate` |
| `Sites.Localize` | `Data.List`, `Data.List.NonEmpty`, `Data.Maybe`, `Lara.AST`, `Lara.Blocked`, `Lara.Diagnostics`, `Lara.Policy`, `Lara.Sigma.WellSorted`, `Lara.Mutate`, `Lara.Mutate.Sites`, `Lara.Mutate.Sites.Nav` |
| `Sites.Nav` | `Data.List`, `Lara.AST`, `Lara.Prop` |
| `Suite` | `Lara.AST`, `Lara.Diagnostics`, `Lara.Replay`, `Lara.Wire`, `Lara.Mutate`, `Lara.Mutate.Seed`, `Lara.Mutate.Sites`, `Lara.Mutate.Sites.Localize`, `Lara.Mutate.Sorts` |
| `Codec` | `Lara.Strict`, `Lara.Wire`, `Lara.Mutate` |
| `Cycle` | `Lara.AST`, `Lara.Prop`, `Lara.Replay`, `Lara.Sigma`, `Lara.Wire`, `Lara.Mutate`, `Lara.Mutate.Seed` |

## D1 — Hard split, not a re-export façade

`Lara.Mutate` exports what it owns, plus the `Outcome` names it re-exports
because `Mutant` carries one of them. It does **not** re-export the names that
moved *upward* — the generators in `Sites`, `Suite`, `Codec`, `Cycle`, `Accept`
— and a future change should not add such a re-export.

The rejected alternative is a façade root that imports its siblings and
re-exports their names. It is not merely unwanted — it is unavailable at this
shape of the graph. Every generator sibling imports the root for the operator
vocabulary and the `Mutant`/`Expected` core, so a root that imported them back
would close a cycle. Restoring the old surface would therefore require
interposing a new `Lara.Mutate.Core` module: extra public surface bought purely
for source compatibility, and a different goal from #122.

The resulting source-API break was bounded *before* it was accepted, and is
small in-repo. Exactly two files import `Lara.Mutate` wholesale
(`test/MutationSpec.hs`, `scripts/gen-mutants.hs`); both were updated in #142.
The four selective importers — `Lara.Measure`, `test/AblationSpec.hs`,
`scripts/bench.hs`, `scripts/measure.hs` — take only
`Expected`/`parseExpected`/`statusText`, which stay in the root, so they did not
change at all. Neither did the accept family, whose four imported names also
stay in the root. Since the #143 split those four are spread across its three
modules rather than imported by one: the facade takes `Expected`/`Mutant`/
`MutationOp`, `Lara.Mutate.Accept.Ops` takes `Mutant`/`MutationOp`, and
`Lara.Mutate.Accept.Build` takes all four, `mutantFileName` included.

### The `Outcome` re-export is the one exception, and it is not a façade (#157)

`Lara.Mutate.Outcome` sits *below* the root, not above it: it imports no sibling,
and in particular does not import `Lara.Mutate`. The direction is forced by the
data — `Mutant` has an `Expected` field, so the root must see the type — and it
is what makes the re-export cycle-free where a generator re-export would not be.

Re-exporting rather than repointing importers is deliberate. Fourteen call sites
across `src/`, `test/`, and `scripts/` name `Expected` in an explicit import list
(and five also name `parseExpected` / `statusText` / `expectedText`);
`Lara.Mutate.Suite` imports the root openly, so it is a fifteenth module that
would have been affected, though not by name. Repointing them would be a
wide diff for no gain, and would additionally force `Outcome` into
`exposed-modules`, growing the public surface. With the re-export, `Outcome`
stays an `other-module`, **no importer changed**, and the public surface is
byte-for-byte what it was.

The rule this leaves for a future contributor: a re-export from the root is
admissible only for a module the root itself imports — i.e. one strictly below it
in the graph. Everything above it stays a hard split.

## D2 — Seven ownership modules, six of them new

Issue #122 sketches `Sites` / `Codec` / `Corpus` plus core. Measured against the
line counts at the time, that three-way split leaves **core at ~460 and `Sites`
at ~465** — both still over the guideline it was meant to satisfy. Three further
cuts along seams already present in the file fix that: `Seed` (the SplitMix64
stream), `Cycle` (the constructed rebut-cycle family), and `Manifest` (the
`MANIFEST.tsv` contract).

The frozen public `mutationSeed` constant and the operator metadata function
`codecDiagnostics` stay in the root. That is what keeps `Seed` internal and the
root small enough to read in one sitting.

`codecDiagnostics` also *cannot* move to `Outcome`, which is worth stating
because #157 proposed it and costed the split on the assumption that it would
(predicting a ~250-line root). Its type is `MutationOp -> Maybe (String, String)`,
so an `Outcome` that owned it would import the root for `MutationOp` — and the
root already imports `Outcome` for `Expected`, because `Mutant` has an `Expected`
field. That is a cycle. Moving it would require `MutationOp` and `Mutant` to
part company, which is a larger redesign than the seam calls for. So the
seam cuts at `Expected` and its spellings only, and the root lands at 328 rather
than the ~250 the issue projected. It is operator metadata, and D2 has always
placed it with the operators.

## D3 — `Suite`, not the issue's `Corpus`

The issue names the sweep module `Lara.Mutate.Corpus`. The corpus sweep
(`sweepOps`, `corpusMutants`) and the worked-example assembly (`mutantsForBase`,
`unitMutants`) are the same job over two base populations: they share
`unitMutants` and the same operator order, and splitting them would put a
~106-line module beside a ~109-line one that has to be read together.
`Lara.Mutate.Suite` owns both. Here `Suite` means *seeded rejection-suite
assembly*, not the complete fixture suite — `scripts/gen-mutants.hs` combines it
with the codec, cycle, and accept families.

This is a deliberate deviation from the issue's sketch. The issue is closed; if
its wording and this record disagree, this record is the one that shipped.

## Module size

There is **no numeric line bound in this namespace**, and CI does not measure
one. The rule this section used to carry — every module at or below 300 code
lines, warning from 250, enforced by `scripts/check-module-size.sh` against a
table of per-module counts kept here (#161) — is **retired**. The guard, its
self-test, the CI step that ran them, and the table are gone.

The bound measured the wrong quantity. Every split recorded in this document was
decided by a *seam*: specified outcome versus operator vocabulary, certificate
family versus shared navigation, operator constructions versus mutant assembly.
Each of those was visible in the export list, which already grouped the names
under separate headings, before any line count was consulted. What the number
added was pressure at the wrong moment — a two-line Haddock clarification asked
for in review broke the rule once, and was repaired by reflowing prose to buy
the line back, the metric driving the work instead of the reverse. Its own scope
caveat said the rest: eleven modules elsewhere in `src/` exceed 400 lines by
design, three of them past 800 (`Lara.Syntax` at 2136, `Lara.Wire` at 1579,
`Lara.BindingAudit` at 1365). The bound was never a property of this repository,
only a local habit that got mechanized.

What governs module boundaries here is the rest of this record: D1 (a hard
split, with a re-export admissible only for a module the root itself imports),
D2 (what each module owns), D3 (what stays together because it has to be read
together). Split when a nameable seam appears — a group of definitions with its
own vocabulary, its own dependencies, or its own reason to be read alone. Length
is a hint that one may have appeared, not by itself a reason to cut, and a
module that is long because it is well documented is not a module to split.

The splits recorded below explain the current graph.

`Lara.Mutate.Sites.Cert` and `Lara.Mutate.Sites.Nav` are the #125 split. Adding
the `cert-wrong-fraction` operator took `Sites` to 428 lines and, more to the
point, gave the certificate family enough of its own vocabulary to be read
alone, so the certificate-family enumerators moved to `Sites.Cert` and the
navigation helpers they share with `Sites` moved to `Sites.Nav`. The shape
mirrors the #143 `Accept` split: a facade that keeps the single import site, one
module of shared helpers, one of family operators. `Sites` re-exports the three
cert enumerators, so `Lara.Mutate.Suite` was unchanged. Both new modules are
`other-modules`, so this added no public surface, and the split is byte-neutral:
regeneration reproduces `fixtures/mutants` exactly, since enumerator order is
what fixes the seeded picks and no list order moved.

`Lara.Mutate.Sites.Conflict` is the #124 addition. It is a new module rather
than a sixteenth enumerator in `Sites` because this enumerator is the only one
that imports the checker (`Lara.Check` / `Lara.Compile` / `Lara.Policy`) — it
mirrors the completeness scan's search order so it can publish the *located*
ground truth, and that dependency deserves its own module rather than being
smuggled into the shared one.

Since **#159** it also imports `Lara.Driver`, a strictly higher layer than the
checker modules above. It reaches for exactly one name, `groupConflictReject`:
the enumerator must know whether the driver will escalate a group conflict to
R9 *before* the completeness scan runs, because on such a base no deletion can
produce a `MissingConflict` mutant. That is a driver-ordering fact, not a
checker fact, so there is nowhere lower to get it from. It strengthens rather
than weakens the case for the separate module — `Sites.Conflict` is the only
enumerator whose correctness depends on the pipeline stage order, and confining
that dependency to one module is the point. There is no cycle: `Lara.Driver`
does not depend on `Lara.Mutate`.

`Lara.Mutate.Sites.Localize` is the **#123** addition. The localization
family's composite enumerators consume `Sites`' single-site enumerators as
components, so the module inverts the facade's usual direction: it imports
`Sites`, and a re-export through the facade would cycle. It therefore follows
the `Sorts` precedent, not the `Cert` one — no re-export, imported directly by
`Lara.Mutate.Suite`, which gains one edge while the graph stays acyclic
(`Sites` does not import it back). Its off-site enumerator also imports
`Lara.Policy` and `Lara.Sigma.WellSorted`: a retraction must keep the mutated
policy clean through the stages ahead of support, and those gates are checker
components, not navigation.

`Lara.Mutate.Outcome` is the **#157** split, and it is the reason the root landed
at 328 lines rather than 400 (past tense on purpose: later operator additions
move the number — it reads 340 after #123's three, at this document's own stated
cost of 3 root lines each). The root's growth had concentrated in one place:
`drop-covering-attack` cost it thirteen lines (a `MutationOp` constructor with
its `opName` / `opFamily` rows, plus a new `Expected` constructor with its
Haddock and its `expectedText` / `parseExpected` rows), of which only three were
operator vocabulary and ten were specified outcome.

The seam is *specified outcome* versus *operator vocabulary*, the one the export
list already grouped under two headings. `Expected`, `expectedText`,
`parseExpected`, and `statusText` moved; `MutationOp`, `opName`, `opFamily`,
`codecDiagnostics`, `Mutant`, `mutantFileName`, and the two frozen constants
stayed. This is the split D1's new sub-section governs: the root imports the
child and re-exports it, so no importer changed and no public surface was added.

What it buys:

- an operator costs the root **3** code lines;
- an operator that also needs a new *specified outcome* costs the root 3 and
  `Outcome` **10**, instead of costing the root 13. The growth that was pushing
  the root is the growth that moved.

`codecDiagnostics` could not move with it; see D2 for why that is a cycle rather
than a preference.

### History of the `Accept` exception, and how it closed

_When this section was written the namespace still carried a hard line bound;
the exception below was an exception to that bound. The bound is retired, the
split it prompted is not._

`Lara.Mutate.Accept` landed at **445** lines, the one module over the bound of
the day.
It predates the #122 split — it was extracted as new material in M5 T1, so it
never went through the re-partitioning pass the rest of the namespace had — and
splitting it was explicitly outside #122's scope. This record originally carried
it as a single documented exception, explicitly not precedent, with the deferral
tracked as issue #143 so the exception had a home in the tracker rather than
only in a sentence here.

**#143 closed it by splitting along the seam this record predicted** — the
constructed accept-verdict family versus its site/assembly helpers — into three
modules under a facade:

- `Lara.Mutate.Accept` (154) — the facade and the whole public surface:
  `acceptMutants` (which operators, in what order), `isJustified` (which bases),
  and `acceptStructureOk` (was it the mutant asked for).
- `Lara.Mutate.Accept.Ops` (241) — the six constructions and the vocabulary each
  injects.
- `Lara.Mutate.Accept.Build` (162) — mutant assembly, the asserted
  justified-unit invariants, and the attack-site helpers.

The dependency order is forced, and is why assembly sits *below* the operators
rather than beside them in the facade: every operator emits through
`acceptMutantWith`, so a facade that both listed the operators and owned the
assembly would close an import cycle.

**The public API did not change.** `Lara.Mutate.Accept` stays the only exposed
module of the three, still exporting exactly `acceptMutants` and
`acceptStructureOk`; `Ops` and `Build` are `other-modules`, like
`Lara.Mutate.Seed` and `Lara.Mutate.Sites`. The source-API break #143 warned
about — `Accept` being in `exposed-modules`, so a split that moved exported
names would break importers — never materialized, because the facade kept both
names. `scripts/gen-mutants.hs` and `test/MutationSpec.hs`, the only two
importers, are untouched.

The move was verified byte-preserving in two independent ways: the generated
suite came out byte-identical (`gen-mutants.hs` → empty `fixtures/mutants`
diff, so `m5-freeze-v4` stays valid), and every non-comment, non-import code
line of the original file is present in the union of the three new files with
none lost. The `error` messages still name `Lara.Mutate.Accept`, the public
entry point, rather than the module they now live in.

## D4 — The index-space contract the site enumerators publish (#159, #165)

The checker does not run on the declared unit; it runs on the §4.3 quarantine of
it. Before #159, `dropCoveringAttackSites` handled that by refusing to emit any
site when the quarantine was not the identity (`quarantineIsIdentity`) — a
fail-closed gate. #159 replaced the gate with a mapping. The contract that
replaced it is frozen here because it is split across three modules and is not
reconstructable from any one of them:

- **The published `si`/`ti` are in checked index space.** The scan cache, the
  coverage decider, and the emitted `Lara.Diagnostics.CConflictPair` all index
  the *checked* unit. This is not a free choice: `Lara.Diagnostics` builds the
  verdict's pair as `CConflictPair (mcSourceIndex mc) (mcTargetIndex mc)` with no
  remapping, so checked space is the space the verdict names, and the mirror must
  name the same one or the answer key is wrong.
- **The deletion is in declared index space.** The mutation edits
  `unitAttacks` of the declared unit, because that is what gets re-encoded.
- **`Lara.Blocked.retainedAttackIndices` is the sole bridge.** Entry `i` of it is
  the declared index of checked attack `i`. Nothing else may map between the two
  spaces.

Soundness rests on attack deletion commuting with the prune, which holds because
the kept-argument set is attack-independent: `pruneWithPolicySeed` derives it
from the policy seed and inconsistent-group members via `supportUsesLeafSet` over
*arguments*, strictly before any attack is examined. So deleting retained
declared attack `d` prunes to exactly the checked attack list minus entry `i`.
Deleting a *pruned* attack is an accepting no-op, which is why only retained
attacks are candidate sites.

**The rejected alternative is widening the gate.** Keeping a fail-closed
`quarantineIsIdentity`-style guard and merely relaxing its condition was
considered and rejected: it preserves the defect it was hiding. The gate existed
because a declared-space mirror publishes a *plausible but wrong* pair on a
quarantining base rather than failing loudly, and no widening of a guard fixes a
wrong mapping — only the mapping does. The gate is therefore gone, replaced by
`retainedAttackIndices` plus the R9 pre-scan gate (`Lara.Driver.groupConflictReject`),
which is a different condition: it excludes bases the driver rejects *before* the
scan, where no deletion could yield `MissingConflict` at all.

**Why no Lean entry is owed.** The prune's attack-retention predicate is already
mechanized. `Admission.buildPrune`'s `keepAttack` is exactly "both endpoints ∈
keptIds" (`lean/Lara/Admission.lean` `retained_attack_endpoints`, axiom-checked),
and `retained_attacks_selectAligned` with `RawAttack.resolve_filter_commute` pins
that the checker consumes exactly that filtered sublist. `retainedAttackIndices`
only re-expresses that proved filter as an index list for the generator; it
introduces no new definition the proofs do not already quantify over. This is the
*strong* form of the exemption argument — the one
`docs/mechanization-scope-decision.md` says is worth relying on — not the weak
"the type has no counterpart" form, which is false here anyway: a `retainedIndices`
counterpart does exist at `lean/Lara/BlockedProgram.lean`.

**Guarded by.** `test/BlockedSpec.hs` `prop_retainedAttackIndices` (the bridge is
an exact projection, with `CheckSpec.quarantiningConflictBase` supplying the
gapped retained list `[1]` that makes it non-vacuous), and `test/MutationSpec.hs`
`prop_conflictSiteQuarantiningBase` / `prop_conflictSiteMatchesChecker` (the
published pair is the one the checker reports). No corpus base declares a
`groups` form, so on every committed mutant `retainedAttackIndices == [0..n-1]`
and the emitted sites are byte-identical to the pre-#159 ones — which is why the
change needed no corpus regeneration and no freeze-tag bump, and equally why the
quarantining path is reachable only from the in-memory fixtures.

### Generalized to every enumerator (#165)

**Scope.** The contract above bound `Sites.Conflict` alone, and the sibling
enumerators in `Lara.Mutate.Sites` and `Sites.Cert` still published `CArgument`
in *declared* index space — latent for the same reason (no corpus base
quarantines). #165 closed that asymmetry, and the contract now binds **every
site enumerator**:

- **Sites are drawn from the checked unit.** `Sites.Nav`'s `argSites` /
  `ruleSites` / `leafSites` / `attackSites` read a `Prune`, not a `Unit`. A
  mutation into pruned material is an accepting no-op the checker never sees, so
  it can witness nothing — self-gating on retained material is part of the
  contract, not an optimization. This binds the space-free enumerators too: the
  `Lara.Mutate.Sorts` leaf/θ operators publish `CPolicy`, which needs no
  mapping, but still draw their sites from retained leaves and arguments.
- **Every indexed constituent is published in checked space.** `CArgument`,
  `CAttack`, and `CConflictPair` all index the checked unit, because that is the
  space `Lara.Diagnostics` names in the verdict. `CPolicy`, `CGroup`, and
  `CReplayEnvelope` are space-free and are published as-is.
- **Only the rewrite maps back to declared space**, and the three retained-index
  lists are the **sole bridges**: `Lara.Blocked.retainedIndices` (arguments),
  `retainedAttackIndices` (attacks), and `retainedLeafIndices` (leaves, added by
  #165). Nothing else may map between the two spaces.

**The two spaces are types, not a naming convention (#166 review).** `Sites.Nav`
exports `CheckedIx` and `DeclaredIx` newtypes, and the site tuples pair them;
`rewriteArg` / `setAttackAt` / `dropAttackAt` take a `DeclaredIx`. A transposed
pair is a compile error rather than a silently corrupted answer key — the repo's
"separate namespaces get separate types" rule.

The invariant is **not a count of unwrap sites**; it is that nothing pairs the
two spaces except a retained-index list. Construction is either from such a list
(`argSites` / `attackSites` in `Sites.Nav`, `retainedLeafDecls` /
`retainedArgDecls` in `Sorts`), or directly in checked space from a measurement
of the checked unit, which pairs nothing — `unlicensedAttackSites`'
`CheckedIx (length (unitAttacks checked))` is the one such site. Unwrapping
happens in three kinds of place, each staying within one space:

1. publishing a `Constituent`, through `checkedIx`;
2. inside a rewrite helper taking a `DeclaredIx` — `rewriteArg`, `setAttackAt`,
   `dropAttackAt` in `Sites.Nav`, and `mapLeaf` / the θ rewrite in `Sorts`;
3. where a `CheckedIx` indexes the *checked* unit itself, crossing nothing —
   `Sites.Conflict`'s survivor scan (`dropIx (checkedIx ci) checkedAttacks`) is
   the only such site.

`Constituent` and the `Lara.Blocked` retained-index lists keep their bare-`Int`
APIs.

**The rejected alternative is a quarantining corpus base.** The quarantining
path is exercised only from in-memory fixtures (`CheckSpec.quarantiningConflictBase`
and the derived skew below), so no committed mutant file walks it. Adding a
corpus base whose §4.3 quarantine is non-trivial was considered and rejected on
cost: it forces a full corpus regeneration and a freeze-tag bump, which must be
budgeted rather than discovered. It rides with **#156** if ever wanted.

**Known boundary, and it fails closed.** A leaf-mutating operator striking a
member of a *consistent* group would flip that group inconsistent, turning the
mutant's outcome into R9/quarantine instead of R2. No base carries a consistent
group today. If one enters the corpus, `scripts/gen-mutants.hs`'s per-mutant
`verify` and `prop_siteMatchesChecker` both fail loudly at that point — unlike
the index skew #165 closed, which failed *open*.

**Guarded by.** `test/MutationSpec.hs` `prop_siteMatchesChecker` (every site of
every enumerator, over the worked examples, all corpus units, the quarantining
fixture, and a skewed sibling of each, rejects with its specified outcome at
exactly the predicted `Constituent` — this is what turns `expected-location`
from a measured column into a gated one), `prop_sitesQuarantiningBase` (the
hand-checked absolute pins on the fixture), and `prop_siteDirectionSkewed`.

That last one is the answer to the coverage gap the #166 review found: the one
committed quarantining base has no rules, so every `ruleSites`-based enumerator
was exercised only where checked and declared indices coincide, and a
per-operator transposition would have failed open. `quarantineSkewed` gives
*every* base a skewed sibling — it prepends an inconsistent group, an argument
on one of its members, and an attack targeting that argument, all declared
first, so quarantine removes exactly the added material and the checked unit is
the original base. The property then states the mapping itself (the declared
index a rewrite edits is the one the retained-index list pairs with the
published checked index) and carries an anti-vacuity gate: every operator
publishing an indexed constituent must have at least one site where the two
spaces actually differ.

**Why no Lean entry is owed for `retainedLeafIndices`.** The same strong-form
argument #159 made for `retainedAttackIndices`. `Admission.buildPrune` proves
`p.removedLeaves = leaves.filterMap …` and
`p.checkedLeaves = Groups.quarantineLeaves qs leaves`
(`lean/Lara/Admission.lean:764-765`), and the argument-side `retainedIndices`
counterpart exists at `lean/Lara/BlockedProgram.lean:57` with axiom-checked
theorems. `retainedLeafIndices` only re-expresses an already-proved filter as an
index list for the generator.

**Cost.** No corpus regeneration and no freeze-tag bump: every committed base
prunes to itself, so regeneration is byte-identical and `fixtures/mutants/` is
untouched. #156's scope is unchanged.

## What the split deliberately did not change

Every moved definition and signature is cut-and-paste: no renaming, no signature
change, no reformatting, no while-I'm-here cleanup. Only module headers, imports,
export lists, and Haddock links differ from the pre-split text. This is what lets
byte-identical regeneration of the frozen suite (504 mutants) serve as the
primary correctness gate: because the seeded stream is keyed `(base, operator)`
*through* `opName` and selection draws from each enumerator's list in order, a
reordered constructor, a reordered `mutantsForBase` entry, a reordered
comprehension, or a renamed operator would each move committed bytes. The suite
came out byte-identical, so `m5-freeze-v4` stayed valid and no freeze tag was
cut.

Consolidating operator registration to a single site was **not** attempted and is
not implied by this layout. Adding an operator still requires coordinated
vocabulary, metadata, generator, assembly, and sweep edits; that consolidation
would be a behavioral redesign, out of scope for a byte-preserving move.
