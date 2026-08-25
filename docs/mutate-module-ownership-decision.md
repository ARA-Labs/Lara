# Decision: module ownership in the `Lara.Mutate` namespace

_Records the settled ownership contract for the seeded mutation generators
after the seven-module split (issue #122, PR #142). The implementation plan that
produced the split was deleted when the work landed, per the `plans/` rule; this
record carries its durable decisions — which module owns what, why the root
deliberately does not re-export, and which alternatives were rejected. Companion
to `docs/m5-freeze-checklist.md` (the freeze the generators feed) and the root
module Haddock in `src/Lara/Mutate.hs` (the same graph, stated for readers of the
code)._

## The namespace

`A → B` is an import inside the `Lara.Mutate` namespace.

```
Lara.Mutate                 core; imports no sibling
├── Manifest ─────────────→ core
├── Seed ─────────────────→ core
├── Sites ────────────────→ core + Sites.Cert + Sites.Conflict + Sites.Nav
│   ├── Sites.Cert ───────→ core + Sites.Nav
│   ├── Sites.Conflict ───→ core (no sibling; mirrors the checker)
│   └── Sites.Nav ────────→ (no sibling; structural only)
├── Suite ────────────────→ core + Seed + Sites + Sorts
├── Codec ────────────────→ core
├── Cycle ────────────────→ core + Seed
├── Accept ───────────────→ core + Accept.Ops + Accept.Build
│   ├── Accept.Ops ───────→ core + Accept.Build
│   └── Accept.Build ─────→ core
└── Sorts ────────────────→ core
```

The graph is acyclic **because the root imports no sibling**. That is the load-
bearing property of the whole arrangement, and it is what D1 below protects.

### Export ownership

| Module | Exported names |
|---|---|
| `Lara.Mutate` | `MutationOp(..)`, `opName`, `opFamily`, `Expected(..)`, `expectedText`, `parseExpected`, `statusText`, `codecDiagnostics`, `Mutant(..)`, `mutantFileName`, `mutationSeed`, `mutationBases` |
| `Lara.Mutate.Manifest` | `mutantPath`, `manifestFor` |
| `Lara.Mutate.Seed` (internal) | `streamForKey`, `streamFor`, `pickWithStream`, `pickSome` |
| `Lara.Mutate.Sites` (internal) | the sixteen per-operator site enumerators, four of them re-exported from `Sites.Cert` and `Sites.Conflict` |
| `Lara.Mutate.Sites.Cert` (internal) | `certTheorySwapSites`, `certPayloadSites`, `certWrongFractionSites`, `bumpWitness` |
| `Lara.Mutate.Sites.Conflict` (internal) | `dropCoveringAttackSites` |
| `Lara.Mutate.Sites.Nav` (internal) | `occurrences`, `rewriteAt`, `rewriteArg`, `ruleSites`, `leafSites`, `ruleOf`, `inequivLeaf` |
| `Lara.Mutate.Suite` | `mutantsForBase`, `corpusBudget`, `corpusMutants`, `corpusSweepReport`, `dropCoveringAttackSites` (re-export, tests only) |
| `Lara.Mutate.Codec` | `codecMutantsForBase` |
| `Lara.Mutate.Cycle` | `cycleMutants` |

`Seed`, `Sites`, `Sites.Cert`, `Sites.Conflict`, and `Sites.Nav` are in
`other-modules`: their names had to become module-visible so `Suite`, `Cycle`,
and `Sites` could consume them, but keeping them out of `exposed-modules` means
the package's public surface does not grow — with one deliberate exception. The
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
| `Seed` | `Data.Bits`, `Data.Char`, `Data.Word`, `Lara.Mutate` |
| `Manifest` | `Lara.Diagnostics`, `Lara.Mutate` |
| `Sites` | `Data.List`, `Lara.AST`, `Lara.Diagnostics`, `Lara.Prop`, `Lara.Sigma`, `Lara.SupportTerm`, `Lara.Mutate`, `Lara.Mutate.Sites.Cert`, `Lara.Mutate.Sites.Conflict`, `Lara.Mutate.Sites.Nav` |
| `Sites.Cert` | `Data.Ratio`, `Lara.AST`, `Lara.Diagnostics`, `Lara.Strict`, `Lara.Strict.Cell`, `Lara.Strict.RA`, `Lara.Mutate`, `Lara.Mutate.Sites.Nav` |
| `Sites.Conflict` | `Lara.AST`, `Lara.Attack`, `Lara.Blocked`, `Lara.Check`, `Lara.Compile`, `Lara.Diagnostics`, `Lara.Policy`, `Lara.Prop`, `Lara.SupportTerm`, `Lara.Mutate` |
| `Sites.Nav` | `Data.List`, `Lara.AST`, `Lara.Prop` |
| `Suite` | `Lara.AST`, `Lara.Diagnostics`, `Lara.Replay`, `Lara.Wire`, `Lara.Mutate`, `Lara.Mutate.Seed`, `Lara.Mutate.Sites`, `Lara.Mutate.Sorts` |
| `Codec` | `Lara.Strict`, `Lara.Wire`, `Lara.Mutate` |
| `Cycle` | `Lara.AST`, `Lara.Prop`, `Lara.Replay`, `Lara.Sigma`, `Lara.Wire`, `Lara.Mutate`, `Lara.Mutate.Seed` |

## D1 — Hard split, not a re-export façade

`Lara.Mutate` exports only what it still owns. It does **not** re-export the
names that moved, and a future change should not add such a re-export.

The rejected alternative is a façade root that imports its siblings and
re-exports their names. It is not merely unwanted — it is unavailable at this
shape of the graph. Every sibling imports the root for the operator vocabulary
and the `Mutant`/`Expected` core, so a root that imported them back would close
a cycle. Restoring the old surface would therefore require interposing a new
`Lara.Mutate.Core` module: extra public surface bought purely for source
compatibility, and a different goal from #122.

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

## D2 — Seven ownership modules, six of them new

Issue #122 sketches `Sites` / `Codec` / `Corpus` plus core. Measured against the
line counts at the time, that three-way split leaves **core at ~460 and `Sites`
at ~465** — both still over the guideline it was meant to satisfy. Three further
cuts along seams already present in the file fix that: `Seed` (the SplitMix64
stream), `Cycle` (the constructed rebut-cycle family), and `Manifest` (the
`MANIFEST.tsv` contract).

The frozen public `mutationSeed` constant and the operator metadata function
`codecDiagnostics` stay in the root. That is what keeps `Seed` internal and the
root under 400 lines.

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

## Sizing rule

Every module in the namespace stays at or below the coding guideline's 400-line
upper bound. **There is no longer an exception** (#143). As it now stands:

| Module | Lines |
|---|---|
| `Lara.Mutate` | 400 |
| `Lara.Mutate.Sorts` | 302 |
| `Lara.Mutate.Sites` | 294 |
| `Lara.Mutate.Suite` | 274 |
| `Lara.Mutate.Accept.Ops` | 241 |
| `Lara.Mutate.Accept.Build` | 162 |
| `Lara.Mutate.Accept` | 154 |
| `Lara.Mutate.Sites.Cert` | 141 |
| `Lara.Mutate.Sites.Conflict` | 130 |
| `Lara.Mutate.Codec` | 128 |
| `Lara.Mutate.Cycle` | 123 |
| `Lara.Mutate.Sites.Nav` | 91 |
| `Lara.Mutate.Seed` | 76 |
| `Lara.Mutate.Manifest` | 69 |
| **Σ** | **2585** |

`Lara.Mutate.Sites.Cert` and `Lara.Mutate.Sites.Nav` are the #125 split. Adding
the `cert-wrong-fraction` operator took `Sites` to 428 — the first breach of
this rule since #143 removed its last exception — so the certificate-family
enumerators moved to `Sites.Cert` and the navigation helpers they share with
`Sites` moved to `Sites.Nav`. The shape mirrors the #143 `Accept` split: a
facade that keeps the single import site, one module of shared helpers, one of
family operators. `Sites` re-exports the three cert enumerators, so
`Lara.Mutate.Suite` was unchanged. Both new modules are `other-modules`, so
this added no public surface, and the split is byte-neutral: regeneration
reproduces `fixtures/mutants` exactly, since enumerator order is what fixes the
seeded picks and no list order moved.

`Lara.Mutate.Sites.Conflict` is the #124 addition. It is a new module rather
than a sixteenth enumerator in `Sites` for two reasons: `Sites` was at 291 with
its own history of breaching this bound, and this enumerator is the only one that
imports the checker (`Lara.Check` / `Lara.Compile` / `Lara.Policy`) — it mirrors
the completeness scan's search order so it can publish the *located* ground
truth, and that dependency deserves its own module rather than being smuggled
into the shared one.

Counts are `git ls-files` / `wc -l`. The root reads 400 rather than the 386
recorded at #125: three lines for the `drop-covering-attack` operator — one
`MutationOp` constructor and its `opName` / `opFamily` rows — ten for the new
`Expected` constructor, its Haddock, and its `expectedText` / `parseExpected`
rows, and one for the #158 review reword that names the two `Rejection`
constructors no operator targets. An operator costs the root three lines; an
operator that also needs a new *specified outcome* costs it thirteen, which is
the case this count records.

**The root is now at the bound exactly, with zero headroom.** It briefly went to
401 during the #158 review — the first actual breach of this rule since #143 —
and came back to 400 by reflowing that Haddock, which is the whole of the
runway that was available. Nothing further fits: not a new operator (3 lines),
not a new `Expected` constructor (13), not another comment line.

The split that buys headroom back is **#157**, still taken there rather than
here so #124 stays one reviewable change. It is no longer a prediction — the
condition it was opened against has occurred, and the next change to this module
of any kind has to land it first.

The breach was silent: no test, no CI step, and no `scripts/*.sh` measures
module length, so this table is the only thing standing between a contributor
and a repeat. **#161** adds the mechanical guard.

### History of the `Accept` exception, and how it closed

`Lara.Mutate.Accept` landed at **445** lines, the one module over the bound.
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
- `Lara.Mutate.Accept.Build` (161) — mutant assembly, the asserted
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
