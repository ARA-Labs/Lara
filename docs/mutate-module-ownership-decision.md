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
├── Sites ────────────────→ core
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
| `Lara.Mutate.Sites` (internal) | the fourteen per-operator site enumerators |
| `Lara.Mutate.Suite` | `mutantsForBase`, `corpusBudget`, `corpusMutants`, `corpusSweepReport` |
| `Lara.Mutate.Codec` | `codecMutantsForBase` |
| `Lara.Mutate.Cycle` | `cycleMutants` |

`Seed` and `Sites` are in `other-modules`: their names had to become module-
visible so `Suite` and `Cycle` could consume them, but keeping them out of
`exposed-modules` means the package's public surface does not grow. `splitMix64`
and `stringSeed` stay private inside `Seed` — the old "exposed for tests"
heading was stale, no test or script imported either name.

### Import ownership

| Module | Imports |
|---|---|
| `Seed` | `Data.Bits`, `Data.Char`, `Data.Word`, `Lara.Mutate` |
| `Manifest` | `Lara.Diagnostics`, `Lara.Mutate` |
| `Sites` | `Data.List`, `Lara.AST`, `Lara.Diagnostics`, `Lara.Prop`, `Lara.Sigma`, `Lara.Strict`, `Lara.SupportTerm`, `Lara.Mutate` |
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
| `Lara.Mutate` | 379 |
| `Lara.Mutate.Sites` | 363 |
| `Lara.Mutate.Sorts` | 302 |
| `Lara.Mutate.Suite` | 260 |
| `Lara.Mutate.Accept.Ops` | 241 |
| `Lara.Mutate.Accept.Build` | 161 |
| `Lara.Mutate.Accept` | 154 |
| `Lara.Mutate.Codec` | 128 |
| `Lara.Mutate.Cycle` | 123 |
| `Lara.Mutate.Seed` | 76 |
| `Lara.Mutate.Manifest` | 69 |
| **Σ** | **2256** |

Counts are `git ls-files` / `wc -l`. The root reads 379 rather than the 374 it
measured before this document's own five-line Haddock cross-reference was added
to it.

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
