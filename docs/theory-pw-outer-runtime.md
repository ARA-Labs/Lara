# PW outer runtime: `pw-run 1` and Haskell/Lean conformance

Issue [#322](https://github.com/ARA-Labs/lara/issues/322) gives the
possible-world outer language a Haskell runtime. Before it, PW had Lean
definitions and proofs, plus a Lean example with a fixed host
(`docs/theory-pw-declared-wire.md`). Now an author writes one file that
declares worlds, candidate edges, bridges and queries. `lara pw` evaluates
that file, and a Lean reference executable must print the same bytes. Proofs
connect the Lean reference to `PW.Sat`.

```sh
cabal run -v0 exe:lara -- pw fixtures/pw/run/fields.sexp   # the Haskell runtime
(cd lean && lake build pw-run)
lean/.lake/build/bin/pw-run fixtures/pw/run/fields.sexp    # the Lean reference
make pw-conformance                                         # the differential gate
```

## 1. The contract

A run file contains exactly one S-expression:

```text
(pw-run 1
  (worlds (world WORLD_ID CONTEXT_ID SOURCE)*)
  (edges (edge BRIDGE_ID SOURCE_WORLD TARGET_WORLD ACCEPTANCE)*)
  (comparisons (compare BRIDGE_ID SOURCE_WORLD ATOM)*)
  DOCUMENT)
SOURCE     ::= (inline CHECK_INPUT) | (file PATH)
ACCEPTANCE ::= accepted | rejected
DOCUMENT   ::= (pw-surface 1 ...)    ; the #314 contract, unchanged
```

Stars mark repetition. The four sections occur once each, in this order, and
each may be empty. `ATOM` is the `pw-surface` atom production. Version `1` is
exact, and the version is read before the layout, as for `pw-surface`.
Sections decode in order, and each section finishes before the next header is
read. The reader, quoting and error categories (`syntax`, `malformed`,
`unsupported-version`) are those of `pw-surface 1`. The embedded document goes
through the #314 decoder unchanged, so its bridge declarations and posed
queries keep their contract exactly.

A world's `CHECK_INPUT` is the frozen local checker envelope
(`check-input`, `lara-core@0.2`), the same bytes `lara check` reads. A
`file` path is resolved relative to the run file's directory. The run codec
carries an envelope as an untyped tree. The envelope is decoded when its world
loads, so a malformed envelope is a world failure, not a run-codec failure.

## 2. Loading and evaluation

Stages run in this order, and the first refusal is the run's error:

1. **Worlds**, in declaration order. A repeated world ID is refused. Otherwise
   the envelope is read, parsed and decoded. An envelope that declares
   duplicate-report groups is refused (see §3). Replay preflight comes next
   (R13), then the unchanged checker (`checkUnit` in Lean,
   `checkUnitWith fullConfig` in Haskell). The checker sees the envelope's
   leaves, theories and queries as its ground atoms, exactly as the local
   drivers do. A context is created by its first world, and that world fixes
   the context's environment: Σ, the policy, the leaf table and the theory
   table. Every later world of the context must declare the same environment.
   Two worlds of one context may not have the same checked program.
2. **Bridges**: `Declared.load` over the loaded contexts. It refuses a
   duplicate ID, an unknown endpoint, a missing clause, and a failed `rule-ok`.
3. **Edges**, in order. The bridge must exist, both worlds must exist, each
   world must lie in the bridge's corresponding context, and the triple
   (bridge, source, target) may occur at most once.
4. **Queries**: `elabPosed` against the checked registry's naming, so
   `elabPosed_declared` applies. Each query is answered at **every world of
   its context**, in declaration order.
5. **Comparisons**: the bridge must exist, and the world must exist in the
   bridge's source context. Then `crossComparePosed` runs over that world's
   declared candidates, in edge order. Accepted and rejected edges are both
   candidates.

A completed run prints

```text
(pw-result 1
  (queries (query (at WORLD BOOL)*)*)
  (comparisons (comparison BRIDGE WORLD ATOM RESULT)*))
RESULT ::= (comparable STATUS+) | (incomparable REASON) | (not-posable FAULT)
```

A refused run prints `(pw-error 1 STAGE FAULT)`. `STAGE` is one of `wire`,
`world`, `bridge`, `edge`, `query`, `comparison`, or `io`. The fault
constructors are listed in `Lara.PW.Run.encodeError` and in its Haskell
mirror. Only three faults carry runtime-specific text as their last atom: a
reader's `syntax` message, `world-input` (a world that could not be read or
decoded), and `io` (the run file could not be read). Consumers branch on the
constructors.

Exit `0` means the run completed. A false modal answer and an incomparable
comparison are results, not errors. Exit `2` means the run file could not be
read or decoded. Exit `1` means a decoded run was refused. Both drivers print
exactly one UTF-8 line on stdout and nothing on stderr, and both read the
run-file argument and every file path as UTF-8, whatever the locale.
A wrong argument count is outside the contract: `lara pw` falls through to
`lara`'s usage message on stderr (exit 2), and `pw-run` prints
`(pw-error 1 usage …)` (exit 2). `lara pw` therefore departs
from the other `lara` doors, which report failures on stderr. The output
protocol here is structured, and the Lean reference must be able to print the
same bytes.

Primitive `box` and `dia` evaluate their operands as written, in the target
context; they never translate them. A comparison is the separate
source-claim operation: it translates the claim through the bridge's declared
symbol map. The gate checks both halves directly: remapping `p` to `q` in a
bridge changes the comparison profile, and the run's `queries` section stays
equal to the unmapped golden's.

## 3. The finite model boundary

The runtime evaluates one specific frame: the frame the file declares.

* A context's worlds are exactly its declared worlds. Each world is an
  accepted local unit under the context's environment, so its status atoms are
  `statusC` over its compiled framework (`Instance.cmpStatus`).
* A bridge's candidate relation is its declared edge list. Acceptance is each
  edge's declared flag. Nothing here claims that the flag reflects T6
  applicability: acceptance is host data, as in `PWFileHost`.
* Context environments are compared as decoded, in declaration order, on both
  sides. Two worlds whose signatures list the same predicates in a different
  order therefore get `context-environment`. This is deliberate: the
  environment is the envelope's declared data, not a normalized set.
* A world is identified by its checked program. This is why a context may not
  hold two worlds with the same program. Otherwise one world value would name
  two declarations, and the frame could not tell their edges apart.
* Envelopes that declare duplicate-report groups are refused. §4.3 quarantine
  makes a public status conditional (`evidence-blocked`), and a Boolean
  status atom cannot say "conditionally justified". Whether PW should read the
  conditional label, or refuse only when quarantine actually fires, is tracked
  in [#326](https://github.com/ARA-Labs/lara/issues/326).

`Sat` over an arbitrary frame is proposition-valued, and nothing here claims
it is executable. The finite frame above is what makes evaluation decidable.

## 4. What is proved, tested, and assumed

**Proved in Lean** (`lean/Lara/PW/Run.lean`, all in `AxCheck.lean`, standard
axioms only):

| Result | Statement |
|---|---|
| `decodeRun_encode`, `encodeRun_injective` | Structured round trip of the run document, including the embedded surface document. |
| `Model.evaluates_iff` | Each printed query answer is `evalFinite` over the declared `Finite` presentation, hence `PW.Sat` of the elaborated formula under `Sorted.cmpVal`. |
| `Model.presents`, `Model.compare_mem_iff_sat` | Comparison inputs `Presents` the frame by construction. So when a claim poses and translates, a status occurs in the printed profile exactly when `⟨b⟩Status_s(τ_b(c))` holds at that world. |
| `indexIn_declared`, `Model.index_declared`, `Model.candidates_declared`, `Model.accepts_declared` | At declared worlds, the frame's candidates and acceptance are exactly the resolved edges, read at world positions, in order. This uses the loader's distinct-program invariant (`LoadedCtx.distinct`). |
| `positionIn_some`, `resolveEdge_declared`, `resolveEdges_declared` | Resolution keeps the file's edges one for one: each resolved edge lies along the bridge its declared name finds, carries its declared acceptance, and sits at the positions of the worlds its declared names identify. |
| `loadWorlds_nodup` (via `IdsOk`, `addWorld_ids`, `loadWorlds_ids`) | No context of a loaded run holds two worlds with one identifier: the loader refuses a repeated name before it checks anything. |
| `Model.candidates_named`, `Model.accepts_named`, `loadModel_spec`, `load_candidates_named`, `load_accepts_named` | For a loaded run, the frame's candidates at a declared world are the worlds named as targets by exactly the file's edges along that bridge from that world's identifier, in declaration order. Acceptance between two declared worlds is the declared flag of such an edge. |
| `distinct_append`, `Hosted.find_isSome`, `Hosted.entry_mem` | The loader's invariant and host naming lemmas. The host's context bijection holds by construction: context indices are declared names. |
| `ResultTag.parse_text`, `ResultTag.text_injective` | Every keyword of the result protocol has exactly one spelling. |

The existing results then apply unchanged to a loaded run: `elabPosed_declared`
(every modal occurrence resolves to a declaration from the file, with that
declaration's symbol map), `evalFinite_iff`, `mem_compare_iff_sat_dia`, and the
posing theorems of `Lara.PW.Sorted`.

**Tested, not proved.** The Haskell runtime (`src/Lara/PW/*.hs`) transcribes
the Lean definitions. `scripts/check-pw-conformance.py` requires both drivers
to print identical bytes and exit codes, in two families.

The six committed fixtures `fixtures/pw/run/*.sexp`, each with a committed
`*.expected` golden, cover:

* nested modalities that complete, and a world with no candidates
* translation-domain and sort failures: all five posing faults
* canonical numerals
* the rule clause under a renaming symbol map, through a constructor
  sub-pattern and a critical question (`renamed.sexp`)

The 94 generated cases mutate those fixtures. They cover:

* every error stage and fault, and declaration/name mismatches
* stage order, and fault order within each stage
* every field of a context's environment
* each position the rule clause translates, broken in turn
* map and acceptance dependence, including all-rejected bridges
* quoted Unicode names; non-ASCII world paths, run-file paths and run
  directories, including missing ones; and files that are not UTF-8

The Unicode-name and non-ASCII path cases run again under `LC_ALL=C` and
under an ISO-8859-1 locale, which the gate builds with glibc's `localedef`
(no root needed). An unreadable run file is one more run, so a passing gate
reports 107 runs.
Every comparison is byte equality, except for the three detail-bearing
faults. For those, the gate checks the fault's arity, masks only the final
atom, and compares the rest atom for atom.
`test/PWSpec.hs` holds the Haskell side to the goldens in-process, and to the
mirrored laws of the Lean development. The byte reader and printer remain the
tested boundary they were in #314, and so does the world pipeline's use of
`decodeCheckInput`. Edge resolution's step from names to positions is proved
(`resolveEdges_declared`, `load_candidates_named`). The reader's nesting bound
is Haskell-only; that divergence is tracked in
[#331](https://github.com/ARA-Labs/lara/issues/331).

**Explicit, unproved obligations.** Canonicalizer agreement holds because
every context uses the production `dcanon`; it is not a checked condition.
`leaf-ok` and `cert-ok` must be listed, but listing them proves nothing: they
remain `BridgeObligations` premises, and a run file's maps are not claimed to
satisfy them. `rule-ok` is decided by the loader (`ruleOkB_iff`).

## 5. Boundaries

Unchanged: the local checker wire and its drivers, `pw-surface 1`,
`PW.Frame`, `PW.Sat`, `crossCompare`, the T6 contract, the corpus, and every
freeze tag. No corpus regeneration was needed. The `pw-example` executable
from #314 is kept; it remains the fixed-host example.

Out of scope, as #322 states: approximation bridges, epistemic, dynamic and
hybrid operators, global scenarios, and T10. World sources are check-input
envelopes only. A `.lara` source would be a Haskell-only door, since the Lean
reference has no surface parser, and the differential could not cover it. A
derivation door in the style of `lara map-input` is tracked in
[#327](https://github.com/ARA-Labs/lara/issues/327).
