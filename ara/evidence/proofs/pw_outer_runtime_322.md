# PW outer runtime and Haskell/Lean conformance

The user asked for the outer-runtime work to be finished directly and submitted as a PR. The
work is on branch `feat/pw-outer-runtime-322`. The decision record is
`docs/theory-pw-outer-runtime.md`.

## What was built

- **`pw-run 1`.** An execution contract that declares:
  - worlds, as check-input envelopes given inline or by file
  - candidate edges, each with its acceptance
  - source-claim comparisons
  - an embedded `pw-surface 1` document, which the declared-wire decoder reads unchanged
- **`lara pw <file>`.** The Haskell runtime, in `src/Lara/PW/{Surface,Sorted,Wire,Run}.hs`. It checks every world with the unchanged local checker (`checkUnitWith fullConfig`) and prints a `pw-result 1` or `pw-error 1` envelope.
- **`pw-run`.** The Lean reference executable, in `lean/Lara/PW/{Run,RunMain}.lean`. It uses `Declared.load`, `elabPosed`, `evalFinite` and `crossComparePosed` over a host built from the file.

## What is proved (Lean, `lean/Lara/PW/Run.lean`, all in AxCheck)

- `Model.evaluates_iff`: each printed answer is `evalFinite` over a `Finite` presentation. It is therefore `PW.Sat` of the elaborated query in the frame the file declares.
- `Model.presents`, `Model.compare_mem_iff_sat`: the declared candidate list and acceptance test `Presents` the frame by construction. So a status is in a printed comparison profile exactly when `⟨b⟩Status_s(τ_b(c))` holds.
- `indexIn_declared`, `Model.index_declared`, `Model.candidates_declared`, `Model.accepts_declared`: at declared worlds, the frame's candidates and acceptance are exactly the resolved edges, read at world positions. This rests on the loader's invariant that no two worlds of a context share a checked program.
- `resolveEdges_declared`, `loadWorlds_nodup`: resolution keeps the file's edges one for one, each along the bridge its name finds, with its declared acceptance, at the positions of the worlds it names; and no context holds two worlds with one identifier.
- `Model.candidates_named`, `Model.accepts_named`, `load_candidates_named`, `load_accepts_named`: for a loaded run, the frame's candidates and acceptance are the file's declared edges read by name. Added in the second review round; before it, the step from names to positions was only tested.
- `ResultTag.parse_text`, `ResultTag.text_injective`: every keyword of the result protocol has one spelling.
- `decodeRun_encode`, `encodeRun_injective`: the run document round-trips through its structured codec, including the embedded surface document.

## Conformance experiment

`scripts/check-pw-conformance.py` runs both drivers on the 6 committed fixtures (`fixtures/pw/run/*.sexp`), each with a golden. The fixtures cover nested modalities that complete, a world with no candidates, all five posing faults, canonical numerals, and the rule clause under a renaming symbol map (`renamed.sexp`).

The gate also runs 94 generated cases, which mutate those fixtures. They cover:

- every stage and fault, and declaration/name mismatches
- stage order, and fault order within each stage
- every field of a context's environment
- each position the rule clause translates, broken in turn
- symbol-map and acceptance dependence, including all-rejected bridges
- quoted Unicode names; non-ASCII world paths, run-file paths and run directories, including missing ones; and files that are not UTF-8

The Unicode-name and path cases run again under `LC_ALL=C` and under an ISO-8859-1 locale, and an unreadable run file is one more run: 107 runs in all. The two drivers agree byte for byte and on exit codes. The exception is three faults whose final atom is runtime-specific text; there the gate checks the arity and masks only that atom. The fixtures reproduce the PW0 T7 witness from a file (p is justified at w0 and defeated along the accepted edge). Remapping `p → q` changes a comparison profile, and the gate checks that the run's queries section stays equal to the unmapped golden's.

An independent review compared the Haskell code with the Lean definitions line by line and found no input on which the runtimes' output diverges. It found two gaps, both fixed before commit:

- The gate compared mutation cases as parsed trees; it now compares bytes.
- `lara pw` encoded stdout through the locale, so under `LC_ALL=C` it would crash on a Unicode name; it now forces UTF-8.

### Second review round

Two further reviews found one real divergence the first review and the gate had missed. Under `LC_ALL=C`, a world file with a non-ASCII path made `lara pw` refuse the run (exit 1, `world-input … cannot encode character`) while `pw-run` completed it (exit 0). GHC encodes file paths with the locale's encoding, which is ASCII under `C`; Lean always uses UTF-8. The gate missed it because its only `LC_ALL=C` case used inline worlds. Fix: `lara pw` sets GHC's file-system encoding to `UTF-8//ROUNDTRIP`. The new `non-ascii world path` case fails on the pre-fix binary under `LC_ALL=C` and passes after the fix.

The same round:
- proved the step from edge names to positions (above);
- replaced the result protocol's string literals with one closed `ResultTag` table on both sides;
- added the fault-order, environment-field, renamed-rule-clause and text-boundary cases counted above;
- made the gate's detail masking check each fault's arity.

A re-review then found that fix incomplete. `getArgs` had already decoded the run-file argument with the locale, so under ISO-8859-1 a run file under `café/` was looked up as `cafÃ©/`, which regressed runs that had worked at 502a564. Under `LC_ALL=C`, a missing non-ASCII path also crashed stdout partway through the envelope. `lara pw` now turns the argument back into its original bytes and decodes them as UTF-8, and stdout writes escaped bytes back instead of failing. The gate builds an ISO-8859-1 locale with `localedef` and reruns every non-ASCII path case under it. Those cases fail on the intermediate binary and pass after the fix.

The reader's Haskell-only nesting bound (10000) is a pre-existing divergence, now tracked as follow-up work.

Commands and results are in `pw_outer_runtime_verification.txt`.

## Limits retained

The following are documented, not proved:

- The Haskell runtime is conformance-tested against the reference, not proved.
- The byte reader and printer remain a tested boundary.
- Canonicalizer agreement comes from the shared `dcanon`.
- `leaf-ok` and `cert-ok` must be listed but are never proved.
- Acceptance is declared host data, not T6 applicability.

Deferred and filed as follow-up issues:

- Worlds that declare duplicate-report groups are refused.
- `.lara` world sources are not supported.

Unchanged: the local checker wire, `pw-surface 1`, `PW.Frame`, `PW.Sat`, `crossCompare`, T6, the corpus, and every freeze tag.
