# The Lean wire reader's nesting bound, proved (issue #335)

Trace nodes: `N335_reader_totalization` (the design), `N335_bound_proved` (the result).
Branch `fix/335-lean-reader-nesting-bound-proved`, commit `81dea71`. Every declaration
below is gated in `lean/AxCheck.lean`.

## What was open

`Lara.Driver.parseWire` enforced the shared `maxDepth = 10000` bound byte for byte with
`Lara.Wire.parseSExprBS` — same message, same column, same exit code (#331). Nothing about
it was provable. `parseForm`, `parseList` and `parseQuoted` were a `partial def` mutual
block, and Lean's kernel has no reduction behaviour for a `partial def`: there are no
equation lemmas, so no statement about the function's results can be discharged. The
enforcement was real; the only evidence was behavioural — the straddling cases in
`scripts/differential.sh`, `scripts/check-map-conformance.sh` and
`scripts/check-pw-conformance.py`, plus `prop_envelopeNestingBound` in `test/MapSpec.hs`.

`AxCheck.lean` was correctly untouched at #331: there was no theorem to cover.

## What made it provable

The blocker was structural, so the reader is now a total definition. Three moves:

1. `skipComment` / `skipSpace` become well-founded on the remaining input. Both rest on
   `step_input` — `(step p).input = p.input.tail`, i.e. `step` drops exactly one character
   and nothing once the input is spent — which also yields `skipComment_length_le` and
   `skipSpace_length_le`.
2. `parseQuoted` leaves the mutual block. It never recurses back into a form, so it
   terminates on the remaining input alone.
3. `parseForm` / `parseList` stay mutual, measured `2 * |input|` against `2 * |input| + 1`.
   The half-step is what lets `parseList` hand `parseForm` a `skipSpace`d state that may be
   no shorter than its own.

Move 3 leaves one real gap, and it is the whole difficulty: `parseList`'s element loop
recurses on `parseForm`'s *output* state, and nothing outside `parseForm` knows that state
is smaller. Establishing it afterwards is circular — the lemma would be about a function
whose definition needs the lemma. It is closed by carrying the fact in the result type:

```lean
structure Parsed (p : PState) where
  sx : Sx
  rest : PState
  consumed : rest.input.length < p.input.length
```

`parseWire` re-exports the plain `Except String Sx` contract, so the subtype reaches no
consumer — `Lara.Map.Driver`, `Lara.PW.Wire`, `Lara.PW.Run` and `Lara.AdmissionDriver` are
untouched.

## What is proved

| Declaration | Meaning |
| --- | --- |
| `parseForm_of_maxDepth_lt` | past the bound the reader refuses on depth alone: `parseForm depth p = .error (p.locate depthExceededMsg)` whenever `maxDepth < depth`, before it dispatches on the input |
| `parseList_error_of_parseForm_error` | a failed element read is reported verbatim, at the **post-`skipSpace`** state `parseList` handed to `parseForm` |
| `parseList_of_maxDepth_lt` | the specialization of the two: a list whose elements would sit past the bound is refused at the post-`skipSpace` position, not the list's own |
| `parseForm_nested_error` | `n` nested lists around a form put it at depth `depth + n`; when `depth + n = maxDepth + 1` the refusal fires there, located `n` columns right of where the opens began, independently of what the form is |
| `parseWire_nested_error` | the top-level statement: `parseWire (String.ofList (opens n ++ u))` with `maxDepth < n` and `u` starting a form is `.error` with the depth message at line 1, column `maxDepth + 2` |

The supporting lemmas (`step_input`, `step_length_lt`, `step_length_le`, `step_of_cons`,
`skipComment_length_le`, `skipSpace_length_le`, `skipSpace_eq_self`,
`skipSpace_eq_self_startsForm`, `spanBare_length`, `spanBare_fst_ne_nil`,
`spanBare_snd_length_lt`, `isBareChar_props`, `startsForm_of_isBareChar`,
`startsForm_opens`, `opens_add`) are pinned too, as whole-tree AxCheck coverage requires.

The position half is the one worth naming. The two readers agree on the *column* because
both skip leading space before fixing the reported position; `parseList_error_of_parseForm_error`
is that fact as a theorem rather than as three gates' worth of cases that happen to agree.

## Outside the proofs

- The Haskell reader. `src/Lara/Wire.hs` is unchanged and carries no proof; the two sides
  are still tied by the three differentials and by the source-level constant check, not by
  a shared mechanization.
- `printSx` remains a `partial def` — it is the printer, not the reader, and #335 is about
  the bound.
- Nothing is proved about the reader's *accepting* behaviour. The theorems are refusal
  statements; that an input at or under the bound parses is still gate evidence only.

## Checks run

Every gate below is the committed one, run unmodified, and every number is unchanged from
before the rewrite — the refusal behaviour did not move.

- `lake build`: `Build completed successfully (218 jobs).`
- Whole-tree AxCheck coverage: `AxCheck coverage passed (3147 declarations).`
- Axiom audit: `Axiom audit passed.` — the five theorems above report only `propext`,
  `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`.
- `scripts/differential.sh`: `pass=673 fail=0`, `negative pass=66 fail=0`,
  `shared nesting bound: 10000`, `depth-bound pass=3 fail=0` (over, at, and the
  wide-not-deep counter-case).
- `scripts/check-map-conformance.sh`: `differential pass=1322 fail=0`,
  `depth-bound pass=2 fail=0`, `map anchors: cross-driver pass=4  pre-boundary=3  fail=0`.
- `scripts/check-pw-conformance.py`: `PW outer runtime conformance passed: 7 fixtures, 101
  cases, 114 runs; 1 .lara source fixtures, 17 source cases, 21 runs.` Run with
  `check_pw_subtree_total` skipped: that assertion fails on `fixtures/pw/source/lara.sexp`
  on `main` as well (the tree arrived in #332, after the assertion was written) and is
  unrelated to this change.
- `scripts/check-lean-citations.py`: `Lean citations: PASS (420 citations, 29 allowlisted)`
  after repointing the nine `lean/AxCheck.lean` line citations in
  `docs/paper-lean-name-map.md` (+33, by name).
- `scripts/check_ara_source_spans.py`: `ARA source spans: PASS (66 quotations)`.
- Timing spot-check: `lara-driver` on the largest anchor
  (`corpus-units/adaptive-pruning/C04/unit.core.sexp`, 17 055 bytes) runs in 0.01 s total.
  The 10 002-sibling wide case and the 10 001-deep over-bound case both still exit 2, so
  the loss of `parseList`'s tail call to the `liftParsed` wrapper costs no stack.

## Cost

None of the costs the issue budgeted were incurred: no corpus regeneration, no freeze-tag
bump, no wire, mutant or replay-identity byte moved. The re-audit of proofs consuming
`parseWire` was empty — nothing consumed `parseForm`/`parseList`/`parseQuoted` outside the
mutual block, and `parseWire`'s type is unchanged.
