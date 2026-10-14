# Process-corpus pilot

This pilot runs the research-process semantics
([`docs/theory-process.md`](../../docs/theory-process.md)) on one real record from
the corpus, decoded by hand, before anyone writes a decoder (#63). The record is
MALT run 4 (`run_id=345751`) of
`corpus/ara-paperbench/artifacts/rebench/rebench-fix_embedding/`, at corpus pin
`62e9b54`. It is evidence about the corpus and the mapping. It makes no claim
about the agent or the task.

## The question

The run reports a best score after a sequence of attempts. A best-of-k result
needs k: how many attempts competed for "best"? The query is
`family-count-at-most fix-embedding k`: did at most k runs occur in the
attempt family?

## How the trace was decoded

| Trace | Process entry |
| --- | --- |
| Task specification (node `N01`) | `commit-plan agent task 0`, the plan every attempt runs under |
| Each run-4 node `N250`–`N255`, scored or dead end | One `run` event in family `fix-embedding`; dead ends count, as failed runs do |
| Header line "all attempts included" (line 145) | `complete` coverage of `analysis-run` events in the family, basis `author-declaration` |
| One attempt that may have gone unrecorded | The declared `universe` |

The trace has no timestamps (every `timestamp` is `null`), so there is no order
evidence. `strict.sexp` and `lax.sexp` chain the attempts in list position as an
enumeration device, labelled as such in the file. The family-count query reads
only how many runs occurred, so the chain changes no verdict. A 4-attempt cut
gives identical verdicts ordered (6 histories) and unordered (144).

## Results

```sh
cabal run -v0 exe:lara -- inquiry evaluation/process-corpus-pilot/strict.sexp
cabal run -v0 exe:lara -- inquiry evaluation/process-corpus-pilot/lax.sexp
# Expected exit 1: refused at the declarations ceiling.
cabal run -v0 exe:lara -- inquiry evaluation/process-corpus-pilot/unordered.sexp
```

| Document | Reader admits author declarations | Histories | At most 6 runs | At most 5 runs |
| --- | --- | ---: | --- | --- |
| `strict.sexp` | no | 8 | `unknown` | `certainFalse` |
| `lax.sexp` | yes | 1 | `certainTrue` | `certainFalse` |
| `unordered.sexp` | no | 5,760 | refused (`declarations` 17,280 > 10,000) | refused |

The `.expected` files hold both drivers' output. The Lean reference runner
(`lake exe inquiry-run`) gives the same bytes for all three.

## Findings

1. **A trace node is not an event.** The six nodes hide at least 15 `score.py`
   calls: N250 two (one failed with `KeyError 'config'`), N251 one, N252 four
   (α ∈ {0.7, 1.0, 1.5, 2.0}), N253 two, N254 five, and N255 at least one, which
   failed out of memory. The lax reader's `certainTrue` for "at most 6 runs" is
   correct for the decoded record and wrong about the run. That is the
   decode-boundary assumption (`SourceRel`) failing, not the semantics: the
   theorems promise correctness only for a faithful source. A faithful decoder
   needs one event per scoring call, and the trace states those counts only in
   the prose of `method` and `result`.
2. **List order is not chronology.** Some nodes cite transcript message
   numbers. In run 4, N255 (listed last) cites msg 45 and N250 (listed first)
   cites msgs 69 and 77. Across the two RE-Bench traces with per-run node lists
   (`fix_embedding`, `triton_cumsum`), 130 of 549 nodes cite message numbers. Of the 15 runs with at least two citing nodes, 9 list them
   out of message order. A decoder must not emit `order` entries from list
   position.
3. **Without order evidence, enumeration explodes.** Six unordered attempts give
   720 orderings, and with one possible unrecorded attempt, 5,760 histories. The
   document is refused even at the checker's fixed ceilings. The median
   `fix_embedding` run has 12 nodes and the largest has 18, before splitting
   nodes into scoring calls.
4. **The completeness claim is not trusted.** "All attempts included" is the
   trace author's statement. Under the default reader it is not applied, so a
   family-size bound stays `unknown`. The raw MALT logs that could back it with
   an instrumented-log basis are not in the corpus, and #63 proceeds without
   them.

## What this means for #63

Family-size questions about these runs can be stated. Without the raw logs, the
honest answer is `unknown`, and the pilot reproduces exactly that. A decoder
built on node granularity would produce confident and wrong answers under any
reader that trusts the trace. The decoder has to count scoring calls, and it
must never infer order. Lifting the 8-event cap matters only after both.
