# Decision: what `lean/Lara/Examples/` is for, and why it is not a duplicate test suite

_Records the settled rule for the Lean example corpus, fixed by the Lean-volume
audit of 2026-09-04. That audit asked whether a 93,897-line `lean/` against a
24,239-line `src/` was carrying redundant weight, and examined `Examples/` as
the largest candidate for removal. It is not removable; this record says why, so
the "delete the duplicate test suite" refactor is not attempted again.
Companion to `docs/mechanization-scope-decision.md` (what the Lean development
mechanizes) and `docs/mechanization-plan.md` (how)._

Two terms used throughout: a *differential emitter* is a Lean program that
prints checker output so it can be compared byte-for-byte against the Haskell
checker's output on the same input; "the gates" are the CI checks that fail on
any disagreement.

## The rule

**`Examples/` is the shared fixture corpus the differential emitters run on,
plus the concrete witnesses that separation results require. It is not a second
copy of the gates.**

Two distinct loads, both structural:

1. **Fixtures the emitters import.** Every golden emitter that anchors a
   cross-language differential gets its definitions from `Examples.*`. Deleting
   the corpus does not shrink the gates; it breaks them.
2. **Witnesses for negative results.** A differential proves *agreement* with
   the Haskell checker. It can never establish a negative — "this weaker
   property does not imply that stronger one", "this observation is not
   determined by that profile". Those need an exhibited counterexample, and the
   counterexample is a closed term in `Examples/`.

## Evidence

### The emitters import the corpus

All five golden emitters `import` `Examples.*` and reuse its definitions:

| emitter | imports |
| --- | --- |
| `lean/BackendDepsGolden.lean` | `Lara.Examples.BackendComposition` |
| `lean/SemanticsGoldens.lean` | `Lara.Examples.Semantics` |
| `lean/UpdateMatrices.lean` | `Lara.Examples.Update` |
| `lean/Lara/SurfaceConformanceMain.lean` | `Lara.Examples.Surface` |
| `lean/Lara/UpdatePreconditionParityMain.lean` | `Lara.Examples` |

Reproduce from `lean/`:

```
for f in BackendDepsGolden.lean SemanticsGoldens.lean UpdateMatrices.lean \
         Lara/SurfaceConformanceMain.lean Lara/UpdatePreconditionParityMain.lean; do
  echo "== $f"; grep '^import' "$f" | grep -i example
done
```

### The separation results have no differential counterpart

`Examples/` declares **797** theorems. Of those, **116** carry a negative or
separation morpheme in the name — `not`, `no`, `ne`, `non`, `never`, `fails`,
`rejected`, `counter`, `strictly`, `absent`, `excluded`, `weaker`. Named
instances, all in `Lara/Examples/Semantics.lean`:

- `agreesOnArgs_strictly_weaker_than_faithful` (`:772`) — the weaker relation
  does *not* imply faithfulness, so the transport theorems may not be restated
  over it.
- `observe_not_determined_by_profile` (`:366`) — two semantics agreeing on the
  acceptance profile can still be separated by observation.
- `not_faithful_eJunk` (`:755`) — an exhibited non-faithful compilation.

Reproduce the count from `lean/`:

```
grep -rhoE '^[[:space:]]*(@\[[^]]*\][[:space:]]*)*(private[[:space:]]+)?(protected[[:space:]]+)?(theorem|lemma)[[:space:]]+[^[:space:]:{(\[]+' \
  --include='*.lean' Lara/Examples Lara/Examples.lean | awk '{print $NF}' \
  | grep -cE '(^|_)(not|no|ne|non|never|fails|rejected|counter|strictly|absent|excluded|weaker)'
```

The morpheme scan is a name-shape heuristic, not a proof-shape classifier;
treat 116 as a floor on the separation results, not an exact partition. The
argument does not depend on the exact figure — one irreproducible negative
would carry it — but the figure shows the category is large, not incidental.

### Removable surface: zero

Combining the two: the fixtures are load-bearing for the gates, and the
separation results are unreachable from the gates. No subset of `Examples/` is
redundant with the differential machinery, and the audit identified no file to
remove.

## Rejected alternative

*Delete `Examples/` as redundant with the cross-language differential gates.*

Rejected on both loads at once:

- **It does not preserve the gates.** The emitters import the corpus; removing
  it removes the definitions the goldens are generated *from*. The differential
  would have to re-declare the same fixtures under another name — the same
  lines, relocated, with the proofs about them dropped.
- **It destroys results the differential cannot restate.** Agreeing with the
  Haskell checker on every input never establishes a negative. A differential
  has no way to say "no faithful compilation exists here"; only an exhibited
  witness does. Those 116 theorems have no cross-language surrogate.

The volume question that prompted the audit has a separate answer: scored in
CompCert's published categories, `lean/` is 24.4% definitions, 18.1% theorem
statements, 43.4% proof scripts, against CompCert's 14% / 21% / 44%.
Verification-to-code is ~2.5x here, ~6x for CompCert, ~23x for seL4. The
mechanization is not disproportionate for what it claims.

## Methodology notes for the next audit

Two rules that cost false starts the first time. Both are about counting, and
both bite anyone re-running this analysis.

**1. Ledger absence is meaningful only for public declarations.** `#print
axioms` cannot reach a `private` declaration from another module, and
`AxCheck.lean` references zero private names — it cannot. `Examples/` holds
**137** private theorems. Reading their absence from the ledger as evidence of
deadness produced two false positives before the rule was found. The coverage
checker already knows this; ad-hoc greps do not.

**2. Use `scripts/check-axcheck-coverage.py` for any recount.** Two
reimplementations written during the audit reported 264 and 449 gaps against
the checker's 353 — one missed attribute-prefixed declarations
(`@[simp] theorem …`), the other mishandled bare `end`. The checked-in script
handles both, is itself unit-tested by
`scripts/test_check_axcheck_coverage.py`, and is the number of record. It also
resolves names fully-qualified, so an `open Lara` in `AxCheck.lean` with a
short-name `#print axioms` entry reads as a gap — write ledger entries
fully-qualified.

Run it from `lean/`:

```
python3 ../scripts/check-axcheck-coverage.py AxCheck.lean $(find Lara -name '*.lean' | sort)
```

Of the 353 gaps the audit found, only 9 were in `Examples/`; the gap was in the
core mechanization — not a reason to touch this corpus.
