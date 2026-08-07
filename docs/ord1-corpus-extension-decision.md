# Decision: how `ord@1` earns corpus evidence (and why not yet)

_Resolves the `TODOS.md` item "Corpus extension exercising `ord@1` end-to-end"
(eng review 2026-08-06, PR #83). Companion to
`docs/strict-backend-decision.md` and `plans/2026-08-06-ord1-comparison-backend.md`._

## The question

`ord@1` is motivated by "the most common claim shape in ML methodology papers".
PR #83 landed the backend, its Lean metatheory, and a synthetic worked example,
but kept `corpus-v1` frozen. So the motivation is currently an argument, not a
measurement: no real paper's beats-claim has gone through the backend.

The open question was whether to extend the corpus with real measurement units
flowing cells → `num_lt` → bridge rule → comparative claim.

## Decision

**Not before the PLDI submission. The demonstration lands in `examples/`, and
the corpus extension is deferred to a `corpus-v2` cycle.**

Concretely, what was built instead (this branch):

- **S3** (`examples/S3/`) — the `num_le` tie. The family's second member had no
  worked example at all; it now has one, and it sits exactly on the boundary
  where the two members separate.
- **S4** (`examples/S4/`) — an audit undermines the binding leaf, so the bridge
  is defeated while the certified comparison stays justified.

Together with S2 these are three artifacts sharing one shape and varying one
thing each, which is what makes them readable as a set.

## Why defer the corpus half

1. **Cost is a refreeze, not an edit.** `corpus-units/` is row 2 of
   `docs/m5-freeze-checklist.md`. Touching it regenerates the seeded mutant
   suite (the sweep derives mutants per corpus unit), invalidates
   `measurements/frozen/`, and forces a re-run of `scripts/measure.hs` plus a new
   `m5-freeze-v4` tag. That is M5-scale work, and #60/#78 already ruled an
   M5-scale refreeze out inside the PLDI window.

2. **The paper's claim does not rest on it.** The evaluation section reports
   axis (a) mutation/differential testing and checker-side axis (c). `ord@1`'s
   contribution to that section is conformance evidence — the differential
   anchors and the property suite — not corpus coverage. The corpus establishes
   that the *calculus* handles real claims; it does not need every backend
   represented to do so.

3. **What a corpus unit would add is a different kind of evidence.** It would
   answer "do real beats-claims fit this shape without distortion?", which is an
   empirical question about the *modeling*, and one worth asking properly rather
   than by adding one unit to an otherwise frozen sample. Doing it well means
   sampling beats-claims the way M5 sampled the original 60, which is a
   measurement task with its own protocol.

## What the corpus extension would need, when it runs

Recorded now so the deferral does not lose the design. `examples/S2` is the
template; a corpus unit instantiates it with a real paper's numbers.

- **Two reported cells as observed leaves**, each carrying exactly one numeric
  literal (the premise-cell convention) and its own `refs` into the artifact's
  evidence.
- **A binding leaf** — S2's `comparison_setup` — naming which systems and
  measurand the two numbers belong to. This is the piece a real paper usually
  leaves implicit in a table caption, and eliciting it is the part of the
  lowering that will take judgment.
- **A strict re-check rule** with `certifiers = [(ord@1, <digest>)]` and an empty
  theory, plus **a defeasible bridge rule** consuming the comparison and the
  binding. Both already exist verbatim in `examples/S2/ord-v1.policy.lara`; a
  corpus policy would adopt them rather than reinvent them.
- **A decision about `corpus-v1`'s rule vocabulary.** The existing corpus policy
  has no comparison family. Adding one is a policy change affecting every unit's
  `unit.core.sexp` through the shared policy — which is precisely why this is a
  `corpus-v2` question and not a unit-level edit.

## Status of the motivation claim, stated honestly

Until the above runs, the correct wording in the paper is that `ord@1` certifies
a claim shape that is *pervasive in the literature*, evidenced by the design
argument and the worked examples — **not** that it has been measured over the
corpus. `docs/m5-freeze-checklist.md` reports the frozen claim-support number as
`1/1` (`adaptive-pruning/C04`, `ra@1`); `ord@1` contributes no corpus row and
should not be described as if it does.
