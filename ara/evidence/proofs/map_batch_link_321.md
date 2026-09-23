# The batch link construction, mechanized

Trace node: `N321_batch_link`. Commit `bf31acc` on branch `map-followups-316-321`
(cherry-picked from `104aa86`). All declarations are gated in `lean/AxCheck.lean`.

## What was open

`linkMembers_checked` proved acceptance for a *fold* that links one member at a time and
saturates only each step's boundary. Both drivers instead saturate every cross-member pair of the
fully merged argument list in one batch. The two were argued to coincide, not proved to.

## What is proved

| Declaration | File | Meaning |
| --- | --- | --- |
| `crossPairs` | `lean/Lara/Map/Batch.lean` | the one batch saturation generator |
| `batch_checked` | `lean/Lara/Map/Batch.lean` | the batch unit is accepted by `checkUnit`, for any duplicate-free argument list and any attack list with the right members |
| `batch_atts_mem_iff_fold` | `lean/Lara/Map/Link.lean` | batch and fold produce the same attacks |
| `batch_args_mem_iff_fold` | `lean/Lara/Map/Link.lean` | batch and fold produce the same arguments |
| `linkedUnitOf_checked` | `lean/Lara/Map/Driver.lean` | `batch_checked` applied to the Lean driver's own linked unit |
| `contestedPairs_batchUnit_checked` | `lean/Lara/Map/Link.lean` | a two-member witness discharging every premise |

Premises of `batch_checked`: distinct member aliases; no leaf identity declared twice across the
map; each member well-formed (`SideOk`) under its own environment; a cross-member predicate
admitting every pair declared by two differently aliased members; and the signature-stage,
scope, rule-id and policy well-formedness premises that `linkMembers_checked` also takes.

Key step of the equivalence: a member's argument has the same conclusion in every environment
that extends the member's own (`SideOk.mono_gamma` plus `hasSupport_unique`), which reconciles
the fold's per-step environment with the batch's whole-map one. The equivalence takes one premise
`batch_checked` does not: every member carries the shared policy (`hpol`), because the fold reads
each member's own policy at every step. `linkMembers_checked` already takes it, and the loader
establishes it for every real map by comparing each member to the manifest's contract.

## Outside the proofs

- Each member's solo check: no envelope byte records that it passed.
- The Haskell driver: tied to the Lean driver by `scripts/check-map-conformance.sh`, byte for byte.

## Checks run

- Lean driver output identical before and after the refactor on all 19 envelopes
  (3 anchors + 16 malformed).
- `lake build`: 186 jobs, success. Whole-tree AxCheck coverage: 3026 declarations. Axiom audit:
  passed, only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`.
- Map conformance after the cherry-pick: cross-driver pass 4, 1322/1322 differential cases.
