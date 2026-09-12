# Possible-world semantics spike: close-out record (tracker #189)

_Status: closed 2026-09-06 at `c4363eb`. Every child issue of tracker #189 —
#192 (PW0), #191 (T6), #193 (T8), #190 (T9) — is landed and closed. This
document is the spike's index and the durable home for the work the tracker
deferred, so the deferral survives the tracker's closure. It records no new
result: each frozen contract keeps its own document._

_Updated 2026-09-09: the deferrals this document and
`docs/theory-pw0-outer-model.md` §5 were holding for the M5 surface machinery
were scheduled and landed as #307 — the `Query_κ` well-sortedness refinement
(a `docs/theory-pw0-outer-model.md` §5 non-goal row) and the outer language's
surface syntax (the §3 row below, which mentioned the refinement in prose).
Their frozen contract is `docs/theory-pw-sorted-queries.md`, listed in §1
below. Everything else in §3 stands._

_What the wrapper is, in one sentence: an outer model that treats each
checking context (its vocabulary, policy, setting) as a world, so that
support and status established in one world can be transported to another
only along an explicitly declared, checked bridge._

**Audience:** anyone asking what the possible-world wrapper delivered, whether
a possible-world extension is scheduled, or why an idea they have in mind was
deliberately not built.

## 1. What the spike delivered

| Result | Issue | PRs | Lean | Frozen contract recorded in |
|---|---|---|---|---|
| PW0 — outer model, executable comparison boundary, T0–T5, the T7 counterexample | #192 | #221 | `Lara/PW/{Outer,Instance,Uniform,Compare}.lean`, `Lara/Examples/PW.lean` | `docs/theory-pw0-outer-model.md` |
| T6 — exact checked-support transport | #191 | #223, #230 (off-identity `cert_ok` witness, #224) | `Lara/PW/{Structural,Translation}.lean`, `Lara/Examples/PWStructural.lean` | `docs/theory-pw-t6-structural-transport.md` |
| T8 — conditional status preservation | #193 | #240; #244 (decider, #239); #246 (`AttackBridge`, #238) | `Lara/PW/{Status,AFBisim,StatusCheck,AttackTransport}.lean`, `Lara/Examples/{PWStatus,PWStatusCheck,PWAttack}.lean` | `docs/theory-pw-t8-status-preservation.md` |
| T9 — exact structural-path composition | #190 | #233, #236; #243 (executable witnesses, #235); #245 (traversal seam, #234) | `Lara/PW/Compose.lean`, `Lara/Examples/PWCompose.lean` | `docs/theory-pw-t9-path-composition.md` |
| Sorted queries and the outer surface — `Query_κ` well-sortedness, the refined `gap` report, bridge and query authoring forms | #307 | #311 | `Lara/PW/{Sorted,Surface}.lean`, `Lara/Examples/{PWSorted,PWSurface}.lean` | `docs/theory-pw-sorted-queries.md` |

Stable declaration names for all five are in `docs/paper-lean-name-map.md`
§§PW0, PW-T6, PW-T8, PW-T9, PW-sorted.

## 2. Gate record

The tracker set an **entry gate** (PW0 blocked by M2a #185; exact support
transport additionally by B0 #182) and a five-condition **advancement gate**.
Both were met and the exit decision was taken on #192; the assessment itself
is `docs/theory-pw0-outer-model.md` §3, condition by condition, and is not
restated here. The tracker's execution order (PW0 → T6 → T8 and T9 as
independent results) is the order the PRs above landed in.

The one gate condition that outlived PW0 — *"the structural-bridge contract is
small enough to make T6 feasible"* — was sized in `docs/theory-pw0-outer-model.md`
§6 before T6 was scheduled, and T6 landed against that sizing.

## 3. Deferred work (moved here from tracker #189)

Nothing below is scheduled except where struck through. This is the list the
tracker carried; it lives here now because a closed issue is a poor home for a
standing decision.

| Deferred | Condition for scheduling |
|---|---|
| **T10 — translated-query bisimulation** | Only if bridge-global translation proves inadequate. Today it does not: T6 limitation 1 (bridge-global, functional symbol translation) is a recorded design commitment, not an observed failure. |
| Approximation bridges | None set. Out of the wrapper's scope by design. |
| Epistemic relations | None set. |
| Dynamic modal update operators | None set. |
| Hybrid / named-world operators | None set. |
| Global scenarios | None set. |
| ~~Surface syntax for the outer language~~ | This row recorded **no scheduling condition**. The condition it was really waiting on — M5's sorting machinery (#188) — landed, and the row was then **scheduled and landed as #307**, together with the `Query_κ` well-sortedness refinement it mentioned in prose (a `docs/theory-pw0-outer-model.md` §5 row, not a row of this table). Both are in `docs/theory-pw-sorted-queries.md`. The follow-up **#313/#314** now adds a concrete codec, checked declaration/query linkage, and a file-driven Lean example with proved finite evaluation. See `docs/theory-pw-declared-wire.md`. Haskell outer execution and differential conformance then landed as **#322**; see `docs/theory-pw-outer-runtime.md`. |

Also standing from the tracker, and unchanged: do not weaken a failed theorem
into a definitional restatement, and do not move any of the above into the core
calculus tracker.

## 4. What is still open

The spike closes with open *limitations*, all of them recorded design
commitments with named homes — §4 of the PW0 document, §8 of T6, §9 of T8, §7
of T9. Two are live issues rather than accepted boundaries:

- **#231** — guard the T6 strict-certificate fixture against certifier and
  assurance drift. Follow-up coverage, not a soundness defect in
  `support_transport`.
- **#248** — name the T8 `matched` clause and unify the two totality deciders.
  Readability only; see §5.

## 5. The T8 checker landed off its plan, deliberately

`plans/2026-09-05-pw-t8-statusbridge-checker.md` specified the decider as a new
§5 *inside* `Lara/PW/Status.lean`, built on a shared `bisimScanB` scan proved
sound and complete once and instantiated twice, with the three hand-proved
positive cells in `Lara/Examples/PWStatus.lean` rewritten to `decide`. PR #244
landed something simpler, and the difference is worth keeping:

- **A separate module.** `Lara/PW/StatusCheck.lean` only imports the T8 layer,
  so the frozen T8 record — `Status.lean` and the hand proofs in
  `Examples/PWStatus.lean` — is untouched. The hand proofs state *why* the
  bridge holds in the source language's own terms; the decider cross-checks
  them instead of replacing them.
- **`decide (∀ i < …, …)` instead of hand-rolled scans.** `forthB`/`backB` go
  through `Nat.decidableBallLT`, so there is no scan ladder to factor and no
  `forthB_sound`/`_complete` pair: `statusBridgeB_sound` and
  `statusBridgeB_complete` discharge both clauses directly, using `corr_lt` for
  the corresponded indices and `edgeB_faithful.ranged` for the attacking one.
  This is why the plan's `bisimScanB` and its geometry diagram are moot rather
  than outstanding (#248).
- **Fixture-scale only.** The decider is `O(n²m²)` kernel steps, each
  recomputing a `trSupport` traversal and a `coveredB` scan. Free on the T8
  conformance cells, useless on a realistic argument count. The full statement
  of that boundary, and why hoisting `trSupport` out of `corrB` is not to be
  done speculatively, is the module docstring of `Lara/PW/StatusCheck.lean`.

The plan file is deleted with this record, per the repository's plan discipline.

## 6. Verification snapshot

At `c4363eb`, whole-tree AxCheck coverage passes at **2319 declarations**
(`scripts/check-axcheck-coverage.py` over `lean/AxCheck.lean` and all 99
`lean/Lara/**/*.lean` sources). The axiom audit admits only `propext`,
`Classical.choice`, and `Quot.sound`, so no PW declaration can reach a
`sorryAx`, `ofReduceBool`, or `nativeDecide` obligation. Per-result
verification sections — including re-verification dates after later merges —
are in each result's own document.
