# M4a checklist — compiler end to end on the worked-examples suite

_Operational freeze/tracker for milestone **M4a** (`plans/2026-07-27-m4a-compiler-worked-examples.md`,
GitHub #31, child of the #29 M4 umbrella). Companion to `docs/worked-examples-plan.md` (the six-example
coverage design) and `docs/spec.md` (the frozen contract). Mirrors `docs/m1-freeze-checklist.md` and
`docs/m3-closeout-notes.md` in role: it records what M4a locks before frontend code lands, freezes the
verdicts that already have oracles, and lists what stays provisional until the parser + elaborator exist.
This is **Task A0** — a scope-lock/freeze doc, not a re-plan._

## What M4a is (and is not)

**M4a definition of done** (plan §"M4a Definition of Done"): the compiler works end to end on the
worked-examples suite. Concretely — `Lara.Syntax` parses `.lara` → the presentation AST
(`Program`/`Policy`), a new trusted `Program + Policy + TheoryRegistry + Σ → Unit` elaborator lowers to
the M3 checker anchor, the canonical `.core.sexp` is *derived* from the elaborated `Unit`, and golden
verdicts pin each example. It also produces the paper's motivating examples and discharges
`docs/worked-examples-plan.md` §4 (each `.lara` → `.core.sexp` + `expected.json`).

**M4a is not the walking skeleton.** The *untrusted* elaborator producing a certificate from a
real/structured source, and the "no hand-authored certificate" clause, are **M4b (#32)**. A tiny `.lara`
file *is* a hand-authored certificate; the worked-examples suite therefore satisfies the compiler + type
checker (M4a) but not M4b's machine-producer clause.

### In scope (M4a)

- The `Lara.Syntax` parser/printer and the trusted `Program → Unit` surface elaborator (A1).
- The `.lara` grammar freeze + A/B reconciliation (A0.5).
- Golden wiring of the worked-examples suite (E1–E3, R1–R3, A, B) to `.core.sexp` + `expected.json`,
  extending the existing differential harness (A2).
- Mechanizing **result 12** (`parse ∘ print == id`) in Lean, round-trip only (A3).
- Located parse/elaborate errors + a negatives suite; the `.sexp` CLI regression test.

### Out of scope (→ #32 / M5+ / TODOS)

- The untrusted elaborator + the "no hand-authored certificate" clause → **M4b (#32)**.
- The `eraseCert` / stable-argument-id `CheckedProgram` representation and **result-9**
  backend-replacement mechanization → `TODOS.md` (split from A3; A3 is result 12 only).
- A **strict-certificate worked example** was outside the original M4a scope and
  has since landed as `examples/S1/`: `lara-syntax@0.2` assurance + policy theory
  table → elaboration → `nd@1` replay.
- `Lara.Json` LLM-producer surface (#30); PaperBench evaluation (M5); elaborator faithfulness
  measurement (M5).
- Serializing gap-holes / located diagnostics into the frozen wire verdict (would reopen M3) — kept
  Haskell-side, outside the byte-differential.
- Incremental re-checking, large-graph performance, diagnostic UX; preferred/stable/complete semantics;
  the optional LP adapter.

## A0 gate

> **Gate (plan Task A0):** the A/B golden set and the coverage matrix are committed and reviewed before
> frontend code lands.

This document *is* the A0 deliverable: the frozen A/B verdicts (§1), the confirmed coverage matrix +
authored-vs-to-author accounting (§2), the provisional E/R intent (§3), and the open items carried to
A0.5/A2 (§4).

## 1. Frozen golden verdicts — Examples A and B

A and B are the only examples with a hand-computed oracle **today** (an inline `EXPECTED VERDICT (golden
oracle)` block at the bottom of each `.lara`). Their verdicts are **frozen here**, transcribed exactly
from those blocks — the four-state status of each `status`-queried claim and the grounded label of every
argument. These are the frozen golden values Task A2 will wire to the derived `.core.sexp` goldens. The
`Status` codomain is `Gap | Justified | Contested | Defeated` and the `Label` codomain is
`LIn | LOut | LUndec` (in/out/undec), per `src/Lara/AST.hs`.

Do not silently re-annotate these once the Lean oracle runs in A2: any Haskell↔Lean disagreement is a
bug fixed with a recorded note (plan Global Constraints; M3 review D16). If the oracle disagrees, the
disagreement is investigated, not the golden overwritten.

### Example A — `A/example.lara` (one paper rebuts + undercuts + undermines itself)

Compiled AF: all four arguments complete; `a1` has its critical questions discharged.

| Argument | Grounded label | Why (per inline oracle) |
| --- | --- | --- |
| `a1` | `out` (LOut) | attacked by `d1` (undercut), `d2` (undermine), `d3` (rebut); each attacker is unattacked ⇒ each `in`, driving `a1` `out` under grounded semantics |
| `d1` | `in` (LIn) | unattacked |
| `d2` | `in` (LIn) | unattacked |
| `d3` | `in` (LIn) | unattacked |

| `status`-queried claim | Four-state status | Why (per inline oracle) |
| --- | --- | --- |
| `c1` | **Defeated** | its only support `a1` is `out`; spec §8 aggregation |

Only `c1` is `status`-queried. `c1_neg` is the conclusion of `d3` but is **not** a `status` query in the
file, so it carries no frozen claim status here. (`c1_neg` being undeclared is a surface-grammar item for
A0.5, not a verdict question.)

### Example B — `B/example.lara` (two papers, cross-paper 2-cycle → `contested`)

Compiled AF: two arguments in a mutual-attack 2-cycle (`pa <-> pb`).

| Argument | Grounded label | Why (per inline oracle) |
| --- | --- | --- |
| `pa` | `undec` (LUndec) | 2-cycle with `pb`; grounded labels neither `in` nor `out` (spec §8, assumption A5) |
| `pb` | `undec` (LUndec) | 2-cycle with `pa`; same |

| `status`-queried claim | Four-state status | Why (per inline oracle) |
| --- | --- | --- |
| `c_pos` | **Contested** | its support `pa` is `undec`, none `in` (spec §8 priority) |
| `c_neg` | **Contested** | its support `pb` is `undec`, none `in` (spec §8 priority) |

Both `c_pos` and `c_neg` are `status`-queried.

## 2. Coverage matrix — confirmed + authored-vs-to-author accounting

The six-example coverage matrix (`docs/worked-examples-plan.md` §1) is reproduced and confirmed below;
the two existing teaching examples A and B are appended. Together they must touch every claim status
(justified / gap / contested / defeated), every attack kind (rebut / undercut / undermine), plus the
illegal attack and the three rejection representatives.

| # | Name | Kind | Claim status(es) | Attack type(s) | Backend | Rejection class (per §1) | File exists? |
| --- | --- | --- | --- | --- | --- | --- | --- |
| E1 | `justified-clean` | complete | justified | none | ND (trusted-policy) | — | **to author (A1)** |
| E2 | `open-gap` | complete | gap | none | ND | — | **to author (A1)** |
| E3 | `defeat-suite` | complete | defeated, contested, justified | rebut, undercut, undermine (all three) | ND | — | **to author (A1)** |
| R1 | `undeclared-leaf` | rejected | — | — | — | leaf not in `Γ` (§1 label "R1") | **to author (A1)** |
| R2 | `strict-contrary-violation` | rejected | — | — | ND | §8.1 strict-reachable `contrary` (§1 label "R2") | **to author (A1)** |
| R3 | `bad-attack-target` | rejected | — | (attempted) rebut on a **strict** rule | ND | strict rule not rebuttable (§1 label "R3") | **to author (A1)** |
| A | `self-defeating-paper` | complete | defeated | rebut + undercut + undermine (all three, in-paper) | ND | — | **exists** (`examples/A/example.lara`) |
| B | `two-paper-contested` | complete | contested ×2 | rebut (mutual 2-cycle) | ND | — | **exists** (`examples/B/example.lara`) |

**Status coverage:** justified (E1, E3), gap (E2), contested (E3, B), defeated (E3, A) — all four.
**Attack coverage:** rebut, undercut, undermine (E3, A) — all three; plus the *illegal* attack (R3) and
the non-attack dead-end N04 (E3, compiles to no edge).
**Rejection coverage:** three distinct representatives (R1/R2/R3 example labels above; see §4 for the
spec-class mapping the full mutation suite already carries).

### Authored vs to-be-authored

- **Already authored** (`.lara` files present in `examples/`, verified 2026-07-27): `A`, `B`, and the
  shared policy `empirical-v1.policy.lara` (the trusted policy both A and B check against). A and B
  additionally have inline oracles and are frozen in §1 above.
- **To be authored in A1** (`.lara` files do **not** exist yet): `E1`, `E2`, `E3`, `R1`, `R2`, `R3`.
  Per the plan, **E1 is the vertical slice** — authored first, its verdict frozen from the Lean oracle,
  then E2/E3/R1–R3 follow as the layers land.

## 3. Frozen verdicts for E1–E3 / R1–R3 (A1, verified by `test/WorkedExamplesSpec.hs`)

**These verdicts are now FROZEN.** As of A1c-2 (2026-07-28) the six examples are authored as
`.lara` files, elaborate through the real parser + elaborator, and are verified by
`test/WorkedExamplesSpec.hs`, which loads each `.lara` + its co-located policy, `elaborate`s to a
`Unit`, runs `Lara.Driver.runUnit`, and asserts the values below (the same in-process path
`app/Main.hs` takes for a `.lara` file, so these are the exact CLI verdict bytes). The Lean
byte-differential over the derived `.core.sexp` and the per-example `expected.json` remain **A2's**
job; A1 freezes the verdicts from the Haskell `runUnit` (the M3 checker, byte-mirrored to Lean).

The **R-series spec-class mapping is now resolved** (superseding the earlier "R7" question in §4
item 2): R1 → **R1**, R2 → **R12**, R3 → **R10**. All three are verified verdicts, not intentions.

| Example | Frozen verdict (verified) | File |
| --- | --- | --- |
| E1 `justified-clean` | **VAccept**; single support `a1 → in`; `status c1 → justified`; no attacks. Smallest end-to-end path (leaf → scheme → support term → compile → grounded → aggregate). | `examples/E1/example.lara` |
| E2 `open-gap` | **VAccept**; no arguments; `status c1 → gap` (empty complete support — the §4-item-3 re-word: a claim with no assembled support, `statusC = Gap iff null claimSupport`, not an open mandatory CQ). | `examples/E2/example.lara` |
| E3 `defeat-suite` | **VAccept**; three (M,D) contexts: `a_j→in` (c_j **justified**), `a_d→out` (c_d **defeated**, via undercut `d_uc` + undermine `d_um`), `a_c/a_cn→undec` 2-cycle (c_c/c_cn **contested**). All three attack kinds — **rebut + undercut + undermine** — in one graph. | `examples/E3/example.lara` |
| R1 `undeclared-leaf` | **VReject R1** — support term references leaf `e_missing` not in Γ (root leaf, not a premise); **not** a `gap`, exit 1. | `examples/R1/example.lara` |
| R2 `strict-contrary` | **VReject R12** — policy `strict-bad-v1` declares a strict rule whose conclusion `derived(X)` sits in a `contrary` pair (§8.1 Path B); `checkUnit` stage 2 rejects the unit. | `examples/R2/example.lara` + `examples/R2/strict-bad-v1.policy.lara` |
| R3 `bad-attack-target` | **VReject R10** — `rebut a1 d_leaf` targets a **leaf-rooted** argument (wrong occurrence kind for a rebut, which must hit a defeasible rule occurrence). R10 (wrong occurrence), not R11: the conclusions *are* contrary. | `examples/R3/example.lara` |

Reminder: E3 exhibits three non-gap statuses in one graph (defeated + contested + justified from its
three roots), and gap is carried by E2 — together the four statuses are all witnessed. The M4a suite
is **defeasible-only** (the frozen grammar has no support-term assurance syntax): R2's spec class is
**R12** (a strict *rule* declared in the policy with its conclusion in a `contrary` pair — a policy
well-formedness reject; the *artifact* stays minimal/defeasible), and R3's is **R10** (a `rebut`
targeting a leaf occurrence). The strict-rule-unattackable / R7-assurance teachings are deferred to
`TODOS.md`, not authored here.

## 4. Open items — flagged, not resolved here

A0 records these; it does not resolve them. Resolution owners are noted.

1. **Rejection-class naming collision (namespace clash).** `docs/worked-examples-plan.md` §1 uses
   `R1/R2/R3` as **example identifiers** for the three rejected examples. These tokens collide with the
   **spec §10.1 rejection-class numbers** `R1–R14`, which are a *different namespace*. The example labels
   do **not** line up one-to-one with the spec classes:
   - Example **R1** `undeclared-leaf` → spec class **R1** (reference, undeclared id). *Note:* §1 phrases
     it "leaf not in `Γ` (admission `reject`/absent)", which conflates two spec classes — **R1** (leaf
     *absent/undeclared*, inside the executable core) vs **R8** (admission `reject`, *outside* the
     executable core, `src/Lara/AST.hs` line 483). A1 keeps these distinct; the intended R1 example is
     the undeclared/absent case (R1), not admission-reject (R8).
   - Example **R2** `strict-contrary-violation` → spec class **R12** (policy-wf, §8.1) — **not** spec
     class R2 (signature). `worked-examples-plan.md` §3 itself cites the §8.1 Path-B check, i.e. R12.
   - Example **R3** `bad-attack-target` (strict rule not rebuttable) → spec class **R10/R11**
     (attack-position / attack-relation: "target rule strict", spec §10.1 line 1229–1230, and the
     mutation-list mapping "bad attack targets → R10/R11", line 1239) — **not** spec class R7
     (assurance).

2. **A2's spec-class citation "R1/R12/R7" looks partly wrong. — RESOLVED (A1c-2, 2026-07-28).** The
   M4a plan's Task A2 says the suite asserts "three rejection classes (**R1/R12/R7** per §1)". R1 ✓ and
   R12 ✓ match; **R7 was a mis-citation** (spec §10.1 R7 is the *assurance* class). The authored R3
   example (`examples/R3/example.lara`) is a `rebut` targeting a **leaf occurrence**, which
   `checkUnit` rejects **R10** (wrong occurrence kind), verified by `test/WorkedExamplesSpec.hs`. The
   frozen R-series mapping is therefore **R1 / R12 / R10** (see §3). The strict-rule-not-rebuttable
   teaching (which would be R11 `StrictTarget`) is deferred to `TODOS.md` — the defeasible-only M4a
   suite does not author a strict support term.

3. **E2's gap mechanism is re-worded between §3 and A2.** `worked-examples-plan.md` §1/§3 describe E2's
   gap as arising from an **open mandatory CQ** (`open external_validity as o1`). The M4a plan
   (decision #8 / Task A2) re-words this: a declared argument with an open mandatory CQ is an
   `IncompleteArgument` **rejection** (`Check.hs:179`), *not* a gap; the intended `gap` must instead come
   from a claim with **empty complete support** (`statusC = Gap iff null claimSupport`,
   `Grounded.hs:127`), keeping `runUnit` unchanged. The "incomplete attempt" teaching moves to a
   Haskell-only `Lara.Reporting` `incompleteAlternative` golden. **The intended status stays `gap`**;
   only the mechanism (and the §3 wording) changes. **Owner: A2** (re-word `worked-examples-plan.md` §1
   E2 to match). A0 only records it.

4. **Surface constructs A/B use that the AST cannot yet represent.** A/B contain attack-supporting
   arguments without a declared claim (`arg d1 : challenges(external_validity(a1)) by leaf(e4)`), an
   undeclared conclusion (`supports(c1_neg)` with `c1_neg` undeclared), dotted position suffixes
   (`a1.rule`, `a1.external_validity.leaf`), implicit premise selection, and `#`-in-source-ref lexing.
   These are the A0.5 grammar-freeze items (plan Task A0.5) and gate A1. **Owner: A0.5.** A0 does not
   edit `examples/*.lara`; A0.5 reconciles them.

## A2 closeout — `expected.json` goldens + coverage matrix (2026-07-28)

Task A2's `expected.json` half is delivered, **discharging `docs/worked-examples-plan.md` §4**:
every example dir (`A`, `B`, `E1`–`E3`, `R1`–`R3`) now ships `example.core.sexp` **and**
`expected.json`. The JSON is rendered by a hand-rolled emitter (`src/Lara/ExpectedJson.hs`, no new
dependency) from the elaborated `Unit`; schema `{ "verdict-class", "located-diagnostic" }`. The
located diagnostic is **Haskell-only** (the wire verdict / differential carries only the class): for a
reject it names the offending argument / attack / policy constituent and the failing `checkUnit` stage
(`Lara.Diagnostics.locate`); for an accept it carries the per-claim statuses plus the gap /
incomplete-alternative reporting (`Lara.Reporting.claimReports`). `scripts/gen-worked-examples.hs`
regenerates both goldens; `test/WorkedExamplesSpec.hs` adds an `expected.json` freshness assertion
(sibling of the `.core.sexp` one) and a **measured** coverage-matrix test — read off the elaborated
units and their verdicts, not asserted in prose — that every status (justified/gap/contested/defeated),
every attack kind (rebut/undercut/undermine), and R1/R12/R10 are witnessed. The
original A2 suite was **defeasible-only** (`nd@1` inert); post-M4a example
`examples/S1/` now exercises the strict-certificate frontend path end to end.

## Correction log

- **2026-07-28 (A1b) — Example A corrected to reach its frozen golden.** Wiring the
  compiler (parse → elaborate → `runUnit`) revealed that `A/example.lara`, as
  authored, was **rejected R6** (and would then have hit `missing-conflict`), so it never
  actually reached the §1 golden. Two authoring bugs: (1) `a1` discharged the mandatory CQ
  `external_validity` (policy pattern `generalizes(M,Q,D)`) with a `measured(…)` leaf; (2)
  `d3` (the `exp_9` instance) discharged its CQs with `exp_3`'s `randomized`/`powered`
  leaves. Per the plan's Lean-is-oracle discipline (the golden is never re-annotated), the
  **example** was corrected to match the (unchanged) golden — user-approved 2026-07-28: `e6`
  is now `generalizes(M,accuracy,D)`, `e5` is `not_generalizes(M,accuracy,D)`, the shared
  policy's `measured/instrument_artifact` contrary became `generalizes/not_generalizes`, `d3`
  gained its own `exp_9` leaves `e8`/`e9`, and a reverse `rebut a1 d3` was added for attack
  completeness (both contrary orientations are declared). The §1 golden values are
  **unchanged** (`a1→out, d1/d2/d3→in, c1→Defeated`) and are now checker-verified end-to-end
  (`test/ElaborateSpec.hs`). The undermine narrative shifted from "measurement is an
  instrument artifact" to "the result does not generalize" (forced by the CQ pattern).

## Exit checklist (A0)

- [x] `docs/m4a-checklist.md` created, mirroring `m1-freeze-checklist.md` / `m3-closeout-notes.md`.
- [x] M4a scope lock stated (in scope / out of scope → #32 / M5 / TODOS).
- [x] A and B expected verdicts **frozen** from their inline oracles — four-state claim status +
      per-argument grounded label (§1).
- [x] Coverage matrix confirmed against `worked-examples-plan.md` §1, with A/B appended and every
      example classified authored-vs-to-author (§2).
- [x] E1–E3 / R1–R3 **intended** verdicts recorded as provisional design intent, to be oracle-frozen in
      A1 (§3).
- [x] Rejection-class naming/mapping discrepancies and the E2 wording re-scope **flagged, not resolved**;
      owners noted (§4).
- [ ] Reviewed and committed **before** frontend code lands (A0 gate; orchestrator commits after review).

_Frozen 2026-07-27 as Task A0 of `plans/2026-07-27-m4a-compiler-worked-examples.md`. Next: A0.5 grammar
freeze (gates A1), then A1 (E1 vertical slice first)._
