# Decision: what `location_match` measures once mutants carry more than one defect

_Resolves the metric question of #123 (discriminating localization benchmark),
Task 3 of the batch frozen as `m5-freeze-v5` (#156). The decision was required
in `docs/` before any mutant was generated: it is a measurement contract, not an
implementation detail. Companion
to `src/Lara/Diagnostics.hs` (the shared location vocabulary) and
`docs/m5-freeze-checklist.md` (the frozen headline this changes)._

_Status: settled, as part of the `m5-freeze-v5` batch._ Background for cold
readers: the mutation benchmark seeds known defects (*mutants*) into valid
corpus units, recording each seeded site in a manifest; `location_match` is
the benchmark column scoring whether the checker's rejection points at a
seeded site. This record decides what that column means once a mutant can
carry more than one defect.

## The problem being fixed

`location_match` today is `==` on `Constituent`: the checker's reported
constituent against the single seeded `mutantSite` (manifest column 8,
`expected-location`). Every mutant in the suite is single-defect, so the
rejection can only fire at the mutated constituent, and the frozen snapshot
reports 399/399. The number verifies the harness wiring; it cannot fall below
100% for a reason that would interest a reader. The eng review (D10) flagged
exactly this, and issue #123 exists to make the column a signal.

## What the checker can and cannot be benchmarked on

Two facts bound the design space, and the metric must not pretend otherwise.

**The checker reports exactly one location.** `checkUnitWith` is fail-fast:
`Either UnitError CheckedUnit`, one `UnitError`, one located constituent. There
is no "report all defects" mode, and adding one is a semantics change to the
frozen acceptance boundary, out of scope here.

**The reported location is deterministic and spec-fixed.** The seven-stage
order is public contract (spec §10, mirrored in `lean/Lara/Check/Unit.lean`),
and within a stage, constituents are visited in declaration-index order. Given
any input — multi-defect or not — the constituent a spec-conformant checker
reports is *computable at generation time* without running the checker.

Consequently there is no "search quality" to benchmark: localization for this
checker is not a ranking problem. The honest claims available are

1. **faithfulness** — the reported constituent is a genuinely defective one,
   i.e. a seeded site or a spec-predicted manifestation site, never an
   artifact of cascading elsewhere; and
2. **ordering conformance** — the reported constituent is the one the spec's
   stage order designates first.

Both are falsifiable by implementation error (a traversal that deviates from
spec order, a cascade the diagnostics mislocate) and by modeling error (our
generation-time prediction of the manifestation site is wrong). Neither is a
tautology once the corpus contains inputs where prediction is non-trivial.
Nothing stronger is honestly claimable, and the write-up must say so — see
"The caveat" below.

## Decision

**Ground truth becomes an ordered, non-empty list of admissible constituents,
predicted at generation time from the spec's stage order. Two metrics are
derived from it:**

- **`location_match` (headline, keeps its name): membership.** The reported
  constituent is an element of the list. This is the faithfulness claim: the
  checker pointed at a seeded/predicted defect site, not somewhere else.
- **`location_primary` (new column): equality with the list head.** The head
  is the constituent the spec's stage order designates first. This makes
  diagnostic ordering *measured*, in keeping with the existing harness stance
  ("measured, never gated" — `src/Lara/Measure.hs`); class match remains the
  only gate.

**Ground truth means the predicted manifestation site, not the edit site.**
For every existing operator the two coincide. For an off-site operator they do
not, by construction: an edit to the policy whose manifestation is an
argument's support failure has ground truth `[arg:i]`, not `[policy]`. Writing
the edit site there would guarantee a miss and measure nothing. The operator's
site enumerator owns the prediction, per operator, the same way it owns the
expected class today.

**Existing rows keep their meaning.** A single-defect row's list is the
singleton of its current `mutantSite`. Membership and primary-equality both
degenerate to today's `==`, so the ~400 existing localized rows are the same
measurements under the new definition — no silent reinterpretation.

## Alternatives rejected

- **Keep single-site equality and add multi-defect mutants anyway.** Ill-posed:
  with two seeded sites there is no single right answer for an equality check,
  and picking one silently smuggles the ordering claim into the headline.
- **Ground truth = "whatever the checker reports."** Circular; the metric
  becomes 100% by definition, which is worse than today's
  100%-by-construction.
- **Ordering-only (primary-equality as the headline).** Overstates what the
  paper needs. The paper's location claim is that diagnostics point at real
  defects; ordering conformance is a secondary, differential-style property.
  It is worth a column, not the headline.
- **A report-all-defects checker mode.** Changes the frozen acceptance
  boundary and its Lean mirror for the benefit of a metric. Rejected outright.

## What makes the metric discriminating, stated precisely

Membership alone does **not** become discriminating just by composing two
existing single-site defects: a fail-fast checker reports the stage-first one,
which is in the set whenever the prediction is right. The discrimination
budget comes from, in order of value:

1. **Off-site families** — the edit site and the manifestation site differ, so
   ground truth is a genuine prediction that a mislocating implementation (or a
   wrong model of the cascade) fails. This is the strongest gate the suite can
   state; it is not a number that moves — see the note below.
2. **Multi-defect families crossing stage boundaries** — e.g. a support defect
   in `arg:i` composed with an attack defect at `attack:j`. `location_match`
   stays membership; `location_primary` now tests that stage order, not
   accident, chose the report.
3. **Multi-defect families within one stage** — two defective arguments test
   the declaration-index order the same way.

**These families do not make the reported rate move, and saying otherwise
would be wrong** (#167 review). Every published site — head and tail, on every
base the answer key is generated from — is gated against the checker before it
can reach `MANIFEST.tsv`: `prop_siteMatchesChecker` pins every list's head to
the constituent `runCheckLocated` actually reports, and
`prop_localizationSites` pins the tails (`retract-rule`'s manifestation set
re-derived from the mutant; each composite's tail re-derived by reverting the
head defect in the mutant and re-running the checker). A row whose ground
truth the checker disagreed with fails CI at generation time, so it never
becomes a measured row. Both `location_match` and `location_primary` are
therefore 100% on the committed suite **by construction**, exactly as the
single-defect families are — just under a strictly stronger construction.

What these families buy is the strength of that gate, not the value of the
rate: their ground truth is a genuine prediction that a mislocating checker
fails, which the echo-the-edit-site families could not state at all. Prose
that quotes 399/399 as evidence of discriminating localization is wrong. Cite
the gate — what the answer key predicts and what would fail if the prediction
were wrong — not the number.

## Consequences for the implementation (Task 3 scope)

- `mutantSite :: Maybe Constituent` widens to `[Constituent]` (empty = no
  seeded site, today's `Nothing`); likewise `imExpectedLocation` in
  `src/Lara/Measure.hs`. `detLocationMatch` becomes membership;
  `detLocationPrimary` is added beside it.
  **Superseded by #169:** both fields are now `Maybe SeededSites`, a newtype
  over `NonEmpty Constituent`. The widening above made `[]` mean "no seeded
  site" — the same state as the old `Nothing` — which also made an enumerator
  that accidentally published `[]` indistinguishable from one that seeds
  nothing, silently dropping the row from the `location-accuracy-rate`
  denominator instead of counting it as a miss. The wrapper restores the
  distinction in the type: `Nothing` seeds nothing, and a `SeededSites` cannot
  be empty. The rendered column is unchanged.
- **Manifest column 8 spelling:** elements joined by `,` in ground-truth order
  (`arg:0,attack:2`); `-` still means no seeded site. `,` appears in no
  spelling `constituentText` produces today and is TSV-safe; single-element
  rows are byte-identical to today's column, so the existing manifest rows do
  not change spelling. One guard: `GroupId` is free-form, so the `group:`
  spelling could in principle contain a comma — the list codec must reject
  group ids containing `,` (every id in use is comma-free: `g`, `mut_g`, …),
  keeping the round-trip unambiguous.
- `report.tsv` gains the `location_primary` column. The pinned
  `cut -f1-14 report.tsv` projection hash moves at the refreeze regardless; a
  new hash is v5's deliverable (#156). Place the new column after
  `location_match` and update the pinned `cut` range in the same change.
- New families are new operators, appended per the enum-additivity rules in
  the batch plan: no existing enumerator output is reordered, no operator
  renamed (`Lara.Mutate.Seed` streams are string-keyed; reordering moves
  bytes). Existing mutant files stay byte-identical.
- Cost: adds mutant families, hence regenerates the suite — this is precisely
  the change #156 budgets. Nothing here forces an extra cycle.

## The caveat, carried until the paper states it

The batch plan records that the ≈100%-by-construction caveat currently lives
only in issue #123's body. This document is now its canonical home, and the
Task-3 change must also place one sentence next to the headline number in
`docs/m5-freeze-checklist.md` so the number is not quotable without it:

> `location_match` is ≈100% by construction and stays that way — every
> published site is checker-gated before it reaches `MANIFEST.tsv`, so a
> mislocating ground truth fails CI instead of lowering the rate. The
> off-site and multi-defect rows add a stronger gate, not a number that
> moves; the ordering claim is `location_primary`, reported separately.

The results prose lives in the paper repository, so this repo can only carry
the obligation, not discharge it. That half is tracked in **#168** — #60, the
M7 paper-package tracker it was previously parked on, closed 2026-08-24, which
left the obligation recorded only in prose here (#167 review).
