# D2 — mechanical reviewer

*Demo for the M7 paper package (#60 T1); sub-issue #63 of the demos tracker (#61).*

## What it demonstrates

The claim-support checker already computes a four-state status for every claim in
the frozen 60-unit corpus (`justified` / `gap` / `defeated` / `contested`, spec
§8). This demo makes the paper's point that **those statuses *are* review
content**: a `gap` verdict with its unmet obligation reads as the reviewer
complaint it corresponds to, and a `defeated` verdict names the attacking
argument that sinks the claim.

The renderer is a **deterministic, untrusted presentation layer** — no LLM and
no new trusted code. It takes the checker's own per-claim verdict and located
diagnostic (the accept-path detail `Lara.ExpectedJson` pins) and fills a **fixed
phrasing table** keyed on the diagnostic shape. Re-running it reproduces the
committed bytes; a freshness test enforces that.

- Renderer: `scripts/render-reviews.hs` (IO) over `Lara.MechReview` (pure) +
  `Lara.MechReview.Load` (shared decode/parse).
- Golden: `measurements/frozen/mechanical-reviews.md` — one review comment per
  non-`justified` claim over the corpus, in manifest order.
- Freshness test: `test/MechReviewSpec.hs` (re-render must equal the committed
  golden byte-for-byte; plus the demo's shape invariants).

Over the frozen corpus this yields **51 review comments — 48 `gap`, 3
`defeated`** (the 9 `justified` claims raise none, and the corpus contains no
`contested` claim).

## The phrasing table (keyed on diagnostic shape)

| Status | What the checker gives | Rendered review |
| --- | --- | --- |
| `gap` (incomplete alternative) | open mandatory obligations of an incomplete candidate (`Lara.Reporting.claimReports`) | names the unmet obligation(s): "the mandatory obligation `q` has no discharging leaf …" |
| `gap` (no candidate) | empty complete-support set | "no argument assembles the unit's evidence into a checked support … status **gap**." |
| `defeated` | the `out`-labelled support argument + its `in` attacker (kind + `challenges(…)` target) | names the attacking argument and its kind |
| `contested` | the `undec` cycle | names the unresolved conflict |

The frozen corpus's `gap` claims all take the *no-candidate* branch (the units
state the claim and its evidence but declare no assembling argument, because the
mandatory `variance_reported` CQ has no honest leaf — see
`corpus-units/adaptive-pruning/C03/unit.lara`). The obligation-naming branch is
implemented and fires whenever a unit ships an incomplete candidate alternative
(`holes > 0`); no frozen unit exercises it.

## Demo figure — a `defeated` review

The richest shape is `defeated`, which names the attacking argument exactly as
issue #63 specifies. Reproduced verbatim from the golden
(`measurements/frozen/mechanical-reviews.md`), unit `fre/C04`:

> ## fre.C04 — defeated
>
> Claim `c04`: `contributes(reward_diversity, fre_all, antmaze_total_score)`
>
> *Stated:* On AntMaze, performance scales smoothly with reward diversity and
> FRE-all dominates all reward-subset ablations — total score FRE-all 47.3 +- 7
> is the argmax over the 7 variants
>
> > The claim's only support `a1` is labelled `out`: the undercut `d1`
> > (challenging the `variance_reported` critical question of `a1`) is unattacked
> > and defeats `a1` — status **defeated**.

Every token in that review comment is derived from the checker's output: `a1`
and its `out` label from the grounded labelling, `d1` and `undercut` from the
declared typed attack, and `variance_reported` from `d1`'s `challenges(…)`
target. The paper's own Table 4 (`+- 7` overlapping seed intervals) is what
undercuts the strict-dominance ordering — the review states precisely that,
without any language model.

## Reproduce

```
cabal build
cabal exec -- runghc scripts/render-reviews.hs   # writes the golden; deterministic
cabal test                                        # includes the freshness test
```

## Scope

This demo shows that LARA verdicts *are expressible as* review comments. Whether
they *predict* human reviewer complaints (a correlation study against real
OpenReview reviews) is an axis-(d) study deferred to the ACL/EMNLP follow-up
(out of scope per #63).
