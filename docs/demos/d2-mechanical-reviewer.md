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

## Read the verdicts as comments on papers

These examples show the source prose a reviewer might read, the bounded comment
the LARA renderer can produce, and—where useful—the fuller methodological
interpretation a human reviewer could make from the paper. The renderer is not
credited with that last step. The paper excerpts are **illustrative
reconstructions**, not quotations. The first two are grounded in the frozen
corpus; the `contested` example points to the checked cross-paper examples
because that status does not occur in the 60-unit corpus.

### Gap — the paper has not supplied the required evidence

> **Paper excerpt.** Removing the kurtosis-based salience term lowers the
> OpenLLM average from 50.0 to 38.1 in our ablation, demonstrating that the term
> is critical to APT's performance.

> **Mechanical review.** No argument assembles the unit's evidence into a
> checked support for this claim; its complete-support set is empty, so at the
> `corpus-v1` evidential bar the claim is unsupported — status **gap**.

This is `adaptive-pruning.C04`. In the frozen unit the missing mandatory
obligation prevents declaration of a complete argument, so the committed
renderer takes its `gap (no candidate)` branch. If an incomplete candidate were
retained explicitly, the renderer would instead take `gap (incomplete
alternative)` and name `variance_reported` directly. Both phrasings mean the
same thing to an author: the paper has not yet supplied evidence required by the
policy; LARA is not claiming that contrary evidence has disproved the result.
Reading the cited ablation gives the ordinary reviewer request—“report repeated
runs and error bars”—but the current no-candidate diagnostic does not generate
that extra sentence.

### Defeated — the paper's own numbers undercut its conclusion

> **Paper excerpt.** FRE-all obtains the highest AntMaze total score among all
> seven reward-subset variants (47.3 ± 7 versus 46.9 ± 7 for the nearest
> alternative), showing that the full reward-diversity design dominates every
> ablation.

> **Mechanical review.** The claim's only support `a1` is labelled `out`: the
> undercut `d1` (challenging the `variance_reported` critical question of `a1`)
> is unattacked and defeats `a1` — status **defeated**.

This is `fre.C04`. Unlike a `gap`, all required evidence is present and a
complete support argument exists. The problem is that an unattacked
`within_noise` argument undercuts that inference, so the support is labelled
`out` and the claim is `defeated`. In ordinary review prose, the paper context
makes the criticism concrete: the claimed 0.4-point advantage lies inside
overlapping ±7 seed intervals, so those results do not support the strict
“dominates every ablation” conclusion. That explanation comes from reading the
cited table; the fixed renderer itself stays with the checked attack structure
quoted above. There is also a modeling boundary here: the formal conclusion
`contributes(reward_diversity, fre_all, antmaze_total_score)` is broader than
the paper's strict-dominance sentence. The demo audits and checks the chosen
binding; it does not mechanically prove that the broader predicate preserves
every nuance of that sentence.

### Contested — two checked papers remain in unresolved conflict

> **Paper A.** Under the shared RoBERTa/MNLI protocol at 60% sparsity, APT
> outperforms CoFi.
>
> **Paper B.** Under that same protocol, our replication finds no APT advantage
> over CoFi.

> **Natural-language reading.** The two complete arguments reach contrary conclusions
> about the same system, baseline, metric, and setting. Neither has an accepted
> defeater or preference over the other, so the conflict is unresolved — both
> claims are `contested`.

This branch is exercised by `examples/B/` and the P1 pair in
`examples/agreement-map/`, although not by the frozen corpus used to generate
the 51-comment golden. It is not a softer spelling of `defeated`: neither side
is labelled `out`. Mutual rebuttal is one concrete way to obtain `contested`,
not its definition: an `undec` label can also propagate through a larger attack
graph without the two queried supports attacking each other directly.

## The phrasing table (keyed on diagnostic shape)

| Status | What the checker gives | Rendered review |
| --- | --- | --- |
| `gap` (incomplete alternative) | open mandatory obligations of an incomplete candidate (`Lara.Reporting.claimReports`) | names the unmet obligation(s): "the mandatory obligation `q` has no discharging leaf …" |
| `gap` (no candidate) | empty complete-support set | "no argument assembles the unit's evidence into a checked support … status **gap**." |
| `defeated` | the `out`-labelled support argument + its `in` attacker (kind + `challenges(…)` target) | names the attacking argument and its kind |
| `contested` | an `undec`-labelled support | uses a generic unresolved-conflict template; it does not report conflict provenance |

The current fixed `contestedBody` template says that arguments “attack each
other.” That is accurate for the checked B/P1 example above but narrower than
the status definition: `undec` can be inherited from a larger graph. Because no
frozen corpus unit exercises this branch, the committed golden does not expose
the limitation. A provenance-aware contested review would require additional
reporting; the present renderer should be read only as a generic gloss on the
`undec` label.

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

Every claim-specific field in that review comment is derived from the checker's
output: `a1` and its `out` label from the grounded labelling, `d1` and
`undercut` from the declared typed attack, and `variance_reported` from `d1`'s
`challenges(…)` target. Fixed connective prose comes from the renderer's
template. The paper's own Table 4 (`+- 7` overlapping seed intervals) motivates
the declared undercut of the strict-dominance reading; interpreting those
numbers is part of the hand-authored lowering, not something the renderer
infers with a language model.

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
