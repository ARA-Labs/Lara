# Decision: what the Lean development mechanizes, and when a checker-boundary flag owes an `AxCheck.lean` entry

_Records the settled scope rule for the Lean development, fixed when issue #124
split the attack-completeness scan out of the typed-attack bundle and added a
third `Lara.Check.CheckConfig` flag. The implementation plan that produced the
split has since been executed and deleted, per the `plans/` rule; this record
carries the durable half, and the cycle it fed is `m5-freeze-v5`
(`docs/m5-freeze-checklist.md`). Companion to
`docs/mechanization-plan.md` (what is mechanized) and the Haddock on
`Lara.Check.CheckConfig` (the same rule, stated for readers of the code)._

## The rule

**The Lean development mechanizes the frozen semantics — `fullConfig` alone.**

`Lara.Check.CheckConfig` is an ablation carrier that exists only at the checker
boundary, for the M5 baselines. It never reaches the support kernel, is never
carried on the wire, and has no Lean counterpart by design.

> A new checker-boundary flag owes an `AxCheck.lean` entry **only if it changes
> what `fullConfig` accepts** — which, by construction, it must not.

Each flag only ever *removes* a rejection arm, so `accept(fullConfig) ⊆
accept(cfg)` for every `cfg`. Adding a flag that satisfies that inclusion moves
nothing the Lean development is responsible for.

## Why this is sound — the stronger form of the argument

There are two arguments available, and only the second is worth relying on.

**The weak one: "the type has no counterpart."** `lean/` contains zero
occurrences of `CheckConfig`, `ablation`, `noTypedConfig`, `noCQConfig`,
`ccConflictScan`, or `ccTypedAttacks` (whole tree, excluding `.lake/`). True,
and easy to check, but it only says the flag is absent — it does not answer
"what if the split changed `fullConfig`?".

**The strong one: `fullConfig`'s behaviour is pinned independently.** The
conflict scan — the stage #124 made separately ablatable — is itself fully
mechanized *and* axiom-checked. Six `AxCheck.lean` entries cover it:

| `AxCheck.lean` | theorem |
| --- | --- |
| `:811` | `Lara.Compile.conflictAttackableB_iff` |
| `:813` | `Lara.Compile.complete_conflict_edge` |
| `:814` | `Lara.Check.missingConflict_no_rejectClass` |
| `:817` | `Lara.Check.conflictCache_terms` |
| `:819` | `Lara.Check.firstMissingConflict_none_iff` |
| `:852` | `Lara.Examples.check_unit_missing_conflict_wrapped` |

So the semantics the flag switches off is proved, `sorry`-free and within the
standard axiom trio, *regardless of what the Haskell-side switch does*. A split
that silently changed `fullConfig` would break these proofs or the differential
that anchors them — it could not pass quietly. That is the reason no entry is
owed, and it survives the "but what if" question the weak argument does not.

## Where the inclusion is enforced instead

In Haskell, by `test/AblationSpec.hs`'s `prop_monotonicity`, over every manifest
input and over **all 8 inhabitants** of `CheckConfig` (its `allConfigs`) — not
merely the three named baselines in `Lara.Measure.ablationConfigs`, which are
the reporting vocabulary for `ablation.{json,tsv}`.

The distinction matters: enumerating only the named list left five states
unenforced, including `ccTypedAttacks = False, ccConflictScan = True`, which
first became reachable when #124 split the two. Three flags is eight states and
needs no new fixtures, so the property quantifies over the whole record and the
enforcement matches the claim exactly.

This is deliberately **not** a Lean obligation, for the reason above.

## Rejected alternative

*Mechanize `CheckConfig` in Lean and prove the inclusion there.* Rejected: it
would put the ablation apparatus — an artifact of how M5 measures the system —
inside the development whose job is to pin the frozen semantics. The inclusion
is a property of a measurement harness, not of the calculus; proving it in Lean
would freeze a carrier that is expected to churn as baselines are added and
retired, and would owe `AxCheck.lean` churn on every such change for no gain in
what is actually guaranteed about `fullConfig`.
