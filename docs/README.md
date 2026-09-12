# docs/ — what lives here and how to find it

`docs/` records *decisions and contracts*; open work is tracked as GitHub
issues, never here. Most files are one of four kinds: a **spec/contract**
(normative, frozen, versioned), a **decision record** (why something is the
way it is, with its status and date in an italic header), a **milestone
record** (a closed tracker preserved as history), or a **theory note** (the
durable record of one mechanized result). New to the project? Read the
top-level [`../README.md`](../README.md) first, then [spec §0](spec.md) for
the vocabulary and reading paths.

## Entry points

| Doc | What it is |
| --- | --- |
| [`spec.md`](spec.md) | The frozen v0.1 language specification; §0 is the reader's guide |
| [`lara-surface-grammar.md`](lara-surface-grammar.md) | The concrete `.lara` syntax contract, with per-version appendices |
| [`foundations.md`](foundations.md) | The four lines of prior work LARA builds on |
| [`novelty-and-related-work.md`](novelty-and-related-work.md) | The novelty claim and the delta table against prior art |
| [`demos/`](demos/) | Prose-first walkthroughs of checked artifacts: a rebuttal exchange (D1), mechanical review comments (D2), a cross-paper agreement map (D3) |

## Decision records

Design decisions with status headers, roughly in dependency order:
[`claim-support-calculus-decision.md`](claim-support-calculus-decision.md)
(one support-term language),
[`strict-backend-decision.md`](strict-backend-decision.md) (the opaque
strict-certificate seam),
[`gap-resolution.md`](gap-resolution.md) (making `(Inst)` checkable),
[`substrate-decision.md`](substrate-decision.md) (Haskell core / Python
front-end),
[`policy-admission-calculus-decision.md`](policy-admission-calculus-decision.md)
(the source-boundary leaf filter),
[`ord1-corpus-extension-decision.md`](ord1-corpus-extension-decision.md) and
[`insp1-code-inspection-decision.md`](insp1-code-inspection-decision.md)
(what the `ord@1` / `insp@1` backends certify),
[`evidence-admission-decision.md`](evidence-admission-decision.md) (gated
byte-level evidence layer),
[`registration-receipt-contract.md`](registration-receipt-contract.md)
(documentation-only receipt seam),
[`naturalness-boundary.md`](naturalness-boundary.md) (where natural language
is allowed),
[`mechanization-scope-decision.md`](mechanization-scope-decision.md) and
[`examples-corpus-decision.md`](examples-corpus-decision.md) (what the Lean
side does and does not carry),
[`mutate-module-ownership-decision.md`](mutate-module-ownership-decision.md)
and [`localization-metric-decision.md`](localization-metric-decision.md)
(mutation-benchmark contracts),
[`ara-session-record-decision.md`](ara-session-record-decision.md) (the
session-file schema and what `session_index.yaml` rows project from it),
[`venue-decision.md`](venue-decision.md) (publication strategy).

## Plans, references, and operational notes

[`engineering-plan.md`](engineering-plan.md) (build order and module graph; a
living contributor log), [`mechanization-plan.md`](mechanization-plan.md)
(the Lean track; status table in [`../lean/README.md`](../lean/README.md)),
[`performance.md`](performance.md) (the checker bench),
[`rejection-surface.md`](rejection-surface.md) (what the checker refuses,
with runnable anchors), [`corpus-map.md`](corpus-map.md) (the M0 ARA→LARA
lowering map), [`paper-lean-name-map.md`](paper-lean-name-map.md) (paper
display ↔ Lean declaration), [`prior-art-lessons.md`](prior-art-lessons.md)
and [`comparison-rit-lara.md`](comparison-rit-lara.md) (firsthand reads of
neighboring systems), [`study-plan.md`](study-plan.md) (dated onboarding
reading list), [`worked-examples-plan.md`](worked-examples-plan.md)
(historical; the live catalogue is
[`../examples/README.md`](../examples/README.md)).

## Milestone records (closed engineering spine)

[`m1-freeze-checklist.md`](m1-freeze-checklist.md),
[`m3-closeout-notes.md`](m3-closeout-notes.md),
[`m4a-checklist.md`](m4a-checklist.md), and
[`m5-freeze-checklist.md`](m5-freeze-checklist.md) are the preserved trackers
of the closed engineering milestones M1–M5 (M5's current evaluation-freeze
snapshot lives at the top of its file and is still updated per freeze cycle).

## Theory notes — two series, one prefix

The `theory-*.md` files record mechanized results, and the prefix is
load-bearing: **`theory-m0`…`theory-m5` are the POPL theory spine (tracker
#180) and are unrelated to the engineering milestones of the same numbers
above.**

- **Theory spine (tracker #180)**, in order:
  [`theory-m0-compilation-invariants.md`](theory-m0-compilation-invariants.md)
  (the carrier everything quantifies over),
  [`theory-m1-compilation-image.md`](theory-m1-compilation-image.md),
  [`theory-m2a-observation.md`](theory-m2a-observation.md),
  [`theory-m2b-complexity.md`](theory-m2b-complexity.md) (gate history in
  [`theory-m2b-complexity-spike.md`](theory-m2b-complexity-spike.md), which
  is superseded reading),
  [`theory-m3-source-updates.md`](theory-m3-source-updates.md),
  [`theory-m4-context-calculus-decision.md`](theory-m4-context-calculus-decision.md)
  and [`theory-m4-contextual-adequacy.md`](theory-m4-contextual-adequacy.md)
  with follow-ons
  [`theory-m4-generic-observation.md`](theory-m4-generic-observation.md),
  [`theory-m4-relational-parametricity.md`](theory-m4-relational-parametricity.md),
  [`theory-m4-g0-interface-spike.md`](theory-m4-g0-interface-spike.md)
  (Part B gate: re-descoped),
  and [`theory-term-level-holes.md`](theory-term-level-holes.md),
  [`theory-m5-surface-calculus.md`](theory-m5-surface-calculus.md), plus the
  side milestone
  [`theory-b0-backend-compositionality.md`](theory-b0-backend-compositionality.md).
- **Possible-world spike (tracker #189)**: start from
  [`theory-pw-closeout.md`](theory-pw-closeout.md), the subseries index; the
  contracts are [`theory-pw0-outer-model.md`](theory-pw0-outer-model.md),
  [`theory-pw-t6-structural-transport.md`](theory-pw-t6-structural-transport.md),
  [`theory-pw-t8-status-preservation.md`](theory-pw-t8-status-preservation.md),
  and
  [`theory-pw-t9-path-composition.md`](theory-pw-t9-path-composition.md).

Some theory notes cite design sources in the separate `lara-paper`
repository; those links require access to that repo.

## Subdirectories

- [`demos/`](demos/) — the three prose-first demo write-ups (see entry
  points above).
- `references/` — long-form reading notes on external sources feeding the
  related-work and annotation vocabulary.
- `slides/` — presentation material: a project keynote and a teaching deck
  on argumentation background.
- `superpowers/` — dated implementation plans and specs produced by skill
  workflows for individual features.
