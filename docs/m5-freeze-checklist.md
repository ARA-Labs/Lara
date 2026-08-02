# M5 freeze checklist — evaluation corpus (deterministic scope)

_Operational record for milestone **M5 — evaluation corpus** task **T5 (freeze
protocol)** (`plans/research-proposal.md` §7, tracker #48). Companion to the M1
analogue (`docs/m1-freeze-checklist.md`) and the T6 ablation plan
(`plans/2026-08-02-m5-t6-ablation-baselines.md`). This file freezes the fixture
set, corpus sample, and generator seeds before the final measurement runs; the
paper's axis-(c) tables are generated only from post-freeze runs against the
inputs pinned here._

## What T5 is (and is not)

**T5 definition of done** (tracker #48): commit the fixture set, corpus sample,
and generator seeds before final measurement runs — the deterministic analogue
of the proposal's blinded held-out freeze. Final numbers come only from
post-freeze runs. T5 does not add checker or corpus content; it locks what T1–T4
and T6 produced and records the reproducibility anchors.

**Scope (matches the PLDI/POPL paper).** The frozen corpus covers the
LLM-independent axes only: axis (a) mutation/differential testing and the
checker side of axis (c). The human-authored natural-defect ablation (#52,
`post-pldi`) and every LLM-producer / annotator axis (#30, axes b/d) are
**deferred to the ACL/EMNLP follow-up** and are deliberately **not** in this
freeze.

## Frozen inputs

State legend: **Frozen** = pinned for the measurement runs, do not regenerate;
the git tree object SHA is itself the content hash of the tree.

| # | Frozen input | Path | Count | Content anchor (git tree SHA) |
| --- | --- | --- | --- | --- |
| 1 | Seeded mutation suite (verdict + specified-status anchors) | `fixtures/mutants/` | 358 mutants (313 verdict/status-anchored + 45 codec-reject malformed negatives) | `baaa4ac59249ba9f49a470bfa76bfe82f6e9a171` |
| 2 | Corpus units (T2, hand-lowered M0 sample) | `corpus-units/` | 60 units | `00b25fae26319ae5493ffe90c83edafba8cfb843` |
| 3 | Worked examples (golden verdicts, both drivers) | `examples/` | 11 examples | `95e978b1608ea31a37ef0107a172d0adb16e1957` |

**Generator seed.** `mutationSeed = 20260801` (`src/Lara/Mutate.hs:308`,
SplitMix64, keyed per `(base, operator)`). Verified byte-identically
reproducible: `cabal exec -- runghc scripts/gen-mutants.hs` over the committed
tree leaves an empty `git diff` (358 mutants regenerated identically).

**Ablation configs.** `noCQConfig` / `noTypedConfig` from
`Lara.Check.CheckConfig` (`src/Lara/Check.hs`); `fullConfig` is the frozen
semantics. Pinned by the freeze commit SHA below.

## Reproducibility gates (all green pre-freeze)

| Gate | Command | Result |
| --- | --- | --- |
| Seed reproducibility | `cabal exec -- runghc scripts/gen-mutants.hs` | 358 mutants byte-identical (empty `git diff`) ✓ |
| Cross-driver differential (positive) | `bash scripts/differential.sh` | pass=416 fail=0 ✓ |
| Cross-driver differential (negative) | `bash scripts/differential.sh` | pass=54 fail=0 ✓ |
| Test suite | `cabal test all` | green (incl. `AblationSpec`) ✓ |

## Post-freeze measurement run

Command (one command, manifest-driven discovery):

```
cabal exec -- runghc scripts/measure.hs
```

Emits `measurements/{report,ablation}.{json,tsv}` over 418 inputs (358 mutants +
60 corpus units). The canonical snapshot is committed under
`measurements/frozen/` (the working `measurements/` is gitignored as regenerable
output).

### Frozen headline numbers

| Metric | Value |
| --- | --- |
| Measurement records | 418 (358 mutants + 60 corpus units) |
| Class match (`actual` = `expected`) | 418 / 418 |
| Cross-driver agreement (`lean_agree`) | 418 / 418 |
| Location match (where applicable) | 264 / 264 (154 n/a: accepts, codec-fails, corpus units) |
| Replay success (corpus units) | 60 / 60 |
| Ablation **no-cq** missed rejections | 18 — all `reject-IncompleteArgument` (surgical) |
| Ablation **no-typed** missed rejections | 30 — 11 `reject-R10` + 19 `reject-R11` (surgical) |

Corpus-unit status diversity (T2): 48 gap, 9 justified, 3 defeated (contested is
carried by worked example E5).

### Determinism note

`report.{json,tsv}` columns 1–14 are deterministic; columns `hs_check_ns` and
`lean_wall_ns` are wall-clock timing (reported, environment-dependent, **not**
frozen). `ablation.{json,tsv}` carries no timing and is fully deterministic. The
reproducibility anchors below hash only the deterministic content.

| Frozen output anchor | SHA-256 |
| --- | --- |
| `report.tsv` deterministic projection (`cut -f1-14`) | `b241a5761687952a7b441419a534d7a3e1606fc3228fa22f1508b4f5ceb210d2` |
| `ablation.tsv` (full, deterministic) | `e744bbd7b9bb87b8aae7c3e16483f50c6800d511def989e552b2ac91e50383dd` |

Measurement environment of record: GHC 9.14.1, Lean 4.32.0, darwin/aarch64
(recorded in `report.json` `environment`).

## Freeze commit and tag

- **Freeze commit:** `<FILL-AFTER-COMMIT>` (merge commit of the T5 freeze PR).
- **Tag:** `m5-freeze-v1` (annotated), on the freeze commit — the M1 analogue is
  `spec-v0.1`.
- Post-freeze rule: any change to a frozen input (rows 1–3) or the seed
  invalidates this freeze; re-run the gates and cut `m5-freeze-v2`.

## Reproduce from scratch

```
git checkout m5-freeze-v1
cabal build all
cabal exec -- runghc scripts/gen-mutants.hs   # empty git diff = seed reproduces
bash scripts/differential.sh                  # positive 416/0, negative 54/0
cabal exec -- runghc scripts/measure.hs       # regenerates measurements/
cut -f1-14 measurements/report.tsv | shasum -a 256   # matches anchor above
shasum -a 256 measurements/ablation.tsv               # matches anchor above
```
