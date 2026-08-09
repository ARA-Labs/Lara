# M5 freeze checklist — evaluation corpus (deterministic scope)

_Operational record for milestone **M5 — evaluation corpus** task **T5 (freeze
protocol)** (`plans/research-proposal.md` §7, tracker #48). Companion to the M1
analogue (`docs/m1-freeze-checklist.md`). This file freezes the fixture
set, corpus sample, and generator seeds before the final measurement runs; the
paper's axis-(c) tables are generated only from post-freeze runs against the
inputs pinned here._

_**Re-freeze history.** `m5-freeze-v1` (tag on the #55 merge commit) froze the
358-mutant suite over the all-defeasible corpus. Issue #57 (the `ra@1`
rational-arithmetic certifier, PR #59) changed frozen inputs — the
shared policy gained the strict Family-10 rule (rippling through every
`unit.core.sexp`), `adaptive-pruning/C04` gained the certificate-checked
strict arg, and the seeded sweep grew the suite 358 → 360 — so per the
post-freeze rule this file now records **`m5-freeze-v2`**. The v1 anchors
remain addressable via the tag._

_**`m5-freeze-v3`, issues #76/#79 (snapshot commit `4d5c6ae`, 2026-08-06).**
Conservative reporting for quarantine-affected claims added the
`quarantine-attacker` accept-family operator, so the seeded sweep grew
**360 → 369** mutants (9 new: one per justified corpus unit) and the measured
input set **420 → 429**. Only additions: no existing mutant's bytes changed, no
measured input changed (`unit.core.sexp` × 60 and the 11 worked-example goldens
are byte-identical to v2), and `bundles/` and
`measurements/frozen/claim-support.*` are untouched — no frozen artifact
declares a duplicate-report group, so nothing that was already frozen reports
`evidence-blocked`. The rows-2/3 tree SHAs below moved anyway because of
non-measured content: docs (`LOWERING.md`, `examples/README.md`), the #79
surface-policy repair (`corpus-v1.policy.lara`, `adaptive-pruning/C04/unit.lara`
— the `.lara` surface path, not the measured core), and additive demo /
running-example files (#65–#73). The v3 snapshot was produced at a clean
`3108a5f` (`report.json` `environment`: `git-dirty: false`) and committed as
`4d5c6ae`; the tables below describe **v3**._

_**Post-v3 movement, still `m5-freeze-v3` (the `ord@1` / premise-only branch).**
The measured inputs are untouched: rows 1 and 2 hold their v3 SHAs exactly
(`fixtures/mutants/` = `11160a8…`, `corpus-units/` = `4f4c4ec…`), so
`measurements/frozen/` and every headline number below remain the numbers of
record and no re-run is owed. Row 3's tree moved again, additively and outside
the measured set: worked examples **S2** (`ord@1` comparison, landed with #83),
**S3** (the `num_le` tie) and **S4** (an undermined binding) were added, and the
11 measured examples are byte-identical. The differential gate row rose
436 → 445; the last four of those are this branch's (+2 `ra@1` premise-only
fixtures, +2 worked-example anchors), and the other five arrived with #83
alone, which was measured at 441 on `main` before this branch. (#81 is an
ancestor of the v3 commit, so its anchors were already counted in the 436
baseline.) Making `ra@1` premise-only changed
**zero** frozen bytes because `corpus-v1`'s `ra@1` theory is declared empty
(`corpus-units/corpus-v1.policy.lara`), so no certificate in the frozen set
could cite a theory entry in the first place._

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
| 1 | Seeded mutation suite (verdict + specified-status anchors) | `fixtures/mutants/` | 369 mutants (324 verdict/status-anchored + 45 codec-reject malformed negatives) | `11160a8fdeb47a7e3772d26e6878e472a7a64dbe` |
| 2 | Corpus units (T2, hand-lowered M0 sample; C04 carries the #57 `ra@1` certificate; every measured `unit.core.sexp` byte-identical to v2 — tree moved on docs + #79 surface-policy repair only) | `corpus-units/` | 60 units | `4f4c4ec7841b0a231771d5ba20bfe97302e3b4d4` |
| 3 | Worked examples (golden verdicts, both drivers; the 11 measured examples byte-identical to v1 — tree moved on additive demos/running-example + README + the additive S2/S3/S4 `ord@1` examples only) | `examples/` | 11 measured examples (+ additive demonstrators) | `d985156f5be5134dba14bf0a28455fb697305837` |

**Generator seed.** `mutationSeed = 20260801` (`src/Lara/Mutate.hs:308`,
SplitMix64, keyed per `(base, operator)`). Verified byte-identically
reproducible: `cabal exec -- runghc scripts/gen-mutants.hs` over the committed
tree leaves an empty `git diff` (360 mutants regenerated identically).

**Ablation configs.** `noCQConfig` / `noTypedConfig` from
`Lara.Check.CheckConfig` (`src/Lara/Check.hs`); `fullConfig` is the frozen
semantics. Pinned by the freeze commit SHA below.

## Reproducibility gates (all green pre-freeze)

| Gate | Command | Result |
| --- | --- | --- |
| Seed reproducibility | `cabal exec -- runghc scripts/gen-mutants.hs` | 369 mutants byte-identical (empty `git diff`) ✓ |
| Cross-driver differential (positive) | `bash scripts/differential.sh` | pass=445 fail=0 ✓ (at branch HEAD; **436**/436 at the `m5-freeze-v3` tag — see the post-v3 note) |
| Cross-driver differential (negative) | `bash scripts/differential.sh` | pass=54 fail=0 ✓ |
| Admission differential (#81) | `bash scripts/admission-differential.sh` | pass=20 fail=0 (15 semantic byte-identical + 5 codec rejects) ✓ |
| Replay-tamper detection | `bash scripts/test-replay-tamper.sh` | both tamper classes detected ✓ |
| Lean axiom audit | `cd lean && lake env lean AxCheck.lean \| ../scripts/check-axioms.sh` | `sorry`-free, standard trio (incl. `Lara.RA`) ✓ |
| Test suite | `cabal test all` | green (incl. `AblationSpec`, `ClaimSupportSpec`) ✓ |
| Freeze-bundle tests | `python3 scripts/test_freeze_bundle.py` | 4/4 ✓ |

## Post-freeze measurement run

Command (one command, manifest-driven discovery):

```
cabal exec -- runghc scripts/measure.hs
```

Emits `measurements/{report,ablation}.{json,tsv}` over 429 inputs (369 mutants +
60 corpus units); `scripts/claim-support.hs` emits the claim-support
aggregation and the committed `measurements/binding-audit/worklist.tsv`.
The canonical aggregate snapshot is committed under `measurements/frozen/`;
other working measurement outputs remain gitignored as regenerable output.

### Frozen headline numbers

| Metric | Value |
| --- | --- |
| Measurement records | 429 (369 mutants + 60 corpus units) |
| Class match (`actual` = `expected`) | 429 / 429 |
| Cross-driver agreement (`lean_agree`) | 429 / 429 |
| Location match (where applicable) | 266 / 266 (163 n/a: accepts — incl. the 9 `quarantine-attacker` mutants — codec-fails, corpus units) |
| Replay success (corpus units) | 60 / 60 |
| Claim-support (4): load-bearing strict steps carrying a checked certificate | 1 / 1 (#57, `adaptive-pruning/C04`) |
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
| `report.tsv` deterministic projection (`cut -f1-14`) | `1152aba34e36535bea21511bebb950f79fc17681f1ddd9125067394ed5c07226` |
| `ablation.tsv` (full, deterministic) | `76b89045cbf47ddfd0767efce81c82e339da35e436d3c35bf7efd496508e58c2` |

Measurement environment of record: GHC 9.14.1, Lean 4.32.0, darwin/aarch64
(recorded in `report.json` `environment`).

## Freeze commit and tag

- **v1 tag:** `m5-freeze-v1` (annotated), on `300b235` (merge commit of the T5
  freeze PR #55) — the M1 analogue is `spec-v0.1`.
- **v2 freeze commit:** `68e7298` (merge commit of the #57 PR, #59). The tag
  was not cut at merge time; it was cut retroactively alongside v3.
- **v2 tag:** `m5-freeze-v2` (annotated), on `68e7298`.
- **v3 snapshot commit:** `4d5c6ae` (measurement run at clean `3108a5f`).
- **v3 tag:** `m5-freeze-v3` (annotated), on `62eea92` (merge commit of the v3
  re-freeze PR, #82).
- Post-freeze rule: any change to a frozen input (rows 1–3) or the seed
  invalidates this freeze; re-run the gates and cut the next tag (e.g. the
  deferred wrong-fraction certificate mutation operator would cut
  `m5-freeze-v3`).

## Reproduce from scratch

Every number in this block is **the tag's**, not the current branch's — the
post-v3 note above records where they differ (the positive differential is
436 at `m5-freeze-v3` and 445 at branch HEAD; the anchors and headline numbers
are unchanged, since no frozen input moved).

```
git checkout m5-freeze-v3
cabal build all
cabal exec -- runghc scripts/gen-mutants.hs   # empty git diff = seed reproduces
bash scripts/differential.sh                  # positive 436/0, negative 54/0
cabal exec -- runghc scripts/measure.hs       # regenerates measurements/
cabal exec -- runghc scripts/claim-support.hs # claim-support aggregation
cut -f1-14 measurements/report.tsv | shasum -a 256   # matches anchor above
shasum -a 256 measurements/ablation.tsv               # matches anchor above
```
