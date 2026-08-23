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

_**`m5-freeze-v4`, `lara-core@0.2` / issue #89 closeout (snapshot commit
`ced19fe`, 2026-08-10).** The many-sorted signature is now checked core state,
so every measured core input was regenerated for `lara-core@0.2`. PR #97 grew
the mutation suite **369 → 496**; the closeout adds one dedicated integrated
stage-2 fixture for each of the six Σ well-formedness clauses and two pinned
codec-boundary fixtures for the new `sigma` section, growing it **496 → 504**.
The measured input set is therefore **429 → 564** (504 mutants + 60 corpus
units). The seed remains `20260801`. The #89 boundary diffs over the 369
pre-existing manifest outcomes and all 60 corpus verdict/status goldens were
empty; the eight closeout rows are additive. The current input anchors,
measurements, and gates below describe **v4**.

_**Post-v4 movement, still `m5-freeze-v4` (S6 and the running-example @0.6
refresh).** The measured inputs are untouched: rows 1 and 2 hold their v4 SHAs
exactly (`fixtures/mutants/` = `fd71420…`, `corpus-units/` = `1dc20ea…`), the
11 measured worked-example goldens are byte-identical, and
`measurements/frozen/` axis-(c) numbers remain the numbers of record — no
re-run is owed. Row 3's tree moved twice, both outside the measured set:
worked example **S6** (the `lara-syntax@0.6` named-slot byte-identity witness,
#105/#110) was added, and the paper's **running-example** run1/run2 — demo
content this file has classified as non-measured since the v3 note — was
refreshed to the then-current surface (@0.4 value bindings, @0.5 inferred
instantiation, a strict `ord@1` step with an @0.6 named-slot certificate, on a
run-local `empirical-v3` policy). Unlike prior row-3 movement the refresh
*modifies* existing demo bytes, so its derived goldens
(`example.core.sexp`, `expected.json`) and the pinned report
`measurements/frozen/running-example.txt` were regenerated together and are
re-pinned by `RunningExampleSpec` / `DifferentialSpec`. The differential gate
row rose 580 → 581 (+1 S6 anchor; the refresh changes bytes, not counts)._

_**Post-`lara-syntax@0.7` movement, still `m5-freeze-v4` (surface strictness,
2026-08-20).** `lara-syntax@0.7` (grammar Appendix F) is a surface-only release:
three restrictions on the `.lara` presentation surface, no `lara-core` change,
no AST change, and no wire change. Migrating the controlled sources to the new
`open q` hole spelling moved **10 lines in 7 of 109 tracked `.lara` files** —
`corpus-units/bam/C05`, `corpus-units/fre/C01`,
`corpus-units/rebench-restricted_mlm/C14`,
`corpus-units/rebench-triton_cumsum/C09` (one line each), and
`examples/rebuttal-replay/round0`, `round1`, `round2` (two lines each). All ten
were the equal form `open X as X`, so the migration is textual.

**No derived byte changed.** Verified by explicit pathspec diff over
`corpus-units/**/*.core.sexp`, `corpus-units/**/expected.json`,
`examples/**/*.core.sexp`, `examples/**/expected.json`, `fixtures/mutants` and
`measurements/frozen` — empty. Rows 1 and 3's measured content is therefore
unchanged, and `fixtures/mutants/` holds its v4 SHA exactly
(`fd7142072d58da4d35642cbad6f144c970627afa`), as does `measurements/frozen/`
(`a067c921e0142eae69b34ed500ff18c7efea1bed`).

**Two source trees re-pin, intentionally**, because authored `.lara` sources
live inside them. Both prior hashes are retained here as provenance:

| tree | through `@0.6` | at `@0.7` |
| --- | --- | --- |
| `corpus-units/` | `1dc20ea9d79adb2690731a66216dae828a100cf3` | `cadb5fa62b9f7f6ace14129f1435e3c32b2dff7b` |
| `examples/` | `4ab6b5f480d9e3bddd94b17908d1c6a910b7944f` | `9e6291fbf1a53703092123a4550ab2099cbed52c` |

Record each anchor only after the final commit that touches its tree. The
commit that records an anchor must not also modify that anchored tree; if it
does, recompute the anchor from the resulting tree.

(Row 3's table cell still carries the v4 anchor `2f7fa9ad…`; `examples/` has
been classified as moved-since-v4 in the note above since S6 landed, and its
measured goldens are the 11 worked-example files, all byte-identical.)

**No measurement re-run is owed.** The harness consumes `.core.sexp` bytes,
every one of which is unchanged, so the numbers of record stand as measured:
564/564 class match, 564/564 `lean_agree`, 60/60 replay. The gate counts are
also unchanged (differential 581 pass / 0 fail, admission 20/20,
presentation-parity 73 rows)._

_**Post-`lara-syntax@0.8` movement, still `m5-freeze-v4` (premise-label
citation, 2026-08-21).** `lara-syntax@0.8` (grammar Appendix G) is an additive
surface release: a certificate premise reference may cite the citing rule's
declared premise label beside the `@0.6` leaf and prior-argument names. No
`lara-core` change, no AST change, no wire change.

**No source migration, and none was possible.** `@0.8` adds names to a
namespace and removes nothing, so **zero** of the 109 tracked `.lara` files
moved a line. The new class is also empty corpus-wide: no tracked policy labels
a premise of a rule whose certificates cite names, so `premiseLabelIndex`
returns `Nothing` for every name in every controlled source and the resolver's
behavior there is bitwise `@0.6`'s. Acceptance is unchanged.

**One tree re-pins, for the S6 reason.** `examples/` moved because worked
example **S7** was added — the `lara-syntax@0.8` premise-label byte-identity
witness (#131), four new files under `examples/S7/`. This is the same shape as
S6's addition recorded in the `@0.7` note above: new content in a
classified-as-moved-since-v4 tree, not a modification of measured bytes. The
prior hash is retained here as provenance:

| tree | at `@0.7` | at `@0.8` |
| --- | --- | --- |
| `examples/` | `9e6291fbf1a53703092123a4550ab2099cbed52c` | `9ac2b03eec8dd3043ccb9ac99e685265cc69b122` |

**The other three frozen trees hold their `@0.7` SHAs exactly**, verified by
`git rev-parse`: `corpus-units/` = `cadb5fa62b9f7f6ace14129f1435e3c32b2dff7b`,
`fixtures/mutants/` = `fd7142072d58da4d35642cbad6f144c970627afa`,
`measurements/frozen/` = `a067c921e0142eae69b34ed500ff18c7efea1bed`.

**No derived byte outside `examples/S7/` changed.** Re-running
`scripts/gen-worked-examples.hs` over the whole registry rewrote every anchor
and left all of them byte-identical except the two new S7 files; S7's own
goldens were separately verified byte-equal to those its numeric twin produces
(both certificates lower to `(ordcmp (prem 0) (prem 1))`).

**No measurement re-run is owed**, for the reason above: every measured
`.core.sexp` byte is unchanged, so 564/564 class match, 564/564 `lean_agree`
and 60/60 replay stand as measured. One gate count moves: the differential row
rose **581 → 582** (+1 S7 anchor, the same `+1` bookkeeping S6 produced).
`admission 20/20` and `presentation-parity 73 rows` are unchanged._

_**Post-`lara-syntax@0.9` movement, still `m5-freeze-v4` (named `nd@1` proof
terms, 2026-08-22).** `lara-syntax@0.9` (grammar Appendix H) adds named binders,
premise references, and numeric theory references inside the existing opaque
`nd@1` certificate payload. Elaboration lowers them to the unchanged de Bruijn
kernel image. There is no `lara-core`, AST, wire, checker, replay, corpus, mutant,
or frozen-measurement change, and no source migration.

Worked example **S8** is the additive byte-identity witness: its named redex
lowers to its numeric twin's exact `.core.sexp`. The worked-example freshness
tests re-prove that equality. Fresh verification measured differential
**583 pass / 0 fail** (+1 S8 anchor), presentation parity **73 rows**, and mutant
regeneration **504 verified mutants with an empty tracked diff**. The measured
564/564 class match, 564/564 `lean_agree`, and 60/60 replay numbers therefore
remain the numbers of record; no measurement re-run or freeze-tag bump is owed._

_**Post-`lara-syntax@0.10` movement, still `m5-freeze-v4` (source-authored
`nd@1` formula annotations, 2026-08-23).** `lara-syntax@0.10` (grammar
Appendix I, closing #144) adds the `(prop TEXT)` presentation formula, lowered
during elaboration through the shared `encodeAtomKey ∘ nf` path to the frozen
`(atom KEY)` node. There is again no `lara-core`, AST, wire, checker, replay,
corpus, mutant, or frozen-measurement change, and no source migration. Worked
example **S8** was rewritten to the authored spelling; its committed
`.core.sexp` and `expected.json` are byte-unchanged, so it remains the same
differential anchor and the worked-example freshness tests re-prove the
byte-identity. All gate counts and the numbers of record are unchanged; no
measurement re-run or freeze-tag bump is owed._

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
| 1 | Seeded mutation suite (verdict + specified-status anchors; includes dedicated Σ-WF and `sigma` codec closeout fixtures) | `fixtures/mutants/` | 504 mutants (457 verdict/status-anchored + 47 codec-reject malformed negatives) | `fd7142072d58da4d35642cbad6f144c970627afa` |
| 2 | Corpus units (T2, hand-lowered M0 sample; `lara-core@0.2` signatures; C04 carries the #57 `ra@1` certificate) | `corpus-units/` | 60 units | `cadb5fa62b9f7f6ace14129f1435e3c32b2dff7b` (was `1dc20ea9d79adb2690731a66216dae828a100cf3` through `@0.6`; the `@0.7` re-pin is source-only — see the note below) |
| 3 | Worked examples (golden verdicts, both drivers; 11 measured examples plus additive demonstrators including S2–S5) | `examples/` | 11 measured examples (+ additive demonstrators) | `2f7fa9adf45fefe649f9a9ed59def3f3d2257fc0` |

**Generator seed.** `mutationSeed = 20260801` (`src/Lara/Mutate.hs`,
SplitMix64, keyed per `(base, operator)`). Verified byte-identically
reproducible: `cabal exec -- runghc scripts/gen-mutants.hs` over the committed
tree leaves the generated suite unchanged (504 mutants).

**Ablation configs.** `noCQConfig` / `noTypedConfig` from
`Lara.Check.CheckConfig` (`src/Lara/Check.hs`); `fullConfig` is the frozen
semantics. Pinned by the freeze commit SHA below.

## Reproducibility gates (all green pre-freeze)

| Gate | Command | Result |
| --- | --- | --- |
| Seed reproducibility | `cabal exec -- runghc scripts/gen-mutants.hs` | 504 mutants byte-identical (empty generated-suite diff) ✓ |
| Cross-driver differential (positive) | `bash scripts/differential.sh` | pass=582 fail=0 ✓ |
| Cross-driver differential (negative) | `bash scripts/differential.sh` | pass=56 fail=0 ✓ |
| Admission differential (#81) | `bash scripts/admission-differential.sh` | pass=20 fail=0 (15 semantic byte-identical + 5 codec rejects) ✓ |
| Replay-tamper detection | `bash scripts/test-replay-tamper.sh` | both tamper classes detected ✓ |
| Lean build | `cd lean && lake build` | green ✓ |
| Lean axiom audit | `cd lean && lake env lean AxCheck.lean \| ../scripts/check-axioms.sh` | `sorry`-free, standard trio (incl. `Lara.RA`) ✓ |
| Test suite | `cabal test all` | green (incl. `AblationSpec`, `ClaimSupportSpec`, Σ closeout coverage) ✓ |
| Freeze-bundle tests | `python3 scripts/test_freeze_bundle.py` | 4/4 ✓ |

The positive differential row tracks the **live** count, not the count as it
stood at the freeze commit: it is pure `+1`-per-anchor bookkeeping, and each
movement is recorded in the addenda above (`580 → 581` with S6, `581 → 582`
with S7). Re-measured 2026-08-22 during PR #142: `pass=582 fail=0`,
`negative pass=56 fail=0`. Every other row is the freeze-time result and does
not move. The `580/0` under "Reproduce from scratch" below is **correct as
written and must not be refreshed**: it is scoped to `git checkout
m5-freeze-v4`, a tree in which the S6 and S7 anchors do not exist.

## Post-freeze measurement run

Command (one command, manifest-driven discovery):

```
cabal exec -- runghc scripts/measure.hs
```

Emits `measurements/{report,ablation}.{json,tsv}` over 564 inputs (504 mutants +
60 corpus units); `scripts/claim-support.hs` emits the claim-support
aggregation and the committed `measurements/binding-audit/worklist.tsv`.
The canonical aggregate snapshot is committed under `measurements/frozen/`;
other working measurement outputs remain gitignored as regenerable output.

The same rule covers the E1 performance table: `make bench` prints it and
writes the raw `measurements/bench.json`, but **no rendered table is committed
to this repository** — a timing table is valid only for the machine and commit
that produced it. Protocol, snapshot, and rationale: `performance.md`.

### Frozen headline numbers

| Metric | Value |
| --- | --- |
| Measurement records | 564 (504 mutants + 60 corpus units) |
| Class match (`actual` = `expected`) | 564 / 564 |
| Cross-driver agreement (`lean_agree`) | 564 / 564 |
| Location match (where applicable) | 399 / 399 (165 n/a: accepts — incl. the 9 `quarantine-attacker` mutants — and codec failures) |
| Replay success (corpus units) | 60 / 60 |
| Claim-support (4): load-bearing strict steps carrying a checked certificate | 1 / 1 (#57, `adaptive-pruning/C04`) |
| Ablation **no-cq** missed rejections | 18 — all `reject-IncompleteArgument` (surgical) |
| Ablation **no-typed** missed rejections | 30 — 11 `reject-R10` + 19 `reject-R11` (surgical) |

**`lara-core@0.2` (#89) re-freeze.** The suite grew from 369 to 496 mutants: the
signature family adds 107 `reject-R2` rows (five operators, one per clause of
the amended class) and 20 `reject-R12` rows from `out-of-scope-var`, the witness
for R12's new spec-§4.1 arm. Two diffs were taken across the regeneration
boundary and **both are empty**, which is the measurement this pass claims:

- the `MANIFEST.tsv` `expected`-column diff over the 369 pre-existing rows, and
- the verdict-and-status diff over all 60 corpus `expected.json` files.

The empty first diff is the design commitment of #89 §8 paying off: every
symbol-injecting operator now extends its mutant's carried Σ, so a mutant tests
the class it seeds rather than incidental signature noise.
`measurements/binding-audit/**` is **frozen input, excluded from regeneration**
(#89 §8, decision D-5); the pre-regeneration byte-compare of the recomputed
`worklist.tsv` against the committed one was empty, confirming the wire bump
cannot reach the 38-leaf denominator.

The v4 closeout adds six `reject-R2` rows (one for each `SigmaFault`
constructor) and two codec-reject rows (`codec-sigma-junk`,
`codec-sigma-order`). It changes no pre-existing expected outcome and raises
the measured totals **556 → 564**, `reject-R2` **107 → 113**, and codec rejects
**45 → 47**.

Corpus-unit status diversity (T2): 48 gap, 9 justified, 3 defeated (contested is
carried by worked example E5).

### Determinism note

`report.{json,tsv}` columns 1–14 are deterministic; columns `hs_check_ns` and
`lean_wall_ns` are wall-clock timing (reported, environment-dependent, **not**
frozen). `ablation.{json,tsv}` carries no timing and is fully deterministic. The
reproducibility anchors below hash only the deterministic content.

| Frozen output anchor | SHA-256 |
| --- | --- |
| `report.tsv` deterministic projection (`cut -f1-14`) | `eae0c82e8c1607a4daf74b8dfb8ecab333996f0e213bcbf22f9b81533add3d7a` |
| `ablation.tsv` (full, deterministic) | `23112189212d4e6e154fafa4a7a2d9425e9d77de2b228702f3bf52b29859cdc3` |

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
- **v4 snapshot commit:** `ced19fe` (clean measurement input and environment
  recorded in `report.json`).
- **v4 tag:** `m5-freeze-v4` (annotated), on `f4327b4` (merge commit of the v4
  re-freeze PR #99). Cut after main CI run `31463095876` passed on PR #100's
  benchmark-harness repair.
- Post-freeze rule: any change to a frozen input (rows 1–3) or the seed
  invalidates this freeze; re-run the gates and cut the next tag. The deferred
  `drop-covering-attack` / `wrong-fraction` operators would therefore require
  `m5-freeze-v5`.

## Reproduce from scratch

Reproduce v4 from the annotated tag:

```
git checkout m5-freeze-v4
cabal build all
cabal exec -- runghc scripts/gen-mutants.hs   # empty generated-suite diff
bash scripts/differential.sh                  # positive 580/0, negative 56/0
cabal exec -- runghc scripts/measure.hs       # regenerates measurements/
cabal exec -- runghc scripts/claim-support.hs # claim-support aggregation
cut -f1-14 measurements/report.tsv | shasum -a 256   # matches anchor above
shasum -a 256 measurements/ablation.tsv               # matches anchor above
```

## Clean-tree verification (M7 task T7, tracker #60)

T7 is the exit criterion that the artifact reproduces the frozen numbers **from a
fresh clone**, not from a working tree. The re-freeze half of T7 is done (PR #82
produced v3; v4 followed with #99); the written clean-clone record is
**deferred to the artifact/release stage** by researcher decision on #60 —
artifact evaluation runs post-submission, so the record is produced with artifact
packaging rather than now.

When it is produced, the protocol is:

```
git clone --branch <tag-or-branch> <this-repo> "$SCRATCH/lara-t7"
cd "$SCRATCH/lara-t7" && git submodule update --init
cabal build all && (cd lean && lake build)
cabal exec -- runghc scripts/gen-mutants.hs   # empty generated-suite diff
bash scripts/differential.sh                  # positive/negative counts above
bash scripts/admission-differential.sh        # 20 files: 15 semantic + 5 codec-reject
bash scripts/test-replay-tamper.sh            # both tamper classes detected
(cd lean && lake env lean AxCheck.lean) | scripts/check-axioms.sh
cabal test all --test-show-details=direct
python3 scripts/test_freeze_bundle.py -v      # 4/4
cabal exec -- runghc scripts/measure.hs
cut -f1-14 measurements/report.tsv | shasum -a 256   # must equal the anchor above
shasum -a 256 measurements/ablation.tsv              # must equal the anchor above
```

Two notes carried over from the T7 execution pass, both easy to get wrong:

- `scripts/replay.sh` takes a `BUNDLE_DIR` argument (see its usage header), so a
  bare `bash scripts/replay.sh` is not a gate. Replay coverage comes from
  `scripts/test-replay-tamper.sh` plus the harness `replay_ok` column (60/60
  corpus units) — iterate over `bundles/` only if a per-bundle record is wanted.
- The record must state the environment (GHC, Lean, OS/arch) and note that the
  wall-clock columns (`hs_check_ns`, `lean_wall_ns`) are excluded from the
  deterministic projection being hashed.

If any gate is red, stop and diagnose — never adjust an anchor to match observed
output.
