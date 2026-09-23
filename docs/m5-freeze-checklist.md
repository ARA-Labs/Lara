# M5 freeze checklist — evaluation corpus (deterministic scope)

_What this is: the protocol and record for the evaluation freeze, the pinned
inputs and measurements the paper's numbers reproduce from. A *corpus unit*
is a checked program lowered from a real research artifact; a *mutant* is a
unit with a known seeded defect that the checker must reject with the right
rejection class at the right location. The section directly below is the
current snapshot; the freeze protocol and the historical record follow it._

## Current snapshot: evaluation freeze v6

Recorded 2026-09-09. The committed `measurements/frozen/` snapshot now describes
**595 mutants + 60 corpus units = 655 measured inputs**. It was measured from
clean input commit `bc888a5d4b60438565bcf0922a8a3f04cfc645b8` (`git-dirty: false`).
The publication tag **`m5-freeze-v6` is pending merge**: cut an annotated tag on
the eventual merge commit after verifying the anchors and gates below, following
the v3–v5 procedure. The latest published tag remains `m5-freeze-v5`; its
numbers and reproduction recipe are preserved in the historical record below.

### Scope and additive class deltas

The v6 cycle adds S9 (`insp@1`) and batches S2 (`ord@1`) into the same freeze.
Each adds 27 verified mutants: 22 verdict anchors and 5 codec negatives.
The seed remains `20260801`; the checker and operators are unchanged.
A byte comparison against parent `08ebe6a` verified **all 541 old mutant files
and all 541 old manifest rows unchanged**. Only 54 mutant files are added;
`MANIFEST.tsv` and the generated `README.md` are the only existing mutation-suite
files modified. All 601 pre-existing report rows retain identical deterministic
columns 1–15, and every old ablation row is unchanged. Corpus inputs,
claim-support TSV, and the binding-audit worklist remain byte-identical.

| Outcome | v5 | Added | v6 |
| --- | ---: | ---: | ---: |
| `reject-R1` | 63 | +8 | 71 |
| `reject-R12` | 40 | +4 | 44 |
| `reject-R3` | 19 | +2 | 21 |
| `reject-R4` | 30 | +4 | 34 |
| `reject-R7` | 20 | +4 | 24 |
| `reject-R13` | 43 | +6 | 49 |
| `reject-R11` | 19 | +2 | 21 |
| `reject-R9` | 19 | +2 | 21 |
| `reject-R2` | 113 | +12 | 125 |
| `codec-reject` | 47 | +10 | 57 |

All other outcome counts are unchanged. The new certificate cases cover the
backend payload decoder (R13) and certificate theory allowlist (R7).
`cert-payload-tamper` writes `mut_corrupt`; it does **not** drop a slot.
For S9 it corrupts an `inspect` certificate, while `cert-theory-swap` changes
an `inspectdiff` certificate's digest. These are not measurements of every
inspection semantic guard or of well-formed false certificates. The existing
backend properties and Lean proofs remain the evidence for those obligations.
`MutationSpec.prop_backendCertificateCoverage` now requires measured certificate
mutants for both backends and replays them to their specified R7/R13 outcomes.

### Frozen inputs and deterministic outputs

| Input | Count | Git tree SHA |
| --- | --- | --- |
| `fixtures/mutants/` | 595 (538 verdict/status anchors + 57 codec negatives) | `e68a33bf80de8535d64c9483d24626ee0d8c5959` |
| `corpus-units/` | 60 measured units | `cadb5fa62b9f7f6ace14129f1435e3c32b2dff7b` |
| `examples/` | 11 historically measured examples plus additive demonstrators; S2/S9 now feed mutations | `046c0981e575b6efd944e217dd4b2572855459b2` |

| Output | SHA-256 |
| --- | --- |
| `report.tsv`, `cut -f1-15` | `32aa22cdcbe159d460124c932911848dc776723b7b73c6063755cef3261f7262` |
| `ablation.tsv`, full | `df25144c687e831fb4401eb4ad4f25373e8e987611e69e6aaed82dfabc86e01f` |

Environment: GHC **9.10.3**, Lean **4.32.0** (commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`),
Linux/x86_64. The two report timing columns remain machine-dependent and are
excluded from the deterministic hash. These timings must not be interpreted as
a performance change relative to the v5 macOS/ARM run. Claim-support is
Haskell-only and intentionally records an empty Lean-version field.

### Measured results

| Metric | v6 result |
| --- | --- |
| Class match | 655 / 655 |
| Haskell–Lean agreement | 655 / 655 |
| Location match and primary | 480 / 480 each (175 not applicable) |
| Corpus replay | 60 / 60 |
| Load-bearing strict steps with checked certificates | 1 / 1 |
| `no-cq` missed rejections | 18, all `reject-IncompleteArgument` |
| `no-typed` missed rejections | 37: 11 R10 + 21 R11 + 5 MissingConflict |
| `no-conflict-scan` missed rejections | 5, all MissingConflict |

`no-typed` grows 35 → 37 solely from the two new `unlicensed-attack` mutants;
no ablation configuration changed. Location agreement remains a construction
and harness check, not an independent localization-accuracy estimate.

### Verification and reproduction

| Gate | Result on the v6 input tree |
| --- | --- |
| `cabal build all` / `cabal test all --test-show-details=direct` | pass |
| `cabal exec -- runghc scripts/gen-mutants.hs --check` | 595 mutants byte-identical |
| `bash scripts/differential.sh` | 669 verdict anchors, 66 codec negatives; zero failures |
| `bash scripts/admission-differential.sh` | 20 / 20 |
| `bash scripts/test-replay-tamper.sh` | both tamper classes detected |
| `cd lean && lake build` | pass (existing linter warnings) |
| `lake env lean AxCheck.lean` piped through `check-axioms.sh` with `pipefail` | pass; standard axiom trio only |
| `python3 -m unittest scripts/test_freeze_bundle.py -v` | 4 / 4 |
| `make presentation-parity` | 78 rows |

The positive differential grows 625 → 669 and the negative 56 → 66, exactly
44 verdict additions and 10 codec additions. These are fresh local checks;
CI status belongs to the PR, not this measurement record.

Reproduce from the clean input commit now, or from `m5-freeze-v6` once published:

```sh
git checkout bc888a5d4b60438565bcf0922a8a3f04cfc645b8
cabal build all
(cd lean && lake build)
cabal exec -- runghc scripts/gen-mutants.hs --check
bash scripts/differential.sh
ELAN_TOOLCHAIN=leanprover/lean4:v4.32.0 make measure
cabal exec -- runghc scripts/claim-support.hs
cut -f1-15 measurements/report.tsv | sha256sum
sha256sum measurements/ablation.tsv
```

Pinning `ELAN_TOOLCHAIN` makes the measurement harness's root-directory
`lean --version` agree with the driver built under `lean/lean-toolchain`, even
when the machine's default toolchain differs. Freeze publication verifies all
three input tree SHAs and both deterministic output hashes above; do not move
an old tag or replace an anchor merely to match an unexplained difference.

## Historical record: v1–v5

Everything below describes the previous freezes, including the then-current v5
snapshot, counts, and commands. It is retained as provenance, not as a description
of the current `measurements/frozen/` contents.

_Operational record for milestone **M5 — evaluation corpus** task **T5 (freeze
protocol)**. Companion to the M1
analogue (`docs/m1-freeze-checklist.md`). This file freezes the fixture
set, corpus sample, and generator seeds before the final measurement runs; the
paper's axis-(c) tables are generated only from post-freeze runs against the
inputs pinned here._

_**The `m5-` prefix is legacy.** M5 closed long ago; this series
is the **evaluation-corpus freeze**, and all four re-cuts after v1 were
unrelated to that milestone — v2 for the `ra@1` certifier, v3 for
conservative quarantine reporting, v4 for the `lara-core@0.2`
signature bump, v5 for the evaluation-suite completion batch. The
name is kept because v1–v4 are published, addressable anchors and a mid-series
rename would give "the freeze after v4" two names; `corpus-units/corpus-v1.policy.lara`
is itself a frozen input that references this file by path, so renaming it would
change frozen corpus bytes for a cosmetic reason. Current tag:
**`m5-freeze-v5`**._

_**Re-freeze history.** `m5-freeze-v1` (tag on merge commit `300b235`) froze the
358-mutant suite over the all-defeasible corpus. The `ra@1`
rational-arithmetic certifier changed frozen inputs — the
shared policy gained the strict Family-10 rule (rippling through every
`unit.core.sexp`), `adaptive-pruning/C04` gained the certificate-checked
strict arg, and the seeded sweep grew the suite 358 → 360 — so per the
post-freeze rule this file now records **`m5-freeze-v2`**. The v1 anchors
remain addressable via the tag._

_**`m5-freeze-v3` (snapshot commit `4d5c6ae`, 2026-08-06).**
Conservative reporting for quarantine-affected claims added the
`quarantine-attacker` accept-family operator, so the seeded sweep grew
**360 → 369** mutants (9 new: one per justified corpus unit) and the measured
input set **420 → 429**. Only additions: no existing mutant's bytes changed, no
measured input changed (`unit.core.sexp` × 60 and the 11 worked-example goldens
are byte-identical to v2), and `bundles/` and
`measurements/frozen/claim-support.*` are untouched — no frozen artifact
declares a duplicate-report group, so nothing that was already frozen reports
`evidence-blocked`. The rows-2/3 tree SHAs below moved anyway because of
non-measured content: docs (`LOWERING.md`, `examples/README.md`), the
surface-policy repair (`corpus-v1.policy.lara`, `adaptive-pruning/C04/unit.lara`
— the `.lara` surface path, not the measured core), and additive demo /
running-example files. The v3 snapshot was produced at a clean
`3108a5f` (`report.json` `environment`: `git-dirty: false`) and committed as
`4d5c6ae`; the tables below describe **v3**._

_**Post-v3 movement, still `m5-freeze-v3` (the `ord@1` / premise-only branch).**
The measured inputs are untouched: rows 1 and 2 hold their v3 SHAs exactly
(`fixtures/mutants/` = `11160a8…`, `corpus-units/` = `4f4c4ec…`), so
`measurements/frozen/` and every headline number below remain the numbers of
record and no re-run is owed. Row 3's tree moved again, additively and outside
the measured set: worked examples **S2** (`ord@1` comparison),
**S3** (the `num_le` tie) and **S4** (an undermined binding) were added, and the
11 measured examples are byte-identical. The differential gate row rose
436 → 445; the last four of those are this branch's (+2 `ra@1` premise-only
fixtures, +2 worked-example anchors), and the other five arrived with the
`ord@1` change alone, which was measured at 441 on `main` before this branch. (The
admission-differential change is an ancestor of the v3 commit, so its anchors
were already counted in the 436
baseline.) Making `ra@1` premise-only changed
**zero** frozen bytes because `corpus-v1`'s `ra@1` theory is declared empty
(`corpus-units/corpus-v1.policy.lara`), so no certificate in the frozen set
could cite a theory entry in the first place._

_**`m5-freeze-v4`, `lara-core@0.2` closeout (snapshot commit
`ced19fe`, 2026-08-10).** The many-sorted signature is now checked core state,
so every measured core input was regenerated for `lara-core@0.2`. The migration grew
the mutation suite **369 → 496**; the closeout adds one dedicated integrated
stage-2 fixture for each of the six Σ well-formedness clauses and two pinned
codec-boundary fixtures for the new `sigma` section, growing it **496 → 504**.
The measured input set is therefore **429 → 564** (504 mutants + 60 corpus
units). The seed remains `20260801`. The `lara-core@0.2` boundary diffs over the 369
pre-existing manifest outcomes and all 60 corpus verdict/status goldens were
empty; the eight closeout rows are additive. The current input anchors,
measurements, and gates below describe **v4**.

_**Post-v4 movement, still `m5-freeze-v4` (S6 and the running-example @0.6
refresh).** The measured inputs are untouched: rows 1 and 2 hold their v4 SHAs
exactly (`fixtures/mutants/` = `fd71420…`, `corpus-units/` = `1dc20ea…`), the
11 measured worked-example goldens are byte-identical, and
`measurements/frozen/` axis-(c) numbers remain the numbers of record — no
re-run is owed. Row 3's tree moved twice, both outside the measured set:
worked example **S6** (the `lara-syntax@0.6` named-slot byte-identity witness)
was added, and the paper's **running-example** run1/run2 — demo
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
witness, four new files under `examples/S7/`. This is the same shape as
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
Appendix I) adds the `(prop TEXT)` presentation formula, lowered
during elaboration through the shared `encodeAtomKey ∘ nf` path to the frozen
`(atom KEY)` node. There is again no `lara-core`, AST, wire, checker, replay,
corpus, mutant, or frozen-measurement change, and no source migration. Worked
example **S8** was rewritten to the authored spelling; its committed
`.core.sexp` and `expected.json` are byte-unchanged, so it remains the same
differential anchor and the worked-example freshness tests re-prove the
byte-identity. All gate counts and the numbers of record are unchanged; no
measurement re-run or freeze-tag bump is owed._

_**`m5-freeze-v5`, the evaluation-suite completion batch (snapshot
measured at clean `89c25ef`, 2026-08-25).** Three landed code tasks each changed
a frozen input, so they share one regeneration cycle rather than three: the
`cert-wrong-fraction` operator, the `drop-covering-attack` operator with the
standalone conflict-scan ablation, and the discriminating localization
benchmark. The seeded sweep grew **504 → 541** mutants and the measured input
set **564 → 601** (541 mutants + 60 corpus units). The seed is unchanged at
`20260801`.

**The 37 new mutants are five new operators, and they account for every class
delta**, which is the additivity check this cycle claims:

| Operator | Mutants | Class |
| --- | --- | --- |
| `cert-wrong-fraction` | 1 | `reject-R13` (42 → 43) |
| `drop-covering-attack` | 5 | `reject-MissingConflict` (0 → 5, a new class) |
| `retract-rule` | 19 | `reject-R1` (44 → 63) |
| `cross-stage-defect` | 7 | `reject-R4` (18 → 30, with `twin-support-defect`) |
| `twin-support-defect` | 5 | `reject-R4` |

No other class moved, and **no pre-existing mutant's bytes changed** — measured,
not assumed: `git diff --name-status m5-freeze-v4 HEAD -- fixtures/mutants/`
reports 37 additions and two modifications, which are `MANIFEST.tsv` (37
insertions, **zero deletions** — the generated index grew and no existing row
moved) and `README.md` (prose). The mechanism is the string-keyed generator
streams (`src/Lara/Mutate/Seed.hs`), which key on `base ++ "/" ++ opName op`, so
a new constructor cannot perturb an existing operator's draw wherever it sits in
the enum. `corpus-units/` holds its `@0.7`
SHA exactly (`cadb5fa6…`), so **`claim-support.{json,tsv}` is content-identical
to v4**: 1/1 load-bearing strict step carrying a checked certificate, and the
same 48 gap / 9 justified / 3 defeated status diversity. `measurements/binding-audit/worklist.tsv`
was regenerated and is byte-identical, re-confirming that the 38-leaf audit
denominator is untouched by this cycle.

**The location denominator moved, the rate did not.** `location_match` is
399/399 → **436/436**, and the new deterministic `location_primary` column
reports **436/436** beside it. This is the caveat below paying off rather
than an accuracy improvement: both are ≈100% *by construction*, because every
site of the `localization` family is gated against the checker before it reaches
`MANIFEST.tsv`. Cite the gate, not the rate.

**Two provenance repairs land with this snapshot.** `claim-support.json` is now
recorded from a clean tree — the v4 copy carried `git-dirty: true` at
`16fa55fa`, while `report.json` correctly carried `git-dirty: false`, so the two
halves of the frozen snapshot disagreed about their own provenance. And the
deterministic projection widens from `cut -f1-14` to `cut -f1-15`, absorbing
`location_primary`; the v4 anchors below are retained as provenance and stay
correct for the tree they describe.

**On the series name.** Cutting a fifth tag was the moment to decide whether the
series keeps its legacy `m5-` name. It does; see the note at the top of this
file for the decision and its cost._

_**Post-v5 movement, still `m5-freeze-v5` (the `insp@1` backend,
2026-09-07).** The measured inputs are untouched: rows 1 and 2 hold their v5
SHAs exactly (`fixtures/mutants/` = `9c174f4…`, `corpus-units/` = `cadb5fa…`),
the 11 measured worked-example goldens are byte-identical, and
`measurements/frozen/` holds `bef2bd1…` — the axis-(c) numbers remain the
numbers of record and no re-run is owed. Row 3's tree moved additively and
outside the measured set: worked example **S9** (the static code-inspection
demonstration, both certificate arities under one defeasible bridge) was added
with its co-located `insp-v1` policy and derived goldens. The differential gate
row rose **620 → 625**: +1 S9 anchor and +4 hand-authored
`fixtures/corpus/insp-*.sexp` replay anchors. Registering a fourth backend
changed **zero** frozen bytes — no frozen unit selects `insp@1`, the registry is
keyed by `(name, version)`, and `Lara.Replay.supportedBackends` only widens.

**The one deferral, stated as a cost rather than discovered as one.** Adding
`S9` to `Lara.Mutate.mutationBases` would give `insp@1` genuine mutation
coverage — the certificate-tampering operators would run against its payloads
and theory digests instead of only `nd@1`'s. It was built and verified (27
mutants, all passing the generator's verified-by-construction gate) and then
**reverted**, because it grows the seeded suite **541 → 568** and
`fixtures/mutants/` is frozen input row 1: that is a v5 → v6 re-cut plus a full
axis-(c) re-run, which that landing did not budget. It rides the next freeze
cycle, recorded in the v6 snapshot above. `ord@1` shipped under the same constraint and likewise
has no mutation base._

## What T5 is (and is not)

**T5 definition of done**: commit the fixture set, corpus sample,
and generator seeds before final measurement runs — the deterministic analogue
of the proposal's blinded held-out freeze. Final numbers come only from
post-freeze runs. T5 does not add checker or corpus content; it locks what T1–T4
and T6 produced and records the reproducibility anchors.

**Scope.** The frozen corpus covers the
LLM-independent axes only: axis (a) mutation/differential testing and the
checker side of axis (c). The human-authored natural-defect ablation and
every LLM-producer / annotator axis (axes b/d) are
**deferred to future work** and are deliberately **not** in this
freeze.

## Frozen inputs

State legend: **Frozen** = pinned for the measurement runs, do not regenerate;
the git tree object SHA is itself the content hash of the tree.

| # | Frozen input | Path | Count | Content anchor (git tree SHA) |
| --- | --- | --- | --- | --- |
| 1 | Seeded mutation suite (verdict + specified-status anchors; includes dedicated Σ-WF and `sigma` codec closeout fixtures, and the localization families) | `fixtures/mutants/` | 541 mutants (494 verdict/status-anchored + 47 codec-reject malformed negatives) | `9c174f459d3fd856d306282d1ceb38891e0beff2` (was `fd7142072d58da4d35642cbad6f144c970627afa` at v4) |
| 2 | Corpus units (T2, hand-lowered M0 sample; `lara-core@0.2` signatures; C04 carries the `ra@1` certificate) | `corpus-units/` | 60 units | `cadb5fa62b9f7f6ace14129f1435e3c32b2dff7b` (was `1dc20ea9d79adb2690731a66216dae828a100cf3` through `@0.6`; the `@0.7` re-pin is source-only — see the note below) |
| 3 | Worked examples (golden verdicts, both drivers; 11 measured examples plus additive demonstrators including S2–S8) | `examples/` | 11 measured examples (+ additive demonstrators) | `34b3451b4afc2a5a30814db8062ea1d69803f9bb` (re-pinned at v5; the post-v4 addenda above record the intermediate moves from `2f7fa9ad…`) |

**Generator seed.** `mutationSeed = 20260801` (`src/Lara/Mutate.hs`,
SplitMix64, keyed per `(base, operator)`). Verified byte-identically
reproducible: `cabal exec -- runghc scripts/gen-mutants.hs` over the committed
tree leaves the generated suite unchanged (541 mutants). CI enforces this
between freezes: the **Generated mutation suite is fresh** step runs
`gen-mutants.hs --check`, so a tree that no longer regenerates its own committed
suite fails before it can reach a measurement run.

**Ablation configs.** `noCQConfig` / `noTypedConfig` / `noConflictScanConfig`
from `Lara.Check.CheckConfig` (`src/Lara/Check.hs`); `fullConfig` is the frozen
semantics. Pinned by the freeze commit SHA below. `noConflictScanConfig` is new
at v5 and adds a third ablation run, so `ablation.{json,tsv}` grows by a
whole run rather than only by rows.

## Reproducibility gates (all green pre-freeze)

| Gate | Command | Result |
| --- | --- | --- |
| Seed reproducibility | `cabal exec -- runghc scripts/gen-mutants.hs --check` | 541 mutants byte-identical (empty generated-suite diff) ✓ |
| Cross-driver differential (positive) | `bash scripts/differential.sh` | pass=620 fail=0 ✓ |
| Cross-driver differential (negative) | `bash scripts/differential.sh` | pass=56 fail=0 ✓ |
| Admission differential | `bash scripts/admission-differential.sh` | pass=20 fail=0 (15 semantic byte-identical + 5 codec rejects) ✓ |
| Replay-tamper detection | `bash scripts/test-replay-tamper.sh` | both tamper classes detected ✓ |
| Lean build | `cd lean && lake build` | green ✓ |
| Lean axiom audit | `cd lean && lake env lean AxCheck.lean \| ../scripts/check-axioms.sh` | `sorry`-free, standard trio (incl. `Lara.RA`) ✓ |
| Test suite | `cabal test all` | green (incl. `AblationSpec`, `ClaimSupportSpec`, Σ closeout coverage, and the site-gating properties) ✓ |
| Freeze-bundle tests | `python3 scripts/test_freeze_bundle.py` | 4/4 ✓ |
| Presentation parity | `make presentation-parity` | 73 rows ✓ |

Every row above is the **v5 freeze-time result**, measured on the clean tree
`89c25ef` on 2026-08-25 with the toolchain recorded under "Measurement
environment of record" below.

The positive differential row tracks the **live** count rather than a
freeze-frozen one: it grows by one per added anchor, and each movement is
recorded in the addenda above (`580 → 581` with S6, `581 → 582` with S7,
`582 → 583` with S8). This cycle moved it `583 → 620`, exactly the 37 new
mutants and no more — which is the same additivity the empty pre-existing-bytes
diff claims, measured from the other side.

The recipe numbers under "Reproduce from scratch" below are **scoped to the tag
they name and must not be refreshed** to track later movement: reproducing from
`m5-freeze-v5` checks out a tree in which exactly these anchors exist.

## Post-freeze measurement run

Command (one command, manifest-driven discovery):

```
cabal exec -- runghc scripts/measure.hs
```

Emits `measurements/{report,ablation}.{json,tsv}` over 601 inputs (541 mutants +
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
| Measurement records | 601 (541 mutants + 60 corpus units) |
| Class match (`actual` = `expected`) | 601 / 601 |
| Cross-driver agreement (`lean_agree`) | 601 / 601 |
| Location match (where applicable) | 436 / 436 (165 n/a: accepts — incl. the 9 `quarantine-attacker` mutants — and codec failures) |
| Location primary (`location_primary`) | 436 / 436 |
| Replay success (corpus units) | 60 / 60 |
| Claim-support (4): load-bearing strict steps carrying a checked certificate | 1 / 1 (`adaptive-pruning/C04`) |
| Ablation **no-cq** missed rejections | 18 — all `reject-IncompleteArgument` (surgical) |
| Ablation **no-typed** missed rejections | 35 — 11 `reject-R10` + 19 `reject-R11` + 5 `reject-MissingConflict` (surgical) |
| Ablation **no-conflict-scan** missed rejections | 5 — all `reject-MissingConflict` (surgical) |

**`no-typed` was not redefined when the flags split.** `CheckConfig`
gained `ccConflictScan` beside `ccTypedAttacks`, but `noTypedConfig` still
clears **both**, because it is the paper's "nodes and arbitrary attack edges"
baseline and narrowing it would silently change what an already-published number
means. So no pre-existing row changed its ablation outcome: `no-typed` moved
30 → 35 purely by missing the five new `drop-covering-attack` mutants, which is
correct for a baseline that requires no completeness. The isolating cell is the
new `no-conflict-scan` run. The monotonicity invariant `accept(fullConfig) ⊆
accept(cfg)` still holds for all three and is asserted over every manifest input
by `test/AblationSpec.hs`'s `prop_monotonicity`.

**Location-match caveat.** `location_match` is ≈100% by construction and
stays that way. For single-defect rows a reject can only localize at its mutated
constituent; and every site of the `localization` operator family (post-v4
trees) — off-site and multi-defect alike — is gated against the checker by
`prop_siteMatchesChecker` / `prop_localizationSites` before it reaches
`MANIFEST.tsv`, so a mislocating ground truth fails CI at generation time
instead of lowering the rate. The 436/436 above therefore verifies the harness
and the answer key, not localization accuracy, and the discriminating families
do **not** turn it into a number that can move. What they add is a
stronger gate — ground truth re-derived from the mutant rather than echoed from
the edit site — plus the ordering claim `location_primary`, reported separately.
The headline is not quotable as localization evidence at all; cite the gate.
Contract and rationale in `docs/localization-metric-decision.md`.

**`lara-core@0.2` re-freeze.** The suite grew from 369 to 496 mutants: the
signature family adds 107 `reject-R2` rows (five operators, one per clause of
the amended class) and 20 `reject-R12` rows from `out-of-scope-var`, the witness
for R12's new spec-§4.1 arm. Two diffs were taken across the regeneration
boundary and **both are empty**, which is the measurement this pass claims:

- the `MANIFEST.tsv` `expected`-column diff over the 369 pre-existing rows, and
- the verdict-and-status diff over all 60 corpus `expected.json` files.

The empty first diff is the design commitment behind the `lara-core@0.2` re-freeze paying off: every
symbol-injecting operator now extends its mutant's carried Σ, so a mutant tests
the class it seeds rather than incidental signature noise.
`measurements/binding-audit/**` is **frozen input, excluded from regeneration**
(decision D-5); the pre-regeneration byte-compare of the recomputed
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

v5's `report.{json,tsv}` carries **17 columns, of which 1–15 are deterministic**;
columns 16–17 (`hs_check_ns`, `lean_wall_ns`) are wall-clock timing (reported,
environment-dependent, **not** frozen). `ablation.{json,tsv}` carries no timing
and is fully deterministic. The reproducibility anchors below hash only the
deterministic content.

The projection widened at v5. `report.tsv` gained the deterministic
`location_primary` column after `location_match`
(`docs/localization-metric-decision.md`), so the projection is `cut -f1-15`
where v1–v4 used `cut -f1-14`. `test/MeasureSpec.hs`'s `prop_reportColumnOrder`
pins the header verbatim and pins `location_match` and `location_primary` apart
on a synthetic record, which is what makes this field numbering executable
rather than prose — a silent column swap would keep the arity identical while
mislabelling every `cut -f` consumer, this document included.

| Frozen output anchor | SHA-256 |
| --- | --- |
| `report.tsv` deterministic projection (`cut -f1-15`) | `d7396558022965c842e51bb223dce9ef6753325d2a638c2753558239e99aaff0` |
| `ablation.tsv` (full, deterministic) | `503c231a2e9759c1207cbf48dbb9b446466c84237b2cdac2091a26de85821c1b` |

Superseded v4 anchors, retained as provenance (`cut -f1-14`, 564 records):
`report.tsv` `eae0c82e8c1607a4daf74b8dfb8ecab333996f0e213bcbf22f9b81533add3d7a`,
`ablation.tsv` `23112189212d4e6e154fafa4a7a2d9425e9d77de2b228702f3bf52b29859cdc3`.
Both remain correct for the tree `m5-freeze-v4` names.

Measurement environment of record: GHC 9.14.1, Lean 4.32.0, darwin/aarch64
(recorded in `report.json` `environment`).

## Freeze commit and tag

- **v1 tag:** `m5-freeze-v1` (annotated), on `300b235` (the T5
  freeze merge commit) — the M1 analogue is `spec-v0.1`.
- **v2 freeze commit:** `68e7298` (merge commit of the `ra@1` certifier change). The tag
  was not cut at merge time; it was cut retroactively alongside v3.
- **v2 tag:** `m5-freeze-v2` (annotated), on `68e7298`.
- **v3 snapshot commit:** `4d5c6ae` (measurement run at clean `3108a5f`).
- **v3 tag:** `m5-freeze-v3` (annotated), on `62eea92` (merge commit of the v3
  re-freeze).
- **v4 snapshot commit:** `ced19fe` (clean measurement input and environment
  recorded in `report.json`).
- **v4 tag:** `m5-freeze-v4` (annotated), on `f4327b4` (merge commit of the v4
  re-freeze). Cut after main CI run `31463095876` passed on the
  benchmark-harness repair that preceded it.
- **v5 snapshot commit:** `89c25ef` (clean measurement input and environment
  recorded in `report.json`: `git-dirty: false`, GHC 9.14.1, Lean 4.32.0,
  darwin/aarch64).
- **v5 tag:** `m5-freeze-v5` (annotated), on `5dd326b` (merge commit of the v5
  re-freeze). Cut after the evaluation-suite completion batch landed and all
  gates above were re-run green on the snapshot tree. Verified at the tag before
  cutting: the three frozen-input tree SHAs and both output anchors reproduce
  the values recorded above exactly. CI could not corroborate — GitHub Actions
  was not running any job in this window (account billing), so every gate result
  in this document is a local run on the environment of record.
- Post-freeze rule: any change to a frozen input (rows 1–3) or the seed
  invalidates this freeze; re-run the gates and cut the next tag. **Every number
  in this document describes v5 and the working tree it was measured on.** Two
  mechanisms keep that true between freezes rather than by trust: CI's
  `gen-mutants.hs --check` step fails a tree that no longer regenerates its own
  committed suite, and the generator's string-keyed streams
  (`src/Lara/Mutate/Seed.hs`) make a *new* operator additive by construction, so
  intermediate PRs may grow `fixtures/mutants/` without owing a measurement run.
  The bytes do move, however, if an enumerator's output is **reordered** or an
  existing operator is **renamed** — `pickWithStream` draws in candidate-list
  order — so neither is a cosmetic edit and both invalidate the freeze.

## Reproduce from scratch

Reproduce v5 from the annotated tag:

```
git checkout m5-freeze-v5
cabal build all
cabal exec -- runghc scripts/gen-mutants.hs   # empty generated-suite diff (541 mutants)
bash scripts/differential.sh                  # positive 620/0, negative 56/0
cabal exec -- runghc scripts/measure.hs       # regenerates measurements/ (601 records)
cabal exec -- runghc scripts/claim-support.hs # claim-support aggregation
cut -f1-15 measurements/report.tsv | shasum -a 256   # matches anchor above
shasum -a 256 measurements/ablation.tsv               # matches anchor above
```

The v4 recipe is recoverable from the `m5-freeze-v4` tag itself; against that
tree the projection is `cut -f1-14`, the suite is 504 mutants, and the
differential reads positive `580/0`.

## Clean-tree verification (M7 task T7)

T7 is the exit criterion that the artifact reproduces the frozen numbers **from a
fresh clone**, not from a working tree. The re-freeze half of T7 is done (the v3
re-freeze produced it; v4 followed); the written clean-clone record is
**deferred to the artifact/release stage** by researcher decision —
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
(set -o pipefail; cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
cabal test all --test-show-details=direct
python3 scripts/test_freeze_bundle.py -v      # 4/4
cabal exec -- runghc scripts/measure.hs
cut -f1-15 measurements/report.tsv | shasum -a 256   # must equal the anchor above
shasum -a 256 measurements/ablation.tsv              # must equal the anchor above
```

The projection line above is v5's. For a `<tag-or-branch>` at v4 or earlier it
is `cut -f1-14` (the determinism note above), against that freeze's own anchor.

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
