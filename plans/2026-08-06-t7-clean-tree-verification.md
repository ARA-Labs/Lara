# T7 clean-tree verification and the m5-freeze-v3 re-freeze

> **Scope (M7 tracker #60, task T7).** Verify that the artifact reproduces the
> frozen numbers from a clean checkout: differential, replay, and axiom gates
> green against the frozen anchors. **Precondition discovered while planning:**
> the anchors are stale. The `m5-freeze-v3` re-freeze that #76 (PR #79)
> deferred to its merge commit was never run — `fixtures/mutants/` grew
> 360 → 369 at `a7fdb29`, but `measurements/frozen/` still holds the v2
> snapshot (420 records) from before that merge. T7 therefore has two parts:
> complete the v3 re-freeze first, then verify from a clean tree against the
> refreshed anchors. Also backfilled here: the `m5-freeze-v2` tag and freeze
> commit were never recorded (the checklist still reads `<FILL-AFTER-MERGE>`,
> and `git tag` lists only `m5-freeze-v1` and `spec-v0.1`).

> **Status update (2026-08-06).** Tasks 1–3 executed on this branch (all gates
> green; v3 snapshot `4d5c6ae`). Tasks 4–5's clean-clone verification record is
> **deferred to the artifact/release stage** by researcher decision (see the
> #60 comment): artifact evaluation runs post-submission, so the formal record
> is produced with artifact packaging (T6). Correction from execution: Task 1's
> bare `bash scripts/replay.sh` is wrong — the script requires a `BUNDLE_DIR`
> argument, so the replay gate must iterate over `bundles/`; replay coverage
> here came from `test-replay-tamper.sh` plus the harness `replay_ok` column
> (60/60). Tag cutting from Task 5 still happens at merge.

**Goal:** `measurements/frozen/` matches the current frozen inputs
(369 mutants + 60 corpus units = 429 records), `docs/m5-freeze-checklist.md`
records v3 with new anchors, and a written verification record shows every
reproducibility gate green from a fresh clone.

**Non-goals:** no checker, corpus, or mutant content changes; no new gates.
This is measurement refresh + bookkeeping + verification only. If any gate
fails, stop and diagnose — do not adjust anchors to match observed output.

**Expected number changes (from the #76 fix-branch verification recorded in
the checklist's pending-v3 note):** mutants 360 → 369 (9 new
`quarantine-attacker` accept-family mutants, one per justified corpus unit),
measured records 420 → 429, differential positive 418 → 436, negative 54
(unchanged). `corpus-units/`, `examples/`, `bundles/`,
`measurements/frozen/claim-support.*`, and the pinned running-example reports
are expected byte-identical (nothing frozen declares a duplicate-report group,
so nothing frozen reports `evidence-blocked`).

---

## Task 1: Pre-flight gates on this branch

All gates must be green *before* the measurement refresh, on an up-to-date
`main` ancestor (this branch forks from `aaa9a21`).

**Steps**

```bash
cabal build all && (cd lean && lake build)
cabal exec -- runghc scripts/gen-mutants.hs   # expect: empty git diff (369 mutants reproduce)
bash scripts/differential.sh                  # expect: positive 436/436, negative 54/54
bash scripts/admission-differential.sh        # expect: 20-file manifest, 15 semantic + 5 codec-reject
bash scripts/replay.sh                        # expect: 60/60 corpus units
bash scripts/test-replay-tamper.sh            # expect: tamper detected
(cd lean && lake env lean AxCheck.lean) | scripts/check-axioms.sh   # expect: sorry-free, standard trio
cabal test all --test-show-details=direct     # expect: green
python3 scripts/test_freeze_bundle.py -v      # expect: 4/4
```

**Acceptance:** every command exits 0 with the expected counts; `git status`
clean after `gen-mutants.hs`. No commit from this task.

---

## Task 2: v3 measurement refresh

**Files**
- Modify: `measurements/frozen/report.json`, `measurements/frozen/report.tsv`
- Modify: `measurements/frozen/ablation.json`, `measurements/frozen/ablation.tsv`
- Verify unchanged: `measurements/frozen/claim-support.{json,tsv}`,
  `measurements/frozen/running-example.txt`, `measurements/frozen/mechanical-reviews.md`

**Steps**

```bash
cabal exec -- runghc scripts/measure.hs        # regenerates measurements/{report,ablation}.{json,tsv}
cabal exec -- runghc scripts/claim-support.hs  # claim-support aggregation
```

1. Confirm the working `measurements/report.tsv` has 429 records with
   `class_match` 429/429 and `lean_agree` 429/429; confirm ablation cells are
   still surgical (no-cq 18 `reject-IncompleteArgument`; no-typed 30 =
   11 `reject-R10` + 19 `reject-R11` — the 9 new accept-family mutants must
   not perturb the ablation families; if they do, stop and diagnose).
2. Confirm claim-support output is byte-identical to the frozen copy
   ((4) = 1/1 unchanged).
3. Copy the refreshed `report.{json,tsv}` and `ablation.{json,tsv}` into
   `measurements/frozen/` and record the new anchors:

```bash
cut -f1-14 measurements/frozen/report.tsv | shasum -a 256   # new deterministic projection
shasum -a 256 measurements/frozen/ablation.tsv              # new full-file anchor
```

Note: `report.json` `environment` embeds `git rev-parse HEAD` and a dirty
flag, so the snapshot must be produced from a **clean** branch commit; the
recorded SHA will be this branch's head (an ancestor of the merge commit),
matching the v2 precedent where the snapshot was produced on the PR branch.

**Commit**

```bash
git add measurements/frozen/
git commit -m "measure(m5-freeze-v3): post-#76 snapshot — 429/429 class-match, 429/429 lean_agree"
```

---

## Task 3: Checklist bookkeeping (v3 record + v2 backfill)

**Files**
- Modify: `docs/m5-freeze-checklist.md`

**Steps**

1. Move the "Pending re-freeze (`m5-freeze-v3`)" paragraph into the re-freeze
   history block as the v3 entry, recording: cause (#76 `quarantine-attacker`
   operator), suite 360 → 369, records 420 → 429, and the snapshot commit SHA
   from Task 2.
2. Update the frozen-inputs table: mutant count and the new
   `fixtures/mutants/` git tree SHA (`git rev-parse HEAD:fixtures/mutants`);
   verify rows 2–3 tree SHAs are unchanged and leave them as-is.
3. Update the reproducibility-gates table (differential 436/436, 54/54; add
   the `admission-differential.sh` row introduced by #81) and the headline
   numbers table (429s; location-match and status-diversity counts as
   observed in Task 2).
4. Replace the two frozen-output anchor hashes with the Task 2 values.
5. Freeze commit and tag section: backfill the v2 freeze commit (`68e7298`,
   merge commit of PR #59) and note the `m5-freeze-v2` tag is cut
   retroactively alongside v3; add the v3 line with
   `<FILL-AFTER-MERGE>` for the merge commit.
6. Update the "Reproduce from scratch" block: `git checkout m5-freeze-v3`,
   differential 436/0 + 54/0, and the new hash anchors.

**Commit**

```bash
git add docs/m5-freeze-checklist.md
git commit -m "docs(m5-freeze-v3): record re-freeze, backfill v2 freeze commit"
```

---

## Task 4: T7 clean-tree verification run

The M7 exit criterion proper: everything reproduces from a **fresh clone**,
not the working tree. Run after Tasks 1–3 so the anchors being verified are
the v3 anchors.

**Files**
- Create: `docs/t7-clean-tree-verification.md` (verification record)

**Steps**

1. Fresh clone into the session scratchpad (clone the local repo at this
   branch's head; the published record cites the merge commit after landing):

```bash
git clone --branch t7-clean-tree-verification ~/repos/ara/lara "$SCRATCH/lara-t7"
cd "$SCRATCH/lara-t7" && git submodule update --init
```

2. Run the full gate sequence from Task 1, plus the anchor checks:

```bash
cut -f1-14 measurements/report.tsv | shasum -a 256   # must equal the v3 projection anchor
shasum -a 256 measurements/ablation.tsv              # must equal the v3 ablation anchor
```

   (Regenerated working output vs. committed frozen anchors — this is the
   byte-identity claim in #60's exit criteria.)

3. Write `docs/t7-clean-tree-verification.md`: date, clone source commit,
   environment of record (GHC, Lean, OS/arch), the gate table with observed
   counts, and the two matched hashes. Explicitly note wall-clock columns
   (`hs_check_ns`, `lean_wall_ns`) are environment-dependent and excluded by
   the deterministic projection.

**Acceptance:** every gate green in the fresh clone; both hashes match the
committed v3 anchors; the record documents exact commands and outputs.

**Commit**

```bash
git add docs/t7-clean-tree-verification.md
git commit -m "docs(t7): clean-tree verification record — all gates green from fresh clone (#60)"
```

---

## Task 5: Land and tag

**Steps**

1. Open the PR (base `main`) with the gate table in the description; merge on
   green CI.
2. On the merge commit: fill the v3 `<FILL-AFTER-MERGE>` SHA in the checklist
   (follow-up commit or amend before merge if using a merge commit is not
   desired), then cut the annotated tags:

```bash
git tag -a m5-freeze-v2 68e7298 -m "M5 freeze v2 (retroactive): 420-record snapshot after #57 ra@1"
git tag -a m5-freeze-v3 <merge-sha> -m "M5 freeze v3: 429-record snapshot after #76 conservative reporting"
git push origin m5-freeze-v2 m5-freeze-v3
```

3. Tick T7 on #60 and note the headline-number change (420 → 429) so the
   draft's results section (T4) and any doc citing 420/420 are updated in the
   draft-sync pass. Repo-side texts to sweep: `TODOS.md`, `README.md`,
   issue #60/#78 body text, `tables/` (regenerate `make bench` only if
   `tables/performance.tex` states the harness size).

---

## Risks and stop conditions

- **Any pre-flight gate red on this branch** → stop; #79/#81 regressions are
  a bug-fix task, not part of this plan.
- **Measurement disagrees with the expected 429/429** → stop; the pending-v3
  note's fix-branch numbers were verified pre-#81, so a mismatch implicates
  #81 and needs diagnosis before any anchor is written.
- **Ablation families perturbed by the new mutants** → stop; the paper's
  ablation claim ("surgical") is load-bearing.
- **Frozen bytes outside `report/ablation` change** (claim-support,
  running-example, bundles, corpus trees) → stop; the #76 zero-frozen-bytes
  property was the basis for fixing it inside the PLDI window.
