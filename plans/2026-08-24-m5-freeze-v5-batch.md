# m5-freeze-v5 batch — evaluation-suite completion

> **Status (2026-08-24): live, Tasks 1–2 landed (#154, #124); Tasks 3–4 remain.**
> Three code tasks plus one shared refreeze cycle. Delete this file once Task 4
> lands and `m5-freeze-v5` is cut; move anything durable into
> `docs/m5-freeze-checklist.md` first. Update this line as each task lands.

## Where this sits

No milestone is open in this repository. M0–M5 are closed (#48), M6 is partial
by design — axes (a)/(c) measured and frozen, the LLM-dependent axes (b)/(d)
deferred to the ACL/EMNLP follow-up (#52, #30) — and M7 left the repo on
2026-08-24 when #60 closed, moving paper and submission-package work to the
paper repository. `plans/research-proposal.md` §7 is now a record rather than a
worklist; `docs/engineering-plan.md` §0 carries the module-level state.

What remains here is issue-tracked work, and this batch is the largest open
piece of it. The current core is `lara-core@0.2`, the authoring surface is
`lara-syntax@0.10`, and the evaluation corpus stands at `m5-freeze-v4` (504
mutants + 60 corpus units = 564 measured inputs). This plan takes it to v5.

## Scope decision

Run issues #123, #124, #125 now, as one regeneration cycle cutting
`m5-freeze-v5`. Researcher decision, 2026-08-24: get the evaluation as complete
as possible for the submission rather than protect the PLDI window.

This sets aside the deferral recorded in #78 ("an M5-scale refreeze ... must not
happen inside the PLDI window") and the post-freeze note in
`docs/m5-freeze-checklist.md`, which names the `drop-covering-attack` and
`wrong-fraction` operators as deferred. Both records get updated in Task 4.

That deferral was protecting drafting time against a regeneration cycle, and
**that contention no longer lives in this repository**: #60 (the M7 paper-package
tracker) was closed 2026-08-24 as completed, "because paper-writing and
submission-package work is tracked in the paper repository, not in the LARA code
repository." The window argument is therefore weaker than #78 states, and this
batch is a code-repo change that no longer competes with the write-up.

**Milestone naming.** M5 closed long ago (tracker #48). The `m5-freeze-v*` series
is a legacy name for the *evaluation-corpus freeze*, and its last three re-cuts
were unrelated to M5: v2 for the `ra@1` certifier (#57), v3 for conservative
quarantine reporting (#76/#79), v4 for the `lara-core@0.2` signature bump (#89).
See the open question below before cutting v5.

**#126 is excluded and stays gated.** It requires the possible-worlds design
decision (are eval settings worlds?), which is a follow-up-paper direction, and
the issue specifies the human pass is *merge-and-name*, not authoring. Labelled
`future-work` on 2026-08-24. It is not blocked on this batch and this batch is
not blocked on it.

## Why the code splits but the freeze does not

The expensive, batch-worthy step is the regeneration cycle: re-run `measure.hs`
and `claim-support.hs`, re-run every gate in the checklist, update
`measurements/frozen/`, rewrite the three tree SHAs and the headline numbers,
cut the tag. That happens **once**, in Task 4.

The three code diffs are unrelated to each other (a certificate operator, a
checker-config split, a metric-semantics change) and land as three reviewable
PRs. Two facts make this safe:

- **Streams are string-keyed.** `Lara.Mutate.Seed.streamFor` keys on
  `base ++ "/" ++ opName op` (`src/Lara/Mutate/Seed.hs:53-54`), not on the
  `MutationOp` enum index. A new constructor cannot perturb an existing
  operator's stream wherever it sits in the enum — the same additivity v3 relied
  on ("no existing mutant's bytes changed").
- **CI does not gate `gen-mutants.hs`.** `.github/workflows/ci.yml` runs
  `differential.sh` and `admission-differential.sh` only, so intermediate PRs
  regenerate `fixtures/mutants/` additively without owing a measurement run.

Caveat carried from `src/Lara/Mutate/Seed.hs:11-14`: `pickWithStream` draws in
candidate-list order, so **reordering an enumerator's output or renaming an
operator moves bytes**. No task below may reorder `certPayloadSites` or rename
an existing operator.

## Task 1 — #125 wrong-fraction `ra@1` operator (branch `mutate/125-wrong-fraction-cert-operator`)

Separates "the checker rejects garbage" from "the checker rejects a
plausible-looking but false certificate". Today only `OpCertPayloadTamper`
exists, and it substitutes `SAtom "mut_corrupt"`
(`src/Lara/Mutate/Sites.hs:304-306`) — structurally malformed, so it exercises
the decoder, not the value check.

`Lara.Strict.RA` is built for exactly this distinction
(`src/Lara/Strict/RA.hs:20-21`): the payload is lowest terms with `Q > 0`, one
wire form per value, so *a well-formed payload carrying a different value is a
replay rejection (R13), not a decode failure*.

Steps:

1. Add `OpCertWrongFraction` to `MutationOp` (`src/Lara/Mutate.hs:85-128`).
   Append at the end of the certificate group; the enum derives
   `(Eq, Ord, Show, Enum, Bounded)`, so `opName` (`:144`) and the family table
   (`:191`) are exhaustiveness-checked and will fail to compile until both are
   filled in. Spelling: `"cert-wrong-fraction"`, family
   `"certificate-tampering"`.
2. Add `certWrongFractionSites` to `src/Lara/Mutate/Sites.hs`, modelled on
   `certPayloadSites` (`:295-306`) but restricted to `ra@1` assurance cells.
   Rewrite only the `(frac P Q)` node of a `(radrop _ _ (frac P Q))` payload,
   leaving the two `prem` slots intact.
3. Derive the wrong value **deterministically from the true one**, not a
   literal: `P/Q -> (P+1)/Q` renormalized to lowest terms. This always changes
   the value and always stays decodable. For C04's real certificate
   `(radrop (prem 0) (prem 1) (frac 119 500))`
   (`corpus-units/adaptive-pruning/C04/unit.core.sexp`) that yields
   `(frac 6 25)` — `120/500` reduced — i.e. `0.24` against the true
   `119/500 = 0.238`.
4. Expected verdict `ExpectClass R13`, located at `CArgument ix`.
5. Register in both places in `src/Lara/Mutate/Suite.hs`: `unitMutants` at
   `:71`-adjacent and `unitSweep` at `:194`-adjacent, both immediately after
   the `OpCertPayloadTamper` line.
6. Regenerate additively: `cabal exec -- runghc scripts/gen-mutants.hs`.

Verification for this PR: `cabal build all`; `cabal test all`; confirm the
generated diff is **additive only** (`git diff --stat fixtures/mutants/` shows
no modified pre-existing mutant); confirm the new mutant decodes cleanly and
rejects at R13 rather than failing the codec — the whole point of the operator
is that it gets past the decoder.

**Manifest ordering — checked, not a risk.** `fixtures/mutants/MANIFEST.tsv` is
written in suite-builder order, which is per base following the registration
order in `Suite.hs` (its first row is `A--undeclared-leaf-0.sexp`, matching
`OpUndeclaredLeaf` as the first registration at `:61`). Registering the new
operator after `OpCertPayloadTamper` therefore *inserts* rows mid-block rather
than appending them, and `measure.hs` — being manifest-driven — reflects that in
`report.tsv`.

That is diff noise, not a correctness problem. Existing mutant *files* stay
byte-identical (string-keyed streams), `MANIFEST.tsv` is a generated index whose
growth is the intended outcome, and the pinned `cut -f1-14 report.tsv` hash moves
at any refreeze by construction — a new hash is v5's deliverable. Keep the
logical grouping with the other certificate operators; do not reorder
registrations to chase a tidier diff, since `Lara.Mutate.Seed` warns that
reordering an enumerator's output moves bytes.

## Task 2 — #124 standalone conflict-scan ablation

Result 7 (attack completeness, mechanized in #18 — `docs/mechanization-plan.md:50`,
`:255`) currently has **no isolating ablation cell**, because
`firstMissingConflictInfo` is folded into `ccTypedAttacks`. The fold is visible
in the field's own comment (`src/Lara/Check.hs:193-197`): one flag governs both
the per-attack typing and the completeness scan. The manifest carries zero
expected-`MissingConflict` rows today.

Steps:

1. Split `CheckConfig` (`src/Lara/Check.hs:188-199`): keep `ccTypedAttacks` for
   the per-attack `checkAttack` typing, add `ccConflictScan` for the
   `firstMissingConflictInfo` completeness scan.
2. `fullConfig = CheckConfig True True True` (`:202-203`); add
   `noConflictScanConfig` beside `noCQConfig` / `noTypedConfig` (`:206-211`) and
   export it (`:53-55`).
3. Preserve the monotonicity invariant asserted at `:184`
   (`accept(fullConfig) ⊆ accept(cfg)`) — a third flag must still only *remove*
   a rejection arm.
4. Add a `drop-covering-attack` operator (enum + `opName` + family + sites +
   both `Suite.hs` registrations, as in Task 1), expected
   `reject-MissingConflict`.
5. Extend the ablation partition in the measure harness to the third dimension.

Note this task is additive for *mutants* but **not** for *ablations*:
`ablation.tsv` gains a whole third run.

**How the published cells actually moved (measured in the Task 2 PR).** The
flags were split, but `noTypedConfig` was NOT redefined: it still drops the
whole typed-attack bundle, because it is the paper's "nodes and arbitrary attack
edges" baseline and redefining it would silently change what a published number
means. So no existing row changed its ablation outcome. The cells moved only by
the five new mutants: **no-cq 18 → 18**, **no-typed 30 → 35** (the baseline
misses the new rows too — correct, it requires no completeness), and the new
isolating cell **no-conflict-scan = 5**, all `reject-MissingConflict`. The cost
is that `no-typed` now flips two partition buckets rather than one, so
`ablationConfigs` carries a bucket *list* per run.

**Open question — resolved (2026-08-24, in the Task 2 PR): Haskell only, and no
Lean entry is owed.** `CheckConfig` has no counterpart anywhere in `lean/`
(no hit for `CheckConfig`, ablation, or the inclusion), which is consistent with
the type's own contract — it "exists only at the checker boundary" and never
reaches the kernel or the wire. The Lean development mechanizes the *frozen*
semantics, i.e. `fullConfig` alone. The inclusion is pinned in Haskell by
`test/AblationSpec.hs`'s `prop_monotonicity`, over every manifest input. A new
flag therefore owes an `AxCheck.lean` entry only if it changes what `fullConfig`
accepts — which by construction it must not. Recorded at the definition site in
`src/Lara/Check.hs`.

## Task 3 — #123 discriminating localization benchmark

Runs **last**: it is the only task that changes a metric definition, and its
multi-defect families should be able to compose with Task 2's new operator.

`location_match` is ≈100% by construction. Ground truth is a single
`imExpectedLocation` compared by equality
(`src/Lara/Measure.hs:229-234`), and the code says so in its own comment:
"single-defect rejects localize at the mutated constituent by construction".
The frozen snapshot reports 399/399 (`docs/m5-freeze-checklist.md:276`).

Steps:

1. **Decide the metric first, before generating anything.** With multi-defect
   mutants the ground truth becomes a *set* of constituents, so "match" needs a
   definition: must the checker name the constituent it should report first
   (diagnostic-ordering is then part of the claim), or does any seeded site
   count? Write the decision into `docs/` — it is a measurement contract, not an
   implementation detail.
2. Widen `imExpectedLocation` from `Maybe Constituent` to the chosen
   representation; update `detLocationMatch` (`src/Lara/Measure.hs:229-234`).
3. Add the multi-defect and off-site mutant families.
4. Keep the existing single-defect rows interpretable under the new metric — the
   400-odd existing rows must not silently change meaning.

## Task 4 — the single refreeze cycle

Tracked as **#156**. Only after Tasks 1–3 have landed.

1. `cabal exec -- runghc scripts/gen-mutants.hs` — final suite, seed unchanged
   at `20260801`.
2. Re-run every gate in `docs/m5-freeze-checklist.md:227-240`: seed
   reproducibility, cross-driver differential (positive + negative), admission
   differential, replay-tamper, `lake build`, axiom audit (`sorry`-free,
   standard trio), `cabal test all`, freeze-bundle tests.
3. `cabal exec -- runghc scripts/measure.hs` and
   `cabal exec -- runghc scripts/claim-support.hs` from a **clean tree**
   (`report.json` must record `git-dirty: false`).
4. Update `measurements/frozen/`.
5. Update `docs/m5-freeze-checklist.md`: new re-freeze history paragraph, three
   tree SHAs, mutant/input counts, headline numbers, and the deterministic
   projection hashes at `:317`. Rewrite the post-freeze rule at `:338` — it
   currently names the two operators from Tasks 1–2 as deferred.
6. Cut annotated tag `m5-freeze-v5` on the merge commit.
7. Update the "Reproduce from scratch" recipe to the v5 tag and its counts.

Records to update outside the checklist: #78's gated-scope block (the
refreeze-window argument no longer holds), and the `refreeze-batch` label
description (it points at v5; retire or re-point it once cut).

## Deferred / excluded

- **#126** — gated on the possible-worlds design; `future-work`.
- **#52, #30** — `post-pldi`, ACL/EMNLP follow-up. Unaffected.

## Caveat owed regardless

Even with Task 3 landed, the write-up owes an explicit statement of what
`location_match` measures. The ≈100%-by-construction caveat currently exists
**only** in issue #123's body: it appears nowhere in `docs/` or `plans/`, and
`docs/m5-freeze-checklist.md:276` reports `399 / 399` with no such note.

The results section itself now lives in the paper repository (#60, closed
2026-08-24), so this repository cannot discharge the obligation — it can only
carry it. Record the caveat next to the headline number in
`docs/m5-freeze-checklist.md` so the number is not quotable without it. If Task 3
slips, that note is the minimum.

## Open question — the tag name

Cutting a fifth tag is the natural moment to decide whether the series keeps its
legacy name.

- **Keep `m5-freeze-v5`.** v1–v4 are published, addressable anchors and
  `docs/m5-freeze-checklist.md` is named for them; a mid-series rename means
  "the freeze after v4" has two names, which is exactly the confusion a
  reproducibility anchor exists to prevent.
- **Rename** to something milestone-neutral (`corpus-freeze-v5`), and note in
  the checklist that it succeeds `m5-freeze-v4`. Buys a name that will not keep
  drifting as the repo moves past M7.

**Recommendation: keep `m5-freeze-v5`, and add one line to the checklist saying
the "m5" prefix is legacy — the series is the evaluation-corpus freeze, not an
M5 deliverable.** The rename is not cosmetic-cheap: `m5-freeze` appears 112
times across ~30 files, and two of those locations make it actively expensive.
`corpus-units/corpus-v1.policy.lara:5` — a **frozen input**, row 2 of the freeze
— references `docs/m5-freeze-checklist.md` by path, so renaming the checklist
either changes frozen corpus bytes for a cosmetic reason or leaves a dangling
pointer inside the frozen set. `measurements/frozen/mechanical-reviews.md` and
the `ara/trace/` session records carry the name as *history*, which should not be
retro-edited at all.

Researcher's call, but the evidence points one way. Everything else in this plan
is unaffected either way.

## ARA

This batch crosses the CLAUDE.md threshold ("materially changes an existing
feature ... or runs or interprets an experiment"). Run `/research-manager` at the
end of the qualifying session, not per-PR.
