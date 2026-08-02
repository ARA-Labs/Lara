# M5 — T6 ablation baselines (tracker #48)

Branch `feat/m5-t6-ablation-baselines`. Scope: the last open task of M5 — the
two deterministic Phase F ablations (`popl-research-review.md` §5 / §7,
`research-proposal.md` §7): **LARA without typed attacks** and **LARA without
critical-question obligations**, run through the T3 harness against the same
corpus units and generated mutants the full system already scores. The
deliverable is the axis-(a)/Phase F evidence for two paper claims:

- *Typed attacks catch bad-defeat certificates an untyped-edge checker accepts.*
  (`popl-research-review.md:303`)
- *Critical-question obligations expose omissions schema validation misses.*
  (`popl-research-review.md:304`)

No new Lean metatheory: like the T1 generator and T3 harness, ablation configs
are **evaluation tooling, Haskell-only**. Soundness stays with the frozen full
pipeline (Lean driver + `differential.sh`), which this task leaves byte-for-byte
untouched. The T5 freeze then covers the ablation config definitions and any
seeds; final ablation numbers come only from post-freeze runs.

The intended scope for this paper is the **seeded-mutant** ablation: the mutants
carry a controlled defect class, so the result is confirmatory-by-construction
— each cell demonstrates *that the named rule is load-bearing* (every seeded
defect of its class is caught only by that rule), not defect-diversity or
discovery. The paper table must be captioned accordingly (eng review D10; the
discriminating version over natural defects is #52).

Out of scope (recorded, not built here): the LLM-producer baselines (schema-only
JSON, unconstrained LLM graph/prose) — deferred to the ACL/EMNLP paper per #48;
the discriminating multi-defect / off-site **localization** benchmark — the
separate T6 follow-up already in `TODOS.md`; the **human-authored-certificate
ablation** (same two configs over natural, un-seeded defects — the discriminating
form) — deferred to the ACL/EMNLP follow-up as **#52**; and the **standalone
completeness (conflict-scan) ablation** for result 7 — recorded in `TODOS.md`
(eng review D11), since this task folds the scan into the typed-attack bundle
(D9, below). All kept out to hold the diff reviewable and the paper scope
LLM-independent.

## Design decision: config parameter, not input transform

The code map (`src/Lara/`) confirms there is **no checker-config record today**;
behavior is hardcoded through direct arguments (`Driver.hs`, `Check.hs`,
`Attack.hs`). Two ways to realize an ablation:

- **(A) `Unit → Unit` pre-transform in the harness** (least plumbing). Rejected.
  An ablation must *disable a check*, but transforming the input to remove a
  feature *triggers other checks*: deleting mandatory-question declarations makes
  a certificate that discharges them fail R5 (undeclared-discharge) instead of
  passing No-CQ; there is no untyped-attack constructor to rewrite `Undercut`/
  `Undermine` into without inheriting `Rebut`'s contrary obligation
  (`AST.hs:417-421`). A transform turns "skip this check" into "a different
  defect," which measures the wrong thing.
- **(B) a `CheckConfig` threaded into the checker, defaulted to full** (chosen).
  Semantically clean — the config names exactly the rules to skip — and keeps
  the symbolic-core rule (CLAUDE.md): a closed record, not a stringly-typed flag.

### The config

New record in `Lara.Check` — closed, composable; every consultation site lives
in `Check.hs`, so no new module and no import cycle (eng review D8):

```haskell
data CheckConfig = CheckConfig
  { ccObligationGate :: Bool   -- enforce the open-obligation gate (Check.hs:178-179)
  , ccTypedAttacks   :: Bool   -- enforce the typed-attack bundle (Check.hs:202, Check.hs:290)
  }

fullConfig  :: CheckConfig     -- CheckConfig True  True  — the frozen semantics
noCQConfig  :: CheckConfig     -- fullConfig { ccObligationGate = False }
noTypedConfig :: CheckConfig   -- fullConfig { ccTypedAttacks   = False }
```

**Every existing call site keeps `fullConfig` and its current behavior.** The
wire envelope never carries a config: `CheckConfig` is neither encoded nor
decoded, so the Lean driver and `differential.sh` see the same fixed pipeline
they do today (map §F, option 1).

```
                 CheckInput
                     │
        runCheckLocatedWith cfg          (Driver.hs — cfg defaulted fullConfig)
                     │
     R13 preflight ──┤  (never ablated)
     R9 group ───────┤  (never ablated)
                     ▼
        checkUnit cfg                    (Check.hs — ALL cfg sites live here)
          ├─ dup rules, R12 policy       (never ablated)
          ├─ checkArguments cfg
          │    ├─ inferSupport           (UNTOUCHED kernel — R3..R7 incl. R5/R6)
          │    └─ obligation gate ◄──────── ccObligationGate   (No-CQ skips)
          ├─ checkAttacks cfg
          │    ├─ R1 endpoints           (never ablated)
          │    └─ checkAttack call ◄─────── ccTypedAttacks     (No-typed skips)
          └─ firstMissingConflictInfo ◄──── ccTypedAttacks     (No-typed skips)
                     ▼
        buildAccept → statuses           (byte-identical whenever full accepts)
```

### What each ablation skips (all sites in `Check.hs`; kernel untouched)

- **No-CQ** (`ccObligationGate = False`): at `checkArguments`
  (`src/Lara/Check.hs:178-179`) skip the `PEIncompleteArgument` rejection when
  `srObligations result` is non-empty. The argument becomes a complete node
  despite an open mandatory CQ (a declared **hole**), flows into
  `completeClaimFor` (`Grounded.hs:138-146`), and the defective claim gets a
  status where the full system rejected the certificate outright. **All of R5
  and R6 stay ON** — including the `Uncovered` arm: a certificate that *silently*
  drops a discharge is a structural/schema defect the ablated baseline still
  catches. The ablation removes exactly the check that schema validation cannot
  express: a schema-valid certificate whose mandatory question is explicitly
  left open (`(holes …)` is wire-well-formed, `Wire.hs:641,664-666`). This is
  the precise shape of the `popl-research-review.md:304` claim (eng review
  D3→D8: the earlier draft's plan to also skip `Uncovered` was rejected — it
  over-ablates optional-question coverage and would push a config parameter
  into `inferSupport`, the documented Lean-mirror kernel).
- **No-typed** (`ccTypedAttacks = False`): skip the **typed-attack bundle**, the
  baseline `popl-research-review.md:280` calls "nodes and arbitrary attack
  edges" (eng review D9):
  1. the `checkAttack` call at `Check.hs:202` — kind-specific target typing
     (rebut→declared-contrary R10/R11, undercut→matching-exception,
     undermine→leaf-contrary). Skipping the whole call is behavior-equivalent
     to skipping only `checkAttackTarget`: the source's `inferSupport` is
     redundant there, since stage 4 (`checkArguments`) already inferred every
     declared argument. `Attack.hs` is byte-untouched.
  2. the contrary-driven completeness scan `firstMissingConflictInfo` at
     `Check.hs:290` — an arbitrary-edge checker has no contrary-table scan
     either, and (verified) the seeded rebut-retarget mutants would otherwise
     re-reject here instead of flipping (`Mutate.hs:686-688`, `Compile.hs:83-85`).

  Endpoint *declaration* (R1, `Check.hs:197-201`) stays ON — an attack still
  has to reference real arguments. `checkedAF`/`runtimeAF` and their parity
  cross-check are untouched — the scan is a rejection arm; AF construction
  never consults it (`Compile.hs:101-106`). The coverage-collapse variant
  (positional → whole-term), which would shift statuses, stays a follow-up.

Both flags only ever *remove* rejections, giving the invariant the tests
assert: **accept-set monotonicity** — `accept(full) ⊆ accept(ablation)`.

## Mutation-suite addition: the hole-seeding operator (pre-freeze)

The manifest today has **zero** inputs that reach the obligation gate: the
existing `open-obligation` operator drops a discharge *without* a hole
(`Mutate.hs:600-606`), which fires `CE_R5 Uncovered` — a check that stays ON.
The gap is in the mutation suite, not the checker (eng review D8), and T5 has
not frozen it. Add to `Lara.Mutate`:

- **`OpHoleObligation`** — replace one *mandatory* discharge with a declared
  hole (site enumerator: clone of `openObligationSites` swapping the entry into
  `hs` instead of deleting it). The mutant is schema-valid (R5 coverage holds:
  question covered by the hole), and the full system rejects it only at the
  obligation gate → expected **`reject-IncompleteArgument`** — a new manifest
  spelling for the existing `Rejection` constructor (`AST.hs:591`;
  `rejectionText` already renders it; extend `Measure.parseExpected` /
  `Expected` with the non-R-class arm). Family: `open-obligations`.
- Regenerate the suite with `scripts/gen-mutants.hs` (deterministic); the PR
  diff over `fixtures/mutants/` must be **additions-only** (existing fixtures
  byte-identical) — assert by inspection in the execution record.
- `MutationSpec` gains the operator witness, per suite convention.
- Bonus coverage: `differential.sh` (manifest-discovered) now exercises the
  `IncompleteArgument` reject path **cross-driver for the first time** — the
  Lean driver must spell the same verdict, which the differential gate proves.

## Harness integration (T3 reuse)

Entry point: add `runCheckLocatedWith :: CheckConfig -> CheckInput -> (Verdict,
Maybe LocatedRejection)` in `Lara.Driver`, identical to `runCheckLocated`
(`Driver.hs:91-110`) except it passes the config to `checkUnit`; define
`runCheckLocated = runCheckLocatedWith fullConfig` and `runCheck =
fst . runCheckLocated`. Preflight (R13) and group (R9) paths are not ablated and
ignore the config. Thread `CheckConfig` through `checkUnit` →
`checkProgramDetailed` → `{checkArguments, checkAttacks, conflict-scan site}`
(`Check.hs:337-355`, `275-293`, `167-183`, `186-204`) — mechanical, ~5
functions, **all in `Check.hs` + `Driver.hs`**; `Attack.hs`, `SupportTerm.hs`,
`Compile.hs` untouched; every boundary defaults to `fullConfig` so no other
caller changes.

Measurement (`src/Lara/Measure.hs`, `scripts/measure.hs`):

- Extract a small shared core — decode + `runCheckLocatedWith cfg` + outcome
  text (`actualText`) + codec-row handling — so `computeDeterministic`
  (`Measure.hs:152-194`) becomes its `fullConfig` projection with **bit-stable**
  `report.{json,tsv}`, and the ablation pass is a thin second projection (eng
  review D6: the codec-row rule and outcome spelling exist once).
- Add `computeAblation :: CheckConfig -> InputMeta -> String -> AblationCell`
  producing, per (input, config): the ablation's verdict/outcome text, and
  `missed_reject :: Bool` (full rejects, ablation accepts). **No `status_shift`
  column** — provably vacuous, since the config only removes rejections: on
  full-accepts the ablation path is byte-identical (eng review D5). The
  informative datum on a missed reject is the ablation's **accept class**
  (`accept-justified` vs `accept-gap` — the former is the paper's alarming
  case), which the cell records via the shared outcome text.
- New aggregate `AblationReport`: per (ablation × expected class) the count of
  full-system rejects the ablation misses, with accept-class breakdown, plus
  the expected-surgical check (all other classes unchanged). Emit
  `measurements/ablation.json` + `measurements/ablation.tsv` (the paper's
  ablation-table input), same house `ExpectedJson.JValue` codec, same env
  block. `measurements/` stays gitignored (T5 owns committed post-freeze
  numbers).
- Lean is invoked only for the full-config `lean_agree`/timing
  (`measure.hs:118-130`) — left as-is. Ablations are Haskell-only by
  construction. Add an **`--ablation-only`** mode to `scripts/measure.hs` that
  skips the Lean sampling and emits only the ablation report, so the smoke loop
  is seconds, not the full timing sweep (eng review D10).

### Class partition (drives the per-ablation table + surgical assertion)

Partition on the **typed** `Expected` values `Lara.Mutate.parseExpected` already
produces from the manifest's `expected` column (341 lines = header +
340 data rows; not a prose family list — the spelling table is
`parseExpected`/`rejectionText`, and hand lists drift,
`hand_partitioned_operator_lists_drift`):

- **`reject-IncompleteArgument`** (the new hole-seeding mutants) → No-CQ must
  flip these reject→accept, and leave every other row byte-identical.
- **`reject-R10` / `reject-R11`** (bad-attack-targets: `bad-attack-position`,
  `unlicensed-attack`) → No-typed must flip these reject→accept, and leave
  every other row byte-identical.
- **Everything else** — `reject-R1/R3/R4/R5/R6/R7/R9/R12/R13`, `codec-reject`
  (decode fails before any config is consulted — unchanged by definition), and
  all `accept-*` rows (monotonicity: identical path) — unchanged under both
  ablations.

Totality is asserted in the spec: every `Expected` value present in either
manifest lands in exactly one bucket, so a future class or spelling cannot
silently fall outside the partition.

## Verification

`test/AblationSpec.hs` (new), pure — no subprocess, no timing — over both
manifests (`fixtures/mutants/MANIFEST.tsv`, `corpus-units/MANIFEST.tsv`):

- **Full-path guard**: `runCheckLocatedWith fullConfig ≡ runCheckLocated` over
  every manifest-discovered input. This is *definitional* once the alias is
  written (eng review D10) — it guards against a future non-aliased divergence,
  but the real regression net for the refactor is the existing suites, the
  bit-stable `report.{json,tsv}`, and CI-enforced `differential.sh`.
- **Accept-set monotonicity**: for each ablation, every input the full system
  accepts is accepted with the identical outcome by the ablation.
- **No-CQ surgical (strict)**: every `reject-IncompleteArgument` mutant flips
  reject→accept under `noCQConfig`; every other reject row rejects identically
  (same class). The cell's recorded outcome text makes any violation
  immediately diagnosable (eng review D4).
- **No-typed surgical (strict)**: every `reject-R10`/`reject-R11` mutant flips
  reject→accept under `noTypedConfig` (satisfiable by construction now that the
  conflict scan is in the bundle — D9); every other reject row rejects
  identically.
- **Codec rows**: unchanged under every config — decode fails before the
  checker; asserted explicitly, not implied.
- **Non-triviality**: each ablation misses ≥1 reject, and the `AblationReport`
  counts match the manifest partition (no silent gaps).
- **Partition totality**: every `Expected` in both manifests lands in exactly
  one bucket.
- **Renderer shape**: `ablation.{json,tsv}` renderers produce the declared
  columns (house `JValue` codec round-trip on a small report).
- **Accept-class recording**: a known hole-mutant flip records the expected
  accept class (e.g. a justified base's omission mutant → `accept-justified`).
- **Hand-written hole unit**: one minimal in-spec unit with a declared hole —
  full rejects `IncompleteArgument`, `noCQConfig` accepts — a fast witness
  independent of the generated manifest.
- `MutationSpec`: the `OpHoleObligation` witness (operator produces its
  expected class), per suite convention.

`bash scripts/differential.sh` — must stay green: all pre-existing rows
byte-identical (proves the config refactor didn't touch the full path; wire
format unchanged), and the regenerated manifest's new hole-mutant rows agree
cross-driver (first differential coverage of the `IncompleteArgument` path).
This is the soundness gate; the ablations ride entirely above it. CI enforces
it on every push.

Smoke: `cabal exec -- runghc scripts/measure.hs --ablation-only`, then inspect
`measurements/ablation.tsv` by hand once — confirm No-CQ misses exactly the
`IncompleteArgument` rows and No-typed exactly the R10/R11 rows, with their
accept classes; then one full run to confirm `report.{json,tsv}` are unchanged
from pre-refactor.

## Execution order

1. `CheckConfig` + `fullConfig`/`noCQConfig`/`noTypedConfig` in `Lara.Check`;
   thread through `checkUnit`/`checkProgramDetailed`/`checkArguments`/
   `checkAttacks` with the flags gating **only** the three named sites
   (`Check.hs:179`, `:202`, `:290`); `Driver.runCheckLocatedWith` +
   `runCheckLocated = …With fullConfig`. Land with existing suites and
   `differential.sh` green **before** any ablation behavior is measured — this
   step is a pure, behavior-preserving refactor.
2. `OpHoleObligation` in `Lara.Mutate` + the `reject-IncompleteArgument`
   spelling in `Measure.Expected`/`parseExpected`; regenerate via
   `scripts/gen-mutants.hs`; `MutationSpec` witness; verify the fixture diff is
   additions-only and `differential.sh` is green over the new rows.
3. `Lara.Measure`: shared core, `computeAblation`, `AblationCell`/
   `AblationReport`, the partition, JSON/TSV renderers; the full `AblationSpec`
   property list above.
4. `scripts/measure.hs`: emit `measurements/ablation.{json,tsv}` alongside the
   existing report; `--ablation-only` mode; env block; hand-inspect the smoke
   run once.
5. `cabal test all` + `bash scripts/differential.sh`; execution record here;
   `TODOS.md` already updated in review (D11 completeness-ablation follow-up;
   localization-benchmark and `Lara.Mutate`-split follow-ups kept — note the
   new operator makes the split marginally more pressing).

## Exit (T6 slice of #48)

- Both deterministic ablations (`no typed attacks`, `no CQ obligations`) run
  through the T3 harness over the frozen corpus + regenerated mutants; one
  command emits a machine-readable ablation report the paper's table is
  generated from.
- Each ablation's missed-rejection set is exactly its mapped classes
  ({`IncompleteArgument`} / {R10, R11}) — surgical — and every ablation accepts
  a superset of the full system (monotone). The paper claims this as
  **rule-is-load-bearing evidence over seeded defects** (three operator
  templates × bases, confirmatory-by-construction); the discriminating claim
  belongs to #52.
- Full pipeline byte-identical across Haskell and Lean (`differential.sh`,
  CI-enforced), now including the hole-mutant rows; no new Lean metatheory —
  ablation configs are evaluation tooling; the `inferSupport` kernel is
  byte-untouched.
- Hand-off to T5: the ablation config definitions and the regenerated mutation
  suite (incl. `OpHoleObligation`) are inputs to the freeze; final numbers come
  from post-freeze runs.

## Execution record (2026-08-01)

Implemented via `/implement` in four reviewed commits (spec-compliance +
code-quality review per step, all PASS), plus this close-out:

1. `a58a6fa` — `CheckConfig` + `fullConfig`/`noCQConfig`/`noTypedConfig`
   threaded through `Check.hs`/`Driver.hs`; gates at exactly the three named
   sites. One structural deviation from the plan text: `checkUnit` kept its
   3-arg signature and gained a `checkUnitWith` sibling (mirroring
   `runCheckLocated`/`runCheckLocatedWith`), because `checkUnit` has callers in
   `ExpectedJson.hs` and `test/RuntimeSpec.hs` that the plan requires
   untouched. Reviewed and accepted.
2. `30bf673` — `OpHoleObligation` (family `open-obligations`, expected
   `reject-IncompleteArgument`; sites are mandatory discharges only, so every
   mutant rejects exactly at the obligation gate). Suite regenerated 340→358:
   18 new mutants (6 worked-example bases A, B, E1, E3, E4, E5 + 12/12
   applicable corpus units). **Additions-only verified by inspection**:
   18 new `.sexp` files, `MANIFEST.tsv` +18/−0, zero existing fixture files
   modified (README diff is regenerated counts only). Generator determinism
   confirmed (repeat runs byte-identical). `Expected`/`parseExpected` live in
   `Lara.Mutate` (the plan's "Measure.parseExpected" named the consumer);
   `detLocationMatch` gained the one-line `ExpectIncompleteArgument` arm so the
   seeded `arg:N` column keeps round-tripping.
3. `a8a1e78` — shared `rowOutcome` core; `computeDeterministic` is its
   `fullConfig` projection — bit-stability proven by rendering
   `report.{json,tsv}` over all 418 inputs before/after and `cmp`
   (byte-identical). `computeAblation`/`AblationCell` (no `status_shift`, per
   D5), total `ablationBucket` partition (compile-time total over `Expected` —
   no wildcard), `ClassSummary`/`AblationReport`, `ablation.{json,tsv}`
   renderers on the house `JValue` codec. `AblationSpec`: 10 pure properties
   over both manifests, all green.
4. `2cb743c` — `scripts/measure.hs` emits `measurements/ablation.{json,tsv}` in
   both modes; `--ablation-only` skips the Lean preflight, the timing sweep,
   and `report.{json,tsv}` (~2s smoke loop). Reads forced (stock-`ulimit`
   safety). Ablation outputs byte-identical between full and ablation-only
   runs.

Measured (smoke, pre-freeze — final numbers come from post-freeze runs per T5):

- No-CQ misses **18** rejects — exactly the `reject-IncompleteArgument` rows
  (accept classes: 10 `accept-justified`, 4 `accept-defeated`,
  1 `accept-all-contested`, 3 `accept-other`).
- No-typed misses **30** rejects — exactly the `reject-R10` (11) +
  `reject-R11` (19) rows.
- Zero changed rows outside the 48 misses (surgical); all full-accepts
  byte-identical under both ablations (monotone).

Final gates, run at close-out on the assembled branch: `cabal test all` green
(all suites incl. the 10 `AblationSpec` properties);
`bash scripts/differential.sh` green — `pass=416 fail=0` (398 pre-existing
rows byte-identical + 18 new hole-mutant rows agreeing cross-driver: first
differential coverage of the `IncompleteArgument` path, `lean_agree` 418/418
in the full measurement run), `negative pass=54 fail=0`. `lean/` and the
kernel modules (`Attack.hs`, `SupportTerm.hs`, `Compile.hs`, `Grounded.hs`)
byte-untouched across the branch; `CheckConfig` never appears in `Wire.hs`.

Close-out also: `TODOS.md` Mutate-split note (new operator makes the split
marginally more pressing); `Reporting.hs` module comments qualified with
"under `fullConfig`" (their unconditional phrasing predated `noCQConfig`).

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | `/codex review` | Independent 2nd opinion | 1 | ISSUES ABSORBED | outside voice (Claude subagent fallback): 9 findings, 3 absorbed as D8/D9/D10, rest editorial/verified |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | CLEAR | 11 issues, 0 critical gaps; 9 decisions (D3–D11), all resolved |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | — |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | — |

- **CODEX:** Codex CLI errored (workspace spend cap); outside voice ran as a fresh-context Claude subagent. Its findings 1–4 were verified against the code and reversed two review decisions (D8: hole-seeding operator instead of widening the ablation into the `inferSupport` kernel; D9: fold the conflict scan into the No-typed bundle), and finding 9 added the `--ablation-only` smoke mode (D10).
- **CROSS-MODEL:** Review and outside voice agreed the original No-CQ config measured nothing (0 of 339 mutants); they disagreed on the fix — checker-side widening vs mutation-suite addition — resolved in favor of the outside voice (D8) on verified evidence (Uncovered over-ablates optional questions; third `inferSupport` call site; suite un-frozen until T5; one-script regen).
- **VERDICT:** ENG CLEARED — ready to implement (`/implement plans/2026-08-02-m5-t6-ablation-baselines.md`).

NO UNRESOLVED DECISIONS
