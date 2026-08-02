# M5 — T1 corpus half + T3 measurement harness (tracker #48)

Branch `m5-t1corpus-t3`. Scope: the open half of T1 (mutation generators over
the corpus units, generated mutants exercising every status and attack kind)
and T3 (the axis-(c) measurement harness). They land together because they
interlock: the generator records the seeded ground truth (defect class +
location) that the harness scores the checker's diagnostics against. T5
(freeze) and T6 (ablations) follow separately.

## T1 corpus half — generators over the corpus units

### Bases

Corpus bases come from `corpus-units/MANIFEST.tsv` (manifest-driven, never by
glob), anchors `corpus-units/<artifact>/<claim>/unit.core.sexp`. Base label in
the mutant manifest: `<artifact>.<claim_id>` (the `.` separator cannot collide
with the `--` operator separator; artifact names already contain `-` and `_`).
Worked-example bases and their mutants are unchanged.

### Operator sweep and the per-operator unit budget

The existing operators run unchanged over corpus bases; site enumeration
already makes them self-gating (a gap unit has no args, so arg-dependent
operators propose nothing there — no special casing). **One uniform sweep
rule, derived from site enumeration — no hand-maintained operator
partition** (eng review 2026-08-01, D9): for each operator, enumerate the
applicable bases (those with ≥1 site); if the applicable set has ≤ B bases,
take all of them (full coverage, subsumes the "full sweep" case); otherwise
the SplitMix64 stream keyed by the operator picks **B = 12** bases from the
applicable set. Cap 1 mutant per (base, op) throughout. The regenerated
`fixtures/mutants/README.md` records measured per-operator applicable and
selected counts (no silent caps), so the suite's composition is documented
by measurement, never by a classification that can drift from the code.

Why derived, not declared: the review found the draft's hand-partition wrong
on both sides — `undeclaredLeafSites` rewrites a leaf reference *inside a
declared argument* (arg-dependent: sites on the 12 arg-bearing units only,
9 justified + 3 defeated), while `hiddenContrarySites` ignores the unit and
always offers one policy-image site (universal: 60 applicable bases, needs
the budget). The uniform rule makes such misfilings impossible.

Cert operators (cert-theory-swap, cert-payload-tamper) find no sites — corpus
units carry no strict certificates — and contribute nothing over corpus bases;
their coverage stays with the S1 worked example. Recorded here, asserted
nowhere (site enumeration handles it).

### Status/attack-kind mutants — the new operator family

#48 requires generated mutants exercising **every status and every attack
kind** over corpus units. The rejection operators cannot do this (they produce
rejects); a new family of *accept-verdict* operators over the 9 justified
corpus units, each constructed against `corpus-v1`'s licensing (the E4/E5
construction templates, instantiated per unit). The family lives in a new
module `src/Lara/Mutate/Accept.hs` (eng review D6/3C): `Lara.Mutate` is
already 820 lines against the 400-line module rule, so new code lands in a
new right-sized module importing `Mutant`/seeding/manifest helpers, and the
legacy module gets zero churn in this PR (full split is a TODOS.md
follow-up).

| operator | construction | specified status of the queried claim |
| --- | --- | --- |
| `drop-support` | remove the claim's args, keep claim + leaves (E2-style) | `gap` |
| `attach-undercut` | attacker arg via the rule's undercut-licensing exception | `defeated` |
| `attach-rebut-cycle` | attacker arg on a symmetric contrary pair; attack completeness mandates the mutual edge → 2-cycle | `contested` |
| `attach-undermine` | attacker arg targeting a premise-leaf occurrence, contrary declared one-directionally in the injected extension | `defeated` (via undermine) |
| `attach-reinstate` | `attach-undercut` + a second undercut defeating the attacker (E4-style) | `justified` (under attack) |

Notes pinned by the E4/E5 findings (mutation-suite plan, 2026-08-01):
undercuts are voluntary (exceptions are outside the completeness scan), so
one-directional defeat is expressible; a symmetric contrary FORCES the mutual
rebut edge, so rebut mutants specify `contested`, never `defeated`. Where a
construction needs vocabulary `corpus-v1` lacks, the mutant injects it as a
hidden-extension-style *declared* extension in the unit's policy image —
legal, since these mutants must ACCEPT; nothing is smuggled past R1/R12.
**Injection is the common case, not an undermine special case** (eng review
D13): only 3 of the 9 justified units query a predicate with a declared
`corpus-v1` contrary (`better`; the others query `holds`,
`holds_analytically`, `contributes`, `code_property`), so `attach-rebut-cycle`
needs an injected symmetric contrary pair (plus the contrary predicate's
vocabulary) on 6 of 9 units, and `attach-undermine` injects its
one-directional contrary everywhere.

The construction templates assume — and generation ASSERTS, with a clear
message (eng review D13/OV-11) — that each justified corpus unit has exactly
one supporting argument for the queried claim: `justified` is "some complete
support arg in", so `attach-undercut → defeated` holds only under this
invariant. A future multi-arg unit must fail the assertion loudly, not
surface as a confusing verification abort.

New `Expected` variant: `ExpectPrimaryStatus Status` (manifest spelling
`accept-<status>`), carrying the constructed attacker's identity, verified at
generation and in `MutationSpec` **structurally, not just by final status**
(eng review D7/4A — status-only verification passes vacuously on a no-op
`attach-reinstate`, whose specified status equals the base status): the
verdict accepts, the queried claim's status is exactly the specified one, AND
the per-operator label shape holds — `attach-undercut`/`attach-undermine`:
attacker arg present and IN, target OUT; `attach-rebut-cycle`: both
mutual-edge endpoints undec; `attach-reinstate`: attacker present and OUT
with its own undercutter IN; `drop-support`: no args remain for the claim.

### Verification (same three-layer discipline as the worked-example half)

- `scripts/gen-mutants.hs`: reads corpus bases from the corpus manifest,
  verifies every mutant against `runCheck` before writing (class-exact for
  rejects, status-exact **plus the 4A structural label assertions** for the
  new family, pinned diagnostics for codec).
- `test/MutationSpec.hs`, extended coverage assertions: every rejection class
  witnessed by ≥1 *corpus-based* mutant (where sites exist); every status in
  {justified, gap, defeated, contested} and every attack kind
  {rebut, undercut, undermine} witnessed by ≥1 generated corpus mutant;
  the 4A structural assertions re-verified; **budget assertion**: per
  operator, selected-base count = min(applicable, B = 12) and the README's
  measured counts match the manifest (no silent caps).
  Freshness (seeded reproducibility) unchanged, now spanning corpus bases.
- `scripts/differential.sh`: no change needed — both mutant halves are
  already discovered from `fixtures/mutants/MANIFEST.tsv`; the new rows ride
  along. Every mutant byte-identical across drivers, Lean as oracle.

## T3 — measurement harness

### Ground truth: the `expected-location` manifest column

**One location vocabulary, shared by seeded ground truth and located
diagnostics** (eng review D4/1A — no parallel SiteRef type):
`Lara.Diagnostics.Constituent`, extended with the variants the corpus
operators need — a replay-envelope constituent (ground truth for
`duplicate-backend`/`unknown-backend`) and a group constituent (for
`group-conflict`); `CConflictPair` keeps its pair shape. One render/parse
table in `Lara.Diagnostics` owns the manifest spelling (symbolic-core rule);
`location_match` is `Eq` on the type.

Because replay-preflight R13 and the §4.3 group check reject in
`Lara.Driver` *before* `checkUnit` (Driver.hs:76-77) and never become a
`UnitError`, `locate` alone cannot cover them. Add
`Driver.runCheckLocated :: CheckInput -> (Verdict, Maybe LocatedRejection)`
unifying all three reject paths — preflight, group check, `checkUnit` — so
every reject carries a located constituent from the same path that produced
its class; `runCheck` becomes its projection. **Regression property
(critical, iron rule):** `runCheck ≡ fst . runCheckLocated` over every input
discovered from both manifests, asserted in `MeasureSpec`.

Extend `Mutant` with `mutantSite :: Maybe Constituent`, rendered as the new
`expected-location` manifest column — **appended as column 8, never inserted
earlier**: `differential.sh` hardcodes `$5` (expected, lines 132-133) and
`$6`/`$7` (diagnostic pins, lines 346-347). Rows with no seeded site
(corpus units, accept-family mutants, codec mutants) render `-`. Note the
threading is mechanical but module-wide: every site enumerator in
`Lara.Mutate` returns `(Expected, Unit -> Unit)` today and gains a site
payload — not a drop-in column.

**Generation does NOT gate on location** — `gen-mutants.hs` keeps verifying
the class only. Location agreement is a *measured* quantity: if the checker's
first-failure ordering locates a different constituent than the mutated one,
that is an honest data point for the paper's location-accuracy number, not a
generation failure. Framing (eng review D10): this is a *verification-style*
number — single-defect mutants localize at the mutated constituent by
construction, so ≈100% is the expected result and any deviation is a
diagnostic-ordering finding; it is not a discriminating benchmark. The
discriminating variant (multi-defect, off-site manifestation) is recorded as
a T6 TODO, out of scope here.

### `src/Lara/Measure.hs` + `scripts/measure.hs`

Metrics logic is a pure library module (record types, metric computation,
JSON/TSV rendering via `ExpectedJson.JValue` — no aeson, house codec style);
the script does IO, subprocesses, and timing. Inputs are the two manifests
(`fixtures/mutants/MANIFEST.tsv`, `corpus-units/MANIFEST.tsv`); discovery is
manifest-driven, never by glob.

Per-run record (one row per mutant + one per corpus unit). Every column is
defined for **both manifest regimes** — verdict-bearing rows and
codec/malformed rows (eng review D5/2A + D13/OV-3); `-` marks a column
outside a row's domain:

- **identity**: input path, base, family, operator (`-` for corpus units),
  expected outcome;
- **rejection outcome**: verdict-bearing rows: actual class via
  `runCheckLocated`; `class_match` against expected. Codec rows:
  `class_match` = `decodeCheckInputFile` fails AND the failure contains the
  manifest's pinned `hs-diagnostic` (any-failure is not enough — the
  deletion-sensitivity pin carries into the metric);
- **defect location**: located constituent from `runCheckLocated` (rejects
  only); `location_match` against `expected-location`; `-` on accept rows
  and codec rows;
- **cross-driver agreement** (`lean_agree`), two regimes mirroring
  `differential.sh`'s split on the expected column: verdict-bearing rows —
  Lean stdout byte-equal to `printSExpr (encodeVerdict v) ++ "\n"` (the
  exact `app/Main.hs:158` rendering, reused from `Lara.Wire`, not
  re-derived) and Lean exit code equal to the outcome-derived code
  (0 accept / 1 reject); codec rows — Lean exits 2 with empty stdout and
  stderr containing the manifest's pinned `lean-diagnostic`;
- **replay success** (#36 tuple): **corpus units only** (`-` on mutant rows,
  which carry no pinned replay identity — self-comparison would be a
  tautology): second run byte-identical and the carried tuple equals the
  unit's pinned replay identity (`replay_ok`);
- **certificate size**: three columns — total input bytes on disk,
  policy-section rendered bytes, and payload bytes (total − policy) — the
  fixed ~6-7KB `corpus-v1` policy image dominates totals, so payload is the
  distribution-bearing number (eng review D11); the policy-bytes convention
  (rendered bytes of the policy subtree) is documented in the report schema;
- **checking time**: wall-clock via `GHC.Clock.getMonotonicTimeNSec` (base,
  no new dep). `hs_check`: in-process, decode excluded, and the timed
  section **forces the fully rendered verdict text** (length-seq of
  `printSExpr (encodeVerdict v)`) — timing an unforced lazy `runCheck` call
  measures thunk allocation, ~0ns (eng review D8/5A). `lean_wall`: subprocess
  wall time, which includes process startup + decode. The report schema
  labels the two as **different protocols, not comparable** — no cross-driver
  time ratio may be derived from them. Codec rows: decode-failure wall time,
  reported as its own column. Median of 5 runs, all 5 retained in the JSON.

`scripts/measure.hs` preflights the Lean side the way `differential.sh` does
(eng review D13/OV-10): run `lake build` (or verify
`lean/.lake/build/bin/lara-driver` exists and is current) and fail loudly
with a build hint if absent — never a mid-run subprocess error. The smoke
run makes on the order of 2,000 Lean subprocess invocations (~400 rows × 5
timed runs); acknowledged, still cheap (minutes).

Output: `measurements/report.json` (full records + an aggregate block:
per-class accuracy, location-accuracy rate, replay success rate, size/time
distributions over both total and payload bytes) and
`measurements/report.tsv` (flat, the paper's table generator input), plus an
environment block (git rev + dirty flag, GHC/Lean versions, OS, CPU) per the
reproducibility rule. Rendering stays `ExpectedJson.JValue` (house codec, no
library deps); the *test-side* JSON parse uses **aeson as a test-suite
dependency only** (D12 — an independent, established parser is a stronger
check on the house renderer than a hand-rolled dual; `src/` stays
base+containers). `measurements/` is **gitignored** in this PR: pre-freeze
numbers are development output; committed measurement records are T5's
post-freeze deliverable, from this harness, unchanged.

### Verification

`test/MeasureSpec.hs` runs the library path (no subprocess, no timing) over
both manifests and asserts the deterministic columns: every mutant's actual
class/status equals its specified one (re-derivation of the MutationSpec
invariant through the measurement path — the harness must not disagree with
the test suite), `replay_ok` on all corpus units (and `-` on mutant rows),
report JSON parsed by aeson (test-dep) + TSV round-trip through a real TSV
parser, aggregate counts consistent with the manifests. Additional spec
coverage from the eng review:

- **`runCheck ≡ fst . runCheckLocated`** over every manifest-discovered
  input (critical — regression guard on the D4/1A driver refactor);
- the `lean_agree` comparison functions are pure and unit-tested against
  synthetic stdout/exit/stderr fixtures for **both regimes**, including
  mismatch cases (the spec never spawns a subprocess, so without this the
  comparison logic ships untested);
- the median/timing-statistics helpers unit-tested (median of 5, retention
  of all samples);
- the `Constituent` render/parse manifest-spelling table round-trips.

Timing and Lean-subprocess columns are exercised by a harness smoke run in
CI-adjacent usage (`bash scripts/differential.sh` remains the cross-driver
gate — and runs in CI, ci.yml:105), not pinned by the spec test.

## Execution order

1. `Constituent` extension + render/parse table + `Driver.runCheckLocated`
   (with the `runCheck ≡ fst . runCheckLocated` regression property) +
   `expected-location` appended as manifest column 8 + manifest/README
   regeneration for the existing worked-example suite (no new mutants yet);
   `MutationSpec` freshness green. Note: threading `mutantSite` changes every
   site-enumerator return type in `Lara.Mutate` — mechanical but module-wide.
2. Corpus bases into `gen-mutants.hs` (manifest-driven), rejection-operator
   sweep under the uniform derived-applicability rule (B = 12); regenerate;
   `MutationSpec` corpus-coverage + budget assertions; `differential.sh`
   green over the enlarged suite.
3. The status/attack operator family in `Lara.Mutate.Accept` over the 9
   justified units (`ExpectPrimaryStatus` + 4A structural verification +
   single-support-arg generation assertion); regenerate; full T1 coverage
   assertions green.
4. `Lara.Measure` + `scripts/measure.hs` (lake-build preflight) +
   `MeasureSpec` (incl. the pure `lean_agree` fixtures and timing-stat
   units); smoke run; inspect `report.json` aggregates by hand once.
5. `cabal test all` + `bash scripts/differential.sh`; execution record added
   here; TODOS.md updated: M5 note (T1 closes; T3 closes; T5/T6 remain),
   retire the stale #36 entry (closed by 100f5b8), add the
   `Lara.Mutate` full-split follow-up, add the T6 off-site/multi-defect
   localization follow-up.

## Exit (T1 + T3 slices of #48)

- Generators run over the corpus units; every rejection class (where corpus
  sites exist), every status, and every attack kind is exercised by generated
  corpus mutants; all byte-identical across drivers.
- Seeded ground truth (class + location) recorded per mutant in the manifest.
- One command emits the machine-readable axis-(c) report (rejection outcome,
  defect class + location vs. ground truth, replay success, certificate size,
  checking time) the paper's tables are generated from.
- Lean side: no new metatheory — generator and harness are corpus tooling;
  soundness coverage remains the Lean driver + differential harness.

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | `/codex review` | Independent 2nd opinion | 1 | ISSUES_FOUND (outside voice, Claude subagent — Codex spend cap) | 12 findings, all resolved: 1 HIGH (operator partition factually wrong → derived-applicability rule), 11 MED/LOW folded |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | CLEAR | 11 issues, 0 critical gaps — all decisions folded into this plan (D3–D15) |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | — |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | — |

- **CROSS-MODEL:** one tension — outside voice argued location-accuracy is near-circular; resolved (D10) by keeping the metric, reframing it as verification-style (≈100% expected), and deferring discriminating cases to a T6 TODO. All other outside-voice findings were complementary and verified against code before folding.
- **VERDICT:** ENG CLEARED — ready to implement (commit 372e430, 2026-08-01).

NO UNRESOLVED DECISIONS

## Execution record (2026-08-01)

Implemented via `/implement` (subagent-driven, two-stage spec + quality review per
step; both gates PASS on every step). Branch `m5-t1corpus-t3`.

| Step | Commit | Delivered |
|------|--------|-----------|
| 1 | `11c5c2a` | `Lara.Diagnostics` located-rejection vocabulary (`CReplayEnvelope`/`CGroup`, `constituentText`/`parseConstituent`), `Driver.runCheckLocated` (all three reject paths), `runCheck = fst . runCheckLocated`, `Mutant.mutantSite` + `expected-location` manifest column 8. |
| 2 | `74176cf` | Corpus rejection sweep — uniform derived-applicability rule (B=12) over the 60 corpus units; `corpusSweepReport` (measured applicable/selected, no silent caps); 148 → 295 mutants. |
| 3 | `2e02829` | `Lara.Mutate.Accept` — five accept-verdict operators over the 9 justified units; `ExpectPrimaryStatus`; 4A structural verification; 295 → 340 mutants. |
| 4 | `510b5ff` | `Lara.Measure` + `scripts/measure.hs` + `MeasureSpec` — the one-command axis-(c) report; aggregate with per-class accuracy + size/time distributions. |
| 5 | (this) | Final verification, TODOS + plan record, PR. |

**Final verification:** `cabal test` PASS (all suites, incl. the new MutationSpec
corpus/accept/coverage/budget properties and the 7 MeasureSpec properties);
`scripts/differential.sh` green (positive pass=398, negative pass=54 —
byte-identical across the Haskell and Lean drivers over the whole enlarged
suite). Smoke run of `scripts/measure.hs`: 400 records, class-match 400/400,
lean-agree 400/400, location-accuracy 246/246 (the ≈100% verification-style
number D10 predicted), replay 60/60; payload median 841 B under the ~7 KB policy
image (D11).

**Exit met:** generators run over the corpus units; every rejection class (where
sites exist), every status, and every attack kind is exercised by generated
corpus mutants, all byte-identical across drivers; seeded ground truth (class +
location) is recorded per mutant; one command emits the machine-readable
axis-(c) report. No new Lean metatheory (generator + harness are corpus tooling,
per the plan). T5 (freeze) and T6 (discriminating localization) remain, tracked
in `TODOS.md`.
