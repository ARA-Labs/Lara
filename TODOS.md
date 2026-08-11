# TODOS

> M3 closed (issue #27, PR #28). M4 closed: the walking-skeleton spine
> (research-proposal.md §7) is satisfied — M4a compiler-on-worked-examples
> (#31, PR #33) and M4b untrusted elaborator + replay bundle (#32, PR #34)
> both landed; the strict-certificate `nd@1` worked example (#39) followed.
> Result 9 (backend replacement) is also complete: PR #41 mechanized the
> uniform-injective-relabel theorem and PR #43 added well-checkedness transport,
> making it non-vacuous by construction.
>
> Next milestone: **M5 — evaluation corpus, deterministic scope** (tracker
> #48; research-proposal.md §7). The paper targets PLDI/POPL and presents the
> core language and its calculus, so M5 covers only the LLM-independent axes:
> axis (a) mutation/differential testing and checker-side axis (c) metrics.
> Its implementation prerequisites are both closed: verdict-carried replay
> identity (#36, the audit story) and duplicate-report groups (#38, the
> mutation-suite spine). All LLM work — the D3 flip and the JSON producer
> (#30, tagged `post-pldi`) — is deferred to an ACL/EMNLP follow-up paper.
> M5 progress: T1 (seeded mutation generators), T2 (corpus units), T3
> (measurement harness), and T4 (worked cases E4/E5) are complete. T1 now
> covers both halves — the worked-example rejection-class sweep AND generators
> over the 60 corpus units (uniform derived-applicability sweep, B=12), with a
> new accept-verdict operator family exercising every claim status and every
> attack kind. T3 emits the one-command machine-readable axis-(c) report
> (`scripts/measure.hs`: rejection outcome, defect location vs ground truth,
> replay success, certificate size, checking time), all byte-identical across
> the Haskell and Lean drivers. T6 (ablation baselines) is complete: the
> `CheckConfig` no-cq / no-typed cells run over the suite, grown 340→358 by
> the hole-seeding `OpHoleObligation` operator. T5 (freeze protocol) is complete:
> `docs/m5-freeze-checklist.md` pins the frozen inputs (358-mutant suite, 60
> corpus units, 11 worked examples, seed 20260801) by git-tree content hash, the
> post-freeze `scripts/measure.hs` run is committed under `measurements/frozen/`,
> and tag `m5-freeze-v1` marks the #55 merge commit. Issue #57 then exercised
> the strict/certificate path: the registered `ra@1` rational-arithmetic
> backend (both drivers + Lean metatheory), the strict Family-10
> `rational_drop_recheck` rule in corpus-v1, and `adaptive-pruning/C04`'s
> certificate-checked derived-arithmetic arg — growing the suite 358→360
> (cert tamper/theory-swap now exercised on the corpus) and re-freezing as
> `m5-freeze-v2` (420 records, class-match 420/420, `lean_agree` 420/420,
> claim-support number (4) now **1/1**). **M5 is complete** for the
> PLDI/POPL scope; the human-authored natural-defect ablation (#52) and all
> LLM-producer axes stay in the ACL/EMNLP follow-up. Next: M6/M7 — the paper
> package (`research-proposal.md` §7, milestone M7).

## Performance

### Criterion-grade performance lab for the grounded evaluator

**What:** A proper benchmark suite (criterion) for the production grounded
evaluator with percentile reporting and regression curves.

**Why:** M3 ships a wall-clock smoke guard (absolute ceiling in CI, label
equality as the real assertion — plan-eng-review D10/D16). A real perf lab
becomes valuable when input sizes grow.

**Pros:** Regression curves instead of thresholds; catches gradual degradation
that a ceiling cannot.

**Cons:** New dependency and CI time; pointless at current corpus scale.

**Context:** Revisit when AF sizes exceed ~1k arguments or M4 incremental
checking lands. The M3 smoke guard (test-suite wall-clock assertion on the
ported #18 stress fixture plus a 100+ arg synthetic AF) is the interim guard.

**Effort:** M
**Priority:** P3
**Depends on:** M3 production evaluator; trigger: AF sizes >1k or M4 scope

## Runtime (M4 candidates)

### Production-runtime concerns beyond the frozen core

**What:** Incremental re-checking (re-evaluate only affected claims when a
unit changes), large-graph performance, and diagnostic UX beyond located
rejections.

**Why:** M3 deliberately optimizes for conformance of the frozen symbolic
core; "production" eventually means more than a conformant batch checker
(outside-voice point, plan-eng-review 2026-07-26).

**Pros:** Captured before M4 planning; prevents M3's conformance focus from
becoming the permanent definition of done.

**Cons:** Explicitly out of M3 scope; some items may require spec evolution
(lara-core version bump governance).

**Context:** The frozen spec governs semantics, but incremental checking is a
runtime concern that does not touch semantics. Candidate M4 scope now that M3
closed issue #27.

**Effort:** L
**Priority:** P3
**Depends on:** M3 closeout (#27)

## M5 prerequisites and language cleanup

### Split `Lara.Mutate` into right-sized modules

**What:** `Lara.Mutate` is ~900 lines (well past the 400-line guideline). The
accept-verdict family already lives in `Lara.Mutate.Accept` (M5 T1); finish the
split — e.g. `Lara.Mutate.Sites` (site enumerators), `Lara.Mutate.Codec` (the
codec-corruption family), `Lara.Mutate.Corpus` (the sweep) — leaving `Lara.Mutate`
as the vocabulary + `Mutant`/`Expected` core.

**Why:** The module grew organically across T1's worked-example, corpus-sweep,
and accept-family stages; the vocabulary/construction boundary is now clear
enough to factor cleanly.

**Context:** Deferred from the M5 T1-corpus + T3 PR to keep that change reviewable
(the accept family already split off the largest new block). T6 added another
operator (`OpHoleObligation` + its site enumerator), making the split marginally
more pressing. `lara-core@0.2` added `Lara.Mutate.Sorts` (the six signature-family
operators) as a second split module rather than growing `Lara.Mutate` further, so
the pattern is now established twice — what remains is factoring the *existing*
bulk out.

**Effort:** S
**Priority:** P3
**Depends on:** nothing.

### Discriminating localization benchmark (multi-defect / off-site) — T6

**What:** The T3 harness's `location_match` is a verification-style number:
single-defect mutants localize at the mutated constituent by construction, so
the measured rate is ≈100% and any deviation is a diagnostic-ordering finding,
not a discriminating benchmark (eng review D10). Add the discriminating variant
— multi-defect mutants and mutants whose manifestation is off the mutated site —
so location accuracy becomes a real signal.

**Why:** The paper's location-accuracy claim is only interesting once the metric
can be < 100%; the current corpus establishes the harness, not the hard case.

**Context:** Recorded as a T6 (ablation/robustness) follow-up when folding the
M5 T1-corpus + T3 measurement work; out of scope for that PR.

**Effort:** M
**Priority:** P3
**Depends on:** M5 T3 measurement harness (landed).

### Standalone completeness (conflict-scan) ablation — result 7 evidence

**What:** Add a third ablation dimension (`ccConflictScan`) plus a
drop-covering-attack mutation operator (expected `reject-MissingConflict`), so
the missing-conflict scan's load-bearing-ness is measured on its own, the way
T6 measures typing and CQ obligations.

**Why:** T6's eng review (D9) folded `firstMissingConflictInfo` into the
No-typed flag to match the paper's "nodes and arbitrary attack edges" baseline,
so no T6 cell isolates result 7 (attack completeness, the frozen
unlabelled-edge theorem) — and the mutant manifest has zero
expected-MissingConflict rows today.

**Context:** Surfaced during the M5 T6 ablation work (review D9/D11;
`docs/m5-freeze-checklist.md`). Same harness and partition pattern as T6; one
more `gen-mutants.hs` regeneration cycle.

**Effort:** S
**Priority:** P3
**Depends on:** T6 ablation baselines (this branch); land before the T5 freeze
or record as a post-freeze suite extension.

### Wrong-fraction certificate mutation operator (semantic cert corruption)

**What:** A mutation operator producing a WELL-FORMED `ra@1` payload carrying a
wrong lowest-terms fraction (expected `reject-R13`), distinguishing "the checker
rejects garbage" (the generic `OpCertPayloadTamper`) from "the checker rejects a
plausible-looking but false certificate."

**Why:** Strengthens the axis-(c) invalid-certificate datum now that the corpus
carries a real certificate (adaptive-pruning/C04, #57). The D1 payload design
(the fraction IS the certified value) exists precisely to make this corruption
meaningful.

**Context:** Deferred from the #57 PR (decision D3; `docs/m5-freeze-checklist.md`)
to keep it reviewable. A suite extension: regenerating cuts `m5-freeze-v3` per
the checklist's post-freeze rule.

**Effort:** S
**Priority:** P3
**Depends on:** #57 (landed).

### Print hole-lines in support terms

**What:** Make `printSupportTerm` preserve `open … as …` hole lines. It currently
drops `srHoles`, so a parsed open obligation does not survive the surface
round-trip.

**Context:** Low priority until an authored example needs `open`; recorded as an
explicit out-of-scope item in the strict-certificate implementation plan.

**Effort:** S
**Priority:** P3

### Theory-line groundness

**What:** Enforce the grammar's requirement that policy `theory` entries are
ground propositions, or revise the grammar to admit variables explicitly.

**Context:** `propP` accepts variable-looking identifiers in theory entries
(harmless in practice because `encodeND` flattens every entry to an atom).
Tighten the parser or update the grammar.

**Effort:** S
**Priority:** P3

### θ-matching for plain `arg` declarations (generalize the comparison form's mechanism)

**What:** Let an ordinary `arg` name its premise leaves and derive θ by one-way
matching against the rule's premise patterns, instead of transcribing the full
positional θ vector.

**Why:** The mechanism `lara-syntax@0.3` builds for the `comparison` expansion
(match named leaves against premise patterns, consistency-checked) kills
transcribed θ for *every* rule if exposed on plain `arg` — no new declaration
form needed. Deferred from the 0.3 track (eng review 2026-08-08, outside-voice
finding 3): the comparison form uniquely delivers goal generation and polarity
checking, but the general θ relief is separable and cheaper.

**Context:** The matcher lands in `src/Lara/Elaborate/Internal.hs` as part of
plan `plans/2026-08-08-lara-syntax-03-surface.md` §5. Exposing it on `arg`
needs only a surface form for "premises by name" plus the same consistency
errors. Candidate rider for #88b.

**Effort:** M
**Priority:** P3
**Depends on:** lara-syntax@0.3 (D4's matcher)

### Σ sort-naming refinement pass (possible-worlds trigger)

**What:** A curated naming/merge pass over the frozen opaque-sort corpus Σ
(`S1, S2, …` from `infer-sigma`'s inferred partition), replacing generated
names with the deliberate ontology once the possible-worlds design resolves.

**Why:** The sorts-in-checker eng review (2026-08-10, OV-2C) shipped the Σ
with machine names precisely because Dataset-vs-EvalSetting is the
possible-worlds question; the deferral needs a tracked trigger. Renaming
edits frozen policy text, so this pass is a full regeneration cycle with a
new freeze tag — budget it, don't discover it.

**Pros:** The ontology commitment is made deliberately, with the follow-up
paper's design in hand; regeneration cost scheduled.

**Cons:** May never fire if opaque names prove fine; costs a regeneration +
freeze tag when it does.

**Context:** Plan `plans/2026-08-10-sorts-in-checker.md` §7; memory note
"possible-worlds future direction" marks the trigger.

**Effort:** M
**Priority:** P3
**Depends on:** sorts-in-checker D8/D11 landed; blocked by the
possible-worlds design decision.

### spec.md's presentation-version pointer

**What:** Decide how `docs/spec.md` (≈lines 144-149) refers to presentation
syntax versions as grammar appendices accumulate, and record it — e.g. one
sentence: "presentation syntax versions live in `docs/lara-surface-grammar.md`;
spec.md pins the core."

**Why:** spec.md names `lara-syntax@0.1` as *the* presentation version; App. A
(0.2) shipped without updating it and App. B (0.3) repeats the question. The
current state is precedent-by-accident, not a decision.

**Context:** Found during the 2026-08-08 eng review of the 0.3 surface plan
while checking App. A as the App. B precedent. Purely editorial; deliberately
kept out of the 0.3 diff to avoid pulling spec.md into a surface-track PR.

**Effort:** S
**Priority:** P4

## Completed

### AST ↔ Presentation.lean parity guard

The recurring silent narrowing of result 12 is now mechanically detected. It had
happened three times: theories, then `groupMode` (both recorded 2026-08-09 and
patched by `syntax-03` D8), then Σ + signature blocks (recorded 2026-08-10 and
patched by the sorts-in-checker plan's D9). Nothing prevented a fourth. The
Lean mirror first caught up with the live Haskell surface: `lean/Lara/Presentation.lean`
carries `policySigma` as a second `Policy` field and models measurands as
`Sort × Option Polarity`, reusing `Lara.Sigma`'s types, with the round-trip proofs
audited in `AxCheck.lean`. On top of that synced state, `scripts/presentation-shape.hs`
and `lean/Lara/PresentationParity.lean` each emit a normalized name-and-arity
inventory of the surface-reachable types, and `scripts/check-presentation-parity.sh`
diffs the two — 68 rows, byte-identical — exposed as `make presentation-parity` and
run as a CI step.

The guard never parses source text. Each side's inventory is protected by its own
compiler. Exact constructor signatures pin every record field type and every
payload-carrying sum arm, including same-arity retypes. Alias and anonymous-entry
rows have explicit local type anchors instead of relying on the cross-language
diff. The shape tripwires re-derive every row's real part count and every named
record's normalized selector sequence — `GHC.Generics` metadata in Haskell and
`Lean.Meta` at elaboration time in Lean — so named field renames and reorders also
fail the build. Positional constructors have no source selector names: exact
signatures pin their arity and positional type sequence, but semantic labels and
swaps among same-typed positions remain assertions. Both runtimes are rebuilt
inside the script, so a stale artifact cannot produce a false PASS.
Two representation exemptions are stated in full in both witness files:
`SortName` is witnessed but row-erased (Lean's `Sigma` carries `List String`),
and `Cert`'s payload is each language's native S-expression type and is exempt
from shape comparison.

Consequence for future work: divergence is no longer silent. Growing the
surface on one side only fails CI; a genuinely intended asymmetry must update both
inventories — and, where it is a representation choice rather than a missing field,
the documented exemption list — in one reviewed change.

### Cut the `lara-core@0.2` freeze tag

The annotated `m5-freeze-v4` tag now points to `f4327b4`, the merge commit of
the v4 re-freeze PR #99. It was cut after PR #100's benchmark-harness repair
merged and main CI run `31463095876` passed both Lean and Haskell jobs. The
freeze records 504 mutants plus 60 corpus units: 564/564 class matches,
564/564 Lean agreement, and 60/60 replay.

### Backend rejection reasons reach the author (PR #83 review)

`CertOk` now returns `CertOutcome` (`CertAccepted` / `CertRejected String`)
instead of `Bool`. `assuranceOkB` branches on the `certAccepted` projection —
so the checked graph, and every soundness statement over it, still depends on
nothing but the old boolean — while `assuranceError` puts the backend's own
reason into `BackendReason.ReplayRejected`, and
`Lara.Driver.runCheckLocatedReported` emits it as one `stderr` line from the
same single pass that produced the verdict. Both front doors use it.
`Lara.Strict.Cell.renderDecimal` (inverse to `parseDecimal`, pinned by a
round-trip property) lets `ord@1` and `ra@1` cell-mismatch messages name the
offending numerals in the author's own notation rather than as `71 % 100`.

**The re-run shortcut, revisited.** The open entry ruled out "re-running the
failing backend purely to recover a string for stderr", on the ground that *a
second evaluation path that can diverge from the checked one is the wrong shape
for a system built around a single checked path*. That objection was revisited
and it does not bite here, for a reason the open entry did not distinguish:
`assuranceError` re-*applies* `certOk` to the identical `(cert, As, C)`.
`CertOk` is a pure function, so the two applications are the same value — one
evaluation path with two projections (`certAccepted` for the graph, the reason
for stderr), not two paths that could disagree. What the entry was right to
reject — reconstructing the decision from the input by an independent route —
is exactly what is *not* done. The cost is confined to the rejecting branch: an
accepted step asks once, so the E1 bench's accept-dominated workload is
unaffected. The distinction is recorded on `Lara.SupportTerm.CertOk` and at the
`assuranceError` call site.

The Lean seam was deliberately **not** widened: `certOkBOf` stays `Bool` and no
proof changed. The two drivers reach the same acceptance set by different
routes (Haskell adapters guard slots directly; Lean's `buildRegistry` resolves
known digests to the empty theory, because the abstract core sees only
`Γ = Δ ++ T`), so they cannot agree on the *wording* of a slot rejection.
`scripts/differential.sh` byte-compares stdout and the exit code everywhere and
leaves stderr free except on the preflight and group-conflict anchors, which
this line is not; the rationale is recorded on `backendRejectionMessage`.

### Raw-door backend theory content: seam-wide decision (ra@1 / ord@1 parity)

Decided in favour of parity: **`ra@1` refuses theory-entry slots, like
`ord@1`.** Its own documentation already said theory entries "are never
consulted"; citing one as a *cell* was never intended, and it was the one path
by which a certificate-consulted value bypassed the leaf/admission layer on the
raw `.sexp` door. Both rational-arithmetic backends now share one trusted-base
sentence: every certificate-consulted cell traces to a consulted premise, hence
to a leaf. `nd@1` deliberately keeps free-context indexing — its de Bruijn free
variables are *meant* to reach theory axioms.

Rejected alternative: pinning theory *content* at the raw door. It touches the
frozen replay/preflight contract and needs a trusted content registry in the
driver; heavier, and unnecessary once the values are premise-backed.

Byte-preserving for every frozen artifact: `corpus-v1`'s `ra@1` theory is
declared empty, so no frozen certificate could cite an entry. Pinned by
`fixtures/corpus/ra-premise-only-{accept,reject}.sexp` (the reject twin declares
a theory entry carrying the goal's full cell, so free-context indexing *would*
have accepted it) and by `prop_raTheorySlotRejected`. Lean mirrors it the same
way it mirrors `ord@1`: `buildRegistry` resolves a known `ra@1` digest to `[]`.

### Corpus extension exercising ord@1 end-to-end

Decided and recorded in `docs/ord1-corpus-extension-decision.md`: **not before
the PLDI submission.** The corpus half is a `corpus-v2` cycle — touching
`corpus-units/` regenerates the mutant suite, invalidates
`measurements/frozen/`, and forces an `m5-freeze-v4`, which #60/#78 already
ruled out inside the window. The demonstration landed in `examples/` instead
(S3, the `num_le` tie; S4, an undermined binding defeating the bridge while the
certified comparison survives), and the decision note records what a real
corpus unit would need so the deferral does not lose the design. The paper must
not describe `ord@1` as corpus-measured; it contributes no corpus row.

### ra@1 rational-arithmetic certifier — the strict/certificate path (issue #57)

The registered `ra@1` backend re-checks `rel_drop_ge(F, A, C, T)` in exact
rational arithmetic on both sides of the differential seam
(`src/Lara/Strict/RA.hs`, `lean/Lara/RA.lean`): the certificate
`(radrop (prem N) (prem M) (frac P Q))` names its two consulted slots and
carries the claimed drop as a lowest-terms fraction; replay recomputes
`(F − A)/F` exactly — no floats. The Lean `Backend` instance is `sorry`-free
within the standard trio (replay adequacy, soundness via witness cancellation,
and the three obligation-4 dependency laws; AxCheck extended). The fixed
registry generalizes to `[nd@1, ra@1]` (`buildCertOk`, `buildRegistry`, replay
preflight `supportedBackends`). corpus-v1 gains the strict Family-10
`rational_drop_recheck` rule + empty theory; `adaptive-pruning/C04`'s
derived-arithmetic leg migrates onto it (score cells as observed premise
leaves, unstatused sub-claim `c04a`, headline claim honestly stays `gap`).
All 60 anchors regenerated; suite 358→360 (C04 cert tamper/theory-swap picked
up by the existing operators); differential 418/54 byte-identical; re-frozen
as `m5-freeze-v2` with claim-support number (4) = 1/1. The wrong-fraction
semantic-corruption operator is recorded above as the deferred follow-up.

### M5 T5 — freeze protocol (tracker #48)

`docs/m5-freeze-checklist.md` freezes the deterministic evaluation corpus before
the final measurement runs (the analogue of the proposal's blinded held-out
freeze). Frozen inputs are pinned by git-tree content hash: the 358-mutant suite
(`fixtures/mutants/`), 60 corpus units (`corpus-units/`), 11 worked examples
(`examples/`), and `mutationSeed = 20260801` (verified byte-identically
reproducible — regeneration leaves an empty `git diff`). Pre-freeze gates all
green: `scripts/differential.sh` positive 416/0 + negative 54/0, `cabal test all`
PASS. The one-command post-freeze run (`cabal exec -- runghc scripts/measure.hs`)
is committed under `measurements/frozen/` (the working `measurements/` stays
gitignored): 418 records, class-match 418/418, cross-driver `lean_agree` 418/418,
ablation surgical (no-cq misses exactly 18 `IncompleteArgument`, no-typed exactly
30 R10/R11). Timing columns are reported but excluded from the reproducibility
anchors (wall-clock, environment-dependent); the deterministic projection
(`report.tsv` cols 1–14) and `ablation.tsv` are hashed in the checklist. Tag
`m5-freeze-v1` will mark the freeze commit (post-merge). **M5 is complete** for the PLDI/POPL
scope; #52 (human-authored natural defects) and the LLM-producer axes remain in
the ACL/EMNLP follow-up.

### M5 T6 — deterministic ablation baselines (tracker #48, PR #53)

`Lara.Check.CheckConfig` (`ccObligationGate` / `ccTypedAttacks`) gates exactly
three checker sites, each flag only ever removing a rejection arm; `fullConfig`
is behavior-identical to the frozen semantics, is what every production caller
uses, and never reaches the wire. The two ablation cells — no-cq (obligation
gate off) and no-typed (attack typing + conflict scan off) — are computed by a
pure pass in `Lara.Measure` (`scripts/measure.hs`, with `--ablation-only`
skipping the Lean timing sweep) and rendered as `ablation.{json,tsv}`. The new
`OpHoleObligation` operator seeds 18 `reject-IncompleteArgument` mutants,
growing the suite 340→358 (verified at generation, byte-identical on re-run);
the differential harness holds 416/54 byte-exact across drivers — the first
differential coverage of the `IncompleteArgument` path. The ablations are
surgical and monotone: no-cq misses exactly the 18 hole rows, no-typed exactly
the 30 `reject-R10`/`reject-R11` rows, every other row byte-identical — pinned
by the `AblationSpec` properties (partition totality, surgical flips,
monotonicity, conflict-scan gating, renderer shape). T5 (freeze) remains, with
the ablation configs and the 358-mutant suite as freeze inputs.

### M5 T1 (corpus half) + T3 measurement harness (tracker #48)

T1's corpus half and the status/attack requirement: `Lara.Mutate` runs every
rejection operator over the 60 T2 corpus units under the uniform
derived-applicability sweep (B=12, per-operator applicability from site
enumeration, no hand partition), and `Lara.Mutate.Accept` adds five
accept-verdict operators over the 9 justified units exercising every claim
status {gap, justified, defeated, contested} and every attack kind {rebut,
undercut, undermine}, each verified structurally (verdict + label shape, not
status alone — eng review D7/4A). T3: `Lara.Measure` + `scripts/measure.hs`
emit the one-command axis-(c) report (rejection outcome + defect location vs
seeded ground truth, replay success, certificate size, checking time) from both
manifests, rendered via the house `JValue` codec (aeson is a test-only check);
`Lara.Diagnostics` gained the shared located-rejection vocabulary
(`constituentText`/`parseConstituent`, `CReplayEnvelope`/`CGroup`) and
`Lara.Driver.runCheckLocated` unifying all three reject paths. 340 mutants +
60 corpus units are byte-identical across the Haskell and Lean drivers
(`scripts/differential.sh`). Verdict-carried replay identity (#36, spec §2.1)
is closed: the `.core.sexp` anchors carry the `replayId` tuple and the harness
measures replay success on every corpus unit. No new Lean metatheory —
generator and harness are corpus tooling; soundness stays with the Lean driver
+ differential harness. T5 (freeze) and T6 (discriminating localization)
remain.

### M5 T1 (worked-example half) + T4 — seeded mutation suite and worked cases (tracker #48)

T1, worked-example half: `Lara.Mutate` + `scripts/gen-mutants.hs` generate a
seeded (SplitMix64, committed seed), verified-at-generation mutation suite
over the accept-verdict worked examples: every executable rejection class
(R1/R3/R4/R5/R6/R7/R9/R10/R11/R12/R13) is exercised by generated mutants,
codec corruption lands in the `fixtures/mutants/malformed/` negative half
(both drivers exit 2, per-operator diagnostic pinned via the manifest), and
the constructed rebut-cycle family is the specified non-rejection (accept,
all-undec/contested). `test/MutationSpec.hs` re-verifies specified outcomes,
seeded reproducibility, and class coverage; `scripts/differential.sh` holds
every mutant byte-identical across drivers. T1's corpus-unit half — the #48
requirement that the generators also run over corpus units and that generated
mutants exercise every status/attack kind — stays open until T2 lands the
corpus units. T4: worked examples E4
(reinstatement — justified UNDER each attack kind) and E5 (contested via
undermine- and undercut-native 2-cycles, gap amid attacks) on policy
`empirical-v2` close the attack-kind × target-label matrix, measured by the
extended `prop_coverageMatrix`.

### Duplicate-report groups, spec §4.3 (issue #38)

Groups are carried end-to-end: surface `group g = [l, …]` and the policy
`duplicate-reports = quarantine|reject` setting (`Lara.Syntax`), the `DupGroup`
/ `GroupConflictMode` AST carrier and `unitGroups` / `unitGroupMode` on `Unit`
(`Lara.AST`), the wire `groups` section (`Lara.Wire`, byte-identical Lean
`Lara.Driver`), the elaborator lowering (`Lara.Elaborate`), and the
driver-boundary check (`Lara.Driver.runCheck` / Lean `runOnContents`): a
`≡`-consistent group admits normally; an inconsistent group quarantines its
members so the dependent claim routes to `gap`; an escalated conflict rejects
R9 (a boundary reject like R13). Lean metatheory (`Lara.Groups`, AxCheck-clean):
pairwise-`≡` ⟺ representative, quarantine membership, arg exclusion, the
leaf-rule connection, and the escalation characterization. Differential
fixtures `group-consistent-accept` / `group-conflict-quarantine` / `reject-r9`
pass both drivers byte-exact; R9 negative in `Lara.Negatives` and `CheckSpec`.

### Result-9 backend replacement (PRs #41 and #43)

`lean/Lara/Erase.lean` proves backend replacement under a uniform injective
assurance relabel. `lean/Lara/EraseTransport.lean` transports well-checkedness
under acceptance preservation and constructs the relabeled `CheckedProgram`,
so the theorem is non-vacuous by construction. Both developments are
`sorry`-free and AxCheck-clean within the standard axiom trio.

### Strict-certificate worked example (nd@1 frontend cert path)

S1 lands the full frontend certificate path (`.lara` → elaborate → verdict +
`.core.sexp`); the hypothesis-reuse boundary is recorded in
`examples/S1/strict-v1.policy.lara`.

### Cache grounded adjacency for the M3 production evaluator (PR #28)

Production grounded evaluator (`Lara.Runtime`) computes adjacency once and is
byte-identical to the un-cached `Lara.Compile.checkedAF` path, differential-
tested against `Grounded.grounded` with a 120-argument ≤5 s perf guard.

### Full claim holes and incomplete-alternative diagnostics (PR #28)

`Lara.Reporting` computes `holes(P,p)` from the raw `Unit` boundary and emits
the `incompleteAlternative` diagnostics defined by spec §8 / §10.1.
