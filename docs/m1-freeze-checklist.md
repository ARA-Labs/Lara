# M1 freeze checklist — frozen language v0.1

_Operational tracker for milestone **M1 — frozen language v0.1** (`plans/research-proposal.md` §7).
Companion to `engineering-plan.md` (module dependency graph) and `spec.md` (the contract). This file
records, component by component, what is already frozen, what still needs a lock before the v0.1 tag,
and the mechanization obligation each frozen definition triggers._

## What M1 is (and is not)

**M1 definition of done** (`research-proposal.md` §7): a versioned freeze of the *whole* language —
concrete/abstract syntax and JSON, static judgments, policy language, typed attacks, holes, AF
compilation, claim aggregation, and specified rejection behavior; the strict-chain `contrary`
well-formedness check (spec §8.1, Path B) and the proposition normalization `nf`/`≡` (spec §3.2) are
part of the frozen definition.

**M1 is not PR #9.** PR #9 (`41a97f9`) froze the *corpus-derived* decisions — leaf grain, scheme
vocabulary, adapter portfolio, defeat typing (spec §3, §4.3, §4.5, §5.2, §7, §11; claims C13–C17).
Those are M1 *inputs*. M1 additionally freezes the corpus-*independent* language surface (syntax,
JSON, the full static-judgment set, compilation, rejection behavior) and versions the whole thing.

M1 is a **spec-freeze / docs task**, not Haskell (that is M3). Its output triggers M2 (mechanization).

## Pre-freeze gates

| Gate | Status | Evidence |
| --- | --- | --- |
| §8 #8 — TCB enumeration + Lean/Rocq host | **Resolved (2026-07-22)** | spec §1.1; host = Lean 4 |
| M0 exit (≥80% construct coverage) | **Passed** | `m0/annotation-summary.md` §3 (~90%, PR #8/#9) |
| §8 #1/#2/#3/#5 — adapters / schemes / defeat / leaf grain | **Frozen** | spec §5.2/§4.5/§7/§3 (C13–C16) |

All blocking gates for the freeze are clear. Remaining M1 work is the language-surface lock below.

## Freeze checklist — per component

State legend: **Frozen** = fixed for v0.1, do not re-litigate; **Lock** = drafted, needs a final
v0.1-lock pass; **Defer** = explicitly out of v0.1 (recorded, not an open gap).

| # | M1 component | Spec | State | Remaining action before the v0.1 tag | Mechanization obligation |
| --- | --- | --- | --- | --- | --- |
| 1 | `nf` / `≡` proposition normalization | §3.2 | **Frozen** | none (carve-out 1) | §9 r11 — **done** (`lean/Lara/Prop.lean`) |
| 2 | Proposition / leaf shape (`nl`/`formal`/`binding`, per-cell grain) | §3, §3.1 | **Frozen** | none (C15); distribution-valued leaf → Defer (C17) | serializes into core AST |
| 3 | Policy language: patterns, substitution, CQ discharge, admission table | §4.1–§4.4 | **Frozen** | ✅ §4.1 instantiation + §4.2 accounting markers; §4.3 `Gamma(P)` construction figure; Lean: `instPat`/`instAPat`, `InstSide`, `DefeatPolicy` | §9 r1, r3 (see rows 8/9) |
| 4 | Reference scheme vocabulary (9 families) | §4.5 | **Frozen** | none (C13); spellings revisitable until `empirical-v1` ships | schema instances, no new theorem |
| 5 | §8.1 strict-reachable `contrary` well-formedness (Path B) | §8.1 | **Frozen** | ✅ frozen as part of the definition; violation = R12; duplicate rule IDs and R12 run before program checking | §9 r7/C09 ✅ for the Lean reference PL (`Lara.Policy`, `Lara.Check.Unit`, `Lara.Consistency`; #18 implementation) |
| 6 | Strict-backend seam + ND reference adapter | §5.1, §5.3 | **Frozen** | none (carve-out 2) | §9 r2, r8, r10 — **done for ND** (`lean/Lara/{Strict,ND}.lean`) |
| 7 | Shipped adapter portfolio (`ra@1` + `ord@1` + `insp@1`; LP non-shipping) — **amended 2026-09-07 (#256), completed 2026-09-07 (#260)** | §5.2 | **Frozen** | C14; `ord@1` added under PR #83; `insp@1` (static code inspection) shipped under #260 | §9 r10 per shipped adapter — ND ✅ (`lean/Lara/{Strict,ND}.lean`); `ra@1`/`ord@1`/`insp@1` ✅ (`lean/Lara/{RA,Ord,Insp}.lean`) |
| 8 | Support-term `w` AST + typing (`⊢ w : supports(p) ▷ O`, `leaves`, `certDeps`) | §6, **§6.1** | **Frozen (def)** | ✅ typing rules, exact executable Lean checker (`Lara.Check.inferSupport`), and the `certDeps` layer over `Backend.uses` landed (#46) | §9 r1 support/program checker ✅; r3 both halves ✅; r11 relational ✅ |
| 9 | Typed positional attacks (rebut / undercut / undermine, `w@π`) | §7, **§7.1** | **Frozen (def)** | ✅ typing rules, exact executable Lean checker (`Lara.Check.checkAttack`), and relational compile-facing soundness landed | §9 r1 positional checker ✅; r4 (with item 11) ✅ |
| 10 | Holes (open obligations) | §4.2, §6.1, §10.1 | **Frozen** | ✅ absorbed by the §6.1 `D ⊎ H` fix + §4.2 marker; mis-declared holes = R5, open mandatory = gap-routed (not rejection) | §9 r1 (mechanized invariants, row 8) |
| 11 | Compilation `compile(P) = AF` + subargument closure | §8 (**compilation rules**) | **Frozen (def)** | ✅ generic `checkProgram`/`CheckedProgram` remains unchanged; detailed acceptance adds exact conflict coverage and retained checker nodes — pending: r9 | §9 r4 both halves ✅; r6 source-vs-compiled half ✅ (#17); r7 attack completeness ✅ (#18); r9 pending |
| 12 | Grounded labelling + four-state aggregation | §8, §8.2 | **Frozen** | none | §9 r5 ✅; r6 source-vs-compiled half ✅ (#17 closed); r7/C09 computed-complete-claim consistency ✅ for the Lean reference PL (#18 implementation) |
| 13 | Abstract syntax + wire schema (S-expression codec `Lara.Wire`; JSON producer surface is #30 — **amended 2026-09-07 (#256)**), **versioning** | §2, **§2.1** | **Frozen** | ✅ `lara-core@0.1` / `lara-syntax@0.1` + the replay-identity tuple. Declared deferral: the complete presentation grammar lands with `Lara.Syntax` (M3) under `lara-syntax@0.1`, gated by r12 | §9 r12 — presentation half ✅ (`parse ∘ print` at `lara-syntax@0.10`, spec §2.1); wire-decode boundary ✅ (`WireSpec` malformed-input matrix) |
| 14 | Specified rejection behavior (located, per rejection class) | **§10.1** | **Frozen** | ✅ R1–R14 enumerated with locations; quarantine and cycles deliberately non-classes; mapped onto the mutation list | §9 r1 (decidability); M5 mutation-suite spine |

## M0 conditions the freeze must absorb

From the M0 gate verdict (`annotation-summary.md` §3), the ~90% PASS came with conditions:

1. **Kind-(a) annotation conventions → spec.** Open-class/asymptotic scope via `binding`;
   heterogeneous strands as multiple `arg` (N19 no-accrual); conjunctive claim-splitting.
   *Partly in PR #9; confirm each is stated in §3/§4/§11 before the tag.*
2. **C17 six-item construct wishlist → Defer, recorded.** Equivalence/non-inferiority scheme,
   monotone-functional propositions, parametric growth-rate, distribution-valued leaf, negative
   existentials over code, graded predicates. Held in `ara/logic/solution/constraints.md`; the freeze
   must state these are **outside** the v0.1 fragment, not gaps.
3. **Kind-(c) evidence-model calls.** Result-cell conflict → §4.3 (done); dead-end→support → §7/§11
   task 6 (done). Confirm nothing else in kind-(c) dangles.
4. **N29 authored adversarial attack cases.** Corpus is too polished to supply rebut/undermine tests;
   defeat-layer evaluation uses self-authored adversarial reports. Not a freeze blocker — flags a
   test-asset task for M3/M5.

## Exit action — all complete (2026-07-22)

1. ✅ All Lock rows closed (items 3, 5, 8–11, 13, 14) — derivation chain (8/9/11) frozen *and*
   ported to Lean; surface rows (3/5/10/13/14) frozen in the final spec pass.
2. ✅ M0 conditions absorbed (kind-(a) conventions in §3/§4/§11; C17 wishlist recorded as
   deferred in `ara/logic/solution/constraints.md`; kind-(c) calls in §4.3/§7/§11; N29 flagged
   for M3/M5 test assets).
3. ✅ Spec header lifted to **v0.1 — frozen at M1**; M1-frozen blockquote added. Apply the git tag
   `spec-v0.1` on the merge commit of the freeze PR.
4. ✅ M2 backlog opened (below).

## M2 backlog (opened at freeze; ordered by dependency, all corpus-independent)

1. **§8.1 validator + accepted-unit consistency — done for the Lean reference PL
   (#18 implementation)**: `lean/Lara/Policy.lean` defines the finite
   strict-reachable set, proves `strictReachable_iff_mem`, conservatively checks instance overlap,
   proves canonically equivalent ground instances are caught
   (`aPatMayOverlap_of_instances`), decides `wf(Pi)` via `wfB_iff`, connects the judgment to
   `ContraryMatch`, and returns a located R12 rule/pair. Public `checkUnit`
   canonically constructs `Unit.CheckedUnit` in the fixed order duplicate rule
   IDs → R12 → duplicate arguments → support → typed attacks → missing conflict.
   Detailed acceptance carries exact attack completeness and the retained
   checker cache; support is not re-inferred. `Lara.Consistency` is
   downstream-only and proves result 7/C09 for claims computed by exact
   `completeClaimFor`, including self-conflict. Manual proof-level
   `CheckedUnit` construction still requires all invariants.
2. **Executable checkers — result-1 portion done**: `Lara.Check.inferSupport`,
   `checkAttack`, and `checkProgram` exactly decide the frozen support,
   positional-attack, and raw-program judgments; their legacy generic behavior
   is unchanged. The checker-built
   `Compile.edgeB`/`edgeB_faithful` edge decider (issue #17) now discharges
   `Compile.Faithful` constructively, closing r6's source-vs-compiled half.
3. **`certDeps` accountability — done (#46)**: the abstract `Backend` is a
   theory-free core, fixed per registered `(name, version)`; a digest
   resolves only to theory *data* (`RegisteredBackend.resolveTheory`), and
   the core carries `uses` with obligation 4's coverage (`uses_covers`),
   validity (`uses_valid`), and semantic accounting (`uses_account`) laws
   over the explicit full consulted context `Δ ++ T` (so a digest swap is
   observable only through reported theory slots —
   `certOkBOf_theory_covers`); the ND adapter discharges them via
   `infer_agree`/`fv_in_range`/`nd_relevance`,
   and `Lara.Support`'s `certDeps` layer proves r3's certificate half over
   the typed premise/theory `CertDep` report: `cert_steps_accounted`,
   `mem_certDeps_step`/`certStep_deps_subset`, `certDeps_resolved`,
   `certDeps_theory_valid`.
4. **r9 backend replacement — representation blocker**: the relational §6.1/§8 layers are frozen,
   but `CheckedProgram` stores certificate-bearing `SupportTerm` nodes and has no stable argument
   ids or certificate-erased skeleton. Payload-different programs therefore lack the node bijection
   needed to state the promised AF isomorphism faithfully. Add argument identity plus `eraseCert`
   at the compile boundary, then prove checking transport, graph isomorphism, and status equality.
5. **Shipped-adapter obligations (r10) — done, portfolio complete**: `ra@1`, `ord@1`, and
   `insp@1` each discharge the same soundness/dependency obligations as ND (`lean/Lara/RA.lean`,
   `lean/Lara/Ord.lean`, `lean/Lara/Insp.lean`). Issue #260 closed the last designed-but-unshipped
   portfolio item, so no adapter now carries an outstanding r10 debt.
6. **r12 codec round-trip — resolved**: the presentation half (`parse ∘ print`,
   `lean/Lara/Presentation.lean` at `lara-syntax@0.10`) and the wire-decode boundary (`WireSpec`)
   landed with `Lara.Syntax`/`Lara.Wire`; there is no JSON codec in the TCB — `Lara.Json` is the
   #30 LLM-producer surface.

Issue #18 does **not** claim Path A, a production Haskell checker,
NL-to-structure validation, full `holes(P,p)`, or `incompleteAlternative`
computation. `Lara.Grounded` is the proof-oriented reference evaluator, not the
deferred optimized implementation. The passing Haskell gates (`cabal build`;
one test suite with 30 QuickCheck groups at 100 cases each) are
regression-compatibility evidence only. Lean evidence comprises all 70
traceability IDs and six author flows, `lake build` (25 jobs), 430 AxCheck
reports with no `sorryAx` and only the allowed axiom trio, plus the repaired,
negative-tested multiline CI axiom parser.

### M3 delivered (2026-07-27): production checker + differential anchor

The deferrals the #18 note lists above are now implemented in Haskell, each the
executable mirror of the frozen Lean development:

- **Production Haskell checker** — `Lara.Check.checkUnit` decides the seven-stage
  whole-unit boundary (duplicate rule ids → R12 → duplicate arguments → support
  → typed attacks → missing conflict), the exact order of the Lean `checkUnit`.
  Layers 3–8 landed as `Lara.{Policy,SupportTerm,Attack,Compile,Grounded,
  Diagnostics}`.
- **Cached-adjacency runtime** — `Lara.Runtime` is the deferred optimized
  evaluator; `RuntimeSpec` proves its verdict byte-identical to the un-cached
  reference path over random AFs, with a 120-argument ≤5 s perf guard.
- **`holes(P,p)` / `incompleteAlternative`** — `Lara.Reporting` computes the
  claim-diagnostic projections (spec §8, §10.1); `ReportingSpec` covers gap
  routing, located unresolved alternatives, and non-suppression of complete
  winners.
- **N11 differential anchor** — `Lara.Wire` is the single S-expression codec;
  the `lara check` CLI (`app/Main.hs`) and the Lean driver
  (`lean/Lara/Driver.lean`, exe `lara-driver`) print verdicts through it.
  `scripts/differential.sh` runs every `fixtures/**/*.sexp` through both drivers
  and asserts byte-exact stdout + exit-code agreement (Lean is the oracle);
  `test/DifferentialSpec.hs` pins the agreed verdict bytes for `cabal test`.
- **R1–R14 mutation coverage** (row 14) — `checkUnit` decides R1, R2, R3,
  R4, R5, R6, R7, R10, R11, R12, and R13 (certificate replay at the support
  stage), plus the four structural outcomes (duplicate-rule, duplicate-argument,
  incomplete-argument, missing-conflict); `CheckSpec` pins each with a rejected
  golden. The production driver decides replay-preflight R13 and escalated
  data-integrity R9. R8 is the
  source-admission boundary. R14 is the wire-decode boundary, covered by
  `WireSpec`'s malformed-input matrix. The mutation and differential corpora
  exercise these boundaries. This lands the "M5 mutation-suite spine" the
  row-14 mechanization pointer anticipated.

These Haskell tests are conformance evidence; soundness stays in the Lean
proofs. The former numeric caveat is resolved: both production drivers use
`canonNum`, with a non-canonical numeric differential fixture pinning parity.

_Done so far (2026-07-22): §8 #8 resolved — TCB written into spec §1.1, host fixed to Lean 4.
Lock pass item 8 — support-term typing rules made explicit and v0.1-frozen in spec §6.1 (defect
found and fixed on review: the syntactic hole set `H` covers optional questions, only
`H ∩ mandatory(r)` contributes obligations), then ported to Lean per the port-as-we-lock
discipline: `lean/Lara/Support.lean`, six sorry-free theorems in the AxCheck gate.
Lock pass item 9 — attack-typing rules made explicit and v0.1-frozen in spec §7.1 (position
lookup, contrary-instance relation, [A-Rebut]/[A-Undercut]/[A-Undermine]; checked-not-complete
source, occurrence-local premises), ported as `lean/Lara/Attack.lean`: six sorry-free theorems —
checked source, strict-unattackability (rebut + undercut), position-kind partition, local/global
conclusion coherence.
Lock pass item 11 — compile rules made explicit and v0.1-frozen in spec §8 (`Args` = complete
declared arguments, `occ(k)`, closure edges by structural occurrence containment), ported as
`lean/Lara/Compile.lean`: seven sorry-free theorems — result 4 both halves
(`compile_nodes_checked`, `edge_iff`), closure ⊇ direct, and the N16 bridge
(`srcIn_iff_directIn`/`srcIn_iff_grounded`) connecting source-level declarative status to the
abstract grounded layer, oracle-parametric (`Compile.Faithful`) until the executable checkers
land.
Final spec pass (rows 3/5/10/13/14) — §4.1/§4.2 freeze markers, §4.3 `Gamma(P)` construction,
§8.1 frozen as definition (violation = R12), §2.1 versioning + replay identity
(`lara-core@0.1`), §10.1 rejection classes R1–R14, §9 per-result mechanization pointers, and the
header lifted to **v0.1 — frozen at M1**. **M1 is complete**; tag `spec-v0.1` at the freeze-PR
merge commit.
Review follow-up (2026-07-24) — §8.1's finite validator is now mechanized in
`lean/Lara/Policy.lean` and audited in `AxCheck.lean`. A second review exposed that syntactic
pattern equality did not align with instance-level `ContraryMatch`; `wf(Pi)` now uses a
conservative pattern-overlap check with a proved ground-instance soundness bridge. The exact model
blockers for the remaining r7 theorem and r9 are recorded above rather than deferred on queue order
alone._

### Amendment (2026-09-07, issue #256): shipped-adapter portfolio and wire wording

Rows 7 and 13 and M2 backlog items 5–6 above are amended to match the Haskell tree:

- **Shipped portfolio.** v0.1 ships `ra@1` (rational-arithmetic/table-recheck) and `ord@1`
  (ordered comparison, PR #83) beside the §5.1 reference backend `nd@1`. The static code-inspection
  checker remained portfolio-designed but **unshipped** at the time of this amendment, with its
  build tracked in issue #260; that issue has since landed — see the #260 amendment below.
- **Wire wording.** The M1-era spec named JSON as the wire encoding; the implementation
  deliberately ships a single S-expression codec (`Lara.Wire`, the N11 differential anchor).
  Spec §1/§1.1/§2.1/§3.2/§4.1/§9 r12/§10.1 R14 and `docs/rejection-surface.md` now name that
  codec; `Lara.Json` is tracked as the future LLM-producer surface (issue #30). No corpus
  regeneration or freeze-tag bump is owed: the amendment is prose-only and no byte reaches the
  corpus, the wire, or replay identity.

### Amendment (2026-09-07, issue #260): the portfolio is complete

Row 7 and M2 backlog item 5 are amended again: the third §5.2 portfolio member ships.

- **`insp@1`** (static code inspection, `Lara.Strict.Insp`) is registered beside `nd@1`, `ra@1`,
  and `ord@1` in the fixed backend registry. It certifies structural facts about referenced source
  — `code_absent`, `code_present`, `code_unique`, `code_planned_not_shipped` — over declared
  exhaustive inventories; the certified content is the closed-world step from an enumeration to a
  negative existential, never the faithfulness of the enumeration itself. Design record:
  `docs/insp1-code-inspection-decision.md`.
- **r10 is discharged** for it in `lean/Lara/Insp.lean` (`enc_iff`, `inspReplay_iff`, `inspSound`,
  and the obligation-4 laws), pinned in `lean/AxCheck.lean` inside the standard axiom trio. No
  shipped adapter now carries an outstanding r10 debt.
- **Conformance evidence** is `test/InspSpec.hs`, four hand-authored wire anchors under
  `fixtures/corpus/insp-*.sexp`, and the worked example `examples/S9` (both certificate arities
  under one defeasible bridge). A mutation base for `S9` is *not* included: it would grow the
  seeded suite 541 → 568 and so cost an evaluation-corpus freeze-tag bump, which #260 did not
  budget — tracked in issue #266; see the `m5-freeze-checklist.md` post-v5 addendum.
- **No freeze-tag bump or corpus regeneration is owed.** The adapter is additive at the registry,
  no existing unit selects it, and no corpus, wire, mutant, or replay-identity bytes change.
