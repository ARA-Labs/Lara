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
| 3 | Policy language: patterns, substitution, CQ discharge, admission table | §4.1–§4.4 | **Lock** | freeze the static admission judgment as v0.1 rules | §9 r1, r3 |
| 4 | Reference scheme vocabulary (9 families) | §4.5 | **Frozen** | none (C13); spellings revisitable until `empirical-v1` ships | schema instances, no new theorem |
| 5 | §8.1 strict-reachable `contrary` well-formedness (Path B) | §8.1 | **Lock** | state as part of the frozen definition, not an aside | §9 r7 |
| 6 | Strict-backend seam + ND reference adapter | §5.1, §5.3 | **Frozen** | none (carve-out 2) | §9 r2, r8, r10 — **done for ND** (`lean/Lara/{Strict,ND}.lean`) |
| 7 | Shipped adapter portfolio (arithmetic-recheck, code-inspection; LP non-shipping) | §5.2 | **Frozen** | none (C14); per-adapter soundness is M2/M3 | §9 r10 per shipped adapter — **pending** |
| 8 | Support-term `w` AST + typing (`⊢ w : supports(p) ▷ O`, `leaves`, `certDeps`) | §6, **§6.1** | **Frozen (def)** | ✅ typing rules written (§6.1); ✅ Lean port landed (`lean/Lara/Support.lean`) — pending: executable checker, `certDeps` | §9 r3 leaf half ✅, r1 uniqueness half ✅, r11 relational ✅ |
| 9 | Typed positional attacks (rebut / undercut / undermine, `w@π`) | §7, **§7.1** | **Frozen (def)** | ✅ typing rules written (§7.1); ✅ Lean port landed (`lean/Lara/Attack.lean`) — pending: executable checker, compile-facing edge soundness | §9 r1 (strict-unattackability, partition, coherence ✅; decision procedure pending), r4 (with item 11) |
| 10 | Holes (open obligations) | §4.2, §10 | **Lock** | confirm hole surface + located reporting are v0.1-fixed | §9 r1 |
| 11 | Compilation `compile(P) = AF` + subargument closure | §8 (**compilation rules**) | **Frozen (def)** | ✅ compile rules written (§8, v0.1-frozen); ✅ Lean port landed (`lean/Lara/Compile.lean`) — pending: executable edge oracle (`Faithful`), r9 | §9 r4 both halves ✅; r6 source-vs-compiled bridged oracle-parametrically ✅; r9 pending |
| 12 | Grounded labelling + four-state aggregation | §8, §8.2 | **Frozen** | none | §9 r5, r6, r7 — **done abstract** (`Grounded.lean`); compile-composed step pending |
| 13 | Abstract syntax + JSON wire schema, **versioning** | §1, §2 | **Lock** | assign v0.1 version ids (`Sigma`, `Pi`, backends, JSON schema); codec round-trip contract | §9 r12 |
| 14 | Specified rejection behavior (located, per rejection class) | §1, §10 | **Lock** | enumerate the rejection classes (mutation-suite spine) as v0.1 | §9 r1 (decidability) |

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

## Exit action

1. Complete the **Lock** rows above in one spec pass (items 3, 5, 8–11, 13, 14).
2. Absorb the four M0 conditions.
3. Tag the spec **v0.1** and lift the "Phase 0 / WIP" header.
4. Open the **M2 mechanization backlog** for every newly frozen corpus-independent definition —
   per CLAUDE.md discipline, port as each freezes, do not batch to a later milestone. The pending
   obligations are: compile relation (§9 r4, r6-composed, r9) and each shipped adapter (§9 r10).

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
land._
