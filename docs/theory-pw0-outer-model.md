# Theory PW0: the possible-world outer-model gate

_Status: mechanized for the possible-world semantics spike on 2026-09-02
(issue #192, tracker #189). This document records what PW0 froze, what it
proved, what it deliberately left out, and the three limitations of the frozen
contract that its successors inherit._

_The spike's motivating question: when two artifacts check in different
contexts — different vocabularies, policies, settings — what can be compared
or transported between them, and under what declared bridge? The outer model
wraps unchanged local judgments in a frame of worlds to make that question
statable. `theory-pw-closeout.md` indexes the four PW records._

The intended readers are the paper author, whoever takes the exit decision on
#192, and whoever implements T6 (#191). They should cite the declarations below
rather than re-deriving them; `docs/paper-lean-name-map.md` §PW0 carries the
stable keys.

PW0 adds an outer comparison layer over **unchanged** local Lara judgments.
No local checking, compilation, grounded labelling, or status behavior was
redefined: the five new modules only import. The canonical design source is
`lara-paper/plan/possible-world-semantics-brainstorm.md`.

## 1. What PW0 froze

**Frame plus valuation, not one monolithic model.** `PW.Frame`
(`lean/Lara/PW/Outer.lean`) carries contexts `K`, bridges `B` with `src`/`tgt`,
per-context `World` and `Query`, the candidate relation `R`, the applicability
judgment `accept`, and the claim translation `translate`. The valuation is
*not* a frame field: it is a parameter of `PW.Sat`. The design's T4 instantiates
one parameterized model twice, `M[V := V^src]` and `M[V := V^cmp]`; making the
valuation a parameter states that parameterization once instead of duplicating
the model. The accepted-edge relation is `A_b = R_b ∩ accept_b`
(`PW.Frame.A`), fixed per bridge and independent of the formula being
evaluated — the condition that supports normal modal logic.

**Satisfaction is formula-first.** The Lean is `Sat F V φ w`, where the paper
writes `M, w ⊨ φ`. This is forced, not stylistic. With the world argument
first, the context index `κ` is determined by no earlier argument — a world
does not name its context — so the `box`/`dia` arms fail to elaborate with

```
Type mismatch: Form.box b φ has type Form ?m (Frame.src ?m b)
but is expected to have type Form F ?m
```

Naming the index explicitly (`∀ {κ : F.K}, …`) and making it an explicit binder
both fail identically. Putting the formula first lets the match refine `κ` from
the constructor. `PW.KSat` follows the same order so both sides of T3 read
alike. The name map carries a row stating this correspondence explicitly.

**Queries are all of `Atom`.** The design refines `Query_κ` to well-sorted
claims over `Σ_κ`. Both status observations are total on `Atom` (a query with
no matching retained node has empty complete support, hence `gap`), so PW0
takes the total query set and defers well-sortedness to the surface layer
(M5-gated). See limitation 2 below for the cost.

**Translations are bridge-global and partial** (`translate : (b : B) → Query
(src b) → Option (Query (tgt b))`), the design's explicitly chosen first-model
restriction. Edge-dependent translation is the documented fallback and is not
mechanized; see limitation 3.

**The primitive modalities do not translate their operands.** Translation
appears only in derived formulas. That is what keeps each accepted relation
formula-independent, and hence the logic normal (T2).

**`crossCompare`'s guard order is translation, then candidates, then acceptance**
(`lean/Lara/PW/Compare.lean`). It is generic over world and query types and
takes the finite candidate list, the decidable acceptance, and the target
status function as *explicit inputs* — the frame's `R`/`accept` are
`Prop`-valued and carry no enumeration, and the design is explicit that no
executability claim applies to an implicit set of admissible states without an
effective finite representation.

**`Presents` is the obligation that makes `crossCompare` an implementation rather
than a lookalike.** Nothing in `crossCompare`'s type says the candidate list
enumerates `R_b(w, ·)` or that `acceptB` decides `accept_b(w, ·)`; it takes
them on trust. `PW.Presents` states that obligation, and
`PW.mem_compare_iff_sat_dia` then proves the executable interface computes the
model's `⟨b⟩`. Without it, `crossCompare` and `Sat` are two unconnected islands and
`Frame.translate` is a field no definition reads.

**A `Prop`-valued valuation does not by itself say a claim has one status.**
`PW.Valuation.Functional` and `.Total` name that side condition. A model
satisfying every T2 law can otherwise make `Justified(c) ∧ Defeated(c)` true;
such a model is not a Lara model.

## 2. Theorem table

Every row is `lean/AxCheck.lean`-gated: sorry-free, within the standard trio
`propext` / `Classical.choice` / `Quot.sound`, no `native_decide` (which would
add `ofReduceBool`). Fifty-four theorems were registered — every theorem the
five modules declare, with no exceptions.

| # | Content | Lean declaration | File |
|---|---|---|---|
| T0 | Current-Lara conservativity, compiled side | `PW.Instance.t0_cmp` | `Lara/PW/Instance.lean` |
| T0 | Current-Lara conservativity, source side | `PW.Instance.t0_src` | `Lara/PW/Instance.lean` |
| T1 | World-local source/compiled preservation | `PW.Instance.srcStatus_iff_cmpStatus` | `Lara/PW/Instance.lean` |
| T2 | Derived implication semantics | `PW.sat_imp` | `Lara/PW/Outer.lean` |
| T2 | Typed K | `PW.sat_K` | `Lara/PW/Outer.lean` |
| T2 | Typed necessitation | `PW.sat_nec` | `Lara/PW/Outer.lean` |
| T2 | Duality `⟨b⟩φ ↔ ¬[b]¬φ` | `PW.sat_dia_iff_not_box_neg` | `Lara/PW/Outer.lean` |
| T2 | Top preservation | `PW.sat_box_top` | `Lara/PW/Outer.lean` |
| T2 | Finite-meet preservation | `PW.sat_box_conj` | `Lara/PW/Outer.lean` |
| T2⁻ | **Every stronger frame axiom fails** (normal, and no more): T, D, B, 5 on one frame, 4 on a chain | `Examples.PW.sat_T_fails`, `sat_D_fails`, `sat_B_fails`, `sat_5_fails`, `sat_4_fails` | `Lara/Examples/PW.lean` |
| T3 | Uniform-language reduction to multimodal Kripke | `PW.sat_lift` | `Lara/PW/Uniform.lean` |
| T4 | Valuation congruence (generic core) | `PW.sat_congr` | `Lara/PW/Outer.lean` |
| T4 | Modal source/compiled coherence | `PW.Instance.sat_src_iff_cmp` | `Lara/PW/Instance.lean` |
| T4 | Worked instances of the congruence, both readings | `Examples.PW.t7_dia_defeated_src`, `t7_box_defeated_src` | `Lara/Examples/PW.lean` |
| T5 | Undefined translation | `PW.compare_none`, `PW.compare_translationUndefined_iff` | `Lara/PW/Compare.lean` |
| T5 | No candidate world | `PW.compare_no_candidate` | `Lara/PW/Compare.lean` |
| T5 | All candidates rejected | `PW.compare_all_rejected` | `Lara/PW/Compare.lean` |
| T5 | Comparable profile | `PW.compare_comparable`, `PW.mem_compare_profile_iff` | `Lara/PW/Compare.lean` |
| T5 | Constructor disjointness (gate 3, structural) | `PW.incomparable_ne_comparable` | `Lara/PW/Compare.lean` |
| T5 | Adequacy: the profile *is* `⟨b⟩` | `PW.mem_compare_iff_sat_dia` | `Lara/PW/Compare.lean` |
| T5 | Gate 3, semantically: incomparable ⇒ no accepted witness | `PW.not_sat_dia_of_incomparable` | `Lara/PW/Compare.lean` |
| T5 | The presentation obligation, discharged at a real bridge | `Examples.PW.presentsT7` | `Lara/Examples/PW.lean` |
| T5 | Adequacy round trip: `crossCompare` ⇒ `⟨b⟩`, on that bridge | `Examples.PW.t7_dia_via_adequacy` | `Lara/Examples/PW.lean` |
| T5 | Gate 3's semantic arm, discharged at a rejected bridge | `Examples.PW.presentsOverlapRejected`, `overlap_rejected_no_dia` | `Lara/Examples/PW.lean` |
| — | Valuation coherence, compiled | `PW.Instance.cmpVal_functional`, `cmpVal_total` | `Lara/PW/Instance.lean` |
| — | Valuation coherence, source (**only through T1**) | `PW.Instance.srcVal_functional`, `srcVal_total` | `Lara/PW/Instance.lean` |
| — | No world reports two statuses | `PW.not_sat_two_status` | `Lara/PW/Outer.lean` |
| — | …instantiated at a Lara bridge | `Examples.PW.t7_no_two_status` | `Lara/Examples/PW.lean` |
| T7 | Status non-preservation witness | `Examples.PW.t7_witness` | `Lara/Examples/PW.lean` |
| T7 | The `⟨b⟩` reading | `Examples.PW.t7_dia_defeated` | `Lara/Examples/PW.lean` |
| T7 | The `[b]` reading | `Examples.PW.t7_box_defeated` | `Lara/Examples/PW.lean` |
| T7 | The transport is the identity on the source support | `Examples.PW.t7_support_transported` | `Lara/Examples/PW.lean` |
| — | The local `gap` gate 3 declines to report | `Examples.PW.overlap_local_gap` | `Lara/Examples/PW.lean` |

**T1 is the substantive theorem, and its two sides are independently defined.**
`PW.Instance.srcStatus` is the relational, oracle-free `Compile.SrcStatus`,
read off `SrcIn`/`SrcOut` with no compiled framework, no grounded labelling,
and no enumeration. `PW.Instance.cmpStatus` is the executable
`Grounded.statusC` over `Compile.checkedAF`. Neither is defined through the
other. Their agreement is `Compile.srcStatus_iff_checked` — Lara's existing
source-to-compilation preservation chain — instantiated at the world.

**T4 is an integration theorem, not an independent Lara result.**
`sat_congr` is a routine structural induction whose content is that
satisfaction is extensional in the atomic valuation; the substantive result
underneath it is T1. It is stated over the *same* frame, so the accepted
relations are literally shared and the modal cases move across for free. That
is what makes it a genuine lifting theorem rather than definitional
duplication. `t7_dia_defeated_src` is its worked instance — a congruence
theorem with no instance can be true and useless.

**T7's content.** One context (`ctxT7`, whose defeat table declares `q`
contrary to `p`), two accepted worlds. The source world admits only the `p`
argument and justifies `p`. The target world admits the same `p` argument plus
one unattacked `q` attacker with the required typed undermine edge, and
defeats `p`. The transported support term `SupportTerm.leaf l1` remains a
checked argument of the target program (`t7_transport_wellFormed`), and the
transport really is the identity on the source claim's support rather than
mere coincidental membership: source and target complete supports for `p` are
the same nonempty index set `[0]`, and that shared index resolves through both
retained node caches — the structure support indices actually index — to the
same term `leaf l1` (`t7_support_transported`). So
transporting well-formed support does **not** transport grounded status: status
preservation needs strictly more than support transport, which fixes the
boundary between T6 (exact support transport, future) and T8.

The witness exists at all only because the missing-conflict search is
directional: `firstMissingConflict?` (`Lara/Check/Program.lean:294-317`) tests
`contraryMatchB canon dp source.conclusion target.conclusion` in one direction,
so the contrary pair demands the edge `q → p` and no reverse edge. A forced
symmetric edge would leave `p` *contested* rather than defeated.

## 3. Gate assessment

The five advancement-gate conditions of #189 / #192:

1. **The wrapper changes no local checking, compilation, grounded labelling, or
   status behavior.** Mechanized as an import discipline and verified by the
   diff: the only Lean files `git diff main` touches are the new `Lara/PW/*`
   and `Lara/Examples/PW.lean` modules plus the two roots `Lara.lean` and
   `AxCheck.lean`, and the diff is pure insertion — no deletions, and no
   existing semantics module changed. T0 (`t0_cmp` /
   `t0_src`) states the same thing internally: in the bridge-free singleton
   embedding, atomic satisfaction is *definitionally* the unchanged local status
   judgment — `Iff.rfl` is the whole proof, because there is no
   wrapper-introduced layer to unfold, and with `B := Empty` the language
   contains no modal formula at all.

2. **T1 compares independently defined observations.** Discharged as described
   above: a relation versus a function, neither defined through the other, with
   the existing preservation chain as the bridge. The asymmetry is visible in
   the coherence discharges — `cmpVal_functional` is `h₁ ▸ h₂` against a total
   function, while `srcVal_functional` must route through T1 twice.

3. **Incomparability cannot collapse into a local status.** Enforced three
   ways. *Structurally*: `CrossResult` keeps reasons and profiles in different
   constructors, `IncomparabilityReason` contains no `Status`, so no coercion
   exists to build, and `incomparable_ne_comparable` records the disjointness.
   *Behaviorally*: each reason is pinned to exactly its defining condition, and
   the profile to exactly the statuses of accepted candidate worlds
   (`mem_compare_profile_iff`). *Semantically*: `not_sat_dia_of_incomparable`
   shows that with the translation defined, an incomparable result means the
   model has no accepted witness at all, for any status — a condition no local
   status could report — and `overlap_rejected_no_dia` discharges it at a
   concrete `Presents`-verified bridge (`presentsOverlapRejected`), so the
   semantic arm has a worked instance just as the adequacy theorem does.
   Nonemptiness of the profile is structural too:
   `comparable` carries a first element and a rest, never a bare list.

4. **The T7 counterexample is expressible and checked.** Every *decidable*
   example fact is closed by `decide`; the rest — `t7_witness`, the four
   reading × valuation cells (`t7_dia_defeated`, `t7_box_defeated`,
   `t7_dia_defeated_src`, `t7_box_defeated_src`), `presentsT7`,
   `t7_dia_via_adequacy`, `t7_no_two_status`, `presentsOverlapRejected`,
   `overlap_rejected_no_dia`, and the five frame-axiom refutations
   (`sat_T_fails`, `sat_D_fails`, `sat_B_fails`, `sat_5_fails`,
   `sat_4_fails`) — are ordinary term or tactic proofs. `native_decide` is
   banned and appears nowhere: it adds `ofReduceBool` and fails the audit. The
   whole example module — three `checkUnit` runs and twelve `decide`-closed
   theorems — builds in under three seconds.

5. **No approximation bridges, epistemic relations, dynamic updates,
   named-world operators, global scenarios, or surface syntax.** None is
   present; see §5.

## 4. Known limitations of the frozen contract

These are design commitments of PW0, not oversights. Each has a named
successor.

**1. `accept` is an arbitrary `Prop`.** Nothing ties it to a checker, to a
certificate, to a soundness condition, or even to `R`. The name promises more
than the model supplies. PW0 posits *no* connection between applicability and
any Lara judgment; supplying that connection is the structural-bridge work of
T6, deliberately out of scope here.

**2. `gap` conflates four conditions** — *out of vocabulary*, *ill-sorted*,
*not posed*, and *posed but unsupported* — because queries are all of `Atom`
(§1). Modal instability at a `gap` may therefore reflect a vocabulary mismatch
rather than a scientific disagreement, and a reader must not read `⟨b⟩Gap(c)`
as "the target field considered this and found it unsupported". The executable
layer separates only the bridge-domain case, and reports it as
`translationUndefined` rather than as any status — which is exactly what
`overlap_translationUndefined` fixes for the source-only claim `s`. The rest
waits on the M5 well-sortedness refinement.

_Narrowed, not closed, by #307 (`docs/theory-pw-sorted-queries.md`)._ Refining
`Query_κ` to well-sorted claims over `Σ_κ` removes the two Σ-level conditions:
an out-of-vocabulary or ill-sorted atom is not a query, so `PW.Sorted.pose`
reports it — naming which — before any world is consulted, and
`PW.Sorted.notPosable_world_independent` proves that verdict depends on no
world at all. `translationUndefined` is likewise split, into *outside the
bridge's symbol map* and *the target field cannot state this*. The remaining
two conditions **coincide in this model, by theorem**: every argument an
accepted unit retains is complete, and `Grounded.statusC` gaps exactly on empty
complete support, so `PW.Sorted.cmpStatus_gap_iff_not_addresses` reads the
residual `gap` off one precise condition — the world declares no complete
argument concluding the claim — and `PW.Sorted.not_gap_of_addresses` says
nothing else produces one. Separating an incomplete attempt from an absent one
would need `holes(P, p)` at the instance layer, which
`Consistency.completeClaimFor` deliberately does not compute. So the count goes
from four conflated conditions to two reported ones plus a proved collapse, and
no display may call this limitation closed.

**3. `Context` fixes the checking environment, not a scientific state.** A
`Context` is (Σ, Policy, Registry) plus the checker parameters; two worlds of
one context may differ in program, admitted evidence, declared supports, and
attacks. That is intended — it is what makes `⟨b⟩` and `[b]` non-trivial
*within* a context, and the T7 witness is exactly such a pair. But "world of
this context" must not be read as "this artifact". Nothing pins the program.

## 5. What PW0 deliberately does not contain

Read as of PW0. The first three rows have since landed — T6 (#191), T8 (#193),
and T9 (#190) — and tracker #189 is closed; `docs/theory-pw-closeout.md` is the
spike index and the home of everything the tracker deferred.

| Absent | Home |
|---|---|
| Structural bridges, T6 (exact checked-support transport) | **#191**, gated by the #192 exit decision on tracker #189 |
| T8 (conditional status preservation) | **#193** |
| T9 (exact structural-path composition) | **#190** |
| T10 and beyond | `docs/theory-pw-closeout.md` §3 (moved there when tracker #189 closed) |
| Approximation bridges | `docs/theory-pw-closeout.md` §3 |
| Epistemic relations, dynamic update operators, hybrid/named-world operators | `docs/theory-pw-closeout.md` §3 |
| Global scenarios | `docs/theory-pw-closeout.md` §3 |
| Surface syntax for the outer language | **Landed** (#307) — `docs/theory-pw-sorted-queries.md` |
| Well-sortedness refinement of `Query_κ` | **Landed** (#307) — `docs/theory-pw-sorted-queries.md`; limitation 2 above |
| Sensitivity predicates (`WorldSensitive`, `ContextSensitive`) | In the design doc but **not** in #192's Work list — excluded as YAGNI |
| Stronger modal laws (T, 4, B, D, 5) | Not posited; they belong only to bridges whose accepted relations satisfy the corresponding relational laws. All five are refuted on PW0-legal frames: `sat_T_fails`, `sat_D_fails`, `sat_B_fails`, `sat_5_fails` (two-world frame), `sat_4_fails` (three-world chain) |

## 6. T6 feasibility note (#191)

Input to the #192 exit decision; the decision itself is taken on the issue, not
here. The work this section sizes is tracked by **#191** (*theory(PW-T6):
prove exact checked-support transport*); its two successors are **#193** (T8,
conditional status preservation — the theorem whose boundary `t7_witness`
fixes) and **#190** (T9, exact structural-path composition).

A `StructuralBridge` contract would need, from B0's occurrence-level
obligations, enough to relate a source support term's occurrences to target
occurrences under the target context's signature — which is where the
bridge-global `Option` translation breaks first.

**The concrete case a bridge-global `Option` cannot express.** Take a source
atom naming an entity by an obsolete alias. One target world under the bridge
carries the ontology version that resolves that alias; another target world
under the *same* bridge does not. A single global `translate b : Query (src b)
→ Option (Query (tgt b))` must answer once for both, and either answer is
wrong at one of the two worlds. The edge-indexed successor is a relation

```
Translate : (b : B) → World (src b) → World (tgt b) →
              Query (src b) → Query (tgt b) → Prop
```

which also admits *ambiguity* — several target queries for one source query —
that `Option` forbids by construction. Moving to it is a genuine contract
change, not a refinement: `mem_compare_iff_sat_dia` and
`compare_translationUndefined_iff` are both stated against the `Option` form,
and the executable `crossCompare` takes a single `Option Q` as its first guard.
Budget the change accordingly.
