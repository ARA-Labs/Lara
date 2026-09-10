# Theory PW-T8: conditional status preservation

_Status: mechanized on 2026-09-04 (issue #193, tracker #189). This document
records the status-preservation hypotheses frozen by T8, the consequences it
proves, and the boundary it leaves to later work._

_Part of the possible-world spike (comparing artifacts across differing
contexts); start from `theory-pw-closeout.md` for the subseries index — T8
layers over T6 and T9._

The intended readers are the paper author, whoever takes decisions on tracker
#189, and anyone extending or citing structural bridges to status. They should
cite the declarations below rather than reconstructing the hypotheses from
implementation details; `docs/paper-lean-name-map.md` §PW-T8 carries the
stable keys.

T8 adds a status layer over the exact structural layer frozen by T6 and
composed by T9. Its generic core is `Lara/PW/AFBisim.lean` (frameworks and
relations only — no support term, bridge, or world), its instantiation at
structural bridges is `Lara/PW/Status.lean`, and executable conformance
witnesses are in `Lara/Examples/PWStatus.lean`. All three modules only
import: nothing in the checker, compilation, grounded labelling, local status,
the PW0 outer model, T6, or T9 was modified.

The design being mechanized is
`lara-paper/plan/possible-world-semantics-brainstorm.md` §Status-Preserving
Bridge and §T8 (external to this repository, as for PW0, T6 and T9). Its
vocabulary — `RobustlyJustified`, `PossiblyJustified`, `Comparable`,
`Translatable`, `Reachable` — is quoted here for citation and is not
defined by any Lean declaration; the Lean hypotheses those names correspond
to are given where each is used.

## 1. What T8 froze

**The primitive is a total attack bisimulation, not an isomorphism.**
`PW.AttackBisim F G Z` relates two finite frameworks through a relation `Z`
on argument ids with five clauses: `dom` (`Z` relates carrier members only),
`left_total` (every source argument is related to a target argument),
`right_total` (every target argument is related to a source argument),
`forth` (a source attacker of a related argument is matched by a related
target attacker), and `back` (a target attacker of a related argument is
matched by a related source attacker). Grounded labels and the four-state
status are invariant under such a relation (`labelC_of_bisim`,
`statusC_of_bisim`).

The design's AF isomorphism is `PW.AFIso F G f` — the graph of a bijection
that preserves and reflects attack (fields `maps`, `inj`, `surj`,
`attack_iff`) — and `AFIso.toBisim` shows its graph is a bisimulation, so
the isomorphism route (`statusC_of_iso`) is a corollary. **The `inj` field is
consumed by no proof.** Both right-totality and the `back` clause of the
induced bisimulation are discharged by `surj` alone: a target attacker must
be exhibited as an `f`-image before `attack_iff` can reflect it, and nothing
ever needs two source arguments with the same image to be equal. The design's
isomorphism is therefore strictly stronger than what status preservation
requires; a surjective bounded morphism already suffices. `inj` is recorded
because it is what "isomorphism" means, and it stays recorded so the
design's vocabulary remains citable.

**At a structural bridge the relation is index-level.** Compiled arguments
are list positions (`Compile.toAF`), so the relation the bisimulation lives
on is `PW.Corr m lm w v i j`: the `i`-th argument of the source world's
accepted program transports under `trSupport m lm` to the `j`-th argument of
the target world's. The T8 hypotheses are the four fields of
`PW.StatusBridge m lm w v`:

- `admits`: T6's `Admits` — every source argument transports into the target
  program (left-totality of `Corr`);
- `matched`: every target argument *is* a transport of some source argument
  (right-totality) — the clause that excludes unmatched target supports and
  attackers, and the one the T7 target violates;
- `forth` and `back`: the attack conditions, stated on the compiled edge
  decider `Compile.edgeB` — a source attacker of a `Corr`-related argument is
  matched by a target attacker of its counterpart, and conversely.

```text
source: checkedAF w.unit.program        target: checkedAF v.unit.program

     k --edgeB--> i  ---- Corr i j ----  j <--edgeB-- k'

forth: from a source edge k → i and Corr i j, find k' with Corr k k'
       and a target edge k' → j
back:  from a target edge k' → j and Corr i j, find k with Corr k k'
       and a source edge k → i
```

`StatusBridge.bisim` shows these four clauses are exactly an `AttackBisim` of
the two `checkedAF`s under `Corr`. Nothing in the `StructuralBridge` contract
implies any of them; that is the point.

**The support-set correspondence is derived, not assumed.** For every
translatable query `c` with `trAtom B.sym c = some c'`, `PW.claimSupport_corr`
proves `SupportCorr (Corr …) (claimAt w c) (claimAt v c')` from the contract
and the hypotheses. Its forward half runs T6 transport and `equiv_tr` through
`corr_conclusion` (the target node's conclusion at a related index *is* the
translated source conclusion, by `hasSupport_unique`); its backward half runs
`matched` and `equiv_tr_reflect`, and it is the backward half that needs
`PW.SymMap.Injective`. `PW.status_transport` is the headline for injective
bridges; `PW.status_transport_of_corr` is the theorem for bridges whose
translation is not injective but whose support correspondence is supplied by
other means.

**Three findings from mechanization**, recorded for future readers:

1. `AFIso.inj` is never consumed (above); the frozen primitive is the
   bisimulation.
2. `StatusBridge.forth`/`back` drop `AttackBisim`'s `b ∈ F.args` premise on
   the attacker; `StatusBridge.bisim` discards it. An instance discharging
   these fields must therefore recover in-rangeness of the attacker index
   itself, via `(Compile.edgeB_faithful P).ranged`. Every executable witness
   in `Lara/Examples/PWStatus.lean` does exactly this.
3. The two layers' composition operators take their legs in opposite orders —
   `StatusBridge.comp h₁ h₂` in path order, T9's `StructuralBridge.comp B₂ B₁`
   in function-composition order (§6).

## 2. Theorem table

Every public theorem declared by the five modules appears below. Definition
rows are included to identify the objects those theorems constrain; they are
audited transitively through the gated theorems that mention them.

Generic layer, `Lara/PW/AFBisim.lean`:

| Result | Declaration | File |
|---|---|---|
| Total attack bisimulation and its converse | `PW.AttackBisim` (fields `dom`, `left_total`, `right_total`, `forth`, `back`); `PW.AttackBisim.symm` | `Lara/PW/AFBisim.lean` |
| The declarative grounded judgments transfer along a bisimulation | `PW.directIn_bisim`, `PW.directOut_bisim`; iff forms `PW.directIn_iff_of_bisim`, `PW.directOut_iff_of_bisim` | `Lara/PW/AFBisim.lean` |
| Grounded labels are bisimulation-invariant | `PW.labelC_of_bisim` | `Lara/PW/AFBisim.lean` |
| Complete-support correspondence and the status congruence it feeds | `PW.SupportCorr`; `PW.statusC_congr` | `Lara/PW/AFBisim.lean` |
| Four-state status is bisimulation-invariant on corresponding claims | `PW.statusC_of_bisim` | `Lara/PW/AFBisim.lean` |
| The design's AF isomorphism and its graph | `PW.AFIso` (fields `maps`, `inj`, `surj`, `attack_iff`); `PW.AFIso.graph` | `Lara/PW/AFBisim.lean` |
| An isomorphism is a bisimulation (`inj` unused) | `PW.AFIso.toBisim` | `Lara/PW/AFBisim.lean` |
| Labels and status along an isomorphism | `PW.labelC_of_iso`, `PW.statusC_of_iso` | `Lara/PW/AFBisim.lean` |
| The design's "onto the complete support set" yields the correspondence | `PW.supportCorr_of_image` | `Lara/PW/AFBisim.lean` |

Instantiation at structural bridges, `Lara/PW/Status.lean`:

| Result | Declaration | File |
|---|---|---|
| Injectivity-where-defined of a partial translation, and the identity | `PW.SymMap.Injective`; `PW.SymMap.id_injective` | `Lara/PW/Status.lean` |
| An injective translation is injective on terms, term lists, and atoms | `PW.trTerm_inj`, `PW.trTerms_inj`, `PW.trAtom_inj` | `Lara/PW/Status.lean` |
| `≡` reflects along an injective translation (converse of T6's `equiv_tr`) | `PW.equiv_tr_reflect` | `Lara/PW/Status.lean` |
| The index relation a translation induces, and its range bound | `PW.Corr`; `PW.corr_lt` | `Lara/PW/Status.lean` |
| The T8 hypotheses | `PW.StatusBridge` (fields `admits`, `matched`, `forth`, `back`) | `Lara/PW/Status.lean` |
| The hypotheses are a bisimulation of the compiled frameworks | `PW.StatusBridge.bisim` | `Lara/PW/Status.lean` |
| Target conclusion at a related index is the translated source conclusion | `PW.corr_conclusion` | `Lara/PW/Status.lean` |
| Derived support-set correspondence for every translatable query | `PW.claimSupport_corr` | `Lara/PW/Status.lean` |
| Status preservation from a supplied correspondence | `PW.status_transport_of_corr` | `Lara/PW/Status.lean` |
| **T8 — conditional status preservation** | `PW.status_transport` | `Lara/PW/Status.lean` |
| T8 at the source observation (T1 on both sides) | `PW.srcStatus_transport` | `Lara/PW/Status.lean` |
| The modal reading: `[b]` and `⟨b⟩` collapse to the local atom | `PW.sat_status_iff_box`, `PW.sat_status_iff_dia`, `PW.sat_status_iff_box_src` | `Lara/PW/Status.lean` |
| Injectivity is closed under Kleisli composition | `PW.SymMap.Injective.comp` | `Lara/PW/Status.lean` |
| `Corr` along the composite factors through the intermediate world | `PW.corr_comp_iff` | `Lara/PW/Status.lean` |
| Status bridges compose along the T9 composite | `PW.StatusBridge.comp` | `Lara/PW/Status.lean` |
| Declared-attack translation and its list lift | `PW.trAttack`, `PW.trAttackList`; `PW.trAttackList_cons` | `Lara/PW/AttackTransport.lean` |
| Translation injectivity on support terms, and equality reflection | `PW.trSubst_inj`, `PW.trSupport_inj`, `PW.trSupportList_inj`, `PW.trSupportDis_inj`, `PW.trSupport_eq_iff` | `Lara/PW/AttackTransport.lean` |
| Positional navigation commutes with translation | `PW.lookupDis_trSupportDis`, `PW.trSupport_subterm`, `PW.trSupport_subterm_some` (helpers `PW.trSupport_leaf`, `PW.trSupport_inst_inv`, `PW.lookupDis_mem`, `PW.trSupportList_some_of_mem`, `PW.trSupportDis_some_of_mem`) | `Lara/PW/AttackTransport.lean` |
| Containment, attack closure, and declared-edge coverage are translation-invariant under injectivity | `PW.containsB_trSupport`, `PW.containsBList_trSupport`, `PW.containsBDis_trSupport`, `PW.trAttack_source`, `PW.attackClosureB_trAttack`, `PW.coveredB_trAttack` | `Lara/PW/AttackTransport.lean` |
| The `Contains`/`AttackOcc` Prop faces | `PW.Contains_trSupport`, `PW.AttackOcc_trSupport` | `Lara/PW/AttackTransport.lean` |
| T8's attack hypotheses on the source language, and the index-level clauses derived | `PW.AttackBridge`; `PW.AttackBridge.toStatusBridge` | `Lara/PW/AttackTransport.lean` |

Executable decider, `Lara/PW/StatusCheck.lean` (issue #239):

| Result | Declaration | File |
|---|---|---|
| `Corr`, `Admits`, and the matched conjunct as `Bool` scans over the shared transport test, with their Prop reflections | `PW.corrB`, `PW.admitsB`, `PW.matchedB`; `PW.transportsB`; `PW.corrB_iff`, `PW.admitsB_iff`, `PW.matchedB_iff`, `PW.transportsB_iff` | `Lara/PW/StatusCheck.lean` |
| `forth`/`back` as one directed bisimulation scan at the two orientations, with the range bound of a `true` `corrB` cell | `PW.bisimScanB`; `PW.forthB`, `PW.backB`; `PW.corrB_lt` | `Lara/PW/StatusCheck.lean` |
| The scan is sound and complete, once generically and once per orientation | `PW.bisimScanB_sound`, `PW.bisimScanB_complete`; `PW.forthB_sound`, `PW.forthB_complete`, `PW.backB_sound`, `PW.backB_complete` | `Lara/PW/StatusCheck.lean` |
| The `StatusBridge` decider (a four-way `&&` of the scans) | `PW.statusBridgeB` | `Lara/PW/StatusCheck.lean` |
| The decider decides `StatusBridge` exactly | `PW.statusBridgeB_sound`, `PW.statusBridgeB_complete`, `PW.statusBridgeB_iff` | `Lara/PW/StatusCheck.lean` |

Two shape decisions, recorded from the executed checker plan (#239). A
`Decidable (StatusBridge …)` instance was rejected: `StatusBridge`
quantifies unboundedly over `Nat`, so it is not decidable as stated — a
`Bool` checker with a sound/complete pair is the correct shape, matching
`edgeB`/`edgeB_faithful`. And `StatusBridge.back` is `StatusBridge.forth`
with the two sides swapped, so the directed scan, its soundness, and its
completeness are written once over abstract `Nat → Nat → Bool` relations
(`bisimScanB`) and instantiated at the two orientations, rather than
duplicating ~40 lines of mirrored tactic proof.

`status_transport` states: for contexts `κ`, `λ` with `λ.canon = κ.canon`
(`hcanon`, T6's shared-canonicalizer commitment), a structural bridge `B`
between them, worlds `w : World κ` and `v : World λ` with
`StatusBridge B.sym B.leafMap w v` and `B.sym.Injective`, and any `c`, `c'`
with `trAtom B.sym c = some c'`: `cmpStatus v c' = cmpStatus w c`.

Executable witnesses, `Lara/Examples/PWStatus.lean` (namespace
`Lara.Examples.PW.Status`):

| Witness | Declaration | File |
|---|---|---|
| The T7 identity edge satisfies `forth` (vacuously: no source attacks) | `Examples.PW.Status.t7_forth` | `Lara/Examples/PWStatus.lean` |
| The T7 target's attacker is unmatched: `matched` fails at `leaf l2` | `Examples.PW.Status.t7_l2_mem`, `t7_unmatched`, `t7_not_statusBridge` | `Lara/Examples/PWStatus.lean` |
| The same, by T8's contrapositive from the status flip alone | `Examples.PW.Status.t7_not_statusBridge_of_flip` | `Lara/Examples/PWStatus.lean` |
| A forward attack homomorphism is insufficient | `Examples.PW.Status.t7_forward_hom_insufficient` | `Lara/Examples/PWStatus.lean` |
| Source context over the empty registry and its two accepted worlds | `Examples.PW.Status.regEmpty`, `ctxS`, `wS1`, `wS2`; `unitS1_accepted`, `unitS2_accepted` | `Lara/Examples/PWStatus.lean` |
| Renamed context, vocabulary, policy, and its two accepted worlds | `Examples.PW.Status.pR`, `qR`, `sR`, `ΓR`, `sigmaR`, `polR`, `ctxR`, `wR1`, `wR2`; `unitR1_accepted`, `unitR2_accepted` | `Lara/Examples/PWStatus.lean` |
| The renaming translation, leaf map, and structural bridge off the identity | `Examples.PW.Status.symR`, `leafMapR`, `bridgeR`; `symR_injective` | `Lara/Examples/PWStatus.lean` |
| Status bridges between the one-argument and the attacked two-argument worlds | `Examples.PW.Status.s1_r1_statusBridge`, `s2_r2_statusBridge` | `Lara/Examples/PWStatus.lean` |
| `justified` transports, with both cells evaluated | `Examples.PW.Status.t8_justified_preserved`, `t8_justified_cells` | `Lara/Examples/PWStatus.lean` |
| `defeated` transports through a real matched attacker, with both cells | `Examples.PW.Status.t8_defeated_preserved`, `t8_defeated_cells` | `Lara/Examples/PWStatus.lean` |
| `gap` transports on the unsupported claim, with both cells | `Examples.PW.Status.t8_gap_preserved`, `t8_gap_cells` | `Lara/Examples/PWStatus.lean` |
| `contested` transports, with both cells evaluated (symmetric contraries, two matched attacks each way) | `Examples.PW.Status.polS3`, `ctxS3`, `wS3`, `polR3`, `ctxR3`, `wR3`, `bridgeR3`; `unitS3_accepted`, `unitR3_accepted`, `s3_corr_diag`, `s3_r3_statusBridge`; `t8_contested_preserved`, `t8_contested_cells` | `Lara/Examples/PWStatus.lean` |
| The transported claim is genuinely renamed | `Examples.PW.Status.t8_renamed` | `Lara/Examples/PWStatus.lean` |
| Two-context bridge data, its accepted edge, and every successor bridged | `Examples.PW.Status.bridgeDataR`; `r_edge_accepted`, `r_all_bridged` | `Lara/Examples/PWStatus.lean` |
| The `[b]` cell at `defeated`, and its inhabitation | `Examples.PW.Status.t8_box_defeated_r`, `t8_box_defeated_r_holds` | `Lara/Examples/PWStatus.lean` |

Decider conformance cells, `Lara/Examples/PWStatusCheck.lean` (namespace
`Lara.Examples.PW.StatusCheck`, issue #239):

| Witness | Declaration | File |
|---|---|---|
| The three positive bridges re-established by one `decide` each | `Examples.PW.StatusCheck.s1_r1_decider`, `s2_r2_decider`, `s3_r3_decider` | `Lara/Examples/PWStatusCheck.lean` |
| Soundness turns a decider cell back into the Prop-level bridge | `Examples.PW.StatusCheck.s2_r2_statusBridge_via_decider` | `Lara/Examples/PWStatusCheck.lean` |
| The T7 negative through the decider: a `false` scan, refuted via completeness | `Examples.PW.StatusCheck.t7_decider_rejects`, `t7_not_statusBridge_via_decider` | `Lara/Examples/PWStatusCheck.lean` |
| T7 clause by clause: `matched` and `back` fail, `admits` and `forth` hold | `Examples.PW.StatusCheck.t7_matchedB_false`, `t7_backB_false`, `t7_admits_forth_hold` | `Lara/Examples/PWStatusCheck.lean` |
| Isolating negatives pinning `admitsB` and `matchedB` independently (eng review, decision 6A) | `Examples.PW.StatusCheck.s2_r1_admits_fails`, `s2_r1_matched_holds`, `s1_r2_matched_fails`, `s1_r2_admits_holds` | `Lara/Examples/PWStatusCheck.lean` |
| Isolating negatives pinning `forthB` and `backB` independently | `Examples.PW.StatusCheck.forthB_discriminates`, `backB_discriminates` | `Lara/Examples/PWStatusCheck.lean` |

The positive witnesses are off the identity: `symR` renames all three
predicates, `leafMapR` renames every leaf, and `bridgeR` discharges `leaf_ok`
at each of the three source leaves under that renaming. `s2_r2_statusBridge`
exercises `forth` and `back` on a real compiled edge (`1 → 0` on each side),
index by index, which is what makes `t8_defeated_preserved` a transport
through a matched attacker rather than a vacuous one.

## 3. Why status needs the target's attackers

A claim's status at a world is
`Grounded.statusC (Compile.checkedAF w.unit.program) (claimAt w c)`, with
`claimAt w c = Consistency.completeClaimFor w.unit c` (`PW.cmpStatus`,
`Lara/PW/Instance.lean`). That is a global grounded fixed point over the whole
compiled framework — every argument, every attack — read at the claim's
complete-support index set. It is not a property of any one support term.
T6's contract is term-local by design: `support_transport` carries one checked
derivation across, and "attacks do not transport" (T6 §8 limitation 3).

The boundary has two ends, both at the live T7 fixtures:

- `Examples.PW.t7_t6_boundary` (T6, unchanged): the identity endobridge's
  `Admits` holds between `wT7src` and `wT7tgt`, and `cmpStatus` flips from
  `justified` to `defeated`. Support transport alone cannot give status.
- `Examples.PW.Status.t7_forward_hom_insufficient` (T8): on the same edge,
  left-totality (`Admits`) *and* `forth` hold — the edge is a forward attack
  homomorphism — and the status still flips. A forward homomorphism alone
  cannot give status either.

The field the T7 edge fails is `matched`, at `leaf l2`: the target's
attacker is in the target program (`t7_l2_mem`) and is the transport of no
source argument (`t7_unmatched`), so `t7_not_statusBridge` refutes
`StatusBridge` directly at that field. The hand refutation needs no other
clause, but the executable checker records a second failure: `back` also
fails (`t7_backB_false`) — the target's `1 → 0` attack has no counterpart
across the identity correlation, the source program having no attacks at
all. `t7_not_statusBridge_of_flip` recovers
the same refutation from the flip alone, by running `status_transport` at the
identity bridge and contradicting the two evaluated cells: T8's contrapositive
reads a status flip as proof that some hypothesis fails, without naming
which.

## 4. Where injectivity enters and what breaks without it

`claimSupport_corr`'s backward half must show that every target support
argument for `τ(c)` is the transport of a source support argument for `c`.
`matched` supplies a source argument whose transport it is; what remains is
that its conclusion is `≡ c`. T6's `equiv_tr` runs the wrong way for this —
it takes `≡` forward. `equiv_tr_reflect` runs it backward, and it is exactly
here that `SymMap.Injective` is consumed: `nf` commutes with translation
(`trAtom_nf`), so equal target normal forms are translations of the two
source normal forms, and injectivity identifies them.

Without injectivity the derivation stops: a merging translation — two source
predicates sent to one target predicate — is exactly what `equiv_tr_reflect`
cannot invert, so the backward half of `claimSupport_corr` is unavailable. No
Lean cell witnesses a concrete flip under a merging translation; the claim
recorded here is only that the derivation needs injectivity.
`status_transport` is therefore stated with `hinj : B.sym.Injective`.
`status_transport_of_corr` is the escape hatch for bridges whose translation
merges: it takes the support correspondence as an explicit hypothesis and
proves the same equation from `StatusBridge.bisim`.

`PW.SymMap.Injective` is injectivity-*where-defined*, in the three-variable
form `∀ x y z, m.predMap x = some z → m.predMap y = some z → x = y` (and the
same on `conMap`) — deliberately not `Function.Injective` on the partial
`String → Option String` fields. Total injectivity would identify any two
symbols mapped to `none`, forbidding a translation from leaving more than one
symbol out of vocabulary; the reflection argument only ever compares two
`some` images. `SymMap.id_injective` and `SymMap.Injective.comp` (closure
under T9's Kleisli composition) are the two instances the examples and §6
use.

## 5. The modal reading

The design (§T8 of the document cited above) defines
`RobustlyJustified_b(w,c) := Comparable_b(w,c) ∧ w ⊨ [b]Justified(τ_b c)` and
`PossiblyJustified_b(w,c) := Translatable_b(c) ∧ w ⊨ ⟨b⟩Justified(τ_b c)`.
`sat_status_iff_box` and `sat_status_iff_dia` state: when every accepted
`b`-successor of `w` is T8-related to `w` (`hall`) and there is at least one
such successor (`hreach`), the local status atom at `w` is equivalent to its
boxed and to its diamonded translation at the successors — for every status
`s`, not only `justified`. In the design's vocabulary, the translatability
hypothesis `trAtom B.sym c = some c'` is `Translatable` and `hreach` is
`Reachable`; `Comparable` is discharged by the same hypotheses.
`sat_status_iff_box_src` is the same equivalence under the source valuation,
through T4 (`sat_src_iff_cmp`) on both sides.

The executable cell is `Examples.PW.Status.t8_box_defeated_r`, at the
two-context `bridgeDataR` whose single accepted edge is `wS2 → wR2`: `wS2 ⊨
Defeated(p) ↔ wS2 ⊨ [b] Defeated(p_r)`, the `RobustlyJustified` shape at
`defeated` with the guard discharged. `t8_box_defeated_r_holds` then shows
the left side is true, so the box is inhabited rather than vacuous.

## 6. Composition

Statuses are values. Preservation along a path of status bridges is
`Eq.trans` of the per-edge `status_transport` instances, together with the
per-edge canonicalizer equalities (`hcanon`) — no path-indexed status theorem
is needed and none is declared. What needs proving is that the *hypotheses*
compose, and `PW.StatusBridge.comp` proves it: the T9 composite bridge of two
status bridges is a status bridge, through a chosen intermediate world. T9's
intermediate-world dependence (`docs/theory-pw-t9-path-composition.md` §5) is
kept, not erased: the intermediate world is an explicit argument, and
`corr_comp_iff` — `Corr` along the composite factors through it — needs only
the first leg's `Admits`, so that the intermediate term is an intermediate
*argument*. `SymMap.Injective.comp` carries injectivity along.

This discharges T9 §7 limitation 4 ("status preservation is not a T9
theorem"), and T6 §8 limitation 3 with it.

Record the argument-order convention, since the two layers differ:
`StatusBridge.comp h₁ h₂` and `SymMap.Injective.comp h₁ h₂` take their legs
in *path* order — first leg first — while T9's `StructuralBridge.comp B₂ B₁`
and `SymMap.comp m₂ m₁` take them in *function-composition* order. The
composite `StatusBridge.comp h₁ h₂` is stated over `m₂.comp m₁` and
`lm₂ ∘ lm₁`, so the two conventions meet at the type.

## 7. Acceptance mapping

Issue #193's four bullets, each with the declaration that discharges it.

1. *Lean proves status preservation from explicit structural correspondence.*
   `PW.status_transport` (T8), with `PW.statusC_of_bisim` and
   `PW.statusC_of_iso` as the generic core over an explicit relation. Live
   at `Examples.PW.Status.t8_justified_preserved`, `t8_defeated_preserved`,
   `t8_gap_preserved`, and the modal cell `t8_box_defeated_r`.
2. *The hypotheses exclude unmatched target attackers and supports.*
   `StatusBridge.matched` (no target argument is unmatched) and
   `StatusBridge.back` (no target attacker is unmatched). The T7 target fails
   `matched` at `leaf l2` (`t7_unmatched`, `t7_not_statusBridge`), and
   `t7_forward_hom_insufficient` retains the forward-homomorphism
   counterexample: left-totality and `forth` are not enough.
3. *The result preserves all four aggregated statuses without treating them
   as argument labels.* `status_transport` is an equation between
   `cmpStatus` values — `Grounded.statusC` over `Claim.support` — proved
   through `statusC_congr`, which reads a claim only through emptiness of its
   support and, per label, existence of a support argument with that label.
   No status is ever a label of an argument. `srcStatus_transport` restates
   the equation at the source observation.
4. *The theorem does not strengthen T6 implicitly.* Every theorem takes
   `StatusBridge` (or an explicit `SupportCorr`) as an additional hypothesis;
   `Examples.PW.t7_t6_boundary` (unchanged) still shows `Admits` alone flips
   status; and the wrapper-discipline diff against T6's and T9's modules is
   empty (§8).

## 8. Verification

`lean/AxCheck.lean` is the declaration-level axiom audit: every public theorem
in `Lara/PW/AFBisim.lean` and `Lara/PW/Status.lean`, and every substantive
theorem witness in `Lara/Examples/PWStatus.lean`, has a corresponding
`#print axioms` entry. `scripts/check-axcheck-coverage.py` is the targeted
coverage guard that compares public theorem declarations in the named source
files with those entries. `scripts/check-axioms.sh` checks the emitted audit
and permits only the standard axiom trio: `propext`, `Classical.choice`, and
`Quot.sound`.

```
$ cd lean && lake build
Build completed successfully (143 jobs).

$ cd lean && python3 ../scripts/check-axcheck-coverage.py AxCheck.lean \
    Lara/PW/AFBisim.lean Lara/PW/Status.lean Lara/Examples/PWStatus.lean
AxCheck coverage passed (60 declarations).

$ cd lean && (set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
Axiom audit passed.
```

2058 audited declarations across the library, of which 60 are PW-T8 (12 in
`Lara/PW/AFBisim.lean`, 18 in `Lara/PW/Status.lean`, 30 in
`Lara/Examples/PWStatus.lean`); every PW-T8 row reports a subset of
`[propext, Classical.choice, Quot.sound]`, none reports `sorryAx` or
`ofReduceBool` — every theorem the three modules declare, together with the
definitions those theorems are stated over, audited transitively.
`Classical.choice` reaches the T8 rows through `Grounded.labelC_spec`, which
`labelC_of_bisim` rewrites with; no T8 proof step introduces it.

The wrapper discipline — no existing semantics module touched — is the empty
diff of

```
$ git diff origin/main --stat -- lean/Lara/Grounded.lean lean/Lara/Compile.lean \
    lean/Lara/Support.lean lean/Lara/Consistency.lean \
    lean/Lara/PW/Translation.lean lean/Lara/PW/Structural.lean \
    lean/Lara/PW/Compose.lean lean/Lara/PW/Outer.lean lean/Lara/PW/Instance.lean
(empty)
```

Those mechanisms, rather than an example's reducibility or a property test,
carry the audit contract. Every decidable cell in `Lara/Examples/PWStatus.lean`
closes by `decide`; `native_decide` is not used.

### Re-verification after merging #237 (2026-09-04, merge commit 84c51b6)

`origin/main` moved `Support.lean`, `Consistency.lean`, `Attack.lean`, and
`AxCheck.lean` after this branch's base, so the gates were re-run on the merged
tree: `Build completed successfully (143 jobs).`; `AxCheck coverage passed (60
declarations).`; `Axiom audit passed.` with 2073 reports (the 2058 above plus
#237's 15), the 60 PW-T8 rows unchanged and still within the standard trio; the
wrapper-discipline diff against `origin/main` remains empty. The ARA journey
identifiers this work allocated were renumbered past #237's (`N302`–`N306`,
`O132`–`O136`, session `2026-09-04_004`); no Lean or docs content changed.

## 9. Known limitations of the frozen contract

These are design commitments with named homes, not oversights.

1. **The attack clauses are index-level, not derived from declared attacks.**
   `StatusBridge.forth`/`back` are stated on the compiled edge decider
   `Compile.edgeB`, over argument indices. They are *not* derived from a
   correspondence between the two programs' declared `atts`: doing that
   needs `trSupport` to commute with `Attack.subterm`, `Compile.Contains`,
   `Compile.AttackOcc`, and `coveredB` — an `Erase.lean`-scale lemma set over
   a partial map. T8's statement per the design is the AF-level
   correspondence, so the clauses are stated where the design states them; a
   reader should not mistake them for structural conditions on the source
   language. Follow-up: #238.

   **Narrowed by #238.** `AttackBridge` (`Lara/PW/AttackTransport.lean`)
   states the attack hypotheses on declared `atts` via `trAttack`, and
   `AttackBridge.toStatusBridge` derives the index-level `forth`/`back`
   clauses from them; the commutation ladder mirrors `Erase.lean` over the
   partial map. This route additionally assumes `Function.Injective lm`,
   which the frozen `StatusBridge` contract does not — injectivity is
   load-bearing because `containsB` compares subterms by
   `decide (v = t)` (`Lara/Compile.lean:120-123`), so a collapsing leaf map
   makes two distinct source subterms translate equal. The general,
   injectivity-free index-level statement of limitation 1 therefore still
   stands; #238 supplies a bridge-contract-level sufficient condition for
   it, witnessed at `Examples.PW.Attack.*`.
2. **`status_transport` needs an injective translation.** A merging
   translation breaks the reflection half of `claimSupport_corr` (§4).
   Non-injective bridges use `status_transport_of_corr` and supply the
   support correspondence themselves.
3. **There is no executable `StatusBridge` checker.** The examples prove
   `StatusBridge` by hand, index by index; a `Bool` decider over the finite
   index ranges with a soundness theorem, in the `Presents`/`crossCompare`
   style of the comparison layer, would make each new cell one `decide`.
   Follow-up: #239. Discharged by #239: `statusBridgeB` with
   `statusBridgeB_sound`/`statusBridgeB_complete`
   (`Lara/PW/StatusCheck.lean`); each conformance cell is now one `decide`
   (`Lara/Examples/PWStatusCheck.lean`), and the T7 negative is refuted
   through completeness.
4. **T6 limitations 1, 2, and 5 are inherited.** Symbol translation remains
   bridge-global and functional, the leaf map remains total, and question
   keys remain frozen across the bridge. See
   `docs/theory-pw-t6-structural-transport.md` §8 for the original statements
   and their rationale.
5. **The `contested` cell is executable, not merely covered by the theorem.**
   The plan left this optional: `checkUnit` might have rejected symmetric
   contraries. It does not — `Policy.WellFormed` constrains only
   strict-reachable rule conclusions, and the `polS3`/`polR3` policies have
   no rules — so `t8_contested_preserved` and `t8_contested_cells` are
   evaluated cells, and all four statuses have one.

T8 discharges T6 limitation 3 — the absence of attack transport — and T9
limitation 4 — the absence of status preservation along paths — without
weakening or deleting either historical limitation record.

Full stable keys: `docs/paper-lean-name-map.md` §PW-T8.
