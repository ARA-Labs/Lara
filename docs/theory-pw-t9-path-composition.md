# Theory PW-T9: exact structural-path composition

_Status: mechanized on 2026-09-03 (issue #190, tracker #189). This document
records the exact path-composition contract frozen by T9, the consequences it
proves, and the boundary it leaves to later work._

The intended readers are the paper author, whoever takes decisions on tracker
#189, and anyone extending or citing structural bridges. They should cite the
declarations below rather than reconstructing the contract from implementation
details; `docs/paper-lean-name-map.md` §PW-T9 carries the stable keys.

T9 adds composition over the exact structural layer frozen by T6. Its core is
`Lara/PW/Compose.lean`; executable conformance witnesses are in
`Lara/Examples/PWCompose.lean`. It does not change the checker, compilation,
grounded labelling, local status, or the PW0 outer model.

## 1. What T9 froze

**Composition is first-leg-first Kleisli composition.** For partial symbol maps,
`SymMap.comp m₂ m₁` denotes τ₂ ∘ τ₁: apply `m₁`, then apply `m₂` to the
result. The lifted `trX_comp` laws are theorem-level bind equations, not
reduction rules or definitions of the lifts. `StructuralBridge.comp B₂ B₁`
uses the same order, composes the total leaf maps as `B₂.leafMap ∘ B₁.leafMap`,
and chains each bridge-contract clause through the chosen middle checking
environment.

The following diagram fixes both the typed endpoints and the flow direction.
`Eᵢ` abbreviates one checking environment over the shared canonicalizer.

```text
E₀  -- B₁ : (m₁, lm₁) -->  E₁  -- B₂ : (m₂, lm₂) -->  E₂
 |                              |                              |
 t -- trSupport m₁ lm₁ --> some t' -- trSupport m₂ lm₂ --> some t''

composite E₀ -> E₂:  B₂.comp B₁
symbol map:            m₂.comp m₁       (τ₂ ∘ τ₁)
leaf map:              lm₂ ∘ lm₁
```

**Paths are first-class indexed data.** `BridgePath` is indexed by its source
and target policy, evidence, and certificate environments and lives in
`Type 1`, because `.cons` quantifies over an intermediate environment. A path
therefore retains its chosen intermediates rather than existentially erasing
them. `BridgePath.compose` folds the path into a named structural bridge from
`StructuralBridge.refl` at `.nil`.

This fold equation explains why the first edge remains the first translation
even though the recursive composite appears on the left of `.comp`.

```text
compose(nil) = refl

compose(cons b rest)
  = compose(rest).comp b
  = first run b, then run every edge in rest
```

`BridgePath.trans` is the corresponding stepwise Kleisli chain of partial
support maps. `BridgePath.trans_eq_compose` proves that this stepwise chain is
the support map induced by the folded bridge.

## 2. Theorem table

Every public theorem currently declared by `Lara/PW/Compose.lean` appears in
the first table. Definition rows are included to identify the objects those
theorems constrain.

| Result | Declaration |
|---|---|
| First-leg-first partial symbol composition and its two unit laws | `PW.SymMap.comp`; `PW.SymMap.id_comp`, `PW.SymMap.comp_id` |
| Term and term-list bind laws | `PW.trTerm_comp`, `PW.trTerms_comp` |
| Atom and atom-list bind laws | `PW.trAtom_comp`, `PW.trAtoms_comp` |
| First-edge and intermediate-edge atom gaps remain composite gaps | `PW.trAtom_comp_none_left`, `PW.trAtom_comp_none_mid` |
| Pattern and pattern-list bind laws | `PW.trPat_comp`, `PW.trPats_comp` |
| Atomic-pattern and atomic-pattern-list bind laws | `PW.trAPat_comp`, `PW.trAPats_comp` |
| Substitution bind law | `PW.trSubst_comp` |
| Support, support-list, and discharge-list bind laws | `PW.trSupport_comp`, `PW.trSupportList_comp`, `PW.trSupportDis_comp` |
| Question and question-list bind laws | `PW.trQuestion_comp`, `PW.trQuestions_comp` |
| Rule bind law | `PW.trRule_comp` |
| Binary structural-bridge composition | `PW.StructuralBridge.comp` |
| Explicit two-stage applicability predicate and exact factorization | `PW.AdmitsSteps`; `PW.admits_comp`, `PW.admits_steps_of_intermediate` |
| Binary transport with intermediate and final judgments exposed | `PW.support_transport_comp` |
| Indexed paths, their fold, and their stepwise partial support map | `PW.BridgePath`, `PW.BridgePath.compose`, `PW.BridgePath.trans` |
| Equality of stepwise and folded transport | `PW.BridgePath.trans_eq_compose` |
| Direct/path commuting contract and exact map-equality characterization | `PW.Commutes` (fields `atom_eq`, `support_eq`); `PW.Commutes.of_maps_eq` |
| Map equalities extracted from a commuting direct/path pair | `PW.Commutes.leafMap_eq`, `PW.Commutes.predMap_eq`, `PW.Commutes.conMap_eq`, `PW.Commutes.sym_eq` |
| Direct and path transport agree on a checked source support | `PW.direct_transport_agrees` |
| Rule and admitted-leaf translations pinned by common target typing | `PW.commutes_on_rules`, `PW.commutes_on_leaves` |
| Direct/path checker-tied applicability equivalence | `PW.admits_iff_of_commutes` |
| Full accepted edge as caller relation conjoined with checker applicability | `PW.Accepted`; `PW.accepted_iff_of_commutes` |
| T9 path theorem for an arbitrary chosen exact path | `PW.path_support_transport` |

The following facts in `Lara/Examples/PWCompose.lean` are the substantive
conformance witnesses intended for the final `AxCheck.lean` gate.

| Witness | Declaration |
|---|---|
| Live second rename and concrete two-edge path | `Examples.PW.Compose.ren2Sym`, `bridgeRen2`, `pathRen`, `bridgeRenDirect`, `wRenTgt2`; `ren2_conclusion`, `ren_path_trans`, `ren_path_transport` |
| Positive direct/two-edge commuting triangle and checked transport agreement | `Examples.PW.Compose.ren_path_commutes`, `ren_direct_transport_agrees` |
| A real three-edge path with a positive triangle and transport agreement | `Examples.PW.Compose.pathRen3`; `ren_path3_commutes`, `ren_path3_transport_agrees` |
| Binary theorem path with the intermediate and final checked judgments visible | `Examples.PW.Compose.ren_support_transport_comp` |
| Common-target consequences and map equalities on the live rename | `Examples.PW.Compose.ren_commutes_on_rule`, `ren_commutes_on_leaf`, `ren_commutes_on_symbol_maps` |
| Inhabited identity applicability and a chosen intermediate world | `Examples.PW.Compose.bridgeIdT7`, `pathIdT7`; `admitsSelfT7`, `t7_admits_steps_of_intermediate` |
| Both directions of composite applicability and an inhabited result | `Examples.PW.Compose.t7_admits_comp_iff`, `t7_admits_composite` |
| Positive identity direct/path triangle and applicability equivalence | `Examples.PW.Compose.t7_identity_path_commutes`, `t7_admits_iff_of_commutes` |
| Candidate-relation premise, accepted-edge equivalence, inhabitation, and negative separation | `Examples.PW.Compose.candidateDirectT7`, `candidatePathT7`, `candidatePathFalseT7`; `t7_candidate_relations_agree`, `t7_accepted_iff_of_commutes`, `t7_accepted_inhabited`, `t7_accepted_needs_candidate_coherence` |
| Negative triangle caused by a different leaf renaming | `Examples.PW.Compose.bridgeSwap`, `twinIdentityPath`; `direct_ne_composed_support` |
| Negative triangle caused only by different predicate translation | `Examples.PW.Compose.claimOnlySym`, `claimOnlyBridge`, `claimIdentityPath`; `direct_ne_composed_claim` |
| Non-vacuous certificate acceptance through two live bridge legs | `Examples.PW.Compose.certCertTgt2`, `bridgeCert2`, `certCompBridge`; `certComp_two_live_legs` |
| Real atom, support-transport, and context-tied applicability vocabulary gaps | `Examples.PW.Compose.gapSym`, `gapBridgeRen`, `gapBridgeRen2`, `gapBridgeDrop`, `gapPath`, `gapSupportPath`; `mid_path_out_of_vocabulary`, `mid_path_translationUndefined`, `mid_path_support_undefined`; `gapConFirstBridge`, `gapConDropBridge`, `gapAppContext`, `gapAppWorld`, `gap_admits_comp_fails` |
| Nonempty lifted-map computations and their concrete inputs and outputs | `Examples.PW.Compose.substRenSrc`, `substRenTgt`, `substRenTgt2`, `patRenSrc`, `patRenTgt`, `patRenTgt2`, `questionRenSrc`, `questionRenTgt`, `questionRenTgt2`, `supportDisRenSrc`, `supportDisRenTgt`, `supportDisRenTgt2`; `trSubst_nonempty_computes`, `trPat_nonempty_computes`, `trQuestions_nonempty_computes`, `trSupportDis_nonempty_computes` |
| First-leg atom gap witnessed both computed and via the law | `Examples.PW.Compose.first_leg_gap_computes`, `first_leg_gap_law` |
| Unit laws pinned at a non-identity partial map | `Examples.PW.Compose.id_comp_ren2`, `comp_id_ren2` |

The three-edge witness is genuinely a `BridgePath` with three `.cons`
constructors: the two live rename edges are followed by a reflexive edge in the
final environment. Its positive triangle and transport theorem establish that
the path-level statements are not merely a binary encoding.

## 3. Pinned consequences, not commuting premises

`Commutes B P` has exactly two fields. The diagram shows one named direct bridge
against an arbitrary chosen path with the same endpoints and labels those two
induced-map equalities.

```text
                         B
                    +----------+
                    |          v
source environment  |     target environment
                    |          ^
                    +-- b₁ ... bₙ --+
                         path P

Commutes.atom_eq:    trAtom B.sym a
                   = trAtom P.compose.sym a

Commutes.support_eq: trSupport B.sym B.leafMap w
                   = P.trans w
```

`commutes_on_rules` is a consequence of the two bridges' `rule_ok` clauses:
when a source rule is present at a shared rule id, both routes must put its
translation at that same id in the common target policy, so the translations
cannot disagree there. `commutes_on_leaves` is a consequence once the direct
and composite leaf maps agree at an admitted source leaf: their `leaf_ok`
clauses and the common target evidence environment then pin the translated
atom. Neither theorem is an input to `Commutes`, and neither discharges one of
its fields.

The negative witnesses identify the two fields' independent content. In
`direct_ne_composed_support`, a valid bridge swaps equally typed leaves while
the competing path leaves them fixed. In `direct_ne_composed_claim`, the
direct bridge and path have equal leaf and constructor maps and agree on a
constructor-bearing support translation, but their predicate translations
differ. The latter fixture uses empty policy and evidence environments so no
typing clause can introduce a second disagreement.

`Commutes.leafMap_eq` extracts pointwise equality of the direct and folded leaf
maps from `support_eq`; `Commutes.predMap_eq` extracts predicate-map equality
from `atom_eq`. Support terms also expose constructor translation directly:
an `.inst` substitution containing `.con k ...` lets `Commutes.conMap_eq`
extract constructor-map equality from `support_eq`. `Commutes.sym_eq` combines
the predicate and constructor results. Consequently `Commutes.of_maps_eq` is
an iff: this `Commutes` contract is exactly full symbol-map and leaf-map
equality, not a weaker observational triangle.

## 4. Applicability and acceptance

`Admits m lm w u` remains T6's checker-tied `accept` discipline: every program
argument in `w` has a defined translated support term that belongs to `u`'s
program. It is not, by itself, PW0's full accepted-edge relation.

For a binary bridge composite, `AdmitsSteps B₂ B₁ w u` exposes a chosen
intermediate support term for every source program term and requires the two
translations and final membership. `admits_comp` is the exact iff between
`Admits (B₂.comp B₁)` and that two-stage translation/membership condition.
`admits_steps_of_intermediate` supplies the step predicate from two admitted
legs through an explicitly chosen middle world; the converse of `admits_comp`
does not reconstruct such a world.

`gap_admits_comp_fails` exercises the failure direction on a checked world.
Both bridge types use that world's actual policy lookup, evidence environment,
and certificate relation at their endpoints. The first bridge renames a
constructor inside an instance substitution, the second bridge omits that
image, and both `AdmitsSteps` and composite `Admits` are false.

`admits_iff_of_commutes` says a commuting direct bridge and path have the same
checker-tied applicability because their support maps agree. The full relation
is instead
`Accepted R m lm w u = R w u ∧ Admits m lm w u`: a caller-owned candidate
relation conjoined with checker-tied applicability. Accordingly,
`accepted_iff_of_commutes` requires both `Commutes` and a separately supplied
pointwise equivalence between the direct and path candidate relations. The T7
examples prove the candidate premise, applicability, and inhabitation
separately before combining them; `t7_accepted_needs_candidate_coherence`
keeps the bridges commuting and applicability true while a false path
candidate relation makes the path edge unaccepted.

## 5. Intermediate-world dependence

All path theorems are per chosen `BridgePath`; equal endpoints do not identify
different paths. `support_transport_comp` returns both the intermediate and
final checked `HasSupport` judgments, so the middle environment remains in the
evidence. `admits_steps_of_intermediate` takes the intermediate world as an
explicit argument. At path level, `BridgePath.trans_eq_compose` states that the
final partial support map is the map obtained through that chosen path's fold.
It does not assert that every path between the same endpoints induces the same
map.

The mid-path failure case makes that dependence observable. Here the first
edge succeeds on `a`, but the second edge has no translation for the running
image `a'`; partiality propagates through the fold and comparison reports an
incomparability reason, never a local status.

```text
a -- trAtom m₁ --> some a' -- trAtom m₂ --> none
\________________ trAtom (m₂.comp m₁) ________________/ = none

none -- crossCompare --> incomparable(translationUndefined)
                         (not justified/defeated/both/neither)
```

`Examples.PW.Compose.mid_path_out_of_vocabulary` realizes this with `e`
translating to `e_r` on the first edge and `e_r` missing on the second.
`mid_path_translationUndefined` then derives
`.incomparable .translationUndefined` through the comparison API.

## 6. Boundary

Every result here concerns exact `StructuralBridge` paths. Nothing generalizes
these theorems to approximation bridges. Approximate composition needs its own
domains, observables or comparison spaces, and error and convergence laws;
none is smuggled into `Commutes`, `Admits`, or path transport.

## 7. Known limitations of the frozen contract

1. **There are no bridge-level associativity or unit equalities.** `SymMap`
   has `id_comp` and `comp_id`, but T9 does not identify differently nested
   `StructuralBridge.comp` values. Semantic path flattening is expressed by
   `BridgePath.trans_eq_compose`, per chosen path.
2. **Paths retain T6 limitations 1, 2, and 5.** Symbol translation remains
   bridge-global and functional, the leaf map remains total, and question keys
   remain fixed. See `docs/theory-pw-t6-structural-transport.md` §8 for the
   original statements and their rationale.
3. **Endpoint equality is not path independence.** Different chosen paths may
   induce different translations; `Commutes` is the explicit agreement needed
   to compare a named direct bridge with one path.
4. **Status preservation is not a T9 theorem.** Checked-support preservation
   along paths is T6 composed by T9. Status preservation along such paths is T8
   composed with T9 and requires T8's attack-correspondence hypotheses.
   Discharged by T8 (#193): `PW.StatusBridge.comp` composes the hypotheses
   along the T9 composite, and status along a path is `Eq.trans` of
   per-edge `status_transport`; see
   docs/theory-pw-t8-status-preservation.md.
5. **Approximation remains out of scope.** The exact boundary in §6 is a
   separate theory problem, not an omitted case of structural composition.

T9 discharges T6 limitation 4—the absence of path composition and a commuting
triangle—without weakening or deleting that historical limitation record.

## 8. Verification contract

`lean/AxCheck.lean` is the declaration-level axiom audit: every public theorem
in `Lara/PW/Compose.lean` and every substantive theorem witness in
`Lara/Examples/PWCompose.lean` must have a corresponding `#print axioms` entry.
`scripts/check-axcheck-coverage.py` is the targeted coverage guard that compares
public theorem declarations in named source files with those entries.
`scripts/check-axioms.sh` checks the emitted audit and permits only the standard
axiom trio: `propext`, `Classical.choice`, and `Quot.sound`.

Those mechanisms, rather than an example's reducibility or a property test,
carry the audit contract. Final job and declaration counts belong to the
controller's final gates; this freeze record does not predict or invent them.

Full stable keys: `docs/paper-lean-name-map.md` §PW-T9.
