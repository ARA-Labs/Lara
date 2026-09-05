# PW-T8/PW-T9 follow-ups — witnesses, traversal seam, StatusBridge decider, declared-attack transport

## Result

The four follow-ups the PW-T8/PW-T9 freezes left behind (tracker #189) are
implemented as four pull requests, planned in
`plans/2026-09-04-pw-t8-t9-followups.md` (eng-review cleared, ten decisions)
and executed task-by-task. No frozen module is modified except
`Lara/PW/Compose.lean` (public statements byte-identical; proofs refactored)
and the example modules; no corpus regeneration, no freeze-tag bump.

**#235 — executable witnesses for the remaining T9 laws (PR #243).**
`Lara/Examples/PWCompose.lean` gains four focused witnesses:
`first_leg_gap_computes`/`first_leg_gap_law` pin `trAtom_comp_none_left` on a
concrete first-leg vocabulary gap, both computed and derived via the law;
`id_comp_ren2`/`comp_id_ren2` pin `SymMap.id_comp`/`comp_id` at the
non-identity partial map `ren2Sym` with the composite's action pinned on
predicate/constructor hits and misses. They are the regression pins the #234
refactor relies on.

**#234 — reusable traversal seam under the T9 composition proofs (PR #245,
stacked on #243).** The seven-times-repeated cons-step argument is factored
into `zipOpt` (all-or-nothing `Option` combination), `zipOpt_bind` (the
single generic cons-step algebra, mutual families included), and nine
per-traversal cons equation lemmas (`trAtoms_cons`, `trTerms_cons`,
`trTerm_con`, `trPats_cons`, `trAPats_cons`, `trSubst_cons`,
`trQuestions_cons`, `trSupportList_cons`, `trSupportDis_cons`). All eight
list-shaped `tr*_comp` proofs (plus `trTerm_comp`'s `.con` case) are rewritten
through the seam with every public statement byte-identical. `zipOpt` is a
`def`, invisible to the coverage gate, so `zipOpt_computes` pins all four
cases by computation (eng review 7A).

**#239 — executable `StatusBridge` decider with soundness and completeness
(PR #244).** New wrapper modules `Lara/PW/StatusCheck.lean` and
`Lara/Examples/PWStatusCheck.lean`; the frozen `Lara/PW/Status.lean` is
untouched. `statusBridgeB` scans the two finite index ranges (completeness of
the scan follows from `corr_lt` and `edgeB_faithful.ranged`);
`statusBridgeB_sound`/`statusBridgeB_complete` tie it to the Prop both ways,
so each conformance cell is one `decide` and the T7 negative is refuted
through completeness. Four cross-paired isolating cells pin `admitsB` and
`matchedB` independently (eng review 6A — an accidentally always-true
conjunct would otherwise pass every cell). The O(n²m²) kernel-reduction
bound is documented in the module header (8A); `native_decide` is not used.

**#238 — compiled attack correspondence derived from declared-attack
transport (PR #246, stacked on #245).** New modules
`Lara/PW/AttackTransport.lean` and `Lara/Examples/PWAttack.lean`.
`trAttack`/`trAttackList` translate declared attacks (both stored terms
translated, kind and position verbatim); `AttackBridge` restates T8's attack
hypotheses on the source language (`atts_eq`: the target's declared attacks
are exactly the transports of the source's);
`AttackBridge.toStatusBridge` derives the index-level `forth`/`back` clauses.
The commutation ladder mirrors `Lara/Erase.lean` over the partial map — 23
theorems: substitution/support injectivity (`trSubst_inj`, the
`trSupport_inj` mutual triple, `trSupport_eq_iff`), positional navigation
(`lookupDis_trSupportDis`, `trSupport_subterm`, plus partial-map inversion
helpers with no total-map analogue: `trSupport_inst_inv`,
`trSupport_subterm_some`, `lookupDis_mem`, the two `_some_of_mem` lemmas),
containment/coverage invariance (the `containsB_trSupport` mutual triple,
`trAttack_source`, `attackClosureB_trAttack`, `coveredB_trAttack`), and the
`Contains_trSupport`/`AttackOcc_trSupport` Prop corollaries the issue names
(`DisNodup` discharged at use sites via `hasSupport_disNodup`, as
`edgeB_iff` does). `trAttackList`'s cons step goes through the #234 seam
(`trAttackList_cons`) — the seam's first reuse outside the eight traversals
(eng review 3A).

**Limitation 1 is narrowed, not discharged** (eng review 1A):
`toStatusBridge` additionally assumes `Function.Injective lm`, which the
frozen `StatusBridge` contract does not — `containsB` compares subterms by
`decide (v = t)`, so a collapsing leaf map makes two distinct source
subterms translate equal. The example module witnesses both boundaries:
`gap_attack_undefined` (an attack-vocabulary gap refutes `atts_eq`) and
`collapsed_containsB_breaks` (the injectivity boundary), plus
`ques_position_computes`/`ques_position_law` pinning `Attack.subterm`
commutation at a discharge key — the ladder step that depends on T6's
question-key preservation (7A). The S2/R2 pair is re-established as an
`AttackBridge` and its `StatusBridge` rederived
(`s2_r2_attackBridge`, `s2_r2_statusBridge_via_attacks`).

## Gates (per PR; CI known broken, #225 — local gates are the record)

- PR #243: `lake build` 144 jobs; coverage 2262 declarations; axiom audit
  passed (`[propext, Quot.sound]` on the new rows).
- PR #244: `lake build` 146 jobs; coverage 2273 declarations; axiom audit
  passed; the five StatusCheck theorems `[propext, Quot.sound]`, the ten
  cells `[propext, Classical.choice, Quot.sound]`; no `ofReduceBool`.
- PR #245: `lake build` 144 jobs; coverage 2273 declarations (+11);
  axiom audit passed.
- PR #246: `lake build` 146 jobs; coverage 2304 declarations (+31);
  axiom audit passed, standard trio only, no `sorryAx`.

## Execution notes

Two lanes per the plan's worktree-parallelization table: lane A
(#235 → #234 → #238, stacked branches `pw-t9-witnesses`,
`pw-t9-traversal-seam`, `pw-t8-attack-transport`) and lane B (#239, branch
`pw-t8-status-decider` off main in a separate worktree, executed by a
subagent verbatim from the plan). Task 4 was built ladder-first: all
signatures elaborated with `sorry` before any proof (eng review 5A), then
filled bottom-up. The one real tactic-level surprise: Lean's `cases h : e`
substitutes only in the goal, not in hypotheses, so destructuring
`zipOpt`-valued equalities requires rewriting the case equations into the
hypothesis before `simp only [zipOpt]` can fire.
