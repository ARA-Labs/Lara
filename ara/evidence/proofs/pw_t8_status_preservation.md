# PW-T8 — conditional status preservation

## Result

Issue #193 (tracker #189) is implemented in PR #240 (branch
`claude/eyh0602-lara-193-plan-9b752b`, commits `424e4e7`..`5637540`, 14
commits including the plan and its retirement). Three new modules only import;
no local, PW0, T6, or T9 definition is touched.

`Lara/PW/AFBisim.lean` is the generic layer: two finite frameworks and a
relation `Z` on argument ids. `AttackBisim F G Z` is a total attack
bisimulation (`dom`, `left_total`, `right_total`, `forth`, `back`). One mutual
induction on `DirectIn`/`DirectOut` carries the declarative grounded judgment
across `Z` in both directions; `labelC_spec` transfers the executable label
(`labelC_of_bisim`), and `statusC_congr` — which reads a claim only through
support emptiness and per-label existence — gives `statusC_of_bisim` for any
two claims whose complete-support index sets correspond (`SupportCorr`). The
design's AF isomorphism `AFIso` is a corollary (`AFIso.toBisim`); its `inj`
field is consumed by no proof, so a surjective bounded morphism already
suffices.

`Lara/PW/Status.lean` instantiates this at structural bridges. `Corr m lm w v
i j` relates the `i`-th source compiled argument to the `j`-th target one when
`trSupport` sends the first to the second. `StatusBridge` is the T8 hypothesis
set: T6's `Admits` (left-total), `matched` (right-total — every target
argument is a transport; the clause the T7 target violates at `leaf l2`), and
attack `forth`/`back` stated on the compiled edge decider `Compile.edgeB`.
`StatusBridge.bisim` shows these form an `AttackBisim` of the two `checkedAF`s.
`claimSupport_corr` derives the complete-support correspondence for every
translatable query from T6 transport, `hasSupport_unique`, `equiv_tr`, and the
new `equiv_tr_reflect`, which needs `SymMap.Injective` (injectivity where
defined, not `Function.Injective` on the partial fields). T8 is
`status_transport : cmpStatus v c' = cmpStatus w c` under `hcanon`, a
structural bridge, `StatusBridge`, injectivity, and `trAtom B.sym c = some c'`;
`status_transport_of_corr` takes an explicit `SupportCorr` instead of
injectivity. `sat_status_iff_box`/`_dia`/`_box_src` collapse the design's
guarded `RobustlyJustified`/`PossiblyJustified` to the local status atom when
every accepted successor is T8-related. `StatusBridge.comp` composes the
hypotheses along T9's composite through a chosen intermediate world, with
`corr_comp_iff` needing only the first leg's `Admits`; status along a path is
`Eq.trans` of per-edge instances.

`Lara/Examples/PWStatus.lean` carries both halves. The T7 identity edge
satisfies `admits` and `forth` (a forward attack homomorphism) and fails
`matched` at `leaf l2` (`t7_unmatched`, `t7_not_statusBridge`,
`t7_forward_hom_insufficient`); `t7_not_statusBridge_of_flip` recovers the
same fact from the status flip through T8's contrapositive. A renaming
translation `symR`/`leafMapR` between disjoint-vocabulary contexts over the
empty backend registry transports `justified`, `defeated`, `gap`, and
`contested` off the identity (`t8_justified_preserved`,
`t8_defeated_preserved`, `t8_gap_preserved`, `t8_contested_preserved`, each
with an evaluated `_cells` twin); the contested pair uses symmetric contraries,
which `checkUnit` accepts because `Policy.WellFormed` constrains only
strict-reachable rule conclusions. `t8_box_defeated_r` instantiates the `[b]`
collapse at a two-context `BridgeData`, and `t8_box_defeated_r_holds` shows
the box is inhabited.

## Verification (2026-09-04, head 5637540)

```
$ cd lean && lake build
Build completed successfully (143 jobs).

$ cd lean && python3 ../scripts/check-axcheck-coverage.py AxCheck.lean \
    Lara/PW/AFBisim.lean Lara/PW/Status.lean Lara/Examples/PWStatus.lean
AxCheck coverage passed (60 declarations).

$ cd lean && (set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
Axiom audit passed.
```

The audit reports 2058 declarations across the library, of which 60 are PW-T8
(12 in `Lara/PW/AFBisim.lean`, 18 in `Lara/PW/Status.lean`, 30 in
`Lara/Examples/PWStatus.lean`); every PW-T8 row is within `propext`,
`Classical.choice`, `Quot.sound`, with no `sorryAx` and no `ofReduceBool`.
`Classical.choice` reaches the T8 rows through `Grounded.labelC_spec`; the
bisimulation lemmas, `AFIso.toBisim`, and `supportCorr_of_image` use no
axioms. The wrapper-discipline diff against `origin/main` over
`Grounded.lean`, `Compile.lean`, `Support.lean`, `Consistency.lean`,
`PW/Translation.lean`, `PW/Structural.lean`, `PW/Compose.lean`,
`PW/Outer.lean`, and `PW/Instance.lean` is empty. Removing either `hSB` or
`hinj` from `status_transport`'s signature leaves an unfillable goal
(scratch negative check, two errors as expected).

## Re-verification after merging #237 (2026-09-04, merge commit 84c51b6)

`origin/main` moved `Support.lean`, `Consistency.lean`, `Attack.lean`, and
`AxCheck.lean` after this branch's base, so the gates were re-run on the merged
tree: `Build completed successfully (143 jobs).`; `AxCheck coverage passed (60
declarations).`; `Axiom audit passed.` with 2073 reports (the 2058 above plus
#237's 15), the 60 PW-T8 rows unchanged and still within the standard trio; the
wrapper-discipline diff against `origin/main` remains empty. The ARA journey
identifiers this work allocated were renumbered past #237's (`N302`–`N306`,
`O132`–`O136`, session `2026-09-04_004`); no Lean or docs content changed.

## Process record

The plan (`8a77787`, since retired) carried no cleared engineering review and
was implemented at the user's decision. Every plan Lean block was compiled in
scratch before its implementer was dispatched; that pre-flight found 12
defect sites in the plan's proof scripts across 5 of the 7 Lean tasks, only 2
of which the plan had flagged as risks, while every pitfall the plan did flag
compiled as written. One defect was a `decide` over a proposition quantifying
over `SupportTerm`, undecidable in principle. All fixes were proof-script or
binder-spelling only; each step's spec review confirmed the elaborated
signatures against the plan.

## Boundary

`forth`/`back` are index-level conditions on `edgeB`, not derived from a
correspondence of declared attacks (issue #238). There is no executable
`StatusBridge` decider (issue #239). `status_transport` needs an injective
translation; non-injective bridges use `status_transport_of_corr`. T6
limitations 1, 2, and 5 are inherited. Approximation bridges remain tracker
#189.

Full record: `docs/theory-pw-t8-status-preservation.md`.
