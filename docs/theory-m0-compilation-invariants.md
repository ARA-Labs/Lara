# Theory M0 — the compilation carrier and invariant record

_Status: frozen for the POPL 2028 theory spine. Recorded 2026-08-26 (issue #183,
tracker #180). The carrier, the erasure function, and the invariant record fixed
here are what M1 (#184), M2a (#185), M2b (#181), M3 (#186) and the possible-world
wrapper (#192) quantify over. Changing any of them after this point invalidates a
downstream theorem statement, not just a proof._

Canonical scope: [M0 in the theory-depth plan](https://github.com/EYH0602/lara-paper/blob/main/plan/theory-depth-plan.md#m0-extract-compilation-invariants).
That plan lives in the `lara-paper` repository, not here; issues #180–#184 cite
the same URL.

The `theory-` prefix is load-bearing: this M0 belongs to the open POPL 2028
theory spine (tracker #180), not to the closed engineering spine of
`plans/research-proposal.md` §7, whose M0 was the semantic corpus study
(`docs/corpus-map.md`) and whose milestone documents are the unprefixed
`docs/m1-freeze-checklist.md`, `docs/m3-closeout-notes.md`,
`docs/m4a-checklist.md`, and `docs/m5-freeze-checklist.md`. The two series
share numbers and nothing else.

---

## 1. Decision

**The M1 carrier is a conclusion-labelled finite argumentation framework.**

```lean
structure StructuredAF where
  nodes  : List Atom          -- node i's conclusion, in declaration order
  attack : Nat → Nat → Bool   -- the compiled closure-edge relation
```

`Lara.Invariants.StructuredAF` (`lean/Lara/Invariants.lean:67`). Node identity is
the declaration-order position, matching `Compile.toAF`, where
`Grounded.Arg = Nat` already indexes `CheckedProgram.args`.

**The erasure is `eraseAF`** (`lean/Lara/Invariants.lean:84`): drop the
conclusion labelling, keep positions and edges. It is not a new construction —
`Invariants.erase_compileUnit` proves that erasing a compiled accepted unit
returns exactly `Compile.checkedAF`, the AF the existing pipeline already
evaluates.

**The invariant record is `CompilerInvariant`** (`lean/Lara/Invariants.lean:121`),
with two fields: `ranged` and `conflictComplete`. Section 2 classifies every
other candidate invariant and says why it is not a field of the record.

### Why conclusions, and only conclusions

Three carriers were considered.

| Carrier | Consequence for M1 |
| --- | --- |
| Naked AF (`Grounded.AF`) | Uninformative. The constraint that makes the image interesting — that edges are *forced* by the fixed contrary policy — is invisible without node labels, so an erased-AF characterization says nothing about Lara specifically. |
| Conclusion-labelled AF | **Chosen.** Enough structure to state the forcing constraint, little enough that realizability is a real question in both directions. |
| Term-labelled AF | Vacuous. "Realizable" would degenerate to "already built out of checked support terms", making M1's sufficiency direction true by construction. |

The choice is also *adequate*, not merely convenient:
`Invariants.status_compileUnit` (`:257`) proves that the four-state status of
any claim, computed entirely inside the carrier, equals the status the existing
pipeline reports over `Compile.checkedAF`. Nothing an accepted unit says about a
claim survives outside `StructuredAF`, which is what licenses M1 to quantify
over carriers instead of over programs.

### Why there is no `attackable` node label

`Compile.AttackComplete` (`lean/Lara/Compile.lean:515`) is guarded by
`Compile.ConflictAttackable` (`:405`), a property of a support *term* — a leaf,
or an instance whose root rule is defeasible. Terms are gone from the carrier,
so the obvious reading needs a per-node Boolean label, and an early draft of
`StructuredAF` carried one.

It is redundant. `Consistency.wellFormed_contrary_target_attackable`
(`lean/Lara/Consistency.lean:42`) proves that in a well-formed accepted policy a
contrary target can never be a strict-rule root, so conflict attackability
follows from the contrary match itself. The label was dropped, and
`CompilerInvariant.conflictComplete` is correspondingly unguarded — a strictly
stronger invariant than the guarded version would have been.

---

## 2. The invariant table

Every invariant named in the M0 scope, its layer, its Lean home, and its
rejecting counterexample. "Layer" is the classification M0 owes its dependents:

- **carrier** — visible in `StructuredAF`, a field of `CompilerInvariant`;
- **source** — an invariant of the source judgment, quantifying over term
  structure that erasure discards; it constrains which carriers arise but cannot
  be restated as a carrier predicate;
- **adequacy** — not an invariant with a violating instance, but a theorem that
  the carrier retains an observation.

| # | Invariant | Layer | Lean declaration | Rejecting counterexample |
| --- | --- | --- | --- | --- |
| 1 | Endpoint-safe pruning | carrier | `Invariants.CompilerInvariant.ranged`; holds by `Invariants.compileUnit_ranged` (`:162`), from `Compile.edgeB_faithful` (`Compile.lean:649`) | `Examples.CompilerInvariants.unrangedEx` (`:30`), rejected by `unrangedEx_not_realizable` (`:41`) |
| 2 | Conflict completeness (forced edges) | carrier | `Invariants.CompilerInvariant.conflictComplete`; holds by `Invariants.compileUnit_conflictComplete` (`:175`), from `Unit.CheckedUnit.attack_complete` (`Lara/Unit.lean:193`) via `Compile.complete_conflict_edge` | `Examples.CompilerInvariants.unforcedConflictEx` (`:58`), rejected by `unforcedConflictEx_not_realizable` (`:71`); non-vacuous **off the diagonal** by `unforcedDistinctConflict_not_invariant` (`:118`) via `sharedContrary` (`:114`), which forces an edge between the *distinct* conclusions `pTa`/`qTa` under `Examples.dpShared`. Without it the field would be witnessed only where row 3 already bites |
| 3 | Self-attack condition | carrier (derived) | `Invariants.compileUnit_selfConflict` (`:217`) — the `i = j` diagonal of #2, not an independent field | `unforcedSelfConflict_not_invariant` (`:97`), non-vacuous by `selfContrary` (`:89`); source-level witness `Examples.GroundedConsistency.missing_self_edge_rejected` (`:128`) |
| 4 | Conclusion and claim ownership | adequacy | `Invariants.support_compileUnit` (`:246`) — carrier support agrees with `Consistency.claimSupportFor` (`Consistency.lean:63`); lifted to status by `Invariants.status_compileUnit` (`:257`) | none: a violation is not a framework but a disagreement between two projections, excluded by the theorem |
| 5 | Subargument closure | source | `Compile.Covered` (`Compile.lean:435`), decided by `Compile.coveredB_iff` (`:446`) over the per-attack closure test `Compile.attackClosureB_iff` (`:352`); `Compile.closure_includes_direct` (`:576`) shows closure extends, never replaces, the direct attack | `Examples.CompilerInvariants.closure_rejects_noncontaining_target` (`:133`) — in the running fixture node `0` is in range and is the attack's own source, yet receives no edge, because it does not contain the attacked occurrence. Closure adds edges onto containing arguments only |
| 6 | Positional attack coherence | source | `Compile.AttackOcc` (`Compile.lean:76`), `attackOcc_unique` (`:82`), `target_contains_occ` (`:97`) | the inversion theorems *are* the rejections: `Attack.undercut_target_rule` (`Lara/Attack.lean:622`) and `Attack.undermine_target_leaf` (`:631`) exclude the mismatched position kinds; `rebut_top_defeasible` (`:589`) and `undercut_pos_defeasible` (`:602`) exclude strict occurrences |
| 7 | Strict-chain well-formedness | source | `Support.cert_steps_accounted` (`Lara/Support.lean:1244`) over `Support.CertStepIn` (`:980`) | **open — B0 (#182).** The backend-leakage rejection is B0's deliverable; this row closes when #182 lands |
| 8 | Declared-identity preservation | source | `Compile.CheckedProgram.nodup` (`Compile.lean:478`); `Unit.CheckedUnit.nodes_terms` (`Lara/Unit.lean:198`) aligns the cache with the argument list | none at the carrier level, deliberately: two nodes *may* share a conclusion. Term-level identity is a source invariant and is not observable after labelling |

### Recorded obligations

M0 recorded two downstream obligations rather than dropping them, following
the scope rule to give every candidate invariant a Lean declaration or mark it
as a new obligation:

- **Row 7** still waits on B0 (#182) for its rejecting example. The invariant
  itself is proved; only its counterexample remains outstanding.
- **Signature well-sortedness of node conclusions.** M0 recorded that
  `Unit.CheckedUnit.args_well_sorted` (`Lara/Unit.lean:204`) covers argument terms,
  not node conclusions. M1 now closes the executable realization obligation
  with `Realizability.Realization.node_conclusion_wellSorted`, under successful
  checking and used-leaf ground coverage. The result does not add a field to
  the frozen invariant record.

---

## 3. What M1 established

`Invariants.compileUnit_invariant` (`:208`) supplies the carrier-level premise
for M1's necessity result. `Realizability.realizable_invariant` now proves the
fixed-context only-if direction: every executable realization compiles, up to
`StructuredAFIso`, to a framework satisfying the unchanged M0 record.

M1 tested the proposed converse and refuted it under an empty defeat policy.
`Examples.Realizability.oneSelfEdge_invariant` proves that a one-node self-edge
framework satisfies both frozen fields: its endpoints are in range, and
conflict completeness is vacuous because the policy declares no contraries.
`Examples.Realizability.oneSelfEdge_not_realizable` proves that the same
framework is not realizable under any fixed signature and registry paired with
that policy. `emptyUnitCheck_ok` supplies a successful executable unit in the
same empty-policy context, so the negative result does not depend on an
inconsistent checker context.

The counterexample identifies the information M0 deliberately erased.
`conflictComplete` constrains which edges must be present, but it does not show
that every present edge has a typed source attack. Optional edge support,
including support terms, attacked positions, and declared attack provenance,
does not survive in `StructuredAF`. Under the empty defeat policy no typed
attack exists, so compilation produces no edge even though the carrier-only
record accepts the self-edge.

The recorded conclusion-sortedness obligation is now closed at the executable
realization boundary by
`Realizability.Realization.node_conclusion_wellSorted`. The theorem requires a
`Realization`, including successful checking and used-leaf ground coverage; it
does not strengthen the frozen M0 record or state an unconditional property of
every standalone `CheckedUnit`.

There is therefore no `realize` operation under M1's original quantifiers and
no sufficiency theorem. The paper-facing result is necessity together with a
fixed-policy failure of sufficiency. The erased-AF result is omitted: after
labels and term structure disappear, the surviving range condition is generic
endpoint well-formedness rather than a Lara-specific image characterization.
The full declaration map and prohibited paper claims are recorded in
`docs/theory-m1-compilation-image.md`.

---

## 4. Boundary

- This record does not state M1, any erased-AF expressiveness claim, or any
  complexity result. The M0 scope forbids committing to those before the carrier
  freezes; the freeze is this document.
- `Lara.Erase` is unrelated despite the name: it is the backend-relabel
  development for result 9, not an erasure to a naked framework.
- `Consistency.contrary_args_not_both_grounded` (`Consistency.lean:106`) derives
  the same forced edge inline that `compileUnit_conflictComplete` now derives as
  a named invariant. The duplication is left in place: `Lara.Consistency` is a
  frozen headline result and `Lara.Invariants` imports it, so factoring the
  derivation out would invert the dependency.
