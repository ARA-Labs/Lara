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
| 2 | Conflict completeness (forced edges) | carrier | `Invariants.CompilerInvariant.conflictComplete`; holds by `Invariants.compileUnit_conflictComplete` (`:175`), from `Unit.CheckedUnit.attack_complete` (`Unit.lean:193`) via `Compile.complete_conflict_edge` | `Examples.CompilerInvariants.unforcedConflictEx` (`:58`), rejected by `unforcedConflictEx_not_realizable` (`:71`); non-vacuous **off the diagonal** by `unforcedDistinctConflict_not_invariant` (`:118`) via `sharedContrary` (`:114`), which forces an edge between the *distinct* conclusions `pTa`/`qTa` under `Examples.dpShared`. Without it the field would be witnessed only where row 3 already bites |
| 3 | Self-attack condition | carrier (derived) | `Invariants.compileUnit_selfConflict` (`:217`) — the `i = j` diagonal of #2, not an independent field | `unforcedSelfConflict_not_invariant` (`:97`), non-vacuous by `selfContrary` (`:89`); source-level witness `Examples.GroundedConsistency.missing_self_edge_rejected` (`:128`) |
| 4 | Conclusion and claim ownership | adequacy | `Invariants.support_compileUnit` (`:246`) — carrier support agrees with `Consistency.claimSupportFor` (`Consistency.lean:75`); lifted to status by `Invariants.status_compileUnit` (`:257`) | none: a violation is not a framework but a disagreement between two projections, excluded by the theorem |
| 5 | Subargument closure | source | `Compile.Covered` (`Compile.lean:435`), decided by `Compile.coveredB_iff` (`:446`) over the per-attack closure test `Compile.attackClosureB_iff` (`:352`); `Compile.closure_includes_direct` (`:576`) shows closure extends, never replaces, the direct attack | `Examples.CompilerInvariants.closure_rejects_noncontaining_target` (`:133`) — in the running fixture node `0` is in range and is the attack's own source, yet receives no edge, because it does not contain the attacked occurrence. Closure adds edges onto containing arguments only |
| 6 | Positional attack coherence | source | `Compile.AttackOcc` (`Compile.lean:76`), `attackOcc_unique` (`:82`), `target_contains_occ` (`:97`) | the inversion theorems *are* the rejections: `Attack.undercut_target_rule` (`Attack.lean:620`) and `Attack.undermine_target_leaf` (`:630`) exclude the mismatched position kinds; `rebut_top_defeasible` (`:588`) and `undercut_pos_defeasible` (`:601`) exclude strict occurrences |
| 7 | Strict-chain well-formedness | source | `Support.cert_steps_accounted` (`Support.lean:1179`) over `Support.CertStepIn` (`:980`) | **open — B0 (#182).** The backend-leakage rejection is B0's deliverable; this row closes when #182 lands |
| 8 | Declared-identity preservation | source | `Compile.CheckedProgram.nodup` (`Compile.lean:478`); `Unit.CheckedUnit.nodes_terms` (`Unit.lean:198`) aligns the cache with the argument list | none at the carrier level, deliberately: two nodes *may* share a conclusion. Term-level identity is a source invariant and is not observable after labelling |

### Recorded obligations

Two rows are not fully discharged and are recorded rather than quietly dropped,
per the M0 scope's "give every candidate invariant a Lean declaration **or** mark
it as a new obligation":

- **Row 7** waits on B0 (#182) for its rejecting example. M1 may proceed: the
  invariant itself is proved, only its counterexample is outstanding.
- **Signature well-sortedness of node conclusions.** `Unit.CheckedUnit`
  carries `args_well_sorted` (`Unit.lean:204`) over argument *terms*, but there
  is no theorem that a checked node's *conclusion* is well-sorted under Σ. M1's
  `realize` construction will need one to build a program from a labelled
  framework, since it must produce well-sorted conclusions. This is a new
  mechanization obligation for M1, not a gap in the carrier, and it is tracked
  as a Work item on #184 rather than by this record alone.

---

## 3. What M1 inherits

`Invariants.compileUnit_invariant` (`:208`) is M1's necessity direction in the
carrier: every accepted unit compiles to a framework satisfying the record. M1
owes the converse — a `realize` operation from an invariant-satisfying framework
back to an accepted unit, and a proof that compiling it returns an isomorphic
framework.

Two consequences of the record are worth stating before M1 begins, because they
determine whether the sufficiency direction is even plausible:

1. **The image is not all finite AFs.** M1 fixes the signature, policy, and
   backend registry. With the contrary relation fixed, `conflictComplete` forces
   an edge between every declared-contrary pair of node conclusions. A framework
   that labels two nodes with contrary conclusions and omits the edge is outside
   the image — that is `unforcedConflictEx`, witnessed at two *distinct*
   conclusions by `unforcedDistinctConflict_not_invariant`.
2. **Forcing is one-directional.** `conflictComplete` constrains which edges must
   be *present*; it does not say an edge implies contrariety between its
   endpoints' conclusions. `Attack.HasAttack` (`Attack.lean:538`) is precise
   about why: only the rebut rule matches the source conclusion against the
   *target's* conclusion. An undercut matches it against a declared exception
   pattern for a rule occurrence inside the target and requires no contrary at
   all; an undermine matches it against a leaf proposition drawn from Γ inside
   the target. Both therefore produce edges invisible to the conclusion
   labelling, so M1's sufficiency direction will have to *construct* the
   attacks backing an edge, not read them off the labels.

The erased-AF corollary stays open by design. The M0 scope permits an erased
statement "only if it remains nontrivial after labels and term structure
disappear"; whether it does is an M1 question, and `eraseAF` is frozen here so
that question has a fixed subject.

---

## 4. Boundary

- This record does not state M1, any erased-AF expressiveness claim, or any
  complexity result. The M0 scope forbids committing to those before the carrier
  freezes; the freeze is this document.
- `Lara.Erase` is unrelated despite the name: it is the backend-relabel
  development for result 9, not an erasure to a naked framework.
- `Consistency.contrary_args_not_both_grounded` (`Consistency.lean:117`) derives
  the same forced edge inline that `compileUnit_conflictComplete` now derives as
  a named invariant. The duplication is left in place: `Lara.Consistency` is a
  frozen headline result and `Lara.Invariants` imports it, so factoring the
  derivation out would invert the dependency.
