# PW — sorted queries and a surface for the outer language

## Result

Issue #307, PR #311 (branch `theory/307-sorted-queries-outer-surface`). The two
deferrals held for the M5 surface machinery (#188): the `Query_κ`
well-sortedness row of `docs/theory-pw0-outer-model.md` §5, and the
surface-syntax row of `docs/theory-pw-closeout.md` §3, which recorded *no*
scheduling condition and mentioned the refinement in prose. Four new modules
that only import — `Lara.PW.Sorted`,
`Lara.Examples.PWSorted`, `Lara.PW.Surface`, `Lara.Examples.PWSurface` — over
the unchanged local checker and the unchanged PW0 wrapper. `PW.Frame`,
`PW.Sat`, `PW.crossCompare`, `PW.CrossResult` and `PW.IncomparabilityReason`
are untouched.

## The finding: PW0 limitation 2 narrows, but cannot close

The limitation states in print that `gap` conflates **four** conditions:

> **2. `gap` conflates four conditions** — *out of vocabulary*, *ill-sorted*,
> *not posed*, and *posed but unsupported* — because queries are all of `Atom`

The design that entered this work was a four-way split. It does not exist. Two
of the four coincide, and the reason is a theorem already in the development:

```
theorem statusC_gap_iff (F : AF) (c : Claim) : statusC F c = Status.gap ↔ c.support = []
```

together with the fact that every argument an accepted unit retains is
*complete* — `Compile.CheckedNode.valid` has type
`HasSupport canon Pi Gamma CertOk term conclusion []`, with the empty
obligation list, and `Unit.CheckedUnit.nodes_terms` ties the retained nodes to
`program.args`. So an addressed claim has nonempty complete support and cannot
gap:

```
theorem cmpStatus_gap_iff_not_addresses {κ : Context} (w : World κ) (c : Atom) :
    cmpStatus w c = Status.gap ↔ ¬ Addresses w c

theorem not_gap_of_addresses {κ : Context} (w : World κ) (c : Atom)
    (h : Addresses w c) : cmpStatus w c ≠ Status.gap
```

"Posed but unsupported" is therefore not a fourth `gap` cause in this model; it
surfaces as `defeated` or `contested`. Separating a genuinely *incomplete*
attempt from an absent one would need `holes(P, p)` at the instance layer,
which `Consistency.completeClaimFor` deliberately does not compute — its
`holes` field is definitionally empty, an N17 point (1) modeling convention.
Computing it is a change to the *local* layer, which the wrapper's gate-1
discipline forbids.

Net: four conflated conditions become **two reported ones plus a proved
collapse**. `docs/theory-pw-sorted-queries.md` §4 and the PW0 record's
limitation 2 both say *narrowed*, not *closed*.

## What the two Σ-level conditions became

`PW.Sorted.Query sg` is `{c : Atom // Sigma.WellSorted sg c}` — the existing
`Sigma` judgment (result 13), not a second one. `pose` is the sanctioned
*decision procedure* — the subtype makes an ill-sorted query unrepresentable,
which is stronger than a hidden constructor — and the two faults are literally
the two arms of `Sigma.wsAtom`, with `not_wellSorted_iff_exists_fault` proving
they exhaust ill-formedness.

Every fault is *located*, including the bridge's: `vocabFault` is `trAtom`'s
own traversal reporting the first symbol the bridge cannot carry, in whichever
of `SymMap`'s two namespaces it falls, and `vocabFault_eq_none_iff` proves the
scan is exactly `trAtom`'s domain condition — so the located report costs
nothing in the definedness theorems. PW0's `translationUndefined` is
unreachable past the new guard (`crossComparePosed_ne_translationUndefined`),
so the split it was replaced by has no live rival in the result type.

The load-bearing theorem is that the verdict consults no world:

```
theorem notPosable_world_independent {W W' : Type} (sgS sgT : Lara.Sigma.Sigma)
    (m : SymMap) (raw : Atom)
    (candidates : List W) (acceptB : W → Bool) (statusOf : W → Query sgT → Status)
    (candidates' : List W') (acceptB' : W' → Bool)
    (statusOf' : W' → Query sgT → Status) (f : PosingFault) :
    crossComparePosed sgS sgT m raw candidates acceptB statusOf = .notPosable f ↔
      crossComparePosed sgS sgT m raw candidates' acceptB' statusOf'
        = .notPosable f
```

Same verdict for *any* candidate list, acceptance predicate and status
function, including at a target context with no worlds at all. That is what
stops a vocabulary or sorting mismatch from being read as "the target field
considered this and found it unsupported".

`report_ne_observed_iff_gap` — the theorem that the split moves no PW0 answer —
carries a real hypothesis, `SortedWorld`. `Gamma` is a checker *parameter*, so
an admitted evidence leaf can carry an atom outside `Σ_κ`; at such a world an
ill-sorted atom could be `justified` and the refinement would be *changing* an
answer rather than splitting one. `sortedWorld_of_nodes` discharges it from a
finite check on the retained nodes when `canon = id`.

## Which contract clauses a surface can check

T6's `StructuralBridge` has three clauses. Exactly **one** is decidable from
declared data, and the split is decided by whether the environment component is
a finite table or a function:

| clause | reads | decidable? |
|---|---|---|
| `rule_ok` | `Policy.ruleLookup`, backed by a finite `List RuleDecl` | **yes** — `ruleOkB`, proved to be the clause by `ruleOkB_iff` |
| `leaf_ok` | `Gamma : LeafId → Option Atom`, a function | no — declared premise |
| `cert_ok` | `CertOk : … → Prop`, arbitrary | no — declared premise |
| shared `canon` | `String → String`, function equality | no — a field of `BridgeEnv` |

So `elabBridge_support_transport` carries T6 to a surface-authored bridge only
against the premises the surface cannot discharge, and the type records which.
At the fixture those premises are *discharged* (`obligations_declOK`), not
assumed: the two contexts carry a `Gamma` pair inside the declared vocabulary,
so `bridgeDeclOK` is a real `PW.StructuralBridge` at a concrete declaration and
`support_transport_declOK` carries a checked support across it into the target
field's own judgment.

The declaration's own names are read too. `BridgeEnv` carries the bridge and
context names, so a declaration reading `src → tgt` no longer elaborates
identically against any environment. What is still unjoined is the declared
`BridgeId` and `Naming.bridgeOf`, so a declared bridge cannot yet be *named* by
a posed query — the two halves meet at the status-atom level (`Sorted.pose`)
and not at the bridge level (#313).

One honest negative: `predMapOf_eq_none` implies `StructuralBridge.refl` is not
in this surface's image, since `SymMap.id` is total and no finite entry list
is.

## The witness: one world, three PW0 `gap`s, three reports

`Lara/Examples/PWSorted.lean` reuses PW0's overlapping-fields pair unchanged —
`sigmaEx` declares `p`, `q`, `s`; `sigmaOverlap` declares `p`, `q`, `r` and not
`s` — because `overlap_local_gap` already pins the PW0 answer being refined. At
`wOverlap`, whose single admitted argument concludes `q`:

| authored claim | PW0 (`cmpStatus`) | refined (`report`) |
|---|---|---|
| `p()` | `gap` | `unaddressed` |
| `s()` | `gap` | `outOfVocabulary "s"` |
| `q(z)` | `gap` | `illSorted "q"` |
| `q()` | `justified` | `observed justified` (unchanged) |

`reports_distinct` proves the three are pairwise distinct; `split_not_change`
proves all three are still PW0 `gap`s. So the split is real *and* is a split.

`sorted_s_targetQuery` is the sharpened `overlap_translationUndefined`;
`sorted_t_targetIllSorted` closes the target fault's other branch — a predicate
declared at *both* ends with different arities, which a vocabulary-membership
test would pass — and `sorted_t_bridgeVocabulary_con` closes the vocabulary
fault's constructor namespace. `bridge_and_target_faults_distinct` compares two
`crossComparePosed` applications rather than two constructors.

`elab_illSorted` (`Lara/Examples/PWSurface.lean`) is the cell that joins the
two halves: an ill-sorted authored claim is a typing error at authoring time,
named and located, where PW0 had no choice but to send it to a world.

## Gates

Run locally (CI has not run since 2026-08-25; #225 reopened), from a build in
which the four new `.olean`s were deleted first, so nothing ran against a stale
artifact.

```
✔ [168/173] Built Lara.PW.Sorted (4.4s)
✔ [169/173] Built Lara.Examples.PWSorted (2.6s)
✔ [170/173] Built Lara.PW.Surface (5.2s)
✔ [171/173] Built Lara.Examples.PWSurface (3.2s)
Build completed successfully (173 jobs).
```

```
AxCheck coverage passed (2934 declarations).
Axiom audit passed.
Lean citations: PASS (420 citations, 29 allowlisted)
ARA source spans: PASS (62 quotations)
```

The axiom audit admits only `propext`, `Classical.choice` and `Quot.sound`, so
no declaration here can reach a `sorryAx`, `ofReduceBool` or `nativeDecide`
obligation. All four modules are inside the `lake build` closure through
`lean/Lara.lean` (#259's discipline), which the deleted-olean rebuild confirms.

No Haskell change: the outer language has no Haskell runtime, and the surface
is a structured AST with no parser or wire format — the same cut
`Lara.Surface` makes. That gap is unscheduled work and is tracked as #314.
