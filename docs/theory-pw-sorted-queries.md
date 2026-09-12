# Theory PW: sorted queries and the outer language's surface

_Status: mechanized 2026-09-09 for issue #307, the two halves scheduled out of
the `docs/theory-pw0-outer-model.md` §5 non-goal rows and the
`docs/theory-pw-closeout.md` §3 surface-syntax row. This document records what the refinement
froze, what it proved, what it deliberately left out, and the one limitation of
PW0's contract it could **not** remove._

PW0 froze `Query_κ` as all of `Atom` and deferred the refinement to the M5
surface layer (`docs/theory-pw0-outer-model.md` §1, limitation 2). M5 landed
(#188), so the condition fired — for the surface-syntax row, which recorded
*no* scheduling condition, this is the condition it was really waiting on. The
two halves scheduled here are:

1. **`Query_κ` well-sortedness** — per-context queries become well-sorted
   claims over `Σ_κ`, and the executable layer gains a posing stage that runs
   before any world is consulted.
2. **Surface syntax for the outer language** — authoring forms for declaring a
   bridge and posing a modal query, elaborated in the M5 shape.

The intended readers are the paper author, whoever cites limitation 2 in print,
and whoever next touches `Lara/PW/`. They should cite the declarations below
rather than re-deriving them; `docs/paper-lean-name-map.md` §PW-sorted carries
the stable keys.

**Nothing local was redefined, and nothing PW0 froze was edited.** `PW.Frame`,
`PW.Sat`, `PW.crossCompare`, `PW.CrossResult` and `PW.IncomparabilityReason`
are untouched. The refinement is a second frame *builder* plus a strictly
earlier guard, and `PW.Sorted.sat_erase` proves the two models agree.

## 1. What the refinement froze

**A query is a claim its context's signature can state.** `PW.Sorted.Query sg`
is the subtype `{c : Atom // Sigma.WellSorted sg c}` — the *existing* `Sigma`
judgment (result 13), not a second one. An ill-sorted query is therefore
*unrepresentable* — `Subtype.mk` demands a `WellSorted` proof — which is a
stronger guarantee than a hidden constructor. `PW.Sorted.pose` is the sanctioned
*decision procedure* over that type: it either returns a query or names which of
exactly two conditions stopped it.

**The two query faults are the two arms of `Sigma.wsAtom`, and no more.**
`undeclaredPredicate` is *out of vocabulary* (the head is not in `Σ_κ`);
`illSortedArguments` is *ill-sorted* (the head is declared, the argument list
fails its declared sort vector — arity included, arity being the length of that
vector). `not_wellSorted_iff_exists_fault` proves they exhaust ill-formedness,
and `queryFault_pred` proves a fault is *located*: it names the atom's own head
predicate. That is the discipline `Sigma.sigmaFault` already follows.

**`gap` now has exactly one meaning, and it is a theorem.**
`cmpStatus_gap_iff_not_addresses` reads the compiled observation's `gap` off one
condition: the world declares no complete argument concluding the claim. The
proof is `Grounded.statusC_gap_iff` instantiated at the world — no new
definition — and `srcStatus_gap_iff_not_addresses` says the same for the
relational source observation, through T1.

**The refined report is a partition, not a new answer.** `PW.Sorted.report` has
four constructors — `outOfVocabulary`, `illSorted`, `unaddressed`, `observed` —
each pinned to exactly its condition. `report_ne_observed_iff_gap` proves that
at a `SortedWorld` the three non-`observed` reports are exactly the atoms PW0
answered `gap` for, so the refinement splits one report and moves no other.

**`SortedWorld` is a real hypothesis, not a formality.** `Gamma` is a checker
*parameter*, so an admitted evidence leaf can carry an atom outside `Σ_κ`; at
such a world an ill-sorted atom could be `justified`, and the refinement would
be changing an answer rather than splitting one. The condition is stated where
it is used. `sortedWorld_of_nodes` discharges it from a finite check on the
retained nodes whenever `canon = id`.

**Every fault is located, including the bridge's.** `queryFault` names the
offending head predicate, and `PW.Sorted.vocabFault` — `trAtom`'s own traversal
— names the first symbol a bridge's map cannot carry, in whichever of the two
namespaces it falls (`OutOfVocabulary.pred` / `.con`).
`vocabFault_eq_none_iff` proves the scan is exactly `trAtom`'s domain
condition, so carrying the symbol costs nothing in the definedness theorems.
That matters because a surface-declared bridge always has a finite vocabulary
(`Surface.predMapOf_eq_none`), which makes this the fault most likely to reach
an author.

**Posing is world-independent, and that is the point.**
`notPosable_world_independent` proves the three bridge-level posing faults give
the same verdict for *any* candidate list, acceptance predicate and status
function — including at a target context with no worlds at all. This is what
stops a vocabulary or sorting mismatch from being read as "the target field
considered this and found it unsupported", the misreading PW0's limitation 2
had to warn about in prose.

**The bridge translation is derived from a symbol map, not a free field.**
`PW.Sorted.SortedBridgeData` carries `sym : B → SymMap` (T6's), and
`PW.Sorted.trQuery` derives the typed partial translation: translate the
symbols, then demand the result be a query of the *target* signature. So a
translated claim the target field cannot state is a reported fault rather than a
`gap` at a target world.

**`translationUndefined` is split.** PW0's one reason conflated *outside the
bridge's symbol map* with *the target field cannot state this*.
`PosingFault.bridgeVocabulary` and `PosingFault.targetQuery` separate them, and
the second names the offending predicate.

**The surface is untyped and elaboration is a typing pass.** `Surface.SForm`
carries raw `Atom`s and names bridges by identifier; `PW.Form` is intrinsically
typed by its context index. `Surface.elabForm` resolves and types, and its
status-atom case *is* `Sorted.pose` — which is where the two halves meet.

**One of T6's three clauses is decidable; two are not.** A `Policy` carries its
rules as a finite `List RuleDecl`, so `Surface.ruleOkB` decides
`StructuralBridge.rule_ok` and `ruleOkB_iff` proves the decider is the clause.
`leaf_ok` quantifies over `Gamma`, a function, and `cert_ok` is an arbitrary
`Prop` over backends; both stay declared premises in
`Surface.BridgeObligations`. The canonicalizer agreement is likewise
undecidable and is a *field* of `Surface.BridgeEnv` rather than a check the
elaborator pretends to perform.

## 2. Theorem table

Every *theorem* row is `lean/AxCheck.lean`-gated: sorry-free, within the
standard trio (`propext`, `Classical.choice`, `Quot.sound`), no
`native_decide`. Rows that also name a *definition* — `structuralBridgeOf` in
U4, `unelab` in U9, `SortedWorld` in S9 — name it for orientation; a definition
carries no `#print axioms` line of its own and is audited transitively through
the gated theorems that mention it. `docs/paper-lean-name-map.md` §PW-sorted
states the same hedge.

| # | Result | Lean |
|---|---|---|
| S1 | No fault is exactly well-sortedness | `PW.Sorted.queryFault_eq_none_iff` |
| S2 | Each fault pinned to exactly its condition | `PW.Sorted.queryFault_undeclaredPredicate_iff`, `queryFault_illSortedArguments_iff` |
| S3 | A fault is located at the atom's own head | `PW.Sorted.queryFault_pred` (the total classifier behind it is `private`: it fabricates a fault for a well-sorted atom, so only the gated report is public) |
| S4 | The two faults exhaust ill-formedness | `PW.Sorted.not_wellSorted_iff_exists_fault` |
| S5 | Posing is sound, complete, and does not rewrite the claim | `PW.Sorted.pose_ok_iff`, `pose_error_iff`, `pose_ok_val`, `pose_val_self` |
| S6 | **`gap` means exactly "the world declares no complete argument for this"** | `PW.Sorted.cmpStatus_gap_iff_not_addresses`, `srcStatus_gap_iff_not_addresses` |
| S7 | An addressed claim never gaps; it gets a substantive status | `PW.Sorted.not_gap_of_addresses`, `status_of_addresses` |
| S8 | The refined report's four constructors, each pinned | `PW.Sorted.report_observed_iff`, `report_unaddressed_iff`, `report_outOfVocabulary_iff`, `report_illSorted_iff` |
| S9 | **The split moves no PW0 answer** | `PW.Sorted.report_ne_observed_iff_gap` (hypothesis `SortedWorld`, discharged by `sortedWorld_of_nodes`) |
| S10 | The three bridge posing faults, each pinned | `PW.Sorted.crossComparePosed_sourceQuery_iff`, `_bridgeVocabulary_iff`, `_targetQuery_iff` |
| S10a | The vocabulary fault names its symbol, and the scan is exactly `trAtom`'s domain | `PW.Sorted.vocabFault_eq_none_iff`, `vocabFault_isSome_of_trAtom_none`, `vocabFaultTerm_eq_none_iff`, `vocabFaultTerms_eq_none_iff` |
| S10b | PW0's `translationUndefined` is unreachable past the new guard, so the split has no live rival | `PW.Sorted.crossComparePosed_ne_translationUndefined`, `crossCompare_some_ne_translationUndefined` |
| S11 | **A posing fault consults no world** | `PW.Sorted.notPosable_world_independent` |
| S12 | A fault carries no `Status`, structurally | `PW.Sorted.notPosable_ne_compared` |
| S13 | Where PW0 answered, the refined interface returns PW0's answer | `PW.Sorted.crossComparePosed_compared` |
| S14 | T4 and valuation coherence at the sorted frame | `PW.Sorted.sat_src_iff_cmp`, `cmpVal_functional`, `cmpVal_total`, `srcVal_functional`, `srcVal_total` |
| S15 | **Conservativity: the sorted and PW0 models satisfy the same formulas** | `PW.Sorted.sat_erase`, `sat_erase_src` |
| U1 | The declared symbol map is undefined outside its declaration | `PW.Surface.predMapOf_eq_none` |
| U2 | **`ruleOkB` decides `StructuralBridge.rule_ok`** | `PW.Surface.ruleOkB_iff` |
| U2a | The clause-completeness check quantifies over the `Clause` *type*, not over a maintained list | `PW.Surface.Clause.mem_all`, `find?_missing_none_iff` |
| U3 | Bridge declarations: sound, complete, deterministic — with the judgment stating T6's `rule_ok` verbatim, so the trio is not bookkeeping over the decider | `PW.Surface.elabBridge_sound`, `elabBridge_complete`, `elaboratesBridge_deterministic` |
| U4 | **Preservation: a derivable declaration is T6's contract** | `PW.Surface.elabBridge_preserves`; the contract is carried by the *type* of `structuralBridgeOf`, exercised at a fixture by `Examples.PWSurface.bridgeDeclOK` with `obligations_declOK` discharged |
| U5 | **T6 at a surface-authored bridge**, concluding in the target's own judgment | `PW.Surface.elabBridge_support_transport`, instantiated at `Examples.PWSurface.support_transport_declOK` |
| U6 | Reflection | `PW.Surface.elabBridge_reflects` |
| U7 | Names identify frame indices, and resolution round-trips in both directions so an error report echoes the spelling the author wrote | `PW.Surface.Naming.ctxName_inj`, `bridgeName_inj` (premises `ctxName_of_ctxOf`, `bridgeName_of_bridgeOf`) |
| U8 | Modal queries: sound, complete, deterministic — with the judgment stating that the typed query carries the authored claim, not that `pose` succeeded | `PW.Surface.elabForm_sound`, `elabForm_complete`, `elaborates_deterministic` |
| U9 | **Preservation: the typing pass renames nothing** | `PW.Surface.elaborates_preserves` (round trip `unelab ∘ elab = id`) |
| U10 | Reflection, and the other round trip | `PW.Surface.elaborates_reflects`, `elabForm_unelab` |
| U11 | Posing resolves the context name | `PW.Surface.elabPosed_ok_iff` |

## 3. The witnesses

Mechanized results about a refinement are worth little without a case where the
refinement fires, so the headline fixture is **one world at which PW0 reports
`gap` three times for three different reasons**
(`lean/Lara/Examples/PWSorted.lean`). It reuses PW0's overlapping-fields pair
unchanged — `sigmaEx` declares `p`, `q`, `s`; `sigmaOverlap` declares `p`, `q`,
`r` and not `s` — because that pair exists precisely to make "neither
vocabulary contains the other" concrete, and `overlap_local_gap` already pins
the PW0 answer being refined.

At `wOverlap`, whose single admitted argument concludes `q`:

| authored claim | PW0 (`cmpStatus`) | refined (`report`) |
|---|---|---|
| `p()` | `gap` | `unaddressed` |
| `s()` | `gap` | `outOfVocabulary "s"` |
| `q(z)` | `gap` | `illSorted "q"` |
| `q()` | `justified` | `observed justified` (unchanged) |

`reports_distinct` proves the three are pairwise distinct and
`split_not_change` proves all three are still PW0 `gap`s — so the split is real
*and* is a split.

At the bridge, `sorted_s_targetQuery` is the sharpened form of
`overlap_translationUndefined`, and `bridge_and_target_faults_distinct` pins
that the two conditions PW0 could not tell apart now differ — as an inequality
between two `crossComparePosed` applications, not between two constructors.
`sorted_t_targetIllSorted` closes the target fault's other branch (a predicate
declared at *both* ends with different arities, which a vocabulary-membership
test would pass), and `sorted_t_bridgeVocabulary_con` closes the vocabulary
fault's constructor namespace.

For the surface (`lean/Lara/Examples/PWSurface.lean`), the bridge fixture
declares a policy with a *rule*, so `ruleOkB` is not vacuous:
`rule_clause_holds` is the positive cell, and there is one negative cell per
way the clause can fail — the target carries nothing at the identifier
(`rule_clause_fails`), the target carries a *different* rule there
(`rule_clause_fails_mistranslated`), and the declared map cannot translate the
source rule at all (`rule_clause_fails_untranslatable`).

The fixture's two contexts carry a `Gamma` pair **inside the declared
vocabulary**, so `obligations_declOK` *discharges* `BridgeObligations` instead
of assuming it: `bridgeDeclOK` is a real `PW.StructuralBridge` at a concrete
declaration, and `support_transport_declOK` carries a checked support across it
into the target field's own judgment — U4 and U5 exercised, not merely stated.
`elabBridge_nameMismatch` / `_sourceMismatch` / `_targetMismatch` show the
declaration's own names are read.

`elab_illSorted` is the fixture that joins the two halves — an ill-sorted
authored claim is a typing error at authoring time, named and located, where
PW0 had no choice but to send it to a world and report the `gap` that came
back. `elab_sourceMismatch` exercises the typing of the modality itself:
reading `⟨b⟩` from the wrong field is rejected, and
`elabPosed_unknownContext` the one step `elabPosed` adds over `elabForm`.

## 4. The one limitation that could not be removed

PW0's limitation 2 named **four** conditions that `gap` conflated: *out of
vocabulary*, *ill-sorted*, *not posed*, and *posed but unsupported*. The first
two are gone. The last two **coincide in this model**, and that is a theorem
rather than an omission:

- every argument an accepted unit retains is *complete* —
  `Compile.CheckedNode.valid` carries the empty obligation list, and
  `Unit.CheckedUnit.nodes_terms` ties the retained nodes to `program.args`; and
- `Grounded.statusC` gaps exactly on empty complete support
  (`Grounded.statusC_gap_iff`).

So there is no world at which a claim is addressed and still gaps
(`PW.Sorted.not_gap_of_addresses`), and "posed but unsupported" is not a fourth
`gap` cause: it surfaces as `defeated` or `contested`.

Separating a genuinely *incomplete* attempt from an absent one would need
`holes(P, p)` at the instance layer, which `Consistency.completeClaimFor`
deliberately does not compute — its `holes` field is definitionally empty, an
N17 point (1) modeling convention recorded in `Lara/Grounded.lean` and
`Lara/Consistency.lean`. Computing it is a change to the local layer, which the
outer wrapper's gate-1 discipline forbids. **The paper must therefore not claim
limitation 2 is closed. It is narrowed: four conditions become two reported
ones plus a proved collapse.**

## 5. What this deliberately does not contain

| Absent | Why |
|---|---|
| ~~A Haskell outer runtime and differential gate~~ | Landed in **#322**; see [the outer runtime contract](theory-pw-outer-runtime.md). Concrete input and declaration/query linkage landed earlier in **#313/#314** ([the wire contract](theory-pw-declared-wire.md)). The byte parser remains a tested boundary; structured codec round trips are proved. |
| An edit to `PW.Frame`, `PW.Sat`, `crossCompare`, or `CrossResult` | PW0's frozen contract. The refinement is a second builder and an earlier guard; `sat_erase` relates them |
| `holes(P, p)` at the instance layer | §4 |
| Edge-dependent (configuration) translation | Still PW0 limitation 3 / T6 limitation 1. `trQuery` is bridge-global, exactly as `Frame.translate` was |
| `StructuralBridge.refl` as a surface declaration | `SymMap.id` is total and no finite entry list is (`predMapOf_eq_none`). A surface-declared bridge always carries a finite, written vocabulary — a boundary of the authoring form, not of the model |
| A decided `leaf_ok`, `cert_ok`, or canonicalizer agreement | Undecidable: `Gamma` and `canon` are functions and `CertOk` is an arbitrary `Prop`. They are declared premises, named where used |
| Approximation bridges, epistemic relations, dynamic update operators, hybrid/named-world operators, global scenarios, T10 | Still deferred; `docs/theory-pw-closeout.md` §3, unchanged |

## 6. Verification

At the merge commit of #307: whole-tree AxCheck coverage passes at **2934
declarations** (`scripts/check-axcheck-coverage.py` over `lean/AxCheck.lean`
and every `lean/Lara/**/*.lean`), and the axiom audit admits only `propext`,
`Classical.choice` and `Quot.sound` — so no declaration here can reach a
`sorryAx`, `ofReduceBool`, or `nativeDecide` obligation. The four new modules
are `Lara/PW/Sorted.lean`, `Lara/Examples/PWSorted.lean`,
`Lara/PW/Surface.lean`, and `Lara/Examples/PWSurface.lean`; all four are inside
the `lake build` closure through `lean/Lara.lean` (issue #259's discipline).
