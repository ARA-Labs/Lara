# Paper ↔ Lean name map (P1–P3 gate, issue #68)

Rule (from #68 / the M7 paper package): every formal object displayed in the
PLDI draft is **transcribed from the Lean development, never invented
paper-side**. Each paper display cites its Lean declaration in a provenance
comment of the form `% lean: <File.lean> : <declaration>`. Line numbers below
are as of commit `93d2a85` and are a convenience only; the declaration name is
the stable citation key.

All theorems named here are covered by `lean/AxCheck.lean` (sorry-free,
standard trio `propext` / `Classical.choice` / `Quot.sound`).

---

## 1. Direct source semantics + status preservation (paper `thm:preservation`, G3)

**Confirmed pairing.** The theorem the paper must cite for source-vs-compiled
status preservation is

> `Lara.Compile.srcStatus_iff_checked` (`lean/Lara/Compile.lean:900`)
>
> ```lean
> theorem srcStatus_iff_checked
>     (P : CheckedProgram canon Pi Gamma CertOk dp) (c : Grounded.Claim)
>     (s : Grounded.Status) :
>     SrcStatus P c s ↔ s = Grounded.statusC (checkedAF P) c
> ```

**Not** `Lara.Grounded.status_preservation` (`Grounded.lean:607`). That lemma
is framework-level only: it proves `statusDirect F c = statusC F c` over a
*single* abstract `F : AF` — both sides read the same `F.attack`, so it never
exercises `compile`. Its own docstring says so, pointing at the file-level
scope note. (The scope note referenced in #68 as "Compile.lean:606" actually
lives in `Grounded.lean`: the module header at `Grounded.lean:7–20` and the
`status_preservation` docstring at `Grounded.lean:601–606`.) The paper may
cite `status_preservation` only as the abstract-AF core of the equivalence,
never as the headline preservation theorem.

### The equivalence is genuinely two-sided — contingency not needed

The independent direct source semantics exists: `SrcIn` / `SrcOut`
(`Compile.lean:668–678`) is a mutually inductive declarative judgment defined
over the **Prop-level** closure-edge relation `Edge P` (`Compile.lean:505`) —
it never materializes the grounded iteration and never consults the Boolean
edge oracle. `SrcStatus` (`Compile.lean:751`) lifts it to four-state claim
status, again with no AF, no iteration, no oracle. `srcStatus_iff_checked`
is a true iff between that source-side relation and executable compiled
evaluation, so option (a)/(b) of #68's contingency is moot.

### Exact hypotheses

The only hypothesis is `P : CheckedProgram canon Pi Gamma CertOk dp`
(`Compile.lean:471`) — the checker's postcondition, carrying:

- `nodup : args.Nodup` — `Args(P)` is a set of terms (spec §8);
- `complete : ∀ w ∈ args, ∃ C, HasSupport canon Pi Gamma CertOk w C []` —
  every declared argument is a complete checked support term (`O = ∅`);
- `typed : ∀ k ∈ atts, Attack.HasAttack canon Pi Gamma CertOk dp k` — every
  declared attack types (§7.1);
- `source_declared` / `target_declared` — attack endpoints are declared
  arguments (R1 boundary).

No oracle hypothesis remains: the oracle-parametric bridge (`Faithful`,
`srcStatus_iff` at `Compile.lean:860`) is instantiated constructively by the
checker-built decider `edgeB` (`Compile.lean:617`) via `edgeB_faithful`
(`Compile.lean:649`), yielding the oracle-free wrappers.

### What plays the simulation-relation role

There is no separately named simulation relation. The two sides share the
argument carrier by **positional indexing**: `toAF` (`Compile.lean:597`)
takes `Grounded.Arg = Nat` to be the index into `P.args`, and the structure
`Faithful` (`Compile.lean:605`, fields `ranged` / `agrees`) is the
correspondence: the Bool edge decider agrees with the Prop-level `Edge` on
in-range indices (`P.args[i]? = some a`) and is false off-range. The paper
should describe the relation as "argument *i* of the compiled AF ↔ the *i*-th
declared checked term", certified by `Faithful` and discharged by
`edgeB_faithful`.

### Row map

| Paper object | Lean declaration | File:line |
|---|---|---|
| Direct source judgment (in/out) | `Compile.SrcIn`, `Compile.SrcOut` | `Compile.lean:669,674` |
| Source-level four-state status | `Compile.SrcStatus` | `Compile.lean:751` |
| Compiled edge relation (subargument closure) | `Compile.Edge` | `Compile.lean:505` |
| Well-formed source program (checker postcondition) | `Compile.CheckedProgram` | `Compile.lean:471` |
| Index correspondence certificate | `Compile.Faithful` | `Compile.lean:605` |
| Checker-built edge decider + its faithfulness | `Compile.edgeB`, `Compile.edgeB_faithful` | `Compile.lean:617,649` |
| Compiled AF (oracle-free) | `Compile.checkedAF` | `Compile.lean:880` |
| Argument-level bridge (oracle-parametric) | `Compile.srcIn_iff_directIn`, `Compile.srcOut_iff_directOut` | `Compile.lean:726,732` |
| Argument-level bridge (oracle-free, vs executable grounded) | `Compile.srcIn_iff_checkedGrounded` | `Compile.lean:885` |
| Status functionality | `Compile.srcStatus_unique` | `Compile.lean:828` |
| **Headline: status preservation (two-sided, oracle-free)** | `Compile.srcStatus_iff_checked` | `Compile.lean:900` |
| Abstract-AF core only (do not cite as headline) | `Grounded.status_preservation` | `Grounded.lean:607` |

---

## 2. Grounded machinery (paper P2)

All in `lean/Lara/Grounded.lean`; every theorem quantifies over an arbitrary
finite `F : AF`. No Mathlib.

| Paper object | Lean declaration | Line |
|---|---|---|
| Argumentation framework (finite carrier + decidable attack) | `Grounded.AF` | 65 |
| Defense ("every attacker of `a` is attacked by `S`") | `Grounded.defendedB`, spec `defendedB_iff` | 86, 89 |
| Characteristic function (one round) | `Grounded.step`, monotone: `step_mono` | 109, 120 |
| Iteration from ∅ | `Grounded.iter` (ascending: `iter_mono`) | 133, 148 |
| Grounded extension (least fixpoint, computed) | `Grounded.grounded` | 141 |
| Termination/determinism: stabilizes within \|args\| steps | `Grounded.grounded_stable` | 334 |
| Fixpoint property | `Grounded.grounded_fixpoint` | 359 |
| Conflict-freedom of the grounded extension | `Grounded.ConflictFree`, `grounded_conflictFree` | 157, 179 |
| Declarative (direct) in/out judgment | `Grounded.DirectIn`, `Grounded.DirectOut` | 195, 198 |
| Declarative ≡ executable, argument level | `Grounded.directIn_iff` | 382 |
| Three-way labels in/out/undec | `Grounded.Label`, `Grounded.labelC` | 54, 404 |
| Label characterizations | `labelC_inn_iff`, `labelC_out_iff`, `labelC_undec_iff` | 433, 449, 458 |
| Four-state claim status | `Grounded.Status`, `Grounded.statusC` | 59, 516 |
| `gap` ⇔ empty complete support (N17 pt 1, mechanized half) | `Grounded.statusC_gap_iff` | 525 |
| `justified` ⇔ some support argument labelled in | `Grounded.statusC_justified_iff` | 541 |
| Compilation with subargument closure (abstract) | `Grounded.compile`, `compile_attack_iff` | 480, 489 |

Wording caveats the paper must respect (from the module docstrings):
`contested := grounded undec` is the broad reading (N17 pt 2); "holes surface
via a diagnostic" (`incompleteAlternative`, line 588) is a modeling
convention, not a theorem; the evaluator is a proof-oriented reference, not
the production evaluator.

---

## 3. Strict-chain well-formedness (paper P2 / `thm:rationality`, G6)

The rationality theorem is

> `Lara.Consistency.contrary_claims_not_both_justified`
> (`lean/Lara/Consistency.lean:165`)
>
> ```lean
> theorem contrary_claims_not_both_justified
>     (unit : Unit.CheckedUnit canon Gamma CertOk)
>     {p q : Atom}
>     (hcontrary : Attack.ContraryMatch canon unit.policy.defeat p q) :
>     ¬ (Grounded.statusC (Compile.checkedAF unit.program)
>           (completeClaimFor unit p) = Grounded.Status.justified ∧
>        Grounded.statusC (Compile.checkedAF unit.program)
>           (completeClaimFor unit q) = Grounded.Status.justified)
> ```

Scope the paper must keep: the claims are `completeClaimFor`
(`Consistency.lean:84`) — computed from the accepted unit's retained checked
nodes; the statement does **not** quantify over arbitrary caller-supplied
claims, and holes are definitionally empty here.

The strict-chain hypothesis enters as the `policy_wf` field of
`Unit.CheckedUnit` (`lean/Lara/Unit.lean:35`), whose exact Lean form is
(`lean/Lara/Policy.lean:448`), **verbatim**:

```lean
def WellFormed (canon : String → String) (P : Policy) : Prop :=
  ∀ p, StrictReachable P p →
    ∀ ab ∈ P.defeat.contraries,
      aPatMayOverlap canon p ab.1 = false ∧
      aPatMayOverlap canon p ab.2 = false
```

with (`Policy.lean:201`), **verbatim**:

```lean
inductive StrictReachable (P : Policy) : APat → Prop where
  | conclusion {d : RuleDecl}
      (hdecl : d ∈ P.rules) (hstrict : d.rule.mode = .strict) :
      StrictReachable P d.rule.concl
```

Reading the paper must transcribe exactly:

- **Strict-reachable = conclusion pattern of a declared strict rule.** This
  is the finite presentation of the spec's least set; closure under the
  premises-to-conclusion chain step is `strictReachable_closed`
  (`Policy.lean:209`), and the list form is `strictReachable_iff_mem`
  (`Policy.lean:220`).
- **Overlap is a conservative unifiability check** (`aPatMayOverlap`,
  variables as wildcards, one-sided guarantee — can reject a safe policy,
  cannot accept overlapping ground instances; `Policy.lean:234–259` notes).
- Decidability / executable check: `wfB` (`Policy.lean:444`), adequacy
  `wfB_iff` (`Policy.lean:620`), `decideWellFormed` (`Policy.lean:657`).
- Where the hypothesis bites in the proof: `wellFormed_no_strict_contrary_right`
  (`Policy.lean:642`) via `wellFormed_contrary_target_attackable`
  (`Consistency.lean:42`, Path B: a contrary target cannot be a strict-rule
  root, hence is conflict-attackable).

Other hypotheses of the theorem, all carried by `Unit.CheckedUnit`
(`Unit.lean:30`): `ruleIds_nodup`, the `program : CheckedProgram` invariants
(§1 above), `attack_complete : Compile.AttackComplete …`
(`Compile.lean:515`), and the retained node cache `nodes` with
`nodes_terms`. The contrary hypothesis is `Attack.ContraryMatch`
(`Attack.lean:85`), the implicitly-universally-quantified `contrary` of §4.1.

---

## 4. Backend interface laws B1–B4 (paper P3)

The interface is `Lara.Strict.Backend` (`lean/Lara/Strict.lean:77`), one core
per registered `(name, version)` identity, indexed by the source
canonicalizer, operating on the explicit full context `Γ = Δ ++ T` (premises
then digest-resolved theory *data*). Two registered instances discharge every
law: ND (`Strict.ndBackend`, `Strict.lean:759`) and RA (`RA.raBackend`,
`RA.lean:450`).

| Law | Interface (Strict.lean) | ND discharge | RA discharge |
|---|---|---|---|
| **B1** deterministic terminating replay | `Backend.replayFull` (:91) is a total Lean function — termination and determinism by construction; adequacy `replayFull_iff` (:93); caller-facing `replay` / `replay_iff` (:136, :140) | `ndReplay` (:664, decode + `ND.infer`, "no proof search"), `ndReplay_iff` (:673); uniqueness `ND.hasType_unique` (`ND.lean:861`) | `raReplay` (`RA.lean:341`, decode + `checkB`, "no search"), `raReplay_iff` (:346) |
| **B2** normalization reflection: `encode p = encode q ↔ p ≡ q` | field `enc_iff` (:83), with `p ≡ q` := `Lara.equiv canon p q` = `nf canon p = nf canon q` (`Prop.lean:70`) | `ndEnc_iff` (:642), via `encodeAtomKey_injective` (:631) and round-trip `decodeAtomKey_encodeAtomKey` (:590) | `enc := nf canon` (identity encoding), `enc_iff` = `equiv_iff_nf_eq` (`Prop.lean:78`) |
| **B3** certificate soundness w.r.t. the backend consequence relation | field `soundFull` (:94); consequence relation = `modelsFull` (:85); derived `Backend.sound` (:145); headline **Theorem 1** `strict_step_sound` (:217) | `ND.nd_sound` (`ND.lean:396`), algorithmic side `ND.infer_sound` (`ND.lean:549`); consequence `ndModels` (:649) | `raSound` (`RA.lean:386`) via `checkB_extract` (:361); consequence `raModels` (:326) |
| **B4** exact dependency reporting (obligation 4, three clauses) | `uses` (:101); coverage `uses_covers` (:107); validity `uses_valid` (:113); accounting `uses_account` (:118); theory corollaries `replay_theory_covers` (:166), `replay_theory_agnostic` (:181), `uses_valid_closed` (:152) | `ndReplay_agree` (:720), `ndUses_valid` (:736), `ndUses_account` (:703); checker tie `ndUses_eq_infer_deps` (:747); operational core `ND.nd_relevance` (`ND.lean:360`), `ND.fv_in_range` (:404), `ND.infer_deps_eq_fv` (:711), `ND.infer_agree` (:799) | `raUses_covers` (`RA.lean:396`), `raUses_valid` (:417), `raUses_account` (:432) |

Notes for the paper wording:

- B1's "deterministic, terminating" is definitional in Lean (total function
  into `Bool`), so the paper should phrase it as "replay is a total Boolean
  function of the submitted certificate, context, and goal; adequate for
  propositional acceptance (`replayFull_iff`)" — there is no separate
  termination lemma to cite, and none is needed.
- B4's paper gloss "exact dependency reporting" is carried jointly by the
  three clauses; "the report is exactly what the running checker computes" is
  specifically `ndUses_eq_infer_deps`.
- Non-factivity (if displayed): `no_truth_projection` (`Strict.lean:811`),
  witness `nd_nonfactive_witness` (:800), side-by-side
  `nd_relative_not_absolute` (:817).

---

## Validation status

- Read-only audit; no Lean changes (happy path of #68).
- `lean/AxCheck.lean` already `#print axioms`-gates every headline row:
  `srcStatus_iff_checked` (:381), `srcIn_iff_checkedGrounded` (:379),
  `status_preservation` (:562), `grounded_stable` (:550),
  `contrary_claims_not_both_justified` (:600), `strict_step_sound` (:157),
  `ndBackend` (:159), `raBackend` (:185), `ndUses_eq_infer_deps` (:217).
- Remaining paper-side step (P1–P3 edits in the Overleaf repo): check each
  display side-by-side against the quoted quantifiers/hypotheses above, and
  in particular ensure `thm:preservation` cites `srcStatus_iff_checked`
  (source-vs-compiled), not `status_preservation` (single-framework), and
  that `thm:rationality` is scoped to computed complete claims of an
  accepted unit.

## 4. Policy admission (source boundary)

Issue #77 follow-on family (metatheory plan Task 2, commit `014173e`).
Every paper display in the source-boundary paragraph and
`figures/admissionrules.tex` is transcribed from `lean/Lara/Admission.lean`;
every theorem row is `lean/AxCheck.lean`-gated (sorry-free, standard trio). Rows
that name only definitions carry no independent axiom obligation.

| Paper object | Lean declaration | File |
|---|---|---|
| Total decision, default admit | `Admission.decisionFor` | `Lara/Admission.lean` |
| Source validity | `firstDuplicateKey`, `firstDuplicateLeafId`, `metadataLeafAligned`, `accepted_metadata_aligned` | `Lara/Admission.lean` |
| First rejected leaf (R8) | `firstAdmissionRejection` | `Lara/Admission.lean` |
| Policy quarantine seed | `policyQuarantineSeed` | `Lara/Admission.lean` |
| Γ_policy / Γ_checked | `policyAdmitted`, `checkedLeafTable`, `checkedAdmittedIds` | `Lara/Admission.lean` |
| Combined prune / canonical audit | `buildPrune`, `buildAdmissionAudit` | `Lara/Admission.lean` |
| Declarative judgment / evaluator | `AdmissionJudgment`, `evaluateAdmission` | `Lara/Admission.lean` |
| Correspondence / determinism | `evaluateAdmission_iff_judgment`, `admission_deterministic` | `Lara/Admission.lean` |
| Exact contexts | `policy_admitted_iff`, `checked_admitted_iff`, `checked_admitted_ids_eq_prune`, `policy_quarantined_absent`, `accepted_checked_context_exact` | `Lara/Admission.lean` |
| Endpoint-safe pruning and validated alignment | `AlignedAttacks`, `accepted_resolved_aligned`, `retained_attacks_selectAligned`; `RawAttack.resolve_filter_commute`, `RawAttack.resolveAttacks_endpoints_mem`, `RawAttack.selectAligned_mono`; `retained_attack_endpoints` | `Lara/Admission.lean`, `Lara/RawAttack.lean` |
| Unique argument ids (R14) as a carried invariant | `AlignedAttacks.ids_nodup`, `retained_attack_source_retained`; `RawAttack.lookupArg_of_mem_nodup`; `Driver.firstDup_none_nodup`, `Driver.Decoded.argIdsNodup` | `Lara/Admission.lean`, `Lara/RawAttack.lean`, `Lara/Driver.lean` |
| Audit exactness | `admission_audit_exact`, `audit_leaves_nonempty` | `Lara/Admission.lean` |
| All-admit identity | `policy_all_admit_group_identity` (prune + blocked queries); `policy_all_admit_checkUnit_identity` (exact checker accept/reject outcome), both over `AlignedAttacks`. Neither proves verdict identity — see the note below | `Lara/Admission.lean` |
| Restrictiveness | `more_restrictive_cannot_add_structure` (leaves, arguments, raw keep predicate, and retained semantic attacks); `Groups.usesLeaf_mono` | `Lara/Admission.lean`, `Lara/Groups.lean` |
| R8 carries no checked unit | `source_reject_no_checked_unit` | `Lara/Admission.lean` |
| Source non-promotion | `source_justified_nonpromotion` (instantiates `BlockedProgram.checked_production_justified_nonpromotion_of_not_blocked`) | `Lara/Admission.lean`, `Lara/BlockedProgram.lean` |

The paper must not claim the `.lara` parser, Haskell elaborator, or final
public verdict are proved by the admission differential. Lean proves the
semantic judgment. `scripts/admission-differential.sh` compares its evaluator
with a test-only Haskell adapter over the production admission/prune
primitives. `test/AdmissionSpec.hs` separately exercises the real
`prepareSource` / `runSourceCheck` seam, including all-admit exact verdict
bytes and quarantine-sensitive blocked status rendering.

---

## 5. M0 compilation carrier and invariant record (theory spine)

Issue #183, tracker #180. The carrier decision and the full invariant
classification live in `docs/theory-m0-compilation-invariants.md`; this section
is the declaration index. Every *theorem* row is `lean/AxCheck.lean`-gated
(sorry-free, standard trio). The rows naming the carrier, the erasure, the
compilation and the invariant record name *definitions*, which carry no
independent axiom obligation — each is transitively audited through a gated
theorem that mentions it: `StructuredAF` and `compileUnit` through
`compileUnit_invariant`, `StructuredAF.size` through `compileUnit_size`,
`eraseAF` through `erase_compileUnit`, and `CompilerInvariant` with both its
fields through `compileUnit_invariant`, `compileUnit_ranged` and
`compileUnit_conflictComplete`. So the frozen carrier *is* covered by the audit,
just not by a line of its own.

No paper display cites these yet. The theory-depth plan's follow-through rule
applies: an M-item becomes claimable only when its own gate closes, and M0 is a
carrier freeze, not a paper theorem. Rows are listed so M1–M3 and the
possible-world wrapper can cite a stable key rather than re-deriving one.

| Object | Lean declaration | File |
|---|---|---|
| The M1 carrier (conclusion-labelled AF) | `Invariants.StructuredAF`, `StructuredAF.size` | `Lara/Invariants.lean` |
| The frozen erasure to a naked Dung framework | `Invariants.eraseAF`; coherence with the existing pipeline by `Invariants.erase_compileUnit` | `Lara/Invariants.lean` |
| Structured compilation of an accepted unit | `Invariants.compileUnit`, `Invariants.compileUnit_size` | `Lara/Invariants.lean` |
| The invariant record | `Invariants.CompilerInvariant` (fields `ranged`, `conflictComplete`) | `Lara/Invariants.lean` |
| M0 necessity (M1's only-if direction, carrier level) | `Invariants.compileUnit_invariant`, from `Invariants.compileUnit_ranged` and `Invariants.compileUnit_conflictComplete` | `Lara/Invariants.lean` |
| Self-attack as the conflict-completeness diagonal | `Invariants.compileUnit_selfConflict` | `Lara/Invariants.lean` |
| Observational adequacy of the carrier | `Invariants.support_compileUnit` (claim support), `Invariants.status_compileUnit` (four-state status) | `Lara/Invariants.lean` |
| Rejecting counterexample: endpoint-safe pruning | `Examples.CompilerInvariants.unrangedEx`, `unrangedEx_not_invariant`, `unrangedEx_not_realizable` | `Lara/Examples/CompilerInvariants.lean` |
| Rejecting counterexample: conflict completeness and self-attack | `Examples.CompilerInvariants.unforcedConflictEx`, `unforcedConflictEx_not_invariant`, `unforcedConflictEx_not_realizable`, `selfContrary`, `unforcedSelfConflict_not_invariant` | `Lara/Examples/CompilerInvariants.lean` |
| Conflict completeness off the diagonal (distinct conclusions) | `Examples.CompilerInvariants.sharedContrary`, `unforcedDistinctConflict_not_invariant` | `Lara/Examples/CompilerInvariants.lean` |
| Rejecting counterexample: subargument closure (source-level) | `Examples.CompilerInvariants.closure_rejects_noncontaining_target` | `Lara/Examples/CompilerInvariants.lean` |
| Positive anchor (a real accepted unit in the carrier) | `Examples.CompilerInvariants.selfEdgeUnit_nodes`, `selfEdgeUnit_selfEdge` | `Lara/Examples/CompilerInvariants.lean` |

M0 recorded two downstream obligations. B0 (#182), not M1, owns the
strict-chain rejecting example. M1 closes conclusion sortedness at the
executable realization boundary:
`Realizability.Realization.node_conclusion_wellSorted` requires successful
checking and used-leaf ground coverage. It does not assert sorted conclusions
for every standalone `CheckedUnit`. See
`docs/theory-m1-compilation-image.md` for the resulting theorem boundary.

---

## 6. M1 compilation-image boundary (theory spine)

Issue #184, tracker #180. M1 fixes `canon`, `sigma`, `policy`, and `reg`, then
defines executable realizability up to exact structured-framework isomorphism.
Necessity holds in every fixed context. The empty-defeat counterexample refutes
a converse quantified over all fixed contexts; it does not prove
non-sufficiency for every policy. Every theorem row below is gated by
`lean/AxCheck.lean` (sorry-free, standard trio).

| Paper object | Lean declaration | File |
|---|---|---|
| Equality up to node renaming | `Realizability.StructuredAFIso` | `Lara/Realizability.lean` |
| Isomorphism equivalence proofs | `Realizability.StructuredAFIso.refl`, `Realizability.StructuredAFIso.symm`, `Realizability.StructuredAFIso.trans` | `Lara/Realizability.lean` |
| Executable witness and realizability proposition | `Realizability.Realization`, `Realizability.Realizable` | `Lara/Realizability.lean` |
| Invariant transport across isomorphism | `Realizability.compilerInvariant_iso` | `Lara/Realizability.lean` |
| **Only-if direction: realizability implies the frozen invariant** | `Realizability.realizable_invariant` | `Lara/Realizability.lean` |
| Conclusion sortedness under successful checking and used-leaf ground coverage | `Realizability.Realization.node_conclusion_wellSorted` | `Lara/Realizability.lean` |
| Nonempty checker, coverage, and non-identity isomorphism witness | `Examples.Realizability.nonempty_swapped_realizable` | `Lara/Examples/Realizability.lean` |
| Sortedness instantiated on a retained nonempty-fixture node | `Examples.Realizability.nonempty_swapped_node_wellSorted` | `Lara/Examples/Realizability.lean` |
| Accepted empty-policy positive anchor | `Examples.Realizability.emptyUnitCheck_ok` | `Lara/Examples/Realizability.lean` |
| Empty-policy edge impossibility used by the counterexample | `Examples.Realizability.noAttack_of_emptyDefeat`, `Examples.Realizability.compiled_no_edges_of_emptyDefeat` | `Lara/Examples/Realizability.lean` |
| Invariant-satisfying self-edge | `Examples.Realizability.oneSelfEdge_invariant` | `Lara/Examples/Realizability.lean` |
| Empty-defeat non-realizability of that self-edge | `Examples.Realizability.oneSelfEdge_not_realizable` | `Lara/Examples/Realizability.lean` |

The paper may claim necessity and the failure of the universal converse. For
the latter, it must state the hypothesis
`policy.defeat = Examples.Realizability.emptyDefeat` from
`oneSelfEdge_not_realizable` and cite `emptyUnitCheck_ok` to show that the
fixed context accepts an executable unit.

The paper must not print the original unconditional iff, name a constructive
`realize` theorem, or say that every invariant-satisfying framework has a
checked source program. No such declaration exists. M1 also omits an erased-AF
theorem because the surviving range condition is not a Lara-specific image
characterization.

---

## 7. M2a semantics-parametric claim observation (theory spine)

Issue #185, tracker #180. M2a makes the semantics parameter of the development
an object: `ExtensionSemantics` bundles a declarative specification, a
proof-oriented enumerator, and adequacy, and the grounded results become the
`groundedSem` instance. The landing is additive — `Lara/Compile.lean` was not
modified, and no result here lifts a `grounded`-indexed theorem to an arbitrary
semantics. Every theorem row below is gated by `lean/AxCheck.lean` (sorry-free,
standard trio); 157 declarations across the four modules are covered (67 in
`Lara/Semantics.lean`, 7 in `Lara/Semantics/Sublists.lean`, 43 in
`Lara/Observation.lean`, 40 in `Lara/Examples/Semantics.lean`). See
`docs/theory-m2a-observation.md` for the boundary and for six corrections the
mechanization forced on the plan.

| Paper object | Lean declaration | File |
|---|---|---|
| The semantics interface (fields `spec`, `enumerate`, `sound`) | `Semantics.ExtensionSemantics` | `Lara/Semantics.lean` |
| The five instances | `Semantics.groundedSem`, `completeSem`, `preferredSem`, `stableSem`, `semiStableSem` | `Lara/Semantics.lean` |
| The carrier-bounded extension predicates | `Semantics.Bounded`, `Admissible`, `Complete`, `Stable`, `LeastComplete`, `Preferred`, `SemiStable`, each with its `..B` decider and `..B_iff` | `Lara/Semantics.lean` |
| Dung's fundamental lemma, and preferred ⇒ complete as a theorem | `Semantics.admissible_cons`, `Semantics.preferred_complete` | `Lara/Semantics.lean` |
| Sublist representation (hand-rolled: core Lean v4.32.0 has no `List.sublists`, and the project carries no Mathlib dependency today — `lean/lakefile.toml` records it as planned for result 5) | `Semantics.subseqs`, `mem_subseqs`, `sublist_ext`, `subseqs_ext`, `subseqs_nodup` | `Lara/Semantics/Sublists.lean` |
| Representative uniqueness from `sound` alone, for any instance | `Semantics.enumerate_ext`, from `Semantics.candidates_ext` and `candidates_nodup` | `Lara/Semantics.lean` |
| **Adequacy needs no `Nodup`** (the refutation of the plan's D4 rationale) | `Examples.Semantics.sound_holds_without_nodup` | `Lara/Examples/Semantics.lean` |
| **Representative uniqueness genuinely fails without `Nodup`** | `Examples.Semantics.not_candidates_ext_without_nodup`, `not_enumerate_ext_without_nodup`, `dupCarrier`, `dupCarrier_candidates`, `dupCarrier_enumerate` | `Lara/Examples/Semantics.lean` |
| Grounded is the singleton instance | `Semantics.groundedSem_enumerate`, `mem_canonize_grounded`, `groundedSem_singleton` | `Lara/Semantics.lean` |
| The argument-level acceptance record | `Semantics.AcceptanceProfile` (fields `inAll`, `inSome`, `outAll`, `outSome`), `Semantics.profile` | `Lara/Semantics.lean` |
| Skeptical/credulous collapse under grounded | `Semantics.profile_grounded` | `Lara/Semantics.lean` |
| The claim-level observation type and its aggregation | `Semantics.ClaimObservation` (constructors `noExtension`, `observed`), `Semantics.observe`, `claimAcceptedB`, `claimDefeatedB` | `Lara/Semantics.lean` |
| The two "attacked by" notions, kept apart | `Semantics.attackedByB`, `Semantics.mem_attacked_iff` | `Lara/Semantics.lean` |
| **The four-state status the paper prints is the grounded instance** | `Semantics.observe_grounded` | `Lara/Semantics.lean` |
| **`gap` is semantics-independent** (arbitrary `sem`, no hypothesis but `c.support = []`) | `Semantics.observe_gap`, converse `Semantics.observe_gap_iff` | `Lara/Semantics.lean` |
| `gap` exercised at all five instances, including where the guards compete | `Examples.Semantics.observe_claimNoSupport_uniform` | `Lara/Examples/Semantics.lean` |
| The two vacuity hazards, mechanized rather than described | `Semantics.claimDefeatedB_of_nil`, `claimAcceptedB_of_nil` (support), `Semantics.no_verdict_on_empty` (enumeration) | `Lara/Semantics.lean` |
| Emptiness report recovered; verdict backed by an extension | `Semantics.observe_noExtension_iff`, `Semantics.enumerate_ne_nil_of_observed_ne_gap` | `Lara/Semantics.lean` |
| Exclusivity of `justified` and `defeated`, and its hypothesis | `Semantics.justified_defeated_exclusive`, `Semantics.observe_justified_not_all_defeated`, `Semantics.SpecConflictFree` | `Lara/Semantics.lean` |
| The five `SpecConflictFree` discharges | `Semantics.groundedSem_specConflictFree`, `completeSem_specConflictFree`, `preferredSem_specConflictFree`, `stableSem_specConflictFree`, `semiStableSem_specConflictFree` | `Lara/Semantics.lean` |
| Carrier-locality of a specification | `Observation.AttackExtensional`, `Observation.attackExtensional_of_imp`, and its seven instances `attackExtensional_bounded`, `attackExtensional_admissible`, `attackExtensional_complete`, `attackExtensional_leastComplete`, `attackExtensional_preferred`, `attackExtensional_stable`, `attackExtensional_semiStable` | `Lara/Observation.lean` |
| **`AttackExtensional ConflictFree` is false** | `Observation.not_attackExtensional_conflictFree`; positive contrast `Observation.admissible_transports_on_junk`; correct decomposition `Observation.conflictFree_congr_af` | `Lara/Observation.lean` |
| Observation transport, and the support bound it needs | `Observation.observe_congr`; necessity by `Observation.not_observe_congr_of_unbounded_support`, `observe_congr_needs_support_bound` | `Lara/Observation.lean` |
| The transport hypothesis on the oracle | `Observation.AgreesOnArgs`, `agreesOnArgs_of_faithful`, `agreesOnArgs_edgeB` | `Lara/Observation.lean` |
| **Why the hypothesis is not `Faithful`** | `Observation.faithful_unique` (any two are equal); `Examples.Semantics.agreesOnArgs_strictly_weaker_than_faithful`, from `eJunk_agreesOnArgs` and `not_faithful_eJunk` | `Lara/Observation.lean`, `Lara/Examples/Semantics.lean` |
| Source-level observation and its preservation theorem | `Observation.SrcObservation`, `Observation.srcObservation_iff_checked`, `srcObservation_checked`, `srcObservation_unique` | `Lara/Observation.lean` |
| **The honest bridge to result 6** (an equivalence, not an instantiation) | `Observation.srcStatus_iff_srcObservation` | `Lara/Observation.lean` |
| Stable nonexistence, and `noExtension` actually reached | `Examples.Semantics.stableSem_enumerate_threeCycle`, `observe_stableSem_threeCycle`, `observe_stableSem_threeCycle_ne_justified`, `observe_stableSem_threeCycle_ne_defeated`, `threeCycle_enumerate_nonStable` | `Lara/Examples/Semantics.lean` |
| Nonexistence is the bare cycle's, not an odd cycle's | `Examples.Semantics.stableSem_enumerate_threeCycleAttacked` | `Lara/Examples/Semantics.lean` |
| All ten pairwise separations, count checked by the elaborator | `Examples.Semantics.five_semantics_pairwise_distinct` | `Lara/Examples/Semantics.lean` |
| Reinstatement exercised by a two-element extension in all five semantics | `Examples.Semantics.reinstatementChain` | `Lara/Examples/Semantics.lean` |
| **No four-state function realizes both credulous readings** | `Examples.Semantics.credulous_not_functional`, `profile_preferredSem_twoCycle_symm`, `profile_preferredSem_twoCycle`, `profile_groundedSem_twoCycle` | `Lara/Examples/Semantics.lean` |
| **`observe` does not factor through `profile`** | `Examples.Semantics.observe_not_determined_by_profile` | `Lara/Examples/Semantics.lean` |
| The three non-`gap` statuses vary with the semantics | `Examples.Semantics.observe_twoCycle_grounded_ne_preferred`, `observe_twoCycleSink_grounded_ne_preferred` | `Lara/Examples/Semantics.lean` |
| Structural contrasts among the four non-grounded instances | `Examples.Semantics.preferred_exists_where_stable_does_not`, `semiStable_exists_where_stable_does_not`, `semiStable_proper_refinement_of_preferred` | `Lara/Examples/Semantics.lean` |
| `defeated` unreachable on the two-cycle, for an arbitrary supported claim | `Examples.Semantics.twoCycle_defeated_unreachable`, from `twoCycle_extensions`, `twoCycle_defeat_split`, `observe_ne_defeated_of_mem_enumerate`, `claimDefeatedB_nil_eq_false` | `Lara/Examples/Semantics.lean` |
| The observation table (the paper figure), generated not transcribed | `Examples.Semantics.observationTable`, `tableRow`, and the closed vocabularies `SemanticsName` / `FrameworkName` / `ClaimName` with `semanticsInstance` / `frameworkAF` / `claimOf` | `Lara/Examples/Semantics.lean` |
| No table row can be silently dropped | `Examples.Semantics.allSemantics_complete`, `allFrameworks_complete`, `allClaims_complete` | `Lara/Examples/Semantics.lean` |

The paper may claim that the observation interface is parametric and that the
four-state status it already prints is the `groundedSem` instance of it
(`observe_grounded`); that `gap` is the one semantics-independent status
(`observe_gap`, `observe_gap_iff`); that stable extensions can fail to exist and
that `observe` then reports `noExtension` rather than fabricating a `Status`;
and that all ten pairwise separations among the five semantics are witnessed
(`five_semantics_pairwise_distinct`). Where the table is displayed, the `|E|`
column must be displayed with it: `groundedSem` and `completeSem` occupy 48 of
the 120 rows, and on all 24 (framework, claim) inputs their observations are
identical. They separate only by extension count, which differs on 12 of the 24.

**`thm:preservation` does not change.** It continues to cite
`Lara.Compile.srcStatus_iff_checked` (§1 above), unmodified and with no support
side condition attached. `Observation.srcObservation_iff_checked` is **not** a
generalization of it: the observation form requires
`∀ i ∈ c.support, i < P.args.length`, so it asks for more, and the two subjects
differ — `Compile.SrcStatus` is an inductive relation over `SrcIn`/`SrcOut`,
while `SrcObservation` quantifies over every `Edge`-deciding oracle satisfying
`AgreesOnArgs`. Neither is a substitution instance of the other. If the paper
wants the connection displayed, the declaration to cite is
`Observation.srcStatus_iff_srcObservation`, with its support hypothesis stated.

The paper must not print the credulous reading as a four-state verdict.
`credulous_not_functional` refutes every function that would make
`justified ↔ inSome` and `defeated ↔ outSome` under preferred semantics;
`profile_preferredSem_twoCycle_symm` shows that a framework-internal tie-break
cannot distinguish the two arguments. The paper must also not say that `observe`
is determined by
per-argument acceptance data (`observe_not_determined_by_profile`), assert the
general non-emptiness of preferred extensions (stated in `preferredSem`'s
docstring, never proved), state a transport hypothesising `Compile.Faithful` on
both sides (`faithful_unique` makes it contentless), or claim
`AttackExtensional ConflictFree` (`not_attackExtensional_conflictFree`). It must
also not claim that the table's completeness theorems rule out a missing
semantics: they catch a dropped constructor, and nothing enumerates the
instances of a structure, so a sixth `ExtensionSemantics` declared elsewhere
would be invisible.

The Haskell mirror (`src/Lara/Semantics.hs`, `test/SemanticsSpec.hs`) is
conformance evidence, not soundness. The goldens agreeing is evidence about
outputs on six frameworks under five semantics; it is not a proof that the two
sets of definitions correspond, and the paper must not describe it as one.
`make semantics-goldens` prevents the checked-in Haskell transcript from
drifting from the Lean emitter.
