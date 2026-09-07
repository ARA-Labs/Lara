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
then digest-resolved theory *data*). The table below works the laws through two
registered instances — ND (`Strict.ndBackend`, `Strict.lean:759`) and RA
(`RA.raBackend`, `RA.lean:450`) — chosen as the two extremes: ND's recursive
de Bruijn proof terms with a non-identity encoding, and RA's flat
slots-plus-witness certificate over the identity encoding.

Two further registered instances discharge the same four laws and are omitted
from the table only because they add no new *shape* of discharge, not because
they are exempt: `ord@1` (`Ord.ordBackend`, `Ord.lean`; `ordReplay_iff`,
`ordSound`, `ordUses_covers`/`_valid`/`_account`) and `insp@1`
(`Insp.inspBackend`, `Insp.lean:595`; `inspReplay_iff` :344, `inspSound` :403,
`inspUses_covers` :421, `inspUses_valid` :438, `inspUses_account` :461). Both
follow RA's column pattern — identity encoding, so B2 is `equiv_iff_nf_eq`;
decode-then-decide replay, so B1 is a case split; and slot-naming
certificates, so B4 falls out of the lookups `checkB` performs. `insp@1`'s
consequence relation `inspModels` (:321) is the one that is not arithmetic:
it is membership and non-membership in a *declared exhaustive enumeration*, so
the paper should introduce it as the closed-world instance of `models_beta`
rather than as a third numeric checker.

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
standard trio); 157 declarations across the four modules were covered at the
M2a landing (67 in `Lara/Semantics.lean`, 7 in `Lara/Semantics/Sublists.lean`,
43 in `Lara/Observation.lean`, 40 in `Lara/Examples/Semantics.lean`), plus the
five added on 2026-09-06 by issue #196 (four in `Lara/Semantics.lean`, one in
`Lara/Semantics/Sublists.lean`). See
`docs/theory-m2a-observation.md` for the boundary and for six corrections the
mechanization forced on the plan.

| Paper object | Lean declaration | File |
|---|---|---|
| The semantics interface (fields `spec`, `enumerate`, `sound`) | `Semantics.ExtensionSemantics` | `Lara/Semantics.lean` |
| The five instances | `Semantics.groundedSem`, `completeSem`, `preferredSem`, `stableSem`, `semiStableSem` | `Lara/Semantics.lean` |
| The carrier-bounded extension predicates | `Semantics.Bounded`, `Admissible`, `Complete`, `Stable`, `LeastComplete`, `Preferred`, `SemiStable`, each with its `..B` decider and `..B_iff` | `Lara/Semantics.lean` |
| Dung's fundamental lemma, and preferred ⇒ complete as a theorem | `Semantics.admissible_cons`, `Semantics.preferred_complete` | `Lara/Semantics.lean` |
| **Dung's existence result: every framework has a preferred extension** (no `Nodup`, no Mathlib; added 2026-09-06 by issue #196) | `Semantics.preferred_exists`, scan-level form `Semantics.preferred_exists_candidate`, consumer form `Semantics.preferredSem_enumerate_ne_nil`; seed `Semantics.admissible_nil`, finiteness principle `Semantics.exists_max_length` | `Lara/Semantics.lean`, `Lara/Semantics/Sublists.lean` |
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
general non-emptiness of *stable* extensions or read `preferred_exists` as
licensing one (`stableSem_enumerate_threeCycle` refutes it), state a transport
hypothesising `Compile.Faithful` on
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

---

## 8. M3 source updates and status dynamics (theory spine)

M3 is a first-fragment, one-step source-transition calculus. Its four core
matrices instantiate `CoreTransition` with `Semantics.groundedSem`. In matrix
labels, paper `refuted` means Lean `Grounded.Status.defeated`, and paper `both`
means Lean `Grounded.Status.contested`. The five-valued public target adds
`PublicReport.evidenceBlocked`. Public equality with core for additive updates is
proved under `CleanBase` on the exact source `AcceptedRun`; the result is not
unconditional. See `docs/theory-m3-source-updates.md` for the frozen claim
boundary and emitted tables.

### Source, Acceptance, and Update Surface

All declarations in this table are in `lean/Lara/Update.lean`.

| Paper object | Lean declaration |
|---|---|
| Raw source carrier; existential and proof-relevant acceptance | `Update.SourceState`, `Update.Accepted`, `Update.AcceptedRun`, `Update.AcceptedRun.accepted` |
| Closed update and rejection vocabularies | `Update.SourceUpdate`, `Update.UpdateRejection` |
| `addLeaf` freshness over leaf rows, metadata, and group members | `Update.AddLeafFresh`, `Update.addLeafFreshB`, `Update.addLeafFreshB_iff` |
| Admit-at-key condition, including default admit | `Update.AdmittedAt`, `Update.admittedAtB`, `Update.admittedAtB_iff` |
| Raw attack endpoint declaration | `Update.EndpointDeclared`, `Update.endpointDeclaredB`, `Update.endpointDeclaredB_iff` |
| Raw argument name-and-term freshness | `Update.InstanceFresh`, `Update.instanceFreshB`, `Update.instanceFreshB_iff` |
| Executable edit followed by admission and whole-unit rechecking | `Update.applyUpdate` |
| Constructor-side rejection mapping | `Update.applyUpdate_addLeaf_notFresh`, `Update.applyUpdate_tighten_notAdmitted`, `Update.applyUpdate_addAttack_endpointNotDeclared`, `Update.applyUpdate_addInstance_notFresh` |
| Sufficient-condition preservation | `Update.applyUpdate_addLeaf_ok`, `Update.applyUpdate_tighten_ok`, `Update.applyUpdate_addAttack_ok`, `Update.applyUpdate_addInstance_ok` |

The preservation theorem directions are `Accepted source` plus each theorem's
constructor-local hypotheses to existence of `target` with
`applyUpdate ... = .ok target ∧ Accepted target`. They do not state converses or
unconditional constructor success. In particular, `applyUpdate_addInstance_ok`
requires well-sortedness, complete support, and attack completeness after
extending the retained argument list.

### Support Lemmas Promoted for M3

| Role | Lean declaration | File |
|---|---|---|
| Accepted admission conditions and retained structure | `Admission.firstDuplicateLeafId_none_iff_nodup`, `Admission.evaluateAdmission_accepted_conditions`, `Admission.retained_semantic_attack_endpoints`, `Admission.retained_identity_of_length_eq` | `Lara/Admission.lean` |
| Raw attack selection, append, lookup, and resolution transport | `RawAttack.mem_of_mem_selectAligned`, `RawAttack.resolveAttacks_append`, `RawAttack.resolveAttacks_attack_lookup`, `RawAttack.resolveAttacks_mono_lookup`, `RawAttack.lookupArg_append_of_some`, `RawAttack.lookupArg_some_row`, `RawAttack.selectAligned_append_of_length_eq`, `RawAttack.resolveAttacks_length`, `RawAttack.selectAligned_congr_on` | `Lara/RawAttack.lean` |
| Checked/declared carrier identity | `Admission.liftSupport_range_eq_of_mem`, `Admission.checkedAF_eq_declaredAF` | `Lara/Admission.lean` |
| Embedding reflection and unblocked-label transport | `BlockedProgram.directIn_reflect_embedding`, `BlockedProgram.directOut_reflect_embedding`, `BlockedProgram.labelC_eq_of_embedding`, `BlockedProgram.production_unblocked_label_agree` | `Lara/BlockedProgram.lean` |
| Direct-in and direct-out transport for old nodes across a fresh sink | `Grounded.SinkExtension.directIn_forward`, `Grounded.SinkExtension.directOut_forward`, `Grounded.SinkExtension.directIn_backward`, `Grounded.SinkExtension.directOut_backward` | `Lara/Grounded.lean` |
| Status facts and old-node status behavior under a fresh sink | `Grounded.statusC_defeated_all_out`, `Grounded.SinkExtension`, `Grounded.SinkExtension.label_old`, `Grounded.statusC_contested_has_undec`, `Grounded.statusC_ne_defeated_of_undec`, `Grounded.SinkExtension.justified_preserved`, `Grounded.SinkExtension.contested_not_defeated` | `Lara/Grounded.lean` |
| Holes independence for arbitrary extension semantics | `Semantics.observe_holes_independent` | `Lara/Semantics.lean` |

### Core and Public Transition API

All declarations in this table are in `lean/Lara/Update.lean`.

| Paper object | Lean declaration and direction |
|---|---|
| Semantics-indexed observation and belief projection | `Update.coreObs`, `Update.beliefSet`, `Update.CoreTransition` |
| Public report vocabulary and spellings | `Update.PublicReport`, `Update.PublicReport.ofStatus`, `Update.PublicReport.ofStatus_injective`, `Update.PublicReport.render`, `Update.PublicReport.publicationLabel` |
| Exact production blocked-query path | `Update.blockedQueriesForRun`, `Update.blockedSeedForRun`, `Update.blockedSetForRun`, `Update.publicReport`, `Update.publicReport_gap_of_empty_support`, `Update.PublicTransition` |
| Clean source boundary | `Update.CleanBase`, `Update.AcceptedRun.prune_eq` |
| Clean source collapses public to core | `Update.blockedQueriesForRun_eq_nil_of_clean`, `Update.publicReport_eq_core_of_clean`, `Update.keptArgs_eq_raw_of_clean`, `Update.retainedIndices_eq_range_of_clean`, `Update.keptAttacks_eq_resolved_of_clean`, `Update.checkedArgs_eq_raw_of_clean`, `Update.checkedAF_eq_declaredAF_of_clean`, `Update.blockedSeedForRun_eq_nil_of_clean`, `Update.blockedSetForRun_eq_nil_of_clean` |
| Empty-closure and no-prune bridge lemmas | `Update.blockedSet_eq_nil_of_seed_nil`, `Update.blockedQueriesForRun_eq_nil_of_empty_closure`, `Update.publicReport_eq_core_of_empty_closure`, `Update.checkedAF_eq_declaredAF_of_no_arg_prune` |
| Additive update classification and public/core equality | `Update.AdditiveUpdate`, `Update.additive_clean_target`, `Update.additive_target_blockedSeed_eq_nil`, `Update.additive_target_blockedSet_eq_nil`, `Update.additive_public_eq_core`, `Update.additive_public_ne_evidenceBlocked` |
| Non-instance classification used by public tightening | `Update.NonInstanceUpdate`, `Update.tighten_lifted_support_subset` |
| Core unreachable-cell theorems | `Update.addAttack_gap_fixed`, `Update.additive_no_gap_entry`, `Update.addLeaf_core_fixed`, `Update.nonInstance_gap_fixed`, `Update.addInstance_sink_status_monotone` |
| Public tighten unreachable-cell theorems | `Update.tighten_public_defeated_not_contested`, `Update.tighten_public_justified_source_justified`, `Update.tighten_public_gap_fixed` |
| Source checked-to-declared legacy bridge | `Update.tighten_public_row_justified_nonpromotion`: a justified checked complete claim on one exact clean run implies that run's lifted claim is justified in its declared framework |
| Matrix-to-legacy quarantine safety | `Update.quarantine_nonpromotion_corollary`: exact source and target `AcceptedRun`s plus `applyUpdate reg source (.tighten key) = .ok target`, the `.tighten` `Update.NonInstanceUpdate` hypotheses, `Update.CleanBase sourceRun`, and `publicReport targetRun p = .justified` imply that the source lifted claim is justified in the source declared framework |

`tighten_public_justified_source_justified` runs from a justified target public
report back to a justified source core status under the exact clean-base,
successful-update, and `.tighten` `NonInstanceUpdate` hypotheses.
`quarantine_nonpromotion_corollary` applies that transition theorem, then the
clean source's checked-framework and lifted-claim identities, to recover the
legacy declared-framework conclusion. Its proof does not call
`Admission.source_justified_nonpromotion`. This is a backward safety result; it
does not say that tightening preserves every justified claim forward.

### Reachable Witness Theorems

The following declarations are in `lean/Lara/Examples/Update.lean`.
`Examples.Update.AcceptedRun` abbreviates the fixed fixture registry.
`SuccessfulCoreCell` and `SuccessfulPublicCell` package exact accepted runs and
successful `applyUpdate` equalities; `SuccessfulCoreCell.transition` exposes
those witnesses.

| Matrix family | Exact reachable declarations |
|---|---|
| `addLeaf` core, 4 | `addLeaf_justified_to_justified`, `addLeaf_refuted_to_refuted`, `addLeaf_both_to_both`, `addLeaf_gap_to_gap` |
| `tighten` core, 13 | `tighten_justified_to_justified`, `tighten_justified_to_refuted`, `tighten_justified_to_both`, `tighten_justified_to_gap`, `tighten_refuted_to_justified`, `tighten_refuted_to_refuted`, `tighten_refuted_to_both`, `tighten_refuted_to_gap`, `tighten_both_to_justified`, `tighten_both_to_refuted`, `tighten_both_to_both`, `tighten_both_to_gap`, `tighten_gap_to_gap` |
| `addAttack` core, 10 | `addAttack_justified_to_justified`, `addAttack_justified_to_refuted`, `addAttack_justified_to_both`, `addAttack_refuted_to_justified`, `addAttack_refuted_to_refuted`, `addAttack_refuted_to_both`, `addAttack_both_to_justified`, `addAttack_both_to_refuted`, `addAttack_both_to_both`, `addAttack_gap_to_gap` |
| `addInstance` core, 10 | `addInstance_justified_to_justified`, `addInstance_refuted_to_justified`, `addInstance_refuted_to_refuted`, `addInstance_refuted_to_both`, `addInstance_both_to_justified`, `addInstance_both_to_both`, `addInstance_gap_to_justified`, `addInstance_gap_to_refuted`, `addInstance_gap_to_both`, `addInstance_gap_to_gap` |
| `tighten` public under `CleanBase`, 13 | `tighten_public_justified_to_justified`, `tighten_public_justified_to_defeated`, `tighten_public_justified_to_contested`, `tighten_public_justified_to_gap`, `tighten_public_justified_to_evidenceBlocked`, `tighten_public_defeated_to_defeated`, `tighten_public_defeated_to_gap`, `tighten_public_defeated_to_evidenceBlocked`, `tighten_public_contested_to_defeated`, `tighten_public_contested_to_contested`, `tighten_public_contested_to_gap`, `tighten_public_contested_to_evidenceBlocked`, `tighten_public_gap_to_gap` |

`Examples.Update.addInstance_uncovered_rejected` is the negative acceptance
anchor for the extended attack-completeness premise.
`Examples.Update.addAttack_blocked_growth` is the non-clean public-growth
witness that refutes unconditional additive/core equality.

### Typed Matrix and Evidence Inventory

All declarations below are in `lean/Lara/Examples/Update.lean`.

| Paper or supplement object | Lean declarations |
|---|---|
| Core axes and canonical product | `UpdateKind`, `PublicationStatus`, `PublicationStatus.grounded`, `publicationStatuses`, `MatrixCoordinate`, `canonicalCoordinates`, `canonicalCoordinates_nodup`, `canonicalCoordinates_length`, `UpdateOfKind` |
| Reachable and unreachable semantics | `ReachableClaim`, `ReachableTag`, `ReachableTag.sound`, `UnreachableTag`, `MatrixRun`, `InstanceSinkPremises`, `UnreachablePremises`, `UnreachableClaim`, `UnreachableTag.sound` |
| Total core cell evidence | `CellEvidence`, `CellEvidence.Claim`, `CellEvidence.sound`, `evidenceFor`, `MatrixCellEntry` |
| Four complete core matrices | `addLeafMatrix`, `tightenMatrix`, `addAttackMatrix`, `addInstanceMatrix` |
| Core coordinate completeness | `addLeaf_coordinates`, `tighten_coordinates`, `addAttack_coordinates`, `addInstance_coordinates` |
| Core counts | `addLeaf_reachable_count`, `tighten_reachable_count`, `addAttack_reachable_count`, `addInstance_reachable_count`, `grounded_matrix_cell_count`, `grounded_reachable_count` |
| Core report | `groundedCoreMatrixReport` |
| Public axis and canonical 4 by 5 product | `publicReports`, `PublicMatrixCoordinate`, `canonicalPublicCoordinates`, `canonicalPublicCoordinates_nodup`, `canonicalPublicCoordinates_length`, `canonicalPublicCoordinates_order` |
| Public tighten runs and indexed evidence | `TightenPublicRun`, `TightenPublicReachableTag`, `TightenPublicReachableClaim`, `TightenPublicReachableTag.sound`, `TightenPublicUnreachableTag`, `TightenPublicUnreachableClaim`, `TightenPublicUnreachableTag.sound`, `TightenPublicCellEvidence`, `TightenPublicCellEvidence.Claim`, `TightenPublicCellEvidence.sound`, `tightenPublicEvidenceFor`, `TightenPublicCellEntry`, `tightenPublicMatrix`, `tightenPublicMatrix_coordinates` |
| Public tighten counts | `tighten_public_reachable_count`, `tighten_public_blocked_reachable_count` |
| Additive public bridge | `AdditiveKind`, `AdditiveKind.updateKind`, `AdditiveKind.label`, `AdditivePublicRun`, `AdditivePublicRun.toCore`, `AdditivePublicRun.publicTransition`, `AdditivePublicReachableClaim`, `ReachableTag.additivePublicSound` |
| Additive blocked-column impossibility | `AdditiveBlockedRun`, `AdditiveBlockedRun.emptyClosure`, `AdditiveBlockedRun.false` |
| Total additive public evidence | `AdditivePublicCellEvidence`, `AdditivePublicCellEvidence.Claim`, `AdditivePublicCellEvidence.sound`, `additivePublicEvidenceFor`, `AdditivePublicCellEntry` |
| Three complete additive public matrices | `addLeafPublicMatrix`, `addAttackPublicMatrix`, `addInstancePublicMatrix` |
| Additive public coordinate and length checks | `addLeafPublicMatrix_coordinates`, `addAttackPublicMatrix_coordinates`, `addInstancePublicMatrix_coordinates`, `addLeafPublicMatrix_length`, `addAttackPublicMatrix_length`, `addInstancePublicMatrix_length` |
| Additive public counts | `addLeaf_public_reachable_count`, `addAttack_public_reachable_count`, `addInstance_public_reachable_count`, `addLeaf_public_blocked_reachable_count`, `addAttack_public_blocked_reachable_count`, `addInstance_public_blocked_reachable_count` |
| Public report and executable golden entry | `fiveValuedPublicMatrixReport`; `main` in `lean/UpdateMatrices.lean` prints it after `groundedCoreMatrixReport` |

The count theorem for `addInstance` is
`Examples.Update.addInstance_reachable_count = 10`, not 13. The three additional
unreachable cells use `Update.addInstance_sink_status_monotone`; this is a
mechanized consequence of old-node sink monotonicity, not a missing witness.

### Holes and AGM Names

| Paper object | Lean declaration | File |
|---|---|---|
| Complete-support projection with definitionally empty holes | `Consistency.claimSupportFor`, `Consistency.completeClaimFor` | `Lara/Consistency.lean` |
| Observation does not depend on holes | `Semantics.observe_holes_independent` | `Lara/Semantics.lean` |
| Separate holes diagnostic | `Grounded.incompleteAlternative` | `Lara/Grounded.lean` |
| Grounded belief-set projection | `Update.beliefSet` | `Lara/Update.lean` |
| Failed AGM success and inclusion probes | `Examples.Update.agm_success_fails`, `Examples.Update.agm_inclusion_fails` | `Lara/Examples/Update.lean` |

Only success and additive inclusion were probed, and both fail. This name map
does not license a full AGM-compliance claim. Holes remain a separate diagnostic
and do not create a sixth `PublicReport`.

---

## Heterogeneous backend compositionality (B0, issue #182)

Frozen definitions and the claim boundary are recorded in
`docs/theory-b0-backend-compositionality.md`. The paper plan's
`LocalBackendConsequence` is this development's `OccurrenceConsequence`; the
paper plan's `CertOccurrence` field list is to be revised to the
derived-fields phrasing the mechanization uses (EYH0602/lara-paper#2).

### Vocabulary

| Paper object | Lean declaration | File |
|---|---|---|
| Certified occurrence record | `BackendComposition.CertOccurrence`, `.node`, `BackendComposition.OccursIn` | `Lara/BackendComposition.lean` |
| Backend identities a term names | `BackendComposition.usedBackends`, `usedBackendsList`, `usedBackendsDis` | `Lara/BackendComposition.lean` |
| Occurrence-local backend consequence (`LocalBackendConsequence`) | `BackendComposition.OccurrenceConsequence` | `Lara/BackendComposition.lean` |
| Named identities are exactly the occurrences' | `BackendComposition.mem_usedBackends_iff` | `Lara/BackendComposition.lean` |
| Collection helpers | `BackendComposition.usedBackends_mem_list`, `usedBackends_mem_dis`, `certStep_usedBackends_subset`, `usedBackends_node`, `mem_usedBackends_occ`, `mem_usedBackendsListOcc`, `mem_usedBackendsDisOcc` | `Lara/BackendComposition.lean` |

### The firewall

| Paper object | Lean declaration | File |
|---|---|---|
| Backend firewall, premise half | `BackendComposition.prem_subterm_swap` | `Lara/BackendComposition.lean` |
| Backend firewall, discharge half | `BackendComposition.dis_subterm_swap` | `Lara/BackendComposition.lean` |
| Discharge keys survive the swap | `BackendComposition.map_fst_set_of_getElem?` | `Lara/BackendComposition.lean` |

Neither statement mentions a backend; that is the content. See the frozen
record for why naming the backends is a corollary rather than the theorem.

### Accounting

| Paper object | Lean declaration | File |
|---|---|---|
| Dependencies are the union of occurrence-local reports | `BackendComposition.certDeps_eq_union` | `Lara/BackendComposition.lean` |
| Report shape inversion | `BackendComposition.stepDeps_cert_shape` | `Lara/BackendComposition.lean` |
| **B0 headline** — occurrence-level compositionality | `BackendComposition.hetero_occurrences_accounted` | `Lara/BackendComposition.lean` |
| Every named backend discharges an occurrence | `BackendComposition.usedBackends_accounted` | `Lara/BackendComposition.lean` |

### The worked witness

| Paper object | Lean declaration | File |
|---|---|---|
| Fixture child core and its obligation-4 laws | `Examples.BackendComposition.fixReplay_iff`, `fixSound`, `fixUses_covers`, `fixUses_valid`, `fixUses_account` | `Lara/Examples/BackendComposition.lean` |
| Mixed registry agreeing with `registryEx` | `Examples.BackendComposition.registryMix_nd`, `registryMix_ord`, `registryMix_fix`, `certOkOf_registry_congr` | `Lara/Examples/BackendComposition.lean` |
| Acceptance at the mixed registry | `Examples.BackendComposition.nd_accepts_mix`, `fix_certOkB_pA`, `fix_accepts_pA`, `fix_certOkB_pB`, `fix_accepts_pB` | `Lara/Examples/BackendComposition.lean` |
| A term naming two shipped identities | `Examples.BackendComposition.mixed_usedBackends` | `Lara/Examples/BackendComposition.lean` |
| Distinct *registrations* (not distinct `Form`s) | `Examples.BackendComposition.mixed_registrations_distinct`, `ndRegistered_theory_length`, `ordRegistered_theory_length` | `Lara/Examples/BackendComposition.lean` |
| Firewall instantiated, premise half | `Examples.BackendComposition.mixed_swap`, `mixed_swap_usedBackends`, `sideNdParent`, `ndParent_prems`, `ndParent_typed`, `sideFixA`, `fixChildA_typed` | `Lara/Examples/BackendComposition.lean` |
| Firewall instantiated, discharge half | `Examples.BackendComposition.mixed_dis_swap`, `mixed_dis_swap_usedBackends`, `sideFixB`, `fixChildB_typed`, `sideDisMix`, `disParent_dis`, `disParent_typed` | `Lara/Examples/BackendComposition.lean` |
| Headline at a concrete mixed term | `Examples.BackendComposition.mixed_swap_accounted` | `Lara/Examples/BackendComposition.lean` |

`mixed_registrations_distinct` is named for *registrations* deliberately. Lean
cannot state that two backends' `Form` types differ, record inequality would
not imply it, and a registry may map two identities to the same core. A paper
display asserting distinct formula types would be false; see the frozen record.

`mixed_swap` and `mixed_dis_swap` both use a fixture core as the swapped-in
child, because `ord@1` acceptance is kernel-opaque under Lean 4.32's
Slice-based `String` API. They differ in what sits above that child, and the
difference matters for how much each witnesses:

- `mixed_swap` (premise half) has the real `nd@1` as **parent** —
  `ndParent`, discharged by `registry_success_bridge` — and swaps a declared
  leaf premise for the fixture-certified `fixChildA`. The swapped term names
  both identities (`mixed_swap_usedBackends : usedBackends mixedSwapTerm =
  [ndId, fixId]`), so it is a genuinely mixed witness.
- `mixed_dis_swap` (discharge half) has an **unassured defeasible `ruleMix`
  node as parent**, not `nd@1`: `strictNoQ` forces `D = []` on strict nodes, so
  a certified node in a discharge position needs a defeasible ancestor, and
  `sideDisMix` supplies one with `assur := .defeasible rfl`. Here `nd@1` is the
  **replaced child** — `disParent` holds `ndParent` at `q1` and `disSwapTerm`
  holds `fixChildB` — which is why `mixed_dis_swap_usedBackends` proves
  `usedBackends disParent = [ndId]` and `usedBackends disSwapTerm = [fixId]`.
  The swap crosses a backend boundary; the post-swap term is homogeneous.

The syntactic, resolution, and `certDeps` results use the shipped `nd@1` +
`ord@1`. The worked mixed acceptance vector is Haskell's (`test/StrictSpec.hs`).

---

## Verified surface calculus and elaboration (M5, issue #188)

The exact theorem boundary, hypotheses, counterexamples, and paper-safe
wording are frozen in `docs/theory-m5-surface-calculus.md`. Unless a table
says otherwise, declarations below are in namespace `Lara.Surface`.

### Surface boundary and supported fragment

| Paper object | Lean declaration | File |
|---|---|---|
| Abstract environment, full-AST input, retained output | `Env`, `Input`, `Elaborated` | `Lara/Surface/Syntax.lean` |
| Closed surface error vocabulary | `Error` | `Lara/Surface/Syntax.lean` |
| Structural supported-fragment proposition and executable decider | `Supported`, `supportedB` | `Lara/Surface/Syntax.lean` |
| Supported Boolean/Prop correspondence | `supportedB_iff` | `Lara/Surface/Syntax.lean` |
| Named field correspondences used by reflection | `declarationIdsNodupB_iff`, `ruleNamespacesWellFormedB_iff`, `valueBindingsWellFormedB_iff`, `comparisonsWellFormedB_iff`, `inferredArgsWellFormedB_iff`, `namedCertificatesWellFormedB_iff`, `surfaceAttacksWellFormedB_iff`, `canonicalPremiseLabelsB_iff` | `Lara/Surface/Syntax.lean` |
| Sole presentation-to-core identifier/support conversion layer | `toSupportLeafId`, `toSupportQuestionId`, `toSupportRuleId`, `toSupportBackendId`, `toSupportDigest`, `toSupportTheoryDigest`, `toSupportParam`, `toSupportObligationId`, `toSupportTerm`, `toSupportTerms`, `toSupportDischarges` | `Lara/Surface/Syntax.lean` |

### Binding, alpha-equivalence, and global renaming

| Paper object | Lean declaration | File |
|---|---|---|
| Capture-avoiding rule-parameter substitution laws | `Binding.substParam_fresh_identity`, `Binding.substParam_preserves_wellSorted`, `Binding.substParam_compose_of_fresh` | `Lara/Surface/Binding.lean` |
| Rule-parameter alpha-equivalence | `Binding.RuleAlpha`, `Binding.ruleAlpha_refl`, `Binding.ruleAlpha_symm`, `Binding.ruleAlpha_trans` | `Lara/Surface/Binding.lean` |
| Named-ND binder alpha-equivalence | `NDNamed.Alpha`, `NDNamed.alpha_refl`, `NDNamed.alpha_symm`, `NDNamed.alpha_trans` | `Lara/NDNamed.lean` |
| Alpha-equivalent named certificates have equal de Bruijn/kernel lowering | `NDNamed.toDB_eq_of_alpha`, `NDNamed.lowerNamed_eq_of_alpha`, `alpha_elaboration_invariant` | `Lara/NDNamed.lean`; `Lara/Surface/Correctness.lean` |
| Typed global renamer (replay identities excluded) | `Binding.GlobalRenaming` | `Lara/Surface/Binding.lean` |
| Structural and environment soundness hypotheses | `RenamingSound`, `Renaming.EnvRenamingSound` | `Lara/Surface/Syntax.lean`; `Lara/Surface/Check.lean` |
| Supported fragment is equivariant | `Binding.supported_rename_iff` | `Lara/Surface/Syntax.lean` |
| Per-stage and core-check transport package | `Renaming.GlobalRenamingStageTransports`, `Renaming.global_renaming_stage_transports`, `Renaming.checkUnit_ok_rename`, `Renaming.checkUnit_isOk_rename` | `Lara/Surface/Correctness.lean` |
| Actual-output mixed-ground relation | `Renaming.GroundRelated`, `Renaming.ElaboratedRelated.ground` | `Lara/Surface/Correctness.lean` |
| Fully mapped-ground accepted-carrier relation | `Renaming.CheckedUnitRelated` | `Lara/Surface/Correctness.lean` |
| Headline all-namespace equivariance | `Renaming.global_renaming_equivariant` | `Lara/Surface/Correctness.lean` |

`RenamingSound` supplies structural and fixed-spelling premises.
`Renaming.EnvRenamingSound` has exactly classifier preservation
(`startsIdent`) and registry replay fields. It has no proposition-encoder
field: `Env.encodeProp` is reused unchanged on formula source text fixed by
the structural renaming premises.

Alpha-equivalence applies only to rule parameters and named `nd@1` lambda
binders. Do not cite `GlobalRenaming` as an alpha-equivalence theorem, and do
not describe backend IDs, policy IDs, versions, or digests as renamable.
`GroundRelated` relates actual elaboration outputs by renaming the executable
ground prefix while retaining the literal theory suffix. The final
`CheckedUnitRelated` existential in `global_renaming_equivariant` instead uses
the fully mapped source ground and renamed core unit; do not identify that
witness ground with the actual target output ground.

### Independent expansion and checking

| Paper object | Lean declaration | File |
|---|---|---|
| Prose/value interpolation relation and correspondence | `ExpandsNl`, `expandNl_sound`, `expandNl_complete` | `Lara/Surface/ValueBinding.lean` |
| Whole-program value expansion relation and correspondence | `ExpandsValues`, `expandValues_sound`, `expandValues_complete` | `Lara/Surface/ValueBinding.lean` |
| Comparison expansion relation and correspondence | `ExpandsComparisons`, `expandComparisons_sound`, `expandComparisons_complete` | `Lara/Surface/Comparison.lean` |
| Independent syntax-directed surface judgment | `Checks` | `Lara/Surface/Check.lean` |
| Authored argument-role relation and executable correspondence | `ChecksAuthoredConclusion`, `checkAuthoredConclusion`, `checkAuthoredConclusion_sound`, `checkAuthoredConclusion_complete` | `Lara/Surface/Check.lean` |
| Raw attack-endpoint predicate/decider before group validation | `AttackEndpointsDeclared`, `attackEndpointsDeclaredB`, `attackEndpointsDeclaredB_iff`, `validateAttackEndpoints`, `validateAttackEndpoints_sound`, `validateAttackEndpoints_complete` | `Lara/Surface/Check.lean` |
| Requested-status and duplicate-group predicates/deciders | `StatusesWellFormed`, `statusesWellFormedB`, `statusesWellFormedB_iff`, `resolveStatuses`, `resolveStatuses_sound`, `resolveStatuses_complete`; `GroupsWellFormed`, `groupsWellFormedB`, `groupsWellFormedB_iff`, `validateGroups`, `validateGroups_sound`, `validateGroups_complete` | `Lara/Surface/Syntax.lean`; `Lara/Surface/Check.lean` |
| Declarative core-acceptance premises and completeness bridge | `CoreObligations`, `CoreObligations.of_checkUnit_ok`, `CoreObligations.checkUnit_complete` | `Lara/Surface/Check.lean` |
| Executable checker correspondence and determinism | `check_sound`, `check_complete`, `checks_deterministic`, `checks_supported` | `Lara/Surface/Check.lean` |

`Checks` is not an abbreviation for successful elaboration. Its final
`core` field is `CoreObligations`: declarative signature, policy,
support/certificate, typed-attack, endpoint, and conflict-completeness facts.
`CoreObligations.checkUnit_complete` derives actual checker success through the
core checker's completeness theorem; it does not store an executable-success
wrapper.

### Production-ordered elaboration and correctness

| Paper object | Lean declaration | File |
|---|---|---|
| Audited pure pipeline and output projection | `elaborateWithAudit`, `elaborate` | `Lara/Surface/Elaborate.lean` |
| Successful-run alignment record | `ElaborationAlignment`, `elaborateWithAudit_alignment` | `Lara/Surface/Elaborate.lean` |
| Adjacent production pass boundaries | `elaborateWithAudit_reconstruction_boundary`, `elaborateWithAudit_attack_boundary`, `elaborateWithAudit_unit_boundary`, `elaborateWithAudit_admission_boundary`, `elaborateWithAudit_output_boundary` | `Lara/Surface/Elaborate.lean` |
| Argument, certificate, attack, and admission alignment helpers | `reconstructArgument_preserves_conclusion`, `reconstructArgument_preserves_obligations`, `lowerCertificate_sound`, `lowerCertificate_kernel_identity`, `lowerCertificate_alpha_invariant`, `resolveSurfaceAttacks_order_alignment`, `resolveSurfaceAttacks_endpoint_membership`, `outputFromAdmission_alignment` | `Lara/Surface/Elaborate.lean` |
| Derivation-to-pass completeness | `elaborationPrologue_complete`, `value_pass_complete`, `comparison_pass_complete` | `Lara/Surface/Elaborate.lean` |
| A surface derivation lowers successfully | `elaborate_complete` | `Lara/Surface/Elaborate.lean` |
| **M5 preservation headline** | `elaborate_preserves` | `Lara/Surface/Correctness.lean` |
| **M5 supported-fragment reflection headline** | `elaborate_reflects` | `Lara/Surface/Correctness.lean` |
| Authored obligation ledger preservation | `obligations_preserved` | `Lara/Surface/Correctness.lean` |
| Retained attack preservation | `attacks_preserved` | `Lara/Surface/Correctness.lean` |
| Per-argument conclusion preservation | `conclusions_preserved` | `Lara/Surface/Correctness.lean` |
| Authored/core question-order alignment | `argument_order_preserved` | `Lara/Surface/Correctness.lean` |

There is no unconditional `elaborate_sound`. Cite `elaborate_reflects` only
with both `Supported input` and the explicit successful `checkUnit` premise.
It is reflection for the given surface input, not surjectivity from arbitrary
core units and not unique source recovery.

### Direct and compiled observation

| Paper object | Lean declaration | File |
|---|---|---|
| Direct retained framework and optional claim | `directAF`, `directClaims`, `directClaim` | `Lara/Surface/Observation.lean` |
| Independent core optional lookup and lookup agreement | `coreClaim?`, `directClaims_eq_claims`, `directClaim_eq_coreClaim?` | `Lara/Surface/Observation.lean` |
| Optional direct observation | `Surface.observe` | `Lara/Surface/Observation.lean` |
| Direct carrier/edge equations | `directAF_args`, `directAF_attack_iff` | `Lara/Surface/Observation.lean` |
| Direct support is carrier-local | `directClaim_support_bound` | `Lara/Surface/Observation.lean` |
| Direct and compiled frameworks are equal | `direct_compiled_agree` | `Lara/Surface/Observation.lean` |
| **M5 attack-extensional semantics-parametric observation headline** | `observe_coherent` (requires `Observation.AttackExtensional sem.spec`) | `Lara/Surface/Observation.lean` |
| Grounded/complete/preferred/stable/semi-stable corollaries | `observe_grounded_coherent`, `observe_complete_coherent`, `observe_preferred_coherent`, `observe_stable_coherent`, `observe_semiStable_coherent` | `Lara/Surface/Observation.lean` |
| Carrier-local support is load-bearing | `unboundedDirectClaim_support_unaligned`, `not_observe_coherent_of_unbounded_support` | `Lara/Surface/Observation.lean` |

The generic theorem ranges only over extension semantics satisfying
`Observation.AttackExtensional sem.spec`. Its five named corollaries discharge
that premise internally. The stable theorem preserves `noExtension`; it is not
a five-valued local status collapse. Grounded coherence is instantiated through
`Observation.attackExtensional_leastComplete`.

### Checked boundary witnesses and conformance

| Boundary | Checked declaration/evidence | File |
|---|---|---|
| Fresh generated IDs | `Examples.Surface.necessity_generated_ids_fresh` | `Lara/Examples/Surface.lean` |
| Unambiguous earlier premise resolution | `inferredArgsWellFormedB_iff` plus executable example | `Lara/Surface/Syntax.lean`; `Lara/Examples/Surface.lean` |
| Capture-free named certificates | `namedCertificatesWellFormedB_iff` plus captured-binder/bypass examples | `Lara/Surface/Syntax.lean`; `Lara/Examples/Surface.lean` |
| Comparison polarity | `comparisonsWellFormedB_iff` plus executable example | `Lara/Surface/Syntax.lean`; `Lara/Examples/Surface.lean` |
| Argument-ID uniqueness before attack indexing | `declarationIdsNodupB_iff` plus executable example | `Lara/Surface/Syntax.lean`; `Lara/Examples/Surface.lean` |
| Successful core checking | `CoreObligations.checkUnit_complete` plus invalid-core-support examples | `Lara/Surface/Check.lean`; `Lara/Examples/Surface.lean` |
| Authored conclusion mismatch / undeclared challenge target | `checkAuthoredConclusion_sound` plus executable examples | `Lara/Surface/Check.lean`; `Lara/Examples/Surface.lean` |
| Unknown requested status | `resolveStatuses_sound` plus executable example | `Lara/Surface/Check.lean`; `Lara/Examples/Surface.lean` |
| Duplicate/malformed groups | `validateGroups_sound` plus executable examples | `Lara/Surface/Check.lean`; `Lara/Examples/Surface.lean` |
| Production precedence and first-repeat diagnostics | `elaborateWithAudit_*_boundary` plus executable adversarial examples | `Lara/Surface/Elaborate.lean`; `Lara/Examples/Surface.lean`; `fixtures/surface/` |
| Missing claim preserves absence | `directClaim_eq_coreClaim?` plus executable example | `Lara/Surface/Observation.lean`; `Lara/Examples/Surface.lean` |
| Full-AST positive fixture | `Examples.Surface.allFormsInput`, `allForms_supported`, plus executable check examples | `Lara/Examples/Surface.lean` |
| Cross-language ordered case provenance | `fixtures/surface/MANIFEST.tsv` | manifest, 25 cases, including `gap`, `defeated`, `contested`, and stable `noExtension` |
| Canonical seven-column conformance table | `test/surface-conformance.golden` | committed golden |
| Nonempty, ordered-manifest/closed-feature-complete two-emitter gate | `scripts/check-surface-conformance.sh` | executable conformance evidence |

The executable necessity witnesses are examples, not additional foundational
paper theorems. The Haskell rows exercise the production parser/elaborator;
they provide finite representative conformance evidence and do not prove
Haskell correctness. Manifest completeness covers the required closed feature
vocabulary, not exhaustive parser paths or every AST instance.

The conformance `obligations` cell enumerates open questions recursively in
retained core support terms after admission/group pruning, keyed by retained
authored argument ID. It is distinct from `obligations_preserved`, whose
subject is the unpruned source-authored root-obligation ledger.
## M2b restricted-class complexity closure (issue #209)

The frozen decisions, both gate records, and the claim boundary live in
`docs/theory-m2b-complexity.md` (gate history:
`docs/theory-m2b-complexity-spike.md`). Every theorem row is
`lean/AxCheck.lean`-gated (sorry-free, standard trio). All statements are
under the frozen M2b context — `canon := id`, `m2bSigma`, `m2bPolicy`,
`m2bRegistry` — and the cost statements count `F.attack` queries of the
instrumented Lean reference mirrors, not production-runtime measurements.

| Paper object | Lean declaration | File |
|---|---|---|
| Family-wide checker equation (realization closure) | `Complexity.checkUnit_formula_ok` | `Lara/Complexity/Gadget.lean` |
| Carrier-status agreement with `Invariants.status` | `Complexity.carrierStatusC_fst` | `Lara/Complexity.lean` |
| **GroundedStatus upper bound (the paper-citable headline)**: `n³(1 + n) + 2n²` | `Complexity.carrierStatusC_cost_le` | `Lara/Complexity.lean` |
| Universal grounded upper bound `n³(1 + n)` | `Complexity.groundedC_cost_le` | `Lara/Complexity.lean` |
| Universal grounded lower bound `n²` | `Complexity.groundedC_cost_ge` | `Lara/Complexity.lean` |
| Quartic witness class membership (fixed context) | `Examples.Complexity.quartic_realizable` | `Lara/Examples/Complexity.lean` |
| Quartic worst-case grounded cost (existential, `2 ≤ k`) | `Examples.Complexity.quartic_cost_ge` | `Lara/Examples/Complexity.lean` |
| Quartic worst-case carrier-status cost | `Examples.Complexity.carrierStatus_quartic_cost_ge` | `Lara/Examples/Complexity.lean` |
| Reduction output class membership | `Complexity.reduce_realizable` | `Lara/Complexity/Reduction.lean` |
| Reduction output size (quadratic carrier accounting) | `Complexity.reduce_byteSize` | `Lara/Complexity/Reduction.lean` |
| **3SAT reduction correctness (two-sided)** | `Complexity.reduce_correct` | `Lara/Complexity/Reduction.lean` |
| Class-membership negative control (`g(0)` self-edge not realizable) | `Complexity.selfEdgeCode_not_realizable` | `Lara/Complexity/Reduction.lean` |

Quantifier discipline the paper must respect (constraint D4 of the frozen
record): `groundedC_cost_ge` is a *universal* quadratic lower bound;
`quartic_cost_ge` and `carrierStatus_quartic_cost_ge` are *existential*
worst-case results on a realizable family. No display may merge the two
quantifiers, and correctness must be quoted with class membership and output
size adjacent (`reduce_correct_realizable`, `reduce_correct_nodes`,
`reduce_correct_byteSize` package them).

**Not X** notes:

- `Grounded.deficit_bound` (`Lara/Grounded.lean`) bounds *rounds* of the
  grounded iteration, not attack queries. It must not be cited as a
  query-cost bound; the query bounds are the `*_cost_le` / `*_cost_ge`
  rows above.
- The generic Claim bound `Complexity.statusSharedC_cost_le` is internal
  accounting behind `carrierStatusC_cost_le`. It must not be cited as the
  restricted-class headline.
- `Invariants.CompilerInvariant` alone is **not** class membership.
  Realizability claims require the executable checker equation and a
  `StructuredAFIso` under the fixed context (`Realizability.Realization`);
  `selfEdgeCode_not_realizable` is the witness keeping the reduction a
  restricted-class statement.
- `reduce_correct` is **not** an NP-completeness statement. The
  complexity-class bookkeeping (encodings, machine model, membership in NP)
  stays paper-level and cites the mechanized obligations
  `reduce_correct` + `reduce_realizable` + `reduce_byteSize`.

---

## PW0 possible-world outer-model gate (issue #192)

Tracker #189. The frozen contract, the gate assessment, and the three known
limitations live in `docs/theory-pw0-outer-model.md`; this section is the
declaration index. Every *theorem* row is `lean/AxCheck.lean`-gated
(sorry-free, standard trio, no `native_decide`). Rows naming `Frame`,
`Valuation`, `Form`, `Sat`, `CrossResult`, `IncomparabilityReason`, `crossCompare`,
`Context`, `World`, `cmpStatus`, `srcStatus` and the two Lara valuations name
*definitions*, which carry no independent axiom obligation — each is
transitively audited through a gated theorem that mentions it (`Frame`/`Sat`
through the T2 laws, `crossCompare` through the T5 lemmas, `Context`/`World`/
`cmpStatus`/`srcStatus` through T1, `srcVal`/`cmpVal` through T4).

No paper display cites these yet. PW0 is a spike whose exit decision is taken
on #192; the rows exist so that the decision, T6, and any later possible-world
display can cite a stable key rather than re-deriving one.

**Naming.** The executable comparison is `PW.crossCompare`, not `compare`.
Core exports `Ord.compare` into the root namespace, and under `open Lara.PW` a
plain `compare` loses in ways that are not merely cosmetic: `unfold compare`
fails with `ambiguous term, use fully qualified name`, and an unapplied
`compare` silently resolves to `Ord.compare`. Since the T5 proofs unfold this
definition and downstream modules (T6, #191) will too, the prefix is
load-bearing. The *theorem* names deliberately keep the `compare_*` prefix —
they are namespace qualified and collide with nothing, so renaming them would
churn citation keys for no gain.

**Notation.** The paper writes `M, w ⊨ φ`. The Lean writes `Sat F V φ w` —
**formula first**, and the valuation is an explicit parameter rather than a
frame field. Both departures are load-bearing: the argument order is forced by
elaboration (a world does not determine its context index, so a world-first
`Sat` fails to elaborate at the `box`/`dia` arms), and the valuation parameter
*is* the design's `M[V := …]` instantiation, stated once instead of duplicating
the model. See `Sat`'s doc comment and `docs/theory-pw0-outer-model.md` §1.

| Object | Lean declaration | File |
|---|---|---|
| The outer frame (contexts, bridges, worlds, queries, `R`, `accept`, `translate`) | `PW.Frame`; accepted edges `PW.Frame.A` | `Lara/PW/Outer.lean` |
| Selected local observation valuation | `PW.Valuation` | `Lara/PW/Outer.lean` |
| Typed outer formula language | `PW.Form` (`status`, `top`, `neg`, `conj`, `box`, `dia`), derived `PW.Form.imp` | `Lara/PW/Outer.lean` |
| Satisfaction (paper `M, w ⊨ φ`) | `PW.Sat` — formula-first, valuation-parameterized | `Lara/PW/Outer.lean` |
| Singleton index types (never bare `Unit`, which binds `Lara.Unit`) | `PW.OneCtx`, `PW.OneBridge` | `Lara/PW/Outer.lean` |
| T2 typed normality | `PW.sat_imp`, `PW.sat_K`, `PW.sat_nec`, `PW.sat_dia_iff_not_box_neg`, `PW.sat_box_top`, `PW.sat_box_conj` | `Lara/PW/Outer.lean` |
| T2 negative controls (every stronger frame axiom refuted: T, D, B, 5 on the two-world frame, 4 on a three-world chain) | `Examples.PW.frameT`, `valT`, `sat_T_fails`, `sat_D_fails`, `sat_B_fails`, `sat_5_fails`; `Examples.PW.frame4`, `val4`, `sat_4_fails` | `Lara/Examples/PW.lean` |
| Valuation coherence side conditions | `PW.Valuation.Functional`, `PW.Valuation.Total`; consequences `PW.not_sat_two_status`, `PW.exists_status_of_total` | `Lara/PW/Outer.lean` |
| Their four discharges (source side **only through T1**) | `PW.Instance.cmpVal_functional`, `cmpVal_total`, `srcVal_functional`, `srcVal_total` | `Lara/PW/Instance.lean` |
| T3 ordinary multimodal Kripke semantics (defined independently) | `PW.Kripke`, `PW.KForm`, `PW.KVal`, `PW.KSat`; embedding `PW.Kripke.frame`, `PW.KForm.lift`, `PW.KVal.lift` | `Lara/PW/Uniform.lean` |
| T3 uniform-language reduction | `PW.sat_lift` | `Lara/PW/Uniform.lean` |
| T4 generic valuation congruence | `PW.sat_congr` | `Lara/PW/Outer.lean` |
| Incomparability reasons and the tagged result | `PW.IncomparabilityReason`, `PW.CrossResult` (neither contains a `Status`) | `Lara/PW/Compare.lean` |
| The executable comparison | `PW.crossCompare` (guard order: translation, candidates, acceptance) | `Lara/PW/Compare.lean` |
| T5 reason/profile characterization | `PW.compare_none`, `PW.compare_no_candidate`, `PW.compare_all_rejected`, `PW.compare_comparable`, `PW.mem_compare_profile_iff`, `PW.incomparable_ne_comparable`, `PW.compare_translationUndefined_iff` | `Lara/PW/Compare.lean` |
| The presentation obligation on the executable inputs | `PW.Presents` (fields `mem_iff`, `accept_iff`) | `Lara/PW/Compare.lean` |
| Adequacy: `crossCompare` computes the model's `⟨b⟩` | `PW.mem_compare_iff_sat_dia`; incomparability has no accepted witness by `PW.not_sat_dia_of_incomparable` | `Lara/PW/Compare.lean` |
| The presentation obligation discharged, and the adequacy round trip run, at a real Lara bridge | `Examples.PW.presentsT7`, `Examples.PW.t7_dia_via_adequacy` | `Lara/Examples/PW.lean` |
| The semantic incomparability theorem discharged at a real Lara bridge | `Examples.PW.bridgeOverlapRejected`, `presentsOverlapRejected`, `overlap_rejected_no_dia` | `Lara/Examples/PW.lean` |
| Scientific context (the stable checking environment) | `PW.Instance.Context` | `Lara/PW/Instance.lean` |
| Admissible local world (an accepted `CheckedUnit` under that environment) | `PW.Instance.World`; claim projection `PW.Instance.claimAt` | `Lara/PW/Instance.lean` |
| The two independent world-local observations | `PW.Instance.srcStatus` (relational, oracle-free), `PW.Instance.cmpStatus` (executable) | `Lara/PW/Instance.lean` |
| T1 world-local preservation | `PW.Instance.srcStatus_iff_cmpStatus` — `Compile.srcStatus_iff_checked` at the world | `Lara/PW/Instance.lean` |
| Bridge data and the induced frame | `PW.Instance.BridgeData`, `PW.Instance.BridgeData.frame` | `Lara/PW/Instance.lean` |
| The two Lara valuations | `PW.Instance.srcVal`, `PW.Instance.cmpVal` | `Lara/PW/Instance.lean` |
| T4 modal source/compiled coherence | `PW.Instance.sat_src_iff_cmp`; worked instances `Examples.PW.t7_dia_defeated_src`, `t7_box_defeated_src` | `Lara/PW/Instance.lean`, `Lara/Examples/PW.lean` |
| T0 current-Lara conservativity | `PW.Instance.singleton`, `PW.Instance.t0_cmp`, `PW.Instance.t0_src` (both `Iff.rfl`) | `Lara/PW/Instance.lean` |
| T7 fixtures (context, two accepted worlds, the bridge) | `Examples.PW.polT7`, `ctxT7`, `unitT7src`, `unitT7tgt`, `unitT7src_accepted`, `unitT7tgt_accepted`, `wT7src`, `wT7tgt`, `bridgeT7` | `Lara/Examples/PW.lean` |
| T7 status non-preservation | `Examples.PW.t7_src_justified`, `t7_tgt_defeated`, `t7_transport_wellFormed`, `t7_support_transported`, `t7_witness` | `Lara/Examples/PW.lean` |
| T7 through the modal layer, both readings under both valuations | `Examples.PW.t7_dia_defeated`, `t7_box_defeated`, `t7_dia_defeated_src`, `t7_box_defeated_src` | `Lara/Examples/PW.lean` |
| Overlapping fields (shared `p`/`q`; the second field declares `r` and not `s`, so neither language contains the other) | `Examples.PW.sigmaOverlap`, `polOverlap`, `ctxOverlap`, `unitOverlap`, `unitOverlap_accepted`, `wOverlap`, `tauOverlap` | `Lara/Examples/PW.lean` |
| One executable fixture per incomparability reason | `Examples.PW.overlap_comparable`, `overlap_translationUndefined`, `overlap_noCandidate`, `overlap_allRejected` | `Lara/Examples/PW.lean` |
| The local `gap` the outer layer declines to report, and the two-status instance | `Examples.PW.overlap_local_gap`, `Examples.PW.t7_no_two_status` | `Lara/Examples/PW.lean` |

**Not X** notes:

- `PW.Instance.sat_src_iff_cmp` (T4) is **not** the substantive result. It is
  `PW.sat_congr` instantiated at T1 — an integration theorem whose content is
  that satisfaction is extensional in the atomic valuation. The Lara theorem
  underneath it is `PW.Instance.srcStatus_iff_cmpStatus` (T1), which is itself
  `Compile.srcStatus_iff_checked` applied at a world. No display may cite T4
  as source/compiled preservation.
- `PW.Frame.accept` is **not** a checker, a certificate, or a soundness
  condition. It is an arbitrary `Prop` with no posited connection to any Lara
  judgment; supplying that connection is T6. See
  `docs/theory-pw0-outer-model.md` §4 limitation 1.
- A `PW.Valuation` alone does **not** say a claim has exactly one status. Any
  claim about the four-state status being a function at the modal layer must
  quote `Valuation.Functional`/`.Total` and their discharges alongside.
- `PW.crossCompare` alone is **not** an implementation of `⟨b⟩`. It takes its
  candidate list and acceptance test on trust; the implementation claim
  requires `PW.Presents` and `PW.mem_compare_iff_sat_dia` adjacent.
- `Status.gap` in the PW0 layer is **not** "considered and unsupported". It
  conflates four conditions because queries are all of `Atom`; only the
  bridge-domain case is separated, and it is reported as
  `IncomparabilityReason.translationUndefined`, never as a status. See
  `docs/theory-pw0-outer-model.md` §4 limitation 2.
- `Examples.PW.t7_transport_wellFormed` alone is **not** the support-transport
  half of the T7/T8 boundary: it says only that `leaf l1` is among the target's
  arguments, which any coincidental argument would satisfy. Cite
  `Examples.PW.t7_support_transported` beside it — that is the statement that
  source and target complete supports are the same nonempty index set `[0]`
  and that the shared index resolves, through both retained node caches (the
  structure support indices actually index), to the same term `leaf l1`.
- The T2 block is **not** a claim that the logic is more than normal.
  No stronger frame axiom (T, 4, B, D, 5) is assumed or proved, and each of
  the five is refuted on a PW0-legal frame (`Examples.PW.sat_T_fails`,
  `sat_D_fails`, `sat_B_fails`, `sat_5_fails`, `sat_4_fails`).

## PW-T6 exact checked-support transport (issue #191)

Tracker #189. The frozen contract and its limitations live in
`docs/theory-pw-t6-structural-transport.md`; this section is the declaration
index. Every *theorem* row is `lean/AxCheck.lean`-gated (sorry-free, standard
trio, no `native_decide`). Rows naming `SymMap`, the `tr*` lifts,
`StructuralBridge`, and `Admits` name *definitions*, transitively audited
through the gated theorems that mention them.

No paper display cites these yet. The rows exist so that T8 (#193), T9
(#190), and any later structural-bridge display can cite a stable key.

| Object | Lean declaration | File |
|---|---|---|
| The partial symbol translation (predicate and constructor namespaces independent) | `PW.SymMap`; identity `PW.SymMap.id` | `Lara/PW/Translation.lean` |
| The structural lifts (terms, atoms, patterns, substitutions, questions, rules) | `PW.trTerm`/`trTerms`, `PW.trAtom`/`trAtoms`, `PW.trPat`/`trPats`, `PW.trAPat`/`trAPats`, `PW.trSubst`, `PW.trQuestion`/`trQuestions`, `PW.trRule` | `Lara/PW/Translation.lean` |
| The dependent partial support map `T_b` (leaves renamed, rule ids / hole sets / assurances verbatim) | `PW.trSupport`, `PW.trSupportList`, `PW.trSupportDis` | `Lara/PW/Translation.lean` |
| Instantiation commutes with translation (the conclusion law at pattern level) | `PW.instPat_tr`/`instPats_tr`, `PW.instAPat_tr`/`instAPats_tr` | `Lara/PW/Translation.lean` |
| `≡` survives translation (`nf` touches literals only, the translation touches names only) | `PW.trTerm_nf`/`trTerms_nf`, `PW.trAtom_nf`, `PW.equiv_tr` | `Lara/PW/Translation.lean` |
| Carriers the translation preserves on the nose | `PW.trSubst_fst`, `PW.trRule_mode`/`_params`/`_allowTrusted`/`_certifiers`/`_questionNames`/`_mandatoryNames`, `PW.trSupportDis_fst` | `Lara/PW/Translation.lean` |
| The structural-bridge contract (three clauses over a shared `canon`) | `PW.StructuralBridge` (fields `sym`, `leafMap`, `leaf_ok`, `rule_ok`, `cert_ok`); identity `PW.StructuralBridge.refl` | `Lara/PW/Structural.lean` |
| **T6 — exact checked-support transport** (translated conclusion, verbatim obligations) | `PW.support_transport` | `Lara/PW/Structural.lean` |
| T6 completeness clause | `PW.support_transport_complete` | `Lara/PW/Structural.lean` |
| Claim-level transport (`≡`-closure survives) | `PW.supports_transport` | `Lara/PW/Structural.lean` |
| Target-side occurrence replay against the target registry (B0's headline on the transported derivation) | `PW.transport_occurrences_accounted` | `Lara/PW/Structural.lean` |
| The induced checker-tied applicability judgment (PW0 limitation 1 discharged at structural bridges) | `PW.Admits`; world-level transport `PW.admits_transport` | `Lara/PW/Structural.lean` |
| The identity endobridge at the T7 pair | `Examples.PW.admitsIdT7`, `t7_t6_transport` | `Lara/Examples/PWStructural.lean` |
| The T6/T8 boundary packaged at a live instance (transport succeeds, status flips) | `Examples.PW.t7_t6_boundary` | `Lara/Examples/PWStructural.lean` |
| The genuine renaming bridge and its transported derivation | `Examples.PW.renSym`, `ruleRen`, `piRenSrc`, `piRenTgt`, `lRen`, `leafMapRen`, `gammaRenSrc`, `gammaRenTgt`, `bridgeRen`, `wRen`, `wRenTgt`, `hasSupport_ren`, `ren_conclusion`, `ren_transport` | `Lara/Examples/PWStructural.lean` |
| The strict-certificate renaming bridge and its transported derivation | `Examples.PW.βRen`, `hdRen`, `κRen`, `ruleCert`, `rnCert`, `piCertSrc`, `piCertTgt`, `certCertSrc`, `certCertTgt`, `bridgeCert`, `wCert`, `wCertTgt`, `hasSupport_cert`, `cert_accept_translated`, `cert_reject_untranslated`, `cert_support_renamed`, `cert_transport` | `Lara/Examples/PWStructural.lean` |
| The bridge's three non-vacuous clauses exercised off the identity (`rule_ok` by the translated policy, `leaf_ok` by the renamed leaf at the translated atom, `cert_ok` by translated certificate acceptance) | `Examples.PW.ren_support_renamed`, `ren_leaf_translated`, `cert_accept_translated`, `cert_reject_untranslated`, `cert_support_renamed` | `Lara/Examples/PWStructural.lean` |
| The strict fixture's drift guards (the acceptance judgments read the certifier triple; the certificate arm is the only reachable assurance) | `Examples.PW.βOther`, `hdOther`, `κOther`, `cert_reject_mismatched_certifier`, `ruleCertTgt`, `cert_target_rule`, `cert_only_assurance` | `Lara/Examples/PWStructural.lean` |
| The translation-domain negative | `Examples.PW.ren_out_of_vocabulary`, `ren_translationUndefined` | `Lara/Examples/PWStructural.lean` |

**Not X** notes:

- `PW.support_transport` is **not** status preservation. It transports the
  checked-support judgment only; `Examples.PW.t7_t6_boundary` is the
  mechanized instance where the transport succeeds and grounded status still
  flips. Any status-preservation display cites T8 (#193), not T6.
- The transport's `some` hypothesis is **not** redundant. `trSupport` is not
  total on checked supports: a substitution may bind a declared-but-unused
  parameter to a term outside the bridge's vocabulary (`θDom` forces the
  domain, not that every binding occurs in a pattern). Definedness of the
  *conclusion's* translation is derived; definedness of the *term's*
  translation is the design's explicit translation-domain evidence.
- "Mapped obligations" is the **identity** map, not a claim that a bridge may
  rename question keys. Question names, mandatory flags, discharge keys, and
  hole sets are preserved verbatim (`trRule_questionNames`,
  `trSupportDis_fst`), which is exactly why obligations — and hence
  completeness — transport for free.
- A `StructuralBridge` does **not** relate two canonicalizers. The `canon` is
  shared by construction — the one thing bridged environments must agree on
  for conclusions to be comparable as claims (the same shared binder B0
  records for registries; see `docs/theory-b0-backend-compositionality.md`).
- `PW.Admits` is **not** an acceptance oracle. It is one checker-tied
  instantiation of PW0's `accept` — target program membership of every
  transported source argument — supplied so `Frame.accept`'s name stops
  promising more than the model provides at structural bridges. Other
  disciplines remain expressible.

## PW-T9 exact structural-path composition (issue #190)

Tracker #189. The frozen contract, interpretation, and limitations live in
`docs/theory-pw-t9-path-composition.md`; this section is the declaration
index. Every *theorem* row is intended for the final `lean/AxCheck.lean` gate
(sorry-free, standard trio, no `native_decide`). Definition rows are audited
transitively through the gated theorems stated over them.

No paper display cites these yet. The rows exist so that later
structural-path, acceptance, and status-preservation displays can cite a
stable key.

| Object | Lean declaration | File |
|---|---|---|
| First-leg-first Kleisli composition of partial symbol maps, with its two unit laws | `PW.SymMap.comp`; `PW.SymMap.id_comp`, `PW.SymMap.comp_id` | `Lara/PW/Compose.lean` |
| Term and term-list composition laws | `PW.trTerm_comp`, `PW.trTerms_comp` | `Lara/PW/Compose.lean` |
| Atom and atom-list composition laws | `PW.trAtom_comp`, `PW.trAtoms_comp` | `Lara/PW/Compose.lean` |
| First-leg and mid-path atom-domain negatives | `PW.trAtom_comp_none_left`, `PW.trAtom_comp_none_mid` | `Lara/PW/Compose.lean` |
| Pattern and pattern-list composition laws | `PW.trPat_comp`, `PW.trPats_comp` | `Lara/PW/Compose.lean` |
| Atomic-pattern and atomic-pattern-list composition laws | `PW.trAPat_comp`, `PW.trAPats_comp` | `Lara/PW/Compose.lean` |
| Substitution composition law | `PW.trSubst_comp` | `Lara/PW/Compose.lean` |
| Support, support-list, and discharge-list composition laws | `PW.trSupport_comp`, `PW.trSupportList_comp`, `PW.trSupportDis_comp` | `Lara/PW/Compose.lean` |
| Question and question-list composition laws | `PW.trQuestion_comp`, `PW.trQuestions_comp` | `Lara/PW/Compose.lean` |
| Shared all-or-nothing traversal seam under the composition family (issue #234) | `PW.zipOpt`; `PW.zipOpt_bind`, `PW.trAtoms_cons`, `PW.trTerms_cons`, `PW.trTerm_con`, `PW.trPats_cons`, `PW.trAPats_cons`, `PW.trSubst_cons`, `PW.trQuestions_cons`, `PW.trSupportList_cons`, `PW.trSupportDis_cons` | `Lara/PW/Compose.lean` |
| Rule composition law | `PW.trRule_comp` | `Lara/PW/Compose.lean` |
| Binary exact-bridge composition | `PW.StructuralBridge.comp` | `Lara/PW/Compose.lean` |
| Explicit two-step checker applicability and its exact composite factorization | `PW.AdmitsSteps`; `PW.admits_comp`, `PW.admits_steps_of_intermediate` | `Lara/PW/Compose.lean` |
| Binary support transport exposing intermediate and final checked judgments | `PW.support_transport_comp` | `Lara/PW/Compose.lean` |
| First-class indexed exact paths, their folded bridge, and stepwise partial support map | `PW.BridgePath`, `PW.BridgePath.compose`, `PW.BridgePath.trans` | `Lara/PW/Compose.lean` |
| Stepwise path transport equals transport by the folded bridge | `PW.BridgePath.trans_eq_compose` | `Lara/PW/Compose.lean` |
| Direct/path commuting contract and exact map-equality characterization | `PW.Commutes` (fields `atom_eq`, `support_eq`); `PW.Commutes.of_maps_eq` | `Lara/PW/Compose.lean` |
| Leaf, predicate, constructor, and full symbol-map equalities extracted from `Commutes` | `PW.Commutes.leafMap_eq`, `PW.Commutes.predMap_eq`, `PW.Commutes.conMap_eq`, `PW.Commutes.sym_eq` | `Lara/PW/Compose.lean` |
| Agreement of direct and path transport on a checked source support | `PW.direct_transport_agrees` | `Lara/PW/Compose.lean` |
| Rule and admitted-leaf translations pinned by common target typing | `PW.commutes_on_rules`, `PW.commutes_on_leaves` | `Lara/PW/Compose.lean` |
| Direct/path checker-tied applicability equivalence | `PW.admits_iff_of_commutes` | `Lara/PW/Compose.lean` |
| Full accepted edge (`R ∧ Admits`) and direct/path equivalence with a separate candidate-relation premise | `PW.Accepted`; `PW.accepted_iff_of_commutes` | `Lara/PW/Compose.lean` |
| **T9 — checked-support transport along an arbitrary chosen exact path** | `PW.path_support_transport` | `Lara/PW/Compose.lean` |
| Live second rename and concrete two-edge path | `Examples.PW.Compose.ren2Sym`, `bridgeRen2`, `pathRen`, `bridgeRenDirect`, `wRenTgt2`; `ren2_conclusion`, `ren_path_trans`, `ren_path_transport` | `Lara/Examples/PWCompose.lean` |
| Positive direct/two-edge commuting triangle and transport agreement | `Examples.PW.Compose.ren_path_commutes`, `ren_direct_transport_agrees` | `Lara/Examples/PWCompose.lean` |
| Concrete three-edge path, positive triangle, and transport agreement | `Examples.PW.Compose.pathRen3`; `ren_path3_commutes`, `ren_path3_transport_agrees` | `Lara/Examples/PWCompose.lean` |
| Concrete binary theorem path with both checked judgments exposed | `Examples.PW.Compose.ren_support_transport_comp` | `Lara/Examples/PWCompose.lean` |
| Concrete common-target and symbol-map consequences | `Examples.PW.Compose.ren_commutes_on_rule`, `ren_commutes_on_leaf`, `ren_commutes_on_symbol_maps` | `Lara/Examples/PWCompose.lean` |
| Inhabited identity applicability and explicit intermediate world | `Examples.PW.Compose.bridgeIdT7`, `pathIdT7`; `admitsSelfT7`, `t7_admits_steps_of_intermediate` | `Lara/Examples/PWCompose.lean` |
| Exact composite-applicability iff and inhabited reverse direction | `Examples.PW.Compose.t7_admits_comp_iff`, `t7_admits_composite` | `Lara/Examples/PWCompose.lean` |
| Positive identity direct/path triangle and applicability equivalence | `Examples.PW.Compose.t7_identity_path_commutes`, `t7_admits_iff_of_commutes` | `Lara/Examples/PWCompose.lean` |
| Candidate coherence, accepted-edge equivalence, inhabitation, and negative separation | `Examples.PW.Compose.candidateDirectT7`, `candidatePathT7`, `candidatePathFalseT7`; `t7_candidate_relations_agree`, `t7_accepted_iff_of_commutes`, `t7_accepted_inhabited`, `t7_accepted_needs_candidate_coherence` | `Lara/Examples/PWCompose.lean` |
| Negative triangle: distinct leaf renaming despite checked supports | `Examples.PW.Compose.bridgeSwap`, `twinIdentityPath`; `direct_ne_composed_support` | `Lara/Examples/PWCompose.lean` |
| Negative triangle: predicate-only disagreement with equal leaf and constructor maps | `Examples.PW.Compose.claimOnlySym`, `claimOnlyBridge`, `claimIdentityPath`; `direct_ne_composed_claim` | `Lara/Examples/PWCompose.lean` |
| Non-vacuous certificate acceptance through two live bridge legs | `Examples.PW.Compose.certCertTgt2`, `bridgeCert2`, `certCompBridge`; `certComp_two_live_legs` | `Lara/Examples/PWCompose.lean` |
| Real atom, support-transport, and context-tied applicability vocabulary gaps | `Examples.PW.Compose.gapSym`, `gapBridgeRen`, `gapBridgeRen2`, `gapBridgeDrop`, `gapPath`, `gapSupportPath`; `mid_path_out_of_vocabulary`, `mid_path_translationUndefined`, `mid_path_support_undefined`; `gapConFirstBridge`, `gapConDropBridge`, `gapAppContext`, `gapAppWorld`, `gap_admits_comp_fails` | `Lara/Examples/PWCompose.lean` |
| Nonempty substitution, pattern, question-list, and discharge-list computations | `Examples.PW.Compose.substRenSrc`, `substRenTgt`, `substRenTgt2`, `patRenSrc`, `patRenTgt`, `patRenTgt2`, `questionRenSrc`, `questionRenTgt`, `questionRenTgt2`, `supportDisRenSrc`, `supportDisRenTgt`, `supportDisRenTgt2`; `trSubst_nonempty_computes`, `trPat_nonempty_computes`, `trQuestions_nonempty_computes`, `trSupportDis_nonempty_computes` | `Lara/Examples/PWCompose.lean` |
| Focused first-leg-gap and unit-law witnesses (issue #235) | `Examples.PW.Compose.first_leg_gap_computes`, `first_leg_gap_law`, `id_comp_ren2`, `comp_id_ren2` | `Lara/Examples/PWCompose.lean` |
| `zipOpt` all-or-nothing computation witness (issue #234) | `Examples.PW.Compose.zipOpt_computes` | `Lara/Examples/PWCompose.lean` |

**Not X** notes:

- `PW.Commutes` is **not** a binary-only bridge predicate. It compares one
  direct bridge with an arbitrary `PW.BridgePath`; the real three-edge
  `pathRen3` witnesses that scope.
- `PW.commutes_on_rules` and `PW.commutes_on_leaves` are **not** fields of, or
  premises for, `PW.Commutes`. Common target typing pins those local
  consequences; the two fields remain `atom_eq` and `support_eq`.
- `PW.Commutes` is **not** weaker than bridge-data equality. Support
  substitutions expose constructor translation, so `Commutes.of_maps_eq`
  characterizes it exactly as equality of the full symbol map and leaf map.
- `PW.Admits` is **not** the full accepted-edge relation. `PW.Accepted` is
  literally a caller-supplied relation conjoined with `Admits`, and
  `accepted_iff_of_commutes` requires candidate-relation coherence separately.
- `BridgePath.trans_eq_compose` is **not** independence from the chosen
  intermediate environments. The path is data, and the theorem identifies
  its stepwise map with that same path's fold.
- `PW.path_support_transport` is **not** status preservation. It preserves the
  checked-support judgment and obligations along an exact path; pathwise
  status preservation is T8 composed with T9.
- The T9 laws are **not** approximation-bridge composition and do **not**
  provide bridge-level associativity or unit equalities. Approximation needs
  separate domains, observables/comparison spaces, and error/convergence laws;
  the available unit equalities are only `PW.SymMap.id_comp` and
  `PW.SymMap.comp_id`.

---

## PW-T8 conditional status preservation (issue #193)

Tracker #189. The frozen hypotheses, interpretation, and limitations live in
`docs/theory-pw-t8-status-preservation.md`; this section is the declaration
index. Every *theorem* row is intended for the final `lean/AxCheck.lean` gate
(sorry-free, standard trio, no `native_decide`). Definition rows are audited
transitively through the gated theorems stated over them.

No paper display cites these yet. The rows exist so that later status,
robust-justification, and approximation-bridge displays can cite a stable
key.

| Object | Lean declaration | File |
|---|---|---|
| Total attack bisimulation between finite frameworks, with its converse | `PW.AttackBisim` (fields `dom`, `left_total`, `right_total`, `forth`, `back`); `PW.AttackBisim.symm` | `Lara/PW/AFBisim.lean` |
| Attack forth condition (source attacker matched by a related target attacker) | `PW.AttackBisim.forth`; at a bridge `PW.StatusBridge.forth` | `Lara/PW/AFBisim.lean`, `Lara/PW/Status.lean` |
| Attack back condition (target attacker matched by a related source attacker; no unmatched target attacker) | `PW.AttackBisim.back`; at a bridge `PW.StatusBridge.back` | `Lara/PW/AFBisim.lean`, `Lara/PW/Status.lean` |
| Declarative grounded judgments transfer along a bisimulation | `PW.directIn_bisim`, `PW.directOut_bisim`; iff forms `PW.directIn_iff_of_bisim`, `PW.directOut_iff_of_bisim` | `Lara/PW/AFBisim.lean` |
| Grounded label invariance under bisimulation | `PW.labelC_of_bisim` | `Lara/PW/AFBisim.lean` |
| Support-set correspondence (complete-support index sets correspond both ways) and the status congruence | `PW.SupportCorr`; `PW.statusC_congr` | `Lara/PW/AFBisim.lean` |
| Status invariance under bisimulation — all four statuses at once, none read as a label | `PW.statusC_of_bisim` | `Lara/PW/AFBisim.lean` |
| AF isomorphism (the design's bijection preserving and reflecting attack; `inj` recorded, never consumed) and its graph | `PW.AFIso` (fields `maps`, `inj`, `surj`, `attack_iff`); `PW.AFIso.graph` | `Lara/PW/AFBisim.lean` |
| An AF isomorphism is a total attack bisimulation | `PW.AFIso.toBisim` | `Lara/PW/AFBisim.lean` |
| Labels and status along an isomorphism | `PW.labelC_of_iso`, `PW.statusC_of_iso` | `Lara/PW/AFBisim.lean` |
| "Maps the complete support set for `c` onto the complete support set for `τ(c)`" yields the correspondence | `PW.supportCorr_of_image` | `Lara/PW/AFBisim.lean` |
| Injective translation (injectivity-where-defined on both partial namespaces), the identity, and closure under Kleisli composition | `PW.SymMap.Injective`; `PW.SymMap.id_injective`, `PW.SymMap.Injective.comp` | `Lara/PW/Status.lean` |
| Injectivity on lifted terms, term lists, and atoms | `PW.trTerm_inj`, `PW.trTerms_inj`, `PW.trAtom_inj` | `Lara/PW/Status.lean` |
| `≡` reflects along an injective translation (converse of `PW.equiv_tr`) | `PW.equiv_tr_reflect` | `Lara/PW/Status.lean` |
| Argument correspondence induced by a translation (source argument `i` transports to target argument `j`) and its range bound | `PW.Corr`; `PW.corr_lt` | `Lara/PW/Status.lean` |
| **Status-preserving bridge** — the T8 hypotheses: left-total (`Admits`), right-total (no unmatched target argument), attack forth, attack back | `PW.StatusBridge` (fields `admits`, `matched`, `forth`, `back`) | `Lara/PW/Status.lean` |
| The status-preserving bridge is a total attack bisimulation of the two compiled frameworks | `PW.StatusBridge.bisim` | `Lara/PW/Status.lean` |
| Translated conclusion at corresponding indices | `PW.corr_conclusion` | `Lara/PW/Status.lean` |
| Support-set correspondence derived for every translatable query | `PW.claimSupport_corr` | `Lara/PW/Status.lean` |
| Status preservation from a supplied support-set correspondence (non-injective bridges) | `PW.status_transport_of_corr` | `Lara/PW/Status.lean` |
| **T8 — conditional status preservation** (`cmpStatus v (τ c) = cmpStatus w c`) | `PW.status_transport` | `Lara/PW/Status.lean` |
| T8 at the source observation (T1 on both sides) | `PW.srcStatus_transport` | `Lara/PW/Status.lean` |
| RobustlyJustified collapse: `Comparable ∧ [b]Justified(τ c)` reduces to the local atom, at every status | `PW.sat_status_iff_box`; under the source valuation `PW.sat_status_iff_box_src` | `Lara/PW/Status.lean` |
| PossiblyJustified collapse: `Translatable ∧ ⟨b⟩Justified(τ c)` reduces to the local atom, at every status | `PW.sat_status_iff_dia` | `Lara/PW/Status.lean` |
| Composite argument correspondence factors through the chosen intermediate world | `PW.corr_comp_iff` | `Lara/PW/Status.lean` |
| Status-preserving bridges compose along the T9 composite (legs in path order, first leg first); pathwise status is then `Eq.trans` of per-edge T8 | `PW.StatusBridge.comp` | `Lara/PW/Status.lean` |
| Right-totality of the translation on program arguments (the `matched` clause, named) | `PW.Matched` | `Lara/PW/Status.lean` |
| Forward attack homomorphism is insufficient: T7 satisfies `Admits` and `forth`, and status flips | `Examples.PW.Status.t7_forth`, `t7_forward_hom_insufficient` | `Lara/Examples/PWStatus.lean` |
| The T7 target fails `matched` at `leaf l2`, directly and by T8's contrapositive | `Examples.PW.Status.t7_l2_mem`, `t7_unmatched`, `t7_not_statusBridge`, `t7_not_statusBridge_of_flip` | `Lara/Examples/PWStatus.lean` |
| Source context over the empty registry and its accepted worlds | `Examples.PW.Status.regEmpty`, `ctxS`, `wS1`, `wS2`; `unitS1_accepted`, `unitS2_accepted` | `Lara/Examples/PWStatus.lean` |
| Renamed context, vocabulary, policy, and its accepted worlds | `Examples.PW.Status.pR`, `qR`, `sR`, `ΓR`, `sigmaR`, `polR`, `ctxR`, `wR1`, `wR2`; `unitR1_accepted`, `unitR2_accepted` | `Lara/Examples/PWStatus.lean` |
| Renaming translation, leaf map, and structural bridge off the identity | `Examples.PW.Status.symR`, `leafMapR`, `bridgeR`; `symR_injective` | `Lara/Examples/PWStatus.lean` |
| Status-preserving bridges between the renamed worlds (`forth`/`back` on a real compiled edge) | `Examples.PW.Status.s1_r1_statusBridge`, `s2_r2_statusBridge` | `Lara/Examples/PWStatus.lean` |
| `justified`, `defeated`, and `gap` transport, each with both cells evaluated | `Examples.PW.Status.t8_justified_preserved`, `t8_justified_cells`, `t8_defeated_preserved`, `t8_defeated_cells`, `t8_gap_preserved`, `t8_gap_cells` | `Lara/Examples/PWStatus.lean` |
| `contested` transport, with both cells evaluated | `Examples.PW.Status.polS3`, `ctxS3`, `wS3`, `polR3`, `ctxR3`, `wR3`, `bridgeR3`; `unitS3_accepted`, `unitR3_accepted`, `s3_corr_diag`, `s3_r3_statusBridge`; `t8_contested_preserved`, `t8_contested_cells` | `Lara/Examples/PWStatus.lean` |
| The transported claim is genuinely renamed | `Examples.PW.Status.t8_renamed` | `Lara/Examples/PWStatus.lean` |
| Two-context bridge data, its accepted edge, every successor bridged, and the inhabited `[b]` cell at `defeated` | `Examples.PW.Status.bridgeDataR`; `r_edge_accepted`, `r_all_bridged`, `t8_box_defeated_r`, `t8_box_defeated_r_holds` | `Lara/Examples/PWStatus.lean` |
| Declared-attack translation (both stored terms translated, kind and position verbatim) and its all-or-nothing list lift through the #234 seam | `PW.trAttack`, `PW.trAttackList`; `PW.trAttackList_cons` | `Lara/PW/AttackTransport.lean` |
| Translation injectivity on support terms (substitution helper, mutual triple, equality reflection) | `PW.trSubst_inj`, `PW.trSupport_inj`, `PW.trSupportList_inj`, `PW.trSupportDis_inj`, `PW.trSupport_eq_iff` | `Lara/PW/AttackTransport.lean` |
| Positional navigation commutes with translation (`lookupDis` first-match, `subterm` at `prem`/`ques`; partial-map inversion and some-of-membership helpers) | `PW.trSupport_leaf`, `PW.trSupport_inst_inv`, `PW.lookupDis_mem`, `PW.lookupDis_trSupportDis`, `PW.trSupportList_some_of_mem`, `PW.trSupportDis_some_of_mem`, `PW.trSupport_subterm`, `PW.trSupport_subterm_some` | `Lara/PW/AttackTransport.lean` |
| Containment, attack closure, and declared-edge coverage are translation-invariant under injectivity | `PW.containsB_trSupport`, `PW.containsBList_trSupport`, `PW.containsBDis_trSupport`, `PW.trAttack_source`, `PW.attackClosureB_trAttack`, `PW.coveredB_trAttack` | `Lara/PW/AttackTransport.lean` |
| Prop-level corollaries for the two faces #238 names | `PW.Contains_trSupport`, `PW.AttackOcc_trSupport` | `Lara/PW/AttackTransport.lean` |
| **Attack bridge** — T8's attack hypotheses restated on declared `atts` — and the derivation of the index-level clauses | `PW.AttackBridge` (fields `admits`, `matched`, `atts_eq`); `PW.AttackBridge.toStatusBridge` | `Lara/PW/AttackTransport.lean` |
| The S2/R2 pair as an `AttackBridge` and its `StatusBridge` rederived from the source-language contract | `Examples.PW.Attack.leafMapR_injective`, `s2_r2_atts_transported`, `s2_r2_attackBridge`, `s2_r2_statusBridge_via_attacks` | `Lara/Examples/PWAttack.lean` |
| Negatives: attack-vocabulary gap refutes `atts_eq`; collapsing leaf map breaks `containsB` commutation (the `Function.Injective lm` boundary) | `Examples.PW.Attack.gapAttack`, `collapsedMap`; `gap_attack_undefined`, `collapsed_containsB_breaks` | `Lara/Examples/PWAttack.lean` |
| `ques`-position commutation pinned, computed and via the law | `Examples.PW.Attack.quesInstSrc`, `quesInstTgt`; `ques_position_computes`, `ques_position_law` | `Lara/Examples/PWAttack.lean` |

Executable `StatusBridge` decider (issue #239), `Lara/PW/StatusCheck.lean`
and `Lara/Examples/PWStatusCheck.lean`:

| Object | Lean declaration | File |
|---|---|---|
| `Corr`, `Admits`, the matched conjunct, `forth`, `back` as `Bool` scans, and the `StatusBridge` decider over them; the shared transport test | `PW.corrB`, `PW.admitsB`, `PW.matchedB`, `PW.forthB`, `PW.backB`, `PW.statusBridgeB`; `PW.transportsB` | `Lara/PW/StatusCheck.lean` |
| Bool/Prop reflection for the conjunct scans, and the range bound of a `true` `corrB` cell | `PW.corrB_iff`, `PW.admitsB_iff`, `PW.matchedB_iff`, `PW.transportsB_iff`; `PW.corrB_lt` | `Lara/PW/StatusCheck.lean` |
| One directed bisimulation scan over abstract index relations, sound and complete under a correlation bound and an edge-range bound; `forthB`/`backB` are its two orientations, each with named soundness and completeness | `PW.bisimScanB`, `PW.bisimScanB_sound`, `PW.bisimScanB_complete`; `PW.forthB_sound`, `PW.forthB_complete`, `PW.backB_sound`, `PW.backB_complete` | `Lara/PW/StatusCheck.lean` |
| Decider soundness and completeness; the checker decides `StatusBridge` exactly | `PW.statusBridgeB_sound`, `PW.statusBridgeB_complete`, `PW.statusBridgeB_iff` | `Lara/PW/StatusCheck.lean` |
| The three positive bridges re-established by one `decide` each | `Examples.PW.StatusCheck.s1_r1_decider`, `s2_r2_decider`, `s3_r3_decider` | `Lara/Examples/PWStatusCheck.lean` |
| Soundness turns a decider cell back into the Prop-level bridge | `Examples.PW.StatusCheck.s2_r2_statusBridge_via_decider` | `Lara/Examples/PWStatusCheck.lean` |
| The T7 negative through the decider: a `false` scan, refuted via completeness | `Examples.PW.StatusCheck.t7_decider_rejects`, `t7_not_statusBridge_via_decider` | `Lara/Examples/PWStatusCheck.lean` |
| T7 clause by clause: `matched` and `back` fail, `admits` and `forth` hold | `Examples.PW.StatusCheck.t7_matchedB_false`, `t7_backB_false`, `t7_admits_forth_hold` | `Lara/Examples/PWStatusCheck.lean` |
| Isolating negatives pinning `admitsB` and `matchedB` independently (eng review, decision 6A) | `Examples.PW.StatusCheck.s2_r1_admits_fails`, `s2_r1_matched_holds`, `s1_r2_matched_fails`, `s1_r2_admits_holds` | `Lara/Examples/PWStatusCheck.lean` |
| Isolating negatives pinning `forthB` and `backB` independently | `Examples.PW.StatusCheck.forthB_discriminates`, `backB_discriminates` | `Lara/Examples/PWStatusCheck.lean` |

**Not X** notes:

- `PW.AttackBisim` is **not** an isomorphism, and `PW.AFIso` is **not** the
  primitive. `AFIso.toBisim` consumes `maps`, `surj`, and `attack_iff` only;
  `inj` is recorded because it is what "isomorphism" means and is consumed
  by no proof. A surjective bounded morphism already suffices.
- `PW.StatusBridge.forth`/`back` are **not** conditions on declared attacks.
  They are index-level clauses on the compiled edge decider `Compile.edgeB`;
  deriving them from a correspondence of the programs' `atts` is deferred
  (freeze record §9 limitation 1). They also carry **no** `b ∈ F.args`
  premise, so an instance recovers in-rangeness itself via
  `(Compile.edgeB_faithful P).ranged`.
- `PW.SymMap.Injective` is **not** `Function.Injective` on the partial
  fields. It is injectivity-where-defined; total injectivity would force all
  out-of-vocabulary symbols to be equal.
- `PW.status_transport` is **not** a strengthening of T6. It takes
  `StatusBridge` and `SymMap.Injective` as additional hypotheses;
  `Examples.PW.t7_t6_boundary` still shows `Admits` alone flips status.
- `PW.claimSupport_corr` is **not** an assumed correspondence. The support-set
  correspondence is derived from the contract and the hypotheses for every
  translatable query; only `status_transport_of_corr` takes one as input.
- `PW.StatusBridge.comp` is **not** a path-indexed status theorem, and none
  is declared. Statuses are values, so pathwise status is `Eq.trans` of
  per-edge `status_transport`; the composition theorem is about the
  hypotheses. Its legs are in *path* order (`h₁` then `h₂`), unlike
  `StructuralBridge.comp B₂ B₁`.
- `PW.sat_status_iff_box` is **not** specific to `justified`. It holds at
  every `Status`; the executable cell happens to be at `defeated`.

## M4 Part A: fragment/linking calculus and contextual representation independence (issue #187)

Tracker #180. The design freeze is `docs/theory-m4-context-calculus-decision.md`;
the claim boundary is `docs/theory-m4-contextual-adequacy.md`. Every *theorem*
row is `lean/AxCheck.lean`-gated (sorry-free, standard trio, no
`native_decide`). Rows naming `Fragment`, `Context`, `link`, `obs`, `SideOk`,
`Admissible`, `AFMerge`, `CarrierMerge` name *definitions*, transitively
audited through the gated theorems that mention them.

| Object | Lean declaration | File |
|---|---|---|
| Fragments, interfaces, contexts, import environments | `Context.Fragment`, `Context.Interface`, `Context.Context`, `Context.ImportEnv` | `Lara/Context/Fragment.lean` |
| The structural merge of argument lists | `Context.dedupList`; `Context.mem_dedupList`, `dedupList_nodup`, `dedupList_eq_self` | `Lara/Context/Fragment.lean`, `Lara/Context/Link.lean` |
| The conclusion cache (inferred, because `link` runs before checking) | `Context.conclusionOf`, `Context.conclusionCache`; `Context.conclusionOf_eq_some_iff`, `mem_conclusionCache`; the bridge to the checker's cache (#226) `Context.conclusionCache_of_nodes`, `conclusionCache_eq_conflictCache`, `mem_conclusionCache_of_sub`, `link_some_inv`, `link_cache_bridge`, with `Check.conflictCache_conclusions` | `Lara/Context/Link.lean`, `Lara/Check/Program.lean` |
| Saturation: the attack a target admits, and the cross-boundary emission | `Context.attackFor`, `Context.crossAttsFrom`, `Context.crossAtts`; `Context.mem_crossAttsFrom`, `hasAttack_attackFor`, `crossAtts_spec`, `crossAtts_covers`/`crossAtts_covers'` | `Lara/Context/Fragment.lean`, `Lara/Context/Link.lean` |
| The **witnessed** link guard and its rejection classes (R-L1/R-L2/R-L3) | `Context.LinkSide`, `Context.LinkFault`, `Context.linkFault`, `Context.linkOk`; `Context.linkOk_eq_true_iff`, `idHygieneFault_none_iff`, `sigmaPolicyFault_none_iff`, `firstDup?_none_iff`, `firstMissing?_none_iff`, `firstShared?_none_iff` | `Lara/Context/Fragment.lean`, `Lara/Context/Link.lean` |
| Linking, the linked unit and Γ | `Context.link`, `Context.linkedUnit`, `Context.linkGamma`, `Context.linkGround`; `Context.link_eq_some`, `link_eq_none` | `Lara/Context/Fragment.lean`, `Lara/Context/Link.lean` |
| A side's well-formedness relative to the linked environment | `Context.SideOk`; `Context.SideOk.mono_gamma` | `Lara/Context/Link.lean` |
| Γ transport into the linked environment (the generic lemmas are public at their owning modules, #220/#228) | `Support.hasSupport_mono_gamma`, `Support.hasSupport_inst_root`, `Support.hasSupport_leaf_gamma`, `Attack.hasAttack_mono_gamma`, `Admission.buildGamma_append_of_some`, `buildGamma_append_ne`, `buildGamma_append_fresh`, `buildGamma_some_mem`; `Context.linkGamma_extends_left`, `linkGamma_extends_right` | `Lara/Support.lean`, `Lara/Attack.lean`, `Lara/Admission.lean`, `Lara/Context/Link.lean` |
| **Saturation correctness** — the linked attacks satisfy `AttackComplete` | `Context.link_attackComplete` | `Lara/Context/Link.lean` |
| Stage 2 of a link, from per-side data | `Context.signatureStage_link`, `argsWellSorted_link`, `groundWellSorted_append`, `termsWellSorted_iff_mem` | `Lara/Context/Link.lean` |
| **Linking respects checking** — a well-linked composition is accepted | `Context.link_checked` | `Lara/Context/Link.lean` |
| The fragment-relative carrier and AF (an open fragment has no `CheckedProgram`) | `Context.fragmentCarrier`, `Context.fragmentAF`, `Context.fragmentGamma`, `Context.fragmentGround`; `Context.fragmentAF_eq` | `Lara/Context/Fragment.lean`, `Lara/Context/Link.lean` |
| Re-indexing a fragment position into the linked program | `Context.linkedPos`, `Context.posOf`; `Context.linkedUnit_args_linkedPos_frag`/`_ctx`, `linkedPos_of_index` | `Lara/Context/Merge.lean` |
| **Node-merging morphisms of argumentation frameworks** (generic) | `Invariants.AFMerge`, `Invariants.CarrierMerge`; `AFMerge.iter_iff`, `AFMerge.grounded_iff`, `AFMerge.labelC_eq`, `AFMerge.statusC_eq`, `CarrierMerge.status_eq`; `Grounded.mem_grounded_iff_iter` | `Lara/Invariants/Merge.lean` |
| **The structural merge is semantically inert** (D3 discharged) | `Context.termCarrier`, `Context.checkerConcl`; `Context.dedup_carrierMerge`, `dedup_status_eq`, `compileUnit_eq_termCarrier`, `link_merge_status_eq`, `termCarrier_attack_eq_edgeB` | `Lara/Context/Merge.lean` |
| Context composition, its guard, and closure | `Context.composedContext`, `Context.compose`, `Context.composeFault`, `Context.composeOk`, `Context.residualImports`; `Context.composeOk_eq_true_iff`, `composed_declared`, `composed_args`, `composed_atts`, `composed_imports`, `composed_ownIds`, `linkOk_composed` | `Lara/Context/Fragment.lean`, `Lara/Context/Compose.lean` |
| Composition associates (guard, interface, material, remaining fields) | `Context.composeOk_assoc_left`/`_right`, `residualImports_assoc`, `compose_assoc_mem`, `compose_assoc_fields` | `Lara/Context/Compose.lean` |
| Detailed observation over exported conclusions (D4), separating incompatibility, checker rejection, and statuses | `Context.Observation`, `Context.obs`; `Context.obs_eq_of_ok` | `Lara/Context/Fragment.lean`, `Lara/Context/Equivalence.lean` |
| Contextual equivalence over detailed outcomes, admissibility, and the relabel's context side-condition | `Context.CtxEquiv`, `Context.Admissible`, `Context.FixesContext`; `Context.exists_accepted_of_admissible` | `Lara/Context/Equivalence.lean` |
| Fragment relabeling, and the guard's blindness to it | `Context.mapAssurFrag`, `Context.relabelEntry`; `Context.linkFault_mapAssurFrag`, `linkOk_mapAssurFrag` | `Lara/Context/Equivalence.lean` |
| **The one new lemma** — saturation commutes with a relabel | `Context.crossAttsFrom_map`, `Context.crossAtts_relabel`, `Context.conclusionCache_map` | `Lara/Context/Equivalence.lean` |
| **`link_relabel_commutes`** — the linked unit of the relabeled fragment is the relabeled linked unit | `Context.link_relabel_commutes` | `Lara/Context/Equivalence.lean` |
| Acceptance transports (stage 2 cannot see a certificate) | `Context.termWellSorted_mapAssur`, `argsWellSorted_map`, `signatureStage_map`, `attackComplete_map`, `covered_mapAssur`, `checkUnit_map`, `exists_accepted_relabel` | `Lara/Context/Equivalence.lean` |
| The carrier is relabel-invariant | `Context.nodes_conclusion_map`, `Context.compileUnit_map`, `Context.compileUnit_link_relabel` | `Lara/Context/Equivalence.lean` |
| **Contextual representation independence** (the M4 Part A headline) | `Context.backend_replacement_congruence` | `Lara/Context/Equivalence.lean` |
| The acceptance-profile generalization (D6, no relabel, no injectivity) | `Context.registry_swap_congruence`; identity-relabel lemmas `Context.mapAssur_id`, `mapAssurFrag_id`, `fixesContext_id` | `Lara/Context/Equivalence.lean` |
| Composite linkability from the halves (explicit cross-coverage — `compose` does not saturate; the boundary is witnessed, #229) | `Context.sideOk_composed`, `Context.admissible_composed`; `Examples.Linking.hostile_composite_not_sideOk`, `hostile_composite_not_admissible` | `Lara/Context/Compose.lean`, `Lara/Context/Equivalence.lean`, `Lara/Examples/Linking.lean` |
| Stability under embedding into a larger context | `Context.backend_replacement_congruence_composed`, `Context.fixesContext_composed` | `Lara/Context/Equivalence.lean` |
| Result 9 as the whole-program instance (cited, not re-derived) | `Context.whole_program_replacement` → `Erase.backend_replacement` | `Lara/Context/Equivalence.lean` |
| **Surface transport** (D1's corollary) | `Context.checkedAF_map`, `Context.surface_directAF_relabel`, `Context.surface_directAF_link` | `Lara/Context/Surface.lean` |
| **A certificate-bearing split, and a real backend swap**: the certified argument built relationally from `registry_exact_digest_accepts`, an unwrapping backend core, and the two witnesses that move an actual certificate | `Examples.Linking.certArg`, `certArg_checked`, `certAdmissible`, `renameCore`, `wrapCert`, `registryWrapped`, `certSwap`, `certSwap_injective`, `certSwap_preserving`, `cert_registry_swap_witness`, `cert_congruence_witness`, `cert_relabel_moves` | `Lara/Examples/Linking.lean` |
| Witnesses: located rejection faults, distinct incompatible/rejected outcomes, saturation, merge, gap-flip, four statuses, `CtxEquiv` negative, D6 pair, composition rejection and admissibility, composition not closed for linkability | `Examples.Linking.reject_duplicate_own_id`, `reject_id_clash`, `reject_unsatisfied_import`, `reject_unsatisfied_context_import`, `reject_sigma_mismatch`, `reject_policy_mismatch`, `obs_incompatible_id_clash`, `obs_rejected_signature`, `reject_compose_id_clash`, `compose_rejected`, `crossAtts_nonempty`, `crossAttsFrom_skips_strict_target`, `merge_fires`, `merge_obs_unchanged`, `obs_gap`, `obs_gap_flipped`, `obs_four_states`, `ctxEquiv_negative`, `obs_no_exports`, `admissible_split`, `link_checked_split`, `admissible_composite`, `registry_swap_witness`, `congruence_witness`, `compose_assoc_witness`; composition not closed for linkability (#229) `hostile_compose_ok`, `hostile_composite_links`, `hostile_left_admissible`, `hostile_right_admissible`, `hostile_composite_not_sideOk`, `hostile_composite_not_admissible` | `Lara/Examples/Linking.lean` |

**Not X** notes:

- `backend_replacement_congruence` is **not parametricity** (no relational
  quantification over related backends — #215) and **not full abstraction** (no
  logical relation; Part B is gated and unentered). A paper display must use
  *contextual representation independence*.
- The context quantifier is over **admissible** contexts satisfying
  `FixesContext`. `obs` distinguishes checker rejection from an observed status
  list and the acceptance hypothesis is forward-only, so the unconditional
  form would be false; see `docs/theory-m4-contextual-adequacy.md` §3.
- `link_checked` is **not** "linking always succeeds". It is the conditional
  that a well-linked composition of two well-formed sides is accepted;
  `Examples.Linking.admissible_split` discharges its premises on a concrete
  pair so the conditional is not vacuous.
- `dedup_status_eq` is **not** about `link` — it is about `termCarrier`.
  `link_merge_status_eq` is the statement at the linked program, and
  `compileUnit_eq_termCarrier` is what connects the two.
- The assurance-free witnesses (`congruence_witness`, `registry_swap_witness`)
  are *shape* witnesses only: their fragment declares no certificate, so
  `mapAssurFrag f` is the identity on it for every `f`. The witnesses that
  exercise the theorems are the certificate-bearing ones
  (`cert_congruence_witness`, `cert_registry_swap_witness`), where
  `cert_relabel_moves` proves the relabel is not the identity.
- `surface_directAF_relabel` is witnessed by
  `Lara.Examples.SurfaceTransport.surfaceTransport_directAF_eq`
  (`lean/Lara/Examples/SurfaceTransport.lean`, issue #227). The fixture avoids
  `native_decide` by authoring its `nd@1` certificate in kernel form — so
  `lowerNamed` short-circuits past the well-founded payload pass — and by
  hand-building `Checks` and `CoreObligations` from their relational
  constructors. Non-vacuity is guarded by `surfaceTransport_relabel_moves`
  (`output₂.unit.args ≠ output₁.unit.args`) and `surfaceTransport_inputs_differ`
  (`input₂ ≠ input₁`), without which `f = id` would satisfy every hypothesis.
- That first witness declares **no attacks**, so `checkedAF_map`'s edge half
  (`coveredB_relabel`) runs on `[]`. The attack-bearing witness is
  `Lara.Examples.SurfaceTransportAttack.surfaceTransportAttack_directAF_eq`
  (`lean/Lara/Examples/SurfaceTransportAttack.lean`, issue #258): three
  arguments and one declared rebut, so `coveredB_relabel` is applied to a
  one-element attack list. The certified argument is a *premise* of both attack
  endpoints rather than an endpoint itself — `Policy.WellFormed` forbids any
  contrary overlapping a strict-reachable conclusion, and the certified rule is
  strict — so `mapAssurAtt certSwap` moves the attack too. Guards:
  `surfaceTransportAttack_atts_nonempty`,
  `surfaceTransportAttack_relabel_moves_atts` and
  `surfaceTransportAttack_directAF_edge` (`directAF.attack 1 2 = true` on both
  sides), which together rule out a silent regression to the degenerate case.
- `surface_directAF_link`, the stronger sibling, is witnessed by
  `Lara.Examples.SurfaceTransport.surfaceTransport_link_directAF_eq`
  (`lean/Lara/Examples/SurfaceTransport.lean`, issue #255), on the same
  fixture. The two elaborated units are exhibited as the two sides of one link
  (`transport_unit_is_link`, `transport_unit_wrapped_is_link`) over
  `linkCtx`/`linkFrag`, with `transportLink_admissible` supplying the
  admissible context; the argument and attack correspondence is then *derived*
  from `link_relabel_commutes` rather than assumed. Non-vacuity:
  `surfaceTransport_link_relabel_moves_args`,
  `surfaceTransport_link_relabel_moves`, and
  `surfaceTransport_link_imports_nonempty` (the fragment genuinely imports the
  leaf the context declares). Two degeneracies of *that* fixture are recorded in
  `docs/theory-m4-contextual-adequacy.md` §4 and each has its own sibling: the
  context declares no arguments (so `FixesContext` is trivial) and the fixture
  declares no attacks (so the edge half is empty — the attack-bearing case is
  `SurfaceTransportAttack`, issue #258).
- The context-bearing link witness is
  `Lara.Examples.SurfaceTransportContext.surfaceTransportContext_link_directAF_eq`
  (`lean/Lara/Examples/SurfaceTransportContext.lean`, issue #264): the same
  `surface_directAF_link` over a context with a **non-empty** `C.frame.args`.
  The elaborated unit declares two core arguments split across the boundary —
  the context owns a plain defeasible `p ⊢ n` with `.none`, which `certSwap`
  fixes, and the fragment owns the #227 certified `p ⊢ q`, which `certSwap`
  moves — so `contextLink_fixesContext` is an equation over material the
  relabel could have touched. Guards:
  `surfaceTransportContext_ctx_args_nonempty` (`C.frame.args ≠ []` and the
  context's argument survives into the linked unit) and
  `surfaceTransportContext_fixes_is_substantive` (the same `certSwap` fixes the
  context's argument and moves the fragment's). `linkedUnit_of_empty_ctx` is
  unavailable here — a context argument makes `crossAtts` build both conclusion
  caches, through `certOkOf` on the kernel-opaque `nd` core — so the saturation
  is collapsed instead by `crossAtts_of_no_contraries`, which reads
  `contraryMatchB`'s `dp.contraries.any …` guard rather than the caches.
