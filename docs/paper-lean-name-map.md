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
all rows are `lean/AxCheck.lean`-gated (sorry-free, standard trio).

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
