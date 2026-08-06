# Policy Admission Metatheory, Semantic Differential, and Paper Plan

> **Dependency:** This plan is the formal companion to [`2026-08-05-policy-admission-calculus.md`](./2026-08-05-policy-admission-calculus.md). Start after the runtime plan's source API, audit encoding, and focused fixtures are stable. Do not change the runtime contract from this plan without revising both plans.

**Goal:** Mechanize policy-relative context construction, prove its composition with existing quarantine non-promotion, validate the Haskell production admission/prune primitives byte-for-byte against executable Lean definitions, exercise the real Haskell source/checker seam separately, and update the paper with claims that match the audited declarations.

**Paper claim:** LARA derives its checking context from a deterministic, policy-relative admission judgment. Accepted admission excludes quarantined evidence and dependent structure; rejected admission has no checked unit; all-admit policy reproduces the group-only pipeline — proved in Lean for the prune, the blocked queries, and the checker's accept/reject outcome, and validated in Haskell for the emitted verdict bytes. Composed with quarantine non-promotion, a public `justified` result cannot be manufactured by withholding inadmissible evidence.

**Compatibility boundary:** No change to `lara-core@0.1`, `Unit`, core `RejectClass`, raw replay identity, frozen corpus, or four-state semantics. The test-only source-admission encoding is not a production wire format.

---

## 1. What already exists

| Existing component | Reuse |
|---|---|
| `Lara.Presentation` | Closed Lean `LeafKind`, `Provenance`, and `Admission` vocabulary. |
| `Lara.Groups` | Group consistency, quarantined leaves, structural leaf use, and leaf/argument filtering. |
| `Lara.Driver.RawAttack` / `resolveAttacks` | Existing raw endpoint identity and raw-to-semantic resolution. Factor rather than duplicate. |
| `Lara.BlockedProgram.selectAligned` | Load-bearing raw/resolved lockstep filter. |
| `Lara.BlockedProgram` | Declared-index frameworks, blocked seed, compact embedding, and production non-promotion theorem. |
| `Lara.AxCheck` | Transitive axiom audit entry point. |
| `scripts/differential.sh` | Core-wire oracle harness; keep source admission in a dedicated sibling script. |
| `/Users/yfhe/overleaf/ara/lara/plan/lean-name-map.md` | Paper-to-Lean declaration map. |

**Prior learning applied:** grammar and prose are not implementation evidence. The concrete `.lara` parser/elaborator remains validated by Haskell tests; Lean verifies the semantic source judgment only.

---

## 2. Formal boundary

### 2.1 Two context layers

Name both layers explicitly:

```text
Gamma_policy = declared leaves whose policy decision is admit
Gamma_checked = Gamma_policy minus members quarantined by inconsistent groups
```

Then state exact membership theorems:

```text
l in Gamma_policy
  iff l is declared and decisionFor Pi meta(l) = admit

l in Gamma_checked
  iff l in Gamma_policy and l is not group-quarantined
```

Do not use “subject to later quarantine” inside an `iff` theorem.

### 2.2 Declarative judgment and evaluator

Define both:

1. a declarative source-admission relation corresponding to the displayed rules;
2. an executable evaluator with the runtime ordering and canonical audit.

```text
Pi |- <M, U> => reject R8(l)

Pi |- <M, U> => accept
      <U_declared, U_checked, Q_policy, Q_group, audit>
```

Prove evaluator/relation correspondence in both directions. `admission_deterministic` is then a theorem that the relation is functional, not the trivial observation that a function returns one value.

The relation must encode first-rejected-leaf precedence in declaration order and require valid admission keys and unique metadata alignment.

### 2.3 Raw and semantic attacks

Endpoint-safe filtering cannot use semantic `Lara.Attack.Attack` values alone. Distinct argument IDs may carry equal support terms.

Factor the raw vocabulary from `Lara.Driver` into a shared module, for example `lean/Lara/RawAttack.lean`:

```text
RawAttack: source ArgId, target ArgId, position
resolveAttacks: declared raw args -> RawAttack list -> semantic Attack list
selectAligned: keep RawAttack -> raw list -> resolved list -> retained resolved list
```

The admission carrier keeps raw declarations and resolved semantic attacks aligned. Filtering uses raw endpoint IDs; proofs consume the aligned resolved sublist.

```text
raw attacks -------- resolve --------> semantic attacks
     |                                      |
 endpoint filter                         selectAligned
     |                                      |
kept raw attacks ---- resolve/align ----> kept semantic attacks
```

Prove the retained resolved list is the exact `selectAligned` projection of the declared resolved list. Reuse the attack-subset and non-promotion lemmas from `BlockedProgram`; do not reintroduce support-term equality as identity.

### 2.4 Canonical audit

Mirror the runtime contract:

- leaf rows in declaration order;
- non-empty causes;
- policy cause first;
- every inconsistent group containing the leaf contributes one cause in group declaration order;
- argument and raw/semantic attack projections in declaration order;
- one leaf row even when policy plus several groups cause quarantine.

Cross-group membership is valid. Exactness includes multiplicity and order, not set equality only.

---

## 3. Executable Lean model

Create `lean/Lara/Admission.lean` with:

- metadata aligned to unique declared `LeafId`s;
- total `decisionFor` with default `admit`;
- duplicate-key and duplicate-LeafId validity;
- policy-admitted and checked contexts;
- first policy-rejected leaf;
- policy and group quarantine seeds;
- one combined leaf/argument/raw-attack prune;
- raw/resolved `selectAligned` attack filtering;
- canonical audit projections;
- declarative `AdmissionJudgment`;
- executable `evaluateAdmission`;
- accepted and rejected outcome types where rejected outcomes carry no checked unit.

Use closed constructors from `Lara.Presentation`. Test-only encoding tags must be centralized in the test driver, not repeated in proofs or production code.

---

## 4. Theorems

Prove without `sorry` and register every public result in `lean/AxCheck.lean`.

1. **`evaluateAdmission_iff_judgment`**: the evaluator returns an outcome exactly when the declarative judgment relates the same input and outcome.
2. **`admission_deterministic`**: the declarative judgment is functional.
3. **`policy_admitted_iff`**: exact membership in `Gamma_policy`.
4. **`checked_admitted_iff`**: exact membership in `Gamma_checked`, including group exclusion.
5. **`policy_quarantined_absent`**: policy-quarantined leaves are absent from checked `Gamma`.
6. **`policy_quarantined_arg_excluded`**: retained arguments use no policy-quarantined leaf.
7. **`retained_attack_endpoints`**: every retained raw attack names retained endpoints.
8. **`retained_attacks_selectAligned`**: checked semantic attacks are exactly the raw-endpoint-filtered aligned projection of declared resolved attacks.
9. **`admission_audit_exact`**: leaf causes, removed arguments, and removed attacks equal the combined prune projections with canonical multiplicity/order.
10. **`policy_all_admit_group_identity`**: all-admit policy equals the existing group-only pipeline on the combined prune (seeds, checked leaves, retained arguments and attacks, keep predicates) and on `blockedQueries`. **`policy_all_admit_checkUnit_identity`** extends this to the checker's own accept/reject outcome. Neither states verdict identity: the R13 preflight, the R9 group boundary, and the emitted public verdict (labels, statuses, evidence-blocked overlay) are outside the Lean admission model, and their identity is Haskell conformance evidence (Task 5), not a proof. Do not restate these theorems as "verdict".
11. **`more_restrictive_cannot_add_structure`**: admit-to-quarantine changes cannot add leaves, arguments, or attacks. State that claim statuses are non-monotonic.
12. **`source_reject_no_checked_unit`**: an R8 outcome carries no checked unit and has no core-check branch.
13. **`source_justified_nonpromotion`**: compose admission with `checked_production_justified_nonpromotion_of_not_blocked`; published `justified` in the checked source result implies justified in the reinstated declared framework.

Theorem names may change during proof engineering, but statements and scope may not weaken without updating this plan and the paper.

---

## 5. Implementation tasks

### Task 1: Factor shared raw attack identity

**Files**

- Create: `lean/Lara/RawAttack.lean`
- Modify: `lean/Lara/Driver.lean`
- Modify: `lean/Lara/BlockedProgram.lean`
- Modify: `lean/Lara.lean`
- Modify: `lean/AxCheck.lean`

**Work**

1. Move `RawAttack`, endpoint access, and reusable raw/resolved alignment definitions out of `Driver.lean` without changing decoder behavior.
2. Reuse `selectAligned` or factor it into the shared module when that avoids a dependency cycle.
3. Prove resolution/filter alignment and retain existing `BlockedProgram` theorem statements.
4. Verify that the refactor alone is behavior- and axiom-neutral before adding admission.

### Task 2: Mechanize admission relation and evaluator

**Files**

- Create: `lean/Lara/Admission.lean`
- Modify: `lean/Lara/Groups.lean` only for reusable combined-prune lemmas
- Modify: `lean/Lara/BlockedProgram.lean` only for source-admission composition
- Modify: `lean/Lara.lean`
- Modify: `lean/AxCheck.lean`

**Work**

1. Implement both context layers, validity, canonical causes, and first-reject semantics.
2. Define the declarative judgment and executable evaluator.
3. Carry raw and resolved attacks through the accepted carrier.
4. Prove the thirteen properties above.
5. Connect non-promotion to the exact compact `Compile.checkedAF`, `completeClaimFor`, retained-index embedding, and source blocked-query predicate.
6. Keep source invalidity, R8, group quarantine, and group R9 distinct.

**Gate**

```bash
cd lean
lake build
lake env lean AxCheck.lean | ../scripts/check-axioms.sh
```

The audit input must be the real `AxCheck.lean` output. Only `propext`, `Classical.choice`, and `Quot.sound` may appear where genuinely required.

### Task 3: Add dedicated Haskell/Lean semantic admission differential

**Files**

- Create: `fixtures/admission/`
- Create: `scripts/check-admission.hs`
- Create: `lean/AdmissionDriver.lean`
- Create: `scripts/admission-differential.sh`
- Modify: `test/DifferentialSpec.hs`
- Modify: `.github/workflows/ci.yml`

**Canonical fixture schema**

Encode only test data:

- leaf metadata;
- admission rows;
- declared semantic unit;
- raw and resolved attacks or enough canonical input to derive both;
- adapter validity or admission outcome;
- canonical audit.

Do not add this schema to `lara-core@0.1` or replay identity.

**Cases**

1. explicit admit and default admit;
2. duplicate admission key invalidity;
3. duplicate `LeafId` / metadata-alignment invalidity;
4. policy reject and first-reject ordering;
5. direct and nested dependency pruning;
6. raw source- and target-endpoint attack pruning;
7. distinct argument IDs with equal support terms, proving identity is not term equality;
8. policy plus one and multiple group causes in canonical order;
9. group evaluation on declared leaves;
10. attacker-removal audit, with affected/unaffected public statuses covered separately through Haskell `prepareSource` / `runSourceCheck`;
11. all-admit group-only identity;
12. malformed harness values that cannot silently drop metadata.

Require byte-identical Haskell/Lean semantic admission outcomes and audit encodings. This test-only adapter does not exercise the `.lara` parser, elaborator, or final public verdict; `test/AdmissionSpec.hs` covers the real Haskell source/checker seam. Every executable Lean definition used by the proofs needs a focused conformance case.

Run `scripts/admission-differential.sh` in CI as its own named step beside the core differential.

### Task 4: Update the paper after theorem names stabilize

Paper repository: `/Users/yfhe/overleaf/ara/lara`.

**Files**

- Create: `figures/admissionrules.tex`
- Modify: `src/language.tex`
- Modify: `src/semantics.tex`
- Modify: `src/metatheory.tex`
- Modify: `tables/mechanization.tex`
- Modify as needed: `src/abstract.tex`, `src/intro.tex`, `src/conclusion.tex`
- Modify: `plan/lean-name-map.md`

**Work**

1. Add the declarative admission judgment before support checking and define the total default.
2. State that elaboration recovers dependencies before admission prunes them.
3. Explain policy-admitted versus final checked contexts.
4. State evaluator/judgment correspondence, admission safety, raw-endpoint exactness, all-admit identity, and source non-promotion using final AxCheck names.
5. Extend the mechanization table as a source-boundary theorem family; do not renumber or overstate the twelve frozen core results.
6. Preserve the verified-versus-validated caveat: Lean proves the semantic model; differential tests validate Haskell; neither proves the whitespace-sensitive parser or source extraction.
7. Claim deterministic policy-relative context construction, not evidence truth or byte-level evidence verification.

**Paper gate**

```bash
cd /Users/yfhe/overleaf/ara/lara
latexmk -pdf main.tex
```

Require no undefined references/citations and no material overfull boxes. Every paper theorem name must resolve to an AxCheck-audited declaration.

### Task 5: Full formal compatibility gates

Run from a clean verification worktree after Tasks 1-3:

```bash
cabal test
(cd lean && lake build)
(cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
bash scripts/differential.sh
bash scripts/admission-differential.sh
bash scripts/replay.sh
bash scripts/test-replay-tamper.sh
python3 scripts/test_freeze_bundle.py
git diff --check
```

Also verify:

- the raw-attack factoring leaves existing Lean driver outputs unchanged;
- corpus/mutant regeneration changes no committed core or frozen bytes;
- `measurements/frozen/`, bundles, and existing goldens have no diff;
- Haskell `AdmissionSpec` proves all-admit production source verdict bytes match the legacy checker and pins quarantine-sensitive blocked statuses;
- test-adapter validity and audit outcomes agree byte-for-byte across Haskell and Lean;
- no `sorry`, `admit`, `axiom`, `partial`, or unaudited public theorem is introduced.

---

## 6. Failure modes

| Failure | Prevention | Evidence |
|---|---|---|
| Equal support terms collapse attack identity | raw ArgId endpoints + `selectAligned` | equal-term/distinct-id differential fixture |
| Displayed judgment differs from evaluator | correspondence theorem | AxCheck + evaluator fixtures |
| Multi-group causes are lost or reordered | canonical cause construction | multi-group byte golden |
| Haskell and Lean accept different validity domains | duplicate-key/LeafId differential cases | dedicated script + CI |
| Core and source protocols are conflated | dedicated source fixture schema and script | separate CI steps |
| Paper overstates parser/extractor proof | verified-versus-validated caveat | paper review + name map |
| Theorem name drifts after paper edit | paper waits for AxCheck stabilization | `lean-name-map.md` + build |

---

## 7. NOT in scope

- Re-implementing the Haskell runtime repair; this plan consumes its stable contract.
- Changing raw `.sexp` or `lara-core@0.1` wire/rejection semantics.
- Proving the concrete `.lara` parser, file IO, or Haskell elaborator correct.
- Proving evidence truth, scientific adequacy, provenance honesty, or byte extraction.
- `lara-evidence@0.1`, manifests, artifact extractors, or the broader #78 inventory.
- Treating quarantined evidence as false or constructing attacks from provenance.
- Open mandatory-obligation acceptance; that remains a separately versioned core question.
- New deployment/distribution artifacts.

---

## 8. Parallelization

After the runtime contract is stable:

| Lane | Work | Depends on |
|---|---|---|
| A | Factor Lean raw attack identity, then admission relation/proofs | runtime types and audit contract |
| B | Define test-only canonical fixture schema and Haskell encoder | runtime types and audit contract |
| C | Prepare paper locations and terminology only; no theorem names | runtime contract |

Execution:

```text
Runtime plan merged
      |
      +--> Lane A: raw attack factor -> admission proofs
      |
      +--> Lane B: fixture schema -> Haskell fixture encoder
      |
      +--> Lane C: paper staging notes only

Lane A + Lane B merge
      -> Lean encoder + admission-differential.sh + CI
      -> stabilize AxCheck names
      -> paper edits and build
      -> full compatibility gates
```

Conflict flags:

- Lane A owns `lean/Lara/*` and `lean/AxCheck.lean`.
- Lane B owns `fixtures/admission/`, test-only Haskell code, and the new script until integration.
- Paper edits occur in a separate repository and wait for theorem-name stabilization.

Suggested code-repository commits:

```text
refactor(lean): share raw attack identity and alignment
feat(lean): mechanize policy admission judgment
test: add policy admission Haskell-Lean differential
```

Paper changes remain one separate paper-repository commit.

---

## 9. Acceptance criteria

- [ ] Lean defines a declarative admission judgment and executable evaluator with proved correspondence.
- [ ] Policy-admitted and final checked contexts have separate exact membership theorems.
- [ ] Raw endpoint identity and resolved semantic attacks remain aligned through pruning.
- [ ] Audit exactness includes every policy/group cause, multiplicity, and canonical order.
- [ ] R8 outcomes carry no checked unit.
- [ ] All-admit policy is identical to the existing group-only pipeline.
- [ ] More restrictive policy cannot add structural material, without claiming status monotonicity.
- [ ] Source `justified` non-promotion composes with the exact production blocked path.
- [ ] All public theorems are `sorry`-free and AxCheck-audited.
- [ ] Dedicated Haskell/Lean semantic admission differential runs locally and in CI.
- [ ] Valid, invalid, quarantine, reject, equal-term attack identity, and multi-group audit cases agree byte-for-byte.
- [ ] Haskell source tests exercise `prepareSource` / `runSourceCheck`, all-admit exact verdict bytes, and quarantine-sensitive blocked statuses.
- [ ] The paper uses final theorem names and accurately separates proved semantics, semantic differential validation, and production source tests.
- [ ] Existing core, replay, corpus, and frozen bytes remain unchanged.
