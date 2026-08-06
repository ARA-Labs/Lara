# Policy Admission Runtime Conformance Plan

> **Reviewed scope decision (2026-08-05):** Split the original 37-path code/proof/paper program into two linked delivery units. This plan closes issue #77 with the source-runtime contract, Haskell implementation, tests, and compatibility gates. The dependent formalization, Haskell/Lean source differential, and paper changes live in [`2026-08-05-policy-admission-metatheory.md`](./2026-08-05-policy-admission-metatheory.md).
>
> This split changes delivery shape, not final coverage. The formalization plan may start only after this plan's source API, audit encoding, and runtime fixtures are stable.

**Goal:** Make every `.lara` path enforce the policy's `admit` / `quarantine` / `reject` table before core checking, preserve conservative public reporting after quarantine, and leave raw `lara-core@0.1` behavior byte-identical.

**Issue:** #77.

**Compatibility boundary:** `lara-core@0.1`, `Unit`, core `RejectClass`, raw `.sexp`, replay identity, the Lean core checker, frozen corpus, and four-state semantics remain unchanged. R8 remains a source-level semantic rejection, not a new core rejection constructor.

---

## 1. What already exists

Reuse these components. Do not build parallel versions.

| Existing component | Role in this change |
|---|---|
| `Lara.Syntax` admission parser/printer | Keeps concrete tag spelling and source syntax. |
| `Lara.Elaborate` declared-leaf elaboration | Reconstructs full support trees before admission so dependencies are known. |
| `Lara.Blocked.Prune` | Binds one declared `Unit` to its own checked view. Generalize its seed; do not introduce a second prune carrier. |
| `Lara.Blocked.supportUsesLeaf` | Finds direct, nested-premise, and discharge dependencies. |
| `Lara.Blocked.blockedQueries` | Prevents attacker removal from publishing promoted `justified` results. |
| `Lara.Driver.runCheck` | Remains the raw `.sexp` entry point. Its R13 → R9 → core behavior is unchanged. |
| `Lara.Negatives.admissionReject` | Canonical in-memory N7 R8 fixture. Promote it into the executable admission suite. |
| `test/CliSpec.hs` | Real-process exit/stdout/stderr contract tests. |
| `test/BlockedSpec.hs` | Existing group-quarantine and non-promotion conformance. |

`Lara.Policy.lookupAdmission` is not retained as a second public path. Move total lookup and duplicate-key validation into `Lara.Admission`, migrate callers, and delete the old export without an alias.

**Prior learning applied:** `lara_driver_level_rejects_bypass_locate` (confidence 9/10, 2026-08-01). R8, like R13/R9, is selected before `checkUnit`; it needs its own source diagnostic rather than `Diagnostics.locate`.

---

## 2. Source contract

### 2.1 Admission decision

For a declared leaf `l`:

```text
decide_Pi(l) = table[(kind(l), provenance(l))] when present
             = admit                              otherwise
```

The table is valid only when every `(LeafKind, Provenance)` key occurs once. Omitted and unmatched rows default to `admit`. Validation happens before leaf decisions, so row order never acquires semantic meaning.

Source leaf identifiers must also be unique. A duplicated `LeafId` makes metadata alignment ambiguous and is a source-invalidity error.

### 2.2 Outcome taxonomy

```haskell
data PreparedSource
  = SourceRejected AdmissionRejection
  | SourceAccepted SourceCheckInput

prepareSource
  :: Sigma
  -> Program
  -> Policy
  -> Either SourceInvalid PreparedSource
```

Required distinctions:

- `Left SourceInvalid`: malformed or inconsistent source boundary, including duplicate admission keys, duplicate `LeafId`, elaboration failure, and replay-construction invalidity. CLI exit `2`, empty stdout, deterministic stderr.
- `Right (SourceRejected r8)`: valid program and policy; the policy rejects the first matching leaf in declaration order. CLI exit `1`, empty stdout, exactly one deterministic R8 stderr line.
- `Right (SourceAccepted input)`: replay-bound, unforgeable source input for `runSourceCheck`.

`R8` is a valid source judgment result, not a generic error. It names the leaf, kind, provenance, and matched row.

### 2.3 Hidden carrier

`SourceCheckInput` has a hidden constructor. It binds:

- replay identity from the same `Program` and `Policy`;
- the structurally elaborated declared `Unit`;
- the policy quarantine seed;
- the final declared/checked `Prune` derived from that unit;
- the canonical admission audit.

Read-only accessors may expose views. No public function may accept independently supplied declared and checked units, replay identity, or audit.

The legacy presentation chain is removed:

```text
elaborate -> sourceCheckInput -> runCheck
```

All presentation callers migrate to:

```text
prepareSource -> SourceRejected | SourceAccepted -> runSourceCheck
```

Keep `runCheck :: CheckInput -> Verdict` unchanged for raw core input. Do not add compatibility wrappers, aliases, or deprecated exports.

### 2.4 CLI protocol

R8 deliberately creates a source-only exception to the current core-reject output shape:

| Outcome | Exit | stdout | stderr |
|---|---:|---|---|
| accepted source | 0 | core verdict + newline | audit lines only when nonempty |
| core/R13/R9 rejection | 1 | core verdict + newline | existing boundary diagnostic when applicable |
| source R8 | 1 | empty | exactly one R8 diagnostic |
| source invalidity | 2 | empty | exactly one invalidity diagnostic |

No second source wire format is added in this change.

---

## 3. Data flow and precedence

```text
.lara text + co-located policy
            |
            v
  parse Program / Policy
            |
            v
  validate policy identity
  validate unique admission keys
  validate unique source LeafIds
            |
            v
  elaborate full declared Unit
  against every declared leaf
            |
            v
  decide leaves in declaration order
       /                    \
 first reject            admit/quarantine
      |                         |
      v                         v
 SourceRejected R8       policy quarantine seed
 exit 1, stderr only            |
                                v
                     bind replay identity
                                |
                                v
                    runtime replay preflight
                         /             \
                       R13             pass
                                        |
                                        v
                      group consistency on DECLARED leaves
                           /                         \
                  RejectOnConflict R9          quarantine/default
                                                    |
                                                    v
                               union policy + group seeds once
                                                    |
                                                    v
                               Prune(declared, checked) + audit
                                                    |
                                                    v
                                checkUnit on checked view only
                                                    |
                                                    v
                            blockedQueries from the same Prune
                                                    |
                                                    v
                                SourceResult(verdict, audit)
```

Observable precedence is:

```text
source invalidity > R8 > replay R13 > group R9 > core rejection
```

Pure preparation may compute immutable data eagerly, but no lower-precedence outcome may be published when a higher-precedence one applies.

Group consistency always reads the original declared leaf table. Policy quarantine must not turn a group member into a spurious missing-member conflict or hide a real inconsistency.

Add a compact version of this diagram to `Lara.Admission` and to the source-driver boundary comment. Diagram maintenance is part of future pipeline changes.

---

## 4. Admission and audit model

### 4.1 Module ownership

Create `src/Lara/Admission.hs` as the only owner of:

- admission-table validation;
- total `decisionFor` lookup;
- policy quarantine and first-reject selection;
- admission causes and audit construction;
- pure R8 and audit diagnostic renderers.

`Lara.Reporting` remains limited to incomplete support alternatives and claim reports. Do not add source-admission rendering there.

`Lara.Elaborate` owns `prepareSource` and the hidden `SourceCheckInput` orchestration. Structural elaboration remains private to the safe source entry point. `Lara.Replay` retains the raw `CheckInput` vocabulary and no longer exports the old presentation helper.

### 4.2 Combined prune

Generalize the existing `Prune` producer with an explicit policy seed:

```text
policy seed
   union
inconsistent-group members
   -> one ordered quarantine set
   -> one checked Unit
   -> one blocked calculation
```

Use private `Map` / `Set` indexes for admission lookup and membership checks. Preserve all observable order by filtering the original policy, leaf, argument, attack, and group lists.

Do not recompute removed material in the reporting layer.

### 4.3 Canonical audit

```haskell
data AdmissionCause
  = PolicyQuarantine
  | GroupQuarantine GroupId

data AdmissionAudit = AdmissionAudit
  { aaLeaves  :: [(LeafId, NonEmpty AdmissionCause)]
  , aaArgs    :: [ArgId]
  , aaAttacks :: [Attack]
  }
```

Constructors remain hidden; expose read-only accessors.

Canonical order:

1. leaf rows follow source leaf declaration order;
2. every row has at least one cause;
3. `PolicyQuarantine` comes first when present;
4. every inconsistent group containing the leaf contributes one `GroupQuarantine` cause, once, in group declaration order;
5. removed arguments and attacks follow their original declaration order;
6. one leaf quarantined by policy and several groups still appears as one audit row.

Cross-group membership is valid. The audit records every causing group rather than rejecting the source.

---

## 5. Implementation tasks

### Task 1: Freeze the runtime source contract

**Files**

- Create: `docs/policy-admission-calculus-decision.md`
- Modify: `docs/spec.md`
- Modify: `docs/lara-surface-grammar.md`
- Modify: `docs/comparison-rit-lara.md`
- Modify: `plans/2026-08-04-rit-informed-evidence-admission.md`

**Work**

1. Record total default-admit lookup, duplicate-key and duplicate-LeafId invalidity, R8/R13/R9/core precedence, combined pruning, audit canonicality, and the R8 CLI exception.
2. Correct text that implies removing only `Gamma(l)` routes a dependent term to `gap`; production prunes dependent arguments before core checking.
3. Distinguish source R8, group R9, and core R1.
4. Link the older evidence-admission sketch to this plan and the companion metatheory plan.
5. State that byte-level `lara-evidence@0.1` work under #78 remains gated.

### Task 2: Add failing source-admission tests

**Files**

- Create: `test/AdmissionSpec.hs`
- Modify: `test/Spec.hs`
- Modify: `test/ElaborateSpec.hs`
- Modify: `test/BlockedSpec.hs`
- Modify: `test/CliSpec.hs`
- Modify: `src/Lara/Negatives.hs`
- Modify: `lara.cabal`

**Pure cases**

1. Omitted and unmatched rows admit by default.
2. Explicit admit preserves the leaf and dependent graph.
3. Duplicate admission keys produce source invalidity before leaf decisions.
4. Duplicate source `LeafId` values produce source invalidity before metadata alignment.
5. `Lara.Negatives.admissionReject` executes as the canonical first-leaf R8 golden.
6. Quarantine removes direct, nested-premise, and discharge dependencies.
7. Attacks with a removed source or target are removed; unrelated attacks survive in order.
8. Policy and group quarantine union once.
9. One leaf with policy plus multiple group causes has one canonical audit row.
10. Group consistency is computed on declared leaves even when a member is policy-quarantined.
11. Removing the only attacker publishes `evidence-blocked`; an unaffected query keeps its ordinary status.
12. Audit leaf, argument, and attack projections are exact and declaration ordered.

**Real CLI matrix**

- duplicate admission key: exit 2, empty stdout, exact deterministic stderr;
- duplicate `LeafId`: exit 2, empty stdout, exact deterministic stderr;
- R8: exit 1, empty stdout, one exact R8 stderr line;
- accepted quarantine: exit 0, verdict stdout, canonical audit stderr;
- combined defects pin `invalid > R8 > R13 > R9 > core` by removing one higher-precedence defect at a time;
- existing A/B/S1 `.lara` cases retain exact stdout and empty audit stderr.

Use falsification checks: deleting duplicate validation, dependency pruning, raw-endpoint filtering, R8 short-circuit, declared-table group evaluation, or blocked overlay must fail the intended test for the intended reason.

### Task 3: Implement the safe source path

**Files**

- Create: `src/Lara/Admission.hs`
- Modify: `src/Lara/Policy.hs`
- Modify: `src/Lara/Elaborate.hs`
- Modify: `src/Lara/Blocked.hs`
- Modify: `src/Lara/Driver.hs`
- Modify: `src/Lara/Replay.hs`
- Modify: `src/Lara/Negatives.hs`
- Modify: `app/Main.hs`
- Modify: `src/Lara/RunningExample.hs`
- Modify: `test/CorpusUnitsSpec.hs`
- Modify: `test/ElaborateSpec.hs`
- Modify: `test/ReplaySpec.hs`
- Modify: `test/WorkedExamplesSpec.hs`
- Modify: `scripts/check-corpus-unit.hs`
- Modify: `scripts/gen-corpus-units.hs`
- Modify: `scripts/gen-worked-examples.hs`
- Modify: `lara.cabal`

**Work**

1. Add unique `LeafId` validation beside existing source argument/group validation.
2. Elaborate full support terms against all declared leaves before admission.
3. Implement total lookup and duplicate-key validation in `Lara.Admission`; remove `Lara.Policy.lookupAdmission`.
4. Add `PreparedSource`, `SourceInvalid`, `AdmissionRejection`, hidden `SourceCheckInput`, and `SourceResult` with exhaustive mappings.
5. Generalize `Prune` with one explicit policy seed; evaluate groups on declared leaves and prune once.
6. Build canonical `NonEmpty` audit causes and pure source diagnostic renderers.
7. Add `prepareSource` and `runSourceCheck`; remove the legacy presentation chain and migrate every listed caller.
8. Keep `runCheck`, raw `CheckInput`, raw `.sexp`, and core verdict encoding unchanged.
9. Use private `Map` / `Set` indexes while preserving source-order outputs.
10. Add and maintain compact pipeline diagrams in the source-boundary modules.

### Task 4: Runtime compatibility and freeze gates

Run from a clean verification worktree:

```bash
cabal test
bash scripts/differential.sh
bash scripts/replay.sh
bash scripts/test-replay-tamper.sh
python3 scripts/test_freeze_bundle.py
git diff --check
```

Also verify:

- all former presentation callers compile only through `prepareSource` / `runSourceCheck`;
- no exported compatibility wrapper can bypass admission;
- examples A/B/S1 produce their exact pre-change core input and verdict bytes;
- raw `.sexp` R1, R13, R9, replay, and core verdict behavior are unchanged;
- corpus and mutant regeneration leaves committed bytes unchanged;
- `measurements/frozen/`, bundles, and existing core goldens have no diff;
- changed files build under `-Wall` with no new warnings.

---

## 6. Failure modes

| Failure | Handling | Test | User-visible result |
|---|---|---|---|
| Duplicate admission key | `SourceInvalid` before lookup | pure + CLI | exit 2, empty stdout, exact stderr |
| Duplicate source `LeafId` | `SourceInvalid` before metadata map | pure + CLI | exit 2, empty stdout, exact stderr |
| Policy-rejected leaf | first declaration-order R8 | N7 + CLI + precedence | exit 1, empty stdout, one stderr line |
| Quarantined dependency reaches core | impossible after combined prune | nested/dependency falsification | accepted gap/blocked result, never R1 |
| Group evaluated after policy prune | forbidden; group reads declared leaves | adversarial group matrix | no spurious or hidden R9 |
| Removed attacker promotes a claim | blocked closure demotes label to conditional | existing + policy fixture | `evidence-blocked`, never published `justified` |
| Audit recomputed from another unit | hidden carrier prevents construction | API cutover + exact golden | one deterministic audit |
| Legacy caller bypasses admission | old exports removed | full `cabal test` compile | compile failure during migration, no runtime bypass |

No silent failure remains in the new source branches.

---

## 7. NOT in scope

- Lean admission definitions, theorems, AxCheck, and source differential: companion metatheory plan after this API stabilizes.
- Paper edits: companion plan and separate paper commit after theorem names stabilize.
- Byte-level evidence checkers, manifests, extraction, or `lara-evidence@0.1`: gated by #78.
- New core wire fields, core rejection constructors, or replay-identity components.
- Treating quarantined evidence as false or constructing attacks from provenance.
- Changing grounded semantics or the four core statuses.
- Accepting submitted arguments with open mandatory obligations; that remains a `lara-core@0.2` refreeze question.
- Criterion performance lab; `TODOS.md` already defers it until argumentation frameworks exceed roughly 1,000 arguments.
- New binary/package/container distribution; this changes the existing `lara` library and CLI only.

---

## 8. Delivery and parallelization

This runtime plan is sequential because contract, tests, carrier, driver, and CLI share the same boundary modules:

```text
contract docs
    -> failing tests
    -> Admission + source carrier
    -> driver/CLI/caller cutover
    -> runtime compatibility gates
```

Do not parallelize structural and behavioral edits across worktrees. The formal companion can begin in a separate worktree only after the runtime source types, audit encoding, and fixtures are stable.

Suggested commits:

```text
docs: freeze policy admission source contract
test: pin policy admission runtime semantics
fix(#77): enforce policy admission before core checking
```

---

## 9. Acceptance criteria

- [ ] No `.lara` path treats explicit `quarantine` or `reject` as `admit`.
- [ ] Omitted/unmatched rows default to `admit`.
- [ ] Duplicate admission keys and duplicate source `LeafId`s fail deterministically as source invalidity.
- [ ] R8 short-circuits before replay, groups, and core checking.
- [ ] R8 exits 1 with empty stdout and exactly one diagnostic.
- [ ] Quarantine removes the leaf, every dependent argument, and every attack with a removed endpoint.
- [ ] Group consistency reads declared leaves; policy/group quarantine share one `Prune` and blocked calculation.
- [ ] Multi-cause audits are non-empty, exact, deduplicated, and canonical.
- [ ] Policy-driven attacker removal cannot publish a promoted `justified` result.
- [ ] Every presentation caller uses the hidden source carrier; no legacy bypass remains.
- [ ] All-admit source artifacts preserve existing core and verdict bytes.
- [ ] Raw `.sexp`, open-obligation, replay, and frozen-measurement behavior remain unchanged.
- [ ] The companion metatheory plan is linked but not required to merge this runtime repair.

## GSTACK REVIEW REPORT

**Runs / Status / Findings**

| Run | Status | Findings |
|---|---|---:|
| Scope challenge | Resolved | Split runtime issue #77 from dependent formalization/differential/paper work |
| Architecture | Resolved | 7 |
| Code quality | Resolved | 8 |
| Tests | Resolved | 5 |
| Performance | Resolved | 1 |
| Outside voice | Absorbed | 5 raised; 4 were new, 1 confirmed the multi-group audit test |

**Total unique findings:** 21, all incorporated into the two linked plans.

**Critical gaps:** 0 unresolved. The outside review found one critical raw-attack identity gap; the companion plan now factors and carries raw `ArgId` endpoints beside resolved semantic attacks.

**Lake Score:** 11/11 coverage-bearing recommendations chose the complete option. No accepted decision silently reduced behavior, error, test, proof, differential, or paper coverage.

**Test Plan:** `/Users/yfhe/.gstack/projects/EYH0602-lara/yfhe-fix-77-policy-admission-eng-review-test-plan-20260805-213026.md`

**Task Artifact:** `/Users/yfhe/.gstack/projects/EYH0602-lara/tasks-20260805.jsonl`

**Outside voice:** Independent review completed. Its surviving findings are explicit in the companion plan: raw/resolved attack alignment, cross-group audit multiplicity, one mandatory `admission-differential.sh` command, a declarative relation with evaluator correspondence, and promotion of `Lara.Negatives.admissionReject` into the runtime suite.

**VERDICT: APPROVED FOR IMPLEMENTATION**

**NO UNRESOLVED DECISIONS**
