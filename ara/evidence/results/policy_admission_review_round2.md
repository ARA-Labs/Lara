# Policy admission boundary — second-round review repairs

Follow-up to [`policy_admission_boundary.md`](./policy_admission_boundary.md). A
second independent review of branch `fix/77-policy-admission` returned one
critical and four important findings. All five were repaired at their source
(trace node `N120`); gates re-run at `N121`.

## Findings and repairs

1. **Critical — public admission bypass** (`src/Lara/Elaborate.hs`). The exported
   `elaborate` → `mkReplayId` → `mkCheckInput` → `runCheck` path accepted a source
   that `prepareSource` rejects as R8. The structural lowering moved to a new
   exposed escape-hatch module `Lara.Elaborate.Internal`; `Lara.Elaborate` now
   exports only the boundary (`prepareSource` / `runSourceCheck` and its
   projections). Tests and golden generators that study the lowering itself
   (`test/ElaborateSpec.hs`, `test/WorkedExamplesSpec.hs`) import the `.Internal`
   module explicitly, matching the `Lara.Strict.ND.Internal` convention.
2. **Important — located rejection discarded** (`runSourceCheck`). The function
   took `fst` of `runCheckWithPrune`, dropping the `Maybe LocatedRejection`; a
   policy-pruned R1 then rendered `"messages": []`, since the driver's message
   list is non-empty only for R13 and R9. `SourceResult` now retains the located
   rejection and the checked argument ids, exposed as
   `sourceResultLocatedRejection` / `sourceResultCheckedArgIds`, and
   `sourceResultJsonValue` renders `class` / `stage` / `constituent`. Constituent
   indices are named from the **checked** argument list — the checked unit itself
   is deliberately not exported, so a caller still cannot rebuild a pruned
   envelope and re-run it without the blocked-status overlay.
3. **Important — Lean carrier omitted unique argument ids**
   (`lean/Lara/Admission.lean`). A duplicate-`ArgId` witness compiled: retention is
   decided per argument row but attacks are filtered by endpoint id, so a
   surviving duplicate kept the id "present" after the resolved row was pruned,
   and `evaluateAdmission` retained an attack whose semantic source was gone.
   `AlignedAttacks` now carries `ids_nodup`. The wire decoder supplies it as a
   proof (`Lara.Driver.firstDup_none_nodup`, `Decoded.argIdsNodup`) instead of
   discarding its R14 boolean, and two new theorems make it load-bearing:
   `RawAttack.lookupArg_of_mem_nodup` and
   `Admission.retained_attack_source_retained`.
4. **Important — all-admit theorem scope overstated**. The
   `policy_all_admit_group_identity` docstring and the metatheory plan's paper
   claim and theorem 10 claimed verdict identity.
   The theorem proves the combined prune's component equalities plus
   `blockedQueries`; `policy_all_admit_checkUnit_identity` separately proves the
   checker's accept/reject outcome. The R13 preflight, the R9 group boundary, and
   the emitted public verdict (labels, statuses, evidence-blocked overlay) are
   outside the Lean admission model — their identity is Haskell conformance
   evidence (`prop_allAdmitSourceVerdictIdentity`), and the prose now says so.
5. **Important — differential failures suppressed diagnostics**
   (`scripts/admission-differential.sh`). A valid-but-wrong fixture oracle made
   both drivers exit 1 with explanatory stderr and empty stdout; the harness fell
   through to the "wrong outcome class" branch, printed an empty report, and the
   EXIT trap deleted the capture. The mismatch path now always prints both exit
   codes and both stderr streams.

## Verification (2026-08-06)

- `cabal test all --test-show-details=direct`: PASS (1/1 suites). New property
  **"admission pruned rejection keeps its located stage/constituent"** pins class
  `R1`, stage `support`, constituent `{argument a_bad, index 0}`, and empty
  `messages` — checked index 0 versus declared index 1, so it also pins that the
  constituent is named from the pruned list.
- `cd lean && lake build` (incl. `admission-driver`): PASS.
- `cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh`: PASS —
  standard trio only, no `sorryAx`, across the three added declarations.
- `scripts/differential.sh`: 436/436 positive, 54/54 negative (unchanged).
- `scripts/admission-differential.sh`: 20/20.
- **Adversarial check of repair 5**: `(leaf e_assumed)` → `(leaf e_wrong)` injected
  into `fixtures/admission/reject-first-leaf.sexp`. The harness reported
  `exit: haskell=1 lean=1`, "both drivers produced empty stdout", and both stderr
  streams including the computed-versus-expected outcome lines. Fixture restored
  with `git checkout`.
