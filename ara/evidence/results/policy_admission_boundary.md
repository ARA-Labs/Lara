# Policy admission boundary (source conformance + mechanization)

## Result

The trusted `.lara` source boundary now enforces the policy admission table
(`admit` / `quarantine` / `reject`) before core checking, with the
invalid > R8 > R13 > R9 > core precedence, one canonical combined
policy/group prune, and an exact canonical audit (issue #77, plan
`2026-08-05-policy-admission-calculus.md`). The dependent metatheory plan
(`2026-08-05-policy-admission-metatheory.md`) is delivered in full:

- **Lean raw-attack refactor** (`lean/Lara/RawAttack.lean`): `RawAttack`,
  `endpoints`, `lookupArg`, `resolveAttacks`, and `selectAligned` factored
  out of the wire driver; `resolve_filter_commute` proves filtering by raw
  endpoint id commutes with resolution (identity is never support-term
  equality).
- **Admission judgment** (`lean/Lara/Admission.lean`): the declarative
  `AdmissionJudgment` and executable `evaluateAdmission` mirror the production
  admission/prune primitives, require exact ordered metadata/leaf alignment,
  and accept semantic attacks only through `AlignedAttacks`, whose proof field
  records the successful resolution of the declared raw attacks. They derive
  both context views from one checked leaf table and construct the canonical
  audit. The audited theorem family includes evaluator/judgment
  correspondence, determinism, accepted raw/resolved alignment, exact
  policy/final checker contexts, policy-quarantined exclusion,
  retained-endpoint and retained-semantic-attack subset properties, audit
  exactness with non-empty causes, all-admit group-only structure and actual
  `checkUnit` outcome identity, restrictiveness,
  reject-carries-no-checked-unit, and source `justified` non-promotion composed
  with the production blocking theorem.
- **Exact semantic differential** (`fixtures/admission/MANIFEST`,
  `scripts/check-admission.hs`, `test/Lara/AdmissionFixture.hs`,
  `lean/Lara/AdmissionDriver.lean`, `scripts/admission-differential.sh`):
  one manifest pins the exact 20-file set, all four outcome classes, and
  per-driver codec diagnostics. The corpus has nine accepted outcomes, four
  source-invalid outcomes (including combined-invalidity precedence and
  swapped metadata order), two R8 rejections, and five codec rejections
  (unknown kind, malformed nested expected outcome, wrong `expected` tag,
  trailing metadata field, and trailing outer section). Every executable
  semantic outcome and audit is byte-identical across the test-only Haskell
  adapter and proved Lean evaluator; both adapters reject malformed expected
  payloads before evaluation.
- **Production source/checker coverage** (`test/AdmissionSpec.hs`) is
  separate from that semantic differential: it invokes
  `prepareSource` / `runSourceCheck`, proves all-admit source verdict bytes
  equal the frozen raw checker, and pins quarantine-sensitive
  `evidence-blocked` versus unaffected public statuses. The differential
  does not claim `.lara` parser/elaborator or final public-verdict equivalence.

## Verification (2026-08-06)

- `cabal test all --test-show-details=direct`: PASS (1/1 suites; 230
  registered properties).
- `cd lean && lake build` (incl. `admission-driver` exe): PASS.
- `cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh`: PASS
  (standard trio only; 24 admission + 3 monotonicity + 5 raw-attack
  declarations audited).
- `scripts/differential.sh`: positive 436/436; negative 54/54 (unchanged —
  the raw-attack refactor and driver-main move are behavior-neutral).
- `scripts/admission-differential.sh`: 15/15 semantic outcomes byte-identical
  and 5/5 malformed fixtures rejected at both codec boundaries.
- `scripts/replay.sh bundles/walking-skeleton`: PASS byte-for-byte.
- `scripts/test-replay-tamper.sh`: PASS.
- `python3 -m unittest scripts/test_freeze_bundle.py -v`: PASS (4/4).
- `git diff --check`: clean; no committed core, replay, corpus, frozen, or
  golden bytes changed.
