# M5 — mutation suite + worked cases (tracker #48, T1 + T4)

Branch `feat/m5-mutation-suite-worked-cases`. Scope: T1 (seeded mutation
generators) and T4 (worked cases) of issue #48. T2/T3/T5/T6 follow separately.

## T4 — worked cases

The existing suite (E1, E2, E3, A, B, S1) already jointly spans all four
statuses and all three attack kinds (`prop_coverageMatrix`). Three cells are
structurally absent and are what the paper's worked-case section needs:

- **E4 — reinstatement**: a claim stays `justified` *while attacked*, because
  its attacker is itself defeated. Two contexts on policy `empirical-v2`:
  - Context R: `a_r` (controlled_experiment) vs `a_rn` (null_result) in the
    completeness-mandated mutual rebut; `d_sr` undercuts `a_rn.rule` via the
    new `exception null_result : selective_reporting(M, Q, D)`. Grounded:
    `d_sr` in ⇒ `a_rn` out ⇒ `a_r` in ⇒ `c_r` justified-under-rebut,
    `c_rn` defeated.
  - Context U: `n_ng` undermines `a_u.external_validity.leaf`; `n_rr`
    (concl `refuted_replication`, new one-directional
    `contrary refuted_replication(M,Q,D) not_generalizes(M,Q,D)`) undermines
    `n_ng.leaf`. Grounded: `n_rr` in ⇒ `n_ng` out ⇒ `a_u` in ⇒ `c_u`
    justified-under-undermine. The one-directional contrary is the point:
    a symmetric pair would force the reverse edge (attack completeness is
    arg-conclusion-level, `firstMissingConflictInfo`) and collapse the
    reinstatement into a cycle.
- **E5 — contested beyond rebut, and gap amid attacks**: three contexts:
  - Context V: mutual undermine 2-cycle `m_ng ⇄ m_g` (both directions of
    `generalizes`/`not_generalizes` declared ⇒ both edges mandated), with
    `m_ng` also undermining `a_v.external_validity.leaf` ⇒ `a_v` undec ⇒
    `c_v` contested via undermine.
  - Context W: mutual undercut 2-cycle via new rules `shift_report` (concl
    `distribution_shift`, `exception shift_report : miscalibrated(M,Q,D)`)
    and `miscalibration_report` (concl `miscalibrated`,
    `exception miscalibration_report : distribution_shift(M,Q,D)`);
    `w_shift` also undercuts `a_w.rule` ⇒ `c_w` contested via undercut.
    Undercut cycles are voluntary (exceptions don't participate in the
    completeness scan) — the worked case documents that asymmetry.
  - Context G: `c_g` with no argument ⇒ gap, coexisting with attacks.

Policy `empirical-v2` = `empirical-v1` + the two rules, three exceptions, one
contrary above. All rules defeasible ⇒ R12-clean. Wire-up: add both dirs to
`scripts/gen-worked-examples.hs` and `test/WorkedExamplesSpec.hs`
(`examplePolicies` + per-example props), extend `prop_coverageMatrix` with the
new cells (justified-under-attack, contested-via-undercut/undermine,
gap-with-attacks-present).

## T1 — seeded mutation generators

New library module `src/Lara/Mutate.hs` (base + containers only; hand-rolled
SplitMix64 PRNG, committed seed) + thin writer `scripts/gen-mutants.hs` +
`test/MutationSpec.hs`.

Design:
- Bases: the eight accept-verdict worked-example anchors
  `examples/{A,B,E1–E5,S1}/example.core.sexp` (decoded `CheckInput`s). The
  already-rejecting R1–R3 anchors are excluded — a second defect would make
  the specified class ambiguous. The constructed rebut-cycle family
  (`cycle-rebut-*`) mutates no anchor: it is built independently and carries
  base `-` in the manifest. Operators enumerate all applicable sites in a
  base; the seeded PRNG picks a bounded sample per (base, operator).
- Operators → expected outcome (spec §10.1 mutation table):
  - wrong-formula/premise → R4; wrong-formula/subst-domain → R3;
    discharge-answer swap → R6 (open-obligations family)
  - undeclared-leaf ref → R1; hidden-policy-extension/rule ref → R1;
    hidden-policy-extension/contrary-on-strict → R12
  - bad-attack-target/occurrence-kind → R10; bad-attack-target/unlicensed →
    R11
  - open-obligation (drop discharge of mandatory question) → R5
  - assurance misuse (`trusted` on a defeasible instance) and certificate
    theory/allowlist swap → R7; allowlisted-cert payload corruption and
    duplicate/unknown replay backend selection → R13
  - group ≢ escalation injection → R9
  - cycles → NOT a reject: constructed seeded N-cycle rebut family, expected
    accept with all-undec labels / contested statuses
  - codec corruption → R14-family: exit 2, empty stdout (structured
    corruptions of the S-expression envelope)
- Output: canonical `printSExpr` bytes under `fixtures/mutants/` (verdict
  mutants) and `fixtures/mutants/malformed/` (codec mutants), plus
  `fixtures/mutants/MANIFEST.tsv` with columns (file, base, family, operator,
  expected, hs-diagnostic, lean-diagnostic) — the last two are the codec
  rows' per-driver deletion-sensitivity pins; the seed is global
  (`mutationSeed` in `Lara.Mutate`), not a manifest column.
  `scripts/differential.sh` discovers both mutant halves from the manifest
  (each required non-empty, files ⇔ rows exact), never by glob.
- `test/MutationSpec.hs`: per-manifest-row expected verdict via `runCheck`;
  regeneration freshness (committed bytes = re-derived bytes, the seeded
  reproducibility guard); coverage assertion: every executable reject class
  {R1,R3,R4,R5,R6,R7,R9,R10,R11,R12,R13} + codec negatives + a
  contested-by-cycle accept are each witnessed by ≥1 generated mutant.
- Lean side: no new metatheory — the generator is corpus tooling, not a
  frozen definition; Lean soundness coverage is the existing driver +
  differential harness, which cross-checks every committed mutant.

## Experiment record (2026-08-01)

Generated suite: **148 mutants** over 8 accept bases (A, B, E1–E5, S1), seed
20260801, every one verified at generation time against `runCheck` /
`decodeCheckInputFile` — zero specification mismatches on the first full
generation run. Per-outcome counts (also in `fixtures/mutants/README.md`):

| expected | count | | expected | count |
| --- | --- | --- | --- | --- |
| reject-R1 | 20 | | reject-R9 | 7 |
| reject-R3 | 7 | | reject-R10 | 8 |
| reject-R4 | 6 | | reject-R11 | 7 |
| reject-R5 | 6 | | reject-R12 | 8 |
| reject-R6 | 6 | | reject-R13 | 17 |
| reject-R7 | 7 | | codec-reject | 45 |
| accept-all-contested (cycles) | 4 | | | |

All 11 executable rejection classes are exercised by generated mutants, plus
the codec negatives and the specified-status cycle family. This is the
rejection-class half of the T1 exit criterion; the other half — generators
over corpus units, and generated mutants exercising every status and attack
kind — stays open until the T2 corpus units exist (#48 remains partially
open on T1).

Cross-driver differential (`scripts/differential.sh`, Lean as oracle):
**positive pass=146 fail=0** (byte-exact stdout + exit code, includes all 103
verdict mutants and the new E4/E5 anchors), **negative pass=54 fail=0**
(9 hand-written + 45 generated codec mutants, both drivers exit 2 with empty
stdout). `cabal test all` green, including the three new `MutationSpec`
properties (specified outcomes, seeded reproducibility, coverage) and the
extended `prop_coverageMatrix` (all nine attack-kind × target-label cells,
gap-amid-attacks).

Findings worth keeping:
- The checker's attack completeness is arg-conclusion-level
  (`firstMissingConflictInfo`), so a symmetric contrary pair FORCES mutual
  attack edges. E4's undermine-reinstatement is only expressible with a
  one-directional contrary; E5's undermine cycle is forced by the symmetric
  pair; undercut cycles are voluntary (exceptions are outside the
  completeness scan). E4 context X vs E5 context W differ by exactly one
  voluntary undercut edge — reinstatement vs contested.
- Certificate theory-digest tampering lands in **R7**
  (`CertifierUnallowlisted`), not R13: R13 is reachable only through payload
  corruption of an allowlisted cert (replay reject) or the replay preflight
  (duplicate/unknown backend). The mutation suite pins this boundary.
