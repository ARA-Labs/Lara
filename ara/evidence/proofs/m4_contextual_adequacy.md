# Evidence: Theory M4 Part A — contextual representation independence (#187, PR #218)

Gates run at commit `c61c91f` on branch `plan/m4-context-calculus`, from the
repository root. Verbatim outputs.

## Build

```
$ cd lean && lake build
Build completed successfully (138 jobs).
```

## Axiom audit

```
$ cd lean && (set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
'Lara.Examples.Linking.cert_relabel_moves_args' depends on axioms: [propext]
'Lara.Examples.Linking.cert_relabel_moves' depends on axioms: [propext]
Axiom audit passed.
EXIT: 0
```

At `c61c91f`, `AxCheck.lean` listed 1911 declarations across the library
(1725 reporting the standard trio, 186 axiom-free), including 204 M4 entries.
The audit checks only names already listed; review later found seven public
`@[simp]` theorems absent from that roster, so this run did not justify the
original universal-coverage claim. The review-fix rerun below supersedes it.

```
$ bash scripts/test-check-axioms.sh
All check-axioms tests passed.
```

### Review-fix rerun (2026-09-03)

```
$ python3 scripts/test_check_axcheck_coverage.py
..
Ran 2 tests in 0.146s
OK

$ python3 scripts/check-axcheck-coverage.py lean/AxCheck.lean \
    lean/Lara/Invariants/Merge.lean lean/Lara/Context/Fragment.lean \
    lean/Lara/Context/Link.lean lean/Lara/Context/Merge.lean \
    lean/Lara/Context/Compose.lean lean/Lara/Context/Equivalence.lean \
    lean/Lara/Context/Surface.lean lean/Lara/Examples/Linking.lean
AxCheck coverage passed (218 declarations).

$ cd lean && (set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
'Lara.Examples.Linking.cert_relabel_moves' depends on axioms: [propext]
Axiom audit passed.

$ cd lean && lake build
Build completed successfully (138 jobs).
```

`AxCheck.lean` now lists 1925 declarations across the library. The committed
coverage checker derives all 218 public theorem/lemma names from the named M4
modules and fails if any is absent from that roster; the axiom audit then
permits only `propext`, `Classical.choice`, and `Quot.sound`. Its regression
tests cover inline attributes, `mutual` blocks, nested namespaces and comments,
and private declarations and sections.

## Diff shape

```
$ git diff 424bd8f..HEAD --stat | tail -1
 15 files changed, 4659 insertions(+), 32 deletions(-)
```

The 32 deletions are the plan's Part A checkboxes and status banner, the M3
debt paragraph, and the `lean/Lara.lean` roster edit; every Lean change is an
insertion. No Haskell, CLI, wire, or corpus surface is touched.

## The headline

```lean
theorem backend_replacement_congruence
    (hf : Function.Injective f)
    (hpres : AssurPreserving f (certOkOf reg₁) (certOkOf reg₂))
    (hadm : Admissible reg₁ C F) (hfix : FixesContext f C) :
    obs reg₁ C F = obs reg₂ C (mapAssurFrag f F)
```

`lean/Lara/Context/Equivalence.lean`. The generalization with neither relabel
nor injectivity is `registry_swap_congruence` in the same module.

## Non-vacuity

The witnesses that exercise the theorem carry a real certificate
(`lean/Lara/Examples/Linking.lean`):

- `certAdmissible` — admissibility of a split whose fragment argument is
  `.inst rCertId [] [.leaf l1] [] [] (.cert ndId digestA slot1Cert)`, so it
  holds only because the registry accepts that certificate.
- `cert_congruence_witness` — the headline applied to `certSwap`, which wraps
  every `nd` certificate payload, against `registryWrapped`, the same registry
  read through a core that unwraps before replaying.
- `cert_relabel_moves` — the relabel is **not** the identity on the fragment.
- `cert_registry_swap_witness` — D6 at two genuinely different registries on
  the same certificate-bearing fragment.

The earlier assurance-free fixtures (`congruence_witness`,
`registry_swap_witness`) are retained as shape witnesses only: a fragment of
bare leaves has no certificate, so `mapAssurFrag f` is the identity on it for
every `f`.

### Debt clearance (2026-09-04)

Gates run at commit `14b9e34` on branch `claude/m4-debts-clearance-af1b56`
after closing #219, #220, #226, #228, #229 (and #222 as moot). Verbatim
outputs.

```
$ cd lean && lake build Lara
Build completed successfully (85 jobs).

$ cd lean && lake build
Build completed successfully (140 jobs).

$ cd lean && (set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
'Lara.Examples.Linking.cert_relabel_moves' depends on axioms: [propext]
Axiom audit passed.

$ python3 scripts/check-axcheck-coverage.py lean/AxCheck.lean \
    lean/Lara/Invariants/Merge.lean lean/Lara/Context/Fragment.lean \
    lean/Lara/Context/Link.lean lean/Lara/Context/Merge.lean \
    lean/Lara/Context/Compose.lean lean/Lara/Context/Equivalence.lean \
    lean/Lara/Context/Surface.lean lean/Lara/Examples/Linking.lean
AxCheck coverage passed (224 declarations).

$ python3 scripts/test_check_axcheck_coverage.py
Ran 2 tests in 0.124s
OK

$ bash scripts/test-check-axioms.sh
All check-axioms tests passed.
```

The audit reported 2013 declarations. The new entries and their axiom sets:

```
'Lara.Admission.buildGamma_append_fresh' depends on axioms: [propext, Quot.sound]
'Lara.Support.hasSupport_inst_root' depends on axioms: [propext]
'Lara.Support.hasSupport_mono_gamma' depends on axioms: [propext]
'Lara.Attack.hasAttack_mono_gamma' depends on axioms: [propext]
'Lara.Check.conflictCache_conclusions' depends on axioms: [propext, Quot.sound]
'Lara.Context.conclusionCache_eq_conflictCache' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Context.link_cache_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.Linking.hostile_compose_ok' depends on axioms: [propext]
'Lara.Examples.Linking.hostile_composite_links' depends on axioms: [propext]
'Lara.Examples.Linking.hostile_left_admissible' depends on axioms: [propext, Quot.sound]
'Lara.Examples.Linking.hostile_right_admissible' depends on axioms: [propext, Quot.sound]
'Lara.Examples.Linking.hostile_composite_not_sideOk' depends on axioms: [propext, Quot.sound]
'Lara.Examples.Linking.hostile_composite_not_admissible' depends on axioms: [propext, Quot.sound]
```

Diff shape: `14 files changed, 452 insertions(+), 227 deletions(-)`; the
deletions are the private lemma copies in `Lara/Update.lean`,
`Lara/Consistency.lean`, and `Lara/Context/Link.lean` and the `DecidableEq`
block in `Lara/Context/Fragment.lean`. No Haskell, CLI, wire, or corpus
surface is touched, and no freeze tag moves.
