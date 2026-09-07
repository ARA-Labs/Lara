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

## The surface corollary, witnessed (#227, 2026-09-07)

`Lara.Context.surface_directAF_relabel` shipped with documented hypotheses and
no instance, because every accepted surface fixture in
`lean/Lara/Examples/Surface.lean` is proved by `native_decide` and D9 bans
`Lean.ofReduceBool` from the audit. `lean/Lara/Examples/SurfaceTransport.lean`
(PR #257) closes that gap with a purpose-built pair.

The headline is `surfaceTransport_directAF_eq`: two accepted surface programs
differing only in one `nd@1` certificate related by
`Examples.Linking.certSwap` present the same framework. The statement is
**unconditional** — the two accepted units come from
`CoreObligations.checkUnit_complete`, not from hypotheses.

Non-vacuity, in the same spirit as `cert_relabel_moves` above:

- `surfaceTransport_relabel_moves` — the relabel is **not** the identity on the
  elaborated unit (`output₂.unit.args ≠ output₁.unit.args`).
- `surfaceTransport_inputs_differ` — the two surface programs are two programs,
  not one cited twice.
- `transport_relabel_moves_cert` / `transport_payloads_differ` — the
  certificate and the payload each genuinely move.

**Scope limit (issue #258).** The witnessed pair declares no attacks:
`transportElaborated` sets `resolvedAttacks := []`, so `checkedAF_map`'s edge
half — `coveredB_relabel` at `lean/Lara/Erase.lean:198`, called from
`lean/Lara/Context/Surface.lean:53` — is exercised on an empty attack list.
Nothing is unsound and every hypothesis is discharged, but the AF equality is
witnessed only in its degenerate one-node no-edge case. An attack-bearing
witness is #258; `surface_directAF_link`, the other half of the §4 gap, remains
#255.

### Gates (2026-09-07, commit `ae5b408`)

Run from a **wiped** build cache (`git clean -xdf lean/.lake`). The first run
of this table was contaminated: `SurfaceTransport` was outside the lake build
closure and the olean the audit consumed had been hand-built rather than
produced by `lake build`. `ae5b408` adds the missing `Lara.lean` import; the
outputs below are from the clean re-run. Verbatim.

```
$ cd lean && lake build
✔ [136/149] Built Lara.Examples.SurfaceTransport (485ms)
Build completed successfully (149 jobs).

$ cd lean && python3 ../scripts/check-axcheck-coverage.py AxCheck.lean $(find Lara -name '*.lean' | sort)
AxCheck coverage passed (2375 declarations).

$ cd lean && ../scripts/test-check-axioms.sh && python3 ../scripts/test_check_axcheck_coverage.py
All check-axioms tests passed.
Ran 2 tests in 0.044s
OK

$ cd lean && (set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
Axiom audit passed.
```

Job count 148 → 149: the one new job is the module itself, which `lake build`
had never compiled before this commit.

### Axiom footprint

34 theorems, all inside the standard trio. No `Lean.ofReduceBool`, no
`sorryAx`. Five depend on no axioms at all; ten on `propext` alone; the
remaining nineteen on the full trio.

```
'Lara.Examples.SurfaceTransport.kernelRef_eq_slot1' does not depend on any axioms
'Lara.Examples.SurfaceTransport.sxToSExpr_kernelPayload' depends on axioms: [propext]
'Lara.Examples.SurfaceTransport.transport_lower_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.firstNamedMarker_wrappedPayload' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_lower_wrapped' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_relabel_moves_cert' does not depend on any axioms
'Lara.Examples.SurfaceTransport.transport_payloads_differ' does not depend on any axioms
'Lara.Examples.SurfaceTransport.transport_certSwap_image' depends on axioms: [propext]
'Lara.Examples.SurfaceTransport.theoryDigestA_lowers' does not depend on any axioms
'Lara.Examples.SurfaceTransport.transport_cert_accepted' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_cert_accepted_wrapped' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_supported' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_supported_wrapped' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_freshness' depends on axioms: [propext]
'Lara.Examples.SurfaceTransport.transport_freshness_wrapped' depends on axioms: [propext]
'Lara.Examples.SurfaceTransport.transport_checksArgument' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_checksProgram_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_checksProgram_wrapped' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_expansions' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_gamma_leafP' depends on axioms: [propext]
'Lara.Examples.SurfaceTransport.transport_ruleLookup' depends on axioms: [propext]
'Lara.Examples.SurfaceTransport.transport_hasSupport' depends on axioms: [propext]
'Lara.Examples.SurfaceTransport.transport_cert_accepted_wrapped_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_args_kernel' depends on axioms: [propext]
'Lara.Examples.SurfaceTransport.transport_args_wrapped' depends on axioms: [propext]
'Lara.Examples.SurfaceTransport.transport_coreObligations_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_coreObligations_wrapped' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_checks_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_checks_wrapped' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_checkUnit_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.transport_checkUnit_wrapped' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.surfaceTransport_directAF_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Lara.Examples.SurfaceTransport.surfaceTransport_relabel_moves' depends on axioms: [propext]
'Lara.Examples.SurfaceTransport.surfaceTransport_inputs_differ' does not depend on any axioms
```

Rows with a wrapped `[propext,` in the raw output are shown joined; the audit
script normalizes multiline reports before extracting each list.
