# Environment

- **Language/runtime**: Haskell — GHC 9.14.1, cabal 3.16.1.0 (via ghcup). GHC2021 language edition.
  The mechanization is **Lean 4** (settled; v4.32.0 via elan, Lake project in `lean/`) — result 11
  (`nf`/`≡`) is already machine-checked there. The eventual untrusted front-end is Python (added at
  Phase 3 / Phase E).
- **Framework**: `base`, `containers`; QuickCheck for the property suite. No heavy dependencies —
  the trusted core is deliberately small.
- **Hardware**: developer workstation (Darwin/arm64, aarch64-osx build target). No GPU; n/a for a
  theory/checker artifact.
- **Data sources**: the evaluation corpus (not part of this build) is `AmberLJC/ara-paperbench`
  (32 ARAs, 231 claims) plus the `ARA-Labs/Agent-Native-Research-Artifact` format repo (which ships
  `rigor-reviewer`, the named baseline). See `docs/corpus-map.md`.
- **Key dependencies**: `base >=4 && <5`, `containers`, `QuickCheck` (test suite).
- **Protocols**: `cabal build all` (library + demo); `cabal run lara` (LP-seed demo); `cabal test`
  (property suite). Build discipline and module dependency order in `docs/engineering-plan.md`.
- **Random seeds**: QuickCheck default (100 cases per property); not pinned — properties are laws
  expected to hold for all inputs.

## Reproducing the implemented layer

```sh
# from the repo root
cabal build all      # library + demo executable
cabal test           # runs test/Spec.hs + test/PropSpec.hs (14 properties)
```

All 14 properties pass on GHC 9.14.1 (see `evidence/status/test_status.md`): 6 from the LP-seed
`Spec.hs` and 8 from the `Lara.Prop` `PropSpec.hs`.

## Reproducing the mechanized layer (result 11)

```sh
# needs elan/lean/lake on PATH (installed to ~/.elan; toolchain pinned in lean/lean-toolchain)
cd lean
lake build          # builds Lara.Prop + Lara (~1s each)
```

`lean/Lara/Prop.lean` machine-checks the `nf`/`≡` laws (result 11 / C01): equivalence relation,
decidability, idempotence, no-argument-reordering. No `sorry`/`admit`; every main theorem depends on
at most `propext`. See `lean/README.md`.
