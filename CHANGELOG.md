# Changelog

All notable changes to Lara are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/), and versions follow the rules
in [AGENTS.md](AGENTS.md#versioning).

## [Unreleased]

## [0.3.8] - 2026-10-14

### Added

- Inquiry outer contracts `process-input 1`, `process-result 1` and
  `process-error 1`, with a Lean reference runner and fixtures (#42).
- Checked-source inquiry analyses in Lean: finite source alternatives, witness
  audit, exact stability/sensitivity/minimal-assumption results and
  source-impact certificates, behind the `inquiry-input 1` wrapper (#47).
- `lara inquiry FILE`: a native Haskell inquiry implementation with full
  input/result/error codecs, and the `make inquiry-conformance` parity gate (#48).
- Lean proof that `maxSearchSteps` bounds every admissible search (#56).
- Ville's inequality without a horizon for nonnegative supermartingales (#57).
- e-LOND and LORD++ FDR control over complete ordered ledgers (#58).

### Changed

- LORD++ FDR control now assumes only independence of each null p-value, not
  a full product law (#59).

### Fixed

- Compiled Lean sensitivity no longer traverses the declared-slot powerset;
  corrective input-review, runner and approval checks (#52).

## [0.3.0] - 2026-10-10

### Added

- Research-process semantics (`lean/Lara/Process/`,
  [`docs/theory-process.md`](docs/theory-process.md)): when a record that omits
  part of what happened still entitles a claim (#41).

`v0.3.0` is tagged retroactively on `2ed05d8`, whose version files still read
`0.2.0`.

## [0.2.0] - 2026-10-09

### Added

- Belief Hoare Logic in Lean: derivation soundness, scoped relative
  completeness, calibrated exact finite statistical methods and executable
  rule checking (#34).
- Artifact composition: warrant bound to source and evidence, dependency loss
  and safe rebinding (#34).
- `lara check` reports open mandatory holes as a located gap (#12).
- The certified-leaf checker witness is enforced for evidence (#19).

### Changed

- Reviewed evidence is frozen and observation ids are disambiguated (#21).

## [0.1.0] - 2026-09-22

### Added

- First public release: the Haskell checker and `lara` CLI for the Lara v0.1
  language (`lara-core@0.2`, `lara-syntax@0.10`), its Lean 4 mechanization and
  the frozen evaluation corpus (#3).

[Unreleased]: https://github.com/ARA-Labs/Lara/compare/v0.3.8...HEAD
[0.3.8]: https://github.com/ARA-Labs/Lara/compare/v0.3.0...v0.3.8
[0.3.0]: https://github.com/ARA-Labs/Lara/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/ARA-Labs/Lara/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/ARA-Labs/Lara/releases/tag/v0.1.0
