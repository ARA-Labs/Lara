# Executable ND adapter verification — 2026-07-24

- **Provenance**: ai-executed
- **Grounds**: C03, C05
- **Implementation**:
  `lean/Lara/ND.lean`, `lean/Lara/Strict.lean`, `lean/Lara/Examples.lean`,
  `src/Lara/Strict/ND.hs`, `test/StrictSpec.hs`

## Verified claims

- The exact submitted symbolic `CertRef` is decoded and inferred; replay performs no
  existential proof search.
- `ndReplay = true` iff the submitted certificate decodes and has the requested
  declarative type.
- Source Atom encoding is injective after normalization. Lean proves
  `decodeAtomKey (encodeAtomKey a) = some a`; no generated display parser is trusted.
- Resolved backends append a digest's fixed theory encodings after premise encodings.
- Lean and Haskell agree on exact bytes for empty, delimiter-bearing, non-ASCII,
  nullary, nested, different-arity, and reordered-argument fixtures.
- The A/N/S/C/L frame vocabulary is a closed `FrameTag` sum in both
  implementations. Encoding and decoding share one render/parse table; Lean
  proves `FrameTag.parse_toString`, and the Haskell golden-vector gate checks
  the same round trip.
- Unknown tags are rejected universally in Lean and by generated Haskell
  properties; every Formula/Cert constructor has one-shorter and one-longer
  malformed fixtures.
- Generated non-canonical natural strings are rejected as certificate indices;
  replay fixtures distinguish both application-child failure directions and
  both successful and non-false abort cases.
- Lean regressions pin injective encoding when predicate and arity are fixed
  but an argument term differs, plus equal encoding of numeric spellings
  identified by the canonicalizer.
- All six Lean atom-key/decoder/replay matrices are active `#guard` build gates,
  so a false conformance fixture now fails `lake build`.

## Gates

```text
cd lean && lake build                         PASS
cd lean && lake env lean AxCheck.lean        PASS
AxCheck axiom set                             {propext, Classical.choice, Quot.sound}
cabal build all                              PASS
cabal test all --test-show-details=direct    PASS (30 property groups, 100 cases each)
git diff --check                             PASS
```
