# Checker test status

- **Source**: `cabal test` on the LARA repo (test/Spec.hs + test/PropSpec.hs), GHC 9.14.1 / cabal 3.16.
- **As of**: 2026-07-21 (commit f811575 onward).
- **Grounds**: C01 (the `Lara.Prop` properties).

## Verbatim runner output

```
== valid derivations check
+++ OK, passed 100 tests.
== sum monotonicity
+++ OK, passed 100 tests.
== check introspection
+++ OK, passed 100 tests.
== unknown constant rejected
+++ OK, passed 100 tests.
== apply non-implication rejected
+++ OK, passed 100 tests.
== apply mismatch rejected
+++ OK, passed 100 tests.
== prop ≡ reflexive
+++ OK, passed 100 tests.
== prop ≡ symmetric
+++ OK, passed 100 tests.
== prop ≡ transitive
+++ OK, passed 100 tests.
== prop ≡ is nf-equality
+++ OK, passed 100 tests.
== prop nf idempotent
+++ OK, passed 100 tests.
== prop no argument reordering
+++ OK, passed 100 tests.
== canonNum variants collapse
+++ OK, passed 100 tests.
== canonNum idempotent
+++ OK, passed 100 tests.
Test suite lara-test: PASS
```

## Reading

Two suites, 14 properties, all pass (100 QuickCheck cases each):

**`Lara.Prop` (8 properties — grounds C01, spec §9 result 11):**
- `prop ≡ reflexive`, `prop ≡ symmetric`, `prop ≡ transitive` — `≡` is an equivalence relation.
- `prop ≡ is nf-equality` — `≡` is exactly `nf`-equality.
- `prop nf idempotent` — `nf(nf p) = nf p`.
- `prop no argument reordering` — `p(a,b) ≢ p(b,a)` for distinct normalized `a,b` (no AC symbols).
- `canonNum variants collapse` — `+2.1`, `2.10`, `02.100` → `2.1`; `-0.0` → `0`; etc.
- `canonNum idempotent`.

**LP adapter seed `Lara.Kernel` (6 properties — the non-conforming seed, N18):**
- `valid derivations check`, `sum monotonicity`, `check introspection` — the LP rules hold by
  construction on generated valid derivations.
- `unknown constant rejected`, `apply non-implication rejected`, `apply mismatch rejected` — the three
  rejection classes the seed distinguishes.

These are **conformance evidence, not soundness proofs** (spec §9 closing note; docs/mechanization-plan.md
§1). They cross-check the implementation; the mechanized theorems (none yet) carry soundness.
