# Checker test status

- **Source**: `cabal test` on the LARA repo (test/Spec.hs + test/PropSpec.hs + test/StrictSpec.hs), GHC 9.14.1 / cabal 3.16.
- **As of**: 2026-07-24 (30-group suite; literal ND wire vectors and unbounded canonical indices).
- **Grounds**: C01, C03, C05, C12.

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
== ND replay + dependency exactness
+++ OK, passed 100 tests.
== ND certificate soundness (Thm 4)
+++ OK, passed 100 tests.
== ND out-of-range index rejected
+++ OK, passed 100 tests.
== ND local is not a dependency
+++ OK, passed 100 tests.
== encodeND normalization fidelity
+++ OK, passed 100 tests.
== atom-key exact golden vectors
+++ OK, passed 100 tests.
== atom-key malformed inputs rejected
+++ OK, passed 100 tests.
== atom-key generated round-trip
+++ OK, passed 100 tests.
== ND wire tag round-trip
+++ OK, passed 100 tests.
== ND literal wire keyword vectors
+++ OK, passed 100 tests.
== ND unknown tags universally rejected
+++ OK, passed 100 tests.
== ND malformed indices universally rejected
+++ OK, passed 100 tests.
== ND unbounded canonical index reaches replay
+++ OK, passed 100 tests.
== ND closed decoder/infer matrix
+++ OK, passed 100 tests.
== strict unregistered backend rejected
+++ OK, passed 100 tests.
== strictCheck seals a judgment
+++ OK, passed 100 tests.
Test suite lara-test: PASS
```

## Reading

Three suites, 30 properties, all pass (100 QuickCheck cases each):

**`Lara.Prop` (8 properties — grounds C01, spec §9 result 11):**
- `prop ≡ reflexive`, `prop ≡ symmetric`, `prop ≡ transitive` — `≡` is an equivalence relation.
- `prop ≡ is nf-equality` — `≡` is exactly `nf`-equality.
- `prop nf idempotent` — `nf(nf p) = nf p`.
- `prop no argument reordering` — `p(a,b) ≢ p(b,a)` for distinct normalized `a,b` (no AC symbols).
- `canonNum variants collapse` — `+2.1`, `2.10`, `02.100` → `2.1`; `-0.0` → `0`; etc.
- `canonNum idempotent`.

**Strict-backend seam `Lara.Strict` + reference adapter `Lara.Strict.ND` (16 properties — carve-out
2, grounds C03/C04/C05, spec §9 results 2/8/9/10 conformance; strict-backend-decision.md §2/§5):**
- `ND replay + dependency exactness` — `inferType` replays every constructed well-typed certificate
  to exactly its built type and its built free-dependency set (obligation 1 + Lemma 5). The expected
  set is computed by the generator independently of `inferType`, so this is a differential check.
- `ND certificate soundness (Thm 4)` — every Boolean valuation satisfying the free-context formulas a
  certificate depends on satisfies its conclusion (checked by full 2^n valuation enumeration over the
  5-atom pool). Non-vacuously exercised by the modus-ponens family.
- `ND out-of-range index rejected`, `ND local is not a dependency` — the checker rejects an
  out-of-range free de Bruijn index, and a locally bound assumption is never reported as a dependency
  (Lemma 5 exactness in the negative direction).
- `encodeND normalization fidelity` — `p ≡ q  iff  encodeND p == encodeND q` (obligation 2).
- `atom-key exact golden vectors`, `atom-key malformed inputs rejected` — the Lean/Haskell
  A/N/S/C/L UTF-8 byte-framed wire agrees byte-for-byte on empty, delimiter, non-ASCII, nullary,
  nested, arity, and ordering cases, and rejects non-canonical/truncated/trailing inputs. Both
  codecs route the fixed vocabulary through a closed `FrameTag`; the Lean parse/render inverse is
  proved and the Haskell golden-vector gate checks its exhaustive round trip.
- `atom-key generated round-trip` — 100 generated source atoms with bounded
  nested terms, delimiter-bearing fields, and Unicode identifiers/payloads
  satisfy `decodeAtomKey (encodeAtomKey p) = Just p`.
- `ND wire tag round-trip`, `ND literal wire keyword vectors`, `ND unknown tags universally
  rejected` — the closed keyword vocabulary is coherent; production-independent literal fixtures
  pin every Formula/Cert keyword without using `tagToString`; and generated strings outside the
  vocabulary are rejected in every tag position.
- `ND malformed indices universally rejected` — generated strings outside the canonical
  unbounded natural-number grammar are rejected, in addition to fixed empty, negative,
  leading-zero, and non-numeric regressions.
- `ND unbounded canonical index reaches replay` — the literal index `9223372036854775808`, beyond
  the host `Int` range, decodes successfully and is then rejected by replay as out of range rather
  than being misclassified as malformed wire input.
- `ND closed decoder/infer matrix` — every Formula/Cert constructor has one-shorter and one-longer
  arity regressions (including malformed list encodings of `false`); application inference rejects
  function-child failure, argument-child failure, a non-implication, and an antecedent mismatch;
  abort success and non-false rejection are both exercised directly. The matching Lean executable
  matrices are enforced by `#guard` build gates and additionally pin these replay cases and
  distinct-vs-canonically-equivalent `ndEnc` behavior.
- `strict unregistered backend rejected` — a backend absent from the closed registry yields
  `UnregisteredBackend` (obligation 5); a program cannot introduce one.
- `strictCheck seals a judgment` — an end-to-end pass through the opaque `SExpr` wire form seals a
  `StrictJudgment` with the expected conclusion and premise-slot dependency (obligations 3–5).

**LP adapter seed `Lara.Kernel` (6 properties — the non-conforming seed, N18):**
- `valid derivations check`, `sum monotonicity`, `check introspection` — the LP rules hold by
  construction on generated valid derivations.
- `unknown constant rejected`, `apply non-implication rejected`, `apply mismatch rejected` — the three
  rejection classes the seed distinguishes.

These are **conformance evidence, not soundness proofs** (spec §9 closing note; docs/mechanization-plan.md
§1). They cross-check the implementation; the Lean theorems and AxCheck audit carry soundness.
