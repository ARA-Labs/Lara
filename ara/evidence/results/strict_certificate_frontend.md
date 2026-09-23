# Strict-certificate frontend worked example — 2026-07-29

- **Provenance**: ai-executed
- **Grounds**: C03, C05
- **Implementation**:
  `src/Lara/Syntax.hs`, `src/Lara/Elaborate.hs`, `app/Main.hs`,
  `examples/S1/`, `test/SyntaxSpec.hs`, `test/ElaborateSpec.hs`,
  `test/WorkedExamplesSpec.hs`, `test/CliSpec.hs`,
  `test/DifferentialSpec.hs`

## Question

Can a strict rule carrying an `nd@1` certificate be authored in `.lara`,
lowered with its policy-carried theory table, replayed by the unchanged checker,
and produce the same verdict in the Haskell and Lean drivers?

## Fixture

S1 instantiates `certified_citation(X, D)` with premise and conclusion
`holds(X, D)`, cites the policy-declared empty theory
`sha256:strict-v1-theory-0`, and submits `(hyp 0)`.

This is the maximal source-referencing certificate shape under the current
adapter: `encodeND` maps source propositions to flat atoms, so richer
`lam`/`app` terms require opaque internal atom keys and do not certify
source-level formula structure.

## Results

```text
$ cabal run lara -- check examples/S1/example.lara
(verdict accept (labels (0 in)) (edges) (statuses (status (atom holds (con safety_invariant) (con D)) justified)))
```

```text
$ bash scripts/differential.sh
example.core.sexp  0  (verdict accept (labels (0 in)) (edges) (statuses (status (atom holds (con safety_invariant) (con D)) justified)))
pass=33 fail=0
```

The full Haskell suite also passed. The focused gates reported:

```text
syntax program round-trip (result 12)                 passed 2000 tests
syntax policy round-trip (result 12)                  passed 2000 tests
elaborate strict nd@1 cert presentation path accepts  passed
elaborate strict cert missing theory rejects R13      passed
S1 strict nd@1 cert -> accept, arg in, claim justified passed
cli .lara accept S1 strict cert exit 0 + bytes         passed
```

## Interpretation

The frontend path is now exercised end to end without changing
`Lara.Check`, `Lara.Driver`, `Lara.Strict*`, `Lara.Wire`, or Lean semantics.
The absent-theory mutation reaches R13, demonstrating that the policy theory
table is part of replay rather than parser/elaborator validation.
