# Certified-evidence landing gate evidence (2026-10-06)

Raw output of the landing gates for `lara-evidence@0.1`, captured from the
`make local-gates` run (`/tmp/gates5.log`, exit 0) and `cabal test all`
(exit 0) on branch `feat/enforce-certified-leaf-checker`, commit `fd8b74d`.
Lines below are copied verbatim; they are the empirical record behind the
implemented-status revision in `logic/solution/constraints.md` and the
crystallization of O185/O186.

```text
Build completed successfully (252 jobs).
Axiom audit passed.
presentation parity: PASS (91 rows)
surface conformance: PASS (28 cases)
differential pass=1651 fail=0
map anchors: cross-driver pass=5  pre-boundary=3  fail=0
PW outer runtime conformance passed: 7 fixtures, 102 cases, 115 runs; 1 .lara source fixtures, 1 refused source fixtures, 17 source cases, 21 runs.
evidence differential: PASS 50 typed cases; concrete byte parsers and OS capture are separate checks
evidence CLI acceptance: 58 scenarios passed
```

Package-door observations from the same branch, each produced by
`cabal run -v0 lara -- check-ara <package>`, reported in the feature PR and
re-asserted by `test/evidence-cli.sh` (the `...` elisions are excerpts of one
canonical report line each; the checked/declared/assurance fields shown are the
asserted ones):

```text
package-a: exit 0  (lara-evidence-report 1 ... (assurance evidence-checked) ... (checked forward-1631 forward-1632) (declared))
package-b: exit 0  (lara-evidence-report 1 ... (assurance evidence-checked) ... (checked train-0 train-1 train-2 loss-0 loss-1 loss-2 loss-3 loss-4) (declared))
fixtures/evidence/quarantined: exit 0  (lara-evidence-report 1 ... (assurance mixed) ... (checked drop) (declared keep))
```

Borrowed-capture seal, reproduced before the fix and after it (the same
property, run with the promotion check removed and restored):

```text
== evidence: a captured object is only usable under its own manifest entry
*** Failed! Falsified (after 1 test):          # check removed
+++ OK, passed 1 test.                          # check in place
```

Trusted boundaries for every number above: the concrete byte parsers, SHA-256,
the POSIX capture shim and the Haskell/Lean compilers. The 50 typed cases are
conformance evidence over a finite model, not a parser proof.
