# Non-empirical examples: issue #349

Executed 2026-09-20. Provenance: ai-executed.

P1's exact statuses and labels are in `examples/P1/expected.json`;
`prop_P1Defense` tests reinstatement by removing its defending edge.
`prop_axiomAdmissionBoundary` checks admitted ND hypothesis reuse, loss of
sole support under quarantine, and target-world refusal before bridge loading.

Validation output (copied from the runs):

```text
Test suite lara-test: PASS
1 of 1 test suites (1 of 1 test cases) passed.
Axiom audit passed.
Semantics registry audit passed (144 modules).
Ran 9 tests in 107.840s
presentation parity: PASS (78 rows)
surface conformance: PASS (25 cases)
surface gate test: PASS
semantics goldens: PASS
backend deps golden: PASS
update goldens: PASS
update differential: PASS (37 decisions)
pass=674 fail=0
negative pass=66 fail=0
depth-bound pass=3 fail=0
pass=20 fail=0 expected=20
differential pass=1322 fail=0
map anchors: cross-driver pass=4  pre-boundary=3  fail=0
PW outer runtime conformance passed: 7 fixtures, 101 cases, 114 runs; 1 .lara source fixtures, 17 source cases, 21 runs.
```

All `make local-gates` prerequisites completed. The run resumed at the failed
stages after redirecting Cabal's log and build-summary paths to `/tmp` and
registering the new P1 anchor in `fixtures/ANCHORS.tsv`; completed Lean and
conformance stages were not needlessly rerun. The earlier full Haskell run
caught the missing P1 entry in `DifferentialSpec.corpusGoldens`; the final
full run passed after adding it. No kernel behavior changed.

The Demo 2 decision and follow-up scope are in
`docs/non-empirical-worlds-decision.md` and issue #350. These checks establish
behavior of the encoded examples, not faithfulness of philosophical prose.
