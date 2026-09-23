# Axiom-withdrawal witness

Executed 2026-09-20. Provenance: ai-executed.

The interface decision and reproduction commands are in
`docs/demos/d5-axiom-withdrawal.md`. The example uses the existing admission
evaluator and production ND backend. `source_support` checks the strict
hypothesis-reuse step; `units_accepted` applies the production unit checker's
exact completeness theorem to the admission evaluator's retained programs.
`retained_transport` applies T6. `leafCheck_iff` connects the executable
identity-map check to `leaf_ok`; `no_withdrawn_bridge` rules out every
structural bridge to the empty target leaf environment.

The following is copied from the executable gate in the successful
`make local-gates` run:

```text
Axiom withdrawal: separate Lean structural-contract witness
source admission (admit): accepted
source admission (quarantine): accepted
source admission (reject): rejected (R8)
unit checker (admit): true
unit checker (quarantine): true
local status (admit): justified
local status (quarantine): gap
identity leaf preservation (retained): true
identity leaf preservation (withdrawn): false
ND replay (premise present): true
ND replay (premise absent): false
Axiom-withdrawal executable gate passed.
```

Validation output, copied from the final Haskell suite and local-gates runs
(both exited successfully):

```text
Test suite lara-test: PASS
1 of 1 test suites (1 of 1 test cases) passed.
AxCheck coverage passed (3157 declarations).
Axiom audit passed.
Semantics registry audit passed (146 modules).
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
negative pass=16 fail=0
differential pass=1322 fail=0
depth-bound pass=2 fail=0
map anchors: cross-driver pass=4  pre-boundary=3  fail=0
PW outer runtime conformance passed: 7 fixtures, 101 cases, 114 runs; 1 .lara source fixtures, 1 refused source fixtures, 17 source cases, 21 runs.
```

A temporary mutation changed the withdrawn environment from the quarantine
result to the admit result. Lean refused the withdrawal and bridge proofs;
the mutation was confined to `/tmp` and is not part of the implementation.
The first local-gates run caught the PW document under `examples/` in the
core-anchor discovery. It was moved into the explicitly covered
`fixtures/pw/source-rejected/` family, with separate Haskell and Lean refusal
goldens. The final complete local-gates invocation passed. No core anchor
manifest, frozen corpus, or freeze tag changed.

Independent review found no important or critical issues. Its suggestion to
pin `pw-input` rejection directly was applied: the negative fixture requires
exit 1 with the Haskell run's exact error, without deriving a temporary file.
This witness does not establish a triangle theorem or add structural-contract
verification to `lara pw`.
