# M4 G0 finite checks

Run on base `7d0f738`, branch `theory/305-m4-g0-interface-spike`.
Provenance: ai-executed. Toolchain: `leanprover/lean4:v4.32.0`.

Input: [G0 record](../../../docs/theory-m4-g0-interface-spike.md#reproduce-the-finite-checks).
Its exact Lean block was extracted to `/tmp/lara-305-g0-record.lean`.
From `lean/`, `lake env lean /tmp/lara-305-g0-record.lean` exited 0:

```text
("hidden-feedback", true)
("empty-defeat-hidden-node", true)
("certificate-collapse", true)
("closure-sees-payload", true)
("same-context-copy", true)
```

The prerequisite build of `Lara.Examples.CertificateCollapse`,
`Lara.Context.FiniteExtension`, and `Lara.Examples.Realizability` succeeded
(51 jobs; existing linter warnings). These are executable finite calculations,
not new kernel proofs. No universal equivalence or characterization was tested.
An earlier temporary input had record-indentation errors; the results above
come from the corrected input reproduced in the decision record.
