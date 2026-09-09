# Accepted semantic negative (#273)

`Lara.Examples.ContextSemantics.ctxEquivSem_semantic_negative` refutes
`CtxEquivSem stableSem registryEx fullCycleFrag singletonCycleFrag` by applying
its universal context hypothesis to `semanticNegativeCtx`.

Both fragments export `[pA]`, use `cyclePolicy`, and pass the link guard and
whole-unit checker. The context has no declarations or arguments. The full
cycle fragment moves #270's complete linked arguments and attacks to the fragment
side; `semantic_negative_cycle_shape` checks that linking preserves both lists.
The comparison fragment contains one unattacked argument for the same claim.

`obsSem_semantic_negative` pins the two stable observations to
`.observed [ClaimObservation.noExtension]` and
`.observed [ClaimObservation.observed Grounded.Status.justified]`, with an
explicit disequality. Thus separation occurs inside the semantic payload after
acceptance. `obsSem_semantic_negative_grounded` pins the cycle's grounded payload
to `observed contested` and its disagreement with stable at this context.

This is a finite non-triviality witness. It does not prove grounded contextual
equivalence of the fragments across every context, and does not resolve #268.

Verification:

- Direct Lean kernel check of `ContextSemantics.lean`: exit 0, no diagnostics.
- All new public theorems are listed in `AxCheck.lean`; whole-tree coverage:
  `AxCheck coverage passed (2629 declarations).`
- Lean citation gate: `Lean citations: PASS (286 citations, 28 allowlisted)`.
- Mutation check in a temporary copy: replacing stable with grounded in
  `obsSem_semantic_negative` fails with `Tactic decide proved that the proposition
  ... is false`, at the expected no-extension payload.
- Independent read-only review: no actionable findings.
- Full `lake build`: `Build completed successfully (158 jobs).` Existing
  warnings are confined to unchanged modules.
- Full `AxCheck.lean` kernel run and standard-trio audit: `Axiom audit passed.`
- ARA source-span gate: `ARA source spans: PASS (59 quotations)`; edited YAML
  files parse successfully.
