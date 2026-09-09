# Relational congruence family completion (#277)

Provenance: ai-executed. Source: `lean/Lara/Context/Parametricity.lean`.

`relFixesContext_composed` uses relational deduplication and list append.
`obsGen_parametricity_composed` instantiates `obsGen_parametricity`; the old
`admissible_composed` still assembles admissibility from the halves.

`edgeB_rel` and `checkedAF_rel` support `whole_program_parametricity_sem` and
its grounded companion with only `RelInj` and related argument/attack lists.
They preserve the original checked-program contract. A route through contextual
acceptance would require premises absent from that contract.

`occurrences_composed` proves membership union under context composition.
`closedOccurrences` includes both context and fragment. `closedOccRel` supplies
`obsGen_parametricity_closed_local` without fragment-containment premises, with
semantics and grounded wrappers. This is the closed-link route through the
contextual generic root, and it retains original-link admissibility.

Validation on the issue branch:

```text
Build completed successfully (158 jobs).
AxCheck coverage passed (2649 declarations).
Axiom audit passed.
ARA source spans: PASS (59 quotations)
```

The audit restricts dependencies to propext, Classical.choice, Quot.sound.
`git diff --check` passed. Compile-only graphOf specializations in
`/tmp/Regression277.lean` recovered the composed and whole-program functional
semantics APIs with their original premises; Lean accepted both.

No Haskell, corpus, freeze tag, Mathlib, or existing theorem API changed.
