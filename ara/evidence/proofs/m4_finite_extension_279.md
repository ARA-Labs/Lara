# Finite injective realization (#279)

The requested unrestricted extension statement is false on `Assurance`.
`not_every_relInj_has_total_extension` gives a kernel-checked counterexample:
`shiftAssurance` increments certificate backend versions, fixes `none` and
`trusted`, is injective and misses every version-zero certificate. Its inverse
graph has full range and a proper domain, preventing a total injective extension.

The corrected constructive scope is finite occurrence agreement.
`exists_total_injective_extension_on` extends every related pair whose source
belongs to a supplied finite list. Induction starts at identity and swaps
outputs while preserving earlier pairs. Classical choice is used, but no
countability machinery or Mathlib dependency is introduced.

`relFrag_exists_injective` realizes the fragment. The stronger
`relFrag_exists_injective_fixesContext` simultaneously fixes context material
by using the concatenation of both occurrence lists. Acceptance preservation
is independent and is not asserted by these structural theorems. This corrects
C53's previous unrestricted-extension premise; historical #215 evidence is
retained as the record of what was stated then.

Verification:

- Full Lean build: `Build completed successfully (159 jobs).`
- Full AxCheck kernel run and standard-trio audit: `Axiom audit passed.`
- Coverage for finite extension and parametricity: `AxCheck coverage passed (95 declarations).`
- ARA source-span gate: `ARA source spans: PASS (59 quotations)`.
- The finite realization and the negation of the unrestricted assertion are
  checked Lean theorem statements, rather than executable conformance tests.
