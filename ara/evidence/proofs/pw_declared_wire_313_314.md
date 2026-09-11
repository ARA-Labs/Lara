# Declared outer bridges and wire input (#313/#314)

The user adopted a combined checked environment, codec, and file-driven Lean
example, with the Haskell runtime and differential gate in a separate issue.
Issue #322 was opened before code changes. Implementation is on the new branch
`feat/pw-declared-wire`; the PR is prepared after verification and this record.

## What is proved

- `PW.Surface.Declared.Registry.coherent`: registry bridge indices, declarations,
  endpoints, symbol maps, and evidence-leaf maps refer to the same checked object.
- `load_declarations`: successful loading retains the original declaration list
  exactly. Duplicate bridge IDs and unresolved endpoints are rejected.
- `elabPosed_declared`: every nested modal name in an elaborated query resolves to
  an original loaded declaration whose symbol map is precisely the frame's map.
- `PW.Wire.decodeDocument_encode`: structured S-expression decoding inverts
  encoding for all declarations, queries, and nested terms. Encoding is injective.
- `PW.evalFinite_iff`: Boolean evaluation agrees with unchanged `PW.Sat` when
  successor lists exactly present the accepted relation.
- `Examples.PWFileHost.evaluates_iff`: the executable host's observation is the
  compiled local observation on checked worlds.

Proofs and witnesses: `lean/Lara/PW/{Declared,Wire,Finite}.lean`,
`lean/Lara/Examples/{PWDeclared,PWWire,PWFinite,PWFileHost}.lean`.
Every new public theorem is included in `lean/AxCheck.lean`.

## File experiment

The original file declares `q → q`; its explicit source probe `q()` compares as
`justified`. Replacing the map with `q → p` makes the same source probe compare as
`gap`. The modal query asking about target `q()` stays true in both cases.
This observes the distinction between bridge-global source-claim translation
and primitive modal operands, which are evaluated as written.

Exact commands/results are in `pw_declared_wire_verification.txt`, including:

```text
Build completed successfully (209 jobs).
AxCheck coverage passed (3046 declarations).
PW file-driven gate passed (23 cases).
Lean citations: PASS (420 citations, 29 allowlisted)
ARA source spans: PASS (66 quotations)
Axiom audit passed.
```

The committed file gate includes duplicate/unknown bridge and context failures,
sorting errors, missing clauses, malformed/versioned input, first-match map
behavior, Unicode names, false answers, two-bridge nesting/order, and usage/I/O
errors. Independent component and whole-branch reviews found no correctness
blockers; a stale boundary description was fixed and extra runtime probes were
added to the gate. Gate self-tests passed: theorem coverage, Lean citations,
and the axiom parser's standard/nonstandard/empty/error diagnostic cases.

## Limits retained

Text parsing/printing uses the existing tested Driver boundary; its correctness
is not claimed by the structured round-trip theorem. The file host supplies
fixed contexts, one checked world per context, and an explicit acceptance
relation. It does not certify arbitrary maps for T6: leaf/certificate transport
obligations remain explicit premises, and canonicalizer equality is supplied
by the host. Haskell execution and cross-language agreement are not tested here;
they remain #322. PW.Frame, PW.Sat, crossCompare, and T6 are unchanged.
