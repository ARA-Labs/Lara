# Declared outer bridges, concrete input, and finite execution

Issues #313 and #314 join the two outer authoring forms and make them readable
from a file. A checked registry derives both the frame's bridges and query-name
resolution from the declarations. The file-driven Lean example evaluates modal
queries and runs source-claim comparisons through those same bridges.

Haskell outer execution and the cross-language differential gate landed in
[#322](https://github.com/ARA-Labs/lara/issues/322). See
[the outer runtime contract](theory-pw-outer-runtime.md): its `pw-run 1`
files declare their own worlds and edges and embed a `pw-surface 1` document
unchanged.

## The declaration/query guarantee

`Lara/PW/Declared.lean` adds `Surface.Declared.Host`, `Resolved`, and `Registry`.
The host supplies context identities, their checking environments, and explicit
canonicalizer agreement. `resolve` resolves both endpoints and runs the existing
`elabBridge`. A `Resolved` value retains the original declaration and its
`ElaboratesBridge` proof. `load` processes declarations in order and rejects a
repeated bridge ID, an unknown endpoint, a missing clause, or a failed rule check.

Frame bridge indices are names whose registry lookup succeeds. Both the frame
symbol map and `Naming.bridgeOf` come from that lookup. They cannot independently
choose different meanings for a name. `Registry.coherent` also ties the declared
source, target, and evidence-leaf map to the resolved bridge.

`load_declarations` proves that a successful load retains exactly the input
list, in order. `elabPosed_declared` then proves that **every modal occurrence**
in a successfully elaborated posed query, including nested occurrences, resolves
to an original declaration from that list with precisely the frame's symbol map.
`elabForm_declared` gives the same result before the outer context is resolved.

The low-level `Naming` and `BridgeEnv` APIs remain useful for hand-authored
models. The stronger guarantee applies when callers use the checked registry.

## Wire contract: `pw-surface` version 1

A file contains exactly one S-expression:

```text
(pw-surface 1
  (bridges
    (bridge BRIDGE_ID SOURCE_CONTEXT TARGET_CONTEXT
      (symbols (pred SOURCE TARGET)* (con SOURCE TARGET)*)
      (leaves (leaf SOURCE TARGET)*)
      (clauses CLAUSE*)))
  (queries (pose CONTEXT FORM)*))
```

The stars describe repetition, not literal input. There may be any number of
bridge declarations. Predicate and constructor entries may be interleaved;
the decoder preserves their original order. All sections occur exactly once,
in the displayed order. Empty bridge/query lists are valid.

```text
FORM   ::= (status STATUS ATOM) | (top) | (not FORM) | (and FORM FORM)
         | (box BRIDGE_ID FORM) | (dia BRIDGE_ID FORM)
STATUS ::= gap | justified | contested | defeated
CLAUSE ::= leaf-ok | rule-ok | cert-ok
ATOM   ::= (atom PREDICATE TERM*)
TERM   ::= (num TEXT) | (str TEXT) | (con CONSTRUCTOR TERM*)
```

Identifiers and literal payloads are S-expression atoms. The existing
`Lara.Driver` reader/printer supplies quoting and escapes. Bare atoms use
printable ASCII excluding parentheses, semicolon, quote, and backslash; empty
or other text is quoted. Quoted text accepts `\"`, `\\`, and `\n`; other escape
sequences are rejected. Unicode is preserved. Whitespace and semicolon comments
are accepted; a second top-level expression is rejected. The canonical printer
puts one space between list elements and adds no line breaks. Inside quoted
atoms it escapes only `"`, `\`, and newline, so a tab, carriage return, or NUL
in a name is printed raw.

Numeric term payloads retain their authored text, as the existing `Atom` AST
requires. No numeric normalization happens in this codec. Version `1` is exact;
`01` and other versions are rejected. The decoder reads the version before the
section layout, so a later version reports `unsupported-version` even when its
sections differ from version 1's. Fixed tokens use closed types with one
spelling table. `num`, `str`, `con`, and `atom` encode the same `Term`/`Atom`
shape as the inner checker wire, so `Wire.Tag` takes those four spellings from
`Lara.Driver.tagToString`; renaming one there renames it here. Domain names
become the existing distinct identifier types.

`Wire.Document` contains lists of `BridgeDecl` and `Posed`. The structured
codec preserves every list, including duplicates. First-match symbol and leaf
map semantics therefore remain unchanged. Duplicate *bridge IDs* are rejected
by the loader, not erased or normalized by the codec. Repeated clause entries
are retained; the existing elaborator checks that all required clauses occur.

`decodeDocument_encode` proves `decodeDocument (encodeDocument d) = .ok d`,
with corresponding proofs for each nested AST type. `encodeDocument_injective`
proves that distinct documents cannot share an encoding. These theorems cover
structured S-expression trees. The existing byte reader/printer is a **tested
boundary**, not a newly verified textual parser. Executable round trips cover
all constructors, escaping, Unicode, and malformed input.

Wire failures have stable categories `syntax`, `malformed`, and
`unsupported-version`. Syntax diagnostics preserve reader line/column detail.
Other detail text explains the failed constructor; consumers should branch on
the category, not parse the detail string. Loading and query elaboration have
separate typed errors, preserving the offending names and query faults.

## Running the file example

From the repository root:

```sh
(cd lean && lake build pw-example)
lean/.lake/build/bin/pw-example fixtures/pw/declared.sexp
python3 scripts/check-pw-example.py
```

The host in `Examples/PWFileHost.lean` supplies `src` and `tgt` contexts, reusing
PW's checked `wT7src` and `wOverlap` worlds. Each context has one selected world.
Every bridge's candidate relation selects the target context's world, and the
host's acceptance predicate is true. The file supplies all bridge declarations
and posed formulas; those are not hardcoded into the executable.

The bundled file returns:

```text
(pw-example-result 1 (queries true true true) (comparisons (comparison b (atom q) (comparable justified))))
```

Query answers occur in input order. Separately, the example compares the
explicit source probe `q()` through each declared bridge, also in input order.
The probe is printed beside the result. Changing the file's `q → q` map to
`q → p` changes that comparison from `justified` to `gap`, while its modal
query about target `q()` stays true. Removing the map reports
`not-posable (bridge-vocabulary ...)`, not `gap`.

This separation is semantic: primitive `box` and `dia` evaluate their operands
as written in the target context. They never implicitly translate them.
`compareProbe` is the separate `crossComparePosed` operation that translates a
source claim using the frame's exact declared symbol map.

Exit 0 means the document executed. A false modal answer or tagged
incomparability is a result, not a process error. Exit 1 means wire decoding
(`syntax`, `malformed`, or `unsupported-version`), loading, elaboration, file
access, or command usage failed. Both paths print a single
S-expression; error envelopes begin `pw-example-error 1`. The example result
protocol is separate from `pw-surface` input and the local checker wire format.

## Finite execution and proof boundary

`Lara/PW/Finite.lean` adds a finite presentation of accepted successors and a
Boolean evaluator for the existing grammar. Its `mem_successors` premise states
that list membership is exactly the frame's accepted relation. `evalFinite_iff`
proves agreement with unchanged `PW.Sat` under the host's Boolean observation.
The example discharges this premise and `PWFileHost.evaluates_iff` connects its
observation to `Sorted.cmpVal` over real checked worlds.

This does not assert that every abstract frame has an executable enumeration.
Empty lists give vacuously true boxes and false diamonds. Duplicates do not
change Boolean answers. The fixture suite exercises both cases and nesting.

The loader checks T6's rule clause, exactly as `elabBridge` does.
`Examples.PWDeclared.rule_rejected` shows a load failing that check. In the file
example it is vacuous: both host policies (`polT7`, `polOverlap`) have no rules,
so every file map passes. Merely listing `leaf-ok` and `cert-ok` does not prove
them. Evidence-leaf and certificate
transport obligations remain explicit premises when constructing a
`StructuralBridge`; arbitrary file maps are not claimed to satisfy them. The
host's canonicalizer agreement is also a supplied proof, not a decidable check.
The example's chosen acceptance relation does not assert T6 applicability.

No changes are made to `PW.Frame`, `PW.Sat`, `crossCompare`, the T6 contract,
the local compiler, or the corpus. No existing freeze tag is bumped. Haskell
execution, configurable world loading, and differential conformance are in
[the outer runtime contract](theory-pw-outer-runtime.md) (#322).

## Verification

The default `lake build` includes the executable and all proof/fixture modules.
`AxCheck.lean` covers every new public theorem. `PWWire` runs textual codec
boundary tests during compilation; `check-pw-example.py` runs real file inputs
against the compiled executable and is included in the Lean CI job. It covers
map-dependent results, first-match lookup, unknown and duplicate names, sorting
failures, missing clauses, malformed/versioned input, and quoted Unicode names.
