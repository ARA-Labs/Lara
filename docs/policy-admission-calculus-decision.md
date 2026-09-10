# Policy-admission source calculus decision

_Status: frozen runtime-source contract, 2026-08-05. This decision is the prose
contract for the policy-admission runtime program and its companion Lean
metatheory program. It adds no construct to `lara-core@0.1`._

Background for cold readers: a *leaf* is a declared piece of evidence, and the
policy's admission rows say which kinds of leaf (by kind and provenance) an
artifact may rely on. This record fixes the filtering layer that applies those
rows at the `.lara` source boundary: it decides, deterministically, which
declared leaves reach the core checker and which are *quarantined* (set aside
as inadmissible, which is not the same as declared false). It filters inputs;
it changes nothing about the calculus or the four statuses behind it.

## 1. Boundary and non-goals

Policy admission is a deterministic judgment at the `.lara` source boundary.
It decides which declared leaves and dependent source declarations reach the
already-frozen core checker. It is not an alternative support calculus, it does
not turn quarantine into falsity, and it does not change the raw core `.sexp`
interface, replay identity, frozen corpus, or the four core statuses.

The byte-level `lara-evidence@0.1` work tracked by issue #78 remains gated and
out of scope. In particular, this decision does not make source references
byte-checked and does not add a leaf-certificate format or evidence-checker
registry.

## 2. Total policy lookup and source validity

For every declared leaf `l`, the runtime looks up its exact
`(LeafKind, Provenance)` key in the policy admission rows:

```text
policyOutcome(Pi, l) =
  Pi.admission[(kind(l), provenance(l))]  when that row is present
  admit                                    otherwise
```

Thus the semantic lookup is total even though the source table is finite and
may be omitted. An omitted table, an empty table, and an unmatched key all mean
`admit`; there is no wildcard or first-match behavior.

Two ambiguities are source invalidity, before any policy or core judgment:

- two admission rows with the same `(LeafKind, Provenance)` key; and
- two leaf declarations with the same `LeafId`.

These are not R8 or R1. The `.lara` CLI reports source invalidity with exit 2,
empty stdout, and one deterministic located diagnostic on stderr.

## 3. Source outcomes and precedence

The source pipeline has this fixed outcome order:

```text
source invalidity > policy R8 > replay R13 > group R9 > core rejection
```

The first applicable outcome is the only public outcome. Policy-reject R8 scans
leaves in source declaration order and selects the first leaf whose exact
`(LeafKind, Provenance)` key matches a `reject` row. R8 is a valid source
judgment, not malformed syntax and not a core R1: it produces CLI exit 1, empty
stdout, and exactly one deterministic stderr line. That line identifies the
selected leaf, its kind, its provenance, and the matched admission row. This is
the deliberate CLI exception to the ordinary verdict path because R8 is outside
the frozen core verdict codec.

Replay R13, group R9, accepted programs, and core rejections retain the existing
core-verdict stdout contract (with their existing exit status and any canonical
stderr diagnostic). Admission `quarantine` is not rejection.

The classes remain disjoint:

- **R8, source admission:** a declared leaf is rejected by policy admission;
- **R9, group integrity:** a declared duplicate-report group is inconsistent
  and policy escalates group conflict to rejection; and
- **R1, core reference:** a declaration reaching the core refers to an
  undeclared core identifier.

In particular, quarantine cannot be implemented by deleting only `Gamma(l)`
and allowing a surviving dependent term to fail as R1.

## 4. One combined prune

Duplicate-report consistency is evaluated against the full declared leaf
sequence, before anything is removed. This ensures that policy quarantine
cannot hide a group conflict. The runtime then computes two ordered seed sets:

```text
policySeed = leaves whose policy outcome is quarantine
groupSeed  = leaves in every inconsistent group when group mode is quarantine
removeSeed = policySeed union groupSeed
```

After all earlier rejecting boundaries have passed, policy and group seeds are
unioned once and exactly one prune is applied. The prune removes:

1. every leaf in `removeSeed`;
2. every argument whose full support term depends on a removed leaf, including
   leaves nested in premises and in question discharges; and
3. every attack whose raw source or raw target argument was removed.

The admitted `Gamma`, retained arguments, retained attacks, and blocked-status
input are projections of this same prune. The production core therefore never
sees a dangling dependent leaf occurrence. A conditional core query can be
`gap` because no complete retained support remains, but that result comes from
checking the pruned program, not from treating a missing `Gamma(l)` as a typing
route to gap. Public `evidence-blocked` reporting is derived from the same prune
and retains the conditional four-state result only as a diagnostic.

## 5. Hidden source carrier

The implementation may expose ordinary verdict/report projections, but the
value threaded between source checking and reporting is an opaque carrier. Its
sole smart constructor binds together:

- the unchanged replay identity;
- the full declared unit, including declaration order;
- the ordered policy-quarantine seed;
- the one combined policy-plus-group prune; and
- the canonical admission audit.

The carrier prevents reporting from recomputing admission against a different
unit, constructing a second prune, or deriving blocked status from different
removed material. Hiding the constructor is an API invariant, not a new trust or
serialization boundary.

## 6. Canonical audit

The audit is deterministic and is rendered in leaf declaration order. For each
removed leaf it records causes in this order:

1. `PolicyQuarantine`, if policy caused removal;
2. every causing `GroupQuarantine` value, once each and in group declaration
   order.

Removed arguments and removed attacks are rendered in their respective source
declaration order. The leaf portion contains exactly one row per removed leaf,
and every row has a nonempty cause list; a leaf removed by both mechanisms is
not duplicated. This canonical audit, the retained source projections, and
blocked reporting all describe the same combined prune.

## 7. Compatibility lock

This decision changes only the `.lara` runtime source boundary and its
mechanized metatheory. It does not change:

- `lara-core@0.1` judgments, rejection classes, wire grammar, or four-state
  semantics;
- raw `.sexp` checking relative to a caller-supplied `Gamma`;
- replay identity or the frozen corpus; or
- byte-level evidence verification, which remains gated under #78.

This contract landed with PR #81 (issue #77). The runtime lives in
`src/Lara/Admission.hs` and `src/Lara/Admission/`, threaded through
`src/Lara/Driver.hs`; the mechanized side is `lean/Lara/Admission.lean` with the
executable reference driver `lean/Lara/AdmissionDriver.lean`, and the two are
compared byte-for-byte by `scripts/admission-differential.sh` (20 files: 15
semantic, 5 codec rejects). The implementation plans that specified this work
were retired once it landed; their content is this decision record plus the code.
