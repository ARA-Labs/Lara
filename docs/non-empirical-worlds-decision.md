# Axiom-relative worlds demo: defer the proposed bridge-failure story

Decision for [#349](https://github.com/ARA-Labs/Lara/issues/349), 2026-09-20:
ship the level-one [P1 philosophy demo](demos/d4-philmath.md). Defer the
triangle/parallel-postulate worlds story because today's runtime cannot
produce the proposed *checked structural-bridge failure*. The follow-up is
[#350](https://github.com/ARA-Labs/Lara/issues/350).

Follow-up in #350: [D5](demos/d5-axiom-withdrawal.md) now supplies the
separate executable Lean structural-contract witness and a positive transport
control. The CLI limitations below still hold. D5 reuses the assumed
postulate itself and makes no triangle-theorem claim.

The admission table **can** withhold an assumed leaf. The obstacle is what
happens after admission, plus the scope of the current natural-deduction
encoding. Saying that the admission table cannot express the case would be
incorrect.

## Admission can withdraw the assumption

A policy can declare:

```text
admission { (assumed, ai-executed) = quarantine }
```

The key is exactly `(kind, provenance)`, not a leaf name or proposition.
This withdraws every matching assumed leaf. It can single out the postulate
when that leaf is the only one with the matching key, as in the test probe;
it cannot select one of several identically classified assumptions by name.
An omitted row defaults to `admit`, so omission does not withdraw anything.
A `reject` row stops source admission with R8 instead of yielding a target
world. See the [admission contract](policy-admission-calculus-decision.md).

`WorkedExamplesSpec.prop_axiomAdmissionBoundary` constructs a small source
with an `assumed` parallel-postulate atom and an `nd@1` hypothesis-reuse
certificate. With admission enabled it is `Justified`. Under quarantine the
leaf and its dependent argument are removed, leaving the queried atom `Gap`.
There is no retained support to mark `evidence-blocked`; losing all support
is a gap, as described in `Lara.Blocked.blockedQueries`.

The same test tries to load both sources as PW worlds. The target fails as
`PWWorld (WorldInputError tgt ...)`, with a policy-quarantine diagnostic.
This happens before bridge loading. `sourceResultCheckInput` refuses to
export a policy-pruned source as a frozen `CheckInput`; the
[world loader](theory-pw-outer-runtime.md) respects that boundary.

## A declaration is not a proof of leaf preservation

Even a target file that simply omits the premise would not give the requested
runtime demonstration. `Lara.PW.Run.loadBridges` checks `rule-ok` but requires
only the presence of the `leaf-ok` and `cert-ok` declarations. Candidate edges
also carry author-supplied `accepted` or `rejected` flags. Marking an edge
`rejected` would exhibit an input choice, not detection of the missing axiom.

The [Lean structural contract](theory-pw-t6-structural-transport.md) does require
`leaf_ok`: a source leaf must exist at its translated proposition in the
target environment. A source leaf with no corresponding target leaf cannot
satisfy that clause. That mathematical fact and the CLI's current refusal
stage are different claims. The follow-up must choose an honest executable
witness and a positive control before calling this a checked bridge failure.

## The triangle theorem needs a different proof path

The shipped source encoder for `nd@1` encodes each proposition as a flat atom.
A hypothesis for `parallel_postulate()` cannot, by hypothesis reuse, prove a
different atom `triangle_sum_180()`. Adding the triangle atom to the trusted
theory would make it available independently of the alleged premise and
would not demonstrate the intended dependence. The existing
[S1 policy](../examples/S1/strict-v1.policy.lara) documents this same limit.
Moreover, the geometric consequence would need the rest of the geometric
axioms, not the parallel postulate alone.

The regression probe deliberately certifies the assumed postulate itself.
A future demo can retain that narrow shape, mechanize a separate Lean
contract witness, or provide a backend that checks the intended geometric
proof. Those are design choices in #350, not results of this example PR.

## Cost and paper boundary

No calculus, wire contract, frozen corpus, or freeze tag changes in #349.
A runtime extension needs matching Haskell/Lean work and conformance gates;
any new envelope version or corpus regeneration must be budgeted in #350.
The decision here meets #349's request to resolve Demo 2 before presenting it.
Only P1's checked statuses are available for paper-side reporting after this
change lands; no paper sentence should claim the deferred bridge outcome.
