# D5 — withdrawing an assumed axiom

An argument can reuse an admitted assumption, but cannot carry that assumption
into a context that withholds it. This demo checks both sides: a retained
assumption permits structural transport; a withdrawn assumption makes the
structural bridge contract impossible.

The runnable [Lean witness](../../lean/Lara/Examples/AxiomWithdrawal.lean)
proves that failure. The companion [.lara files](../../examples/axiom-withdrawal/)
show the existing source-admission behavior. These are separate entry points:
`lara pw` still refuses a policy-pruned world before loading any bridges.

## The claim and its proof

The only premise is an `assumed`, `ai-executed` leaf named `pp`, with claim
`parallel_postulate()`. A strict rule reuses that same atom through an `nd@1`
certificate, `(hyp 0)`. The theory is empty and trusted assurance is disabled.
The certificate therefore needs premise zero. The Lean proof checks that replay
succeeds with the premise and fails without it; the Haskell test checks the
reported dependency is exactly that premise and contains no theory entry.

The atom names an assumption for this illustration. It does not formalize
Euclidean geometry. In particular, the demo proves no triangle-sum theorem:
the shipped source encoder treats propositions as flat atoms, so this
certificate cannot derive a different geometric atom from the postulate.
Bindings remain `unreviewed`; the demonstration certifies the encoded step,
not the truth of the assumed statement.

## Three decisions, three different meanings

All source files declare the same leaf, argument, and query. Only the policy
name and admission decision differ.

| Admission decision | Source result | Local status | Structural result in Lean |
| --- | --- | --- | --- |
| `admit` | Leaf and argument retained | `Justified` | Identity bridge exists; T6 transports the complete, certificate-bearing support. |
| `quarantine` | Source admitted; leaf and dependent argument removed | `Gap` | Finite leaf-preservation check fails. No structural bridge to this empty leaf environment exists. |
| `reject` | Source admission stops with R8 | No checked world or status | No target environment supplied for checking a bridge. |

Quarantine is not source rejection. `Gap` here means the local program has
lost its only support; it does not mean the claim has been disproved or
attacked. The structural failure is another fact: the source leaf has no
image in the target's admitted evidence. The executable's Boolean check is
proved equivalent to the identity map's `leaf_ok` clause for this source.
The stronger `no_withdrawn_bridge` theorem rules out every symbol and leaf
map to the empty target environment.

The positive control uses the retained context on both ends. Its bridge's
rules and certificate judgment are identical, and its live leaf is preserved.
`retained_transport` applies the existing T6 theorem to the checked strict
support. It asserts support transport only. Grounded status is computed
separately; T6 alone does not promise status preservation.

Admission is keyed by `(kind, provenance)`, so quarantine withdraws every
matching leaf. This example has just one. Omitting an admission row would
default to `admit`, not withdraw the assumption.

## Run the demo

From the repository root:

```sh
cabal run -v0 exe:lara -- check examples/axiom-withdrawal/admitted.lara
cabal run -v0 exe:lara -- check examples/axiom-withdrawal/withdrawn.lara
# Expected nonzero exit: source admission rejection (R8).
cabal run -v0 exe:lara -- check examples/axiom-withdrawal/rejected.lara

cd lean
lake build axiom-withdrawal
lake exe axiom-withdrawal
```

The Lean executable computes this report from admission, ND replay, checked
worlds, and the finite leaf check:

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
```

To reproduce the existing PW loader boundary from the repository root:

```sh
# Expected nonzero exit: world-input at tgt, before bridge loading.
cabal run -v0 exe:lara -- pw fixtures/pw/source-rejected/axiom-withdrawal.sexp
```

The document supplies no bridge or candidate-edge flag. Its refusal therefore
cannot be mistaken for detection of a failed structural contract by `lara pw`.
The separate Lean witness supplies that proof.

## Verification and interface decision

The follow-up allowed either a new
source-admission-aware world interface or a separate Lean structural witness.
This demo selects the latter and uses the existing admission evaluator,
production ND registry, unit checker, and `PW.StructuralBridge` contract.
No runtime definition, frozen envelope, corpus anchor, or freeze tag changes.
There is no new CLI bridge-verification claim.

`WorkedExamplesSpec.prop_axiomAdmissionBoundary` reads the committed source
files and checks statuses, dependencies, the quarantine audit, source rejection,
and the PW refusal stage. The committed `fixtures/pw/source-rejected/` case
also checks `lara pw-input` refusal and pins the Lean front door’s earlier
refusal separately in the PW conformance gate. These boundary examples have no `example.core.sexp` exports: a frozen
`CheckInput` cannot represent policy pruning. They are tested directly rather
than registered in the ordinary worked-example wire generator.

The Lean worlds carry verified support nodes for the admission evaluator’s
retained programs. `units_accepted` applies the unit checker’s exact completeness
theorem to those same programs; the executable also runs the checker on them.
Every new theorem is covered by `lean/AxCheck.lean`. The executable report is
checked by `make axiom-withdrawal-example`, included in `make lean-gate`.
Before review, run:

```sh
cabal test all --test-show-details=direct
make local-gates
```

The [earlier decision](../non-empirical-worlds-decision.md) records why the
original CLI story was deferred. This witness resolves the demo using the
separate Lean option. Paper text may describe that bounded result; it must
not claim a checked geometric consequence or new `lara pw` capability.
