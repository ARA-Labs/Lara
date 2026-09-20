# D4 — a philosophy-of-mathematics debate

[P1](../../examples/P1/example.lara) is a checked, non-empirical argument:
its leaves are assumptions and attestations, with no measurements. Its
[policy](../../examples/P1/philmath-v1.policy.lara) supplies the philosophical
inference schemes and questions. The same checker used by D1–D3 finds a
contested pair and a reinstated argument. There is one program and no
possible-world layer.

This is an illustrative reconstruction, not a transcript or a verdict on
the literature. The bindings are marked `unreviewed`: source checking by an
AI is not specialist approval of the philosophical interpretation.

## Read it as a debate

**The indispensability argument.** Suppose the mathematics used in the
scientific fragment under discussion is indispensable. If we accept that
such indispensability warrants ontological commitment, we have a defeasible
reason to accept abstract mathematical objects. P1 makes that second premise
a mandatory question, `commitment`, discharged by an explicit assumption.

**The nominalist challenge.** Field's *Science without Numbers* develops a
programme for dispensing with mathematical entities in physical theory and
explains mathematical utility without requiring literal mathematical truth.
P1 represents the programme as an attestation. Its separate `scope` question
requires an assumption that the reconstruction covers the fragment being
discussed. This is not a claim that Field nominalized all of contemporary
science. The resulting `dispensable` argument undermines the indispensability
premise. [Field, *Science without Numbers*](https://academic.oup.com/book/26363)

**The identification dispute.** A second proponent proposes that natural
numbers are intrinsically particular sets. Benacerraf's competing reductions
motivate the opposing view that number identity rests on structural role.
P1 makes these narrow positions mutual contraries. It does not identify
platonism in general with a particular set reduction, or make every kind of
structuralism incompatible with abstract objects. The indispensability
argument and the set-identification argument therefore have separate
conclusions. [Benacerraf, “What Numbers Could Not Be,” pp. 47–73](https://gwern.net/doc/philosophy/ontology/1965-benacerraf.pdf)

**The fictionalist reading and its defense.** A conservative application can
be useful without establishing literal mathematical truth. That reading
undercuts the indispensability inference. An illustrative objector challenges
it by insisting that useful application requires truth. A Field-style reply
appeals to consistency under the conservativity assumptions. The policy lets
this reply undercut the objector, reinstating the fictionalist argument.
The reply is an attested position in this reconstruction, not a certified
general conservativity theorem. [Field, *Science without Numbers*](https://academic.oup.com/book/26363)

## What the checker finds

| Claim | Argument | Status | Reason in this program |
| --- | --- | --- | --- |
| Abstract objects via indispensability | `a_realism` | `Defeated` | Its premise is undermined by `a_field`; `a_fiction` also undercuts the inference. |
| Intrinsic set identity | `a_sets` | `Contested` | Mutual rebuttal with `a_structure`; neither has an accepted defender. |
| Structural identity | `a_structure` | `Contested` | The same unresolved cycle. |
| Dispensability in the stipulated fragment | `a_field` | `Justified` | Unattacked, with its scope question discharged by assumption. |
| Usefulness without literal truth | `a_fiction` | `Justified` | Its attacker `a_objection` is defeated by `a_reply`. |
| Truth is required for usefulness | `a_objection` | `Defeated` | The reply undercuts this inference. |
| Consistency suffices in these applications | `a_reply` | `Justified` | An unattacked attestation. |

In the first grounded round, `a_field` and `a_reply` enter. Their targets
`a_realism` and `a_objection` are out. With its attacker defeated,
`a_fiction` enters next. Neither argument in the set/structure cycle enters
or goes out, so both remain undecided. This is where the encoded debate
stalls. Removing just the reply's undercut makes `a_fiction` defeated; the
test checks that contrast as well as the final graph.

## Two limits on every verdict

**The policy is ours.** We authored `philmath-v1`, including which assumptions
are admitted, which questions are mandatory, which positions conflict, and
which replies license attacks. A different policy or another argument can
change the result. `Justified` means accepted under this policy and this
argument population. The demo does not settle the philosophy of mathematics.

**The binding is disputable.** Prose-to-atom encoding is an interpretation.
For example, the scope of `dispensable` and the strength of
`structural_identity` matter to whether the declared attacks are faithful.
This is the paper's binding-faithfulness assumption (A3), also illustrated by
[example B](../../examples/B/example.lara). Checking the graph cannot establish
that the interpretation is right. `attested` records an attributed premise;
references are pointers, not byte-verified evidence. Here `ai-executed`
identifies who authored the extraction, and `unreviewed` preserves the need
for human scrutiny.

## Reproduce it

From the repository root:

```sh
cabal run -v0 exe:lara -- check examples/P1/example.lara
cabal exec -- runghc scripts/gen-worked-examples.hs
bash scripts/gen-anchor-manifest.sh
cabal test all --test-show-details=direct
make local-gates
```

The generator writes [example.core.sexp](../../examples/P1/example.core.sexp)
and [expected.json](../../examples/P1/expected.json).
`Lara.WorkedExamples` registers P1 for generation and freshness checks.
`WorkedExamplesSpec` pins the statuses, edges, non-observational leaves and
reinstatement contrast. `DifferentialSpec` pins the wire verdict, and
`fixtures/ANCHORS.tsv` registers the anchor for the differential gate, which runs it through
both Haskell and Lean. These are instances of the existing calculus; they
introduce no new inference rule in the kernel or metatheorem.

The proposed axiom-relative worlds example has a separate
[decision record](../non-empirical-worlds-decision.md). No paper text is changed
here. Paper-side scope wording may cite this committed example once it lands;
the separate [D5 Lean witness](d5-axiom-withdrawal.md) now checks axiom withdrawal
under the structural contract, without extending the CLI worlds loader.
