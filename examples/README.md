# Worked examples — the "unit of argumentation is not the paper" pair

These two examples answer a specific design question: *if one paper cannot rebut itself, how does
the framework work in practice — should we lift to paper + reviews, or to multiple papers?*

The answer, made concrete here: **the unit of argumentation is the support term (spec §6), not the
paper.** Single-paper, paper-plus-reviews, and field-corpus are the *same* Dung framework at
different population sizes (spec §8, cross-framework non-monotonicity) — not three calculi.

Each example is a **self-contained directory** `examples/<NAME>/` (a paper
artifact): the surface `example.lara`, its co-located policy (`empirical-v1.policy.lara`,
or `strict-bad-v1.policy.lara` for R2), the derived `example.core.sexp` wire
anchor, and the derived `expected.json` golden. Both derived files are regenerated
by `scripts/gen-worked-examples.hs` (parse → elaborate, then `encodeUnit` /
`Lara.ExpectedJson.expectedJson`); a freshness test (`test/WorkedExamplesSpec.hs`)
asserts each stays in sync with its `.lara` source.

- `example.core.sexp` is the byte-exact Haskell↔Lean differential target
  (`scripts/differential.sh`): both drivers agree on the wire **verdict class**.
- `expected.json` adds the piece the wire verdict does not carry — the **located
  diagnostic**, which is **Haskell-only** (the Lean driver emits only the wire
  verdict). For a reject it names the offending argument / attack / policy
  constituent and the failing checker stage; for an accept it carries the
  per-claim statuses plus the gap / incomplete-alternative reporting. Schema:
  `{ "verdict-class", "located-diagnostic" }`.

| Directory | Witnesses | Attack kinds | Statuses | Key point |
| --- | --- | --- | --- | --- |
| `A/empirical-v1.policy.lara` | the shared trusted policy both examples check against | declares all contraries + the one exception | — | cross-paper attack can only form through the *same* declared `contrary` relation |
| `A/example.lara` | one paper attacks its own headline claim | rebut + undercut + undermine (all three), all in-paper | **defeated** | "a paper can't rebut itself" is a category error; self-attacks = the paper's honesty about its limits |
| `B/example.lara` | two papers, contrary conclusions | rebut (mutual, a 2-cycle) | **contested** ×2 | no new calculus for corpus scale; and the attack only forms because both claims hit the *same atoms* under `≡` |

## Relationship to the planned E-series (`docs/worked-examples-plan.md`)

The plan's E1–E3 / R1–R3 are the paper's coverage-matrix set. These two are complementary teaching
artifacts aimed at the design question above:

The E1–E3 / R1–R3 examples now live alongside A and B as sibling per-example
directories (`examples/E1/`, …, `examples/R3/`), each with the same
`example.lara` + policy + `example.core.sexp` layout.

- **A** overlaps E3 (`defeat-suite`) on attack coverage but foregrounds *self-attack from a single
  artifact* — the specific intuition to dislodge. Its `distribution_shift` undercut is literally the
  spec §10 snippet, extended.
- **B** is not in the E-series at all: it is the **cross-artifact** demonstrator and doubles as the
  **atom-matching stress test** (assumption A3, the load-bearing `binding` step). It is the example
  that would trigger the spec §8.1 **flip criterion** if a corpus deployment wanted replication
  *preferences* instead of a symmetric `contested` 2-cycle.

## Two design constraints these examples expose (not the self-rebuttal one)

1. **Shared proposition identity is load-bearing at corpus scale.** Cross-paper rebuttal fires only
   if both papers' conclusions are a declared `contrary` pair under `≡` (spec §3.2). Two papers that
   "disagree" in prose but formalize to non-matching atoms produce **zero** attacks — a silent
   false-independence. This is why B's `binding` rationale explicitly asserts atom identity.
2. **The strict well-formedness restriction (spec §8.1, Path B) bites harder across a contested
   field.** Within one careful paper it is easy to keep contested propositions off strict chains;
   across a field whose headline claims *are* the contested ones, that is exactly the condition the
   spec flags for a flip to Path A (involutive negation + transposition-closed strict rules).

## Status

These are wired end to end: each `example.lara` parses (`Lara.Syntax`), elaborates
(`Lara.Elaborate`) to a `Unit`, and serializes to the committed `example.core.sexp`
anchor that both the Haskell and Lean drivers check byte-exactly
(`scripts/differential.sh`), plus the committed `expected.json` located-diagnostic
golden (`Lara.ExpectedJson`, Haskell-only). This **discharges
`worked-examples-plan.md` §4**: every example now ships its per-example dir with
`.core.sexp` + `expected.json`. The expected verdict for each is also recorded
inline at the bottom of its `example.lara` as a human oracle. A coverage-matrix
test (`test/WorkedExamplesSpec.hs`) *measures* — from the elaborated units and
their verdicts, not from prose — that the suite witnesses every claim status
(justified / gap / contested / defeated), every attack kind (rebut / undercut /
undermine), and the three rejection classes (R1 / R12 / R10).

### Honesty note — the suite is defeasible-only

Every artifact declares `use backends [nd@1]`, but the empirical policy is
all-defeasible with no certificates, so **`nd@1` is inert**: no support term here
carries an assurance, and the strict-certificate frontend path (certificate
surface syntax → elaboration → `buildCertOk`) is **not** exercised by this suite.
That gap is captured as a P3 backlog item in `TODOS.md` ("Strict-certificate
worked example (nd@1 frontend cert path)"). R2's `strict-bad-v1` policy declares a
strict *rule* only to exercise the R12 policy-well-formedness reject; its artifact
stays defeasible.
