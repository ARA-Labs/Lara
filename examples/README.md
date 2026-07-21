# Worked examples — the "unit of argumentation is not the paper" pair

These two examples answer a specific design question: *if one paper cannot rebut itself, how does
the framework work in practice — should we lift to paper + reviews, or to multiple papers?*

The answer, made concrete here: **the unit of argumentation is the support term (spec §6), not the
paper.** Single-paper, paper-plus-reviews, and field-corpus are the *same* Dung framework at
different population sizes (spec §8, cross-framework non-monotonicity) — not three calculi.

| File | Witnesses | Attack kinds | Statuses | Key point |
| --- | --- | --- | --- | --- |
| `empirical-v1.policy.lara` | the shared trusted policy both examples check against | declares all contraries + the one exception | — | cross-paper attack can only form through the *same* declared `contrary` relation |
| `A-self-defeating-paper.lara` | one paper attacks its own headline claim | rebut + undercut + undermine (all three), all in-paper | **defeated** | "a paper can't rebut itself" is a category error; self-attacks = the paper's honesty about its limits |
| `B-two-paper-contested.lara` | two papers, contrary conclusions | rebut (mutual, a 2-cycle) | **contested** ×2 | no new calculus for corpus scale; and the attack only forms because both claims hit the *same atoms* under `≡` |

## Relationship to the planned E-series (`docs/worked-examples-plan.md`)

The plan's E1–E3 / R1–R3 are the paper's coverage-matrix set. These two are complementary teaching
artifacts aimed at the design question above:

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

These are **presentation-syntax specifications**, not yet wired into the checker. Per
`worked-examples-plan.md` §4 they still need their `*.core.sexp` serialization and an `expected.json`
golden file once the `Policy` / `SupportTerm` / `Attack` layers land. The expected verdict for each
is recorded inline at the bottom of the file as the interim oracle.
