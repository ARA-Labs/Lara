# Worked examples — the "unit of argumentation is not the paper" pair

These two examples answer a specific design question: *if one paper cannot rebut itself, how does
the framework work in practice — should we lift to paper + reviews, or to multiple papers?*

The answer, made concrete here: **the unit of argumentation is the support term (spec §6), not the
paper.** Single-paper, paper-plus-reviews, and field-corpus are the *same* Dung framework at
different population sizes (spec §8, cross-framework non-monotonicity) — not three calculi.

The **paper + reviews** population is exhibited end-to-end in the D1 demo
([`docs/demos/d1-rebuttal-replay.md`](../docs/demos/d1-rebuttal-replay.md)): a paper, its reviews,
and the rebuttal replayed as three checked programs under one policy, with the claim status
flipping across rounds — the concrete answer to the design question above.

For readers who want to see the formal examples as ordinary research writing
before reading `.lara`, the demo documents now include natural-language
companions: D1 reconstructs a submission/review/rebuttal exchange,
[`D2`](../docs/demos/d2-mechanical-reviewer.md) pairs paper excerpts with each
review-diagnostic shape, and
[`D3`](../docs/demos/d3-agreement-map.md) presents its four checked arguments as
miniature paper abstracts. These passages are explicitly illustrative rather
than purported quotations.

Each example is a **self-contained directory** `examples/<NAME>/` (a paper
artifact): the surface `example.lara`, its co-located policy (`empirical-v1.policy.lara`,
`empirical-v2.policy.lara` for E4/E5, `strict-bad-v1.policy.lara` for R2, or
`strict-v1.policy.lara` for S1), the
derived `example.core.sexp` wire anchor, and the derived `expected.json` golden.
Both derived files are regenerated
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
| `S1/example.lara` | strict rule with an `nd@1` certificate | — | **justified** | closes the frontend certificate path: surface assurance + policy theory → elaboration → replay |
| `S2/example.lara` | `ord@1` comparison certificate + a defeasible bridge rule, authored as one `comparison` block (policy `ord-v1`) | — | **justified** | the §3.6 layering: an accepted comparison atom is *terminal* until a rule binds it to systems and measurand. Strict arithmetic, defeasible bridge — and the author writes neither the `num_lt` argument order, the certificate slots, nor the θ vectors |
| `S3/example.lara` | the same certificate shape at the **tie**, `relation = at-least-as-good` (policy `ord-le-v1`) | — | **justified** (`at_least_as_good`) | the family's two members separate here: `num_le` accepts on two equal cells where `num_lt` is an R13 replay rejection, so no certificate can upgrade "at least as good" to "beats". S3 is S2 with three lines changed, under a different policy — which is why the block names a *relation* and lets the policy name its own rules |
| `S4/example.lara` | S2's artifact plus a settings audit undermining the binding, attacked by **label** (`a2.binding.leaf`) (policy `ord-setting-v1`) | undermine (on a premise leaf) | **defeated** (`better`) + **justified** (`num_lt`) | the factivity firewall in the grounded semantics: the attack lands on the layer that asserted comparability and stops at the certified arithmetic. Also that *generated* structure is ordinary structure — attackable at exactly the same point, by a name rather than a slot index |
| `S5/example.lara` | the same `strictly-better` source shape over a **`lower-is-better`** measurand (perplexity, policy `ord-ppl-v1`) | — | **justified** (`better`) + **justified** (`num_lt`) | direction of goodness is *declared* domain knowledge, not inferable from use. The same authored relation generates the mirrored goal `num_lt(ours, theirs)`, which `ord@1` then accepts — polarity chooses which comparison to make, the backend still decides it |
| `E4/example.lara` | reinstatement — three claims justified **while attacked** (policy `empirical-v2`) | rebut + undermine + undercut, each defended | **justified** ×3 (under attack) + **defeated** | defense is policy vocabulary (an exception, a one-directional contrary, a withheld edge), not a new mechanism |
| `E5/example.lara` | contested beyond rebut + gap amid attacks (policy `empirical-v2`) | undermine 2-cycle + undercut 2-cycle | **contested** ×2 + **gap** | `contested` is any-kind undec, not a rebut artifact; `gap` is missing support, orthogonal to conflict |

## Relationship to the planned E-series (`docs/worked-examples-plan.md`)

The plan's E1–E3 / R1–R3 are the paper's coverage-matrix set. These two are complementary teaching
artifacts aimed at the design question above:

The E1–E3 / R1–R3 examples and strict-certificate S1 now live alongside A and B
as sibling per-example directories (`examples/E1/`, …, `examples/S1/`), each
with the same `example.lara` + policy + `example.core.sexp` layout.

- **A** overlaps E3 (`defeat-suite`) on attack coverage but foregrounds *self-attack from a single
  artifact* — the specific intuition to dislodge. Its `distribution_shift` undercut is literally the
  spec §10 snippet, extended.
- **B** is not in the E-series at all: it is the **cross-artifact** demonstrator and doubles as the
  **atom-matching stress test** (assumption A3, the load-bearing `binding` step). It is the example
  that would trigger the spec §8.1 **flip criterion** if a corpus deployment wanted replication
  *preferences* instead of a symmetric `contested` 2-cycle.
- **S1** is the strict-backend demonstrator: its policy carries the trusted empty
  theory, its artifact carries `assurance = cert(…)`, and `nd@1` replays the
  certificate before the claim becomes justified.
- **S2–S5** are the ordered-comparison set, on `ord@1`. They share one artifact
  shape — two reported score cells, a strict re-check, a defeasible bridge — and
  vary one thing each, so the comparisons between them are the content. All four
  author that shape as a single `comparison` block (`lara-syntax@0.3`); each
  elaborates to the byte-identical unit its hand-written predecessor produced,
  so what varies below is the research content and not the encoding:
  - **S2** is the base case: `num_lt` on two different cells, nothing attacked.
  - **S3** moves to the **tie**. The cells are equal, so `num_le` is the only
    family member a certificate can carry, and the bridge concludes
    `at_least_as_good` instead of `better`. What S2 and S3 jointly show is that
    the upgrade from "no worse" to "beats" is refused by arithmetic rather than
    by review; `fixtures/corpus/ord-{le-boundary-accept,lt-boundary-reject}.sexp`
    are the same boundary pinned at the wire level.
  - **S4** attacks S2. An audit finds the two cells came from different
    evaluation settings and *undermines the binding leaf*, so the bridge goes
    `out` and `better` is **defeated** — while the strict step stays `in` and
    `num_lt(0.71, 0.74)` stays **justified**. This is the sharpest statement of
    what a certificate does and does not buy: it discharged the arithmetic, the
    disputed content was never inside it, and the grounded labelling separates
    the two. It also attacks the bridge by the premise *label* its policy
    declares (`a2.binding.leaf`) rather than by counting to `a2.1.leaf` — both
    spellings resolve to the same premise, which is what makes the readable one
    safe to prefer.
  - **S5** changes the **direction of goodness**. Perplexity is declared
    `lower-is-better`, so the same `relation = strictly-better` source generates
    the mirrored goal `num_lt(28.4, 31.6)` — ours below theirs — and `ord@1`
    accepts it. S2 and S5 are the two halves of the polarity contract: an author
    states one research relation, and which arithmetic supports it follows from
    a fact about the metric, declared once in the policy.
- **E4/E5** are the M5 worked cases (tracker #48, T4). E1–E3/A/B leave three
  label cells structurally empty: an attacked argument that *survives* (E4 —
  grounded reinstatement, one context per attack kind), a `contested` produced
  by something other than a rebut 2-cycle (E5 — undermine-native and
  undercut-native cycles), and a `gap` claim coexisting with attacks (E5). They
  share the `empirical-v2` policy — `empirical-v1` plus the defense vocabulary
  (a `null_result` exception, a one-directional meta-review contrary, and the
  deliberately circular `shift_report`/`miscalibration_report` exception pair).
  E4's context X and E5's context W are the same graph up to ONE voluntary
  undercut edge — the pair demonstrates that reinstatement vs. contested is
  decided by the declared attack set, not by the attack kinds available.

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
undermine), every attack-kind × target-label cell (each kind with an attacked
target that is `in`, `out`, and `undec` — E4/E5 close the `in`/`undec`-beyond-
rebut cells), a gap claim in an attack-carrying unit, and the three rejection
classes (R1 / R12 / R10).

For the full rejection-class picture — all fourteen classes with a runnable anchor each, the
source-boundary-vs-checker exit-code story, and why an unsupported claim (`gap`, as in `E2`) is not
the same failure as a rejected one (`reject R1`, as in `R1`) — see
[`docs/rejection-surface.md`](../docs/rejection-surface.md).

### Honesty note — what S1's certificate establishes

The suite is no longer defeasible-only: S1 exercises certificate surface syntax
→ elaboration → `Driver.buildCertOk` → `nd@1` replay. The empirical examples
remain defeasible, and R2's strict rule still exists only to exercise R12.

S1 deliberately uses premise ≡ conclusion with `(hyp 0)`. `nd@1` encodes every
source proposition — premises and theory entries alike — as a flat atom
(`src/Lara/Strict/ND.hs`, `encodeND`), so hypothesis reuse over a premise or
theory slot is the only certificate shape that references source-level content.
Richer `lam`/`app` structure is technically replayable only by hand-spelling the
backend's internal atom keys in payload-embedded formulas
(`decodeCert`/`decodeFormula`) — opaque, produced by no surface encoding, and
certifying nothing about source-level structure; `abort` cannot close a goal
from atomic premises. The premise ≡ conclusion shape is therefore the maximal
honest shape under the current backend encoding, not a simplification.
