# Worked examples — the "unit of argumentation is not the paper" pair

**New here? A suggested order.** Read the [README](../README.md)'s running
example first, then `A/` (one paper honestly attacking its own headline
claim), then `B/` (two papers with contrary conclusions), then `P1/` (a
non-empirical philosophy-of-mathematics debate with contested positions and
reinstatement). Its [D4 companion](../docs/demos/d4-philmath.md) explains the
arguments and the limits of its authored policy. After those, the
S-series walks the strict-certificate machinery one feature at a time, and
E4/E5 exercise the defeat semantics (reinstatement, contested, gap). The demo
write-ups in [`docs/demos/`](../docs/demos/) present checked artifacts as
ordinary research prose — a rebuttal exchange, mechanical review comments, a
cross-paper agreement map — and are the gentlest entry of all.

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
`empirical-v2.policy.lara` for E4/E5, `philmath-v1.policy.lara` for P1,
`strict-bad-v1.policy.lara` for R2, or
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

`agreement-map-multi/` is a **map** (issue #303), not an example directory. Like
`rebuttal-replay/` and `running-example/`, it is a container: it holds four
ordinary example directories (`paper-a/` … `paper-d/`, each registered in
`Lara.WorkedExamples` like any other) rather than an `example.lara` of its own.
What makes it a map is what it holds *in addition* — the `map.laramap` manifest
that composes those four members, and the two derived map anchors,
`map.core.sexp` (the `map-check-input@1` parity envelope) and `map.verdict.sexp`
(the golden `map-verdict@1` composite). Neither is a wire check-input envelope,
so neither is `scripts/differential.sh`'s: `map.core.sexp` is what
`scripts/check-map-conformance.sh` hands the Lean `lara-map-driver` in order to
compare the two drivers, and `map.verdict.sexp` is a golden pinned by
`test/MapExampleSpec.hs`. Run the map with
`cabal run exe:lara -- check examples/agreement-map-multi/map.laramap`, or
`make map-check`.

| Directory | Witnesses | Attack kinds | Statuses | Key point |
| --- | --- | --- | --- | --- |
| `A/empirical-v1.policy.lara` | the shared trusted policy both examples check against | declares all contraries + the one exception | — | cross-paper attack can only form through the *same* declared `contrary` relation |
| `A/example.lara` | one paper attacks its own headline claim | rebut + undercut + undermine (all three), all in-paper | **defeated** | "a paper can't rebut itself" is a category error; self-attacks = the paper's honesty about its limits |
| `B/example.lara` | two papers, contrary conclusions | rebut (mutual, a 2-cycle) | **contested** ×2 | no new calculus for corpus scale; and the attack only forms because both claims hit the *same atoms* under `≡` |
| `P1/example.lara` | a philosophy-of-mathematics debate; every leaf is assumed or attested | undermine + rebut + undercut | **contested** ×2, **justified** ×3 (including reinstatement), **defeated** ×2 | policy supplies the subject matter; an unresolved set/structure dispute coexists with a defended fictionalist argument. The [D4 write-up](../docs/demos/d4-philmath.md) states the policy and binding caveats; the [worlds decision](../docs/non-empirical-worlds-decision.md) records the original CLI limitation; [D5](../docs/demos/d5-axiom-withdrawal.md) supplies the separate Lean axiom-withdrawal witness. |
| `S1/example.lara` | strict rule with an `nd@1` certificate | — | **justified** | closes the frontend certificate path: surface assurance + policy theory → elaboration → replay |
| `S2/example.lara` | `ord@1` comparison certificate + a defeasible bridge rule, authored as one `comparison` block (policy `ord-v1`) | — | **justified** | the §3.6 layering: an accepted comparison atom is *terminal* until a rule binds it to systems and measurand. Strict arithmetic, defeasible bridge — and the author writes neither the `num_lt` argument order, the certificate slots, nor the θ vectors |
| `S3/example.lara` | the same certificate shape at the **tie**, `relation = at-least-as-good` (policy `ord-le-v1`) | — | **justified** (`at_least_as_good`) | the family's two members separate here: `num_le` accepts on two equal cells where `num_lt` is an R13 replay rejection, so no certificate can upgrade "at least as good" to "beats". S3 is S2 with three lines changed, under a different policy — which is why the block names a *relation* and lets the policy name its own rules |
| `S4/example.lara` | S2's artifact plus a settings audit undermining the binding, attacked by **label** (`a2.binding.leaf`) (policy `ord-setting-v1`) | undermine (on a premise leaf) | **defeated** (`better`) + **justified** (`num_lt`) | the factivity firewall in the grounded semantics: the attack lands on the layer that asserted comparability and stops at the certified arithmetic. Also that *generated* structure is ordinary structure — attackable at exactly the same point, by a name rather than a slot index |
| `S5/example.lara` | the same `strictly-better` source shape over a **`lower-is-better`** measurand (perplexity, policy `ord-ppl-v1`) | — | **justified** (`better`) + **justified** (`num_lt`) | direction of goodness is *declared* domain knowledge, not inferable from use. The same authored relation generates the mirrored goal `num_lt(ours, theirs)`, which `ord@1` then accepts — polarity chooses which comparison to make, the backend still decides it |
| `S6/example.lara` | S2's strict leg with the certificate premises cited **by source name** — `(ordcmp (prem base_cell) (prem new_cell))` (policy `ord-named-v1`, `lara-syntax@0.6`) | — | **justified** (`num_lt`) | the committed golden is the standing byte-identity witness for #105: the symbolic spelling elaborates to the numeric spelling's exact `.core.sexp` bytes, so the freshness check re-proves the lowering on every run |
| `S7/example.lara` | S6's shape with the certificates cited **by premise label** — `(ordcmp (prem base) (prem new))` — plus a second argument where **one leaf fills both slots** of a two-premise rule, citable only as `(prem left)`/`(prem right)` (policy `ord-labeled-v1`, `lara-syntax@0.8`) | — | **justified** (`num_lt`) + **justified** (`num_le`) | the standing byte-identity witness for #131. A label names the *slot* rather than the term filling it, so it keeps working where the `@0.6` leaf name is `CertSlotMultiSlot` — the one case names could not express, and the reason labels earned their own name class |
| `S8/example.lara` | S1's strict `nd@1` step with one named binder, a source-authored formula annotation, and the same named premise on both sides of a beta-redex — `(app (lam h (prop "holds(safety_invariant, D)") (prem e1)) (prem e1))` (policy `strict-v1`, `lara-syntax@0.10`) | — | **justified** (`holds`) | the inner `prem e1`, at binder depth 1, lowers to `(hyp 1)`; the outer one at depth 0 lowers to `(hyp 0)`; the `(prop …)` annotation lowers through `encodeAtomKey ∘ nf` to the frozen `(atom KEY)` wrapper. The redex adds no source-level logical strength: it isolates binder-depth shifting. Since grammar Appendix I (`lara-syntax@0.10`) landed, no out-of-band key-generation command remains in the example's provenance. |
| `S9/example.lara` | the `insp@1` static code-inspection backend: a plan-vs-shipped diff over two declared exhaustive inventories (`(inspectdiff (prem 0) (prem 1))`) plus the pure negative existential over one (`(inspect (prem 0))`), under a defeasible bridge (policy `insp-v1`) | — | **justified** (`implementation_gap`, `code_planned_not_shipped`, `code_absent`) | what a code inspection can and cannot certify. The strict step discharges the *closed-world inference* — given an exhaustive enumeration, absence follows — and nothing about whether the enumeration is faithful to the bytes. S9 is the corpus unit `rebench-rust_codecontests/C09` with the one leaf C09 lacks: C09's `version_match` CQ has no honest discharging leaf, so it is a `gap`; supply the attestation and the same shape is `justified`. Read the two together and the difference is exactly the half no certificate supplies |
| `E4/example.lara` | reinstatement — three claims justified **while attacked** (policy `empirical-v2`) | rebut + undermine + undercut, each defended | **justified** ×3 (under attack) + **defeated** | defense is policy vocabulary (an exception, a one-directional contrary, a withheld edge), not a new mechanism |
| `E5/example.lara` | contested beyond rebut + gap amid attacks (policy `empirical-v2`) | undermine 2-cycle + undercut 2-cycle | **contested** ×2 + **gap** | `contested` is any-kind undec, not a rebut artifact; `gap` is missing support, orthogonal to conflict |
| `agreement-map/example.lara` | four "papers" in **one** file: a same-setting disagreement beside a setting mismatch (policy `agreement-v1`) | rebut (mutual, declared by hand) | **contested** ×2 + **justified** ×2 | atom identity, not prose, decides whether papers disagree — the single difference of a setting index flips `contested ×2` to `justified ×2` |
| `agreement-map-multi/` | the **same** demonstration as four independently checkable artifacts under one `map.laramap` (issue #303) | rebut (mutual, **generated** by cross-member saturation) | **contested** ×2 + **justified** ×2 | a member cannot name another member's argument, so the two edges the single-file version writes by hand are here *derived*. Each `paper-*/` alone is `justified`; the composite reproduces the single-file oracle's labels, edges and statuses |

`axiom-withdrawal/` is the [D5 boundary demo](../docs/demos/d5-axiom-withdrawal.md).
It contains admitted, quarantined, and rejected versions of one assumption-reuse
argument. Its [PW refusal fixture](../fixtures/pw/source-rejected/axiom-withdrawal.sexp)
exposes the current world-loader boundary.
Its structural-bridge proof runs separately in Lean. These sources are tested
directly by `WorkedExamplesSpec`; policy-pruned sources cannot be exported to
the ordinary frozen wire anchors.

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
- **S6** is the named-certificate-slot demonstrator (`lara-syntax@0.6`, #105):
  S2's strict leg alone, with the hand-authored certificate citing its premises
  by source name — `(ordcmp (prem base_cell) (prem new_cell))` — instead of
  0-based slots. Elaboration lowers the names against the argument's own
  premise list, so the committed `.core.sexp` carries only the numeric
  spelling; the golden is the standing byte-identity witness that the symbolic
  and numeric authors produce the same wire bytes.
- **S7** is the premise-label demonstrator (`lara-syntax@0.8`, #131), and its
  point is the *second* argument. A name in a certificate now resolves in three
  classes — the rule's declared premise label, a declared leaf, a prior
  argument — and `a1` shows the two spellings agreeing on the easy case: its
  two slots hold two different leaves, so `@0.6`'s leaf names already worked
  and `(prem base)`/`(prem new)` are simply the rule's own names for the same
  slots. `a2` is the case `@0.6` cannot express at all. Both premises of
  `le_reflex` share one pattern and `a2` fills both with the leaf `base_cell`,
  so `(prem base_cell)` occupies slots 0 and 1 at once and is rejected as
  `CertSlotMultiSlot` — before `@0.8` the only exit was to count slots by hand.
  A label names the slot rather than the term filling it, so `left` and `right`
  stay unambiguous however the instance is filled. Both certificates lower to
  the same `(ordcmp (prem 0) (prem 1))` the numeric twin produces.
- **S8** is the named-`nd@1` binder/premise/formula demonstrator
  (`lara-syntax@0.10`).
  It keeps S1's single strict premise and conclusion, but deliberately inserts
  a beta-redex: `(app (lam h (prop "holds(safety_invariant, D)") (prem e1))
  (prem e1))`. The inner occurrence of the same source name sits at binder
  depth 1 and lowers to `(hyp 1)`; the outer occurrence at depth 0 lowers to
  `(hyp 0)`; the formula annotation is the surface `prop` production itself
  and lowers through the shared `encodeAtomKey ∘ nf` path to the frozen
  `(atom KEY)` wrapper (grammar Appendix I). Thus the
  committed anchor is the numeric twin's redex, while replay still reports
  only free premise slot 0 as a dependency. The redex is not a new
  source-level inference, and no out-of-band key-generation command remains
  in the example's provenance.
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
