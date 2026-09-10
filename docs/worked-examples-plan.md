# LARA worked-examples plan

_The six worked examples the paper and test suite require, with a coverage matrix over every claim
status and every attack type. Expands `spec.md` §10 (which currently has one incomplete example) to
"at least five worked cases spanning every status/attack kind" and "three complete + three rejected
examples". Anchored in the real corpus shapes catalogued in `corpus-map.md`._

_This is the historical design plan; the authoritative catalogue of what
exists now is `../examples/README.md`. A worked example is a self-contained
directory: a surface `.lara` artifact, its co-located policy, and its pinned
expected verdict._

_**What actually shipped (2026-08-19; augmented 2026-08-22).** This plan
specifies the E/R series. The
delivered suite is larger — it also carries `R2-sort` (the `lara-core@0.2`
well-sortedness negative) and the strict-certificate series `S1`–`S8` (`nd@1`,
`ord@1` comparison, the `num_le` tie, an undermined binding, a lower-is-better
measurand, the `lara-syntax@0.6` named-slot byte-identity witness, the
`lara-syntax@0.8` premise-label witness, and the `lara-syntax@0.9`/`@0.10`
named-`nd@1` binder/premise/formula byte-identity witness S8). The
authoritative catalogue of every committed example, with its witnesses, attack
kinds, and statuses, is `../examples/README.md`._

## 0. Why worked examples are load-bearing for this paper

For a calculus paper, worked examples are not illustration — they are the primary way a reviewer
checks that the abstraction *captures the phenomenon it claims to*. LARA claims to localize
claim-support failures that proof terms or abstract argument graphs cannot ("the composite bet").
Each example must make one such capability legible, and the set together must
**exercise every status and every attack constructor** so no corner of the calculus is unwitnessed.

Two hard requirements:

1. **Every example is dual-form.** Each ships as (a) a presentation-syntax `.lara` listing for the
   paper and (b) the serialized core (S-expression) that the Haskell checker *and* the Lean model
   consume — the differential-testing anchor (`mechanization-plan.md` §3). The two must decode to the
   same AST (`spec.md` §9 result 12).
2. **Every example carries its expected verdict.** Golden output: the four-state status of each claim
   root, the grounded label of each argument, the located obligations, and for rejected examples the
   exact diagnostic (rule + position + reason). The golden file is the test oracle
   (`engineering-plan.md` §5).

## 1. Coverage matrix

Six examples. The three "complete" ones parse, check, and compile to a well-formed AF; the three
"rejected" ones must be refused with a specific located diagnostic. Together they must touch every
cell below.

| # | Name | Kind | Claim status(es) exercised | Attack type(s) | Backend | Rejection class |
| --- | --- | --- | --- | --- | --- | --- |
| E1 | `justified-clean` | complete | **justified** | none | ND (trusted-policy scheme) | — |
| E2 | `open-gap` | complete | **gap** (open mandatory CQ) | none | ND | — |
| E3 | `defeat-suite` | complete | **defeated**, **contested**, **justified** (3 claims) | **rebut**, **undercut**, **undermine** (all three) | ND | — |
| R1 | `undeclared-leaf` | rejected | — | — | — | leaf not in `Gamma` (admission `reject`/absent) |
| R2 | `strict-contrary-violation` | rejected | — | — | ND | §8.1 strict-reachable `contrary` well-formedness |
| R3 | `bad-attack-target` | rejected | — | (attempted) rebut on a **strict** rule | ND | strict rule not rebuttable (§7) |

Status coverage: justified (E1, E3), gap (E2), contested (E3), defeated (E3) — all four.
Attack coverage: rebut, undercut, undermine (E3) — all three; plus the *illegal* attack (R3).
Rejection coverage spans three distinct classes; the full mutation suite (`engineering-plan.md` §5)
covers the rest, but these three are the human-readable representatives.

## 1.5 M5 additions — E4 and E5 (landed in PR #49)

M6 pulled forward (issue #48, T4) added two further worked cases to close
coverage cells the six-example matrix cannot reach, both on policy
`empirical-v2` (= `empirical-v1` + the rules/exceptions/contrary below) with
golden verdicts through both drivers (`examples/{E4,E5}/`):

- **E4 — reinstatement** (`examples/E4/`): a claim stays `justified` *while
  attacked* because its attacker is itself defeated — `justified-under-rebut`
  (context R) and `justified-under-undermine` (context U, via the
  one-directional `contrary refuted_replication not_generalizes`; a symmetric
  pair would force the reverse edge and collapse the reinstatement into a
  cycle).
- **E5 — contested beyond rebut, and gap amid attacks** (`examples/E5/`):
  `contested` via a mutual-undermine 2-cycle (context V) and via a
  mutual-undercut 2-cycle (context W — undercut cycles are voluntary because
  exceptions don't participate in the completeness scan), plus a `gap` claim
  coexisting with attacks (context G).

`prop_coverageMatrix` extends with the new cells (justified-under-attack,
contested-via-undercut/undermine, gap-with-attacks-present); the frozen suite
carries them — contested is held by E5 (`docs/m5-freeze-checklist.md`).

## 2. Anchoring in the real corpus

The examples must not be toy-only. Anchor them in the ResNet ARA dissected in `corpus-map.md` §3 so
reviewers see the abstraction on a claim they can recognize:

- **E1/E2** build on **C01** ("residual connections enable training of substantially deeper
  networks") — a real comparative claim from `resnet-ara-example`. E1 is the version where the
  controlled-experiment scheme's critical questions are all discharged; E2 leaves `external_validity`
  open to force a `gap`.
- **E3** uses **C01 + C02** and, critically, demonstrates the **dead-end discrimination**
  (`corpus-map.md` §3.1): node **N04 "vanishing-gradient hypothesis"** is a real `dead_end` that
  rules out an *alternative explanation* — it compiles to **no edge**, not an attack. E3 must include
  N04-as-non-attack alongside a *constructed* conflicting-measurement dead-end that *is* a typed
  `rebut`, so the example directly shows the differentiator: "a dead end is not automatically a
  defeater."

The constructed conflicts in E3 (needed to exercise undercut/undermine/contested) are clearly labeled
as synthetic extensions of the real artifact — honesty about what is real vs. constructed is itself a
reviewer trust signal.

## 3. Example-by-example specification

### E1 — `justified-clean` (status: justified)

Real C01 with a `controlled_experiment` scheme whose critical questions (randomization, adequate
power, baseline) are all discharged by declared leaves, no open holes, no attacks. Expected: the
single support argument is `in`; `status C01 = justified`. This is the "happy path" and the smallest
end-to-end pipeline test (leaf → scheme → support term → compile → grounded → aggregate).

### E2 — `open-gap` (status: gap)

E1 with `external_validity` left as an **open mandatory obligation** (`open external_validity`;
`lara-syntax@0.7`, grammar Appendix F.3 — a hole carries one name, the question it leaves open).
Expected: the incomplete argument is excluded from the AF (`spec.md` §4.4, §8), no complete
alternative exists, so `status C01 = gap` with located obligation `external_validity`. This is the corrected
definition of `gap` as an explicit hole, *not* underivability.

**Note — resolve the open definitional point first.** `spec.md` §8 leaves open what happens when a
hole coexists with a complete alternative. E2 as written has *no* alternative, so it is unaffected;
but add a variant E2′ once §8 is closed (`mechanization-plan.md` §5) to witness the decided behavior.

### E3 — `defeat-suite` (statuses: defeated, contested, justified; attacks: all three)

The centerpiece. Three claim roots on the shared C01/C02 evidence base:

- **rebut** — a constructed dead-end reporting a *conflicting measurement* on C01's conclusion;
  `(concl(rebutter), concl(support))` is a declared `contrary` pair, the rebutted rule is defeasible.
  Drives its target claim to **defeated** (or contested if a surviving alternative exists).
- **undercut** — the real `distribution_shift` challenge to `external_validity(a1)` from `spec.md`
  §10, typed as `undercut d1 a1.rule` via a declared `exception`. Shows exact-instance targeting.
- **undermine** — a constructed challenge to a *leaf* (e.g. contests the measurement leaf itself),
  typed `undermine … a1/π.leaf` against a `contrary` of the leaf's proposition.
- **N04 as non-attack** — included and annotated as compiling to **no edge** (the differentiator).
- At least one claim must land **contested** (a cycle or mutual `undec`) and one **justified**
  (survives all attacks), so all four statuses appear in one graph.

Expected golden output enumerates every argument's grounded label, the responsible SCC for the
contested claim (a diagnostic obligation), and the four claim statuses.

### R1 — `undeclared-leaf` (rejected)

A support term references a leaf that is not declared / not admitted into `Gamma` (admission table
yields `reject` or the leaf is absent). Expected: located diagnostic naming the leaf and the term
position; **not** a `gap` (a `gap` is an open obligation, not an undeclared reference).

### R2 — `strict-contrary-violation` (rejected at compile time)

A policy declares a `contrary` pair whose side may overlap a **strict-reachable** pattern at the
ground-instance level (a strict rule's consequent or something on a strict chain). Expected: the §8.1
Path-B well-formedness check rejects the *program* at compile time with a diagnostic naming the
offending rule and contrary pair
(`spec.md` §8.1). This example is the human-readable witness that the consistency guarantee is
enforced, not just proved.

### R3 — `bad-attack-target` (rejected)

An attack attempts to **rebut or undercut a strict rule**. Expected: rejected — strict rules are
deductively valid and unattackable (`spec.md` §7; ASPIC+ strict rules are unnamed). Diagnostic names
the attack, the target position, and that the target's rule is strict. Witnesses that attack
construction is inside the trust boundary: the checker refuses an ill-typed edge rather than
compiling it.

## 4. Deliverables and sequencing

- **Format.** Each example is a directory: `example.lara` (presentation), `example.core.sexp`
  (serialized AST / differential anchor), `expected.json` (golden verdict + diagnostics), and a short
  `README` explaining what capability it witnesses and what is real vs. constructed.
- **Test wiring.** Golden tests assert checker output equals `expected.json`; the same `.core.sexp`
  feeds the Haskell↔Lean differential test once the mechanization track is live
  (`mechanization-plan.md` §3).
- **Sequencing.** E1 is the **vertical-slice target** — buildable now on the two carve-out layers
  (`Lara.Prop`, `Lara.Strict.ND`) plus a hand-authored support term and stub policy
  (`engineering-plan.md` §3, the vertical slice). E2/E3 and R1–R3 require corpus-gated layers
  (`Policy`, `SupportTerm`, `Attack`) and so land after M0 fixes the rule/attack shapes. Write all
  six *specifications* now (this doc); implement E1 with the vertical slice; complete the rest as the
  layers land.
- **Paper mapping.** E3 is the figure that carries the contribution (the differentiator). E1/E2 are
  the pipeline walkthrough. R1–R3 are the "the checker actually refuses bad input" evidence. Together
  these match the venue calibration's five headline items: a novel typed claim-support calculus, a
  semantics-preserving compilation into structured argumentation, mechanized accountability and
  status theorems, an implementation with replayable diagnostics, and an evaluation showing
  localization on real research artifacts.

## 5. Relationship to the full evaluation

These six are **worked examples**, not the evaluation corpus. The stratified corpus study (M0) and
the four-axis evaluation are separate and larger. The worked examples
prove the calculus *works and is legible*; the corpus proves it *covers reality*. Per the current
decision, quantitative benchmarking is out of scope for the first submission — which raises the bar
on these examples plus the metatheory to carry the empirical weight, so E3's differentiator and the
R-series rejections must be airtight.

## 6. External corroboration (deep-research, 2026-07-21, adversarially verified)

The research pass on POPL/PLDI evaluation norms sharpens two things about this set:

- **The R-series is not a footnote — it is the soundness evidence, and it must be *adversarial*.**
  Clover (arXiv 2310.17807) is the exemplar reviewers respect for a trusted-checker: it reports high
  acceptance on correct instances *and* **zero false positives on deliberately-incorrect (adversarial)
  instances**. That is exactly what R1–R3 plus the full mutation suite must demonstrate — every
  mutant/ill-formed program is *rejected*, and any accepted one is a soundness bug, not a metric miss.
  Frame R1–R3 (and the mutation suite, `engineering-plan.md` §5) as the "no false positives" result,
  and report the **kill rate** (fraction of rejection-class mutants correctly refused) as the headline
  number, since benchmarking is otherwise out of scope.
- **"Spans every status" needs a coverage argument, not an assertion.** Feature-sensitive coverage
  over a mechanized specification (OOPSLA 2023 / TOSEM 2026) applies graph-coverage criteria to
  inductive semantic definitions. Once the Lean reference exists (`mechanization-plan.md` §3), report
  **rule/status coverage of the six examples over the mechanized grounded semantics** — this turns the
  §1 coverage matrix from a claim into measured evidence that every status (in/out/undec →
  justified/defeated/contested/gap) and every attack constructor is exercised.

Both are cheap to add and directly answer the two open questions the research left unresolved (how to
show status coverage; whether mutation kill-rate is expected alongside coverage). Given benchmarking
is out, these two framings carry disproportionate weight.
