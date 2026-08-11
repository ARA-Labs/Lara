# Sorts in the checker: `lara-core@0.2` and a real R2

**Goal:** make well-sortedness a *checked* property of the unit. Today `num_lt(sys_new,
accuracy)` is a well-formed `Prop`: on a strict step `ord@1` catches it late as an R13
replay rejection — a type error surfacing as an evidence failure — and on a defeasible step
nothing catches it at all. A declared, static, many-sorted signature carried in `Unit` and
enforced in `checkUnit` turns that into a located R2 at the earliest honest point, and
fills the one rejection class the spec reserves and no implementation has ever enforced.

**The invariant that makes this expensive:** unlike the surface track, this plan *does*
move the core. Σ enters `Unit`, the wire bumps to `lara-core@0.2`, the six-stage checker
becomes seven stages in both languages, `docs/spec.md` §10.1 needs an amendment to a frozen
class, and every generated artifact is regenerated. There is no version of this that is
additive-over-the-surface, which is why #89 left the #91 tracker.

**Scope boundary.** The measurand *polarity* table stays on the surface track
(`plans/2026-08-08-lara-syntax-03-surface.md` §3.1); it never enters `Unit`. This plan
extends the same declaration it introduces rather than forking a second one (that plan's
F7). #90 and #88a do not wait on this and are not touched by it.

Issues: #89 (this plan). Related: #91/#90/#88 (surface track), #87 (binding audit — see
§8's denominator hazard), #60 (paper package — see D-4).

**Status:** IMPLEMENTED (branch `feature/89-sorts-in-checker`). D-4 — the one open sign-off,
the scheduling question of whether this lands inside the #60 submission window — was decided by
the user in favour of implementing now; the regeneration's two measurement diffs both came back
empty, so the evaluation table this decision was protecting did not move.

Delivered: D0–D11. What was scoped differently from the plan is recorded in §13.

---

## 1. What exists today

**Σ exists and is never read.** `src/Lara/Elaborate/Internal.hs:73`:

```haskell
-- v0.1 Σ-arity checking (rejection class R2) is __outside the executable core__,
-- so the elaborator carries Σ for shape only and performs __no__ arity check
newtype Sigma = Sigma {sigmaArities :: [(Pred, Int)]}
emptySigma           = Sigma []
defeasibleSuiteSigma = emptySigma
```

It is threaded through `elaborate` and `prepareSource` (`Elaborate/Internal.hs:149,163`)
and every construction site passes `defeasibleSuiteSigma`, which is empty
(`RunningExample.hs:75`, `ClaimSupport/Load.hs:59`). Nothing consults it.

**`Unit` has no signature field.** `src/Lara/AST.hs:794-806` carries ten fields — rules,
contraries, exceptions, theories, leaves, args, attacks, queries, groups, group mode. Lean's
`Lara.Unit` (`lean/Lara/Unit.lean`) is the same object as `policy / args / atts`.

**There is no constructor table at all.** `[(Pred, Int)]` cannot represent `FunSym`
arities, so `score_cell/4` vs. `score_cell/3` is not merely unchecked — it is not
*expressible*. Spec §2's "separate arity tables for predicates and function symbols" was
never implemented on the constructor side.

**R2 is not exercised anywhere.** `docs/rejection-surface.md:93-98` lists R2 as one of two
classes "not individually anchored above because they are exercised only inside larger
worked cases". For R8 that is true. For R2 it is not: `fixtures/mutants/MANIFEST.tsv` has
**zero** `reject-R2` rows across all 369 mutants, and no `examples/` directory produces one.
R2 is unexercised, not under-anchored, and that sentence is wrong today (D7 fixes it).

**Rule well-formedness is unenforced.** Spec §4.1 — every variable in premises,
conclusion, answers, and exceptions is among `ruleParams`, and symbol arities match Σ — is
documented at `AST.hs:316` as *"a checker obligation, not enforced by the datatype"*, and
it is enforced by no checker either. `Lara.Policy.firstViolation` (the R12 stage) covers
only §8.1's strict-conclusion/contrary overlap.

---

## 2. Σ: the object

### 2.1 Shape

```
sort System, Measurand, Dataset, Experiment, Cell

con  score_cell(System, Measurand, Dataset, Num) : Cell
pred reports(Experiment, Cell)
pred num_lt(Num, Num)
pred better(System, System, Measurand, Dataset)
```

- **Two base sorts are built in:** `Num` and `Str`, the sorts of `TNum` and `TStr`. Not
  declarable, not shadowable.
- **Declared sorts are opaque names.** No subtyping, no sort variables, no sort
  constructors; sort equality is name equality. This is a first-order signature and
  nothing more.
- **`sortOf` is a simple recursion**, total except on undeclared symbols:
  `sortOf(TNum _) = Num`; `sortOf(TStr _) = Str`; `sortOf(TCon k ts)` is `k`'s declared
  result sort provided `|ts|` equals `k`'s arity and each `sortOf(tᵢ)` equals `k`'s
  declared *i*-th argument sort.
- **Arity is subsumed**, not replaced: it is the length of the argument-sort vector, so the
  old `[(Pred, Int)]` is recoverable as `map (second length)` and the new Σ is strictly
  stronger on every axis (#89 §6). Since the old was never read, the enforcement delta is
  from zero.
- **Rule parameter sorts are derived, not declared** (eng review 2026-08-10, OV-3). Under a
  validated Σ every parameter occupies sorted positions in its rule's own patterns; its
  sort is the unique sort of all its occurrences, and disagreeing occurrences are a
  stage-2 reject. A parameter with no pattern occurrence is unconstrained (its θ bindings
  are checked vacuously). No rule-grammar change, no ninth wire field in the `rules`
  section, no stored `Rule` field — the derivation rule is spec text in §3.

**What this still does not give**, and deliberately: `num_lt(0.71, 0.74)` is well-sorted
whether those numbers are accuracies, BLEU scores, or learning rates. Measurand identity
stays in the `comparison_setup` binding leaf and stays defeasible. `examples/S4` attacks
exactly that leaf and must keep working unchanged.

### 2.2 Surface: extends the measurand declaration, never forks it

The surface track's `measurand accuracy : Num where higher-is-better` was written with the
`: Num` slot deliberately a *sort position* (`plans/2026-08-08-lara-syntax-03-surface.md`
§3.1, F7). Σ's `sort` / `con` / `pred` blocks live in the same policy header and share that
slot's grammar. One declaration surface, two consumers: the elaborator reads polarity and
drops it; the wire codec reads sorts and carries them into `Unit`.

**Polarity is `Num`-gated** (eng review 2026-08-10, OV-6). The slot admits any declared
sort — that is D-1 — but a polarity clause (`higher-is-better` / `lower-is-better`)
presupposes an ordered domain and only `Num` is ordered, so the clause is well-formed only
on `Num`-sorted measurands, rejected by the surface elaborator otherwise. Surface-side
check, core untouched; the surface track's §3.1 gains the same side condition (its own
one-line sign-off).

### 2.3 The class boundary — what R2 is, and what it is not

**R2 answers exactly one question: is this term well-sorted under Σ.** It never answers
"does this identifier resolve" (R1), "is this substitution total" (R3), or "does this
conclusion match that pattern" (R4). Four consequences, and they are what keep the
existing mutation suite stable (§8):

1. **An undeclared *symbol* — predicate head or constructor — is R2, not R1.** R1 is about
   declaration identifiers (leaf, argument, rule, question, backend, policy); symbols have
   never been in its list.
2. **Arity mismatch is R2.** Already the frozen spec text; unchanged.
3. **A substitution whose *domain* is wrong is R3, not R2.** The sort stage checks the
   sorts of θ's range terms at keys that *are* declared parameters, and says nothing about
   whether θ covers every parameter. Domain totality remains R3's sole business.

4. **An instance whose rule id does not resolve in the policy is R1's business.** The
   θ-range check (§3.2) quantifies only over instances whose `SRule` rule id resolves;
   an unresolved id is left to R1 at the support stage. The 19 existing `hidden-rule`
   mutants are the executable witness — they must stay R1, not become a stage-2 lookup
   error.

Rules 3 and 4 are not stylistic preferences. They are the difference between a
regeneration that moves the paper's per-class evaluation table and one that does not (§8).

---

## 3. Where the check runs

Σ's whole journey, both doors converging on the one checked path:

```
 .lara policy header                          raw .sexp door
 sort / con / pred blocks                          │
        │                                          │
        ▼                                          ▼
   Syntax.hs parse ──► Elaborate ──► Unit.unitSigma ◄── Wire `sigma` section
   (D4)                (reads+drops   (D3)              (D5, lara-core@0.2)
                        polarity)          │
                                           ▼
                              checkUnit stage 2 (D6)
                              ├─ static: Σ-WF (dups, undeclared sorts,
                              │  base-name shadowing) + policy/Γ/queries/
                              │  theories under derived param sorts
                              └─ per-instance: θ-range sorts at resolvable
                                 rule ids only (§2.3 rules 3-4)
                                           │
                                           ▼
                              CheckedUnit.sigma_wf / policy_well_sorted /
                              args_well_sorted (D9)
                                           │
                                           ▼
                              checkUnit_wellSorted  ← the paper's citation
```

### 3.1 Seven stages

`checkUnit`'s public stage order is currently six, identical in both languages
(`src/Lara/Check.hs:1-13`, `lean/Lara/Check/Unit.lean`). The sort stage inserts at
position 2:

| # | stage | change |
|---|---|---|
| 1 | duplicate rule identifiers | — |
| 2 | **Σ well-formedness + well-sortedness (R2)** | **new** |
| 3 | R12 policy well-formedness (`firstViolation`) | absorbs spec §4.1 rule WF (§3.3) |
| 4 | duplicate arguments | — |
| 5 | support | — |
| 6 | typed attacks | — |
| 7 | missing conflict | — |

**Why position 2.** Σ conformance is a precondition for reading the policy as patterns at
all. Both the R12 Path-B validator and support inference instantiate patterns; both should
be entitled to assume well-sortedness rather than re-derive it. Running after duplicate-rule
detection means the stage never has to reason about which of two same-named rules it is
checking.

Both languages move together, and the "six-stage" prose in `Check.hs:1-13` and in
`Check/Unit.lean`'s docstring is pinned text that must change in the same commit.

### 3.2 A static half and a per-instance half

**Static — Σ against the policy and the context.** One pass, no support terms:

- Σ itself: no duplicate `sort` / `pred` / `con` declarations; no declaration reusing a
  reserved base sort name (`sort Num` and `sort Str` are stage-2 rejects, not silent
  shadows — eng review 2026-08-10, finding 4); every sort named in a signature is declared;
- every rule's premise patterns, conclusion pattern, answer patterns, and exception
  patterns, well-sorted under Σ extended with the rule's derived parameter sorts (§2.1);
- every `contrary` pair and every `exception`;
- every leaf conclusion in Γ, every query, every proposition in the theory table.

**Per-instance — Σ against `unitArgs`.** Required, and the reason is not thoroughness:

> θ's range terms are *authored*, not drawn from Γ. A rule instance's **conclusion** is
> θ-instantiated and need not match any leaf, so an ill-sorted range value produces an
> ill-sorted argument conclusion that no other stage catches. Premises escape only
> incidentally — via R4's `≢`-match against a leaf that the static half already sorted.

So the stage also walks `unitArgs` and checks, for every `SRule r θ …` **whose rule id
resolves in the policy** (§2.3 rule 4) and every `(X, t) ∈ θ` with `X ∈ ruleParams r`,
that `sortOf(t)` equals `X`'s derived parameter sort. That is the smallest per-instance
check that closes the hole, and by §2.3 rule 3 it touches nothing about θ's domain.

**This creates the pass's central proof obligation** (§6): static half + θ-range check must
together imply that *every* proposition reachable in an accepted unit is well-sorted —
including the instantiated patterns nobody checks directly. That is a substitution lemma,
and it is the load-bearing metatheory of this pass rather than a lemma-shaped afterthought.
It is also what licenses the per-instance half being as thin as it is.

### 3.3 Absorbing rule well-formedness (#89 §8)

Spec §4.1's obligation is unenforced (§1) and wants the same Σ, the same traversal, and the
same stage neighbourhood. Fold it in — but **as R12, inside stage 3**, not as a second
class emitted from stage 2. Out-of-scope pattern variables are policy well-formedness, which
is R12's existing territory; keeping them there leaves R2 purely about sorts (§2.3) and
leaves each stage emitting exactly one class. Concretely: extend `Lara.Policy.firstViolation`
with new `Violation` constructors and give it the Σ that stage 2 has already validated.

---

## 4. The spec amendment

The new Σ is stronger than the **spec's** R2, not merely stronger than the implementation.
`docs/spec.md:1339`:

> | **R2** signature | arity or symbol mismatch against `Sigma`; non-ground term where ground required | the offending term | §3, §4.1 |

Sort mismatch is not in that definition, and §10.1 freezes fourteen classes. This widens a
frozen class. Of #89 §7's three options, take **option 1 — amend R2 in place**: it widens a
class no implementation has ever enforced, so no existing behavior changes and no other
class moves. A new R15 adds to a frozen list for no benefit; a split gives two classes for
one pass and is harder to explain.

Proposed replacement row:

> | **R2** signature | undeclared predicate or constructor symbol; arity mismatch against Σ; argument-sort or result-sort mismatch against Σ; a rule-parameter binding whose term's sort differs from the parameter's derived sort (§2.1) | the offending term | §3, §4.1 |

**The dropped clause is vacuous by construction, and should be recorded as such.** "Non-ground
term where ground required" has never been violable: `Term = TNum | TStr | TCon` has no
variable constructor, so every `Prop` is ground *structurally*, and `PVar` exists only in
`Pat`. It is removed rather than left looking unimplemented, with a footnote saying why —
otherwise a reader reasonably concludes a check went missing.

**Two governance items, not one.** The row above amends frozen §10.1 and needs its own
sign-off, the same discipline as the surface track's §7 amendment. Defining Σ, `sortOf`, and
well-sortedness requires **new** spec text in §3 — additive, not an amendment, but it should
be reviewed as its own artifact rather than smuggled in beside the table edit.

---

## 5. Wire: `lara-core@0.2`, hard cutover

`Wire.hs:815-824` takes the `unit` sections in fixed order and errors on any leftover
(`"unexpected section: "`), and `CoreVersion` has one constructor
(`coreVersionText LaraCoreV01 = "lara-core@0.1"`, `Wire.hs:1081-1082`). A `sigma` section
therefore requires the version bump.

**Hard cutover** per #91 decision 5: no dual-version decoder, `LaraCoreV01` retired. Nothing
is released, so there is no external compatibility burden. Two consequences worth naming:

- the replay-id grammar embeds the core version (`Wire.hs:33`), so **every** `.sexp`
  carrying a replay section changes bytes, not only those with a signature;
- the `codec-core-version` mutation family (8 mutants) asserts that an unsupported core
  version is a codec reject. Its fixture text moves; its expectation does not.

---

## 6. Mechanization

Per CLAUDE.md's discipline these land **with** the code, not after it.

**New Lean module `lean/Lara/Sigma.lean`:** sorts, predicate and constructor signatures,
`sortOf`, `WellSorted` for `Term` / `Atom` / `Pat` / `Rule` / `Policy`, and decidability
instances.

**Extended objects.** `Lara.Unit.Unit` gains `sigma`. `Unit.CheckedUnit` gains
`sigma_wf` and `policy_well_sorted` alongside its existing `ruleIds_nodup` / `policy_wf` /
`attack_complete` / `nodes` / `nodes_terms` fields, plus a program-level `args_well_sorted`.
`Lara.Check.Unit.checkUnit` gains the stage, and `checkUnit_sound`'s conjunction extends
with the new components.

**`docs/mechanization-plan.md` gains result 13 — well-sortedness is decidable and preserved
by rule instantiation.** Two theorems and one payoff:

| | statement |
|---|---|
| `wellSorted_decidable` | the executable check decides the relation |
| `wellSorted_subst` | if a checked pattern is instantiated by a sort-respecting θ, the resulting atom is well-sorted |
| `thetaWellSorted_ruleSortRespecting` | stage 2's θ-range check plus accepted support's exact-domain invariant (R3) discharges the substitution lemma's θ premise |
| `checkUnit_wellSorted` | every actual rule instance recursively reachable through an accepted support term contributes only well-sorted instantiated premises, conclusions, and answers; the unit's ground environment is well-sorted under the same Σ |

`checkUnit_wellSorted` is the statement the paper cites and the justification for §3.2's
scoping: it closes the executable θ check over the accepted support terms rather than assuming
`RuleSortRespecting` for arbitrary substitutions.

`AxCheck.lean` gains `import Lara.Sigma` and a `#print axioms` line per new theorem. The
gate is unchanged: no `sorryAx`, nothing outside `propext` / `Classical.choice` /
`Quot.sound`.

**`lean/Lara/Presentation.lean` re-syncs here, not later** (eng review 2026-08-10,
finding 2). The presentation mirror is already two features stale (no theories, no
groupMode — recorded 2026-08-09) and its re-sync currently rides the surface track's D8.
This plan adds signature blocks to the surface; leaving the mirror behind narrows
result 12 (round-trip) a third time. D9 therefore includes: the `sigma` block mirrored in
`Presentation.lean`, the round-trip lemma extended over signature-bearing policies, and a
coordination note against `plans/2026-08-08-lara-syntax-03-surface.md` D8 so the two
tracks do not collide in the same file. (Rule parameter sorts need no mirror — they are
derived, §2.1.)

---

## 7. Authoring Σ for `corpus-v1`

Strict mode (#91 decision 2) gates on a complete signature for **every** policy in the
tree, so this is a real task with its own review — and **it is roughly three times the
size #89 §5.1 estimates** (eng review 2026-08-10, outside voice 1). Recounted against the
tree:

| | §5.1 estimate | actual |
|---|---|---|
| corpus units | 30 | **60** (`corpus-units/*/*/`, each `unit.lara` + `unit.core.sexp` + `expected.json`, under 27 paper directories) |
| policy rules | 13 | **17** `rule` occurrences in `corpus-v1.policy.lara` |
| symbol heads | ~35 predicates | **96** distinct `name(` head tokens across the `.lara` files — but that sweep conflates predicates with constructors |
| nullary constants | *uncounted* | **~239** distinct bare-identifier argument tokens — each a `TCon k []` constant (`Prop.hs:75-77`) needing a `con k : Sort` declaration. **The dominant term, missed by the head-token grep.** |
| other policies | *uncounted* | 8+ `examples/` policies (`empirical-v1`/`v2`, `ord-v1`, `ord-le-v1`, `ord-setting-v1`, `strict-v1`, `strict-bad-v1`, `agreement-v1`), the `mutation-cycles-v1` synthetic unit (§8), and every constructed unit in six test spec files currently built against `emptySigma` |

The counts are upper bounds, not the census. They should not be refined by better
grepping: separating predicate heads from constructor heads and sorting the nullary
constants is exactly what the Σ-inference tool does, and the census is its first output.

**`scripts/infer-sigma.hs` is the bootstrap, is tooling, not a language feature (#89 §2) —
and it runs first.** It is a small sort-inference pass, not a sweep: a nullary constant
has no argument positions, so its sort must be inferred from the predicate and constructor
argument positions it *occupies*, and a constant appearing under two heads forces those
positions to share a sort — union-find over occurrences. The tool needs only the existing
parser, so it is **step 0 of the implementation order**: its output — the true symbol
census and the finest consistent sort partition — sizes D8 before anything freezes.
Separate reviewable script, generated-then-edited, never hand-transcribed — the same
discipline #95 applied to the audit worklist.

**The inferred partition IS the sort structure; human judgment is merge-and-name, not
authoring** (eng review 2026-08-10, OV-2). The tool's finest consistent partition ships
with generated opaque sort names (`S1, S2, …`); the human pass merges obvious duplicates
and names only the sorts the paper displays. Whether `imagenet_val` is a `Dataset` or an
`EvalSetting` is precisely the possible-worlds question, and an opaque name presumes no
answer — the curated naming pass is a tracked follow-up gated on that design (TODOS.md).
The finest partition also maximizes `wrong-arg-sort`'s corpus sites, keeping R2
non-vacuous on real data.

**The merge pass is gated** (OV-5): every human merge re-runs the new operators'
site-count assertion (§8) — a merge that zeroes `wrong-arg-sort`'s corpus sites fails the
gate and must be justified or reverted — and the frozen corpus Σ must reject the
motivating example itself (`num_lt(sys_new, accuracy)`) as a committed negative, so the
plan's opening sentence is literally witnessed under the shipped signature, not only
under `examples/R2-sort`'s bespoke one.

---

## 8. Regeneration, and what the reclassification measurement actually is

#89 §3.1 predicts R2 will reclassify mutants and makes the delta a deliverable. **The
zero-delta expectation is achievable — but not for free** (eng review 2026-08-10,
finding 1). The full well-formed inventory is 24 operators (30 `MutationOp` constructors
minus the six `OpCodec*`), and it splits in two:

Operators that reuse existing declared material are safe:

- `wrong-premise` (18 mutants, R4) swaps in `inequivLeaf` — an *existing* leaf from Γ,
  well-sorted by the static half (`Mutate.hs:600-613`);
- `wrong-subst-domain` (19, R3) renames a θ key to `mut_x` — a domain change, and R3 by
  §2.3 rule 3 (`Mutate.hs:584-598`);
- `undeclared-leaf` (25, R1) and `hidden-rule` (19, R1) substitute fresh *identifiers*, not
  terms — and rule 4 (§2.3) keeps hidden-rule instances R1 rather than a stage-2 lookup
  error;
- the certificate, attack-position, group, and replay operators never touch propositions.

**But three operator groups synthesize fresh undeclared symbols, which by §2.3 rule 1 are
R2:** `hidden-contrary` injects `mut_p`/`mut_q` predicates (`Mutate.hs:577-578`) and would
flip R12 → R2, stripping R12 of its only mutation family; the accept family injects
`mut_undermine_contrary` and `mut_quarantine_conflict` (`Accept.hs:252,272`) and would flip
accept-verdict mutants to reject-R2, destroying the status × attack-kind coverage matrix;
and `rebut-cycle` builds the whole synthetic `mutation-cycles-v1` unit from fresh
`holds`/`obs`/`c0..cN` vocabulary (`Mutate.hs:1028-1030`).

**The design commitment: generators become Σ-aware.** Σ travels per-unit, and the operator
that injects a symbol is exactly the site that knows its argument sorts — so every
symbol-injecting operator extends the mutant's carried Σ with the fresh symbol's
signature, and `mutation-cycles-v1` gets its own generated Σ. A mutant then tests the
class it seeds, not incidental Σ noise. With that in place the expected reclassification
delta over the 324 pre-existing well-formed mutants is **zero by design**, and the paper's
per-class table does not move. **This must still be verified by diffing the regenerated
`MANIFEST.tsv` `expected` column against the current one — not assumed.** That diff *is*
the measurement, and "empty" is the claim being made.

Had §3.2's θ check been scoped to include domain totality, `wrong-subst-domain`'s 19 R3
mutants would have become R2 and the table would have moved. That is why §2.3 rules 3 and 4
are design commitments and not details.

**The real gap is the opposite one.** Spec §10.1 states its own invariant: *"every class
must be exercised by at least one rejected example and one mutation."* R2 satisfies neither
(§1). This pass must therefore **grow** the suite, not merely re-run it — one operator per
clause of the amended class:

| operator | mutation | expected |
|---|---|---|
| `undeclared-pred` | rewrite an atom's head to an undeclared `Pred` | `reject-R2` |
| `wrong-pred-arity` | drop or duplicate an atom argument | `reject-R2` |
| `wrong-arg-sort` | replace an argument with a well-sorted term of a *different* sort taken from the same unit | `reject-R2` |
| `undeclared-con` | rewrite a `TCon` head to an undeclared `FunSym` | `reject-R2` |
| `wrong-theta-sort` | replace a θ range term with a different-sorted one at a declared parameter | `reject-R2` |
| `out-of-scope-var` | rewrite a rule pattern variable to one not in `ruleParams` (premise / conclusion / answer / exception positions) | `reject-R12` |

`wrong-theta-sort` is the per-instance half's own witness: under a static-only design it
would be accepted, so it is the executable statement of §3.2's argument. `out-of-scope-var`
is §3.3's witness (eng review 2026-08-10, finding 7): the extended `firstViolation` arm is
new enforcement and must not land witness-free the way R2 once did.

**Suite additions beyond the operators** (eng review 2026-08-10, findings 9, OV-5; scope
gate):

- **Σ-WF negatives**: duplicate `sort`/`pred`/`con` declarations, a signature naming an
  undeclared sort, and `sort Num` builtin shadowing — each a stage-2 reject with a
  dedicated negative;
- **`OpCodecSigma` rows** in the malformed family: junk inside the `sigma` section and
  `sigma` out of the fixed section order → R14, exit 2 — the new section decoder gets the
  same corruption coverage every other section has;
- **applicability anti-vacuity**: generation asserts each new operator's corpus site count
  is nonzero (reported in the manifest like the B=12 applicability) — `wrong-arg-sort`
  must not pass forever on hand-built examples alone; the same assertion re-runs in §7's
  merge gate;
- **bundled suite-extension TODOs** (scope gate 2026-08-10): the drop-covering-attack
  operator (`reject-MissingConflict`, standalone conflict-scan ablation evidence) and the
  wrong-fraction `ra@1` certificate operator (`reject-R13`, semantic cert corruption) ride
  this same regeneration cycle instead of forcing two future freeze tags;
- the new operators land in the pending `Lara.Mutate` split modules (TODOS.md), not in the
  ~900-line `Lara.Mutate`.

Plus one negative example. **It cannot be called `examples/R2`** — that directory already
holds the R12 demonstration, a naming collision the docs apologize for in three places
(`docs/rejection-surface.md:89,96-98`). Use `examples/R2-sort/` and do not compound the
collision.

**Regeneration scope, corrected:**

| artifact | count | generator |
|---|---|---|
| well-formed mutants | 324 → 324 + N | `scripts/gen-mutants.hs` (Σ-aware) |
| malformed mutants | 45 → 45 + sigma rows | ditto (core-version fixtures move) |
| `MANIFEST.tsv` rows | 369 → 369 + N | generated |
| corpus units | **60** × 3 files | `scripts/gen-corpus-units.hs` |
| example cores | `examples/*` (policies gain Σ) | generated |
| `measurements/frozen/` | all | measurement harness |
| freeze tag | new | `docs/m5-freeze-checklist.md` |
| **`measurements/binding-audit/**`** | **excluded — frozen input, never regenerated** | — |

**Cross-issue hazard — answered** (eng review 2026-08-10, finding 3; was open decision
D-5). The audit's sealed identity hashes the exact bytes of `worklist.tsv`,
leaf-results, and object-results (`plans/2026-08-09-binding-audit-results.md`:
"`git hash-object --stdin` digest of the exact worklist, leaf-results, and object-results
bytes") — **not** corpus `.sexp` bytes — and no worklist column carries the core version
or wire bytes, so the wire bump cannot reach the 38-leaf denominator. Regeneration is
therefore safe under one written rule: `measurements/binding-audit/**` is frozen input,
excluded from D11 (table row above). Pre-D11 verification: re-run the worklist derivation
into a temp file and byte-compare against the committed `worklist.tsv`; a non-empty diff
reopens D-5 before anything regenerates.

---

## 9. Deliverables

**D1 — spec.** `docs/spec.md`: the §10.1 R2 amendment with its vacuity footnote, plus the
new §3 subsection defining Σ, `sortOf`, and well-sortedness. Two sign-offs (§4). **Gates
everything below.**

**D2 — `Lara.Sigma` (Haskell).** The object, `sortOf`, the well-sortedness relations, the
decision procedure. New module; `Sigma` leaves `Elaborate.Internal`, since it is no longer
an elaborator-private shape.

**D3 — `AST.hs`.** `Unit` gains `unitSigma`; rule parameter sorts are **derived, not
stored** (§2.1 — no `Rule` field, no wire change to the `rules` section). Expect
construction-site churn on every module that builds or matches a `Unit`.

**D4 — grammar, parser, printer.** `docs/lara-surface-grammar.md` §4 policy signature block;
`src/Lara/Syntax.hs` parse and print, round-tripping raw.

**D5 — wire.** `Wire.hs`: the `sigma` section, `lara-core@0.2`, `LaraCoreV01` retired (§5).

**D6 — checker.** `Check.hs` stage 2 (§3.1-3.2); `Lara.Policy.firstViolation` extended with
spec §4.1 rule WF under R12 (§3.3).

**D7 — rejection surface.** `docs/rejection-surface.md`: R2 promoted to an anchored row with
a verified transcript; the §93-98 note corrected (R2 is unexercised today, not
under-anchored); the groundness clause marked vacuous.

**D0 — Σ inference tool (runs first).** `scripts/infer-sigma.hs` as §7 specifies:
union-find sort inference over predicate/constructor argument occurrences, nullary
constants included; first output is the true symbol census and finest consistent
partition. Needs only the existing parser — no dependency on D1-D7.

**D8 — Σ for every policy in the tree** (§7; eng review 2026-08-10, OV-4). The
merge-and-name pass over D0's partition for `corpus-v1` (opaque names, merge gate,
motivating-example negative); per-policy Σs for the 8+ `examples/` policies; a shared
test-fixture Σ helper so the six spec files' constructed units (`CheckSpec`,
`AdmissionSpec`, `WorkedExamplesSpec`, `BlockedSpec`, `ReportingSpec`, `RuntimeSpec`) are
Σ-coherent without six divergent copies; `RunningExample.hs` and `ClaimSupport/Load.hs`
move off `defeasibleSuiteSigma`.

**D9 — Lean.** `lean/Lara/Sigma.lean`; `Unit` / `CheckedUnit` / `checkUnit` /
`checkUnit_sound` extended; result 13's theorem suite; `AxCheck.lean` extended;
`Presentation.lean` carries an explicit scope caveat for the two deferred fields (§6).
*(Superseded 2026-08-11: the caveat is gone — the mirror now carries both fields. See §13's
post-closeout paragraph.)*

**D10 — suite.** The six shipped sort mutation operators, the unit-level Σ-WF fault matrix,
and the wire-decoder malformed-Σ matrix. Generated Σ-WF fixtures and `OpCodecSigma` remain
deferred under §13.

**D11 — regeneration + measurement.** The shipped subset of §8's scope table
(binding-audit and the §13 deferrals excluded), plus two committed diffs reported as results:
the `MANIFEST.tsv`
`expected`-column diff over the 324 pre-existing mutants **and** the verdict diff over all
60 corpus `expected.json` files — both with "empty" as the claim (§10).

Order: **D0 → D1 → D2/D3 → D4/D5 → D6+D9 → D7 → D8 → D10 → D11.** D0 runs before even D1
— its census sizes D8 and informs the §3 spec text. D9 lands with D6, not after D11 — the
mechanization discipline is that frozen definitions get proved when they freeze, and D6 is
where they freeze.

---

## 10. Verification

- **The acceptance set does not shrink — verified mechanically, not by prose.** Every
  currently-accepted unit still accepts under its authored Σ. This is strict mode's real
  risk: an over-tight Σ silently rejecting valid corpus units reads as a checker
  improvement and is a regression — and D11 *regenerates* `expected.json`, which would
  write the flip into the new baseline. So the check is a **committed verdict diff over
  all 60 corpus `expected.json` files across the regeneration boundary** (old verdicts vs
  new, claim: empty), and the same diff is D8's merge gate before the Σ freezes (eng
  review 2026-08-10, finding 8).
- **The `expected`-column diff over the 324 pre-existing mutants is empty** (§8), and the
  diff is committed as the measurement rather than asserted in prose.
- **The corpus Σ rejects the motivating example.** `num_lt(sys_new, accuracy)` is a
  committed negative under the frozen `corpus-v1` Σ specifically (§7's merge gate), not
  only under `examples/R2-sort`'s bespoke signature.
- **Σ-WF negatives and `OpCodecSigma` rows reject as specified** (§8), and each new
  operator's corpus site count is nonzero at generation and after every Σ merge.
- **The 19 `hidden-rule` mutants still reject R1** — the executable pin of §2.3 rule 4.
- **The six spec files' fixtures pass under the shared Σ helper** with no test weakened to
  expect a stage-2 reject that was an accept before (D8).
- **One new mutant per new operator rejects R2 in both languages, with byte-identical
  diagnostics** — the Haskell/Lean differential is the conformance evidence, as everywhere
  else.
- **A dedicated θ negative:** a unit whose *conclusion* is ill-sorted only through θ, which
  the static half alone would accept. This is the executable form of §3.2's argument and
  must exist as a test, not only as a mutant.
- **`parse ∘ print = id`** extended over policies carrying signature blocks, with the
  QuickCheck generators extended and a `cover`/`label` assertion so the property cannot pass
  vacuously — the surface track hit exactly this trap (its 9A).
- **`lake env lean AxCheck.lean` clean:** no `sorryAx`, axioms within the standard trio.
- **`cabal test all` green**; `measurements/frozen/` regenerated; the freeze checklist
  re-run and a new tag cut.

---

## 11. Non-goals and deferred

- **Measurand-indexed numeric sorts** (`Num[accuracy @ imagenet_val]`), which would make
  comparing an accuracy against a BLEU score a sort error. Attractive here and deferred for
  a reason: it is a units-of-measure design that starts eating `comparison_setup`'s job and
  converts something currently *attackable* into something *statically rejected*. That is a
  change to what the calculus claims, not an enforcement improvement. It rides with the
  possible-worlds direction.
- **Sort inference as a language feature.** Inference is tooling only (§7). LARA terms are
  ground first-order with no abstraction, application, or polymorphism, and no site to put
  an annotation — a declared signature already delivers the zero-annotation property
  inference would have been for.
- **Open mode / undeclared-symbol tolerance.** Strict per #91 decision 2. The fallback can
  be added later without changing the Σ syntax if the friction proves obstructive (#89 §5.2).
- **Polarity in `Unit`.** Stays surface-only, forever; nothing downstream consumes it.
- **The surface track.** #90 and #88a are independent and must not be sequenced behind this.

---

## 12. Decisions needing sign-off before implementation

| # | decision | recommendation |
|---|---|---|
| **D-1** | Does the `measurand` declaration's sort slot admit declared sorts other than `Num`? (§2.2) | Yes — the slot is a sort position; restricting it to `Num` re-forks the declaration F7 exists to prevent. **Amended (eng review 2026-08-10, OV-6):** polarity clauses are well-formed only on `Num`-sorted measurands — the slot is open, the `where` clause is `Num`-gated |
| **D-2** | Rule WF rejects as R12 via extended `firstViolation`, or as a second class out of stage 2? (§3.3) | **R12** — one class per stage, R2 stays purely about sorts |
| **D-3** | Spec amendment shape: widen R2, add R15, or split? (§4) | **Widen R2** — no behavior changes, no other class moves |
| **D-4** | Timing against #60. This plan's implementation sits outside the submission window (#91 decision 4). | Confirm. The regeneration touches `measurements/frozen/` and the evaluation table; doing it mid-draft is the wrong order even though §8 predicts the numbers hold. **Still open — the one remaining sign-off.** |
| **D-5** | Can regeneration move #87's 38-leaf audit denominator? (§8) | **Answered (eng review 2026-08-10):** no — the sealed identity hashes worklist/results bytes, none core-version-dependent, provided `measurements/binding-audit/**` is excluded from D11 (written into §8's table) and the pre-D11 byte-compare passes |

## GSTACK REVIEW REPORT

| Review | Trigger | Why | Runs | Status | Findings |
|--------|---------|-----|------|--------|----------|
| CEO Review | `/plan-ceo-review` | Scope & strategy | 0 | — | — |
| Codex Review | `/codex review` | Independent 2nd opinion | 0 | — | — |
| Eng Review | `/plan-eng-review` | Architecture & tests (required) | 1 | ISSUES_RESOLVED | 9 issues (3 arch, 3 quality, 3 test) + 8 outside-voice findings; all 15 decisions resolved and folded into the plan |
| Design Review | `/plan-design-review` | UI/UX gaps | 0 | — | — |
| DX Review | `/plan-devex-review` | Developer experience gaps | 0 | — | — |

- **CROSS-MODEL:** Outside voice (Claude subagent; Codex timed out) found 8 issues the primary review missed — most materially the ~239 uncounted nullary-constant declarations (3x authoring cost), the rule-parameter-sort declaration gap (resolved: derived from patterns), and strict-mode coverage of the 8+ example policies and six test spec files. All verified against the repo and resolved OV-1A/2C/3C/4A/5A/6A.
- **VERDICT:** ENG REVIEWED — 15/15 review decisions resolved; plan amended in place (§§2-12, D0 added). Implementation remains gated on the plan's own sign-offs: D1's two spec sign-offs and D-4 below.

**UNRESOLVED DECISIONS:**
- D-4 (timing against #60): implementation sits outside the submission window per #91 decision 4 — the scheduling confirmation is the user's call and was not resolved by this review.


---

## 13. What landed, and where it differs from this plan

Every deliverable D0–D11 landed. Four scoping decisions differ from the text above, each
with its reason.

**Σ is a policy field, not a caller-supplied input.** The plan left `elaborate`'s `Sigma`
parameter in place and had D8 move its callers off `defeasibleSuiteSigma`. Instead the
parameter is *removed*: Σ comes from `policySigma`, so no caller can hand the elaborator a
signature the policy does not declare. `emptySigma` survives as the unit of the object (the
`Sigma [] [] []` a symbol-free unit carries), not as a permissive default.

**The Haskell deliverable is two modules, not one.** `Lara.Sigma` owns the object and ground
sorting; `Lara.Sigma.WellSorted` owns the pattern half and the stage. The split is forced by
the module graph — `Lara.AST.Unit` carries a `Sigma`, so `Lara.Sigma` cannot see `Lara.AST` —
and it keeps both files inside the 400-line rule.

**§3.3's R12 absorption is a second `UnitError` arm, not a widened `Violation`.** In Haskell
`Violation` did become a sum, as §3.3 recommends. In Lean it did not: `Policy.Violation`,
`WellFormed`, and `firstViolation_none_iff` are a proved correspondence that other results
cite, and reopening it to add a disjunct would have put a load-bearing frozen theorem at risk
for no behavioural gain. Lean adds `Policy.firstOutOfScope?` / `ScopesWellFormed` and a
`UnitError.scopeViolation` arm instead. Both drivers reject the same units with the same
class, in the same stage order — which `scripts/differential.sh` checks byte-for-byte over
574 fixtures.

**Lean's `checkUnit` takes the ground atoms as an argument.** §3.2's static half sorts Γ, the
theory table, and the queries. Lean's `Unit` deliberately carries Γ as a *function*, so those
finite lists are not on the unit. Storing them would have meant threading a new field through
every quarantine/prune reconstruction — including several proved unit equalities. Passing them
to `checkUnit` keeps the stage *order* identical between the two drivers, which is the property
that actually matters: a unit that is both duplicate-rule and ill-sorted-in-Γ must get the same
class from both.

### The one divergence mechanization caught

Lean's θ-range check inspected the range term at *every* θ key and consulted the
parameter list only afterwards, so an ill-sorted term at a **non-parameter** key
was R2 in Lean and R3 in Haskell. It was unreachable on the committed corpus —
`wrong-subst-domain` keeps a well-sorted term when it renames a key, which is
why the differential stayed green — but it is exactly the reclassification §2.3
rule 3 exists to prevent, and it would have moved the 19 `wrong-subst-domain`
mutants the first time an operator renamed a key onto an ill-sorted value.
Fixed, and pinned by a dedicated `CheckSpec` negative rather than left to the
next mutation operator to discover.

### Measurements, as taken

| claim | result |
|---|---|
| `MANIFEST.tsv` `expected`-column diff over the 369 pre-existing mutants | **empty** |
| verdict + status diff over all 60 corpus `expected.json` | **empty** |
| `measurements/binding-audit/worklist.tsv` re-derivation (pre-D11, decision D-5) | **byte-identical** |
| suite size | 369 → 496 mutants; `reject-R2` 0 → 107 |
| corpus census (D0's first output) | 27 sorts, 196 constructors (187 nullary), 54 predicates |
| differential | 574 fixtures byte-identical across both drivers; 54 negatives agree |
| axiom audit | clean — no `sorryAx`, nothing outside `propext` / `Classical.choice` / `Quot.sound` |

Both diffs are committed as a deliverable at
`measurements/frozen/lara-core-0.2-regeneration-diffs.md`, with the commands that produce them
and an account of why "empty" was not free.

### Deferred, and tracked

- **Dedicated generated Σ-WF negatives and `OpCodecSigma`.** `CheckSpec` now pins all six
  `SigmaFault` constructors plus declaration-order precedence, and `WireSpec` covers the malformed
  `sigma`/`sorts`/`cons`/`preds` decoder branches. What remains deferred is a generated committed
  negative fixture per Σ-WF clause and a mutation operator for codec corruption.
- **The two bundled TODO operators** (drop-covering-attack, wrong-fraction `ra@1`), which §8
  put on this regeneration cycle to avoid two future freeze tags. They did not land, so they
  still cost a future tag.
- **`Presentation.lean` re-sync** (§6, D9). The structured mirror does not yet carry
  `policySigma` and still models measurands with a mandatory `Num` polarity. The Haskell
  `parse ∘ print = id` property covers the current signature blocks and optional polarity.
- **The curated sort-naming pass for `corpus-v1`**, which §7 already gated on the
  possible-worlds design. The corpus ships the finest partition under opaque `S1 … S27`; the
  `examples/` policies, which the paper displays, are named.

**Post-closeout (2026-08-11).** The deferred D9 `Presentation.lean` re-sync above is
resolved by `plans/2026-08-10-result-12-presentation-parity.md` and is no longer an open gap.
The Lean mirror now covers the complete live structured `Program`/`Policy` AST — `policySigma` as a
second `Policy` field, measurands as `Sort × Option Polarity` — with the round-trip proofs
audited in `AxCheck.lean` (commit `ce00fbe`), and a cross-language shape guard
(`scripts/presentation-shape.hs`, `lean/Lara/PresentationParity.lean`, compared by
`scripts/check-presentation-parity.sh` in CI) prevents the narrowing from recurring silently
(commit `376b6dc`). The bullet above is retained as the historical record of the deferral;
the other three deferred items are unaffected.
