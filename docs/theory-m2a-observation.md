# Theory M2a: semantics-parametric claim observation

_Status: mechanized for the POPL 2028 theory spine on 2026-08-28 (issue #185,
tracker #180). This document records what the observation interface proves,
what it refutes, and the six places where the plan's own prose was wrong._

_Update 2026-09-06 (issue #196): the general non-emptiness of preferred
extensions, listed below as follow-up work and as a paper must-not, is now
proved — `Semantics.preferred_exists`, `Semantics.preferred_exists_candidate`
and `Semantics.preferredSem_enumerate_ne_nil`, supported by
`Semantics.admissible_nil` and `Semantics.exists_max_length`. §3, §9 and §10
are corrected in place; the §1 landing snapshot is left as it was, since it
records the M2a landing at `042beed` and not the current tree._

The intended readers are the paper author and future M2b/M3 implementers. They
should cite the declarations below. The executed plan was deleted by `1ed83df`
after its durable content moved here. Section 4 quotes each defective plan
sentence inline and distinguishes it from the two pre-commit review catches.

M2a exists for one reason: before it, every status theorem in the development
read `Grounded.grounded` and nothing else, so a paper sentence about the
compiler being semantics-agnostic would have sat next to mechanized sentences
without being one. M2a makes the semantics parameter an object.

## 1. Fixed Context and What Is Parametric

M2a quantifies over an arbitrary finite `Grounded.AF` and an arbitrary
`Semantics.ExtensionSemantics`. It knows nothing about policies, support terms,
checkers, or accepted units; the compiled side enters only in
`Lara.Observation`, which as of `042beed` is the sole module besides the library
root and the axiom audit that depends on both `Lara.Compile` and
`Lara.Semantics`. (Dated deliberately. A sentence naming a module's reverse
dependencies is falsified by the next `import` line and nothing checks it; this
one's docstring ancestor was falsified twice during this milestone — see §8.)

The M2a landing is purely additive at the file level. Commits `3f57e4e`
through `042beed` add 3710 lines under `lean/` — four new modules plus
`Lara.lean` imports and `AxCheck.lean` coverage — and modify no pre-existing
proof. `lean/Lara/Compile.lean` is untouched. No result in M2a lifts a
`grounded`-indexed theorem to an arbitrary semantics, and none re-derives one.

157 declarations are covered by `lean/AxCheck.lean`, all sorry-free and within
the standard trio: 67 in `Lara/Semantics.lean`, 7 in
`Lara/Semantics/Sublists.lean` (which shares the `Lara.Semantics` namespace),
43 in `Lara/Observation.lean`, and 40 in `Lara/Examples/Semantics.lean`.

## 2. The Interface and the Observation Layer

`Semantics.ExtensionSemantics` has exactly three fields:

```lean
structure ExtensionSemantics where
  spec : AF → List Arg → Prop
  enumerate : AF → List (List Arg)
  sound : ∀ F, F.args.Nodup → ∀ S, S ∈ enumerate F ↔ (S.Sublist F.args ∧ spec F S)
```

Five instances are declared: `groundedSem`, `completeSem`, `preferredSem`,
`stableSem`, `semiStableSem`. `groundedSem.spec` is `LeastComplete`, not
`S = Grounded.grounded F`; picking the grounded case out by a first-order
condition in the same shape as the other four is what makes a theorem
quantified over `ExtensionSemantics` say something about it.

An extension is an order-preserving subsequence of `F.args`. `Semantics.subseqs`
and its characterization (`mem_subseqs`, `sublist_ext`, `subseqs_ext`,
`subseqs_nodup`, `nodup_flatMap_pair`) live in `Lara/Semantics/Sublists.lean`.
Core Lean at `leanprover/lean4:v4.32.0` has no `List.sublists`, and this project
carries no Mathlib dependency today, so the module is a hand-rolled stand-in for
Mathlib's `List.sublists`. That is a statement about the current build, not a
closed door: `lean/lakefile.toml` records Mathlib as a planned dependency for
result 5, and a later milestone that takes it on could replace this module. See
§10, whose first follow-up needs exactly that machinery. `candidates` stays in
`Lara/Semantics.lean` because it takes an `AF`.

The carrier bound lives inside the predicates (`Bounded` is a conjunct of
`Admissible` and `Stable`), not in the quantifiers. `Grounded.defendedB` scans
attackers only inside `F.args`, so under an unbounded reading `[0, 5]` is
admissible in `{args := [0], attack := fun _ _ => false}` and the maximality
clause of `Preferred` collapses.

The observation layer has two levels, deliberately not defined through each
other:

- `AcceptanceProfile` carries four `Bool` fields (`inAll`, `inSome`, `outAll`,
  `outSome`), computed by `profile`. Four rather than two because rejection is
  not the complement of acceptance — `profile_groundedSem_twoCycle` exhibits an
  argument with all four bits `false`.
- `ClaimObservation` is `noExtension | observed (s : Status)`, computed by
  `observe`. `noExtension` is a constructor rather than a side condition
  because `List.all [] p = true`: on an empty enumeration the acceptance and
  defeat guards both fire.

`observe` uses `attackedByB`, not `Semantics.attacked`. `mem_attacked_iff`
makes the difference a theorem: `attacked` intersects with the carrier, while
`Grounded.labelC` bounds the attacker and leaves the target unbounded. Reusing
`attacked` would make `observe_grounded` false.

## 3. Proved Boundary

### Adequacy is unconditional; `Nodup` buys representative uniqueness

`ExtensionSemantics.sound` binds `F.args.Nodup` and no instance consumes it.
`Examples.Semantics.sound_holds_without_nodup` re-proves all five adequacy
statements with the hypothesis absent from the statement entirely.

What `Nodup` buys is that no two entries of an enumeration denote the same set:
`candidates_ext`, `candidates_nodup`, and `enumerate_ext` — the last derived
for **any** instance from `sound` alone. It genuinely fails without the
hypothesis: `not_candidates_ext_without_nodup` and
`not_enumerate_ext_without_nodup` refute both over `dupCarrier`, with `[0]` and
`[0, 0]` as witnesses (`dupCarrier_candidates`, `dupCarrier_enumerate`).

The field stays in the record. An instance whose enumeration depends on unique
representatives — one deduplicating, counting, or indexing extensions — could
not add the hypothesis after the fact.

### The grounded instance

`Semantics.groundedSem_enumerate` proves that `groundedSem.enumerate F` is a
one-element **list**, not merely that some entry exists; `mem_canonize_grounded`
pins that entry's members to `Grounded.grounded F` with no hypothesis, and
`groundedSem_singleton` fuses both halves so the sublist-representation artifact
`canonize` stays out of downstream statements.

`Semantics.observe_grounded` is the regression theorem:

```lean
theorem observe_grounded {F : AF} (h : F.args.Nodup) (c : Grounded.Claim) :
    observe groundedSem F c = ClaimObservation.observed (Grounded.statusC F c)
```

The `noExtension` arm is excluded rather than assumed — the singleton makes
`isEmpty` provably `false`. `Nodup` is consumed at exactly one place, obtaining
the singleton; the `gap` branch closes before that.

`profile_grounded` is the corresponding collapse at the argument level:
skeptical and credulous bits coincide under `groundedSem`. That is the precise
sense in which the pre-M2a development could not tell the two readings apart.

### Exclusivity is not free

`justified_defeated_exclusive` needs a non-empty enumeration **and**
conflict-freedom of every extension. `ExtensionSemantics` supplies neither — its
`spec` is an arbitrary `AF → List Arg → Prop` — so conflict-freedom enters as an
explicit hypothesis, `SpecConflictFree`, discharged once per instance
(`groundedSem_specConflictFree`, `completeSem_specConflictFree`,
`preferredSem_specConflictFree`, `stableSem_specConflictFree`,
`semiStableSem_specConflictFree`). `observe_justified_not_all_defeated` is the
consumer-facing form: when `observe` reports `justified`, the `defeated` guard
it never reached is genuinely false.

`SpecConflictFree` is phrased over `spec` rather than `enumerate`, which is the
only reason `F.args.Nodup` appears in those compatibility theorems: crossing from
enumeration membership to `spec` goes through `sound`.

Issue #197 adds `EnumerateConflictFree sem F`, requiring conflict-freedom of
exactly the extensions returned by `sem.enumerate F`. The theorems
`justified_defeated_exclusive_of_enumerate` and
`observe_justified_not_all_defeated_of_enumerate` prove the same conclusions
without `Nodup`. Each of the five instances has an unconditional
`*_enumerateConflictFree` discharge, proved from its actual enumerator. The
old theorems retain their signatures and delegate through
`specConflictFree_enumerateConflictFree`; this bridge alone needs `Nodup`.

The *non-emptiness* half is also discharged for preferred semantics:
`preferredSem_enumerate_ne_nil` (§10, issue #196) holds for every framework.
Together with `preferredSem_enumerateConflictFree`, it makes exclusivity at
preferred semantics unconditional in the carrier. `stableSem` has no
non-emptiness counterpart: `stableSem_enumerate_threeCycle` refutes it.

### Source-to-framework transport

`Observation.AttackExtensional` is carrier-locality of a specification: two
frameworks with equal `args` that agree pointwise on `attack` at carrier members
satisfy the same specification. Proved for all five specs
(`attackExtensional_leastComplete`, `attackExtensional_complete`,
`attackExtensional_preferred`, `attackExtensional_stable`,
`attackExtensional_semiStable`) plus `attackExtensional_bounded` and
`attackExtensional_admissible`.

`Observation.observe_congr` lifts that to observations, and
`srcObservation_iff_checked` states the source-level form:

```lean
theorem srcObservation_iff_checked (sem : ExtensionSemantics)
    (hext : AttackExtensional sem.spec)
    (P : Compile.CheckedProgram canon Pi Gamma CertOk dp) (c : Grounded.Claim)
    (hsupp : ∀ i ∈ c.support, i < P.args.length) (o : ClaimObservation) :
    SrcObservation sem P c o ↔ o = observe sem (Compile.checkedAF P) c
```

`SrcObservation` quantifies over every `Edge`-deciding oracle satisfying
`AgreesOnArgs`. `srcObservation_checked` is existence and
`srcObservation_unique` is functionality, the latter with no hypotheses at all.

Every claim-level *transport* result carries the support-boundedness hypothesis
— `observe_congr`, `srcObservation_iff_checked`, `srcObservation_checked`,
`srcStatus_iff_srcObservation`. The results that read one framework do not, and
`srcObservation_unique` does not either. It is necessary where it appears, not
an artifact: `attackedByB` bounds the attacker and deliberately
leaves the target unbounded (without which `observe_grounded` is false), so
`observe` reads `attack` at support arguments outside the carrier, exactly where
`AgreesOnArgs` says nothing. `not_observe_congr_of_unbounded_support` is the
concrete separation and `observe_congr_needs_support_bound` is the refutation of
the hypothesis-free statement.

### Failure of collapse

Every theorem up to Task 4 is either generic over `sem` or names at most one
instance, so nothing in it rules out `ExtensionSemantics` being an abstraction
over a one-element set. `Examples.Semantics` supplies the separations.

- **Nonexistence.** `stableSem_enumerate_threeCycle` proves stable has no
  extension on the bare three-cycle, `observe_stableSem_threeCycle` proves the
  `noExtension` constructor is reached for an arbitrary supported claim, and
  `observe_stableSem_threeCycle_ne_justified` /
  `observe_stableSem_threeCycle_ne_defeated` name the two answers vacuous
  `all`-guards would otherwise have produced. `threeCycle_enumerate_nonStable`
  shows the other four are non-empty there, so nonexistence is stable's
  property and not the framework being hard.
- **Ten pairwise separations.** `five_semantics_pairwise_distinct` states all
  ten unordered pairs in a single theorem, so the count is checked by the
  elaborator rather than by a reader counting theorems.
- **Structural contrasts.** `preferred_exists_where_stable_does_not`,
  `semiStable_exists_where_stable_does_not`,
  `semiStable_proper_refinement_of_preferred`.
- **No four-state function realizes both credulous readings.**
  `credulous_not_functional` quantifies over every candidate
  `AF → Arg → Status` function and refutes the simultaneous requirements
  `justified ↔ inSome` and `defeated ↔ outSome` under preferred semantics.
  Argument `0` of the two-cycle makes both bits true.
  `profile_preferredSem_twoCycle_symm` shows that argument `1` has the same
  profile, so a framework-internal tie-break cannot distinguish them.
- **`observe` does not factor through `profile`.**
  `observe_not_determined_by_profile`: `completeSem` and `preferredSem` give the
  identical `AcceptanceProfile` for every carrier argument of the two-cycle and
  different `ClaimObservation`s for the same claim. The mechanism is a checked
  conjunct — the two enumerations differ by exactly the entry `[]`, and
  `claimAcceptedB [] claimBoth = false`.
- **`AgreesOnArgs` is strictly weaker than `Compile.Faithful`.**
  `agreesOnArgs_strictly_weaker_than_faithful`, from `eJunk_agreesOnArgs` and
  `not_faithful_eJunk` against `Examples.PEx`.

## 4. Six Corrections

M2a's stated purpose was to stop the paper putting unmechanized semantic claims
next to mechanized ones. It did that, and in doing so found six statements in
the milestone's own prose that the mechanization contradicts.

They fall into two kinds, and the distinction matters for anyone checking this
record. **(1), (4), (5) and (6) are defects in the executed plan**. Each entry
below quotes the defective sentence inline, because the plan was correctly
deleted after execution. The complete pre-deletion source remains inspectable
with
`git show dce7a28^:plans/2026-08-27-theory-m2a-semantics-observation.md`.
**(2) and (3) are pre-commit review catches**: the false docstring and the wrong
guard order were found and fixed before the commits that introduced them, so
`git show` on those commits returns the corrected text and the repository
records no defective version. They are kept because the errors were real and
are the two clearest cases of review working, but do not look for them in the
history; each entry says where the false version lived.

**(1) `sound` is unconditional; D4 attached `Nodup` to the wrong theorems.**
D4 states that "each subset of a **nodup** `args` has exactly one
order-preserving representative", and concludes: "Every enumeration theorem
therefore carries `F.args.Nodup`". The conclusion is too wide. Adequacy carries
the hypothesis and never consumes it — `sound_holds_without_nodup` re-proves all
five adequacy statements with no hypothesis in scope at all, and every instance
binds `Nodup` and discards it. What `Nodup` buys is exactly the representative
uniqueness D4's premise names and nothing else — `subseqs_ext`,
`candidates_ext`, `enumerate_ext` — and that does fail without it
(`not_candidates_ext_without_nodup`, `not_enumerate_ext_without_nodup`). The
field is kept for the consumer's sake, not the producer's — see §3.

**(2) Stable nonexistence is a property of the bare three-cycle, not of
containing an odd cycle.** *Caught in review before the first commit.* A draft
`stableSem` docstring asserted the general version — a framework containing an
odd attack cycle has no stable extension. It is false: adding a fourth argument
that attacks all of `0, 1, 2` leaves the cycle present and gives stable
extensions `[[3]]`. Only the bare cycle collapses. The correction was applied
before `3f57e4e`, so `git show 3f57e4e:lean/Lara/Semantics.lean` already carries
the corrected paragraph and no commit contains the false claim.

It is recorded anyway because the milestone's whole stable-nonexistence result
rests on that sentence, and because the fix is not just a reworded docstring:
`stableSem_enumerate_threeCycleAttacked` states the three cycle edges of
`threeCycleAttacked` and its stable extensions `[[3]]` in a single theorem, so
the two halves of the counterexample cannot drift apart.

**(3) Plan §6's semantics-independence sentence was false of the first draft of
`observe`, and the code moved to make it true.** *Caught in review before the
commit that introduced `observe`.* Plan §6 says, verbatim:

> **`gap` is semantics-independent.** It reads `c.support = []` and nothing
> else (`Grounded.statusC_gap_iff`, `:525`). It survives unchanged under every
> semantics. This is worth stating because it is the only one that does.

As `observe` was first drafted, the empty-enumeration guard preceded the
empty-support guard, so a claim with no support under `stableSem` on the bare
three-cycle reported `noExtension`, not `gap` — the sentence was false of the
function it described. The guards were reordered before `8502326`, so the
committed `observe` tests `c.support = []` first and no commit contains the
other ordering. Reordering is what makes `observe_gap` statable for an arbitrary
`sem` with no hypothesis beyond `c.support = []`, so a design principle the plan
asserted in prose is now a theorem the axiom gate checks.
`observe_gap_iff` is the converse, and `observe_claimNoSupport_uniform`
instantiates it at all five instances, including the one where the two guards
compete.

The ordering itself carries **no safety content**. There are two vacuity
hazards, and each is blocked by its own guard: at the enumeration, an empty
extension set would satisfy both `all`-guards, blocked by the enumeration guard;
at the support, `claimDefeatedB` is vacuously `true` and `claimAcceptedB`
vacuously `false` on empty support (`claimDefeatedB_of_nil`,
`claimAcceptedB_of_nil`), so an unsupported claim reaching the `all`-guards
would be reported specifically `defeated` — the worst available verdict, on a
framework with perfectly good extensions — blocked by the `gap` guard. Both
guards precede both `all`-guards under either arrangement of the first two arms.
`no_verdict_on_empty` is the general fact, `observe_noExtension_iff` recovers
the emptiness report exactly, and `enumerate_ne_nil_of_observed_ne_gap` recovers
"this verdict is backed by an extension" for every status but `gap`. Nothing is
lost by the demotion.

**(4) `srcStatus_iff_checked` is not an instance of `srcObservation_iff_checked`.**
The plan directs this documentation step to write that "`srcStatus_iff_checked`
is now the `groundedSem` instance of `srcObservation_iff_checked`, so the
paper's existing preservation citation stays valid." That is false and is not
written anywhere in this repository.

`Compile.srcStatus_iff_checked` has no support side condition.
`srcObservation_iff_checked` requires `∀ i ∈ c.support, i < P.args.length`. The
new result therefore asks for **more**, not less: it is not a generalization.
The subjects differ as well — `Compile.SrcStatus` is an inductive relation whose
constructors are built from `SrcIn`/`SrcOut`, while `SrcObservation` quantifies
over every `Edge`-deciding oracle that agrees on declared arguments. Neither is
a substitution instance of the other.

The honest bridge is `Observation.srcStatus_iff_srcObservation`: under the
support bound, `Compile.SrcStatus P c s` holds exactly when the `groundedSem`
source observation is `observed s`. It is stated as an equivalence because it is
not an instantiation.

The consequence for the paper is *stronger* than the plan's version, not weaker.
`Compile.srcStatus_iff_checked` is unchanged and independently proved —
`Lara/Compile.lean` was not modified by any M2a commit — so the paper's existing
citation of it stays valid **as-is, unmodified**, and needs no support
hypothesis attached to it. A citation rewritten to route through the observation
form would acquire a side condition the original never had.

**(5) `AttackExtensional ConflictFree` is false, and it was asked for.**
D7's closing sentence — "the bound is also what makes Task 5's
`AttackExtensional` true: `ConflictFree` applies `F.attack` at members of `S`,
and two frameworks agreeing on `args` can disagree outside it" — reads as a
claim that `ConflictFree` itself transports, and the task brief written from it
asked for that theorem. (The plan's Task 5 parenthetical is compatible with the
refutation: it says that without the carrier bound "`ConflictFree` reads
`F.attack` at junk members where the two frameworks may disagree, and the
transport fails". The two passages point in opposite directions, which is why
the brief could be written from one of them.)

`not_attackExtensional_conflictFree` refutes the theorem, using D7's own
example: the carrier `[0]` and the junk set `[0, 5]`.
`admissible_transports_on_junk` is the
positive contrast on the same framework pair, so the failure is about dropping
the carrier bound and not about the frameworks chosen. The right decomposition
is the `Bounded`-relativized `conflictFree_congr_af`, which is what
`attackExtensional_admissible` actually consumes.

**(6) A transport hypothesising `Faithful` would be contentless.** Plan Task 5
specifies the "generic transport" as being stated "for `P :
Compile.CheckedProgram` and `hf : Faithful P edgeB`".
`Observation.faithful_unique` proves that any two `Compile.Faithful` oracles for
the same program are literally equal. A transport stated over `Faithful` on both
sides is therefore a `funext` away, and `AttackExtensional` would never be
invoked — the module would be vacuous. The transport is stated over
`AgreesOnArgs`, which is `Compile.Faithful.agrees` alone
(`agreesOnArgs_of_faithful` is the projection), leaving the frameworks free to
differ off the carrier so the transport has to be earned. That the weakening is
real, and not merely a weaker-looking statement, is
`agreesOnArgs_strictly_weaker_than_faithful`.

## 5. The Observation Table

`Examples.Semantics.observationTable` is the milestone's paper figure: 120 rows,
one per (semantics, framework, claim) over five semantics, six frameworks, and
four claims, printed by `#eval` from the definitions rather than written by
hand, so the figure cannot drift from what it depicts.

The row labels come from closed sum types declared in the module —
`SemanticsName`, `FrameworkName`, `ClaimName` — each with exactly one spelling
table (`semanticsLabel`, `frameworkLabel`, `claimLabel`) and exactly one map to
the object it names (`semanticsInstance`, `frameworkAF`, `claimOf`). Every cell
reads its semantics through `semanticsInstance`, so no row can name one instance
and evaluate another.

The `|E|` column is load-bearing rather than decoration. `grounded` and
`complete` occupy 48 of the 120 rows, two per (framework, claim) input. On all
24 of those inputs their observations are identical; their extension counts
differ on 12 of the 24. Without `|E|` the table would read as though the two
semantics were the same.

`reinstatementChain` contributes 20 rows in which all five semantics enumerate
the two-element extension `[0, 2]`. Argument `2` is defended only because
argument `0` attacks its attacker `1`, so these rows exercise reinstatement
rather than only unattacked singleton extensions.

The table also makes §4(3) visible: the only `noExtension` cells are
`stable`/`threeCycle` on the three supported claims, and that same
(semantics, framework) pair reports `gap` on `claimNoSupport` with `|E| = 0`,
because the `gap` guard is tested first.

**The limit of the completeness guarantee, stated precisely.** Adding a
constructor to one of the three sum types breaks its label map and its object
map, which are total matches, and `allSemantics_complete`,
`allFrameworks_complete`, `allClaims_complete` break the hand-written order
lists too — so a dropped row is a compile error. What no mechanism here can
catch is a sixth `ExtensionSemantics` declared in another module: nothing
enumerates the instances of a structure, so such a semantics would simply not
appear and the table would be five rows out of six with no complaint. The
guarantee is over this module's declared vocabulary, not over the interface —
a *constructor* guarantee, not an *instance* guarantee. That limit is tracked as
[#198](https://github.com/ARA-Labs/lara/issues/198).

## 6. The Haskell Conformance Mirror

`src/Lara/Semantics.hs` mirrors the executable layer of `Lara.Semantics`: the
powerset scan, the `Bool` deciders, and the five `enumerate` functions.
`test/SemanticsSpec.hs` checks them against golden values Lean computed.

The `Prop` layer and the adequacy theorems have no Haskell counterpart, and the
`ExtensionSemantics` record is not mirrored — its content is the bundled `sound`
field, without which the record would be a five-element enum of functions
dressed up as the Lean interface.

**The epistemic status does not upgrade.** Per `CLAUDE.md`, Haskell property
tests are conformance evidence, not soundness; the Lean proofs carry soundness.
The goldens agreeing is evidence about *outputs on six frameworks under five
semantics*. It is not a proof that the two sets of definitions correspond, and
no number of agreeing rows makes it one. The frameworks are hand-copied into the
Haskell test module rather than derived, so a mistranscribed edge shows up as a
golden mismatch. `prop_goldensCoverProduct` catches a dropped or duplicated row,
and `make semantics-goldens` regenerates the Lean block and diffs it against the
checked-in Haskell transcript.

Neither the enumerations nor `candidates` is a proposed runtime, in Lean or in
Haskell. `candidates` is an exponential powerset scan and `preferredB` /
`semiStableB` / `leastCompleteB` scan that list once per candidate. The runtime
evaluator stays grounded.

## 7. Gate Coupling: Anything Printed During the Lean Build

`scripts/check-axioms.sh` extracts every `[...]` in its input and treats the
comma-separated contents as axiom names. It reads the whole stream, not only
lines matching a declaration report.

A Haskell list literal is nothing but brackets. The script matches
`\[[^]]*\]`, strips `[` and `]`, then splits on commas — so a `#eval` printing
`[[0],[0,2]]` during `lake build` contributes the bracket-runs `[[0]` and
`[0,2]`, which reduce to the three tokens `0`, `0`, `2`. The gate exits 1 with
`::error::A proof depends on a non-standard axiom: 0` followed by `0` and `2`.
Anyone debugging that message should grep for the bare digits, not for a
bracketed name: the brackets are gone by the time the comparison happens.

Two consequences are already in force. `renderObservation` prints one word per
cell rather than delegating to the derived `Repr`, and the observation table
carries no extension lists. The golden emitter, which must print list literals,
is guarded on `LARA_EMIT_GOLDENS`, which no build or gate command sets;
`lake env lean` on the file re-elaborates from source, which is what makes the
guarded `#eval` fire on demand even though the `.olean` is current.

The hazard is latent today rather than active — the gate runs
`lake env lean AxCheck.lean`, which loads `Lara.Examples.Semantics` from its
`.olean` and never re-runs the `#eval`. The constraint is recorded because it is
invisible from either side on its own: anything that prints during the Lean
build shares a channel with the axiom audit, and the coupling is between two
files that never mention each other.

## 8. A Methodological Finding

Review of this development, across the milestone's rounds, caught false
statements in its prose at a steady rate, and they were of one kind. Every one
was a claim about dependencies, counts, locations, or causes: "needed three
times" (twice), "together with X" where X played no part, "a different route
for each of five" where there were three, "without this the constructor is
unreachable" stated backwards, "all three of which" over four items, and an
importer list falsified twice by later commits.

Not one was a claim about what the code outputs. Every evaluation-backed claim,
from every author, checked out.

No count is given here on purpose. A running total of defects found in review
is exactly the kind of claim this section is about — unverifiable from the
repository, and stale the moment the next round finishes. What is checkable is
the shape, and the shape held through the review of this document too: its own
findings were about history, counts, scopes and dependencies, and every
output-level claim it recomputed was correct.

The sharpest instance is worth naming because it is the general shape at its
limit. A theorem (`twoCycle_extensions`) was added specifically to replace an
evaluation-only docstring claim. Its own docstring then argued an entailment
resting on an enumeration that no theorem in the tree stated: the fix for an
unchecked claim introduced an unchecked claim one level up, in the sentence
justifying the fix.

The response that worked was to stop repairing sentences and state theorems.
`mem_attacked_iff` replaced a docstring argument about two "attacked by"
notions; `claimDefeatedB_of_nil` and `claimAcceptedB_of_nil` replaced a hazard
paragraph that had been written wrongly twice; `twoCycle_defeated_unreachable`
replaced the entailment above, proved for an arbitrary non-empty-support claim
across all five semantics, with the lower bound consumed where the enumeration
supplies it; `allSemantics_complete` and its two siblings replaced the table's
own claim about what would be a compile error.

The finding, for anyone building this kind of artifact: in a development where
proofs are machine-checked and prose is not, the causal prose is where the
errors live, and the remedy is to move load-bearing claims into statements the
gate checks. A docstring that enumerates its own reverse dependencies, or
explains why a result follows, is a claim the next commit can silently break.

## 9. Paper Claims

The paper **may** claim:

- that compilation is semantics-agnostic in a precise sense: the observation
  interface is parametric in `ExtensionSemantics`, and the compilation pipeline
  (`Compile.toAF`, `Compile.checkedAF`) never inspects a semantics. The support
  for this is structural — `Lara.Compile` does not
  import `Lara.Semantics`, and no M2a commit modified it — together with
  `Observation.srcObservation_iff_checked`, which holds for every `sem` whose
  specification is `AttackExtensional`. That theorem must not be displayed
  without its support hypothesis `∀ i ∈ c.support, i < P.args.length` — see
  §4(4), whose entire content is that the hypothesis is there;
- that the four-state status the pipeline already prints is the grounded
  instance of the general definition, citing `Semantics.observe_grounded`, and
  that the source-level bridge is `Observation.srcStatus_iff_srcObservation`
  with its support hypothesis named;
- that all ten pairwise separations among the five semantics are witnessed,
  citing `Examples.Semantics.five_semantics_pairwise_distinct`;
- that stable extensions can fail to exist and that `observe` then reports
  `noExtension` rather than fabricating a `Status`, citing
  `stableSem_enumerate_threeCycle` and `observe_stableSem_threeCycle` with its
  two negative halves;
- that `gap` is the one semantics-independent status, citing
  `Semantics.observe_gap` and `observe_gap_iff` — and, if the uniqueness half is
  stated, `observe_twoCycle_grounded_ne_preferred` and
  `observe_twoCycleSink_grounded_ne_preferred` as the witnesses that the other
  three vary.

The paper **must not**:

- print the credulous reading as a four-state verdict.
  `Examples.Semantics.credulous_not_functional` refutes every
  `AF → Arg → Status` function that would make `justified ↔ inSome` and
  `defeated ↔ outSome` under preferred semantics. Argument `0` of the
  two-cycle makes both bits true, and
  `profile_preferredSem_twoCycle_symm` shows that argument `1` has the same
  profile. The credulous reading is exposed only through `profile`'s `inSome`
  / `outSome` bits;
- say that `observe` factors through per-argument acceptance data.
  `observe_not_determined_by_profile` refutes it;
- assert the general non-emptiness of *stable* extensions, or read
  `preferred_exists` as licensing one. `stableSem_enumerate_threeCycle` refutes
  it, and that contrast is the point of
  `preferred_exists_where_stable_does_not`. (This bullet previously forbade
  asserting the general non-emptiness of *preferred* extensions. It was lifted
  on 2026-09-06 by `preferred_exists`, issue #196 — the paper may now state
  Dung's existence result for preferred extensions and cite the mechanization,
  with no `Nodup` side condition;)
- say that `Compile.srcStatus_iff_checked` is an instance or a special case of
  `srcObservation_iff_checked`, or rewrite the existing preservation citation to
  route through it. See §4(4). The existing citation stands unmodified;
- state any transport over `Compile.Faithful` on both sides, or claim
  `AttackExtensional ConflictFree`. See §4(5) and §4(6).

## 10. Proposed Follow-up Work

Four items are visible from here and none is an M2a result. Each is tracked as
a GitHub issue, per `CLAUDE.md`; this document records the decision, the issue
records the work.

- Non-emptiness of preferred extensions — [#196](https://github.com/ARA-Labs/lara/issues/196). **Closed 2026-09-06.**
- Enumeration-based conflict freedom — [#197](https://github.com/ARA-Labs/lara/issues/197). Implemented alongside the compatible spec-based API; see §3.
- A registry that would make a sixth `ExtensionSemantics` visible — [#198](https://github.com/ARA-Labs/lara/issues/198).
- Generic-`ExtensionSemantics` contextual equivalence —
  [#216](https://github.com/ARA-Labs/lara/issues/216). **Landed 2026-09-07**;
  see `docs/theory-m4-generic-observation.md`. Filed later than the three
  above, from the M4 plan rather than from here. The M2a interface is now
  quantified over by the *contextual* theorems and not only by the
  framework-level ones: `Lara.Context.obsSem` and `Lara.Context.CtxEquivSem`
  generalize M4's `obs` and `CtxEquiv`, the grounded case is recovered as a
  theorem (`obsSem_grounded`, `ctxEquivSem_grounded_iff`), and the congruences
  hold with no additional hypothesis. What it does **not** settle is how the
  equivalence *relations* at different semantics compare — that is
  [#268](https://github.com/ARA-Labs/lara/issues/268).

The general non-emptiness of preferred extensions was expected to need a
maximal-element principle over `candidates F`, and with it `Nodup` and a
subset-implies-shorter fact core Lean does not supply. That sizing was wrong,
and the correction is worth recording because it is what made the result cheap:
the proof never compares two extensions by `⊆`. It takes a *longest* admissible
candidate `S` and meets a competitor `T` at `canonize F T`, where
`List.Sublist.filter` places `S` **inside** the competitor as a sublist rather
than as a subset; `List.Sublist.eq_of_length` then closes it. `Nodup` was only
ever needed to stop a shorter list from having the same members as a longer one,
and a shared carrier already rules that out. No Mathlib, and no hypothesis on
`F` at all — see `Semantics.preferred_exists` and the section note above it.

The enumeration-based API now removes the incidental `Nodup` hypothesis without
replacing the spec-level property. This preserves the original abstraction
trade-off for clients that reason about alternative adequate enumerators, while
clients of the concrete enumeration can use the weaker assumptions directly.

Nothing enumerates the instances of a structure, so a sixth `ExtensionSemantics`
declared elsewhere would be invisible to the observation table's completeness
theorems. Closing that would need a registry the interface does not currently
have.
