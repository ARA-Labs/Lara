/-
Concrete witnesses for the semantics parameter (theory M2a, issue #185): what
the parametric layer of `Lara.Semantics` actually buys.

No theorem in `Lara.Semantics` compares two instances: each names at most one, or
is generic over `sem : ExtensionSemantics`. That shape cannot
exhibit a *disagreement*, and a disagreement is the whole reason the interface
exists: if all five instances always returned the same thing, `ExtensionSemantics`
would be an abstraction over a one-element set and `ClaimObservation.noExtension`
would be an arm nothing forces you into. This module supplies the missing half
with six table frameworks: five witness separations, while
`reinstatementChain` exercises a defended argument in a multi-element
extension. A seventh framework, `dupCarrier`, asks what the `Nodup` hypothesis
is for and witnesses no separation.

The headline separations are:

* **Stable extensions can fail to exist** (`stableSem_enumerate_threeCycle`), and
  when they do `observe` returns `noExtension` rather than a fabricated `Status`
  (`observe_stableSem_threeCycle` with its two negative halves). This is the case
  a `grounded`-only development cannot express.
* **No four-state function realizes both credulous readings**
  (`credulous_not_functional`): the theorem quantifies over candidate functions
  and refutes the simultaneous requirements `justified ↔ inSome` and
  `defeated ↔ outSome` on the preferred-semantics two-cycle.
* **`observe` does not factor through `profile`**
  (`observe_not_determined_by_profile`): two semantics agree on the acceptance
  profile of every carrier argument yet disagree on the claim.
* **Semi-stable sits strictly inside preferred on one framework and strictly
  outside stable on another** (`semiStable_proper_refinement_of_preferred`,
  `semiStable_exists_where_stable_does_not`).
* **No two of the five instances are the same enumerator**
  (`five_semantics_pairwise_distinct`): all ten unordered pairs, each separated
  by one of the frameworks here, in a single statement so the count is checked.

Three further results are not separations between semantics:

* **`Nodup` buys representative uniqueness, not adequacy.**
  `sound_holds_without_nodup` re-proves all five adequacy statements with the
  hypothesis absent; `not_candidates_ext_without_nodup` and
  `not_enumerate_ext_without_nodup` refute `candidates_ext` and `enumerate_ext`
  with it absent. This is the *Representation* paragraph of `Lara.Semantics`'s
  module header, mechanized on both sides.
* **`Observation.AgreesOnArgs` is strictly weaker than `Compile.Faithful`**
  (`agreesOnArgs_strictly_weaker_than_faithful`), so the transport theorems of
  `Lara.Observation` really do apply to oracles that `Faithful` rejects.
* **The observation table** at the end of the file, printed by `#eval` from the
  definitions rather than written out, one row per (semantics, framework,
  claim).

Twenty-one of the forty theorems below are closed by a bare `decide`. The
frameworks carry two to four arguments, so the powerset scan `Lara.Semantics`'s
module header warns about is a
scan of four to sixteen candidates and the kernel evaluates it directly, with no
`simp` chain to maintain. That is deliberate — an evaluated counterexample is a
fact about the definitions as written, which is exactly the kind of evidence a
docstring cannot be trusted to carry.

The nineteen exceptions fall into seven groups. (i) `observe_stableSem_threeCycle`
goes through `observe_noExtension_iff` and its two negative halves are rewrites
along it, so all three hold for an *arbitrary* claim rather than one chosen
witness. (ii) `observe_claimNoSupport_uniform` and
`agreesOnArgs_strictly_weaker_than_faithful` are term-level compositions of other
results. (iii) `observe_ne_defeated_of_mem_enumerate`,
`claimDefeatedB_nil_eq_false`, `twoCycle_defeat_split` and
`twoCycle_defeated_unreachable` quantify over an arbitrary `Grounded.Claim`.
(iv) `twoCycle_extensions`, `not_candidates_ext_without_nodup`,
`not_enumerate_ext_without_nodup` and `sound_holds_without_nodup` quantify over
something else `decide` cannot scan — an arbitrary `Arg`, an arbitrary `AF`, an
arbitrary `ExtensionSemantics`. (v) `eJunk_agreesOnArgs` and
`not_faithful_eJunk` are about a compiled `CheckedProgram` rather than a
hand-written framework. (vi) `credulous_not_functional` quantifies over a
candidate function, then calls `decide` only for the finite two-cycle witness.
(vii) `allSemantics_complete`, `allFrameworks_complete` and
`allClaims_complete` need a `cases` first, since the quantifier has no
`Decidable` instance even though each instantiation does. Eight of the nineteen
still call `decide` on their finite parts: `twoCycle_extensions`,
`twoCycle_defeated_unreachable`, the two `not_*_ext_without_nodup`,
`credulous_not_functional`, and the three `*_complete`.

Several claims that docstrings in `Lara.Semantics` could once only assert as
"checked by evaluation outside the file" are discharged here; those docstrings
now name a theorem instead, and this is the module those names live in. The same
has now been done for this module's own docstrings. `threeCycle_conflictFree`
and `twoCycle_extensions` promote the last two *facts* that `threeCycle`'s and
`twoCycleSink`'s docstrings asserted without a proof behind them, and
`twoCycle_defeated_unreachable` promotes the *entailment* those docstrings drew
from them — which review found to be invalid as drawn, since the extension list
`twoCycle_extensions` states is an upper bound and the entailment needs a lower
one. That correction is written up at `twoCycle_extensions`, since a wrong
argument is worth keeping visible next to its fix.
-/

import Lara.Semantics.Registry
import Lara.Observation
import Lara.Examples

namespace Lara.Examples.Semantics

open Lara.Grounded Lara.Semantics

/-- The bare three-cycle `0 → 1 → 2 → 0`, with no other attacks. The standard
framework with no stable extension: a stable set must attack every argument it
omits, and here the conflict-free sets are exactly the empty set and the three
singletons (`threeCycle_conflictFree`) — each singleton attacks only its one
successor, so each leaves an omitted argument unattacked.
`stableSem_enumerate_threeCycle` is the resulting emptiness, checked. -/
def threeCycle : AF where
  args := [0, 1, 2]
  attack := fun a b => (a == 0 && b == 1) || (a == 1 && b == 2) || (a == 2 && b == 0)

/-- The same three-cycle with a fourth argument `3` that attacks each of `0, 1,
2` and is attacked by nothing. Present only to make the contrast in
`stableSem_enumerate_threeCycleAttacked` statable: the odd cycle survives
verbatim, yet the stable extensions are back. -/
def threeCycleAttacked : AF where
  args := [0, 1, 2, 3]
  attack := fun a b =>
    (a == 0 && b == 1) || (a == 1 && b == 2) || (a == 2 && b == 0)
      || (a == 3 && (b == 0 || b == 1 || b == 2))

/-- The two-cycle `0 ↔ 1`. Every separation about *acceptance* below is stated
over it: `groundedSem` sees one extension here (`groundedSem_enumerate_twoCycle`)
and `preferredSem` sees two (`preferredSem_enumerate_twoCycle`), which is what a
skeptical/credulous split needs. -/
def twoCycle : AF where
  args := [0, 1]
  attack := fun a b => (a == 0 && b == 1) || (a == 1 && b == 0)

/-- The two-cycle with a third argument `2` attacked by both of `0, 1` and
attacking nothing. Its role is to make `defeated` reachable, which the bare
two-cycle cannot: `twoCycle_defeated_unreachable` proves that no claim with
non-empty support is observed `defeated` on `twoCycle` under any of the five
instances, and `observe_twoCycleSink_grounded_ne_preferred` reports `defeated`
here. The extension lists and attack facts behind that are `twoCycle_extensions`;
the entailment from them is `twoCycle_defeated_unreachable`, which is a theorem
rather than a docstring argument because the docstring argument this replaces was
wrong — see `twoCycle_extensions`. -/
def twoCycleSink : AF where
  args := [0, 1, 2]
  attack := fun a b => (a == 0 && b == 1) || (a == 1 && b == 0) || ((a == 0 || a == 1) && b == 2)

/-- The two-cycle `0 ↔ 1` extended by a self-attacking argument `2` that `1`
attacks. The two preferred extensions `[0]` and `[1]` have *different ranges* —
`[1]` also reaches `2` — so semi-stability breaks the tie the preferred semantics
leaves open. This is the witness for
`semiStable_proper_refinement_of_preferred`. -/
def rangeSplit : AF where
  args := [0, 1, 2]
  attack := fun a b =>
    (a == 0 && b == 1) || (a == 1 && b == 0) || (a == 1 && b == 2) || (a == 2 && b == 2)

/-- The reinstatement chain `0 → 1 → 2`. Argument `2` is defended by `{0, 2}`
because `0` attacks its sole attacker `1`, so every one of the five semantics
enumerates the two-element extension `[0, 2]`. This framework keeps the
Haskell conformance goldens sensitive to the defended-argument clause in
`Complete`, rather than exercising only unattacked singleton extensions. -/
def reinstatementChain : AF where
  args := [0, 1, 2]
  attack := fun a b => (a == 0 && b == 1) || (a == 1 && b == 2)

/-- A claim supported by argument `0` alone. -/
def claimZero : Grounded.Claim := { support := [0], holes := [] }

/-- A claim supported by *both* arguments of the two-cycle. The claim-level and
argument-level readings of `justified` disagree on exactly this input — see
`observe_not_determined_by_profile`. -/
def claimBoth : Grounded.Claim := { support := [0, 1], holes := [] }

/-- A claim supported by the sink argument `2` of `twoCycleSink`. -/
def claimSink : Grounded.Claim := { support := [2], holes := [] }

/-- A claim with no complete support and one hole. The `holes` field is non-empty
on purpose: `observe`'s `gap` arm reads `support` only, so a claim that *does*
have a hole-bearing argument still observes `gap`, and
`observe_claimNoSupport_uniform` checks that under all five semantics. -/
def claimNoSupport : Grounded.Claim := { support := [], holes := [0] }

/-! ### Stable nonexistence, and the `noExtension` arm it forces -/

/-- **The bare three-cycle has no stable extension.** The fact `stableSem`'s
docstring asserts, and the reason `ClaimObservation` has a `noExtension`
constructor at all. Decided by evaluation over the eight candidates of a
three-element carrier. -/
theorem stableSem_enumerate_threeCycle : stableSem.enumerate threeCycle = [] := by decide

/-- **The `noExtension` arm, reached.** Any claim with non-empty support observes
`noExtension` under `stableSem` on the bare three-cycle. Proved from
`observe_noExtension_iff` and `stableSem_enumerate_threeCycle`, so it holds for an
*arbitrary* claim rather than for one chosen witness; nothing here is decided by
evaluation. -/
theorem observe_stableSem_threeCycle {c : Grounded.Claim} (hs : c.support ≠ []) :
    observe stableSem threeCycle c = ClaimObservation.noExtension :=
  (observe_noExtension_iff stableSem threeCycle c).mpr ⟨stableSem_enumerate_threeCycle, hs⟩

/-- **The first negative half.** The observation is not `justified`.
`observe_stableSem_threeCycle` already proves the constructor is reached — it is
an equation to `noExtension`, and this theorem is derived from it — so what these
two add is the refutation form, naming the two `Status` answers the vacuous
`all`-guards would otherwise have produced. The hazard is real rather than
notional: `List.all [] p` is
`true`, so on this framework both of `observe`'s aggregation guards would fire,
and the only thing between this input and a fabricated `justified` is the
enumeration guard tested ahead of them. These two theorems check that the guard
does its job. -/
theorem observe_stableSem_threeCycle_ne_justified {c : Grounded.Claim} (hs : c.support ≠ []) :
    observe stableSem threeCycle c ≠ ClaimObservation.observed Status.justified := by
  rw [observe_stableSem_threeCycle hs]; intro h; exact ClaimObservation.noConfusion h

/-- **The second negative half.** The observation is not `defeated` either. -/
theorem observe_stableSem_threeCycle_ne_defeated {c : Grounded.Claim} (hs : c.support ≠ []) :
    observe stableSem threeCycle c ≠ ClaimObservation.observed Status.defeated := by
  rw [observe_stableSem_threeCycle hs]; intro h; exact ClaimObservation.noConfusion h

/-- **Emptiness is a property of the framework, not of containing an odd cycle.**
The first three conjuncts say the `0 → 1 → 2 → 0` cycle is present verbatim in
`threeCycleAttacked`; the fourth says its stable extensions are `[[3]]`. The two
halves are one theorem so they cannot drift apart: together they are the exact
claim `stableSem`'s docstring makes about the four-argument variant. -/
theorem stableSem_enumerate_threeCycleAttacked :
    threeCycleAttacked.attack 0 1 = true ∧ threeCycleAttacked.attack 1 2 = true ∧
      threeCycleAttacked.attack 2 0 = true ∧
      stableSem.enumerate threeCycleAttacked = [[3]] := by decide

/-- **Only `stableSem` collapses on the bare three-cycle.** The other four
instances all return the single empty extension, so the framework is not "hard"
in any sense the interface can see — nonexistence is specific to the stable
condition, which is the only one of the five that demands an attack on every
omitted argument. -/
theorem threeCycle_enumerate_nonStable :
    completeSem.enumerate threeCycle = [[]] ∧ preferredSem.enumerate threeCycle = [[]] ∧
      semiStableSem.enumerate threeCycle = [[]] ∧ groundedSem.enumerate threeCycle = [[]] := by
  decide

/-! ### The structural contrast between preferred and stable -/

/-- **Preferred extensions exist where stable ones do not.** One theorem rather
than two because the contrast is the content: the same framework has a preferred
extension and no stable one. The general non-emptiness fact `preferredSem`'s
docstring states is now proved (`Semantics.preferred_exists`); this concrete
instance is kept because the contrast with `stableSem` — which has no
counterpart and cannot acquire one — is the content, and the general theorem
does not supply it. -/
theorem preferred_exists_where_stable_does_not :
    preferredSem.enumerate threeCycle ≠ [] ∧ stableSem.enumerate threeCycle = [] := by decide

/-! ### Credulous acceptance is not a function -/

/-- The two preferred extensions of the two-cycle. No proof below cites it —
every separation over `twoCycle` is decided directly from the definitions — but it
is what makes those separations readable, since `[0]` and `[1]` are the two
extensions the folds in `profile` and `observe` range over. -/
theorem preferredSem_enumerate_twoCycle : preferredSem.enumerate twoCycle = [[0], [1]] := by decide

/-- The grounded semantics sees a single, empty extension on the two-cycle. This
is the framework the *four-bit* argument for `AcceptanceProfile` is made on, and
an empty extension neither contains an argument nor attacks one;
`profile_groundedSem_twoCycle` records the resulting all-`false` profile. -/
theorem groundedSem_enumerate_twoCycle : groundedSem.enumerate twoCycle = [[]] := by decide

/-- **No four-state function realizes both credulous bits (D6).** There is no
function on frameworks and arguments that returns `justified` exactly when
`inSome` is true and returns `defeated` exactly when `outSome` is true under
preferred semantics. Argument `0` of the two-cycle makes both bits true, so the
two required outputs would be distinct constructors at the same input.

This formalizes the functional failure rather than merely naming the two-cycle
witness. It is why `observe` returns the skeptical reading and exposes the
credulous one only through `profile`'s `inSome` / `outSome` bits.
`profile_preferredSem_twoCycle_symm` separately records that argument `1` has
the same profile, so a framework-internal tie-break cannot distinguish the two
arguments. -/
theorem credulous_not_functional :
    ¬ ∃ credulous : AF → Arg → Status,
      (∀ F a, credulous F a = .justified ↔
        (profile preferredSem F a).inSome = true) ∧
      (∀ F a, credulous F a = .defeated ↔
        (profile preferredSem F a).outSome = true) := by
  rintro ⟨credulous, hjustified, hdefeated⟩
  have hj : credulous twoCycle 0 = .justified :=
    (hjustified twoCycle 0).2 (by decide)
  have hd : credulous twoCycle 0 = .defeated :=
    (hdefeated twoCycle 0).2 (by decide)
  cases hj.symm.trans hd

/-- **The symmetry shows the counterexample is not an artifact of argument
`0`.** Decided independently rather than derived from
`profile_preferredSem_twoCycle`, so the two theorems have no dependency between
them. -/
theorem profile_preferredSem_twoCycle_symm :
    profile preferredSem twoCycle 0 = profile preferredSem twoCycle 1 := by decide

/-- **The full profile record, for every carrier argument.** `inAll` and `outAll`
are `false` while `inSome` and `outSome` are `true`: skeptical and credulous
readings genuinely separate here, which is the counterpoint `profile_grounded`'s
docstring points at. The `inAll = false` half is also the exact fact `observe`'s
docstring cites when it argues that the argument-level reading of `justified` has
nothing to report on `claimBoth`. -/
theorem profile_preferredSem_twoCycle : ∀ a ∈ twoCycle.args,
    profile preferredSem twoCycle a =
      { inAll := false, inSome := true, outAll := false, outSome := true } := by decide

/-- **All four bits `false`.** Under `groundedSem` the two-cycle's arguments are
accepted by no extension and attacked by no extension. This is the witness the
`AcceptanceProfile` section note is built on: `¬ inSome` here does *not* mean
"attacked", and a two-field record that derived rejection from acceptance would
report a defeat the grounded semantics never asserts. -/
theorem profile_groundedSem_twoCycle : ∀ a ∈ twoCycle.args,
    profile groundedSem twoCycle a =
      { inAll := false, inSome := false, outAll := false, outSome := false } := by decide

/-- **Grounded and preferred differ on a two-node framework.** Read off the four
conjuncts: on `claimZero` the two agree (`contested`), so the difference is not an
artifact of the semantics disagreeing everywhere; on `claimBoth` they separate,
`groundedSem` reporting `contested` where `preferredSem` reports `justified`.
The last two conjuncts are the witness `observe_gap`'s docstring cites for
`justified` varying with the semantics. -/
theorem observe_twoCycle_grounded_ne_preferred :
    observe groundedSem twoCycle claimZero = ClaimObservation.observed Status.contested ∧
      observe preferredSem twoCycle claimZero = ClaimObservation.observed Status.contested ∧
      observe groundedSem twoCycle claimBoth = ClaimObservation.observed Status.contested ∧
      observe preferredSem twoCycle claimBoth = ClaimObservation.observed Status.justified := by
  decide

/-- **`defeated` varies with the semantics too.** The last two conjuncts are the
reason for the first two: the sink argument `2` is attacked by both preferred
extensions of `twoCycleSink`, while the sole grounded extension is empty and
attacks nothing — so `preferredSem` reports `defeated` where `groundedSem` reports
`contested`. With `observe_twoCycle_grounded_ne_preferred` this completes the case
that each of the three non-`gap` statuses is semantics-dependent, which is what
makes `observe_gap` a statement about `gap` in particular rather than about
`observe` in general. -/
theorem observe_twoCycleSink_grounded_ne_preferred :
    observe groundedSem twoCycleSink claimSink = ClaimObservation.observed Status.contested ∧
      observe preferredSem twoCycleSink claimSink = ClaimObservation.observed Status.defeated ∧
      preferredSem.enumerate twoCycleSink = [[0], [1]] ∧
      groundedSem.enumerate twoCycleSink = [[]] := by
  decide

/-! ### `observe` does not factor through `profile` -/

/-- The complete extensions of the two-cycle. Compare with
`preferredSem_enumerate_twoCycle`: the two lists differ by exactly the entry `[]`,
since the empty set is complete but not `⊆`-maximal among admissible sets. -/
theorem completeSem_enumerate_twoCycle :
    completeSem.enumerate twoCycle = [[], [0], [1]] := by decide

/-- **The claim-level reading is not recoverable from per-argument data (D8).**
Two adequate semantics assign *every* carrier argument of the two-cycle the same
`AcceptanceProfile`, and still disagree about `claimBoth`: `completeSem` observes
`contested`, `preferredSem` observes `justified`. So `observe`'s refusal to be
defined through `profile` is forced rather than stylistic: it cannot be rewritten
as a function of the framework, the claim, and the per-argument profiles alone.

The fourth conjunct is the mechanism. Comparing `completeSem_enumerate_twoCycle`
with `preferredSem_enumerate_twoCycle`, the two enumerations differ by exactly the
entry `[]`, and `claimAcceptedB [] claimBoth = false` — so that one extra
extension falsifies the `∀E ∃a` fold while leaving every profile bit where it
already was.

This is sharper evidence than the argument-level statement recorded in `observe`'s
docstring. That one only shows the `∃a ∀E` reading is *silent* on `claimBoth`
(`profile_preferredSem_twoCycle` gives `inAll = false` for both support
arguments); this one exhibits two semantics that are loud and contradictory about
the claim while being indistinguishable on every per-argument bit. -/
theorem observe_not_determined_by_profile :
    (∀ a ∈ twoCycle.args, profile completeSem twoCycle a = profile preferredSem twoCycle a) ∧
      observe completeSem twoCycle claimBoth = ClaimObservation.observed Status.contested ∧
      observe preferredSem twoCycle claimBoth = ClaimObservation.observed Status.justified ∧
      claimAcceptedB [] claimBoth = false := by
  decide

/-! ### `gap` is semantics-independent, exercised -/

/-- **`observe_gap` at all five instances.** Each conjunct is `observe_gap`
applied to the corresponding instance with `rfl : claimNoSupport.support = []`; no
conjunct is decided by evaluation, and no hypothesis about the framework is used.

The `stableSem` conjunct is the one worth reading. By
`stableSem_enumerate_threeCycle` there is no extension at all on this framework,
so this is precisely the input where the two guards of `observe` compete — and the
answer is still `gap`, uniformly with the other four. That is the ordering
decision `observe`'s docstring records, exercised on the input that makes it
visible. -/
theorem observe_claimNoSupport_uniform :
    observe completeSem threeCycle claimNoSupport = ClaimObservation.observed Status.gap ∧
      observe stableSem threeCycle claimNoSupport = ClaimObservation.observed Status.gap ∧
      observe preferredSem threeCycle claimNoSupport = ClaimObservation.observed Status.gap ∧
      observe semiStableSem threeCycle claimNoSupport = ClaimObservation.observed Status.gap ∧
      observe groundedSem threeCycle claimNoSupport = ClaimObservation.observed Status.gap :=
  ⟨observe_gap _ _ _ rfl, observe_gap _ _ _ rfl, observe_gap _ _ _ rfl,
   observe_gap _ _ _ rfl, observe_gap _ _ _ rfl⟩

/-! ### Semi-stable sits strictly between stable and preferred -/

/-- **Semi-stable is a proper refinement of preferred.** On `rangeSplit` the
preferred extensions are `[0]` and `[1]`, but only `[1]` is semi-stable. The last
two conjuncts are the reason, computed rather than asserted: the range of `[0]` is
`[0, 1]` while the range of `[1]` is `[1, 0, 2]`. `SemiStable`'s maximality clause
compares ranges among *complete* extensions, and `[1]` is one — every semi-stable
set is complete by the first conjunct of `SemiStable` — so `[0]` is rejected while
`[1]` survives. -/
theorem semiStable_proper_refinement_of_preferred :
    preferredSem.enumerate rangeSplit = [[0], [1]] ∧
      semiStableSem.enumerate rangeSplit = [[1]] ∧
      reach rangeSplit [0] = [0, 1] ∧ reach rangeSplit [1] = [1, 0, 2] := by decide

/-- **…and strictly outside stable on the three-cycle.** There the semi-stable
semantics still returns the empty extension where the stable semantics returns
nothing. Together with `semiStable_proper_refinement_of_preferred` this
places semi-stable strictly between the two on these two frameworks: strictly
below preferred on `rangeSplit`, strictly above stable on `threeCycle`. -/
theorem semiStable_exists_where_stable_does_not :
    semiStableSem.enumerate threeCycle = [[]] ∧ stableSem.enumerate threeCycle = [] := by decide

/-! ### The two enumerations the pairwise separations were missing

Ten unordered pairs can be formed from the five instances, and each is separated
by at least one of the five separation frameworks above; `reinstatementChain`
exists for conformance coverage rather than separation. Two of the ten were
separated only by *evaluation* before this section, because no theorem stated
both members' enumerations on a common framework: (`groundedSem`,
`semiStableSem`) and
(`completeSem`, `semiStableSem`). The reason is the same for both —
`semiStableSem.enumerate` was stated by a theorem at `threeCycle` and at
`rangeSplit` only, `groundedSem.enumerate` and `completeSem.enumerate` were never
stated at `rangeSplit`, and on `threeCycle` every instance except `stableSem`
returns `[[]]` (`threeCycle_enumerate_nonStable`), so the one shared framework was
one where the pair agrees. -/

/-- **The semi-stable extensions of the two-cycle.** Both preferred extensions
survive, so the list is the one `preferredSem_enumerate_twoCycle` already
states. Read with `groundedSem_enumerate_twoCycle` and
`completeSem_enumerate_twoCycle`, this single equation closes both of the two
unbacked pairs. `twoCycle` is the only framework carrying a stated
`semiStableSem` enumeration, a stated `groundedSem` one, *and* a difference
between them — `threeCycle` carries both but there the two agree. -/
theorem semiStableSem_enumerate_twoCycle :
    semiStableSem.enumerate twoCycle = [[0], [1]] := by decide

/-- **The complete extensions of `rangeSplit`.** With the
`semiStableSem.enumerate rangeSplit = [[1]]` conjunct of
`semiStable_proper_refinement_of_preferred` this separates `completeSem` from
`semiStableSem` a second time, on a framework where the semi-stable extensions
are a *proper* subset of the preferred ones — unlike `twoCycle`, where
`semiStableSem_enumerate_twoCycle` and `preferredSem_enumerate_twoCycle` are the
same list. It does not close the (`groundedSem`, `semiStableSem`) pair, since
`groundedSem.enumerate rangeSplit` is stated by no theorem. -/
theorem completeSem_enumerate_rangeSplit :
    completeSem.enumerate rangeSplit = [[], [0], [1]] := by decide

/-- **The five instances are pairwise distinct as enumerators.** Ten conjuncts,
one per unordered pair, each naming a framework that separates that pair: five
pairs are separated by `twoCycle`, four by `threeCycle`, one by `rangeSplit`.
This is the statement that rules out `ExtensionSemantics` being an abstraction
over a one-element set, and it is stated in one place so that the count "ten"
is checked by the elaborator rather than by a reader counting theorems.

Every conjunct is decided directly from the definitions, so none of it depends
on the equations above; what those equations add is that each conjunct can also
be *read off* two stated enumerations. -/
theorem five_semantics_pairwise_distinct :
    groundedSem.enumerate twoCycle ≠ completeSem.enumerate twoCycle ∧
      groundedSem.enumerate twoCycle ≠ preferredSem.enumerate twoCycle ∧
      groundedSem.enumerate threeCycle ≠ stableSem.enumerate threeCycle ∧
      groundedSem.enumerate twoCycle ≠ semiStableSem.enumerate twoCycle ∧
      completeSem.enumerate twoCycle ≠ preferredSem.enumerate twoCycle ∧
      completeSem.enumerate threeCycle ≠ stableSem.enumerate threeCycle ∧
      completeSem.enumerate twoCycle ≠ semiStableSem.enumerate twoCycle ∧
      preferredSem.enumerate threeCycle ≠ stableSem.enumerate threeCycle ∧
      preferredSem.enumerate rangeSplit ≠ semiStableSem.enumerate rangeSplit ∧
      stableSem.enumerate threeCycle ≠ semiStableSem.enumerate threeCycle := by
  decide


/-! ### The last two evaluation-only claims in this module, promoted

Two `def` docstrings above used to assert facts that nothing checked: what the
conflict-free sets of `threeCycle` are, and what extensions the five instances
produce on `twoCycle`. Both are now theorems, and both docstrings cite them. -/

/-- **The conflict-free sets of the bare three-cycle.** Exactly the empty set and
the three singletons — the fact `threeCycle`'s docstring states. Phrased over the
same `candidates` scan the enumerators filter, so it is a statement about
`conflictFreeB` on this framework rather than about a hand-listed collection.
`stableSem_enumerate_threeCycle` records the consequence (a stable set is
conflict-free, and none of these four attacks every argument it omits) and is
decided independently of this equation. -/
theorem threeCycle_conflictFree :
    (candidates threeCycle).filter (conflictFreeB threeCycle) = [[], [0], [1], [2]] := by
  decide

/-- **The two-cycle produces only three extensions, under any of the five
instances.** The first conjunct is the exact sentence `twoCycleSink`'s docstring
used to assert by evaluation. The second supplies the one enumeration of the five
that no theorem in the tree stated — `groundedSem`, `completeSem`, `preferredSem`
and `semiStableSem` on `twoCycle` are `groundedSem_enumerate_twoCycle`,
`completeSem_enumerate_twoCycle`, `preferredSem_enumerate_twoCycle` and
`semiStableSem_enumerate_twoCycle`. The last two say `0` attacks `1` and nothing
else while `1` attacks `0` and nothing else, quantified over *all* arguments
rather than over the carrier, since `Semantics.attackedByB` leaves its target
unbounded and a claim may be supported outside `twoCycle.args`.

**The first conjunct is an upper bound and proves nothing about defeat on its
own.** An earlier draft of this docstring argued from it that `Status.defeated`
is unreachable here; that argument was wrong. Read the bound as a property of an
enumeration and `[[0]]` has it, yet a semantics enumerating exactly `[[0]]`
observes the claim supported by `[1]` as `defeated`, because `[0]` attacks `1`
and there is no second extension to disagree. The unreachability needs a *lower*
bound as
well — that each enumeration contains `[]`, or contains both `[0]` and `[1]` —
which is what the five exact equations give and what the first conjunct does not.
`twoCycle_defeated_unreachable` is the corrected statement, proved rather than
argued. -/
theorem twoCycle_extensions :
    (∀ sem ∈ [groundedSem, completeSem, preferredSem, stableSem, semiStableSem],
        ∀ E ∈ sem.enumerate twoCycle, E = [] ∨ E = [0] ∨ E = [1]) ∧
      stableSem.enumerate twoCycle = [[0], [1]] ∧
      (∀ b, twoCycle.attack 0 b = true ↔ b = 1) ∧
      (∀ b, twoCycle.attack 1 b = true ↔ b = 0) := by
  refine ⟨by decide, by decide, ?_, ?_⟩ <;> (intro b; simp [twoCycle])

/-- **One non-defeating extension is enough.** If some enumerated extension fails
to defeat the claim, `observe` cannot report `defeated`, whatever the semantics
and whatever the framework: the `defeated` arm is guarded by a `List.all` over the
enumeration, so a single counterexample in the list closes it. Proved by
splitting `observe`'s four `if`s; the other three arms return a constructor that
`Status.defeated` is not.

This is the lemma the unreachability argument needs, and it is where the "one
extension suffices" step is discharged once instead of five times. -/
theorem observe_ne_defeated_of_mem_enumerate {sem : ExtensionSemantics} {F : AF}
    {c : Grounded.Claim} {E : List Arg} (hE : E ∈ sem.enumerate F)
    (hd : claimDefeatedB F E c = false) :
    observe sem F c ≠ ClaimObservation.observed Status.defeated := by
  intro h
  unfold observe at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · rename_i hall
          have hE' := List.all_eq_true.mp hall E hE
          rw [hd] at hE'
          exact Bool.noConfusion hE'
        · simp at h

/-- **The empty extension defeats nothing with support to defeat.**
`claimDefeatedB F [] c` is `c.support.all (attackedByB F [])`, and
`attackedByB F [] a` is `List.any [] _`, which is `false`; a non-empty support
therefore has a witness that fails. No hypothesis on `F`. -/
theorem claimDefeatedB_nil_eq_false {F : AF} {c : Grounded.Claim}
    (hs : c.support ≠ []) : claimDefeatedB F [] c = false := by
  cases hsup : c.support with
  | nil => exact absurd hsup hs
  | cons a t => simp [claimDefeatedB, hsup, attackedByB]

/-- **On `twoCycle`, `[0]` and `[1]` cannot both defeat the same supported
claim.** Case on the head `a` of the support: if `a = 1` then `[1]` does not
attack it (`twoCycle.attack 1 1 = false`), and otherwise `[0]` does not
(`twoCycle.attack 0 a` is `a == 1`). This is the disjointness of the two attacked
sets, stated in the form the guard actually consumes — as a claim about
`claimDefeatedB`, not about the carrier-filtered `Semantics.attacked`, so it
covers a support argument outside `twoCycle.args` too. -/
theorem twoCycle_defeat_split (c : Grounded.Claim) (hs : c.support ≠ []) :
    claimDefeatedB twoCycle [0] c = false ∨ claimDefeatedB twoCycle [1] c = false := by
  cases hsup : c.support with
  | nil => exact absurd hsup hs
  | cons a t =>
    by_cases ha : a = 1
    · right; subst ha; simp [claimDefeatedB, hsup, attackedByB, twoCycle]
    · left; simp [claimDefeatedB, hsup, attackedByB, twoCycle, ha]

/-- **`Status.defeated` is unreachable on the bare two-cycle**, under all five
instances, for every claim with non-empty support. The claim the `twoCycleSink`
docstring makes, now proved rather than inferred from an upper bound.

The two halves of the proof are the two lower bounds, and each is used where the
enumeration supplies it. `groundedSem` and `completeSem` enumerate `[]`
(`groundedSem_enumerate_twoCycle`, `completeSem_enumerate_twoCycle`), and
`claimDefeatedB_nil_eq_false` kills the guard there. `preferredSem`, `stableSem`
and `semiStableSem` enumerate both `[0]` and `[1]`
(`preferredSem_enumerate_twoCycle`, the second conjunct of `twoCycle_extensions`,
`semiStableSem_enumerate_twoCycle`), and `twoCycle_defeat_split` supplies one of
the two as the non-defeating witness. Every membership is discharged by `decide`
against the enumerator, so the proof does not depend on those four equations
being stated — it depends on them being *true*, which is the same fact.

`twoCycleSink` exists because adding an argument `2` that both `0` and `1` attack
removes the obstruction: `observe_twoCycleSink_grounded_ne_preferred` reports
`defeated` there. -/
theorem twoCycle_defeated_unreachable (c : Grounded.Claim) (hs : c.support ≠ []) :
    observe groundedSem twoCycle c ≠ ClaimObservation.observed Status.defeated ∧
      observe completeSem twoCycle c ≠ ClaimObservation.observed Status.defeated ∧
      observe preferredSem twoCycle c ≠ ClaimObservation.observed Status.defeated ∧
      observe stableSem twoCycle c ≠ ClaimObservation.observed Status.defeated ∧
      observe semiStableSem twoCycle c ≠ ClaimObservation.observed Status.defeated := by
  refine ⟨observe_ne_defeated_of_mem_enumerate (E := []) (by decide)
            (claimDefeatedB_nil_eq_false hs),
          observe_ne_defeated_of_mem_enumerate (E := []) (by decide)
            (claimDefeatedB_nil_eq_false hs), ?_, ?_, ?_⟩
  · rcases twoCycle_defeat_split c hs with h0 | h1
    · exact observe_ne_defeated_of_mem_enumerate (E := [0]) (by decide) h0
    · exact observe_ne_defeated_of_mem_enumerate (E := [1]) (by decide) h1
  · rcases twoCycle_defeat_split c hs with h0 | h1
    · exact observe_ne_defeated_of_mem_enumerate (E := [0]) (by decide) h0
    · exact observe_ne_defeated_of_mem_enumerate (E := [1]) (by decide) h1
  · rcases twoCycle_defeat_split c hs with h0 | h1
    · exact observe_ne_defeated_of_mem_enumerate (E := [0]) (by decide) h0
    · exact observe_ne_defeated_of_mem_enumerate (E := [1]) (by decide) h1


/-! ### What the `Nodup` hypothesis is for, and what it is not for

The M2a plan asked for a witness aimed at "the `Nodup` hypothesis in Task 1's
adequacy". There is no such hypothesis to witness against: `ExtensionSemantics`
binds `F.args.Nodup` in the `sound` field, but all five instances discard it, and
`sound_holds_without_nodup` below is the five adequacy statements re-proved with
no hypothesis in scope at all. What `Nodup` actually buys is *representative
uniqueness* — `Semantics.candidates_ext` and `Semantics.enumerate_ext`, which say
that over a duplicate-free carrier no two candidates, and no two enumerated
extensions, denote the same set of arguments. The witnesses below are aimed at
that, so this section mechanizes the two-sided claim made in prose by the
*Representation* paragraph of `Lara.Semantics`'s module header. -/

/-- A carrier with the argument `0` repeated. The smallest framework on which
`List.Nodup` fails; `attack` is constantly `false` so nothing about the attack
relation can be blamed for what the next two theorems exhibit. -/
def dupCarrier : AF where
  args := [0, 0]
  attack := fun _ _ => false

/-- **The candidate scan over-counts on a duplicated carrier.** The carrier is
not `Nodup`, and `candidates` lists four entries for a two-element multiset whose
underlying set has two subsets: `[0]` occurs twice, and `[0, 0]` is a fourth entry
with the same members as `[0]`. This is the concrete shape of the failure that
`Semantics.candidates_nodup` and `Semantics.candidates_ext` rule out under
`Nodup`. -/
theorem dupCarrier_candidates :
    ¬ dupCarrier.args.Nodup ∧ candidates dupCarrier = [[], [0], [0], [0, 0]] := by
  decide

/-- **Representative uniqueness is genuinely false without `Nodup`**, at the
candidate level. The refutation of `Semantics.candidates_ext` with its hypothesis
deleted, witnessed by `[0]` and `[0, 0]` in `candidates dupCarrier`: two entries
that are not equal as lists and have the same members. -/
theorem not_candidates_ext_without_nodup :
    ¬ (∀ (F : AF) (S T : List Arg), S ∈ candidates F → T ∈ candidates F →
        (∀ x, x ∈ S ↔ x ∈ T) → S = T) := by
  intro h
  have hEq := h dupCarrier [0] [0, 0] (by decide) (by decide) (by intro x; simp)
  simp at hEq

/-- **…and at the enumeration level.** The refutation of
`Semantics.enumerate_ext` with its hypothesis deleted. `completeSem` is used
because both `[0]` and `[0, 0]` are complete extensions of `dupCarrier`; the
choice of instance is not the point, and any of the five would do here, since all
five enumerate the same three entries on this attack-free framework. -/
theorem not_enumerate_ext_without_nodup :
    ¬ (∀ (sem : ExtensionSemantics) (F : AF) (S T : List Arg),
        S ∈ sem.enumerate F → T ∈ sem.enumerate F → (∀ x, x ∈ S ↔ x ∈ T) → S = T) := by
  intro h
  have hEq := h completeSem dupCarrier [0] [0, 0] (by decide) (by decide) (by intro x; simp)
  simp at hEq

/-- **All five instances agree on `dupCarrier`, and all three entries survive.**
The supporting fact for the previous theorem's "any of the five would do", and
the reason it can be said without hedging. -/
theorem dupCarrier_enumerate :
    groundedSem.enumerate dupCarrier = [[0], [0], [0, 0]] ∧
      completeSem.enumerate dupCarrier = [[0], [0], [0, 0]] ∧
      preferredSem.enumerate dupCarrier = [[0], [0], [0, 0]] ∧
      stableSem.enumerate dupCarrier = [[0], [0], [0, 0]] ∧
      semiStableSem.enumerate dupCarrier = [[0], [0], [0, 0]] := by
  decide

/-- **Adequacy needs no `Nodup`, at every instance and every framework.** Each
conjunct is `ExtensionSemantics.sound`'s conclusion for one of the five instances
with the `F.args.Nodup` hypothesis simply absent, proved by the same
`rw [mem_filter_candidates, ..B_iff]` the instance's own `sound` field uses,
behind a `show` that spells out the filter the field's projection hides. Since
`F` is universally quantified, `dupCarrier` is covered.

Read against `not_enumerate_ext_without_nodup`, this is the separation the
section is for: on `dupCarrier` the adequacy characterization still holds
verbatim, and representative uniqueness fails. The hypothesis therefore stays in
the field for the consumer's sake (`enumerate_ext`), not for the producer's. -/
theorem sound_holds_without_nodup (F : AF) (S : List Arg) :
    (S ∈ completeSem.enumerate F ↔ (S.Sublist F.args ∧ completeSem.spec F S)) ∧
      (S ∈ stableSem.enumerate F ↔ (S.Sublist F.args ∧ stableSem.spec F S)) ∧
      (S ∈ groundedSem.enumerate F ↔ (S.Sublist F.args ∧ groundedSem.spec F S)) ∧
      (S ∈ preferredSem.enumerate F ↔ (S.Sublist F.args ∧ preferredSem.spec F S)) ∧
      (S ∈ semiStableSem.enumerate F ↔ (S.Sublist F.args ∧ semiStableSem.spec F S)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show S ∈ (candidates F).filter (completeB F) ↔ (S.Sublist F.args ∧ Complete F S)
    rw [mem_filter_candidates, completeB_iff]
  · show S ∈ (candidates F).filter (stableB F) ↔ (S.Sublist F.args ∧ Stable F S)
    rw [mem_filter_candidates, stableB_iff]
  · show S ∈ (candidates F).filter (leastCompleteB F) ↔ (S.Sublist F.args ∧ LeastComplete F S)
    rw [mem_filter_candidates, leastCompleteB_iff]
  · show S ∈ (candidates F).filter (preferredB F) ↔ (S.Sublist F.args ∧ Preferred F S)
    rw [mem_filter_candidates, preferredB_iff]
  · show S ∈ (candidates F).filter (semiStableB F) ↔ (S.Sublist F.args ∧ SemiStable F S)
    rw [mem_filter_candidates, semiStableB_iff]


/-! ### `AgreesOnArgs` is strictly weaker than `Compile.Faithful`

`Lara.Observation`'s header explains that every transport theorem there is stated
over `AgreesOnArgs` — `Compile.Faithful.agrees` on its own — rather than over
`Compile.Faithful`, because the two `Faithful` fields together pin the oracle down
as a function (`Observation.faithful_unique`) and a transport hypothesising them
would be a `funext` away. That argument establishes that `Faithful` is *rigid*; it
does not by itself establish that `AgreesOnArgs` is *weaker*, and step 5 of this
milestone said so rather than overclaiming. The witness below closes that gap.

It lives here and not in `Lara.Observation` for a structural reason: it needs a
concrete `Compile.CheckedProgram`, and the only one in the tree is
`Lara.Examples.PEx`. Putting it in `Observation.lean` would make that module
import `Lara.Examples`, inverting the dependency direction its header is built
on — `Observation` is the module that depends on `Compile` and `Semantics` and on
nothing further out. -/

section AgreesOnArgsStrictness

open Lara.Observation

/-- The checker's own edge decider for `PEx`, with one junk edge bolted on at the
undeclared index pair `(999, 999)`. `PEx.args` has three entries, so the junk
edge is invisible to any test that indexes into the declared arguments and
visible to `Compile.Faithful.ranged`, which quantifies over all index pairs. -/
def eJunk : Nat → Nat → Bool :=
  fun i j => Compile.edgeB Examples.PEx i j || (i == 999 && j == 999)

/-- `eJunk` agrees on declared arguments. `P.args[i]? = some a` forces
`i < PEx.args.length = 3`, hence `i ≠ 999`, so at every pair the hypothesis
reaches, `eJunk` is `Compile.edgeB PEx` and `Compile.edgeB_faithful` supplies the
verdict. -/
theorem eJunk_agreesOnArgs : AgreesOnArgs Examples.PEx eJunk := by
  intro i j a b ha hb
  obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp ha
  rw [Examples.PEx_args] at hi
  simp only [List.length_cons, List.length_nil] at hi
  have hne : ¬ (i = 999) := by omega
  have hE : eJunk i j = Compile.edgeB Examples.PEx i j := by simp [eJunk, hne]
  rw [hE]
  exact (Compile.edgeB_faithful Examples.PEx).agrees i j a b ha hb

/-- `eJunk` is not faithful. `eJunk 999 999 = true`, so `ranged` would give
`999 < PEx.args.length`, and `Examples.PEx_args` makes that length `3`. Only
`ranged` fails; `agrees` is the previous theorem. -/
theorem not_faithful_eJunk : ¬ Compile.Faithful Examples.PEx eJunk := by
  intro hf
  have h999 : eJunk 999 999 = true := by simp [eJunk]
  obtain ⟨hlt, -⟩ := hf.ranged 999 999 h999
  rw [Examples.PEx_args] at hlt
  simp only [List.length_cons, List.length_nil] at hlt
  omega

/-- **`AgreesOnArgs` is strictly weaker than `Compile.Faithful`.** One oracle
satisfies the first and not the second, so the implication
`Observation.agreesOnArgs_of_faithful` has no converse and the transport theorems
of `Lara.Observation` really do apply to oracles that `Faithful` rejects. This
upgrades step 5's honest disclaimer — that `AgreesOnArgs` "asks for less" — to a
theorem.

Stated as one conjunction because the pair is the content: either half alone is
a fact about `eJunk` and says nothing about the two hypotheses. -/
theorem agreesOnArgs_strictly_weaker_than_faithful :
    AgreesOnArgs Examples.PEx eJunk ∧ ¬ Compile.Faithful Examples.PEx eJunk :=
  ⟨eJunk_agreesOnArgs, not_faithful_eJunk⟩

end AgreesOnArgsStrictness


/-! ### The observation table

The milestone deliverable: one row per (semantics, framework, claim), printed
from Lean rather than written by hand, so the figure it becomes cannot drift from
the definitions. Everything above is a theorem about one or two cells of this
table; the table is what shows the whole grid at once.

`ExtensionSemantics` deliberately carries no name field — an instance is a
specification, an enumerator and an adequacy proof, and a `String` in the record
would be data no theorem could use. The row labels therefore come from closed sum
types (`CLAUDE.md`: a fixed vocabulary is a sum type, not string literals), each with exactly one spelling table and exactly one mapping to the
object it names.

The semantics vocabulary is owned by `Lara.Semantics.Registry`; the names here
are compatibility aliases. Total object/label maps and the completeness theorem
cover the closed vocabulary. The repository environment audit additionally
rejects named closed `ExtensionSemantics` declarations absent from that registry,
including declarations in modules outside the root import graph. Generic
parameters and local values remain outside this finite repository inventory. -/

/-- Compatibility alias for the core registry's closed vocabulary. -/
abbrev SemanticsName := Lara.Semantics.Registry.SemanticsName

namespace SemanticsName
export Lara.Semantics.Registry.SemanticsName
  (grounded complete preferred stable semiStable)
end SemanticsName

/-- The six table frameworks of this module, as a closed sum type. Constructor
names are the `def` names verbatim. -/
inductive FrameworkName where
  /-- `threeCycle` -/
  | threeCycle
  /-- `threeCycleAttacked` -/
  | threeCycleAttacked
  /-- `twoCycle` -/
  | twoCycle
  /-- `twoCycleSink` -/
  | twoCycleSink
  /-- `rangeSplit` -/
  | rangeSplit
  /-- `reinstatementChain` -/
  | reinstatementChain
deriving DecidableEq, Repr

/-- The four claims of this module, as a closed sum type. Constructor names are
the `def` names verbatim. -/
inductive ClaimName where
  /-- `claimZero` -/
  | claimZero
  /-- `claimBoth` -/
  | claimBoth
  /-- `claimSink` -/
  | claimSink
  /-- `claimNoSupport` -/
  | claimNoSupport
deriving DecidableEq, Repr

/-- Compatibility alias for the core registry's spelling table. -/
abbrev semanticsLabel := Lara.Semantics.Registry.semanticsLabel

/-- Compatibility alias for the core registry's object map. -/
abbrev semanticsInstance := Lara.Semantics.Registry.semanticsInstance

/-- Compatibility alias for the core registry's row order. -/
abbrev allSemantics := Lara.Semantics.Registry.allSemantics

/-- The core registry lists every supported semantics constructor. -/
theorem allSemantics_complete : ∀ s : SemanticsName, s ∈ allSemantics :=
  Lara.Semantics.Registry.allSemantics_complete

/-- The one place a framework's printed spelling is written. -/
def frameworkLabel : FrameworkName → String
  | .threeCycle         => "threeCycle"
  | .threeCycleAttacked => "threeCycleAttacked"
  | .twoCycle           => "twoCycle"
  | .twoCycleSink       => "twoCycleSink"
  | .rangeSplit         => "rangeSplit"
  | .reinstatementChain => "reinstatementChain"

/-- The one place a framework name is mapped to its `AF`. -/
def frameworkAF : FrameworkName → AF
  | .threeCycle         => threeCycle
  | .threeCycleAttacked => threeCycleAttacked
  | .twoCycle           => twoCycle
  | .twoCycleSink       => twoCycleSink
  | .rangeSplit         => rangeSplit
  | .reinstatementChain => reinstatementChain

/-- Block order for the framework axis, in declaration order. -/
def allFrameworks : List FrameworkName :=
  [.threeCycle, .threeCycleAttacked, .twoCycle, .twoCycleSink, .rangeSplit,
    .reinstatementChain]

/-- `allFrameworks` lists every constructor. Same reason as
`allSemantics_complete`. -/
theorem allFrameworks_complete : ∀ f : FrameworkName, f ∈ allFrameworks := by
  intro f; cases f <;> decide

/-- The one place a claim's printed spelling is written. -/
def claimLabel : ClaimName → String
  | .claimZero      => "claimZero"
  | .claimBoth      => "claimBoth"
  | .claimSink      => "claimSink"
  | .claimNoSupport => "claimNoSupport"

/-- The one place a claim name is mapped to its `Grounded.Claim`. -/
def claimOf : ClaimName → Grounded.Claim
  | .claimZero      => claimZero
  | .claimBoth      => claimBoth
  | .claimSink      => claimSink
  | .claimNoSupport => claimNoSupport

/-- Block order for the claim axis, in declaration order. -/
def allClaims : List ClaimName :=
  [.claimZero, .claimBoth, .claimSink, .claimNoSupport]

/-- `allClaims` lists every constructor. Same reason as
`allSemantics_complete`. -/
theorem allClaims_complete : ∀ c : ClaimName, c ∈ allClaims := by
  intro c; cases c <;> decide

/-- The printed spelling of an observation: the four `Status` constructors plus
`noExtension`. Written out rather than delegated to the derived `Repr` so that a
cell is one word — the derived `Repr` prints
`Lara.Semantics.ClaimObservation.observed (Lara.Grounded.Status.justified)`,
which no column width survives. Keeping the
emitted rows free of `[...]` is deliberate too: the `#eval` runs during
`lake build`, and `scripts/check-axioms.sh` reads every bracketed list in its
input as a set of axiom names, so a table that printed extension lists would be
one redirected pipe away from breaking the gate. (It does not today — the gate
runs `lake env lean AxCheck.lean`, which loads this module from its `.olean` and
never re-runs the `#eval`.) -/
def renderObservation : ClaimObservation → String
  | .noExtension          => "noExtension"
  | .observed .justified  => "justified"
  | .observed .contested  => "contested"
  | .observed .defeated   => "defeated"
  | .observed .gap        => "gap"

/-- Left-justify in a fixed column width. `Nat` subtraction saturates at zero, so
an over-long cell is printed in full and pushes the row rather than truncating a
label. -/
def padRight (w : Nat) (s : String) : String := s ++ "".pushn ' ' (w - s.length)

/-- Right-justify, for the numeric column. -/
def padLeft (w : Nat) (s : String) : String := "".pushn ' ' (w - s.length) ++ s

/-- One table row. `|E|` is the number of extensions the semantics enumerates on
that framework. It is what makes a `justified` or `defeated` cell readable as a
claim about one extension or about several, and it is the column that shows
`observe`'s guard order: `|E| = 0` gives `noExtension` on the three supported
claims and still gives `gap` on `claimNoSupport`, because the `gap` guard is
tested first. -/
def tableRow (s : SemanticsName) (f : FrameworkName) (c : ClaimName) : String :=
  let sem := semanticsInstance s
  let F := frameworkAF f
  padRight 12 (semanticsLabel s) ++ padRight 20 (frameworkLabel f)
    ++ padRight 16 (claimLabel c)
    ++ padLeft 4 (toString (sem.enumerate F).length) ++ "  "
    ++ renderObservation (observe sem F (claimOf c))

/-- The column headings, using the same widths as `tableRow`. -/
def tableHeader : String :=
  padRight 12 "semantics" ++ padRight 20 "framework" ++ padRight 16 "claim"
    ++ padLeft 4 "|E|" ++ "  " ++ "observation"

/-- The rule under the headings; 65 is the total row width
(12 + 20 + 16 + 4 + 2 + 11). -/
def tableRule : String := "".pushn '-' 65

/-- **The table.** Rows are grouped framework-major, then by claim, so the five
semantics on one (framework, claim) input sit adjacent and a disagreement is a
difference between neighbouring lines. Each row still carries all three labels,
so a single line is meaningful on its own when the figure is cropped. -/
def observationTable : String :=
  String.intercalate "\n"
    (tableHeader :: tableRule ::
      allFrameworks.flatMap (fun f =>
        allClaims.flatMap (fun c =>
          "" :: allSemantics.map (fun s => tableRow s f c))))

/-! Emit the table. What is checked in is the generator, not a transcript: the
figure is regenerated on every build of this module, so it cannot drift from the
definitions the way a pasted table would. -/

#eval IO.println observationTable

/-! ### The Haskell conformance goldens

`src/Lara/Semantics.hs` is a hand-written Haskell mirror of the enumeration half
of `Lara.Semantics`, and `test/SemanticsSpec.hs` checks it against the values
Lean computes here. Those values are *transcribed* into the Haskell test module,
so the emitter below prints them already formatted as a Haskell literal: refreshing
the goldens is a copy-paste, never a re-derivation by hand.

Regenerate with

    cd lean && LARA_EMIT_GOLDENS=1 lake env lean Lara/Examples/Semantics.lean

and paste the emitted block over `leanGoldens` in `test/SemanticsSpec.hs`.

**Why the environment guard.** `renderObservation`'s docstring records that the
rows this file emits during `lake build` are deliberately free of `[...]`,
because `scripts/check-axioms.sh` reads every bracketed list in its input as a
set of axiom names. A Haskell list literal is nothing but brackets, so this
`#eval` prints only when `LARA_EMIT_GOLDENS` is set, which no build or gate
command sets. `lake env lean` on this file re-elaborates it from source, which is
what makes the guarded `#eval` fire on demand even though the `.olean` is
current. -/

/-- One extension as a Haskell list literal. -/
def renderArgs (S : List Arg) : String :=
  "[" ++ String.intercalate "," (S.map toString) ++ "]"

/-- An enumeration as a Haskell list-of-lists literal. -/
def renderExtensions (E : List (List Arg)) : String :=
  "[" ++ String.intercalate "," (E.map renderArgs) ++ "]"

/-- One row of the golden table, as a Haskell tuple. Reads the semantics through
`semanticsInstance` and the framework through `frameworkAF`, the same two
functions `tableRow` uses, so a golden row cannot name one instance and evaluate
another. -/
def haskellGoldenRow (f : FrameworkName) (s : SemanticsName) : String :=
  "  , (\"" ++ frameworkLabel f ++ "\", \"" ++ semanticsLabel s ++ "\", "
    ++ renderExtensions ((semanticsInstance s).enumerate (frameworkAF f)) ++ ")"

/-- The whole golden block, ready to paste. Framework-major then semantics, the
same order as `observationTable`. The first row's leading `, ` is rewritten to
`[ ` so the block opens the way a hand-written Haskell list would. -/
def haskellGoldens : String :=
  let rows := allFrameworks.flatMap (fun f => allSemantics.map (haskellGoldenRow f))
  String.intercalate "\n"
    ([ "leanGoldens :: [(String, String, [[Int]])]", "leanGoldens =" ]
      ++ (match rows with
          | [] => ["  []"]
          | r :: rest => ("  [ " ++ r.drop 4) :: rest)
      ++ ["  ]"])

/-! Emit the goldens, but only on demand — see the section note. The type
ascription is required twice over: `IO.getEnv` would otherwise fix the monad to
`BaseIO`, and `Unit` alone resolves to `Lara.Unit` inside this namespace. -/

#eval show IO _root_.Unit from do
  if (← IO.getEnv "LARA_EMIT_GOLDENS").isSome then
    IO.println haskellGoldens

end Lara.Examples.Semantics
