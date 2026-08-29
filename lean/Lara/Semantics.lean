/-
Semantics-parametric claim observation (`Lara.Semantics`). This file makes the
*semantics parameter* of the whole development explicit.

**Why this module exists.** Every status theorem in the tree so far reads
`Lara.Grounded.grounded` and nothing else: `labelC`, `statusC`, result 6 and
result 7 are all statements about one particular extension semantics. That was a
choice, not a necessity, and until now the choice was invisible — there was no
object in the development that a *different* Dung semantics could instantiate.
`ExtensionSemantics` is that object. It packages a declarative specification
(`spec : AF → List Arg → Prop`), a proof-oriented enumerator (`enumerate`), and
the adequacy proof tying them together; the grounded results become *the grounded
instance* of an interface rather than the only thing sayable.

**Scope.** Exactly the scope discipline of `Lara.Grounded`: everything here
quantifies over an arbitrary finite `F : AF`. This module knows nothing about
policies, support terms, checkers, compiled programs, or accepted units, and
nothing downstream of `Lara.Grounded` may leak into it. It re-uses
`Grounded.defendedB`, `Grounded.ConflictFree`, `Grounded.grounded` and their
lemmas rather than restating them, so there is exactly one characteristic
operator in the development.

**Performance disclaimer — read this before reading `candidates`.** The
enumeration here is a *proof-oriented reference*, in exactly the sense of
`Grounded.lean`'s evaluator, only more so. `candidates` is a powerset scan: it
enumerates every order-preserving subsequence of the carrier, so it is
exponential in `|args|`, and `preferredB` / `semiStableB` scan that list once per
candidate, i.e. quadratically in an exponential. Nobody should read `candidates`
as a proposed runtime. The runtime evaluator stays grounded — `Grounded.grounded`
is the total, deterministic, polynomial fixed-point computation, and it is what
the driver, the checker, and the claim-status layer call. The enumerations below
exist to give the non-grounded semantics a *meaning* that theorems can quantify
over and that small examples can exercise, not to be executed on real
frameworks.

**Representation, and what `Nodup` buys.** An extension is represented as an
order-preserving subsequence of `F.args` (`List.Sublist`), not as an arbitrary
list. When `F.args.Nodup` holds, each subset of the carrier has *exactly one*
representative, so set equality is list equality and the enumeration is a
faithful powerset. That is not a comment: it is `subseqs_ext` /
`candidates_ext` (same members ⇒ literally equal) together with
`candidates_nodup` (the enumeration itself repeats nothing). `subseqs`,
`subseqs_ext`, `subseqs_nodup` and the lemmas behind them are proved in
`Lara.Semantics.Sublists`; this module transports them to the carrier.

Two things are worth separating here, because they came apart under review.
`ExtensionSemantics.sound` is a pure membership characterization of a filtered
list, and it is true *unconditionally* — all five instances below bind the
`Nodup` hypothesis and discard it, and all five would still compile with the
hypothesis deleted. What `Nodup` actually buys is representative uniqueness,
which is a statement about the enumeration's *shape* rather than its
membership: `enumerate_ext` says that for **any** instance, including ones not
written here, no two entries of `enumerate F` denote the same set. The field
therefore stays in the record — an instance whose enumeration depends on unique
representatives (one deduplicating, counting, or indexing extensions) could not
add the hypothesis after the fact, and `enumerate_ext` derives that guarantee
for it from `sound` alone.

**Why this is additive.** The grounded case is not merely *representable* in the
interface, it is the interface's singleton instance: `groundedSem_enumerate`
shows `groundedSem.enumerate F` is a one-element list whose entry has exactly the
members of `Grounded.grounded F`. That is what makes the agreement checkable —
the `grounded`-indexed theorems downstream (result 6,
`Compile.srcStatus_iff_checked`, `Invariants.status_compileUnit`) still speak
about the same object, so nothing there is weakened, restated, or re-proved. The
theorem is evidence of agreement between the new interface and the old subject,
not a re-derivation of anything downstream, and no result in this module lifts
those theorems to an arbitrary semantics.

Additivity itself is structural, not something this theorem establishes: nothing
that existed before this milestone imports this module, so no pre-existing proof
can change meaning because of it. (Stated that way on purpose. An earlier draft
listed the importers by name and was falsified twice as the milestone added
modules — a docstring that enumerates its own reverse dependencies is a claim the
next `import` line silently breaks, and nothing checks it.)
What `groundedSem_enumerate` adds is that
the new interface and the frozen development provably describe the same set,
rather than two things nobody compared.

`Grounded.AF` deliberately does *not* carry `Nodup` as a field (the M0-frozen
carrier was not changed for this milestone), so the hypothesis is stated
explicitly wherever it is wanted and never silently assumed.

**Where the disagreements live.** No theorem in this module compares two
instances: each names at most one, or is generic over `sem : ExtensionSemantics`.
That shape cannot exhibit two semantics
*disagreeing*, and without a disagreement nothing rules out the interface being an
abstraction over a one-element set. `Lara.Examples.Semantics` supplies the
missing half: five frameworks witness the separations, and a sixth exercises
reinstatement through a defended argument in a multi-element extension. The
concrete-witness theorems that the docstrings below name —
`stableSem_enumerate_threeCycle`, `profile_preferredSem_twoCycle`,
`observe_not_determined_by_profile` and the rest — are declarations of that
module, not of this one.

No Mathlib: `subseqs` and its characterization are done by hand in core Lean 4 in
`Lara.Semantics.Sublists`, as is every proof in this file.
-/

import Lara.Grounded
import Lara.Semantics.Sublists

namespace Lara.Semantics

open Lara.Grounded

/-! ### Candidate extensions

`candidates` and the two facts about it that the rest of the module quotes: what
membership means (`mem_candidates`), and the two `Nodup` consequences proved in
`Lara.Semantics.Sublists`, transported from `subseqs` to the carrier. -/

/-- The candidate extensions of `F`: every order-preserving subsequence of the
carrier. Exponential by construction — see the module header's performance
disclaimer. Every `enumerate` below is a filter of this list, so all five
semantics share one representation choice and one adequacy shape. -/
def candidates (F : AF) : List (List Arg) := subseqs F.args

/-- Membership in `candidates` is exactly the sublist relation the
`ExtensionSemantics.sound` contract quantifies over. -/
theorem mem_candidates {F : AF} {S : List Arg} : S ∈ candidates F ↔ S.Sublist F.args :=
  mem_subseqs

/-- **Representative uniqueness at the carrier level.** Over a duplicate-free
carrier, a candidate is determined by the set of arguments it contains — so the
powerset scan really is a scan of *subsets*, with no set enumerated twice under a
different list layout. This is the fact the module header's representation
paragraph rests on. -/
theorem candidates_ext {F : AF} (h : F.args.Nodup) {S T : List Arg}
    (hS : S ∈ candidates F) (hT : T ∈ candidates F) (hmem : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  subseqs_ext h hS hT hmem

/-- The candidate list itself is duplicate-free over a duplicate-free carrier, so
`(candidates F).length` counts subsets rather than over-counting them. -/
theorem candidates_nodup {F : AF} (h : F.args.Nodup) : (candidates F).Nodup :=
  subseqs_nodup h

/-! ### The predicates

Each Dung condition appears three times: as a `Prop` (what a theorem says), as a
`Bool` (what the reference enumerator computes), and as an `iff` between them.
The split is forced by `Grounded.defendedB`, which is `Bool`-valued, so the
`Prop` layer spells `= true` explicitly rather than hiding it behind a coercion.

**The carrier bound is inside the predicates, not the quantifiers.** This is
load-bearing and must not be "simplified" away. `Grounded.defendedB` only scans
attackers that lie *inside* `F.args`, so an argument outside the carrier that no
carrier member attacks is *vacuously* defended by everything. Concretely, in
`{args := [0], attack := fun _ _ => false}` the junk set `[0, 5]` satisfies the
unbounded reading of admissibility; the intended preferred extension `[0]` would
then fail any unrestricted maximality statement, and `preferredSem`'s adequacy
proof would be unprovable. Requiring `Bounded` as a conjunct of `Admissible` and
`Stable` closes that hole at the source, which is what lets the maximality
clauses below quantify over *arbitrary* lists `T` with no side condition. -/

/-- `S` lies inside the carrier of `F`. A conjunct of `Admissible` and `Stable`
rather than a hypothesis on the ambient quantifiers — see the section note: it is
what rules out vacuously-defended junk outside `F.args`. -/
def Bounded (F : AF) (S : List Arg) : Prop := ∀ a ∈ S, a ∈ F.args

/-- `S` is **admissible**: it lies in the carrier, is conflict-free, and defends
each of its own members. -/
def Admissible (F : AF) (S : List Arg) : Prop :=
  Bounded F S ∧ ConflictFree F S ∧ ∀ a ∈ S, defendedB F S a = true

/-- `S` is a **complete** extension: admissible, and closed under defence — every
carrier argument `S` defends is already in `S`. -/
def Complete (F : AF) (S : List Arg) : Prop :=
  Admissible F S ∧ ∀ a ∈ F.args, defendedB F S a = true → a ∈ S

/-- `S` is a **stable** extension: conflict-free inside the carrier and attacking
every carrier argument it does not contain. Note this is *not* defined through
`Admissible`; stability implies admissibility but the textbook definition is the
attack condition, and keeping it that way leaves the implication a theorem. -/
def Stable (F : AF) (S : List Arg) : Prop :=
  Bounded F S ∧ ConflictFree F S ∧ ∀ a ∈ F.args, a ∉ S → ∃ b ∈ S, F.attack b a = true

/-! ### Boolean deciders -/

/-- Containment as a `Bool`. One notion, used at both scales: `boundedB` is
containment in the carrier, and the maximality scans are containment between two
extensions. Keeping it single means the `List.all` unfolding is done once, in
`subB_iff`, instead of once per site. -/
def subB (S T : List Arg) : Bool := S.all (fun x => memB x T)

/-- Adequacy of `subB`. This is the *only* place `List.all` is unfolded for a
containment check: `boundedB_iff` is literally this lemma, and `maximalB_iff`
quotes it rather than reasoning about `List.all` itself. -/
theorem subB_iff {S T : List Arg} : subB S T = true ↔ ∀ x ∈ S, x ∈ T := by
  simp [subB, List.all_eq_true]

/-- `Bool` decider for `Bounded`. Definitionally `subB S F.args` — carrier
membership is not a second notion of containment, and writing it as one would
mean a second adequacy proof to keep in step. -/
def boundedB (F : AF) (S : List Arg) : Bool := subB S F.args

/-- `Bool` decider for `Grounded.ConflictFree`. The doubly-nested scan is the
same transparent-over-fast trade `Grounded.defendedB` makes. -/
def conflictFreeB (F : AF) (S : List Arg) : Bool :=
  S.all (fun a => S.all (fun b => ! F.attack a b))

/-- `Bool` decider for `Admissible`. -/
def admissibleB (F : AF) (S : List Arg) : Bool :=
  boundedB F S && conflictFreeB F S && S.all (fun a => defendedB F S a)

/-- `Bool` decider for `Complete`. -/
def completeB (F : AF) (S : List Arg) : Bool :=
  admissibleB F S && F.args.all (fun a => (! defendedB F S a) || memB a S)

/-- `Bool` decider for `Stable`. -/
def stableB (F : AF) (S : List Arg) : Bool :=
  boundedB F S && conflictFreeB F S &&
    F.args.all (fun a => memB a S || S.any (fun b => F.attack b a))

/-! ### Decider adequacy -/

/-- Adequacy of `boundedB` — the special case of `subB_iff` at `T := F.args`, so
it is that lemma and nothing more. It is stated separately only because
`admissibleB_iff` and `stableB_iff` need `boundedB F S = true` as a `simp only`
rewrite target; nothing else consumes it. (In particular `exists_candidate_ext`
does *not*: that takes the `Prop` `Bounded`, never the decider.) -/
theorem boundedB_iff {F : AF} {S : List Arg} : boundedB F S = true ↔ Bounded F S :=
  subB_iff

/-- Adequacy of `conflictFreeB`, the one decider whose `Prop` side is imported
from `Lara.Grounded` rather than defined here. -/
theorem conflictFreeB_iff {F : AF} {S : List Arg} :
    conflictFreeB F S = true ↔ ConflictFree F S := by
  simp [conflictFreeB, ConflictFree, List.all_eq_true]

/-- Adequacy of `admissibleB`. Consumed by `preferredB_iff` through
`maximalB_iff`, which needs a decider it can trust on arbitrary candidates. -/
theorem admissibleB_iff {F : AF} {S : List Arg} :
    admissibleB F S = true ↔ Admissible F S := by
  simp only [admissibleB, Admissible, Bool.and_eq_true, List.all_eq_true, boundedB_iff,
    conflictFreeB_iff, and_assoc]

/-- Adequacy of `completeB`. The `!… || …` encoding of the defence-closure
implication is the reason this one is not a `simp` one-liner. -/
theorem completeB_iff {F : AF} {S : List Arg} :
    completeB F S = true ↔ Complete F S := by
  simp only [completeB, Complete, Bool.and_eq_true, admissibleB_iff, List.all_eq_true,
    Bool.or_eq_true, memB_iff]
  constructor
  · rintro ⟨hadm, h⟩
    refine ⟨hadm, fun a ha hd => ?_⟩
    rcases h a ha with hf | hm
    · exact absurd hd (not_eq_true_iff.mp hf)
    · exact hm
  · rintro ⟨hadm, h⟩
    refine ⟨hadm, fun a ha => ?_⟩
    by_cases hd : defendedB F S a = true
    · exact Or.inr (h a ha hd)
    · exact Or.inl (not_eq_true_iff.mpr hd)

/-- Adequacy of `stableB`. The decider tests "in `S`, or attacked by `S`" where
the `Prop` tests "not in `S` implies attacked by `S`"; the two are matched here
once, so `stableSem.sound` stays a rewrite. -/
theorem stableB_iff {F : AF} {S : List Arg} :
    stableB F S = true ↔ Stable F S := by
  simp only [stableB, Stable, Bool.and_eq_true, boundedB_iff, conflictFreeB_iff,
    List.all_eq_true, Bool.or_eq_true, List.any_eq_true, memB_iff, and_assoc]
  refine and_congr_right (fun _ => and_congr_right (fun _ => ?_))
  constructor
  · intro h a ha hna
    rcases h a ha with hm | hb
    · exact absurd hm hna
    · exact hb
  · intro h a ha
    by_cases hm : a ∈ S
    · exact Or.inl hm
    · exact Or.inr (h a ha hm)

/-! ### Monotonicity of defence -/

/-- Defence is monotone in the defending set. `Grounded.step_mono` is the same
argument one level up, stated for `step`; this level is what the two users here
need, because in neither is the enlarged set an iteration stage —
`iter_subset_complete` enlarges to an arbitrary defence-closed set, and
`admissible_cons` enlarges to `a :: S`. -/
theorem defendedB_mono {F : AF} {S T : List Arg} (hST : ∀ x ∈ S, x ∈ T) {a : Arg}
    (ha : defendedB F S a = true) : defendedB F T a = true := by
  rw [defendedB_iff] at ha ⊢
  intro b hb hab
  obtain ⟨c, hc, hcb⟩ := ha b hb hab
  exact ⟨c, hST c hc, hcb⟩

/-! ### Membership extensionality

The gap this section closes. Every maximality (and, for `groundedSem`,
minimality) clause below is stated as `∀ T, …` over *arbitrary* lists, because
that is the mathematically honest statement and it does not depend on how a set
happens to be laid out as a list. A `Bool` decider cannot scan arbitrary lists;
it can only scan `candidates F`, which is finite. Bridging the two needs exactly
two ingredients, proved once here and reused by `preferredSem`, `semiStableSem`
and `groundedSem`:

1. **Congruence** — each predicate depends only on the *member set* of its
   argument, so replacing a list by any other list with the same members
   preserves it.
2. **Canonical representative** — every `Bounded` list has a member-equal
   representative that *is* a sublist of the carrier, namely the carrier filtered
   by membership. So the restricted scan loses nothing.

Together: a `∀ T ∈ candidates F` check transfers to `∀ T` for any predicate that
entails `Bounded`. This is where the carrier bound built into `Admissible` and
`Stable` pays for itself. -/

/-- Defence depends only on the member set of the defending set. -/
theorem defendedB_congr {F : AF} {S S' : List Arg} (h : ∀ x, x ∈ S ↔ x ∈ S') (a : Arg) :
    defendedB F S a = true ↔ defendedB F S' a = true := by
  rw [defendedB_iff, defendedB_iff]
  constructor
  · intro hd b hb hab
    obtain ⟨c, hc, hcb⟩ := hd b hb hab
    exact ⟨c, (h c).mp hc, hcb⟩
  · intro hd b hb hab
    obtain ⟨c, hc, hcb⟩ := hd b hb hab
    exact ⟨c, (h c).mpr hc, hcb⟩

/-- `Bounded` sees only the member set. Base case of the congruence family: every
lemma below rebuilds this one first. -/
theorem bounded_congr {F : AF} {S S' : List Arg} (h : ∀ x, x ∈ S ↔ x ∈ S')
    (hb : Bounded F S) : Bounded F S' := fun a ha => hb a ((h a).mpr ha)

/-- `ConflictFree` sees only the member set. -/
theorem conflictFree_congr {F : AF} {S S' : List Arg} (h : ∀ x, x ∈ S ↔ x ∈ S')
    (hc : ConflictFree F S) : ConflictFree F S' :=
  fun a ha b hb => hc a ((h a).mpr ha) b ((h b).mpr hb)

/-- `Admissible` sees only the member set — the hypothesis `maximalB_iff` demands
of `P` when it is instantiated for `preferredB`. -/
theorem admissible_congr {F : AF} {S S' : List Arg} (h : ∀ x, x ∈ S ↔ x ∈ S')
    (hs : Admissible F S) : Admissible F S' := by
  obtain ⟨hb, hc, hd⟩ := hs
  refine ⟨bounded_congr h hb, conflictFree_congr h hc, fun a ha => ?_⟩
  exact (defendedB_congr h a).mp (hd a ((h a).mpr ha))

/-- `Complete` sees only the member set. Used twice: by `leastCompleteB_iff` for
the minimality scan, and by `semiStableB_iff` through `maximalB_iff`. -/
theorem complete_congr {F : AF} {S S' : List Arg} (h : ∀ x, x ∈ S ↔ x ∈ S')
    (hs : Complete F S) : Complete F S' := by
  obtain ⟨hadm, hcl⟩ := hs
  refine ⟨admissible_congr h hadm, fun a ha hd => ?_⟩
  exact (h a).mp (hcl a ha ((defendedB_congr h a).mpr hd))

/-- `Stable` sees only the member set. Not needed by `stableSem` (stability has no
quantifier over other extensions) but stated for symmetry, and because the
non-collapse comparisons of later tasks will move between representatives. -/
theorem stable_congr {F : AF} {S S' : List Arg} (h : ∀ x, x ∈ S ↔ x ∈ S')
    (hs : Stable F S) : Stable F S' := by
  obtain ⟨hb, hc, hat⟩ := hs
  refine ⟨bounded_congr h hb, conflictFree_congr h hc, fun a ha hna => ?_⟩
  obtain ⟨b, hbS, hba⟩ := hat a ha (fun hc' => hna ((h a).mp hc'))
  exact ⟨b, (h b).mp hbS, hba⟩

/-- The canonical sublist representative of a set: the carrier, filtered by
membership. For `Bounded` inputs this has exactly the same members as the
original but is a genuine `List.Sublist` of `F.args`, hence a member of
`candidates F`. -/
def canonize (F : AF) (T : List Arg) : List Arg := F.args.filter (fun a => memB a T)

/-- Membership in the canonical representative: carrier membership conjoined with
the original. The `Bounded` hypothesis drops the left conjunct — that step is
`exists_candidate_ext`. -/
theorem mem_canonize {F : AF} {T : List Arg} {x : Arg} :
    x ∈ canonize F T ↔ x ∈ F.args ∧ x ∈ T := by
  simp [canonize, List.mem_filter]

/-- The representative really is a candidate, for *any* input: filtering a list
always yields a sublist of it, so no hypothesis on `T` is needed here. -/
theorem canonize_mem_candidates {F : AF} {T : List Arg} : canonize F T ∈ candidates F :=
  mem_candidates.mpr List.filter_sublist

/-- **The bridging lemma.** Every set inside the carrier is member-equal to a
candidate. Combined with the congruence lemmas above, a property checked over
`candidates F` therefore holds of every `Bounded` list, which is what turns the
`Bool` deciders for maximality into adequate deciders for the `∀ T` `Prop`s. -/
theorem exists_candidate_ext {F : AF} {T : List Arg} (h : Bounded F T) :
    ∃ T' ∈ candidates F, ∀ x, x ∈ T' ↔ x ∈ T :=
  ⟨canonize F T, canonize_mem_candidates, fun x => by
    rw [mem_canonize]
    exact ⟨fun h' => h'.2, fun h' => ⟨h x h', h'⟩⟩⟩

/-! ### The bundled interface

`ExtensionSemantics` is the object this module exists to introduce. It is a
*bundle*, not a class: a declarative `spec`, a proof-oriented `enumerate`, and
`sound`, the proof that the second computes the first. Bundling adequacy into the
record is the point — every instance owes the proof at construction time, so no
downstream theorem ever has to re-establish that a particular enumerator is the
semantics it claims to be, and no instance can be added by writing an enumerator
and hoping. A downstream statement quantified over `σ : ExtensionSemantics` is
therefore automatically a statement about *every* adequate semantics. -/

/-- An extension semantics: a declarative condition on sets of arguments,
together with a reference enumerator proved to compute exactly the sublists of
the carrier satisfying it.

`sound` is stated relative to `F.args.Nodup`, and `enumerate_ext` immediately
below is what that hypothesis is for. The full argument — why the field stays
even though no instance's `sound` proof consumes it — is in the module header's
*Representation* paragraph, and is deliberately written down in that one place
only, so the two cannot drift apart. -/
structure ExtensionSemantics where
  /-- the declarative condition an extension must satisfy -/
  spec : AF → List Arg → Prop
  /-- the proof-oriented reference enumerator (exponential — see the header) -/
  enumerate : AF → List (List Arg)
  /-- adequacy: the enumerator lists exactly the carrier sublists meeting `spec` -/
  sound : ∀ F, F.args.Nodup → ∀ S, S ∈ enumerate F ↔ (S.Sublist F.args ∧ spec F S)

/-- **The payoff of bundling adequacy.** For *any* extension semantics — the five
below, or any instance written later — no two entries of `enumerate F` denote the
same set of arguments over a duplicate-free carrier. Nothing about the particular
enumerator is used: `sound` alone forces every entry to be a carrier sublist, and
`candidates_ext` then forces same-members to mean equal. An instance therefore
gets representative uniqueness by constructing the record, not by proving anything
extra. This is what the `Nodup` field in `sound` is for. -/
theorem enumerate_ext (sem : ExtensionSemantics) {F : AF} (h : F.args.Nodup)
    {S T : List Arg} (hS : S ∈ sem.enumerate F) (hT : T ∈ sem.enumerate F)
    (hmem : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  candidates_ext h (mem_candidates.mpr ((sem.sound F h S).mp hS).1)
    (mem_candidates.mpr ((sem.sound F h T).mp hT).1) hmem

/-- Every instance below enumerates by filtering `candidates`, so adequacy always
reduces to the corresponding decider `iff`. Factoring that step out keeps the
five `sound` proofs to one line each plus whatever the decider genuinely needs. -/
theorem mem_filter_candidates {F : AF} {p : List Arg → Bool} {S : List Arg} :
    S ∈ (candidates F).filter p ↔ (S.Sublist F.args ∧ p S = true) := by
  rw [List.mem_filter, mem_candidates]

/-- The **complete** semantics. -/
def completeSem : ExtensionSemantics where
  spec := Complete
  enumerate := fun F => (candidates F).filter (completeB F)
  sound := fun _ _ _ => by rw [mem_filter_candidates, completeB_iff]

/-- The **stable** semantics. Unlike the other four this one can be *empty*: the
bare three-cycle `0→1→2→0` has no stable extension.

Read that precisely. Emptiness is a property of the whole framework, **not** of
containing an odd cycle: adding a fourth argument that attacks all three of
`0,1,2` gives a framework which still contains that cycle and whose stable
extensions are `[[3]]`. Only the bare cycle collapses.

That possible emptiness is the non-collapse content the milestone is after, and
it is exactly what a `grounded`-only development cannot express. Both halves of
the paragraph above are theorems in `Lara.Examples.Semantics`:
`stableSem_enumerate_threeCycle` for the bare cycle, and
`stableSem_enumerate_threeCycleAttacked` for the four-argument variant, which
states the three cycle edges and the extension list together so the two cannot
drift apart. -/
def stableSem : ExtensionSemantics where
  spec := Stable
  enumerate := fun F => (candidates F).filter (stableB F)
  sound := fun _ _ _ => by rw [mem_filter_candidates, stableB_iff]

/-! ### The grounded semantics, in this vocabulary

`groundedSem.spec` is deliberately *not* `S = Grounded.grounded F`. That would
make the instance a tautology and defeat the purpose: the point of the interface
is that each semantics is picked out by a first-order condition on `F` and `S`,
in the same shape as the other four, so that a theorem quantified over
`ExtensionSemantics` says something about the grounded case too. The condition
used is the standard characterization — the *least complete extension* under set
inclusion.

`grounded_complete` and `grounded_least` connect that characterization back to
`Grounded.grounded`, so the spec is demonstrably inhabited by the evaluator the
runtime actually uses. -/

/-- Being *the* grounded extension, stated without mentioning the evaluator:
complete, and contained in every complete extension. -/
def LeastComplete (F : AF) (S : List Arg) : Prop :=
  Complete F S ∧ ∀ T, Complete F T → ∀ x ∈ S, x ∈ T

/-- Every stage of the grounded iteration is contained in any defence-closed set.
The induction is on the stage: the base case is vacuous, and the successor case
lands in `T` because `T` absorbs everything it defends and defence is monotone. -/
theorem iter_subset_complete {F : AF} {T : List Arg}
    (hT : ∀ a ∈ F.args, defendedB F T a = true → a ∈ T) :
    ∀ k, ∀ x ∈ iter F k, x ∈ T
  | 0, x, hx => by simp [iter] at hx
  | k + 1, x, hx => by
      rw [iter, mem_step] at hx
      exact hT x hx.1 (defendedB_mono (iter_subset_complete hT k) hx.2)

/-- The executable grounded extension is a complete extension. Admissibility is
`iter_subset_args` plus `grounded_conflictFree` plus the forward half of
`grounded_fixpoint`; defence closure is the backward half. -/
theorem grounded_complete {F : AF} : Complete F (grounded F) := by
  refine ⟨⟨fun a ha => iter_subset_args F.args.length a ha, grounded_conflictFree,
    fun a ha => ?_⟩, fun a ha hd => ?_⟩
  · exact (mem_step.mp ((grounded_fixpoint a).mpr ha)).2
  · exact (grounded_fixpoint a).mp (mem_step.mpr ⟨ha, hd⟩)

/-- The executable grounded extension is the least complete extension. -/
theorem grounded_least {F : AF} {T : List Arg} (hT : Complete F T) :
    ∀ x ∈ grounded F, x ∈ T :=
  iter_subset_complete hT.2 F.args.length

/-- `Grounded.grounded` satisfies the declarative grounded condition. This is
what makes `groundedSem` non-vacuous: the evaluator the runtime calls is a
witness of the spec the interface states. -/
theorem grounded_leastComplete {F : AF} : LeastComplete F (grounded F) :=
  ⟨grounded_complete, fun _ hT => grounded_least hT⟩

/-- `Bool` decider for `LeastComplete`. The minimality clause can only scan
`candidates F`; `exists_candidate_ext` and `complete_congr` are what make the
restricted scan adequate for the unrestricted `∀ T`. -/
def leastCompleteB (F : AF) (S : List Arg) : Bool :=
  completeB F S &&
    (candidates F).all (fun T => (! completeB F T) || S.all (fun x => memB x T))

/-- Adequacy of `leastCompleteB`. This is the minimality mirror of
`maximalB_iff`, written out rather than abstracted: it is the only minimality
clause in the module, so factoring it would buy nothing. -/
theorem leastCompleteB_iff {F : AF} {S : List Arg} :
    leastCompleteB F S = true ↔ LeastComplete F S := by
  rw [leastCompleteB, Bool.and_eq_true, completeB_iff]
  constructor
  · rintro ⟨hS, hall⟩
    refine ⟨hS, fun T hT x hx => ?_⟩
    obtain ⟨T', hT'c, hT'e⟩ := exists_candidate_ext hT.1.1
    have h := List.all_eq_true.mp hall T' hT'c
    rw [Bool.or_eq_true] at h
    rcases h with hneg | hsub
    · exact absurd (completeB_iff.mpr (complete_congr (fun y => (hT'e y).symm) hT))
        (not_eq_true_iff.mp hneg)
    · exact (hT'e x).mp (memB_iff.mp (List.all_eq_true.mp hsub x hx))
  · rintro ⟨hS, hmin⟩
    refine ⟨hS, List.all_eq_true.mpr (fun T _ => ?_)⟩
    rw [Bool.or_eq_true]
    by_cases hc : completeB F T = true
    · exact Or.inr (List.all_eq_true.mpr (fun x hx =>
        memB_iff.mpr (hmin T (completeB_iff.mp hc) x hx)))
    · exact Or.inl (not_eq_true_iff.mpr hc)

/-- The **grounded** semantics as an instance of the interface. Its `spec` is the
least-complete characterization, not a reference to `Grounded.grounded`; the two
are tied together by `grounded_leastComplete`. -/
def groundedSem : ExtensionSemantics where
  spec := LeastComplete
  enumerate := fun F => (candidates F).filter (leastCompleteB F)
  sound := fun _ _ _ => by rw [mem_filter_candidates, leastCompleteB_iff]

/-! ### Maximality, checked over a finite scan

Both `Preferred` and `SemiStable` are "maximal among the sets satisfying `P`",
differing only in *what* is compared: `Preferred` compares the extensions
themselves, `SemiStable` compares their ranges. `maximalB_iff` is that shape
proved once, parameterized by the comparison map `f`, so neither instance repeats
the `exists_candidate_ext` argument.

**Maximality is mutual containment, not list equality.** `∀ T, P T → S ⊆ T →
T ⊆ S` says exactly "nothing satisfying `P` strictly extends `S`" without
committing to a list representation, which matters because `AF.args` is not
`Nodup`-constrained. Stating it as `T = S` would silently make the statement
depend on element order and duplication. This phrasing is sound only because the
carrier bound sits inside `P` — without it, `T` could range over junk outside
`F.args` (see the predicates section). -/

/-- **The maximality bridge.** A `⊆`-maximality clause quantified over arbitrary
lists is equivalent to the same clause scanned over `candidates F`, provided the
predicate entails `Bounded`, respects member-set equality, and the compared map
`f` does too. Instantiated at `f := id` for `preferredB` and at
`f := reach F` (the range map) for `semiStableB`. -/
theorem maximalB_iff {F : AF} {P : List Arg → Prop} {pB : List Arg → Bool}
    {f : List Arg → List Arg} {S : List Arg}
    (hiff : ∀ T, pB T = true ↔ P T)
    (hbdd : ∀ T, P T → Bounded F T)
    (hcongr : ∀ T T', (∀ x, x ∈ T ↔ x ∈ T') → P T → P T')
    (hfcongr : ∀ T T', (∀ x, x ∈ T ↔ x ∈ T') → ∀ x, x ∈ f T ↔ x ∈ f T') :
    ((candidates F).all
        (fun T => (! (pB T && subB (f S) (f T))) || subB (f T) (f S)) = true)
      ↔ (∀ T, P T → (∀ x ∈ f S, x ∈ f T) → (∀ x ∈ f T, x ∈ f S)) := by
  constructor
  · intro hall T hT hsub x hx
    obtain ⟨T', hT'c, hT'e⟩ := exists_candidate_ext (hbdd T hT)
    have hPT' : P T' := hcongr T T' (fun y => (hT'e y).symm) hT
    have hfe : ∀ y, y ∈ f T' ↔ y ∈ f T := hfcongr T' T hT'e
    have h := List.all_eq_true.mp hall T' hT'c
    rw [Bool.or_eq_true] at h
    rcases h with hneg | hsup
    · exact absurd ⟨(hiff T').mpr hPT',
        subB_iff.mpr (fun y hy => (hfe y).mpr (hsub y hy))⟩ (not_and_eq_true.mp hneg)
    · exact subB_iff.mp hsup x ((hfe x).mpr hx)
  · intro hprop
    refine List.all_eq_true.mpr (fun T _ => ?_)
    rw [Bool.or_eq_true]
    by_cases hc : pB T = true ∧ subB (f S) (f T) = true
    · exact Or.inr (subB_iff.mpr
        (hprop T ((hiff T).mp hc.1) (subB_iff.mp hc.2)))
    · exact Or.inl (not_and_eq_true.mpr hc)

/-! ### The preferred semantics -/

/-- `Preferred` is the **textbook** definition: admissible and `⊆`-maximal among
admissible sets. That every preferred extension is also complete is proved below
(`preferred_complete`), not assumed. Defining `Preferred := Complete ∧ maximal`
would bake that theorem into the definition and leave a paper transcribing a
non-standard shape. -/
def Preferred (F : AF) (S : List Arg) : Prop :=
  Admissible F S ∧ ∀ T, Admissible F T → (∀ x ∈ S, x ∈ T) → (∀ x ∈ T, x ∈ S)

/-- `Bool` decider for `Preferred`. -/
def preferredB (F : AF) (S : List Arg) : Bool :=
  admissibleB F S &&
    (candidates F).all (fun T => (! (admissibleB F T && subB S T)) || subB T S)

/-- Adequacy of `preferredB`: the first instantiation of `maximalB_iff`, at the
identity comparison map. -/
theorem preferredB_iff {F : AF} {S : List Arg} :
    preferredB F S = true ↔ Preferred F S := by
  unfold preferredB Preferred
  rw [Bool.and_eq_true, admissibleB_iff]
  refine and_congr_right (fun _ => ?_)
  exact maximalB_iff (F := F) (P := Admissible F) (pB := admissibleB F) (f := id)
    (fun _ => admissibleB_iff) (fun _ h => h.1)
    (fun _ _ h hA => admissible_congr h hA) (fun _ _ h => h)

/-- The **preferred** semantics, and the structural contrast with `stableSem`: a
finite framework always has at least one preferred extension, because the empty
set is admissible and the finite candidate list must therefore contain a
`⊆`-maximal admissible member.

That non-emptiness is **stated, not proved here** — unlike everything else in
this section it carries no theorem. The argument needs a maximal-element
principle over `candidates F`, which in turn needs `Nodup` and a
subset-implies-shorter fact that core Lean does not supply; nothing downstream of
this module relies on it, so it was not worth the machinery.
`preferred_exists_where_stable_does_not` is the concrete instance on the bare
three-cycle, and establishes nothing about the general case. -/
def preferredSem : ExtensionSemantics where
  spec := Preferred
  enumerate := fun F => (candidates F).filter (preferredB F)
  sound := fun _ _ _ => by rw [mem_filter_candidates, preferredB_iff]

/-! ### Dung's fundamental lemma, and preferred ⇒ complete -/

/-- **Dung's fundamental lemma.** An admissible set that defends a carrier
argument stays admissible when that argument is added. The three conflict cases
all reduce to the same move: an offending edge forces two members of `S` to
attack each other, contradicting conflict-freedom of `S`. -/
theorem admissible_cons {F : AF} {S : List Arg} {a : Arg} (hS : Admissible F S)
    (ha : a ∈ F.args) (hd : defendedB F S a = true) : Admissible F (a :: S) := by
  obtain ⟨hbnd, hcf, hdef⟩ := hS
  -- No member of `S` attacks `a`: defence of `a` would supply a counter-attacker inside `S`.
  have hin : ∀ b ∈ S, F.attack b a ≠ true := by
    intro b hb hba
    obtain ⟨c, hc, hcb⟩ := defendedB_iff.mp hd b (hbnd b hb) hba
    exact hcf c hc b hb hcb
  -- Nor does `a` attack any member of `S`: that member's own defence supplies one.
  have hout : ∀ b ∈ S, F.attack a b ≠ true := by
    intro b hb hab
    obtain ⟨c, hc, hca⟩ := defendedB_iff.mp (hdef b hb) a ha hab
    exact hin c hc hca
  have hself : F.attack a a ≠ true := by
    intro haa
    obtain ⟨c, hc, hca⟩ := defendedB_iff.mp hd a ha haa
    exact hin c hc hca
  have hmono : ∀ x ∈ S, x ∈ a :: S := fun x hx => List.mem_cons_of_mem a hx
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with hxa | hxS
    · subst hxa; exact ha
    · exact hbnd x hxS
  · intro x hx y hy
    rcases List.mem_cons.mp hx with hxa | hxS
    · subst hxa
      rcases List.mem_cons.mp hy with hya | hyS
      · subst hya; exact hself
      · exact hout y hyS
    · rcases List.mem_cons.mp hy with hya | hyS
      · subst hya; exact hin x hxS
      · exact hcf x hxS y hyS
  · intro x hx
    rcases List.mem_cons.mp hx with hxa | hxS
    · subst hxa; exact defendedB_mono hmono hd
    · exact defendedB_mono hmono (hdef x hxS)

/-- Every preferred extension is complete. Immediate from the fundamental lemma:
a defended carrier argument outside `S` would extend `S` to a strictly larger
admissible set, contradicting maximality. Stated as a theorem precisely because
`Preferred` was defined the textbook way. -/
theorem preferred_complete {F : AF} {S : List Arg} (h : Preferred F S) : Complete F S := by
  refine ⟨h.1, fun a ha hd => ?_⟩
  exact h.2 (a :: S) (admissible_cons h.1 ha hd)
    (fun x hx => List.mem_cons_of_mem a hx) a List.mem_cons_self

/-! ### The semi-stable semantics

Semi-stable is the semantics that repairs `stableSem`'s defect: on a finite
framework it always exists, yet it coincides with stable whenever a stable
extension is available. (Neither of those two facts is proved in this module;
they are stated to say what the semantics is *for*.) It is defined by maximizing
not the extension but its **range** — the extension together with everything the
extension attacks — among complete extensions. So it needs one more piece of
vocabulary than the others, and one more congruence lemma, which is why it is
stated last.

Vocabulary, matching Dung and Caminada: `attacked F S` is `S⁺`, and the *range*
of `S` is `S ∪ S⁺`, which is `reach F S` here. -/

/-- `S⁺`: the carrier arguments that `S` attacks. Not the range — the range is
`S ∪ S⁺`, which is `reach`. -/
def attacked (F : AF) (S : List Arg) : List Arg :=
  F.args.filter (fun a => S.any (fun b => F.attack b a))

/-- Membership in `S⁺`, unfolded once so `reach_congr` never has to touch
`List.filter` or `List.any`. -/
theorem mem_attacked {F : AF} {S : List Arg} {a : Arg} :
    a ∈ attacked F S ↔ a ∈ F.args ∧ ∃ b ∈ S, F.attack b a = true := by
  simp [attacked, List.mem_filter, List.any_eq_true]

/-- **The range of `S`** in Dung's sense: `S ∪ S⁺`, the extension plus everything
it attacks. Semi-stable maximizes this rather than `S` itself, so that an
extension leaving fewer arguments undecided wins even when it is not larger.

Named `reach` rather than `range` only to avoid colliding with core `List.range`,
which this repo already uses (`Lara.Compile.toAF`); every docstring and paper
sentence about "the range of `S`" means this declaration. -/
def reach (F : AF) (S : List Arg) : List Arg := S ++ attacked F S

/-- The range of `S` is `S` together with `S⁺`; `++` is only a way to write that
union as a list, and this lemma is the only place it is read. -/
theorem mem_reach {F : AF} {S : List Arg} {x : Arg} :
    x ∈ reach F S ↔ x ∈ S ∨ x ∈ attacked F S := List.mem_append

/-- The range depends only on the member set of the extension — the fourth
hypothesis `maximalB_iff` needs for the semi-stable instantiation. -/
theorem reach_congr {F : AF} {S S' : List Arg} (h : ∀ x, x ∈ S ↔ x ∈ S') :
    ∀ x, x ∈ reach F S ↔ x ∈ reach F S' := by
  intro x
  rw [mem_reach, mem_reach, mem_attacked, mem_attacked]
  constructor
  · rintro (hx | ⟨hc, b, hb, hba⟩)
    · exact Or.inl ((h x).mp hx)
    · exact Or.inr ⟨hc, b, (h b).mp hb, hba⟩
  · rintro (hx | ⟨hc, b, hb, hba⟩)
    · exact Or.inl ((h x).mpr hx)
    · exact Or.inr ⟨hc, b, (h b).mpr hb, hba⟩

/-- `S` is **semi-stable**: complete, with `⊆`-maximal range (`reach`) among
complete extensions. Maximality is again mutual containment, for the same
representation-independence reason as `Preferred`. -/
def SemiStable (F : AF) (S : List Arg) : Prop :=
  Complete F S ∧
    ∀ T, Complete F T → (∀ x ∈ reach F S, x ∈ reach F T) → (∀ x ∈ reach F T, x ∈ reach F S)

/-- `Bool` decider for `SemiStable`. -/
def semiStableB (F : AF) (S : List Arg) : Bool :=
  completeB F S &&
    (candidates F).all (fun T =>
      (! (completeB F T && subB (reach F S) (reach F T))) || subB (reach F T) (reach F S))

/-- Adequacy of `semiStableB`: the second instantiation of `maximalB_iff`, at the
range map `reach`. That the same lemma serves both is the reason
`maximalB_iff` is parameterized by `f` rather than written twice. -/
theorem semiStableB_iff {F : AF} {S : List Arg} :
    semiStableB F S = true ↔ SemiStable F S := by
  unfold semiStableB SemiStable
  rw [Bool.and_eq_true, completeB_iff]
  refine and_congr_right (fun _ => ?_)
  exact maximalB_iff (F := F) (P := Complete F) (pB := completeB F) (f := reach F)
    (fun _ => completeB_iff) (fun _ h => h.1.1)
    (fun _ _ h hC => complete_congr h hC) (fun _ _ h => reach_congr h)

/-- The **semi-stable** semantics. -/
def semiStableSem : ExtensionSemantics where
  spec := SemiStable
  enumerate := fun F => (candidates F).filter (semiStableB F)
  sound := fun _ _ _ => by rw [mem_filter_candidates, semiStableB_iff]

/-! ### Grounded is the singleton instance

**Why this section exists: it is what makes M2a additive.** Everything proved
before this milestone about claim status reads `Grounded.grounded` — result 6,
`Compile.srcStatus_iff_checked`, `Invariants.status_compileUnit`. Introducing
`ExtensionSemantics` would reopen all of it if the grounded case turned out to
sit awkwardly inside the new interface, or to denote something other than what
the evaluator computes. It does not: `groundedSem` enumerates exactly one
extension, and that extension has exactly the members of `Grounded.grounded F`
(`groundedSem_enumerate`). The generic interface therefore *extends* the
development rather than reinterpreting it.

Read the scope of that claim precisely. This section does **not** re-prove any
downstream theorem, and it does not lift any of them to arbitrary semantics: the
`grounded`-indexed statements downstream stay exactly as strong and exactly as
narrow as they were. What is established here is narrower and is only about this
module's own interface — that the grounded semantics is the *singleton* instance
of `ExtensionSemantics`, with its unique extension member-equal to the evaluator's
output. The downstream theorems remain valid because their subject, `grounded F`,
was not touched by this milestone; this section is the evidence that the new
interface agrees with that subject rather than a re-derivation of the theorems
about it. -/

/-- Two least-complete extensions have the same members. Immediate — each is
complete, so each minimality clause applies to the other — but worth naming: it
is the entire reason `groundedSem` has a *singleton* enumeration, and it is what
`groundedSem_enumerate` feeds to `enumerate_ext`. Stated at the membership level
because `LeastComplete` says nothing about list layout; the upgrade to list
equality needs `Nodup` and happens later. -/
theorem leastComplete_unique {F : AF} {S T : List Arg}
    (hS : LeastComplete F S) (hT : LeastComplete F T) : ∀ x, x ∈ S ↔ x ∈ T :=
  fun x => ⟨fun hx => hS.2 T hT.1 x hx, fun hx => hT.2 S hS.1 x hx⟩

/-- `LeastComplete` sees only the member set — the last member of the congruence
family that lives in the *Membership extensionality* section, stated down here
instead because `LeastComplete` is not defined until well after it, and because
it is needed only once: to transport `grounded_leastComplete` onto the canonical
representative `canonize F (grounded F)`. -/
theorem leastComplete_congr {F : AF} {S S' : List Arg} (h : ∀ x, x ∈ S ↔ x ∈ S')
    (hs : LeastComplete F S) : LeastComplete F S' :=
  ⟨complete_congr h hs.1, fun T hT x hx => hs.2 T hT x ((h x).mpr hx)⟩

/-- The canonical representative of the grounded extension has exactly the
members of the grounded extension — the carrier conjunct that `mem_canonize`
leaves behind is discharged by `Grounded.iter_subset_args`, since every stage of
the iteration lies inside `F.args`. This is the regression evidence that the
element `groundedSem_enumerate` produces is not merely *some* least-complete set
but the evaluator's own output up to layout. -/
theorem mem_canonize_grounded {F : AF} {x : Arg} :
    x ∈ canonize F (grounded F) ↔ x ∈ grounded F := by
  rw [mem_canonize]
  exact ⟨fun h => h.2, fun h => ⟨iter_subset_args F.args.length x h, h⟩⟩

/-- A duplicate-free list all of whose members are equal to a given member *is*
the one-element list holding it. Core Lean supplies no such lemma at this
toolchain, and it is what turns "the enumeration contains the grounded
representative, and any two entries coincide" into an equation about the whole
list — the singleton-ness, which is the content of `groundedSem_enumerate`. It is
stated at `List Arg`-elements rather than polymorphically because that is the only
instantiation the module has. -/
theorem eq_singleton_of_nodup_of_unique {l : List (List Arg)} {a : List Arg}
    (hnd : l.Nodup) (ha : a ∈ l) (huniq : ∀ x ∈ l, x = a) : l = [a] := by
  cases l with
  | nil => nomatch ha
  | cons b rest =>
      have hba : b = a := huniq b List.mem_cons_self
      have hb : b ∉ rest := (List.nodup_cons.mp hnd).1
      have hrest : rest = [] := by
        refine List.eq_nil_iff_forall_not_mem.mpr (fun c hc => hb ?_)
        have hca : c = a := huniq c (List.mem_cons_of_mem b hc)
        rw [hba, ← hca]
        exact hc
      rw [hba, hrest]

/-- **The grounded semantics is the singleton instance.** Its enumeration is a
one-element list, and that element is the canonical carrier-sublist
representative of `Grounded.grounded F`; with `mem_canonize_grounded` the two
denote the same set of arguments.

Both halves are the point. Existence is `grounded_leastComplete` transported onto
the representative; uniqueness is `leastComplete_unique` (any two entries have the
same members) upgraded to list equality by `enumerate_ext`. `F.args.Nodup` does
real work at exactly two points: `enumerate_ext` needs it for representative
uniqueness, and `candidates_nodup` supplies the duplicate-freedom that
`eq_singleton_of_nodup_of_unique` needs to rule out a repeated entry. It appears
a third time, in `groundedSem.sound`, which binds it and discards it — see the
header. A statement
that merely placed `grounded F` *in* the enumeration would leave open that some
other set also satisfies `LeastComplete`, and that is exactly what must be
excluded for the interface to agree with the `grounded`-indexed development
downstream. -/
theorem groundedSem_enumerate {F : AF} (h : F.args.Nodup) :
    groundedSem.enumerate F = [canonize F (grounded F)] := by
  have hspec : LeastComplete F (canonize F (grounded F)) :=
    leastComplete_congr (fun _ => mem_canonize_grounded.symm) grounded_leastComplete
  have hmem : canonize F (grounded F) ∈ groundedSem.enumerate F :=
    (groundedSem.sound F h _).mpr ⟨mem_candidates.mp canonize_mem_candidates, hspec⟩
  have hnd : (groundedSem.enumerate F).Nodup := (candidates_nodup h).filter _
  refine eq_singleton_of_nodup_of_unique hnd hmem (fun S hS => ?_)
  exact enumerate_ext groundedSem h hS hmem
    (leastComplete_unique ((groundedSem.sound F h S).mp hS).2 hspec)

/-- The form the claim-level observation layer consumes: *there is* an extension,
the enumeration is exactly it, and its members are the grounded ones. A
semantics-parametric status function folds over `groundedSem.enumerate F`; it can
rewrite by the first component to reduce that fold to a single extension, then use
the second to replace the extension by `Grounded.grounded F` wherever membership is
tested. That is the shape a proof that semantics-parametric observation collapses
to `Grounded.statusC` on the grounded instance needs. Packaged existentially so
the consumer never mentions `canonize`, which is an artifact of the sublist
representation and not part of what the corollary means. -/
theorem groundedSem_singleton {F : AF} (h : F.args.Nodup) :
    ∃ E, groundedSem.enumerate F = [E] ∧ ∀ x, x ∈ E ↔ x ∈ grounded F :=
  ⟨canonize F (grounded F), groundedSem_enumerate h, fun _ => mem_canonize_grounded⟩

/-! ### Semantics-parametric claim observation

The layer this module was built for. `Grounded.statusC` reads one extension —
`Grounded.grounded F` — and reports a four-state status. Once a framework can be
read under five semantics, "the status of a claim" needs a definition that says
*which* aggregation over *which* extension set it is, and needs to survive the
case the grounded reading cannot express: a semantics with no extension at all.

Three things are separated here on purpose.

**Per-argument acceptance (`profile`) carries four bits, not two.** Skeptical and
credulous acceptance are the familiar two; skeptical and credulous *rejection* are
two more, and they are not the negations of the first two. Under `groundedSem` on
the two-cycle `0 ↔ 1` the single extension is empty, so argument `0` is accepted
by no extension and attacked by no extension — all four bits are `false`
(`profile_groundedSem_twoCycle`; the sole extension of that framework is `[]` by
`groundedSem_enumerate_twoCycle`, and an empty extension neither contains nor
attacks anything, which is why). Deriving `out*` from `in*` would turn that
undecided argument into a rejected one, which is exactly the fabricated verdict
this module exists to avoid.

**Claim observation (`observe`) is not computed from `profile`.** See `observe`'s
docstring: the aggregation adopted is `∀E ∃a` (every extension accepts *some*
support argument), which per-argument data cannot reconstruct.

**"No extension" is a constructor of the answer type, not a footnote.** See
`ClaimObservation`.

Scope, stated so it is not overread: nothing here lifts a downstream
`grounded`-indexed theorem to an arbitrary semantics. The only bridge proved is
`observe_grounded`, which says the new aggregation *agrees with* `Grounded.statusC`
on the grounded instance. -/

/-- The four-bit acceptance record of a single argument under a semantics:
skeptical and credulous acceptance, and skeptical and credulous rejection.

Four fields rather than two because rejection is not the complement of
acceptance — see the section note for the two-cycle witness under `groundedSem`,
where an argument has all four bits `false` (`profile_groundedSem_twoCycle`). A
two-field record forces the reader of `¬ inSome` to guess between "attacked" and
"undecided", and any consumer that
guesses "attacked" reports a defeat the semantics never asserted. -/
structure AcceptanceProfile where
  /-- accepted in *every* extension — skeptical acceptance -/
  inAll   : Bool
  /-- accepted in *some* extension — credulous acceptance -/
  inSome  : Bool
  /-- attacked by *every* extension — skeptical rejection -/
  outAll  : Bool
  /-- attacked by *some* extension — credulous rejection -/
  outSome : Bool
deriving DecidableEq, Repr

/-- `a` is attacked by some member of `S`. Deliberately **not** `memB a (attacked
F S)`: `attacked` intersects with the carrier (`mem_attacked` carries an
`a ∈ F.args` conjunct), whereas `Grounded.labelC` bounds the *attacker* to the
carrier and leaves the target unbounded. Reusing `attacked` here would make a
support argument outside `F.args` unattackable by definition, while `labelC` can
still label it `out`, and `observe_grounded` would then be false. -/
def attackedByB (F : AF) (S : List Arg) (a : Arg) : Bool :=
  S.any (fun b => F.attack b a)

/-- **The exact relationship between the two "attacked by" notions**, so that the
distinction `attackedByB`'s docstring argues for is a checked theorem rather than
prose: `attacked` is `attackedByB` intersected with the carrier. A later reader who
reaches for one where the other is meant is reintroducing the `a ∈ F.args`
conjunct, which is precisely what would break `observe_grounded`. -/
theorem mem_attacked_iff {F : AF} {S : List Arg} {a : Arg} :
    a ∈ attacked F S ↔ a ∈ F.args ∧ attackedByB F S a = true := by
  simp [mem_attacked, attackedByB, List.any_eq_true]

/-- `attackedByB` sees only the member set of the attacking extension. The
counterpart of the *Membership extensionality* family for the new predicate, and
the step that lets `observe_grounded` replace the enumerated extension by
`Grounded.grounded F` under an attack test. -/
theorem attackedByB_congr {F : AF} {S S' : List Arg} (h : ∀ x, x ∈ S ↔ x ∈ S')
    (a : Arg) : attackedByB F S a = true ↔ attackedByB F S' a = true := by
  unfold attackedByB
  rw [List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨b, hb, hba⟩ => ⟨b, (h b).mp hb, hba⟩,
         fun ⟨b, hb, hba⟩ => ⟨b, (h b).mpr hb, hba⟩⟩

/-- The same congruence as a `Bool` equation. `attackedByB_congr` is the shape a
proof consumes with `.mp` / `.mpr`; this is the shape `rw` and `simp` want, since
they rewrite terms rather than transport propositions. Both are kept because
converting at each site costs a `Bool.eq_iff_iff` that reads as noise. -/
theorem attackedByB_congr_eq {F : AF} {S S' : List Arg} (h : ∀ x, x ∈ S ↔ x ∈ S')
    (a : Arg) : attackedByB F S a = attackedByB F S' a :=
  Bool.eq_iff_iff.mpr (attackedByB_congr h a)

/-- The acceptance profile of one argument under one semantics, folded over the
enumeration. This is the *argument-level* reading; the claim-level reading is
`observe`, and the two are deliberately not defined through each other. -/
def profile (sem : ExtensionSemantics) (F : AF) (a : Arg) : AcceptanceProfile where
  inAll   := (sem.enumerate F).all (fun E => memB a E)
  inSome  := (sem.enumerate F).any (fun E => memB a E)
  outAll  := (sem.enumerate F).all (fun E => attackedByB F E a)
  outSome := (sem.enumerate F).any (fun E => attackedByB F E a)

/-- **The single-extension collapse.** Under the grounded semantics the skeptical
and credulous bits coincide, both for acceptance and for rejection, because
`groundedSem_singleton` makes the enumeration a one-element list and `all`/`any`
agree there. This is the precise sense in which the pre-M2a development could not
tell skeptical from credulous reasoning: the distinction is invisible on the only
semantics it had. It is *not* a statement that the four bits are redundant in
general: `profile_preferredSem_twoCycle` separates them on the two-cycle `0 ↔ 1`,
where `preferredSem_enumerate_twoCycle` lists two extensions. -/
theorem profile_grounded {F : AF} (h : F.args.Nodup) (a : Arg) :
    (profile groundedSem F a).inAll = (profile groundedSem F a).inSome ∧
      (profile groundedSem F a).outAll = (profile groundedSem F a).outSome := by
  obtain ⟨E, hE, _⟩ := groundedSem_singleton h
  constructor <;> · simp [profile, hE]

/-- What a semantics reports about a claim.

`noExtension` is a constructor rather than a side condition because the empty
enumeration is a real case — `stableSem` on the bare three-cycle has no extension
(`stableSem_enumerate_threeCycle`), and `observe_stableSem_threeCycle` shows the
constructor is actually reached, with `observe_stableSem_threeCycle_ne_justified`
and `observe_stableSem_threeCycle_ne_defeated` ruling out the two `Status` answers
it could otherwise have been confused with. On an empty enumeration every
`List.all` guard is vacuously `true`, so an aggregation that only produced a
`Status` would report the same claim as both skeptically justified and
skeptically defeated. Making the
empty case a distinct constructor means "this semantics says nothing here" is
representable, and `observe_noExtension_iff` makes it checkable. -/
inductive ClaimObservation where
  /-- the semantics has no extension on this framework, so it reports nothing -/
  | noExtension
  /-- the skeptical reading: total whenever at least one extension exists, plus
  the `gap` case, which is reported without consulting the semantics at all.
  Note this arm does *not* imply an extension exists — see
  `enumerate_ne_nil_of_observed_ne_gap`, which needs `s ≠ gap` for exactly that
  reason. -/
  | observed (s : Status)
deriving DecidableEq, Repr

/-- Extension `E` accepts claim `c`: *some* complete support argument of `c` is in
`E`. The per-extension event that `observe`'s `justified` arm quantifies over.
Takes no `AF`, unlike `claimDefeatedB`: acceptance is a pure membership test,
while defeat has to consult the attack relation. -/
def claimAcceptedB (E : List Arg) (c : Grounded.Claim) : Bool :=
  c.support.any (fun a => memB a E)

/-- Extension `E` defeats claim `c`: *every* complete support argument of `c` is
attacked by `E`. Note the quantifier is the opposite of `claimAcceptedB`'s, which
is why the two are not each other's negation and why `observe` tests them
independently rather than branching once. -/
def claimDefeatedB (F : AF) (E : List Arg) (c : Grounded.Claim) : Bool :=
  c.support.all (fun a => attackedByB F E a)

/-- **The support-level vacuity, half one.** On empty support the defeat guard is
unconditionally `true`, for *every* extension and every framework — `List.all`
over `[]`.

Together with `claimAcceptedB_of_nil` this pair *is* the second fabrication
hazard, stated rather than described, because the paragraph describing it has
twice been written wrongly. Note the asymmetry, which is what makes the hazard
worth a theorem: acceptance goes vacuously `false` and defeat vacuously `true`,
so an unsupported claim that reached the `all`-guards would not be reported
ambiguously — it would be reported specifically `defeated`, the worst verdict
available, on a framework whose extensions are perfectly well behaved. `observe`
never gets there: `observe_gap` fires first. -/
theorem claimDefeatedB_of_nil {F : AF} {E : List Arg} {c : Grounded.Claim}
    (hs : c.support = []) : claimDefeatedB F E c = true := by
  unfold claimDefeatedB
  rw [hs]
  rfl

/-- **The support-level vacuity, half two.** On empty support the acceptance guard
is unconditionally `false`. See `claimDefeatedB_of_nil` for why the pair is stated
as theorems rather than left to the prose. -/
theorem claimAcceptedB_of_nil {E : List Arg} {c : Grounded.Claim}
    (hs : c.support = []) : claimAcceptedB E c = false := by
  unfold claimAcceptedB
  rw [hs]
  rfl

/-- **The semantics-parametric claim observation.**

Two design decisions are frozen here.

*Claim-level, not argument-level.* There are two inequivalent generalizations of
"justified" to many extensions: argument-level (`∃a ∀E` — one support argument
survives every extension) and claim-level (`∀E ∃a` — every extension accepts some
support argument). They differ: on the two-cycle `0 ↔ 1` with
`support = [0, 1]`, `preferredSem.enumerate` is `[[0], [1]]`, so every extension
accepts a support argument while *no single* support argument is accepted by every
extension — `(profile preferredSem F 0).inAll` and `(profile preferredSem F 1).inAll`
are both `false`. Claim-level therefore reports `justified` where the
argument-level reading has nothing to report. (Those three evaluations are now
mechanized: `preferredSem_enumerate_twoCycle` for the enumeration, and
`profile_preferredSem_twoCycle` — stated for every carrier argument — for the two
`inAll` bits. `observe_not_determined_by_profile` is the sharper form: two
semantics with the same profile on every carrier argument and different
observations of the same claim.) The claim-level reading is adopted
because it is the `∀`-generalization
of what `Grounded.statusC` already means on a single extension, and because it is
skeptical acceptance of the *conclusion* rather than of an argument for it.
Because `∀E ∃a` is not a function of per-argument acceptance data, `observe`
folds over `sem.enumerate F` directly and does **not** factor through `profile`.

*`gap` outranks `noExtension`.* Both guards can fire at once — empty support under
a semantics with no extension — so the order is a decision, and it is made in
favour of `gap`. `gap` is the one status that reads no extension data at all: it
inspects `c.support` and nothing else, so it is the same verdict under every
semantics. Testing it first is what keeps that true, and `observe_gap` is the
statement, proved for an arbitrary `sem` with no hypothesis beyond
`c.support = []` itself — nothing about the semantics, the carrier, or the
enumeration.

Nothing is lost by demoting the emptiness report. `observe_noExtension_iff`
recovers it exactly — and in this order it recovers something sharper, since
`noExtension` now also carries `c.support ≠ []`. Where a consumer needs "this
verdict is backed by an extension", `enumerate_ne_nil_of_observed_ne_gap` supplies
it for every status other than `gap`.

**Where the fabrication hazards live — there are two, and neither is decided by
this ordering.** Both come from `List.all [] p = true`, but over different lists.

*At the enumeration.* On an empty enumeration the acceptance and defeat guards
would both hold, and a claim would be reported as both skeptically justified and
skeptically defeated. What rules that out is the enumeration guard preceding both
`all`-guards.

*At the support.* `claimDefeatedB F E c` is `c.support.all …`, so on empty support
it is vacuously `true` for *every* `E`, however many extensions exist — while
`claimAcceptedB` is vacuously `false`. An unsupported claim reaching the
`all`-guards would therefore be reported specifically `defeated`, the worst
available verdict, on a framework with perfectly good extensions. What rules that
out is the `gap` guard preceding both `all`-guards.

Each guard blocks its own hazard, and both guards precede the `all`-guards under
*either* arrangement of the first two arms — so the `gap`-vs-`noExtension` order
carries no safety content. It changes only which of two non-vacuous answers the
doubly-empty corner case gets, and that choice is made on the semantics-
independence argument above, not on safety. -/
def observe (sem : ExtensionSemantics) (F : AF) (c : Grounded.Claim) : ClaimObservation :=
  if c.support = [] then ClaimObservation.observed Status.gap
  else if (sem.enumerate F).isEmpty then ClaimObservation.noExtension
  else if (sem.enumerate F).all (fun E => claimAcceptedB E c) then
    ClaimObservation.observed Status.justified
  else if (sem.enumerate F).all (fun E => claimDefeatedB F E c) then
    ClaimObservation.observed Status.defeated
  else ClaimObservation.observed Status.contested

/-- **`gap` is semantics-independent, mechanized.** An unsupported claim gets the
same answer out of `observe` under every semantics, with no hypothesis on `sem`,
on the carrier, or on the enumeration: the `gap` arm reads `c.support` and no
extension data whatsoever, so there is nothing for a choice of semantics to
change. This is the reason the `gap` guard is tested first, and it is the only
status for which such a statement can be made: each of the other three is
witnessed to vary with the semantics — on the two-cycle `0 ↔ 1` with
`support = [0, 1]`, `groundedSem` observes `contested` where `preferredSem`
observes `justified`; adding an argument `2` attacked by both of `0, 1` and taking
`support = [2]` gives `contested` under `groundedSem` and `defeated` under
`preferredSem`. (Those are `observe_twoCycle_grounded_ne_preferred` and
`observe_twoCycleSink_grounded_ne_preferred`; `observe_claimNoSupport_uniform`
instantiates this theorem itself at all five instances.)

Read the scope narrowly. This is a fact about what `observe` returns. It says
nothing about `Grounded.statusC` — the corresponding fact there is
`Grounded.statusC_gap_iff`, proved separately, and the two are connected only
through `observe_grounded`. -/
theorem observe_gap (sem : ExtensionSemantics) (F : AF) (c : Grounded.Claim)
    (hs : c.support = []) : observe sem F c = ClaimObservation.observed Status.gap := by
  unfold observe
  rw [if_pos hs]

/-- **`observe_gap`'s converse.** `gap` is reported for no reason other than empty
support, so the implication is in fact a biconditional. Stated because
`Grounded.statusC_gap_iff` is an `iff` and the two are meant to be read side by
side; without this the asymmetry invites the reading that some *other* input could
also produce `gap`. -/
theorem observe_gap_iff (sem : ExtensionSemantics) (F : AF) (c : Grounded.Claim) :
    observe sem F c = ClaimObservation.observed Status.gap ↔ c.support = [] := by
  constructor
  · intro h
    by_cases hs : c.support = []
    · exact hs
    · exfalso
      unfold observe at h
      rw [if_neg hs] at h
      split at h
      · exact absurd h (by decide)
      · split at h
        · exact absurd h (by decide)
        · split at h
          · exact absurd h (by decide)
          · exact absurd h (by decide)
  · exact observe_gap sem F c

/-- **N17 point (1), holes independence.** For every extension semantics,
changing only `Grounded.Claim.holes` leaves observation unchanged, and the
resulting observation is `gap` exactly when complete support is empty.  Thus
holes are an independent `Grounded.incompleteAlternative` diagnostic, not a
fifth grounded status or a sixth public report.  M3 public transitions consume
this result. -/
theorem observe_holes_independent (sem : ExtensionSemantics) (F : AF)
    (support holes₁ holes₂ : List Arg) :
    observe sem F { support := support, holes := holes₁ } =
        observe sem F { support := support, holes := holes₂ } ∧
      (observe sem F { support := support, holes := holes₁ } =
          ClaimObservation.observed Status.gap ↔ support = []) := by
  constructor
  · rfl
  · exact observe_gap_iff sem F { support := support, holes := holes₁ }

/-- **No verdict escapes an empty enumeration.** For every semantics, framework and
claim, an empty extension set forces one of the two answers that consult no
extension data. This is the general fact behind the concrete
`observe_stableSem_threeCycle` witnesses: the `all`-guards are unreachable when
`sem.enumerate F` is empty, so the vacuous-`List.all` fabrication cannot arise for
*any* instance, including ones not written here. -/
theorem no_verdict_on_empty (sem : ExtensionSemantics) (F : AF) (c : Grounded.Claim)
    (hnil : sem.enumerate F = []) :
    observe sem F c = ClaimObservation.observed Status.gap ∨
      observe sem F c = ClaimObservation.noExtension := by
  by_cases hs : c.support = []
  · exact Or.inl (observe_gap sem F c hs)
  · refine Or.inr ?_
    unfold observe
    rw [if_neg hs, if_pos (by rw [hnil]; rfl)]

/-- **The emptiness report, recovered exactly.** Demoting `noExtension` below `gap`
does not lose the fact that the semantics had no extension; this biconditional is
where it is kept. Under this ordering the constructor is *sharper* than it would
be at the top: `noExtension` now implies `c.support ≠ []` as well, so it reports
"the semantics has nothing to say about a claim that was otherwise answerable"
rather than merging that with the unsupported case. -/
theorem observe_noExtension_iff (sem : ExtensionSemantics) (F : AF) (c : Grounded.Claim) :
    observe sem F c = ClaimObservation.noExtension
      ↔ (sem.enumerate F = [] ∧ c.support ≠ []) := by
  unfold observe
  by_cases hs : c.support = []
  · rw [if_pos hs]
    exact iff_of_false (by decide) (fun hc => hc.2 hs)
  · rw [if_neg hs]
    by_cases h0 : (sem.enumerate F).isEmpty = true
    · rw [if_pos h0]
      exact iff_of_true rfl ⟨List.isEmpty_iff.mp h0, hs⟩
    · rw [if_neg h0]
      refine iff_of_false ?_ (fun hc => h0 (List.isEmpty_iff.mpr hc.1))
      intro hc
      split at hc
      · exact absurd hc (by decide)
      · split at hc
        · exact absurd hc (by decide)
        · exact absurd hc (by decide)

/-- **Every non-`gap` verdict is backed by an extension.** The uniform invariant a
consumer wants when it pattern-matches on `.observed s`: apart from `gap`, which
is answered without consulting the semantics at all, a status can only be reported
when the enumeration is non-empty, so no verdict below rests on a vacuous
`List.all`. Stated here rather than reconstructed at each use site, because the
side condition `s ≠ .gap` is easy to forget. Forgetting it is an unsound step in
*reasoning* — believing a `gap` verdict is backed by an extension — not a route to
the justified-and-defeated fabrication, and Lean blocks it regardless: without
`hgap` there is nothing to discharge the `gap` case with, and the conclusion is
false there. -/
theorem enumerate_ne_nil_of_observed_ne_gap (sem : ExtensionSemantics) {F : AF}
    {c : Grounded.Claim} {s : Status}
    (hobs : observe sem F c = ClaimObservation.observed s) (hgap : s ≠ Status.gap) :
    sem.enumerate F ≠ [] := by
  intro hnil
  unfold observe at hobs
  by_cases hs : c.support = []
  · rw [if_pos hs] at hobs
    injection hobs with hst
    exact hgap hst.symm
  · rw [if_neg hs, if_pos (List.isEmpty_iff.mpr hnil)] at hobs
    exact ClaimObservation.noConfusion hobs

/-! ### The grounded instance of the observation

`observe_grounded` is the regression statement of this milestone: the four-state
status the development already prints is exactly what the semantics-parametric
observation returns on `groundedSem`. Two small bridges are needed first, both
translating a `Grounded.labelC` case into the vocabulary `observe` folds over. -/

/-- `labelC = in` is membership in the grounded extension. A composition of two
existing results (`labelC_inn_iff`, `directIn_iff`) named here because
`observe_grounded` needs the membership form twice — once in each direction — and
the `DirectIn` detour is irrelevant to it. -/
theorem labelC_inn_iff_mem {F : AF} {a : Arg} :
    labelC F a = Label.inn ↔ a ∈ grounded F :=
  (labelC_inn_iff a).trans (directIn_iff a)

/-- Being attacked by the grounded extension is `Grounded.DirectOut`. The carrier
bound in `directOut_iff_bex` is discharged by `Grounded.iter_subset_args`, since
every member of the grounded extension is a carrier argument — so the unbounded
scan `attackedByB` performs loses nothing. -/
theorem attackedByB_grounded_iff {F : AF} {a : Arg} :
    attackedByB F (grounded F) a = true ↔ DirectOut F a := by
  unfold attackedByB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨b, hb, hba⟩
    exact directOut_iff_bex.mpr
      ⟨b, iter_subset_args F.args.length b hb, (directIn_iff b).mpr hb, hba⟩
  · intro h
    obtain ⟨b, hb, hba⟩ := directOut_sound h
    exact ⟨b, hb, hba⟩

/-- `labelC = undec` is "neither in the grounded extension nor attacked by it",
phrased in `observe`'s vocabulary. This is the case that carries the `contested`
verdict, and stating it positively is what keeps the `contested` arm of
`observe_grounded` from being a leftover branch. -/
theorem labelC_undec_iff_unattacked {F : AF} {a : Arg} :
    labelC F a = Label.undec ↔ a ∉ grounded F ∧ attackedByB F (grounded F) a ≠ true := by
  rw [labelC_undec_iff a]
  exact and_congr (not_congr (directIn_iff a))
    (not_congr attackedByB_grounded_iff).symm

/-- **The headline regression theorem.** On the grounded semantics the
semantics-parametric observation is exactly `Grounded.statusC`: the status the
paper already prints is the grounded instance of the general definition, not a
different function that happens to agree on examples.

The `noExtension` arm is *excluded rather than assumed*: `groundedSem_singleton`
gives a one-element enumeration, and `isEmpty` of a one-element list is `false`,
so that guard provably cannot fire. The remaining three arms match `statusC`'s
three by the two `labelC` bridges above, with `groundedSem_singleton`'s membership
component transporting every test from the enumerated extension onto
`Grounded.grounded F`. `F.args.Nodup` is used at exactly one place: obtaining
`groundedSem_singleton`. Note that the `gap` branch is discharged before that
lemma is invoked, so it consumes neither the singleton fact nor `Nodup` — the
proof mirrors the definition, where `gap` is decided without reading the
enumeration. -/
theorem observe_grounded {F : AF} (h : F.args.Nodup) (c : Grounded.Claim) :
    observe groundedSem F c = ClaimObservation.observed (Grounded.statusC F c) := by
  unfold observe
  by_cases hs : c.support = []
  · rw [if_pos hs, (statusC_gap_iff F c).mpr hs]
  · rw [if_neg hs]
    obtain ⟨E, hE, hmem⟩ := groundedSem_singleton h
    rw [hE]
    have hempty : ¬ ((([E] : List (List Arg))).isEmpty = true) := by simp
    have hall : ∀ f : List Arg → Bool, ([E] : List (List Arg)).all f = f E := by
      intro f; simp
    rw [if_neg hempty, hall, hall]
    by_cases hacc : claimAcceptedB E c = true
    · rw [if_pos hacc]
      obtain ⟨a, ha, haE⟩ :=
        List.any_eq_true.mp (show c.support.any (fun a => memB a E) = true from hacc)
      rw [(statusC_justified_iff F c).mpr
        ⟨a, ha, labelC_inn_iff_mem.mpr ((hmem a).mp (memB_iff.mp haE))⟩]
    · rw [if_neg hacc]
      have hnotin : ∀ a ∈ c.support, a ∉ grounded F := by
        intro a ha hga
        exact hacc (show c.support.any (fun a => memB a E) = true from
          List.any_eq_true.mpr ⟨a, ha, memB_iff.mpr ((hmem a).mpr hga)⟩)
      have hinn : ¬ (c.support.any (fun a => labelC F a == Label.inn) = true) := by
        intro hc
        obtain ⟨a, ha, hlab⟩ := List.any_eq_true.mp hc
        exact hnotin a ha (labelC_inn_iff_mem.mp (by simpa using hlab))
      by_cases hdef : claimDefeatedB F E c = true
      · rw [if_pos hdef]
        have hundec : ¬ (c.support.any (fun a => labelC F a == Label.undec) = true) := by
          intro hc
          obtain ⟨a, ha, hlab⟩ := List.any_eq_true.mp hc
          have hat : attackedByB F E a = true :=
            List.all_eq_true.mp
              (show c.support.all (fun a => attackedByB F E a) = true from hdef) a ha
          exact (labelC_undec_iff_unattacked.mp (by simpa using hlab)).2
            ((attackedByB_congr hmem a).mp hat)
        unfold statusC
        rw [if_neg hs, if_neg hinn, if_neg hundec]
      · rw [if_neg hdef]
        have hfalse : c.support.all (fun a => attackedByB F E a) = false := by
          cases hb : c.support.all (fun a => attackedByB F E a) with
          | false => rfl
          | true => exact absurd (show claimDefeatedB F E c = true from hb) hdef
        obtain ⟨a, ha, hna⟩ := List.all_eq_false.mp hfalse
        have hundec : c.support.any (fun a => labelC F a == Label.undec) = true := by
          refine List.any_eq_true.mpr ⟨a, ha, ?_⟩
          rw [labelC_undec_iff_unattacked.mpr
            ⟨hnotin a ha, fun hc => hna ((attackedByB_congr hmem a).mpr hc)⟩]
          rfl
        unfold statusC
        rw [if_neg hs, if_neg hinn, if_pos hundec]

/-! ### Justified and defeated cannot both hold

Nothing in `ClaimObservation` or `observe` forces the `justified` and `defeated`
guards to be exclusive; `observe` merely tests them in order. That the order is
not silently resolving a genuine tie has to be *proved*, and the proof needs two
facts the interface does not supply on its own: that at least one extension
exists, and that extensions are conflict-free. `ExtensionSemantics` requires
neither — its `spec` field is an arbitrary `AF → List Arg → Prop`. Rather than
add a field (the record is frozen and five instances depend on its shape), the
conflict-freedom requirement is an explicit hypothesis, `SpecConflictFree`, and is
discharged once per instance below. -/

/-- The hypothesis `justified_defeated_exclusive` needs: every set the semantics
admits on `F` is conflict-free. Named rather than inlined because it is discharged
five separate times, and because a sixth instance added later owes exactly this
and nothing else to inherit the exclusivity result.

**The cost of phrasing this over `spec` rather than `enumerate`, recorded for
downstream callers.** Because the condition is about `sem.spec`, a proof holding
`E ∈ sem.enumerate F` must cross to `sem.spec F E` through `sem.sound F hnd`,
which binds `F.args.Nodup` — and that is the *only* reason `F.args.Nodup` appears
in `justified_defeated_exclusive` and `observe_justified_not_all_defeated`. An
`enumerate`-phrased variant (`∀ E ∈ sem.enumerate F, ConflictFree F E`) proves the
same exclusivity with no `Nodup` hypothesis at all. The `spec` phrasing is kept
deliberately: it is a property of the *semantics* rather than of its enumerator,
so it stays true of any other adequate enumerator for the same `spec`, and each of
the five discharges remains a single projection. Callers in later milestones
should expect to supply `Nodup`, and should know it is this trade and not a
mathematical necessity. -/
def SpecConflictFree (sem : ExtensionSemantics) (F : AF) : Prop :=
  ∀ S, sem.spec F S → ConflictFree F S

/-- **Exclusivity is not free.** With at least one extension present and every
extension conflict-free, a claim cannot be both skeptically accepted and
skeptically defeated. `hne` and `hcf` are both load-bearing: on an empty
enumeration both `List.all` guards hold vacuously, and without conflict-freedom a
single extension could contain a support argument *and* an attacker of it. The
third hypothesis, `hnd`, is not about exclusivity at all — it is consumed solely
by the `sem.sound F hnd` crossing that turns membership in the enumeration into
`sem.spec`, and it is there because `SpecConflictFree` is phrased over `spec`
rather than `enumerate`; see that definition's docstring. The proof is
exactly that — pick any extension `E`, get a support argument inside `E` from the
acceptance guard and an attacker of it inside `E` from the defeat guard, and let
`ConflictFree F E` close the contradiction. -/
theorem justified_defeated_exclusive (sem : ExtensionSemantics) {F : AF}
    (hnd : F.args.Nodup) (hcf : SpecConflictFree sem F) (c : Grounded.Claim)
    (hne : sem.enumerate F ≠ []) :
    ¬ ((sem.enumerate F).all (fun E => claimAcceptedB E c) = true ∧
        (sem.enumerate F).all (fun E => claimDefeatedB F E c) = true) := by
  rintro ⟨hacc, hdef⟩
  have hex : ∃ E, E ∈ sem.enumerate F := by
    cases hL : sem.enumerate F with
    | nil => exact absurd hL hne
    | cons E rest => exact ⟨E, List.mem_cons_self⟩
  obtain ⟨E, hE⟩ := hex
  have hcfE : ConflictFree F E := hcf E ((sem.sound F hnd E).mp hE).2
  obtain ⟨a, ha, haE⟩ :=
    List.any_eq_true.mp (show c.support.any (fun x => memB x E) = true from
      List.all_eq_true.mp hacc E hE)
  obtain ⟨b, hb, hba⟩ :=
    List.any_eq_true.mp (show E.any (fun b => F.attack b a) = true from
      List.all_eq_true.mp
        (show c.support.all (fun x => attackedByB F E x) = true from
          List.all_eq_true.mp hdef E hE) a ha)
  exact hcfE b hb a (memB_iff.mp haE) hba

/-- **The priority order in `observe` is not hiding a tie.** When `observe`
reports `justified` under a conflict-free semantics, the `defeated` guard it never
reached is genuinely false, so the verdict does not depend on which guard was
tested first. This is the consumer-facing form of `justified_defeated_exclusive`;
its enumeration-non-emptiness hypothesis is not passed in because the proof case
splits on `observe`'s own enumeration guard and reads it off the negative branch,
so this theorem depends on no other result about `observe`. -/
theorem observe_justified_not_all_defeated (sem : ExtensionSemantics) {F : AF}
    (hnd : F.args.Nodup) (hcf : SpecConflictFree sem F) (c : Grounded.Claim)
    (hj : observe sem F c = ClaimObservation.observed Status.justified) :
    ¬ ((sem.enumerate F).all (fun E => claimDefeatedB F E c) = true) := by
  intro hdef
  unfold observe at hj
  by_cases hs : c.support = []
  · rw [if_pos hs] at hj; exact absurd hj (by decide)
  · rw [if_neg hs] at hj
    by_cases h0 : (sem.enumerate F).isEmpty = true
    · rw [if_pos h0] at hj; exact absurd hj (by decide)
    · rw [if_neg h0] at hj
      have hne : sem.enumerate F ≠ [] := fun hc => h0 (List.isEmpty_iff.mpr hc)
      by_cases hacc : (sem.enumerate F).all (fun E => claimAcceptedB E c) = true
      · exact justified_defeated_exclusive sem hnd hcf c hne ⟨hacc, hdef⟩
      · rw [if_neg hacc, if_pos hdef] at hj
        exact absurd hj (by decide)

/-! ### Discharging `SpecConflictFree` for the five instances

The hypothesis cannot be discharged once and for all inside the interface for the
reason the previous section note gives: `ExtensionSemantics.spec` is an arbitrary
`AF → List Arg → Prop`, so there is nothing generic to project from. That is true
however uniform the instances happen to be.

The five instances take **three** distinct routes, not five: `Stable` names the
conjunct itself (`hS.2.1`); `Complete` and `Preferred` reach it through
`Admissible` (`hS.1.2.1`); `SemiStable` and `LeastComplete` reach it through
`Complete` and then `Admissible` (`hS.1.1.2.1`). Each corollary below is the
projection path for its instance. -/

/-- `Complete` extensions are conflict-free (via `Admissible`). -/
theorem completeSem_specConflictFree {F : AF} : SpecConflictFree completeSem F :=
  fun _ hS => hS.1.2.1

/-- `Stable` extensions are conflict-free — the conjunct is part of the
definition, since `Stable` is stated by the attack condition rather than through
`Admissible`. -/
theorem stableSem_specConflictFree {F : AF} : SpecConflictFree stableSem F :=
  fun _ hS => hS.2.1

/-- `Preferred` extensions are conflict-free (via `Admissible`); note this uses
the maximality-free half of the definition only. -/
theorem preferredSem_specConflictFree {F : AF} : SpecConflictFree preferredSem F :=
  fun _ hS => hS.1.2.1

/-- `SemiStable` extensions are conflict-free (via `Complete`, then
`Admissible`). -/
theorem semiStableSem_specConflictFree {F : AF} : SpecConflictFree semiStableSem F :=
  fun _ hS => hS.1.1.2.1

/-- `LeastComplete` extensions are conflict-free (via `Complete`, then
`Admissible`). This is the whole of what `observe_justified_not_all_defeated`
needs beyond `F.args.Nodup` to apply to the instance the runtime actually
evaluates. -/
theorem groundedSem_specConflictFree {F : AF} : SpecConflictFree groundedSem F :=
  fun _ hS => hS.1.1.2.1

end Lara.Semantics
