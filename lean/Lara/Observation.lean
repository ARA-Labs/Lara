/-
Source-to-framework observation transport (`Lara.Observation`).

**Why this module exists — the seam, not the line count.** It owns the
source-side multi-extension vocabulary, and — the library root and the axiom
audit aside, which import everything — it is the only module that depends
on *both* `Lara.Compile` (the checked program, the frozen closure-edge relation
`Edge`, and the compiled framework `toAF`) and `Lara.Semantics` (the generic
`ExtensionSemantics` interface and the claim observation `observe`). Neither of
those two imports the other, and neither needs anything defined here, so the
dependency edge only ever points inward. That is the `CLAUDE.md` split test — a
group of definitions with its own vocabulary and its own dependencies — and it is
the reason this is a new module rather than a new section of `Compile.lean`.

**What is transported, and what the hypothesis is.** `Compile.Faithful` bundles
two obligations: `agrees` (the oracle decides `Edge` at declared argument
positions) and `ranged` (no edge touches an out-of-range index). Only the first
is used below, and the difference is not cosmetic: `faithful_unique` proves that
the two obligations *together* pin the oracle down as a function, so a transport
theorem stated over `Faithful` alone would be provable by `funext` and would
carry no content. Stated over `AgreesOnArgs` — `Faithful.agrees` on its own —
the hypothesis leaves the frameworks free to differ off the carrier, and the
transport has to be earned. Every *transport* result below therefore asks for
`agrees` and not `ranged` (`faithful_unique` and `agreesOnArgs_of_faithful` are
the exceptions: they are about the relationship between the two hypotheses, so
they necessarily mention `Faithful`), and `agreesOnArgs_of_faithful` supplies it from a
`Faithful` witness whenever a caller has one.

**Why the transport is possible at all: the carrier bound (D7).** A
specification survives replacing the framework only if it never reads
`F.attack` outside `F.args`. `Semantics.Bounded` *is* the condition
`∀ a ∈ S, a ∈ F.args`, and `Admissible` and `Stable` each carry it as their
first conjunct, so every attack test they perform has both endpoints in the
carrier. That this is load-bearing rather than stylistic is a
theorem here, not a comment: `not_attackExtensional_conflictFree` exhibits two
frameworks with the same carrier `[0]`, the same attack behaviour on `[0]`, and
opposite `Grounded.ConflictFree` verdicts on the junk set `[0, 5]` — the very
set D7 was written about. `ConflictFree` alone is *not* `AttackExtensional`;
`Admissible`, which is `ConflictFree` plus the bound, is.

**The claim side needs one more hypothesis.** `Semantics.attackedByB` bounds the
attacker to the extension but deliberately leaves the *target* unbounded (see its
docstring in `Lara.Semantics`), so `observe` can read `F.attack b a` at a support
argument `a` outside the carrier — exactly where `AgreesOnArgs` says nothing.
`not_observe_congr_of_unbounded_support` is the witness that this is a real gap
and not a proof artefact, and every claim-level result below therefore assumes
the claim's support lies in the carrier (for a compiled program: the support
indices are declared arguments).

**Relation to `Compile.srcStatus_iff_checked`.** `SrcObservation` is the
observation analogue of `Compile.SrcStatus`: a claim-and-answer relation that
mentions no oracle. `srcObservation_iff_checked` mirrors
`Compile.srcStatus_iff_checked` in shape, and `srcStatus_iff_srcObservation`
proves the two agree at `groundedSem`. Read that pairing precisely, because the
name map depends on it: `srcStatus_iff_checked` is *not literally* an instance of
`srcObservation_iff_checked` — its subject is the inductive `SrcStatus`
derivation, whose four constructors are defined from `SrcIn`/`SrcOut` and not
from any extension enumeration, and it carries no support-boundedness side
condition. What is proved is the equivalence: under the support-boundedness
hypothesis, `SrcStatus P c s` holds exactly when the `groundedSem` source
observation of `c` is `observed s`. The paper may say the grounded status
relation *is* the grounded instance of the observation relation, with that side
condition named; it may not say the old theorem was re-derived as a special case
of the new one, because it was not.

No Mathlib; every proof here is core Lean 4.
-/

import Lara.Compile
import Lara.Semantics

namespace Lara.Observation

open Lara.Grounded
open Lara.Semantics

/-! ### Carrier-local invariance of a specification

The property a specification needs in order to survive a change of framework
that only alters attacks *outside* the carrier. -/

/-- **`spec` reads the attack relation only inside the carrier.** Two frameworks
with the same `args`, whose `attack` agrees pointwise at pairs of carrier
members, are indistinguishable to `spec`.

The agreement hypothesis is deliberately restricted to carrier members.
`Grounded.AF` has exactly two fields, so demanding `F.attack = G.attack` outright
would force `F` and `G` to be the same structure and the property would hold of
every specification; demanding agreement only on `args` is what leaves room for
`not_attackExtensional_conflictFree`. -/
def AttackExtensional (spec : AF → List Arg → Prop) : Prop :=
  ∀ F G : AF, F.args = G.args →
    (∀ a ∈ F.args, ∀ b ∈ F.args, F.attack a b = G.attack a b) →
    ∀ S, spec F S ↔ spec G S

/-- Carrier agreement is symmetric. Needed because the two hypotheses of
`AttackExtensional` are stated over `F.args`, so swapping the frameworks has to
move the membership side conditions across the carrier equation. -/
theorem agree_symm {F G : AF} (hargs : F.args = G.args)
    (hatt : ∀ a ∈ F.args, ∀ b ∈ F.args, F.attack a b = G.attack a b) :
    ∀ a ∈ G.args, ∀ b ∈ G.args, G.attack a b = F.attack a b := by
  intro a ha b hb
  exact (hatt a (by rw [hargs]; exact ha) b (by rw [hargs]; exact hb)).symm

/-- **One direction suffices.** `AttackExtensional` is a biconditional between two
symmetric situations, so an implication proved for an arbitrary ordered pair
yields the biconditional by applying it twice. Every instance below is proved
through this combinator, so no proof states the same argument in both
directions. -/
theorem attackExtensional_of_imp {spec : AF → List Arg → Prop}
    (h : ∀ F G : AF, F.args = G.args →
      (∀ a ∈ F.args, ∀ b ∈ F.args, F.attack a b = G.attack a b) →
      ∀ S, spec F S → spec G S) :
    AttackExtensional spec :=
  fun F G hargs hatt S =>
    ⟨h F G hargs hatt S, h G F hargs.symm (agree_symm hargs hatt) S⟩

/-! ### The carrier-local congruences the instances are built from -/

/-- `Bounded` mentions `args` and never `attack`, so it transports on the carrier
equation alone. -/
theorem bounded_congr_af {F G : AF} (hargs : F.args = G.args) (S : List Arg) :
    Bounded F S ↔ Bounded G S := by
  unfold Bounded
  rw [hargs]

/-- **The carrier bound doing its work, first instance.** Conflict-freedom
transports *given* that `S` lies in the carrier: both endpoints of every attack
test are then carrier members, which is exactly where the two frameworks are
assumed to agree. Drop `hb` and the statement is false —
`not_attackExtensional_conflictFree` is the counterexample.

Note what is *absent*: the carrier equation `F.args = G.args`. Conflict-freedom
never mentions `G.args`, and `hb` already places `S` inside `F.args`, so the
hypothesis would be dead weight — the unused-variable linter flags it. (A
warning, not an error: nothing in `lakefile.toml` or CI turns it into one.)
The other three congruences in this section (`bounded_congr_af`,
`defendedB_congr_af`, `mem_reach_congr_af`) each stop compiling when it is
removed. -/
theorem conflictFree_congr_af {F G : AF}
    (hatt : ∀ a ∈ F.args, ∀ b ∈ F.args, F.attack a b = G.attack a b)
    {S : List Arg} (hb : Bounded F S) :
    ConflictFree F S ↔ ConflictFree G S := by
  constructor
  · intro h a ha b hbS hab
    exact h a ha b hbS ((hatt a (hb a ha) b (hb b hbS)).trans hab)
  · intro h a ha b hbS hab
    exact h a ha b hbS ((hatt a (hb a ha) b (hb b hbS)).symm.trans hab)

/-- **The carrier bound doing its work, second instance.** `Grounded.defendedB`
scans attackers inside `args` and looks for counter-attackers inside `S`, so with
`S` bounded and the defended argument itself a carrier member, every attack test
it performs has both endpoints in the carrier. Both side conditions are consumed
in the proof: `ha` for the attacker-vs-target test, `hb` for the
counter-attacker-vs-attacker test. -/
theorem defendedB_congr_af {F G : AF} (hargs : F.args = G.args)
    (hatt : ∀ a ∈ F.args, ∀ b ∈ F.args, F.attack a b = G.attack a b)
    {S : List Arg} (hb : Bounded F S) {a : Arg} (ha : a ∈ F.args) :
    defendedB F S a = true ↔ defendedB G S a = true := by
  rw [defendedB_iff, defendedB_iff]
  constructor
  · intro h x hx hxa
    have hxF : x ∈ F.args := by rw [hargs]; exact hx
    obtain ⟨c, hc, hcx⟩ := h x hxF ((hatt x hxF a ha).trans hxa)
    exact ⟨c, hc, (hatt c (hb c hc) x hxF).symm.trans hcx⟩
  · intro h x hx hxa
    have hxG : x ∈ G.args := by rw [← hargs]; exact hx
    obtain ⟨c, hc, hcx⟩ := h x hxG ((hatt x hx a ha).symm.trans hxa)
    exact ⟨c, hc, (hatt c (hb c hc) x hx).trans hcx⟩

/-- The range map `Semantics.reach` sees the attack relation only through
`attacked`, which filters `F.args`; with `S` bounded, both endpoints are again
carrier members. Stated at the membership level because `SemiStable`'s maximality
clause compares ranges by membership and never by list layout. -/
theorem mem_reach_congr_af {F G : AF} (hargs : F.args = G.args)
    (hatt : ∀ a ∈ F.args, ∀ b ∈ F.args, F.attack a b = G.attack a b)
    {S : List Arg} (hb : Bounded F S) :
    ∀ x, x ∈ reach F S ↔ x ∈ reach G S := by
  intro x
  rw [mem_reach, mem_reach, mem_attacked, mem_attacked]
  constructor
  · rintro (hx | ⟨hc, y, hy, hyx⟩)
    · exact Or.inl hx
    · exact Or.inr ⟨by rw [← hargs]; exact hc,
        y, hy, (hatt y (hb y hy) x hc).symm.trans hyx⟩
  · rintro (hx | ⟨hc, y, hy, hyx⟩)
    · exact Or.inl hx
    · have hcF : x ∈ F.args := by rw [hargs]; exact hc
      exact Or.inr ⟨hcF, y, hy, (hatt y (hb y hy) x hcF).trans hyx⟩

/-! ### Carrier-locality of the specifications -/

/-- `Bounded` is carrier-local. -/
theorem attackExtensional_bounded : AttackExtensional Bounded :=
  attackExtensional_of_imp (fun _ _ hargs _ S => (bounded_congr_af hargs S).mp)

/-- `Admissible` is carrier-local. Its own `Bounded` conjunct supplies the side
condition that `conflictFree_congr_af` and `defendedB_congr_af` need, which is
why the compound predicate transports where its `ConflictFree` conjunct alone
does not (`not_attackExtensional_conflictFree`). -/
theorem attackExtensional_admissible : AttackExtensional Admissible :=
  attackExtensional_of_imp <| by
    rintro F G hargs hatt S ⟨hbd, hcf, hdef⟩
    exact ⟨(bounded_congr_af hargs S).mp hbd,
      (conflictFree_congr_af hatt hbd).mp hcf,
      fun a ha => (defendedB_congr_af hargs hatt hbd (hbd a ha)).mp (hdef a ha)⟩

/-- `Complete` is carrier-local. The defence-closure clause ranges over `F.args`,
so its `defendedB` test is at a carrier member and `defendedB_congr_af`
applies. -/
theorem attackExtensional_complete : AttackExtensional Complete :=
  attackExtensional_of_imp <| by
    rintro F G hargs hatt S ⟨hadm, hclosed⟩
    refine ⟨attackExtensional_admissible F G hargs hatt S |>.mp hadm, fun a ha hdef => ?_⟩
    have haF : a ∈ F.args := by rw [hargs]; exact ha
    exact hclosed a haF ((defendedB_congr_af hargs hatt hadm.1 haF).mpr hdef)

/-- `Stable` is carrier-local. Its attack clause quantifies the target over
`F.args` and the attacker over `S`, which `Bounded` places in `F.args` too. -/
theorem attackExtensional_stable : AttackExtensional Stable :=
  attackExtensional_of_imp <| by
    rintro F G hargs hatt S ⟨hbd, hcf, hattacks⟩
    refine ⟨(bounded_congr_af hargs S).mp hbd,
      (conflictFree_congr_af hatt hbd).mp hcf, fun a ha hna => ?_⟩
    have haF : a ∈ F.args := by rw [hargs]; exact ha
    obtain ⟨b, hbS, hba⟩ := hattacks a haF hna
    exact ⟨b, hbS, (hatt b (hbd b hbS) a haF).symm.trans hba⟩

/-- `Preferred` is carrier-local. The maximality clause quantifies over arbitrary
lists `T`, with no side condition — which is sound only because `Admissible F T`
already forces `T` into the carrier, so `attackExtensional_admissible` can move
the comparison set between the two frameworks. -/
theorem attackExtensional_preferred : AttackExtensional Preferred :=
  attackExtensional_of_imp <| by
    rintro F G hargs hatt S ⟨hadm, hmax⟩
    refine ⟨attackExtensional_admissible F G hargs hatt S |>.mp hadm, fun T hT hsub => ?_⟩
    exact hmax T (attackExtensional_admissible F G hargs hatt T |>.mpr hT) hsub

/-- `LeastComplete` — the specification of `Semantics.groundedSem` — is
carrier-local, by the same move as `Preferred` with `Complete` in place of
`Admissible`. -/
theorem attackExtensional_leastComplete : AttackExtensional LeastComplete :=
  attackExtensional_of_imp <| by
    rintro F G hargs hatt S ⟨hc, hmin⟩
    refine ⟨attackExtensional_complete F G hargs hatt S |>.mp hc, fun T hT => ?_⟩
    exact hmin T (attackExtensional_complete F G hargs hatt T |>.mpr hT)

/-- `SemiStable` is carrier-local. Beyond the `Complete` transport this needs the
range comparison to move as well, which is `mem_reach_congr_af` applied to `S`
and to the comparison set `T`; the boundedness side condition each application
needs comes from the `Complete` hypothesis already in hand. -/
theorem attackExtensional_semiStable : AttackExtensional SemiStable :=
  attackExtensional_of_imp <| by
    rintro F G hargs hatt S ⟨hc, hmax⟩
    refine ⟨attackExtensional_complete F G hargs hatt S |>.mp hc, fun T hT hsub x hx => ?_⟩
    have hTF : Complete F T := attackExtensional_complete F G hargs hatt T |>.mpr hT
    have hrS := mem_reach_congr_af hargs hatt hc.1.1
    have hrT := mem_reach_congr_af hargs hatt hTF.1.1
    have hsubF : ∀ y ∈ reach F S, y ∈ reach F T :=
      fun y hy => (hrT y).mpr (hsub y ((hrS y).mp hy))
    exact (hrS x).mp (hmax T hTF hsubF x ((hrT x).mpr hx))

/-! ### The carrier bound is load-bearing, not stylistic

D7 in the M2a plan claims the bound inside the predicates is what makes the
transport possible. The two frameworks below turn that claim into a refutation
of the unbounded reading. -/

/-- One argument, no attacks at all. -/
def oneNoAttack : AF where
  args := [0]
  attack := fun _ _ => false

/-- The same carrier and the same attack behaviour *on that carrier*, differing
only at the pair `(5, 5)`, which lies outside `args`. -/
def oneJunkSelfAttack : AF where
  args := [0]
  attack := fun a b => a == 5 && b == 5

/-- The two frameworks have the same carrier and agree on it. Checked by
`decide`, so the agreement is not taken on trust. -/
theorem oneJunk_agree :
    oneNoAttack.args = oneJunkSelfAttack.args ∧
      ∀ a ∈ oneNoAttack.args, ∀ b ∈ oneNoAttack.args,
        oneNoAttack.attack a b = oneJunkSelfAttack.attack a b := by
  refine ⟨rfl, ?_⟩
  decide

/-- **`Grounded.ConflictFree` is not carrier-local.** The junk set `[0, 5]` is
conflict-free in `oneNoAttack` and not in `oneJunkSelfAttack`, even though the
two frameworks have the same carrier and agree on it. This is the D7 example
mechanized as a refutation: the bound cannot be moved out of `Admissible` into
the ambient quantifiers, because the very first conjunct that would be left
behind fails to transport. -/
theorem not_attackExtensional_conflictFree : ¬ AttackExtensional ConflictFree := by
  intro h
  have hcf : ConflictFree oneNoAttack [0, 5] := by
    intro a _ b _ hab
    simp [oneNoAttack] at hab
  have hcf' :=
    (h oneNoAttack oneJunkSelfAttack oneJunk_agree.1 oneJunk_agree.2 [0, 5]).mp hcf
  exact hcf' 5 (by decide) 5 (by decide) (by decide)

/-- The positive contrast, on the same pair of frameworks: `Admissible` *does*
transport there, so the failure above is specific to dropping the carrier bound
and not a defect of the frameworks chosen. -/
theorem admissible_transports_on_junk (S : List Arg) :
    Admissible oneNoAttack S ↔ Admissible oneJunkSelfAttack S :=
  attackExtensional_admissible oneNoAttack oneJunkSelfAttack
    oneJunk_agree.1 oneJunk_agree.2 S

/-! ### From carrier-local specifications to carrier-local observations

`AttackExtensional` is about `sem.spec`. `Semantics.observe` reads
`sem.enumerate` and the attack relation, not `spec`, so the lift is two steps:
adequacy (`ExtensionSemantics.sound`) moves the specification agreement onto the
enumerations, and the guards of `observe` are then shown to depend on the
enumeration only through its member set. -/

/-- Two lists with the same members give the same `List.all`, for predicates that
agree on those members. The three guards of `observe` are all `List.all` or
`List.isEmpty` over the enumeration, and the enumerations of two agreeing
frameworks are only known to have the same *members* — `ExtensionSemantics.sound`
characterizes membership and says nothing about order — so member-level lemmas
are the only ones available. -/
theorem all_congr_of_mem {α : Type _} {l₁ l₂ : List α} {p q : α → Bool}
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) (hpq : ∀ x ∈ l₁, p x = q x) :
    l₁.all p = l₂.all q := by
  refine Bool.eq_iff_iff.mpr ?_
  rw [List.all_eq_true, List.all_eq_true]
  constructor
  · intro h x hx
    have hx1 := (hmem x).mpr hx
    rw [← hpq x hx1]
    exact h x hx1
  · intro h x hx
    rw [hpq x hx]
    exact h x ((hmem x).mp hx)

/-- The companion for the emptiness guard: same members, same `isEmpty`. -/
theorem isEmpty_congr_of_mem {α : Type _} {l₁ l₂ : List α}
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.isEmpty = l₂.isEmpty := by
  cases l₁ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons y ys => exact absurd ((hmem y).mpr (by simp)) (by simp)
  | cons x xs =>
    cases l₂ with
    | nil => exact absurd ((hmem x).mp (by simp)) (by simp)
    | cons => rfl

/-- Every enumerated extension lies in the carrier. Read off `sound`'s sublist
component; it is what supplies the `Bounded` side condition that
`attackedByB_congr_af` needs at each enumerated extension. -/
theorem bounded_of_mem_enumerate (sem : ExtensionSemantics) {F : AF}
    (hnd : F.args.Nodup) {S : List Arg} (hS : S ∈ sem.enumerate F) : Bounded F S :=
  fun _ ha => ((sem.sound F hnd S).mp hS).1.subset ha

/-- **Specification agreement lifts to enumeration agreement.** `sound`
characterizes membership in `enumerate F` as "carrier sublist satisfying `spec`",
and both halves transport: the carrier is shared by hypothesis and the
specification by `AttackExtensional`. The `Nodup` hypothesis is `sound`'s own and
is not used for anything else here. -/
theorem enumerate_mem_congr (sem : ExtensionSemantics)
    (hext : AttackExtensional sem.spec) {F G : AF} (hargs : F.args = G.args)
    (hatt : ∀ a ∈ F.args, ∀ b ∈ F.args, F.attack a b = G.attack a b)
    (hnd : F.args.Nodup) (S : List Arg) :
    S ∈ sem.enumerate F ↔ S ∈ sem.enumerate G := by
  rw [sem.sound F hnd S, sem.sound G (hargs ▸ hnd) S, hargs]
  exact and_congr_right (fun _ => hext F G hargs hatt S)

/-- `Semantics.attackedByB` transports at a carrier target with a bounded
attacking set. Both side conditions are needed and neither is decorative: the
attacker ranges over `E`, which `hb` places in the carrier, and the target is the
argument `ha` names. `attackedByB` deliberately leaves its target unbounded (see
its docstring in `Lara.Semantics`), which is why `ha` has to be supplied by the
caller rather than derived. -/
theorem attackedByB_congr_af {F G : AF}
    (hatt : ∀ a ∈ F.args, ∀ b ∈ F.args, F.attack a b = G.attack a b)
    {E : List Arg} (hb : Bounded F E) {a : Arg} (ha : a ∈ F.args) :
    attackedByB F E a = attackedByB G E a := by
  refine Bool.eq_iff_iff.mpr ?_
  unfold attackedByB
  rw [List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨b, hbE, hba⟩ => ⟨b, hbE, (hatt b (hb b hbE) a ha).symm.trans hba⟩,
         fun ⟨b, hbE, hba⟩ => ⟨b, hbE, (hatt b (hb b hbE) a ha).trans hba⟩⟩

/-- Claim defeat transports under the same two side conditions, now with the
carrier bound demanded of the *claim's support* rather than derived. -/
theorem claimDefeatedB_congr_af {F G : AF}
    (hatt : ∀ a ∈ F.args, ∀ b ∈ F.args, F.attack a b = G.attack a b)
    {E : List Arg} (hb : Bounded F E) {c : Grounded.Claim}
    (hsupp : ∀ a ∈ c.support, a ∈ F.args) :
    claimDefeatedB F E c = claimDefeatedB G E c :=
  all_congr_of_mem (fun _ => Iff.rfl)
    (fun a ha => attackedByB_congr_af hatt hb (hsupp a ha))

/-- **The observation is carrier-local too.** Two frameworks with the same
carrier, agreeing on it, and a claim whose support lies in that carrier, receive
the same observation under any semantics whose specification is carrier-local.

`hsupp` is not removable: `not_observe_congr_of_unbounded_support` exhibits two
agreeing frameworks and a claim supported outside the carrier whose observations
differ. -/
theorem observe_congr (sem : ExtensionSemantics) (hext : AttackExtensional sem.spec)
    {F G : AF} (hargs : F.args = G.args)
    (hatt : ∀ a ∈ F.args, ∀ b ∈ F.args, F.attack a b = G.attack a b)
    (hnd : F.args.Nodup) (c : Grounded.Claim)
    (hsupp : ∀ a ∈ c.support, a ∈ F.args) :
    observe sem F c = observe sem G c := by
  have hmem := enumerate_mem_congr sem hext hargs hatt hnd
  have hempty : (sem.enumerate F).isEmpty = (sem.enumerate G).isEmpty :=
    isEmpty_congr_of_mem hmem
  have hacc : (sem.enumerate F).all (fun E => claimAcceptedB E c)
      = (sem.enumerate G).all (fun E => claimAcceptedB E c) :=
    all_congr_of_mem hmem (fun _ _ => rfl)
  have hdef : (sem.enumerate F).all (fun E => claimDefeatedB F E c)
      = (sem.enumerate G).all (fun E => claimDefeatedB G E c) :=
    all_congr_of_mem hmem
      (fun E hE => claimDefeatedB_congr_af hatt (bounded_of_mem_enumerate sem hnd hE) hsupp)
  unfold observe
  rw [hempty, hacc, hdef]

/-! ### The support bound is load-bearing too

`observe_congr` needs the claim's support inside the carrier. The witness below
shows why: the two frameworks agree everywhere the carrier can see, and differ
only on an edge whose target is undeclared — which is precisely where a claim
supported by an undeclared argument looks. -/

/-- The same carrier as `oneNoAttack`, and the same behaviour on it, but argument
`0` attacks the undeclared argument `7`. -/
def oneAttacksJunk : AF where
  args := [0]
  attack := fun a b => a == 0 && b == 7

/-- The two frameworks have the same carrier and agree on it. -/
theorem oneAttacksJunk_agree :
    oneNoAttack.args = oneAttacksJunk.args ∧
      ∀ a ∈ oneNoAttack.args, ∀ b ∈ oneNoAttack.args,
        oneNoAttack.attack a b = oneAttacksJunk.attack a b := by
  refine ⟨rfl, ?_⟩
  decide

/-- A claim supported by the undeclared argument `7`. -/
def claimJunkSupport : Grounded.Claim := { support := [7], holes := [] }

/-- **The support bound cannot be dropped from `observe_congr`.** Under
`groundedSem` the two agreeing frameworks report `contested` and `defeated` for
the same claim: the sole grounded extension is `[0]` in both, but `[0]` attacks
the support argument `7` in one framework and not in the other. Both observations
are computed by `decide`, so the separation is checked rather than argued. -/
theorem not_observe_congr_of_unbounded_support :
    observe groundedSem oneNoAttack claimJunkSupport
      ≠ observe groundedSem oneAttacksJunk claimJunkSupport := by
  decide

/-- **`observe_congr` without `hsupp` is false**, stated as the refutation rather
than left to the reader: the hypothesis-free version of the transport, applied to
`groundedSem` and the two agreeing frameworks above, would equate the two
observations that `not_observe_congr_of_unbounded_support` separates. -/
theorem observe_congr_needs_support_bound :
    ¬ (∀ (sem : ExtensionSemantics), AttackExtensional sem.spec →
        ∀ (F G : AF), F.args = G.args →
          (∀ a ∈ F.args, ∀ b ∈ F.args, F.attack a b = G.attack a b) →
          F.args.Nodup → ∀ c : Grounded.Claim, observe sem F c = observe sem G c) := by
  intro h
  exact not_observe_congr_of_unbounded_support
    (h groundedSem attackExtensional_leastComplete oneNoAttack oneAttacksJunk
      oneAttacksJunk_agree.1 oneAttacksJunk_agree.2 (by decide) claimJunkSupport)


/-! ### The compiled framework: what a faithful oracle pins down, and what it does not

`Compile.Faithful` has two fields. `agrees` says the oracle decides `Edge` at
declared argument positions; `ranged` says no edge touches an out-of-range index.
`faithful_unique` shows the pair is *rigid* — it determines the oracle as a
function — so a transport theorem hypothesising `Faithful` on both sides would be
a `funext` away and would exercise nothing. Every transport below therefore
assumes `agrees` only, under the name `AgreesOnArgs`; `faithful_unique` itself
and `agreesOnArgs_of_faithful` are the two exceptions, since their subject *is*
`Faithful`. -/

section Compiled

open Lara.Support

variable {canon : String → String} {Pi : RuleId → Option Rule}
  {Gamma : LeafId → Option Atom}
  {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
  {dp : Attack.DefeatPolicy}

/-- **The hypothesis actually used**: the oracle decides the frozen closure-edge
relation `Compile.Edge` at declared argument positions, and nothing is required
of it anywhere else. This is `Compile.Faithful.agrees` on its own, extracted so a
caller can supply it without owning a `ranged` proof — and so the theorems below
apply to frameworks that carry arbitrary junk edges among undeclared indices. -/
def AgreesOnArgs (P : Compile.CheckedProgram canon Pi Gamma CertOk dp)
    (edgeB : Nat → Nat → Bool) : Prop :=
  ∀ (i j : Nat) (a b : SupportTerm),
    P.args[i]? = some a → P.args[j]? = some b →
      (edgeB i j = true ↔ Compile.Edge P a b)

/-- Every faithful oracle agrees on declared arguments — the field projection,
named so the transport theorems can be applied to a `Faithful` witness. -/
theorem agreesOnArgs_of_faithful {P : Compile.CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hf : Compile.Faithful P edgeB) :
    AgreesOnArgs P edgeB :=
  hf.agrees

/-- The checker's own decider agrees on declared arguments, constructively —
`Compile.edgeB_faithful` supplies the witness, so no caller manufactures one. -/
theorem agreesOnArgs_edgeB (P : Compile.CheckedProgram canon Pi Gamma CertOk dp) :
    AgreesOnArgs P (Compile.edgeB P) :=
  agreesOnArgs_of_faithful (Compile.edgeB_faithful P)

/-- **Why the transport below is not stated over `Compile.Faithful`.** The two
`Faithful` fields together determine the oracle as a function: `ranged` forces
`false` outside the declared range, and `agrees` forces the `Edge` verdict
inside it, so any two faithful oracles for the same program are equal. A
transport theorem assuming `Faithful` on both sides could therefore be proved by
rewriting along this equality, and would say nothing about carrier-locality. The
results below assume only `AgreesOnArgs`, where this argument is unavailable. -/
theorem faithful_unique {P : Compile.CheckedProgram canon Pi Gamma CertOk dp}
    {e₁ e₂ : Nat → Nat → Bool}
    (h₁ : Compile.Faithful P e₁) (h₂ : Compile.Faithful P e₂) : e₁ = e₂ := by
  funext i j
  have key : ∀ f g : Nat → Nat → Bool, Compile.Faithful P f → Compile.Faithful P g →
      f i j = true → g i j = true := by
    intro f g hf hg hij
    obtain ⟨hi, hj⟩ := hf.ranged i j hij
    obtain ⟨a, ha⟩ := getElem?_some_of_lt P.args i hi
    obtain ⟨b, hb⟩ := getElem?_some_of_lt P.args j hj
    exact (hg.agrees i j a b ha hb).mpr ((hf.agrees i j a b ha hb).mp hij)
  cases hb1 : e₁ i j <;> cases hb2 : e₂ i j
  · rfl
  · exact absurd (key e₂ e₁ h₂ h₁ hb2) (by rw [hb1]; simp)
  · exact absurd (key e₁ e₂ h₁ h₂ hb1) (by rw [hb2]; simp)
  · rfl

/-- Membership in the compiled carrier is exactly being a declared position. The
carrier of `Compile.toAF` is `List.range P.args.length` by definition;
`List.mem_range` is quoted here and nowhere else in this module. (The two
`List.nodup_range` appeals below lean on the same definitional carrier, without
going through this lemma.) -/
theorem mem_toAF_args {P : Compile.CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} {i : Nat} :
    i ∈ (Compile.toAF P edgeB).args ↔ i < P.args.length :=
  List.mem_range

/-- **The carrier-local agreement of two `Edge`-deciding frameworks.** At a pair
of declared positions the two oracles decide the same `Edge` fact, hence return
the same `Bool`. Off the carrier they may differ arbitrarily, which is exactly
why the transport needs `AttackExtensional` rather than framework equality. -/
theorem toAF_attack_agree {P : Compile.CheckedProgram canon Pi Gamma CertOk dp}
    {e₁ e₂ : Nat → Nat → Bool} (h₁ : AgreesOnArgs P e₁) (h₂ : AgreesOnArgs P e₂) :
    ∀ i ∈ (Compile.toAF P e₁).args, ∀ j ∈ (Compile.toAF P e₁).args,
      (Compile.toAF P e₁).attack i j = (Compile.toAF P e₂).attack i j := by
  intro i hi j hj
  obtain ⟨a, ha⟩ := getElem?_some_of_lt P.args i (mem_toAF_args.mp hi)
  obtain ⟨b, hb⟩ := getElem?_some_of_lt P.args j (mem_toAF_args.mp hj)
  exact Bool.eq_iff_iff.mpr ((h₁ i j a b ha hb).trans (h₂ i j a b ha hb).symm)

/-- **The generic transport, proved once.** Any carrier-local specification takes
the same value on two compiled frameworks built from oracles that decide
`Compile.Edge` at declared positions. Every per-semantics corollary below is this
theorem applied to the corresponding `AttackExtensional` proof; nothing is
re-proved per instance. -/
theorem spec_congr_of_agreesOnArgs {spec : AF → List Arg → Prop}
    (hext : AttackExtensional spec)
    {P : Compile.CheckedProgram canon Pi Gamma CertOk dp}
    {e₁ e₂ : Nat → Nat → Bool} (h₁ : AgreesOnArgs P e₁) (h₂ : AgreesOnArgs P e₂)
    (S : List Arg) :
    spec (Compile.toAF P e₁) S ↔ spec (Compile.toAF P e₂) S :=
  hext (Compile.toAF P e₁) (Compile.toAF P e₂) rfl (toAF_attack_agree h₁ h₂) S

/-- The oracle-free form: transport onto `Compile.checkedAF`, which is
`Compile.toAF` at the checker's own decider. The second agreement hypothesis is
discharged by `agreesOnArgs_edgeB`, so a caller supplies only its own. -/
theorem spec_toAF_iff_checkedAF {spec : AF → List Arg → Prop}
    (hext : AttackExtensional spec)
    {P : Compile.CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hag : AgreesOnArgs P edgeB) (S : List Arg) :
    spec (Compile.toAF P edgeB) S ↔ spec (Compile.checkedAF P) S :=
  spec_congr_of_agreesOnArgs hext hag (agreesOnArgs_edgeB P) S

/-! ### The per-semantics corollaries -/

/-- Admissibility transports. -/
theorem admissible_toAF_iff_checkedAF
    {P : Compile.CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hag : AgreesOnArgs P edgeB) (S : List Arg) :
    Admissible (Compile.toAF P edgeB) S ↔ Admissible (Compile.checkedAF P) S :=
  spec_toAF_iff_checkedAF attackExtensional_admissible hag S

/-- The complete semantics transports. -/
theorem complete_toAF_iff_checkedAF
    {P : Compile.CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hag : AgreesOnArgs P edgeB) (S : List Arg) :
    Complete (Compile.toAF P edgeB) S ↔ Complete (Compile.checkedAF P) S :=
  spec_toAF_iff_checkedAF attackExtensional_complete hag S

/-- The stable semantics transports. -/
theorem stable_toAF_iff_checkedAF
    {P : Compile.CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hag : AgreesOnArgs P edgeB) (S : List Arg) :
    Stable (Compile.toAF P edgeB) S ↔ Stable (Compile.checkedAF P) S :=
  spec_toAF_iff_checkedAF attackExtensional_stable hag S

/-- The preferred semantics transports. -/
theorem preferred_toAF_iff_checkedAF
    {P : Compile.CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hag : AgreesOnArgs P edgeB) (S : List Arg) :
    Preferred (Compile.toAF P edgeB) S ↔ Preferred (Compile.checkedAF P) S :=
  spec_toAF_iff_checkedAF attackExtensional_preferred hag S

/-- The semi-stable semantics transports. -/
theorem semiStable_toAF_iff_checkedAF
    {P : Compile.CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hag : AgreesOnArgs P edgeB) (S : List Arg) :
    SemiStable (Compile.toAF P edgeB) S ↔ SemiStable (Compile.checkedAF P) S :=
  spec_toAF_iff_checkedAF attackExtensional_semiStable hag S

/-- The grounded semantics transports — its specification is `LeastComplete`, so
this is the same corollary at the sixth `AttackExtensional` proof. -/
theorem leastComplete_toAF_iff_checkedAF
    {P : Compile.CheckedProgram canon Pi Gamma CertOk dp}
    {edgeB : Nat → Nat → Bool} (hag : AgreesOnArgs P edgeB) (S : List Arg) :
    LeastComplete (Compile.toAF P edgeB) S ↔ LeastComplete (Compile.checkedAF P) S :=
  spec_toAF_iff_checkedAF attackExtensional_leastComplete hag S

/-! ### The claim-level deliverable

`Compile.SrcStatus` is a claim-and-answer relation that mentions no oracle: it is
read off `SrcIn`/`SrcOut`, which quantify over the frozen `Compile.Edge`
relation. `SrcObservation` is its observation analogue, and it is oracle-free in
the same sense — it says the answer is what *every* `Edge`-deciding framework
reports, so nothing about a particular compiled framework leaks into it. -/

/-- **The source-level claim observation.** `o` is the observation the source
program determines: every framework whose attack relation decides
`Compile.Edge P` at declared positions reports `o` for the claim `c` under `sem`.

Quantifying over the oracle rather than fixing one is what makes this a
*source-level* statement — the definition never names `Compile.edgeB`,
`Compile.checkedAF`, or any other compiled artefact. That the quantification is
non-vacuous, and that it collapses to a single framework's answer, is
`srcObservation_iff_checked`. -/
def SrcObservation (sem : ExtensionSemantics)
    (P : Compile.CheckedProgram canon Pi Gamma CertOk dp)
    (c : Grounded.Claim) (o : ClaimObservation) : Prop :=
  ∀ edgeB : Nat → Nat → Bool, AgreesOnArgs P edgeB →
    observe sem (Compile.toAF P edgeB) c = o

/-- **Source-to-framework observation preservation.** The mirror of
`Compile.srcStatus_iff_checked`: a source-level observation holds exactly for the
single observation the checker's own compiled framework returns.

The forward direction instantiates the source-level quantifier at
`Compile.edgeB P`, so it needs nothing beyond `agreesOnArgs_edgeB`. The reverse
direction is the transport, and needs both hypotheses: `hext` to move the
specification (hence the enumeration) between frameworks, and `hsupp` to move the
defeat guard, which reads the attack relation at the claim's support arguments.
The `Nodup` obligation of `ExtensionSemantics.sound` is discharged by
`List.nodup_range`, since `Compile.toAF`'s carrier is `List.range`. -/
theorem srcObservation_iff_checked (sem : ExtensionSemantics)
    (hext : AttackExtensional sem.spec)
    (P : Compile.CheckedProgram canon Pi Gamma CertOk dp) (c : Grounded.Claim)
    (hsupp : ∀ i ∈ c.support, i < P.args.length) (o : ClaimObservation) :
    SrcObservation sem P c o ↔ o = observe sem (Compile.checkedAF P) c := by
  constructor
  · intro h
    exact (h (Compile.edgeB P) (agreesOnArgs_edgeB P)).symm
  · rintro rfl edgeB hag
    exact observe_congr (F := Compile.toAF P edgeB) (G := Compile.checkedAF P)
      sem hext rfl (toAF_attack_agree hag (agreesOnArgs_edgeB P)) List.nodup_range c
      (fun i hi => mem_toAF_args.mpr (hsupp i hi))

/-- **Existence.** The observation the checker's framework returns is a source
observation — the analogue of `Compile.srcStatus_checked`, and the `mpr` half of
`srcObservation_iff_checked` applied at the reflexivity witness. -/
theorem srcObservation_checked (sem : ExtensionSemantics)
    (hext : AttackExtensional sem.spec)
    (P : Compile.CheckedProgram canon Pi Gamma CertOk dp) (c : Grounded.Claim)
    (hsupp : ∀ i ∈ c.support, i < P.args.length) :
    SrcObservation sem P c (observe sem (Compile.checkedAF P) c) :=
  (srcObservation_iff_checked sem hext P c hsupp _).mpr rfl

/-- **Functionality, with no hypotheses at all.** Unlike `srcObservation_checked`
this needs neither `hext` nor `hsupp`: `Compile.edgeB P` agrees on declared
arguments, so both source observations are pinned to that one framework's answer
and must coincide. The analogue of `Compile.srcStatus_unique`, which is likewise
proved without the oracle. -/
theorem srcObservation_unique {sem : ExtensionSemantics}
    {P : Compile.CheckedProgram canon Pi Gamma CertOk dp} {c : Grounded.Claim}
    {o₁ o₂ : ClaimObservation}
    (h₁ : SrcObservation sem P c o₁) (h₂ : SrcObservation sem P c o₂) : o₁ = o₂ := by
  rw [← h₁ (Compile.edgeB P) (agreesOnArgs_edgeB P),
    ← h₂ (Compile.edgeB P) (agreesOnArgs_edgeB P)]


/-- **How the frozen result 6 statement sits inside this one.** Under the
support bound, the source status relation of `Lara.Compile` and the `groundedSem`
source observation of this module hold of exactly the same claims.

Stated as an equivalence rather than as an instantiation, because it is not one:
`Compile.SrcStatus` is an inductive relation whose four constructors are built
from `SrcIn`/`SrcOut`, not from any extension enumeration, and
`Compile.srcStatus_iff_checked` carries no support-boundedness hypothesis. What
this theorem licenses is the reading "the grounded source observation of a
compiled claim is the source status", with `hsupp` named; it does not re-derive
`Compile.srcStatus_iff_checked`, which stands on its own proof and is unchanged
by this module. -/
theorem srcStatus_iff_srcObservation
    (P : Compile.CheckedProgram canon Pi Gamma CertOk dp) (c : Grounded.Claim)
    (hsupp : ∀ i ∈ c.support, i < P.args.length) (s : Grounded.Status) :
    Compile.SrcStatus P c s
      ↔ SrcObservation groundedSem P c (ClaimObservation.observed s) := by
  rw [srcObservation_iff_checked groundedSem attackExtensional_leastComplete P c hsupp,
    observe_grounded (F := Compile.checkedAF P) List.nodup_range c,
    Compile.srcStatus_iff_checked P c s]
  exact ⟨congrArg ClaimObservation.observed,
    fun h => ClaimObservation.observed.inj h⟩


end Compiled

end Lara.Observation
