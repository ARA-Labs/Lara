/-
# Multi-artifact maps, part 2 — the N-member fold

The mechanized half of `Lara.Map.Link` (issue #303). `Lara.Context.Link` proves
the linking calculus for a **two-sided** link: `link_attackComplete` shows the
saturated attack list satisfies `Compile.AttackComplete`, and `link_checked`
shows a well-linked composition of two well-formed sides is accepted by the
executable checker, with `SideOk` as the per-side hypothesis bundle.

A map has N members, so this module folds. `linkStep` merges one member into the
side accumulated so far and saturates the boundary between them; `linkMembers`
iterates it; `linkMembers_sideOk` proves by induction that the accumulated side
is itself a `SideOk` side, and `linkMembers_checked` hands the result to
`link_checked`. **Nothing about the argumentation semantics is restated** —
the induction step is exactly `link_attackComplete` for completeness,
`crossAtts_spec` for the saturation's typing, and `mem_dedupList` for the merge.

The invariant is carried at *each step's own environment* rather than at the
final one, and that direction is forced: `SideOk.mono_gamma` transports a side
into a **larger** Γ, so a member proved well-formed under its own declarations
can be moved into the accumulated environment, but not the other way round. The
freshness premise `FoldHygiene` is what licenses the right-hand move, and
`foldHygiene_of_distinct_aliases` discharges it from alias distinctness alone —
`qualifyGamma_disjoint` is the pairwise fact, and that theorem is the induction
from it to the whole accumulated side.

The fold's other premise splits, and it is worth being exact about where. Alias
distinctness discharges the **cross-member** half: two members cannot collide
after qualification, whatever each declares. It says nothing about a member
colliding with **itself**, and `linkMembers_declared_nodup` does not claim
otherwise — it takes each member's own `Nodup` as a hypothesis (and the
accumulator's), and proves the fold preserves it. So one of
`linkMembers_checked`'s two hygiene hypotheses is discharged from alias
distinctness alone and the other from alias distinctness *plus* each member's
own duplicate-freedom, which the map's loader establishes per member before any
of them becomes linkable.

## No monotonicity theorem, and a witness for why

There is deliberately **no** theorem here saying a member's claim keeps its
status when the map grows. There is none to prove: grounded status is not
preserved across framework extension, and that is the whole reason a map is
worth computing. `linkMembers_status_not_preserved` exhibits the failure
concretely — one accepted map in which a claim is `justified`, and one accepted
map, differing only by a member whose conclusion is a declared contrary of it,
in which the same claim is `defeated`.

`Lara.Examples` is imported for that witness alone. Re-deriving a second closed
fixture would be a second thing to keep in step with the checker for no gain,
and `Lara.Examples.Linking` already sets the precedent of building linking
witnesses on it.
-/

import Lara.Context.Link
import Lara.Map.Qualify
import Lara.Examples

namespace Lara.Map

open Lara.Support Lara.Attack Lara.Compile
open Lara.Context

/-! ### One fold step -/

/-- The environment a side declares on its own. After a step this is exactly the
`linkGamma` of that step, which is what lets the fold's invariant be stated at
the accumulated side rather than at the finished map. -/
def sideGamma (C : Lara.Context.Context) : LeafId → Option Atom :=
  Admission.buildGamma C.frame.gammaFrag

/-- **Merge one member into the accumulated side, and saturate the boundary.**

The material is `linkedUnit`'s, lifted back into a `Context` so the next member
can be folded onto it: the arguments are merged structurally, the two attack
lists are concatenated, and the cross-boundary conflicts between the accumulated
side and this member are completed. `Lara.Context.compose` is deliberately not
used — it does not saturate, so a composite of two members would carry no
cross-member attacks and could not satisfy `Compile.AttackComplete`.

`imports` is closed because a map member is a closed artifact: v1 refuses member
imports outright, and the fold's terminator relies on the accumulated side owing
nothing. -/
def linkStep {canon : String → String} (reg : BackendRegistry canon)
    (C : Lara.Context.Context) (F : Fragment) : Lara.Context.Context :=
  ⟨{ sigma     := F.sigma
   , policy    := F.policy
   , gammaFrag := C.frame.gammaFrag ++ F.gammaFrag
   , ground    := C.frame.ground ++ F.ground
   , args      := dedupList (C.frame.args ++ F.args)
   , atts      := C.frame.atts ++ F.atts ++ crossAtts reg (linkGamma C F) C F
   , imports   := Interface.closed
   , exports   := C.frame.exports ++ F.exports }⟩

/-- The step's own environment is the link's environment: the two sides'
declarations, in order. -/
theorem sideGamma_linkStep {canon : String → String} (reg : BackendRegistry canon)
    (C : Lara.Context.Context) (F : Fragment) :
    sideGamma (linkStep reg C F) = linkGamma C F := rfl

/-- **One step preserves `SideOk`.** Every field is the corresponding arm of
`Lara.Context.link_checked`'s proof, read as a side rather than as a unit:
support and the two endpoint conditions come from the two sides plus
`crossAtts_spec`, and attack completeness is `link_attackComplete` verbatim. -/
theorem linkStep_sideOk {canon : String → String} {reg : BackendRegistry canon}
    {C : Lara.Context.Context} {F : Fragment}
    (hC : SideOk canon reg (linkGamma C F) F.policy C.frame.args C.frame.atts)
    (hF : SideOk canon reg (linkGamma C F) F.policy F.args F.atts) :
    SideOk canon reg (linkGamma C F) F.policy
      (dedupList (C.frame.args ++ F.args))
      (C.frame.atts ++ F.atts ++ crossAtts reg (linkGamma C F) C F) where
  support := by
    intro w hw
    rcases List.mem_append.mp (mem_dedupList.mp hw) with h | h
    · exact hC.support w h
    · exact hF.support w h
  typed := by
    intro k hk
    rcases List.mem_append.mp hk with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact hC.typed k h'
      · exact hF.typed k h'
    · exact (crossAtts_spec h).1
  source_declared := by
    intro k hk
    rcases List.mem_append.mp hk with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact mem_dedupList.mpr (List.mem_append_left _ (hC.source_declared k h'))
      · exact mem_dedupList.mpr (List.mem_append_right _ (hF.source_declared k h'))
    · exact (crossAtts_spec h).2.1
  target_declared := by
    intro k hk
    rcases List.mem_append.mp hk with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact mem_dedupList.mpr (List.mem_append_left _ (hC.target_declared k h'))
      · exact mem_dedupList.mpr (List.mem_append_right _ (hF.target_declared k h'))
    · exact (crossAtts_spec h).2.2
  attack_complete := link_attackComplete hC hF

/-! ### The fold -/

/-- **Fold the members into one side.** Left-associated, in member order, which
is the order every deterministic map output is keyed by. -/
def linkMembers {canon : String → String} (reg : BackendRegistry canon) :
    Lara.Context.Context → List Fragment → Lara.Context.Context
  | C, [] => C
  | C, F :: Fs => linkMembers reg (linkStep reg C F) Fs

/-- **Identifier hygiene along the fold**: each member's declared leaf
identifiers are fresh for everything already accumulated.

This is R-L1's `idClash` class, stated once per step rather than pairwise, and
it is the premise `SideOk.mono_gamma` needs to carry a member's own derivations
into the accumulated environment (`Admission.buildGamma` is first-wins, so an
identifier already accumulated would shadow the member's own).

`foldHygiene_of_distinct_aliases` below proves it for a qualified map: it is a
consequence of alias distinctness, not something a map has to be trusted for. -/
def FoldHygiene {canon : String → String} (reg : BackendRegistry canon) :
    Lara.Context.Context → List Fragment → Prop
  | _, [] => True
  | C, F :: Fs =>
      (∀ l ∈ F.declared, l ∉ C.frame.declared) ∧ FoldHygiene reg (linkStep reg C F) Fs

/-- **The fold preserves `SideOk`.**

The three premises are the ones a map supplies: every member is checked on its
own (`hmembers`), the accumulated seed is a well-formed side (`hseed`), and the
members' identifiers do not clash (`hygiene`). Each member enters under its
*own* environment and is moved into the accumulated one by
`SideOk.mono_gamma`, which is why `hmembers` is stated at
`Admission.buildGamma F.gammaFrag` rather than at the finished map's Γ. -/
theorem linkMembers_sideOk {canon : String → String} {reg : BackendRegistry canon}
    {P : Policy.Policy} :
    ∀ (Fs : List Fragment) (C : Lara.Context.Context),
      (∀ F ∈ Fs, F.policy = P) →
      FoldHygiene reg C Fs →
      SideOk canon reg (sideGamma C) P C.frame.args C.frame.atts →
      (∀ F ∈ Fs, SideOk canon reg (Admission.buildGamma F.gammaFrag) P F.args F.atts) →
      SideOk canon reg (sideGamma (linkMembers reg C Fs)) P
        (linkMembers reg C Fs).frame.args (linkMembers reg C Fs).frame.atts
  | [], C, _, _, hseed, _ => hseed
  | F :: Fs, C, hpol, hyg, hseed, hmembers => by
      have hFP : F.policy = P := hpol F (List.mem_cons_self ..)
      -- The accumulated side moves right, into the linked environment: the
      -- linked Γ extends it by appending, and `buildGamma` is first-wins.
      have hCstep : SideOk canon reg (linkGamma C F) P C.frame.args C.frame.atts :=
        SideOk.mono_gamma (fun _ _ h => Admission.buildGamma_append_of_some _ _ h) hseed
      -- The member moves right too, and *this* direction is where hygiene is
      -- consumed: an identifier the accumulated side already declares would
      -- shadow the member's own.
      have hFstep : SideOk canon reg (linkGamma C F) P F.args F.atts := by
        refine SideOk.mono_gamma ?_ (hmembers F (List.mem_cons_self ..))
        intro l p h
        have hmem : l ∈ F.declared := Admission.buildGamma_some_mem h
        have hfresh : l ∉ C.frame.declared := hyg.1 l hmem
        rw [linkGamma, Admission.buildGamma_append_fresh _ _ hfresh]
        exact h
      have hstep :
          SideOk canon reg (sideGamma (linkStep reg C F)) P
            (linkStep reg C F).frame.args (linkStep reg C F).frame.atts := by
        rw [sideGamma_linkStep]
        exact hFP ▸ linkStep_sideOk (hFP ▸ hCstep) (hFP ▸ hFstep)
      exact linkMembers_sideOk Fs (linkStep reg C F)
        (fun G hG => hpol G (List.mem_cons_of_mem _ hG))
        hyg.2 hstep
        (fun G hG => hmembers G (List.mem_cons_of_mem _ hG))

/-! ### Closing the fold -/

/-- The fold's terminator: a closed fragment carrying only the shared contract.

`Lara.Context.link_checked` links a `Context` with a `Fragment`, so the finished
side is closed by linking it against a member that declares nothing. Everything
the guard asks of this side is then a property of the accumulated side alone,
and the saturation it triggers is empty because one of its two caches is. -/
def closedTail (sg : Sigma.Sigma) (P : Policy.Policy) : Fragment :=
  { sigma     := sg
  , policy    := P
  , gammaFrag := []
  , ground    := []
  , args      := []
  , atts      := []
  , imports   := Interface.closed
  , exports   := [] }

/-- The empty map: the shared contract and no members. -/
def emptyMap (sg : Sigma.Sigma) (P : Policy.Policy) : Lara.Context.Context :=
  ⟨closedTail sg P⟩

/-- Nothing is shared with a side that declares nothing. -/
theorem firstShared?_nil (xs : List LeafId) : firstShared? xs [] = none := by
  simp [firstShared?, List.find?_eq_none]

/-- **The terminator's guard reduces to the accumulated side's own hygiene.** -/
theorem linkOk_closedTail {sg : Sigma.Sigma} {P : Policy.Policy}
    {C : Lara.Context.Context}
    (hdup : firstDup? C.frame.declared = none)
    (himports : C.frame.imports.leaves = [])
    (hsigma : C.frame.sigma = sg) (hpolicy : C.frame.policy = P) :
    linkOk C (closedTail sg P) = true := by
  have hid : idHygieneFault C.frame (closedTail sg P) = none := by
    simp only [idHygieneFault, hdup]
    simp [closedTail, Fragment.declared, firstDup?, firstShared?_nil]
  simp only [linkOk, linkFault, hid]
  simp [closedTail, Interface.closed, firstMissing?, himports,
    Fragment.declared, sigmaPolicyFault, hsigma, hpolicy]

/-- A side that declares nothing is trivially well-formed. -/
theorem sideOk_closedTail {canon : String → String} {reg : BackendRegistry canon}
    {Gamma : LeafId → Option Atom} {P : Policy.Policy} :
    SideOk canon reg Gamma P [] [] where
  support := by intro w hw; simp at hw
  typed := by intro k hk; simp at hk
  source_declared := by intro k hk; simp at hk
  target_declared := by intro k hk; simp at hk
  attack_complete := by intro source hs; simp at hs

/-- **A folded map is accepted by the executable checker.**

`Lara.Context.link_checked`, instantiated at the folded side and the closed
terminator. The four premises it leaves open — the signature stage and the three
policy conditions — stay open here for the same reason they do there: no
structural property of linking can supply them, and in a map they are discharged
by the shared contract every member was compared against at load time.

**What this is about, and what it is not.** The conclusion is stated at
`linkedUnit reg (linkMembers reg C Fs) (closedTail sg P)` — a unit built by the
*fold*, where each `linkStep` saturates only the boundary between the
accumulated side and the incoming member. Neither driver builds it that way:
both saturate all pairs over the fully merged argument list in one pass
(`crossMemberAttacks` on the Haskell side, inline in `linkAndEvaluate` here),
and neither calls `linkMembers` or `linkStep`. The two coincide, because the
union of the fold's per-step cross-boundary pairs is exactly the ordered pairs
drawn from distinct members — but that is an argument in this comment, not a
theorem, so nothing here transfers to the drivers' unit by proof. The drivers'
saturation is covered by `scripts/check-map-conformance.sh`, which compares the
bytes both of them produce. Mechanizing the equivalence is issue #321.

`soloMap_linkMembers_checked` below discharges every premise at a concrete map,
so this is non-vacuous. -/
theorem linkMembers_checked {canon : String → String} {reg : BackendRegistry canon}
    {sg : Sigma.Sigma} {P : Policy.Policy}
    {C : Lara.Context.Context} {Fs : List Fragment}
    (hdup : firstDup? (linkMembers reg C Fs).frame.declared = none)
    (himports : (linkMembers reg C Fs).frame.imports.leaves = [])
    (hsigma : (linkMembers reg C Fs).frame.sigma = sg)
    (hpolicy' : (linkMembers reg C Fs).frame.policy = P)
    (hpol : ∀ F ∈ Fs, F.policy = P)
    (hyg : FoldHygiene reg C Fs)
    (hseed : SideOk canon reg (sideGamma C) P C.frame.args C.frame.atts)
    (hmembers : ∀ F ∈ Fs, SideOk canon reg (Admission.buildGamma F.gammaFrag) P F.args F.atts)
    (hsignature : Check.Unit.signatureStage
      (linkGround (linkMembers reg C Fs) (closedTail sg P))
      (linkedUnit reg (linkMembers reg C Fs) (closedTail sg P)) = none)
    (hscope : Policy.firstOutOfScope? P = none)
    (hruleIds : (P.rules.map (·.id)).Nodup)
    (hpolicyWf : Policy.WellFormed canon P) :
    ∃ accepted,
      Check.Unit.checkUnit (linkGamma (linkMembers reg C Fs) (closedTail sg P)) reg
        (linkGround (linkMembers reg C Fs) (closedTail sg P))
        (linkedUnit reg (linkMembers reg C Fs) (closedTail sg P)) = .ok accepted := by
  have hguard := linkOk_closedTail (sg := sg) (P := P) hdup himports hsigma hpolicy'
  have hfolded := linkMembers_sideOk (reg := reg) (P := P) Fs C hpol hyg hseed hmembers
  refine link_checked (link_eq_some hguard) hsignature hscope hruleIds hpolicyWf ?_ ?_
  · refine SideOk.mono_gamma ?_ hfolded
    intro l p h
    exact Admission.buildGamma_append_of_some _ _ h
  · exact sideOk_closedTail

/-! ### Discharging the fold's premises for a qualified map

`linkMembers_checked` takes `FoldHygiene` and `hdup` as premises, and those two
are exactly what decides whether it is instantiable for a real map. They are not
assumptions a map makes: they are consequences of alias qualification, and this
section is the induction from "the aliases are pairwise distinct" to "the fold's
premises hold". `qualifyGamma_disjoint` is the pairwise fact; what is needed is
the fact against the whole *accumulated* side, which grows by one member at each
step. -/

/-- A step declares what the accumulated side declared, then what the member
declares. -/
theorem linkStep_declared {canon : String → String} (reg : BackendRegistry canon)
    (C : Lara.Context.Context) (F : Fragment) :
    (linkStep reg C F).frame.declared = C.frame.declared ++ F.declared := by
  simp [linkStep, Fragment.declared]

/-- A folded map declares exactly the seed's identifiers followed by every
member's, in member order. -/
theorem linkMembers_declared {canon : String → String} (reg : BackendRegistry canon) :
    ∀ (Fs : List Fragment) (C : Lara.Context.Context),
      (linkMembers reg C Fs).frame.declared
        = C.frame.declared ++ Fs.flatMap Fragment.declared
  | [], C => by simp [linkMembers]
  | F :: Fs, C => by
      rw [linkMembers, linkMembers_declared reg Fs (linkStep reg C F),
        linkStep_declared, List.flatMap_cons, List.append_assoc]

/-- **Every identifier this member declares carries its own alias.** -/
def QualifiedBy (memberAlias : String) (F : Fragment) : Prop :=
  ∀ l ∈ F.declared, ∃ l₀, l = qualifyLeaf memberAlias l₀

/-- **Every identifier this side declares carries one of `as`.** The fold's
invariant: `as` is the aliases consumed so far. -/
def DeclaredBy (as : List String) (C : Lara.Context.Context) : Prop :=
  ∀ l ∈ C.frame.declared, ∃ a ∈ as, ∃ l₀, l = qualifyLeaf a l₀

/-- **Qualify a whole member by its alias**: its leaf environment, and every
argument and attack that refers to it, through one rename. The fragment-level
counterpart of `Lara.Map.Qualify.qualifyMember`, and what makes `mapLeaf`'s
transport results apply to a map member rather than to an arbitrary rename. -/
def qualifyFragment (memberAlias : String) (F : Fragment) : Fragment :=
  { F with
    gammaFrag := qualifyGamma memberAlias F.gammaFrag
  , args      := F.args.map (mapLeaf (qualifyLeaf memberAlias))
  , atts      := F.atts.map (mapLeafAtt (qualifyLeaf memberAlias)) }

theorem qualifyFragment_declared (memberAlias : String) (F : Fragment) :
    (qualifyFragment memberAlias F).declared
      = F.declared.map (qualifyLeaf memberAlias) := by
  simp [qualifyFragment, Fragment.declared, qualifyGamma, List.map_map]

/-- A qualified member is `QualifiedBy` its own alias, by construction. -/
theorem qualifiedBy_qualifyFragment (memberAlias : String) (F : Fragment) :
    QualifiedBy memberAlias (qualifyFragment memberAlias F) := by
  intro l hl
  rw [qualifyFragment_declared] at hl
  obtain ⟨l₀, _, he⟩ := List.mem_map.mp hl
  exact ⟨l₀, he.symm⟩

/-- **Pairwise-distinct aliases discharge the fold's hygiene premise.**

The induction the module header used to assert in prose. `as` accumulates the
aliases already folded in, `DeclaredBy` is the invariant that every identifier
the accumulated side declares carries one of them, and the step consumes
`qualifyLeaf_ne_of_alias_ne` once against the whole accumulated side rather than
against one prior member. -/
theorem foldHygiene_of_distinct_aliases {canon : String → String}
    (reg : BackendRegistry canon) (pairs : List (String × Fragment)) :
    ∀ (as : List String) (C : Lara.Context.Context),
      (pairs.map Prod.fst).Nodup →
      (∀ p ∈ pairs, QualifiedBy p.1 p.2) →
      (∀ p ∈ pairs, p.1 ∉ as) →
      DeclaredBy as C →
      FoldHygiene reg C (pairs.map Prod.snd) := by
  induction pairs with
  | nil => intro _ _ _ _ _ _; trivial
  | cons p rest ih =>
    obtain ⟨a, F⟩ := p
    intro as C hnodup hqual hfresh hdecl
    simp only [List.map_cons, List.nodup_cons] at hnodup
    refine ⟨?_, ?_⟩
    · intro l hl hmem
      obtain ⟨l₀, rfl⟩ := hqual (a, F) List.mem_cons_self l hl
      obtain ⟨a', ha', l₁, heq⟩ := hdecl _ hmem
      have hane : a ≠ a' := fun h => hfresh (a, F) List.mem_cons_self (h ▸ ha')
      exact qualifyLeaf_ne_of_alias_ne hane l₀ l₁ heq
    · refine ih (a :: as) (linkStep reg C F) hnodup.2
        (fun q hq => hqual q (List.mem_cons_of_mem _ hq)) ?_ ?_
      · intro q hq hin
        rcases List.mem_cons.mp hin with h | h
        · exact hnodup.1 (List.mem_map.mpr ⟨q, hq, h⟩)
        · exact hfresh q (List.mem_cons_of_mem _ hq) h
      · intro l hl
        rw [linkStep_declared] at hl
        rcases List.mem_append.mp hl with h | h
        · obtain ⟨a', ha', l₀, heq⟩ := hdecl l h
          exact ⟨a', List.mem_cons_of_mem _ ha', l₀, heq⟩
        · obtain ⟨l₀, heq⟩ := hqual (a, F) List.mem_cons_self l h
          exact ⟨a, List.mem_cons_self, l₀, heq⟩

/-- The same, for a map folded onto the empty seed: distinct aliases are then
the whole premise. -/
theorem foldHygiene_emptyMap {canon : String → String} (reg : BackendRegistry canon)
    {sg : Sigma.Sigma} {P : Policy.Policy} (pairs : List (String × Fragment))
    (hnodup : (pairs.map Prod.fst).Nodup)
    (hqual : ∀ p ∈ pairs, QualifiedBy p.1 p.2) :
    FoldHygiene reg (emptyMap sg P) (pairs.map Prod.snd) :=
  foldHygiene_of_distinct_aliases reg pairs [] (emptyMap sg P) hnodup hqual
    (fun _ _ => List.not_mem_nil)
    (by intro l hl; simp [emptyMap, closedTail, Fragment.declared] at hl)

/-! ### The second premise: the folded side declares nothing twice -/

/-- A step keeps `Nodup`, given the step's own hygiene. -/
theorem linkStep_declared_nodup {canon : String → String} {reg : BackendRegistry canon}
    {C : Lara.Context.Context} {F : Fragment}
    (hC : C.frame.declared.Nodup) (hF : F.declared.Nodup)
    (hfresh : ∀ l ∈ F.declared, l ∉ C.frame.declared) :
    (linkStep reg C F).frame.declared.Nodup := by
  rw [linkStep_declared]
  refine List.nodup_append.mpr ⟨hC, hF, ?_⟩
  intro x hx y hy hxy
  exact hfresh y hy (hxy ▸ hx)

/-- **The fold keeps `Nodup`**, which is `linkMembers_checked`'s `hdup` premise
read through `Lara.Context.firstDup?_none_iff`. -/
theorem linkMembers_declared_nodup {canon : String → String} (reg : BackendRegistry canon) :
    ∀ (Fs : List Fragment) (C : Lara.Context.Context),
      C.frame.declared.Nodup →
      (∀ F ∈ Fs, F.declared.Nodup) →
      FoldHygiene reg C Fs →
      (linkMembers reg C Fs).frame.declared.Nodup
  | [], _, hC, _, _ => hC
  | F :: Fs, C, hC, hmembers, hyg =>
      linkMembers_declared_nodup reg Fs (linkStep reg C F)
        (linkStep_declared_nodup hC (hmembers F List.mem_cons_self) hyg.1)
        (fun G hG => hmembers G (List.mem_cons_of_mem _ hG))
        hyg.2

/-- Qualification preserves a member's own duplicate-freedom: the rename is
injective within one member. -/
theorem qualifyFragment_declared_nodup {memberAlias : String} {F : Fragment}
    (h : F.declared.Nodup) : (qualifyFragment memberAlias F).declared.Nodup := by
  rw [qualifyFragment_declared]
  exact h.map (qualifyLeaf memberAlias)
    (fun _ _ hab habeq => hab (qualifyLeaf_injective memberAlias habeq))

/-- **The bridge is not vacuous.** Two members that are the *same* fragment under
two different aliases — the sharpest colliding case, every local identifier
shared — satisfy the fold's hygiene premise. -/
theorem foldHygiene_two_aliases_of_one_member {canon : String → String}
    (reg : BackendRegistry canon) {sg : Sigma.Sigma} {P : Policy.Policy} (F : Fragment) :
    FoldHygiene reg (emptyMap sg P)
      [qualifyFragment "pa" F, qualifyFragment "pb" F] :=
  foldHygiene_emptyMap reg
    [("pa", qualifyFragment "pa" F), ("pb", qualifyFragment "pb" F)]
    (by simp)
    (by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact qualifiedBy_qualifyFragment _ _
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact qualifiedBy_qualifyFragment _ _
        · exact absurd hp (by simp))

/-! ### Status is not preserved when a map grows

The concrete accepted witness. Two maps over the same shared contract, differing
by exactly one member, in which one claim atom takes two different statuses. -/

/-- The status a folded map assigns an atom, or `none` if the folded unit does
not check. -/
def mapStatus {canon : String → String} (reg : BackendRegistry canon)
    (L : Lara.Context.Context) (p : Atom) : Option Grounded.Status :=
  match Check.Unit.checkUnit (sideGamma L) reg L.frame.ground (fragmentUnit L.frame) with
  | .ok accepted => some (Invariants.status canon (Invariants.compileUnit accepted) p)
  | .error _ => none

/-- The member that asserts `p` from its own evidence leaf. -/
def memberP : Fragment :=
  { sigma     := Lara.Examples.sigmaEx
  , policy    := Lara.Examples.unitPolicyEx
  , gammaFrag := [(Lara.Examples.l1, Lara.Examples.pA)]
  , ground    := [Lara.Examples.pA]
  , args      := [.leaf Lara.Examples.l1]
  , atts      := []
  , imports   := Interface.closed
  , exports   := [Lara.Examples.pA] }

/-- The member that asserts `q`, which `unitPolicyEx` declares contrary to `p`.
It shares the contract and declares a disjoint leaf identifier, so it is an
ordinary further member — nothing about it is adversarial except its
conclusion. -/
def memberQ : Fragment :=
  { sigma     := Lara.Examples.sigmaEx
  , policy    := Lara.Examples.unitPolicyEx
  , gammaFrag := [(Lara.Examples.l2, Lara.Examples.pB)]
  , ground    := [Lara.Examples.pB]
  , args      := [.leaf Lara.Examples.l2]
  , atts      := []
  , imports   := Interface.closed
  , exports   := [] }

/-- The one-member map. -/
def soloMap : Lara.Context.Context :=
  linkMembers Lara.Examples.registryEx
    (emptyMap Lara.Examples.sigmaEx Lara.Examples.unitPolicyEx) [memberP]

/-- The same map with the contrary member added. -/
def contestedMap : Lara.Context.Context :=
  linkMembers Lara.Examples.registryEx
    (emptyMap Lara.Examples.sigmaEx Lara.Examples.unitPolicyEx) [memberP, memberQ]

/-- The second map is the first plus one member: nothing about `memberP` changed.
-/
theorem contestedMap_extends :
    contestedMap = linkStep Lara.Examples.registryEx soloMap memberQ := rfl

/-- The saturation is what the second map adds: one attack, which neither member
declared. -/
theorem contestedMap_atts :
    contestedMap.frame.atts = [Lara.Examples.kAtk] := by decide

/-- Both maps are accepted by the executable checker, so neither status below is
read off a rejected unit. -/
theorem soloMap_accepted :
    (Check.Unit.checkUnit (sideGamma soloMap) Lara.Examples.registryEx
      soloMap.frame.ground (fragmentUnit soloMap.frame)).isOk = true := by decide

theorem contestedMap_accepted :
    (Check.Unit.checkUnit (sideGamma contestedMap) Lara.Examples.registryEx
      contestedMap.frame.ground (fragmentUnit contestedMap.frame)).isOk = true := by decide

/-- In the one-member map the claim is `justified`. -/
theorem soloMap_status :
    mapStatus Lara.Examples.registryEx soloMap Lara.Examples.pA
      = some .justified := by decide

/-- In the two-member map the same claim is `defeated`. -/
theorem contestedMap_status :
    mapStatus Lara.Examples.registryEx contestedMap Lara.Examples.pA
      = some .defeated := by decide

/-! ### `linkMembers_checked` at a real map

`foldHygiene_two_aliases_of_one_member` makes `foldHygiene_of_distinct_aliases`
and `foldHygiene_emptyMap` non-vacuous, and says nothing about
`linkMembers_checked`'s other eleven premises. The two concrete maps above do not
close that gap either: `soloMap_accepted` and `contestedMap_accepted` check
`fragmentUnit L.frame` under `sideGamma L`, not `linkedUnit reg L (closedTail sg
P)` under `linkGamma`, so neither is an instantiation of the theorem.

This section exhibits all twelve premises holding together, which is what turns
`linkMembers_checked` from a true statement into one known to be about something.
-/

/-- `memberP` declares a leaf the empty map does not, which is the whole of
`FoldHygiene` for a one-member fold. -/
theorem memberP_foldHygiene :
    FoldHygiene Lara.Examples.registryEx
      (emptyMap Lara.Examples.sigmaEx Lara.Examples.unitPolicyEx) [memberP] := by
  refine ⟨?_, trivial⟩
  intro l hl
  simp [emptyMap, closedTail, Fragment.declared] at hl ⊢

/-- `memberP` is a well-formed side under its own environment: one complete
leaf argument, no attacks, and no conflict for an attack to have missed. -/
theorem memberP_sideOk :
    SideOk id Lara.Examples.registryEx
      (Admission.buildGamma memberP.gammaFrag) Lara.Examples.unitPolicyEx
      memberP.args memberP.atts where
  support := by
    intro w hw
    have hw1 : w = .leaf Lara.Examples.l1 := by simpa [memberP] using hw
    subst hw1
    exact ⟨Lara.Examples.pA, .leaf (by decide)⟩
  typed := by intro k hk; simp [memberP] at hk
  source_declared := by intro k hk; simp [memberP] at hk
  target_declared := by intro k hk; simp [memberP] at hk
  attack_complete := by
    intro source hs target ht Cs Ct hsSup htSup hcm _
    exfalso
    have hsEq : source = .leaf Lara.Examples.l1 := by simpa [memberP] using hs
    have htEq : target = .leaf Lara.Examples.l1 := by simpa [memberP] using ht
    subst hsEq; subst htEq
    have h1 : Cs = Lara.Examples.pA :=
      (Support.hasSupport_unique hsSup (.leaf (by decide))).1
    have h2 : Ct = Lara.Examples.pA :=
      (Support.hasSupport_unique htSup (.leaf (by decide))).1
    subst h1; subst h2
    exact absurd
      ((contraryMatchB_iff id Lara.Examples.unitPolicyEx.defeat
          Lara.Examples.pA Lara.Examples.pA).mpr hcm)
      (by decide)

/-- The shared contract satisfies §8.1, through `wfB`'s decision procedure. -/
theorem unitPolicyEx_wellFormed :
    Policy.WellFormed id Lara.Examples.unitPolicyEx :=
  (Policy.wfB_iff (canon := id) (P := Lara.Examples.unitPolicyEx)).mp (by decide)

/-- **`linkMembers_checked` instantiated at a real map**, every premise
discharged.

The witness is deliberately the *one*-member map: its job is to show the twelve
premises are simultaneously satisfiable, which one member settles. What it does
not do is exercise the fold's inductive step, and `contestedMap` is the
two-member witness that folding a second member changes an answer at all
(`linkMembers_status_not_preserved`). -/
theorem soloMap_linkMembers_checked :
    ∃ accepted,
      Check.Unit.checkUnit
        (linkGamma soloMap (closedTail Lara.Examples.sigmaEx Lara.Examples.unitPolicyEx))
        Lara.Examples.registryEx
        (linkGround soloMap (closedTail Lara.Examples.sigmaEx Lara.Examples.unitPolicyEx))
        (linkedUnit Lara.Examples.registryEx soloMap
          (closedTail Lara.Examples.sigmaEx Lara.Examples.unitPolicyEx))
        = .ok accepted :=
  linkMembers_checked
    (sg := Lara.Examples.sigmaEx) (P := Lara.Examples.unitPolicyEx)
    (C := emptyMap Lara.Examples.sigmaEx Lara.Examples.unitPolicyEx) (Fs := [memberP])
    (by decide) (by decide) (by decide) (by decide)
    (by decide)
    memberP_foldHygiene
    sideOk_closedTail
    (by
      intro F hF
      have : F = memberP := by simpa using hF
      subst this
      exact memberP_sideOk)
    (by decide) (by decide) (by decide)
    unitPolicyEx_wellFormed

/-- **Adding a member can change a claim's status, and both maps are accepted.**

There is therefore no monotonicity theorem to be had, and none is claimed
anywhere in this development: the whole point of computing a map is that a claim
justified in isolation need not survive its field. -/
theorem linkMembers_status_not_preserved :
    mapStatus Lara.Examples.registryEx soloMap Lara.Examples.pA
      ≠ mapStatus Lara.Examples.registryEx contestedMap Lara.Examples.pA := by
  rw [soloMap_status, contestedMap_status]
  decide

end Lara.Map
