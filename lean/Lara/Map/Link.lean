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

## The fold is not what the drivers run, and the two agree

Both drivers build a map's linked unit in one batch — merge every member's
arguments, then saturate all cross-member pairs under one cache computed in the
whole map's environment — and neither calls `linkMembers`. `Lara.Map.Batch` is
that construction and `Lara.Map.batch_checked` its acceptance theorem, stated up
to membership so that it applies to the drivers' own spelling of the unit;
`Lara.Map.Driver.linkedUnitOf_checked` instantiates it at the Lean driver's.
This module adds the agreement (issue #321): `linkMembers_emits` characterizes
what the fold produces by the shared `Lara.Map.Emits`, and
`batch_atts_mem_iff_fold` / `batch_args_mem_iff_fold` show the batch produces
the same arguments and the same attacks. It is not a reordering argument. Each
fold step computes its caches under the environment accumulated so far and the
batch computes one under the whole map's, so the agreement rests on a member's
argument having one conclusion in every environment that extends its own
(`support_between`) — which is where the members' well-formedness and the map's
hygiene are consumed.

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
import Lara.Map.Batch
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
(`crossMemberAttacks` on the Haskell side, `Lara.Map.Driver.generatedAttacksOf`
on the Lean side), and neither calls `linkMembers` or `linkStep`. That batch
construction has its own acceptance theorem, `Lara.Map.batch_checked`, proved
directly rather than transferred from this one, and `batch_atts_mem_iff_fold` /
`batch_args_mem_iff_fold` below show the two constructions produce the same
arguments and the same attacks (issue #321). `Lara.Map.Driver.linkedUnitOf_checked`
instantiates the batch theorem at the Lean driver's own linked unit. What stays
outside the proofs is the frontend's side of the boundary — that each member is
well-formed on its own is the solo check the Haskell loader runs, which no
envelope byte records — and the Haskell driver itself, which
`scripts/check-map-conformance.sh` ties to the Lean one by comparing the bytes
both produce.

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

/-- **Distinct aliases plus each member's own duplicate-freedom make the whole
map's declarations duplicate-free** — `Lara.Map.batch_checked`'s `hdecl`, for a
qualified map. The cross-member half is `qualifyLeaf_ne_of_alias_ne`; the
within-member half is the member's own `Nodup`, which the loader establishes. -/
theorem declared_nodup_of_qualified :
    ∀ (pairs : List (String × Fragment)), (pairs.map Prod.fst).Nodup →
      (∀ p ∈ pairs, QualifiedBy p.1 p.2) → (∀ p ∈ pairs, p.2.declared.Nodup) →
      (pairs.flatMap (·.2.declared)).Nodup
  | [], _, _, _ => by simp
  | r :: rest, haliases, hqual, hown => by
      rw [List.map_cons, List.nodup_cons] at haliases
      rw [List.flatMap_cons]
      refine List.nodup_append.mpr ⟨hown r List.mem_cons_self,
        declared_nodup_of_qualified rest haliases.2
          (fun p hp => hqual p (List.mem_cons_of_mem _ hp))
          (fun p hp => hown p (List.mem_cons_of_mem _ hp)), ?_⟩
      intro a ha b hb hab
      obtain ⟨q, hq, hbq⟩ := List.mem_flatMap.mp hb
      obtain ⟨l₀, rfl⟩ := hqual r List.mem_cons_self a ha
      obtain ⟨l₁, rfl⟩ := hqual q (List.mem_cons_of_mem _ hq) b hbq
      have hne : r.1 ≠ q.1 := by
        intro h
        apply haliases.1
        rw [h]
        exact List.mem_map.mpr ⟨q, hq, rfl⟩
      exact qualifyLeaf_ne_of_alias_ne hne l₀ l₁ hab

/-! ### The fold and the batch emit the same attacks (issue #321)

The drivers do not run the fold. They merge every member's arguments into one
list and saturate all cross-member pairs at once, under one cache computed in
the fully merged environment (`Lara.Map.Batch`). The two constructions differ in
more than enumeration order: each `linkStep` computes its caches under the
environment *accumulated so far*, where the batch uses the whole map's. They
still emit the same attacks, because a member's argument has one conclusion in
every environment that extends its own — `support_between`, which is
`SideOk.mono_gamma`'s monotonicity plus `Support.hasSupport_unique`, and which
is where the members' well-formedness and the map's hygiene are consumed.

`linkMembers_emits` characterizes what the fold produces by the shared
`Lara.Map.Emits`; `Lara.Map.mem_crossPairs_iff_emits` characterizes the batch
by the same predicate; `batch_atts_mem_iff_fold` and `batch_args_mem_iff_fold`
are the two meeting. -/

/-- **A member's argument has one conclusion in every environment extending its
own.** The step that lets a fold step's cache and the batch's cache be compared
at all. -/
private theorem support_between {canon : String → String} {reg : BackendRegistry canon}
    {P : Policy.Policy} {Γ₀ Γ₁ Γ₂ : LeafId → Option Atom}
    {args : List SupportTerm} {atts : List Attack}
    (hown : SideOk canon reg Γ₀ P args atts)
    (h₁ : ∀ l a, Γ₀ l = some a → Γ₁ l = some a)
    (h₂ : ∀ l a, Γ₀ l = some a → Γ₂ l = some a)
    {w : SupportTerm} (hw : w ∈ args) {X : Atom}
    (h : HasSupport canon P.ruleLookup Γ₁ (certOkOf reg) w X []) :
    HasSupport canon P.ruleLookup Γ₂ (certOkOf reg) w X [] := by
  obtain ⟨X₀, h₀⟩ := hown.support w hw
  have hX : X₀ = X := (hasSupport_unique (hasSupport_mono_gamma h₁ h₀) h).1
  subst hX
  exact hasSupport_mono_gamma h₂ h₀

/-- The fold's invariant. `done` are the members folded so far and `C` the side
accumulated from them: its environment is theirs, its arguments are theirs, and
its attacks are their own plus what `Emits` describes among them — under the
*whole* map's environment, which is the point. -/
private theorem fold_emits {canon : String → String} {reg : BackendRegistry canon}
    {P : Policy.Policy} (all : List (String × Fragment))
    (haliases : (all.map Prod.fst).Nodup)
    (hdecl : (all.flatMap (·.2.declared)).Nodup)
    (hpol : ∀ p ∈ all, p.2.policy = P)
    (hmembers : ∀ p ∈ all,
      SideOk canon reg (Admission.buildGamma p.2.gammaFrag) P p.2.args p.2.atts) :
    ∀ (todo done : List (String × Fragment)) (C : Lara.Context.Context),
      done ++ todo = all →
      C.frame.gammaFrag = done.flatMap (·.2.gammaFrag) →
      (∀ w, w ∈ C.frame.args ↔ ∃ p ∈ done, w ∈ p.2.args) →
      (∀ k, k ∈ C.frame.atts ↔
        (∃ p ∈ done, k ∈ p.2.atts) ∨ Emits reg P (batchGamma all) done k) →
      (∀ w, w ∈ (linkMembers reg C (todo.map Prod.snd)).frame.args ↔
        ∃ p ∈ all, w ∈ p.2.args) ∧
      (∀ k, k ∈ (linkMembers reg C (todo.map Prod.snd)).frame.atts ↔
        (∃ p ∈ all, k ∈ p.2.atts) ∨ Emits reg P (batchGamma all) all k)
  | [], done, C, hsplit, _, hargs, hatts => by
      rw [List.append_nil] at hsplit
      subst hsplit
      exact ⟨hargs, hatts⟩
  | r :: rest, done, C, hsplit, hgf, hargs, hatts => by
      have hsplit' : (done ++ [r]) ++ rest = all := by simpa using hsplit
      have hr : r ∈ all := hsplit ▸ List.mem_append_right _ List.mem_cons_self
      have hstepAll : ∀ p ∈ done ++ [r], p ∈ all :=
        fun p hp => hsplit' ▸ List.mem_append_left _ hp
      have hP : r.2.policy = P := hpol r hr
      have hΓs : linkGamma C r.2 = batchGamma (done ++ [r]) := by
        simp only [linkGamma, batchGamma, hgf, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
      have hdeclStep : ((done ++ [r]).flatMap (·.2.declared)).Nodup := by
        rw [← hsplit', List.flatMap_append] at hdecl
        exact (List.nodup_append.mp hdecl).1
      have hne : ∀ p ∈ done, p.1 ≠ r.1 := by
        rw [← hsplit, List.map_append] at haliases
        intro p hp he
        exact (List.nodup_append.mp haliases).2.2 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
          r.1 (by simp) he
      have hextStep : ∀ p ∈ done ++ [r], ∀ l a,
          Admission.buildGamma p.2.gammaFrag l = some a → linkGamma C r.2 l = some a := by
        intro p hp l a h
        rw [hΓs]
        exact batchGamma_extends hdeclStep hp l a h
      have hextAll : ∀ p ∈ all, ∀ l a,
          Admission.buildGamma p.2.gammaFrag l = some a → batchGamma all l = some a :=
        fun p hp => batchGamma_extends hdecl hp
      have toAll : ∀ p ∈ done ++ [r], ∀ w ∈ p.2.args, ∀ X,
          HasSupport canon P.ruleLookup (linkGamma C r.2) (certOkOf reg) w X [] →
          HasSupport canon P.ruleLookup (batchGamma all) (certOkOf reg) w X [] :=
        fun p hp w hw _ h =>
          support_between (hmembers p (hstepAll p hp)) (hextStep p hp)
            (hextAll p (hstepAll p hp)) hw h
      have toStep : ∀ p ∈ done ++ [r], ∀ w ∈ p.2.args, ∀ X,
          HasSupport canon P.ruleLookup (batchGamma all) (certOkOf reg) w X [] →
          HasSupport canon P.ruleLookup (linkGamma C r.2) (certOkOf reg) w X [] :=
        fun p hp w hw _ h =>
          support_between (hmembers p (hstepAll p hp)) (hextAll p (hstepAll p hp))
            (hextStep p hp) hw h
      have hrStep : r ∈ done ++ [r] := List.mem_append_right _ (List.mem_singleton_self _)
      -- The accumulated side's cache, read in the whole map's environment.
      have hcc : ∀ s : SupportTerm × Atom,
          s ∈ conclusionCache P.ruleLookup (linkGamma C r.2) reg C.frame.args ↔
            ∃ p ∈ done, s.1 ∈ p.2.args ∧
              HasSupport canon P.ruleLookup (batchGamma all) (certOkOf reg) s.1 s.2 [] := by
        intro s
        show (s.1, s.2) ∈ _ ↔ _
        rw [mem_conclusionCache]
        constructor
        · rintro ⟨hs, hsup⟩
          obtain ⟨p, hp, hsp⟩ := (hargs s.1).mp hs
          exact ⟨p, hp, hsp, toAll p (List.mem_append_left _ hp) s.1 hsp s.2 hsup⟩
        · rintro ⟨p, hp, hsp, hsup⟩
          exact ⟨(hargs s.1).mpr ⟨p, hp, hsp⟩,
            toStep p (List.mem_append_left _ hp) s.1 hsp s.2 hsup⟩
      -- The incoming member's cache, likewise.
      have hcf : ∀ s : SupportTerm × Atom,
          s ∈ conclusionCache P.ruleLookup (linkGamma C r.2) reg r.2.args ↔
            s.1 ∈ r.2.args ∧
              HasSupport canon P.ruleLookup (batchGamma all) (certOkOf reg) s.1 s.2 [] := by
        intro s
        show (s.1, s.2) ∈ _ ↔ _
        rw [mem_conclusionCache]
        constructor
        · rintro ⟨hs, hsup⟩
          exact ⟨hs, toAll r hrStep s.1 hs s.2 hsup⟩
        · rintro ⟨hs, hsup⟩
          exact ⟨hs, toStep r hrStep s.1 hs s.2 hsup⟩
      refine fold_emits all haliases hdecl hpol hmembers rest (done ++ [r])
        (linkStep reg C r.2) hsplit' ?_ ?_ ?_
      · show C.frame.gammaFrag ++ r.2.gammaFrag = _
        rw [hgf, List.flatMap_append]
        simp
      · intro w
        show w ∈ dedupList (C.frame.args ++ r.2.args) ↔ _
        rw [mem_dedupList, List.mem_append, hargs]
        constructor
        · rintro (⟨p, hp, hw⟩ | hw)
          · exact ⟨p, List.mem_append_left _ hp, hw⟩
          · exact ⟨r, hrStep, hw⟩
        · rintro ⟨p, hp, hw⟩
          rcases List.mem_append.mp hp with hp | hp
          · exact Or.inl ⟨p, hp, hw⟩
          · obtain rfl := List.mem_singleton.mp hp
            exact Or.inr hw
      · intro k
        show k ∈ C.frame.atts ++ r.2.atts ++ crossAtts reg (linkGamma C r.2) C r.2 ↔ _
        simp only [crossAtts]
        rw [hP]
        constructor
        · intro hk
          rcases List.mem_append.mp hk with hk | hk
          · rcases List.mem_append.mp hk with hk | hk
            · rcases (hatts k).mp hk with ⟨p, hp, hkp⟩ | hem
              · exact Or.inl ⟨p, List.mem_append_left _ hp, hkp⟩
              · exact Or.inr (hem.mono (fun p hp => List.mem_append_left _ hp))
            · exact Or.inl ⟨r, hrStep, hk⟩
          · right
            rcases List.mem_append.mp hk with hk | hk
            · obtain ⟨s, hs, t, ht, hcm, hca, rfl⟩ := mem_crossAttsFrom.mp hk
              obtain ⟨p, hp, hsp, hsSup⟩ := (hcc s).mp hs
              obtain ⟨htr, htSup⟩ := (hcf t).mp ht
              exact ⟨p, List.mem_append_left _ hp, r, hrStep, hne p hp, s.1, hsp, t.1, htr,
                s.2, t.2, hsSup, htSup, hcm, hca, rfl⟩
            · obtain ⟨s, hs, t, ht, hcm, hca, rfl⟩ := mem_crossAttsFrom.mp hk
              obtain ⟨hsr, hsSup⟩ := (hcf s).mp hs
              obtain ⟨q, hq, htq, htSup⟩ := (hcc t).mp ht
              exact ⟨r, hrStep, q, List.mem_append_left _ hq, fun h => hne q hq h.symm,
                s.1, hsr, t.1, htq, s.2, t.2, hsSup, htSup, hcm, hca, rfl⟩
        · rintro (⟨p, hp, hkp⟩ |
            ⟨p, hp, q, hq, hpq, s, hsp, t, htq, Cs, Ct, hsSup, htSup, hcm, hca, rfl⟩)
          · rcases List.mem_append.mp hp with hp | hp
            · exact List.mem_append_left _
                (List.mem_append_left _ ((hatts k).mpr (Or.inl ⟨p, hp, hkp⟩)))
            · obtain rfl := List.mem_singleton.mp hp
              exact List.mem_append_left _ (List.mem_append_right _ hkp)
          · rcases List.mem_append.mp hp with hpd | hpr <;>
              rcases List.mem_append.mp hq with hqd | hqr
            · exact List.mem_append_left _ (List.mem_append_left _ ((hatts _).mpr
                (Or.inr ⟨p, hpd, q, hqd, hpq, s, hsp, t, htq, Cs, Ct, hsSup, htSup, hcm,
                  hca, rfl⟩)))
            · obtain rfl := List.mem_singleton.mp hqr
              exact List.mem_append_right _ (List.mem_append_left _
                (mem_crossAttsFrom.mpr ⟨(s, Cs), (hcc (s, Cs)).mpr ⟨p, hpd, hsp, hsSup⟩,
                  (t, Ct), (hcf (t, Ct)).mpr ⟨htq, htSup⟩, hcm, hca, rfl⟩))
            · obtain rfl := List.mem_singleton.mp hpr
              exact List.mem_append_right _ (List.mem_append_right _
                (mem_crossAttsFrom.mpr ⟨(s, Cs), (hcf (s, Cs)).mpr ⟨hsp, hsSup⟩,
                  (t, Ct), (hcc (t, Ct)).mpr ⟨q, hqd, htq, htSup⟩, hcm, hca, rfl⟩))
            · exact absurd (by rw [List.mem_singleton.mp hpr, List.mem_singleton.mp hqr]) hpq

/-- **What the fold produces, characterized.** For a map folded onto the empty
seed, the folded side's arguments are exactly the members' arguments, and its
attacks are exactly the members' own attacks plus the ones `Emits` describes
under the whole map's environment.

The premises are `Lara.Map.batch_checked`'s hygiene and well-formedness
premises (pairwise-distinct aliases, duplicate-free declarations across the map,
and each member well-formed under its own environment) plus one it does not
take: `hpol`, that every member carries the shared policy. The fold reads each
member's own policy at every step, which `batch_checked` never does, so the
premise belongs to the fold; `linkMembers_checked` takes it for the same
reason. -/
theorem linkMembers_emits {canon : String → String} {reg : BackendRegistry canon}
    {sg : Sigma.Sigma} {P : Policy.Policy} (pairs : List (String × Fragment))
    (haliases : (pairs.map Prod.fst).Nodup)
    (hdecl : (pairs.flatMap (·.2.declared)).Nodup)
    (hpol : ∀ p ∈ pairs, p.2.policy = P)
    (hmembers : ∀ p ∈ pairs,
      SideOk canon reg (Admission.buildGamma p.2.gammaFrag) P p.2.args p.2.atts) :
    (∀ w, w ∈ (linkMembers reg (emptyMap sg P) (pairs.map Prod.snd)).frame.args ↔
      ∃ p ∈ pairs, w ∈ p.2.args) ∧
    (∀ k, k ∈ (linkMembers reg (emptyMap sg P) (pairs.map Prod.snd)).frame.atts ↔
      (∃ p ∈ pairs, k ∈ p.2.atts) ∨ Emits reg P (batchGamma pairs) pairs k) :=
  fold_emits pairs haliases hdecl hpol hmembers pairs [] (emptyMap sg P) (by simp)
    (by simp [emptyMap, closedTail])
    (by intro w; simp [emptyMap, closedTail])
    (by intro k; simp [emptyMap, closedTail, Emits])

/-- **The batch emits exactly the fold's attacks** (issue #321): the drivers'
all-pairs saturation over the merged arguments, with the reference
cross-member predicate `ownedApart`, and the fold's per-step boundary
saturation produce the same attack set. Order and multiplicity differ, and
neither is observable to the checker, whose every premise is membership-based
(`Lara.Map.batch_checked`). -/
theorem batch_atts_mem_iff_fold {canon : String → String} {reg : BackendRegistry canon}
    {sg : Sigma.Sigma} {P : Policy.Policy} (pairs : List (String × Fragment))
    (haliases : (pairs.map Prod.fst).Nodup)
    (hdecl : (pairs.flatMap (·.2.declared)).Nodup)
    (hpol : ∀ p ∈ pairs, p.2.policy = P)
    (hmembers : ∀ p ∈ pairs,
      SideOk canon reg (Admission.buildGamma p.2.gammaFrag) P p.2.args p.2.atts)
    (k : Attack) :
    k ∈ batchAtts reg P (ownedApart pairs) pairs ↔
      k ∈ (linkMembers reg (emptyMap sg P) (pairs.map Prod.snd)).frame.atts := by
  rw [mem_batchAtts, mem_crossPairs_iff_emits (fun _ _ => ownedApart_iff)
      (fun _ => mem_batchArgs),
    (linkMembers_emits (sg := sg) pairs haliases hdecl hpol hmembers).2 k]

/-- **The batch merges exactly the fold's arguments.** -/
theorem batch_args_mem_iff_fold {canon : String → String} {reg : BackendRegistry canon}
    {sg : Sigma.Sigma} {P : Policy.Policy} (pairs : List (String × Fragment))
    (haliases : (pairs.map Prod.fst).Nodup)
    (hdecl : (pairs.flatMap (·.2.declared)).Nodup)
    (hpol : ∀ p ∈ pairs, p.2.policy = P)
    (hmembers : ∀ p ∈ pairs,
      SideOk canon reg (Admission.buildGamma p.2.gammaFrag) P p.2.args p.2.atts)
    (w : SupportTerm) :
    w ∈ batchArgs pairs ↔
      w ∈ (linkMembers reg (emptyMap sg P) (pairs.map Prod.snd)).frame.args := by
  rw [mem_batchArgs, (linkMembers_emits (sg := sg) pairs haliases hdecl hpol hmembers).1 w]

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

/-! ### The batch construction at a real map

`contestedMap`'s two members, under two aliases, handed to the construction the
drivers run. The batch saturation produces exactly the one attack the fold did
(`contestedMap_atts`), and every premise of `Lara.Map.batchUnit_checked`
discharges, so `Lara.Map.batch_checked` is known to be about something — and at
a map that exercises the saturation, which the one-member witness above does
not. -/

/-- `memberQ` is a well-formed side under its own environment. -/
theorem memberQ_sideOk :
    SideOk id Lara.Examples.registryEx
      (Admission.buildGamma memberQ.gammaFrag) Lara.Examples.unitPolicyEx
      memberQ.args memberQ.atts where
  support := by
    intro w hw
    have hw1 : w = .leaf Lara.Examples.l2 := by simpa [memberQ] using hw
    subst hw1
    exact ⟨Lara.Examples.pB, .leaf (by decide)⟩
  typed := by intro k hk; simp [memberQ] at hk
  source_declared := by intro k hk; simp [memberQ] at hk
  target_declared := by intro k hk; simp [memberQ] at hk
  attack_complete := by
    intro source hs target ht Cs Ct hsSup htSup hcm _
    exfalso
    have hsEq : source = .leaf Lara.Examples.l2 := by simpa [memberQ] using hs
    have htEq : target = .leaf Lara.Examples.l2 := by simpa [memberQ] using ht
    subst hsEq; subst htEq
    have h1 : Cs = Lara.Examples.pB :=
      (Support.hasSupport_unique hsSup (.leaf (by decide))).1
    have h2 : Ct = Lara.Examples.pB :=
      (Support.hasSupport_unique htSup (.leaf (by decide))).1
    subst h1; subst h2
    exact absurd
      ((contraryMatchB_iff id Lara.Examples.unitPolicyEx.defeat
          Lara.Examples.pB Lara.Examples.pB).mpr hcm)
      (by decide)

/-- `contestedMap`'s members, under two aliases. -/
def contestedPairs : List (String × Fragment) := [("pa", memberP), ("pb", memberQ)]

/-- **The batch saturation emits exactly the fold's one attack** at this map —
the list `contestedMap_atts` reads off the fold. -/
theorem contestedPairs_batchAtts :
    batchAtts Lara.Examples.registryEx Lara.Examples.unitPolicyEx
      (ownedApart contestedPairs) contestedPairs = [Lara.Examples.kAtk] := by decide

/-- **`Lara.Map.batch_checked` instantiated at a real two-member map**, every
premise discharged. -/
theorem contestedPairs_batchUnit_checked :
    ∃ accepted,
      Check.Unit.checkUnit (batchGamma contestedPairs) Lara.Examples.registryEx
        (contestedPairs.flatMap (·.2.ground))
        (batchUnit Lara.Examples.registryEx Lara.Examples.sigmaEx
          Lara.Examples.unitPolicyEx (ownedApart contestedPairs) contestedPairs)
        = .ok accepted :=
  batchUnit_checked contestedPairs (ownedApart contestedPairs) _
    (by decide) (by decide)
    (by
      intro p hp
      simp only [contestedPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact memberP_sideOk
      · exact memberQ_sideOk)
    (fun p hp q hq hne s hs t ht => ownedApart_iff.mpr ⟨p, hp, q, hq, hne, hs, ht⟩)
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
