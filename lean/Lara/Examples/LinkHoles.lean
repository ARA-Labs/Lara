/-
# Linking with located holes — executable witnesses (issue #13)

The hole-aware linking results of `Lara.Context.Link`, `Lara.Context.LinkHoles`
and `Lara.Context.Equivalence` are conditional; this module instantiates them
on the `Lara.Examples.Linking` split (the context declares `l2 : q`, the
fragment `l1 : p`, and `q` is contrary to `p`) and records the one statement
that is false with holes.

* `holeFrag` adds the located hole `tMix` (conclusion `p`, open mandatory
  question `q1`) to the fragment. It satisfies `SideOkHoles` but not `SideOk`,
  the link is admissible and accepted *by theorem* (`link_checked_holes` through
  `exists_accepted_of_admissible`), the hole is reported with exactly its
  fragment-side obligations, and — by `obs_hole_blind` — the observation equals
  that of the hole-free fragment in every context admissible for both.
* `hole_erasure_observable` is the counterexample to "units that differ only in
  their holes are observationally equivalent". `d6Frag` covers the conflict
  between its complete arguments `vWrap : q` and `l1 : p` only through an attack
  aimed inside its hole `tHolePair` (D6); deleting the hole and that attack keeps
  the complete arguments but drops the cover, and the link is rejected. The
  corrected statement is `obs_hole_blind`, whose live-attack premise this pair
  violates (`erasure_changes_live_attacks`).
-/

import Lara.Examples.Linking

namespace Lara.Examples.LinkHoles

open Lara.Support Lara.Attack Lara.Compile Lara.Check
open Lara.Context hiding Context
open Lara.Examples.Linking

/-! ### A fragment carrying a located hole -/

/-- `fragEx` plus the located hole `tMix`: an open instance of `ruleMix`
concluding `p` with the mandatory question `q1` left open. -/
def holeFrag : Fragment := { fragEx with args := [.leaf l1, tMix] }

theorem tMix_hole :
    HasSupport id unitPolicyEx.ruleLookup (linkGamma ctxEx holeFrag) (certOkOf registryEx)
      tMix pA [q1] := by
  have h : inferSupport unitPolicyEx.ruleLookup (linkGamma ctxEx holeFrag) registryEx
      .root tMix = .ok ⟨pA, [q1]⟩ := by rfl
  exact inferSupport_sound h

/-- The fragment with a hole is linkable in the hole-aware sense. -/
theorem holeFrag_sideOkHoles :
    SideOkHoles id registryEx (linkGamma ctxEx holeFrag) unitPolicyEx
      holeFrag.args holeFrag.atts where
  support := by
    intro w hw
    have hw' : w = .leaf l1 ∨ w = tMix := by simpa [holeFrag] using hw
    rcases hw' with rfl | rfl
    · exact ⟨pA, [], leaf1_checked _⟩
    · exact ⟨pA, [q1], tMix_hole⟩
  typed := by intro k hk; simp [holeFrag, fragEx] at hk
  source_declared := by intro k hk; simp [holeFrag, fragEx] at hk
  target_declared := by intro k hk; simp [holeFrag, fragEx] at hk
  attack_complete := by
    intro source hs target ht Cs Ct hsSup htSup hcm _
    exfalso
    have hcomplete : ∀ {w : SupportTerm} {A : Atom}, w ∈ holeFrag.args →
        HasSupport id unitPolicyEx.ruleLookup (linkGamma ctxEx holeFrag)
          (certOkOf registryEx) w A [] → w = .leaf l1 ∧ A = pA := by
      intro w A hw hA
      have hw' : w = .leaf l1 ∨ w = tMix := by simpa [holeFrag] using hw
      rcases hw' with rfl | rfl
      · exact ⟨rfl, (hasSupport_unique hA (leaf1_checked _)).1⟩
      · exact absurd (hasSupport_unique hA tMix_hole).2 (by simp)
    obtain ⟨-, rfl⟩ := hcomplete hs hsSup
    obtain ⟨-, rfl⟩ := hcomplete ht htSup
    exact absurd ((contraryMatchB_iff id unitPolicyEx.defeat pA pA).mpr hcm) (by decide)

/-- The hole makes the hole-free side condition fail: `SideOk` is strictly
stronger than `SideOkHoles`. -/
theorem holeFrag_not_sideOk :
    ¬ SideOk id registryEx (linkGamma ctxEx holeFrag) unitPolicyEx
      holeFrag.args holeFrag.atts := by
  intro h
  obtain ⟨A, hA⟩ := h.support tMix (by simp [holeFrag])
  exact absurd (hasSupport_unique hA tMix_hole).2 (by simp)

/-- The context is admissible for the fragment with a hole. -/
theorem admissible_hole : Admissible registryEx ctxEx holeFrag where
  guard := by decide
  ctx := (sideOk_ctx registryEx).toHoles
  frag := holeFrag_sideOkHoles
  signature :=
    signatureStage_link (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  scope := by decide
  ruleIds := by decide
  policy := Policy.firstViolation_none_iff.mp (by decide)

/-- **`link_checked_holes`, instantiated.** The link of a context with a
fragment carrying a located hole is accepted by theorem. -/
theorem link_checked_hole :
    ∃ accepted, Check.Unit.checkUnit (linkGamma ctxEx holeFrag) registryEx
      (linkGround ctxEx holeFrag) (linkedUnit registryEx ctxEx holeFrag) = .ok accepted :=
  exists_accepted_of_admissible admissible_hole

/-- **The accepted link, by theorem.** Its AF arguments are the two sides'
complete arguments, its only hole is `tMix`, and the hole is reported with the
obligation set `[q1]` the fragment gives it. -/
theorem link_hole_accepted :
    ∃ accepted, Check.Unit.checkUnit (linkGamma ctxEx holeFrag) registryEx
        (linkGround ctxEx holeFrag) (linkedUnit registryEx ctxEx holeFrag) = .ok accepted ∧
      accepted.program.args = [.leaf l2, .leaf l1] ∧
      accepted.program.holes = [tMix] ∧
      ∃ h ∈ accepted.holes, h.term = tMix ∧ h.conclusion = pA ∧ h.obligations = [q1] := by
  obtain ⟨accepted, hacc⟩ := link_checked_hole
  obtain ⟨hargs, hholes, -⟩ :=
    link_accepted_holes (link_eq_some admissible_hole.guard) hacc
      admissible_hole.ctx admissible_hole.frag
  refine ⟨accepted, hacc, ?_, ?_, ?_⟩
  · rw [hargs]; decide
  · rw [hholes]; decide
  · exact link_side_hole_reported (link_eq_some admissible_hole.guard) hacc
      (fun _ _ h => h) (Or.inr (by simp [holeFrag])) tMix_hole (by simp)

/-- **Hole blindness, instantiated.** The hole is unobservable: the fragment
with `tMix` and the hole-free fragment are observed identically, by
`obs_hole_blind` rather than by evaluation. -/
theorem obs_holeFrag_eq :
    obs registryEx ctxEx fragEx = obs registryEx ctxEx holeFrag :=
  obs_hole_blind (admissible_split registryEx) admissible_hole rfl rfl rfl
    (by decide) (by decide)

/-- The common observation, by evaluation. -/
theorem obs_holeFrag :
    obs registryEx ctxEx holeFrag = .observed [Grounded.Status.defeated] := by rfl

/-! ### Hole erasure is observable (D6) -/

/-- An attack from the complete `vWrap : q` aimed at the complete premise
`leaf l1 : p` *inside* the hole `tHolePair`. -/
def kHoleWrap : Attack := .undermine vWrap tHolePair [.prem 0]

/-- A fragment whose only cover of the `vWrap`/`l1` conflict is the attack aimed
inside its hole. -/
def d6Frag : Fragment :=
  { fragEx with args := [.leaf l1, vWrap, tHolePair], atts := [kHoleWrap] }

/-- The same fragment with the hole, and the attack aimed at it, deleted. -/
def erasedFrag : Fragment := { fragEx with args := [.leaf l1, vWrap], atts := [] }

/-- The two fragments have the same complete arguments in the linked
environment: they differ only in the hole and the attack aimed at it. -/
theorem erasure_keeps_complete_args :
    Check.completeArgs unitPolicyEx.ruleLookup (linkGamma quietCtx d6Frag) registryEx
        d6Frag.args
      = Check.completeArgs unitPolicyEx.ruleLookup (linkGamma quietCtx d6Frag) registryEx
        erasedFrag.args := by decide

/-- …but not the same live attacks: the attack aimed inside the hole has a
complete source, so it is live (D6). This is the premise of `obs_hole_blind`
the pair violates. -/
theorem erasure_changes_live_attacks :
    Check.liveAttacks
        (Check.completeArgs unitPolicyEx.ruleLookup (linkGamma quietCtx d6Frag) registryEx
          d6Frag.args) d6Frag.atts = [kHoleWrap] ∧
      Check.liveAttacks
        (Check.completeArgs unitPolicyEx.ruleLookup (linkGamma quietCtx d6Frag) registryEx
          erasedFrag.args) erasedFrag.atts = [] := by decide

/-- **Counterexample: hole erasure is observable.** Two fragments with one
interface and the same complete arguments, differing only in a located hole and
the attack aimed inside it, are distinguished by a context: the link with the
hole is observed, the link without it is rejected (the `vWrap`/`l1` conflict
loses its only cover). So "fragments that differ only in their holes are
contextually equivalent" is false; `obs_hole_blind` is the corrected statement,
which also asks the live attacks to agree. -/
theorem hole_erasure_observable :
    obs registryEx quietCtx d6Frag = .observed [Grounded.Status.contested] ∧
      (∃ e, obs registryEx quietCtx erasedFrag = .rejected e) ∧
      obs registryEx quietCtx d6Frag ≠ obs registryEx quietCtx erasedFrag := by
  have h₁ : obs registryEx quietCtx d6Frag = .observed [Grounded.Status.contested] := by rfl
  obtain ⟨e, h₂⟩ : ∃ e, obs registryEx quietCtx erasedFrag = .rejected e := ⟨_, rfl⟩
  refine ⟨h₁, ⟨e, h₂⟩, ?_⟩
  rw [h₁, h₂]
  exact fun h => by cases h

end Lara.Examples.LinkHoles
