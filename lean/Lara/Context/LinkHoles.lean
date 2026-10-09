/-
# Theory M4 — linking units with located holes (issue #13)

`Lara.Context.Link` states acceptance of a link over `SideOkHoles`, the side
condition that asks every declared argument only to type: complete, or a
located hole (`docs/theory-core.md#the-judgment-and-the-declaration-partition`). This module says what the
accepted link *is* when a side carries holes, in terms of the two sides alone.

* `link_accepted_holes` — the AF arguments of the accepted link are the merged
  complete arguments of the two sides, its located holes are the merged holes
  of the two sides, and its compiled attacks are each side's live attacks
  (those sourced at that side's complete arguments) followed by the whole
  saturation. `link_accepted_raw` is its hole-free special case.
* `link_classify`, `link_node_report`, `link_hole_report` — a declaration is an
  AF node of the link exactly when it is complete in its own side's
  environment and a hole exactly when it is a hole there; a linked hole is
  reported with the conclusion and obligation set its side gives it, and every
  side hole is reported. Hole reports transport through linking unchanged.
* `crossAtts_endpoints_complete`, `crossAtts_avoid_holes` — the saturation never
  touches a hole. This is the two-sided form of
  `Lara.Map.crossPairs_endpoints_complete`.
* `link_hole_source_inert` (D4) — a side attack sourced at a hole compiles to
  nothing in the link and no edge leaves the hole.
* `link_shared_occurrence_edge` (D6) — a side attack from a complete source
  edges onto every complete argument of *either* side that contains its
  attacked occurrence, even when the attack's declared target is a hole.
* `link_edge_iff` — the link's AF edges are the closure coverage, between the
  merged complete arguments, of the two sides' declared attacks plus the
  saturation. Attacks aimed at holes count; attacks sourced at holes do not
  (they cover nothing from a complete source).

Nothing here assumes a side is hole-free.
-/

import Lara.Context.Link

namespace Lara.Context

open Lara.Support Lara.Attack Lara.Compile

/-! ### Filtering commutes with the merge -/

/-- Filtering a structural merge is merging the filtered list: `dedupList`
keeps each element's last occurrence, and a filter neither creates nor moves
occurrences. -/
theorem filter_dedupList {α : Type} [DecidableEq α] (p : α → Bool) :
    ∀ xs : List α, (dedupList xs).filter p = dedupList (xs.filter p)
  | [] => rfl
  | v :: vs => by
      have ih := filter_dedupList p vs
      by_cases hp : p v = true
      · have hmem : v ∈ dedupList vs ↔ v ∈ dedupList (vs.filter p) := by
          rw [mem_dedupList, mem_dedupList, List.mem_filter]
          exact ⟨fun h => ⟨h, hp⟩, fun h => h.1⟩
        rw [List.filter_cons_of_pos hp]
        simp only [dedupList]
        by_cases h : v ∈ dedupList vs
        · rw [if_pos h, if_pos (hmem.mp h)]; exact ih
        · rw [if_neg h, if_neg (fun h' => h (hmem.mpr h')),
            List.filter_cons_of_pos hp, ih]
      · rw [List.filter_cons_of_neg hp]
        simp only [dedupList]
        by_cases h : v ∈ dedupList vs
        · rw [if_pos h]; exact ih
        · rw [if_neg h, List.filter_cons_of_neg hp]; exact ih

/-! ### The cache ignores holes -/

section Cache

variable {canon : String → String} {Pi : RuleId → Option Rule}
  {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}

/-- A term that is not complete has no cached conclusion. -/
theorem conclusionOf_eq_none_of_not_complete {w : SupportTerm}
    (h : Check.argComplete Pi Gamma reg w = false) : conclusionOf Pi Gamma reg w = none := by
  cases hc : conclusionOf Pi Gamma reg w with
  | none => rfl
  | some C =>
      have hsup := conclusionOf_eq_some_iff.mp hc
      rw [Check.argComplete_of_hasSupport hsup] at h
      exact absurd h (by simp)

/-- **The saturation cache reads complete terms only**: it is the cache of the
complete view. So two lists with one complete view saturate identically. -/
theorem conclusionCache_completeArgs :
    ∀ args : List SupportTerm,
      conclusionCache Pi Gamma reg (Check.completeArgs Pi Gamma reg args)
        = conclusionCache Pi Gamma reg args
  | [] => rfl
  | w :: ws => by
      have ih := conclusionCache_completeArgs ws
      simp only [Check.completeArgs] at ih ⊢
      by_cases hw : Check.argComplete Pi Gamma reg w = true
      · rw [List.filter_cons_of_pos hw]
        simp only [conclusionCache, List.filterMap_cons] at ih ⊢
        rw [ih]
      · rw [List.filter_cons_of_neg hw]
        simp only [conclusionCache, List.filterMap_cons] at ih ⊢
        rw [conclusionOf_eq_none_of_not_complete (Bool.eq_false_iff.mpr hw)]
        exact ih

end Cache

/-! ### The saturation never touches a hole -/

section Linked

variable {canon : String → String} {reg : BackendRegistry canon}
  {C : Context} {F : Fragment}

/-- **Both endpoints of every saturation attack are complete** under the linked
environment: the caches it ranges over hold complete terms only. The two-sided
form of `Lara.Map.crossPairs_endpoints_complete`. -/
theorem crossAtts_endpoints_complete {Gamma : LeafId → Option Atom} {k : Attack}
    (hk : k ∈ crossAtts reg Gamma C F) :
    (∃ Cs, HasSupport canon F.policy.ruleLookup Gamma (certOkOf reg) k.source Cs []) ∧
      ∃ Ct, HasSupport canon F.policy.ruleLookup Gamma (certOkOf reg) k.target Ct [] := by
  have hpair : ∀ {srcs tgts : List SupportTerm},
      k ∈ crossAttsFrom canon F.policy.defeat F.policy.ruleLookup
        (conclusionCache F.policy.ruleLookup Gamma reg srcs)
        (conclusionCache F.policy.ruleLookup Gamma reg tgts) →
      (∃ Cs, HasSupport canon F.policy.ruleLookup Gamma (certOkOf reg) k.source Cs []) ∧
        ∃ Ct, HasSupport canon F.policy.ruleLookup Gamma (certOkOf reg) k.target Ct [] := by
    intro srcs tgts h
    obtain ⟨s, hs, t, ht, -, -, rfl⟩ := mem_crossAttsFrom.mp h
    obtain ⟨-, hsSup⟩ := mem_conclusionCache.mp (show (s.1, s.2) ∈ _ from hs)
    obtain ⟨-, htSup⟩ := mem_conclusionCache.mp (show (t.1, t.2) ∈ _ from ht)
    exact ⟨⟨s.2, by rw [attackFor_source]; exact hsSup⟩,
      ⟨t.2, by rw [attackFor_target]; exact htSup⟩⟩
  rw [crossAtts, List.mem_append] at hk
  rcases hk with h | h
  · exact hpair h
  · exact hpair h

/-- The saturation reads each side only through its complete view: a fragment's
holes never change what the link emits. -/
theorem crossAtts_completeArgs {Gamma : LeafId → Option Atom} {F' : Fragment}
    (hpolicy : F'.policy = F.policy)
    (hargs : Check.completeArgs F.policy.ruleLookup Gamma reg F'.args
      = Check.completeArgs F.policy.ruleLookup Gamma reg F.args) :
    crossAtts reg Gamma C F' = crossAtts reg Gamma C F := by
  have hcache : conclusionCache F.policy.ruleLookup Gamma reg F'.args
      = conclusionCache F.policy.ruleLookup Gamma reg F.args := by
    rw [← conclusionCache_completeArgs F'.args, hargs, conclusionCache_completeArgs]
  simp only [crossAtts, hpolicy, hcache]

end Linked

/-! ### The accepted link, exactly -/

section Accepted

variable {canon : String → String} {reg : BackendRegistry canon}
  {C : Context} {F : Fragment}

local notation "Π" => F.policy.ruleLookup
local notation "Γ" => linkGamma C F

/-- **The accepted link, with located holes (issue #13).** For two linkable
sides, the AF arguments of the accepted link are the merged complete arguments
of the two sides; its located holes are the merged holes of the two sides; and
its compiled attacks are the context's live attacks, then the fragment's live
attacks, then the whole saturation — a side's attack is live when its source
is one of that side's own complete arguments (D4), and every saturation attack
is live because its source is complete (`crossAtts_endpoints_complete`).

So the link's framework is assembled from the two sides' complete frameworks
plus the saturation; a hole contributes no node and no live attack. It still
contributes the closure edges of the attacks aimed inside it (D6), which
`link_shared_occurrence_edge` states. -/
theorem link_accepted_holes {unit : Lara.Unit} {Gamma : LeafId → Option Atom}
    {ground : List Atom} {checked : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (hlink : link reg C F = some (unit, Gamma))
    (hcheck : Check.Unit.checkUnit Gamma reg ground unit = .ok checked)
    (hC : SideOkHoles canon reg Γ F.policy C.frame.args C.frame.atts)
    (hF : SideOkHoles canon reg Γ F.policy F.args F.atts) :
    checked.program.args =
        dedupList (Check.completeArgs Π Γ reg C.frame.args
          ++ Check.completeArgs Π Γ reg F.args) ∧
      checked.program.holes =
        dedupList (Check.holeArgs Π Γ reg C.frame.args ++ Check.holeArgs Π Γ reg F.args) ∧
      checked.program.atts =
        Check.liveAttacks (Check.completeArgs Π Γ reg C.frame.args) C.frame.atts
          ++ Check.liveAttacks (Check.completeArgs Π Γ reg F.args) F.atts
          ++ crossAtts reg Γ C F := by
  obtain ⟨-, hunit, hgamma⟩ := link_some_inv hlink
  subst hunit; subst hgamma
  have hs := Check.Unit.checkUnit_sound hcheck
  have hargsRaw : checked.program.args =
      Check.completeArgs Π Γ reg (dedupList (C.frame.args ++ F.args)) := hs.args_eq
  have hargs : checked.program.args =
      dedupList (Check.completeArgs Π Γ reg C.frame.args
        ++ Check.completeArgs Π Γ reg F.args) := by
    rw [hargsRaw, Check.completeArgs, filter_dedupList, List.filter_append]; rfl
  refine ⟨hargs, ?_, ?_⟩
  · show checked.program.holes = _
    rw [hs.holes_eq]
    show (dedupList (C.frame.args ++ F.args)).filter _ = _
    rw [filter_dedupList, List.filter_append]; rfl
  · -- A declared endpoint is live in the link exactly when it is complete.
    have hlive : ∀ {side : List SupportTerm}, (∀ w ∈ side,
        w ∈ dedupList (C.frame.args ++ F.args)) →
        ∀ w ∈ side, w ∈ checked.program.args ↔ w ∈ Check.completeArgs Π Γ reg side := by
      intro side hsub w hw
      rw [hargsRaw, Check.mem_completeArgs_iff, Check.mem_completeArgs_iff]
      exact ⟨fun h => ⟨hw, h.2⟩, fun h => ⟨hsub w hw, h.2⟩⟩
    have hsubC : ∀ w ∈ C.frame.args, w ∈ dedupList (C.frame.args ++ F.args) :=
      fun w hw => mem_dedupList.mpr (List.mem_append_left _ hw)
    have hsubF : ∀ w ∈ F.args, w ∈ dedupList (C.frame.args ++ F.args) :=
      fun w hw => mem_dedupList.mpr (List.mem_append_right _ hw)
    rw [hs.atts_eq]
    show Check.liveAttacks _ (C.frame.atts ++ F.atts ++ crossAtts reg Γ C F) = _
    rw [Check.liveAttacks_append, Check.liveAttacks_append]
    congr 1
    · congr 1
      · exact Check.liveAttacks_congr fun k hk =>
          hlive hsubC k.source (hC.source_declared k hk)
      · exact Check.liveAttacks_congr fun k hk =>
          hlive hsubF k.source (hF.source_declared k hk)
    · refine Check.liveAttacks_eq_self fun k hk => ?_
      rw [hargsRaw, Check.mem_completeArgs_iff]
      exact ⟨(crossAtts_spec hk).2.1, (crossAtts_endpoints_complete hk).1⟩

/-- The saturation attacks of an accepted link avoid its holes, at both ends. -/
theorem crossAtts_avoid_holes {unit : Lara.Unit} {Gamma : LeafId → Option Atom}
    {ground : List Atom} {checked : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (hlink : link reg C F = some (unit, Gamma))
    (hcheck : Check.Unit.checkUnit Gamma reg ground unit = .ok checked)
    {k : Attack} (hk : k ∈ crossAtts reg Γ C F) :
    k.source ∉ checked.program.holes ∧ k.target ∉ checked.program.holes := by
  obtain ⟨-, hunit, hgamma⟩ := link_some_inv hlink
  subst hunit; subst hgamma
  have hs := Check.Unit.checkUnit_sound hcheck
  obtain ⟨⟨Cs, hCs⟩, ⟨Ct, hCt⟩⟩ := crossAtts_endpoints_complete hk
  rw [hs.holes_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨-, C', O, hC', hO⟩ := Check.mem_holeArgs_iff.mp h
    exact hO (hasSupport_unique hCs hC').2.symm
  · obtain ⟨-, C', O, hC', hO⟩ := Check.mem_holeArgs_iff.mp h
    exact hO (hasSupport_unique hCt hC').2.symm

/-! ### Classification and reports transport

Each statement takes the side's typing in *its own* environment `Gs`, any leaf
environment the linked one extends (`linkGamma_extends_left`,
`linkGamma_extends_right`), so a side's hole report — computed before linking —
is the link's. -/

/-- **A declaration's classification is its side's.** A declared argument of
either side, typed in that side's environment with obligation set `O`, is an AF
node of the accepted link iff `O` is empty and a located hole iff it is not. -/
theorem link_classify {unit : Lara.Unit} {Gamma : LeafId → Option Atom}
    {ground : List Atom} {checked : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (hlink : link reg C F = some (unit, Gamma))
    (hcheck : Check.Unit.checkUnit Gamma reg ground unit = .ok checked)
    {Gs : LeafId → Option Atom} (hext : ∀ l p, Gs l = some p → Γ l = some p)
    {w : SupportTerm} {A : Atom} {O : List QuestionId}
    (hw : w ∈ C.frame.args ∨ w ∈ F.args)
    (hsup : HasSupport canon Π Gs (certOkOf reg) w A O) :
    (w ∈ checked.program.args ↔ O = []) ∧ (w ∈ checked.program.holes ↔ O ≠ []) := by
  obtain ⟨-, hunit, hgamma⟩ := link_some_inv hlink
  subst hunit; subst hgamma
  have hs := Check.Unit.checkUnit_sound hcheck
  have hsupL := hasSupport_mono_gamma hext hsup
  have hdecl : w ∈ dedupList (C.frame.args ++ F.args) := by
    rcases hw with h | h
    · exact mem_dedupList.mpr (List.mem_append_left _ h)
    · exact mem_dedupList.mpr (List.mem_append_right _ h)
  rw [hs.args_eq, hs.holes_eq]
  refine ⟨?_, ?_⟩
  · show w ∈ Check.completeArgs Π Γ reg (dedupList (C.frame.args ++ F.args)) ↔ _
    rw [Check.mem_completeArgs_iff]
    constructor
    · rintro ⟨-, A', hA'⟩; exact (hasSupport_unique hsupL hA').2
    · intro hO; subst hO; exact ⟨hdecl, A, hsupL⟩
  · show w ∈ Check.holeArgs Π Γ reg (dedupList (C.frame.args ++ F.args)) ↔ _
    rw [Check.mem_holeArgs_iff]
    constructor
    · rintro ⟨-, A', O', hA', hO'⟩
      rw [(hasSupport_unique hsupL hA').2]; exact hO'
    · intro hO; exact ⟨hdecl, A, O, hsupL, hO⟩

/-- **Every linked hole is a side's hole, reported as its side reports it.** It
is declared by one of the sides, and whatever conclusion and obligation set a
side environment `Gs` gives its term, the linked report carries exactly those. -/
theorem link_hole_report {unit : Lara.Unit} {Gamma : LeafId → Option Atom}
    {ground : List Atom} {checked : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (hlink : link reg C F = some (unit, Gamma))
    (hcheck : Check.Unit.checkUnit Gamma reg ground unit = .ok checked)
    {h : Compile.CheckedHole canon checked.policy.ruleLookup Gamma (certOkOf reg)}
    (hh : h ∈ checked.holes) :
    (h.term ∈ C.frame.args ∨ h.term ∈ F.args) ∧
      ∀ {Gs : LeafId → Option Atom}, (∀ l p, Gs l = some p → Γ l = some p) →
        ∀ {A : Atom} {O : List QuestionId},
          HasSupport canon Π Gs (certOkOf reg) h.term A O →
          h.conclusion = A ∧ h.obligations = O := by
  obtain ⟨-, hunit, hgamma⟩ := link_some_inv hlink
  subst hunit; subst hgamma
  have hs := Check.Unit.checkUnit_sound hcheck
  have hmem : h.term ∈ checked.program.holes := by
    rw [← checked.holes_terms]; exact List.mem_map_of_mem hh
  rw [hs.holes_eq] at hmem
  refine ⟨?_, ?_⟩
  · have hdecl := (Check.mem_holeArgs_iff.mp hmem).1
    exact List.mem_append.mp (mem_dedupList.mp hdecl)
  · intro Gs hext A O hsup
    have hsupL : HasSupport canon (linkedUnit reg C F).policy.ruleLookup Γ (certOkOf reg)
        h.term A O := hasSupport_mono_gamma hext hsup
    rw [← hs.policy_eq] at hsupL
    exact hasSupport_unique h.valid hsupL

/-- **Every side hole is reported by the link**, with the conclusion and the
obligation set its side environment gives it. -/
theorem link_side_hole_reported {unit : Lara.Unit} {Gamma : LeafId → Option Atom}
    {ground : List Atom} {checked : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (hlink : link reg C F = some (unit, Gamma))
    (hcheck : Check.Unit.checkUnit Gamma reg ground unit = .ok checked)
    {Gs : LeafId → Option Atom} (hext : ∀ l p, Gs l = some p → Γ l = some p)
    {w : SupportTerm} {A : Atom} {O : List QuestionId}
    (hw : w ∈ C.frame.args ∨ w ∈ F.args)
    (hsup : HasSupport canon Π Gs (certOkOf reg) w A O) (hO : O ≠ []) :
    ∃ h ∈ checked.holes, h.term = w ∧ h.conclusion = A ∧ h.obligations = O := by
  have hhole := ((link_classify hlink hcheck hext hw hsup).2).mpr hO
  rw [← checked.holes_terms] at hhole
  obtain ⟨h, hh, hterm⟩ := List.mem_map.mp hhole
  have hrep := (link_hole_report hlink hcheck hh).2 hext (hterm ▸ hsup)
  exact ⟨h, hh, hterm, hrep⟩

/-- **Every side's complete argument is a node of the link**, with the
conclusion its side environment gives it; and a node's recorded conclusion is
that side conclusion. -/
theorem link_node_report {unit : Lara.Unit} {Gamma : LeafId → Option Atom}
    {ground : List Atom} {checked : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (hlink : link reg C F = some (unit, Gamma))
    (hcheck : Check.Unit.checkUnit Gamma reg ground unit = .ok checked)
    {Gs : LeafId → Option Atom} (hext : ∀ l p, Gs l = some p → Γ l = some p)
    {w : SupportTerm} {A : Atom}
    (hw : w ∈ C.frame.args ∨ w ∈ F.args)
    (hsup : HasSupport canon Π Gs (certOkOf reg) w A []) :
    (∃ n ∈ checked.nodes, n.term = w) ∧
      ∀ n ∈ checked.nodes, n.term = w → n.conclusion = A := by
  have hnode := ((link_classify hlink hcheck hext hw hsup).1).mpr rfl
  obtain ⟨-, hunit, hgamma⟩ := link_some_inv hlink
  subst hunit; subst hgamma
  have hs := Check.Unit.checkUnit_sound hcheck
  refine ⟨?_, ?_⟩
  · rw [← checked.nodes_terms] at hnode
    obtain ⟨n, hn, hterm⟩ := List.mem_map.mp hnode
    exact ⟨n, hn, hterm⟩
  · intro n _ hterm
    have hsupL : HasSupport canon (linkedUnit reg C F).policy.ruleLookup Γ (certOkOf reg)
        n.term A [] := hterm ▸ hasSupport_mono_gamma hext hsup
    rw [← hs.policy_eq] at hsupL
    exact (hasSupport_unique n.valid hsupL).1

/-! ### Attacks at holes: D4 and D6 through a link -/

/-- **D4 through a link.** A side attack sourced at a declaration that is a hole
in its side's environment compiles to nothing in the accepted link, and no edge
leaves its source. -/
theorem link_hole_source_inert {unit : Lara.Unit} {Gamma : LeafId → Option Atom}
    {ground : List Atom} {checked : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (hlink : link reg C F = some (unit, Gamma))
    (hcheck : Check.Unit.checkUnit Gamma reg ground unit = .ok checked)
    {Gs : LeafId → Option Atom} (hext : ∀ l p, Gs l = some p → Γ l = some p)
    {k : Attack} {A : Atom} {O : List QuestionId}
    (hsrc : k.source ∈ C.frame.args ∨ k.source ∈ F.args)
    (hsup : HasSupport canon Π Gs (certOkOf reg) k.source A O) (hO : O ≠ []) :
    k ∉ checked.program.atts ∧ ∀ b, ¬ Compile.Edge checked.program k.source b := by
  have hhole := ((link_classify hlink hcheck hext hsrc hsup).2).mpr hO
  obtain ⟨-, hunit, -⟩ := link_some_inv hlink
  subst hunit
  exact (Check.Unit.checkUnit_sound hcheck).hole_inert_source hhole

/-- **D6 through a link.** A declared attack of either side whose source is
complete edges, in the accepted link, onto every complete argument of either
side that contains its attacked occurrence — whether its declared target is a
complete argument or a located hole. In particular an attack a side aims inside
its own hole can reach a complete argument of the *other* side. -/
theorem link_shared_occurrence_edge {unit : Lara.Unit} {Gamma : LeafId → Option Atom}
    {ground : List Atom} {checked : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (hlink : link reg C F = some (unit, Gamma))
    (hcheck : Check.Unit.checkUnit Gamma reg ground unit = .ok checked)
    (hC : SideOkHoles canon reg Γ F.policy C.frame.args C.frame.atts)
    (hF : SideOkHoles canon reg Γ F.policy F.args F.atts)
    {k : Attack} (hk : k ∈ C.frame.atts ∨ k ∈ F.atts)
    (hsrc : ∃ A, HasSupport canon Π Γ (certOkOf reg) k.source A [])
    {t b : SupportTerm} (hocc : AttackOcc k t)
    (hb : b ∈ C.frame.args ∨ b ∈ F.args)
    (hbsup : ∃ A, HasSupport canon Π Γ (certOkOf reg) b A [])
    (hcontains : Contains b t) :
    Compile.Edge checked.program k.source b := by
  obtain ⟨-, hunit, hgamma⟩ := link_some_inv hlink
  subst hunit; subst hgamma
  have hs := Check.Unit.checkUnit_sound hcheck
  have hdecl : ∀ {w}, w ∈ C.frame.args ∨ w ∈ F.args →
      w ∈ dedupList (C.frame.args ++ F.args) := by
    intro w hw
    rcases hw with h | h
    · exact mem_dedupList.mpr (List.mem_append_left _ h)
    · exact mem_dedupList.mpr (List.mem_append_right _ h)
  have hsrcDecl : k.source ∈ C.frame.args ∨ k.source ∈ F.args := by
    rcases hk with h | h
    · exact Or.inl (hC.source_declared k h)
    · exact Or.inr (hF.source_declared k h)
  have hsrcArg : k.source ∈ checked.program.args := by
    rw [hs.args_eq, Check.mem_completeArgs_iff]; exact ⟨hdecl hsrcDecl, hsrc⟩
  have hbArg : b ∈ checked.program.args := by
    rw [hs.args_eq, Check.mem_completeArgs_iff]; exact ⟨hdecl hb, hbsup⟩
  have hkAtt : k ∈ checked.program.atts := by
    rw [hs.atts_eq, Check.mem_liveAttacks_iff]
    refine ⟨?_, hsrcArg⟩
    show k ∈ C.frame.atts ++ F.atts ++ crossAtts reg Γ C F
    rcases hk with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ h)
    · exact List.mem_append_left _ (List.mem_append_right _ h)
  exact Compile.closure_reaches_shared_occurrence checked.program hkAtt hocc hbArg hcontains

/-- **The edges of a link with holes.** An edge of the accepted link runs between
two merged complete arguments and is closure coverage by the sides' declared
attacks or the saturation; holes are not endpoints, and the attacks aimed inside
them count like any other. -/
theorem link_edge_iff {unit : Lara.Unit} {Gamma : LeafId → Option Atom}
    {ground : List Atom} {checked : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)}
    (hlink : link reg C F = some (unit, Gamma))
    (hcheck : Check.Unit.checkUnit Gamma reg ground unit = .ok checked)
    (hC : SideOkHoles canon reg Γ F.policy C.frame.args C.frame.atts)
    (hF : SideOkHoles canon reg Γ F.policy F.args F.atts) {a b : SupportTerm} :
    Compile.Edge checked.program a b ↔
      a ∈ dedupList (Check.completeArgs Π Γ reg C.frame.args
          ++ Check.completeArgs Π Γ reg F.args) ∧
        b ∈ dedupList (Check.completeArgs Π Γ reg C.frame.args
          ++ Check.completeArgs Π Γ reg F.args) ∧
        Covered (C.frame.atts ++ F.atts ++ crossAtts reg Γ C F) a b := by
  have hargs := (link_accepted_holes hlink hcheck hC hF).1
  obtain ⟨-, hunit, hgamma⟩ := link_some_inv hlink
  subst hunit; subst hgamma
  have hs := Check.Unit.checkUnit_sound hcheck
  rw [← hargs]
  unfold Compile.Edge
  constructor
  · rintro ⟨ha, hb, hcov⟩
    rw [hs.atts_eq, Check.covered_liveAttacks_iff ha] at hcov
    exact ⟨ha, hb, hcov⟩
  · rintro ⟨ha, hb, hcov⟩
    refine ⟨ha, hb, ?_⟩
    rw [hs.atts_eq, Check.covered_liveAttacks_iff ha]
    exact hcov

end Accepted

end Lara.Context
