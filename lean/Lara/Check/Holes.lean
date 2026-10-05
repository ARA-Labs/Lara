/-
Located holes: the specification views of the support-stage partition
(spec §4.4, §8; `docs/located-gap-decision.md`).

`argComplete`/`argHole` classify one declared argument by running support
inference; `completeArgs`/`holeArgs` are `Args(P)` and `Holes(P)` in
declaration order, and `liveAttacks` keeps the attacks whose source is
complete. A term whose inference fails is neither complete nor a hole. These
views state what the checker's partition means; `Lara.Check.Program` derives
the partition from its retained cache, never evaluates the views, and proves
agreement with them. `DeclPartition` is the exact shape of that partition
over the checked declarations: AF node positions, hole positions, cover,
disjointness and order.
-/

import Lara.Compile
import Lara.Check.SupportProof

namespace Lara.Check

open Lara Lara.Support Lara.Attack

/-! ### Complete arguments, holes and live attacks (specification views)

Agreement with the checker's partition: `CheckedArguments.nodes_terms` and
`CheckedArguments.holes_terms`. On the retained core path an inference
failure is a rejection, never an obligation. -/

/-- `w` type-checks with an empty root obligation set: an AF argument. -/
def argComplete {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (w : SupportTerm) : Bool :=
  match inferSupport Pi Gamma reg .root w with
  | .ok result => result.obligations.isEmpty
  | .error _ => false

/-- `w` type-checks with a nonempty root obligation set: a located hole. -/
def argHole {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (w : SupportTerm) : Bool :=
  match inferSupport Pi Gamma reg .root w with
  | .ok result => !result.obligations.isEmpty
  | .error _ => false

/-- `Args(P)` (spec §8): the complete declared arguments, in declaration
order. -/
def completeArgs {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (args : List SupportTerm) :
    List SupportTerm :=
  args.filter (argComplete Pi Gamma reg)

/-- `Holes(P)` (spec §8): the successfully typed declared arguments with a
nonempty root obligation set, in declaration order. -/
def holeArgs {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (args : List SupportTerm) :
    List SupportTerm :=
  args.filter (argHole Pi Gamma reg)

/-- The attacks that compile: those whose source is a complete argument. An
attack sourced at a hole is checked but inert (D4); one targeting a hole is
kept, so its occurrence still reaches complete arguments by closure (D6). -/
def liveAttacks (live : List SupportTerm) (atts : List Attack) :
    List Attack :=
  atts.filter (fun k => decide (k.source ∈ live))

section SpecViews

variable {canon : String → String} {Pi : RuleId → Option Rule}
  {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}

theorem argComplete_iff {w : SupportTerm} :
    argComplete Pi Gamma reg w = true ↔
      ∃ C, HasSupport canon Pi Gamma (certOkOf reg) w C [] := by
  unfold argComplete
  split
  · rename_i result hresult
    constructor
    · intro h
      have hempty : result.obligations = [] := List.isEmpty_iff.mp h
      exact ⟨result.conclusion, by simpa [hempty] using inferSupport_sound hresult⟩
    · rintro ⟨C, hC⟩
      have hinfer := inferSupport_complete hC .root
      rw [hresult] at hinfer
      cases hinfer
      rfl
  · rename_i e herror
    simp only [Bool.false_eq_true, false_iff, not_exists]
    intro C hC
    have hinfer := inferSupport_complete hC .root
    rw [herror] at hinfer
    cases hinfer

theorem argHole_iff {w : SupportTerm} :
    argHole Pi Gamma reg w = true ↔
      ∃ C O, HasSupport canon Pi Gamma (certOkOf reg) w C O ∧ O ≠ [] := by
  unfold argHole
  split
  · rename_i result hresult
    constructor
    · intro h
      have hne : result.obligations ≠ [] := by
        intro hnil
        simp [hnil] at h
      exact ⟨result.conclusion, result.obligations,
        inferSupport_sound hresult, hne⟩
    · rintro ⟨C, O, hC, hO⟩
      have hinfer := inferSupport_complete hC .root
      rw [hresult] at hinfer
      cases hinfer
      cases O with
      | nil => exact absurd rfl hO
      | cons q qs => rfl
  · rename_i e herror
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro C O hC
    have hinfer := inferSupport_complete hC .root
    rw [herror] at hinfer
    cases hinfer

/-- A typed term is complete exactly when its obligations are empty. -/
theorem argComplete_of_hasSupport {w : SupportTerm} {C : Atom}
    {O : List QuestionId}
    (h : HasSupport canon Pi Gamma (certOkOf reg) w C O) :
    argComplete Pi Gamma reg w = O.isEmpty := by
  simp [argComplete, inferSupport_complete h .root]

/-- A typed term is a hole exactly when its obligations are nonempty. -/
theorem argHole_of_hasSupport {w : SupportTerm} {C : Atom}
    {O : List QuestionId}
    (h : HasSupport canon Pi Gamma (certOkOf reg) w C O) :
    argHole Pi Gamma reg w = !O.isEmpty := by
  simp [argHole, inferSupport_complete h .root]

theorem mem_completeArgs_iff {args : List SupportTerm} {w : SupportTerm} :
    w ∈ completeArgs Pi Gamma reg args ↔
      w ∈ args ∧ ∃ C, HasSupport canon Pi Gamma (certOkOf reg) w C [] := by
  simp only [completeArgs, List.mem_filter, argComplete_iff]

theorem mem_holeArgs_iff {args : List SupportTerm} {w : SupportTerm} :
    w ∈ holeArgs Pi Gamma reg args ↔
      w ∈ args ∧
        ∃ C O, HasSupport canon Pi Gamma (certOkOf reg) w C O ∧ O ≠ [] := by
  simp only [holeArgs, List.mem_filter, argHole_iff]

/-- No term is both complete and a hole, whatever lists it is drawn from. -/
theorem completeArgs_holeArgs_disjoint {args args' : List SupportTerm}
    {w : SupportTerm} (hc : w ∈ completeArgs Pi Gamma reg args) :
    w ∉ holeArgs Pi Gamma reg args' := by
  intro hh
  obtain ⟨_, C, hC⟩ := mem_completeArgs_iff.mp hc
  obtain ⟨_, C', O, hC', hO⟩ := mem_holeArgs_iff.mp hh
  exact hO (hasSupport_unique hC hC').2.symm

/-- Under successful support typing, a declaration is complete or a hole. -/
theorem mem_completeArgs_or_holeArgs {args : List SupportTerm}
    {w : SupportTerm} (hw : w ∈ args)
    (htyped : ∃ C O, HasSupport canon Pi Gamma (certOkOf reg) w C O) :
    w ∈ completeArgs Pi Gamma reg args ∨ w ∈ holeArgs Pi Gamma reg args := by
  obtain ⟨C, O, hC⟩ := htyped
  cases O with
  | nil => exact Or.inl (mem_completeArgs_iff.mpr ⟨hw, C, hC⟩)
  | cons q qs => exact Or.inr (mem_holeArgs_iff.mpr ⟨hw, C, _, hC, by simp⟩)

theorem completeArgs_append (xs ys : List SupportTerm) :
    completeArgs Pi Gamma reg (xs ++ ys) =
      completeArgs Pi Gamma reg xs ++ completeArgs Pi Gamma reg ys :=
  List.filter_append _ _

theorem holeArgs_append (xs ys : List SupportTerm) :
    holeArgs Pi Gamma reg (xs ++ ys) =
      holeArgs Pi Gamma reg xs ++ holeArgs Pi Gamma reg ys :=
  List.filter_append _ _

/-- The complete view depends only on the completeness of the listed terms. -/
theorem completeArgs_congr {Pi' : RuleId → Option Rule}
    {Gamma' : LeafId → Option Atom} {reg' : BackendRegistry canon}
    {args : List SupportTerm}
    (h : ∀ w ∈ args, argComplete Pi Gamma reg w = argComplete Pi' Gamma' reg' w) :
    completeArgs Pi Gamma reg args = completeArgs Pi' Gamma' reg' args :=
  List.filter_congr h

theorem completeArgs_subset {args : List SupportTerm} {w : SupportTerm}
    (h : w ∈ completeArgs Pi Gamma reg args) : w ∈ args :=
  (List.mem_filter.mp h).1

theorem completeArgs_sublist (args : List SupportTerm) :
    (completeArgs Pi Gamma reg args).Sublist args :=
  List.filter_sublist

theorem completeArgs_length_le (args : List SupportTerm) :
    (completeArgs Pi Gamma reg args).length ≤ args.length :=
  List.length_filter_le _ _

/-- With every declaration complete, the complete view is the raw list. -/
theorem completeArgs_eq_self {args : List SupportTerm}
    (h : ∀ w ∈ args, ∃ C, HasSupport canon Pi Gamma (certOkOf reg) w C []) :
    completeArgs Pi Gamma reg args = args :=
  List.filter_eq_self.mpr fun w hw => argComplete_iff.mpr (h w hw)

/-- With every declaration complete, there is no hole. -/
theorem holeArgs_eq_nil {args : List SupportTerm}
    (h : ∀ w ∈ args, ∃ C, HasSupport canon Pi Gamma (certOkOf reg) w C []) :
    holeArgs Pi Gamma reg args = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro w hw hhole
  obtain ⟨C, hC⟩ := h w hw
  rw [argHole_of_hasSupport hC] at hhole
  simp at hhole

/-- **Hole status is local to the term's leaves.** Two leaf environments that
agree on the leaves of `w` classify it identically as complete. -/
theorem argComplete_congr_gamma_on {Gamma' : LeafId → Option Atom}
    {w : SupportTerm} (hagree : ∀ l ∈ leaves w, Gamma l = Gamma' l) :
    argComplete Pi Gamma reg w = argComplete Pi Gamma' reg w := by
  apply Bool.eq_iff_iff.mpr
  rw [argComplete_iff, argComplete_iff]
  exact ⟨fun ⟨C, hC⟩ => ⟨C, hasSupport_congr_gamma_on hC hagree⟩,
    fun ⟨C, hC⟩ => ⟨C, hasSupport_congr_gamma_on hC
      fun l hl => (hagree l hl).symm⟩⟩

/-- The hole half of `argComplete_congr_gamma_on`. -/
theorem argHole_congr_gamma_on {Gamma' : LeafId → Option Atom}
    {w : SupportTerm} (hagree : ∀ l ∈ leaves w, Gamma l = Gamma' l) :
    argHole Pi Gamma reg w = argHole Pi Gamma' reg w := by
  apply Bool.eq_iff_iff.mpr
  rw [argHole_iff, argHole_iff]
  exact ⟨fun ⟨C, O, hC, hO⟩ => ⟨C, O, hasSupport_congr_gamma_on hC hagree, hO⟩,
    fun ⟨C, O, hC, hO⟩ => ⟨C, O, hasSupport_congr_gamma_on hC
      (fun l hl => (hagree l hl).symm), hO⟩⟩

end SpecViews

theorem mem_liveAttacks_iff {live : List SupportTerm} {atts : List Attack}
    {k : Attack} : k ∈ liveAttacks live atts ↔ k ∈ atts ∧ k.source ∈ live := by
  simp [liveAttacks]

theorem liveAttacks_eq_self {live : List SupportTerm} {atts : List Attack}
    (h : ∀ k ∈ atts, k.source ∈ live) : liveAttacks live atts = atts :=
  List.filter_eq_self.mpr fun k hk => by simp [h k hk]

/-- Live filtering reads only whether each attack's source is live. -/
theorem liveAttacks_congr {live live' : List SupportTerm} {atts : List Attack}
    (h : ∀ k ∈ atts, k.source ∈ live ↔ k.source ∈ live') :
    liveAttacks live atts = liveAttacks live' atts :=
  List.filter_congr fun k hk => by simp [h k hk]

theorem liveAttacks_append (live : List SupportTerm) (xs ys : List Attack) :
    liveAttacks live (xs ++ ys) = liveAttacks live xs ++ liveAttacks live ys :=
  List.filter_append _ _

/-- Appending an attack whose source is not live leaves the live attacks
unchanged. -/
theorem liveAttacks_snoc_unused_source {live : List SupportTerm}
    (atts : List Attack) {k : Attack} (h : k.source ∉ live) :
    liveAttacks live (atts ++ [k]) = liveAttacks live atts := by
  simp [liveAttacks, h]

/-- Coverage from a live source is unchanged by live filtering: every attack
that can cover an edge from that source is itself live. -/
theorem covered_liveAttacks_iff {live : List SupportTerm} {atts : List Attack}
    {source target : SupportTerm} (hsource : source ∈ live) :
    Compile.Covered (liveAttacks live atts) source target ↔
      Compile.Covered atts source target := by
  constructor
  · rintro ⟨k, hk, hk_source, rest⟩
    exact ⟨k, (mem_liveAttacks_iff.mp hk).1, hk_source, rest⟩
  · rintro ⟨k, hk, hk_source, rest⟩
    exact ⟨k, mem_liveAttacks_iff.mpr ⟨hk, hk_source ▸ hsource⟩,
      hk_source, rest⟩

/-- Attack completeness over the complete arguments is insensitive to live
filtering, since it only asks for coverage from complete sources. -/
theorem attackComplete_iff_complete_live {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    {dp : DefeatPolicy} {args : List SupportTerm} {atts : List Attack} :
    Compile.AttackComplete canon Pi Gamma CertOk dp args
        (liveAttacks args atts) ↔
      Compile.AttackComplete canon Pi Gamma CertOk dp args atts := by
  constructor
  · intro h source hsource target htarget Cs Ct hCs hCt hcontrary hattackable
    exact (covered_liveAttacks_iff hsource).mp
      (h source hsource target htarget Cs Ct hCs hCt hcontrary hattackable)
  · intro h source hsource target htarget Cs Ct hCs hCt hcontrary hattackable
    exact (covered_liveAttacks_iff hsource).mpr
      (h source hsource target htarget Cs Ct hCs hCt hcontrary hattackable)

/-- Attack completeness quantifies only over complete endpoints, so stating it
over the raw declarations or over their complete view is the same. -/
theorem attackComplete_completeArgs_iff {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {reg : BackendRegistry canon} {dp : DefeatPolicy}
    {args : List SupportTerm} {atts : List Attack} :
    Compile.AttackComplete canon Pi Gamma (certOkOf reg) dp
        (completeArgs Pi Gamma reg args) atts ↔
      Compile.AttackComplete canon Pi Gamma (certOkOf reg) dp args atts := by
  constructor
  · intro h source hsource target htarget Cs Ct hCs hCt hcontrary hattackable
    exact h source (mem_completeArgs_iff.mpr ⟨hsource, Cs, hCs⟩)
      target (mem_completeArgs_iff.mpr ⟨htarget, Ct, hCt⟩)
      Cs Ct hCs hCt hcontrary hattackable
  · intro h source hsource target htarget Cs Ct hCs hCt hcontrary hattackable
    exact h source (completeArgs_subset hsource) target
      (completeArgs_subset htarget) Cs Ct hCs hCt hcontrary hattackable

/-- The exact partition of checked declarations `args` into AF nodes and
located holes: AF node `n` sits at declaration `nodeDecls[n]`, each hole at
its own index; every declaration is exactly one of the two; both lists keep
declaration order. -/
structure DeclPartition {canon : String → String}
    {Pi : RuleId → Option Rule} {Gamma : LeafId → Option Atom}
    {CertOk : BackendId → Digest → CertRef → List Atom → Atom → Prop}
    (args : List SupportTerm)
    (nodes : List (Compile.CheckedNode canon Pi Gamma CertOk))
    (nodeDecls : List Nat)
    (holes : List (Compile.CheckedHole canon Pi Gamma CertOk)) : Prop where
  node_decls : nodeDecls.map (fun i => args[i]?) = nodes.map (some ·.term)
  hole_decls : ∀ h ∈ holes, args[h.index]? = some h.term
  cover : ∀ i, i < args.length ↔ i ∈ nodeDecls ∨ ∃ h ∈ holes, h.index = i
  disjoint : ∀ i ∈ nodeDecls, ¬ ∃ h ∈ holes, h.index = i
  nodeDecls_sorted : nodeDecls.Pairwise (· < ·)
  holes_sorted : (holes.map (·.index)).Pairwise (· < ·)

end Lara.Check
