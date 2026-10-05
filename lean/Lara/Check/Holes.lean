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

/-- The executable coverage check from a live source is unchanged by live
filtering. -/
theorem coveredB_liveAttacks {live : List SupportTerm} {atts : List Attack}
    {source target : SupportTerm} (hsource : source ∈ live) :
    Compile.coveredB (liveAttacks live atts) source target =
      Compile.coveredB atts source target := by
  unfold Compile.coveredB liveAttacks
  rw [List.any_filter]
  congr 1
  funext k
  by_cases hk : k.source = source
  · simp [hk, hsource]
  · simp [hk]

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

/-! ### Declaration positions

The partition's index lists are determined by the classification: AF node
positions are exactly the complete declarations, hole positions exactly the
holes, both ascending. Callers that never saw the checker's cache (the surface
observation, a renamed unit) recover the cached maps from this. -/

/-- The ascending positions of the declarations satisfying `p`. -/
def declPositions (p : SupportTerm → Bool) (args : List SupportTerm) :
    List Nat :=
  (List.range args.length).filter fun i => (args[i]?.map p).getD false

/-- The positions of the complete declarations: the AF-node-to-declaration
map, as a specification view. -/
def completeDecls {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (args : List SupportTerm) : List Nat :=
  declPositions (argComplete Pi Gamma reg) args

/-- The positions of the located holes, as a specification view. -/
def holeDecls {canon : String → String}
    (Pi : RuleId → Option Rule) (Gamma : LeafId → Option Atom)
    (reg : BackendRegistry canon) (args : List SupportTerm) : List Nat :=
  declPositions (argHole Pi Gamma reg) args

theorem mem_declPositions_iff {p : SupportTerm → Bool}
    {args : List SupportTerm} {i : Nat} :
    i ∈ declPositions p args ↔ ∃ w, args[i]? = some w ∧ p w = true := by
  unfold declPositions
  rw [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hi, hp⟩
    rw [List.getElem?_eq_getElem hi] at hp ⊢
    exact ⟨_, rfl, by simpa using hp⟩
  · rintro ⟨w, hw, hp⟩
    exact ⟨lt_of_getElem?_some hw, by simp [hw, hp]⟩

theorem declPositions_map {p : SupportTerm → Bool}
    (f : SupportTerm → SupportTerm) (args : List SupportTerm) :
    declPositions p (args.map f) = declPositions (p ∘ f) args := by
  simp [declPositions, List.getElem?_map, Option.map_map]

/-- The position view reads only the predicate on the listed declarations. -/
theorem declPositions_congr {p q : SupportTerm → Bool}
    {args : List SupportTerm} (h : ∀ w ∈ args, p w = q w) :
    declPositions p args = declPositions q args := by
  unfold declPositions
  apply List.filter_congr
  intro i _
  cases hi : args[i]? with
  | none => rfl
  | some w => simp [h w (List.mem_of_getElem? hi)]

theorem declPositions_sorted (p : SupportTerm → Bool)
    (args : List SupportTerm) : (declPositions p args).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

theorem declPositions_cons (p : SupportTerm → Bool) (w : SupportTerm)
    (args : List SupportTerm) :
    declPositions p (w :: args) =
      (if p w then [0] else []) ++ (declPositions p args).map Nat.succ := by
  unfold declPositions
  rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
  cases hp : p w <;> simp [hp, Function.comp_def]

/-- One position per selected declaration. -/
theorem declPositions_length (p : SupportTerm → Bool) :
    ∀ args : List SupportTerm,
      (declPositions p args).length = (args.filter p).length
  | [] => rfl
  | w :: args => by
      rw [declPositions_cons, List.filter_cons]
      cases hp : p w <;> simp [declPositions_length p args]

/-- Two strictly ascending lists with the same members are equal. -/
theorem eq_of_pairwise_lt_of_mem_iff :
    ∀ {l₁ l₂ : List Nat}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
      (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | a :: _, [], _, _, h => absurd ((h a).mp (by simp)) (by simp)
  | [], b :: _, _, _, h => absurd ((h b).mpr (by simp)) (by simp)
  | a :: as, b :: bs, h₁, h₂, h => by
      rw [List.pairwise_cons] at h₁ h₂
      have hab : a = b := by
        rcases List.mem_cons.mp ((h a).mp (by simp)) with hab | ha
        · exact hab
        · rcases List.mem_cons.mp ((h b).mpr (by simp)) with hba | hb
          · exact hba.symm
          · exact absurd (Nat.lt_trans (h₂.1 a ha) (h₁.1 b hb)) (Nat.lt_irrefl b)
      subst hab
      refine congrArg _ (eq_of_pairwise_lt_of_mem_iff h₁.2 h₂.2 fun x => ?_)
      constructor
      · intro hx
        rcases List.mem_cons.mp ((h x).mp (by simp [hx])) with hxa | hx'
        · exact absurd (hxa ▸ h₁.1 x hx) (Nat.lt_irrefl x)
        · exact hx'
      · intro hx
        rcases List.mem_cons.mp ((h x).mpr (by simp [hx])) with hxa | hx'
        · exact absurd (hxa ▸ h₂.1 x hx) (Nat.lt_irrefl x)
        · exact hx'

section PartitionPositions

variable {canon : String → String} {Pi : RuleId → Option Rule}
  {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
  {args : List SupportTerm}
  {nodes : List (Compile.CheckedNode canon Pi Gamma (certOkOf reg))}
  {nodeDecls : List Nat}
  {holes : List (Compile.CheckedHole canon Pi Gamma (certOkOf reg))}

theorem DeclPartition.mem_nodeDecls_iff
    (hp : DeclPartition args nodes nodeDecls holes) {i : Nat} :
    i ∈ nodeDecls ↔ ∃ w, args[i]? = some w ∧ argComplete Pi Gamma reg w = true := by
  constructor
  · intro hi
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hi
    have hmap := congrArg (·[n]?) hp.node_decls
    simp only [List.getElem?_map, hn, Option.map_some] at hmap
    cases hnode : nodes[n]? with
    | none => rw [hnode] at hmap; cases hmap
    | some node =>
      rw [hnode, Option.map_some] at hmap
      exact ⟨node.term, Option.some.inj hmap, by
        rw [argComplete_of_hasSupport node.valid]; rfl⟩
  · rintro ⟨w, hw, hcomplete⟩
    rcases (hp.cover i).mp (lt_of_getElem?_some hw) with hnode | ⟨h, hh, rfl⟩
    · exact hnode
    · have hat := hp.hole_decls h hh
      rw [hw, Option.some.injEq] at hat
      subst hat
      rw [argComplete_of_hasSupport h.valid] at hcomplete
      cases hO : h.obligations with
      | nil => exact absurd hO h.nonempty
      | cons q qs => rw [hO] at hcomplete; cases hcomplete

theorem DeclPartition.mem_holeIndices_iff
    (hp : DeclPartition args nodes nodeDecls holes) {i : Nat} :
    i ∈ holes.map (·.index) ↔
      ∃ w, args[i]? = some w ∧ argHole Pi Gamma reg w = true := by
  constructor
  · intro hi
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hi
    refine ⟨h.term, hp.hole_decls h hh, ?_⟩
    rw [argHole_of_hasSupport h.valid]
    cases hO : h.obligations with
    | nil => exact absurd hO h.nonempty
    | cons q qs => rfl
  · rintro ⟨w, hw, hhole⟩
    rcases (hp.cover i).mp (lt_of_getElem?_some hw) with hnode | ⟨h, hh, rfl⟩
    · obtain ⟨w', hw', hcomplete⟩ := hp.mem_nodeDecls_iff.mp hnode
      rw [hw, Option.some.injEq] at hw'
      subst hw'
      obtain ⟨C, hC⟩ := argComplete_iff.mp hcomplete
      rw [argHole_of_hasSupport hC] at hhole
      cases hhole
    · exact List.mem_map.mpr ⟨h, hh, rfl⟩

/-- **The AF-node map is the complete-position view.** -/
theorem DeclPartition.nodeDecls_eq
    (hp : DeclPartition args nodes nodeDecls holes) :
    nodeDecls = completeDecls Pi Gamma reg args :=
  eq_of_pairwise_lt_of_mem_iff hp.nodeDecls_sorted (declPositions_sorted _ _)
    fun _ => hp.mem_nodeDecls_iff.trans mem_declPositions_iff.symm

/-- **The hole positions are the hole-position view.** -/
theorem DeclPartition.holeIndices_eq
    (hp : DeclPartition args nodes nodeDecls holes) :
    holes.map (·.index) = holeDecls Pi Gamma reg args :=
  eq_of_pairwise_lt_of_mem_iff hp.holes_sorted (declPositions_sorted _ _)
    fun _ => hp.mem_holeIndices_iff.trans mem_declPositions_iff.symm

end PartitionPositions

end Lara.Check
