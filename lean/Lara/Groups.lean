/-
Duplicate-report groups (spec §4.3, M0 C16).

The frozen §4.3 definitions and their metatheory. A duplicate-report group is
untrusted elaborator output: several leaves reporting one measurand cell. The
checker enforces agreement within each group by the frozen `≡` relation
(`Lara.Prop.equiv`):

* a `≡`-consistent group admits normally;
* an inconsistent group quarantines every member — each leaves the checking
  context, so any argument using it is excluded and the dependent claim routes
  to `gap` (never a rejection);
* a policy may escalate a detected conflict to a whole-program reject (R9).

This module is the shared, driver-boundary semantics mirrored by
`Lara.Driver.groupConsistent` / `quarantineUnit` / `groupConflictReject` on the
Haskell side. It carries no `sorry` and stays within the standard axiom trio.
-/

import Lara.Prop
import Lara.Support

namespace Lara.Groups

open Lara Lara.Support

/-- A declared duplicate-report group: a named set of leaf ids reporting one
measurand cell (spec §4.3). The name locates an R9 diagnostic. -/
structure DupGroup where
  id : String
  members : List LeafId
deriving DecidableEq

/-- The policy outcome for a `≢` group (spec §4.3): quarantine (default) or an
escalating whole-program reject. -/
inductive GroupConflictMode where
  | quarantine
  | reject
deriving DecidableEq

/-- The proposition a leaf reports, from the decoded leaf table. -/
def leafProp (leaves : List (LeafId × Atom)) (l : LeafId) : Option Atom :=
  (leaves.find? (fun e => decide (e.1 = l))).map (·.2)

/-- The member propositions of a group, `none` when any member has no leaf-table
entry. Mirrors the Haskell `groupConsistent`'s `mapM` lookup: an unresolvable
member is never silently skipped, so a dangling member cannot degrade a group to
a vacuously-consistent singleton (defense-in-depth — both validated front doors
already reject such a group as malformed, R14). -/
def memberProps (leaves : List (LeafId × Atom)) (g : DupGroup) :
    Option (List Atom) :=
  g.members.mapM (leafProp leaves)

/-- **Spec-level consistency** (§4.3): every member resolves and the members'
propositions are pairwise `≡`. A group with an unresolvable member is
inconsistent, matching the Haskell twin. -/
def Consistent (canon : String → String) (leaves : List (LeafId × Atom))
    (g : DupGroup) : Prop :=
  ∃ ps, memberProps leaves g = some ps ∧ ∀ p ∈ ps, ∀ q ∈ ps, equiv canon p q

/-- **Executable consistency**: every member resolves and is `≡` the first.
Because `≡` is an equivalence this decides `Consistent` (see `consistentB_iff`),
and it is linear rather than quadratic. -/
def consistentB (canon : String → String) (leaves : List (LeafId × Atom))
    (g : DupGroup) : Bool :=
  match memberProps leaves g with
  | none => false
  | some ps =>
    match ps with
    | [] => true
    | p :: ps' => ps'.all (fun q => decide (equiv canon p q))

/-- The leaf ids quarantined by the inconsistent groups (spec §4.3). -/
def quarantined (canon : String → String) (leaves : List (LeafId × Atom))
    (groups : List DupGroup) : List LeafId :=
  (groups.filter (fun g => ! consistentB canon leaves g)).flatMap (·.members)

-- Whether a support term uses any of the given leaves anywhere in its tree
-- (spec §4.3 "any argument using a conflicted cell").
mutual
  def usesLeaf (qs : List LeafId) : SupportTerm → Bool
    | .leaf l => decide (l ∈ qs)
    | .inst _ _ premises discharges _ _ =>
        usesLeafList qs premises || usesLeafDisch qs discharges
  /-- The premise-list companion of `usesLeaf` (structural recursion). -/
  def usesLeafList (qs : List LeafId) : List SupportTerm → Bool
    | [] => false
    | w :: ws => usesLeaf qs w || usesLeafList qs ws
  /-- The discharge-list companion of `usesLeaf`. -/
  def usesLeafDisch (qs : List LeafId) : List (QuestionId × SupportTerm) → Bool
    | [] => false
    | d :: ds => usesLeaf qs d.2 || usesLeafDisch qs ds
end

/-- Keep an argument iff it uses no quarantined leaf. -/
def keepArg (qs : List LeafId) (a : String × SupportTerm) : Bool :=
  ! usesLeaf qs a.2
/-- The surviving arguments after §4.3 quarantine. -/
def quarantineArgs (qs : List LeafId) (args : List (String × SupportTerm)) :
    List (String × SupportTerm) :=
  args.filter (keepArg qs)

/-- The surviving leaf context after §4.3 quarantine. -/
def quarantineLeaves (qs : List LeafId) (leaves : List (LeafId × Atom)) :
    List (LeafId × Atom) :=
  leaves.filter (fun e => ! decide (e.1 ∈ qs))

/-- At least one declared group is inconsistent. -/
def anyConflict (canon : String → String) (leaves : List (LeafId × Atom))
    (groups : List DupGroup) : Bool :=
  groups.any (fun g => ! consistentB canon leaves g)

/-- Whether the policy escalates a detected conflict to a whole-program reject
(R9, spec §4.3): the mode is `reject` and some declared group is `≢`. -/
def conflictReject (canon : String → String) (mode : GroupConflictMode)
    (leaves : List (LeafId × Atom)) (groups : List DupGroup) : Bool :=
  match mode with
  | .reject => anyConflict canon leaves groups
  | .quarantine => false

/-! ## Metatheory of the frozen §4.3 definitions -/

/-- Pairwise-`≡` over a list is equivalent to every element being `≡` the head
(the load-bearing use of `≡`'s transitivity and symmetry). -/
theorem all_equiv_head_iff (canon : String → String) :
    ∀ L : List Atom,
      (match L with
        | [] => true
        | p :: ps => ps.all (fun q => decide (equiv canon p q))) = true
      ↔ (∀ p ∈ L, ∀ q ∈ L, equiv canon p q)
  | [] => by simp
  | p :: ps => by
    constructor
    · intro h
      have hall : ∀ q ∈ ps, equiv canon p q := by
        have := (List.all_eq_true).1 h
        intro q hq
        have := this q hq
        simpa using of_decide_eq_true this
      -- every element of `p :: ps` is `≡ p`
      have hhead : ∀ x ∈ p :: ps, equiv canon p x := by
        intro x hx
        rcases List.mem_cons.1 hx with hx | hx
        · subst hx; exact equiv_refl canon _
        · exact hall x hx
      intro x hx y hy
      exact equiv_trans canon (equiv_symm canon (hhead x hx)) (hhead y hy)
    · intro h
      have : ∀ q ∈ ps, decide (equiv canon p q) = true := by
        intro q hq
        exact decide_eq_true (h p (by simp) q (by simp [hq]))
      exact (List.all_eq_true).2 this

/-- **`≡`-consistency, decided.** The linear `consistentB` decides the quadratic
spec-level `Consistent` — the members resolve and pairwise-`≡` ⟺ every member
resolves and is `≡` the first. -/
theorem consistentB_iff (canon : String → String)
    (leaves : List (LeafId × Atom)) (g : DupGroup) :
    consistentB canon leaves g = true ↔ Consistent canon leaves g := by
  unfold consistentB Consistent
  cases h : memberProps leaves g with
  | none => simp
  | some L =>
    constructor
    · intro hb
      exact ⟨L, rfl, (all_equiv_head_iff canon L).1 hb⟩
    · rintro ⟨ps, hps, hall⟩
      obtain rfl : L = ps := by injection hps
      exact (all_equiv_head_iff canon L).2 hall

/-- Membership in the quarantine set: exactly the members of an inconsistent
group. -/
theorem mem_quarantined_iff (canon : String → String)
    (leaves : List (LeafId × Atom)) (groups : List DupGroup) (l : LeafId) :
    l ∈ quarantined canon leaves groups
      ↔ ∃ g ∈ groups, consistentB canon leaves g = false ∧ l ∈ g.members := by
  unfold quarantined
  simp only [List.mem_flatMap, List.mem_filter]
  constructor
  · rintro ⟨g, ⟨hg, hcon⟩, hmem⟩
    exact ⟨g, hg, by simpa using hcon, hmem⟩
  · rintro ⟨g, hg, hcon, hmem⟩
    exact ⟨g, ⟨hg, by simpa using hcon⟩, hmem⟩

/-- **Quarantine excludes.** An argument that uses a quarantined leaf does not
survive `quarantineArgs`: the dependent claim loses that support, so it can
never be `justified` (spec §4.3, "absence of reliable evidence"). -/
theorem quarantined_arg_excluded (qs : List LeafId)
    (args : List (String × SupportTerm)) (a : String × SupportTerm)
    (h : usesLeaf qs a.2 = true) :
    a ∉ quarantineArgs qs args := by
  intro hmem
  have hkeep : keepArg qs a = true := (List.mem_filter.1 hmem).2
  simp [keepArg, h] at hkeep

/-- **Quarantine leaves the context.** A quarantined leaf has no entry in the
post-quarantine context. This is a supporting fact only: the shipped pipeline
never lets such a leaf reach the §6.1 leaf rule, because every argument that uses
it is already dropped by `quarantineArgs` (see `quarantined_arg_excluded`) — the
actual `gap` mechanism. Removing the leaf from the context is defense-in-depth,
not the route to `gap`. -/
theorem quarantined_leaf_absent (qs : List LeafId)
    (leaves : List (LeafId × Atom)) (l : LeafId) (hl : l ∈ qs) :
    (quarantineLeaves qs leaves).find? (fun e => decide (e.1 = l)) = none := by
  unfold quarantineLeaves
  apply List.find?_eq_none.2
  intro e he
  have hkeep : (! decide (e.1 ∈ qs)) = true := (List.mem_filter.1 he).2
  have hnotmem : e.1 ∉ qs := by
    simpa using hkeep
  intro hdec
  have : e.1 = l := of_decide_eq_true hdec
  exact hnotmem (this ▸ hl)

-- **`usesLeaf` is monotone in the quarantined-leaf list.**  Enlarging the
-- seed only makes more terms report use of a quarantined leaf.  This is the
-- fact that makes a more restrictive admission policy unable to retain an
-- argument (metatheory plan, `more_restrictive_cannot_add_structure`).  A
-- `mutual` block because `SupportTerm` is a plain inductive with list fields
-- (see `SupportTerm.decEq`); the definitions live in `Prop` and are used as
-- theorems.
mutual
  def usesLeaf_mono {qs qs' : List LeafId} (h : ∀ l, l ∈ qs → l ∈ qs') :
      (t : SupportTerm) → usesLeaf qs t = true → usesLeaf qs' t = true
    | .leaf l, huse => by
        simp [usesLeaf] at huse ⊢
        exact h l huse
    | .inst _ _ premises discharges _ _, huse => by
        cases hleft : usesLeafList qs premises with
        | true =>
            have : usesLeafList qs' premises = true :=
              usesLeafList_mono h premises hleft
            simp [usesLeaf, this]
        | false =>
            have hright : usesLeafDisch qs discharges = true := by
              simpa [usesLeaf, hleft] using huse
            have : usesLeafDisch qs' discharges = true :=
              usesLeafDisch_mono h discharges hright
            simp [usesLeaf, hleft, this]
  def usesLeafList_mono {qs qs' : List LeafId} (h : ∀ l, l ∈ qs → l ∈ qs') :
      (ts : List SupportTerm) → usesLeafList qs ts = true → usesLeafList qs' ts = true
    | [], huse => by simp [usesLeafList] at huse
    | w :: ws, huse => by
        cases hleft : usesLeaf qs w with
        | true =>
            have : usesLeaf qs' w = true := usesLeaf_mono h w hleft
            simp [usesLeafList, this]
        | false =>
            have hright : usesLeafList qs ws = true := by
              simpa [usesLeafList, hleft] using huse
            have : usesLeafList qs' ws = true := usesLeafList_mono h ws hright
            simp [usesLeafList, hleft, this]
  def usesLeafDisch_mono {qs qs' : List LeafId} (h : ∀ l, l ∈ qs → l ∈ qs') :
      (ds : List (QuestionId × SupportTerm)) →
        usesLeafDisch qs ds = true → usesLeafDisch qs' ds = true
    | [], huse => by simp [usesLeafDisch] at huse
    | d :: ds, huse => by
        cases hleft : usesLeaf qs d.2 with
        | true =>
            have : usesLeaf qs' d.2 = true := usesLeaf_mono h d.2 hleft
            simp [usesLeafDisch, this]
        | false =>
            have hright : usesLeafDisch qs ds = true := by
              simpa [usesLeafDisch, hleft] using huse
            have : usesLeafDisch qs' ds = true := usesLeafDisch_mono h ds hright
            simp [usesLeafDisch, hleft, this]
end

/-- **Escalation, characterized.** The R9 reject fires exactly when the policy
escalates and some declared group is `≢`. -/
theorem conflictReject_iff (canon : String → String) (mode : GroupConflictMode)
    (leaves : List (LeafId × Atom)) (groups : List DupGroup) :
    conflictReject canon mode leaves groups = true
      ↔ mode = .reject ∧ ∃ g ∈ groups, consistentB canon leaves g = false := by
  cases mode with
  | quarantine => simp [conflictReject]
  | reject =>
    simp only [conflictReject, anyConflict, List.any_eq_true, true_and]
    constructor
    · rintro ⟨g, hg, hcon⟩
      exact ⟨g, hg, by simpa using hcon⟩
    · rintro ⟨g, hg, hcon⟩
      exact ⟨g, hg, by simpa using hcon⟩

/-! ## Consistent groups are inert

When every declared group is `≡`-consistent, quarantine has nothing to remove:
the quarantine set is empty and both quarantine operations are the identity.
This is what lets a reader that cannot report a conditional status — the PW
outer runtime (`Lara.PW.Run`, #326) — accept a world that declares groups
whenever none of them conflicts: the unit it checks is the declared unit, and
the local driver would have checked the same one. -/

/-- **No conflict, no quarantine.** With every declared group consistent, the
quarantine set is empty. -/
theorem quarantined_eq_nil (canon : String → String) (leaves : List (LeafId × Atom))
    (groups : List DupGroup) (h : ∀ g ∈ groups, consistentB canon leaves g = true) :
    quarantined canon leaves groups = [] := by
  unfold quarantined
  have hf : groups.filter (fun g => ! consistentB canon leaves g) = [] := by
    rw [List.filter_eq_nil_iff]
    intro g hg
    simp [h g hg]
  rw [hf]
  rfl

/-- `anyConflict` is false exactly when every declared group is consistent. -/
theorem anyConflict_eq_false_iff (canon : String → String) (leaves : List (LeafId × Atom))
    (groups : List DupGroup) :
    anyConflict canon leaves groups = false ↔ ∀ g ∈ groups, consistentB canon leaves g = true := by
  unfold anyConflict
  simp [List.any_eq_false]

/-- An empty quarantine set keeps every leaf. -/
theorem quarantineLeaves_nil (leaves : List (LeafId × Atom)) :
    quarantineLeaves [] leaves = leaves := by
  unfold quarantineLeaves
  simp

-- No support term uses a leaf from the empty list. Mutual, like `usesLeaf`.
mutual
  theorem usesLeaf_nil : (t : SupportTerm) → usesLeaf [] t = false
    | .leaf l => by simp [usesLeaf]
    | .inst _ _ premises discharges _ _ => by
        simp [usesLeaf, usesLeafList_nil premises, usesLeafDisch_nil discharges]
  theorem usesLeafList_nil : (ts : List SupportTerm) → usesLeafList [] ts = false
    | [] => by simp [usesLeafList]
    | w :: ws => by simp [usesLeafList, usesLeaf_nil w, usesLeafList_nil ws]
  theorem usesLeafDisch_nil : (ds : List (QuestionId × SupportTerm)) → usesLeafDisch [] ds = false
    | [] => by simp [usesLeafDisch]
    | d :: ds => by simp [usesLeafDisch, usesLeaf_nil d.2, usesLeafDisch_nil ds]
end

/-- With nothing quarantined, every argument is kept. -/
theorem keepArg_nil (a : String × SupportTerm) : keepArg [] a = true := by
  simp [keepArg, usesLeaf_nil]

/-- An empty quarantine set keeps every argument. -/
theorem quarantineArgs_nil (args : List (String × SupportTerm)) :
    quarantineArgs [] args = args := by
  unfold quarantineArgs
  simp [keepArg_nil]

end Lara.Groups
