/-
Accepted-unit consistency and the computed complete-claim projection
(spec §9 result 7 / mechanization claim C09).

This module is downstream-only: it imports the public accepted-unit boundary
but no checker or policy module imports it. It uses `Unit.CheckedUnit`'s exact
retained checker cache to compute complete support without re-inference, Path B
to turn a contrary target into an attackable target, detailed acceptance's
whole-program attack completeness to obtain the compiled edge, and generic
grounded conflict-freedom to exclude joint acceptance. The headline theorem is
only about `completeClaimFor` computed from retained nodes; it does not quantify
over arbitrary caller-supplied claims and does not compute `holes(P,p)` or
`incompleteAlternative`. Ordered self-pairs are included, so self-conflict is
covered.
-/

import Lara.Check.Unit
import Lara.Grounded

namespace Lara.Consistency

open Lara.Support

/-! ### Path-B attackability -/

private theorem hasSupport_inst_root
    {Pi : RuleId → Option Rule}
    {rn : RuleId} {θ : Subst} {ws : List SupportTerm}
    {D : List (QuestionId × SupportTerm)} {H : List QuestionId}
    {assurance : Assurance} {C : Atom} {O : List QuestionId}
    (h : HasSupport canon Pi Gamma CertOk
      (.inst rn θ ws D H assurance) C O) :
    ∃ r, Pi rn = some r ∧ instAPat θ r.concl = some C := by
  cases h with
  | inst hside _ _ =>
      exact ⟨_, hside.rule, hside.concl⟩

/-- In a well-formed accepted policy, the target of an instantiated contrary
cannot be a strict-rule root. Hence every complete contrary target is either a
leaf or a defeasible-root instance, exactly the compile layer's conflict
attackability condition. -/
theorem wellFormed_contrary_target_attackable
    (unit : Unit.CheckedUnit canon Gamma CertOk)
    {_source target : SupportTerm} {Cs Ct : Atom}
    (htarget : HasSupport canon unit.policy.ruleLookup Gamma CertOk
      target Ct [])
    (hcontrary :
      Attack.ContraryMatch canon unit.policy.defeat Cs Ct) :
    Compile.ConflictAttackable unit.policy.ruleLookup target := by
  cases target with
  | leaf l =>
      trivial
  | inst rn θ ws D H assurance =>
      obtain ⟨r, hruleLookup, hconclusion⟩ :=
        hasSupport_inst_root htarget
      refine ⟨r, hruleLookup, ?_⟩
      cases hmode : r.mode with
      | defeasible =>
          rfl
      | strict =>
          obtain ⟨declaration, hdeclaration, hid, hrule⟩ :=
            Policy.lookupRuleDecl_some_mem hruleLookup
          have hreachable :
              Policy.StrictReachable unit.policy r.concl := by
            rw [← hrule]
            exact .conclusion hdeclaration (by simpa [hrule] using hmode)
          exact False.elim
            ((Policy.wellFormed_no_strict_contrary_right
              unit.policy_wf hreachable hconclusion) hcontrary)

/-! ### Computed complete-claim support -/

/-- Stable declaration-order indices of retained complete checked nodes whose
exact conclusions are canonically equivalent to `p`. -/
def claimSupportFor
    (unit : Unit.CheckedUnit canon Gamma CertOk) (p : Atom) : List Nat :=
  unit.nodes.zipIdx.filterMap fun entry =>
    if equiv canon entry.1.conclusion p then some entry.2 else none

/-- The complete-support projection for `p`. Its holes are definitionally empty:
this is not the full `holes(P,p)` or `incompleteAlternative` computation, which
is deferred to M3. -/
def completeClaimFor
    (unit : Unit.CheckedUnit canon Gamma CertOk) (p : Atom) : Grounded.Claim :=
  { support := claimSupportFor unit p, holes := [] }

/-- The computed projection contains exactly the indices of retained checked
nodes with canonically equivalent conclusions. -/
theorem mem_claimSupportFor_iff
    {unit : Unit.CheckedUnit canon Gamma CertOk} {p : Atom} {i : Nat} :
    i ∈ claimSupportFor unit p ↔
      ∃ node, unit.nodes[i]? = some node ∧
        equiv canon node.conclusion p := by
  unfold claimSupportFor
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨node, index⟩, hzip, hselected⟩
    by_cases hequiv : equiv canon node.conclusion p
    · simp [hequiv] at hselected
      subst index
      obtain ⟨_, hi, hnode⟩ := List.mem_zipIdx hzip
      have hi' : i < unit.nodes.length := by simpa using hi
      refine ⟨node, ?_, hequiv⟩
      rw [List.getElem?_eq_getElem hi']
      simpa using congrArg some hnode.symm
    · simp [hequiv] at hselected
  · rintro ⟨node, hnode, hequiv⟩
    have hzipGet :
        unit.nodes.zipIdx[i]? = some (node, i) := by
      simp [hnode]
    exact ⟨(node, i), List.mem_of_getElem? hzipGet, by simp [hequiv]⟩

/-! ### Accepted-unit result 7 -/

/-- Contrary retained arguments of an accepted unit cannot both occur in its
compiled grounded extension. -/
theorem contrary_args_not_both_grounded
    (unit : Unit.CheckedUnit canon Gamma CertOk)
    {i j : Nat}
    {source target :
      Compile.CheckedNode canon unit.policy.ruleLookup Gamma CertOk}
    {Cs Ct : Atom}
    (hsource : unit.nodes[i]? = some source)
    (htarget : unit.nodes[j]? = some target)
    (hsourceConclusion : source.conclusion = Cs)
    (htargetConclusion : target.conclusion = Ct)
    (hcontrary :
      Attack.ContraryMatch canon unit.policy.defeat Cs Ct) :
    ¬ (i ∈ Grounded.grounded (Compile.checkedAF unit.program) ∧
       j ∈ Grounded.grounded (Compile.checkedAF unit.program)) := by
  subst Cs
  subst Ct
  intro hgrounded
  have hsourceAt :
      unit.program.args[i]? = some source.term := by
    rw [← unit.nodes_terms, List.getElem?_map, hsource]
    rfl
  have htargetAt :
      unit.program.args[j]? = some target.term := by
    rw [← unit.nodes_terms, List.getElem?_map, htarget]
    rfl
  have hsourceMem : source.term ∈ unit.program.args :=
    List.mem_of_getElem? hsourceAt
  have htargetMem : target.term ∈ unit.program.args :=
    List.mem_of_getElem? htargetAt
  have hattackable :
      Compile.ConflictAttackable unit.policy.ruleLookup target.term :=
    wellFormed_contrary_target_attackable
      (_source := source.term) unit target.valid hcontrary
  have hedge :
      Compile.Edge unit.program source.term target.term :=
    Compile.complete_conflict_edge unit.program unit.attack_complete
      hsourceMem htargetMem source.valid target.valid hcontrary hattackable
  have hedgeB : Compile.edgeB unit.program i j = true :=
    (Compile.edgeB_iff hsourceAt htargetAt).mpr hedge
  apply
    Grounded.grounded_conflictFree
      (F := Compile.checkedAF unit.program)
      i hgrounded.1 j hgrounded.2
  simpa [Compile.checkedAF, Compile.toAF] using hedgeB

/-- **Result 7 for computed complete claims.** Directionally contrary claims
computed from an accepted unit's retained nodes cannot both be justified. No
caller-supplied claim or unchecked support index enters the statement. -/
theorem contrary_claims_not_both_justified
    (unit : Unit.CheckedUnit canon Gamma CertOk)
    {p q : Atom}
    (hcontrary :
      Attack.ContraryMatch canon unit.policy.defeat p q) :
    ¬ (Grounded.statusC (Compile.checkedAF unit.program)
          (completeClaimFor unit p) = Grounded.Status.justified ∧
       Grounded.statusC (Compile.checkedAF unit.program)
          (completeClaimFor unit q) = Grounded.Status.justified) := by
  rintro ⟨hp, hq⟩
  obtain ⟨i, hiSupport, hiLabel⟩ :=
    (Grounded.statusC_justified_iff
      (Compile.checkedAF unit.program) (completeClaimFor unit p)).mp hp
  obtain ⟨j, hjSupport, hjLabel⟩ :=
    (Grounded.statusC_justified_iff
      (Compile.checkedAF unit.program) (completeClaimFor unit q)).mp hq
  obtain ⟨source, hsource, hsourceConclusion⟩ :=
    mem_claimSupportFor_iff.mp hiSupport
  obtain ⟨target, htarget, htargetConclusion⟩ :=
    mem_claimSupportFor_iff.mp hjSupport
  have hnodeContrary :
      Attack.ContraryMatch canon unit.policy.defeat
        source.conclusion target.conclusion :=
    (Attack.contraryMatch_congr
      hsourceConclusion htargetConclusion).mpr hcontrary
  apply contrary_args_not_both_grounded unit
    hsource htarget rfl rfl hnodeContrary
  constructor
  · exact (Grounded.directIn_iff i).mp
      ((Grounded.labelC_inn_iff i).mp hiLabel)
  · exact (Grounded.directIn_iff j).mp
      ((Grounded.labelC_inn_iff j).mp hjLabel)

end Lara.Consistency
