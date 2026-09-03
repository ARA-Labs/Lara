/-
# Theory M4, phase F1 — the structural merge is semantically inert

`link` merges structurally identical arguments instead of rejecting the link
(D3). That choice is forced: rejecting a cross-boundary term collision would
make contextual equivalence syntax-sensitive and refute every congruence
coarser than term-set equality. This module discharges the obligation the
choice creates — that merging changes nothing observable — by instantiating the
generic node-merging morphism of `Lara.Invariants.Merge` at the merge `link`
performs, and tying the result to the carrier an accepted linked program
presents.
-/

import Lara.Context.Link
import Lara.Invariants.Merge

namespace Lara.Context

open Lara.Support Lara.Attack Lara.Compile Lara.Invariants

/-! ### The instance: collapsing duplicate arguments

The position of a term in a list, by structural equality. Core's `List.idxOf`
would supply the bound (`List.idxOf_lt_length_iff`) but not the two facts the
merge morphism actually consumes — what `getElem?` returns at that index, and
that on a duplicate-free list the position of the element at `i` is `i`. Rolling
the recursion here makes all three a two-line induction over the same
definition. -/

/-- The position of the first structurally identical term, or the length. -/
def posOf : List Support.SupportTerm → Support.SupportTerm → Nat
  | [], _ => 0
  | v :: vs, w => if v = w then 0 else posOf vs w + 1

theorem posOf_lt {w : Support.SupportTerm} :
    ∀ {l : List Support.SupportTerm}, w ∈ l → posOf l w < l.length := by
  intro l
  induction l with
  | nil => intro hw; exact absurd hw (by simp)
  | cons v vs ih =>
      intro hw
      simp only [posOf, List.length_cons]
      by_cases h : v = w
      · rw [if_pos h]; exact Nat.succ_pos _
      · rw [if_neg h]
        have hmem : w ∈ vs := by
          rcases List.mem_cons.mp hw with heq | h'
          · exact absurd heq.symm h
          · exact h'
        exact Nat.succ_lt_succ (ih hmem)

theorem getElem?_posOf {w : Support.SupportTerm} :
    ∀ {l : List Support.SupportTerm}, w ∈ l → l[posOf l w]? = some w := by
  intro l
  induction l with
  | nil => intro hw; exact absurd hw (by simp)
  | cons v vs ih =>
      intro hw
      simp only [posOf]
      by_cases h : v = w
      · rw [if_pos h, h]; rfl
      · rw [if_neg h]
        have hmem : w ∈ vs := by
          rcases List.mem_cons.mp hw with heq | h'
          · exact absurd heq.symm h
          · exact h'
        simpa using ih hmem

theorem posOf_getElem : ∀ {l : List Support.SupportTerm}, l.Nodup →
    ∀ {i : Nat} {w : Support.SupportTerm}, l[i]? = some w → posOf l w = i := by
  intro l
  induction l with
  | nil => intro _ i w hget; exact absurd hget (by simp)
  | cons v vs ih =>
      intro hnd i w hget
      obtain ⟨hv, hvs⟩ := List.nodup_cons.mp hnd
      cases i with
      | zero =>
          have hvw : v = w := Option.some.inj (by simpa using hget)
          simp only [posOf, if_pos hvw]
      | succ n =>
          have hget' : vs[n]? = some w := by simpa using hget
          have hmem : w ∈ vs := List.mem_of_getElem? hget'
          have hne : ¬ v = w := fun h => hv (h ▸ hmem)
          simp only [posOf, if_neg hne]
          exact congrArg (· + 1) (ih hvs hget')

/-- **The carrier a declared term list presents.** Node `i` is the conclusion
of the `i`-th term; the edge relation is the compiled closure test, which reads
only the two terms and the declared attacks. This is `Compile.edgeB` — see
`termCarrier_attack_eq_edgeB` — lifted off a `CheckedProgram`, so that the
merge statement can compare a list against its duplicate-free image, which no
`CheckedProgram` can hold (`Compile.CheckedProgram.nodup`). -/
def termCarrier (concl : Support.SupportTerm → Atom) (atts : List Attack.Attack)
    (l : List Support.SupportTerm) : Invariants.StructuredAF where
  nodes := l.map concl
  attack := fun i j =>
    match l[i]?, l[j]? with
    | some s, some t => Compile.coveredB atts s t
    | _, _ => false

/-- The carrier's edge relation *is* the checked program's edge decider. -/
theorem termCarrier_attack_eq_edgeB {canon : String → String}
    {Pi : Support.RuleId → Option Support.Rule} {Gamma : Support.LeafId → Option Atom}
    {CertOk : Support.BackendId → Support.Digest → Support.CertRef →
      List Atom → Atom → Prop}
    {dp : Attack.DefeatPolicy}
    (concl : Support.SupportTerm → Atom)
    (P : Compile.CheckedProgram canon Pi Gamma CertOk dp) :
    (termCarrier concl P.atts P.args).attack = Compile.edgeB P := rfl

/-- The merge map: send a position to the position its term occupies in the
duplicate-free image. -/
def dedupPos (l : List Support.SupportTerm) (i : Nat) : Nat :=
  match l[i]? with
  | some w => posOf (dedupList l) w
  | none => 0

/-- **Collapsing duplicates is a carrier merge.** -/
theorem dedup_carrierMerge (concl : Support.SupportTerm → Atom)
    (atts : List Attack.Attack) (l : List Support.SupportTerm) :
    CarrierMerge (termCarrier concl atts l) (termCarrier concl atts (dedupList l))
      (dedupPos l) := by
  have hsize₁ : (termCarrier concl atts l).size = l.length := by
    simp [termCarrier, Invariants.StructuredAF.size]
  have hsize₂ : (termCarrier concl atts (dedupList l)).size = (dedupList l).length := by
    simp [termCarrier, Invariants.StructuredAF.size]
  have hget : ∀ i, i < l.length → ∃ w, l[i]? = some w ∧ w ∈ l := by
    intro i hi
    exact ⟨l[i], List.getElem?_eq_getElem hi, List.getElem_mem hi⟩
  have hdedup : ∀ {i : Nat} {w : Support.SupportTerm}, l[i]? = some w →
      (dedupList l)[dedupPos l i]? = some w := by
    intro i w hw
    have hmem : w ∈ dedupList l := mem_dedupList.mpr (List.mem_of_getElem? hw)
    simp only [dedupPos, hw]
    exact getElem?_posOf hmem
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hsize₁] at hi
    obtain ⟨w, hw, hmem⟩ := hget i hi
    rw [hsize₂]
    simp only [dedupPos, hw]
    exact posOf_lt (mem_dedupList.mpr hmem)
  · intro j hj
    rw [hsize₂] at hj
    have hw : (dedupList l)[j]? = some (dedupList l)[j] := List.getElem?_eq_getElem hj
    have hmem : (dedupList l)[j] ∈ l := mem_dedupList.mp (List.getElem_mem hj)
    refine ⟨posOf l (dedupList l)[j], ?_, ?_⟩
    · rw [hsize₁]; exact posOf_lt hmem
    · simp only [dedupPos, getElem?_posOf hmem]
      exact posOf_getElem (dedupList_nodup l) hw
  · intro i hi
    rw [hsize₁] at hi
    obtain ⟨w, hw, -⟩ := hget i hi
    simp only [termCarrier, List.getElem?_map, hw, hdedup hw]
  · intro i hi j hj
    rw [hsize₁] at hi hj
    obtain ⟨wi, hwi, -⟩ := hget i hi
    obtain ⟨wj, hwj, -⟩ := hget j hj
    simp only [termCarrier, hwi, hwj, hdedup hwi, hdedup hwj]

/-- **D3, discharged: the structural merge is semantically inert.** Merging
structurally identical declared arguments preserves the four-state status of
every claim. Identical terms have identical edge sets, so the position they
share carries the label each of them had. -/
theorem dedup_status_eq (canon : String → String)
    (concl : Support.SupportTerm → Atom) (atts : List Attack.Attack)
    (l : List Support.SupportTerm) (p : Atom) :
    Invariants.status canon (termCarrier concl atts l) p
      = Invariants.status canon (termCarrier concl atts (dedupList l)) p :=
  (dedup_carrierMerge concl atts l).status_eq canon p

/-! ### The merge, at the linked program

`dedup_status_eq` is about `termCarrier`, so it bites on the real pipeline only
once that carrier is identified with the one an accepted unit presents. It is:
`Compile.edgeB` *is* the term carrier's edge relation
(`termCarrier_attack_eq_edgeB`), and the checker's node cache records exactly
the conclusion `conclusionOf` infers. -/

/-- A conclusion assignment read off the checker. Terms that do not check get a
junk atom; on an accepted program there are none
(`Compile.CheckedProgram.complete`). -/
def checkerConcl {canon : String → String} (Pi : RuleId → Option Rule)
    (Gamma : LeafId → Option Atom) (reg : BackendRegistry canon)
    (w : SupportTerm) : Atom :=
  (conclusionOf Pi Gamma reg w).getD (.atom "" .nil)

/-- **The M1 carrier of an accepted unit is the term carrier of its declared
arguments.** -/
theorem compileUnit_eq_termCarrier {canon : String → String}
    {Gamma : LeafId → Option Atom} {reg : BackendRegistry canon}
    (acc : Lara.Unit.CheckedUnit canon Gamma (certOkOf reg)) :
    Invariants.compileUnit acc
      = termCarrier (checkerConcl acc.policy.ruleLookup Gamma reg)
          acc.program.atts acc.program.args := by
  have hnodes : acc.nodes.map (·.conclusion)
      = acc.program.args.map (checkerConcl acc.policy.ruleLookup Gamma reg) := by
    rw [← acc.nodes_terms, List.map_map]
    refine List.map_congr_left (fun n hn => ?_)
    have hconcl : conclusionOf acc.policy.ruleLookup Gamma reg n.term = some n.conclusion :=
      conclusionOf_eq_some_iff.mpr n.valid
    simp only [Function.comp_apply, checkerConcl, hconcl, Option.getD_some]
  simp only [Invariants.compileUnit, termCarrier, hnodes]
  rfl

/-- **D3, discharged where it is used.** The status every atom receives over an
accepted linked program is the status it receives over the *unmerged*
concatenation of the two sides' declared arguments: the structural merge the
link performs is invisible. -/
theorem link_merge_status_eq {canon : String → String}
    {reg : BackendRegistry canon} {C : Context} {F : Fragment}
    {acc : Lara.Unit.CheckedUnit canon (linkGamma C F) (certOkOf reg)}
    (hargs : acc.program.args = dedupList (C.frame.args ++ F.args))
    (p : Atom) :
    Invariants.status canon
        (termCarrier (checkerConcl acc.policy.ruleLookup (linkGamma C F) reg)
          acc.program.atts (C.frame.args ++ F.args)) p
      = Invariants.status canon (Invariants.compileUnit acc) p := by
  rw [compileUnit_eq_termCarrier, hargs]
  exact dedup_status_eq canon _ _ _ p

/-! ### Re-indexing a fragment into the linked program (D10)

A fragment's own framework is positional (`Grounded.Arg = Nat` indexes
`F.args`), and so is the linked program's. `linkedPos` is the transport between
them: the position a fragment argument occupies after the merge. It is total —
the merge only removes duplicates — and it lands on the same term, which is
what makes a statement about a fragment's node also a statement about a node of
every program the fragment is linked into. -/

/-- The position a declared term occupies in the linked argument list. -/
def linkedPos (C : Context) (F : Fragment) (w : SupportTerm) : Nat :=
  posOf (dedupList (C.frame.args ++ F.args)) w

/-- **A fragment argument keeps its term at its linked position.** -/
theorem linkedUnit_args_linkedPos_frag {canon : String → String}
    {reg : BackendRegistry canon} {C : Context} {F : Fragment} {w : SupportTerm}
    (h : w ∈ F.args) :
    (linkedUnit reg C F).args[linkedPos C F w]? = some w :=
  getElem?_posOf (mem_dedupList.mpr (List.mem_append_right _ h))

/-- The context's arguments are re-indexed by the same map. -/
theorem linkedUnit_args_linkedPos_ctx {canon : String → String}
    {reg : BackendRegistry canon} {C : Context} {F : Fragment} {w : SupportTerm}
    (h : w ∈ C.frame.args) :
    (linkedUnit reg C F).args[linkedPos C F w]? = some w :=
  getElem?_posOf (mem_dedupList.mpr (List.mem_append_left _ h))

/-- The transport from a fragment's own positions: the term at index `i` of
`F.args` is the term at index `linkedPos …` of the linked program. -/
theorem linkedPos_of_index {canon : String → String} {reg : BackendRegistry canon}
    {C : Context} {F : Fragment} {i : Nat} {w : SupportTerm}
    (h : F.args[i]? = some w) :
    (linkedUnit reg C F).args[linkedPos C F w]? = some w :=
  linkedUnit_args_linkedPos_frag (List.mem_of_getElem? h)

end Lara.Context
